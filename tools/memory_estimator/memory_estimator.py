#!/usr/bin/env python3

import io
import os
import re
import json
import argparse
import subprocess
from json_report_generator import update_json_report
from makefile_generator import generate_makefile_from_template


__THIS_FILE_PATH__ = os.path.dirname(os.path.abspath(__file__))
__MAKE_FILE_TEMPLATE__ = os.path.join(__THIS_FILE_PATH__, 'template', 'Makefile.template')
__GENERATED_MAKE_FILE__ = os.path.join(__THIS_FILE_PATH__, 'Makefile')

__JSON_REPORT_TEMPLATE__ = os.path.join(__THIS_FILE_PATH__, 'template', 'report.json.template')
__GENERATED_JSON_REPORT__ = os.path.join(__THIS_FILE_PATH__, 'report.json')
__REPORT_LIBS_JSON__ = os.path.join(__THIS_FILE_PATH__, 'template', 'report_libs.json')

__FREERTOS_SRC_DIR__ = os.path.join('FreeRTOS', 'Source')
__FREERTOS_PLUS_SRC_DIR__ = os.path.join('FreeRTOS-Plus', 'Source')
__IOT_LIBS_DIR__ = os.path.join(__FREERTOS_PLUS_SRC_DIR__, 'FreeRTOS-IoT-Libraries')

__LIB_NAME_TO_SRC_DIRS_MAPPING__ = {
    'light-mqtt' : [
                        os.path.join(__IOT_LIBS_DIR__, 'c_sdk', 'standard', 'mqtt', 'src', 'iot_mqtt_lightweight_api.c'),
                        os.path.join(__IOT_LIBS_DIR__, 'c_sdk', 'standard', 'mqtt', 'src', 'iot_mqtt_helper.c')
                   ],
    'mqtt'       : [
                        os.path.join(__IOT_LIBS_DIR__, 'c_sdk', 'standard', 'mqtt', 'src')
                   ],
    'https'      : [
                        os.path.join(__IOT_LIBS_DIR__, 'c_sdk', 'standard', 'https', 'src'),
                        os.path.join(__FREERTOS_PLUS_SRC_DIR__, 'http-parser')
                   ],
    'shadow'     : [
                        os.path.join(__IOT_LIBS_DIR__, 'c_sdk', 'aws', 'shadow', 'src'),
                        os.path.join(__IOT_LIBS_DIR__, 'c_sdk', 'aws', 'common', 'src')
                   ],
    'jobs'       : [
                        os.path.join(__IOT_LIBS_DIR__, 'c_sdk', 'aws', 'jobs', 'src'),
                        os.path.join(__IOT_LIBS_DIR__, 'c_sdk', 'aws', 'common', 'src')
                   ],
    'ota-mqtt'   : [
                         os.path.join(__IOT_LIBS_DIR__, 'c_sdk', 'aws', 'ota', 'src', 'aws_iot_ota_agent.c'),
                         os.path.join(__IOT_LIBS_DIR__, 'c_sdk', 'aws', 'ota', 'src', 'aws_iot_ota_interface.c'),
                         os.path.join(__IOT_LIBS_DIR__, 'c_sdk', 'aws', 'ota', 'src', 'mqtt', 'aws_iot_ota_mqtt.c'),
                         os.path.join(__IOT_LIBS_DIR__, 'c_sdk', 'aws', 'ota', 'src', 'mqtt', 'aws_iot_ota_cbor.c')
                   ],
    'ota-http'  :  [
                        os.path.join(__IOT_LIBS_DIR__, 'c_sdk', 'aws', 'ota', 'src')
                   ],
    'kernel'     : [
                        os.path.join(__FREERTOS_SRC_DIR__, 'event_groups.c'),
                        os.path.join(__FREERTOS_SRC_DIR__, 'list.c'),
                        os.path.join(__FREERTOS_SRC_DIR__, 'queue.c'),
                        os.path.join(__FREERTOS_SRC_DIR__, 'stream_buffer.c'),
                        os.path.join(__FREERTOS_SRC_DIR__, 'tasks.c'),
                        os.path.join(__FREERTOS_SRC_DIR__, 'timers.c'),
                        os.path.join(__FREERTOS_SRC_DIR__, 'portable', 'GCC', 'ARM_CM4F', 'port.c')
                   ]
}


def apply_patches(freertos_lts, lib_name):
    patches = {}

    # This should ideally be empty as we should be able to control all the
    # configurations via config files. However, OTA currently defines the
    # logging level in a header file as opposed to taking it from a config file.
    # As a result, we need to patch the header file before calculating the size
    # as we want to turn off logging while calculating size. Later when logging
    # level is moved to a config file, it will not be needed and we will turn
    # off logging in the header file tools\memory_estimator\config_files\aws_ota_agent_config.h.
    if 'ota' in lib_name:
        ota_agent_header_file = os.path.join(freertos_lts, __IOT_LIBS_DIR__, 'c_sdk', 'aws', 'ota', 'include', 'aws_iot_ota_agent.h')

        with open(ota_agent_header_file) as ota_agent_header_file_handle:
            original_content = ota_agent_header_file_handle.read()

        # Turn off logging in the OTA code while calculating sizes.
        patched_content = original_content.replace('#define OTA_DEBUG_LOG_LEVEL    1', '#define OTA_DEBUG_LOG_LEVEL    0')

        with open(ota_agent_header_file, 'w') as ota_agent_header_file_handle:
            ota_agent_header_file_handle.write(patched_content)

        patches[ota_agent_header_file] = original_content

    return patches


def revert_patches(patches):
    for patched_file in patches:
        original_content = patches[patched_file]
        with open(patched_file, 'w') as patched_file_handle:
            patched_file_handle.write(original_content)


def calculate_sizes(freertos_lts, optimization, lib_name, compiler, sizetool, dontclean):
    # Apply the required patches to the source code.
    patches = apply_patches(freertos_lts, lib_name)

    # Generate Makefile.
    generate_makefile(freertos_lts, optimization, lib_name)

    # Run make build.
    warnings = make(compiler)

    # Run make size.
    calculated_sizes = calculate_size(sizetool)

    # Remove the generated artifacts.
    if not dontclean:
        clean()
        remove_generated_makefile()

    # Print the generated warnings.
    pretty_print_warnings(warnings)

    # Print the calculated sizes.
    pretty_print_sizes(calculated_sizes)

    # Revert the applied patches to the source code.
    revert_patches(patches)

    return calculated_sizes


def generate_makefile(freertos_lts, optimization, lib_name):
    freertos_src_dir = os.path.join(freertos_lts, __FREERTOS_SRC_DIR__)
    freertos_plus_src_dir = os.path.join(freertos_lts, __FREERTOS_PLUS_SRC_DIR__)

    # Generate include dirs list.
    include_dirs = []
    for root, dirs, files in os.walk(freertos_plus_src_dir):
        for dir in dirs:
            include_dirs.append(os.path.join(root, dir))

    # Add FreeRTOS include dirs for Cortex-M4 to include dirs list.
    include_dirs.append(os.path.join(freertos_src_dir, 'include'))
    include_dirs.append(os.path.join(freertos_src_dir, 'portable', 'GCC', 'ARM_CM4F'))

    # Add config files dir to include dirs list.
    include_dirs.append(os.path.join(__THIS_FILE_PATH__, 'config_files'))

    # Generate source files list.
    if lib_name in __LIB_NAME_TO_SRC_DIRS_MAPPING__:
        source_files=[]
        for lib_src_location in __LIB_NAME_TO_SRC_DIRS_MAPPING__[lib_name]:
            lib_src_full_path = os.path.join(freertos_lts, lib_src_location)

            # Traverse if the location is a directory, otherwise just append it.
            if os.path.isdir(lib_src_full_path):
                for root, dirs, files in os.walk(lib_src_full_path):
                    for file in files:
                        if file.endswith('.c'):
                            source_files.append(os.path.join(root, file))
            else:
                source_files.append(lib_src_full_path)
    else:
        raise ValueError('Library name: {} is invalid'.format(lib_name))

    # Generate makefile.
    generate_makefile_from_template(source_files,
                                    include_dirs,
                                    optimization,
                                    __MAKE_FILE_TEMPLATE__,
                                    __GENERATED_MAKE_FILE__)


def make(compiler):
    compiler_command='CC={}'.format(compiler)

    print('---- Starting Build. Compiler: {} ---- \n'.format(compiler))

    proc = subprocess.Popen(['make', '-f', __GENERATED_MAKE_FILE__, compiler_command],
                            stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT)

    warnings = []
    for line in iter(proc.stdout.readline, b''):
        line = line.decode('utf-8').strip()
        print(line)
        if re.match('.*: warning: .*', line):
            warnings.append(line.strip())

    print('---- Build Finished ---- \n')
    return warnings


def calculate_size(sizetool):
    sizetool_command='SIZETOOL={}'.format(sizetool)

    proc = subprocess.Popen(['make', '-f', __GENERATED_MAKE_FILE__, 'size', sizetool_command],
                            stdout=subprocess.PIPE)

    calculated_sizes = []
    for line in iter(proc.stdout.readline, b''):
        line = line.decode('utf-8').strip()
        calculated_sizes.append(line)

    return calculated_sizes


def clean():
    proc = subprocess.Popen(['make', '-f', __GENERATED_MAKE_FILE__, 'clean'],
                            stdout=subprocess.PIPE)

    for line in iter(proc.stdout.readline, b''):
        line = line.decode('utf-8').strip()
        print(line)


def remove_generated_makefile():
    os.remove(__GENERATED_MAKE_FILE__)


def pretty_print_warnings(warnings):
    if len(warnings) > 0:
        print('\n\n---- Warnings ---- ')
        print('------------------')
        for warning in warnings:
            print(warning)
        print('------------------')


def pretty_print_sizes(sizes):
    print('\n\n---- Sizes ---- ')
    print('---------------')
    for size in sizes[1:]:
        print(size)
    print('---------------')


def parse_arguments():
    parser = argparse.ArgumentParser(description='Memory Estimator.')

    parser.add_argument('-p', '--lts-path', required=True, help='Path to FreeRTOS LTS directory.')
    parser.add_argument('-o', '--optimization', default='O0', help='Compiler optimization (O0, Os etc.).')
    parser.add_argument('-l', '--lib', default='mqtt', help='Library name to generate the memory estimate for.')
    parser.add_argument('-c', '--compiler', default='arm-none-eabi-gcc', help='Compiler to use.')
    parser.add_argument('-s', '--sizetool', default='arm-none-eabi-size', help='Size tool to use.')
    parser.add_argument('-d', '--dontclean', action='store_true', help='Do not clean the generated artifacts.')
    parser.add_argument('-g', '--generate-report', action='store_true', help='Generate the JSON report.')

    return vars(parser.parse_args())



def main():
    args = parse_arguments()

    if args['generate_report']:
        # Start by creating an empty JSON file which is populated as sizes are
        # calculated.
        with open(__GENERATED_JSON_REPORT__, 'w') as json_report_file:
            json_report_file.write(json.dumps({}))

        # Read the libraries which are to be included in the report.
        with open(__REPORT_LIBS_JSON__) as report_libs_file:
            report_libs_json_data = json.load(report_libs_file)
            report_libs = report_libs_json_data['libraries']

        # JSON report has sizes for all the libraries and for both O1 and Os
        # Optimizations. Therefore, values for --lib and --optimization are
        # ignored.
        # Compiled objects files for 'O1' optimization needs to be cleaned
        # before 'Os' optimization and therefore, value for --dontclean is
        # ignored.
        for report_lib in report_libs:
            lib_name = report_lib['lib_name']
            size_description = report_lib['size_description']

            o1_sizes = calculate_sizes(args['lts_path'],
                                       'O1',
                                        lib_name,
                                        args['compiler'],
                                        args['sizetool'],
                                        False)

            os_sizes = calculate_sizes(args['lts_path'],
                                       'Os',
                                        lib_name,
                                        args['compiler'],
                                        args['sizetool'],
                                        False)

            update_json_report(lib_name,
                               o1_sizes,
                               os_sizes,
                               size_description,
                               __JSON_REPORT_TEMPLATE__,
                               __GENERATED_JSON_REPORT__)
    else:
        calculate_sizes(args['lts_path'],
                        args['optimization'],
                        args['lib'],
                        args['compiler'],
                        args['sizetool'],
                        args['dontclean'])


if __name__ == '__main__':
    main()