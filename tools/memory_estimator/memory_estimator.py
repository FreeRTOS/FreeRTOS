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

__LIB_DETAILS_JSON__ = os.path.join(__THIS_FILE_PATH__, 'template', 'lib_details.json')

__JSON_REPORT_TEMPLATE__ = os.path.join(__THIS_FILE_PATH__, 'template', 'report.json.template')
__GENERATED_JSON_REPORT__ = os.path.join(__THIS_FILE_PATH__, 'freertos_lts_memory_estimates.json')


def get_lib_src_and_include(lib_name, src_path):
    with open(__LIB_DETAILS_JSON__) as lib_details_file:
        lib_details_data = json.load(lib_details_file)
        if lib_name not in lib_details_data:
            raise ValueError('Library name: {} is not in lib_details.json'.format(lib_name))
        else:
            lib_details = lib_details_data[lib_name]

    src_files = []
    include_dirs = []
    compiler_flags = []

    for entry in lib_details['src']:
        entry_full_path = os.path.join(src_path, entry)
        if os.path.isdir(entry_full_path):
            for root, dirs, files in os.walk(entry_full_path):
                for file in files:
                    if file.endswith('.c'):
                        src_files.append(os.path.join(root, file))
        else:
            src_files.append(entry_full_path)

    for entry in lib_details['include']:
        include_dirs.append(os.path.join(src_path, entry))

    if 'compiler_flags' in lib_details:
        compiler_flags = lib_details['compiler_flags']

    return src_files, include_dirs, compiler_flags


def get_lib_size_description(lib_name):
    size_description = ''
    with open(__LIB_DETAILS_JSON__) as lib_details_file:
        lib_details_data = json.load(lib_details_file)
        if lib_name not in lib_details_data:
            raise ValueError('Library name: {} is not in lib_details.json'.format(lib_name))
        else:
            size_description = lib_details_data[lib_name]['size_description']
    return size_description


def generate_makefile(lib_name, src_path, optimization, disable_asserts):
    src_files, include_dirs, compiler_flags = get_lib_src_and_include(lib_name, src_path)

    # Add config files dir to include dirs list.
    include_dirs.append(os.path.join(__THIS_FILE_PATH__, 'config_files'))

    # Generate makefile.
    generate_makefile_from_template(src_files,
                                    include_dirs,
                                    optimization,
                                    disable_asserts,
                                    compiler_flags,
                                    __MAKE_FILE_TEMPLATE__,
                                    __GENERATED_MAKE_FILE__)


def make():
    compiler_command='CC={}'.format('arm-none-eabi-gcc')

    print('---- Starting Build. ---- \n')

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


def calculate_size():
    sizetool_command='SIZETOOL={}'.format('arm-none-eabi-size')

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


def calculate_sizes(lib_name, src_path, optimization, disable_asserts, dontclean):
    if not os.path.isabs(src_path):
        cur_dir = os.getcwd()
        resolved_src_path = os.path.join(cur_dir, src_path)
    else:
        resolved_src_path = src_path

    if not os.path.exists(resolved_src_path):
        raise ValueError('Incorrect source path: {}'.format(src_path))

    # Generate Makefile.
    generate_makefile(lib_name, resolved_src_path, optimization, disable_asserts)

    # Run make build.
    warnings = make()

    # Run make size.
    calculated_sizes = calculate_size()

    # Remove the generated artifacts.
    if not dontclean:
        clean()
        remove_generated_makefile()

    # Print the generated warnings.
    pretty_print_warnings(warnings)

    # Print the calculated sizes.
    pretty_print_sizes(calculated_sizes)

    return calculated_sizes


def parse_arguments():
    parser = argparse.ArgumentParser(description='Memory Estimator.')

    parser.add_argument('-p', '--path', required=True, help='Path to the source code for the library.')
    parser.add_argument('-l', '--lib', required=True, help='Library name to generate the memory estimate for.')
    parser.add_argument('-o', '--optimization', default='O0', help='Compiler optimization (O0, Os etc.).')
    parser.add_argument('-a', '--disableasserts', action='store_true', help='Disable asserts in the code.')
    parser.add_argument('-d', '--dontclean', action='store_true', help='Do not clean the generated artifacts.')
    parser.add_argument('-g', '--generate-report', action='store_true', help='Generate the JSON report.')

    return vars(parser.parse_args())


def main():
    args = parse_arguments()

    if args['generate_report']:
        # Start with an empty JSON report.
        generated_json_report = {}

        # Load an existing report, if any.
        if os.path.exists(__GENERATED_JSON_REPORT__):
            with open(__GENERATED_JSON_REPORT__) as generated_json_report_file:
                generated_json_report = json.load( generated_json_report_file)

        # Read the template to obtain the library report format.
        with open(__JSON_REPORT_TEMPLATE__) as json_report_template_file:
            json_report_template_data = json.load(json_report_template_file)
        report_template = json_report_template_data['lib']

        # Compiled objects files for 'O1' optimization needs to be cleaned
        # before 'Os' optimization and therefore, value for --dontclean is
        # ignored.
        lib_name = args['lib']
        size_description = get_lib_size_description(lib_name)

        o1_sizes = calculate_sizes(lib_name,
                                   args['path'],
                                   'O1',
                                   True, #Disable Asserts.
                                   False)

        os_sizes = calculate_sizes(lib_name,
                                   args['path'],
                                   'Os',
                                   True, #Disable Asserts.
                                   False)

        update_json_report(lib_name,
                            o1_sizes,
                            os_sizes,
                            size_description,
                            report_template,
                            generated_json_report)

        # Write the generated report to the output file.
        with open(__GENERATED_JSON_REPORT__, 'w') as generated_json_report_file:
            generated_json_report_file.write(json.dumps(generated_json_report, indent=4, sort_keys=True))
    else:
        calculate_sizes(args['lib'],
                        args['path'],
                        args['optimization'],
                        args['disableasserts'],
                        args['dontclean'])


if __name__ == '__main__':
    main()
