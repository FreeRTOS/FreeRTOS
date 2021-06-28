#!/usr/bin/env python3
import os
import re
import argparse
from collections import defaultdict


_AFR_COMPONENTS = [
    os.path.join('FreeRTOS-Labs','Source','FreeRTOS-IoT-Libraries','abstractions','platform','freertos'),
    os.path.join('FreeRTOS-Labs','Source','FreeRTOS-IoT-Libraries','abstractions','platform','freertos','private','taskpool'),
    os.path.join('FreeRTOS-Labs','Source','FreeRTOS-IoT-Libraries','c_sdk','aws','jobs'),
    os.path.join('FreeRTOS-Labs','Source','FreeRTOS-IoT-Libraries','c_sdk','aws','shadow'),
    os.path.join('FreeRTOS-Labs','Source','FreeRTOS-IoT-Libraries','c_sdk','aws','common'),
    os.path.join('FreeRTOS-Labs','Source','FreeRTOS-IoT-Libraries','c_sdk','standard','common'),
    os.path.join('FreeRTOS-Labs','Source','FreeRTOS-IoT-Libraries','c_sdk','standard','https'),
    os.path.join('FreeRTOS-Labs','Source','FreeRTOS-IoT-Libraries','c_sdk','standard','mqtt'),
    os.path.join('FreeRTOS-Labs','Demo','FreeRTOS_IoT_Libraries'),
    os.path.join('FreeRTOS-Plus','Source','FreeRTOS-Plus-TCP'),
    os.path.join('FreeRTOS-Plus','Source','FreeRTOS-Plus-TCP','portable'),
]

_AFR_EXCLUDE_DIRS = [
    'portable',
    'third_party'
]

_FREERTOS_COMPONENTS = [
    os.path.join('FreeRTOS'),
    os.path.join('FreeRTOS-Plus/Demo'),
    os.path.join('FreeRTOS-Plus/Source'),
    os.path.join('FreeRTOS-Plus/Test')
]
_FREERTOS_VERSION_MACRO_FILE = os.path.join('FreeRTOS', 'Source', 'include', 'task.h')

def ask_question(question):
    answer = input('{}: '.format(question))
    return answer.strip()


def ask_multiple_choice_question(question, choices):
    while True:
        print('{}?'.format(question))
        for i in range(len(choices)):
            print('{}. {}'.format(i, choices[i]))

        try:
            user_choice = int(ask_question('Enter Choice'))
        except ValueError:
            user_choice = None

        if user_choice in range(len(choices)):
            break
        else:
            print('Incorrect choice. Please choose a number between 0 and {}'.format(len(choices) - 1))
    return user_choice


def ask_yes_no_question(question):
    while True:
        answer = ask_question('{} (Y/N)'.format(question))
        if answer.lower() == 'y':
            answer = 'yes'
            break
        elif answer.lower() == 'n':
            answer = 'no'
            break
        else:
            print('Incorrect response. Please answer Y/N.')
    return answer


def list_files_in_a_component(component, afr_path, exclude_dirs=['.git'], ext_filter=['.c', '.h'], exclude_hidden=True):
    '''
    Returns a list of all the files in a component.
    '''
    list_of_files = []
    search_path = os.path.join(afr_path, component)

    for root, dirs, files in os.walk(search_path, topdown=True):
        # Current root is an excluded dir so skip
        if root in exclude_dirs:
            continue

        # Prune excluded dirs
        dirs[:] = [d for d in dirs if d not in exclude_dirs]

        for f in files:
            if exclude_hidden and f[0] == '.':
                continue

            if (ext_filter is None
                or ext_filter is not None and os.path.splitext(f)[-1] in ext_filter):
                    list_of_files.append(os.path.join(os.path.relpath(root, afr_path), f))

    return list_of_files


def extract_version_number_from_file(file_path):
    '''
    Extracts version number from the License header in a file.
    '''
    with open(file_path, encoding='utf-8', errors='ignore') as f:
        content = f.read()
        match = re.search('\s*\*\s*(Amazon FreeRTOS.*V(.*))', content, re.MULTILINE)
        # Is it a kernel file?
        if match is None:
            match = re.search('\s*\*\s*(FreeRTOS Kernel.*V?([0-9]*\.[0-9]*\.[0-9]*|<DEVELOPMENT BRANCH>))', content, re.MULTILINE)
        if match is None:
            match = re.search('\s*\*\s*(FreeRTOS V?([0-9]*\.[0-9]*|<DEVELOPMENT BRANCH>))', content, re.MULTILINE)
        # Is it s FreeRTOS+TCP file?
        if match is None:
            match = re.search('\s*\*\s*(FreeRTOS\+TCP.*V?(.*|<DEVELOPMENT BRANCH>))', content, re.MULTILINE)
        # AWS library from C SDK
        if match is None:
            match = re.search('\s*\*\s*(AWS IoT.*V(.*))', content, re.MULTILINE)
        # IoT library from C SDK
        if match is None:
            match = re.search('\s*\*\s*(IoT.*V(.*))', content, re.MULTILINE)
    return (match.group(1), match.group(2)) if match is not None else (None, None)

def update_version_number_in_files(file_paths, old_version_line, new_version_line):
    '''
    Replaces old_version_line with new_version_line in all the files specified
    by file_paths.
    '''
    for file_path in file_paths:
        with open(file_path, encoding='utf-8', errors='ignore', newline='') as f:
            content = f.read()
            content = content.replace(old_version_line, new_version_line)
        with open(file_path, 'w', newline='') as f:
            f.write(content)

def update_version_number_in_a_component(component, afr_path, exclude_dirs=[]):
    '''
    Updates version numbers in all the files of an AFR component based on user
    choices.
    '''
    # Get all the files in the component.
    files_in_component = list_files_in_a_component(component, afr_path, exclude_dirs)

    version_numbers = defaultdict(list)

    # Extract version numbers from all the files.
    for f in files_in_component:
        file_path = os.path.join(afr_path, f)
        version_number = extract_version_number_from_file(file_path)

        if version_number[0] != None and version_number[1] != None:
            version_numbers[version_number].append(file_path)

    for key in version_numbers.keys():
        v0 = key[0]
        v1 = key[1]
        f = version_numbers[key]
        print('\n{} files have the following version: {}\n'.format(len(f), v0))

        options = [ 'Update version number [i.e. update "{}"].'.format(v1),
                    'Update version line [i.e. update "{}"].'.format(v0),
                    'List files.',
                    'Do not update.' ]

        while True:
            user_selected_option = ask_multiple_choice_question('What do you want to do', options)

            if user_selected_option == 0:
                new_version_number = ask_question('Enter new version number')
                new_version_line = v0.replace(v1, new_version_number)
                print('Old version line: "{}". New version line: "{}".'.format(v0, new_version_line))
                confirm = ask_yes_no_question('Does it look good')
                if confirm == 'yes':
                    update_version_number_in_files(f, v0, new_version_line)
                    print('Updated version line to "{}".\n'.format(new_version_line))
                    break
            elif user_selected_option == 1:
                new_version_line = ask_question('Enter new version line')
                print('Old version line: "{}". New version line: "{}".'.format(v0, new_version_line))
                confirm = ask_yes_no_question('Does it look good')
                if confirm == 'yes':
                    update_version_number_in_files(f, v0, new_version_line)
                    print('Updated version line to "{}".\n'.format(new_version_line))
                    break
            elif user_selected_option == 2:
                for item in f:
                    print(item)
                print('\n')
            else:
                print('Skipping update of {}.\n'.format(v0))
                break

def process_components(root_dir, components, exclude_dirs=[]):
    for c in components:
        print('\n---------------------------------------------')
        print('Component: {}'.format(c))
        print('---------------------------------------------\n')
        wanna_update_version = ask_yes_no_question('Do you want to update the component "{}"'.format(c))
        if wanna_update_version == 'yes':
            update_version_number_in_a_component(c, root_dir, exclude_dirs=exclude_dirs)

def update_freertos_version_macros(path_macrofile, version_str, major, minor, build):
    with open(path_macrofile, encoding='utf-8', errors='ignore', newline='') as macro_file:
        macro_file_content = macro_file.read()
        match_version = re.search(r'(^.*#define *tskKERNEL_VERSION_NUMBER *(".*")$)', macro_file_content, re.MULTILINE)
        match_major = re.search(r'(^.*#define *tskKERNEL_VERSION_MAJOR *(.*)$)', macro_file_content, re.MULTILINE)
        match_minor = re.search(r'(^.*#define *tskKERNEL_VERSION_MINOR *(.*)$)', macro_file_content, re.MULTILINE)
        match_build = re.search(r'(^.*#define *tskKERNEL_VERSION_BUILD *(.*)$)', macro_file_content, re.MULTILINE)

        if match_version.groups() and match_major.groups() and match_minor.groups() and match_build.groups():
            (old_version_string, old_version_number) = match_version.groups()
            new_version_string = old_version_string.replace(old_version_number, '"V%s"' % version_str)
            macro_file_content = macro_file_content.replace(old_version_string, new_version_string)

            (old_major_string, old_major_number) = match_major.groups()
            new_major_string = old_major_string.replace(old_major_number, str(major))
            macro_file_content = macro_file_content.replace(old_major_string, new_major_string)

            (old_minor_string, old_minor_number) = match_minor.groups()
            new_minor_string = old_minor_string.replace(old_minor_number, str(minor))
            macro_file_content = macro_file_content.replace(old_minor_string, new_minor_string)

            (old_build_string, old_build_number) = match_build.groups()
            new_build_string = old_build_string.replace(old_build_number, str(build))
            macro_file_content = macro_file_content.replace(old_build_string, new_build_string)

    with open(path_macrofile, 'w', newline='') as macro_file:
        macro_file.write(macro_file_content)

def update_version_number_in_freertos_component(component, root_dir, old_version_prefix_list, new_version,
                                                verbose=False, exclude_hidden=True):
    assert isinstance(old_version_prefix_list, list), 'Expected a list for arg(old_version_prefix_list)'
    component_files = list_files_in_a_component(component, root_dir, ext_filter=None, exclude_hidden=exclude_hidden)
    version_numbers = defaultdict(list)
    n_updated = 0

    # Extract version numbers from all the files.
    for f in component_files:
        file_path = os.path.join(root_dir, f)
        version_number = extract_version_number_from_file(file_path)

        if version_number[0] != None and version_number[1] != None:
            version_numbers[version_number].append(file_path)

    for vkey in version_numbers.keys():
        old_version_string = vkey[0]
        new_version_string = new_version

        # Check if any of the associated versioning strings are present. Update if so
        for old_prefix in old_version_prefix_list:
            if old_prefix in old_version_string and old_version_string != new_version_string:
                files_using_old_version = version_numbers[vkey]

                if verbose:
                    print('"%s" --> "%s":\n    %s' %
                          (old_version_string,
                           new_version_string,
                           '\n    '.join(files_using_old_version)))

                update_version_number_in_files(files_using_old_version, old_version_string, new_version_string)
                n_updated += len(files_using_old_version)

    return n_updated

def process_freertos_components(root_dir, components, old_version, new_version, verbose=False):
    print('\nUpdating file header version numbers...')
    for c in components:
        print('\n---------------------------------------------')
        print('Component: {}'.format(c))
        print('---------------------------------------------')
        update_version_number_in_freertos_component(c, root_dir, old_version, new_version, verbose)
    print('Done.')

def parse_freertos_version_number(version_str):
    components = version_str.split('.') if version_str else []
    if len(components) == 3:
        return components
    else:
        return (None, None, None)

def configure_arg_parser():
    '''
    Return arg parser, configured for this program
    '''
    parser = argparse.ArgumentParser(description='Updates file headers with new version numbers for AFR or FreeRTOS. '
                                                 'Ideal for preparing upcoming release')
    parser.add_argument('--afr',  metavar='AFR_DIR', default='', help='Location of the AFR Code')
    parser.add_argument('--freertos-dir', metavar='FR_DIR', default='', help='Location of FreeRTOS Code')
    parser.add_argument('--freertos-old-version', metavar='FR_OLD_VERSION', default=None, help='New FreeRTOS version (Ex. "FreeRTOS V202011.00"')
    parser.add_argument('--freertos-new-version', metavar='FR_NEW_VERSION', default=None, help='Previos FreeRTOS version (Ex. "FreeRTOS Kernel V10.3.0"')
    parser.add_argument('--verbose', action='store_true', default=False, help='Increase verbosity of command')

    return parser

def main():
    '''
    Main entry point.
    '''
    parser = configure_arg_parser()
    args = parser.parse_args()

    afr_path = args.afr
    freertos_path = args.freertos_dir

    if afr_path:
        print('AFR Code: {}'.format(afr_path))
        process_components(afr_path, _AFR_COMPONENTS, exclude_dirs=_AFR_EXCLUDE_DIRS)

    if freertos_path:
        # Freertos version is the 'kernel version' string. Since that's a required arg, we replace all kernel version
        # strings with the cmd input, instead of requiring user to input that into every version string match
        print('FreeRTOS Code:\n    %s' % freertos_path)
        print('Old Version:\n    %s' % args.freertos_old_version)
        print('New Version:\n    %s' % args.freertos_new_version)
        process_freertos_components(freertos_path, _FREERTOS_COMPONENTS, args.freertos_old_version.strip(), args.freertos_new_version.strip(), verbose=args.verbose)

    if not afr_path and not freertos_path:
        parser.print_help()

if __name__ == '__main__':
    main()
