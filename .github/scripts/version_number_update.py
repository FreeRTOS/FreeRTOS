import os
import re
import argparse
from collections import defaultdict


_AFR_COMPONENTS = [
    'demos',
    'freertos_kernel',
    os.path.join('libraries','abstractions','ble_hal'),
    os.path.join('libraries','abstractions','common_io'),
    os.path.join('libraries','abstractions','pkcs11'),
    os.path.join('libraries','abstractions','platform'),
    os.path.join('libraries','abstractions','posix'),
    os.path.join('libraries','abstractions','secure_sockets'),
    os.path.join('libraries','abstractions','wifi'),
    os.path.join('libraries','c_sdk','aws','defender'),
    os.path.join('libraries','c_sdk','aws','shadow'),
    os.path.join('libraries','c_sdk','standard','ble'),
    os.path.join('libraries','c_sdk','standard','common'),
    os.path.join('libraries','c_sdk','standard','https'),
    os.path.join('libraries','c_sdk','standard','mqtt'),
    os.path.join('libraries','c_sdk','standard','serializer'),
    os.path.join('libraries','freertos_plus','aws','greengrass'),
    os.path.join('libraries','freertos_plus','aws','ota'),
    os.path.join('libraries','freertos_plus','standard','crypto'),
    os.path.join('libraries','freertos_plus','standard','freertos_plus_posix'),
    os.path.join('libraries','freertos_plus','standard','freertos_plus_tcp'),
    os.path.join('libraries','freertos_plus','standard','pkcs11'),
    os.path.join('libraries','freertos_plus','standard','tls'),
    os.path.join('libraries','freertos_plus','standard','utils'),
    'tests'
]


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
            print('Incorrect choice. Please choose a number between 0 and {}'.format(len(choices) - 1))
            continue
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


def print_file_list(file_list):
    version_line_list = []

    for file in file_list:
        version_number = extract_version_number_from_file(file)
        version_line_list.append(version_number[0] if version_number[0] is not None else 'Could not detect version')

    max_filepath_length = len(max(file_list, key=len))
    max_version_line_length = len(max(version_line_list, key=len))

    print('-' * (max_filepath_length + max_version_line_length + 7))
    print('| {file:<{max_filepath_length}} | {version:<{max_version_line_length}} |'.format(file='File',
                                                                                            max_filepath_length=max_filepath_length,
                                                                                            version='Version Line',
                                                                                            max_version_line_length=max_version_line_length))
    print('-' * (max_filepath_length + max_version_line_length + 7))
    for i in range(len(file_list)):
        print('| {file:<{max_filepath_length}} | {version:<{max_version_line_length}} |'.format(file=file_list[i],
                                                                                                max_filepath_length=max_filepath_length,
                                                                                                version=version_line_list[i],
                                                                                                max_version_line_length=max_version_line_length))

    print('-' * (max_filepath_length + max_version_line_length + 7))
    print('\n')


def list_files_in_a_component(component, afr_path):
    '''
    Returns a list of all the files in a component.
    '''
    list_of_files = []
    search_path = os.path.join(afr_path, component)

    for root, dirs, files in os.walk(search_path, topdown=True):
        # Do not search 'portable' and 'third_party' folders.
        dirs[:] = [d for d in dirs if d not in ['portable', 'third_party']]

        # Do not include hidden files and folders.
        dirs[:] = [d for d in dirs if not d[0] == '.']
        files = [f for f in files if not f[0] == '.']

        for f in files:
            if f.endswith('.c') or f.endswith('.h'):
                list_of_files.append(os.path.join(os.path.relpath(root, afr_path), f))

    return list_of_files


def extract_version_number_from_file(file_path):
    '''
    Extracts version number from the License header in a file.
    '''
    with open(file_path) as f:
        content = f.read()
        match = re.search('\s*\*\s*(FreeRTOS.*V(.*))', content, re.MULTILINE)
        # Is it a kernel file?
        if match is None:
            match = re.search('\s*\*\s*(FreeRTOS Kernel.*V(.*))', content, re.MULTILINE)
        # Is it s FreeRTOS+TCP file?
        if match is None:
            match = re.search('\s*\*\s*(FreeRTOS\+TCP.*V(.*))', content, re.MULTILINE)
    return (match.group(1), match.group(2)) if match is not None else (None, None)


def update_version_number_in_files(file_paths, old_version_line, new_version_line):
    '''
    Replaces old_version_line with new_version_line in all the files specified
    by file_paths.
    '''
    for file_path in file_paths:
        with open(file_path) as f:
            content = f.read()
            content = content.replace(old_version_line, new_version_line)
        with open(file_path, 'w') as f:
            f.write(content)


def update_version_number_in_a_component(component, afr_path):
    '''
    Updates version numbers in all the files of an AFR component based on user
    choices.
    '''
    # Get all the files in the component.
    files_in_component = list_files_in_a_component(component, afr_path)

    version_numbers = defaultdict(list)

    # Extract version numbers from all the files.
    for f in files_in_component:
        file_path = os.path.join(afr_path, f)
        version_number = extract_version_number_from_file(file_path)
        version_numbers[version_number].append(file_path)

    for key in version_numbers.keys():
        old_version_line = key[0]
        old_version_number = key[1]
        files_to_update = version_numbers[key]

        if old_version_line is None:
            print('\nFailed to detect the version number in the following files:')
            while True:
                print_file_list(files_to_update)
                print('Please update the above files manually!')
                confirm = ask_yes_no_question('Done updating')
                if confirm == 'yes':
                    print_file_list(files_to_update)
                    looks_good = ask_yes_no_question('Does it look good')
                    if looks_good == 'yes':
                        break
        else:
            print('\n{} files have the following version: {}\n'.format(len(files_to_update), old_version_line))

            options = [ 'Update version number [i.e. update "{}"].'.format(old_version_number),
                        'Update version line [i.e. update "{}"].'.format(old_version_line),
                        'List files.',
                        'Do not update.' ]

            while True:
                user_selected_option = ask_multiple_choice_question('What do you want to do', options)

                if user_selected_option == 0:
                    new_version_number = ask_question('Enter new version number')
                    new_version_line = old_version_line.replace(old_version_number, new_version_number)
                    print('Old version line: "{}". New version line: "{}".'.format(old_version_line, new_version_line))
                    confirm = ask_yes_no_question('Does it look good')
                    if confirm == 'yes':
                        update_version_number_in_files(files_to_update, old_version_line, new_version_line)
                        print('Updated version line to "{}".\n'.format(new_version_line))
                        break
                elif user_selected_option == 1:
                    new_version_line = ask_question('Enter new version line')
                    print('Old version line: "{}". New version line: "{}".'.format(old_version_line, new_version_line))
                    confirm = ask_yes_no_question('Does it look good')
                    if confirm == 'yes':
                        update_version_number_in_files(files_to_update, old_version_line, new_version_line)
                        print('Updated version line to "{}".\n'.format(new_version_line))
                        break
                elif user_selected_option == 2:
                    print_file_list(files_to_update)
                else:
                    print('Skipping update of {}.\n'.format(old_version_line))
                    break


def parse_arguments():
    '''
    Parses the command line arguments.
    '''
    parser = argparse.ArgumentParser(description='FreeRTOS Checksum Generator')
    parser.add_argument('--afr', required=True, help='Location of the AFR Code.')
    args = parser.parse_args()
    return vars(args)


def main():
    '''
    Main entry point.
    '''
    args = parse_arguments()

    afr_path = args['afr']

    print('AFR Code: {}'.format(afr_path))

    for component in _AFR_COMPONENTS:
        print('\n---------------------------------------------')
        print('Component: {}'.format(component))
        print('---------------------------------------------\n')
        wanna_update_version = ask_yes_no_question('Do you want to update the component "{}"'.format(component))
        if wanna_update_version == 'yes':
            update_version_number_in_a_component(component, afr_path)


if __name__ == '__main__':
    main()
