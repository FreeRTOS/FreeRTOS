#!/usr/bin/python

import os.path
import re
import subprocess
import sys
import tempfile
import argparse

def main(): # pragma: no cover
    args = parse_args()

    if args['uncrustify_all_files']:
        file_names = get_all_files()
        files_to_check = filter_checkable_files(file_names)
        check_uncrustify(files_to_check, uncrustify=True)
    elif args['uncrustify']:
        file_names = args['files']
        if not file_names:
            file_names = get_modified_files()

        files_to_check = filter_checkable_files(file_names)
        check_uncrustify(files_to_check, uncrustify=True)
    else:
        failed_files = commit_is_ready(args['files'])
        if failed_files:
            print("\nYou may run the following command to repeat the check: python tools/git/hooks/src/pre_commit.py")
            print("\nYou may run the following command to uncrustify staged files: python tools/git/hooks/src/pre_commit.py --uncrustify")
            print("\nYou may run the following command to uncrustify a list of files: python tools/git/hooks/src/pre_commit.py --uncrustify <files>")
            print("\nYou may run the following command to uncrustify all files: python tools/git/hooks/src/pre_commit.py --uncrustify-all-files")
            print("Hint: You may need to be at the repository's root directory.")
            print('Aborting Commit.')
            sys.exit(1)
    sys.exit(0)


def parse_args():
    parser = argparse.ArgumentParser(description='pre-commit checks')

    parser.add_argument('--uncrustify', default = False, action='store_true', help='Uncrustify modified files.')
    parser.add_argument('--uncrustify-all-files', default = False, action='store_true', help='Uncrustify all files.')
    parser.add_argument('files', nargs='*', help='List of files to check.')

    args = parser.parse_args()
    return vars(args)


def commit_is_ready(file_names=None):
    """Return False if not ready.  Return True if commit is ready"""
    if not file_names:
        file_names = get_modified_files()

    files_to_check = filter_checkable_files(file_names)

    checks = [
        check_secrets,
        check_uncrustify,
        check_whitespace,
    ]

    # If there is no file to check, return. This can happen if all the modified
    # files are ignored as defined in is_ignored_file_pattern.
    if files_to_check:
        for check in checks:
            failed_files = check(files_to_check)
            if failed_files:
                return failed_files
    return []


def filter_checkable_files(file_names):
    files_to_check = [f for f in file_names if file_exists(f) and file_is_checkable(f)]
    return files_to_check


def get_all_files():
    file_names = []
    for root, dirs, files in os.walk("."):
        for f in files:
            file_names.append(os.path.join(root, f))
    return file_names


def get_modified_files():
    changed_files = subprocess.check_output(
        "git diff-index --name-only --cached HEAD", shell=True)
    if type(changed_files) is not str:
        changed_files = changed_files.decode('utf-8')
    file_names = changed_files.split('\n')
    return file_names


def file_is_checkable(file_name):
    return (
        is_source_file(file_name)
        and is_checked_file_pattern(file_name)
        and not is_ignored_file_pattern(file_name)
    )


def file_exists(file_name):
    return os.path.isfile(file_name)


def is_source_file(file_name):
    if re.findall(r'\.[ch]$', file_name):
        return True
    return False


def is_checked_file_pattern(file_name):
    checked_patterns = [
        r"FreeRTOS-Plus/",
    ]
    for checked_pattern in checked_patterns:
        if re.findall(checked_pattern, file_name):
            return True
    return False


def is_ignored_file_pattern(file_name):
    ignored_patterns = [
        "FreeRTOS-Plus/Source/FreeRTOS-Plus-TCP",
        "FreeRTOS-Plus/Source/http-parser",
        "FreeRTOS-Plus/Source/jsmn",
        "FreeRTOS-Plus/Source/mbedtls",
        "FreeRTOS-Plus/Source/mbedtls-utils",
        "FreeRTOS-Plus/Source/pkcs11",
        "FreeRTOS-Plus/Source/tinycbor",
        "FreeRTOS-Plus/Source/FreeRTOS-Plus-Trace",
        "FreeRTOS-Plus/Demo/FreeRTOS_IoT_Libraries/https/common/WinPCap",
        "FreeRTOS-Plus/Demo/FreeRTOS_IoT_Libraries/jobs/jobs_notify_next/WinPCap",
        "FreeRTOS-Plus/Demo/FreeRTOS_IoT_Libraries/pkcs11/pkcs11_mqtt_tls_mutual_auth/WinPCap",
        "FreeRTOS-Plus/Demo/FreeRTOS_IoT_Libraries/mqtt/common/WinPCap",
        "FreeRTOS-Plus/Demo/FreeRTOS_IoT_Libraries/shadow/shadow_device_operations/WinPCap",
        "FreeRTOS-Plus/Demo/FreeRTOS_IoT_Libraries/ota/common/WinPCap",
        "FreeRTOS-Plus/Demo/FreeRTOS-IoT-Libraries-LTS-Beta1/https/common/WinPCap",
        "FreeRTOS-Plus/Demo/FreeRTOS-IoT-Libraries-LTS-Beta1/jobs/jobs_notify_next/WinPCap",
        "FreeRTOS-Plus/Demo/FreeRTOS-IoT-Libraries-LTS-Beta1/pkcs11/pkcs11_mqtt_tls_mutual_auth/WinPCap",
        "FreeRTOS-Plus/Demo/FreeRTOS-IoT-Libraries-LTS-Beta1/mqtt/common/WinPCap",
        "FreeRTOS-Plus/Demo/FreeRTOS-IoT-Libraries-LTS-Beta1/shadow/shadow_device_operations/WinPCap",
        "FreeRTOS-Plus/Demo/FreeRTOS-IoT-Libraries-LTS-Beta1/ota/common/WinPCap",
        "FreeRTOS-Plus/Demo/FreeRTOS-IoT-Libraries-LTS-Beta2/mqtt/common/WinPCap",
        "tools",
    ]
    for ignored_pattern in ignored_patterns:
        if re.findall(ignored_pattern, file_name):
            return True
    return False


def check_secrets(changed_files):
    if not changed_files:
        return []
    if subprocess.call("git secrets --scan " + " ".join(changed_files), shell=True):
        return ['git_secrets']
    return []


def check_whitespace(changed_files):
    """Return True if check failed.  Return False if check passed"""
    if subprocess.call("git diff-index --check --cached HEAD", shell=True):
        return ['whitespace']
    return []

def check_uncrustify(changed_files, uncrustify=False):
    """Return True if check failed.  Return False if check passed"""
    if "" == changed_files:
        return False
    failed_files = []
    for changed_file in changed_files:
        if subprocess.call(
            (
                "uncrustify --check -q -c tools/uncrustify.cfg " +
                changed_file
            ), shell=True
        ):
            failed_files.append(changed_file)

    if failed_files and uncrustify:
        run_uncrustify(changed_files)

    return failed_files


def run_uncrustify(changed_files):
    """Run uncrustify to fix formatting in a set of files"""
    for file in changed_files:
        format_call = ( 'uncrustify -q -c tools/uncrustify.cfg -f {} -o {}'.format(file, file) )
        subprocess.check_output(format_call, shell=True)


if __name__ == "__main__":  # pragma: no cover
    main()

