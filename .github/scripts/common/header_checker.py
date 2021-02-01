#!/usr/bin/env python3

import os, sys, re
from argparse import ArgumentParser
from difflib import unified_diff
from json import load
from colorama import Fore, Style

def dprint(msg):
    print('[DEBUG]: %s' % str(msg))

class HeaderChecker:
    def __init__(self, header, padding=1000, ignored_files=[], ignored_ext=[], ignored_patterns=[]):
        self.padding = padding
        self.header = header

        self.ignorePatternList = ignored_patterns.copy()
        self.ignoreFileList = ignored_files.copy()
        self.ignoreExtList = ignored_ext.copy()

    def checkJSONList(self, path_json):
        '''
        This is particularly useful when ingesting output from other programs, like git actions
        '''
        assert os.path.exists(path_json), 'No such file: ' + path_json

        # Get list of files to check from JSON file
        with open(path_json) as file_json:
            file_checklist = load(file_json)
            assert isinstance(file_checklist, list), 'Expected list for singular JSON List entry'

        # Accrue how how files fail the check
        n_failed = 0
        for path_file in file_checklist:
            assert isinstance(path_file, str), 'Unexpected JSON format for ' + path_json
            if os.path.exists(path_file) and not self.isValidFile(path_file):
                n_failed += 1

        return n_failed

    def isValidFile(self, path):
        assert os.path.exists(path), 'No such file: ' + path
        print('-------------------------------------------------------------------------------------')

        print('Checking file: %s...' % path, end='')

        if self.isIgnoredFile(path) or os.path.isdir(path):
            print('SKIP')
            print('-------------------------------------------------------------------------------------')
            return True

        # Don't need entire file. Read sufficiently large chunk of file that should contain the header
        with open(path, encoding='utf-8', errors='ignore') as file:
            chunk = file.read(len(''.join(self.header)) + self.padding)
            lines = [('%s\n' % l) for l in chunk.strip().splitlines()][:len(self.header)]
            if self.header == lines:
                print('PASS')
                print('-------------------------------------------------------------------------------------')
                return True
            else:
                print('FAIL')
                print('File Delta: %s' % path)
                print(*unified_diff(lines[:len(self.header)], self.header))
                print('-------------------------------------------------------------------------------------')
                return False

    def ignoreExtension(self, *args):
        for ext in args:
            self.ignoreExtList.append(ext)

    def ignoreFile(self, *args):
        for f in args:
            self.ignoreFileList.append(f)

    def ignorePattern(self, *args):
        for p in args:
            self.ignorePatternList.append(re.compile(p))

    def isIgnoredFile(self, path):
        '''
        There are multiple ways a file can be ignored. This is a catch all
        '''
        assert os.path.exists(path), 'No such file: ' + path


        # Try simpler checks first
        filename  = os.path.split(path)[-1]
        extension = os.path.splitext(filename)[-1]
        if extension in self.ignoreExtList or filename in self.ignoreFileList:
            return True

        # Then iterate against regex patterns. In future consider Trie
        for pattern in self.ignorePatternList:
            if pattern.match(path):
                return True

        return False

    def showHelp(self, path_config):
        print(Fore.YELLOW)
        print(
              "\n\n"
              "*************************************************************************************************\n"
              "*                                FreeRTOS Header Check %s(FAILED)%s                                 *\n"
              "*************************************************************************************************\n"
              "*                                                                                               *\n" 
              "* %sWe do NOT require that all files contain the FreeRTOS File Header (copyright + license).%s      *\n"
              "* While some files in this change-set don't adhere with the FreeRTOS File Header,               *\n"
              "* they can be omitted from this check as needed.                                                *\n"
              "*                                                                                               *\n" 
              "* The Git PR check sources its scripts from your fork.                                          *\n"
              "* For FreeRTOS/FreeRTOS, ignored files are listed in '.github/scripts/core_checker.py'          *\n"
              "* For FreeRTOS/FreeRTOS-Kernel, ignored files are listed in '.github/scripts/kernel_checker.py' *\n"
              "*                                                                                               *\n"
              "* Please fix any offending files that should have the FreeRTOS header,                          *\n"
              "* or add new files to the ignore list as needed to make the check pass.                         *\n"
              "*                                                                                               *\n"
              "* %sInclude the required updates to the '*_checker.py' script in your PR to make the check pass.%s  *\n"
              "*************************************************************************************************\n"
              "\n\n"
              % (Fore.RED, Fore.YELLOW,
                 Fore.RED, Fore.YELLOW,
                 Fore.RED, Fore.YELLOW)
              )
        print(Style.RESET_ALL)

    @staticmethod
    def configArgParser():
        parser = ArgumentParser(description='FreeRTOS file header checker. We expect a consistent header across all '
                                            'first party files. The header includes current version number, copyright, '
                                            'and FreeRTOS license.')

        parser.add_argument('files_checked',
                            nargs   = '+',
                            metavar = 'FILE_LIST',
                            help    = 'Space separated list of files to check.')

        parser.add_argument('-j', '--json',
                            default = False,
                            action  = 'store_true',
                            help    = 'Treat arguments json files that store a list of files to check.')
        return parser

    def processArgs(self, args):
        n_failed = 0
        if args.json:
            for path in args.files_checked:
                n_failed += self.checkJSONList(path)
        else:
            for path in args.files_checked:
                n_failed += not self.isValidFile(path)

        return n_failed
