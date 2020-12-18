#!/usr/bin/env python3

import os, sys, re
from argparse import ArgumentParser
from difflib import unified_diff
from json import load

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
            n_failed += not self.isValidFile(path_file)

        return n_failed

    def isValidFile(self, path):
        assert os.path.exists(path), 'No such file: ' + path

        # Skip any ignored files
        if self.isIgnoredFile(path):
            return True

        # Skip if entry is a directory.
        if os.path.isdir(path):
            print('Skipping valid file check on directory path: %s' % path)
            return True

        # Don't need entire file. Read sufficienly large chunk of file that should contain the header
        with open(path, encoding='utf-8', errors='ignore') as file:
            chunk = file.read(len(''.join(self.header)) + self.padding)
            lines = [('%s\n' % l) for l in chunk.strip().splitlines()][:len(self.header)]
            if self.header == lines:
                return True
            else:
                print('File Delta: %s' % path)
                print(*unified_diff(lines[:len(self.header)], self.header))
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
