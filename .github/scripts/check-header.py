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


def configArgParser():
    parser = ArgumentParser(description='FreeRTOS file header checker. We expect a consistent header across all '
                                        'first party files. The header includes current version number, copyright, '
                                        'and FreeRTOS license.')

    parser.add_argument('files_checked',
                        nargs   = '+',
                        metavar = 'FILE_LIST',
                        help    = 'Space separated list of files to check.')

    parser.add_argument('-k', '--kernel',
                        default = False,
                        action  = 'store_true',
                        help    = 'Compare with kernel file header. It has different versioning.')

    parser.add_argument('-j', '--json',
                        default = False,
                        action  = 'store_true',
                        help    = 'Treat arguments json files that store a list of files to check.')
    return parser

#--------------------------------------------------------------------------------------------------
#                                            CONFIG  
#--------------------------------------------------------------------------------------------------
FREERTOS_IGNORED_EXTENSIONS = [
    '.1',
    '.ASM',
    '.C',
    '.DSW',
    '.G_C',
    '.H',
    '.Hbp',
    '.IDE',
    '.LIB',
    '.Opt',
    '.PC',
    '.PRM',
    '.TXT',
    '.URL',
    '.UVL',
    '.Uv2',
    '.a',
    '.ac',
    '.am',
    '.atsln',
    '.atstart',
    '.atsuo',
    '.bash',
    '.bat',
    '.bbl',
    '.bit',
    '.board',
    '.bsb',
    '.bsdl',
    '.bts',
    '.ccxml',
    '.cdkproj',
    '.cdkws',
    '.cfg',
    '.cgp',
    '.cmake',
    '.cmd',
    '.config',
    '.cpp',
    '.cproj',
    '.crun',
    '.css',
    '.csv',
    '.custom_argvars',
    '.cxx',
    '.cydwr',
    '.cyprj',
    '.cysch',
    '.dat',
    '.datas',
    '.db',
    '.dbgdt',
    '.dep',
    '.dni',
    '.dnx',
    '.doc',
    '.dox',
    '.doxygen',
    '.ds',
    '.dsk',
    '.dtd',
    '.dts',
    '.elf',
    '.env_conf',
    '.ewd',
    '.ewp',
    '.ewt',
    '.eww',
    '.exe',
    '.filters',
    '.flash',
    '.fmt',
    '.ftl',
    '.gdb',
    '.gif',
    '.gise',
    '.gld',
    '.gpdsc',
    '.gui',
    '.h_from_toolchain',
    '.hdf',
    '.hdp',
    '.hex',
    '.hist',
    '.history',
    '.hsf',
    '.htm',
    '.html',
    '.hwc',
    '.hwl',
    '.hwp',
    '.hws',
    '.hzp',
    '.hzs',
    '.i',
    '.icf',
    '.ide',
    '.idx',
    '.in',
    '.inc',
    '.include',
    '.index',
    '.inf',
    '.ini',
    '.init',
    '.ipcf',
    '.ise',
    '.jlink',
    '.json',
    '.la',
    '.launch',
    '.lcf',
    '.lds',
    '.lib',
    '.lk1',
    '.lkr',
    '.lm',
    '.lo',
    '.lock',
    '.lsl',
    '.lst',
    '.m4',
    '.mac',
    '.make',
    '.map',
    '.mbt',
    '.mcp',
    '.mcpar',
    '.mcs',
    '.mcw',
    '.mdm',
    '.mem',
    '.mhs',
    '.mk',
    '.mk1',
    '.mmi',
    '.mrt',
    '.mss',
    '.mtpj',
    '.nav',
    '.ntrc_log',
    '.opa',
    '.opb',
    '.opc',
    '.opl',
    '.opt',
    '.opv',
    '.out',
    '.pack',
    '.par',
    '.patch',
    '.pbd',
    '.pdsc',
    '.pe',
    '.pem',
    '.pgs',
    '.pl',
    '.plg',
    '.png',
    '.prc',
    '.pref',
    '.prefs',
    '.prj',
    '.properties',
    '.ps1',
    '.ptf',
    '.r79',
    '.rapp',
    '.rc',
    '.reggroups',
    '.reglist',
    '.resc',
    '.resources',
    '.rom',
    '.rprj',
    '.s79',
    '.s82',
    '.s90',
    '.sc',
    '.scf',
    '.scfg',
    '.script',
    '.sct',
    '.scvd',
    '.session',
    '.sfr',
    '.sh',
    '.shtml',
    '.sig',
    '.sln',
    '.spec',
    '.stf',
    '.stg',
    '.suo',
    '.sup',
    '.svg',
    '.tags',
    '.tcl',
    '.tdt',
    '.template',
    '.tgt',
    '.tps',
    '.tra',
    '.tree',
    '.tws',
    '.ucf',
    '.url',
    '.user',
    '.ut',
    '.uvmpw',
    '.uvopt',
    '.uvoptx',
    '.uvproj',
    '.uvprojx',
    '.vcproj',
    '.vcxproj',
    '.version',
    '.webserver',
    '.wpj',
    '.wsdt',
    '.wsp',
    '.wspos',
    '.wsx',
    '.x',
    '.xbcd',
    '.xcl',
    '.xise',
    '.xml',
    '.xmp',
    '.xmsgs',
    '.xsl',
    '.yml',
    '.md',
    '.zip'
]

FREERTOS_IGNORED_PATTERNS = [
    r'.*\.git.*',
    r'.*mbedtls_config\.h.*',
    r'.*mbedtls_config\.h.*',
    r'.*CMSIS.*',
    r'.*/makefile',
    r'.*/Makefile',
]

FREERTOS_HEADER = [
    '/*\n',
    ' * FreeRTOS V202011.00\n',
    ' * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.\n',
    ' *\n',
    ' * Permission is hereby granted, free of charge, to any person obtaining a copy of\n',
    ' * this software and associated documentation files (the "Software"), to deal in\n',
    ' * the Software without restriction, including without limitation the rights to\n',
    ' * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of\n',
    ' * the Software, and to permit persons to whom the Software is furnished to do so,\n',
    ' * subject to the following conditions:\n',
    ' *\n',
    ' * The above copyright notice and this permission notice shall be included in all\n',
    ' * copies or substantial portions of the Software.\n',
    ' *\n',
    ' * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR\n',
    ' * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS\n',
    ' * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR\n',
    ' * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER\n',
    ' * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN\n',
    ' * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.\n',
    ' *\n',
    ' * https://www.FreeRTOS.org\n',
    ' * https://github.com/FreeRTOS\n',
    ' *\n',
    ' */\n',
]

KERNEL_IGNORED_EXTENSIONS = [
    '.yml',
    '.css',
    '.idx',
    '.md',
    '.url',
    '.sty',
    '.0-rc2',
    '.s82',
    '.js',
    '.out',
    '.pack',
    '.2',
    '.1-kernel-only',
    '.0-kernel-only',
    '.0-rc1',
    '.readme',
    '.tex',
    '.png',
    '.bat',
    '.sh'
]

KERNEL_IGNORED_PATTERNS = [r'.*\.git.*']

KERNEL_HEADER = [
    '/*\n',
    ' * FreeRTOS Kernel V10.4.2\n',
    ' * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.\n',
    ' *\n',
    ' * Permission is hereby granted, free of charge, to any person obtaining a copy of\n',
    ' * this software and associated documentation files (the "Software"), to deal in\n',
    ' * the Software without restriction, including without limitation the rights to\n',
    ' * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of\n',
    ' * the Software, and to permit persons to whom the Software is furnished to do so,\n',
    ' * subject to the following conditions:\n',
    ' *\n',
    ' * The above copyright notice and this permission notice shall be included in all\n',
    ' * copies or substantial portions of the Software.\n',
    ' *\n',
    ' * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR\n',
    ' * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS\n',
    ' * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR\n',
    ' * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER\n',
    ' * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN\n',
    ' * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.\n',
    ' *\n',
    ' * https://www.FreeRTOS.org\n',
    ' * https://github.com/FreeRTOS\n',
    ' *\n',
    ' */\n',
]


#--------------------------------------------------------------------------------------------------
#                                            MAIN  
#--------------------------------------------------------------------------------------------------
def main():
    parser = configArgParser()
    args = parser.parse_args()

    # Configure checks
    if args.kernel:
        checker = HeaderChecker(KERNEL_HEADER)
        checker.ignoreExtension(*KERNEL_IGNORED_EXTENSIONS)
        checker.ignorePattern(*KERNEL_IGNORED_PATTERNS)
    else:
        checker = HeaderChecker(FREERTOS_HEADER)
        checker.ignoreExtension(*FREERTOS_IGNORED_EXTENSIONS)
        checker.ignorePattern(*FREERTOS_IGNORED_PATTERNS)

    checker.ignoreFile(os.path.split(__file__)[-1])

    # Check all input files
    print()
    n_failed = 0
    for path in args.files_checked:
        if args.json:
            n_failed += checker.checkJSONList(path)
        else:
            n_failed += not checker.isValidFile(path)

    return n_failed

if __name__ == '__main__':
    exit(main())
