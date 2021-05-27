#!/usr/bin/env python3
# /*
# * FreeRTOS V202104.00
# * Copyright (C) 2021 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
# *
# * Permission is hereby granted, free of charge, to any person obtaining a copy of
# * this software and associated documentation files (the "Software"), to deal in
# * the Software without restriction, including without limitation the rights to
# * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
# * the Software, and to permit persons to whom the Software is furnished to do so,
# * subject to the following conditions:
# *
# * The above copyright notice and this permission notice shall be included in all
# * copies or substantial portions of the Software.
# *
# * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
# * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
# * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
# * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
# * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
# * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
# *
# * https://www.FreeRTOS.org
# * https://github.com/FreeRTOS
# *
# */

import os
import re
from argparse import ArgumentParser
from difflib import unified_diff
from json import load

import requests
from colorama import Fore, Style


def dprint(msg):
    print("[DEBUG]: %s" % str(msg))


class HeaderChecker:
    def separateHeaderIntoSections(self, header):
        """
        Separate header into text, copyright, and spdx sections.
        """
        cur_headers = dict()
        cur_headers["text"] = []
        cur_headers["copyright"] = []
        cur_headers["spdx"] = []
        for line in header:
            if "Copyright" in line:
                cur_headers["copyright"].append(line)
            elif "SPDX-License-Identifier:" in line:
                cur_headers["spdx"].append(line)
            else:
                cur_headers["text"].append(line)
        return cur_headers

    def __init__(
        self,
        header,
        padding=1000,
        ignored_files=None,
        ignored_ext=None,
        ignored_patterns=None,
        py_ext=None,
        asm_ext=None,
        third_party_patterns=None,
    ):
        self.padding = padding
        self.header = header

        # Construct mutated header for assembly files
        self.asm_header = [";" + line for line in header]

        # Construct mutated header for python files
        self.py_header = ["#" + line for line in header]

        self.headers = self.separateHeaderIntoSections(self.header)
        self.headers_asm = self.separateHeaderIntoSections(self.asm_header)
        self.headers_py = self.separateHeaderIntoSections(self.py_header)

        self.ignorePatternList = []
        if ignored_patterns:
            for p in ignored_patterns:
                self.ignorePatternList.append(re.compile(p))

        self.ignoreFileList = ignored_files.copy() if ignored_files else []
        self.ignoreExtList = ignored_ext.copy() if ignored_ext else []
        self.pyExtList = py_ext.copy() if py_ext else []
        self.asmExtList = asm_ext.copy() if asm_ext else []

        self.thirdPartyPatternList = []
        if third_party_patterns:
            for p in third_party_patterns:
                self.thirdPartyPatternList.append(re.compile(p))

        self.spdx_data = None
        self.sdpx_regex = None

    def checkJSONList(self, path_json):
        """
        This is particularly useful when ingesting output from other programs, like git actions
        """
        assert os.path.exists(path_json), "No such file: " + path_json

        # Get list of files to check from JSON file
        with open(path_json) as file_json:
            file_checklist = load(file_json)
            assert isinstance(
                file_checklist, list
            ), "Expected list for singular JSON List entry"

        # Accrue how how files fail the check
        n_failed = 0
        for path_file in file_checklist:
            assert isinstance(path_file, str), "Unexpected JSON format for " + path_json
            if os.path.exists(path_file) and not self.isValidFile(path_file):
                n_failed += 1

        return n_failed

    def isValidHeaderSection(self, file_ext, section_name, section):
        """Validate a given section based on file extentions and section name"""
        valid = False
        if file_ext in self.pyExtList:
            valid = self.headers_py[section_name] == section
        elif file_ext in self.asmExtList:
            valid = self.headers[section_name] == section
            valid |= self.headers_asm[section_name] == section
        else:
            valid = self.headers[section_name] == section

        return valid

    def getHeaderDiff(self, file_ext, header):
        diff = []
        if file_ext in self.pyExtList:
            diff = list(unified_diff(header[: len(self.py_header)], self.py_header))
        elif file_ext in self.asmExtList:
            # For assembly files and headers, calculate diffs between both header types.
            # Return the smallest diff.
            diff_default = list(unified_diff(header[: len(self.header)], self.header))
            diff_asm = list(
                unified_diff(header[: len(self.asm_header)], self.asm_header)
            )
            if len(diff_asm) >= len(diff_default):
                diff = diff_default
            else:
                diff = diff_asm
        else:
            diff = list(unified_diff(header[: len(self.header)], self.header))

        return diff

    def isValidFile(self, path):
        assert os.path.exists(path), "No such file: " + path
        print("-" * 85)

        print("Checking file: %s..." % path, end="")

        file_ext = os.path.splitext(path)[-1]

        if self.isIgnoredFile(path) or os.path.isdir(path):
            print("SKIP")
            print("-" * 85)
            return True

        # Read sufficiently large chunk of the file which should contain the header
        with open(path, encoding="utf-8", errors="ignore") as file:
            chunk = file.read(len("".join(self.header)) + self.padding)
            lines = [("%s\n" % line) for line in chunk.strip().splitlines()][
                : len(self.header)
            ]
            if (len(lines) > 0) and (lines[0].find("#!") == 0):
                lines.remove(lines[0])

            # Split lines in sections:
            header_check = self.separateHeaderIntoSections(lines)

            text_equal = self.isValidHeaderSection(
                file_ext, "text", header_check["text"]
            )
            copyright_equal = self.isValidHeaderSection(
                file_ext, "copyright", header_check["copyright"]
            )
            spdx_equal = self.isValidHeaderSection(
                file_ext, "spdx", header_check["spdx"]
            )

            # Most files should have exactly the same sections
            if text_equal and copyright_equal and spdx_equal:
                print("PASS")
                print("-" * 85)
                return True
            # Third party files may have a different copyright
            elif self.isThirdPartyFile(path) and text_equal and spdx_equal:
                print("PASS")
                print("-" * 85)
                return True
            elif self.isThirdPartyFile(path) and self.validateSpdxLine(
                header_check["spdx"]
            ):
                print("PASS")
                print("-" * 85)
                return True
            elif self.isThirdPartyFile(path):
                print("FAIL")
                print("-" * 85)
                return False
            else:
                print("FAIL")
                print("File Delta: %s" % path)
                print(*self.getHeaderDiff(file_ext, lines))
                print("-" * 85)
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

    def addPyExtension(self, *args):
        for p in args:
            self.pyExtList.append(p)

    def addAsmExtension(self, *args):
        for p in args:
            self.asmExtList.append(p)

    def isIgnoredFile(self, path):
        """
        There are multiple ways a file can be ignored. This is a catch all
        """
        assert os.path.exists(path), "No such file: " + path

        # Try simpler checks first
        filename = os.path.split(path)[-1]
        extension = os.path.splitext(filename)[-1]
        if extension in self.ignoreExtList or filename in self.ignoreFileList:
            return True

        # Then iterate against regex patterns. In future consider Trie
        for pattern in self.ignorePatternList:
            # print(pattern)
            if pattern.match(path):
                return True

        # print("DEBUG: did not match any regex")

        return False

    def isThirdPartyFile(self, path):
        # Tterate against regex patterns
        for pattern in self.thirdPartyPatternList:
            if pattern.match(path):
                return True
        return False

    def showHelp(self, path_config):
        print(Fore.YELLOW)
        print(
            "\n\n \
            *************************************************************************************************\n\
            *                                FreeRTOS Header Check %s(FAILED)%s                                 *\n\
            *************************************************************************************************\n\
            *                                                                                               *\n\
            * %sWe do NOT require that all files contain the FreeRTOS File Header (copyright + license).%s      *\n\
            * While some files in this change-set don't adhere with the FreeRTOS File Header,               *\n\
            * they can be omitted from this check as needed.                                                *\n\
            *                                                                                               *\n\
            * The Git PR check sources its scripts from your fork.                                          *\n\
            * For FreeRTOS/FreeRTOS, ignored files are listed in '.github/scripts/core_checker.py'          *\n\
            * For FreeRTOS/FreeRTOS-Kernel, ignored files are listed in '.github/scripts/kernel_checker.py' *\n\
            *                                                                                               *\n\
            * Please fix any offending files that should have the FreeRTOS header,                          *\n\
            * or add new files to the ignore list as needed to make the check pass.                         *\n\
            *                                                                                               *\n\
            * %sInclude the required updates to the '*_checker.py' script in your PR to make the check pass.%s  *\n\
            *************************************************************************************************\n\
            \n\n"  # noqa: B950
            % (Fore.RED, Fore.YELLOW, Fore.RED, Fore.YELLOW, Fore.RED, Fore.YELLOW)
        )
        print(Style.RESET_ALL)

    @staticmethod
    def configArgParser():
        parser = ArgumentParser(
            description="FreeRTOS file header checker. We expect a consistent header across all "
            "first party files. The header includes current version number, copyright, "
            "and FreeRTOS license."
        )

        parser.add_argument(
            "files_checked",
            nargs="+",
            metavar="FILE_LIST",
            help="Space separated list of files to check.",
        )

        parser.add_argument(
            "-j",
            "--json",
            default=False,
            action="store_true",
            help="Treat arguments json files that store a list of files to check.",
        )
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

    def loadSpdxData(self):
        """Load spdx license and license exception information from github."""
        spdx_data = dict()
        spdx_url = "https://raw.githubusercontent.com/spdx/license-list-data/"

        licenses_url = spdx_url + "master/json/licenses.json"
        licenses = requests.get(licenses_url).json()

        assert "licenses" in licenses
        spdx_data["licenses"] = dict()

        for license in licenses["licenses"]:
            spdx_data["licenses"][license["licenseId"]] = True

        exceptions_url = spdx_url + "master/json/exceptions.json"
        exceptions = requests.get(exceptions_url).json()

        assert "exceptions" in exceptions

        spdx_data["exceptions"] = dict()

        for exception in exceptions["exceptions"]:
            spdx_data["exceptions"][exception["licenseExceptionId"]] = True
        self.spdx_data = spdx_data

    def validateSpdxTag(self, tag):
        """
        Validate a given SPDX license tag against SPDX data from github
        """

        error_count = 0
        licenses = tag.split(" ")
        license_exception_flag = False
        paren_depth = 0
        last_paren_depth = 0
        for i in range(0, len(licenses)):
            if licenses[i][0] == "(":
                paren_depth += 1
            # skip "and" "or" keywords
            if licenses[i] in ["and", "AND", "or", "OR"]:
                pass
            # "with" keyword denotes a license exception
            elif licenses[i] in ["with", "WITH"]:
                # Set flag for next iteration
                license_exception_flag = True
            elif license_exception_flag:
                if not licenses[i].strip("()") in self.spdx_data["exceptions"]:
                    dprint(
                        "Invalid license exception id {} in SPDX tag {}".format(
                            licenses[i], tag
                        )
                    )
                    error_count += 1
                # No '(' character -> single license exception
                if paren_depth <= last_paren_depth:
                    license_exception_flag = False
            else:
                if not licenses[i].strip("()") in self.spdx_data["licenses"]:
                    dprint(
                        'Invalid license id "{}" in SPDX tag "{}"'.format(
                            licenses[i], tag
                        )
                    )
                    error_count += 1

            last_paren_depth = paren_depth
            if licenses[i][-1] == ")":
                paren_depth -= 1

        return error_count

    def validateSpdxLine(self, lines):
        """
        Validate an SPDX license data line from a source file.
        Like: /* SPDX-License-Identifier: MIT */
        """

        if len(lines) == 0:
            dprint("No SPDX identifier found.")
            return False

        if not self.spdx_data:
            self.loadSpdxData()

        if not self.sdpx_regex:
            self.spdx_regex = re.compile(
                r"^.*SPDX-License-Identifier:\s*(?P<tag>.*)\s*$"
            )

        error_count = 0

        for line in lines:
            matches = self.spdx_regex.match(line)
            if "tag" in matches.groupdict():
                error_count += self.validateSpdxTag(matches.group("tag"))
            else:
                error_count += 1
        return error_count == 0
