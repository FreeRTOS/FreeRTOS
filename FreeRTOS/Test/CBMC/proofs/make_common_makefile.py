#!/usr/bin/env python3
#
# Generation of common Makefile for CBMC proofs.
#
# Copyright (C) 2020 Amazon.com, Inc. or its affiliates. All Rights Reserved.
#
# Permission is hereby granted, free of charge, to any person obtaining a copy
# of this software and associated documentation files (the "Software"), to deal
# in the Software without restriction, including without limitation the rights
# to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
# copies of the Software, and to permit persons to whom the Software is
# furnished to do so, subject to the following conditions:
#
# The above copyright notice and this permission notice shall be included in all
# copies or substantial portions of the Software.
#
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
# IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
# FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.  IN NO EVENT SHALL THE
# AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
# LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
# OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
# SOFTWARE.

from pprint import pprint
import json
import sys
import re
import os
import argparse

def cleanup_whitespace(string):
    return re.sub('\s+', ' ', string.strip())

################################################################
# Operating system specific values

platform_definitions = {
    "linux": {
        "platform": "linux",
        "separator": "/",
        "define": "-D",
        "include": "-I",
    },
    "macos": {
        "platform": "darwin",
        "separator": "/",
        "define": "-D",
        "include": "-I",
    },
    "windows": {
        "platform": "win32",
        "separator": "\\",
        "define": "/D",
        "include": "/I",
    },
}


def default_platform():
    for platform, definition in platform_definitions.items():
        if sys.platform == definition["platform"]:
            return platform
    return "linux"


def patch_path_separator(opsys, string):
    from_separator = '/'
    to_separator = platform_definitions[opsys]["separator"]

    def escape_separator(string):
        return string.split(from_separator + from_separator)

    def change_separator(string):
        return string.replace(from_separator, to_separator)

    return from_separator.join([change_separator(escaped)
                                for escaped in escape_separator(string)])

def patch_compile_output(opsys, line, key, value):
    if opsys != "windows":
        return line

    if key in ["COMPILE_ONLY", "COMPILE_LINK"] and value is not None:
        if value[-1] == '/Fo':
            return re.sub('/Fo\s+', '/Fo', line)
        if value[-1] == '/Fe':
            return re.sub('/Fe\s+', '/Fe', line)
    return line

################################################################
# Argument parsing
#

def get_arguments():
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--system",
        metavar="OS",
        choices=platform_definitions,
        default=str(default_platform()),
        help="Generate makefiles for operating system OS"
    )
    return parser.parse_args()

################################################################
# Variable definitions
#
# JSON files give variable definitions for common, operating system,
# and harness specific values
#

def read_variable_definitions(filename):
    variable = {}
    with open(filename) as _file:
        for key, values in json.load(_file).items():
            variable[cleanup_whitespace(key)] = [cleanup_whitespace(value)
                                                 for value in values]
    return variable

def find_definition_once(key, defines, prefix=None):

    # Try looking up key with and without prefix
    prefix = "{}_".format(prefix.rstrip('_')) if prefix else ""
    key2 = key[len(prefix):] if key.startswith(prefix) else prefix + key

    for _key in [key, key2]:
        _value = defines.get(_key)
        if _value is not None:
            return _value

    return None

def find_definition(key, defines):
    common_defines, opsys_defines, harness_defines = defines
    return (find_definition_once(key, harness_defines, "H") or
            find_definition_once(key, opsys_defines, "O") or
            find_definition_once(key, common_defines, "C"))

################################################################
# Makefile generation

def construct_definition(opsys, key_prefix, value_prefix, key, definitions):
    values = definitions.get(key)
    if not values:
        return ""
    if key in ["INC", "DEF"]:
        values = [patch_path_separator(opsys, value)
                  for value in values]
    lines = ["\t{}{} \\".format(value_prefix, value) for value in values]
    return "{}_{} = \\\n{}\n\t# empty\n".format(key_prefix,
                                                key,
                                                '\n'.join(lines))

def write_define(opsys, define, defines, makefile):
    value = find_definition(define, defines)
    if value:
        if define in ["FREERTOS", "PROOFS"]:
            value = os.path.abspath(value[0])
        makefile.write("{} = {}\n".format(define, value))

def write_common_defines(opsys, defines, makefile):
    common_defines, opsys_defines, harness_defines = defines

    for key_prefix, defines in zip(["C", "O", "H"],
                                   [common_defines,
                                    opsys_defines,
                                    harness_defines]):
        for value_prefix, key in zip([platform_definitions[opsys]["include"],
                                      platform_definitions[opsys]["define"],
                                      "", ""],
                                     ["INC", "DEF", "OPT", "CBMCFLAGS"]):
            define = construct_definition(opsys,
                                          key_prefix, value_prefix,
                                          key, defines)
            if define:
                makefile.write(define + "\n")


def write_makefile(opsys, template, defines, makefile):
    with open(template) as _template:
        for line in _template:
            line = patch_path_separator(opsys, line)
            keys = re.findall('@(\w+)@', line)
            values = [find_definition(key, defines) for key in keys]
            for key, value in zip(keys, values):
                if value is not None:
                    line = line.replace('@{}@'.format(key), " ".join(value))
                    line = patch_compile_output(opsys, line, key, value)
            makefile.write(line)

def write_cbmcbatchyaml_target(opsys, _makefile):
    target = """
################################################################
# Build configuration file to run cbmc under cbmc-batch in CI

define encode_options
'=$(shell echo $(1) | sed 's/ ,/ /g' | sed 's/ /;/g')='
endef

cbmc-batch.yaml:
	@echo "Building $@"
	@$(RM) $@
	@echo "jobos: ubuntu16" >> $@
	@echo "cbmcflags: $(call encode_options,$(CBMCFLAGS) --unwinding-assertions)" >> $@
	@echo "goto: $(ENTRY).goto" >> $@
	@echo "expected: $(H_EXPECTED)" >> $@

################################################################
"""
    if opsys != "windows":
        _makefile.write(target)

def makefile_from_template(opsys, template, defines, makefile="Makefile"):
    with open(makefile, "w") as _makefile:
        write_define(opsys, "FREERTOS", defines, _makefile)
        write_define(opsys, "PROOFS", defines, _makefile)
        write_common_defines(opsys, defines, _makefile)
        write_makefile(opsys, template, defines, _makefile)
        write_cbmcbatchyaml_target(opsys, _makefile)

################################################################
# Main

def main():
    args = get_arguments()

    common_defines = read_variable_definitions("MakefileCommon.json")
    opsys_defines = read_variable_definitions("MakefileWindows.json"
                                              if args.system == "windows"
                                              else "MakefileLinux.json")
    harness_defines = {}

    makefile_from_template(args.system,
                           "Makefile.template",
                           (common_defines, opsys_defines, harness_defines),
                           "Makefile.common")

if __name__ == "__main__":
    main()
