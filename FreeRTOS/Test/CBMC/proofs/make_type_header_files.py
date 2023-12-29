#!/usr/bin/env python3
#
# Compute type header files for c modules
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


import argparse
import logging
import os
import re
import shutil
import subprocess
import sys
from tempfile import TemporaryDirectory

def epilog():
    return """\
        This program dumps a header file containing the types and macros
        contained in the C file passed as input. It uses `goto-instrument`
        from the CBMC tool suite instead of the preprocessor, to dump types
        and other constructs as well as preprocessor directives.

        This program should be used in cases where types or macros declared
        for internal use in a C file use are needed to write a test harness
        or CBMC proof.  The intention is that the build process will run
        this program to dump the header file, and the proof will #include
        the header.
    """

_DEFINE_REGEX_HEADER = re.compile(r"\s*#\s*define\s*([\w]+)")


def get_module_name(fyle):
    base = os.path.basename(fyle)
    return base.split(".")[0]


def collect_defines(fyle):
    collector_result = ""
    continue_define = False
    in_potential_def_scope = ""
    potential_define = False
    potential_define_confirmed = False
    with open(fyle) as in_file:
        for line in in_file:
            matched = _DEFINE_REGEX_HEADER.match(line)
            if line.strip().startswith("#if"):
                potential_define = True
                in_potential_def_scope += line
            elif line.strip().startswith("#endif") and potential_define:
                if potential_define_confirmed:
                    in_potential_def_scope += line
                    collector_result += in_potential_def_scope
                in_potential_def_scope = ""
                potential_define = False
                potential_define_confirmed = False
            elif matched and potential_define:
                potential_define_confirmed = True
                in_potential_def_scope += line
            elif matched or continue_define:
                continue_define = line.strip("\n").endswith("\\")
                collector_result += line
            elif potential_define:
                in_potential_def_scope += line
    return collector_result


def make_header_file(goto_binary, fyle, target_folder):
    fyle = os.path.normpath(fyle)
    with TemporaryDirectory() as tmpdir:
        module = get_module_name(fyle)
        header_file = "{}_datastructure.h".format(module)

        drop_header_cmd = ["goto-instrument",
                           "--dump-c-type-header",
                           module,
                           goto_binary,
                           header_file]
        res = subprocess.run(drop_header_cmd,
                             stdout=subprocess.PIPE,
                             stderr=subprocess.STDOUT,
                             universal_newlines=True,
                             cwd=tmpdir)
        if res.returncode:
            logging.error("Dumping type header for file '%s' failed", fyle)
            logging.error("The command `%s` returned %s",
                          drop_header_cmd,
                          res.stdout)
            logging.error("The return code is %d", int(res.returncode))
            sys.exit(1)

        header = os.path.normpath(os.path.join(tmpdir, header_file))
        collected = collect_defines(fyle)
        logging.debug("Dumping the following header file to '%s':\n%s\n"
                      "// END GENERATED HEADER FILE", header, collected)
        with open(header, "a") as out:
            print(collected, file=out)

        target_file = os.path.normpath(os.path.join(target_folder, header_file))
        shutil.move(header, target_file)


_ARGS = [{
    "flags": ["--c-file"],
    "metavar": "F",
    "help": "source file to extract types and headers from",
    "required": True
}, {
    "flags": ["--binary"],
    "metavar": "B",
    "help": "file compiled from the source file with CBMC's goto-cc compiler",
    "required": True
}, {
    "flags": ["--out-dir"],
    "metavar": "D",
    "help": ("directory to write the generated header file to "
             "(default: %(default)s)"),
    "default": os.path.abspath(os.getcwd()),
}, {
    "flags": ["--verbose", "-v"],
    "help": "verbose output",
    "action": "store_true"
}]


if __name__ == '__main__':
    pars = argparse.ArgumentParser(
        epilog=epilog(),
        description="Dump a C file's types and macros to a separate file")
    for arg in _ARGS:
        flags = arg.pop("flags")
        pars.add_argument(*flags, **arg)

    args = pars.parse_args()

    fmt = "{script}: %(levelname)s %(message)s".format(
        script=os.path.basename(__file__))
    if args.verbose:
        logging.basicConfig(format=fmt, level=logging.DEBUG)
    else:
        logging.basicConfig(format=fmt, level=logging.INFO)

    make_header_file(args.binary, args.c_file, args.out_dir)
