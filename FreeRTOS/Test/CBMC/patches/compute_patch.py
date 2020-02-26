#!/usr/bin/env python3
#
# Generation of patches for CBMC proofs.
#
# Copyright (C) 2019 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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


import json
import os
import re
import subprocess
import textwrap
import unittest

from patches_constants import PATCHES_DIR
from patches_constants import HEADERS


DEFINE_REGEX_MAKEFILE = re.compile(r"(?:['\"])?([\w]+)")
DEFINE_REGEX_HEADER = re.compile(r"\s*#\s*define\s*([\w]+)")

class DirtyGitError(Exception):
    pass

class PatchCreationError(Exception):
    pass

def prolog():
    return textwrap.dedent("""\
        This script generates patch files for the header files used
        in the cbmc proof. These patches permit setting values of preprocessor
        macros as part of the proof configuration.
    """)


def find_all_defines():
    """Collects all define values in Makefile.json.

       Some of the Makefiles use # in the json to make comments.
       As this is non standard json, we need to remove the comment
       lines before parsing. Then we extract all defines from the file.
    """
    defines = set()

    proof_dir = os.path.abspath(os.path.join(PATCHES_DIR, "..", "proofs"))

    for fldr, _, fyles in os.walk(proof_dir):
        if "Makefile.json" in fyles:
            file = os.path.join(fldr, "Makefile.json")
            key = "DEF"
        elif "MakefileCommon.json" in fyles:
            file = os.path.join(fldr, "MakefileCommon.json")
            key = "DEF "
        else:
            continue
        with open(file, "r") as source:
            content = "".join([line for line in source
                               if line and not line.strip().startswith("#")])
            makefile = json.loads(content)
            if key in makefile.keys():
                """This regex parses the define declaration in Makefile.json
                   'macro(x)=false' is an example for a declaration.
                   'macro' is expected to be matched.
                """
                for define in makefile[key]:
                    matched = DEFINE_REGEX_MAKEFILE.match(define)
                    if matched:
                        defines.add(matched.group(1))
    return defines

def manipulate_headerfile(defines, header_file):
    """Wraps all defines used in an ifndef."""

    # This regex matches the actual define in the header file.
    modified_content = ""
    with open(header_file, "r") as source:
        last = ""
        for line in source:
            match = DEFINE_REGEX_HEADER.match(line)
            if (match and
                    match.group(1) in defines and
                    not last.lstrip().startswith("#ifndef")):
                full_def = line
                # this loop deals with multiline definitions
                while line.rstrip().endswith("\\"):
                    line = next(source)
                    full_def += line
                # indentation for multiline definitions can be improved
                modified_content += textwrap.dedent("""\
                    #ifndef {target}
                        {original}\
                    #endif
                    """.format(target=match.group(1), original=full_def))
            else:
                modified_content += line
            last = line
    with open(header_file, "w") as output:
        output.write(modified_content)


def header_dirty(header_files):
    """Check that the header_file is not previously modified."""

    # Git does not update the modified file list returned by diff-files on
    # apply -R (at least not on MacOS).
    # Running git status updates git's internal state.
    status = subprocess.run(["git", "status"], stdout=subprocess.DEVNULL,
                            stderr=subprocess.PIPE, universal_newlines=True)

    diff_state = subprocess.run(["git", "diff-files"], stdout=subprocess.PIPE,
                                stderr=subprocess.PIPE, universal_newlines=True)

    if status.returncode:
        raise DirtyGitError(textwrap.dedent("""\
                Could not run git status. Exited: {}
                stderr: {}
                """.format(status.returncode, status.stderr)))

    if diff_state.returncode:
        raise DirtyGitError(textwrap.dedent("""\
                Could not run git diff-files. Exited: {}
                stderr: {}
                """.format(diff_state.returncode, diff_state.stderr)))

    for header_file in header_files:
        if os.path.basename(header_file) + "\n" in diff_state.stdout:
            return True
    return False


def create_patch(defines, header_file):
    """Computes a patch enclosing defines used in CBMC proofs with #ifndef."""
    manipulate_headerfile(defines, header_file)
    patch = subprocess.run(["git", "diff", header_file],
                           stdout=subprocess.PIPE,
                           stderr=subprocess.PIPE, universal_newlines=True)
    cleaned = subprocess.run(["git", "checkout", "--", header_file],
                             stdout=subprocess.DEVNULL,
                             stderr=subprocess.PIPE, universal_newlines=True)

    if patch.returncode:
        raise PatchCreationError(textwrap.dedent("""\
                git diff exited with error code: {}
                stderr: {}
                """.format(patch.returncode, patch.stderr)))

    if cleaned.returncode:
        raise DirtyGitError(textwrap.dedent("""\
                git checkout for cleaning files failed with error code: {}
                on file {}
                stderr: {}
                """.format(cleaned.returncode, header_file, cleaned.stderr)))

    header_path_part = header_file.replace(os.sep, "_")
    path_name = "auto_patch_" + header_path_part + ".patch"
    path_name = os.path.join(PATCHES_DIR, path_name)
    if patch.stdout:
        with open(path_name, "w") as patch_file:
            patch_file.write(patch.stdout)


def create_patches(headers):
    defines = find_all_defines()

    if not header_dirty(headers):
        for header in headers:
            create_patch(defines, header)
    else:
        raise DirtyGitError(textwrap.dedent("""\
                It seems like one of the header files is in dirty state.
                This script cannot patch files in dirty state.
                """))

# Invoke 'python3 -m unittest compute_patch.py" for running tests.
class TestDefineRegexes(unittest.TestCase):
    def test_makefile_regex(self):
        input1 = "ipconfigETHERNET_MINIMUM_PACKET_BYTES={MINIMUM_PACKET_BYTES}"
        input2 = "ipconfigETHERNET_MINIMUM_PACKET_BYTES=50"
        input3 = "'configASSERT(X)=__CPROVER_assert(x, \"must hold\")'"
        input4 = '"configASSERT (X)=__CPROVER_assert(x, "must hold")"'
        input5 = "configASSERT(X)=__CPROVER_assert(x,\"must hold\")"

        match1 = DEFINE_REGEX_MAKEFILE.match(input1)
        match2 = DEFINE_REGEX_MAKEFILE.match(input2)
        match3 = DEFINE_REGEX_MAKEFILE.match(input3)
        match4 = DEFINE_REGEX_MAKEFILE.match(input4)
        match5 = DEFINE_REGEX_MAKEFILE.match(input5)

        self.assertIsNotNone(match1)
        self.assertIsNotNone(match2)
        self.assertIsNotNone(match3)
        self.assertIsNotNone(match4)
        self.assertIsNotNone(match5)

        self.assertEqual(match1.group(1),
                         "ipconfigETHERNET_MINIMUM_PACKET_BYTES")
        self.assertEqual(match2.group(1),
                         "ipconfigETHERNET_MINIMUM_PACKET_BYTES")
        self.assertEqual(match3.group(1), "configASSERT")
        self.assertEqual(match4.group(1), "configASSERT")
        self.assertEqual(match5.group(1), "configASSERT")


    def test_header_regex(self):
        input1 = ("#define configASSERT( x )    if( ( x ) == 0 )" +
                  "vAssertCalled( __FILE__, __LINE__ )")
        input2 = "#define ipconfigMAX_ARP_RETRANSMISSIONS           ( 5 )"
        input3 = "#define ipconfigINCLUDE_FULL_INET_ADDR            1"

        match1 = DEFINE_REGEX_HEADER.match(input1)
        match2 = DEFINE_REGEX_HEADER.match(input2)
        match3 = DEFINE_REGEX_HEADER.match(input3)

        self.assertIsNotNone(match1)
        self.assertIsNotNone(match2)
        self.assertIsNotNone(match3)

        self.assertEqual(match1.group(1), "configASSERT")
        self.assertEqual(match2.group(1), "ipconfigMAX_ARP_RETRANSMISSIONS")
        self.assertEqual(match3.group(1), "ipconfigINCLUDE_FULL_INET_ADDR")

if __name__ == '__main__':
    create_patches(HEADERS)
