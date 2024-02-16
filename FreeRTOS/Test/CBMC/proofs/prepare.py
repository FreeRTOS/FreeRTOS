#!/usr/bin/env python3
#
# Python script for preparing the code base for the CBMC proofs.
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

import logging
import os
import sys
import textwrap
from subprocess import CalledProcessError

from make_common_makefile import main as make_common_file
from make_configuration_directories import main as process_configurations
from make_proof_makefiles import main as make_proof_files
from make_cbmc_batch_files import create_cbmc_yaml_files

CWD = os.getcwd()
sys.path.append(os.path.normpath(os.path.join(CWD, "..", "patches")))

#from compute_patch import create_patches
#from compute_patch import DirtyGitError
#from compute_patch import PatchCreationError
from patches_constants import HEADERS

from compute_patch import find_all_defines
from compute_patch import manipulate_headerfile

import patch

PROOFS_DIR = os.path.dirname(os.path.abspath(__file__))

LOGGER = logging.getLogger("PrepareLogger")

################################################################

def patch_headers(headers):
    """Patch headers so we can define symbols on the command line.

    When building for CBMC, it is convenient to define symbols on the
    command line and know that these definitions will override the
    definitions of the same symbols in header files.

    The create_patches function takes a list of header files, searches
    the Makefile.json files for symbols that will be defined in the
    Makefiles, and creates patch files that protect the definition of
    those symbols in header files with #ifndef/#endif.  In this way,
    command line definitions will override header file definitions.

    The create_patches function, however, depends on the fact that all
    header files being modified are included in the top-level git
    repository.  This assumption is violated if header files live in
    submodules.

    This function just updates the header files in place without
    creating patch files.  One potential vulnerability of this
    function is that it could cause preexisting patch files to fail if
    they patch a file being modified here.
    """
    defines = find_all_defines()
    for header in headers:
        manipulate_headerfile(defines, header)

################################################################

def build():
    process_configurations()
    make_common_file()
    make_proof_files()
    try:
        create_cbmc_yaml_files()
    except CalledProcessError as e:
        logging.error(textwrap.dedent("""\
            An error occurred during cbmc-batch generation.
            The error message is: {}
            """.format(str(e))))
        exit(1)

    # Patch headers directly instead of creating patch files.
    patch.patch()
    patch_headers(HEADERS)

    #try:
    #    create_patches(HEADERS)
    #except (DirtyGitError, PatchCreationError) as e:
    #    logging.error(textwrap.dedent("""\
    #        An error occurred during patch creation.
    #        The error message is: {}
    #        """.format(str(e))))
    #    exit(1)

################################################################

if __name__ == '__main__':
    logging.basicConfig(format="{script}: %(levelname)s %(message)s".format(
        script=os.path.basename(__file__)))
    build()
