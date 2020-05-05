#!/usr/bin/env python3
#
# unpatching changes for the CBMC proofs.
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

import subprocess
import os
import sys
from glob import glob

from patches_constants import PATCHES_DIR

try:
    os.remove(os.path.join(PATCHES_DIR, "patched"))
except FileNotFoundError:
    print("Nothing to do here.")
    sys.exit(0)
for tmpfile in glob(os.path.join(PATCHES_DIR, "*.patch")):
    print("unpatch", tmpfile)
    result = subprocess.run(["git", "apply", "-R", "--ignore-space-change", "--ignore-whitespace", tmpfile],
                            cwd=os.path.join("..", "..", "..", ".."))
    if result.returncode:
        print("Unpatching failed: {}".format(tmpfile))
