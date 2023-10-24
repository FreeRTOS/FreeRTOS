#!/usr/bin/env python3
#
# Constants for the generation of patches for CBMC proofs.
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

import os

PATCHES_DIR = os.path.dirname(os.path.abspath(__file__))


shared_prefix = [
    "."
]
shared_prefix_port = [
    "..", "..", "..", "Source", "portable", "MSVC-MingW"
]

absolute_prefix = os.path.abspath(os.path.join(PATCHES_DIR, *shared_prefix))
absolute_prefix_port = os.path.abspath(os.path.join(PATCHES_DIR, *shared_prefix_port))

HEADERS = [os.path.join(absolute_prefix, "FreeRTOSConfig.h"),
		   os.path.join(absolute_prefix, "FreeRTOSIPConfig.h"),
           os.path.join(absolute_prefix_port, "portmacro.h")]
