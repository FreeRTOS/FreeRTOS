#!/usr/bin/env python3
#
# Generation of the cbmc-batch.yaml files for the CBMC proofs.
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
import platform
import subprocess


def remove_cbmc_yaml_files():
    for dyr, _, files in os.walk("."):
        cbmc_batch_files = [os.path.join(os.path.abspath(dyr), file)
                            for file in files if file == "cbmc-batch.yaml"]
        for file in cbmc_batch_files:
            os.remove(file)


def create_cbmc_yaml_files():
    # The YAML files are only used by CI and are not needed on Windows.
    if platform.system() == "Windows":
        return
    for dyr, _, files in os.walk("."):
        harness = [file for file in files if file.endswith("_harness.c")]
        if harness and "Makefile" in files:
            subprocess.run(["make", "cbmc-batch.yaml"],
                           stdout=subprocess.PIPE,
                           stderr=subprocess.PIPE,
                           cwd=os.path.abspath(dyr),
                           check=True)

if __name__ == '__main__':
    remove_cbmc_yaml_files()
    create_cbmc_yaml_files()
