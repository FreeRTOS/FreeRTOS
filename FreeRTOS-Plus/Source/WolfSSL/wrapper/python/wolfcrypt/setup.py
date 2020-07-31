#!/usr/bin/env python
# -*- coding: utf-8 -*-
#
# Copyright (C) 2006-2020 wolfSSL Inc.
#
# This file is part of wolfSSL.
#
# wolfSSL is free software; you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation; either version 2 of the License, or
# (at your option) any later version.
#
# wolfSSL is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program; if not, write to the Free Software
# Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1335, USA
#/

# Python 2.7 Standard Library
from __future__ import absolute_import
import os
import sys
from wolfcrypt.__about__ import metadata
from setuptools import setup, find_packages

os.chdir(os.path.dirname(sys.argv[0]) or ".")

long_description = open("README.rst", "rt").read().replace(
    ".. include:: LICENSING.rst\n",
    open("LICENSING.rst", "rt").read()
)

info = dict(
    metadata     = {k[2:-2]: metadata[k] for k in metadata},
    contents     = {
                     "long_description": long_description,
                     "package_data":     {"":  ["*.txt"]},
                     "packages":         find_packages(),
                     "cffi_modules":     ["./wolfcrypt/build_ffi.py:ffi"],
    },
    requirements = {
                    "setup_requires":    ["cffi>=1.6.0"],
                    "install_requires":  ["cffi>=1.6.0"],
    },
    scripts      = {},
    plugins      = {},
    tests        = {},
)

if __name__ == "__main__":
    kwargs = {k:v for dct in info.values() for (k,v) in dct.items()}
    setup(**kwargs)
