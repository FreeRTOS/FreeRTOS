#!/usr/bin/env python
# -*- coding: utf-8 -*-
#
# setup.py
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

# pylint: disable=import-error, wrong-import-position

from __future__ import absolute_import
import os
import sys
import shutil
from setuptools import setup, find_packages

sys.path.insert(0, 'src')
from wolfssl.__about__ import METADATA

os.chdir(os.path.dirname(sys.argv[0]) or ".")

LONG_DESCRIPTION = open("README.rst", "rt").read().replace(
    ".. include:: LICENSING.rst\n",
    open("LICENSING.rst", "rt").read()
)

INFO = dict(
    metadata={k[2:-2]: METADATA[k] for k in METADATA},
    contents={
        "long_description" : LONG_DESCRIPTION,
        "package_data"     : {"":  ["*.txt"]},
        "packages"         : find_packages("src"),
        "package_dir"      : {"": "src"},
        "cffi_modules"     : ["./src/wolfssl/build_ffi.py:ffi"],
    },
    requirements={
        "setup_requires"   : ["cffi>=1.6.0"],
        "install_requires" : ["cffi>=1.6.0"],
    },
    scripts={},
    plugins={},
    tests={},
)


def update_certs():
    c_certs_dir = "../../../certs"
    py_certs_dir = "certs"
    certs = [
        "ca-cert.pem",
        "client-cert.pem",
        "client-key.pem",
        "server-cert.pem",
        "server-key.pem",
        "external/ca-digicert-ev.pem"
    ]

    if os.path.isdir(c_certs_dir):
        if not os.path.isdir(py_certs_dir):
            os.makedirs(py_certs_dir)

        for cert in certs:
            shutil.copy(os.path.join(c_certs_dir, cert), py_certs_dir)


if __name__ == "__main__":
    update_certs()

    KWARGS = {k:v for dct in INFO.values() for (k, v) in dct.items()}
    setup(**KWARGS)
