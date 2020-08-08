# -*- coding: utf-8 -*-
#
# __about__.py
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

# pylint: disable=missing-docstring

METADATA = dict(
    __name__="wolfssl",
    __version__="0.1.0",
    __license__="GPLv2 or Commercial License",
    __author__="wolfSSL Inc.",
    __author_email__="info@wolfssl.com",
    __url__="https://wolfssl.github.io/wolfssl-py",
    __description__= \
      u"A Python module that encapsulates wolfSSL's C SSL/TLS library.",
    __keywords__="security, cryptography, ssl, embedded, embedded ssl",
    __classifiers__=[
        u"License :: OSI Approved :: GNU General Public License v2 (GPLv2)",
        u"License :: Other/Proprietary License",
        u"Operating System :: OS Independent",
        u"Programming Language :: Python :: 2.7",
        u"Programming Language :: Python :: 3.5",
        u"Topic :: Security",
        u"Topic :: Security :: Cryptography",
        u"Topic :: Software Development"
    ]
)

globals().update(METADATA)

__all__ = list(METADATA.keys())
