# -*- coding: utf-8 -*-
#
# test_context.py
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

# pylint: disable=missing-docstring, invalid-name, import-error
# pylint: disable=redefined-outer-name

import pytest

with open("certs/ca-cert.pem") as ca:
    _CADATA = ca.read()

def test_context_creation(ssl_context):
    assert ssl_context != None

def test_verify_mode(ssl_provider, ssl_context):
    with pytest.raises(ValueError):
        ssl_context.verify_mode = -1

    assert ssl_context.verify_mode == ssl_provider.CERT_NONE

    ssl_context.verify_mode = ssl_provider.CERT_REQUIRED
    assert ssl_context.verify_mode == ssl_provider.CERT_REQUIRED

def test_set_ciphers(ssl_context):
    ssl_context.set_ciphers("DHE-RSA-AES256-SHA256")

    with pytest.raises(Exception):
        ssl_context.set_ciphers("foo")

def test_load_cert_chain_raises(ssl_context):
    with pytest.raises(TypeError):
        ssl_context.load_cert_chain(None)

def test_load_cert_chain(ssl_context):
    ssl_context.load_cert_chain("certs/client-cert.pem",
                                "certs/client-key.pem")

def test_load_verify_locations_raises(ssl_context):
    with pytest.raises(TypeError):
        ssl_context.load_verify_locations(None)

def test_load_verify_locations_with_cafile(ssl_context):
    ssl_context.load_verify_locations(cafile="certs/ca-cert.pem")

def test_load_verify_locations_with_cadata(ssl_provider, ssl_context):
    ssl_context.load_verify_locations(cadata=_CADATA)
