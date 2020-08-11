# -*- coding: utf-8 -*-
#
# test_methods.py
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

# pylint: disable=missing-docstring, redefined-outer-name, import-error

import pytest
from wolfssl._methods import (WolfSSLMethod, PROTOCOL_SSLv3, PROTOCOL_SSLv23,
                              PROTOCOL_TLS, PROTOCOL_TLSv1, PROTOCOL_TLSv1_1,
                              PROTOCOL_TLSv1_2)
from wolfssl._ffi import ffi as _ffi

@pytest.fixture(
    params=[-1, PROTOCOL_SSLv3, PROTOCOL_TLSv1, PROTOCOL_TLSv1_1],
    ids=["invalid", "SSLv3", "TLSv1", "TLSv1_1"])
def unsupported_method(request):
    yield request.param

@pytest.fixture(
    params=[PROTOCOL_SSLv23, PROTOCOL_TLS, PROTOCOL_TLSv1_2],
    ids=["SSLv23", "TLS", "TLSv1_2"])
def supported_method(request):
    yield request.param


def test_unsupported_method(unsupported_method):
    with pytest.raises(ValueError):
        WolfSSLMethod(unsupported_method, False)

    with pytest.raises(ValueError):
        WolfSSLMethod(unsupported_method, True)

def test_supported_method(supported_method):
    client = WolfSSLMethod(supported_method, False)
    server = WolfSSLMethod(supported_method, True)

    assert isinstance(client, WolfSSLMethod)
    assert isinstance(server, WolfSSLMethod)
    assert client.native_object != _ffi.NULL
    assert server.native_object != _ffi.NULL
