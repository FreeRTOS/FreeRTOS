# -*- coding: utf-8 -*-
#
# test_client.py
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

HOST = "www.python.org"
PORT = 443
CA_CERTS = "certs/ca-digicert-ev.pem"

@pytest.fixture(
    params=["wrap_socket", "wrap_socket_with_ca",
            "wrap_socket_from_context", "ssl_socket"])
def secure_socket(request, ssl_provider, tcp_socket):
    sock = None

    if request.param == "wrap_socket":
        sock = ssl_provider.wrap_socket(tcp_socket)

    elif request.param == "wrap_socket_with_ca":
        sock = ssl_provider.wrap_socket(
            tcp_socket, cert_reqs=ssl_provider.CERT_REQUIRED, ca_certs=CA_CERTS)

    elif request.param == "wrap_socket_from_context":
        ctx = ssl_provider.SSLContext(ssl_provider.PROTOCOL_TLSv1_2)

        ctx.verify_mode = ssl_provider.CERT_REQUIRED
        ctx.load_verify_locations(CA_CERTS)

        sock = ctx.wrap_socket(tcp_socket)

    elif request.param == "ssl_socket":
        sock = ssl_provider.SSLSocket(
            tcp_socket, cert_reqs=ssl_provider.CERT_REQUIRED, ca_certs=CA_CERTS)

    if sock:
        yield sock
        sock.close()

def test_secure_connection(secure_socket):
    secure_socket.connect((HOST, PORT))

    secure_socket.write(b"GET / HTTP/1.1\n\n")
    assert secure_socket.read(4) == b"HTTP"
