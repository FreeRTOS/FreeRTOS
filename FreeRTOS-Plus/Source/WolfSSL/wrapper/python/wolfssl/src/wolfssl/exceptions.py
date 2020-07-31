# -*- coding: utf-8 -*-
#
# exceptions.py
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

from socket import error as socket_error


class SSLError(socket_error):
    """
    Raised to signal an error from the wolfSSL's SSL/TLS library. This signifies
    some problem in the higher-level encryption and authentication layer that's
    superimposed on the underlying network connection. This error is a subtype
    of socket.error, which in turn is a subtype of IOError. The error code and
    message of SSLError instances are provided by the wolfSSL library.
    """
    pass


class SSLZeroReturnError(SSLError):
    """
    A subclass of SSLError raised when trying to read or write and the SSL
    connection has been closed cleanly. Note that this doesn't mean that the
    underlying transport (read TCP) has been closed.
    """
    pass


class SSLWantReadError(SSLError):
    """
    A subclass of SSLError raised by a non-blocking SSL socket when trying to
    read or write data, but more data needs to be received on the underlying TCP
    transport before the request can be fulfilled.
    """
    pass


class SSLWantWriteError(SSLError):
    """
    A subclass of SSLError raised by a non-blocking SSL socket when trying to
    read or write data, but more data needs to be sent on the underlying TCP
    transport before the request can be fulfilled.
    """
    pass


class SSLSyscallError(SSLError):
    """
    A subclass of SSLError raised when a system error was encountered while
    trying to fulfill an operation on a SSL socket. Unfortunately, there is no
    easy way to inspect the original errno number.
    """
    pass


class SSLEOFError(SSLError):
    """
    A subclass of SSLError raised when the SSL connection has been terminated
    abruptly. Generally, you shouldn't try to reuse the underlying transport
    when this error is encountered.
    """
    pass

class CertificateError(ValueError):
    """
    Raised to signal an error with a certificate (such as mismatching hostname).
    Certificate errors detected by wolfSSL, though, raise an SSLError.
    """
    pass
