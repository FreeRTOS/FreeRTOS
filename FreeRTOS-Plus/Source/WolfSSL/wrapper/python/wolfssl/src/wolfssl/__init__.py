# -*- coding: utf-8 -*-
#
# __init__.py
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

import sys
import errno
from socket import (
    socket, AF_INET, SOCK_STREAM, SOL_SOCKET, SO_TYPE, error as socket_error
)

try:
    from wolfssl._ffi import ffi as _ffi
    from wolfssl._ffi import lib as _lib
except ImportError:
    pass

from wolfssl.utils import t2b

from wolfssl.exceptions import (
    CertificateError, SSLError, SSLEOFError, SSLSyscallError,
    SSLWantReadError, SSLWantWriteError, SSLZeroReturnError
)

from wolfssl._methods import (
    PROTOCOL_SSLv23, PROTOCOL_SSLv3, PROTOCOL_TLSv1,
    PROTOCOL_TLSv1_1, PROTOCOL_TLSv1_2, PROTOCOL_TLS,
    WolfSSLMethod as _WolfSSLMethod
)

from wolfssl.__about__ import (
    __all__, METADATA
)

globals().update(METADATA)

CERT_NONE = 0
CERT_REQUIRED = 1

_VERIFY_MODE_LIST = [CERT_NONE, CERT_REQUIRED]

_SSL_SUCCESS = 1
_SSL_FILETYPE_PEM = 1
_SSL_ERROR_WANT_READ = 2

_WOLFSSL_ECC_SECP160K1 = 15
_WOLFSSL_ECC_SECP160R1 = 16
_WOLFSSL_ECC_SECP160R2 = 17
_WOLFSSL_ECC_SECP192K1 = 18
_WOLFSSL_ECC_SECP192R1 = 19
_WOLFSSL_ECC_SECP224K1 = 20
_WOLFSSL_ECC_SECP224R1 = 21
_WOLFSSL_ECC_SECP256K1 = 22
_WOLFSSL_ECC_SECP256R1 = 23
_WOLFSSL_ECC_SECP384R1 = 24
_WOLFSSL_ECC_SECP521R1 = 25
_WOLFSSL_ECC_BRAINPOOLP256R1 = 26
_WOLFSSL_ECC_BRAINPOOLP384R1 = 27
_WOLFSSL_ECC_BRAINPOOLP512R1 = 28

_SUPPORTED_CURVES = [
    _WOLFSSL_ECC_SECP160K1, _WOLFSSL_ECC_SECP160R1, _WOLFSSL_ECC_SECP160R2,
    _WOLFSSL_ECC_SECP192K1, _WOLFSSL_ECC_SECP192R1, _WOLFSSL_ECC_SECP224K1,
    _WOLFSSL_ECC_SECP224R1, _WOLFSSL_ECC_SECP256K1, _WOLFSSL_ECC_SECP256R1,
    _WOLFSSL_ECC_SECP384R1, _WOLFSSL_ECC_SECP521R1,
    _WOLFSSL_ECC_BRAINPOOLP256R1, _WOLFSSL_ECC_BRAINPOOLP384R1,
    _WOLFSSL_ECC_BRAINPOOLP512R1
]

_PY3 = sys.version_info[0] == 3

class SSLContext(object):
    """
    An SSLContext holds various SSL-related configuration options and
    data, such as certificates and possibly a private key.
    """

    def __init__(self, protocol, server_side=False):
        method = _WolfSSLMethod(protocol, server_side)

        self.protocol = protocol
        self._side = server_side
        self._verify_mode = None
        self.native_object = _lib.wolfSSL_CTX_new(method.native_object)

        # wolfSSL_CTX_new() takes ownership of the method.
        # the method is freed later inside wolfSSL_CTX_free()
        # or if wolfSSL_CTX_new() failed to allocate the context object.
        method.native_object = _ffi.NULL

        if self.native_object == _ffi.NULL:
            raise MemoryError("Unnable to allocate context object")

        # verify_mode initialization needs a valid native_object.
        self.verify_mode = CERT_NONE

        if not server_side:
            for curve in _SUPPORTED_CURVES:
                ret = _lib.wolfSSL_CTX_UseSupportedCurve(self.native_object,
                                                         curve)
                if ret != _SSL_SUCCESS:
                    raise SSLError("unnable to set curve (%d)" % curve)


    def __del__(self):
        if getattr(self, 'native_object', _ffi.NULL) != _ffi.NULL:
            _lib.wolfSSL_CTX_free(self.native_object)


    @property
    def verify_mode(self):
        """
        Whether to try to verify other peers’ certificates and how to behave
        if verification fails. This attribute must be one of CERT_NONE,
        CERT_OPTIONAL or CERT_REQUIRED.
        """
        return self._verify_mode


    @verify_mode.setter
    def verify_mode(self, value):
        if value not in _VERIFY_MODE_LIST:
            raise ValueError("verify_mode must be one of CERT_NONE, "
                             "CERT_OPTIONAL or CERT_REQUIRED")

        if value != self._verify_mode:
            self._verify_mode = value
            _lib.wolfSSL_CTX_set_verify(self.native_object,
                                        self._verify_mode,
                                        _ffi.NULL)


    def wrap_socket(self, sock, server_side=False,
                    do_handshake_on_connect=True,
                    suppress_ragged_eofs=True):
        """
        Wrap an existing Python socket sock and return an SSLSocket object.
        sock must be a SOCK_STREAM socket; other socket types are unsupported.

        The returned SSL socket is tied to the context, its settings and
        certificates. The parameters server_side, do_handshake_on_connect and
        suppress_ragged_eofs have the same meaning as in the top-level
        wrap_socket() function.
        """
        return SSLSocket(sock=sock, server_side=server_side,
                         do_handshake_on_connect=do_handshake_on_connect,
                         suppress_ragged_eofs=suppress_ragged_eofs,
                         _context=self)


    def set_ciphers(self, ciphers):
        """
        Set the available ciphers for sockets created with this context. It
        should be a string in the wolfSSL cipher list format. If no cipher can
        be selected (because compile-time options or other configuration forbids
        use of all the specified ciphers), an SSLError will be raised.
        """
        ret = _lib.wolfSSL_CTX_set_cipher_list(self.native_object, t2b(ciphers))

        if ret != _SSL_SUCCESS:
            raise SSLError("Unnable to set cipher list")


    def load_cert_chain(self, certfile, keyfile=None, password=None):
        """
        Load a private key and the corresponding certificate. The certfile
        string must be the path to a single file in PEM format containing
        the certificate as well as any number of CA certificates needed to
        establish the certificate's authenticity.

        The keyfile string, if present, must point to a file containing the
        private key in.

        The password parameter is not supported yet.
        """

        if password is not None:
            raise NotImplementedError("password callback support not "
                                      "implemented yet")

        if certfile is not None:
            ret = _lib.wolfSSL_CTX_use_certificate_chain_file(
                self.native_object, t2b(certfile))
            if ret != _SSL_SUCCESS:
                raise SSLError("Unnable to load certificate chain. Err %d"% ret)
        else:
            raise TypeError("certfile should be a valid filesystem path")

        if keyfile is not None:
            ret = _lib.wolfSSL_CTX_use_PrivateKey_file(
                self.native_object, t2b(keyfile), _SSL_FILETYPE_PEM)
            if ret != _SSL_SUCCESS:
                raise SSLError("Unnable to load private key. Err %d" % ret)


    def load_verify_locations(self, cafile=None, capath=None, cadata=None):
        """
        Load a set of "certification authority" (CA) certificates used to
        validate other peers' certificates when verify_mode is other than
        CERT_NONE. At least one of cafile or capath must be specified.

        The cafile string, if present, is the path to a file of concatenated
        CA certificates in PEM format.

        The capath string, if present, is the path to a directory containing
        several CA certificates in PEM format.
        """

        if cafile is None and capath is None and cadata is None:
            raise TypeError("cafile, capath and cadata cannot be all omitted")

        if cafile is not None or capath is not None:
            ret = _lib.wolfSSL_CTX_load_verify_locations(
                self.native_object,
                t2b(cafile) if cafile else _ffi.NULL,
                t2b(capath) if capath else _ffi.NULL)

            if ret != _SSL_SUCCESS:
                raise SSLError("Unnable to load verify locations. Err %d" % ret)

        if cadata is not None:
            ret = _lib.wolfSSL_CTX_load_verify_buffer(
                self.native_object, t2b(cadata), len(cadata), _SSL_FILETYPE_PEM)

            if ret != _SSL_SUCCESS:
                raise SSLError("Unnable to load verify locations. Err %d" % ret)


class SSLSocket(socket):
    """
    This class implements a subtype of socket.socket that wraps the
    underlying OS socket in an SSL/TLS connection, providing secure
    read and write methods over that channel.
    """

    def __init__(self, sock=None, keyfile=None, certfile=None,
                 server_side=False, cert_reqs=CERT_NONE,
                 ssl_version=PROTOCOL_TLS, ca_certs=None,
                 do_handshake_on_connect=True, family=AF_INET,
                 sock_type=SOCK_STREAM, proto=0, fileno=None,
                 suppress_ragged_eofs=True, ciphers=None,
                 _context=None):

        # set options
        self.do_handshake_on_connect = do_handshake_on_connect
        self.suppress_ragged_eofs = suppress_ragged_eofs
        self.server_side = server_side

        # set context
        if _context:
            self._context = _context
        else:
            if server_side and not certfile:
                raise ValueError("certfile must be specified for server-side "
                                 "operations")

            if keyfile and not certfile:
                raise ValueError("certfile must be specified")

            if certfile and not keyfile:
                keyfile = certfile

            self._context = SSLContext(ssl_version, server_side)
            self._context.verify_mode = cert_reqs
            if ca_certs:
                self._context.load_verify_locations(ca_certs)
            if certfile:
                self._context.load_cert_chain(certfile, keyfile)
            if ciphers:
                self._context.set_ciphers(ciphers)

            self.keyfile = keyfile
            self.certfile = certfile
            self.cert_reqs = cert_reqs
            self.ssl_version = ssl_version
            self.ca_certs = ca_certs
            self.ciphers = ciphers

        # preparing socket
        if sock is not None:
            # Can't use sock.type as other flags (such as SOCK_NONBLOCK) get
            # mixed in.
            if sock.getsockopt(SOL_SOCKET, SO_TYPE) != SOCK_STREAM:
                raise NotImplementedError("only stream sockets are supported")

            if _PY3:
                socket.__init__(self,
                                family=sock.family,
                                type=sock.type,
                                proto=sock.proto,
                                fileno=sock.fileno())
            else:
                socket.__init__(self, _sock=sock._sock)

            self.settimeout(sock.gettimeout())

            if _PY3:
                sock.detach()

        elif fileno is not None:
            socket.__init__(self, fileno=fileno)

        else:
            socket.__init__(self, family=family, type=sock_type,
                            proto=proto)

        # see if we are connected
        try:
            self.getpeername()
        except socket_error as exception:
            if exception.errno != errno.ENOTCONN:
                raise
            connected = False
        else:
            connected = True

        self._closed = False
        self._connected = connected

        # create the SSL object
        self.native_object = _lib.wolfSSL_new(self.context.native_object)
        if self.native_object == _ffi.NULL:
            raise MemoryError("Unnable to allocate ssl object")

        ret = _lib.wolfSSL_set_fd(self.native_object, self.fileno())
        if ret != _SSL_SUCCESS:
            self._release_native_object()
            raise ValueError("Unnable to set fd to ssl object")

        if connected:
            try:
                if do_handshake_on_connect:
                    self.do_handshake()
            except:
                self._release_native_object()
                self.close()
                raise


    def __del__(self):
        self._release_native_object()


    def _release_native_object(self):
        if getattr(self, 'native_object', _ffi.NULL) != _ffi.NULL:
            _lib.wolfSSL_CTX_free(self.native_object)
            self.native_object = _ffi.NULL


    @property
    def context(self):
        """
        Returns the context used by this object.
        """
        return self._context


    def dup(self):
        raise NotImplementedError("Can't dup() %s instances" %
                                  self.__class__.__name__)


    def _check_closed(self, call=None):
        if self.native_object == _ffi.NULL:
            raise ValueError("%s on closed or unwrapped secure channel" % call)

    def _check_connected(self):
        if not self._connected:
            # getpeername() will raise ENOTCONN if the socket is really
            # not connected; note that we can be connected even without
            # _connected being set, e.g. if connect() first returned
            # EAGAIN.
            self.getpeername()


    def write(self, data):
        """
        Write DATA to the underlying secure channel.
        Returns number of bytes of DATA actually transmitted.
        """
        self._check_closed("write")
        self._check_connected()

        data = t2b(data)

        return _lib.wolfSSL_write(self.native_object, data, len(data))


    def send(self, data, flags=0):
        if flags != 0:
            raise NotImplementedError("non-zero flags not allowed in calls to "
                                      "send() on %s" % self.__class__)

        return self.write(data)


    def sendall(self, data, flags=0):
        if flags != 0:
            raise NotImplementedError("non-zero flags not allowed in calls to "
                                      "sendall() on %s" % self.__class__)

        length = len(data)
        sent = 0

        while sent < length:
            sent += self.write(data[sent:])

        return sent


    def sendto(self, data, flags_or_addr, addr=None):
        # Ensure programs don't send unencrypted data trying to use this method
        raise NotImplementedError("sendto not allowed on instances "
                                  "of %s" % self.__class__)


    def sendmsg(self, *args, **kwargs):
        # Ensure programs don't send unencrypted data trying to use this method
        raise NotImplementedError("sendmsg not allowed on instances "
                                  "of %s" % self.__class__)


    def sendfile(self, file, offset=0, count=None):
        # Ensure programs don't send unencrypted files trying to use this method
        raise NotImplementedError("sendfile not allowed on instances "
                                  "of %s" % self.__class__)


    def read(self, length=1024, buffer=None):
        """
        Read up to LENGTH bytes and return them.
        Return zero-length string on EOF.
        """
        self._check_closed("read")
        self._check_connected()

        if buffer is not None:
            raise ValueError("buffer not allowed in calls to "
                             "read() on %s" % self.__class__)

        data = _ffi.new('byte[%d]' % length)
        length = _lib.wolfSSL_read(self.native_object, data, length)

        if length < 0:
            err = _lib.wolfSSL_get_error(self.native_object, 0)
            if err == _SSL_ERROR_WANT_READ:
                raise SSLWantReadError()
            else:
                raise SSLError("wolfSSL_read error (%d)" % err)

        return _ffi.buffer(data, length)[:] if length > 0 else b''


    def recv(self, length=1024, flags=0):
        if flags != 0:
            raise NotImplementedError("non-zero flags not allowed in calls to "
                                      "recv() on %s" % self.__class__)

        return self.read(self, length)


    def recv_into(self, buffer, nbytes=None, flags=0):
        raise NotImplementedError("recv_into not allowed on instances "
                                  "of %s" % self.__class__)


    def recvfrom(self, length=1024, flags=0):
        # Ensure programs don't receive encrypted data trying to use this method
        raise NotImplementedError("recvfrom not allowed on instances "
                                  "of %s" % self.__class__)


    def recvfrom_into(self, buffer, nbytes=None, flags=0):
        # Ensure programs don't receive encrypted data trying to use this method
        raise NotImplementedError("recvfrom_into not allowed on instances "
                                  "of %s" % self.__class__)


    def recvmsg(self, *args, **kwargs):
        raise NotImplementedError("recvmsg not allowed on instances of %s" %
                                  self.__class__)


    def recvmsg_into(self, *args, **kwargs):
        raise NotImplementedError("recvmsg_into not allowed on instances of "
                                  "%s" % self.__class__)


    def shutdown(self, how):
        if self.native_object != _ffi.NULL:
            _lib.wolfSSL_shutdown(self.native_object)
            self._release_native_object()
        socket.shutdown(self, how)


    def unwrap(self):
        """
        Unwraps the underlying OS socket from the SSL/TLS connection.
        Returns the wrapped OS socket.
        """
        if self.native_object != _ffi.NULL:
            _lib.wolfSSL_set_fd(self.native_object, -1)

        sock = socket(family=self.family,
                      sock_type=self.type,
                      proto=self.proto,
                      fileno=self.fileno())
        sock.settimeout(self.gettimeout())
        self.detach()

        return sock


    def do_handshake(self, block=False):
        """
        Perform a TLS/SSL handshake.
        """
        self._check_closed("do_handshake")
        self._check_connected()

        ret = _lib.wolfSSL_negotiate(self.native_object)
        if ret != _SSL_SUCCESS:
            raise SSLError("do_handshake failed with error %d" % ret)


    def _real_connect(self, addr, connect_ex):
        if self.server_side:
            raise ValueError("can't connect in server-side mode")

        # Here we assume that the socket is client-side, and not
        # connected at the time of the call.  We connect it, then wrap it.
        if self._connected:
            raise ValueError("attempt to connect already-connected SSLSocket!")

        if connect_ex:
            err = socket.connect_ex(self, addr)
        else:
            err = 0
            socket.connect(self, addr)

        if err == 0:
            self._connected = True
            if self.do_handshake_on_connect:
                self.do_handshake()

        return err


    def connect(self, addr):
        """
        Connects to remote ADDR, and then wraps the connection in a secure
        channel.
        """
        self._real_connect(addr, False)


    def connect_ex(self, addr):
        """
        Connects to remote ADDR, and then wraps the connection in a secure
        channel.
        """
        return self._real_connect(addr, True)


    def accept(self):
        """
        Accepts a new connection from a remote client, and returns a tuple
        containing that new connection wrapped with a server-side secure
        channel, and the address of the remote client.
        """
        if not self.server_side:
            raise ValueError("can't accept in client-side mode")

        newsock, addr = socket.accept(self)
        newsock = self.context.wrap_socket(
            newsock,
            do_handshake_on_connect=self.do_handshake_on_connect,
            suppress_ragged_eofs=self.suppress_ragged_eofs,
            server_side=True)

        return newsock, addr


def wrap_socket(sock, keyfile=None, certfile=None, server_side=False,
                cert_reqs=CERT_NONE, ssl_version=PROTOCOL_TLS, ca_certs=None,
                do_handshake_on_connect=True, suppress_ragged_eofs=True,
                ciphers=None):
    """
    Takes an instance sock of socket.socket, and returns an instance of
    wolfssl.SSLSocket, wrapping the underlying socket in an SSL context.

    The sock parameter must be a SOCK_STREAM socket; other socket types are
    unsupported.

    The keyfile and certfile parameters specify optional files with proper
    key and the certificates used to identify the local side of the connection.

    The parameter server_side is a boolean which identifies whether server-side
    or client-side behavior is desired from this socket.

    The parameter cert_reqs specifies whether a certificate is required from the
    other side of the connection, and whether it will be validated if provided.
    It must be one of the three values:

        * CERT_NONE (certificates ignored)
        * CERT_OPTIONAL (not required, but validated if provided)
        * CERT_REQUIRED (required and validated)

    If the value of this parameter is not CERT_NONE, then the ca_certs parameter
    must point to a file of CA certificates.

    The ca_certs file contains a set of concatenated “certification authority”
    certificates, which are used to validate certificates passed from the other
    end of the connection.

    The parameter ssl_version specifies which version of the SSL protocol to
    use. Typically, the server chooses a particular protocol version, and the
    client must adapt to the server’s choice. Most of the versions are not
    interoperable with the other versions. If not specified, the default is
    PROTOCOL_TLS; it provides the most compatibility with other versions.

    Here’s a table showing which versions in a client (down the side) can
    connect to which versions in a server (along the top):

    +------------------+-------+-----+-------+---------+---------+
    | client \\ server  | SSLv3 | TLS | TLSv1 | TLSv1.1 | TLSv1.2 |
    +------------------+-------+-----+-------+---------+---------+
    | SSLv3            | yes   | yes | no    | no      | no      |
    +------------------+-------+-----+-------+---------+---------+
    | TLS (SSLv23)     | yes   | yes | yes   | yes     | yes     |
    +------------------+-------+-----+-------+---------+---------+
    | TLSv1            | no    | yes | yes   | no      | no      |
    +------------------+-------+-----+-------+---------+---------+
    | TLSv1.1          | no    | yes | no    | yes     | no      |
    +------------------+-------+-----+-------+---------+---------+
    | TLSv1.2          | no    | yes | no    | no      | yes     |
    +------------------+-------+-----+-------+---------+---------+

    Note:
        Which connections succeed will vary depending on the versions of the ssl
        providers on both sides of the communication.

    The ciphers parameter sets the available ciphers for this SSL object. It
    should be a string in the wolfSSL cipher list format.

    The parameter do_handshake_on_connect specifies whether to do the SSL
    handshake automatically after doing a socket.connect(), or whether the
    application program will call it explicitly, by invoking the
    SSLSocket.do_handshake() method. Calling SSLSocket.do_handshake() explicitly
    gives the program control over the blocking behavior of the socket I/O
    involved in the handshake.

    The parameter suppress_ragged_eofs is not supported yet.
    """
    return SSLSocket(sock=sock, keyfile=keyfile, certfile=certfile,
                     server_side=server_side, cert_reqs=cert_reqs,
                     ssl_version=ssl_version, ca_certs=ca_certs,
                     do_handshake_on_connect=do_handshake_on_connect,
                     suppress_ragged_eofs=suppress_ragged_eofs,
                     ciphers=ciphers)
