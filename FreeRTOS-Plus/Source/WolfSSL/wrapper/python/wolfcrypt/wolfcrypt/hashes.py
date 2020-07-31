# hashes.py
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
from wolfcrypt._ffi  import ffi as _ffi
from wolfcrypt._ffi  import lib as _lib
from wolfcrypt.utils import t2b, b2h

from wolfcrypt.exceptions import *

class _Hash(object):
    """
    A **PEP 247: Cryptographic Hash Functions** compliant
    **Hash Function Interface**.
    """
    def __init__(self, string=None):
        self._native_object = _ffi.new(self._native_type)
        ret = self._init()
        if ret < 0:
            raise WolfCryptError("Hash init error (%d)" % ret)

        if (string):
            self.update(string)


    @classmethod
    def new(cls, string=None):
        """
        Creates a new hashing object and returns it. The optional
        **string** parameter, if supplied, will be immediately
        hashed into the object's starting state, as if
        obj.update(string) was called.
        """
        return cls(string)


    def copy(self):
        """
        Returns a separate copy of this hashing object. An update
        to this copy won't affect the original object.
        """
        copy = self.new("")

        _ffi.memmove(copy._native_object,
                     self._native_object,
                     self._native_size)

        return copy


    def update(self, string):
        """
        Hashes **string** into the current state of the hashing
        object. update() can be called any number of times during
        a hashing object's lifetime.
        """
        string = t2b(string)

        ret = self._update(string)
        if ret < 0:
            raise WolfCryptError("Hash update error (%d)" % ret)


    def digest(self):
        """
        Returns the hash value of this hashing object as a string
        containing 8-bit data. The object is not altered in any
        way by this function; you can continue updating the object
        after calling this function.
        """
        result = t2b("\0" * self.digest_size)

        if self._native_object:
            obj = _ffi.new(self._native_type)

            _ffi.memmove(obj, self._native_object, self._native_size)

            ret = self._final(obj, result)
            if ret < 0:
                raise WolfCryptError("Hash finalize error (%d)" % ret)

        return result


    def hexdigest(self):
        """
        Returns the hash value of this hashing object as a string
        containing hexadecimal digits. Lowercase letters are used
        for the digits 'a' through 'f'. Like the .digest() method,
        this method doesn't alter the object.
        """
        return b2h(self.digest())


class Sha(_Hash):
    """
    **SHA-1** is a cryptographic hash function standardized by **NIST**.

    It produces an [ **160-bit | 20 bytes** ] message digest.
    """
    digest_size  = 20
    _native_type = "Sha *"
    _native_size = _ffi.sizeof("Sha")


    def _init(self):
        return _lib.wc_InitSha(self._native_object)


    def _update(self, data):
        return _lib.wc_ShaUpdate(self._native_object, data, len(data))


    def _final(self, obj, ret):
        return _lib.wc_ShaFinal(obj, ret)


class Sha256(_Hash):
    """
    **SHA-256** is a cryptographic hash function from the
    **SHA-2 family** and is standardized by **NIST**.

    It produces a [ **256-bit | 32 bytes** ] message digest.
    """
    digest_size  = 32
    _native_type = "Sha256 *"
    _native_size = _ffi.sizeof("Sha256")


    def _init(self):
        return _lib.wc_InitSha256(self._native_object)


    def _update(self, data):
        return _lib.wc_Sha256Update(self._native_object, data, len(data))


    def _final(self, obj, ret):
        return _lib.wc_Sha256Final(obj, ret)


class Sha384(_Hash):
    """
    **SHA-384** is a cryptographic hash function from the
    **SHA-2 family** and is standardized by **NIST**.

    It produces a [ **384-bit | 48 bytes** ] message digest.
    """
    digest_size  = 48
    _native_type = "Sha384 *"
    _native_size = _ffi.sizeof("Sha384")


    def _init(self):
        return _lib.wc_InitSha384(self._native_object)


    def _update(self, data):
        return _lib.wc_Sha384Update(self._native_object, data, len(data))


    def _final(self, obj, ret):
        return _lib.wc_Sha384Final(obj, ret)


class Sha512(_Hash):
    """
    **SHA-512** is a cryptographic hash function from the
    **SHA-2 family** and is standardized by **NIST**.

    It produces a [ **512-bit | 64 bytes** ] message digest.
    """
    digest_size  = 64
    _native_type = "Sha512 *"
    _native_size = _ffi.sizeof("Sha512")


    def _init(self):
        return _lib.wc_InitSha512(self._native_object)


    def _update(self, data):
        return _lib.wc_Sha512Update(self._native_object, data, len(data))


    def _final(self, obj, ret):
        return _lib.wc_Sha512Final(obj, ret)


# Hmac types

_TYPE_SHA    = 1
_TYPE_SHA256 = 2
_TYPE_SHA384 = 5
_TYPE_SHA512 = 4
_HMAC_TYPES = [_TYPE_SHA, _TYPE_SHA256, _TYPE_SHA384, _TYPE_SHA512]


class _Hmac(_Hash):
    """
    A **PEP 247: Cryptographic Hash Functions** compliant
    **Keyed Hash Function Interface**.
    """
    digest_size  = None
    _native_type = "Hmac *"
    _native_size = _ffi.sizeof("Hmac")


    def __init__(self, key, string=None):
        key = t2b(key)

        self._native_object = _ffi.new(self._native_type)
        ret = self._init(self._type, key)
        if ret < 0:
            raise WolfCryptError("Hmac init error (%d)" % ret)

        if (string):
            self.update(string)



    @classmethod
    def new(cls, key, string=None):
        """
        Creates a new hashing object and returns it. **key** is
        a required parameter containing a string giving the key
        to use. The optional **string** parameter, if supplied,
        will be immediately hashed into the object's starting
        state, as if obj.update(string) was called.
        """
        return cls(key, string)


    def _init(self, type, key):
        return _lib.wc_HmacSetKey(self._native_object, type, key, len(key))


    def _update(self, data):
        return _lib.wc_HmacUpdate(self._native_object, data, len(data))


    def _final(self, obj, ret):
        return _lib.wc_HmacFinal(obj, ret)


class HmacSha(_Hmac):
    """
    A HMAC function using **SHA-1** as it's cryptographic
    hash function.

    It produces a [ **512-bit | 64 bytes** ] message digest.
    """
    _type = _TYPE_SHA
    digest_size = Sha.digest_size


class HmacSha256(_Hmac):
    """
    A HMAC function using **SHA-256** as it's cryptographic
    hash function.

    It produces a [ **512-bit | 64 bytes** ] message digest.
    """
    _type = _TYPE_SHA256
    digest_size = Sha256.digest_size


class HmacSha384(_Hmac):
    """
    A HMAC function using **SHA-384** as it's cryptographic
    hash function.

    It produces a [ **512-bit | 64 bytes** ] message digest.
    """
    _type = _TYPE_SHA384
    digest_size = Sha384.digest_size


class HmacSha512(_Hmac):
    """
    A HMAC function using **SHA-512** as it's cryptographic
    hash function.

    It produces a [ **512-bit | 64 bytes** ] message digest.
    """
    _type = _TYPE_SHA512
    digest_size = Sha512.digest_size
