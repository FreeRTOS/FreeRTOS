# build_ffi.py
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
import os

from cffi import FFI

ffi = FFI()

ffi.set_source("wolfcrypt._ffi",
    """
        #include <wolfssl/options.h>

        #include <wolfssl/wolfcrypt/sha.h>
        #include <wolfssl/wolfcrypt/sha256.h>
        #include <wolfssl/wolfcrypt/sha512.h>

        #include <wolfssl/wolfcrypt/hmac.h>

        #include <wolfssl/wolfcrypt/aes.h>
        #include <wolfssl/wolfcrypt/des3.h>
        #include <wolfssl/wolfcrypt/asn.h>

        #include <wolfssl/wolfcrypt/random.h>

        #include <wolfssl/wolfcrypt/rsa.h>
    """,
    include_dirs=["/usr/local/include"],
    library_dirs=["/usr/local/lib"],
    libraries=["wolfssl"],
)

ffi.cdef(
"""

    typedef unsigned char byte;
    typedef unsigned int  word32;

    typedef struct { ...; } Sha;

    int wc_InitSha(Sha*);
    int wc_ShaUpdate(Sha*, const byte*, word32);
    int wc_ShaFinal(Sha*, byte*);


    typedef struct { ...; } Sha256;

    int wc_InitSha256(Sha256*);
    int wc_Sha256Update(Sha256*, const byte*, word32);
    int wc_Sha256Final(Sha256*, byte*);


    typedef struct { ...; } Sha384;

    int wc_InitSha384(Sha384*);
    int wc_Sha384Update(Sha384*, const byte*, word32);
    int wc_Sha384Final(Sha384*, byte*);


    typedef struct { ...; } Sha512;

    int wc_InitSha512(Sha512*);
    int wc_Sha512Update(Sha512*, const byte*, word32);
    int wc_Sha512Final(Sha512*, byte*);


    typedef struct { ...; } Hmac;

    int wc_HmacSetKey(Hmac*, int, const byte*, word32);
    int wc_HmacUpdate(Hmac*, const byte*, word32);
    int wc_HmacFinal(Hmac*, byte*);


    typedef struct { ...; } Aes;

    int wc_AesSetKey(Aes*, const byte*, word32, const byte*, int);
    int wc_AesCbcEncrypt(Aes*, byte*, const byte*, word32);
    int wc_AesCbcDecrypt(Aes*, byte*, const byte*, word32);


    typedef struct { ...; } WC_RNG;

    int wc_InitRng(WC_RNG*);
    int wc_RNG_GenerateBlock(WC_RNG*, byte*, word32);
    int wc_RNG_GenerateByte(WC_RNG*, byte*);
    int wc_FreeRng(WC_RNG*);


    typedef struct {...; } RsaKey;

    int wc_InitRsaKey(RsaKey* key, void*);
    int wc_RsaSetRNG(RsaKey* key, WC_RNG* rng);
    int wc_FreeRsaKey(RsaKey* key);

    int wc_RsaPrivateKeyDecode(const byte*, word32*, RsaKey*, word32);
    int wc_RsaPublicKeyDecode(const byte*, word32*, RsaKey*, word32);
    int wc_RsaEncryptSize(RsaKey*);

    int wc_RsaPrivateDecrypt(const byte*, word32, byte*, word32,
                             RsaKey* key);
    int wc_RsaPublicEncrypt(const byte*, word32, byte*, word32,
                            RsaKey*, WC_RNG*);

    int wc_RsaSSL_Sign(const byte*, word32, byte*, word32, RsaKey*, WC_RNG*);
    int wc_RsaSSL_Verify(const byte*, word32, byte*, word32, RsaKey*);

"""
)

if __name__ == "__main__":
    ffi.compile(verbose=1)
