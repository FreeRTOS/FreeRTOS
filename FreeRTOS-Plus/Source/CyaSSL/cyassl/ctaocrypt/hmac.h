/* hmac.h
 *
 * Copyright (C) 2006-2014 wolfSSL Inc.
 *
 * This file is part of CyaSSL.
 *
 * CyaSSL is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * CyaSSL is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301, USA
 */


#ifndef NO_HMAC

#ifndef CTAO_CRYPT_HMAC_H
#define CTAO_CRYPT_HMAC_H

#include <cyassl/ctaocrypt/types.h>

#ifndef NO_MD5
    #include <cyassl/ctaocrypt/md5.h>
#endif

#ifndef NO_SHA
    #include <cyassl/ctaocrypt/sha.h>
#endif

#ifndef NO_SHA256
    #include <cyassl/ctaocrypt/sha256.h>
#endif

#ifdef CYASSL_SHA512
    #include <cyassl/ctaocrypt/sha512.h>
#endif

#ifdef HAVE_BLAKE2 
    #include <cyassl/ctaocrypt/blake2.h>
#endif

#ifdef HAVE_CAVIUM
    #include <cyassl/ctaocrypt/logging.h>
    #include "cavium_common.h"
#endif

#ifdef __cplusplus
    extern "C" {
#endif


#define CYASSL_HMAC_CAVIUM_MAGIC 0xBEEF0005

enum {
    HMAC_FIPS_MIN_KEY = 14,   /* 112 bit key length minimum */

    IPAD    = 0x36,
    OPAD    = 0x5C,

/* If any hash is not enabled, add the ID here. */
#ifdef NO_MD5
    MD5     = 0,
#endif
#ifdef NO_SHA
    SHA     = 1,
#endif
#ifdef NO_SHA256
    SHA256  = 2,
#endif
#ifndef CYASSL_SHA512
    SHA512  = 4,
#endif
#ifndef CYASSL_SHA384
    SHA384  = 5,
#endif
#ifndef HAVE_BLAKE2 
    BLAKE2B_ID = 7,
#endif

/* Select the largest available hash for the buffer size. */
#if defined(CYASSL_SHA512)
    MAX_DIGEST_SIZE = SHA512_DIGEST_SIZE,
    HMAC_BLOCK_SIZE = SHA512_BLOCK_SIZE
#elif defined(HAVE_BLAKE2)
    MAX_DIGEST_SIZE = BLAKE2B_OUTBYTES,
    HMAC_BLOCK_SIZE = BLAKE2B_BLOCKBYTES,
#elif defined(CYASSL_SHA384)
    MAX_DIGEST_SIZE = SHA384_DIGEST_SIZE,
    HMAC_BLOCK_SIZE = SHA384_BLOCK_SIZE
#elif !defined(NO_SHA256)
    MAX_DIGEST_SIZE = SHA256_DIGEST_SIZE,
    HMAC_BLOCK_SIZE = SHA256_BLOCK_SIZE
#elif !defined(NO_SHA)
    MAX_DIGEST_SIZE = SHA_DIGEST_SIZE,
    HMAC_BLOCK_SIZE = SHA_BLOCK_SIZE
#elif !defined(NO_MD5)
    MAX_DIGEST_SIZE = MD5_DIGEST_SIZE,
    HMAC_BLOCK_SIZE = MD5_BLOCK_SIZE
#else
    #error "You have to have some kind of hash if you want to use HMAC."
#endif
};


/* hash union */
typedef union {
    #ifndef NO_MD5
        Md5 md5;
    #endif
    #ifndef NO_SHA
        Sha sha;
    #endif
    #ifndef NO_SHA256
        Sha256 sha256;
    #endif
    #ifdef CYASSL_SHA384
        Sha384 sha384;
    #endif
    #ifdef CYASSL_SHA512
        Sha512 sha512;
    #endif
    #ifdef HAVE_BLAKE2 
        Blake2b blake2b;
    #endif
} Hash;

/* Hmac digest */
typedef struct Hmac {
    Hash    hash;
    word32  ipad[HMAC_BLOCK_SIZE  / sizeof(word32)];  /* same block size all*/
    word32  opad[HMAC_BLOCK_SIZE  / sizeof(word32)];
    word32  innerHash[MAX_DIGEST_SIZE / sizeof(word32)];
    byte    macType;                                     /* md5 sha or sha256 */
    byte    innerHashKeyed;                              /* keyed flag */
#ifdef HAVE_CAVIUM
    word16   keyLen;          /* hmac key length */
    word16   dataLen;
    HashType type;            /* hmac key type */
    int      devId;           /* nitrox device id */
    word32   magic;           /* using cavium magic */
    word64   contextHandle;   /* nitrox context memory handle */
    byte*    data;            /* buffered input data for one call */
#endif
} Hmac;


/* does init */
CYASSL_API int HmacSetKey(Hmac*, int type, const byte* key, word32 keySz);
CYASSL_API int HmacUpdate(Hmac*, const byte*, word32);
CYASSL_API int HmacFinal(Hmac*, byte*);

#ifdef HAVE_CAVIUM
    CYASSL_API int  HmacInitCavium(Hmac*, int);
    CYASSL_API void HmacFreeCavium(Hmac*);
#endif

CYASSL_API int CyaSSL_GetHmacMaxSize(void);


#ifdef HAVE_HKDF

CYASSL_API int HKDF(int type, const byte* inKey, word32 inKeySz,
                    const byte* salt, word32 saltSz,
                    const byte* info, word32 infoSz,
                    byte* out, word32 outSz);

#endif /* HAVE_HKDF */


#ifdef HAVE_FIPS
    /* fips wrapper calls, user can call direct */
    CYASSL_API int HmacSetKey_fips(Hmac*, int type, const byte* key,
                                   word32 keySz);
    CYASSL_API int HmacUpdate_fips(Hmac*, const byte*, word32);
    CYASSL_API int HmacFinal_fips(Hmac*, byte*);
    #ifndef FIPS_NO_WRAPPERS
        /* if not impl or fips.c impl wrapper force fips calls if fips build */
        #define HmacSetKey HmacSetKey_fips
        #define HmacUpdate HmacUpdate_fips
        #define HmacFinal  HmacFinal_fips
    #endif /* FIPS_NO_WRAPPERS */

#endif /* HAVE_FIPS */


#ifdef __cplusplus
    } /* extern "C" */
#endif

#endif /* CTAO_CRYPT_HMAC_H */

#endif /* NO_HMAC */

