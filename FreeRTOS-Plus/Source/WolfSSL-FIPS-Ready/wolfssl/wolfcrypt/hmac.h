/* hmac.h
 *
 * Copyright (C) 2006-2020 wolfSSL Inc.
 *
 * This file is part of wolfSSL.
 *
 * wolfSSL is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 3 of the License, or
 * (at your option) any later version.
 *
 * wolfSSL is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1335, USA
 */

/*!
    \file wolfssl/wolfcrypt/hmac.h
*/

#ifndef NO_HMAC

#ifndef WOLF_CRYPT_HMAC_H
#define WOLF_CRYPT_HMAC_H

#include <wolfssl/wolfcrypt/hash.h>

#if defined(HAVE_FIPS) && \
	(!defined(HAVE_FIPS_VERSION) || (HAVE_FIPS_VERSION < 2))
/* for fips @wc_fips */
    #include <cyassl/ctaocrypt/hmac.h>
    #define WC_HMAC_BLOCK_SIZE HMAC_BLOCK_SIZE
#endif


#if defined(HAVE_FIPS) && \
	defined(HAVE_FIPS_VERSION) && (HAVE_FIPS_VERSION >= 2)
	#include <wolfssl/wolfcrypt/fips.h>
#endif

#ifdef __cplusplus
    extern "C" {
#endif

/* avoid redefinition of structs */
#if !defined(HAVE_FIPS) || \
    (defined(HAVE_FIPS_VERSION) && (HAVE_FIPS_VERSION >= 2))

#ifdef WOLFSSL_ASYNC_CRYPT
    #include <wolfssl/wolfcrypt/async.h>
#endif

#ifndef NO_OLD_WC_NAMES
    #define HMAC_BLOCK_SIZE WC_HMAC_BLOCK_SIZE
#endif

#define WC_HMAC_INNER_HASH_KEYED_SW     1
#define WC_HMAC_INNER_HASH_KEYED_DEV    2

enum {
    HMAC_FIPS_MIN_KEY = 14,   /* 112 bit key length minimum */

    IPAD    = 0x36,
    OPAD    = 0x5C,

/* If any hash is not enabled, add the ID here. */
#ifdef NO_MD5
    WC_MD5     = WC_HASH_TYPE_MD5,
#endif
#ifdef NO_SHA
    WC_SHA     = WC_HASH_TYPE_SHA,
#endif
#ifdef NO_SHA256
    WC_SHA256  = WC_HASH_TYPE_SHA256,
#endif
#ifndef WOLFSSL_SHA512
    WC_SHA512  = WC_HASH_TYPE_SHA512,
#endif
#ifndef WOLFSSL_SHA384
    WC_SHA384  = WC_HASH_TYPE_SHA384,
#endif
#ifndef WOLFSSL_SHA224
    WC_SHA224  = WC_HASH_TYPE_SHA224,
#endif
#ifndef WOLFSSL_SHA3
    WC_SHA3_224 = WC_HASH_TYPE_SHA3_224,
    WC_SHA3_256 = WC_HASH_TYPE_SHA3_256,
    WC_SHA3_384 = WC_HASH_TYPE_SHA3_384,
    WC_SHA3_512 = WC_HASH_TYPE_SHA3_512,
#endif
#ifdef HAVE_PKCS11
    HMAC_MAX_ID_LEN = 32,
#endif
};

/* Select the largest available hash for the buffer size. */
#define WC_HMAC_BLOCK_SIZE WC_MAX_BLOCK_SIZE

#if !defined(WOLFSSL_SHA3) && !defined(WOLFSSL_SHA512) && \
    !defined(WOLFSSL_SHA384) && defined(NO_SHA256) && \
    defined(WOLFSSL_SHA224) && defined(NO_SHA) && defined(NO_MD5)
    #error "You have to have some kind of hash if you want to use HMAC."
#endif


/* hash union */
typedef union {
#ifndef NO_MD5
    wc_Md5 md5;
#endif
#ifndef NO_SHA
    wc_Sha sha;
#endif
#ifdef WOLFSSL_SHA224
    wc_Sha224 sha224;
#endif
#ifndef NO_SHA256
    wc_Sha256 sha256;
#endif
#ifdef WOLFSSL_SHA384
    wc_Sha384 sha384;
#endif
#ifdef WOLFSSL_SHA512
    wc_Sha512 sha512;
#endif
#ifdef WOLFSSL_SHA3
    wc_Sha3 sha3;
#endif
} wc_Hmac_Hash;

/* Hmac digest */
struct Hmac {
    wc_Hmac_Hash    hash;
    word32  ipad[WC_HMAC_BLOCK_SIZE  / sizeof(word32)];  /* same block size all*/
    word32  opad[WC_HMAC_BLOCK_SIZE  / sizeof(word32)];
    word32  innerHash[WC_MAX_DIGEST_SIZE / sizeof(word32)];
    void*   heap;                 /* heap hint */
    byte    macType;              /* md5 sha or sha256 */
    byte    innerHashKeyed;       /* keyed flag */
#ifdef WOLFSSL_ASYNC_CRYPT
    WC_ASYNC_DEV asyncDev;
#endif /* WOLFSSL_ASYNC_CRYPT */
#ifdef WOLF_CRYPTO_CB
    int     devId;
    void*   devCtx;
    const byte* keyRaw;
#endif
#ifdef HAVE_PKCS11
    byte    id[HMAC_MAX_ID_LEN];
    int     idLen;
#endif
#if defined(WOLFSSL_ASYNC_CRYPT) || defined(WOLF_CRYPTO_CB)
    word16  keyLen;          /* hmac key length (key in ipad) */
#endif
};

#ifndef WC_HMAC_TYPE_DEFINED
    typedef struct Hmac Hmac;
    #define WC_HMAC_TYPE_DEFINED
#endif


#endif /* HAVE_FIPS */

/* does init */
WOLFSSL_API int wc_HmacSetKey(Hmac*, int type, const byte* key, word32 keySz);
WOLFSSL_API int wc_HmacUpdate(Hmac*, const byte*, word32);
WOLFSSL_API int wc_HmacFinal(Hmac*, byte*);
WOLFSSL_API int wc_HmacSizeByType(int type);

WOLFSSL_API int wc_HmacInit(Hmac* hmac, void* heap, int devId);
WOLFSSL_API int wc_HmacInit_Id(Hmac* hmac, byte* id, int len, void* heap,
                               int devId);
WOLFSSL_API void wc_HmacFree(Hmac*);

WOLFSSL_API int wolfSSL_GetHmacMaxSize(void);

WOLFSSL_LOCAL int _InitHmac(Hmac* hmac, int type, void* heap);

#ifdef HAVE_HKDF

WOLFSSL_API int wc_HKDF_Extract(int type, const byte* salt, word32 saltSz,
                                const byte* inKey, word32 inKeySz, byte* out);
WOLFSSL_API int wc_HKDF_Expand(int type, const byte* inKey, word32 inKeySz,
                               const byte* info, word32 infoSz,
                               byte* out,        word32 outSz);

WOLFSSL_API int wc_HKDF(int type, const byte* inKey, word32 inKeySz,
                    const byte* salt, word32 saltSz,
                    const byte* info, word32 infoSz,
                    byte* out, word32 outSz);

#endif /* HAVE_HKDF */

#ifdef __cplusplus
    } /* extern "C" */
#endif

#endif /* WOLF_CRYPT_HMAC_H */

#endif /* NO_HMAC */

