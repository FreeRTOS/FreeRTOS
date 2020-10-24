/* sha3.h
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


#ifndef WOLF_CRYPT_SHA3_H
#define WOLF_CRYPT_SHA3_H

#include <wolfssl/wolfcrypt/types.h>

#ifdef WOLFSSL_SHA3

#ifdef HAVE_FIPS
    /* for fips @wc_fips */
    #include <wolfssl/wolfcrypt/fips.h>
#endif

#ifdef __cplusplus
    extern "C" {
#endif

#ifdef WOLFSSL_ASYNC_CRYPT
    #include <wolfssl/wolfcrypt/async.h>
#endif

/* in bytes */
enum {
    WC_SHA3_224              = WC_HASH_TYPE_SHA3_224,
    WC_SHA3_224_DIGEST_SIZE  = 28,
    WC_SHA3_224_COUNT        = 18,

    WC_SHA3_256              = WC_HASH_TYPE_SHA3_256,
    WC_SHA3_256_DIGEST_SIZE  = 32,
    WC_SHA3_256_COUNT        = 17,

    WC_SHA3_384              = WC_HASH_TYPE_SHA3_384,
    WC_SHA3_384_DIGEST_SIZE  = 48,
    WC_SHA3_384_COUNT        = 13,

    WC_SHA3_512              = WC_HASH_TYPE_SHA3_512,
    WC_SHA3_512_DIGEST_SIZE  = 64,
    WC_SHA3_512_COUNT        =  9,

#if !defined(HAVE_SELFTEST) || \
    defined(HAVE_SELFTEST_VERSION) && (HAVE_SELFTEST_VERSION >= 2)
    /* These values are used for HMAC, not SHA-3 directly.
     * They come from from FIPS PUB 202. */
    WC_SHA3_224_BLOCK_SIZE = 144,
    WC_SHA3_256_BLOCK_SIZE = 136,
    WC_SHA3_384_BLOCK_SIZE = 104,
    WC_SHA3_512_BLOCK_SIZE = 72,
#endif
};

#ifndef NO_OLD_WC_NAMES
    #define SHA3_224             WC_SHA3_224
    #define SHA3_224_DIGEST_SIZE WC_SHA3_224_DIGEST_SIZE
    #define SHA3_256             WC_SHA3_256
    #define SHA3_256_DIGEST_SIZE WC_SHA3_256_DIGEST_SIZE
    #define SHA3_384             WC_SHA3_384
    #define SHA3_384_DIGEST_SIZE WC_SHA3_384_DIGEST_SIZE
    #define SHA3_512             WC_SHA3_512
    #define SHA3_512_DIGEST_SIZE WC_SHA3_512_DIGEST_SIZE
    #define Sha3 wc_Sha3
#endif



#ifdef WOLFSSL_XILINX_CRYPT
    #include "wolfssl/wolfcrypt/port/xilinx/xil-sha3.h"
#elif defined(WOLFSSL_AFALG_XILINX_SHA3)
    #include <wolfssl/wolfcrypt/port/af_alg/afalg_hash.h>
#else

/* Sha3 digest */
struct Sha3 {
    /* State data that is processed for each block. */
    word64 s[25];
    /* Unprocessed message data. */
    byte   t[200];
    /* Index into unprocessed data to place next message byte. */
    byte   i;

    void*  heap;

#ifdef WOLFSSL_ASYNC_CRYPT
    WC_ASYNC_DEV asyncDev;
#endif /* WOLFSSL_ASYNC_CRYPT */
#if defined(WOLFSSL_HASH_FLAGS) || defined(WOLF_CRYPTO_CB)
    word32 flags; /* enum wc_HashFlags in hash.h */
#endif
};

#ifndef WC_SHA3_TYPE_DEFINED
    typedef struct Sha3 wc_Sha3;
    #define WC_SHA3_TYPE_DEFINED
#endif

#endif

typedef wc_Sha3 wc_Shake;


WOLFSSL_API int wc_InitSha3_224(wc_Sha3*, void*, int);
WOLFSSL_API int wc_Sha3_224_Update(wc_Sha3*, const byte*, word32);
WOLFSSL_API int wc_Sha3_224_Final(wc_Sha3*, byte*);
WOLFSSL_API void wc_Sha3_224_Free(wc_Sha3*);
WOLFSSL_API int wc_Sha3_224_GetHash(wc_Sha3*, byte*);
WOLFSSL_API int wc_Sha3_224_Copy(wc_Sha3* src, wc_Sha3* dst);

WOLFSSL_API int wc_InitSha3_256(wc_Sha3*, void*, int);
WOLFSSL_API int wc_Sha3_256_Update(wc_Sha3*, const byte*, word32);
WOLFSSL_API int wc_Sha3_256_Final(wc_Sha3*, byte*);
WOLFSSL_API void wc_Sha3_256_Free(wc_Sha3*);
WOLFSSL_API int wc_Sha3_256_GetHash(wc_Sha3*, byte*);
WOLFSSL_API int wc_Sha3_256_Copy(wc_Sha3* src, wc_Sha3* dst);

WOLFSSL_API int wc_InitSha3_384(wc_Sha3*, void*, int);
WOLFSSL_API int wc_Sha3_384_Update(wc_Sha3*, const byte*, word32);
WOLFSSL_API int wc_Sha3_384_Final(wc_Sha3*, byte*);
WOLFSSL_API void wc_Sha3_384_Free(wc_Sha3*);
WOLFSSL_API int wc_Sha3_384_GetHash(wc_Sha3*, byte*);
WOLFSSL_API int wc_Sha3_384_Copy(wc_Sha3* src, wc_Sha3* dst);

WOLFSSL_API int wc_InitSha3_512(wc_Sha3*, void*, int);
WOLFSSL_API int wc_Sha3_512_Update(wc_Sha3*, const byte*, word32);
WOLFSSL_API int wc_Sha3_512_Final(wc_Sha3*, byte*);
WOLFSSL_API void wc_Sha3_512_Free(wc_Sha3*);
WOLFSSL_API int wc_Sha3_512_GetHash(wc_Sha3*, byte*);
WOLFSSL_API int wc_Sha3_512_Copy(wc_Sha3* src, wc_Sha3* dst);

WOLFSSL_API int wc_InitShake256(wc_Shake*, void*, int);
WOLFSSL_API int wc_Shake256_Update(wc_Shake*, const byte*, word32);
WOLFSSL_API int wc_Shake256_Final(wc_Shake*, byte*, word32);
WOLFSSL_API void wc_Shake256_Free(wc_Shake*);
WOLFSSL_API int wc_Shake256_Copy(wc_Shake* src, wc_Sha3* dst);

#if defined(WOLFSSL_HASH_FLAGS) || defined(WOLF_CRYPTO_CB)
    WOLFSSL_API int wc_Sha3_SetFlags(wc_Sha3* sha3, word32 flags);
    WOLFSSL_API int wc_Sha3_GetFlags(wc_Sha3* sha3, word32* flags);
#endif

#ifdef __cplusplus
    } /* extern "C" */
#endif

#endif /* WOLFSSL_SHA3 */
#endif /* WOLF_CRYPT_SHA3_H */

