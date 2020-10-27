/* sha512.h
 *
 * Copyright (C) 2006-2020 wolfSSL Inc.
 *
 * This file is part of wolfSSL.
 *
 * wolfSSL is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
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
    \file wolfssl/wolfcrypt/sha512.h
*/


#ifndef WOLF_CRYPT_SHA512_H
#define WOLF_CRYPT_SHA512_H

#include <wolfssl/wolfcrypt/types.h>

#if defined(WOLFSSL_SHA512) || defined(WOLFSSL_SHA384)


#if defined(HAVE_FIPS) && \
    defined(HAVE_FIPS_VERSION) && (HAVE_FIPS_VERSION >= 2)
    #include <wolfssl/wolfcrypt/fips.h>
#endif /* HAVE_FIPS_VERSION >= 2 */

#if defined(HAVE_FIPS) && \
	(!defined(HAVE_FIPS_VERSION) || (HAVE_FIPS_VERSION < 2))
    #ifdef WOLFSSL_SHA512
        #define wc_Sha512             Sha512
        #define WC_SHA512             SHA512
        #define WC_SHA512_BLOCK_SIZE  SHA512_BLOCK_SIZE
        #define WC_SHA512_DIGEST_SIZE SHA512_DIGEST_SIZE
        #define WC_SHA512_PAD_SIZE    SHA512_PAD_SIZE
    #endif /* WOLFSSL_SHA512 */
    #ifdef WOLFSSL_SHA384
        #define wc_Sha384             Sha384
        #define WC_SHA384             SHA384
        #define WC_SHA384_BLOCK_SIZE  SHA384_BLOCK_SIZE
        #define WC_SHA384_DIGEST_SIZE SHA384_DIGEST_SIZE
        #define WC_SHA384_PAD_SIZE    SHA384_PAD_SIZE
    #endif /* WOLFSSL_SHA384 */

    #define CYASSL_SHA512
    #if defined(WOLFSSL_SHA384)
        #define CYASSL_SHA384
    #endif
	/* for fips @wc_fips */
    #include <cyassl/ctaocrypt/sha512.h>
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
#ifdef WOLFSSL_ESP32WROOM32_CRYPT
    #include <wolfssl/wolfcrypt/port/Espressif/esp32-crypt.h>
#endif
#if defined(_MSC_VER)
    #define SHA512_NOINLINE __declspec(noinline)
#elif defined(__IAR_SYSTEMS_ICC__) || defined(__GNUC__)
    #define SHA512_NOINLINE __attribute__((noinline))
#else
    #define SHA512_NOINLINE
#endif

#ifdef WOLFSSL_SHA512

#if !defined(NO_OLD_SHA_NAMES)
    #define SHA512             WC_SHA512
#endif

#if !defined(NO_OLD_WC_NAMES)
    #define Sha512             wc_Sha512
    #define SHA512_BLOCK_SIZE  WC_SHA512_BLOCK_SIZE
    #define SHA512_DIGEST_SIZE WC_SHA512_DIGEST_SIZE
    #define SHA512_PAD_SIZE    WC_SHA512_PAD_SIZE
#endif

#endif /* WOLFSSL_SHA512 */

/* in bytes */
enum {
#ifdef WOLFSSL_SHA512
    WC_SHA512              =   WC_HASH_TYPE_SHA512,
#endif
    WC_SHA512_BLOCK_SIZE   = 128,
    WC_SHA512_DIGEST_SIZE  =  64,
    WC_SHA512_PAD_SIZE     = 112
};


#ifdef WOLFSSL_IMX6_CAAM
    #include "wolfssl/wolfcrypt/port/caam/wolfcaam_sha.h"
#elif defined (WOLFSSL_PSOC6_CRYPTO)
    #include "wolfssl/wolfcrypt/port/cypress/psoc6_crypto.h"
#else
/* wc_Sha512 digest */
struct wc_Sha512 {
    word64  digest[WC_SHA512_DIGEST_SIZE / sizeof(word64)];
    word64  buffer[WC_SHA512_BLOCK_SIZE  / sizeof(word64)];
    word32  buffLen;   /* in bytes          */
    word64  loLen;     /* length in bytes   */
    word64  hiLen;     /* length in bytes   */
    void*   heap;
#ifdef USE_INTEL_SPEEDUP
    const byte* data;
#endif
#ifdef WOLFSSL_ASYNC_CRYPT
    WC_ASYNC_DEV asyncDev;
#endif /* WOLFSSL_ASYNC_CRYPT */
#ifdef WOLFSSL_SMALL_STACK_CACHE
    word64* W;
#endif
#if defined(WOLFSSL_ESP32WROOM32_CRYPT) && \
   !defined(NO_WOLFSSL_ESP32WROOM32_CRYPT_HASH)
    WC_ESP32SHA ctx;
#endif
#if defined(WOLFSSL_HASH_FLAGS) || defined(WOLF_CRYPTO_CB)
    word32 flags; /* enum wc_HashFlags in hash.h */
#endif
};

#ifndef WC_SHA512_TYPE_DEFINED
    typedef struct wc_Sha512 wc_Sha512;
    #define WC_SHA512_TYPE_DEFINED
#endif
#endif

#endif /* HAVE_FIPS */

#ifdef WOLFSSL_ARMASM
WOLFSSL_LOCAL void Transform_Sha512_Len(wc_Sha512* sha512, const byte* data,
                                        word32 len);
#endif

#ifdef WOLFSSL_SHA512


WOLFSSL_API int wc_InitSha512(wc_Sha512*);
WOLFSSL_API int wc_InitSha512_ex(wc_Sha512*, void*, int);
WOLFSSL_API int wc_Sha512Update(wc_Sha512*, const byte*, word32);
WOLFSSL_API int wc_Sha512FinalRaw(wc_Sha512*, byte*);
WOLFSSL_API int wc_Sha512Final(wc_Sha512*, byte*);
WOLFSSL_API void wc_Sha512Free(wc_Sha512*);

WOLFSSL_API int wc_Sha512GetHash(wc_Sha512*, byte*);
WOLFSSL_API int wc_Sha512Copy(wc_Sha512* src, wc_Sha512* dst);

#if defined(WOLFSSL_HASH_FLAGS) || defined(WOLF_CRYPTO_CB)
    WOLFSSL_API int wc_Sha512SetFlags(wc_Sha512* sha512, word32 flags);
    WOLFSSL_API int wc_Sha512GetFlags(wc_Sha512* sha512, word32* flags);
#endif

#endif /* WOLFSSL_SHA512 */

#if defined(WOLFSSL_SHA384)

/* avoid redefinition of structs */
#if !defined(HAVE_FIPS) || \
    (defined(HAVE_FIPS_VERSION) && (HAVE_FIPS_VERSION >= 2))

#if !defined(NO_OLD_SHA_NAMES)
    #define SHA384             WC_SHA384
#endif

#if !defined(NO_OLD_WC_NAMES)
    #define Sha384             wc_Sha384
    #define SHA384_BLOCK_SIZE  WC_SHA384_BLOCK_SIZE
    #define SHA384_DIGEST_SIZE WC_SHA384_DIGEST_SIZE
    #define SHA384_PAD_SIZE    WC_SHA384_PAD_SIZE
#endif

/* in bytes */
enum {
    WC_SHA384              =   WC_HASH_TYPE_SHA384,
    WC_SHA384_BLOCK_SIZE   =   WC_SHA512_BLOCK_SIZE,
    WC_SHA384_DIGEST_SIZE  =   48,
    WC_SHA384_PAD_SIZE     =   WC_SHA512_PAD_SIZE
};


#ifndef WC_SHA384_TYPE_DEFINED
    typedef struct wc_Sha512 wc_Sha384;
    #define WC_SHA384_TYPE_DEFINED
#endif
#endif /* HAVE_FIPS */

WOLFSSL_API int wc_InitSha384(wc_Sha384*);
WOLFSSL_API int wc_InitSha384_ex(wc_Sha384*, void*, int);
WOLFSSL_API int wc_Sha384Update(wc_Sha384*, const byte*, word32);
WOLFSSL_API int wc_Sha384FinalRaw(wc_Sha384*, byte*);
WOLFSSL_API int wc_Sha384Final(wc_Sha384*, byte*);
WOLFSSL_API void wc_Sha384Free(wc_Sha384*);

WOLFSSL_API int wc_Sha384GetHash(wc_Sha384*, byte*);
WOLFSSL_API int wc_Sha384Copy(wc_Sha384* src, wc_Sha384* dst);

#if defined(WOLFSSL_HASH_FLAGS) || defined(WOLF_CRYPTO_CB)
    WOLFSSL_API int wc_Sha384SetFlags(wc_Sha384* sha384, word32 flags);
    WOLFSSL_API int wc_Sha384GetFlags(wc_Sha384* sha384, word32* flags);
#endif

#endif /* WOLFSSL_SHA384 */

#ifdef __cplusplus
    } /* extern "C" */
#endif

#endif /* WOLFSSL_SHA512 || WOLFSSL_SHA384 */
#endif /* WOLF_CRYPT_SHA512_H */

