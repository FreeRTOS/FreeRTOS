/* aes.h
 *
 * Copyright (C) 2006-2015 wolfSSL Inc.
 *
 * This file is part of wolfSSL. (formerly known as CyaSSL)
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
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301, USA
 */

#ifndef WOLF_CRYPT_AES_H
#define WOLF_CRYPT_AES_H

#include <wolfssl/wolfcrypt/types.h>

#ifndef NO_AES

/* included for fips @wc_fips */
#ifdef HAVE_FIPS
#include <cyassl/ctaocrypt/aes.h>
#if defined(CYASSL_AES_COUNTER) && !defined(WOLFSSL_AES_COUNTER)
    #define WOLFSSL_AES_COUNTER
#endif
#if !defined(WOLFSSL_AES_DIRECT) && defined(CYASSL_AES_DIRECT)
    #define WOLFSSL_AES_DIRECT
#endif
#endif

#ifndef HAVE_FIPS /* to avoid redefinition of macros */
#ifdef HAVE_CAVIUM
    #include <wolfssl/ctaocrypt/logging.h>
    #include "cavium_common.h"
#endif

#ifdef WOLFSSL_AESNI

#include <wmmintrin.h>

#if !defined (ALIGN16)
    #if defined (__GNUC__)
        #define ALIGN16 __attribute__ ( (aligned (16)))
    #elif defined(_MSC_VER)
        /* disable align warning, we want alignment ! */
        #pragma warning(disable: 4324)
        #define ALIGN16 __declspec (align (16))
    #else
        #define ALIGN16
    #endif
#endif

#endif /* WOLFSSL_AESNI */

#if !defined (ALIGN16)
    #define ALIGN16
#endif
#endif /* HAVE_FIPS */

#ifdef __cplusplus
    extern "C" {
#endif

#ifndef HAVE_FIPS /* to avoid redefinition of structures */
#define WOLFSSL_AES_CAVIUM_MAGIC 0xBEEF0002

enum {
    AES_ENC_TYPE   = 1,   /* cipher unique type */
    AES_ENCRYPTION = 0,
    AES_DECRYPTION = 1,
    AES_BLOCK_SIZE = 16
};


typedef struct Aes {
    /* AESNI needs key first, rounds 2nd, not sure why yet */
    ALIGN16 word32 key[60];
    word32  rounds;

    ALIGN16 word32 reg[AES_BLOCK_SIZE / sizeof(word32)];      /* for CBC mode */
    ALIGN16 word32 tmp[AES_BLOCK_SIZE / sizeof(word32)];      /* same         */

#ifdef HAVE_AESGCM
    ALIGN16 byte H[AES_BLOCK_SIZE];
#ifdef GCM_TABLE
    /* key-based fast multiplication table. */
    ALIGN16 byte M0[256][AES_BLOCK_SIZE];
#endif /* GCM_TABLE */
#endif /* HAVE_AESGCM */
#ifdef WOLFSSL_AESNI
    byte use_aesni;
#endif /* WOLFSSL_AESNI */
#ifdef HAVE_CAVIUM
    AesType type;            /* aes key type */
    int     devId;           /* nitrox device id */
    word32  magic;           /* using cavium magic */
    word64  contextHandle;   /* nitrox context memory handle */
#endif
#ifdef WOLFSSL_AES_COUNTER
    word32  left;            /* unsued bytes left from last call */
#endif
#ifdef WOLFSSL_PIC32MZ_CRYPT
    word32 key_ce[AES_BLOCK_SIZE*2/sizeof(word32)] ;
    word32 iv_ce [AES_BLOCK_SIZE  /sizeof(word32)] ;
    int    keylen ;
#endif
#ifdef WOLFSSL_TI_CRYPT
    int    keylen ;
#endif
} Aes;


#ifdef HAVE_AESGCM
typedef struct Gmac {
    Aes aes;
} Gmac;
#endif /* HAVE_AESGCM */
#endif /* HAVE_FIPS */

 WOLFSSL_API int  wc_AesSetKey(Aes* aes, const byte* key, word32 len, const byte* iv,
                          int dir);
 WOLFSSL_API int  wc_AesSetIV(Aes* aes, const byte* iv);
 WOLFSSL_API int  wc_AesCbcEncrypt(Aes* aes, byte* out, const byte* in, word32 sz);
 WOLFSSL_API int  wc_AesCbcDecrypt(Aes* aes, byte* out, const byte* in, word32 sz);
 WOLFSSL_API int  wc_AesCbcDecryptWithKey(byte* out, const byte* in, word32 inSz,
                                 const byte* key, word32 keySz, const byte* iv);

/* AES-CTR */
#ifdef WOLFSSL_AES_COUNTER
 WOLFSSL_API void wc_AesCtrEncrypt(Aes* aes, byte* out, const byte* in, word32 sz);
#endif
/* AES-DIRECT */
#if defined(WOLFSSL_AES_DIRECT)
 WOLFSSL_API void wc_AesEncryptDirect(Aes* aes, byte* out, const byte* in);
 WOLFSSL_API void wc_AesDecryptDirect(Aes* aes, byte* out, const byte* in);
 WOLFSSL_API int  wc_AesSetKeyDirect(Aes* aes, const byte* key, word32 len,
                                const byte* iv, int dir);
#endif
#ifdef HAVE_AESGCM
 WOLFSSL_API int  wc_AesGcmSetKey(Aes* aes, const byte* key, word32 len);
 WOLFSSL_API int  wc_AesGcmEncrypt(Aes* aes, byte* out, const byte* in, word32 sz,
                              const byte* iv, word32 ivSz,
                              byte* authTag, word32 authTagSz,
                              const byte* authIn, word32 authInSz);
 WOLFSSL_API int  wc_AesGcmDecrypt(Aes* aes, byte* out, const byte* in, word32 sz,
                              const byte* iv, word32 ivSz,
                              const byte* authTag, word32 authTagSz,
                              const byte* authIn, word32 authInSz);

 WOLFSSL_API int wc_GmacSetKey(Gmac* gmac, const byte* key, word32 len);
 WOLFSSL_API int wc_GmacUpdate(Gmac* gmac, const byte* iv, word32 ivSz,
                              const byte* authIn, word32 authInSz,
                              byte* authTag, word32 authTagSz);
#endif /* HAVE_AESGCM */
#ifdef HAVE_AESCCM
 WOLFSSL_API void wc_AesCcmSetKey(Aes* aes, const byte* key, word32 keySz);
 WOLFSSL_API void wc_AesCcmEncrypt(Aes* aes, byte* out, const byte* in, word32 inSz,
                              const byte* nonce, word32 nonceSz,
                              byte* authTag, word32 authTagSz,
                              const byte* authIn, word32 authInSz);
 WOLFSSL_API int  wc_AesCcmDecrypt(Aes* aes, byte* out, const byte* in, word32 inSz,
                              const byte* nonce, word32 nonceSz,
                              const byte* authTag, word32 authTagSz,
                              const byte* authIn, word32 authInSz);
#endif /* HAVE_AESCCM */

#ifdef HAVE_CAVIUM
     WOLFSSL_API int  wc_AesInitCavium(Aes*, int);
     WOLFSSL_API void wc_AesFreeCavium(Aes*);
#endif

#ifdef __cplusplus
    } /* extern "C" */
#endif


#endif /* NO_AES */
#endif /* WOLF_CRYPT_AES_H */

