/* aes.h
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


#ifndef NO_AES

#ifndef CTAO_CRYPT_AES_H
#define CTAO_CRYPT_AES_H


#include <cyassl/ctaocrypt/types.h>

#ifdef HAVE_CAVIUM
    #include <cyassl/ctaocrypt/logging.h>
    #include "cavium_common.h"
#endif

#ifdef CYASSL_AESNI

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

#endif /* CYASSL_AESNI */

#if !defined (ALIGN16)
    #define ALIGN16
#endif

#ifdef __cplusplus
    extern "C" {
#endif


#define CYASSL_AES_CAVIUM_MAGIC 0xBEEF0002

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
#ifdef CYASSL_AESNI
    byte use_aesni;
#endif /* CYASSL_AESNI */
#ifdef HAVE_CAVIUM
    AesType type;            /* aes key type */
    int     devId;           /* nitrox device id */
    word32  magic;           /* using cavium magic */
    word64  contextHandle;   /* nitrox context memory handle */
#endif
#ifdef CYASSL_AES_COUNTER
    word32  left;            /* unsued bytes left from last call */
#endif
#ifdef CYASSL_PIC32MZ_CRYPT
    word32 key_ce[AES_BLOCK_SIZE*2/sizeof(word32)] ;
    word32 iv_ce [AES_BLOCK_SIZE  /sizeof(word32)] ;
    int    keylen ;
#endif
} Aes;


CYASSL_API int  AesSetKey(Aes* aes, const byte* key, word32 len, const byte* iv,
                          int dir);
CYASSL_API int  AesSetIV(Aes* aes, const byte* iv);
CYASSL_API int  AesCbcEncrypt(Aes* aes, byte* out, const byte* in, word32 sz);
CYASSL_API int  AesCbcDecrypt(Aes* aes, byte* out, const byte* in, word32 sz);
CYASSL_API void AesCtrEncrypt(Aes* aes, byte* out, const byte* in, word32 sz);
CYASSL_API void AesEncryptDirect(Aes* aes, byte* out, const byte* in);
CYASSL_API void AesDecryptDirect(Aes* aes, byte* out, const byte* in);
CYASSL_API int  AesSetKeyDirect(Aes* aes, const byte* key, word32 len,
                                const byte* iv, int dir);
#ifdef HAVE_AESGCM
CYASSL_API void AesGcmSetKey(Aes* aes, const byte* key, word32 len);
CYASSL_API void AesGcmEncrypt(Aes* aes, byte* out, const byte* in, word32 sz,
                              const byte* iv, word32 ivSz,
                              byte* authTag, word32 authTagSz,
                              const byte* authIn, word32 authInSz);
CYASSL_API int  AesGcmDecrypt(Aes* aes, byte* out, const byte* in, word32 sz,
                              const byte* iv, word32 ivSz,
                              const byte* authTag, word32 authTagSz,
                              const byte* authIn, word32 authInSz);

typedef struct Gmac {
    Aes aes;
} Gmac;
CYASSL_API void GmacSetKey(Gmac* gmac, const byte* key, word32 len);
CYASSL_API void GmacUpdate(Gmac* gmac, const byte* iv, word32 ivSz,
                              const byte* authIn, word32 authInSz,
                              byte* authTag, word32 authTagSz);
#endif /* HAVE_AESGCM */
#ifdef HAVE_AESCCM
CYASSL_API void AesCcmSetKey(Aes* aes, const byte* key, word32 keySz);
CYASSL_API void AesCcmEncrypt(Aes* aes, byte* out, const byte* in, word32 inSz,
                              const byte* nonce, word32 nonceSz,
                              byte* authTag, word32 authTagSz,
                              const byte* authIn, word32 authInSz);
CYASSL_API int  AesCcmDecrypt(Aes* aes, byte* out, const byte* in, word32 inSz,
                              const byte* nonce, word32 nonceSz,
                              const byte* authTag, word32 authTagSz,
                              const byte* authIn, word32 authInSz);
#endif /* HAVE_AESCCM */

#ifdef HAVE_CAVIUM
    CYASSL_API int  AesInitCavium(Aes*, int);
    CYASSL_API void AesFreeCavium(Aes*);
#endif


#ifdef HAVE_FIPS
    /* fips wrapper calls, user can call direct */
    CYASSL_API int  AesSetKey_fips(Aes* aes, const byte* key, word32 len,
                                   const byte* iv, int dir);
    CYASSL_API int  AesSetIV_fips(Aes* aes, const byte* iv);
    CYASSL_API int  AesCbcEncrypt_fips(Aes* aes, byte* out, const byte* in,
                                       word32 sz);
    CYASSL_API int  AesCbcDecrypt_fips(Aes* aes, byte* out, const byte* in,
                                       word32 sz);
    #ifndef FIPS_NO_WRAPPERS
        /* if not impl or fips.c impl wrapper force fips calls if fips build */
        #define AesSetKey     AesSetKey_fips
        #define AesSetIV      AesSetIV_fips
        #define AesCbcEncrypt AesCbcEncrypt_fips
        #define AesCbcDecrypt AesCbcDecrypt_fips
    #endif /* FIPS_NO_WRAPPERS */

#endif /* HAVE_FIPS */


#ifdef __cplusplus
    } /* extern "C" */
#endif


#endif /* CTAO_CRYPT_AES_H */
#endif /* NO_AES */

