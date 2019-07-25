/* des3.h
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

#ifndef WOLF_CRYPT_DES3_H
#define WOLF_CRYPT_DES3_H

#include <wolfssl/wolfcrypt/types.h>

#ifndef NO_DES3

#ifdef HAVE_FIPS
/* included for fips @wc_fips */
#include <cyassl/ctaocrypt/des3.h>
#endif

#ifdef __cplusplus
    extern "C" {
#endif

#ifndef HAVE_FIPS /* to avoid redifinition of macros */
#define WOLFSSL_3DES_CAVIUM_MAGIC 0xBEEF0003

enum {
    DES_ENC_TYPE    = 2,     /* cipher unique type */
    DES3_ENC_TYPE   = 3,     /* cipher unique type */
    DES_BLOCK_SIZE  = 8,
    DES_KS_SIZE     = 32,

    DES_ENCRYPTION  = 0,
    DES_DECRYPTION  = 1
};

#define DES_IVLEN 8
#define DES_KEYLEN 8
#define DES3_IVLEN 8
#define DES3_KEYLEN 24


#ifdef STM32F2_CRYPTO
enum {
    DES_CBC = 0,
    DES_ECB = 1
};
#endif


/* DES encryption and decryption */
typedef struct Des {
    word32 reg[DES_BLOCK_SIZE / sizeof(word32)];      /* for CBC mode */
    word32 tmp[DES_BLOCK_SIZE / sizeof(word32)];      /* same         */
    word32 key[DES_KS_SIZE];
} Des;


/* DES3 encryption and decryption */
typedef struct Des3 {
    word32 key[3][DES_KS_SIZE];
    word32 reg[DES_BLOCK_SIZE / sizeof(word32)];      /* for CBC mode */
    word32 tmp[DES_BLOCK_SIZE / sizeof(word32)];      /* same         */
#ifdef HAVE_CAVIUM
    int     devId;           /* nitrox device id */
    word32  magic;           /* using cavium magic */
    word64  contextHandle;   /* nitrox context memory handle */
#endif
} Des3;
#endif /* HAVE_FIPS */

WOLFSSL_API int  wc_Des_SetKey(Des* des, const byte* key, const byte* iv, int dir);
WOLFSSL_API void wc_Des_SetIV(Des* des, const byte* iv);
WOLFSSL_API int  wc_Des_CbcEncrypt(Des* des, byte* out, const byte* in, word32 sz);
WOLFSSL_API int  wc_Des_CbcDecrypt(Des* des, byte* out, const byte* in, word32 sz);
WOLFSSL_API int  wc_Des_EcbEncrypt(Des* des, byte* out, const byte* in, word32 sz);
WOLFSSL_API int  wc_Des_CbcDecryptWithKey(byte* out, const byte* in, word32 sz,
                                               const byte* key, const byte* iv);

WOLFSSL_API int  wc_Des3_SetKey(Des3* des, const byte* key, const byte* iv,int dir);
WOLFSSL_API int  wc_Des3_SetIV(Des3* des, const byte* iv);
WOLFSSL_API int  wc_Des3_CbcEncrypt(Des3* des, byte* out, const byte* in,word32 sz);
WOLFSSL_API int  wc_Des3_CbcDecrypt(Des3* des, byte* out, const byte* in,word32 sz);
WOLFSSL_API int  wc_Des3_CbcDecryptWithKey(byte* out, const byte* in, word32 sz,
                                               const byte* key, const byte* iv);


#ifdef HAVE_CAVIUM
    WOLFSSL_API int  wc_Des3_InitCavium(Des3*, int);
    WOLFSSL_API void wc_Des3_FreeCavium(Des3*);
#endif

#ifdef __cplusplus
    } /* extern "C" */
#endif

#endif /* NO_DES3 */
#endif /* WOLF_CRYPT_DES3_H */

