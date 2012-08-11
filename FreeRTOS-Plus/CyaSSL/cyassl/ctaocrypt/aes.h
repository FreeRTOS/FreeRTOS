/* aes.h
 *
 * Copyright (C) 2006-2012 Sawtooth Consulting Ltd.
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
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA
 */


#ifndef NO_AES

#ifndef CTAO_CRYPT_AES_H
#define CTAO_CRYPT_AES_H


#include <cyassl/ctaocrypt/types.h>

#ifdef CYASSL_AESNI

#include <wmmintrin.h>

#if !defined (ALIGN16)
    #if defined (__GNUC__)
        #define ALIGN16 __attribute__ ( (aligned (16)))
    #elif defined(_MSC_VER)
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
} Aes;


CYASSL_API int  AesSetKey(Aes* aes, const byte* key, word32 len, const byte* iv,
                          int dir);
CYASSL_API int  AesSetIV(Aes* aes, const byte* iv);
CYASSL_API void AesCbcEncrypt(Aes* aes, byte* out, const byte* in, word32 sz);
CYASSL_API void AesCbcDecrypt(Aes* aes, byte* out, const byte* in, word32 sz);
CYASSL_API void AesCtrEncrypt(Aes* aes, byte* out, const byte* in, word32 sz);
CYASSL_API void AesEncryptDirect(Aes* aes, byte* out, const byte* in);
CYASSL_API void AesDecryptDirect(Aes* aes, byte* out, const byte* in);


#ifdef __cplusplus
    } /* extern "C" */
#endif


#endif /* CTAO_CRYPT_AES_H */
#endif /* NO_AES */

