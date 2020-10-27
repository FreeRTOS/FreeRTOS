/* aes.h
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



/*  aes.h defines mini des openssl compatibility layer
 *
 */


#ifndef WOLFSSL_AES_H_
#define WOLFSSL_AES_H_

#include <wolfssl/wolfcrypt/settings.h>

#ifndef NO_AES
#include <wolfssl/openssl/ssl.h> /* for size_t */

#ifdef __cplusplus
    extern "C" {
#endif

/* This structure wrapper is done because there is no aes_new function with
 * OpenSSL compatibility layer. This makes code working with an AES structure
 * to need the size of the structure. */
typedef struct WOLFSSL_AES_KEY {
    /* aligned and big enough for Aes from wolfssl/wolfcrypt/aes.h */
    ALIGN16 void* holder[(376 + WC_ASYNC_DEV_SIZE)/ sizeof(void*)];
    #ifdef GCM_TABLE
    /* key-based fast multiplication table. */
    ALIGN16 void* M0[4096 / sizeof(void*)];
    #endif /* GCM_TABLE */
    #if defined(WOLFSSL_DEVCRYPTO) && \
        (defined(WOLFSSL_DEVCRYPTO_AES) || defined(WOLFSSL_DEVCRYPTO_CBC))
    /* large enough for additional devcrypto information */
    void* devKey[288 / sizeof(void*)];
    #endif
    #ifdef WOLFSSL_AFALG
    void* afalg_holder[288 / sizeof(void*)];
    #endif
    #ifdef HAVE_PKCS11
    void* pkcs11_holder[(AES_MAX_ID_LEN + sizeof(int)) / sizeof(void*)];
    #endif
    #if defined(WOLFSSL_ASYNC_CRYPT) || defined(WOLF_CRYPTO_CB)
    void* async_holder[128 / sizeof(void*)];
    #endif
} WOLFSSL_AES_KEY;
typedef WOLFSSL_AES_KEY AES_KEY;

WOLFSSL_API int wolfSSL_AES_set_encrypt_key
    (const unsigned char *, const int bits, AES_KEY *);
WOLFSSL_API int wolfSSL_AES_set_decrypt_key
    (const unsigned char *, const int bits, AES_KEY *);
WOLFSSL_API void wolfSSL_AES_cbc_encrypt
    (const unsigned char *in, unsigned char* out, size_t len,
     AES_KEY *key, unsigned char* iv, const int enc);
WOLFSSL_API void wolfSSL_AES_ecb_encrypt
    (const unsigned char *in, unsigned char* out,
     AES_KEY *key, const int enc);
WOLFSSL_API void wolfSSL_AES_cfb128_encrypt
    (const unsigned char *in, unsigned char* out, size_t len,
     AES_KEY *key, unsigned char* iv, int* num, const int enc);

#define AES_cbc_encrypt     wolfSSL_AES_cbc_encrypt
#define AES_ecb_encrypt     wolfSSL_AES_ecb_encrypt
#define AES_cfb128_encrypt  wolfSSL_AES_cfb128_encrypt
#define AES_set_encrypt_key wolfSSL_AES_set_encrypt_key
#define AES_set_decrypt_key wolfSSL_AES_set_decrypt_key

#ifdef WOLFSSL_AES_DIRECT
WOLFSSL_API void wolfSSL_AES_encrypt
    (const unsigned char* input, unsigned char* output, AES_KEY *);
WOLFSSL_API void wolfSSL_AES_decrypt
    (const unsigned char* input, unsigned char* output, AES_KEY *);

#define AES_encrypt         wolfSSL_AES_encrypt
#define AES_decrypt         wolfSSL_AES_decrypt
#endif /* HAVE_AES_DIRECT */

#ifndef AES_ENCRYPT
#define AES_ENCRYPT AES_ENCRYPTION
#endif
#ifndef AES_DECRYPT
#define AES_DECRYPT AES_DECRYPTION
#endif

#ifdef __cplusplus
    } /* extern "C" */
#endif

#endif /* NO_AES */

#endif /* WOLFSSL_AES_H_ */
