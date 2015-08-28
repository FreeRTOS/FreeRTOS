/* evp.h
 *
 * Copyright (C) 2015 wolfSSL Inc.
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


/*  evp.h defines mini evp openssl compatibility layer 
 *
 */


#ifndef WOLFSSL_EVP_H_
#define WOLFSSL_EVP_H_

#include <wolfssl/wolfcrypt/settings.h>

#ifdef WOLFSSL_PREFIX
#include "prefix_evp.h"
#endif

#ifndef NO_MD5
    #include <wolfssl/openssl/md5.h>
#endif
#include <wolfssl/openssl/sha.h>
#include <wolfssl/openssl/ripemd.h>
#include <wolfssl/openssl/rsa.h>
#include <wolfssl/openssl/dsa.h>

#include <wolfssl/wolfcrypt/aes.h>
#include <wolfssl/wolfcrypt/des3.h>
#include <wolfssl/wolfcrypt/arc4.h>


#ifdef __cplusplus
    extern "C" {
#endif

typedef char WOLFSSL_EVP_MD;
typedef char WOLFSSL_EVP_CIPHER;

#ifndef NO_MD5
    WOLFSSL_API const WOLFSSL_EVP_MD* wolfSSL_EVP_md5(void);
#endif
WOLFSSL_API const WOLFSSL_EVP_MD* wolfSSL_EVP_sha1(void);
WOLFSSL_API const WOLFSSL_EVP_MD* wolfSSL_EVP_sha256(void);
WOLFSSL_API const WOLFSSL_EVP_MD* wolfSSL_EVP_sha384(void);
WOLFSSL_API const WOLFSSL_EVP_MD* wolfSSL_EVP_sha512(void);
WOLFSSL_API const WOLFSSL_EVP_MD* wolfSSL_EVP_ripemd160(void);

WOLFSSL_API const WOLFSSL_EVP_CIPHER* wolfSSL_EVP_aes_128_cbc(void);
WOLFSSL_API const WOLFSSL_EVP_CIPHER* wolfSSL_EVP_aes_192_cbc(void);
WOLFSSL_API const WOLFSSL_EVP_CIPHER* wolfSSL_EVP_aes_256_cbc(void);
WOLFSSL_API const WOLFSSL_EVP_CIPHER* wolfSSL_EVP_aes_128_ctr(void);
WOLFSSL_API const WOLFSSL_EVP_CIPHER* wolfSSL_EVP_aes_192_ctr(void);
WOLFSSL_API const WOLFSSL_EVP_CIPHER* wolfSSL_EVP_aes_256_ctr(void);
WOLFSSL_API const WOLFSSL_EVP_CIPHER* wolfSSL_EVP_des_cbc(void);
WOLFSSL_API const WOLFSSL_EVP_CIPHER* wolfSSL_EVP_des_ede3_cbc(void);
WOLFSSL_API const WOLFSSL_EVP_CIPHER* wolfSSL_EVP_rc4(void);
WOLFSSL_API const WOLFSSL_EVP_CIPHER* wolfSSL_EVP_enc_null(void);


typedef union {
    #ifndef NO_MD5
        WOLFSSL_MD5_CTX    md5;
    #endif
    WOLFSSL_SHA_CTX    sha;
    WOLFSSL_SHA256_CTX sha256;
    #ifdef WOLFSSL_SHA384
        WOLFSSL_SHA384_CTX sha384;
    #endif
    #ifdef WOLFSSL_SHA512
        WOLFSSL_SHA512_CTX sha512;
    #endif
    #ifdef WOLFSSL_RIPEMD
        WOLFSSL_RIPEMD_CTX ripemd;
    #endif
} WOLFSSL_Hasher;


typedef struct WOLFSSL_EVP_MD_CTX {
    unsigned char macType;
    WOLFSSL_Hasher hash;
} WOLFSSL_EVP_MD_CTX;


typedef union {
#ifndef NO_AES
    Aes  aes;
#endif
#ifndef NO_DES3
    Des  des;
    Des3 des3;
#endif
    Arc4 arc4;
} WOLFSSL_Cipher;


enum {
    AES_128_CBC_TYPE  = 1,
    AES_192_CBC_TYPE  = 2,
    AES_256_CBC_TYPE  = 3,
    AES_128_CTR_TYPE  = 4,
    AES_192_CTR_TYPE  = 5,
    AES_256_CTR_TYPE  = 6,
    DES_CBC_TYPE      = 7,
    DES_EDE3_CBC_TYPE = 8,
    ARC4_TYPE         = 9,
    NULL_CIPHER_TYPE  = 10,
    EVP_PKEY_RSA      = 11,
    EVP_PKEY_DSA      = 12,
    NID_sha1          = 64,
    NID_md5           =  4
};


typedef struct WOLFSSL_EVP_CIPHER_CTX {
    int            keyLen;         /* user may set for variable */
    unsigned char  enc;            /* if encrypt side, then true */
    unsigned char  cipherType;
#ifndef NO_AES
    unsigned char  iv[AES_BLOCK_SIZE];    /* working iv pointer into cipher */
#elif !defined(NO_DES3)
    unsigned char  iv[DES_BLOCK_SIZE];    /* working iv pointer into cipher */
#endif
    WOLFSSL_Cipher  cipher;
} WOLFSSL_EVP_CIPHER_CTX;


WOLFSSL_API int  wolfSSL_EVP_MD_size(const WOLFSSL_EVP_MD* md);
WOLFSSL_API void wolfSSL_EVP_MD_CTX_init(WOLFSSL_EVP_MD_CTX* ctx);
WOLFSSL_API int  wolfSSL_EVP_MD_CTX_cleanup(WOLFSSL_EVP_MD_CTX* ctx);

WOLFSSL_API int wolfSSL_EVP_DigestInit(WOLFSSL_EVP_MD_CTX* ctx,
                                     const WOLFSSL_EVP_MD* type);
WOLFSSL_API int wolfSSL_EVP_DigestUpdate(WOLFSSL_EVP_MD_CTX* ctx, const void* data,
                                       unsigned long sz);
WOLFSSL_API int wolfSSL_EVP_DigestFinal(WOLFSSL_EVP_MD_CTX* ctx, unsigned char* md,
                                      unsigned int* s);
WOLFSSL_API int wolfSSL_EVP_DigestFinal_ex(WOLFSSL_EVP_MD_CTX* ctx,
                                            unsigned char* md, unsigned int* s);
#ifndef NO_MD5
WOLFSSL_API int wolfSSL_EVP_BytesToKey(const WOLFSSL_EVP_CIPHER*,
                              const WOLFSSL_EVP_MD*, const unsigned char*,
                              const unsigned char*, int, int, unsigned char*,
                              unsigned char*);
#endif

WOLFSSL_API void wolfSSL_EVP_CIPHER_CTX_init(WOLFSSL_EVP_CIPHER_CTX* ctx);
WOLFSSL_API int  wolfSSL_EVP_CIPHER_CTX_cleanup(WOLFSSL_EVP_CIPHER_CTX* ctx);

WOLFSSL_API int  wolfSSL_EVP_CIPHER_CTX_iv_length(const WOLFSSL_EVP_CIPHER_CTX*);


WOLFSSL_API int  wolfSSL_EVP_CipherInit(WOLFSSL_EVP_CIPHER_CTX* ctx,
                                    const WOLFSSL_EVP_CIPHER* type,
                                    unsigned char* key, unsigned char* iv,
                                    int enc);
WOLFSSL_API int  wolfSSL_EVP_CIPHER_CTX_key_length(WOLFSSL_EVP_CIPHER_CTX* ctx);
WOLFSSL_API int  wolfSSL_EVP_CIPHER_CTX_set_key_length(WOLFSSL_EVP_CIPHER_CTX* ctx,
                                                     int keylen);
WOLFSSL_API int  wolfSSL_EVP_Cipher(WOLFSSL_EVP_CIPHER_CTX* ctx,
                          unsigned char* dst, unsigned char* src,
                          unsigned int len);

WOLFSSL_API const WOLFSSL_EVP_MD* wolfSSL_EVP_get_digestbynid(int);

WOLFSSL_API WOLFSSL_RSA* wolfSSL_EVP_PKEY_get1_RSA(WOLFSSL_EVP_PKEY*);
WOLFSSL_API WOLFSSL_DSA* wolfSSL_EVP_PKEY_get1_DSA(WOLFSSL_EVP_PKEY*);

/* these next ones don't need real OpenSSL type, for OpenSSH compat only */
WOLFSSL_API void* wolfSSL_EVP_X_STATE(const WOLFSSL_EVP_CIPHER_CTX* ctx);
WOLFSSL_API int   wolfSSL_EVP_X_STATE_LEN(const WOLFSSL_EVP_CIPHER_CTX* ctx);

WOLFSSL_API void  wolfSSL_3des_iv(WOLFSSL_EVP_CIPHER_CTX* ctx, int doset,
                                unsigned char* iv, int len);
WOLFSSL_API void  wolfSSL_aes_ctr_iv(WOLFSSL_EVP_CIPHER_CTX* ctx, int doset,
                                unsigned char* iv, int len);

WOLFSSL_API int  wolfSSL_StoreExternalIV(WOLFSSL_EVP_CIPHER_CTX* ctx);
WOLFSSL_API int  wolfSSL_SetInternalIV(WOLFSSL_EVP_CIPHER_CTX* ctx);


/* end OpenSSH compat */

typedef WOLFSSL_EVP_MD         EVP_MD;
typedef WOLFSSL_EVP_CIPHER     EVP_CIPHER;
typedef WOLFSSL_EVP_MD_CTX     EVP_MD_CTX;
typedef WOLFSSL_EVP_CIPHER_CTX EVP_CIPHER_CTX;

#ifndef NO_MD5
    #define EVP_md5       wolfSSL_EVP_md5
#endif
#define EVP_sha1      wolfSSL_EVP_sha1
#define EVP_sha256    wolfSSL_EVP_sha256
#define EVP_sha384    wolfSSL_EVP_sha384
#define EVP_sha512    wolfSSL_EVP_sha512
#define EVP_ripemd160 wolfSSL_EVP_ripemd160

#define EVP_aes_128_cbc  wolfSSL_EVP_aes_128_cbc
#define EVP_aes_192_cbc  wolfSSL_EVP_aes_192_cbc
#define EVP_aes_256_cbc  wolfSSL_EVP_aes_256_cbc
#define EVP_aes_128_ctr  wolfSSL_EVP_aes_128_ctr
#define EVP_aes_192_ctr  wolfSSL_EVP_aes_192_ctr
#define EVP_aes_256_ctr  wolfSSL_EVP_aes_256_ctr
#define EVP_des_cbc      wolfSSL_EVP_des_cbc
#define EVP_des_ede3_cbc wolfSSL_EVP_des_ede3_cbc
#define EVP_rc4          wolfSSL_EVP_rc4
#define EVP_enc_null     wolfSSL_EVP_enc_null

#define EVP_MD_size        wolfSSL_EVP_MD_size
#define EVP_MD_CTX_init    wolfSSL_EVP_MD_CTX_init
#define EVP_MD_CTX_cleanup wolfSSL_EVP_MD_CTX_cleanup
#define EVP_DigestInit     wolfSSL_EVP_DigestInit
#define EVP_DigestUpdate   wolfSSL_EVP_DigestUpdate
#define EVP_DigestFinal    wolfSSL_EVP_DigestFinal
#define EVP_DigestFinal_ex wolfSSL_EVP_DigestFinal_ex
#define EVP_BytesToKey     wolfSSL_EVP_BytesToKey

#define EVP_CIPHER_CTX_init           wolfSSL_EVP_CIPHER_CTX_init
#define EVP_CIPHER_CTX_cleanup        wolfSSL_EVP_CIPHER_CTX_cleanup
#define EVP_CIPHER_CTX_iv_length      wolfSSL_EVP_CIPHER_CTX_iv_length
#define EVP_CIPHER_CTX_key_length     wolfSSL_EVP_CIPHER_CTX_key_length
#define EVP_CIPHER_CTX_set_key_length wolfSSL_EVP_CIPHER_CTX_set_key_length
#define EVP_CipherInit                wolfSSL_EVP_CipherInit
#define EVP_Cipher                    wolfSSL_EVP_Cipher

#define EVP_get_digestbynid           wolfSSL_EVP_get_digestbynid

#define EVP_PKEY_get1_RSA   wolfSSL_EVP_PKEY_get1_RSA
#define EVP_PKEY_get1_DSA   wolfSSL_EVP_PKEY_get1_DSA

#ifndef EVP_MAX_MD_SIZE
    #define EVP_MAX_MD_SIZE   64     /* sha512 */
#endif

#ifdef __cplusplus
    } /* extern "C" */
#endif


#endif /* WOLFSSL_EVP_H_ */
