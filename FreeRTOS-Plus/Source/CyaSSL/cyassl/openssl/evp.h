/* evp.h
 *
 * Copyright (C) 2013 wolfSSL Inc.
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


/*  evp.h defines mini evp openssl compatibility layer 
 *
 */


#ifndef CYASSL_EVP_H_
#define CYASSL_EVP_H_

#include <cyassl/ctaocrypt/settings.h>

#ifdef YASSL_PREFIX
#include "prefix_evp.h"
#endif

#include <cyassl/openssl/md5.h>
#include <cyassl/openssl/sha.h>
#include <cyassl/openssl/ripemd.h>
#include <cyassl/openssl/rsa.h>
#include <cyassl/openssl/dsa.h>

#include <cyassl/ctaocrypt/aes.h>
#include <cyassl/ctaocrypt/des3.h>
#include <cyassl/ctaocrypt/arc4.h>


#ifdef __cplusplus
    extern "C" {
#endif

typedef char CYASSL_EVP_MD;
typedef char CYASSL_EVP_CIPHER;

CYASSL_API const CYASSL_EVP_MD* CyaSSL_EVP_md5(void);
CYASSL_API const CYASSL_EVP_MD* CyaSSL_EVP_sha1(void);
CYASSL_API const CYASSL_EVP_MD* CyaSSL_EVP_sha256(void);
CYASSL_API const CYASSL_EVP_MD* CyaSSL_EVP_sha384(void);
CYASSL_API const CYASSL_EVP_MD* CyaSSL_EVP_sha512(void);
CYASSL_API const CYASSL_EVP_MD* CyaSSL_EVP_ripemd160(void);

CYASSL_API const CYASSL_EVP_CIPHER* CyaSSL_EVP_aes_128_cbc(void);
CYASSL_API const CYASSL_EVP_CIPHER* CyaSSL_EVP_aes_192_cbc(void);
CYASSL_API const CYASSL_EVP_CIPHER* CyaSSL_EVP_aes_256_cbc(void);
CYASSL_API const CYASSL_EVP_CIPHER* CyaSSL_EVP_aes_128_ctr(void);
CYASSL_API const CYASSL_EVP_CIPHER* CyaSSL_EVP_aes_192_ctr(void);
CYASSL_API const CYASSL_EVP_CIPHER* CyaSSL_EVP_aes_256_ctr(void);
CYASSL_API const CYASSL_EVP_CIPHER* CyaSSL_EVP_des_cbc(void);
CYASSL_API const CYASSL_EVP_CIPHER* CyaSSL_EVP_des_ede3_cbc(void);
CYASSL_API const CYASSL_EVP_CIPHER* CyaSSL_EVP_rc4(void);
CYASSL_API const CYASSL_EVP_CIPHER* CyaSSL_EVP_enc_null(void);


typedef union {
    CYASSL_MD5_CTX    md5;
    CYASSL_SHA_CTX    sha;
    CYASSL_SHA256_CTX sha256;
    #ifdef CYASSL_SHA384
        CYASSL_SHA384_CTX sha384;
    #endif
    #ifdef CYASSL_SHA512
        CYASSL_SHA512_CTX sha512;
    #endif
    #ifdef CYASSL_RIPEMD
        CYASSL_RIPEMD_CTX ripemd;
    #endif
} CYASSL_Hasher;


typedef struct CYASSL_EVP_MD_CTX {
    unsigned char macType;
    CYASSL_Hasher hash;
} CYASSL_EVP_MD_CTX;


typedef union {
    Aes  aes;
#ifndef NO_DES3
    Des  des;
    Des3 des3;
#endif
    Arc4 arc4;
} CYASSL_Cipher;


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


typedef struct CYASSL_EVP_CIPHER_CTX {
    int            keyLen;         /* user may set for variable */
    unsigned char  enc;            /* if encrypt side, then true */
    unsigned char  cipherType;
    unsigned char  iv[AES_BLOCK_SIZE];    /* working iv pointer into cipher */
    CYASSL_Cipher  cipher;
} CYASSL_EVP_CIPHER_CTX;


CYASSL_API int  CyaSSL_EVP_MD_size(const CYASSL_EVP_MD* md);
CYASSL_API void CyaSSL_EVP_MD_CTX_init(CYASSL_EVP_MD_CTX* ctx);
CYASSL_API int  CyaSSL_EVP_MD_CTX_cleanup(CYASSL_EVP_MD_CTX* ctx);

CYASSL_API int CyaSSL_EVP_DigestInit(CYASSL_EVP_MD_CTX* ctx,
                                     const CYASSL_EVP_MD* type);
CYASSL_API int CyaSSL_EVP_DigestUpdate(CYASSL_EVP_MD_CTX* ctx, const void* data,
                                       unsigned long sz);
CYASSL_API int CyaSSL_EVP_DigestFinal(CYASSL_EVP_MD_CTX* ctx, unsigned char* md,
                                      unsigned int* s);
CYASSL_API int CyaSSL_EVP_DigestFinal_ex(CYASSL_EVP_MD_CTX* ctx,
                                            unsigned char* md, unsigned int* s);
CYASSL_API int CyaSSL_EVP_BytesToKey(const CYASSL_EVP_CIPHER*,
                              const CYASSL_EVP_MD*, const unsigned char*,
                              const unsigned char*, int, int, unsigned char*,
                              unsigned char*);

CYASSL_API void CyaSSL_EVP_CIPHER_CTX_init(CYASSL_EVP_CIPHER_CTX* ctx);
CYASSL_API int  CyaSSL_EVP_CIPHER_CTX_cleanup(CYASSL_EVP_CIPHER_CTX* ctx);

CYASSL_API int  CyaSSL_EVP_CIPHER_CTX_iv_length(const CYASSL_EVP_CIPHER_CTX*);


CYASSL_API int  CyaSSL_EVP_CipherInit(CYASSL_EVP_CIPHER_CTX* ctx,
                                    const CYASSL_EVP_CIPHER* type,
                                    unsigned char* key, unsigned char* iv,
                                    int enc);
CYASSL_API int  CyaSSL_EVP_CIPHER_CTX_key_length(CYASSL_EVP_CIPHER_CTX* ctx);
CYASSL_API int  CyaSSL_EVP_CIPHER_CTX_set_key_length(CYASSL_EVP_CIPHER_CTX* ctx,
                                                     int keylen);
CYASSL_API int  CyaSSL_EVP_Cipher(CYASSL_EVP_CIPHER_CTX* ctx,
                          unsigned char* dst, unsigned char* src,
                          unsigned int len);

CYASSL_API const CYASSL_EVP_MD* CyaSSL_EVP_get_digestbynid(int);

CYASSL_API CYASSL_RSA* CyaSSL_EVP_PKEY_get1_RSA(CYASSL_EVP_PKEY*);
CYASSL_API CYASSL_DSA* CyaSSL_EVP_PKEY_get1_DSA(CYASSL_EVP_PKEY*);

/* these next ones don't need real OpenSSL type, for OpenSSH compat only */
CYASSL_API void* CyaSSL_EVP_X_STATE(const CYASSL_EVP_CIPHER_CTX* ctx);
CYASSL_API int   CyaSSL_EVP_X_STATE_LEN(const CYASSL_EVP_CIPHER_CTX* ctx);

CYASSL_API void  CyaSSL_3des_iv(CYASSL_EVP_CIPHER_CTX* ctx, int doset,
                                unsigned char* iv, int len);
CYASSL_API void  CyaSSL_aes_ctr_iv(CYASSL_EVP_CIPHER_CTX* ctx, int doset,
                                unsigned char* iv, int len);

CYASSL_API int  CyaSSL_StoreExternalIV(CYASSL_EVP_CIPHER_CTX* ctx);
CYASSL_API int  CyaSSL_SetInternalIV(CYASSL_EVP_CIPHER_CTX* ctx);


/* end OpenSSH compat */

typedef CYASSL_EVP_MD         EVP_MD;
typedef CYASSL_EVP_CIPHER     EVP_CIPHER;
typedef CYASSL_EVP_MD_CTX     EVP_MD_CTX;
typedef CYASSL_EVP_CIPHER_CTX EVP_CIPHER_CTX;

#define EVP_md5       CyaSSL_EVP_md5
#define EVP_sha1      CyaSSL_EVP_sha1
#define EVP_sha256    CyaSSL_EVP_sha256
#define EVP_sha384    CyaSSL_EVP_sha384
#define EVP_sha512    CyaSSL_EVP_sha512
#define EVP_ripemd160 CyaSSL_EVP_ripemd160

#define EVP_aes_128_cbc  CyaSSL_EVP_aes_128_cbc
#define EVP_aes_192_cbc  CyaSSL_EVP_aes_192_cbc
#define EVP_aes_256_cbc  CyaSSL_EVP_aes_256_cbc
#define EVP_aes_128_ctr  CyaSSL_EVP_aes_128_ctr
#define EVP_aes_192_ctr  CyaSSL_EVP_aes_192_ctr
#define EVP_aes_256_ctr  CyaSSL_EVP_aes_256_ctr
#define EVP_des_cbc      CyaSSL_EVP_des_cbc
#define EVP_des_ede3_cbc CyaSSL_EVP_des_ede3_cbc
#define EVP_rc4          CyaSSL_EVP_rc4
#define EVP_enc_null     CyaSSL_EVP_enc_null

#define EVP_MD_size        CyaSSL_EVP_MD_size
#define EVP_MD_CTX_init    CyaSSL_EVP_MD_CTX_init
#define EVP_MD_CTX_cleanup CyaSSL_EVP_MD_CTX_cleanup
#define EVP_DigestInit     CyaSSL_EVP_DigestInit
#define EVP_DigestUpdate   CyaSSL_EVP_DigestUpdate
#define EVP_DigestFinal    CyaSSL_EVP_DigestFinal
#define EVP_DigestFinal_ex CyaSSL_EVP_DigestFinal_ex
#define EVP_BytesToKey     CyaSSL_EVP_BytesToKey

#define EVP_CIPHER_CTX_init           CyaSSL_EVP_CIPHER_CTX_init
#define EVP_CIPHER_CTX_cleanup        CyaSSL_EVP_CIPHER_CTX_cleanup
#define EVP_CIPHER_CTX_iv_length      CyaSSL_EVP_CIPHER_CTX_iv_length
#define EVP_CIPHER_CTX_key_length     CyaSSL_EVP_CIPHER_CTX_key_length
#define EVP_CIPHER_CTX_set_key_length CyaSSL_EVP_CIPHER_CTX_set_key_length
#define EVP_CipherInit                CyaSSL_EVP_CipherInit
#define EVP_Cipher                    CyaSSL_EVP_Cipher

#define EVP_get_digestbynid           CyaSSL_EVP_get_digestbynid

#define EVP_PKEY_get1_RSA   CyaSSL_EVP_PKEY_get1_RSA
#define EVP_PKEY_get1_DSA   CyaSSL_EVP_PKEY_get1_DSA

#ifndef EVP_MAX_MD_SIZE
    #define EVP_MAX_MD_SIZE   64     /* sha512 */
#endif

#ifdef __cplusplus
    } /* extern "C" */
#endif


#endif /* CYASSL_EVP_H_ */
