/* evp.h
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
    \file wolfssl/openssl/evp.h
    \brief evp.h defines mini evp openssl compatibility layer
 */


#ifndef WOLFSSL_EVP_H_
#define WOLFSSL_EVP_H_

#include <wolfssl/wolfcrypt/settings.h>

#ifdef WOLFSSL_PREFIX
#include "prefix_evp.h"
#endif

#ifndef NO_MD4
    #include <wolfssl/openssl/md4.h>
#endif
#ifndef NO_MD5
    #include <wolfssl/openssl/md5.h>
#endif
#include <wolfssl/openssl/sha.h>
#include <wolfssl/openssl/sha3.h>
#include <wolfssl/openssl/ripemd.h>
#include <wolfssl/openssl/rsa.h>
#include <wolfssl/openssl/dsa.h>
#include <wolfssl/openssl/ec.h>
#include <wolfssl/openssl/dh.h>

#include <wolfssl/wolfcrypt/aes.h>
#include <wolfssl/wolfcrypt/des3.h>
#include <wolfssl/wolfcrypt/arc4.h>
#include <wolfssl/wolfcrypt/hmac.h>
#ifdef HAVE_IDEA
    #include <wolfssl/wolfcrypt/idea.h>
#endif
#include <wolfssl/wolfcrypt/pwdbased.h>

#ifdef __cplusplus
    extern "C" {
#endif


typedef char WOLFSSL_EVP_CIPHER;
#ifndef WOLFSSL_EVP_TYPE_DEFINED /* guard on redeclaration */
typedef char   WOLFSSL_EVP_MD;
typedef struct WOLFSSL_EVP_PKEY     WOLFSSL_EVP_PKEY;
typedef struct WOLFSSL_EVP_MD_CTX   WOLFSSL_EVP_MD_CTX;
#define WOLFSSL_EVP_TYPE_DEFINED
#endif

typedef WOLFSSL_EVP_PKEY       EVP_PKEY;
typedef WOLFSSL_EVP_PKEY       PKCS8_PRIV_KEY_INFO;

#ifndef NO_MD4
    WOLFSSL_API const WOLFSSL_EVP_MD* wolfSSL_EVP_md4(void);
#endif
#ifndef NO_MD5
    WOLFSSL_API const WOLFSSL_EVP_MD* wolfSSL_EVP_md5(void);
#endif
WOLFSSL_API const WOLFSSL_EVP_MD* wolfSSL_EVP_mdc2(void);
WOLFSSL_API const WOLFSSL_EVP_MD* wolfSSL_EVP_sha1(void);
WOLFSSL_API const WOLFSSL_EVP_MD* wolfSSL_EVP_sha224(void);
WOLFSSL_API const WOLFSSL_EVP_MD* wolfSSL_EVP_sha256(void);
WOLFSSL_API const WOLFSSL_EVP_MD* wolfSSL_EVP_sha384(void);
WOLFSSL_API const WOLFSSL_EVP_MD* wolfSSL_EVP_sha512(void);
WOLFSSL_API const WOLFSSL_EVP_MD* wolfSSL_EVP_ripemd160(void);

WOLFSSL_API const WOLFSSL_EVP_MD* wolfSSL_EVP_sha3_224(void);
WOLFSSL_API const WOLFSSL_EVP_MD* wolfSSL_EVP_sha3_256(void);
WOLFSSL_API const WOLFSSL_EVP_MD* wolfSSL_EVP_sha3_384(void);
WOLFSSL_API const WOLFSSL_EVP_MD* wolfSSL_EVP_sha3_512(void);

WOLFSSL_API const WOLFSSL_EVP_CIPHER* wolfSSL_EVP_aes_128_ecb(void);
WOLFSSL_API const WOLFSSL_EVP_CIPHER* wolfSSL_EVP_aes_192_ecb(void);
WOLFSSL_API const WOLFSSL_EVP_CIPHER* wolfSSL_EVP_aes_256_ecb(void);
WOLFSSL_API const WOLFSSL_EVP_CIPHER* wolfSSL_EVP_aes_128_cbc(void);
#if !defined(NO_AES) && defined(HAVE_AES_CBC)
WOLFSSL_API const WOLFSSL_EVP_CIPHER* wolfSSL_EVP_aes_192_cbc(void);
WOLFSSL_API const WOLFSSL_EVP_CIPHER* wolfSSL_EVP_aes_256_cbc(void);
#endif
#ifndef NO_AES
#ifdef WOLFSSL_AES_CFB
WOLFSSL_API const WOLFSSL_EVP_CIPHER* wolfSSL_EVP_aes_128_cfb1(void);
WOLFSSL_API const WOLFSSL_EVP_CIPHER* wolfSSL_EVP_aes_192_cfb1(void);
WOLFSSL_API const WOLFSSL_EVP_CIPHER* wolfSSL_EVP_aes_256_cfb1(void);
WOLFSSL_API const WOLFSSL_EVP_CIPHER* wolfSSL_EVP_aes_128_cfb8(void);
WOLFSSL_API const WOLFSSL_EVP_CIPHER* wolfSSL_EVP_aes_192_cfb8(void);
WOLFSSL_API const WOLFSSL_EVP_CIPHER* wolfSSL_EVP_aes_256_cfb8(void);
WOLFSSL_API const WOLFSSL_EVP_CIPHER* wolfSSL_EVP_aes_128_cfb128(void);
WOLFSSL_API const WOLFSSL_EVP_CIPHER* wolfSSL_EVP_aes_192_cfb128(void);
WOLFSSL_API const WOLFSSL_EVP_CIPHER* wolfSSL_EVP_aes_256_cfb128(void);
#endif
#ifdef WOLFSSL_AES_OFB
WOLFSSL_API const WOLFSSL_EVP_CIPHER* wolfSSL_EVP_aes_128_ofb(void);
WOLFSSL_API const WOLFSSL_EVP_CIPHER* wolfSSL_EVP_aes_192_ofb(void);
WOLFSSL_API const WOLFSSL_EVP_CIPHER* wolfSSL_EVP_aes_256_ofb(void);
#endif
#ifdef WOLFSSL_AES_XTS
WOLFSSL_API const WOLFSSL_EVP_CIPHER* wolfSSL_EVP_aes_128_xts(void);
WOLFSSL_API const WOLFSSL_EVP_CIPHER* wolfSSL_EVP_aes_256_xts(void);
#endif
#endif /* NO_AES */
#if !defined(NO_AES) && defined(HAVE_AESGCM)
WOLFSSL_API const WOLFSSL_EVP_CIPHER* wolfSSL_EVP_aes_128_gcm(void);
WOLFSSL_API const WOLFSSL_EVP_CIPHER* wolfSSL_EVP_aes_192_gcm(void);
WOLFSSL_API const WOLFSSL_EVP_CIPHER* wolfSSL_EVP_aes_256_gcm(void);
#endif
WOLFSSL_API const WOLFSSL_EVP_CIPHER* wolfSSL_EVP_aes_128_ctr(void);
WOLFSSL_API const WOLFSSL_EVP_CIPHER* wolfSSL_EVP_aes_192_ctr(void);
WOLFSSL_API const WOLFSSL_EVP_CIPHER* wolfSSL_EVP_aes_256_ctr(void);
WOLFSSL_API const WOLFSSL_EVP_CIPHER* wolfSSL_EVP_des_ecb(void);
WOLFSSL_API const WOLFSSL_EVP_CIPHER* wolfSSL_EVP_des_ede3_ecb(void);
WOLFSSL_API const WOLFSSL_EVP_CIPHER* wolfSSL_EVP_des_cbc(void);
WOLFSSL_API const WOLFSSL_EVP_CIPHER* wolfSSL_EVP_des_ede3_cbc(void);
WOLFSSL_API const WOLFSSL_EVP_CIPHER* wolfSSL_EVP_rc4(void);
WOLFSSL_API const WOLFSSL_EVP_CIPHER* wolfSSL_EVP_idea_cbc(void);
WOLFSSL_API const WOLFSSL_EVP_CIPHER* wolfSSL_EVP_enc_null(void);
WOLFSSL_API const WOLFSSL_EVP_CIPHER* wolfSSL_EVP_rc2_cbc(void);


typedef union {
    #ifndef NO_MD4
        WOLFSSL_MD4_CTX    md4;
    #endif
    #ifndef NO_MD5
        WOLFSSL_MD5_CTX    md5;
    #endif
    WOLFSSL_SHA_CTX    sha;
    #ifdef WOLFSSL_SHA224
        WOLFSSL_SHA224_CTX sha224;
    #endif
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
    #ifndef WOLFSSL_NOSHA3_224
        WOLFSSL_SHA3_224_CTX sha3_224;
    #endif
    #ifndef WOLFSSL_NOSHA3_256
        WOLFSSL_SHA3_256_CTX sha3_256;
    #endif
        WOLFSSL_SHA3_384_CTX sha3_384;
    #ifndef WOLFSSL_NOSHA3_512
        WOLFSSL_SHA3_512_CTX sha3_512;
    #endif
} WOLFSSL_Hasher;

typedef struct WOLFSSL_EVP_PKEY_CTX WOLFSSL_EVP_PKEY_CTX;
typedef struct WOLFSSL_EVP_CIPHER_CTX WOLFSSL_EVP_CIPHER_CTX;

struct WOLFSSL_EVP_MD_CTX {
    union {
        WOLFSSL_Hasher digest;
    #ifndef NO_HMAC
        Hmac hmac;
    #endif
    } hash;
    enum wc_HashType macType;
    WOLFSSL_EVP_PKEY_CTX *pctx;
#ifndef NO_HMAC
    unsigned int isHMAC;
#endif
};


typedef union {
#ifndef NO_AES
    Aes  aes;
#ifdef WOLFSSL_AES_XTS
    XtsAes xts;
#endif
#endif
#ifndef NO_DES3
    Des  des;
    Des3 des3;
#endif
    Arc4 arc4;
#ifdef HAVE_IDEA
    Idea idea;
#endif
#ifdef WOLFSSL_QT
    int (*ctrl) (WOLFSSL_EVP_CIPHER_CTX *, int type, int arg, void *ptr);
#endif
} WOLFSSL_Cipher;


enum {
    AES_128_CBC_TYPE  = 1,
    AES_192_CBC_TYPE  = 2,
    AES_256_CBC_TYPE  = 3,
    AES_128_CTR_TYPE  = 4,
    AES_192_CTR_TYPE  = 5,
    AES_256_CTR_TYPE  = 6,
    AES_128_ECB_TYPE  = 7,
    AES_192_ECB_TYPE  = 8,
    AES_256_ECB_TYPE  = 9,
    DES_CBC_TYPE      = 10,
    DES_ECB_TYPE      = 11,
    DES_EDE3_CBC_TYPE = 12,
    DES_EDE3_ECB_TYPE = 13,
    ARC4_TYPE         = 14,
    NULL_CIPHER_TYPE  = 15,
    EVP_PKEY_RSA      = 16,
    EVP_PKEY_DSA      = 17,
    EVP_PKEY_EC       = 18,
#ifdef HAVE_IDEA
    IDEA_CBC_TYPE     = 19,
#endif
    AES_128_GCM_TYPE  = 21,
    AES_192_GCM_TYPE  = 22,
    AES_256_GCM_TYPE  = 23,
    NID_sha1          = 64,
    NID_sha224        = 65,
    NID_md2           = 77,
    NID_md4           = 257,
    NID_md5           =  4,
    NID_hmac          = 855,
    NID_dhKeyAgreement= 28,
    EVP_PKEY_DH       = NID_dhKeyAgreement,
    EVP_PKEY_HMAC     = NID_hmac,
    AES_128_CFB1_TYPE = 24,
    AES_192_CFB1_TYPE = 25,
    AES_256_CFB1_TYPE = 26,
    AES_128_CFB8_TYPE = 27,
    AES_192_CFB8_TYPE = 28,
    AES_256_CFB8_TYPE = 29,
    AES_128_CFB128_TYPE = 30,
    AES_192_CFB128_TYPE = 31,
    AES_256_CFB128_TYPE = 32,
    AES_128_OFB_TYPE = 33,
    AES_192_OFB_TYPE = 34,
    AES_256_OFB_TYPE = 35,
    AES_128_XTS_TYPE = 36,
    AES_256_XTS_TYPE = 37
};

enum {
    NID_md5WithRSA    = 104,
    NID_md5WithRSAEncryption = 8,
    NID_dsaWithSHA1   = 113,
    NID_dsaWithSHA1_2 = 70,
    NID_sha1WithRSA   = 115,
    NID_sha1WithRSAEncryption = 65,
    NID_sha224WithRSAEncryption = 671,
    NID_sha256WithRSAEncryption = 668,
    NID_sha384WithRSAEncryption = 669,
    NID_sha512WithRSAEncryption = 670,
    NID_ecdsa_with_SHA1 = 416,
    NID_ecdsa_with_SHA224 = 793,
    NID_ecdsa_with_SHA256 = 794,
    NID_ecdsa_with_SHA384 = 795,
    NID_ecdsa_with_SHA512 = 796,
    NID_dsa_with_SHA224 = 802,
    NID_dsa_with_SHA256 = 803,
    NID_sha3_224        = 1096,
    NID_sha3_256        = 1097,
    NID_sha3_384        = 1098,
    NID_sha3_512        = 1099,
};

enum {
    NID_aes_128_cbc = 419,
    NID_aes_192_cbc = 423,
    NID_aes_256_cbc = 427,
    NID_aes_128_gcm = 895,
    NID_aes_192_gcm = 898,
    NID_aes_256_gcm = 901,
    NID_aes_128_ctr = 904,
    NID_aes_192_ctr = 905,
    NID_aes_256_ctr = 906,
    NID_aes_128_ecb = 418,
    NID_aes_192_ecb = 422,
    NID_aes_256_ecb = 426,
    NID_des_cbc     =  31,
    NID_des_ecb     =  29,
    NID_des_ede3_cbc=  44,
    NID_des_ede3_ecb=  33,
    NID_idea_cbc    =  34,
    NID_aes_128_cfb1= 650,
    NID_aes_192_cfb1= 651,
    NID_aes_256_cfb1= 652,
    NID_aes_128_cfb8= 653,
    NID_aes_192_cfb8= 654,
    NID_aes_256_cfb8= 655,
    NID_aes_128_cfb128 = 421,
    NID_aes_192_cfb128 = 425,
    NID_aes_256_cfb128 = 429,
    NID_aes_128_ofb = 420,
    NID_aes_192_ofb = 424,
    NID_aes_256_ofb = 428,
    NID_aes_128_xts = 913,
    NID_aes_256_xts = 914
};

#define NID_X9_62_id_ecPublicKey EVP_PKEY_EC
#define NID_dhKeyAgreement       EVP_PKEY_DH
#define NID_rsaEncryption        EVP_PKEY_RSA
#define NID_dsa                  EVP_PKEY_DSA

#define WOLFSSL_EVP_BUF_SIZE 16
struct WOLFSSL_EVP_CIPHER_CTX {
    int            keyLen;         /* user may set for variable */
    int            block_size;
    unsigned long  flags;
    unsigned char  enc;            /* if encrypt side, then true */
    unsigned char  cipherType;
#ifndef NO_AES
    /* working iv pointer into cipher */
    ALIGN16 unsigned char  iv[AES_BLOCK_SIZE];
#elif !defined(NO_DES3)
    /* working iv pointer into cipher */
    ALIGN16 unsigned char  iv[DES_BLOCK_SIZE];
#elif defined(HAVE_IDEA)
    /* working iv pointer into cipher */
    ALIGN16 unsigned char  iv[IDEA_BLOCK_SIZE];
#endif
    WOLFSSL_Cipher  cipher;
    ALIGN16 byte buf[WOLFSSL_EVP_BUF_SIZE];
    int  bufUsed;
    ALIGN16 byte lastBlock[WOLFSSL_EVP_BUF_SIZE];
    int  lastUsed;
#if !defined(NO_AES) || !defined(NO_DES3) || defined(HAVE_IDEA) || \
    defined(HAVE_AESGCM) || defined (WOLFSSL_AES_XTS)
#define HAVE_WOLFSSL_EVP_CIPHER_CTX_IV
    int    ivSz;
#ifdef HAVE_AESGCM
    byte*   gcmDecryptBuffer;
    int     gcmDecryptBufferLen;
    ALIGN16 unsigned char authTag[AES_BLOCK_SIZE];
    int     authTagSz;
#endif
#endif
};

struct WOLFSSL_EVP_PKEY_CTX {
    WOLFSSL_EVP_PKEY *pkey;
    WOLFSSL_EVP_PKEY *peerKey;
    int op; /* operation */
    int padding;
    int nbits;
};

typedef int WOLFSSL_ENGINE  ;
typedef WOLFSSL_ENGINE ENGINE;
typedef WOLFSSL_EVP_PKEY_CTX EVP_PKEY_CTX;

#define EVP_PKEY_OP_SIGN    (1 << 3)
#define EVP_PKEY_OP_ENCRYPT (1 << 6)
#define EVP_PKEY_OP_DECRYPT (1 << 7)
#define EVP_PKEY_OP_DERIVE  (1 << 8)

WOLFSSL_API void wolfSSL_EVP_init(void);
WOLFSSL_API int  wolfSSL_EVP_MD_size(const WOLFSSL_EVP_MD* md);
WOLFSSL_API int  wolfSSL_EVP_MD_type(const WOLFSSL_EVP_MD *md);
WOLFSSL_API int  wolfSSL_EVP_MD_block_size(const WOLFSSL_EVP_MD *md);

WOLFSSL_API WOLFSSL_EVP_MD_CTX *wolfSSL_EVP_MD_CTX_new (void);
WOLFSSL_API void                wolfSSL_EVP_MD_CTX_free(WOLFSSL_EVP_MD_CTX* ctx);
WOLFSSL_API void wolfSSL_EVP_MD_CTX_init(WOLFSSL_EVP_MD_CTX* ctx);
WOLFSSL_API int  wolfSSL_EVP_MD_CTX_cleanup(WOLFSSL_EVP_MD_CTX* ctx);
WOLFSSL_API int  wolfSSL_EVP_MD_CTX_copy(WOLFSSL_EVP_MD_CTX *out, const WOLFSSL_EVP_MD_CTX *in);
WOLFSSL_API int  wolfSSL_EVP_MD_CTX_copy_ex(WOLFSSL_EVP_MD_CTX *out, const WOLFSSL_EVP_MD_CTX *in);
WOLFSSL_API int  wolfSSL_EVP_MD_CTX_type(const WOLFSSL_EVP_MD_CTX *ctx);
WOLFSSL_API int  wolfSSL_EVP_MD_CTX_size(const WOLFSSL_EVP_MD_CTX *ctx);
WOLFSSL_API int  wolfSSL_EVP_MD_CTX_block_size(const WOLFSSL_EVP_MD_CTX *ctx);
WOLFSSL_API const WOLFSSL_EVP_MD *wolfSSL_EVP_MD_CTX_md(const WOLFSSL_EVP_MD_CTX *ctx);
WOLFSSL_API const WOLFSSL_EVP_CIPHER *wolfSSL_EVP_get_cipherbyname(const char *name);
WOLFSSL_API const WOLFSSL_EVP_MD     *wolfSSL_EVP_get_digestbyname(const char *name);
WOLFSSL_API int wolfSSL_EVP_CIPHER_nid(const WOLFSSL_EVP_CIPHER *cipher);

WOLFSSL_API int wolfSSL_EVP_DigestInit(WOLFSSL_EVP_MD_CTX* ctx,
                                     const WOLFSSL_EVP_MD* type);
WOLFSSL_API int wolfSSL_EVP_DigestInit_ex(WOLFSSL_EVP_MD_CTX* ctx,
                                     const WOLFSSL_EVP_MD* type,
                                     WOLFSSL_ENGINE *impl);
WOLFSSL_API int wolfSSL_EVP_DigestUpdate(WOLFSSL_EVP_MD_CTX* ctx, const void* data,
                                       size_t sz);
WOLFSSL_API int wolfSSL_EVP_DigestFinal(WOLFSSL_EVP_MD_CTX* ctx, unsigned char* md,
                                      unsigned int* s);
WOLFSSL_API int wolfSSL_EVP_DigestFinal_ex(WOLFSSL_EVP_MD_CTX* ctx,
                                            unsigned char* md, unsigned int* s);

WOLFSSL_API int wolfSSL_EVP_DigestSignInit(WOLFSSL_EVP_MD_CTX *ctx,
                                           WOLFSSL_EVP_PKEY_CTX **pctx,
                                           const WOLFSSL_EVP_MD *type,
                                           WOLFSSL_ENGINE *e,
                                           WOLFSSL_EVP_PKEY *pkey);
WOLFSSL_API int wolfSSL_EVP_DigestSignUpdate(WOLFSSL_EVP_MD_CTX *ctx,
                                             const void *d, unsigned int cnt);
WOLFSSL_API int wolfSSL_EVP_DigestSignFinal(WOLFSSL_EVP_MD_CTX *ctx,
                                            unsigned char *sig, size_t *siglen);

WOLFSSL_API int wolfSSL_EVP_DigestVerifyInit(WOLFSSL_EVP_MD_CTX *ctx,
                                             WOLFSSL_EVP_PKEY_CTX **pctx,
                                             const WOLFSSL_EVP_MD *type,
                                             WOLFSSL_ENGINE *e,
                                             WOLFSSL_EVP_PKEY *pkey);
WOLFSSL_API int wolfSSL_EVP_DigestVerifyUpdate(WOLFSSL_EVP_MD_CTX *ctx,
                                               const void *d, size_t cnt);
WOLFSSL_API int wolfSSL_EVP_DigestVerifyFinal(WOLFSSL_EVP_MD_CTX *ctx,
                                              const unsigned char *sig,
                                              size_t siglen);
WOLFSSL_API int wolfSSL_EVP_Digest(const unsigned char* in, int inSz, unsigned char* out,
                              unsigned int* outSz, const WOLFSSL_EVP_MD* evp,
                              WOLFSSL_ENGINE* eng);


WOLFSSL_API int wolfSSL_EVP_BytesToKey(const WOLFSSL_EVP_CIPHER*,
                              const WOLFSSL_EVP_MD*, const unsigned char*,
                              const unsigned char*, int, int, unsigned char*,
                              unsigned char*);

WOLFSSL_API void wolfSSL_EVP_CIPHER_CTX_init(WOLFSSL_EVP_CIPHER_CTX* ctx);
WOLFSSL_API int  wolfSSL_EVP_CIPHER_CTX_cleanup(WOLFSSL_EVP_CIPHER_CTX* ctx);
WOLFSSL_API int  wolfSSL_EVP_CIPHER_CTX_ctrl(WOLFSSL_EVP_CIPHER_CTX *ctx, \
                                             int type, int arg, void *ptr);
WOLFSSL_API int  wolfSSL_EVP_CIPHER_CTX_iv_length(const WOLFSSL_EVP_CIPHER_CTX*);
WOLFSSL_API int  wolfSSL_EVP_CIPHER_iv_length(const WOLFSSL_EVP_CIPHER*);
WOLFSSL_API int wolfSSL_EVP_Cipher_key_length(const WOLFSSL_EVP_CIPHER* c);


WOLFSSL_API int  wolfSSL_EVP_CipherInit(WOLFSSL_EVP_CIPHER_CTX* ctx,
                                    const WOLFSSL_EVP_CIPHER* type,
                                    const unsigned char* key,
                                    const unsigned char* iv,
                                    int enc);
WOLFSSL_API int  wolfSSL_EVP_CipherInit_ex(WOLFSSL_EVP_CIPHER_CTX* ctx,
                                    const WOLFSSL_EVP_CIPHER* type,
                                    WOLFSSL_ENGINE *impl,
                                    const unsigned char* key,
                                    const unsigned char* iv,
                                    int enc);
WOLFSSL_API int  wolfSSL_EVP_EncryptInit(WOLFSSL_EVP_CIPHER_CTX* ctx,
                                    const WOLFSSL_EVP_CIPHER* type,
                                    const unsigned char* key,
                                    const unsigned char* iv);
WOLFSSL_API int  wolfSSL_EVP_EncryptInit_ex(WOLFSSL_EVP_CIPHER_CTX* ctx,
                                    const WOLFSSL_EVP_CIPHER* type,
                                    WOLFSSL_ENGINE *impl,
                                    const unsigned char* key,
                                    const unsigned char* iv);
WOLFSSL_API int  wolfSSL_EVP_DecryptInit(WOLFSSL_EVP_CIPHER_CTX* ctx,
                                    const WOLFSSL_EVP_CIPHER* type,
                                    const unsigned char* key,
                                    const unsigned char* iv);
WOLFSSL_API int  wolfSSL_EVP_DecryptInit_ex(WOLFSSL_EVP_CIPHER_CTX* ctx,
                                    const WOLFSSL_EVP_CIPHER* type,
                                    WOLFSSL_ENGINE *impl,
                                    const unsigned char* key,
                                    const unsigned char* iv);
WOLFSSL_API int wolfSSL_EVP_CipherUpdate(WOLFSSL_EVP_CIPHER_CTX *ctx,
                                   unsigned char *out, int *outl,
                                   const unsigned char *in, int inl);
WOLFSSL_API int  wolfSSL_EVP_CipherFinal(WOLFSSL_EVP_CIPHER_CTX *ctx,
                                   unsigned char *out, int *outl);
WOLFSSL_API int  wolfSSL_EVP_CipherFinal_ex(WOLFSSL_EVP_CIPHER_CTX *ctx,
                                   unsigned char *out, int *outl, int enc);
WOLFSSL_API int  wolfSSL_EVP_EncryptFinal(WOLFSSL_EVP_CIPHER_CTX *ctx,
                                   unsigned char *out, int *outl);
WOLFSSL_API int  wolfSSL_EVP_EncryptFinal_ex(WOLFSSL_EVP_CIPHER_CTX *ctx,
                                   unsigned char *out, int *outl);
WOLFSSL_API int  wolfSSL_EVP_DecryptFinal(WOLFSSL_EVP_CIPHER_CTX *ctx,
                                   unsigned char *out, int *outl);
WOLFSSL_API int  wolfSSL_EVP_DecryptFinal_ex(WOLFSSL_EVP_CIPHER_CTX *ctx,
                                   unsigned char *out, int *outl);
WOLFSSL_API int  wolfSSL_EVP_DecryptFinal_legacy(WOLFSSL_EVP_CIPHER_CTX *ctx,
                                   unsigned char *out, int *outl);

WOLFSSL_API WOLFSSL_EVP_CIPHER_CTX *wolfSSL_EVP_CIPHER_CTX_new(void);
WOLFSSL_API void wolfSSL_EVP_CIPHER_CTX_free(WOLFSSL_EVP_CIPHER_CTX *ctx);
WOLFSSL_API int  wolfSSL_EVP_CIPHER_CTX_reset(WOLFSSL_EVP_CIPHER_CTX *ctx);
WOLFSSL_API int  wolfSSL_EVP_CIPHER_CTX_key_length(WOLFSSL_EVP_CIPHER_CTX* ctx);
WOLFSSL_API int  wolfSSL_EVP_CIPHER_CTX_set_key_length(WOLFSSL_EVP_CIPHER_CTX* ctx,
                                                     int keylen);
WOLFSSL_API int  wolfSSL_EVP_CIPHER_CTX_set_iv_length(WOLFSSL_EVP_CIPHER_CTX* ctx,
                                                     int ivLen);
WOLFSSL_API int  wolfSSL_EVP_CIPHER_CTX_set_iv(WOLFSSL_EVP_CIPHER_CTX* ctx, byte* iv,
                                                     int ivLen);
WOLFSSL_API int  wolfSSL_EVP_Cipher(WOLFSSL_EVP_CIPHER_CTX* ctx,
                          unsigned char* dst, unsigned char* src,
                          unsigned int len);

WOLFSSL_API const WOLFSSL_EVP_CIPHER* wolfSSL_EVP_get_cipherbynid(int);
WOLFSSL_API const WOLFSSL_EVP_MD* wolfSSL_EVP_get_digestbynid(int);
WOLFSSL_API const WOLFSSL_EVP_CIPHER *wolfSSL_EVP_CIPHER_CTX_cipher(const WOLFSSL_EVP_CIPHER_CTX *ctx);

WOLFSSL_API int wolfSSL_EVP_PKEY_assign_RSA(WOLFSSL_EVP_PKEY* pkey,
                                            WOLFSSL_RSA* key);
WOLFSSL_API int wolfSSL_EVP_PKEY_assign_EC_KEY(WOLFSSL_EVP_PKEY* pkey,
                                               WOLFSSL_EC_KEY* key);
WOLFSSL_API int wolfSSL_EVP_PKEY_assign_DSA(EVP_PKEY* pkey, WOLFSSL_DSA* key);
WOLFSSL_API int wolfSSL_EVP_PKEY_assign_DH(EVP_PKEY* pkey, WOLFSSL_DH* key);
WOLFSSL_API WOLFSSL_RSA* wolfSSL_EVP_PKEY_get0_RSA(struct WOLFSSL_EVP_PKEY *pkey);
WOLFSSL_API WOLFSSL_DSA* wolfSSL_EVP_PKEY_get0_DSA(struct WOLFSSL_EVP_PKEY *pkey);
WOLFSSL_API WOLFSSL_RSA* wolfSSL_EVP_PKEY_get1_RSA(WOLFSSL_EVP_PKEY*);
WOLFSSL_API WOLFSSL_DSA* wolfSSL_EVP_PKEY_get1_DSA(WOLFSSL_EVP_PKEY*);
WOLFSSL_API WOLFSSL_EC_KEY *wolfSSL_EVP_PKEY_get0_EC_KEY(WOLFSSL_EVP_PKEY *pkey);
WOLFSSL_API WOLFSSL_EC_KEY *wolfSSL_EVP_PKEY_get1_EC_KEY(WOLFSSL_EVP_PKEY *key);
WOLFSSL_API WOLFSSL_DH* wolfSSL_EVP_PKEY_get0_DH(WOLFSSL_EVP_PKEY* key);
WOLFSSL_API WOLFSSL_DH* wolfSSL_EVP_PKEY_get1_DH(WOLFSSL_EVP_PKEY* key);
WOLFSSL_API int wolfSSL_EVP_PKEY_set1_RSA(WOLFSSL_EVP_PKEY *pkey, WOLFSSL_RSA *key);
WOLFSSL_API int wolfSSL_EVP_PKEY_set1_DSA(WOLFSSL_EVP_PKEY *pkey, WOLFSSL_DSA *key);
WOLFSSL_API int wolfSSL_EVP_PKEY_set1_DH(WOLFSSL_EVP_PKEY *pkey, WOLFSSL_DH *key);
WOLFSSL_API int wolfSSL_EVP_PKEY_set1_EC_KEY(WOLFSSL_EVP_PKEY *pkey, WOLFSSL_EC_KEY *key);
WOLFSSL_API int wolfSSL_EVP_PKEY_assign(WOLFSSL_EVP_PKEY *pkey, int type, void *key);

WOLFSSL_API WOLFSSL_EVP_PKEY* wolfSSL_EVP_PKEY_new_mac_key(int type, ENGINE* e,
                                          const unsigned char* key, int keylen);
WOLFSSL_API const unsigned char* wolfSSL_EVP_PKEY_get0_hmac(const WOLFSSL_EVP_PKEY* pkey,
        size_t* len);
WOLFSSL_API int wolfSSL_EVP_PKEY_sign_init(WOLFSSL_EVP_PKEY_CTX *ctx);
WOLFSSL_API int wolfSSL_EVP_PKEY_sign(WOLFSSL_EVP_PKEY_CTX *ctx,
  unsigned char *sig, size_t *siglen, const unsigned char *tbs, size_t tbslen);
WOLFSSL_API int wolfSSL_EVP_PKEY_keygen_init(WOLFSSL_EVP_PKEY_CTX *ctx);
WOLFSSL_API int wolfSSL_EVP_PKEY_keygen(WOLFSSL_EVP_PKEY_CTX *ctx,
  WOLFSSL_EVP_PKEY **ppkey);
WOLFSSL_API int wolfSSL_EVP_PKEY_bits(const WOLFSSL_EVP_PKEY *pkey);
WOLFSSL_API int wolfSSL_EVP_PKEY_CTX_free(WOLFSSL_EVP_PKEY_CTX *ctx);
WOLFSSL_API WOLFSSL_EVP_PKEY_CTX *wolfSSL_EVP_PKEY_CTX_new(WOLFSSL_EVP_PKEY *pkey, WOLFSSL_ENGINE *e);
WOLFSSL_API int wolfSSL_EVP_PKEY_CTX_set_rsa_padding(WOLFSSL_EVP_PKEY_CTX *ctx, int padding);
WOLFSSL_API WOLFSSL_EVP_PKEY_CTX *wolfSSL_EVP_PKEY_CTX_new_id(int id, WOLFSSL_ENGINE *e);
WOLFSSL_API int wolfSSL_EVP_PKEY_CTX_set_rsa_keygen_bits(WOLFSSL_EVP_PKEY_CTX *ctx, int bits);

WOLFSSL_API int wolfSSL_EVP_PKEY_derive_init(WOLFSSL_EVP_PKEY_CTX *ctx);
WOLFSSL_API int wolfSSL_EVP_PKEY_derive_set_peer(WOLFSSL_EVP_PKEY_CTX *ctx, WOLFSSL_EVP_PKEY *peer);
WOLFSSL_API int wolfSSL_EVP_PKEY_derive(WOLFSSL_EVP_PKEY_CTX *ctx, unsigned char *key, size_t *keylen);

WOLFSSL_API int wolfSSL_EVP_PKEY_decrypt(WOLFSSL_EVP_PKEY_CTX *ctx,
                     unsigned char *out, size_t *outlen,
                     const unsigned char *in, size_t inlen);
WOLFSSL_API int wolfSSL_EVP_PKEY_decrypt_init(WOLFSSL_EVP_PKEY_CTX *ctx);
WOLFSSL_API int wolfSSL_EVP_PKEY_encrypt(WOLFSSL_EVP_PKEY_CTX *ctx,
                     unsigned char *out, size_t *outlen,
                     const unsigned char *in, size_t inlen);
WOLFSSL_API int wolfSSL_EVP_PKEY_encrypt_init(WOLFSSL_EVP_PKEY_CTX *ctx);
WOLFSSL_API WOLFSSL_EVP_PKEY *wolfSSL_EVP_PKEY_new(void);
WOLFSSL_API WOLFSSL_EVP_PKEY* wolfSSL_EVP_PKEY_new_ex(void* heap);
WOLFSSL_API void wolfSSL_EVP_PKEY_free(WOLFSSL_EVP_PKEY*);
WOLFSSL_API int wolfSSL_EVP_PKEY_size(WOLFSSL_EVP_PKEY *pkey);
WOLFSSL_API int wolfSSL_EVP_PKEY_missing_parameters(WOLFSSL_EVP_PKEY *pkey);
WOLFSSL_API int wolfSSL_EVP_PKEY_cmp(const WOLFSSL_EVP_PKEY *a, const WOLFSSL_EVP_PKEY *b);
WOLFSSL_API int wolfSSL_EVP_PKEY_type(int type);
WOLFSSL_API int wolfSSL_EVP_PKEY_id(const EVP_PKEY *pkey);
WOLFSSL_API int wolfSSL_EVP_PKEY_base_id(const EVP_PKEY *pkey);
WOLFSSL_API int wolfSSL_EVP_SignFinal(WOLFSSL_EVP_MD_CTX *ctx, unsigned char *sigret,
                  unsigned int *siglen, WOLFSSL_EVP_PKEY *pkey);
WOLFSSL_API int wolfSSL_EVP_SignInit(WOLFSSL_EVP_MD_CTX *ctx, const WOLFSSL_EVP_MD *type);
WOLFSSL_API int wolfSSL_EVP_SignInit_ex(WOLFSSL_EVP_MD_CTX* ctx,
                                     const WOLFSSL_EVP_MD* type,
                                     WOLFSSL_ENGINE *impl);
WOLFSSL_API int wolfSSL_EVP_SignUpdate(WOLFSSL_EVP_MD_CTX *ctx, const void *data, size_t len);
WOLFSSL_API int wolfSSL_EVP_VerifyFinal(WOLFSSL_EVP_MD_CTX *ctx,
        unsigned char* sig, unsigned int sig_len, WOLFSSL_EVP_PKEY *pkey);
WOLFSSL_API int wolfSSL_EVP_VerifyInit(WOLFSSL_EVP_MD_CTX *ctx, const WOLFSSL_EVP_MD *type);
WOLFSSL_API int wolfSSL_EVP_VerifyUpdate(WOLFSSL_EVP_MD_CTX *ctx, const void *data, size_t len);


/* these next ones don't need real OpenSSL type, for OpenSSH compat only */
WOLFSSL_API void* wolfSSL_EVP_X_STATE(const WOLFSSL_EVP_CIPHER_CTX* ctx);
WOLFSSL_API int   wolfSSL_EVP_X_STATE_LEN(const WOLFSSL_EVP_CIPHER_CTX* ctx);

WOLFSSL_API void  wolfSSL_3des_iv(WOLFSSL_EVP_CIPHER_CTX* ctx, int doset,
                                unsigned char* iv, int len);
WOLFSSL_API void  wolfSSL_aes_ctr_iv(WOLFSSL_EVP_CIPHER_CTX* ctx, int doset,
                                unsigned char* iv, int len);

WOLFSSL_API int  wolfSSL_StoreExternalIV(WOLFSSL_EVP_CIPHER_CTX* ctx);
WOLFSSL_API int  wolfSSL_SetInternalIV(WOLFSSL_EVP_CIPHER_CTX* ctx);

WOLFSSL_API int wolfSSL_EVP_CIPHER_CTX_block_size(const WOLFSSL_EVP_CIPHER_CTX *ctx);
WOLFSSL_API int wolfSSL_EVP_CIPHER_block_size(const WOLFSSL_EVP_CIPHER *cipher);
WOLFSSL_API unsigned long WOLFSSL_EVP_CIPHER_mode(const WOLFSSL_EVP_CIPHER *cipher);
WOLFSSL_API unsigned long WOLFSSL_CIPHER_mode(const WOLFSSL_EVP_CIPHER *cipher);
WOLFSSL_API unsigned long wolfSSL_EVP_CIPHER_flags(const WOLFSSL_EVP_CIPHER *cipher);
WOLFSSL_API void wolfSSL_EVP_CIPHER_CTX_set_flags(WOLFSSL_EVP_CIPHER_CTX *ctx, int flags);
WOLFSSL_API void wolfSSL_EVP_CIPHER_CTX_clear_flags(WOLFSSL_EVP_CIPHER_CTX *ctx, int flags);
WOLFSSL_API unsigned long wolfSSL_EVP_CIPHER_CTX_mode(const WOLFSSL_EVP_CIPHER_CTX *ctx);
WOLFSSL_API int  wolfSSL_EVP_CIPHER_CTX_set_padding(WOLFSSL_EVP_CIPHER_CTX *c, int pad);
WOLFSSL_API int  wolfSSL_EVP_add_digest(const WOLFSSL_EVP_MD *digest);
WOLFSSL_API int  wolfSSL_EVP_add_cipher(const WOLFSSL_EVP_CIPHER *cipher);
WOLFSSL_API void wolfSSL_EVP_cleanup(void);
WOLFSSL_API int  wolfSSL_add_all_algorithms(void);
WOLFSSL_API int  wolfSSL_OpenSSL_add_all_algorithms_conf(void);
WOLFSSL_API int  wolfSSL_OpenSSL_add_all_algorithms_noconf(void);
WOLFSSL_API int wolfSSL_EVP_read_pw_string(char*, int, const char*, int);

WOLFSSL_API int wolfSSL_PKCS5_PBKDF2_HMAC_SHA1(const char * pass, int passlen,
                                               const unsigned char * salt,
                                               int saltlen, int iter,
                                               int keylen, unsigned char *out);

WOLFSSL_API int wolfSSL_PKCS5_PBKDF2_HMAC(const char *pass, int passlen,
                                           const unsigned char *salt,
                                           int saltlen, int iter,
                                           const WOLFSSL_EVP_MD *digest,
                                           int keylen, unsigned char *out);

WOLFSSL_LOCAL int wolfSSL_EVP_get_hashinfo(const WOLFSSL_EVP_MD* evp,
                                           int* pHash, int* pHashSz);

#define EVP_CIPH_STREAM_CIPHER WOLFSSL_EVP_CIPH_STREAM_CIPHER
#define EVP_CIPH_ECB_MODE WOLFSSL_EVP_CIPH_ECB_MODE
#define EVP_CIPH_CBC_MODE WOLFSSL_EVP_CIPH_CBC_MODE
#define EVP_CIPH_CFB_MODE WOLFSSL_EVP_CIPH_CFB_MODE
#define EVP_CIPH_OFB_MODE WOLFSSL_EVP_CIPH_OFB_MODE
#define EVP_CIPH_CTR_MODE WOLFSSL_EVP_CIPH_CTR_MODE
#define EVP_CIPH_GCM_MODE WOLFSSL_EVP_CIPH_GCM_MODE
#define EVP_CIPH_CCM_MODE WOLFSSL_EVP_CIPH_CCM_MODE
#define EVP_CIPH_XTS_MODE WOLFSSL_EVP_CIPH_XTS_MODE

#define WOLFSSL_EVP_CIPH_MODE           0x0007
#define WOLFSSL_EVP_CIPH_STREAM_CIPHER      0x0
#define WOLFSSL_EVP_CIPH_ECB_MODE           0x1
#define WOLFSSL_EVP_CIPH_CBC_MODE           0x2
#define WOLFSSL_EVP_CIPH_CFB_MODE           0x3
#define WOLFSSL_EVP_CIPH_OFB_MODE           0x4
#define WOLFSSL_EVP_CIPH_CTR_MODE           0x5
#define WOLFSSL_EVP_CIPH_GCM_MODE           0x6
#define WOLFSSL_EVP_CIPH_CCM_MODE           0x7
#define WOLFSSL_EVP_CIPH_XTS_MODE          0x10
#define WOLFSSL_EVP_CIPH_NO_PADDING       0x100
#define EVP_CIPH_VARIABLE_LENGTH          0x200
#define WOLFSSL_EVP_CIPH_TYPE_INIT         0xff

/* end OpenSSH compat */

typedef WOLFSSL_EVP_MD         EVP_MD;
typedef WOLFSSL_EVP_CIPHER     EVP_CIPHER;
typedef WOLFSSL_EVP_MD_CTX     EVP_MD_CTX;
typedef WOLFSSL_EVP_CIPHER_CTX EVP_CIPHER_CTX;

#ifndef NO_MD4
    #define EVP_md4       wolfSSL_EVP_md4
#endif
#ifndef NO_MD5
    #define EVP_md5       wolfSSL_EVP_md5
#endif
#define EVP_sha1      wolfSSL_EVP_sha1
#define EVP_mdc2      wolfSSL_EVP_mdc2
#define EVP_dds1      wolfSSL_EVP_sha1
#define EVP_sha224    wolfSSL_EVP_sha224
#define EVP_sha256    wolfSSL_EVP_sha256
#define EVP_sha384    wolfSSL_EVP_sha384
#define EVP_sha512    wolfSSL_EVP_sha512
#define EVP_ripemd160 wolfSSL_EVP_ripemd160

#define EVP_sha3_224    wolfSSL_EVP_sha3_224
#define EVP_sha3_256    wolfSSL_EVP_sha3_256
#define EVP_sha3_384    wolfSSL_EVP_sha3_384
#define EVP_sha3_512    wolfSSL_EVP_sha3_512

#define EVP_aes_128_cbc    wolfSSL_EVP_aes_128_cbc
#define EVP_aes_192_cbc    wolfSSL_EVP_aes_192_cbc
#define EVP_aes_256_cbc    wolfSSL_EVP_aes_256_cbc
#define EVP_aes_128_cfb1   wolfSSL_EVP_aes_128_cfb1
#define EVP_aes_192_cfb1   wolfSSL_EVP_aes_192_cfb1
#define EVP_aes_256_cfb1   wolfSSL_EVP_aes_256_cfb1
#define EVP_aes_128_cfb8   wolfSSL_EVP_aes_128_cfb8
#define EVP_aes_192_cfb8   wolfSSL_EVP_aes_192_cfb8
#define EVP_aes_256_cfb8   wolfSSL_EVP_aes_256_cfb8
#define EVP_aes_128_cfb128 wolfSSL_EVP_aes_128_cfb128
#define EVP_aes_192_cfb128 wolfSSL_EVP_aes_192_cfb128
#define EVP_aes_256_cfb128 wolfSSL_EVP_aes_256_cfb128
#define EVP_aes_128_ofb    wolfSSL_EVP_aes_128_ofb
#define EVP_aes_192_ofb    wolfSSL_EVP_aes_192_ofb
#define EVP_aes_256_ofb    wolfSSL_EVP_aes_256_ofb
#define EVP_aes_128_xts    wolfSSL_EVP_aes_128_xts
#define EVP_aes_256_xts    wolfSSL_EVP_aes_256_xts
#define EVP_aes_128_gcm    wolfSSL_EVP_aes_128_gcm
#define EVP_aes_192_gcm    wolfSSL_EVP_aes_192_gcm
#define EVP_aes_256_gcm    wolfSSL_EVP_aes_256_gcm
#define EVP_aes_128_ecb    wolfSSL_EVP_aes_128_ecb
#define EVP_aes_192_ecb    wolfSSL_EVP_aes_192_ecb
#define EVP_aes_256_ecb    wolfSSL_EVP_aes_256_ecb
#define EVP_aes_128_ctr    wolfSSL_EVP_aes_128_ctr
#define EVP_aes_192_ctr    wolfSSL_EVP_aes_192_ctr
#define EVP_aes_256_ctr    wolfSSL_EVP_aes_256_ctr
#define EVP_des_cbc        wolfSSL_EVP_des_cbc
#define EVP_des_ecb        wolfSSL_EVP_des_ecb
#define EVP_des_ede3_cbc   wolfSSL_EVP_des_ede3_cbc
#define EVP_des_ede3_ecb   wolfSSL_EVP_des_ede3_ecb
#define EVP_rc4            wolfSSL_EVP_rc4
#define EVP_idea_cbc       wolfSSL_EVP_idea_cbc
#define EVP_enc_null       wolfSSL_EVP_enc_null

#define EVP_MD_size             wolfSSL_EVP_MD_size
#define EVP_MD_CTX_new          wolfSSL_EVP_MD_CTX_new
#define EVP_MD_CTX_create       wolfSSL_EVP_MD_CTX_new
#define EVP_MD_CTX_free         wolfSSL_EVP_MD_CTX_free
#define EVP_MD_CTX_destroy      wolfSSL_EVP_MD_CTX_free
#define EVP_MD_CTX_init         wolfSSL_EVP_MD_CTX_init
#define EVP_MD_CTX_cleanup      wolfSSL_EVP_MD_CTX_cleanup
#define EVP_MD_CTX_reset        wolfSSL_EVP_MD_CTX_cleanup
#define EVP_MD_CTX_md           wolfSSL_EVP_MD_CTX_md
#define EVP_MD_CTX_type         wolfSSL_EVP_MD_CTX_type
#define EVP_MD_CTX_size         wolfSSL_EVP_MD_CTX_size
#define EVP_MD_CTX_block_size   wolfSSL_EVP_MD_CTX_block_size
#define EVP_MD_type             wolfSSL_EVP_MD_type

#define EVP_Digest             wolfSSL_EVP_Digest
#define EVP_DigestInit         wolfSSL_EVP_DigestInit
#define EVP_DigestInit_ex      wolfSSL_EVP_DigestInit_ex
#define EVP_DigestUpdate       wolfSSL_EVP_DigestUpdate
#define EVP_DigestFinal        wolfSSL_EVP_DigestFinal
#define EVP_DigestFinal_ex     wolfSSL_EVP_DigestFinal_ex
#define EVP_DigestSignInit     wolfSSL_EVP_DigestSignInit
#define EVP_DigestSignUpdate   wolfSSL_EVP_DigestSignUpdate
#define EVP_DigestSignFinal    wolfSSL_EVP_DigestSignFinal
#define EVP_DigestVerifyInit   wolfSSL_EVP_DigestVerifyInit
#define EVP_DigestVerifyUpdate wolfSSL_EVP_DigestVerifyUpdate
#define EVP_DigestVerifyFinal  wolfSSL_EVP_DigestVerifyFinal
#define EVP_BytesToKey         wolfSSL_EVP_BytesToKey

#define EVP_get_cipherbyname wolfSSL_EVP_get_cipherbyname
#define EVP_get_digestbyname wolfSSL_EVP_get_digestbyname

#define EVP_CIPHER_CTX_init           wolfSSL_EVP_CIPHER_CTX_init
#define EVP_CIPHER_CTX_cleanup        wolfSSL_EVP_CIPHER_CTX_cleanup
#define EVP_CIPHER_CTX_iv_length      wolfSSL_EVP_CIPHER_CTX_iv_length
#define EVP_CIPHER_CTX_key_length     wolfSSL_EVP_CIPHER_CTX_key_length
#define EVP_CIPHER_CTX_set_key_length wolfSSL_EVP_CIPHER_CTX_set_key_length
#define EVP_CIPHER_CTX_mode           wolfSSL_EVP_CIPHER_CTX_mode
#define EVP_CIPHER_CTX_cipher         wolfSSL_EVP_CIPHER_CTX_cipher

#define EVP_CIPHER_iv_length          wolfSSL_EVP_CIPHER_iv_length
#define EVP_CIPHER_key_length         wolfSSL_EVP_Cipher_key_length

#define EVP_CipherInit                wolfSSL_EVP_CipherInit
#define EVP_CipherInit_ex             wolfSSL_EVP_CipherInit_ex
#define EVP_EncryptInit               wolfSSL_EVP_EncryptInit
#define EVP_EncryptInit_ex            wolfSSL_EVP_EncryptInit_ex
#define EVP_DecryptInit               wolfSSL_EVP_DecryptInit
#define EVP_DecryptInit_ex            wolfSSL_EVP_DecryptInit_ex

#define EVP_Cipher                    wolfSSL_EVP_Cipher
#define EVP_CipherUpdate              wolfSSL_EVP_CipherUpdate
#define EVP_EncryptUpdate             wolfSSL_EVP_CipherUpdate
#define EVP_DecryptUpdate             wolfSSL_EVP_CipherUpdate
#define EVP_CipherFinal               wolfSSL_EVP_CipherFinal
#define EVP_CipherFinal_ex            wolfSSL_EVP_CipherFinal
#define EVP_EncryptFinal              wolfSSL_EVP_CipherFinal
#define EVP_EncryptFinal_ex           wolfSSL_EVP_CipherFinal
#define EVP_DecryptFinal              wolfSSL_EVP_CipherFinal
#define EVP_DecryptFinal_ex           wolfSSL_EVP_CipherFinal

#define EVP_CIPHER_CTX_free           wolfSSL_EVP_CIPHER_CTX_free
#define EVP_CIPHER_CTX_reset          wolfSSL_EVP_CIPHER_CTX_reset
#define EVP_CIPHER_CTX_new            wolfSSL_EVP_CIPHER_CTX_new

#define EVP_get_cipherbynid           wolfSSL_EVP_get_cipherbynid
#define EVP_get_digestbynid           wolfSSL_EVP_get_digestbynid
#define EVP_get_cipherbyname          wolfSSL_EVP_get_cipherbyname
#define EVP_get_digestbyname          wolfSSL_EVP_get_digestbyname

#define EVP_PKEY_assign                wolfSSL_EVP_PKEY_assign
#define EVP_PKEY_assign_RSA            wolfSSL_EVP_PKEY_assign_RSA
#define EVP_PKEY_assign_DSA            wolfSSL_EVP_PKEY_assign_DSA
#define EVP_PKEY_assign_DH             wolfSSL_EVP_PKEY_assign_DH
#define EVP_PKEY_assign_EC_KEY         wolfSSL_EVP_PKEY_assign_EC_KEY
#define EVP_PKEY_get1_DSA              wolfSSL_EVP_PKEY_get1_DSA
#define EVP_PKEY_set1_DSA              wolfSSL_EVP_PKEY_set1_DSA
#define EVP_PKEY_get0_RSA              wolfSSL_EVP_PKEY_get0_RSA
#define EVP_PKEY_get1_RSA              wolfSSL_EVP_PKEY_get1_RSA
#define EVP_PKEY_set1_RSA              wolfSSL_EVP_PKEY_set1_RSA
#define EVP_PKEY_set1_EC_KEY           wolfSSL_EVP_PKEY_set1_EC_KEY
#define EVP_PKEY_get1_EC_KEY           wolfSSL_EVP_PKEY_get1_EC_KEY
#define EVP_PKEY_set1_DH               wolfSSL_EVP_PKEY_set1_DH
#define EVP_PKEY_get0_DH               wolfSSL_EVP_PKEY_get0_DH
#define EVP_PKEY_get1_DH               wolfSSL_EVP_PKEY_get1_DH
#define EVP_PKEY_get0_EC_KEY           wolfSSL_EVP_PKEY_get0_EC_KEY
#define EVP_PKEY_get0_hmac             wolfSSL_EVP_PKEY_get0_hmac
#define EVP_PKEY_new_mac_key           wolfSSL_EVP_PKEY_new_mac_key
#define EVP_MD_CTX_copy                wolfSSL_EVP_MD_CTX_copy
#define EVP_MD_CTX_copy_ex             wolfSSL_EVP_MD_CTX_copy_ex
#define EVP_PKEY_sign_init             wolfSSL_EVP_PKEY_sign_init
#define EVP_PKEY_sign                  wolfSSL_EVP_PKEY_sign
#define EVP_PKEY_keygen                wolfSSL_EVP_PKEY_keygen
#define EVP_PKEY_keygen_init           wolfSSL_EVP_PKEY_keygen_init
#define EVP_PKEY_bits                  wolfSSL_EVP_PKEY_bits
#define EVP_PKEY_CTX_free              wolfSSL_EVP_PKEY_CTX_free
#define EVP_PKEY_CTX_new               wolfSSL_EVP_PKEY_CTX_new
#define EVP_PKEY_CTX_set_rsa_padding   wolfSSL_EVP_PKEY_CTX_set_rsa_padding
#define EVP_PKEY_CTX_new_id            wolfSSL_EVP_PKEY_CTX_new_id
#define EVP_PKEY_CTX_set_rsa_keygen_bits wolfSSL_EVP_PKEY_CTX_set_rsa_keygen_bits
#define EVP_PKEY_derive_init           wolfSSL_EVP_PKEY_derive_init
#define EVP_PKEY_derive_set_peer       wolfSSL_EVP_PKEY_derive_set_peer
#define EVP_PKEY_derive                wolfSSL_EVP_PKEY_derive
#define EVP_PKEY_decrypt               wolfSSL_EVP_PKEY_decrypt
#define EVP_PKEY_decrypt_init          wolfSSL_EVP_PKEY_decrypt_init
#define EVP_PKEY_encrypt               wolfSSL_EVP_PKEY_encrypt
#define EVP_PKEY_encrypt_init          wolfSSL_EVP_PKEY_encrypt_init
#define EVP_PKEY_new                   wolfSSL_EVP_PKEY_new
#define EVP_PKEY_free                  wolfSSL_EVP_PKEY_free
#define EVP_PKEY_up_ref                wolfSSL_EVP_PKEY_up_ref
#define EVP_PKEY_size                  wolfSSL_EVP_PKEY_size
#define EVP_PKEY_missing_parameters    wolfSSL_EVP_PKEY_missing_parameters
#define EVP_PKEY_cmp                   wolfSSL_EVP_PKEY_cmp
#define EVP_PKEY_type                  wolfSSL_EVP_PKEY_type
#define EVP_PKEY_base_id               wolfSSL_EVP_PKEY_base_id
#define EVP_PKEY_id                    wolfSSL_EVP_PKEY_id
#define EVP_SignFinal                  wolfSSL_EVP_SignFinal
#define EVP_SignInit                   wolfSSL_EVP_SignInit
#define EVP_SignInit_ex                wolfSSL_EVP_SignInit_ex
#define EVP_SignUpdate                 wolfSSL_EVP_SignUpdate
#define EVP_VerifyFinal                wolfSSL_EVP_VerifyFinal
#define EVP_VerifyInit                 wolfSSL_EVP_VerifyInit
#define EVP_VerifyUpdate               wolfSSL_EVP_VerifyUpdate

#define EVP_CIPHER_CTX_ctrl        wolfSSL_EVP_CIPHER_CTX_ctrl
#define EVP_CIPHER_CTX_block_size  wolfSSL_EVP_CIPHER_CTX_block_size
#define EVP_CIPHER_block_size      wolfSSL_EVP_CIPHER_block_size
#define EVP_CIPHER_flags           wolfSSL_EVP_CIPHER_flags
#define EVP_CIPHER_CTX_set_flags   wolfSSL_EVP_CIPHER_CTX_set_flags
#define EVP_CIPHER_CTX_clear_flags wolfSSL_EVP_CIPHER_CTX_clear_flags
#define EVP_CIPHER_CTX_set_padding wolfSSL_EVP_CIPHER_CTX_set_padding
#define EVP_CIPHER_CTX_flags       wolfSSL_EVP_CIPHER_CTX_flags
#define EVP_CIPHER_CTX_set_iv      wolfSSL_EVP_CIPHER_CTX_set_iv
#define EVP_add_digest             wolfSSL_EVP_add_digest
#define EVP_add_cipher             wolfSSL_EVP_add_cipher
#define EVP_cleanup                wolfSSL_EVP_cleanup
#define EVP_read_pw_string         wolfSSL_EVP_read_pw_string
#define EVP_rc2_cbc                wolfSSL_EVP_rc2_cbc

#define OpenSSL_add_all_digests()  wolfSSL_EVP_init()
#define OpenSSL_add_all_ciphers()  wolfSSL_EVP_init()
#define OpenSSL_add_all_algorithms wolfSSL_add_all_algorithms
#define OpenSSL_add_all_algorithms_noconf wolfSSL_OpenSSL_add_all_algorithms_noconf
#define OpenSSL_add_all_algorithms_conf   wolfSSL_OpenSSL_add_all_algorithms_conf

#define wolfSSL_OPENSSL_add_all_algorithms_noconf wolfSSL_OpenSSL_add_all_algorithms_noconf
#define wolfSSL_OPENSSL_add_all_algorithms_conf   wolfSSL_OpenSSL_add_all_algorithms_conf

/* provides older OpenSSL API compatibility  */
#define OPENSSL_add_all_algorithms        OpenSSL_add_all_algorithms
#define OPENSSL_add_all_algorithms_noconf OpenSSL_add_all_algorithms_noconf
#define OPENSSL_add_all_algorithms_conf   OpenSSL_add_all_algorithms_conf

#define NO_PADDING_BLOCK_SIZE      1

#define PKCS5_PBKDF2_HMAC_SHA1     wolfSSL_PKCS5_PBKDF2_HMAC_SHA1
#define PKCS5_PBKDF2_HMAC          wolfSSL_PKCS5_PBKDF2_HMAC

/* OpenSSL compat. ctrl values */
#define EVP_CTRL_INIT                  0x0
#define EVP_CTRL_SET_KEY_LENGTH        0x1
#define EVP_CTRL_SET_RC2_KEY_BITS      0x3  /* needed for qt compilation */

#define EVP_CTRL_AEAD_SET_IVLEN        0x9
#define EVP_CTRL_AEAD_GET_TAG          0x10
#define EVP_CTRL_AEAD_SET_TAG          0x11
#define EVP_CTRL_AEAD_SET_IV_FIXED     0x12
#define EVP_CTRL_GCM_IV_GEN            0x13
#define EVP_CTRL_GCM_SET_IVLEN         EVP_CTRL_AEAD_SET_IVLEN
#define EVP_CTRL_GCM_GET_TAG           EVP_CTRL_AEAD_GET_TAG
#define EVP_CTRL_GCM_SET_TAG           EVP_CTRL_AEAD_SET_TAG
#define EVP_CTRL_GCM_SET_IV_FIXED      EVP_CTRL_AEAD_SET_IV_FIXED

#define EVP_PKEY_print_private(arg1, arg2, arg3, arg4)

#ifndef EVP_MAX_MD_SIZE
    #define EVP_MAX_MD_SIZE   64     /* sha512 */
#endif

#ifndef EVP_MAX_KEY_LENGTH
#define EVP_MAX_KEY_LENGTH    64
#endif

#ifndef EVP_MAX_IV_LENGTH
#define EVP_MAX_IV_LENGTH     16
#endif

#ifndef EVP_MAX_BLOCK_LENGTH
    #define EVP_MAX_BLOCK_LENGTH   32  /* 2 * blocklen(AES)? */
    /* They define this as 32. Using the same value here. */
#endif

#ifndef EVP_MAX_IV_LENGTH
    #define EVP_MAX_IV_LENGTH       16
#endif


#define EVP_R_BAD_DECRYPT               (-MIN_CODE_E + 100 + 1)
#define EVP_R_BN_DECODE_ERROR           (-MIN_CODE_E + 100 + 2)
#define EVP_R_DECODE_ERROR              (-MIN_CODE_E + 100 + 3)
#define EVP_R_PRIVATE_KEY_DECODE_ERROR  (-MIN_CODE_E + 100 + 4)

#define EVP_PKEY_NONE                   NID_undef
#define EVP_PKEY_RSA                    6
#define EVP_PKEY_RSA2                   19
#define EVP_PKEY_DH                     28
#define EVP_CIPHER_mode                 WOLFSSL_CIPHER_mode
/* WOLFSSL_EVP_CIPHER is just the string name of the cipher */
#define EVP_CIPHER_name(x)              x
#define EVP_MD_CTX_reset                wolfSSL_EVP_MD_CTX_cleanup
/* WOLFSSL_EVP_MD is just the string name of the digest */
#define EVP_MD_name(x)                  x
#define EVP_CIPHER_nid                  wolfSSL_EVP_CIPHER_nid


WOLFSSL_API void printPKEY(WOLFSSL_EVP_PKEY *k);

#ifdef __cplusplus
    } /* extern "C" */
#endif

#include <wolfssl/openssl/objects.h>

#endif /* WOLFSSL_EVP_H_ */
