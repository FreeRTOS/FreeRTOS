/* rsa.h
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

/* rsa.h for openSSL */


#ifndef WOLFSSL_RSA_H_
#define WOLFSSL_RSA_H_

#include <wolfssl/openssl/bn.h>
#include <wolfssl/openssl/err.h>
#include <wolfssl/wolfcrypt/types.h>

#ifdef __cplusplus
    extern "C" {
#endif

/* Padding types */
#define RSA_PKCS1_PADDING      0
#define RSA_PKCS1_OAEP_PADDING 1
#define RSA_PKCS1_PSS_PADDING  2
#define RSA_NO_PADDING         3

/* Emulate OpenSSL flags */
#define RSA_METHOD_FLAG_NO_CHECK        (1 << 1)
#define RSA_FLAG_CACHE_PUBLIC           (1 << 2)
#define RSA_FLAG_CACHE_PRIVATE          (1 << 3)
#define RSA_FLAG_BLINDING               (1 << 4)
#define RSA_FLAG_THREAD_SAFE            (1 << 5)
#define RSA_FLAG_EXT_PKEY               (1 << 6)
#define RSA_FLAG_NO_BLINDING            (1 << 7)
#define RSA_FLAG_NO_CONSTTIME           (1 << 8)

/* Salt length same as digest length */
#define RSA_PSS_SALTLEN_DIGEST   -1
/* Old max salt length */
#define RSA_PSS_SALTLEN_MAX_SIGN -2
/* Max salt length */
#define RSA_PSS_SALTLEN_MAX      -3

typedef struct WOLFSSL_RSA_METHOD {
    int flags;
    char *name;
} WOLFSSL_RSA_METHOD;

#ifndef WOLFSSL_RSA_TYPE_DEFINED /* guard on redeclaration */
#define WOLFSSL_RSA_TYPE_DEFINED
typedef struct WOLFSSL_RSA {
#ifdef WC_RSA_BLINDING
    WC_RNG* rng;              /* for PrivateDecrypt blinding */
#endif
    WOLFSSL_BIGNUM* n;
    WOLFSSL_BIGNUM* e;
    WOLFSSL_BIGNUM* d;
    WOLFSSL_BIGNUM* p;
    WOLFSSL_BIGNUM* q;
    WOLFSSL_BIGNUM* dmp1;      /* dP */
    WOLFSSL_BIGNUM* dmq1;      /* dQ */
    WOLFSSL_BIGNUM* iqmp;      /* u */
    void*          heap;
    void*          internal;  /* our RSA */
    char           inSet;     /* internal set from external ? */
    char           exSet;     /* external set from internal ? */
    char           ownRng;    /* flag for if the rng should be free'd */
#if defined(OPENSSL_EXTRA)
    WOLFSSL_RSA_METHOD* meth;
#endif
#if defined(HAVE_EX_DATA)
    WOLFSSL_CRYPTO_EX_DATA ex_data;  /* external data */
#endif
#if defined(OPENSSL_EXTRA) || defined(OPENSSL_ALL)
    wolfSSL_Mutex    refMutex;                       /* ref count mutex */
    int              refCount;                       /* reference count */
#endif
} WOLFSSL_RSA;
#endif

typedef WOLFSSL_RSA                   RSA;
typedef WOLFSSL_RSA_METHOD            RSA_METHOD;

WOLFSSL_API WOLFSSL_RSA* wolfSSL_RSA_new(void);
WOLFSSL_API void        wolfSSL_RSA_free(WOLFSSL_RSA*);

WOLFSSL_API int wolfSSL_RSA_generate_key_ex(WOLFSSL_RSA*, int bits, WOLFSSL_BIGNUM*,
                                          void* cb);

WOLFSSL_API int wolfSSL_RSA_blinding_on(WOLFSSL_RSA*, WOLFSSL_BN_CTX*);
WOLFSSL_API int wolfSSL_RSA_public_encrypt(int len, const unsigned char* fr,
	                               unsigned char* to, WOLFSSL_RSA*, int padding);
WOLFSSL_API int wolfSSL_RSA_private_decrypt(int len, const unsigned char* fr,
	                               unsigned char* to, WOLFSSL_RSA*, int padding);
WOLFSSL_API int wolfSSL_RSA_private_encrypt(int len, unsigned char* in,
                            unsigned char* out, WOLFSSL_RSA* rsa, int padding);

WOLFSSL_API int wolfSSL_RSA_size(const WOLFSSL_RSA*);
WOLFSSL_API int wolfSSL_RSA_sign(int type, const unsigned char* m,
                               unsigned int mLen, unsigned char* sigRet,
                               unsigned int* sigLen, WOLFSSL_RSA*);
WOLFSSL_API int wolfSSL_RSA_sign_ex(int type, const unsigned char* m,
                               unsigned int mLen, unsigned char* sigRet,
                               unsigned int* sigLen, WOLFSSL_RSA*, int);
WOLFSSL_API int wolfSSL_RSA_verify(int type, const unsigned char* m,
                               unsigned int mLen, const unsigned char* sig,
                               unsigned int sigLen, WOLFSSL_RSA*);
WOLFSSL_API int wolfSSL_RSA_public_decrypt(int flen, const unsigned char* from,
                                  unsigned char* to, WOLFSSL_RSA*, int padding);
WOLFSSL_API int wolfSSL_RSA_GenAdd(WOLFSSL_RSA*);
WOLFSSL_API int wolfSSL_RSA_LoadDer(WOLFSSL_RSA*, const unsigned char*, int sz);
WOLFSSL_API int wolfSSL_RSA_LoadDer_ex(WOLFSSL_RSA*, const unsigned char*, int sz, int opt);

WOLFSSL_API WOLFSSL_RSA_METHOD *wolfSSL_RSA_meth_new(const char *name, int flags);
WOLFSSL_API void wolfSSL_RSA_meth_free(WOLFSSL_RSA_METHOD *meth);
WOLFSSL_API int wolfSSL_RSA_meth_set(WOLFSSL_RSA_METHOD *rsa, void* p);
WOLFSSL_API int wolfSSL_RSA_set_method(WOLFSSL_RSA *rsa, WOLFSSL_RSA_METHOD *meth);
WOLFSSL_API const WOLFSSL_RSA_METHOD* wolfSSL_RSA_get_method(const WOLFSSL_RSA *rsa);
WOLFSSL_API const WOLFSSL_RSA_METHOD* wolfSSL_RSA_get_default_method(void);

WOLFSSL_API void wolfSSL_RSA_get0_key(const WOLFSSL_RSA *r, const WOLFSSL_BIGNUM **n,
                                      const WOLFSSL_BIGNUM **e, const WOLFSSL_BIGNUM **d);
WOLFSSL_API int wolfSSL_RSA_set0_key(WOLFSSL_RSA *r, WOLFSSL_BIGNUM *n, WOLFSSL_BIGNUM *e,
                                     WOLFSSL_BIGNUM *d);
WOLFSSL_API int wolfSSL_RSA_flags(const WOLFSSL_RSA *r);
WOLFSSL_API void wolfSSL_RSA_set_flags(WOLFSSL_RSA *r, int flags);

WOLFSSL_API WOLFSSL_RSA* wolfSSL_RSAPublicKey_dup(WOLFSSL_RSA *rsa);

WOLFSSL_API void* wolfSSL_RSA_get_ex_data(const WOLFSSL_RSA *rsa, int idx);
WOLFSSL_API int wolfSSL_RSA_set_ex_data(WOLFSSL_RSA *rsa, int idx, void *data);


#define WOLFSSL_RSA_LOAD_PRIVATE 1
#define WOLFSSL_RSA_LOAD_PUBLIC  2
#define WOLFSSL_RSA_F4           0x10001L

#define RSA_new  wolfSSL_RSA_new
#define RSA_free wolfSSL_RSA_free

#define RSA_generate_key_ex wolfSSL_RSA_generate_key_ex

#define RSA_blinding_on     wolfSSL_RSA_blinding_on
#define RSA_public_encrypt  wolfSSL_RSA_public_encrypt
#define RSA_private_decrypt wolfSSL_RSA_private_decrypt
#define RSA_private_encrypt wolfSSL_RSA_private_encrypt

#define RSA_size           wolfSSL_RSA_size
#define RSA_sign           wolfSSL_RSA_sign
#define RSA_verify         wolfSSL_RSA_verify
#define RSA_public_decrypt wolfSSL_RSA_public_decrypt

#define RSA_meth_new            wolfSSL_RSA_meth_new
#define RSA_meth_free           wolfSSL_RSA_meth_free
#define RSA_meth_set_pub_enc    wolfSSL_RSA_meth_set
#define RSA_meth_set_pub_dec    wolfSSL_RSA_meth_set
#define RSA_meth_set_priv_enc   wolfSSL_RSA_meth_set
#define RSA_meth_set_priv_dec   wolfSSL_RSA_meth_set
#define RSA_meth_set_init       wolfSSL_RSA_meth_set
#define RSA_meth_set_finish     wolfSSL_RSA_meth_set
#define RSA_meth_set0_app_data  wolfSSL_RSA_meth_set
#define RSA_get_default_method  wolfSSL_RSA_get_default_method
#define RSA_get_method          wolfSSL_RSA_get_method
#define RSA_set_method          wolfSSL_RSA_set_method
#define RSA_get0_key            wolfSSL_RSA_get0_key
#define RSA_set0_key            wolfSSL_RSA_set0_key
#define RSA_flags               wolfSSL_RSA_flags
#define RSA_set_flags           wolfSSL_RSA_set_flags

#define RSAPublicKey_dup        wolfSSL_RSAPublicKey_dup
#define RSA_get_ex_data        wolfSSL_RSA_get_ex_data
#define RSA_set_ex_data        wolfSSL_RSA_set_ex_data

#define RSA_get0_key       wolfSSL_RSA_get0_key

#define RSA_F4             WOLFSSL_RSA_F4

#ifdef __cplusplus
    }  /* extern "C" */
#endif

#endif /* header */
