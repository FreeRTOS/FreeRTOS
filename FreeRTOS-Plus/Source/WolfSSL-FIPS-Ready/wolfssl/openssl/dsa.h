/* dsa.h
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

/* dsa.h for openSSL */


#ifndef WOLFSSL_DSA_H_
#define WOLFSSL_DSA_H_

#include <wolfssl/openssl/bn.h>

#ifdef __cplusplus
    extern "C" {
#endif

typedef struct WOLFSSL_DSA_SIG {
    WOLFSSL_BIGNUM *r;
    WOLFSSL_BIGNUM *s;
} WOLFSSL_DSA_SIG;

#ifndef WOLFSSL_DSA_TYPE_DEFINED /* guard on redeclaration */
typedef struct WOLFSSL_DSA            WOLFSSL_DSA;
#define WOLFSSL_DSA_TYPE_DEFINED
#endif

typedef WOLFSSL_DSA                   DSA;

struct WOLFSSL_DSA {
    WOLFSSL_BIGNUM* p;
    WOLFSSL_BIGNUM* q;
    WOLFSSL_BIGNUM* g;
    WOLFSSL_BIGNUM* pub_key;      /* our y */
    WOLFSSL_BIGNUM* priv_key;     /* our x */
    void*          internal;     /* our Dsa Key */
    char           inSet;        /* internal set from external ? */
    char           exSet;        /* external set from internal ? */
};


WOLFSSL_API WOLFSSL_DSA* wolfSSL_DSA_new(void);
WOLFSSL_API void wolfSSL_DSA_free(WOLFSSL_DSA*);

WOLFSSL_API int wolfSSL_DSA_generate_key(WOLFSSL_DSA*);

typedef void (*WOLFSSL_BN_CB)(int i, int j, void* exArg);
WOLFSSL_API WOLFSSL_DSA* wolfSSL_DSA_generate_parameters(int bits,
                   unsigned char* seed, int seedLen, int* counterRet,
                   unsigned long* hRet, WOLFSSL_BN_CB cb, void* CBArg);
WOLFSSL_API int wolfSSL_DSA_generate_parameters_ex(WOLFSSL_DSA*, int bits,
                   unsigned char* seed, int seedLen, int* counterRet,
                   unsigned long* hRet, void* cb);

WOLFSSL_API int wolfSSL_DSA_LoadDer(WOLFSSL_DSA*, const unsigned char*, int sz);

WOLFSSL_API int wolfSSL_DSA_LoadDer_ex(WOLFSSL_DSA*, const unsigned char*,
                                       int sz, int opt);

WOLFSSL_API int wolfSSL_DSA_do_sign(const unsigned char* d,
                                    unsigned char* sigRet, WOLFSSL_DSA* dsa);

WOLFSSL_API int wolfSSL_DSA_do_verify(const unsigned char* d,
                                      unsigned char* sig,
                                      WOLFSSL_DSA* dsa, int *dsacheck);

WOLFSSL_API int wolfSSL_DSA_bits(const WOLFSSL_DSA *d);

WOLFSSL_API WOLFSSL_DSA_SIG* wolfSSL_DSA_SIG_new(void);
WOLFSSL_API void wolfSSL_DSA_SIG_free(WOLFSSL_DSA_SIG *sig);
WOLFSSL_API WOLFSSL_DSA_SIG* wolfSSL_DSA_do_sign_ex(const unsigned char* digest,
                                                    int outLen, WOLFSSL_DSA* dsa);
WOLFSSL_API int wolfSSL_DSA_do_verify_ex(const unsigned char* digest, int digest_len,
                                         WOLFSSL_DSA_SIG* sig, WOLFSSL_DSA* dsa);

#define WOLFSSL_DSA_LOAD_PRIVATE 1
#define WOLFSSL_DSA_LOAD_PUBLIC  2

#define DSA_new wolfSSL_DSA_new
#define DSA_free wolfSSL_DSA_free

#define DSA_LoadDer                wolfSSL_DSA_LoadDer
#define DSA_generate_key           wolfSSL_DSA_generate_key
#define DSA_generate_parameters    wolfSSL_DSA_generate_parameters
#define DSA_generate_parameters_ex wolfSSL_DSA_generate_parameters_ex

#define DSA_SIG_new                wolfSSL_DSA_SIG_new
#define DSA_SIG_free               wolfSSL_DSA_SIG_free
#define DSA_do_sign                wolfSSL_DSA_do_sign_ex
#define DSA_do_verify              wolfSSL_DSA_do_verify_ex


#define DSA_SIG                    WOLFSSL_DSA_SIG

#ifdef __cplusplus
    }  /* extern "C" */ 
#endif

#endif /* header */
