/* hmac.h
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


/*  hmac.h defines mini hamc openssl compatibility layer 
 *
 */


#ifndef WOLFSSL_HMAC_H_
#define WOLFSSL_HMAC_H_

#include <wolfssl/wolfcrypt/settings.h>

#ifdef WOLFSSL_PREFIX
#include "prefix_hmac.h"
#endif

#include <wolfssl/openssl/evp.h>
#include <wolfssl/wolfcrypt/hmac.h>

#ifdef __cplusplus
    extern "C" {
#endif


WOLFSSL_API unsigned char* wolfSSL_HMAC(const WOLFSSL_EVP_MD* evp_md,
                               const void* key, int key_len,
                               const unsigned char* d, int n, unsigned char* md,
                               unsigned int* md_len);


typedef struct WOLFSSL_HMAC_CTX {
    Hmac hmac;
    int  type;
} WOLFSSL_HMAC_CTX;


WOLFSSL_API void wolfSSL_HMAC_Init(WOLFSSL_HMAC_CTX* ctx, const void* key,
                                 int keylen, const EVP_MD* type);
WOLFSSL_API void wolfSSL_HMAC_Update(WOLFSSL_HMAC_CTX* ctx,
                                   const unsigned char* data, int len);
WOLFSSL_API void wolfSSL_HMAC_Final(WOLFSSL_HMAC_CTX* ctx, unsigned char* hash,
                                  unsigned int* len);
WOLFSSL_API void wolfSSL_HMAC_cleanup(WOLFSSL_HMAC_CTX* ctx);


typedef struct WOLFSSL_HMAC_CTX HMAC_CTX;

#define HMAC(a,b,c,d,e,f,g) wolfSSL_HMAC((a),(b),(c),(d),(e),(f),(g))

#define HMAC_Init    wolfSSL_HMAC_Init
#define HMAC_Update  wolfSSL_HMAC_Update
#define HMAC_Final   wolfSSL_HMAC_Final
#define HMAC_cleanup wolfSSL_HMAC_cleanup


#ifdef __cplusplus
    } /* extern "C" */
#endif


#endif /* WOLFSSL_HMAC_H_ */
