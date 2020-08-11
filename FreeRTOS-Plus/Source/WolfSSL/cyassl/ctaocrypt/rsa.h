/* rsa.h
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


#ifndef NO_RSA

#ifndef CTAO_CRYPT_RSA_H
#define CTAO_CRYPT_RSA_H

#include <wolfssl/wolfcrypt/rsa.h>
/* includes for their compatibility */
#include <cyassl/ctaocrypt/integer.h>
#include <cyassl/ctaocrypt/random.h>
#include <cyassl/ctaocrypt/settings.h>

#define InitRsaKey       wc_InitRsaKey
#define FreeRsaKey       wc_FreeRsaKey
#define RsaPublicEncrypt wc_RsaPublicEncrypt
#define RsaPrivateDecryptInline wc_RsaPrivateDecryptInline
#define RsaPrivateDecrypt       wc_RsaPrivateDecrypt
#define RsaSSL_Sign             wc_RsaSSL_Sign
#define RsaSSL_VerifyInline     wc_RsaSSL_VerifyInline
#define RsaSSL_Verify           wc_RsaSSL_Verify
#define RsaEncryptSize          wc_RsaEncryptSize
#define RsaFlattenPublicKey     wc_RsaFlattenPublicKey

#ifdef WOLFSSL_KEY_GEN
    #define MakeRsaKey  wc_MakeRsaKey
    #define RsaKeyToDer wc_RsaKeyToDer
    #define CheckProbablePrime wc_CheckProbablePrime
#endif

#ifdef WOLFSSL_ASYNC_CRYPT
    #define RsaAsyncInit wc_RsaAsyncInit
    #define RsaAsyncFree wc_RsaAsyncFree
#endif

#endif /* CTAO_CRYPT_RSA_H */

#endif /* NO_RSA */
