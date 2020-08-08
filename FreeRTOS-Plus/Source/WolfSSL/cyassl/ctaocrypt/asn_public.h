/* asn_public.h
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



#ifndef CTAO_CRYPT_ASN_PUBLIC_H
#define CTAO_CRYPT_ASN_PUBLIC_H

/* pull in compatibility for each of the includes */
#include <cyassl/ctaocrypt/types.h>
#include <cyassl/ctaocrypt/types.h>
#include <cyassl/ctaocrypt/ecc.h>
#ifdef WOLFSSL_CERT_GEN
    #include <cyassl/ctaocrypt/rsa.h>
#endif

#include <wolfssl/wolfcrypt/asn_public.h>
#ifdef WOLFSSL_CERT_GEN
    #define InitCert wc_InitCert
    #define MakeCert wc_MakeCert

    #ifdef WOLFSSL_CERT_REQ
    #define MakeCertReq wc_MakeCertReq
#endif

    #define SignCert     wc_SignCert
    #define MakeSelfCert wc_MakeSelfCert
    #define SetIssuer    wc_SetIssuer
    #define SetSubject   wc_SetSubject

    #ifdef WOLFSSL_ALT_NAMES
    #define SetAltNames wc_SetAltNames
#endif

    #define SetIssuerBuffer   wc_SetIssuerBuffer
    #define SetSubjectBuffer  wc_SetSubjectBuffer
    #define SetAltNamesBuffer wc_SetAltNamesBuffer
    #define SetDatesBuffer    wc_SetDatesBuffer

    #ifdef HAVE_NTRU
        #define MakeNtruCert wc_MakeNtruCert
    #endif

#endif /* WOLFSSL_CERT_GEN */

    #if defined(WOLFSSL_KEY_GEN) || defined(WOLFSSL_CERT_GEN)
    #define DerToPem wc_DerToPem
#endif

#ifdef HAVE_ECC
    /* private key helpers */
    #define EccPrivateKeyDecode wc_EccPrivateKeyDecode
    #define EccKeyToDer         wc_EccKeyToDer
#endif

    /* DER encode signature */
    #define EncodeSignature wc_EncodeSignature
    #define GetCTC_HashOID  wc_GetCTC_HashOID

#endif /* CTAO_CRYPT_ASN_PUBLIC_H */

