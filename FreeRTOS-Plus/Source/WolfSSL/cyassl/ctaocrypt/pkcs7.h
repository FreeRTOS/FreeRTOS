/* pkcs7.h
 *
 * Copyright (C) 2006-2015 wolfSSL Inc.
 *
 * This file is part of wolfSSL. (formerly known as CyaSSL)
 *
 * wolfSSL is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * wolfSSL is distributed in the hope that it will be useful,
 * * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301, USA
 */


#ifdef HAVE_PKCS7

#ifndef CTAO_CRYPT_PKCS7_H
#define CTAO_CRYPT_PKCS7_H

/* pull in compatibility for old includes */
#include <cyassl/ctaocrypt/types.h>
#include <cyassl/ctaocrypt/asn.h>
#include <cyassl/ctaocrypt/asn_public.h>
#include <cyassl/ctaocrypt/random.h>
#include <cyassl/ctaocrypt/des3.h>

#include <wolfssl/wolfcrypt/pkcs7.h>

/* for pkcs7 reverse compatibility */
#define SetContentType      wc_SetContentType
#define GetContentType      wc_GetContentType
#define CreateRecipientInfo wc_CreateRecipientInfo
#define PKCS7_InitWithCert  wc_PKCS7_InitWithCert
#define PKCS7_Free          wc_PKCS7_Free
#define PKCS7_EncodeData    wc_PKCS7_EncodeData
#define PKCS7_EncodeSignedData    wc_PKCS7_EncodeSignedData
#define PKCS7_VerifySignedData    wc_PKCS7_VerifySignedData
#define PKCS7_EncodeEnvelopedData wc_PKCS7_EncodeEnvelopedData
#define PKCS7_DecodeEnvelopedData wc_PKCS7_DecodeEnvelopedData

#endif /* CTAO_CRYPT_PKCS7_H */

#endif /* HAVE_PKCS7 */

