/* crl.h
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



#ifndef WOLFSSL_CRL_H
#define WOLFSSL_CRL_H


#ifdef HAVE_CRL

#include <wolfssl/ssl.h>
#include <wolfssl/wolfcrypt/asn.h>

#ifdef __cplusplus
    extern "C" {
#endif

WOLFSSL_LOCAL int  InitCRL(WOLFSSL_CRL*, WOLFSSL_CERT_MANAGER*);
WOLFSSL_LOCAL void FreeCRL(WOLFSSL_CRL*, int dynamic);

WOLFSSL_LOCAL int  LoadCRL(WOLFSSL_CRL* crl, const char* path, int type, int mon);
WOLFSSL_LOCAL int  BufferLoadCRL(WOLFSSL_CRL*, const byte*, long, int, int);
WOLFSSL_LOCAL int  CheckCertCRL(WOLFSSL_CRL*, DecodedCert*);


#ifdef __cplusplus
    }  /* extern "C" */
#endif

#endif /* HAVE_CRL */
#endif /* WOLFSSL_CRL_H */
