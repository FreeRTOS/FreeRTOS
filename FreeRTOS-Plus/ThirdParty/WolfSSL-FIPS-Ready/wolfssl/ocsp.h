/* ocsp.h
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



/* wolfSSL OCSP API */

#ifndef WOLFSSL_OCSP_H
#define WOLFSSL_OCSP_H

#ifdef HAVE_OCSP

#include <wolfssl/ssl.h>
#include <wolfssl/wolfcrypt/asn.h>

#ifdef __cplusplus
    extern "C" {
#endif

typedef struct WOLFSSL_OCSP WOLFSSL_OCSP;

#if defined(OPENSSL_ALL) || defined(OPENSSL_EXTRA) || defined(WOLFSSL_NGINX) ||\
    defined(WOLFSSL_HAPROXY)
typedef struct OcspResponse WOLFSSL_OCSP_BASICRESP;

typedef struct OcspRequest WOLFSSL_OCSP_CERTID;

typedef struct OcspRequest WOLFSSL_OCSP_ONEREQ;

typedef struct OcspRequest WOLFSSL_OCSP_REQUEST;
#endif

WOLFSSL_LOCAL int  InitOCSP(WOLFSSL_OCSP*, WOLFSSL_CERT_MANAGER*);
WOLFSSL_LOCAL void FreeOCSP(WOLFSSL_OCSP*, int dynamic);

WOLFSSL_LOCAL int  CheckCertOCSP(WOLFSSL_OCSP*, DecodedCert*,
                                           WOLFSSL_BUFFER_INFO* responseBuffer);
WOLFSSL_LOCAL int  CheckCertOCSP_ex(WOLFSSL_OCSP*, DecodedCert*,
                             WOLFSSL_BUFFER_INFO* responseBuffer, WOLFSSL* ssl);
WOLFSSL_LOCAL int  CheckOcspRequest(WOLFSSL_OCSP* ocsp,
                 OcspRequest* ocspRequest, WOLFSSL_BUFFER_INFO* responseBuffer);
WOLFSSL_LOCAL int CheckOcspResponse(WOLFSSL_OCSP *ocsp, byte *response, int responseSz,
                                    WOLFSSL_BUFFER_INFO *responseBuffer, CertStatus *status,
                                    OcspEntry *entry, OcspRequest *ocspRequest);

#if defined(OPENSSL_ALL) || defined(WOLFSSL_NGINX) || defined(WOLFSSL_HAPROXY) || \
    defined(WOLFSSL_APACHE_HTTPD)

    WOLFSSL_API int wolfSSL_OCSP_resp_find_status(WOLFSSL_OCSP_BASICRESP *bs,
                                                  WOLFSSL_OCSP_CERTID *id, int *status, int *reason,
                                                  WOLFSSL_ASN1_TIME **revtime, WOLFSSL_ASN1_TIME **thisupd,
                                                  WOLFSSL_ASN1_TIME **nextupd);
WOLFSSL_API const char *wolfSSL_OCSP_cert_status_str(long s);
WOLFSSL_API int wolfSSL_OCSP_check_validity(WOLFSSL_ASN1_TIME* thisupd,
    WOLFSSL_ASN1_TIME* nextupd, long sec, long maxsec);

WOLFSSL_API void wolfSSL_OCSP_CERTID_free(WOLFSSL_OCSP_CERTID* certId);
WOLFSSL_API WOLFSSL_OCSP_CERTID* wolfSSL_OCSP_cert_to_id(
    const WOLFSSL_EVP_MD *dgst, const WOLFSSL_X509 *subject,
    const WOLFSSL_X509 *issuer);

WOLFSSL_API void wolfSSL_OCSP_BASICRESP_free(WOLFSSL_OCSP_BASICRESP* basicResponse);
WOLFSSL_API int wolfSSL_OCSP_basic_verify(WOLFSSL_OCSP_BASICRESP *bs,
    WOLF_STACK_OF(WOLFSSL_X509) *certs, WOLFSSL_X509_STORE *st, unsigned long flags);

WOLFSSL_API void wolfSSL_OCSP_RESPONSE_free(OcspResponse* response);
WOLFSSL_API OcspResponse* wolfSSL_d2i_OCSP_RESPONSE_bio(WOLFSSL_BIO* bio,
    OcspResponse** response);
WOLFSSL_API OcspResponse* wolfSSL_d2i_OCSP_RESPONSE(OcspResponse** response,
    const unsigned char** data, int len);
WOLFSSL_API int wolfSSL_i2d_OCSP_RESPONSE(OcspResponse* response,
    unsigned char** data);
WOLFSSL_API int wolfSSL_OCSP_response_status(OcspResponse *response);
WOLFSSL_API const char *wolfSSL_OCSP_response_status_str(long s);
WOLFSSL_API WOLFSSL_OCSP_BASICRESP* wolfSSL_OCSP_response_get1_basic(
    OcspResponse* response);

WOLFSSL_API OcspRequest* wolfSSL_OCSP_REQUEST_new(void);
WOLFSSL_API void wolfSSL_OCSP_REQUEST_free(OcspRequest* request);
WOLFSSL_API int wolfSSL_i2d_OCSP_REQUEST(OcspRequest* request,
    unsigned char** data);
WOLFSSL_API WOLFSSL_OCSP_ONEREQ* wolfSSL_OCSP_request_add0_id(OcspRequest *req,
    WOLFSSL_OCSP_CERTID *cid);
WOLFSSL_API WOLFSSL_OCSP_CERTID* wolfSSL_OCSP_CERTID_dup(WOLFSSL_OCSP_CERTID*);
WOLFSSL_API int wolfSSL_i2d_OCSP_REQUEST_bio(WOLFSSL_BIO* out,
    WOLFSSL_OCSP_REQUEST *req);

#endif
#ifdef OPENSSL_EXTRA
WOLFSSL_API int wolfSSL_OCSP_REQUEST_add_ext(OcspRequest* req,
        WOLFSSL_X509_EXTENSION* ext, int idx);
WOLFSSL_API OcspResponse* wolfSSL_OCSP_response_create(int status,
    WOLFSSL_OCSP_BASICRESP* bs);
WOLFSSL_API const char* wolfSSL_OCSP_crl_reason_str(long s);

WOLFSSL_API int wolfSSL_OCSP_id_get0_info(WOLFSSL_ASN1_STRING**,
  WOLFSSL_ASN1_OBJECT**, WOLFSSL_ASN1_STRING**,
  WOLFSSL_ASN1_INTEGER**, WOLFSSL_OCSP_CERTID*);

WOLFSSL_API int wolfSSL_OCSP_request_add1_nonce(OcspRequest* req,
        unsigned char* val, int sz);
WOLFSSL_API int wolfSSL_OCSP_check_nonce(OcspRequest* req,
        WOLFSSL_OCSP_BASICRESP* bs);
#endif


#ifdef __cplusplus
    }  /* extern "C" */
#endif


#endif /* HAVE_OCSP */
#endif /* WOLFSSL_OCSP_H */


