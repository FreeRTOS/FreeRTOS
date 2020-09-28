/* x509v3.h
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

/* x509v3.h for openSSL */

#ifndef WOLFSSL_x509v3_H
#define WOLFSSL_x509v3_H

#include <wolfssl/openssl/conf.h>
#include <wolfssl/openssl/bio.h>

#ifdef __cplusplus
    extern "C" {
#endif

#define X509_PURPOSE_SSL_CLIENT       0
#define X509_PURPOSE_SSL_SERVER       1

#define NS_SSL_CLIENT                 0
#define NS_SSL_SERVER                 1

/* Forward reference */

typedef void *(*X509V3_EXT_D2I)(void *, const unsigned char **, long);
typedef int (*X509V3_EXT_I2D) (void *, unsigned char **);
typedef STACK_OF(CONF_VALUE) *(*X509V3_EXT_I2V) (
                                struct WOLFSSL_v3_ext_method *method,
                                void *ext, STACK_OF(CONF_VALUE) *extlist);
typedef char *(*X509V3_EXT_I2S)(struct WOLFSSL_v3_ext_method *method, void *ext);
typedef int (*X509V3_EXT_I2R) (struct WOLFSSL_v3_ext_method *method,
                               void *ext, BIO *out, int indent);
typedef struct WOLFSSL_v3_ext_method X509V3_EXT_METHOD;

struct WOLFSSL_v3_ext_method {
    int ext_nid;
    int ext_flags;
    void *usr_data;
    X509V3_EXT_D2I d2i;
    X509V3_EXT_I2D i2d;
    X509V3_EXT_I2V i2v;
    X509V3_EXT_I2S i2s;
    X509V3_EXT_I2R i2r;
};

struct WOLFSSL_X509_EXTENSION {
    WOLFSSL_ASN1_OBJECT *obj;
    WOLFSSL_ASN1_BOOLEAN crit;
    ASN1_OCTET_STRING value; /* DER format of extension */
    WOLFSSL_v3_ext_method ext_method;
    WOLFSSL_STACK* ext_sk; /* For extension specific data */
};

#define WOLFSSL_ASN1_BOOLEAN int
#define GEN_OTHERNAME   0
#define GEN_EMAIL       1
#define GEN_DNS         2
#define GEN_X400        3
#define GEN_DIRNAME     4
#define GEN_EDIPARTY    5
#define GEN_URI         6
#define GEN_IPADD       7
#define GEN_RID         8

#define GENERAL_NAME       WOLFSSL_GENERAL_NAME

#define X509V3_CTX         WOLFSSL_X509V3_CTX

typedef struct WOLFSSL_AUTHORITY_KEYID AUTHORITY_KEYID;
typedef struct WOLFSSL_BASIC_CONSTRAINTS BASIC_CONSTRAINTS;
typedef struct WOLFSSL_ACCESS_DESCRIPTION ACCESS_DESCRIPTION;
typedef WOLF_STACK_OF(WOLFSSL_ACCESS_DESCRIPTION) WOLFSSL_AUTHORITY_INFO_ACCESS;

WOLFSSL_API WOLFSSL_BASIC_CONSTRAINTS* wolfSSL_BASIC_CONSTRAINTS_new(void);
WOLFSSL_API void wolfSSL_BASIC_CONSTRAINTS_free(WOLFSSL_BASIC_CONSTRAINTS *bc);
WOLFSSL_API WOLFSSL_AUTHORITY_KEYID* wolfSSL_AUTHORITY_KEYID_new(void);
WOLFSSL_API void wolfSSL_AUTHORITY_KEYID_free(WOLFSSL_AUTHORITY_KEYID *id);
WOLFSSL_API const WOLFSSL_v3_ext_method* wolfSSL_X509V3_EXT_get(
                                                    WOLFSSL_X509_EXTENSION* ex);
WOLFSSL_API void* wolfSSL_X509V3_EXT_d2i(WOLFSSL_X509_EXTENSION* ex);
WOLFSSL_API char* wolfSSL_i2s_ASN1_STRING(WOLFSSL_v3_ext_method *method,
                                          const WOLFSSL_ASN1_STRING *s);
WOLFSSL_API int wolfSSL_X509V3_EXT_print(WOLFSSL_BIO *out,
        WOLFSSL_X509_EXTENSION *ext, unsigned long flag, int indent);

#define BASIC_CONSTRAINTS_free    wolfSSL_BASIC_CONSTRAINTS_free
#define AUTHORITY_KEYID_free      wolfSSL_AUTHORITY_KEYID_free
#define SSL_CTX_get_cert_store(x) wolfSSL_CTX_get_cert_store ((WOLFSSL_CTX*) (x))
#define ASN1_INTEGER              WOLFSSL_ASN1_INTEGER
#define ASN1_OCTET_STRING         WOLFSSL_ASN1_STRING
#define X509V3_EXT_get            wolfSSL_X509V3_EXT_get
#define X509V3_EXT_d2i            wolfSSL_X509V3_EXT_d2i
#define i2s_ASN1_OCTET_STRING     wolfSSL_i2s_ASN1_STRING
#define X509V3_EXT_print          wolfSSL_X509V3_EXT_print
#define X509V3_EXT_conf_nid wolfSSL_X509V3_EXT_conf_nid
#define X509V3_set_ctx      wolfSSL_X509V3_set_ctx
#define X509V3_set_ctx_nodb wolfSSL_X509V3_set_ctx_nodb

#ifdef  __cplusplus
}
#endif

#endif
