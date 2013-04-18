/* ssl.h
 *
 * Copyright (C) 2006-2012 Sawtooth Consulting Ltd.
 *
 * This file is part of CyaSSL.
 *
 * CyaSSL is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * CyaSSL is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA
 */


/* CyaSSL API */

#ifndef CYASSL_SSL_H
#define CYASSL_SSL_H


/* for users not using preprocessor flags*/
#include <cyassl/ctaocrypt/settings.h>
#include <cyassl/version.h>


#ifndef NO_FILESYSTEM
    #include <stdio.h>   /* ERR_printf */
#endif

#ifdef YASSL_PREFIX
    #include "prefix_ssl.h"
#endif

#ifdef LIBCYASSL_VERSION_STRING
    #define CYASSL_VERSION LIBCYASSL_VERSION_STRING
#endif

#ifdef _WIN32
    /* wincrypt.h clashes */
    #undef OCSP_REQUEST
    #undef OCSP_RESPONSE
#endif



#ifdef __cplusplus
    extern "C" {
#endif


typedef struct CYASSL          CYASSL;          
typedef struct CYASSL_SESSION  CYASSL_SESSION;
typedef struct CYASSL_METHOD   CYASSL_METHOD;
typedef struct CYASSL_CTX      CYASSL_CTX;

typedef struct CYASSL_X509       CYASSL_X509;
typedef struct CYASSL_X509_NAME  CYASSL_X509_NAME;
typedef struct CYASSL_X509_CHAIN CYASSL_X509_CHAIN;

typedef struct CYASSL_CERT_MANAGER CYASSL_CERT_MANAGER;

/* redeclare guard */
#define CYASSL_TYPES_DEFINED


typedef struct CYASSL_RSA            CYASSL_RSA;
typedef struct CYASSL_DSA            CYASSL_DSA;
typedef struct CYASSL_CIPHER         CYASSL_CIPHER;
typedef struct CYASSL_X509_LOOKUP    CYASSL_X509_LOOKUP;
typedef struct CYASSL_X509_LOOKUP_METHOD CYASSL_X509_LOOKUP_METHOD;
typedef struct CYASSL_X509_CRL       CYASSL_X509_CRL;
typedef struct CYASSL_BIO            CYASSL_BIO;
typedef struct CYASSL_BIO_METHOD     CYASSL_BIO_METHOD;
typedef struct CYASSL_X509_EXTENSION CYASSL_X509_EXTENSION;
typedef struct CYASSL_ASN1_TIME      CYASSL_ASN1_TIME;
typedef struct CYASSL_ASN1_INTEGER   CYASSL_ASN1_INTEGER;
typedef struct CYASSL_ASN1_OBJECT    CYASSL_ASN1_OBJECT;
typedef struct CYASSL_ASN1_STRING    CYASSL_ASN1_STRING;
typedef struct CYASSL_dynlock_value  CYASSL_dynlock_value;

#define CYASSL_ASN1_UTCTIME CYASSL_ASN1_TIME

typedef struct CYASSL_EVP_PKEY {
    int type;         /* openssh dereference */
    int save_type;    /* openssh dereference */
} CYASSL_EVP_PKEY;

typedef struct CYASSL_MD4_CTX {
    int buffer[32];      /* big enough to hold, check size in Init */
} CYASSL_MD4_CTX;


typedef struct CYASSL_COMP_METHOD {
    int type;            /* stunnel dereference */
} CYASSL_COMP_METHOD;


typedef struct CYASSL_X509_STORE {
    int cache;          /* stunnel dereference */
} CYASSL_X509_STORE;


typedef struct CYASSL_X509_REVOKED {
    CYASSL_ASN1_INTEGER* serialNumber;          /* stunnel dereference */
} CYASSL_X509_REVOKED;


typedef struct CYASSL_X509_OBJECT {
    union {
        char* ptr;
        CYASSL_X509_CRL* crl;           /* stunnel dereference */
    } data;
} CYASSL_X509_OBJECT;


/* in internal.h too, change there !! */
typedef struct CYASSL_X509_STORE_CTX {
    int   error;
    int   error_depth;
    CYASSL_X509* current_cert;   /* stunnel dereference */
    char* domain;                /* subject CN domain name */
    void* ex_data;               /* external data, for fortress build */
    /* in internal.h too, change there !! */
} CYASSL_X509_STORE_CTX;


CYASSL_API CYASSL_METHOD *CyaSSLv3_server_method(void);
CYASSL_API CYASSL_METHOD *CyaSSLv3_client_method(void);
CYASSL_API CYASSL_METHOD *CyaTLSv1_server_method(void);  
CYASSL_API CYASSL_METHOD *CyaTLSv1_client_method(void);
CYASSL_API CYASSL_METHOD *CyaTLSv1_1_server_method(void);  
CYASSL_API CYASSL_METHOD *CyaTLSv1_1_client_method(void);
CYASSL_API CYASSL_METHOD *CyaTLSv1_2_server_method(void);  
CYASSL_API CYASSL_METHOD *CyaTLSv1_2_client_method(void);

#ifdef CYASSL_DTLS
    CYASSL_API CYASSL_METHOD *CyaDTLSv1_client_method(void);
    CYASSL_API CYASSL_METHOD *CyaDTLSv1_server_method(void);
#endif

#ifndef NO_FILESYSTEM

CYASSL_API int CyaSSL_CTX_use_certificate_file(CYASSL_CTX*, const char*, int);
CYASSL_API int CyaSSL_CTX_use_PrivateKey_file(CYASSL_CTX*, const char*, int);
CYASSL_API int CyaSSL_CTX_load_verify_locations(CYASSL_CTX*, const char*,
                                                const char*);
CYASSL_API int CyaSSL_CTX_use_certificate_chain_file(CYASSL_CTX *,
                                                     const char *file);
CYASSL_API int CyaSSL_CTX_use_RSAPrivateKey_file(CYASSL_CTX*, const char*, int);

CYASSL_API int CyaSSL_use_certificate_file(CYASSL*, const char*, int);
CYASSL_API int CyaSSL_use_PrivateKey_file(CYASSL*, const char*, int);
CYASSL_API int CyaSSL_use_certificate_chain_file(CYASSL*, const char *file);
CYASSL_API int CyaSSL_use_RSAPrivateKey_file(CYASSL*, const char*, int);

#ifdef CYASSL_DER_LOAD
    CYASSL_API int CyaSSL_CTX_der_load_verify_locations(CYASSL_CTX*,
                                                    const char*, int);
#endif

#ifdef HAVE_NTRU
    CYASSL_API int CyaSSL_CTX_use_NTRUPrivateKey_file(CYASSL_CTX*, const char*);
    /* load NTRU private key blob */
#endif

CYASSL_API int CyaSSL_PemCertToDer(const char*, unsigned char*, int);

#endif /* NO_FILESYSTEM */

CYASSL_API CYASSL_CTX* CyaSSL_CTX_new(CYASSL_METHOD*);
CYASSL_API CYASSL* CyaSSL_new(CYASSL_CTX*);
CYASSL_API int  CyaSSL_set_fd (CYASSL*, int);
CYASSL_API int  CyaSSL_get_fd(const CYASSL*);
CYASSL_API int  CyaSSL_connect(CYASSL*);     /* please see note at top of README
                                             if you get an error from connect */
CYASSL_API int  CyaSSL_write(CYASSL*, const void*, int);
CYASSL_API int  CyaSSL_read(CYASSL*, void*, int);
CYASSL_API int  CyaSSL_accept(CYASSL*);
CYASSL_API void CyaSSL_CTX_free(CYASSL_CTX*);
CYASSL_API void CyaSSL_free(CYASSL*);
CYASSL_API int  CyaSSL_shutdown(CYASSL*);

CYASSL_API void CyaSSL_CTX_set_quiet_shutdown(CYASSL_CTX*, int);
CYASSL_API void CyaSSL_set_quiet_shutdown(CYASSL*, int);

CYASSL_API int  CyaSSL_get_error(CYASSL*, int);

CYASSL_API int          CyaSSL_set_session(CYASSL* ssl,CYASSL_SESSION* session);
CYASSL_API CYASSL_SESSION* CyaSSL_get_session(CYASSL* ssl);
CYASSL_API void         CyaSSL_flush_sessions(CYASSL_CTX *ctx, long tm);


typedef int (*VerifyCallback)(int, CYASSL_X509_STORE_CTX*);
typedef int (*pem_password_cb)(char*, int, int, void*);

CYASSL_API void CyaSSL_CTX_set_verify(CYASSL_CTX*, int, 
                                      VerifyCallback verify_callback);
CYASSL_API void CyaSSL_set_verify(CYASSL*, int, VerifyCallback verify_callback);

CYASSL_API int  CyaSSL_pending(CYASSL*);

CYASSL_API void CyaSSL_load_error_strings(void);
CYASSL_API int  CyaSSL_library_init(void);
CYASSL_API long CyaSSL_CTX_set_session_cache_mode(CYASSL_CTX*, long);

/* only supports full name from cipher_name[] delimited by : */
CYASSL_API int  CyaSSL_CTX_set_cipher_list(CYASSL_CTX*, const char*);
CYASSL_API int  CyaSSL_set_cipher_list(CYASSL*, const char*);

CYASSL_API int   CyaSSL_ERR_GET_REASON(int err);
CYASSL_API char* CyaSSL_ERR_error_string(unsigned long,char*);
CYASSL_API void  CyaSSL_ERR_error_string_n(unsigned long e, char* buf,
                                           unsigned long sz);

/* extras */

#define STACK_OF(x) x

CYASSL_API int  CyaSSL_set_ex_data(CYASSL*, int, void*);
CYASSL_API int  CyaSSL_get_shutdown(const CYASSL*);
CYASSL_API int  CyaSSL_set_rfd(CYASSL*, int);
CYASSL_API int  CyaSSL_set_wfd(CYASSL*, int);
CYASSL_API void CyaSSL_set_shutdown(CYASSL*, int);
CYASSL_API int  CyaSSL_set_session_id_context(CYASSL*, const unsigned char*,
                                           unsigned int);
CYASSL_API void CyaSSL_set_connect_state(CYASSL*);
CYASSL_API void CyaSSL_set_accept_state(CYASSL*);
CYASSL_API int  CyaSSL_session_reused(CYASSL*);
CYASSL_API void CyaSSL_SESSION_free(CYASSL_SESSION* session);
CYASSL_API int  CyaSSL_is_init_finished(CYASSL*);

CYASSL_API const char*  CyaSSL_get_version(CYASSL*);
CYASSL_API CYASSL_CIPHER*  CyaSSL_get_current_cipher(CYASSL*);
CYASSL_API char*        CyaSSL_CIPHER_description(CYASSL_CIPHER*, char*, int);
CYASSL_API const char*  CyaSSL_CIPHER_get_name(const CYASSL_CIPHER* cipher);
CYASSL_API const char*  CyaSSL_get_cipher(CYASSL*);
CYASSL_API CYASSL_SESSION* CyaSSL_get1_session(CYASSL* ssl);
                           /* what's ref count */

CYASSL_API void CyaSSL_X509_free(CYASSL_X509*);
CYASSL_API void CyaSSL_OPENSSL_free(void*);

CYASSL_API int CyaSSL_OCSP_parse_url(char* url, char** host, char** port,
                                     char** path, int* ssl);

CYASSL_API CYASSL_METHOD* CyaSSLv23_client_method(void);
CYASSL_API CYASSL_METHOD* CyaSSLv2_client_method(void);
CYASSL_API CYASSL_METHOD* CyaSSLv2_server_method(void);

CYASSL_API void CyaSSL_MD4_Init(CYASSL_MD4_CTX*);
CYASSL_API void CyaSSL_MD4_Update(CYASSL_MD4_CTX*, const void*, unsigned long);
CYASSL_API void CyaSSL_MD4_Final(unsigned char*, CYASSL_MD4_CTX*);


CYASSL_API CYASSL_BIO* CyaSSL_BIO_new(CYASSL_BIO_METHOD*);
CYASSL_API int  CyaSSL_BIO_free(CYASSL_BIO*);
CYASSL_API int  CyaSSL_BIO_free_all(CYASSL_BIO*);
CYASSL_API int  CyaSSL_BIO_read(CYASSL_BIO*, void*, int);
CYASSL_API int  CyaSSL_BIO_write(CYASSL_BIO*, const void*, int);
CYASSL_API CYASSL_BIO* CyaSSL_BIO_push(CYASSL_BIO*, CYASSL_BIO* append);
CYASSL_API CYASSL_BIO* CyaSSL_BIO_pop(CYASSL_BIO*);
CYASSL_API int  CyaSSL_BIO_flush(CYASSL_BIO*);
CYASSL_API int  CyaSSL_BIO_pending(CYASSL_BIO*);

CYASSL_API CYASSL_BIO_METHOD* CyaSSL_BIO_f_buffer(void);
CYASSL_API long CyaSSL_BIO_set_write_buffer_size(CYASSL_BIO*, long size);
CYASSL_API CYASSL_BIO_METHOD* CyaSSL_BIO_f_ssl(void);
CYASSL_API CYASSL_BIO*        CyaSSL_BIO_new_socket(int sfd, int flag);
CYASSL_API int         CyaSSL_BIO_eof(CYASSL_BIO*);

CYASSL_API CYASSL_BIO_METHOD* CyaSSL_BIO_s_mem(void);
CYASSL_API CYASSL_BIO_METHOD* CyaSSL_BIO_f_base64(void);
CYASSL_API void CyaSSL_BIO_set_flags(CYASSL_BIO*, int);

CYASSL_API int CyaSSL_BIO_get_mem_data(CYASSL_BIO* bio,const unsigned char** p);
CYASSL_API CYASSL_BIO* CyaSSL_BIO_new_mem_buf(void* buf, int len);


CYASSL_API long        CyaSSL_BIO_set_ssl(CYASSL_BIO*, CYASSL*, int flag);
CYASSL_API void        CyaSSL_set_bio(CYASSL*, CYASSL_BIO* rd, CYASSL_BIO* wr);

CYASSL_API int  CyaSSL_add_all_algorithms(void);

CYASSL_API void        CyaSSL_RAND_screen(void);
CYASSL_API const char* CyaSSL_RAND_file_name(char*, unsigned long);
CYASSL_API int         CyaSSL_RAND_write_file(const char*);
CYASSL_API int         CyaSSL_RAND_load_file(const char*, long);
CYASSL_API int         CyaSSL_RAND_egd(const char*);
CYASSL_API int         CyaSSL_RAND_seed(const void*, int);
CYASSL_API void        CyaSSL_RAND_add(const void*, int, double);

CYASSL_API CYASSL_COMP_METHOD* CyaSSL_COMP_zlib(void);
CYASSL_API CYASSL_COMP_METHOD* CyaSSL_COMP_rle(void);
CYASSL_API int CyaSSL_COMP_add_compression_method(int, void*);

CYASSL_API int CyaSSL_get_ex_new_index(long, void*, void*, void*, void*);

CYASSL_API void CyaSSL_set_id_callback(unsigned long (*f)(void));
CYASSL_API void CyaSSL_set_locking_callback(void (*f)(int, int, const char*,
                                                      int));
CYASSL_API void CyaSSL_set_dynlock_create_callback(CYASSL_dynlock_value* (*f)
                                                   (const char*, int));
CYASSL_API void CyaSSL_set_dynlock_lock_callback(void (*f)(int,
                                      CYASSL_dynlock_value*, const char*, int));
CYASSL_API void CyaSSL_set_dynlock_destroy_callback(void (*f)
                                     (CYASSL_dynlock_value*, const char*, int));
CYASSL_API int  CyaSSL_num_locks(void);

CYASSL_API CYASSL_X509* CyaSSL_X509_STORE_CTX_get_current_cert(
                                                        CYASSL_X509_STORE_CTX*);
CYASSL_API int   CyaSSL_X509_STORE_CTX_get_error(CYASSL_X509_STORE_CTX*);
CYASSL_API int   CyaSSL_X509_STORE_CTX_get_error_depth(CYASSL_X509_STORE_CTX*);

CYASSL_API char*       CyaSSL_X509_NAME_oneline(CYASSL_X509_NAME*, char*, int);
CYASSL_API CYASSL_X509_NAME*  CyaSSL_X509_get_issuer_name(CYASSL_X509*);
CYASSL_API CYASSL_X509_NAME*  CyaSSL_X509_get_subject_name(CYASSL_X509*);
CYASSL_API const char* CyaSSL_X509_verify_cert_error_string(long);

CYASSL_API int CyaSSL_X509_LOOKUP_add_dir(CYASSL_X509_LOOKUP*,const char*,long);
CYASSL_API int CyaSSL_X509_LOOKUP_load_file(CYASSL_X509_LOOKUP*, const char*,
                                            long);
CYASSL_API CYASSL_X509_LOOKUP_METHOD* CyaSSL_X509_LOOKUP_hash_dir(void);
CYASSL_API CYASSL_X509_LOOKUP_METHOD* CyaSSL_X509_LOOKUP_file(void);

CYASSL_API CYASSL_X509_LOOKUP* CyaSSL_X509_STORE_add_lookup(CYASSL_X509_STORE*,
                                                    CYASSL_X509_LOOKUP_METHOD*);
CYASSL_API CYASSL_X509_STORE*  CyaSSL_X509_STORE_new(void);
CYASSL_API int          CyaSSL_X509_STORE_get_by_subject(CYASSL_X509_STORE_CTX*,
                                   int, CYASSL_X509_NAME*, CYASSL_X509_OBJECT*);
CYASSL_API int  CyaSSL_X509_STORE_CTX_init(CYASSL_X509_STORE_CTX*,
                      CYASSL_X509_STORE*, CYASSL_X509*, STACK_OF(CYASSL_X509)*);
CYASSL_API void CyaSSL_X509_STORE_CTX_cleanup(CYASSL_X509_STORE_CTX*);

CYASSL_API CYASSL_ASN1_TIME* CyaSSL_X509_CRL_get_lastUpdate(CYASSL_X509_CRL*);
CYASSL_API CYASSL_ASN1_TIME* CyaSSL_X509_CRL_get_nextUpdate(CYASSL_X509_CRL*);

CYASSL_API CYASSL_EVP_PKEY* CyaSSL_X509_get_pubkey(CYASSL_X509*);
CYASSL_API int       CyaSSL_X509_CRL_verify(CYASSL_X509_CRL*, CYASSL_EVP_PKEY*);
CYASSL_API void      CyaSSL_X509_STORE_CTX_set_error(CYASSL_X509_STORE_CTX*,
                                                     int);
CYASSL_API void      CyaSSL_X509_OBJECT_free_contents(CYASSL_X509_OBJECT*);
CYASSL_API void      CyaSSL_EVP_PKEY_free(CYASSL_EVP_PKEY*);
CYASSL_API int       CyaSSL_X509_cmp_current_time(const CYASSL_ASN1_TIME*);
CYASSL_API int       CyaSSL_sk_X509_REVOKED_num(CYASSL_X509_REVOKED*);

CYASSL_API CYASSL_X509_REVOKED* CyaSSL_X509_CRL_get_REVOKED(CYASSL_X509_CRL*);
CYASSL_API CYASSL_X509_REVOKED* CyaSSL_sk_X509_REVOKED_value(
                                                      CYASSL_X509_REVOKED*,int);
CYASSL_API CYASSL_ASN1_INTEGER* CyaSSL_X509_get_serialNumber(CYASSL_X509*);

CYASSL_API int CyaSSL_ASN1_TIME_print(CYASSL_BIO*, const CYASSL_ASN1_TIME*);

CYASSL_API int  CyaSSL_ASN1_INTEGER_cmp(const CYASSL_ASN1_INTEGER*,
                                       const CYASSL_ASN1_INTEGER*);
CYASSL_API long CyaSSL_ASN1_INTEGER_get(const CYASSL_ASN1_INTEGER*);

CYASSL_API STACK_OF(CYASSL_X509_NAME)* CyaSSL_load_client_CA_file(const char*);

CYASSL_API void  CyaSSL_CTX_set_client_CA_list(CYASSL_CTX*,
                                               STACK_OF(CYASSL_X509_NAME)*);
CYASSL_API void* CyaSSL_X509_STORE_CTX_get_ex_data(CYASSL_X509_STORE_CTX*, int);
CYASSL_API int   CyaSSL_get_ex_data_X509_STORE_CTX_idx(void);
CYASSL_API void* CyaSSL_get_ex_data(const CYASSL*, int);

CYASSL_API void CyaSSL_CTX_set_default_passwd_cb_userdata(CYASSL_CTX*,
                                                          void* userdata);
CYASSL_API void CyaSSL_CTX_set_default_passwd_cb(CYASSL_CTX*, pem_password_cb);


CYASSL_API void CyaSSL_CTX_set_info_callback(CYASSL_CTX*, void (*)(void));

CYASSL_API unsigned long CyaSSL_ERR_peek_error(void);
CYASSL_API int           CyaSSL_GET_REASON(int);

CYASSL_API char* CyaSSL_alert_type_string_long(int);
CYASSL_API char* CyaSSL_alert_desc_string_long(int);
CYASSL_API char* CyaSSL_state_string_long(CYASSL*);

CYASSL_API CYASSL_RSA* CyaSSL_RSA_generate_key(int, unsigned long,
                                               void(*)(int, int, void*), void*);
CYASSL_API void CyaSSL_CTX_set_tmp_rsa_callback(CYASSL_CTX*,
                                             CYASSL_RSA*(*)(CYASSL*, int, int));

CYASSL_API int CyaSSL_PEM_def_callback(char*, int num, int w, void* key);

CYASSL_API long CyaSSL_CTX_sess_accept(CYASSL_CTX*);
CYASSL_API long CyaSSL_CTX_sess_connect(CYASSL_CTX*);
CYASSL_API long CyaSSL_CTX_sess_accept_good(CYASSL_CTX*);
CYASSL_API long CyaSSL_CTX_sess_connect_good(CYASSL_CTX*);
CYASSL_API long CyaSSL_CTX_sess_accept_renegotiate(CYASSL_CTX*);
CYASSL_API long CyaSSL_CTX_sess_connect_renegotiate(CYASSL_CTX*);
CYASSL_API long CyaSSL_CTX_sess_hits(CYASSL_CTX*);
CYASSL_API long CyaSSL_CTX_sess_cb_hits(CYASSL_CTX*);
CYASSL_API long CyaSSL_CTX_sess_cache_full(CYASSL_CTX*);
CYASSL_API long CyaSSL_CTX_sess_misses(CYASSL_CTX*);
CYASSL_API long CyaSSL_CTX_sess_timeouts(CYASSL_CTX*);
CYASSL_API long CyaSSL_CTX_sess_number(CYASSL_CTX*);
CYASSL_API long CyaSSL_CTX_sess_get_cache_size(CYASSL_CTX*);


#define CYASSL_DEFAULT_CIPHER_LIST ""   /* default all */
#define CYASSL_RSA_F4 0x10001L

enum {
    OCSP_NOCERTS     = 1,
    OCSP_NOINTERN    = 2,
    OCSP_NOSIGS      = 4,
    OCSP_NOCHAIN     = 8,
    OCSP_NOVERIFY    = 16,
    OCSP_NOEXPLICIT  = 32,
    OCSP_NOCASIGN    = 64,
    OCSP_NODELEGATED = 128,
    OCSP_NOCHECKS    = 256,
    OCSP_TRUSTOTHER  = 512,
    OCSP_RESPID_KEY  = 1024,
    OCSP_NOTIME      = 2048,

    OCSP_CERTID   = 2,
    OCSP_REQUEST  = 4,
    OCSP_RESPONSE = 8,
    OCSP_BASICRESP = 16,

    CYASSL_CRL_CHECKALL = 1,

    ASN1_GENERALIZEDTIME = 4,

    SSL_OP_MICROSOFT_SESS_ID_BUG = 1,
    SSL_OP_NETSCAPE_CHALLENGE_BUG = 2,
    SSL_OP_NETSCAPE_REUSE_CIPHER_CHANGE_BUG = 3,
    SSL_OP_SSLREF2_REUSE_CERT_TYPE_BUG = 4,
    SSL_OP_MICROSOFT_BIG_SSLV3_BUFFER = 5,
    SSL_OP_MSIE_SSLV2_RSA_PADDING = 6,
    SSL_OP_SSLEAY_080_CLIENT_DH_BUG = 7,
    SSL_OP_TLS_D5_BUG = 8,
    SSL_OP_TLS_BLOCK_PADDING_BUG = 9,
    SSL_OP_TLS_ROLLBACK_BUG = 10,
    SSL_OP_ALL = 11,
    SSL_OP_EPHEMERAL_RSA = 12,
    SSL_OP_NO_SSLv3 = 13,
    SSL_OP_NO_TLSv1 = 14,
    SSL_OP_PKCS1_CHECK_1 = 15,
    SSL_OP_PKCS1_CHECK_2 = 16,
    SSL_OP_NETSCAPE_CA_DN_BUG = 17,
    SSL_OP_NETSCAPE_DEMO_CIPHER_CHANGE_BUG = 18,
    SSL_OP_SINGLE_DH_USE = 19,
    SSL_OP_NO_TICKET = 20,
    SSL_OP_DONT_INSERT_EMPTY_FRAGMENTS = 21,
    SSL_OP_NO_QUERY_MTU = 22,
    SSL_OP_COOKIE_EXCHANGE = 23,
    SSL_OP_NO_SESSION_RESUMPTION_ON_RENEGOTIATION = 24,
    SSL_OP_SINGLE_ECDH_USE = 25,
    SSL_OP_CIPHER_SERVER_PREFERENCE = 26,

    SSL_MAX_SSL_SESSION_ID_LENGTH = 32,

    EVP_R_BAD_DECRYPT = 2,

    SSL_CB_LOOP = 4,
    SSL_ST_CONNECT = 5,
    SSL_ST_ACCEPT  = 6,
    SSL_CB_ALERT   = 7,
    SSL_CB_READ    = 8,
    SSL_CB_HANDSHAKE_DONE = 9,

    SSL_MODE_ENABLE_PARTIAL_WRITE = 2,

    BIO_FLAGS_BASE64_NO_NL = 1,
    BIO_CLOSE   = 1,
    BIO_NOCLOSE = 0,

    NID_undef = 0,

    X509_FILETYPE_PEM = 8,
    X509_LU_X509      = 9,
    X509_LU_CRL       = 12,
    
    X509_V_ERR_CRL_SIGNATURE_FAILURE = 13,
    X509_V_ERR_ERROR_IN_CRL_NEXT_UPDATE_FIELD = 14,
    X509_V_ERR_CRL_HAS_EXPIRED                = 15,
    X509_V_ERR_CERT_REVOKED                   = 16,
    X509_V_ERR_CERT_CHAIN_TOO_LONG            = 17,
    X509_V_ERR_UNABLE_TO_GET_ISSUER_CERT      = 18,
    X509_V_ERR_CERT_NOT_YET_VALID             = 19,
    X509_V_ERR_ERROR_IN_CERT_NOT_BEFORE_FIELD = 20,
    X509_V_ERR_CERT_HAS_EXPIRED               = 21,
    X509_V_ERR_ERROR_IN_CERT_NOT_AFTER_FIELD  = 22,

    X509_V_OK = 0,

    CRYPTO_LOCK = 1,
    CRYPTO_NUM_LOCKS = 10
};

/* extras end */

#ifndef NO_FILESYSTEM
/* CyaSSL extension, provide last error from SSL_get_error
   since not using thread storage error queue */
CYASSL_API void  CyaSSL_ERR_print_errors_fp(FILE*, int err);
#endif

enum { /* ssl Constants */
    SSL_ERROR_NONE      =  0,   /* for most functions */
    SSL_FAILURE         =  0,   /* for some functions */
    SSL_SUCCESS         =  1,

    SSL_BAD_CERTTYPE    = -8,
    SSL_BAD_STAT        = -7,
    SSL_BAD_PATH        = -6,
    SSL_BAD_FILETYPE    = -5,
    SSL_BAD_FILE        = -4,
    SSL_NOT_IMPLEMENTED = -3,
    SSL_UNKNOWN         = -2,
    SSL_FATAL_ERROR     = -1,

    SSL_FILETYPE_ASN1    = 2,
    SSL_FILETYPE_PEM     = 1,
    SSL_FILETYPE_DEFAULT = 2, /* ASN1 */
    SSL_FILETYPE_RAW     = 3, /* NTRU raw key blob */

    SSL_VERIFY_NONE                 = 0,
    SSL_VERIFY_PEER                 = 1,
    SSL_VERIFY_FAIL_IF_NO_PEER_CERT = 2,
    SSL_VERIFY_CLIENT_ONCE          = 4,

    SSL_SESS_CACHE_OFF                = 30,
    SSL_SESS_CACHE_CLIENT             = 31,
    SSL_SESS_CACHE_SERVER             = 32,
    SSL_SESS_CACHE_BOTH               = 33,
    SSL_SESS_CACHE_NO_AUTO_CLEAR      = 34,
    SSL_SESS_CACHE_NO_INTERNAL_LOOKUP = 35,

    SSL_ERROR_WANT_READ        =  2,
    SSL_ERROR_WANT_WRITE       =  3,
    SSL_ERROR_WANT_CONNECT     =  7,
    SSL_ERROR_WANT_ACCEPT      =  8,
    SSL_ERROR_SYSCALL          =  5,
    SSL_ERROR_WANT_X509_LOOKUP = 83,
    SSL_ERROR_ZERO_RETURN      =  6,
    SSL_ERROR_SSL              = 85,

    SSL_SENT_SHUTDOWN     = 1,
    SSL_RECEIVED_SHUTDOWN = 2,
    SSL_MODE_ACCEPT_MOVING_WRITE_BUFFER = 4,
    SSL_OP_NO_SSLv2       = 8,

    SSL_R_SSL_HANDSHAKE_FAILURE           = 101,
    SSL_R_TLSV1_ALERT_UNKNOWN_CA          = 102,
    SSL_R_SSLV3_ALERT_CERTIFICATE_UNKNOWN = 103,
    SSL_R_SSLV3_ALERT_BAD_CERTIFICATE     = 104,

    PEM_BUFSIZE = 1024
};


#ifndef NO_PSK
    typedef unsigned int (*psk_client_callback)(CYASSL*, const char*, char*,
                                    unsigned int, unsigned char*, unsigned int);
    CYASSL_API void CyaSSL_CTX_set_psk_client_callback(CYASSL_CTX*,
                                                    psk_client_callback);
    CYASSL_API void CyaSSL_set_psk_client_callback(CYASSL*,psk_client_callback);

    CYASSL_API const char* CyaSSL_get_psk_identity_hint(const CYASSL*);
    CYASSL_API const char* CyaSSL_get_psk_identity(const CYASSL*);

    CYASSL_API int CyaSSL_CTX_use_psk_identity_hint(CYASSL_CTX*, const char*);
    CYASSL_API int CyaSSL_use_psk_identity_hint(CYASSL*, const char*);

    typedef unsigned int (*psk_server_callback)(CYASSL*, const char*,
                          unsigned char*, unsigned int);
    CYASSL_API void CyaSSL_CTX_set_psk_server_callback(CYASSL_CTX*,
                                                    psk_server_callback);
    CYASSL_API void CyaSSL_set_psk_server_callback(CYASSL*,psk_server_callback);

    #define PSK_TYPES_DEFINED
#endif /* NO_PSK */


/* extra begins */

enum {  /* ERR Constants */
    ERR_TXT_STRING = 1
};

CYASSL_API unsigned long CyaSSL_ERR_get_error_line_data(const char**, int*,
                                                 const char**, int *);

CYASSL_API unsigned long CyaSSL_ERR_get_error(void);
CYASSL_API void          CyaSSL_ERR_clear_error(void);


CYASSL_API int  CyaSSL_RAND_status(void);
CYASSL_API int  CyaSSL_RAND_bytes(unsigned char* buf, int num);
CYASSL_API CYASSL_METHOD *CyaSSLv23_server_method(void);
CYASSL_API long CyaSSL_CTX_set_options(CYASSL_CTX*, long);
CYASSL_API int  CyaSSL_CTX_check_private_key(CYASSL_CTX*);


CYASSL_API void CyaSSL_ERR_free_strings(void);
CYASSL_API void CyaSSL_ERR_remove_state(unsigned long);
CYASSL_API void CyaSSL_EVP_cleanup(void);

CYASSL_API void CyaSSL_cleanup_all_ex_data(void);
CYASSL_API long CyaSSL_CTX_set_mode(CYASSL_CTX* ctx, long mode);
CYASSL_API long CyaSSL_CTX_get_mode(CYASSL_CTX* ctx);
CYASSL_API void CyaSSL_CTX_set_default_read_ahead(CYASSL_CTX* ctx, int m);

CYASSL_API long CyaSSL_CTX_sess_set_cache_size(CYASSL_CTX*, long);

CYASSL_API int  CyaSSL_CTX_set_default_verify_paths(CYASSL_CTX*);
CYASSL_API int  CyaSSL_CTX_set_session_id_context(CYASSL_CTX*,
                                            const unsigned char*, unsigned int);
CYASSL_API CYASSL_X509* CyaSSL_get_peer_certificate(CYASSL* ssl);

CYASSL_API int CyaSSL_want_read(CYASSL*);
CYASSL_API int CyaSSL_want_write(CYASSL*);

CYASSL_API int CyaSSL_BIO_printf(CYASSL_BIO*, const char*, ...);
CYASSL_API int CyaSSL_ASN1_UTCTIME_print(CYASSL_BIO*,
                                         const CYASSL_ASN1_UTCTIME*);
CYASSL_API int   CyaSSL_sk_num(CYASSL_X509_REVOKED*);
CYASSL_API void* CyaSSL_sk_value(CYASSL_X509_REVOKED*, int);

/* stunnel 4.28 needs */
CYASSL_API void* CyaSSL_CTX_get_ex_data(const CYASSL_CTX*, int);
CYASSL_API int   CyaSSL_CTX_set_ex_data(CYASSL_CTX*, int, void*);
CYASSL_API void  CyaSSL_CTX_sess_set_get_cb(CYASSL_CTX*,
                       CYASSL_SESSION*(*f)(CYASSL*, unsigned char*, int, int*));
CYASSL_API void  CyaSSL_CTX_sess_set_new_cb(CYASSL_CTX*,
                                            int (*f)(CYASSL*, CYASSL_SESSION*));
CYASSL_API void  CyaSSL_CTX_sess_set_remove_cb(CYASSL_CTX*,
                                       void (*f)(CYASSL_CTX*, CYASSL_SESSION*));

CYASSL_API int          CyaSSL_i2d_SSL_SESSION(CYASSL_SESSION*,unsigned char**);
CYASSL_API CYASSL_SESSION* CyaSSL_d2i_SSL_SESSION(CYASSL_SESSION**,const unsigned char**,
                                        long);

CYASSL_API long CyaSSL_SESSION_get_timeout(const CYASSL_SESSION*);
CYASSL_API long CyaSSL_SESSION_get_time(const CYASSL_SESSION*);
CYASSL_API int  CyaSSL_CTX_get_ex_new_index(long, void*, void*, void*, void*);

/* extra ends */


/* CyaSSL extensions */

/* call before SSL_connect, if verifying will add name check to
   date check and signature check */
CYASSL_API int CyaSSL_check_domain_name(CYASSL* ssl, const char* dn);

/* need to call once to load library (session cache) */
CYASSL_API int CyaSSL_Init(void);
/* call when done to cleanup/free session cache mutex / resources  */
CYASSL_API int CyaSSL_Cleanup(void);

/* turn logging on, only if compiled in */
CYASSL_API int  CyaSSL_Debugging_ON(void);
/* turn logging off */
CYASSL_API void CyaSSL_Debugging_OFF(void);

/* do accept or connect depedning on side */
CYASSL_API int CyaSSL_negotiate(CYASSL* ssl);
/* turn on CyaSSL data compression */
CYASSL_API int CyaSSL_set_compression(CYASSL* ssl);

CYASSL_API int CyaSSL_set_timeout(CYASSL*, unsigned int);
CYASSL_API int CyaSSL_CTX_set_timeout(CYASSL_CTX*, unsigned int);

/* get CyaSSL peer X509_CHAIN */
CYASSL_API CYASSL_X509_CHAIN* CyaSSL_get_peer_chain(CYASSL* ssl);
/* peer chain count */
CYASSL_API int  CyaSSL_get_chain_count(CYASSL_X509_CHAIN* chain);
/* index cert length */
CYASSL_API int  CyaSSL_get_chain_length(CYASSL_X509_CHAIN*, int idx);
/* index cert */
CYASSL_API unsigned char* CyaSSL_get_chain_cert(CYASSL_X509_CHAIN*, int idx);
/* get index cert in PEM */
CYASSL_API int  CyaSSL_get_chain_cert_pem(CYASSL_X509_CHAIN*, int idx,
                                unsigned char* buffer, int inLen, int* outLen);
CYASSL_API const unsigned char* CyaSSL_get_sessionID(const CYASSL_SESSION* s);
CYASSL_API int  CyaSSL_X509_get_serial_number(CYASSL_X509*,unsigned char*,int*);
CYASSL_API char*  CyaSSL_X509_get_subjectCN(CYASSL_X509*);
CYASSL_API const unsigned char* CyaSSL_X509_get_der(CYASSL_X509*, int*);

CYASSL_API int CyaSSL_cmp_peer_cert_to_file(CYASSL*, const char*);

CYASSL_API char* CyaSSL_X509_get_next_altname(CYASSL_X509*);

/* connect enough to get peer cert */
CYASSL_API int  CyaSSL_connect_cert(CYASSL* ssl);

/* server Diffie-Hellman parameters */
CYASSL_API int  CyaSSL_SetTmpDH(CYASSL*, const unsigned char* p, int pSz,
                                const unsigned char* g, int gSz);
CYASSL_API int  CyaSSL_SetTmpDH_buffer(CYASSL*, const unsigned char* b, long sz,
                                       int format);
CYASSL_API int  CyaSSL_SetTmpEC_DHE_Sz(CYASSL*, unsigned short);
#ifndef NO_FILESYSTEM
    CYASSL_API int  CyaSSL_SetTmpDH_file(CYASSL*, const char* f, int format);
#endif

/* server ctx Diffie-Hellman parameters */
CYASSL_API int  CyaSSL_CTX_SetTmpDH(CYASSL_CTX*, const unsigned char* p,
                                    int pSz, const unsigned char* g, int gSz);
CYASSL_API int  CyaSSL_CTX_SetTmpDH_buffer(CYASSL_CTX*, const unsigned char* b,
                                           long sz, int format);
CYASSL_API int  CyaSSL_CTX_SetTmpEC_DHE_Sz(CYASSL_CTX*, unsigned short);
#ifndef NO_FILESYSTEM
    CYASSL_API int  CyaSSL_CTX_SetTmpDH_file(CYASSL_CTX*, const char* f,
                                             int format);
#endif

/* keyblock size in bytes or -1 */
CYASSL_API int CyaSSL_get_keyblock_size(CYASSL*);
CYASSL_API int CyaSSL_get_keys(CYASSL*,unsigned char** ms, unsigned int* msLen,
                                       unsigned char** sr, unsigned int* srLen,
                                       unsigned char** cr, unsigned int* crLen);

#ifndef _WIN32
    #ifndef NO_WRITEV
        #ifdef __PPU
            #include <sys/types.h>
            #include <sys/socket.h>
        #else
            #include <sys/uio.h>
        #endif
        /* allow writev style writing */
        CYASSL_API int CyaSSL_writev(CYASSL* ssl, const struct iovec* iov,
                                     int iovcnt);
    #endif
#endif


/* SSL_CTX versions */
CYASSL_API int CyaSSL_CTX_load_verify_buffer(CYASSL_CTX*, const unsigned char*,
                                             long, int);
CYASSL_API int CyaSSL_CTX_use_certificate_buffer(CYASSL_CTX*,
                                               const unsigned char*, long, int);
CYASSL_API int CyaSSL_CTX_use_PrivateKey_buffer(CYASSL_CTX*,
                                               const unsigned char*, long, int);
CYASSL_API int CyaSSL_CTX_use_certificate_chain_buffer(CYASSL_CTX*, 
                                                    const unsigned char*, long);
CYASSL_API int CyaSSL_CTX_set_group_messages(CYASSL_CTX*);

/* SSL versions */
CYASSL_API int CyaSSL_use_certificate_buffer(CYASSL*, const unsigned char*,
                                             long, int);
CYASSL_API int CyaSSL_use_PrivateKey_buffer(CYASSL*, const unsigned char*, long,
                                            int);
CYASSL_API int CyaSSL_use_certificate_chain_buffer(CYASSL*, 
                                                    const unsigned char*, long);
CYASSL_API int CyaSSL_set_group_messages(CYASSL*);

/* I/O callbacks */
typedef int (*CallbackIORecv)(char *buf, int sz, void *ctx);
typedef int (*CallbackIOSend)(char *buf, int sz, void *ctx);

CYASSL_API void CyaSSL_SetIORecv(CYASSL_CTX*, CallbackIORecv);
CYASSL_API void CyaSSL_SetIOSend(CYASSL_CTX*, CallbackIOSend);

CYASSL_API void CyaSSL_SetIOReadCtx(CYASSL* ssl, void *ctx);
CYASSL_API void CyaSSL_SetIOWriteCtx(CYASSL* ssl, void *ctx);

/* CA cache callbacks */
enum {
    CYASSL_SSLV3    = 0,
    CYASSL_TLSV1    = 1,
    CYASSL_TLSV1_1  = 2,
    CYASSL_TLSV1_2  = 3,
    CYASSL_USER_CA  = 1,          /* user added as trusted */
    CYASSL_CHAIN_CA = 2           /* added to cache from trusted chain */
};

CYASSL_API int CyaSSL_SetVersion(CYASSL* ssl, int version);
CYASSL_API int CyaSSL_KeyPemToDer(const unsigned char*, int sz, unsigned char*,
                                  int, const char*);

typedef void (*CallbackCACache)(unsigned char* der, int sz, int type);
typedef void (*CbMissingCRL)(const char* url);

CYASSL_API void CyaSSL_CTX_SetCACb(CYASSL_CTX*, CallbackCACache);


CYASSL_API CYASSL_CERT_MANAGER* CyaSSL_CertManagerNew(void);
CYASSL_API void                 CyaSSL_CertManagerFree(CYASSL_CERT_MANAGER*);

CYASSL_API int CyaSSL_CertManagerLoadCA(CYASSL_CERT_MANAGER*, const char* f,
                                        const char* d);
CYASSL_API int CyaSSL_CertManagerVerify(CYASSL_CERT_MANAGER*, const char* f,
                                        int format);
CYASSL_API int CyaSSL_CertManagerVerifyBuffer(CYASSL_CERT_MANAGER* cm,
                                 const unsigned char* buff, int sz, int format);
CYASSL_API int CyaSSL_CertManagerCheckCRL(CYASSL_CERT_MANAGER*, unsigned char*,
                                          int sz);
CYASSL_API int CyaSSL_CertManagerEnableCRL(CYASSL_CERT_MANAGER*, int options);
CYASSL_API int CyaSSL_CertManagerDisableCRL(CYASSL_CERT_MANAGER*);
CYASSL_API int CyaSSL_CertManagerLoadCRL(CYASSL_CERT_MANAGER*, const char*, int,
                                         int);
CYASSL_API int CyaSSL_CertManagerSetCRL_Cb(CYASSL_CERT_MANAGER*, CbMissingCRL);

CYASSL_API int CyaSSL_EnableCRL(CYASSL* ssl, int options);
CYASSL_API int CyaSSL_DisableCRL(CYASSL* ssl);
CYASSL_API int CyaSSL_LoadCRL(CYASSL*, const char*, int, int);
CYASSL_API int CyaSSL_SetCRL_Cb(CYASSL*, CbMissingCRL);

CYASSL_API int CyaSSL_CTX_EnableCRL(CYASSL_CTX* ctx, int options);
CYASSL_API int CyaSSL_CTX_DisableCRL(CYASSL_CTX* ctx);
CYASSL_API int CyaSSL_CTX_LoadCRL(CYASSL_CTX*, const char*, int, int);
CYASSL_API int CyaSSL_CTX_SetCRL_Cb(CYASSL_CTX*, CbMissingCRL);

#define CYASSL_CRL_MONITOR   0x01   /* monitor this dir flag */
#define CYASSL_CRL_START_MON 0x02   /* start monitoring flag */

#ifdef CYASSL_CALLBACKS

/* used internally by CyaSSL while OpenSSL types aren't */
#include <cyassl/callbacks.h>

typedef int (*HandShakeCallBack)(HandShakeInfo*);
typedef int (*TimeoutCallBack)(TimeoutInfo*);

/* CyaSSL connect extension allowing HandShakeCallBack and/or TimeoutCallBack
   for diagnostics */
CYASSL_API int CyaSSL_connect_ex(CYASSL*, HandShakeCallBack, TimeoutCallBack,
                                 Timeval);
CYASSL_API int CyaSSL_accept_ex(CYASSL*, HandShakeCallBack, TimeoutCallBack,
                                Timeval);

#endif /* CYASSL_CALLBACKS */


CYASSL_API long CyaSSL_CTX_OCSP_set_options(CYASSL_CTX*, long);
CYASSL_API int  CyaSSL_CTX_OCSP_set_override_url(CYASSL_CTX*, const char*);

/* OCSP Options */
#define CYASSL_OCSP_ENABLE       0x0001 /* Enable OCSP lookups */
#define CYASSL_OCSP_URL_OVERRIDE 0x0002 /* Use the override URL instead of URL
                                         * in certificate */


#ifdef __cplusplus
    }  /* extern "C" */
#endif


#endif /* CYASSL_SSL_H */

