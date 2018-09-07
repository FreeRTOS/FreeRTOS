/* ssl.h
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
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * a with this program; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301, USA
 */

/*
 * ssl.h makes wolfssl backwards compatibile with cyassl
 */

#ifndef WOLFSSL_CYASSL_H_
#define WOLFSSL_CYASSL_H_
/*
 * Name change
 * include the new ssl.h
 */
#include <wolfssl/ssl.h>
#include <cyassl/ctaocrypt/types.h>
#include <cyassl/ctaocrypt/settings.h>

#ifdef __cplusplus
    extern "C" {
#endif

#ifdef _WIN32
    /* wincrypt.h clashes */
    #undef X509_NAME
#endif

#ifdef CYASSL_TIRTOS
    #undef CYASSL_TIRTOS
    #define CYASSL_TIRTOS WOLFSSL_TIRTOS
#endif

#define CYASSL          WOLFSSL
#define DEBUG_CYASSL    DEBUG_WOLFSSL
#define CYASSL_CTX      WOLFSSL_CTX
#define CYASSL_METHOD   WOLFSSL_METHOD
#define CYASSL_SESSION  WOLFSSL_SESSION

#define CYASSL_X509       WOLFSSL_X509
#define CYASSL_X509_NAME  WOLFSSL_X509_NAME
#define CYASSL_X509_CHAIN WOLFSSL_X509_CHAIN
#ifdef WOLFSSL_SNIFFER
    #define CYASSL_SNIFFER    WOLFSSL_SNIFFER
#endif

/* redeclare guard */
#define CYASSL_TYPES_DEFINED WOLFSSL_TYPES_DEFINED

/* legacy defines */
#define yasslIP          wolfSSLIP                                         /**/
#define yasslPort        wolfSSLPort                                       /**/

/* cyassl/ssl.h (structs) */
#define CYASSL_RSA                WOLFSSL_RSA
#define CYASSL_DSA                WOLFSSL_DSA
#define CYASSL_BIO                WOLFSSL_BIO
#define CYASSL_CIPHER             WOLFSSL_CIPHER
#define CYASSL_MD4_CTX            WOLFSSL_MD4_CTX
#define CYASSL_MFL_2_9            WOLFSSL_MFL_2_9                          /**/
#define CYASSL_MFL_2_13           WOLFSSL_MFL_2_13                         /**/
#define CYASSL_EVP_PKEY           WOLFSSL_EVP_PKEY
#define CYASSL_X509_CRL           WOLFSSL_X509_CRL
#define CYASSL_ASN1_TIME          WOLFSSL_ASN1_TIME
#define CYASSL_BIO_METHOD         WOLFSSL_BIO_METHOD
#define CYASSL_X509_STORE         WOLFSSL_X509_STORE
#define CYASSL_X509_OBJECT        WOLFSSL_X509_OBJECT
#define CYASSL_X509_LOOKUP        WOLFSSL_X509_LOOKUP
#define CYASSL_ASN1_OBJECT        WOLFSSL_ASN1_OBJECT
#define CYASSL_ASN1_STRING        WOLFSSL_ASN1_STRING
#define CYASSL_COMP_METHOD        WOLFSSL_COMP_METHOD
#define CYASSL_CRL_CHECKALL       WOLFSSL_CRL_CHECKALL
#define CYASSL_ASN1_INTEGER       WOLFSSL_ASN1_INTEGER
#define CYASSL_X509_REVOKED       WOLFSSL_X509_REVOKED
#define CYASSL_dynlock_value      WOLFSSL_dynlock_value
#define CYASSL_X509_EXTENSION     WOLFSSL_X509_EXTENSION
#define CYASSL_X509_STORE_CTX     WOLFSSL_X509_STORE_CTX
#define CYASSL_X509_LOOKUP_METHOD WOLFSSL_X509_LOOKUP_METHOD

#define CyaSSL_LoadCRL            wolfSSL_LoadCRL
#define CyaSSL_EnableCRL          wolfSSL_EnableCRL
#define CyaSSL_SetCRL_Cb          wolfSSL_SetCRL_Cb

/* cyassl/test.h */
#ifdef CyaSSL_TEST_H
    #define CYASSL_THREAD         WOLFSSL_THREAD
#endif

/* src/ssl.c */
#define CYASSL_CRL                       WOLFSSL_CRL
#define CYASSL_SSLV3                     WOLFSSL_SSLV3
#define CYASSL_TLSV1                     WOLFSSL_TLSV1
#define CYASSL_TLSV1_1                   WOLFSSL_TLSV1_1
#define CYASSL_TLSV1_2                   WOLFSSL_TLSV1_2
#define CYASSL_USER_CA                   WOLFSSL_USER_CA
#define CYASSL_CLIENT_END                WOLFSSL_CLIENT_END
#define CYASSL_CERT_MANAGER              WOLFSSL_CERT_MANAGER
#define MAX_CYASSL_FILE_SIZE             MAX_WOLFSSL_FILE_SIZE

#define CyaSSL_get_cipher                wolfSSL_get_cipher
#define CyaSSL_get_ciphers               wolfSSL_get_ciphers
#define CyaSSL_KeyPemToDer               wolfSSL_KeyPemToDer
#define CyaSSL_get_version               wolfSSL_get_version
#define CyaSSL_SetServerID               wolfSSL_SetServerID
#define CyaSSL_use_old_poly              wolfSSL_use_old_poly
#define CyaSSL_SetCertCbCtx              wolfSSL_SetCertCbCtx
#define CyaSSL_CertPemToDer              wolfSSL_CertPemToDer
#define CyaSSL_get_shutdown              wolfSSL_get_shutdown
#define CyaSSL_SetMinVersion             wolfSSL_SetMinVersion
#define CyaSSL_CTX_UnloadCAs             wolfSSL_CTX_UnloadCAs
#define CyaSSL_session_reused            wolfSSL_session_reused
#define CyaSSL_UnloadCertsKeys           wolfSSL_UnloadCertsKeys
#define CyaSSL_CIPHER_get_name           wolfSSL_CIPHER_get_name
#define CyaSSL_is_init_finished          wolfSSL_is_init_finished
#define CyaSSL_get_alert_history         wolfSSL_get_alert_history
#define CyaSSL_get_current_cipher        wolfSSL_get_current_cipher
#define CyaSSL_CertManagerUnloadCAs      wolfSSL_CertManagerUnloadCAs
#define CyaSSL_CertManagerEnableOCSP     wolfSSL_CertManagerEnableOCSP
#define CyaSSL_CTX_check_private_key     wolfSSL_CTX_check_private_key
#define CyaSSL_CertManagerDisableOCSP    wolfSSL_CertManagerDisableOCSP
#define CyaSSL_get_current_cipher_suite  wolfSSL_get_current_cipher_suite
#define CyaSSL_CTX_load_verify_locations wolfSSL_CTX_load_verify_locations
#define CyaSSL_CTX_set_default_passwd_cb wolfSSL_CTX_set_default_passwd_cb

#define CyaSSL_save_session_cache        wolfSSL_save_session_cache
#define CyaSSL_restore_session_cache     wolfSSL_restore_session_cache
#define CyaSSL_memsave_session_cache     wolfSSL_memsave_session_cache
#define CyaSSL_memrestore_session_cache  wolfSSL_memrestore_session_cache
#define CyaSSL_get_session_cache_memsize wolfSSL_get_session_cache_memsize

/* certificate cache persistence, uses ctx since certs are per ctx */
#define CyaSSL_CTX_save_cert_cache        wolfSSL_CTX_save_cert_cache
#define CyaSSL_CTX_restore_cert_cache     wolfSSL_CTX_restore_cert_cache
#define CyaSSL_CTX_memsave_cert_cache     wolfSSL_CTX_memsave_cert_cache
#define CyaSSL_CTX_memrestore_cert_cache  wolfSSL_CTX_memrestore_cert_cache
#define CyaSSL_CTX_get_cert_cache_memsize wolfSSL_CTX_get_cert_cache_memsize

/* wolfSSL extensions */
/* get wolfSSL peer X509_CHAIN */
#define CyaSSL_get_chain_count wolfSSL_get_chain_count
/* index cert length */
#define CyaSSL_get_chain_length wolfSSL_get_chain_length
/* index cert in X509 */
#define CyaSSL_get_chain_X509 wolfSSL_get_chain_X509
/* free X509 */
#define CyaSSL_FreeX509 wolfSSL_FreeX509
/* get index cert in PEM */
#define CyaSSL_X509_get_subjectCN wolfSSL_X509_get_subjectCN
#define CyaSSL_X509_get_der       wolfSSL_X509_get_der
#define CyaSSL_X509_notBefore     wolfSSL_X509_notBefore
#define CyaSSL_X509_notAfter      wolfSSL_X509_notAfter
#define CyaSSL_X509_version       wolfSSL_X509_version

#define CyaSSL_cmp_peer_cert_to_file wolfSSL_cmp_peer_cert_to_file

#define CyaSSL_X509_get_next_altname wolfSSL_X509_get_next_altname

#define CyaSSL_X509_d2i wolfSSL_X509_d2i
#ifndef NO_FILESYSTEM
    #ifndef NO_STDIO_FILESYSTEM
        #define CyaSSL_X509_d2i_fp wolfSSL_X509_d2i_fp
    #endif
#define CyaSSL_X509_load_certificate_file wolfSSL_X509_load_certificate_file
#endif

#ifdef WOLFSSL_SEP
#define CyaSSL_X509_get_device_type      wolfSSL_X509_get_device_type
#define CyaSSL_X509_get_hw_type          wolfSSL_X509_get_hw_type
#define CyaSSL_X509_get_hw_serial_number wolfSSL_X509_get_hw_serial_number
#endif

#define CyaSSL_CTX_SetGenCookie wolfSSL_CTX_SetGenCookie
#define CyaSSL_SetCookieCtx     wolfSSL_SetCookieCtx
#define CyaSSL_GetCookieCtx     wolfSSL_GetCookieCtx
#define CyaSSL_ERR_get_error_line_data wolfSSL_ERR_get_error_line_data
#define CyaSSL_ERR_get_error           wolfSSL_ERR_get_error
#define CyaSSL_ERR_clear_error         wolfSSL_ERR_clear_error
#define CyaSSL_RAND_status             wolfSSL_RAND_status
#define CyaSSL_RAND_bytes              wolfSSL_RAND_bytes
#define CyaSSL_CTX_set_options         wolfSSL_CTX_set_options
#define CyaSSL_ERR_free_strings        wolfSSL_ERR_free_strings
#define CyaSSL_ERR_remove_state        wolfSSL_ERR_remove_state
#define CyaSSL_EVP_cleanup             wolfSSL_EVP_cleanup
#define CyaSSL_cleanup_all_ex_data     wolfSSL_cleanup_all_ex_data
#define CyaSSL_CTX_set_mode            wolfSSL_CTX_set_mode
#define CyaSSL_CTX_get_mode            wolfSSL_CTX_get_mode
#define CyaSSL_CTX_set_default_read_ahead   wolfSSL_CTX_set_default_read_ahead
#define CyaSSL_CTX_sess_set_cache_size      wolfSSL_CTX_sess_set_cache_size
#define CyaSSL_CTX_set_default_verify_paths wolfSSL_CTX_set_default_verify_paths
#define CyaSSL_CTX_set_session_id_context   wolfSSL_CTX_set_session_id_context
#define CyaSSL_get_peer_certificate         wolfSSL_get_peer_certificate
#define CyaSSL_BIO_printf                   wolfSSL_BIO_printf
#define CyaSSL_ASN1_UTCTIME_print           wolfSSL_ASN1_UTCTIME_print
#define CyaSSL_sk_num                       wolfSSL_sk_num
#define CyaSSL_sk_value                     wolfSSL_sk_value

/* stunnel 4.28 needs */
#define CyaSSL_CTX_get_ex_data        wolfSSL_CTX_get_ex_data
#define CyaSSL_CTX_set_ex_data        wolfSSL_CTX_set_ex_data
#define CyaSSL_CTX_sess_set_get_cb    wolfSSL_CTX_sess_set_get_cb
#define CyaSSL_CTX_sess_set_new_cb    wolfSSL_CTX_sess_set_new_cb
#define CyaSSL_CTX_sess_set_remove_cb wolfSSL_CTX_sess_set_remove_cb

#define CyaSSL_i2d_SSL_SESSION wolfSSL_i2d_SSL_SESSION
#define CyaSSL_d2i_SSL_SESSION wolfSSL_d2i_SSL_SESSION

#define CyaSSL_SESSION_get_timeout  wolfSSL_SESSION_get_timeout
#define CyaSSL_SESSION_get_time     wolfSSL_SESSION_get_time
#define CyaSSL_CTX_get_ex_new_index wolfSSL_CTX_get_ex_new_index


/* io.c */
#define CYASSL_CBIO_ERR_ISR        WOLFSSL_CBIO_ERR_ISR
#define CYASSL_CBIO_ERR_TIMEOUT    WOLFSSL_CBIO_ERR_TIMEOUT
#define CYASSL_CBIO_ERR_GENERAL    WOLFSSL_CBIO_ERR_GENERAL
#define CYASSL_CBIO_ERR_CONN_RST   WOLFSSL_CBIO_ERR_CONN_RST
#define CYASSL_CBIO_ERR_WANT_READ  WOLFSSL_CBIO_ERR_WANT_READ
#define CYASSL_CBIO_ERR_WANT_WRITE WOLFSSL_CBIO_ERR_WANT_WRITE
#define CYASSL_CBIO_ERR_CONN_CLOSE WOLFSSL_CBIO_ERR_CONN_CLOSE

#define CyaSSL_GetIOReadCtx        wolfSSL_GetIOReadCtx
#define CyaSSL_GetIOWriteCtx       wolfSSL_GetIOWriteCtx

/* src/tls.c */
#define CYASSL_SERVER_END          WOLFSSL_SERVER_END
#define CYASSL_TLS_HMAC_INNER_SZ   WOLFSSL_TLS_HMAC_INNER_SZ

#define CyaSSL_DeriveTlsKeys       wolfSSL_DeriveTlsKeys
#define CyaSSL_make_eap_keys       wolfSSL_make_eap_keys
#define CyaSSL_MakeTlsMasterSecret wolfSSL_MakeTlsMasterSecret

/* src/internal.c */
#define CYASSL_CHAIN_CA                WOLFSSL_CHAIN_CA
#define CYASSL_ALERT_HISTORY           WOLFSSL_ALERT_HISTORY
#define CYASSL_SESSION_TIMEOUT         WOLFSSL_SESSION_TIMEOUT
#define CYASSL_CBIO_ERR_CONN_RST       WOLFSSL_CBIO_ERR_CONN_RST

#define cyassl_rc4                     wolfssl_rc4
#define cyassl_aes                     wolfssl_aes
#define cyassl_chacha                  wolfssl_chacha
#define CyaSSL_ERR_reason_error_string wolfSSL_ERR_reason_error_string

#define CyaSSL_set_ex_data  wolfSSL_set_ex_data
#define CyaSSL_get_shutdown wolfSSL_get_shutdown
#define CyaSSL_set_rfd      wolfSSL_set_rfd
#define CyaSSL_set_wfd      wolfSSL_set_wfd
#define CyaSSL_set_shutdown wolfSSL_set_shutdown
#define CyaSSL_set_session_id_context wolfSSL_set_session_id_context
#define CyaSSL_set_connect_state      wolfSSL_set_connect_state
#define CyaSSL_set_accept_state       wolfSSL_set_accept_state
#define CyaSSL_session_reused         wolfSSL_session_reused
#define CyaSSL_SESSION_free           wolfSSL_SESSION_free
#define CyaSSL_is_init_finished       wolfSSL_is_init_finished

#define CyaSSL_get_version              wolfSSL_get_version
#define CyaSSL_get_current_cipher_suite wolfSSL_get_current_cipher_suite
#define CyaSSL_get_current_cipher       wolfSSL_get_current_cipher
#define CyaSSL_CIPHER_description       wolfSSL_CIPHER_description
#define CyaSSL_CIPHER_get_name          wolfSSL_CIPHER_get_name
#define CyaSSL_get_cipher               wolfSSL_get_cipher
#define CyaSSL_get1_session             wolfSSL_get1_session

#define CyaSSL_X509_free      wolfSSL_X509_free
#define CyaSSL_OPENSSL_free   wolfSSL_OPENSSL_free
#define CyaSSL_OCSP_parse_url wolfSSL_OCSP_parse_url

#define CyaSSLv23_client_method wolfSSLv23_client_method
#define CyaSSLv2_client_method  wolfSSLv2_client_method
#define CyaSSLv2_server_method  wolfSSLv2_server_method

#define CyaSSL_MD4_Init     wolfSSL_MD4_Init
#define CyaSSL_MD4_Update   wolfSSL_MD4_Update
#define CyaSSL_MD4_Final    wolfSSL_MD4_Final


#define CyaSSL_BIO_new      wolfSSL_BIO_new
#define CyaSSL_BIO_free     wolfSSL_BIO_free
#define CyaSSL_BIO_free_all wolfSSL_BIO_free_all
#define CyaSSL_BIO_read     wolfSSL_BIO_read
#define CyaSSL_BIO_write    wolfSSL_BIO_write
#define CyaSSL_BIO_push     wolfSSL_BIO_push
#define CyaSSL_BIO_pop      wolfSSL_BIO_pop
#define CyaSSL_BIO_flush    wolfSSL_BIO_flush
#define CyaSSL_BIO_pending  wolfSSL_BIO_pending

#define CyaSSL_BIO_f_buffer              wolfSSL_BIO_f_buffer
#define CyaSSL_BIO_set_write_buffer_size wolfSSL_BIO_set_write_buffer_size
#define CyaSSL_BIO_f_ssl                 wolfSSL_BIO_f_ssl
#define CyaSSL_BIO_new_socket            wolfSSL_BIO_new_socket
#define CyaSSL_BIO_eof                   wolfSSL_BIO_eof

#define CyaSSL_BIO_s_mem        wolfSSL_BIO_s_mem
#define CyaSSL_BIO_f_base64     wolfSSL_BIO_f_base64
#define CyaSSL_BIO_set_flags    wolfSSL_BIO_set_flags
#define CyaSSL_BIO_get_mem_data wolfSSL_BIO_get_mem_data
#define CyaSSL_BIO_new_mem_buf  wolfSSL_BIO_new_mem_buf


#define CyaSSL_BIO_set_ssl wolfSSL_BIO_set_ssl
#define CyaSSL_set_bio     wolfSSL_set_bio

#define CyaSSL_add_all_algorithms wolfSSL_add_all_algorithms
#define CyaSSL_RAND_screen        wolfSSL_RAND_screen
#define CyaSSL_RAND_file_name     wolfSSL_RAND_file_name
#define CyaSSL_RAND_write_file    wolfSSL_RAND_write_file
#define CyaSSL_RAND_load_file     wolfSSL_RAND_load_file
#define CyaSSL_RAND_egd           wolfSSL_RAND_egd
#define CyaSSL_RAND_seed          wolfSSL_RAND_seed
#define CyaSSL_RAND_add           wolfSSL_RAND_add

#define CyaSSL_COMP_zlib wolfSSL_COMP_zlib
#define CyaSSL_COMP_rle  wolfSSL_COMP_rle
#define CyaSSL_COMP_add_compression_method  wolfSSL_COMP_add_compression_method
#define CyaSSL_set_dynlock_create_callback  wolfSSL_set_dynlock_create_callback
#define CyaSSL_set_dynlock_lock_callback    wolfSSL_set_dynlock_lock_callback
#define CyaSSL_set_dynlock_destroy_callback wolfSSL_set_dynlock_destroy_callback
#define CyaSSL_get_ex_new_index     wolfSSL_get_ex_new_index
#define CyaSSL_set_id_callback      wolfSSL_set_id_callback
#define CyaSSL_set_locking_callback wolfSSL_set_locking_callback
#define CyaSSL_num_locks            wolfSSL_num_locks

#define CyaSSL_X509_STORE_CTX_get_current_cert wolfSSL_X509_STORE_CTX_get_current_cert
#define CyaSSL_X509_STORE_CTX_get_error        wolfSSL_X509_STORE_CTX_get_error
#define CyaSSL_X509_STORE_CTX_get_error_depth  wolfSSL_X509_STORE_CTX_get_error_depth

#define CyaSSL_X509_NAME_oneline            wolfSSL_X509_NAME_oneline
#define CyaSSL_X509_get_issuer_name         wolfSSL_X509_get_issuer_name
#define CyaSSL_X509_get_subject_name        wolfSSL_X509_get_subject_name
#define CyaSSL_X509_ext_isSet_by_NID        wolfSSL_X509_ext_isSet_by_NID
#define CyaSSL_X509_ext_get_critical_by_NID wolfSSL_X509_ext_get_critical_by_NID
#define CyaSSL_X509_get_isCA                wolfSSL_X509_get_isCA
#define CyaSSL_X509_get_isSet_pathLength    wolfSSL_X509_get_isSet_pathLength
#define CyaSSL_X509_get_pathLength          wolfSSL_X509_get_pathLength
#define CyaSSL_X509_get_keyUsage            wolfSSL_X509_get_keyUsage
#define CyaSSL_X509_get_authorityKeyID      wolfSSL_X509_get_authorityKeyID
#define CyaSSL_X509_get_subjectKeyID        wolfSSL_X509_get_subjectKeyID
#define CyaSSL_X509_NAME_entry_count        wolfSSL_X509_NAME_entry_count
#define CyaSSL_X509_NAME_get_text_by_NID    wolfSSL_X509_NAME_get_text_by_NID
#define CyaSSL_X509_verify_cert             wolfSSL_X509_verify_cert
#define CyaSSL_X509_verify_cert_error_string wolfSSL_X509_verify_cert_error_string
#define CyaSSL_X509_get_signature_type      wolfSSL_X509_get_signature_type
#define CyaSSL_X509_get_signature           wolfSSL_X509_get_signature

#define CyaSSL_X509_LOOKUP_add_dir   wolfSSL_X509_LOOKUP_add_dir
#define CyaSSL_X509_LOOKUP_load_file wolfSSL_X509_LOOKUP_load_file
#define CyaSSL_X509_LOOKUP_hash_dir  wolfSSL_X509_LOOKUP_hash_dir
#define CyaSSL_X509_LOOKUP_file      wolfSSL_X509_LOOKUP_file

#define CyaSSL_X509_STORE_add_lookup wolfSSL_X509_STORE_add_lookup
#define CyaSSL_X509_STORE_new        wolfSSL_X509_STORE_new
#define CyaSSL_X509_STORE_free       wolfSSL_X509_STORE_free
#define CyaSSL_X509_STORE_add_cert   wolfSSL_X509_STORE_add_cert
#define CyaSSL_X509_STORE_set_default_paths wolfSSL_X509_STORE_set_default_paths
#define CyaSSL_X509_STORE_get_by_subject    wolfSSL_X509_STORE_get_by_subject
#define CyaSSL_X509_STORE_CTX_new           wolfSSL_X509_STORE_CTX_new
#define CyaSSL_X509_STORE_CTX_init          wolfSSL_X509_STORE_CTX_init
#define CyaSSL_X509_STORE_CTX_free          wolfSSL_X509_STORE_CTX_free
#define CyaSSL_X509_STORE_CTX_cleanup       wolfSSL_X509_STORE_CTX_cleanup

#define CyaSSL_X509_CRL_get_lastUpdate wolfSSL_X509_CRL_get_lastUpdate
#define CyaSSL_X509_CRL_get_nextUpdate wolfSSL_X509_CRL_get_nextUpdate

#define CyaSSL_X509_get_pubkey wolfSSL_X509_get_pubkey
#define CyaSSL_X509_CRL_verify wolfSSL_X509_CRL_verify
#define CyaSSL_X509_STORE_CTX_set_error  wolfSSL_X509_STORE_CTX_set_error
#define CyaSSL_X509_OBJECT_free_contents wolfSSL_X509_OBJECT_free_contents
#define CyaSSL_EVP_PKEY_free             wolfSSL_EVP_PKEY_free
#define CyaSSL_X509_cmp_current_time     wolfSSL_X509_cmp_current_time
#define CyaSSL_sk_X509_REVOKED_num       wolfSSL_sk_X509_REVOKED_num

#define CyaSSL_X509_CRL_get_REVOKED     wolfSSL_X509_CRL_get_REVOKED
#define CyaSSL_sk_X509_REVOKED_value    wolfSSL_sk_X509_REVOKED_value
#define CyaSSL_X509_get_serialNumber    wolfSSL_X509_get_serialNumber
#define CyaSSL_ASN1_TIME_print          wolfSSL_ASN1_TIME_print
#define CyaSSL_ASN1_INTEGER_cmp         wolfSSL_ASN1_INTEGER_cmp
#define CyaSSL_ASN1_INTEGER_get         wolfSSL_ASN1_INTEGER_get
#define CyaSSL_load_client_CA_file      wolfSSL_load_client_CA_file
#define CyaSSL_CTX_set_client_CA_list   wolfSSL_CTX_set_client_CA_list
#define CyaSSL_X509_STORE_CTX_get_ex_data     wolfSSL_X509_STORE_CTX_get_ex_data
#define CyaSSL_get_ex_data_X509_STORE_CTX_idx wolfSSL_get_ex_data_X509_STORE_CTX_idx
#define CyaSSL_get_ex_data                    wolfSSL_get_ex_data

#define CyaSSL_CTX_set_default_passwd_cb_userdata wolfSSL_CTX_set_default_passwd_cb_userdata
#define CyaSSL_CTX_set_default_passwd_cb          wolfSSL_CTX_set_default_passwd_cb
#define CyaSSL_CTX_set_info_callback  wolfSSL_CTX_set_info_callback
#define CyaSSL_ERR_peek_error         wolfSSL_ERR_peek_error
#define CyaSSL_GET_REASON             wolfSSL_GET_REASON
#define CyaSSL_alert_type_string_long wolfSSL_alert_type_string_long
#define CyaSSL_alert_desc_string_long wolfSSL_alert_desc_string_long
#define CyaSSL_state_string_long      wolfSSL_state_string_long

#define CyaSSL_RSA_generate_key         wolfSSL_RSA_generate_key
#define CyaSSL_CTX_set_tmp_rsa_callback wolfSSL_CTX_set_tmp_rsa_callback
#define CyaSSL_PEM_def_callback         wolfSSL_PEM_def_callback
#define CyaSSL_CTX_sess_accept          wolfSSL_CTX_sess_accept
#define CyaSSL_CTX_sess_connect         wolfSSL_CTX_sess_connect
#define CyaSSL_CTX_sess_accept_good     wolfSSL_CTX_sess_accept_good
#define CyaSSL_CTX_sess_connect_good    wolfSSL_CTX_sess_connect_good
#define CyaSSL_CTX_sess_accept_renegotiate  wolfSSL_CTX_sess_accept_renegotiate
#define CyaSSL_CTX_sess_connect_renegotiate wolfSSL_CTX_sess_connect_renegotiate
#define CyaSSL_CTX_sess_hits                wolfSSL_CTX_sess_hits
#define CyaSSL_CTX_sess_cb_hits             wolfSSL_CTX_sess_cb_hits
#define CyaSSL_CTX_sess_cache_full          wolfSSL_CTX_sess_cache_full
#define CyaSSL_CTX_sess_misses              wolfSSL_CTX_sess_misses
#define CyaSSL_CTX_sess_timeouts            wolfSSL_CTX_sess_timeouts
#define CyaSSL_CTX_sess_number              wolfSSL_CTX_sess_number
#define CyaSSL_CTX_sess_get_cache_size      wolfSSL_CTX_sess_get_cache_size



/* src/keys.c */
#define cyassl_triple_des wolfssl_triple_des

/* Initialization and Shutdown */
#define CyaSSL_Init         wolfSSL_Init
#define CyaSSL_library_init wolfSSL_library_init
#define CyaSSL_Cleanup      wolfSSL_Cleanup
#define CyaSSL_shutdown     wolfSSL_shutdown

/* Certs and keys */
#define CyaSSL_SetTmpDH                     wolfSSL_SetTmpDH
#define CyaSSL_KeepArrays                   wolfSSL_KeepArrays
#define CyaSSL_FreeArrays                   wolfSSL_FreeArrays
#define CyaSSL_SetTmpDH_file                wolfSSL_SetTmpDH_file
#define CyaSSL_use_PrivateKey_buffer        wolfSSL_use_PrivateKey_buffer
#define CyaSSL_use_certificate_buffer       wolfSSL_use_certificate_buffer
#define CyaSSL_CTX_load_verify_buffer       wolfSSL_CTX_load_verify_buffer
#define CyaSSL_CTX_use_PrivateKey_file      wolfSSL_CTX_use_PrivateKey_file
#define CyaSSL_CTX_use_certificate_file     wolfSSL_CTX_use_certificate_file
#define CyaSSL_CTX_use_PrivateKey_buffer    wolfSSL_CTX_use_PrivateKey_buffer
#define CyaSSL_CTX_use_PrivateKey_buffer    wolfSSL_CTX_use_PrivateKey_buffer
#define CyaSSL_CTX_use_certificate_buffer   wolfSSL_CTX_use_certificate_buffer
#define CyaSSL_CTX_use_NTRUPrivateKey_file  wolfSSL_CTX_use_NTRUPrivateKey_file
#define CyaSSL_use_certificate_chain_buffer wolfSSL_use_certificate_chain_buffer
#define CyaSSL_CTX_der_load_verify_locations    \
                                            wolfSSL_CTX_der_load_verify_locations
#define CyaSSL_CTX_use_certificate_chain_file   \
                                            wolfSSL_CTX_use_certificate_chain_file
#define CyaSSL_CTX_use_certificate_chain_buffer \
                                            wolfSSL_CTX_use_certificate_chain_buffer

/* Context and Session Setup*/
#define CyaSSL_new                        wolfSSL_new
#define CyaSSL_free                       wolfSSL_free
#define CyaSSL_set_fd                     wolfSSL_set_fd
#define CyaSSL_CTX_new                    wolfSSL_CTX_new
#define CyaSSL_CTX_free                   wolfSSL_CTX_free
#define CyaSSL_SetVersion                 wolfSSL_SetVersion
#define CyaSSL_set_verify                 wolfSSL_set_verify
#define CyaSSL_set_session                wolfSSL_set_session
#define CyaSSL_set_timeout                wolfSSL_set_timeout
#define CyaSSL_CTX_set_verify             wolfSSL_CTX_set_verify
#define CyaSSL_CTX_set_timeout            wolfSSL_CTX_set_timeout
#define CyaSSL_set_cipher_list            wolfSSL_set_cipher_list
#define CyaSSL_set_compression            wolfSSL_set_compression
#define CyaTLSv1_client_method            wolfTLSv1_client_method
#define CyaTLSv1_server_method            wolfTLSv1_server_method
#define CyaSSLv3_client_method            wolfSSLv3_client_method
#define CyaSSLv3_server_method            wolfSSLv3_server_method
#define CyaSSLv23_client_method           wolfSSLv23_client_method
#define CyaSSLv23_server_method           wolfSSLv23_server_method
#define CyaDTLSv1_client_method           wolfDTLSv1_client_method
#define CyaDTLSv1_server_method           wolfDTLSv1_server_method
#define CyaSSL_check_domain_name          wolfSSL_check_domain_name
#define CyaTLSv1_1_client_method          wolfTLSv1_1_client_method
#define CyaTLSv1_1_server_method          wolfTLSv1_1_server_method
#define CyaTLSv1_2_client_method          wolfTLSv1_2_client_method
#define CyaTLSv1_2_server_method          wolfTLSv1_2_server_method
#define CyaDTLSv1_2_client_method         wolfDTLSv1_2_client_method
#define CyaDTLSv1_2_server_method         wolfDTLSv1_2_server_method
#define CyaSSL_set_group_messages         wolfSSL_set_group_messages
#define CyaSSL_set_using_nonblock         wolfSSL_set_using_nonblock
#define CyaSSL_CTX_set_cipher_list        wolfSSL_CTX_set_cipher_list
#define CyaSSL_CTX_set_group_messages     wolfSSL_CTX_set_group_messages
#define CyaSSL_CTX_set_session_cache_mode wolfSSL_CTX_set_session_cache_mode

/* Callbacks */

/* 
 * Empty commment denotes not listed in CyaSSL Manual
 * (soon to be wolfSSL Manual) 
 */

#define CyaSSL_accept_ex              wolfSSL_accept_ex
#define CyaSSL_SetIORecv              wolfSSL_SetIORecv
#define CyaSSL_SetIOSend              wolfSSL_SetIOSend
#define CyaSSL_connect_ex             wolfSSL_connect_ex
#define CyaSSL_CTX_SetCACb            wolfSSL_CTX_SetCACb
#define CyaSSL_SetIOReadCtx           wolfSSL_SetIOReadCtx
#define CyaSSL_SetRsaEncCtx           wolfSSL_SetRsaEncCtx
#define CyaSSL_GetRsaEncCtx           wolfSSL_GetRsaEncCtx
#define CyaSSL_SetRsaDecCtx           wolfSSL_SetRsaDecCtx
#define CyaSSL_GetRsaDecCtx           wolfSSL_GetRsaDecCtx
#define CyaSSL_SetLoggingCb           wolfSSL_SetLoggingCb
#define CyaSSL_SetEccSignCtx          wolfSSL_SetEccSignCtx
#define CyaSSL_GetEccSignCtx          wolfSSL_GetEccSignCtx
#define CyaSSL_SetRsaSignCtx          wolfSSL_SetRsaSignCtx
#define CyaSSL_GetRsaSignCtx          wolfSSL_GetRsaSignCtx
#define CyaSSL_SetIOWriteCtx          wolfSSL_SetIOWriteCtx
#define CyaSSL_SetIOReadFlags         wolfSSL_SetIOReadFlags
#define CyaSSL_SetEccVerifyCtx        wolfSSL_SetEccVerifyCtx
#define CyaSSL_GetEccVerifyCtx        wolfSSL_GetEccVerifyCtx
#define CyaSSL_SetRsaVerifyCtx        wolfSSL_SetRsaVerifyCtx
#define CyaSSL_GetRsaVerifyCtx        wolfSSL_GetRsaVerifyCtx
#define CyaSSL_CTX_SetRsaEncCb        wolfSSL_CTX_SetRsaEncCb
#define CyaSSL_CTX_SetRsaDecCb        wolfSSL_CTX_SetRsaDecCb
#define CyaSSL_SetIOWriteFlags        wolfSSL_SetIOWriteFlags
#define CyaSSL_SetTlsHmacInner        wolfSSL_SetTlsHmacInner
#define CyaSSL_SetMacEncryptCtx       wolfSSL_SetMacEncryptCtx
#define CyaSSL_GetMacEncryptCtx       wolfSSL_GetMacEncryptCtx
#define CyaSSL_CTX_SetEccSignCb       wolfSSL_CTX_SetEccSignCb
#define CyaSSL_CTX_SetRsaSignCb       wolfSSL_CTX_SetRsaSignCb
#define CyaSSL_CTX_SetEccVerifyCb     wolfSSL_CTX_SetEccVerifyCb
#define CyaSSL_CTX_SetRsaVerifyCb     wolfSSL_CTX_SetRsaVerifyCb
#define CyaSSL_CTX_SetMacEncryptCb    wolfSSL_CTX_SetMacEncryptCb
#define CyaSSL_SetDecryptVerifyCtx    wolfSSL_SetDecryptVerifyCtx
#define CyaSSL_GetDecryptVerifyCtx    wolfSSL_GetDecryptVerifyCtx
#define CyaSSL_CTX_SetDecryptVerifyCb wolfSSL_CTX_SetDecryptVerifyCb

/* psk specific */
#ifndef NO_PSK

#define CyaSSL_get_psk_identity          wolfSSL_get_psk_identity          /**/
#define CyaSSL_get_psk_identity_hint     wolfSSL_get_psk_identity_hint     /**/
#define CyaSSL_use_psk_identity_hint     wolfSSL_use_psk_identity_hint     /**/
#define CyaSSL_set_psk_client_callback   wolfSSL_set_psk_client_callback   /**/
#define CyaSSL_set_psk_server_callback   wolfSSL_set_psk_server_callback   /**/
#define CyaSSL_CTX_use_psk_identity_hint wolfSSL_CTX_use_psk_identity_hint /**/
#define CyaSSL_CTX_set_psk_client_callback \
                                      wolfSSL_CTX_set_psk_client_callback  /**/
#define CyaSSL_CTX_set_psk_server_callback \
                                      wolfSSL_CTX_set_psk_server_callback  /**/

#endif
/* end psk specific */

/* Anonymous */
#define CyaSSL_CTX_allow_anon_cipher wolfSSL_CTX_allow_anon_cipher         /**/

/* Error Handling and Debugging*/
#define CyaSSL_get_error           wolfSSL_get_error
#define CyaSSL_want_read           wolfSSL_want_read
#define CyaSSL_want_write          wolfSSL_want_write
#define CyaSSL_Debugging_ON        wolfSSL_Debugging_ON
#define CyaSSL_Debugging_OFF       wolfSSL_Debugging_OFF
#define CyaSSL_ERR_error_string    wolfSSL_ERR_error_string
#define CyaSSL_load_error_strings  wolfSSL_load_error_strings
#define CyaSSL_ERR_error_string_n  wolfSSL_ERR_error_string_n
#define CyaSSL_ERR_print_errors_fp wolfSSL_ERR_print_errors_fp

/* OCSP and CRL */

/* 
 * Empty commment denotes not listed in CyaSSL Manual
 * (soon to be wolfSSL Manual) 
 */

#define CYASSL_CRL_MONITOR               WOLFSSL_CRL_MONITOR               /**/
#define CYASSL_CRL_START_MON             WOLFSSL_CRL_START_MON             /**/
#define CYASSL_OCSP_NO_NONCE             WOLFSSL_OCSP_NO_NONCE             /**/
#define CYASSL_OCSP_URL_OVERRIDE         WOLFSSL_OCSP_URL_OVERRIDE
#define CYASSL_OCSP_CHECKALL             WOLFSSL_OCSP_CHECKALL

#define CyaSSL_CTX_EnableOCSP            wolfSSL_CTX_EnableOCSP
#define CyaSSL_CTX_OCSP_set_options      wolfSSL_CTX_OCSP_set_options      /**/
#define CyaSSL_CTX_SetOCSP_OverrideURL   wolfSSL_CTX_SetOCSP_OverrideURL   /**/
#define CyaSSL_CTX_OCSP_set_override_url wolfSSL_CTX_OCSP_set_override_url /**/

/* Informational */
#define CyaSSL_GetSide            wolfSSL_GetSide
#define CyaSSL_IsTLSv1_1          wolfSSL_IsTLSv1_1
#define CyaSSL_GetKeySize         wolfSSL_GetKeySize
#define CyaSSL_GetHmacSize        wolfSSL_GetHmacSize
#define CyaSSL_GetHmacType        wolfSSL_GetHmacType
#define CyaSSL_GetMacSecret       wolfSSL_GetMacSecret
#define CyaSSL_GetObjectSize      wolfSSL_GetObjectSize
#define CyaSSL_GetBulkCipher      wolfSSL_GetBulkCipher
#define CyaSSL_GetCipherType      wolfSSL_GetCipherType
#define CyaSSL_GetAeadMacSize     wolfSSL_GetAeadMacSize
#define CyaSSL_GetClientWriteIV   wolfSSL_GetClientWriteIV
#define CyaSSL_GetServerWriteIV   wolfSSL_GetServerWriteIV
#define CyaSSL_GetClientWriteKey  wolfSSL_GetClientWriteKey
#define CyaSSL_GetServerWriteKey  wolfSSL_GetServerWriteKey
#define CyaSSL_GetCipherBlockSize wolfSSL_GetCipherBlockSize

/* Connection, Session, and I/O */
#define CyaSSL_peek               wolfSSL_peek
#define CyaSSL_read               wolfSSL_read
#define CyaSSL_recv               wolfSSL_recv
#define CyaSSL_send               wolfSSL_send
#define CyaSSL_write              wolfSSL_write
#define CyaSSL_writev             wolfSSL_writev
#define CyaSSL_accept             wolfSSL_accept
#define CyaSSL_get_fd             wolfSSL_get_fd
#define CyaSSL_connect            wolfSSL_connect
#define CyaSSL_pending            wolfSSL_pending
#define CyaSSL_negotiate          wolfSSL_negotiate
#define CyaSSL_get_session        wolfSSL_get_session
#define CyaSSL_connect_cert       wolfSSL_connect_cert
#define CyaSSL_flush_sessions     wolfSSL_flush_sessions
#define CyaSSL_get_using_nonblock wolfSSL_get_using_nonblock
#define CyaSSL_PrintSessionStats  wolfSSL_PrintSessionStats

/* DTLS Specific */
#define CyaSSL_dtls                     wolfSSL_dtls
#define CyaSSL_dtls_set_peer            wolfSSL_dtls_set_peer
#define CyaSSL_dtls_get_peer            wolfSSL_dtls_get_peer
#define CyaSSL_dtls_got_timeout         wolfSSL_dtls_got_timeout
#define CyaSSL_dtls_get_current_timeout wolfSSL_dtls_get_current_timeout

/* Certificate Manager */
#define CyaSSL_CertManagerNew          wolfSSL_CertManagerNew
#define CyaSSL_CertManagerFree         wolfSSL_CertManagerFree
#define CyaSSL_CertManagerLoadCA       wolfSSL_CertManagerLoadCA
#define CyaSSL_CertManagerVerify       wolfSSL_CertManagerVerify
#define CyaSSL_CertManagerEnableCRL    wolfSSL_CertManagerEnableCRL
#define CyaSSL_CertManagerDisableCRL   wolfSSL_CertManagerDisableCRL
#define CyaSSL_CertManagerVerifyBuffer wolfSSL_CertManagerVerifyBuffer
#ifndef NO_CERTS
	#define CyaSSL_CertManagerCheckCRL   wolfSSL_CertManagerCheckCRL
	#define CyaSSL_CertManagerLoadCRL    wolfSSL_CertManagerLoadCRL
	#define CyaSSL_CertManagerSetCRL_Cb  wolfSSL_CertManagerSetCRL_Cb
	#define CyaSSL_CertManagerCheckOCSP  wolfSSL_CertManagerCheckOCSP
	#define CyaSSL_CertManagerSetOCSP_Cb wolfSSL_CertManagerSetOCSP_Cb
	#define CyaSSL_CertManagerSetOCSPOverrideURL \
                                          wolfSSL_CertManagerSetOCSPOverrideURL

	#define CyaSSL_DisableCRL          wolfSSL_DisableCRL
	#define CyaSSL_EnableOCSP          wolfSSL_EnableOCSP
	#define CyaSSL_DisableOCSP         wolfSSL_DisableOCSP
	#define CyaSSL_SetOCSP_OverrideURL wolfSSL_SetOCSP_OverrideURL
	#define CyaSSL_SetOCSP_Cb          wolfSSL_SetOCSP_Cb

	#define CyaSSL_CTX_EnableCRL   wolfSSL_CTX_EnableCRL
	#define CyaSSL_CTX_DisableCRL  wolfSSL_CTX_DisableCRL
	#define CyaSSL_CTX_LoadCRL     wolfSSL_CTX_LoadCRL
	#define CyaSSL_CTX_SetCRL_Cb   wolfSSL_CTX_SetCRL_Cb
	#define CyaSSL_CTX_DisableOCSP wolfSSL_CTX_DisableOCSP
	#define CyaSSL_CTX_SetOCSP_Cb  wolfSSL_CTX_SetOCSP_Cb
#endif /* !NO_CERTS */


/* OpenSSL Compatibility Layer */
#define CyaSSL_PemCertToDer               wolfSSL_PemCertToDer
#define CyaSSL_get_sessionID              wolfSSL_get_sessionID
#define CyaSSL_get_peer_count             wolfSSL_get_peer_count
#define CyaSSL_get_chain_cert             wolfSSL_get_chain_cert
#define CyaSSL_get_peer_chain             wolfSSL_get_peer_chain
#define CyaSSL_get_peer_length            wolfSSL_get_peer_length
#define CyaSSL_get_chain_cert_pem         wolfSSL_get_chain_cert_pem
#define CyaSSL_use_PrivateKey_file        wolfSSL_use_PrivateKey_file
#define CyaSSL_use_certificate_file       wolfSSL_use_certificate_file
#define CyaSSL_use_RSAPrivateKey_file     wolfSSL_use_RSAPrivateKey_file
#define CyaSSL_X509_get_serial_number     wolfSSL_X509_get_serial_number
#define CyaSSL_CTX_use_RSAPrivateKey_file wolfSSL_CTX_use_RSAPrivateKey_file
#define CyaSSL_use_certificate_chain_file wolfSSL_use_certificate_chain_file

/* TLS Extensions */
#define CYASSL_SNI_HOST_NAME         WOLFSSL_SNI_HOST_NAME

#define CyaSSL_UseSNI                wolfSSL_UseSNI
#define CyaSSL_CTX_UseSNI            wolfSSL_CTX_UseSNI
#define CyaSSL_SNI_SetOptions        wolfSSL_SNI_SetOptions
#define CyaSSL_SNI_GetRequest        wolfSSL_SNI_GetRequest
#define CyaSSL_UseMaxFragment        wolfSSL_UseMaxFragment
#define CyaSSL_UseTruncatedHMAC      wolfSSL_UseTruncatedHMAC
#define CyaSSL_UseSupportedCurve     wolfSSL_UseSupportedCurve
#define CyaSSL_SNI_GetFromBuffer     wolfSSL_SNI_GetFromBuffer
#define CyaSSL_CTX_SNI_SetOptions    wolfSSL_CTX_SNI_SetOptions
#define CyaSSL_CTX_UseMaxFragment    wolfSSL_CTX_UseMaxFragment
#define CyaSSL_CTX_UseTruncatedHMAC  wolfSSL_CTX_UseTruncatedHMAC
#define CyaSSL_CTX_UseSupportedCurve wolfSSL_CTX_UseSupportedCurve

/* End wolfssl -> cyassl -> openssl compatibility */

/* JRB macro redefinitions and api calls for cryptography for reverse compat. */

#ifdef WOLFSSL_SMALL_STACK
    #define CYASSL_SMALL_STACK
#endif


/*
 * wrapper around macros until they are changed in cyassl code
 * needs investigation in regards to macros in fips
 */
#define NO_WOLFSSL_ALLOC_ALIGN NO_CYASSL_ALLOC_ALIGN /* @TODO */


/* examples/client/client.h */
#define CYASSL_THREAD WOLFSSL_THREAD
#ifdef WOLFSSL_DTLS
    #define CYASSL_DTLS   WOLFSSL_DTLS
#endif

/* examples/client/client.c */
#define LIBCYASSL_VERSION_STRING LIBWOLFSSL_VERSION_STRING

#ifdef __cplusplus
    } /* extern "C" */
#endif


#endif /* CyaSSL_openssl_h__ */
