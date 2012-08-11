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
 * a with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA
 */


/*  ssl.h defines openssl compatibility layer 
 *
 */


#ifndef CYASSL_OPENSSL_H_
#define CYASSL_OPENSSL_H_

#include <cyassl/ssl.h>

#ifdef __cplusplus
    extern "C" {
#endif

#ifdef _WIN32
    /* wincrypt.h clashes */
    #undef X509_NAME
    #undef OCSP_REQUEST 
    #undef OCSP_RESPONSE
#endif


typedef CYASSL          SSL;          
typedef CYASSL_SESSION  SSL_SESSION;
typedef CYASSL_METHOD   SSL_METHOD;
typedef CYASSL_CTX      SSL_CTX;

typedef CYASSL_X509       X509;
typedef CYASSL_X509_NAME  X509_NAME;
typedef CYASSL_X509_CHAIN X509_CHAIN;


/* redeclare guard */
#define CYASSL_TYPES_DEFINED


typedef CYASSL_EVP_PKEY       EVP_PKEY;
typedef CYASSL_RSA            RSA;
typedef CYASSL_DSA            DSA;
typedef CYASSL_BIO            BIO;
typedef CYASSL_BIO_METHOD     BIO_METHOD;
typedef CYASSL_CIPHER         SSL_CIPHER;
typedef CYASSL_X509_LOOKUP    X509_LOOKUP;
typedef CYASSL_X509_LOOKUP_METHOD X509_LOOKUP_METHOD;
typedef CYASSL_X509_CRL       X509_CRL;
typedef CYASSL_X509_EXTENSION X509_EXTENSION;
typedef CYASSL_ASN1_TIME      ASN1_TIME;
typedef CYASSL_ASN1_INTEGER   ASN1_INTEGER;
typedef CYASSL_ASN1_OBJECT    ASN1_OBJECT;
typedef CYASSL_ASN1_STRING    ASN1_STRING;
typedef CYASSL_dynlock_value  CRYPTO_dynlock_value;

#define ASN1_UTCTIME CYASSL_ASN1_TIME

typedef CYASSL_MD4_CTX        MD4_CTX;
typedef CYASSL_COMP_METHOD    COMP_METHOD;
typedef CYASSL_X509_STORE     X509_STORE;
typedef CYASSL_X509_REVOKED   X509_REVOKED;
typedef CYASSL_X509_OBJECT    X509_OBJECT;
typedef CYASSL_X509_STORE_CTX X509_STORE_CTX;


#define SSLv3_server_method CyaSSLv3_server_method
#define SSLv3_client_method CyaSSLv3_client_method
#define TLSv1_server_method CyaTLSv1_server_method
#define TLSv1_client_method CyaTLSv1_client_method
#define TLSv1_1_server_method CyaTLSv1_1_server_method
#define TLSv1_1_client_method CyaTLSv1_1_client_method
#define TLSv1_2_server_method CyaTLSv1_2_server_method
#define TLSv1_2_client_method CyaTLSv1_2_client_method

#ifdef CYASSL_DTLS
    #define DTLSv1_client_method CyaDTLSv1_client_method
    #define DTLSv1_server_method CyaDTLSv1_server_method
#endif


#ifndef NO_FILESYSTEM
    #define SSL_CTX_use_certificate_file CyaSSL_CTX_use_certificate_file
    #define SSL_CTX_use_PrivateKey_file CyaSSL_CTX_use_PrivateKey_file
    #define SSL_CTX_load_verify_locations CyaSSL_CTX_load_verify_locations
    #define SSL_CTX_use_certificate_chain_file CyaSSL_CTX_use_certificate_chain_file
    #define SSL_CTX_use_RSAPrivateKey_file CyaSSL_CTX_use_RSAPrivateKey_file
    
    #define SSL_use_certificate_file CyaSSL_use_certificate_file
    #define SSL_use_PrivateKey_file CyaSSL_use_PrivateKey_file
    #define SSL_use_certificate_chain_file CyaSSL_use_certificate_chain_file
    #define SSL_use_RSAPrivateKey_file CyaSSL_use_RSAPrivateKey_file
#endif

#define SSL_CTX_new CyaSSL_CTX_new
#define SSL_new     CyaSSL_new
#define SSL_set_fd  CyaSSL_set_fd
#define SSL_get_fd  CyaSSL_get_fd
#define SSL_connect CyaSSL_connect

#define SSL_write    CyaSSL_write
#define SSL_read     CyaSSL_read
#define SSL_accept   CyaSSL_accept
#define SSL_CTX_free CyaSSL_CTX_free
#define SSL_free     CyaSSL_free
#define SSL_shutdown CyaSSL_shutdown

#define SSL_CTX_set_quiet_shutdown CyaSSL_CTX_set_quiet_shutdown
#define SSL_set_quiet_shutdown CyaSSL_set_quiet_shutdown
#define SSL_get_error CyaSSL_get_error
#define SSL_set_session CyaSSL_set_session
#define SSL_get_session CyaSSL_get_session
#define SSL_flush_sessions CyaSSL_flush_sessions

#define SSL_CTX_set_verify CyaSSL_CTX_set_verify
#define SSL_set_verify CyaSSL_set_verify
#define SSL_pending CyaSSL_pending
#define SSL_load_error_strings CyaSSL_load_error_strings
#define SSL_library_init CyaSSL_library_init
#define SSL_CTX_set_session_cache_mode CyaSSL_CTX_set_session_cache_mode 
#define SSL_CTX_set_cipher_list CyaSSL_CTX_set_cipher_list
#define SSL_set_cipher_list     CyaSSL_set_cipher_list

#define ERR_error_string CyaSSL_ERR_error_string
#define ERR_error_string_n CyaSSL_ERR_error_string_n

#define SSL_set_ex_data CyaSSL_set_ex_data
#define SSL_get_shutdown CyaSSL_get_shutdown
#define SSL_set_rfd CyaSSL_set_rfd 
#define SSL_set_wfd CyaSSL_set_wfd 
#define SSL_set_shutdown CyaSSL_set_shutdown 
#define SSL_set_session_id_context CyaSSL_set_session_id_context
#define SSL_set_connect_state CyaSSL_set_connect_state
#define SSL_set_accept_state CyaSSL_set_accept_state
#define SSL_session_reused CyaSSL_session_reused
#define SSL_SESSION_free CyaSSL_SESSION_free
#define SSL_is_init_finished CyaSSL_is_init_finished

#define SSL_get_version CyaSSL_get_version
#define SSL_get_current_cipher CyaSSL_get_current_cipher
#define SSL_get_cipher CyaSSL_get_cipher
#define SSL_CIPHER_description CyaSSL_CIPHER_description
#define SSL_CIPHER_get_name CyaSSL_CIPHER_get_name
#define SSL_get1_session CyaSSL_get1_session

#define SSL_get_keyblock_size CyaSSL_get_keyblock_size
#define SSL_get_keys          CyaSSL_get_keys

#define X509_free CyaSSL_X509_free
#define OPENSSL_free CyaSSL_OPENSSL_free

#define OCSP_parse_url CyaSSL_OCSP_parse_url
#define SSLv23_client_method CyaSSLv23_client_method
#define SSLv2_client_method CyaSSLv2_client_method
#define SSLv2_server_method CyaSSLv2_server_method

#define MD4_Init CyaSSL_MD4_Init
#define MD4_Update  CyaSSL_MD4_Update  
#define MD4_Final CyaSSL_MD4_Final

#define BIO_new CyaSSL_BIO_new
#define BIO_free CyaSSL_BIO_free
#define BIO_free_all CyaSSL_BIO_free_all
#define BIO_read CyaSSL_BIO_read
#define BIO_write CyaSSL_BIO_write
#define BIO_push CyaSSL_BIO_push
#define BIO_pop CyaSSL_BIO_pop
#define BIO_flush CyaSSL_BIO_flush
#define BIO_pending CyaSSL_BIO_pending

#define BIO_get_mem_data CyaSSL_BIO_get_mem_data
#define BIO_new_mem_buf  CyaSSL_BIO_new_mem_buf

#define BIO_f_buffer CyaSSL_BIO_f_buffer
#define BIO_set_write_buffer_size CyaSSL_BIO_set_write_buffer_size
#define BIO_f_ssl CyaSSL_BIO_f_ssl
#define BIO_new_socket CyaSSL_BIO_new_socket
#define SSL_set_bio CyaSSL_set_bio
#define BIO_eof CyaSSL_BIO_eof
#define BIO_set_ss CyaSSL_BIO_set_ss

#define BIO_s_mem CyaSSL_BIO_s_mem
#define BIO_f_base64 CyaSSL_BIO_f_base64
#define BIO_set_flags CyaSSL_BIO_set_flags

#define OpenSSL_add_all_algorithms CyaSSL_add_all_algorithms
#define SSLeay_add_ssl_algorithms CyaSSL_add_all_algorithms
#define SSLeay_add_all_algorithms CyaSSL_add_all_algorithms

#define RAND_screen CyaSSL_RAND_screen
#define RAND_file_name CyaSSL_RAND_file_name
#define RAND_write_file CyaSSL_RAND_write_file
#define RAND_load_file CyaSSL_RAND_load_file
#define RAND_egd CyaSSL_RAND_egd
#define RAND_seed CyaSSL_RAND_seed
#define RAND_add  CyaSSL_RAND_add

#define COMP_zlib CyaSSL_COMP_zlib
#define COMP_rle CyaSSL_COMP_rle
#define SSL_COMP_add_compression_method CyaSSL_COMP_add_compression_method

#define SSL_get_ex_new_index CyaSSL_get_ex_new_index

#define CRYPTO_set_id_callback CyaSSL_set_id_callback
#define CRYPTO_set_locking_callback CyaSSL_set_locking_callback
#define CRYPTO_set_dynlock_create_callback CyaSSL_set_dynlock_create_callback
#define CRYPTO_set_dynlock_lock_callback CyaSSL_set_dynlock_lock_callback
#define CRYPTO_set_dynlock_destroy_callback CyaSSL_set_dynlock_destroy_callback
#define CRYPTO_num_locks CyaSSL_num_locks

#define X509_STORE_CTX_get_current_cert CyaSSL_X509_STORE_CTX_get_current_cert
#define X509_STORE_CTX_get_error CyaSSL_X509_STORE_CTX_get_error
#define X509_STORE_CTX_get_error_depth CyaSSL_X509_STORE_CTX_get_error_depth

#define X509_NAME_oneline CyaSSL_X509_NAME_oneline
#define X509_get_issuer_name CyaSSL_X509_get_issuer_name
#define X509_get_subject_name CyaSSL_X509_get_subject_name
#define X509_verify_cert_error_string CyaSSL_X509_verify_cert_error_string

#define X509_LOOKUP_add_dir CyaSSL_X509_LOOKUP_add_dir
#define X509_LOOKUP_load_file CyaSSL_X509_LOOKUP_load_file
#define X509_LOOKUP_hash_dir CyaSSL_X509_LOOKUP_hash_dir
#define X509_LOOKUP_file CyaSSL_X509_LOOKUP_file

#define X509_STORE_add_lookup CyaSSL_X509_STORE_add_lookup
#define X509_STORE_new CyaSSL_X509_STORE_new
#define X509_STORE_get_by_subject CyaSSL_X509_STORE_get_by_subject
#define X509_STORE_CTX_init CyaSSL_X509_STORE_CTX_init
#define X509_STORE_CTX_cleanup CyaSSL_X509_STORE_CTX_cleanup

#define X509_CRL_get_lastUpdate CyaSSL_X509_CRL_get_lastUpdate
#define X509_CRL_get_nextUpdate CyaSSL_X509_CRL_get_nextUpdate

#define X509_get_pubkey CyaSSL_X509_get_pubkey
#define X509_CRL_verify CyaSSL_X509_CRL_verify
#define X509_STORE_CTX_set_error CyaSSL_X509_STORE_CTX_set_error
#define X509_OBJECT_free_contents CyaSSL_X509_OBJECT_free_contents
#define EVP_PKEY_free CyaSSL_EVP_PKEY_free
#define X509_cmp_current_time CyaSSL_X509_cmp_current_time
#define sk_X509_REVOKED_num CyaSSL_sk_X509_REVOKED_num
#define X509_CRL_get_REVOKED CyaSSL_X509_CRL_get_REVOKED
#define sk_X509_REVOKED_value CyaSSL_sk_X509_REVOKED_value 

#define X509_get_serialNumber CyaSSL_X509_get_serialNumber

#define ASN1_TIME_pr CyaSSL_ASN1_TIME_pr

#define ASN1_INTEGER_cmp CyaSSL_ASN1_INTEGER_cmp
#define ASN1_INTEGER_get CyaSSL_ASN1_INTEGER_get

#define SSL_load_client_CA_file CyaSSL_load_client_CA_file

#define SSL_CTX_set_client_CA_list CyaSSL_CTX_set_client_CA_list
#define X509_STORE_CTX_get_ex_data CyaSSL_X509_STORE_CTX_get_ex_data 
#define SSL_get_ex_data_X509_STORE_CTX_idx CyaSSL_get_ex_data_X509_STORE_CTX_idx
#define SSL_get_ex_data CyaSSL_get_ex_data

#define SSL_CTX_set_default_passwd_cb_userdata CyaSSL_CTX_set_default_passwd_cb_userdata
#define SSL_CTX_set_default_passwd_cb CyaSSL_CTX_set_default_passwd_cb

#define SSL_CTX_set_timeout CyaSSL_CTX_set_timeout
#define SSL_CTX_set_info_callback CyaSSL_CTX_set_info_callback

#define ERR_peek_error CyaSSL_ERR_peek_error
#define ERR_GET_REASON CyaSSL_ERR_GET_REASON

#define SSL_alert_type_string CyaSSL_alert_type_string
#define SSL_alert_desc_string CyaSSL_alert_desc_string
#define SSL_state_string CyaSSL_state_string

#define RSA_free CyaSSL_RSA_free
#define RSA_generate_key CyaSSL_RSA_generate_key
#define SSL_CTX_set_tmp_rsa_callback CyaSSL_CTX_set_tmp_rsa_callback

#define PEM_def_callback CyaSSL_PEM_def_callback

#define SSL_CTX_sess_accept CyaSSL_CTX_sess_accept
#define SSL_CTX_sess_connect CyaSSL_CTX_sess_connect
#define SSL_CTX_sess_accept_good CyaSSL_CTX_sess_accept_good
#define SSL_CTX_sess_connect_good CyaSSL_CTX_sess_connect_good
#define SSL_CTX_sess_accept_renegotiate CyaSSL_CTX_sess_accept_renegotiate
#define SSL_CTX_sess_connect_renegotiate CyaSSL_CTX_sess_connect_renegotiate
#define SSL_CTX_sess_hits CyaSSL_CTX_sess_hits
#define SSL_CTX_sess_cb_hits CyaSSL_CTX_sess_cb_hits
#define SSL_CTX_sess_cache_full CyaSSL_CTX_sess_cache_full
#define SSL_CTX_sess_misses CyaSSL_CTX_sess_misses
#define SSL_CTX_sess_timeouts CyaSSL_CTX_sess_timeouts
#define SSL_CTX_sess_number CyaSSL_CTX_sess_number
#define SSL_CTX_sess_get_cache_size CyaSSL_CTX_sess_get_cache_size


#define SSL_DEFAULT_CIPHER_LIST CYASSL_DEFAULT_CIPHER_LIST
#define RSA_F4 CYASSL_RSA_F4

#define SSL_CTX_set_psk_client_callback CyaSSL_CTX_set_psk_client_callback
#define SSL_set_psk_client_callback CyaSSL_set_psk_client_callback

#define SSL_get_psk_identity_hint CyaSSL_get_psk_identity_hint
#define SSL_get_psk_identity CyaSSL_get_psk_identity

#define SSL_CTX_use_psk_identity_hint CyaSSL_CTX_use_psk_identity_hint
#define SSL_use_psk_identity_hint CyaSSL_use_psk_identity_hint

#define SSL_CTX_set_psk_server_callback CyaSSL_CTX_set_psk_server_callback
#define SSL_set_psk_server_callback CyaSSL_set_psk_server_callback

#define ERR_get_error_line_data CyaSSL_ERR_get_error_line_data

#define ERR_get_error CyaSSL_ERR_get_error
#define ERR_clear_error CyaSSL_ERR_clear_error

#define RAND_status CyaSSL_RAND_status
#define RAND_bytes CyaSSL_RAND_bytes
#define SSLv23_server_method CyaSSLv23_server_method
#define SSL_CTX_set_options CyaSSL_CTX_set_options 
#define SSL_CTX_check_private_key CyaSSL_CTX_check_private_key

#define ERR_free_strings CyaSSL_ERR_free_strings
#define ERR_remove_state CyaSSL_ERR_remove_state
#define EVP_cleanup CyaSSL_EVP_cleanup

#define CRYPTO_cleanup_all_ex_data CyaSSL_cleanup_all_ex_data
#define SSL_CTX_set_mode CyaSSL_CTX_set_mode
#define SSL_CTX_get_mode CyaSSL_CTX_get_mode
#define SSL_CTX_set_default_read_ahead CyaSSL_CTX_set_default_read_ahead

#define SSL_CTX_sess_set_cache_size CyaSSL_CTX_sess_set_cache_size
#define SSL_CTX_set_default_verify_paths CyaSSL_CTX_set_default_verify_paths

#define SSL_CTX_set_session_id_context CyaSSL_CTX_set_session_id_context
#define SSL_get_peer_certificate CyaSSL_get_peer_certificate

#define SSL_want_read CyaSSL_want_read
#define SSL_want_write CyaSSL_want_write

#define BIO_prf CyaSSL_BIO_prf
#define ASN1_UTCTIME_pr CyaSSL_ASN1_UTCTIME_pr

#define sk_num CyaSSL_sk_num
#define sk_value CyaSSL_sk_value

#define SSL_CTX_get_ex_data CyaSSL_CTX_get_ex_data
#define SSL_CTX_set_ex_data CyaSSL_CTX_set_ex_data
#define SSL_CTX_sess_set_get_cb CyaSSL_CTX_sess_set_get_cb
#define SSL_CTX_sess_set_new_cb CyaSSL_CTX_sess_set_new_cb
#define SSL_CTX_sess_set_remove_cb CyaSSL_CTX_sess_set_remove_cb

#define i2d_SSL_SESSION CyaSSL_i2d_SSL_SESSION
#define d2i_SSL_SESSION CyaSSL_d2i_SSL_SESSION
#define SSL_SESSION_get_timeout CyaSSL_SESSION_get_timeout
#define SSL_SESSION_get_time CyaSSL_SESSION_get_time
#define SSL_CTX_get_ex_new_index CyaSSL_CTX_get_ex_new_index



#ifdef __cplusplus
    } /* extern "C" */
#endif


#endif /* CyaSSL_openssl_h__ */
