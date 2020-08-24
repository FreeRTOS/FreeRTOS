/* internal.h
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



#ifndef WOLFSSL_INT_H
#define WOLFSSL_INT_H


#include <wolfssl/wolfcrypt/types.h>
#include <wolfssl/ssl.h>
#ifdef HAVE_CRL
    #include <wolfssl/crl.h>
#endif
#include <wolfssl/wolfcrypt/random.h>
#ifndef NO_DES3
    #include <wolfssl/wolfcrypt/des3.h>
#endif
#ifndef NO_HC128
    #include <wolfssl/wolfcrypt/hc128.h>
#endif
#ifndef NO_RABBIT
    #include <wolfssl/wolfcrypt/rabbit.h>
#endif
#ifdef HAVE_CHACHA
    #include <wolfssl/wolfcrypt/chacha.h>
#endif
#ifndef NO_ASN
    #include <wolfssl/wolfcrypt/asn.h>
    #include <wolfssl/wolfcrypt/pkcs12.h>
#endif
#ifndef NO_MD5
    #include <wolfssl/wolfcrypt/md5.h>
#endif
#ifndef NO_SHA
    #include <wolfssl/wolfcrypt/sha.h>
#endif
#ifndef NO_AES
    #include <wolfssl/wolfcrypt/aes.h>
#endif
#ifdef HAVE_POLY1305
    #include <wolfssl/wolfcrypt/poly1305.h>
#endif
#ifdef HAVE_CAMELLIA
    #include <wolfssl/wolfcrypt/camellia.h>
#endif
#include <wolfssl/wolfcrypt/logging.h>
#ifndef NO_HMAC
    #include <wolfssl/wolfcrypt/hmac.h>
#endif
#ifndef NO_RC4
    #include <wolfssl/wolfcrypt/arc4.h>
#endif
#ifndef NO_SHA256
    #include <wolfssl/wolfcrypt/sha256.h>
#endif
#if defined(WOLFSSL_SHA384)
    #include <wolfssl/wolfcrypt/sha512.h>
#endif
#ifdef HAVE_OCSP
    #include <wolfssl/ocsp.h>
#endif
#ifdef WOLFSSL_SHA384
    #include <wolfssl/wolfcrypt/sha512.h>
#endif
#ifdef WOLFSSL_SHA512
    #include <wolfssl/wolfcrypt/sha512.h>
#endif
#ifdef HAVE_AESGCM
    #include <wolfssl/wolfcrypt/sha512.h>
#endif
#ifdef WOLFSSL_RIPEMD
    #include <wolfssl/wolfcrypt/ripemd.h>
#endif
#ifdef HAVE_IDEA
    #include <wolfssl/wolfcrypt/idea.h>
#endif
#ifndef NO_RSA
    #include <wolfssl/wolfcrypt/rsa.h>
#endif
#ifdef HAVE_ECC
    #include <wolfssl/wolfcrypt/ecc.h>
#endif
#ifndef NO_DH
    #include <wolfssl/wolfcrypt/dh.h>
#endif
#ifdef HAVE_ED25519
    #include <wolfssl/wolfcrypt/ed25519.h>
#endif
#ifdef HAVE_CURVE25519
    #include <wolfssl/wolfcrypt/curve25519.h>
#endif
#ifdef HAVE_ED448
    #include <wolfssl/wolfcrypt/ed448.h>
#endif
#ifdef HAVE_CURVE448
    #include <wolfssl/wolfcrypt/curve448.h>
#endif

#include <wolfssl/wolfcrypt/wc_encrypt.h>
#include <wolfssl/wolfcrypt/hash.h>

#if defined(WOLFSSL_CALLBACKS) || defined(OPENSSL_EXTRA)
    #include <wolfssl/callbacks.h>
#endif
#ifdef WOLFSSL_CALLBACKS
    #include <signal.h>
#endif

#ifdef USE_WINDOWS_API
    #ifdef WOLFSSL_GAME_BUILD
        #include "system/xtl.h"
    #else
        #if defined(_WIN32_WCE) || defined(WIN32_LEAN_AND_MEAN)
            /* On WinCE winsock2.h must be included before windows.h */
            #include <winsock2.h>
        #endif
        #include <windows.h>
    #endif
#elif defined(THREADX)
    #ifndef SINGLE_THREADED
        #include "tx_api.h"
    #endif

#elif defined(WOLFSSL_DEOS)
    /* do nothing, just don't pick Unix */
#elif defined(MICRIUM)
    /* do nothing, just don't pick Unix */
#elif defined(FREERTOS) || defined(FREERTOS_TCP) || defined(WOLFSSL_SAFERTOS)
    /* do nothing */
#elif defined(EBSNET)
    /* do nothing */
#elif defined(FREESCALE_MQX) || defined(FREESCALE_KSDK_MQX)
    /* do nothing */
#elif defined(FREESCALE_FREE_RTOS)
    #include "fsl_os_abstraction.h"
#elif defined(WOLFSSL_uITRON4)
        /* do nothing */
#elif defined(WOLFSSL_uTKERNEL2)
        /* do nothing */
#elif defined(WOLFSSL_CMSIS_RTOS)
    #include "cmsis_os.h"
#elif defined(WOLFSSL_CMSIS_RTOSv2)
    #include "cmsis_os2.h"
#elif defined(WOLFSSL_MDK_ARM)
    #if defined(WOLFSSL_MDK5)
        #include "cmsis_os.h"
    #else
        #include <rtl.h>
    #endif
#elif defined(MBED)
#elif defined(WOLFSSL_TIRTOS)
    /* do nothing */
#elif defined(INTIME_RTOS)
    #include <rt.h>
#elif defined(WOLFSSL_NUCLEUS_1_2)
    /* do nothing */
#elif defined(WOLFSSL_APACHE_MYNEWT)
    #if !defined(WOLFSSL_LWIP)
        void mynewt_ctx_clear(void *ctx);
        void* mynewt_ctx_new();
    #endif
#elif defined(WOLFSSL_ZEPHYR)
    #ifndef SINGLE_THREADED
        #include <kernel.h>
    #endif
#elif defined(WOLFSSL_TELIT_M2MB)
    /* do nothing */
#else
    #ifndef SINGLE_THREADED
        #define WOLFSSL_PTHREADS
        #include <pthread.h>
    #endif
    #if defined(OPENSSL_EXTRA) && !defined(NO_FILESYSTEM)
        #include <unistd.h>      /* for close of BIO */
    #endif
#endif

#ifndef CHAR_BIT
    /* Needed for DTLS without big math */
    #include <limits.h>
#endif


#ifdef HAVE_LIBZ
    #include "zlib.h"
#endif

#ifdef WOLFSSL_ASYNC_CRYPT
    #include <wolfssl/wolfcrypt/async.h>
#endif

#ifdef OPENSSL_EXTRA
    #ifdef WOLFCRYPT_HAVE_SRP
        #include <wolfssl/wolfcrypt/srp.h>
    #endif
#endif

#ifdef _MSC_VER
    /* 4996 warning to use MS extensions e.g., strcpy_s instead of strncpy */
    #pragma warning(disable: 4996)
#endif

#ifdef NO_SHA
    #define WC_SHA_DIGEST_SIZE 20
#endif

#ifdef NO_SHA256
    #define WC_SHA256_DIGEST_SIZE 32
#endif

#ifdef NO_MD5
    #define WC_MD5_DIGEST_SIZE 16
#endif


#ifdef __cplusplus
    extern "C" {
#endif

/* Define or comment out the cipher suites you'd like to be compiled in
   make sure to use at least one BUILD_SSL_xxx or BUILD_TLS_xxx is defined

   When adding cipher suites, add name to cipher_names, idx to cipher_name_idx

   Now that there is a maximum strength crypto build, the following BUILD_XXX
   flags need to be divided into two groups selected by WOLFSSL_MAX_STRENGTH.
   Those that do not use Perfect Forward Security and do not use AEAD ciphers
   need to be switched off. Allowed suites use (EC)DHE, AES-GCM|CCM, or
   CHACHA-POLY.
*/

/* Check that if WOLFSSL_MAX_STRENGTH is set that all the required options are
 * not turned off. */
#if defined(WOLFSSL_MAX_STRENGTH) && \
    ((!defined(HAVE_ECC) && (defined(NO_DH) || defined(NO_RSA))) || \
     (!defined(HAVE_AESGCM) && !defined(HAVE_AESCCM) && \
      (!defined(HAVE_POLY1305) || !defined(HAVE_CHACHA))) || \
     (defined(NO_SHA256) && !defined(WOLFSSL_SHA384)) || \
     !defined(NO_OLD_TLS))

    #error "You are trying to build max strength with requirements disabled."
#endif

/* Have QSH : Quantum-safe Handshake */
#if defined(HAVE_QSH)
    #define BUILD_TLS_QSH
#endif

#ifndef WOLFSSL_NO_TLS12

#ifndef WOLFSSL_MAX_STRENGTH

#ifdef WOLFSSL_AEAD_ONLY
    /* AES CBC ciphers are not allowed in AEAD only mode */
    #undef HAVE_AES_CBC
#endif

#ifndef WOLFSSL_AEAD_ONLY
    #if !defined(NO_RSA) && !defined(NO_RC4)
        #if defined(WOLFSSL_STATIC_RSA)
            #if !defined(NO_SHA)
                #define BUILD_SSL_RSA_WITH_RC4_128_SHA
            #endif
            #if !defined(NO_MD5)
                #define BUILD_SSL_RSA_WITH_RC4_128_MD5
            #endif
        #endif
        #if !defined(NO_TLS) && defined(HAVE_NTRU) && !defined(NO_SHA) \
            && defined(WOLFSSL_STATIC_RSA)
            #define BUILD_TLS_NTRU_RSA_WITH_RC4_128_SHA
        #endif
    #endif

    #if !defined(NO_RSA) && !defined(NO_DES3)
        #if !defined(NO_SHA)
            #if defined(WOLFSSL_STATIC_RSA)
                #define BUILD_SSL_RSA_WITH_3DES_EDE_CBC_SHA
            #endif
            #if !defined(NO_TLS) && defined(HAVE_NTRU) \
                && defined(WOLFSSL_STATIC_RSA)
                    #define BUILD_TLS_NTRU_RSA_WITH_3DES_EDE_CBC_SHA
            #endif
        #endif
    #endif

    #if !defined(NO_RSA) && defined(HAVE_IDEA)
        #if !defined(NO_SHA) && defined(WOLFSSL_STATIC_RSA)
            #define BUILD_SSL_RSA_WITH_IDEA_CBC_SHA
        #endif
    #endif
#endif /* !WOLFSSL_AEAD_ONLY */

    #if !defined(NO_RSA) && !defined(NO_AES) && !defined(NO_TLS)
        #if !defined(NO_SHA) && defined(HAVE_AES_CBC)
            #if defined(WOLFSSL_STATIC_RSA)
                #ifdef WOLFSSL_AES_128
                    #define BUILD_TLS_RSA_WITH_AES_128_CBC_SHA
                #endif
                #ifdef WOLFSSL_AES_256
                    #define BUILD_TLS_RSA_WITH_AES_256_CBC_SHA
                #endif
            #endif
            #if defined(HAVE_NTRU) && defined(WOLFSSL_STATIC_RSA)
                #ifdef WOLFSSL_AES_128
                    #define BUILD_TLS_NTRU_RSA_WITH_AES_128_CBC_SHA
                #endif
                #ifdef WOLFSSL_AES_256
                    #define BUILD_TLS_NTRU_RSA_WITH_AES_256_CBC_SHA
                #endif
            #endif
        #endif
        #if defined(WOLFSSL_STATIC_RSA)
            #if !defined (NO_SHA256) && defined(HAVE_AES_CBC)
                #ifdef WOLFSSL_AES_128
                    #define BUILD_TLS_RSA_WITH_AES_128_CBC_SHA256
                #endif
                #ifdef WOLFSSL_AES_256
                    #define BUILD_TLS_RSA_WITH_AES_256_CBC_SHA256
                #endif
            #endif
            #if defined (HAVE_AESGCM)
                #ifdef WOLFSSL_AES_128
                    #define BUILD_TLS_RSA_WITH_AES_128_GCM_SHA256
                #endif
                #if defined (WOLFSSL_SHA384) && defined(WOLFSSL_AES_256)
                    #define BUILD_TLS_RSA_WITH_AES_256_GCM_SHA384
                #endif
            #endif
            #if defined (HAVE_AESCCM)
                #ifdef WOLFSSL_AES_128
                    #define BUILD_TLS_RSA_WITH_AES_128_CCM_8
                #endif
                #ifdef WOLFSSL_AES_256
                    #define BUILD_TLS_RSA_WITH_AES_256_CCM_8
                #endif
            #endif
        #endif
    #endif

    #if defined(HAVE_CAMELLIA) && !defined(NO_TLS) && !defined(NO_CAMELLIA_CBC)
        #ifndef NO_RSA
          #if defined(WOLFSSL_STATIC_RSA)
            #if !defined(NO_SHA)
                #define BUILD_TLS_RSA_WITH_CAMELLIA_128_CBC_SHA
                #define BUILD_TLS_RSA_WITH_CAMELLIA_256_CBC_SHA
            #endif
            #ifndef NO_SHA256
                #define BUILD_TLS_RSA_WITH_CAMELLIA_128_CBC_SHA256
                #define BUILD_TLS_RSA_WITH_CAMELLIA_256_CBC_SHA256
            #endif
          #endif
            #if !defined(NO_DH)
              #if !defined(NO_SHA)
                #define BUILD_TLS_DHE_RSA_WITH_CAMELLIA_128_CBC_SHA
                #define BUILD_TLS_DHE_RSA_WITH_CAMELLIA_256_CBC_SHA
              #endif
                #ifndef NO_SHA256
                    #define BUILD_TLS_DHE_RSA_WITH_CAMELLIA_128_CBC_SHA256
                    #define BUILD_TLS_DHE_RSA_WITH_CAMELLIA_256_CBC_SHA256
                #endif
            #endif
        #endif
    #endif

#if defined(WOLFSSL_STATIC_PSK)
    #if !defined(NO_PSK) && !defined(NO_AES) && !defined(NO_TLS)
        #if !defined(NO_SHA)
            #ifdef WOLFSSL_AES_128
                #define BUILD_TLS_PSK_WITH_AES_128_CBC_SHA
            #endif
            #ifdef WOLFSSL_AES_256
                #define BUILD_TLS_PSK_WITH_AES_256_CBC_SHA
            #endif
        #endif
        #ifndef NO_SHA256
            #ifdef WOLFSSL_AES_128
                #ifdef HAVE_AES_CBC
                    #define BUILD_TLS_PSK_WITH_AES_128_CBC_SHA256
                #endif
                #ifdef HAVE_AESGCM
                    #define BUILD_TLS_PSK_WITH_AES_128_GCM_SHA256
                #endif
            #endif /* WOLFSSL_AES_128 */
            #ifdef HAVE_AESCCM
                #ifdef WOLFSSL_AES_128
                    #define BUILD_TLS_PSK_WITH_AES_128_CCM_8
                    #define BUILD_TLS_PSK_WITH_AES_128_CCM
                #endif
                #ifdef WOLFSSL_AES_256
                    #define BUILD_TLS_PSK_WITH_AES_256_CCM_8
                    #define BUILD_TLS_PSK_WITH_AES_256_CCM
                #endif
            #endif
        #endif
        #if defined(WOLFSSL_SHA384) && defined(WOLFSSL_AES_256)
            #ifdef HAVE_AES_CBC
                #define BUILD_TLS_PSK_WITH_AES_256_CBC_SHA384
            #endif
            #ifdef HAVE_AESGCM
                #define BUILD_TLS_PSK_WITH_AES_256_GCM_SHA384
            #endif
        #endif
    #endif
#endif

    #if !defined(NO_TLS) && defined(HAVE_NULL_CIPHER)
        #if !defined(NO_RSA)
            #if defined(WOLFSSL_STATIC_RSA)
                #ifndef NO_MD5
                    #define BUILD_TLS_RSA_WITH_NULL_MD5
                #endif
                #if !defined(NO_SHA)
                    #define BUILD_TLS_RSA_WITH_NULL_SHA
                #endif
                #ifndef NO_SHA256
                    #define BUILD_TLS_RSA_WITH_NULL_SHA256
                #endif
            #endif
        #endif
        #if !defined(NO_PSK) && defined(WOLFSSL_STATIC_PSK)
            #if !defined(NO_SHA)
                #define BUILD_TLS_PSK_WITH_NULL_SHA
            #endif
            #ifndef NO_SHA256
                #define BUILD_TLS_PSK_WITH_NULL_SHA256
            #endif
            #ifdef WOLFSSL_SHA384
                #define BUILD_TLS_PSK_WITH_NULL_SHA384
            #endif
        #endif
    #endif

#if defined(WOLFSSL_STATIC_RSA)
    #if !defined(NO_HC128) && !defined(NO_RSA) && !defined(NO_TLS)
        #ifndef NO_MD5
            #define BUILD_TLS_RSA_WITH_HC_128_MD5
        #endif
        #if !defined(NO_SHA)
            #define BUILD_TLS_RSA_WITH_HC_128_SHA
        #endif
    #endif

    #if !defined(NO_RABBIT) && !defined(NO_TLS) && !defined(NO_RSA)
        #if !defined(NO_SHA)
            #define BUILD_TLS_RSA_WITH_RABBIT_SHA
        #endif
    #endif
#endif

    #if !defined(NO_DH) && !defined(NO_AES) && !defined(NO_TLS) && \
        !defined(NO_RSA)

        #if !defined(NO_SHA)
            #if defined(WOLFSSL_AES_128) && defined(HAVE_AES_CBC)
                #define BUILD_TLS_DHE_RSA_WITH_AES_128_CBC_SHA
            #endif
            #if defined(WOLFSSL_AES_256) && defined(HAVE_AES_CBC)
                #define BUILD_TLS_DHE_RSA_WITH_AES_256_CBC_SHA
            #endif
            #if !defined(NO_DES3)
                #define BUILD_TLS_DHE_RSA_WITH_3DES_EDE_CBC_SHA
            #endif
        #endif
        #if !defined(NO_SHA256) && defined(HAVE_AES_CBC)
            #ifdef WOLFSSL_AES_128
                #define BUILD_TLS_DHE_RSA_WITH_AES_128_CBC_SHA256
            #endif
            #ifdef WOLFSSL_AES_256
                #define BUILD_TLS_DHE_RSA_WITH_AES_256_CBC_SHA256
            #endif
        #endif
    #endif

    #if defined(HAVE_ANON) && !defined(NO_TLS) && !defined(NO_DH) && \
        !defined(NO_AES) && !defined(NO_SHA) && defined(WOLFSSL_AES_128)
        #ifdef HAVE_AES_CBC
            #define BUILD_TLS_DH_anon_WITH_AES_128_CBC_SHA
        #endif

        #if defined(WOLFSSL_SHA384) && defined(HAVE_AESGCM)
            #define BUILD_TLS_DH_anon_WITH_AES_256_GCM_SHA384
        #endif
    #endif

    #if !defined(NO_DH) && !defined(NO_PSK) && !defined(NO_TLS)
        #ifndef NO_SHA256
            #if !defined(NO_AES) && defined(WOLFSSL_AES_128) && \
                                                           defined(HAVE_AES_CBC)
                #define BUILD_TLS_DHE_PSK_WITH_AES_128_CBC_SHA256
            #endif
            #ifdef HAVE_NULL_CIPHER
                #define BUILD_TLS_DHE_PSK_WITH_NULL_SHA256
            #endif
        #endif
        #ifdef WOLFSSL_SHA384
            #if !defined(NO_AES) && defined(WOLFSSL_AES_256) && \
                                                           defined(HAVE_AES_CBC)
                #define BUILD_TLS_DHE_PSK_WITH_AES_256_CBC_SHA384
            #endif
            #ifdef HAVE_NULL_CIPHER
                #define BUILD_TLS_DHE_PSK_WITH_NULL_SHA384
            #endif
        #endif
    #endif

    #if (defined(HAVE_ECC) || defined(HAVE_CURVE25519) || \
                                     defined(HAVE_CURVE448)) && !defined(NO_TLS)
        #if !defined(NO_AES)
            #if !defined(NO_SHA) && defined(HAVE_AES_CBC)
                #if !defined(NO_RSA)
                    #ifdef WOLFSSL_AES_128
                        #define BUILD_TLS_ECDHE_RSA_WITH_AES_128_CBC_SHA
                    #endif
                    #ifdef WOLFSSL_AES_256
                        #define BUILD_TLS_ECDHE_RSA_WITH_AES_256_CBC_SHA
                    #endif
                    #if defined(WOLFSSL_STATIC_DH) && defined(HAVE_ECC)
                        #ifdef WOLFSSL_AES_128
                            #define BUILD_TLS_ECDH_RSA_WITH_AES_128_CBC_SHA
                        #endif
                        #ifdef WOLFSSL_AES_256
                            #define BUILD_TLS_ECDH_RSA_WITH_AES_256_CBC_SHA
                        #endif
                    #endif
                #endif

                #if defined(HAVE_ECC) || \
                        (defined(HAVE_CURVE25519) && defined(HAVE_ED25519)) || \
                        (defined(HAVE_CURVE448) && defined(HAVE_ED448))
                    #ifdef WOLFSSL_AES_128
                        #define BUILD_TLS_ECDHE_ECDSA_WITH_AES_128_CBC_SHA
                    #endif
                    #ifdef WOLFSSL_AES_256
                        #define BUILD_TLS_ECDHE_ECDSA_WITH_AES_256_CBC_SHA
                    #endif
                #endif

                #if defined(WOLFSSL_STATIC_DH) && defined(HAVE_ECC)
                    #ifdef WOLFSSL_AES_128
                        #define BUILD_TLS_ECDH_ECDSA_WITH_AES_128_CBC_SHA
                    #endif
                    #ifdef WOLFSSL_AES_256
                        #define BUILD_TLS_ECDH_ECDSA_WITH_AES_256_CBC_SHA
                    #endif
                #endif
            #endif /* NO_SHA */
            #if !defined(NO_SHA256) && defined(WOLFSSL_AES_128) && \
                                                           defined(HAVE_AES_CBC)
                #if !defined(NO_RSA)
                    #define BUILD_TLS_ECDHE_RSA_WITH_AES_128_CBC_SHA256
                    #if defined(WOLFSSL_STATIC_DH) && defined(HAVE_ECC)
                        #define BUILD_TLS_ECDH_RSA_WITH_AES_128_CBC_SHA256
                    #endif
                #endif
                #if defined(HAVE_ECC) || \
                        (defined(HAVE_CURVE25519) && defined(HAVE_ED25519)) || \
                        (defined(HAVE_CURVE448) && defined(HAVE_ED448))
                    #define BUILD_TLS_ECDHE_ECDSA_WITH_AES_128_CBC_SHA256
                #endif
                #if defined(WOLFSSL_STATIC_DH) && defined(HAVE_ECC)
                    #define BUILD_TLS_ECDH_ECDSA_WITH_AES_128_CBC_SHA256
                #endif
            #endif

            #if defined(WOLFSSL_SHA384) && defined(WOLFSSL_AES_256) && \
                                                           defined(HAVE_AES_CBC)
                #if !defined(NO_RSA)
                    #define BUILD_TLS_ECDHE_RSA_WITH_AES_256_CBC_SHA384
                    #if defined(WOLFSSL_STATIC_DH) && defined(HAVE_ECC)
                        #define BUILD_TLS_ECDH_RSA_WITH_AES_256_CBC_SHA384
                    #endif
                #endif
                #if defined(HAVE_ECC) || \
                        (defined(HAVE_CURVE25519) && defined(HAVE_ED25519)) || \
                        (defined(HAVE_CURVE448) && defined(HAVE_ED448))
                    #define BUILD_TLS_ECDHE_ECDSA_WITH_AES_256_CBC_SHA384
                #endif
                #if defined(WOLFSSL_STATIC_DH) && defined(HAVE_ECC)
                    #define BUILD_TLS_ECDH_ECDSA_WITH_AES_256_CBC_SHA384
                #endif
            #endif

            #if defined (HAVE_AESGCM)
                #if !defined(NO_RSA)
                    #if defined(WOLFSSL_STATIC_DH) && defined(HAVE_ECC)
                        #ifdef WOLFSSL_AES_128
                            #define BUILD_TLS_ECDH_RSA_WITH_AES_128_GCM_SHA256
                        #endif
                    #endif
                    #if defined(WOLFSSL_SHA384)
                        #if defined(WOLFSSL_STATIC_DH) && defined(HAVE_ECC)
                            #ifdef WOLFSSL_AES_256
                                #define BUILD_TLS_ECDH_RSA_WITH_AES_256_GCM_SHA384
                            #endif
                        #endif
                    #endif
                #endif

                #if defined(WOLFSSL_STATIC_DH) && defined(WOLFSSL_AES_128) && \
                                                               defined(HAVE_ECC)
                    #define BUILD_TLS_ECDH_ECDSA_WITH_AES_128_GCM_SHA256
                #endif

                #if defined(WOLFSSL_SHA384)
                    #if defined(WOLFSSL_STATIC_DH) && \
                                   defined(WOLFSSL_AES_256) && defined(HAVE_ECC)
                        #define BUILD_TLS_ECDH_ECDSA_WITH_AES_256_GCM_SHA384
                    #endif
                #endif
            #endif
        #endif /* NO_AES */
        #if !defined(NO_RC4)
            #if !defined(NO_SHA)
                #if !defined(NO_RSA)
                    #ifndef WOLFSSL_AEAD_ONLY
                        #define BUILD_TLS_ECDHE_RSA_WITH_RC4_128_SHA
                    #endif
                    #if defined(WOLFSSL_STATIC_DH) && defined(HAVE_ECC)
                        #define BUILD_TLS_ECDH_RSA_WITH_RC4_128_SHA
                    #endif
                #endif

                #if defined(HAVE_ECC) || \
                        (defined(HAVE_CURVE25519) && defined(HAVE_ED25519)) || \
                        (defined(HAVE_CURVE448) && defined(HAVE_ED448))
                    #ifndef WOLFSSL_AEAD_ONLY
                        #define BUILD_TLS_ECDHE_ECDSA_WITH_RC4_128_SHA
                    #endif
                #endif
                #if defined(WOLFSSL_STATIC_DH) && defined(HAVE_ECC)
                    #define BUILD_TLS_ECDH_ECDSA_WITH_RC4_128_SHA
                #endif
            #endif
        #endif
        #if !defined(NO_DES3)
            #ifndef NO_SHA
                #if !defined(NO_RSA)
                    #define BUILD_TLS_ECDHE_RSA_WITH_3DES_EDE_CBC_SHA
                    #if defined(WOLFSSL_STATIC_DH) && defined(HAVE_ECC)
                        #define BUILD_TLS_ECDH_RSA_WITH_3DES_EDE_CBC_SHA
                    #endif
                #endif

                #if defined(HAVE_ECC) || \
                        (defined(HAVE_CURVE25519) && defined(HAVE_ED25519)) || \
                        (defined(HAVE_CURVE448) && defined(HAVE_ED448))
                    #define BUILD_TLS_ECDHE_ECDSA_WITH_3DES_EDE_CBC_SHA
                #endif
                #if defined(WOLFSSL_STATIC_DH) && defined(HAVE_ECC)
                    #define BUILD_TLS_ECDH_ECDSA_WITH_3DES_EDE_CBC_SHA
                #endif
            #endif /* NO_SHA */
        #endif
        #if defined(HAVE_NULL_CIPHER)
            #if !defined(NO_SHA)
                #if defined(HAVE_ECC) || \
                        (defined(HAVE_CURVE25519) && defined(HAVE_ED25519)) || \
                        (defined(HAVE_CURVE448) && defined(HAVE_ED448))
                    #define BUILD_TLS_ECDHE_ECDSA_WITH_NULL_SHA
                #endif
            #endif
            #if !defined(NO_PSK) && !defined(NO_SHA256)
                #define BUILD_TLS_ECDHE_PSK_WITH_NULL_SHA256
            #endif
        #endif
        #if !defined(NO_PSK) && !defined(NO_SHA256) && !defined(NO_AES) && \
            defined(WOLFSSL_AES_128) && defined(HAVE_AES_CBC)
            #define BUILD_TLS_ECDHE_PSK_WITH_AES_128_CBC_SHA256
        #endif
    #endif
    #if defined(HAVE_CHACHA) && defined(HAVE_POLY1305) && !defined(NO_SHA256)
        #if !defined(NO_OLD_POLY1305)
        #if defined(HAVE_ECC) || \
                        (defined(HAVE_CURVE25519) && defined(HAVE_ED25519)) || \
                        (defined(HAVE_CURVE448) && defined(HAVE_ED448))
            #define BUILD_TLS_ECDHE_ECDSA_WITH_CHACHA20_OLD_POLY1305_SHA256
        #endif
        #if !defined(NO_RSA) && defined(HAVE_ECC)
            #define BUILD_TLS_ECDHE_RSA_WITH_CHACHA20_OLD_POLY1305_SHA256
        #endif
        #if !defined(NO_DH) && !defined(NO_RSA)
            #define BUILD_TLS_DHE_RSA_WITH_CHACHA20_OLD_POLY1305_SHA256
        #endif
        #endif /* NO_OLD_POLY1305 */
        #if !defined(NO_PSK)
            #define BUILD_TLS_PSK_WITH_CHACHA20_POLY1305_SHA256
            #if defined(HAVE_ECC) || defined(HAVE_ED25519) || \
                                                             defined(HAVE_ED448)
                #define BUILD_TLS_ECDHE_PSK_WITH_CHACHA20_POLY1305_SHA256
            #endif
            #ifndef NO_DH
                #define BUILD_TLS_DHE_PSK_WITH_CHACHA20_POLY1305_SHA256
            #endif
        #endif /* !NO_PSK */
    #endif

#endif /* !WOLFSSL_MAX_STRENGTH */

#if !defined(NO_DH) && !defined(NO_AES) && !defined(NO_TLS) && \
    !defined(NO_RSA) && defined(HAVE_AESGCM)

    #if !defined(NO_SHA256) && defined(WOLFSSL_AES_128)
        #define BUILD_TLS_DHE_RSA_WITH_AES_128_GCM_SHA256
    #endif

    #if defined(WOLFSSL_SHA384) && defined(WOLFSSL_AES_256)
        #define BUILD_TLS_DHE_RSA_WITH_AES_256_GCM_SHA384
    #endif
#endif

#if !defined(NO_DH) && !defined(NO_PSK) && !defined(NO_TLS)
    #ifndef NO_SHA256
        #if defined(HAVE_AESGCM) && defined(WOLFSSL_AES_128)
            #define BUILD_TLS_DHE_PSK_WITH_AES_128_GCM_SHA256
        #endif
        #ifdef HAVE_AESCCM
            #ifdef WOLFSSL_AES_128
                #define BUILD_TLS_DHE_PSK_WITH_AES_128_CCM
            #endif
            #ifdef WOLFSSL_AES_256
                #define BUILD_TLS_DHE_PSK_WITH_AES_256_CCM
            #endif
        #endif
    #endif
    #if defined(WOLFSSL_SHA384) && defined(HAVE_AESGCM) && \
        defined(WOLFSSL_AES_256)
        #define BUILD_TLS_DHE_PSK_WITH_AES_256_GCM_SHA384
    #endif
#endif

#if (defined(HAVE_ECC) || defined(HAVE_CURVE25519) || defined(HAVE_CURVE448)) \
                                         && !defined(NO_TLS) && !defined(NO_AES)
    #ifdef HAVE_AESGCM
        #if !defined(NO_SHA256) && defined(WOLFSSL_AES_128)
            #if defined(HAVE_ECC) || \
                        (defined(HAVE_CURVE25519) && defined(HAVE_ED25519)) || \
                        (defined(HAVE_CURVE448) && defined(HAVE_ED448))
                #define BUILD_TLS_ECDHE_ECDSA_WITH_AES_128_GCM_SHA256
            #endif
            #ifndef NO_RSA
                #define BUILD_TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256
            #endif
        #endif
        #if defined(WOLFSSL_SHA384) && defined(WOLFSSL_AES_256)
            #if defined(HAVE_ECC) || \
                        (defined(HAVE_CURVE25519) && defined(HAVE_ED25519)) || \
                        (defined(HAVE_CURVE448) && defined(HAVE_ED448))
                #define BUILD_TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384
            #endif
            #ifndef NO_RSA
                #define BUILD_TLS_ECDHE_RSA_WITH_AES_256_GCM_SHA384
            #endif
        #endif
    #endif
    #if defined(HAVE_AESCCM) && !defined(NO_SHA256)
        #if defined(HAVE_ECC) || \
                        (defined(HAVE_CURVE25519) && defined(HAVE_ED25519)) || \
                        (defined(HAVE_CURVE448) && defined(HAVE_ED448))
            #ifdef WOLFSSL_AES_128
                #define BUILD_TLS_ECDHE_ECDSA_WITH_AES_128_CCM
                #define BUILD_TLS_ECDHE_ECDSA_WITH_AES_128_CCM_8
            #endif
            #ifdef WOLFSSL_AES_256
                #define BUILD_TLS_ECDHE_ECDSA_WITH_AES_256_CCM_8
            #endif
        #endif
    #endif
#endif

#if defined(HAVE_CHACHA) && defined(HAVE_POLY1305) && !defined(NO_SHA256)
    #if defined(HAVE_ECC) || defined(HAVE_CURVE25519) || defined(HAVE_CURVE448)
        #if defined(HAVE_ECC) || \
                        (defined(HAVE_CURVE25519) && defined(HAVE_ED25519)) || \
                        (defined(HAVE_CURVE448) && defined(HAVE_ED448))
            #define BUILD_TLS_ECDHE_ECDSA_WITH_CHACHA20_POLY1305_SHA256
        #endif
        #ifndef NO_RSA
            #define BUILD_TLS_ECDHE_RSA_WITH_CHACHA20_POLY1305_SHA256
        #endif
    #endif
    #if !defined(NO_DH) && !defined(NO_RSA)
        #define BUILD_TLS_DHE_RSA_WITH_CHACHA20_POLY1305_SHA256
    #endif
#endif

#endif

#if defined(WOLFSSL_TLS13)
    #ifdef HAVE_AESGCM
        #if !defined(NO_SHA256) && defined(WOLFSSL_AES_128)
            #define BUILD_TLS_AES_128_GCM_SHA256
        #endif
        #if defined(WOLFSSL_SHA384) && defined(WOLFSSL_AES_256)
            #define BUILD_TLS_AES_256_GCM_SHA384
        #endif
    #endif

    #if defined(HAVE_CHACHA) && defined(HAVE_POLY1305)
        #ifndef NO_SHA256
            #define BUILD_TLS_CHACHA20_POLY1305_SHA256
        #endif
    #endif

    #ifdef HAVE_AESCCM
        #if !defined(NO_SHA256) && defined(WOLFSSL_AES_128)
            #define BUILD_TLS_AES_128_CCM_SHA256
            #define BUILD_TLS_AES_128_CCM_8_SHA256
        #endif
    #endif
    #ifdef HAVE_NULL_CIPHER
        #ifndef NO_SHA256
            #define BUILD_TLS_SHA256_SHA256
        #endif
        #ifdef WOLFSSL_SHA384
            #define BUILD_TLS_SHA384_SHA384
        #endif
    #endif
#endif

#ifdef WOLFSSL_MULTICAST
    #if defined(HAVE_NULL_CIPHER) && !defined(NO_SHA256)
        #define BUILD_WDM_WITH_NULL_SHA256
    #endif
#endif

#if defined(BUILD_SSL_RSA_WITH_RC4_128_SHA) || \
    defined(BUILD_SSL_RSA_WITH_RC4_128_MD5)
    #define BUILD_ARC4
#endif

#if defined(BUILD_SSL_RSA_WITH_3DES_EDE_CBC_SHA)
    #define BUILD_DES3
#endif

#if defined(BUILD_TLS_RSA_WITH_AES_128_CBC_SHA) || \
    defined(BUILD_TLS_RSA_WITH_AES_256_CBC_SHA) || \
    defined(BUILD_TLS_ECDHE_ECDSA_WITH_AES_128_CBC_SHA256) || \
    defined(BUILD_TLS_DHE_PSK_WITH_AES_128_CBC_SHA256)
    #undef  BUILD_AES
    #define BUILD_AES
#endif

#if defined(BUILD_TLS_RSA_WITH_AES_128_GCM_SHA256) || \
    defined(BUILD_TLS_DHE_RSA_WITH_AES_128_GCM_SHA256) || \
    defined(BUILD_TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256) || \
    defined(BUILD_TLS_ECDHE_ECDSA_WITH_AES_128_GCM_SHA256) || \
    defined(BUILD_TLS_PSK_WITH_AES_128_GCM_SHA256) || \
    defined(BUILD_TLS_DHE_PSK_WITH_AES_128_GCM_SHA256) || \
    defined(BUILD_TLS_RSA_WITH_AES_256_GCM_SHA384) || \
    defined(BUILD_TLS_DHE_RSA_WITH_AES_256_GCM_SHA384) || \
    defined(BUILD_TLS_ECDHE_RSA_WITH_AES_256_GCM_SHA384) || \
    defined(BUILD_TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384) || \
    defined(BUILD_TLS_PSK_WITH_AES_256_GCM_SHA384) || \
    defined(BUILD_TLS_DHE_PSK_WITH_AES_256_GCM_SHA384) || \
    defined(BUILD_TLS_AES_128_GCM_SHA256) || \
    defined(BUILD_TLS_AES_256_GCM_SHA384)
    #define BUILD_AESGCM
#else
    /* No AES-GCM cipher suites available with build */
    #define NO_AESGCM_AEAD
#endif

#if defined(BUILD_TLS_DHE_RSA_WITH_CHACHA20_POLY1305_SHA256) || \
    defined(BUILD_TLS_DHE_RSA_WITH_CHACHA20_OLD_POLY1305_SHA256) || \
    defined(BUILD_TLS_DHE_PSK_WITH_CHACHA20_POLY1305_SHA256) || \
    defined(BUILD_TLS_ECDHE_ECDSA_WITH_CHACHA20_POLY1305_SHA256) || \
    defined(BUILD_TLS_ECDHE_ECDSA_WITH_CHACHA20_OLD_POLY1305_SHA256) || \
    defined(BUILD_TLS_ECDHE_RSA_WITH_CHACHA20_POLY1305_SHA256) || \
    defined(BUILD_TLS_ECDHE_RSA_WITH_CHACHA20_OLD_POLY1305_SHA256) || \
    defined(BUILD_TLS_ECDHE_PSK_WITH_CHACHA20_POLY1305_SHA256) || \
    defined(BUILD_TLS_PSK_WITH_CHACHA20_POLY1305_SHA256) || \
    defined(BUILD_TLS_CHACHA20_POLY1305_SHA256)
    /* Have an available ChaCha Poly cipher suite */
#else
    /* No ChaCha Poly cipher suites available with build */
    #define NO_CHAPOL_AEAD
#endif

#if defined(BUILD_TLS_RSA_WITH_HC_128_SHA) || \
    defined(BUILD_TLS_RSA_WITH_HC_128_MD5)
    #define BUILD_HC128
#endif

#if defined(BUILD_TLS_RSA_WITH_RABBIT_SHA)
    #define BUILD_RABBIT
#endif

#ifdef NO_DES3
    #define DES_BLOCK_SIZE 8
#else
    #undef  BUILD_DES3
    #define BUILD_DES3
#endif

#if defined(NO_AES) || defined(NO_AES_DECRYPT)
    #define AES_BLOCK_SIZE 16
    #undef  BUILD_AES
#else
    #undef  BUILD_AES
    #define BUILD_AES
#endif

#ifndef NO_RC4
    #undef  BUILD_ARC4
    #define BUILD_ARC4
#endif

#ifdef HAVE_CHACHA
    #define CHACHA20_BLOCK_SIZE 16
#endif

#if defined(WOLFSSL_MAX_STRENGTH) || \
    (defined(HAVE_AESGCM) && !defined(NO_AESGCM_AEAD)) || \
     defined(HAVE_AESCCM) || \
    (defined(HAVE_CHACHA) && defined(HAVE_POLY1305) && \
     !defined(NO_CHAPOL_AEAD)) || \
    (defined(WOLFSSL_TLS13) && defined(HAVE_NULL_CIPHER))

    #define HAVE_AEAD
#endif

#if defined(WOLFSSL_MAX_STRENGTH) || \
    defined(HAVE_ECC) || !defined(NO_DH)

    #define HAVE_PFS
#endif

#if defined(BUILD_SSL_RSA_WITH_IDEA_CBC_SHA)
    #define BUILD_IDEA
#endif

/* actual cipher values, 2nd byte */
enum {
    TLS_DHE_RSA_WITH_3DES_EDE_CBC_SHA = 0x16,
    TLS_DHE_RSA_WITH_AES_256_CBC_SHA  = 0x39,
    TLS_DHE_RSA_WITH_AES_128_CBC_SHA  = 0x33,
    TLS_DH_anon_WITH_AES_128_CBC_SHA  = 0x34,
    TLS_RSA_WITH_AES_256_CBC_SHA      = 0x35,
    TLS_RSA_WITH_AES_128_CBC_SHA      = 0x2F,
    TLS_RSA_WITH_NULL_MD5             = 0x01,
    TLS_RSA_WITH_NULL_SHA             = 0x02,
    TLS_PSK_WITH_AES_256_CBC_SHA      = 0x8d,
    TLS_PSK_WITH_AES_128_CBC_SHA256   = 0xae,
    TLS_PSK_WITH_AES_256_CBC_SHA384   = 0xaf,
    TLS_PSK_WITH_AES_128_CBC_SHA      = 0x8c,
    TLS_PSK_WITH_NULL_SHA256          = 0xb0,
    TLS_PSK_WITH_NULL_SHA384          = 0xb1,
    TLS_PSK_WITH_NULL_SHA             = 0x2c,
    SSL_RSA_WITH_RC4_128_SHA          = 0x05,
    SSL_RSA_WITH_RC4_128_MD5          = 0x04,
    SSL_RSA_WITH_3DES_EDE_CBC_SHA     = 0x0A,
    SSL_RSA_WITH_IDEA_CBC_SHA         = 0x07,

    /* ECC suites, first byte is 0xC0 (ECC_BYTE) */
    TLS_ECDHE_RSA_WITH_AES_256_CBC_SHA    = 0x14,
    TLS_ECDHE_RSA_WITH_AES_128_CBC_SHA    = 0x13,
    TLS_ECDHE_ECDSA_WITH_AES_256_CBC_SHA  = 0x0A,
    TLS_ECDHE_ECDSA_WITH_AES_128_CBC_SHA  = 0x09,
    TLS_ECDHE_RSA_WITH_RC4_128_SHA        = 0x11,
    TLS_ECDHE_ECDSA_WITH_RC4_128_SHA      = 0x07,
    TLS_ECDHE_RSA_WITH_3DES_EDE_CBC_SHA   = 0x12,
    TLS_ECDHE_ECDSA_WITH_3DES_EDE_CBC_SHA = 0x08,
    TLS_ECDHE_RSA_WITH_AES_128_CBC_SHA256   = 0x27,
    TLS_ECDHE_ECDSA_WITH_AES_128_CBC_SHA256 = 0x23,
    TLS_ECDHE_RSA_WITH_AES_256_CBC_SHA384   = 0x28,
    TLS_ECDHE_ECDSA_WITH_AES_256_CBC_SHA384 = 0x24,
    TLS_ECDHE_ECDSA_WITH_NULL_SHA           = 0x06,
    TLS_ECDHE_PSK_WITH_NULL_SHA256          = 0x3a,
    TLS_ECDHE_PSK_WITH_AES_128_CBC_SHA256   = 0x37,

    /* static ECDH, first byte is 0xC0 (ECC_BYTE) */
    TLS_ECDH_RSA_WITH_AES_256_CBC_SHA    = 0x0F,
    TLS_ECDH_RSA_WITH_AES_128_CBC_SHA    = 0x0E,
    TLS_ECDH_ECDSA_WITH_AES_256_CBC_SHA  = 0x05,
    TLS_ECDH_ECDSA_WITH_AES_128_CBC_SHA  = 0x04,
    TLS_ECDH_RSA_WITH_RC4_128_SHA        = 0x0C,
    TLS_ECDH_ECDSA_WITH_RC4_128_SHA      = 0x02,
    TLS_ECDH_RSA_WITH_3DES_EDE_CBC_SHA   = 0x0D,
    TLS_ECDH_ECDSA_WITH_3DES_EDE_CBC_SHA = 0x03,
    TLS_ECDH_RSA_WITH_AES_128_CBC_SHA256   = 0x29,
    TLS_ECDH_ECDSA_WITH_AES_128_CBC_SHA256 = 0x25,
    TLS_ECDH_RSA_WITH_AES_256_CBC_SHA384   = 0x2A,
    TLS_ECDH_ECDSA_WITH_AES_256_CBC_SHA384 = 0x26,

    /* wolfSSL extension - eSTREAM */
    TLS_RSA_WITH_HC_128_MD5       = 0xFB,
    TLS_RSA_WITH_HC_128_SHA       = 0xFC,
    TLS_RSA_WITH_RABBIT_SHA       = 0xFD,
    WDM_WITH_NULL_SHA256          = 0xFE, /* wolfSSL DTLS Multicast */

    /* wolfSSL extension - NTRU */
    TLS_NTRU_RSA_WITH_RC4_128_SHA      = 0xe5,
    TLS_NTRU_RSA_WITH_3DES_EDE_CBC_SHA = 0xe6,
    TLS_NTRU_RSA_WITH_AES_128_CBC_SHA  = 0xe7,  /* clashes w/official SHA-256 */
    TLS_NTRU_RSA_WITH_AES_256_CBC_SHA  = 0xe8,

    /* wolfSSL extension - NTRU , Quantum-safe Handshake
       first byte is 0xD0 (QSH_BYTE) */
    TLS_QSH      = 0x01,

    /* SHA256 */
    TLS_DHE_RSA_WITH_AES_256_CBC_SHA256 = 0x6b,
    TLS_DHE_RSA_WITH_AES_128_CBC_SHA256 = 0x67,
    TLS_RSA_WITH_AES_256_CBC_SHA256     = 0x3d,
    TLS_RSA_WITH_AES_128_CBC_SHA256     = 0x3c,
    TLS_RSA_WITH_NULL_SHA256            = 0x3b,
    TLS_DHE_PSK_WITH_AES_128_CBC_SHA256 = 0xb2,
    TLS_DHE_PSK_WITH_NULL_SHA256        = 0xb4,

    /* SHA384 */
    TLS_DHE_PSK_WITH_AES_256_CBC_SHA384 = 0xb3,
    TLS_DHE_PSK_WITH_NULL_SHA384        = 0xb5,

    /* AES-GCM */
    TLS_RSA_WITH_AES_128_GCM_SHA256          = 0x9c,
    TLS_RSA_WITH_AES_256_GCM_SHA384          = 0x9d,
    TLS_DHE_RSA_WITH_AES_128_GCM_SHA256      = 0x9e,
    TLS_DHE_RSA_WITH_AES_256_GCM_SHA384      = 0x9f,
    TLS_DH_anon_WITH_AES_256_GCM_SHA384      = 0xa7,
    TLS_PSK_WITH_AES_128_GCM_SHA256          = 0xa8,
    TLS_PSK_WITH_AES_256_GCM_SHA384          = 0xa9,
    TLS_DHE_PSK_WITH_AES_128_GCM_SHA256      = 0xaa,
    TLS_DHE_PSK_WITH_AES_256_GCM_SHA384      = 0xab,

    /* ECC AES-GCM, first byte is 0xC0 (ECC_BYTE) */
    TLS_ECDHE_ECDSA_WITH_AES_128_GCM_SHA256  = 0x2b,
    TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384  = 0x2c,
    TLS_ECDH_ECDSA_WITH_AES_128_GCM_SHA256   = 0x2d,
    TLS_ECDH_ECDSA_WITH_AES_256_GCM_SHA384   = 0x2e,
    TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256    = 0x2f,
    TLS_ECDHE_RSA_WITH_AES_256_GCM_SHA384    = 0x30,
    TLS_ECDH_RSA_WITH_AES_128_GCM_SHA256     = 0x31,
    TLS_ECDH_RSA_WITH_AES_256_GCM_SHA384     = 0x32,

    /* AES-CCM, first byte is 0xC0 but isn't ECC,
     * also, in some of the other AES-CCM suites
     * there will be second byte number conflicts
     * with non-ECC AES-GCM */
    TLS_RSA_WITH_AES_128_CCM_8         = 0xa0,
    TLS_RSA_WITH_AES_256_CCM_8         = 0xa1,
    TLS_ECDHE_ECDSA_WITH_AES_128_CCM   = 0xac,
    TLS_ECDHE_ECDSA_WITH_AES_128_CCM_8 = 0xae,
    TLS_ECDHE_ECDSA_WITH_AES_256_CCM_8 = 0xaf,
    TLS_PSK_WITH_AES_128_CCM           = 0xa4,
    TLS_PSK_WITH_AES_256_CCM           = 0xa5,
    TLS_PSK_WITH_AES_128_CCM_8         = 0xa8,
    TLS_PSK_WITH_AES_256_CCM_8         = 0xa9,
    TLS_DHE_PSK_WITH_AES_128_CCM       = 0xa6,
    TLS_DHE_PSK_WITH_AES_256_CCM       = 0xa7,

    /* Camellia */
    TLS_RSA_WITH_CAMELLIA_128_CBC_SHA        = 0x41,
    TLS_RSA_WITH_CAMELLIA_256_CBC_SHA        = 0x84,
    TLS_RSA_WITH_CAMELLIA_128_CBC_SHA256     = 0xba,
    TLS_RSA_WITH_CAMELLIA_256_CBC_SHA256     = 0xc0,
    TLS_DHE_RSA_WITH_CAMELLIA_128_CBC_SHA    = 0x45,
    TLS_DHE_RSA_WITH_CAMELLIA_256_CBC_SHA    = 0x88,
    TLS_DHE_RSA_WITH_CAMELLIA_128_CBC_SHA256 = 0xbe,
    TLS_DHE_RSA_WITH_CAMELLIA_256_CBC_SHA256 = 0xc4,

    /* chacha20-poly1305 suites first byte is 0xCC (CHACHA_BYTE) */
    TLS_ECDHE_RSA_WITH_CHACHA20_POLY1305_SHA256   = 0xa8,
    TLS_ECDHE_ECDSA_WITH_CHACHA20_POLY1305_SHA256 = 0xa9,
    TLS_DHE_RSA_WITH_CHACHA20_POLY1305_SHA256     = 0xaa,
    TLS_ECDHE_PSK_WITH_CHACHA20_POLY1305_SHA256   = 0xac,
    TLS_PSK_WITH_CHACHA20_POLY1305_SHA256         = 0xab,
    TLS_DHE_PSK_WITH_CHACHA20_POLY1305_SHA256     = 0xad,

    /* chacha20-poly1305 earlier version of nonce and padding (CHACHA_BYTE) */
    TLS_ECDHE_RSA_WITH_CHACHA20_OLD_POLY1305_SHA256   = 0x13,
    TLS_ECDHE_ECDSA_WITH_CHACHA20_OLD_POLY1305_SHA256 = 0x14,
    TLS_DHE_RSA_WITH_CHACHA20_OLD_POLY1305_SHA256     = 0x15,

    /* TLS v1.3 cipher suites */
    TLS_AES_128_GCM_SHA256       = 0x01,
    TLS_AES_256_GCM_SHA384       = 0x02,
    TLS_CHACHA20_POLY1305_SHA256 = 0x03,
    TLS_AES_128_CCM_SHA256       = 0x04,
    TLS_AES_128_CCM_8_SHA256     = 0x05,

    /* TLS v1.3 Integity only cipher suites - 0xC0 (ECC) first byte */
    TLS_SHA256_SHA256            = 0xB4,
    TLS_SHA384_SHA384            = 0xB5,

    /* Fallback SCSV (Signaling Cipher Suite Value) */
    TLS_FALLBACK_SCSV                        = 0x56,
    /* Renegotiation Indication Extension Special Suite */
    TLS_EMPTY_RENEGOTIATION_INFO_SCSV        = 0xff
};


#ifndef WOLFSSL_SESSION_TIMEOUT
    #define WOLFSSL_SESSION_TIMEOUT 500
    /* default session resumption cache timeout in seconds */
#endif


#ifndef WOLFSSL_DTLS_WINDOW_WORDS
    #define WOLFSSL_DTLS_WINDOW_WORDS 2
#endif /* WOLFSSL_DTLS_WINDOW_WORDS */
#define DTLS_WORD_BITS (sizeof(word32) * CHAR_BIT)
#define DTLS_SEQ_BITS  (WOLFSSL_DTLS_WINDOW_WORDS * DTLS_WORD_BITS)
#define DTLS_SEQ_SZ    (sizeof(word32) * WOLFSSL_DTLS_WINDOW_WORDS)

#ifndef WOLFSSL_MULTICAST
    #define WOLFSSL_DTLS_PEERSEQ_SZ 1
#else
    #ifndef WOLFSSL_MULTICAST_PEERS
        /* max allowed multicast group peers */
        #define WOLFSSL_MULTICAST_PEERS 100
    #endif
    #define WOLFSSL_DTLS_PEERSEQ_SZ WOLFSSL_MULTICAST_PEERS
#endif /* WOLFSSL_MULTICAST */

#ifndef WOLFSSL_MAX_MTU
    #define WOLFSSL_MAX_MTU 1500
#endif /* WOLFSSL_MAX_MTU */


/* set minimum DH key size allowed */
#ifndef WOLFSSL_MIN_DHKEY_BITS
    #ifdef WOLFSSL_MAX_STRENGTH
        #define WOLFSSL_MIN_DHKEY_BITS 2048
    #else
        #define WOLFSSL_MIN_DHKEY_BITS 1024
    #endif
#endif
#if (WOLFSSL_MIN_DHKEY_BITS % 8)
    #error DH minimum bit size must be multiple of 8
#endif
#if (WOLFSSL_MIN_DHKEY_BITS > 16000)
    #error DH minimum bit size must not be greater than 16000
#endif
#define MIN_DHKEY_SZ (WOLFSSL_MIN_DHKEY_BITS / 8)
/* set maximum DH key size allowed */
#ifndef WOLFSSL_MAX_DHKEY_BITS
    #if (defined(USE_FAST_MATH) && defined(FP_MAX_BITS) && FP_MAX_BITS >= 16384)
        #define WOLFSSL_MAX_DHKEY_BITS (FP_MAX_BITS / 2)
    #else
        #define WOLFSSL_MAX_DHKEY_BITS 4096
    #endif
#endif
#if (WOLFSSL_MAX_DHKEY_BITS % 8)
    #error DH maximum bit size must be multiple of 8
#endif
#if (WOLFSSL_MAX_DHKEY_BITS > 16000)
    #error DH maximum bit size must not be greater than 16000
#endif
#define MAX_DHKEY_SZ (WOLFSSL_MAX_DHKEY_BITS / 8)

#ifndef MAX_PSK_ID_LEN
    /* max psk identity/hint supported */
    #if defined(WOLFSSL_TLS13)
        /* OpenSSL has a 1472 byte sessiont ticket */
        #define MAX_PSK_ID_LEN 1536
    #else
        #define MAX_PSK_ID_LEN 128
    #endif
#endif

#ifndef MAX_EARLY_DATA_SZ
    /* maximum early data size */
    #define MAX_EARLY_DATA_SZ  4096
#endif

#ifndef WOLFSSL_MAX_RSA_BITS
    #if (defined(USE_FAST_MATH) && defined(FP_MAX_BITS) && FP_MAX_BITS >= 16384)
        #define WOLFSSL_MAX_RSA_BITS (FP_MAX_BITS / 2)
    #else
        #define WOLFSSL_MAX_RSA_BITS 4096
    #endif
#endif
#if (WOLFSSL_MAX_RSA_BITS % 8)
    #error RSA maximum bit size must be multiple of 8
#endif

enum Misc {
    CIPHER_BYTE = 0x00,            /* Default ciphers */
    ECC_BYTE    = 0xC0,            /* ECC first cipher suite byte */
    QSH_BYTE    = 0xD0,            /* Quantum-safe Handshake cipher suite */
    CHACHA_BYTE = 0xCC,            /* ChaCha first cipher suite */
    TLS13_BYTE  = 0x13,            /* TLS v1.3 first byte of cipher suite */

    SEND_CERT       = 1,
    SEND_BLANK_CERT = 2,

    DTLS_MAJOR      = 0xfe,     /* DTLS major version number */
    DTLS_MINOR      = 0xff,     /* DTLS minor version number */
    DTLSv1_2_MINOR  = 0xfd,     /* DTLS minor version number */
    SSLv3_MAJOR     = 3,        /* SSLv3 and TLSv1+  major version number */
    SSLv3_MINOR     = 0,        /* TLSv1   minor version number */
    TLSv1_MINOR     = 1,        /* TLSv1   minor version number */
    TLSv1_1_MINOR   = 2,        /* TLSv1_1 minor version number */
    TLSv1_2_MINOR   = 3,        /* TLSv1_2 minor version number */
    TLSv1_3_MINOR   = 4,        /* TLSv1_3 minor version number */
    TLS_DRAFT_MAJOR = 0x7f,     /* Draft TLS major version number */
    OLD_HELLO_ID    = 0x01,     /* SSLv2 Client Hello Indicator */
    INVALID_BYTE    = 0xff,     /* Used to initialize cipher specs values */
    NO_COMPRESSION  =  0,
    ZLIB_COMPRESSION = 221,     /* wolfSSL zlib compression */
    HELLO_EXT_SIG_ALGO = 13,    /* ID for the sig_algo hello extension */
    HELLO_EXT_EXTMS = 0x0017,   /* ID for the extended master secret ext */
    SECRET_LEN      = WOLFSSL_MAX_MASTER_KEY_LENGTH,
                                /* pre RSA and all master */
#if defined(WOLFSSL_MYSQL_COMPATIBLE) || \
    (defined(USE_FAST_MATH) && defined(FP_MAX_BITS) && FP_MAX_BITS >= 16384)
#ifndef NO_PSK
    ENCRYPT_LEN     = (FP_MAX_BITS / 2 / 8) + MAX_PSK_ID_LEN + 2,
#else
    ENCRYPT_LEN     = 1024,     /* allow 8192 bit static buffer */
#endif
#else
#ifndef NO_PSK
    ENCRYPT_LEN     = 512 + MAX_PSK_ID_LEN + 2,    /* 4096 bit static buffer */
#else
    ENCRYPT_LEN     = 512,      /* allow 4096 bit static buffer */
#endif
#endif
    SIZEOF_SENDER   =  4,       /* clnt or srvr           */
    FINISHED_SZ     = 36,       /* WC_MD5_DIGEST_SIZE + WC_SHA_DIGEST_SIZE */
    MAX_RECORD_SIZE = 16384,    /* 2^14, max size by standard */
    MAX_PLAINTEXT_SZ   = (1 << 14),        /* Max plaintext sz   */
    MAX_TLS_CIPHER_SZ  = (1 << 14) + 2048, /* Max TLS encrypted data sz */
#ifdef WOLFSSL_TLS13
    MAX_TLS13_PLAIN_SZ = (1 << 14) + 1,    /* Max unencrypted data sz */
    MAX_TLS13_ENC_SZ   = (1 << 14) + 256,  /* Max encrypted data sz   */
#endif
    MAX_MSG_EXTRA   = 38 + WC_MAX_DIGEST_SIZE,
                                /* max added to msg, mac + pad  from */
                                /* RECORD_HEADER_SZ + BLOCK_SZ (pad) + Max
                                   digest sz + BLOC_SZ (iv) + pad byte (1) */
    MAX_COMP_EXTRA  = 1024,     /* max compression extra */
    MAX_MTU         = WOLFSSL_MAX_MTU,     /* max expected MTU */
    MAX_UDP_SIZE    = 8192 - 100, /* was MAX_MTU - 100 */
    MAX_DH_SZ       = (MAX_DHKEY_SZ * 3) + 12, /* DH_P, DH_G and DH_Pub */
                                /* 4096 p, pub, g + 2 byte size for each */
    MAX_STR_VERSION = 8,        /* string rep of protocol version */

    PAD_MD5        = 48,       /* pad length for finished */
    PAD_SHA        = 40,       /* pad length for finished */
    MAX_PAD_SIZE   = 256,      /* maximum length of padding */

    LENGTH_SZ      =  2,       /* length field for HMAC, data only */
    VERSION_SZ     =  2,       /* length of proctocol version */
    SEQ_SZ         =  8,       /* 64 bit sequence number  */
    ALERT_SIZE     =  2,       /* level + description     */
    VERIFY_HEADER  =  2,       /* always use 2 bytes      */
    EXTS_SZ        =  2,       /* always use 2 bytes      */
    EXT_ID_SZ      =  2,       /* always use 2 bytes      */
    MAX_DH_SIZE    = MAX_DHKEY_SZ+1,
                               /* Max size plus possible leading 0 */
    NAMED_DH_MASK  = 0x100,    /* Named group mask for DH parameters  */
    MIN_FFHDE_GROUP = 0x100,   /* Named group minimum for FFDHE parameters  */
    MAX_FFHDE_GROUP = 0x1FF,   /* Named group maximum for FFDHE parameters  */
    SESSION_HINT_SZ = 4,       /* session timeout hint */
    SESSION_ADD_SZ = 4,        /* session age add */
    TICKET_NONCE_LEN_SZ = 1,   /* Ticket nonce length size */
    DEF_TICKET_NONCE_SZ = 1,   /* Default ticket nonce size */
    MAX_TICKET_NONCE_SZ = 8,   /* maximum ticket nonce size */
    MAX_LIFETIME   = 604800,   /* maximum ticket lifetime */

    RAN_LEN      = 32,         /* random length           */
    SEED_LEN     = RAN_LEN * 2, /* tls prf seed length    */
    ID_LEN       = 32,         /* session id length       */
    COOKIE_SECRET_SZ = 14,     /* dtls cookie secret size */
    MAX_COOKIE_LEN = 32,       /* max dtls cookie size    */
    COOKIE_SZ    = 20,         /* use a 20 byte cookie    */
    SUITE_LEN    =  2,         /* cipher suite sz length  */
    ENUM_LEN     =  1,         /* always a byte           */
    OPAQUE8_LEN  =  1,         /* 1 byte                  */
    OPAQUE16_LEN =  2,         /* 2 bytes                 */
    OPAQUE24_LEN =  3,         /* 3 bytes                 */
    OPAQUE32_LEN =  4,         /* 4 bytes                 */
    OPAQUE64_LEN =  8,         /* 8 bytes                 */
    COMP_LEN     =  1,         /* compression length      */
    CURVE_LEN    =  2,         /* ecc named curve length  */
    KE_GROUP_LEN =  2,         /* key exchange group length */
    SERVER_ID_LEN = 20,        /* server session id length  */

    HANDSHAKE_HEADER_SZ   = 4,  /* type + length(3)        */
    RECORD_HEADER_SZ      = 5,  /* type + version + len(2) */
    CERT_HEADER_SZ        = 3,  /* always 3 bytes          */
    REQ_HEADER_SZ         = 2,  /* cert request header sz  */
    HINT_LEN_SZ           = 2,  /* length of hint size field */
    TRUNCATED_HMAC_SZ     = 10, /* length of hmac w/ truncated hmac extension */
    HELLO_EXT_SZ          = 4,  /* base length of a hello extension */
    HELLO_EXT_TYPE_SZ     = 2,  /* length of a hello extension type */
    HELLO_EXT_SZ_SZ       = 2,  /* length of a hello extension size */
    HELLO_EXT_SIGALGO_SZ  = 2,  /* length of number of items in sigalgo list */

    DTLS_HANDSHAKE_HEADER_SZ = 12, /* normal + seq(2) + offset(3) + length(3) */
    DTLS_RECORD_HEADER_SZ    = 13, /* normal + epoch(2) + seq_num(6) */
    DTLS_HANDSHAKE_EXTRA     = 8,  /* diff from normal */
    DTLS_RECORD_EXTRA        = 8,  /* diff from normal */
    DTLS_HANDSHAKE_SEQ_SZ    = 2,  /* handshake header sequence number */
    DTLS_HANDSHAKE_FRAG_SZ   = 3,  /* fragment offset and length are 24 bit */
    DTLS_POOL_SZ             = 255,/* allowed number of list items in TX pool */
    DTLS_EXPORT_PRO          = 165,/* wolfSSL protocol for serialized session */
    DTLS_EXPORT_STATE_PRO    = 166,/* wolfSSL protocol for serialized state */
    DTLS_EXPORT_VERSION      = 4,  /* wolfSSL version for serialized session */
    DTLS_EXPORT_OPT_SZ       = 60, /* amount of bytes used from Options */
    DTLS_EXPORT_VERSION_3    = 3,  /* wolfSSL version before TLS 1.3 addition */
    DTLS_EXPORT_OPT_SZ_3     = 59, /* amount of bytes used from Options */
    DTLS_EXPORT_KEY_SZ       = 325 + (DTLS_SEQ_SZ * 2),
                                   /* max amount of bytes used from Keys */
    DTLS_EXPORT_MIN_KEY_SZ   = 85 + (DTLS_SEQ_SZ * 2),
                                   /* min amount of bytes used from Keys */
    DTLS_EXPORT_SPC_SZ       = 16, /* amount of bytes used from CipherSpecs */
    DTLS_EXPORT_LEN          = 2,  /* 2 bytes for length and protocol */
    DTLS_EXPORT_IP           = 46, /* max ip size IPv4 mapped IPv6 */
    MAX_EXPORT_BUFFER        = 514, /* max size of buffer for exporting */
    MAX_EXPORT_STATE_BUFFER  = (DTLS_EXPORT_MIN_KEY_SZ) + (3 * DTLS_EXPORT_LEN),
                                    /* max size of buffer for exporting state */
    FINISHED_LABEL_SZ   = 15,  /* TLS finished label size */
    TLS_FINISHED_SZ     = 12,  /* TLS has a shorter size  */
    EXT_MASTER_LABEL_SZ = 22,  /* TLS extended master secret label sz */
    MASTER_LABEL_SZ     = 13,  /* TLS master secret label sz */
    KEY_LABEL_SZ        = 13,  /* TLS key block expansion sz */
    PROTOCOL_LABEL_SZ   = 9,   /* Length of the protocol label */
    MAX_LABEL_SZ        = 34,  /* Maximum length of a label */
    MAX_HKDF_LABEL_SZ   = OPAQUE16_LEN +
                          OPAQUE8_LEN + PROTOCOL_LABEL_SZ + MAX_LABEL_SZ +
                          OPAQUE8_LEN + WC_MAX_DIGEST_SIZE,
    MAX_REQUEST_SZ      = 256, /* Maximum cert req len (no auth yet */
    SESSION_FLUSH_COUNT = 256, /* Flush session cache unless user turns off */
    TLS_MAX_PAD_SZ      = 255, /* Max padding in TLS */

#if defined(HAVE_FIPS) && \
    (!defined(HAVE_FIPS_VERSION) || (HAVE_FIPS_VERSION < 2))
    MAX_SYM_KEY_SIZE    = AES_256_KEY_SIZE,
#else
    #if defined(HAVE_NULL_CIPHER) && defined(WOLFSSL_TLS13)
        #if defined(WOLFSSL_SHA384) && WC_MAX_SYM_KEY_SIZE < 48
            MAX_SYM_KEY_SIZE    = WC_SHA384_DIGEST_SIZE,
        #elif !defined(NO_SHA256) && WC_MAX_SYM_KEY_SIZE < 32
            MAX_SYM_KEY_SIZE    = WC_SHA256_DIGEST_SIZE,
        #else
            MAX_SYM_KEY_SIZE    = WC_MAX_SYM_KEY_SIZE,
        #endif
    #else
        MAX_SYM_KEY_SIZE    = WC_MAX_SYM_KEY_SIZE,
    #endif
#endif

#if defined(HAVE_SELFTEST) && \
    (!defined(HAVE_SELFTEST_VERSION) || (HAVE_SELFTEST_VERSION < 2))
    #ifndef WOLFSSL_AES_KEY_SIZE_ENUM
    #define WOLFSSL_AES_KEY_SIZE_ENUM
    AES_IV_SIZE         = 16,
    AES_128_KEY_SIZE    = 16,
    AES_192_KEY_SIZE    = 24,
    AES_256_KEY_SIZE    = 32,
    #endif
#endif

    MAX_IV_SZ           = AES_BLOCK_SIZE,

    AEAD_SEQ_OFFSET     = 4,   /* Auth Data: Sequence number */
    AEAD_TYPE_OFFSET    = 8,   /* Auth Data: Type            */
    AEAD_VMAJ_OFFSET    = 9,   /* Auth Data: Major Version   */
    AEAD_VMIN_OFFSET    = 10,  /* Auth Data: Minor Version   */
    AEAD_LEN_OFFSET     = 11,  /* Auth Data: Length          */
    AEAD_AUTH_DATA_SZ   = 13,  /* Size of the data to authenticate */
    AEAD_NONCE_SZ       = 12,
    AESGCM_IMP_IV_SZ    = 4,   /* Size of GCM/CCM AEAD implicit IV */
    AESGCM_EXP_IV_SZ    = 8,   /* Size of GCM/CCM AEAD explicit IV */
    AESGCM_NONCE_SZ     = AESGCM_EXP_IV_SZ + AESGCM_IMP_IV_SZ,

    CHACHA20_IMP_IV_SZ  = 12,  /* Size of ChaCha20 AEAD implicit IV */
    CHACHA20_NONCE_SZ   = 12,  /* Size of ChacCha20 nonce           */
    CHACHA20_OLD_OFFSET = 4,   /* Offset for seq # in old poly1305  */

    /* For any new implicit/explicit IV size adjust AEAD_MAX_***_SZ */

    AES_GCM_AUTH_SZ     = 16, /* AES-GCM Auth Tag length    */
    AES_CCM_16_AUTH_SZ  = 16, /* AES-CCM-16 Auth Tag length */
    AES_CCM_8_AUTH_SZ   = 8,  /* AES-CCM-8 Auth Tag Length  */
    AESCCM_NONCE_SZ     = 12,

    CAMELLIA_128_KEY_SIZE = 16, /* for 128 bit */
    CAMELLIA_192_KEY_SIZE = 24, /* for 192 bit */
    CAMELLIA_256_KEY_SIZE = 32, /* for 256 bit */
    CAMELLIA_IV_SIZE      = 16, /* always block size */

    CHACHA20_256_KEY_SIZE = 32,  /* for 256 bit             */
    CHACHA20_128_KEY_SIZE = 16,  /* for 128 bit             */
    CHACHA20_IV_SIZE      = 12,  /* 96 bits for iv          */

    POLY1305_AUTH_SZ    = 16,  /* 128 bits                */

    HMAC_NONCE_SZ       = 12,  /* Size of HMAC nonce */

    HC_128_KEY_SIZE     = 16,  /* 128 bits                */
    HC_128_IV_SIZE      = 16,  /* also 128 bits           */

    RABBIT_KEY_SIZE     = 16,  /* 128 bits                */
    RABBIT_IV_SIZE      =  8,  /* 64 bits for iv          */

    EVP_SALT_SIZE       =  8,  /* evp salt size 64 bits   */

#ifndef ECDHE_SIZE /* allow this to be overridden at compile-time */
    ECDHE_SIZE          = 32,  /* ECHDE server size defaults to 256 bit */
#endif
    MAX_EXPORT_ECC_SZ   = 256, /* Export ANS X9.62 max future size */
    MAX_CURVE_NAME_SZ   = 16,  /* Maximum size of curve name string */

    NEW_SA_MAJOR        = 8,   /* Most significant byte used with new sig algos */
    ED25519_SA_MAJOR    = 8,   /* Most significant byte for ED25519 */
    ED25519_SA_MINOR    = 7,   /* Least significant byte for ED25519 */
    ED448_SA_MAJOR      = 8,   /* Most significant byte for ED448 */
    ED448_SA_MINOR      = 8,   /* Least significant byte for ED448 */

    MIN_RSA_SHA512_PSS_BITS = 512 * 2 + 8 * 8, /* Min key size */
    MIN_RSA_SHA384_PSS_BITS = 384 * 2 + 8 * 8, /* Min key size */

#ifndef NO_RSA
    MAX_CERT_VERIFY_SZ = WOLFSSL_MAX_RSA_BITS / 8, /* max RSA bytes */
#elif defined(HAVE_ECC)
    MAX_CERT_VERIFY_SZ = ECC_MAX_SIG_SIZE, /* max ECC  */
#elif defined(HAVE_ED448)
    MAX_CERT_VERIFY_SZ = ED448_SIG_SIZE,   /* max Ed448  */
#elif defined(HAVE_ED25519)
    MAX_CERT_VERIFY_SZ = ED25519_SIG_SIZE, /* max Ed25519  */
#else
    MAX_CERT_VERIFY_SZ = 1024, /* max default  */
#endif
    CLIENT_HELLO_FIRST =  35,  /* Protocol + RAN_LEN + sizeof(id_len) */
    MAX_SUITE_NAME     =  48,  /* maximum length of cipher suite string */

    DTLS_TIMEOUT_INIT       =  1, /* default timeout init for DTLS receive  */
    DTLS_TIMEOUT_MAX        = 64, /* default max timeout for DTLS receive */
    DTLS_TIMEOUT_MULTIPLIER =  2, /* default timeout multiplier for DTLS recv */

    NULL_TERM_LEN      =   1,  /* length of null '\0' termination character */
    MAX_PSK_KEY_LEN    =  64,  /* max psk key supported */
    MIN_PSK_ID_LEN     =   6,  /* min length of identities */
    MIN_PSK_BINDERS_LEN=  33,  /* min length of binders */
    MAX_TICKET_AGE_SECS=  10,  /* maximum ticket age in seconds */

#ifndef MAX_WOLFSSL_FILE_SIZE
    MAX_WOLFSSL_FILE_SIZE = 1024ul * 1024ul * 4,  /* 4 mb file size alloc limit */
#endif

    MAX_X509_SIZE      = 2048, /* max static x509 buffer size */
    CERT_MIN_SIZE      =  256, /* min PEM cert size with header/footer */

    MAX_NTRU_PUB_KEY_SZ = 1027, /* NTRU max for now */
    MAX_NTRU_ENCRYPT_SZ = 1027, /* NTRU max for now */
    MAX_NTRU_BITS       =  256, /* max symmetric bit strength */
    NO_SNIFF           =   0,  /* not sniffing */
    SNIFF              =   1,  /* currently sniffing */

    HASH_SIG_SIZE      =   2,  /* default SHA1 RSA */

    NO_COPY            =   0,  /* should we copy static buffer for write */
    COPY               =   1,  /* should we copy static buffer for write */

    INVALID_PEER_ID    = 0xFFFF, /* Initialize value for peer ID. */

    PREV_ORDER         = -1,   /* Sequence number is in previous epoch. */
    PEER_ORDER         = 1,    /* Peer sequence number for verify. */
    CUR_ORDER          = 0,    /* Current sequence number. */
    WRITE_PROTO        = 1,    /* writing a protocol message */
    READ_PROTO         = 0     /* reading a protocol message */
};

/* minimum Downgrade Minor version */
#ifndef WOLFSSL_MIN_DOWNGRADE
    #ifndef NO_OLD_TLS
        #define WOLFSSL_MIN_DOWNGRADE TLSv1_MINOR
    #else
        #define WOLFSSL_MIN_DOWNGRADE TLSv1_2_MINOR
    #endif
#endif

/* Set max implicit IV size for AEAD cipher suites */
#define AEAD_MAX_IMP_SZ 12

/* Set max explicit IV size for AEAD cipher suites */
#define AEAD_MAX_EXP_SZ 8


#ifndef WOLFSSL_MAX_SUITE_SZ
    #define WOLFSSL_MAX_SUITE_SZ 300
    /* 150 suites for now! */
#endif

/* number of items in the signature algo list */
#ifndef WOLFSSL_MAX_SIGALGO
    #define WOLFSSL_MAX_SIGALGO 36
#endif


/* set minimum ECC key size allowed */
#ifndef WOLFSSL_MIN_ECC_BITS
    #ifdef WOLFSSL_MAX_STRENGTH
        #define WOLFSSL_MIN_ECC_BITS  256
    #else
        #define WOLFSSL_MIN_ECC_BITS 224
    #endif
#endif /* WOLFSSL_MIN_ECC_BITS */
#if (WOLFSSL_MIN_ECC_BITS % 8)
    /* Some ECC keys are not divisible by 8 such as prime239v1 or sect131r1.
       In these cases round down to the nearest value divisible by 8. The
       restriction of being divisible by 8 is in place to match wc_ecc_size
       function from wolfSSL.
     */
    #error ECC minimum bit size must be a multiple of 8
#endif
#define MIN_ECCKEY_SZ (WOLFSSL_MIN_ECC_BITS / 8)

/* set minimum RSA key size allowed */
#ifndef WOLFSSL_MIN_RSA_BITS
    #ifdef WOLFSSL_MAX_STRENGTH
        #define WOLFSSL_MIN_RSA_BITS 2048
    #else
        #define WOLFSSL_MIN_RSA_BITS 1024
    #endif
#endif /* WOLFSSL_MIN_RSA_BITS */
#if (WOLFSSL_MIN_RSA_BITS % 8)
    /* This is to account for the example case of a min size of 2050 bits but
       still allows 2049 bit key. So we need the measurement to be in bytes. */
    #error RSA minimum bit size must be a multiple of 8
#endif
#define MIN_RSAKEY_SZ (WOLFSSL_MIN_RSA_BITS / 8)

#ifdef SESSION_INDEX
/* Shift values for making a session index */
#define SESSIDX_ROW_SHIFT 4
#define SESSIDX_IDX_MASK  0x0F
#endif


/* max cert chain peer depth */
#ifndef MAX_CHAIN_DEPTH
    #define MAX_CHAIN_DEPTH 9
#endif

/* max size of a certificate message payload */
/* assumes MAX_CHAIN_DEPTH number of certificates at 2kb per certificate */
#ifndef MAX_CERTIFICATE_SZ
    #define MAX_CERTIFICATE_SZ \
                CERT_HEADER_SZ + \
                (MAX_X509_SIZE + CERT_HEADER_SZ) * MAX_CHAIN_DEPTH
#endif

/* max size of a handshake message, currently set to the certificate */
#ifndef MAX_HANDSHAKE_SZ
    #define MAX_HANDSHAKE_SZ MAX_CERTIFICATE_SZ
#endif

#ifndef SESSION_TICKET_LEN
    #define SESSION_TICKET_LEN 256
#endif

#ifndef SESSION_TICKET_HINT_DEFAULT
    #define SESSION_TICKET_HINT_DEFAULT 300
#endif


/* don't use extra 3/4k stack space unless need to */
#ifdef HAVE_NTRU
    #define MAX_ENCRYPT_SZ MAX_NTRU_ENCRYPT_SZ
#else
    #define MAX_ENCRYPT_SZ ENCRYPT_LEN
#endif


/* states */
enum states {
    NULL_STATE = 0,

    SERVER_HELLOVERIFYREQUEST_COMPLETE,
    SERVER_HELLO_RETRY_REQUEST_COMPLETE,
    SERVER_HELLO_COMPLETE,
    SERVER_ENCRYPTED_EXTENSIONS_COMPLETE,
    SERVER_CERT_COMPLETE,
    SERVER_CERT_VERIFY_COMPLETE,
    SERVER_KEYEXCHANGE_COMPLETE,
    SERVER_HELLODONE_COMPLETE,
	SERVER_CHANGECIPHERSPEC_COMPLETE,
    SERVER_FINISHED_COMPLETE,

    CLIENT_HELLO_RETRY,
    CLIENT_HELLO_COMPLETE,
    CLIENT_KEYEXCHANGE_COMPLETE,
	CLIENT_CHANGECIPHERSPEC_COMPLETE,
    CLIENT_FINISHED_COMPLETE,

    HANDSHAKE_DONE
};

/* SSL Version */
typedef struct ProtocolVersion {
    byte major;
    byte minor;
} WOLFSSL_PACK ProtocolVersion;


WOLFSSL_LOCAL ProtocolVersion MakeSSLv3(void);
WOLFSSL_LOCAL ProtocolVersion MakeTLSv1(void);
WOLFSSL_LOCAL ProtocolVersion MakeTLSv1_1(void);
WOLFSSL_LOCAL ProtocolVersion MakeTLSv1_2(void);
WOLFSSL_LOCAL ProtocolVersion MakeTLSv1_3(void);

#ifdef WOLFSSL_DTLS
    WOLFSSL_LOCAL ProtocolVersion MakeDTLSv1(void);
    WOLFSSL_LOCAL ProtocolVersion MakeDTLSv1_2(void);

    #ifdef WOLFSSL_SESSION_EXPORT
    WOLFSSL_LOCAL int wolfSSL_dtls_import_internal(WOLFSSL* ssl, byte* buf,
                                                                     word32 sz);
    WOLFSSL_LOCAL int wolfSSL_dtls_export_internal(WOLFSSL* ssl, byte* buf,
                                                                     word32 sz);
    WOLFSSL_LOCAL int wolfSSL_dtls_export_state_internal(WOLFSSL* ssl,
                                                          byte* buf, word32 sz);
    WOLFSSL_LOCAL int wolfSSL_dtls_import_state_internal(WOLFSSL* ssl,
                                                          byte* buf, word32 sz);
    WOLFSSL_LOCAL int wolfSSL_send_session(WOLFSSL* ssl);
    #endif
#endif


/* wolfSSL method type */
struct WOLFSSL_METHOD {
    ProtocolVersion version;
    byte            side;         /* connection side, server or client */
    byte            downgrade;    /* whether to downgrade version, default no */
};

/* wolfSSL buffer type - internal uses "buffer" type */
typedef WOLFSSL_BUFFER_INFO buffer;

typedef struct Suites Suites;


/* defaults to client */
WOLFSSL_LOCAL void InitSSL_Method(WOLFSSL_METHOD*, ProtocolVersion);

WOLFSSL_LOCAL int InitSSL_Suites(WOLFSSL* ssl);
WOLFSSL_LOCAL int InitSSL_Side(WOLFSSL* ssl, word16 side);

/* for sniffer */
WOLFSSL_LOCAL int DoFinished(WOLFSSL* ssl, const byte* input, word32* inOutIdx,
                            word32 size, word32 totalSz, int sniff);
#ifdef WOLFSSL_TLS13
WOLFSSL_LOCAL int DoTls13Finished(WOLFSSL* ssl, const byte* input, word32* inOutIdx,
                           word32 size, word32 totalSz, int sniff);
#endif
WOLFSSL_LOCAL int DoApplicationData(WOLFSSL* ssl, byte* input, word32* inOutIdx);
/* TLS v1.3 needs these */
WOLFSSL_LOCAL int  HandleTlsResumption(WOLFSSL* ssl, int bogusID,
                                       Suites* clSuites);
#ifdef WOLFSSL_TLS13
WOLFSSL_LOCAL int FindSuite(Suites* suites, byte first, byte second);
#endif
WOLFSSL_LOCAL int  DoClientHello(WOLFSSL* ssl, const byte* input, word32*,
                                 word32);
#ifdef WOLFSSL_TLS13
WOLFSSL_LOCAL int DoTls13ClientHello(WOLFSSL* ssl, const byte* input,
                                     word32* inOutIdx, word32 helloSz);
#endif
WOLFSSL_LOCAL int  DoServerHello(WOLFSSL* ssl, const byte* input, word32*,
                                 word32);
WOLFSSL_LOCAL int  CompleteServerHello(WOLFSSL *ssl);
WOLFSSL_LOCAL int  CheckVersion(WOLFSSL *ssl, ProtocolVersion pv);
WOLFSSL_LOCAL int  PickHashSigAlgo(WOLFSSL* ssl, const byte* hashSigAlgo,
                                   word32 hashSigAlgoSz);
WOLFSSL_LOCAL int  DecodePrivateKey(WOLFSSL *ssl, word16* length);
#ifdef HAVE_PK_CALLBACKS
WOLFSSL_LOCAL int GetPrivateKeySigSize(WOLFSSL* ssl);
#ifndef NO_ASN
    WOLFSSL_LOCAL int  InitSigPkCb(WOLFSSL* ssl, SignatureCtx* sigCtx);
#endif
#endif
WOLFSSL_LOCAL void FreeKeyExchange(WOLFSSL* ssl);
WOLFSSL_LOCAL void FreeSuites(WOLFSSL* ssl);
WOLFSSL_LOCAL int  ProcessPeerCerts(WOLFSSL* ssl, byte* input, word32* inOutIdx, word32 size);
WOLFSSL_LOCAL int  MatchDomainName(const char* pattern, int len, const char* str);
#ifndef NO_CERTS
WOLFSSL_LOCAL int  CheckForAltNames(DecodedCert* dCert, const char* domain, int* checkCN);
WOLFSSL_LOCAL int  CheckIPAddr(DecodedCert* dCert, const char* ipasc);
#endif
WOLFSSL_LOCAL int  CreateTicket(WOLFSSL* ssl);
WOLFSSL_LOCAL int  HashRaw(WOLFSSL* ssl, const byte* output, int sz);
WOLFSSL_LOCAL int  HashOutput(WOLFSSL* ssl, const byte* output, int sz,
                              int ivSz);
WOLFSSL_LOCAL int  HashInput(WOLFSSL* ssl, const byte* input, int sz);

#if defined(OPENSSL_ALL) || defined(HAVE_STUNNEL) || defined(WOLFSSL_NGINX) || defined(WOLFSSL_HAPROXY)
WOLFSSL_LOCAL int SNI_Callback(WOLFSSL* ssl);
#endif
#ifdef WOLFSSL_TLS13
WOLFSSL_LOCAL int  DecryptTls13(WOLFSSL* ssl, byte* output, const byte* input,
                                word16 sz, const byte* aad, word16 aadSz);
WOLFSSL_LOCAL int  DoTls13HandShakeMsgType(WOLFSSL* ssl, byte* input,
                                           word32* inOutIdx, byte type,
                                           word32 size, word32 totalSz);
WOLFSSL_LOCAL int  DoTls13HandShakeMsg(WOLFSSL* ssl, byte* input,
                                       word32* inOutIdx, word32 totalSz);
WOLFSSL_LOCAL int DoTls13ServerHello(WOLFSSL* ssl, const byte* input,
                                     word32* inOutIdx, word32 helloSz,
                                     byte* extMsgType);
#endif
int TimingPadVerify(WOLFSSL* ssl, const byte* input, int padLen, int t,
                    int pLen, int content);


enum {
    FORCED_FREE = 1,
    NO_FORCED_FREE = 0
};


/* only use compression extra if using compression */
#ifdef HAVE_LIBZ
    #define COMP_EXTRA MAX_COMP_EXTRA
#else
    #define COMP_EXTRA 0
#endif

/* only the sniffer needs space in the buffer for extra MTU record(s) */
#ifdef WOLFSSL_SNIFFER
    #define MTU_EXTRA MAX_MTU * 3
#else
    #define MTU_EXTRA 0
#endif


/* embedded callbacks require large static buffers, make sure on */
#ifdef WOLFSSL_CALLBACKS
    #undef  LARGE_STATIC_BUFFERS
    #define LARGE_STATIC_BUFFERS
#endif


/* give user option to use 16K static buffers */
#if defined(LARGE_STATIC_BUFFERS)
    #define RECORD_SIZE MAX_RECORD_SIZE
#else
    #ifdef WOLFSSL_DTLS
        #define RECORD_SIZE MAX_MTU
    #else
        #define RECORD_SIZE 128
    #endif
#endif


/* user option to turn off 16K output option */
/* if using small static buffers (default) and SSL_write tries to write data
   larger than the record we have, dynamically get it, unless user says only
   write in static buffer chunks  */
#ifndef STATIC_CHUNKS_ONLY
    #define OUTPUT_RECORD_SIZE MAX_RECORD_SIZE
#else
    #define OUTPUT_RECORD_SIZE RECORD_SIZE
#endif

/* wolfSSL input buffer

   RFC 2246:

   length
       The length (in bytes) of the following TLSPlaintext.fragment.
       The length should not exceed 2^14.
*/
#if defined(LARGE_STATIC_BUFFERS)
    #define STATIC_BUFFER_LEN RECORD_HEADER_SZ + RECORD_SIZE + COMP_EXTRA + \
             MTU_EXTRA + MAX_MSG_EXTRA
#else
    /* don't fragment memory from the record header */
    #define STATIC_BUFFER_LEN RECORD_HEADER_SZ
#endif

typedef struct {
    ALIGN16 byte staticBuffer[STATIC_BUFFER_LEN];
    byte*  buffer;       /* place holder for static or dynamic buffer */
    word32 length;       /* total buffer length used */
    word32 idx;          /* idx to part of length already consumed */
    word32 bufferSize;   /* current buffer size */
    byte   dynamicFlag;  /* dynamic memory currently in use */
    byte   offset;       /* alignment offset attempt */
} bufferStatic;

/* Cipher Suites holder */
struct Suites {
    word16 suiteSz;                 /* suite length in bytes        */
    word16 hashSigAlgoSz;           /* SigAlgo extension length in bytes */
    byte   suites[WOLFSSL_MAX_SUITE_SZ];
    byte   hashSigAlgo[WOLFSSL_MAX_SIGALGO]; /* sig/algo to offer */
    byte   setSuites;               /* user set suites from default */
    byte   hashAlgo;                /* selected hash algorithm */
    byte   sigAlgo;                 /* selected sig algorithm */
#if defined(OPENSSL_ALL) || defined(WOLFSSL_NGINX) || defined(WOLFSSL_HAPROXY)
    WOLF_STACK_OF(WOLFSSL_CIPHER)* stack; /* stack of available cipher suites */
#endif
};


WOLFSSL_LOCAL void InitSuitesHashSigAlgo(Suites* suites, int haveECDSAsig,
                                         int haveRSAsig, int haveAnon,
                                         int tls1_2, int keySz);
WOLFSSL_LOCAL void InitSuites(Suites*, ProtocolVersion, int, word16, word16,
                              word16, word16, word16, word16, word16, int);
WOLFSSL_LOCAL int  MatchSuite(WOLFSSL* ssl, Suites* peerSuites);
WOLFSSL_LOCAL int  SetCipherList(WOLFSSL_CTX*, Suites*, const char* list);

#ifndef PSK_TYPES_DEFINED
    typedef unsigned int (*wc_psk_client_callback)(WOLFSSL*, const char*, char*,
                          unsigned int, unsigned char*, unsigned int);
    typedef unsigned int (*wc_psk_server_callback)(WOLFSSL*, const char*,
                          unsigned char*, unsigned int);
#ifdef WOLFSSL_TLS13
    typedef unsigned int (*wc_psk_client_tls13_callback)(WOLFSSL*, const char*,
                          char*, unsigned int, unsigned char*, unsigned int,
                          const char**);
    typedef unsigned int (*wc_psk_server_tls13_callback)(WOLFSSL*, const char*,
                          unsigned char*, unsigned int, const char**);
#endif
#endif /* PSK_TYPES_DEFINED */
#if defined(WOLFSSL_DTLS) && defined(WOLFSSL_SESSION_EXPORT) && \
   !defined(WOLFSSL_DTLS_EXPORT_TYPES)
    typedef int (*wc_dtls_export)(WOLFSSL* ssl,
                   unsigned char* exportBuffer, unsigned int sz, void* userCtx);
#define WOLFSSL_DTLS_EXPORT_TYPES
#endif /* WOLFSSL_DTLS_EXPORT_TYPES */


#if defined(OPENSSL_ALL) || defined(WOLFSSL_QT)
#define MAX_DESCRIPTION_SZ 255
#endif
struct WOLFSSL_CIPHER {
    byte cipherSuite0;
    byte cipherSuite;
    const WOLFSSL* ssl;
#if defined(OPENSSL_ALL) || defined(WOLFSSL_QT)
    char description[MAX_DESCRIPTION_SZ];
    unsigned long offset;
    unsigned int in_stack; /* TRUE if added to stack in wolfSSL_get_ciphers_compat */
    int bits;
#endif
};


#ifdef NO_ASN
    /* no_asn won't have */
    typedef struct CertStatus CertStatus;
#endif

#ifndef HAVE_OCSP
    typedef struct WOLFSSL_OCSP WOLFSSL_OCSP;
#endif

/* wolfSSL OCSP controller */
#ifdef HAVE_OCSP
struct WOLFSSL_OCSP {
    WOLFSSL_CERT_MANAGER* cm;            /* pointer back to cert manager */
    OcspEntry*            ocspList;      /* OCSP response list */
    wolfSSL_Mutex         ocspLock;      /* OCSP list lock */
    int                   error;
#if defined(OPENSSL_ALL) || defined(OPENSSL_EXTRA) || \
    defined(WOLFSSL_NGINX) || defined(WOLFSSL_HAPROXY)
    int(*statusCb)(WOLFSSL*, void*);
#endif
};
#endif

#ifndef MAX_DATE_SIZE
#define MAX_DATE_SIZE 32
#endif

typedef struct CRL_Entry CRL_Entry;

#ifdef NO_SHA
    #define CRL_DIGEST_SIZE WC_SHA256_DIGEST_SIZE
#else
    #define CRL_DIGEST_SIZE WC_SHA_DIGEST_SIZE
#endif

#ifdef NO_ASN
    typedef struct RevokedCert RevokedCert;
#endif

/* Complete CRL */
struct CRL_Entry {
    CRL_Entry* next;                      /* next entry */
    byte    issuerHash[CRL_DIGEST_SIZE];  /* issuer hash                 */
    /* byte    crlHash[CRL_DIGEST_SIZE];      raw crl data hash           */
    /* restore the hash here if needed for optimized comparisons */
    byte    lastDate[MAX_DATE_SIZE]; /* last date updated  */
    byte    nextDate[MAX_DATE_SIZE]; /* next update date   */
    byte    lastDateFormat;          /* last date format */
    byte    nextDateFormat;          /* next date format */
    RevokedCert* certs;              /* revoked cert list  */
    int          totalCerts;         /* number on list     */
    int     verified;
    byte*   toBeSigned;
    word32  tbsSz;
    byte*   signature;
    word32  signatureSz;
    word32  signatureOID;
#if !defined(NO_SKID) && !defined(NO_ASN)
    byte    extAuthKeyIdSet;
    byte    extAuthKeyId[KEYID_SIZE];
#endif
};


typedef struct CRL_Monitor CRL_Monitor;

/* CRL directory monitor */
struct CRL_Monitor {
    char* path;      /* full dir path, if valid pointer we're using */
    int   type;      /* PEM or ASN1 type */
};


#if defined(HAVE_CRL) && defined(NO_FILESYSTEM)
    #undef HAVE_CRL_MONITOR
#endif

/* wolfSSL CRL controller */
struct WOLFSSL_CRL {
    WOLFSSL_CERT_MANAGER* cm;            /* pointer back to cert manager */
    CRL_Entry*            crlList;       /* our CRL list */
#ifdef HAVE_CRL_IO
    CbCrlIO               crlIOCb;
#endif
    wolfSSL_Mutex         crlLock;       /* CRL list lock */
    CRL_Monitor           monitors[2];   /* PEM and DER possible */
#ifdef HAVE_CRL_MONITOR
    pthread_cond_t        cond;          /* condition to signal setup */
    pthread_t             tid;           /* monitoring thread */
    int                   mfd;           /* monitor fd, -1 if no init yet */
    int                   setup;         /* thread is setup predicate */
#endif
    void*                 heap;          /* heap hint for dynamic memory */
};


#ifdef NO_ASN
    typedef struct Signer Signer;
#ifdef WOLFSSL_TRUST_PEER_CERT
    typedef struct TrustedPeerCert TrustedPeerCert;
#endif
#endif


#ifndef CA_TABLE_SIZE
    #define CA_TABLE_SIZE 11
#endif
#ifdef WOLFSSL_TRUST_PEER_CERT
    #define TP_TABLE_SIZE 11
#endif

/* wolfSSL Certificate Manager */
struct WOLFSSL_CERT_MANAGER {
    Signer*         caTable[CA_TABLE_SIZE]; /* the CA signer table */
    void*           heap;                /* heap helper */
#ifdef WOLFSSL_TRUST_PEER_CERT
    TrustedPeerCert* tpTable[TP_TABLE_SIZE]; /* table of trusted peer certs */
    wolfSSL_Mutex   tpLock;                  /* trusted peer list lock */
#endif
    WOLFSSL_CRL*    crl;                 /* CRL checker */
    WOLFSSL_OCSP*   ocsp;                /* OCSP checker */
#if !defined(NO_WOLFSSL_SERVER) && (defined(HAVE_CERTIFICATE_STATUS_REQUEST) \
                               ||  defined(HAVE_CERTIFICATE_STATUS_REQUEST_V2))
    WOLFSSL_OCSP*   ocsp_stapling;       /* OCSP checker for OCSP stapling */
#endif
    char*           ocspOverrideURL;     /* use this responder */
    void*           ocspIOCtx;           /* I/O callback CTX */
#ifndef NO_WOLFSSL_CM_VERIFY
    VerifyCallback  verifyCallback;      /* Verify callback */
#endif
    CallbackCACache caCacheCallback;     /* CA cache addition callback */
    CbMissingCRL    cbMissingCRL;        /* notify through cb of missing crl */
    CbOCSPIO        ocspIOCb;            /* I/O callback for OCSP lookup */
    CbOCSPRespFree  ocspRespFreeCb;      /* Frees OCSP Response from IO Cb */
    wolfSSL_Mutex   caLock;              /* CA list lock */
    byte            crlEnabled;          /* is CRL on ? */
    byte            crlCheckAll;         /* always leaf, but all ? */
    byte            ocspEnabled;         /* is OCSP on ? */
    byte            ocspCheckAll;        /* always leaf, but all ? */
    byte            ocspSendNonce;       /* send the OCSP nonce ? */
    byte            ocspUseOverrideURL;  /* ignore cert's responder, override */
    byte            ocspStaplingEnabled; /* is OCSP Stapling on ? */

#ifndef NO_RSA
    short           minRsaKeySz;         /* minimum allowed RSA key size */
#endif
#if defined(HAVE_ECC) || defined(HAVE_ED25519) || defined(HAVE_ED448)
    short           minEccKeySz;         /* minimum allowed ECC key size */
#endif
};

WOLFSSL_LOCAL int CM_SaveCertCache(WOLFSSL_CERT_MANAGER*, const char*);
WOLFSSL_LOCAL int CM_RestoreCertCache(WOLFSSL_CERT_MANAGER*, const char*);
WOLFSSL_LOCAL int CM_MemSaveCertCache(WOLFSSL_CERT_MANAGER*, void*, int, int*);
WOLFSSL_LOCAL int CM_MemRestoreCertCache(WOLFSSL_CERT_MANAGER*, const void*, int);
WOLFSSL_LOCAL int CM_GetCertCacheMemSize(WOLFSSL_CERT_MANAGER*);
WOLFSSL_LOCAL int CM_VerifyBuffer_ex(WOLFSSL_CERT_MANAGER* cm, const byte* buff,
                                    long sz, int format, int err_val);


#ifndef NO_CERTS
#if !defined NOCERTS &&\
    (!defined(NO_WOLFSSL_CLIENT) || !defined(WOLFSSL_NO_CLIENT_AUTH))
typedef struct ProcPeerCertArgs {
    buffer*      certs;
#ifdef WOLFSSL_TLS13
    buffer*      exts; /* extensions */
#endif
    DecodedCert* dCert;
    word32 idx;
    word32 begin;
    int    totalCerts; /* number of certs in certs buffer */
    int    count;
    int    certIdx;
    int    lastErr;
#ifdef WOLFSSL_TLS13
    byte   ctxSz;
#endif
#if defined(OPENSSL_EXTRA) || defined(OPENSSL_EXTRA_X509_SMALL)
    char   untrustedDepth;
#endif
    word16 fatal:1;
    word16 verifyErr:1;
    word16 dCertInit:1;
#ifdef WOLFSSL_TRUST_PEER_CERT
    word16 haveTrustPeer:1; /* was cert verified by loaded trusted peer cert */
#endif
} ProcPeerCertArgs;
WOLFSSL_LOCAL int DoVerifyCallback(WOLFSSL_CERT_MANAGER* cm, WOLFSSL* ssl,
        int ret, ProcPeerCertArgs* args);
#endif /* !defined(NO_WOLFSSL_CLIENT) || !defined(WOLFSSL_NO_CLIENT_AUTH) */
#endif /* !defined NO_CERTS */

/* wolfSSL Sock Addr */
struct WOLFSSL_SOCKADDR {
    unsigned int sz; /* sockaddr size */
    void*        sa; /* pointer to the sockaddr_in or sockaddr_in6 */
};

typedef struct WOLFSSL_DTLS_CTX {
    WOLFSSL_SOCKADDR peer;
    int rfd;
    int wfd;
} WOLFSSL_DTLS_CTX;


typedef struct WOLFSSL_DTLS_PEERSEQ {
    word32 window[WOLFSSL_DTLS_WINDOW_WORDS];
                        /* Sliding window for current epoch    */
    word16 nextEpoch;   /* Expected epoch in next record       */
    word16 nextSeq_hi;  /* Expected sequence in next record    */
    word32 nextSeq_lo;

    word32 prevWindow[WOLFSSL_DTLS_WINDOW_WORDS];
                        /* Sliding window for old epoch        */
    word32 prevSeq_lo;
    word16 prevSeq_hi;  /* Next sequence in allowed old epoch  */

#ifdef WOLFSSL_MULTICAST
    word16 peerId;
    word32 highwaterMark;
#endif
} WOLFSSL_DTLS_PEERSEQ;


#define MAX_WRITE_IV_SZ 16 /* max size of client/server write_IV */

/* keys and secrets
 * keep as a constant size (no additional ifdefs) for session export */
typedef struct Keys {
#if !defined(WOLFSSL_AEAD_ONLY) || defined(WOLFSSL_TLS13)
    byte client_write_MAC_secret[WC_MAX_DIGEST_SIZE];   /* max sizes */
    byte server_write_MAC_secret[WC_MAX_DIGEST_SIZE];
#endif
    byte client_write_key[MAX_SYM_KEY_SIZE];         /* max sizes */
    byte server_write_key[MAX_SYM_KEY_SIZE];
    byte client_write_IV[MAX_WRITE_IV_SZ];               /* max sizes */
    byte server_write_IV[MAX_WRITE_IV_SZ];
#if defined(HAVE_AEAD) || defined(WOLFSSL_SESSION_EXPORT)
    byte aead_exp_IV[AEAD_MAX_EXP_SZ];
    byte aead_enc_imp_IV[AEAD_MAX_IMP_SZ];
    byte aead_dec_imp_IV[AEAD_MAX_IMP_SZ];
#endif

    word32 peer_sequence_number_hi;
    word32 peer_sequence_number_lo;
    word32 sequence_number_hi;
    word32 sequence_number_lo;

#ifdef WOLFSSL_DTLS
    word16 curEpoch;    /* Received epoch in current record    */
    word16 curSeq_hi;   /* Received sequence in current record */
    word32 curSeq_lo;
#ifdef WOLFSSL_MULTICAST
    byte   curPeerId;   /* Received peer group ID in current record */
#endif
    WOLFSSL_DTLS_PEERSEQ peerSeq[WOLFSSL_DTLS_PEERSEQ_SZ];

    word16 dtls_peer_handshake_number;
    word16 dtls_expected_peer_handshake_number;

    word16 dtls_epoch;                          /* Current epoch    */
    word16 dtls_sequence_number_hi;             /* Current epoch */
    word32 dtls_sequence_number_lo;
    word16 dtls_prev_sequence_number_hi;        /* Previous epoch */
    word32 dtls_prev_sequence_number_lo;
    word16 dtls_handshake_number;               /* Current tx handshake seq */
#endif

    word32 encryptSz;             /* last size of encrypted data   */
    word32 padSz;                 /* how much to advance after decrypt part */
    byte   encryptionOn;          /* true after change cipher spec */
    byte   decryptedCur;          /* only decrypt current record once */
#ifdef WOLFSSL_TLS13
    byte   updateResponseReq:1;   /* KeyUpdate response from peer required. */
    byte   keyUpdateRespond:1;    /* KeyUpdate is to be responded to. */
#endif
#ifdef WOLFSSL_RENESAS_TSIP_TLS

    tsip_hmac_sha_key_index_t tsip_client_write_MAC_secret;
    tsip_hmac_sha_key_index_t tsip_server_write_MAC_secret;

#endif
} Keys;



/** TLS Extensions - RFC 6066 */
#ifdef HAVE_TLS_EXTENSIONS

typedef enum {
    TLSX_SERVER_NAME                = 0x0000, /* a.k.a. SNI  */
    TLSX_MAX_FRAGMENT_LENGTH        = 0x0001,
    TLSX_TRUSTED_CA_KEYS            = 0x0003,
    TLSX_TRUNCATED_HMAC             = 0x0004,
    TLSX_STATUS_REQUEST             = 0x0005, /* a.k.a. OCSP stapling   */
    TLSX_SUPPORTED_GROUPS           = 0x000a, /* a.k.a. Supported Curves */
    TLSX_EC_POINT_FORMATS           = 0x000b,
#if !defined(WOLFSSL_NO_SIGALG)
    TLSX_SIGNATURE_ALGORITHMS       = 0x000d, /* HELLO_EXT_SIG_ALGO */
#endif
    TLSX_APPLICATION_LAYER_PROTOCOL = 0x0010, /* a.k.a. ALPN */
    TLSX_STATUS_REQUEST_V2          = 0x0011, /* a.k.a. OCSP stapling v2 */
#if defined(HAVE_ENCRYPT_THEN_MAC) && !defined(WOLFSSL_AEAD_ONLY)
    TLSX_ENCRYPT_THEN_MAC           = 0x0016, /* RFC 7366 */
#endif
    TLSX_EXTENDED_MASTER_SECRET     = 0x0017, /* HELLO_EXT_EXTMS */
    TLSX_QUANTUM_SAFE_HYBRID        = 0x0018, /* a.k.a. QSH  */
    TLSX_SESSION_TICKET             = 0x0023,
#ifdef WOLFSSL_TLS13
    #if defined(HAVE_SESSION_TICKET) || !defined(NO_PSK)
    TLSX_PRE_SHARED_KEY             = 0x0029,
    #endif
    #ifdef WOLFSSL_EARLY_DATA
    TLSX_EARLY_DATA                 = 0x002a,
    #endif
    TLSX_SUPPORTED_VERSIONS         = 0x002b,
    TLSX_COOKIE                     = 0x002c,
    #if defined(HAVE_SESSION_TICKET) || !defined(NO_PSK)
    TLSX_PSK_KEY_EXCHANGE_MODES     = 0x002d,
    #endif
    #ifdef WOLFSSL_POST_HANDSHAKE_AUTH
    TLSX_POST_HANDSHAKE_AUTH        = 0x0031,
    #endif
    TLSX_SIGNATURE_ALGORITHMS_CERT  = 0x0032,
    TLSX_KEY_SHARE                  = 0x0033,
#endif
    TLSX_RENEGOTIATION_INFO         = 0xff01
} TLSX_Type;

typedef struct TLSX {
    TLSX_Type    type; /* Extension Type  */
    void*        data; /* Extension Data  */
    word32       val;  /* Extension Value */
    byte         resp; /* IsResponse Flag */
    struct TLSX* next; /* List Behavior   */
} TLSX;

WOLFSSL_LOCAL TLSX* TLSX_Find(TLSX* list, TLSX_Type type);
WOLFSSL_LOCAL void  TLSX_Remove(TLSX** list, TLSX_Type type, void* heap);
WOLFSSL_LOCAL void  TLSX_FreeAll(TLSX* list, void* heap);
WOLFSSL_LOCAL int   TLSX_SupportExtensions(WOLFSSL* ssl);
WOLFSSL_LOCAL int   TLSX_PopulateExtensions(WOLFSSL* ssl, byte isRequest);

#if defined(WOLFSSL_TLS13) || !defined(NO_WOLFSSL_CLIENT)
WOLFSSL_LOCAL int   TLSX_GetRequestSize(WOLFSSL* ssl, byte msgType,
                                         word16* pLength);
WOLFSSL_LOCAL int   TLSX_WriteRequest(WOLFSSL* ssl, byte* output,
                                       byte msgType, word16* pOffset);
#endif

#if defined(WOLFSSL_TLS13) || !defined(NO_WOLFSSL_SERVER)
/* TLS 1.3 Certificate messages have extensions. */
WOLFSSL_LOCAL int   TLSX_GetResponseSize(WOLFSSL* ssl, byte msgType,
                                          word16* pLength);
WOLFSSL_LOCAL int   TLSX_WriteResponse(WOLFSSL *ssl, byte* output, byte msgType,
                                        word16* pOffset);
#endif

WOLFSSL_LOCAL int   TLSX_ParseVersion(WOLFSSL* ssl, byte* input, word16 length,
                                      byte msgType, int* found);
WOLFSSL_LOCAL int   TLSX_Parse(WOLFSSL* ssl, byte* input, word16 length,
                               byte msgType, Suites *suites);

#elif defined(HAVE_SNI)                           \
   || defined(HAVE_MAX_FRAGMENT)                  \
   || defined(HAVE_TRUSTED_CA)                    \
   || defined(HAVE_TRUNCATED_HMAC)                \
   || defined(HAVE_CERTIFICATE_STATUS_REQUEST)    \
   || defined(HAVE_CERTIFICATE_STATUS_REQUEST_V2) \
   || defined(HAVE_SUPPORTED_CURVES)              \
   || defined(HAVE_ALPN)                          \
   || defined(HAVE_QSH)                           \
   || defined(HAVE_SESSION_TICKET)                \
   || defined(HAVE_SECURE_RENEGOTIATION)          \
   || defined(HAVE_SERVER_RENEGOTIATION_INFO)

#error Using TLS extensions requires HAVE_TLS_EXTENSIONS to be defined.

#endif /* HAVE_TLS_EXTENSIONS */

/** Server Name Indication - RFC 6066 (session 3) */
#ifdef HAVE_SNI

typedef struct SNI {
    byte                       type;    /* SNI Type         */
    union { char* host_name; } data;    /* SNI Data         */
    struct SNI*                next;    /* List Behavior    */
    byte                       status;  /* Matching result  */
#ifndef NO_WOLFSSL_SERVER
    byte                       options; /* Behavior options */
#endif
} SNI;

WOLFSSL_LOCAL int TLSX_UseSNI(TLSX** extensions, byte type, const void* data,
                                                       word16 size, void* heap);
WOLFSSL_LOCAL byte TLSX_SNI_Status(TLSX* extensions, byte type);
WOLFSSL_LOCAL word16 TLSX_SNI_GetRequest(TLSX* extensions, byte type,
                                                                   void** data);

#ifndef NO_WOLFSSL_SERVER
WOLFSSL_LOCAL void   TLSX_SNI_SetOptions(TLSX* extensions, byte type,
                                                                  byte options);
WOLFSSL_LOCAL int    TLSX_SNI_GetFromBuffer(const byte* buffer, word32 bufferSz,
                                         byte type, byte* sni, word32* inOutSz);
#endif

#endif /* HAVE_SNI */

/* Trusted CA Key Indication - RFC 6066 (section 6) */
#ifdef HAVE_TRUSTED_CA

typedef struct TCA {
    byte                       type;    /* TCA Type            */
    byte*                      id;      /* TCA identifier      */
    word16                     idSz;    /* TCA identifier size */
    struct TCA*                next;    /* List Behavior       */
} TCA;

WOLFSSL_LOCAL int TLSX_UseTrustedCA(TLSX** extensions, byte type,
                    const byte* id, word16 idSz, void* heap);

#endif /* HAVE_TRUSTED_CA */

/* Application-Layer Protocol Negotiation - RFC 7301 */
#ifdef HAVE_ALPN
typedef struct ALPN {
    char*        protocol_name; /* ALPN protocol name */
    struct ALPN* next;          /* List Behavior      */
    byte         options;       /* Behavior options */
    byte         negotiated;    /* ALPN protocol negotiated or not */
} ALPN;

WOLFSSL_LOCAL int TLSX_ALPN_GetRequest(TLSX* extensions,
                                       void** data, word16 *dataSz);

WOLFSSL_LOCAL int TLSX_UseALPN(TLSX** extensions, const void* data,
                               word16 size, byte options, void* heap);

WOLFSSL_LOCAL int TLSX_ALPN_SetOptions(TLSX** extensions, const byte option);

#endif /* HAVE_ALPN */

/** Maximum Fragment Length Negotiation - RFC 6066 (session 4) */
#ifdef HAVE_MAX_FRAGMENT

WOLFSSL_LOCAL int TLSX_UseMaxFragment(TLSX** extensions, byte mfl, void* heap);

#endif /* HAVE_MAX_FRAGMENT */

/** Truncated HMAC - RFC 6066 (session 7) */
#ifdef HAVE_TRUNCATED_HMAC

WOLFSSL_LOCAL int TLSX_UseTruncatedHMAC(TLSX** extensions, void* heap);

#endif /* HAVE_TRUNCATED_HMAC */

/** Certificate Status Request - RFC 6066 (session 8) */
#ifdef HAVE_CERTIFICATE_STATUS_REQUEST

typedef struct {
    byte status_type;
    byte options;
    WOLFSSL* ssl;
    union {
        OcspRequest ocsp;
    } request;
#if defined(WOLFSSL_TLS13) && !defined(NO_WOLFSSL_SERVER)
    buffer response;
#endif
} CertificateStatusRequest;

WOLFSSL_LOCAL int   TLSX_UseCertificateStatusRequest(TLSX** extensions,
           byte status_type, byte options, WOLFSSL* ssl, void* heap, int devId);
#ifndef NO_CERTS
WOLFSSL_LOCAL int   TLSX_CSR_InitRequest(TLSX* extensions, DecodedCert* cert,
                                                                    void* heap);
#endif
WOLFSSL_LOCAL void* TLSX_CSR_GetRequest(TLSX* extensions);
WOLFSSL_LOCAL int   TLSX_CSR_ForceRequest(WOLFSSL* ssl);

#endif

/** Certificate Status Request v2 - RFC 6961 */
#ifdef HAVE_CERTIFICATE_STATUS_REQUEST_V2

typedef struct CSRIv2 {
    byte status_type;
    byte options;
    word16 requests;
    union {
        OcspRequest ocsp[1 + MAX_CHAIN_DEPTH];
    } request;
    struct CSRIv2* next;
} CertificateStatusRequestItemV2;

WOLFSSL_LOCAL int   TLSX_UseCertificateStatusRequestV2(TLSX** extensions,
                         byte status_type, byte options, void* heap, int devId);
#ifndef NO_CERTS
WOLFSSL_LOCAL int   TLSX_CSR2_InitRequests(TLSX* extensions, DecodedCert* cert,
                                                       byte isPeer, void* heap);
#endif
WOLFSSL_LOCAL void* TLSX_CSR2_GetRequest(TLSX* extensions, byte status_type,
                                                                    byte index);
WOLFSSL_LOCAL int   TLSX_CSR2_ForceRequest(WOLFSSL* ssl);

#endif

/** Supported Elliptic Curves - RFC 4492 (session 4) */
#ifdef HAVE_SUPPORTED_CURVES

typedef struct SupportedCurve {
    word16 name;                 /* Curve Names */
    struct SupportedCurve* next; /* List Behavior */
} SupportedCurve;

typedef struct PointFormat {
    byte format;                /* PointFormat */
    struct PointFormat* next;   /* List Behavior */
} PointFormat;

WOLFSSL_LOCAL int TLSX_UseSupportedCurve(TLSX** extensions, word16 name,
                                                                    void* heap);

WOLFSSL_LOCAL int TLSX_UsePointFormat(TLSX** extensions, byte point,
                                                                    void* heap);

#ifndef NO_WOLFSSL_SERVER
WOLFSSL_LOCAL int TLSX_ValidateSupportedCurves(WOLFSSL* ssl, byte first,
                                                                   byte second);
WOLFSSL_LOCAL int TLSX_SupportedCurve_CheckPriority(WOLFSSL* ssl);
WOLFSSL_LOCAL int TLSX_SupportedFFDHE_Set(WOLFSSL* ssl);
#endif
WOLFSSL_LOCAL int TLSX_SupportedCurve_Preferred(WOLFSSL* ssl,
                                                            int checkSupported);

#endif /* HAVE_SUPPORTED_CURVES */

/** Renegotiation Indication - RFC 5746 */
#if defined(HAVE_SECURE_RENEGOTIATION) \
 || defined(HAVE_SERVER_RENEGOTIATION_INFO)

enum key_cache_state {
    SCR_CACHE_NULL   = 0,       /* empty / begin state */
    SCR_CACHE_NEEDED,           /* need to cache keys */
    SCR_CACHE_COPY,             /* we have a cached copy */
    SCR_CACHE_PARTIAL,          /* partial restore to real keys */
    SCR_CACHE_COMPLETE          /* complete restore to real keys */
};

/* Additional Connection State according to rfc5746 section 3.1 */
typedef struct SecureRenegotiation {
   byte                 enabled;  /* secure_renegotiation flag in rfc */
   byte                 verifySet;
   byte                 startScr; /* server requested client to start scr */
   enum key_cache_state cache_status;  /* track key cache state */
   byte                 client_verify_data[TLS_FINISHED_SZ];  /* cached */
   byte                 server_verify_data[TLS_FINISHED_SZ];  /* cached */
   byte                 subject_hash_set; /* if peer cert hash is set */
   byte                 subject_hash[KEYID_SIZE];  /* peer cert hash */
   Keys                 tmp_keys;  /* can't overwrite real keys yet */
} SecureRenegotiation;

WOLFSSL_LOCAL int TLSX_UseSecureRenegotiation(TLSX** extensions, void* heap);

#ifdef HAVE_SERVER_RENEGOTIATION_INFO
WOLFSSL_LOCAL int TLSX_AddEmptyRenegotiationInfo(TLSX** extensions, void* heap);
#endif

#endif /* HAVE_SECURE_RENEGOTIATION */

/** Session Ticket - RFC 5077 (session 3.2) */
#ifdef HAVE_SESSION_TICKET

typedef struct SessionTicket {
    word32 lifetime;
#ifdef WOLFSSL_TLS13
    word64 seen;
    word32 ageAdd;
#endif
    byte*  data;
    word16 size;
} SessionTicket;

WOLFSSL_LOCAL int  TLSX_UseSessionTicket(TLSX** extensions,
                                             SessionTicket* ticket, void* heap);
WOLFSSL_LOCAL SessionTicket* TLSX_SessionTicket_Create(word32 lifetime,
                                           byte* data, word16 size, void* heap);
WOLFSSL_LOCAL void TLSX_SessionTicket_Free(SessionTicket* ticket, void* heap);

#endif /* HAVE_SESSION_TICKET */

/** Quantum-Safe-Hybrid - draft-whyte-qsh-tls12-00 */
#ifdef HAVE_QSH

typedef struct QSHScheme {
    struct QSHScheme* next; /* List Behavior   */
    byte*             PK;
    word16            name; /* QSHScheme Names */
    word16            PKLen;
} QSHScheme;

typedef struct QSHkey {
    struct QSHKey* next;
    word16 name;
    buffer pub;
    buffer pri;
} QSHKey;

typedef struct QSHSecret {
    QSHScheme* list;
    buffer* SerSi;
    buffer* CliSi;
} QSHSecret;

/* used in key exchange during handshake */
WOLFSSL_LOCAL int TLSX_QSHCipher_Parse(WOLFSSL* ssl, const byte* input,
                                                  word16 length, byte isServer);
WOLFSSL_LOCAL word16 TLSX_QSHPK_Write(QSHScheme* list, byte* output);
WOLFSSL_LOCAL word16 TLSX_QSH_GetSize(QSHScheme* list, byte isRequest);

/* used by api for setting a specific QSH scheme */
WOLFSSL_LOCAL int TLSX_UseQSHScheme(TLSX** extensions, word16 name,
                                         byte* pKey, word16 pKeySz, void* heap);

/* used when parsing in QSHCipher structs */
WOLFSSL_LOCAL int QSH_Decrypt(QSHKey* key, byte* in, word32 szIn,
                                                      byte* out, word16* szOut);
#ifndef NO_WOLFSSL_SERVER
WOLFSSL_LOCAL int TLSX_ValidateQSHScheme(TLSX** extensions, word16 name);
#endif

#endif /* HAVE_QSH */

#ifdef WOLFSSL_TLS13
/* Cookie extension information - cookie data. */
typedef struct Cookie {
    word16 len;
    byte   data;
} Cookie;

WOLFSSL_LOCAL int TLSX_Cookie_Use(WOLFSSL* ssl, byte* data, word16 len,
                                  byte* mac, byte macSz, int resp);


/* Key Share - TLS v1.3 Specification */

/* The KeyShare extension information - entry in a linked list. */
typedef struct KeyShareEntry {
    word16                group;     /* NamedGroup               */
    byte*                 ke;        /* Key exchange data        */
    word32                keLen;     /* Key exchange data length */
    void*                 key;       /* Private key              */
    word32                keyLen;    /* Private key length       */
    byte*                 pubKey;    /* Public key               */
    word32                pubKeyLen; /* Public key length        */
    struct KeyShareEntry* next;      /* List pointer             */
} KeyShareEntry;

WOLFSSL_LOCAL int TLSX_KeyShare_Use(WOLFSSL* ssl, word16 group, word16 len,
                                    byte* data, KeyShareEntry **kse);
WOLFSSL_LOCAL int TLSX_KeyShare_Empty(WOLFSSL* ssl);
WOLFSSL_LOCAL int TLSX_KeyShare_Establish(WOLFSSL* ssl);
WOLFSSL_LOCAL int TLSX_KeyShare_DeriveSecret(WOLFSSL* ssl);


#if defined(HAVE_SESSION_TICKET) || !defined(NO_PSK)
/* Ticket nonce - for deriving PSK.
 * Length allowed to be: 1..255. Only support 4 bytes.
 */
typedef struct TicketNonce {
    byte len;
    byte data[MAX_TICKET_NONCE_SZ];
} TicketNonce;

/* The PreSharedKey extension information - entry in a linked list. */
typedef struct PreSharedKey {
    word16               identityLen;             /* Length of identity */
    byte*                identity;                /* PSK identity       */
    word32               ticketAge;               /* Age of the ticket  */
    byte                 cipherSuite0;            /* Cipher Suite       */
    byte                 cipherSuite;             /* Cipher Suite       */
    word32               binderLen;               /* Length of HMAC     */
    byte                 binder[WC_MAX_DIGEST_SIZE]; /* HMAC of handshake */
    byte                 hmac;                    /* HMAC algorithm     */
    byte                 resumption:1;            /* Resumption PSK     */
    byte                 chosen:1;                /* Server's choice    */
    struct PreSharedKey* next;                    /* List pointer       */
} PreSharedKey;

WOLFSSL_LOCAL int TLSX_PreSharedKey_WriteBinders(PreSharedKey* list,
                                                 byte* output, byte msgType,
                                                 word16* pSz);
WOLFSSL_LOCAL int TLSX_PreSharedKey_GetSizeBinders(PreSharedKey* list,
                                                   byte msgType, word16* pSz);
WOLFSSL_LOCAL int TLSX_PreSharedKey_Use(WOLFSSL* ssl, byte* identity,
                                        word16 len, word32 age, byte hmac,
                                        byte cipherSuite0, byte cipherSuite,
                                        byte resumption,
                                        PreSharedKey **preSharedKey);

/* The possible Pre-Shared Key key exchange modes. */
enum PskKeyExchangeMode {
    PSK_KE,
    PSK_DHE_KE
};

/* User can define this. */
#ifndef WOLFSSL_DEF_PSK_CIPHER
#define WOLFSSL_DEF_PSK_CIPHER    TLS_AES_128_GCM_SHA256
#endif

WOLFSSL_LOCAL int TLSX_PskKeModes_Use(WOLFSSL* ssl, byte modes);

#ifdef WOLFSSL_EARLY_DATA
WOLFSSL_LOCAL int TLSX_EarlyData_Use(WOLFSSL* ssl, word32 max);
#endif
#endif /* HAVE_SESSION_TICKET || !NO_PSK */


/* The types of keys to derive for. */
enum DeriveKeyType {
    no_key,
    early_data_key,
    handshake_key,
    traffic_key,
    update_traffic_key
};

WOLFSSL_LOCAL int DeriveEarlySecret(WOLFSSL* ssl);
WOLFSSL_LOCAL int DeriveHandshakeSecret(WOLFSSL* ssl);
WOLFSSL_LOCAL int DeriveTls13Keys(WOLFSSL* ssl, int secret, int side, int store);
WOLFSSL_LOCAL int DeriveMasterSecret(WOLFSSL* ssl);
WOLFSSL_LOCAL int DeriveResumptionPSK(WOLFSSL* ssl, byte* nonce, byte nonceLen, byte* secret);
WOLFSSL_LOCAL int DeriveResumptionSecret(WOLFSSL* ssl, byte* key);

/* The key update request values for KeyUpdate message. */
enum KeyUpdateRequest {
    update_not_requested,
    update_requested
};
#endif /* WOLFSSL_TLS13 */


#ifdef OPENSSL_EXTRA
enum SetCBIO {
    WOLFSSL_CBIO_NONE = 0,
    WOLFSSL_CBIO_RECV = 0x1,
    WOLFSSL_CBIO_SEND = 0x2,
};
#endif

#ifdef WOLFSSL_STATIC_EPHEMERAL
typedef struct {
    int keyAlgo;
    DerBuffer* key;
} StaticKeyExchangeInfo_t;
#endif


/* wolfSSL context type */
struct WOLFSSL_CTX {
    WOLFSSL_METHOD* method;
#ifdef SINGLE_THREADED
    WC_RNG*         rng;          /* to be shared with WOLFSSL w/o locking */
#endif
    wolfSSL_Mutex   countMutex;   /* reference count mutex */
    int         refCount;         /* reference count */
    int         err;              /* error code in case of mutex not created */
#ifndef NO_DH
    buffer      serverDH_P;
    buffer      serverDH_G;
#endif
#ifndef NO_CERTS
    DerBuffer*  certificate;
    DerBuffer*  certChain;
                 /* chain after self, in DER, with leading size for each cert */
    #if defined(OPENSSL_EXTRA) || defined(WOLFSSL_EXTRA)
    WOLF_STACK_OF(WOLFSSL_X509_NAME)* ca_names;
    #endif
    #if defined(OPENSSL_ALL) || defined(OPENSSL_EXTRA) || \
        defined(WOLFSSL_NGINX) || defined (WOLFSSL_HAPROXY)
    WOLF_STACK_OF(WOLFSSL_X509)* x509Chain;
    client_cert_cb CBClientCert;  /* client certificate callback */
    #endif
#ifdef WOLFSSL_TLS13
    int         certChainCnt;
#endif
    DerBuffer*  privateKey;
    byte        privateKeyType:7;
    byte        privateKeyId:1;
    int         privateKeySz;
    int         privateKeyDevId;
    WOLFSSL_CERT_MANAGER* cm;      /* our cert manager, ctx owns SSL will use */
#endif
#ifdef KEEP_OUR_CERT
    WOLFSSL_X509*    ourCert;     /* keep alive a X509 struct of cert */
    int              ownOurCert;  /* Dispose of certificate if we own */
#endif
    Suites*     suites;           /* make dynamic, user may not need/set */
    void*       heap;             /* for user memory overrides */
    byte        verifyDepth;
    byte        verifyPeer:1;
    byte        verifyNone:1;
    byte        failNoCert:1;
    byte        failNoCertxPSK:1; /* fail if no cert with the exception of PSK*/
    byte        sessionCacheOff:1;
    byte        sessionCacheFlushOff:1;
#ifdef HAVE_EXT_CACHE
    byte        internalCacheOff:1;
#endif
    byte        sendVerify:2;     /* for client side (can not be single bit) */
    byte        haveRSA:1;        /* RSA available */
    byte        haveECC:1;        /* ECC available */
    byte        haveDH:1;         /* server DH parms set by user */
    byte        haveNTRU:1;       /* server private NTRU  key loaded */
    byte        haveECDSAsig:1;   /* server cert signed w/ ECDSA */
    byte        haveStaticECC:1;  /* static server ECC private key */
    byte        partialWrite:1;   /* only one msg per write call */
    byte        quietShutdown:1;  /* don't send close notify */
    byte        groupMessages:1;  /* group handshake messages before sending */
    byte        minDowngrade;     /* minimum downgrade version */
    byte        haveEMS:1;        /* have extended master secret extension */
    byte        useClientOrder:1; /* Use client's cipher preference order */
#ifdef WOLFSSL_TLS13
    byte        noTicketTls13:1;  /* Server won't create new Ticket */
    byte        noPskDheKe:1;     /* Don't use (EC)DHE with PSK */
#endif
    byte        mutualAuth:1;     /* Mutual authentication required */
#if defined(WOLFSSL_TLS13) && defined(WOLFSSL_POST_HANDSHAKE_AUTH)
    byte        postHandshakeAuth:1;  /* Post-handshake auth supported. */
#endif
#ifndef NO_DH
    #if !defined(WOLFSSL_OLD_PRIME_CHECK) && !defined(HAVE_FIPS) && \
        !defined(HAVE_SELFTEST)
    byte        dhKeyTested:1;   /* Set when key has been tested. */
    #endif
#endif
#ifdef HAVE_SECURE_RENEGOTIATION
    byte        useSecureReneg:1; /* when set will set WOLFSSL objects generated to enable */
#endif
#ifdef HAVE_ENCRYPT_THEN_MAC
    byte        disallowEncThenMac:1;  /* Don't do Encrypt-Then-MAC */
#endif
#ifdef WOLFSSL_STATIC_MEMORY
    byte        onHeap:1; /* whether the ctx/method is put on heap hint */
#endif
#ifdef WOLFSSL_MULTICAST
    byte        haveMcast;        /* multicast requested */
    byte        mcastID;          /* multicast group ID */
#endif
#if defined(WOLFSSL_SCTP) && defined(WOLFSSL_DTLS)
    byte        dtlsSctp;         /* DTLS-over-SCTP mode */
#endif
#if (defined(WOLFSSL_SCTP) || defined(WOLFSSL_DTLS_MTU)) && \
                                                           defined(WOLFSSL_DTLS)
    word16      dtlsMtuSz;        /* DTLS MTU size */
#endif
#ifndef NO_DH
    word16      minDhKeySz;       /* minimum DH key size */
    word16      maxDhKeySz;       /* maximum DH key size */
#endif
#ifndef NO_RSA
    short       minRsaKeySz;      /* minimum RSA key size */
#endif
#if defined(HAVE_ECC) || defined(HAVE_ED25519) || defined(HAVE_ED448)
    short       minEccKeySz;      /* minimum ECC key size */
#endif
    unsigned long     mask;             /* store SSL_OP_ flags */
#ifdef OPENSSL_EXTRA
    byte              sessionCtx[ID_LEN]; /* app session context ID */
    word32            disabledCurves;   /* curves disabled by user */
    const unsigned char *alpn_cli_protos;/* ALPN client protocol list */
    unsigned int         alpn_cli_protos_len;
    byte              sessionCtxSz;
    byte              cbioFlag;  /* WOLFSSL_CBIO_RECV/SEND: CBIORecv/Send is set */
    CallbackInfoState* CBIS;      /* used to get info about SSL state */
#endif
    CallbackIORecv CBIORecv;
    CallbackIOSend CBIOSend;
#ifdef WOLFSSL_DTLS
    CallbackGenCookie CBIOCookie;       /* gen cookie callback */
#ifdef WOLFSSL_SESSION_EXPORT
    wc_dtls_export  dtls_export;        /* export function for DTLS session */
    CallbackGetPeer CBGetPeer;
    CallbackSetPeer CBSetPeer;
#endif
#endif /* WOLFSSL_DTLS */
    VerifyCallback  verifyCallback;     /* cert verification callback */
#ifdef OPENSSL_ALL
    CertVerifyCallback verifyCertCb;
    void*              verifyCertCbArg;
#endif /* OPENSSL_ALL */
    word32          timeout;            /* session timeout */
#if defined(HAVE_ECC) || defined(HAVE_CURVE25519) || defined(HAVE_ED448)
    word32          ecdhCurveOID;       /* curve Ecc_Sum */
#endif
#ifdef HAVE_ECC
    word16          eccTempKeySz;       /* in octets 20 - 66 */
#endif
#if defined(HAVE_ECC) || defined(HAVE_ED25519) || defined(HAVE_ED448)
    word32          pkCurveOID;         /* curve Ecc_Sum */
#endif
#if defined(HAVE_SESSION_TICKET) || !defined(NO_PSK)
    byte        havePSK;                /* psk key set by user */
    wc_psk_client_callback client_psk_cb;  /* client callback */
    wc_psk_server_callback server_psk_cb;  /* server callback */
#ifdef WOLFSSL_TLS13
    wc_psk_client_tls13_callback client_psk_tls13_cb;  /* client callback */
    wc_psk_server_tls13_callback server_psk_tls13_cb;  /* server callback */
#endif
    void*       psk_ctx;
    char        server_hint[MAX_PSK_ID_LEN + NULL_TERM_LEN];
#endif /* HAVE_SESSION_TICKET || !NO_PSK */
#ifdef WOLFSSL_TLS13
    word16          group[WOLFSSL_MAX_GROUP_COUNT];
    byte            numGroups;
#endif
#ifdef WOLFSSL_EARLY_DATA
    word32          maxEarlyDataSz;
#endif
#ifdef HAVE_ANON
    byte        haveAnon;               /* User wants to allow Anon suites */
#endif /* HAVE_ANON */
#ifdef WOLFSSL_ENCRYPTED_KEYS
    pem_password_cb* passwd_cb;
    void*            passwd_userdata;
#endif
#if defined(OPENSSL_EXTRA) || defined(HAVE_WEBSERVER) || defined(WOLFSSL_WPAS_SMALL)
    WOLFSSL_X509_STORE x509_store; /* points to ctx->cm */
    WOLFSSL_X509_STORE* x509_store_pt; /* take ownership of external store */
    byte            readAhead;
    void*           userPRFArg; /* passed to prf callback */
#endif
#ifdef HAVE_EX_DATA
    WOLFSSL_CRYPTO_EX_DATA ex_data;
#endif
#if defined(HAVE_ALPN) && (defined(OPENSSL_ALL) || defined(WOLFSSL_NGINX) || defined(WOLFSSL_HAPROXY))
    CallbackALPNSelect alpnSelect;
    void*              alpnSelectArg;
#endif
#if defined(OPENSSL_ALL) || (defined(OPENSSL_EXTRA) && (defined(HAVE_STUNNEL) || \
                             defined(WOLFSSL_NGINX) || defined(HAVE_LIGHTY) || \
                             defined(WOLFSSL_HAPROXY) || defined(WOLFSSL_OPENSSH) ))
    CallbackSniRecv sniRecvCb;
    void*           sniRecvCbArg;
#endif
#if defined(WOLFSSL_MULTICAST) && defined(WOLFSSL_DTLS)
    CallbackMcastHighwater mcastHwCb; /* Sequence number highwater callback */
    word32      mcastFirstSeq;    /* first trigger level */
    word32      mcastSecondSeq;   /* second trigger level */
    word32      mcastMaxSeq;      /* max level */
#endif
#ifdef HAVE_OCSP
    WOLFSSL_OCSP      ocsp;
#endif
    int             devId;              /* async device id to use */
#ifdef HAVE_TLS_EXTENSIONS
    TLSX* extensions;                  /* RFC 6066 TLS Extensions data */
    #ifndef NO_WOLFSSL_SERVER
        #if defined(HAVE_CERTIFICATE_STATUS_REQUEST) \
         || defined(HAVE_CERTIFICATE_STATUS_REQUEST_V2)
            OcspRequest* certOcspRequest;
        #endif
        #if defined(HAVE_CERTIFICATE_STATUS_REQUEST_V2)
            OcspRequest* chainOcspRequest[MAX_CHAIN_DEPTH];
        #endif
    #endif
    #if defined(HAVE_SESSION_TICKET) && !defined(NO_WOLFSSL_SERVER)
        SessionTicketEncCb ticketEncCb;   /* enc/dec session ticket Cb */
        void*              ticketEncCtx;  /* session encrypt context */
        int                ticketHint;    /* ticket hint in seconds */
    #endif
    #ifdef HAVE_SUPPORTED_CURVES
        byte userCurves;                  /* indicates user called wolfSSL_CTX_UseSupportedCurve */
    #endif
#endif
#ifdef ATOMIC_USER
    CallbackMacEncrypt    MacEncryptCb;    /* Atomic User Mac/Encrypt Cb */
    CallbackDecryptVerify DecryptVerifyCb; /* Atomic User Decrypt/Verify Cb */
    #ifdef HAVE_ENCRYPT_THEN_MAC
        CallbackEncryptMac    EncryptMacCb;    /* Atomic User Mac/Enc Cb */
        CallbackVerifyDecrypt VerifyDecryptCb; /* Atomic User Dec/Verify Cb */
    #endif
#endif
#ifdef HAVE_PK_CALLBACKS
    #ifdef HAVE_ECC
        CallbackEccKeyGen EccKeyGenCb;  /* User EccKeyGen Callback Handler */
        CallbackEccSign   EccSignCb;    /* User EccSign   Callback handler */
        CallbackEccVerify EccVerifyCb;  /* User EccVerify Callback handler */
        CallbackEccSharedSecret EccSharedSecretCb; /* User EccVerify Callback handler */
        #ifdef HAVE_ED25519
            /* User Ed25519Sign   Callback handler */
            CallbackEd25519Sign   Ed25519SignCb;
            /* User Ed25519Verify Callback handler */
            CallbackEd25519Verify Ed25519VerifyCb;
        #endif
        #ifdef HAVE_CURVE25519
            /* User X25519 KeyGen Callback Handler */
            CallbackX25519KeyGen X25519KeyGenCb;
            /* User X25519 SharedSecret Callback handler */
            CallbackX25519SharedSecret X25519SharedSecretCb;
        #endif
        #ifdef HAVE_ED448
            /* User Ed448Sign   Callback handler */
            CallbackEd448Sign   Ed448SignCb;
            /* User Ed448Verify Callback handler */
            CallbackEd448Verify Ed448VerifyCb;
        #endif
        #ifdef HAVE_CURVE448
            /* User X448 KeyGen Callback Handler */
            CallbackX448KeyGen X448KeyGenCb;
            /* User X448 SharedSecret Callback handler */
            CallbackX448SharedSecret X448SharedSecretCb;
        #endif
    #endif /* HAVE_ECC */
    #ifndef NO_DH
        CallbackDhAgree DhAgreeCb;      /* User DH Agree Callback handler */
    #endif
    #ifndef NO_RSA
        CallbackRsaSign   RsaSignCb;      /* User RsaSign Callback handler (priv key) */
        CallbackRsaVerify RsaVerifyCb;    /* User RsaVerify Callback handler (pub key) */
        CallbackRsaVerify RsaSignCheckCb; /* User VerifyRsaSign Callback handler (priv key) */
        #ifdef WC_RSA_PSS
            CallbackRsaPssSign   RsaPssSignCb;       /* User RsaSign (priv key) */
            CallbackRsaPssVerify RsaPssVerifyCb;     /* User RsaVerify (pub key) */
            CallbackRsaPssVerify RsaPssSignCheckCb; /* User VerifyRsaSign (priv key) */
        #endif
        CallbackRsaEnc    RsaEncCb;     /* User Rsa Public Encrypt  handler */
        CallbackRsaDec    RsaDecCb;     /* User Rsa Private Decrypt handler */
    #endif /* NO_RSA */
#endif /* HAVE_PK_CALLBACKS */
#ifdef HAVE_WOLF_EVENT
    WOLF_EVENT_QUEUE event_queue;
#endif /* HAVE_WOLF_EVENT */
#ifdef HAVE_EXT_CACHE
    WOLFSSL_SESSION*(*get_sess_cb)(WOLFSSL*, unsigned char*, int, int*);
    int (*new_sess_cb)(WOLFSSL*, WOLFSSL_SESSION*);
    void (*rem_sess_cb)(WOLFSSL_CTX*, WOLFSSL_SESSION*);
#endif
#if defined(OPENSSL_EXTRA) && defined(WOLFCRYPT_HAVE_SRP) && !defined(NO_SHA256)
    Srp*  srp;  /* TLS Secure Remote Password Protocol*/
    byte* srp_password;
#endif
#ifdef WOLFSSL_STATIC_EPHEMERAL
    StaticKeyExchangeInfo_t staticKE;
#endif
};

WOLFSSL_LOCAL
int InitSSL_Ctx(WOLFSSL_CTX*, WOLFSSL_METHOD*, void* heap);
WOLFSSL_LOCAL
void FreeSSL_Ctx(WOLFSSL_CTX*);
WOLFSSL_LOCAL
void SSL_CtxResourceFree(WOLFSSL_CTX*);

WOLFSSL_LOCAL
int DeriveTlsKeys(WOLFSSL* ssl);
WOLFSSL_LOCAL
int ProcessOldClientHello(WOLFSSL* ssl, const byte* input, word32* inOutIdx,
                          word32 inSz, word16 sz);

#ifndef NO_CERTS
    WOLFSSL_LOCAL
    int AddCA(WOLFSSL_CERT_MANAGER* cm, DerBuffer** pDer, int type, int verify);
    WOLFSSL_LOCAL
    int AlreadySigner(WOLFSSL_CERT_MANAGER* cm, byte* hash);
#ifdef WOLFSSL_TRUST_PEER_CERT
    WOLFSSL_LOCAL
    int AddTrustedPeer(WOLFSSL_CERT_MANAGER* cm, DerBuffer** pDer, int verify);
    WOLFSSL_LOCAL
    int AlreadyTrustedPeer(WOLFSSL_CERT_MANAGER* cm, byte* hash);
#endif
#endif

/* All cipher suite related info
 * Keep as a constant size (no ifdefs) for session export */
typedef struct CipherSpecs {
    word16 key_size;
    word16 iv_size;
    word16 block_size;
    word16 aead_mac_size;
    byte bulk_cipher_algorithm;
    byte cipher_type;               /* block, stream, or aead */
    byte mac_algorithm;
    byte kea;                       /* key exchange algo */
    byte sig_algo;
    byte hash_size;
    byte pad_size;
    byte static_ecdh;
} CipherSpecs;


void InitCipherSpecs(CipherSpecs* cs);


/* Supported Key Exchange Protocols */
enum KeyExchangeAlgorithm {
    no_kea,
    rsa_kea,
    diffie_hellman_kea,
    fortezza_kea,
    psk_kea,
    dhe_psk_kea,
    ecdhe_psk_kea,
    ntru_kea,
    ecc_diffie_hellman_kea,
    ecc_static_diffie_hellman_kea       /* for verify suite only */
};

/* Supported Authentication Schemes */
enum SignatureAlgorithm {
    anonymous_sa_algo = 0,
    rsa_sa_algo       = 1,
    dsa_sa_algo       = 2,
    ecc_dsa_sa_algo   = 3,
    rsa_pss_sa_algo   = 8,
    ed25519_sa_algo   = 9,
    rsa_pss_pss_algo  = 10,
    ed448_sa_algo     = 11
};

#define PSS_RSAE_TO_PSS_PSS(macAlgo) \
    (macAlgo + (pss_sha256 - sha256_mac))

#define PSS_PSS_HASH_TO_MAC(macAlgo) \
    (macAlgo - (pss_sha256 - sha256_mac))

enum SigAlgRsaPss {
    pss_sha256  = 0x09,
    pss_sha384  = 0x0a,
    pss_sha512  = 0x0b,
};


/* Supprted ECC Curve Types */
enum EccCurves {
    named_curve = 3
};


/* Valid client certificate request types from page 27 */
enum ClientCertificateType {
    rsa_sign            = 1,
    dss_sign            = 2,
    rsa_fixed_dh        = 3,
    dss_fixed_dh        = 4,
    rsa_ephemeral_dh    = 5,
    dss_ephemeral_dh    = 6,
    fortezza_kea_cert   = 20,
    ecdsa_sign          = 64,
    rsa_fixed_ecdh      = 65,
    ecdsa_fixed_ecdh    = 66
};


#ifndef WOLFSSL_AEAD_ONLY
enum CipherType { stream, block, aead };
#else
enum CipherType { aead };
#endif


#if defined(BUILD_AES) || defined(BUILD_AESGCM) || (defined(HAVE_CHACHA) && \
                               defined(HAVE_POLY1305)) || defined(WOLFSSL_TLS13)
    #define CIPHER_NONCE
#endif

#if defined(WOLFSSL_DTLS) && defined(HAVE_SECURE_RENEGOTIATION)
enum CipherSrc {
    KEYS_NOT_SET = 0,
    KEYS,     /* keys from ssl->keys are loaded */
    SCR       /* keys from ssl->secure_renegotiation->tmp_keys are loaded */
};
#endif

/* cipher for now */
typedef struct Ciphers {
#ifdef BUILD_ARC4
    Arc4*   arc4;
#endif
#ifdef BUILD_DES3
    Des3*   des3;
#endif
#if defined(BUILD_AES) || defined(BUILD_AESGCM)
    Aes*    aes;
    #if (defined(BUILD_AESGCM) || defined(HAVE_AESCCM)) && \
                                                      !defined(WOLFSSL_NO_TLS12)
        byte* additional;
    #endif
#endif
#ifdef CIPHER_NONCE
    byte* nonce;
#endif
#ifdef HAVE_CAMELLIA
    Camellia* cam;
#endif
#ifdef HAVE_CHACHA
    ChaCha*   chacha;
#endif
#ifdef HAVE_HC128
    HC128*  hc128;
#endif
#ifdef BUILD_RABBIT
    Rabbit* rabbit;
#endif
#ifdef HAVE_IDEA
    Idea* idea;
#endif
#if defined(WOLFSSL_TLS13) && defined(HAVE_NULL_CIPHER)
    Hmac* hmac;
#endif
    byte    state;
    byte    setup;       /* have we set it up flag for detection */
#if defined(WOLFSSL_DTLS) && defined(HAVE_SECURE_RENEGOTIATION)
    enum CipherSrc src;  /* DTLS uses this to determine which keys
                          * are currently loaded */
#endif
} Ciphers;


#ifdef HAVE_ONE_TIME_AUTH
/* Ciphers for one time authentication such as poly1305 */
typedef struct OneTimeAuth {
#ifdef HAVE_POLY1305
    Poly1305* poly1305;
#endif
    byte    setup;      /* flag for if a cipher has been set */

} OneTimeAuth;
#endif


WOLFSSL_LOCAL void InitCiphers(WOLFSSL* ssl);
WOLFSSL_LOCAL void FreeCiphers(WOLFSSL* ssl);


/* hashes type */
typedef struct Hashes {
    #if !defined(NO_MD5) && !defined(NO_OLD_TLS)
        byte md5[WC_MD5_DIGEST_SIZE];
    #endif
    #if !defined(NO_SHA)
        byte sha[WC_SHA_DIGEST_SIZE];
    #endif
    #ifndef NO_SHA256
        byte sha256[WC_SHA256_DIGEST_SIZE];
    #endif
    #ifdef WOLFSSL_SHA384
        byte sha384[WC_SHA384_DIGEST_SIZE];
    #endif
    #ifdef WOLFSSL_SHA512
        byte sha512[WC_SHA512_DIGEST_SIZE];
    #endif
} Hashes;

WOLFSSL_LOCAL int BuildCertHashes(WOLFSSL* ssl, Hashes* hashes);

#ifdef WOLFSSL_TLS13
typedef union Digest {
#ifndef NO_WOLFSSL_SHA256
    wc_Sha256 sha256;
#endif
#ifdef WOLFSSL_SHA384
    wc_Sha384 sha384;
#endif
#ifdef WOLFSSL_SHA512
    wc_Sha512 sha512;
#endif
} Digest;
#endif

/* Static x509 buffer */
typedef struct x509_buffer {
    int  length;                  /* actual size */
    byte buffer[MAX_X509_SIZE];   /* max static cert size */
} x509_buffer;


/* wolfSSL X509_CHAIN, for no dynamic memory SESSION_CACHE */
struct WOLFSSL_X509_CHAIN {
    int         count;                    /* total number in chain */
    x509_buffer certs[MAX_CHAIN_DEPTH];   /* only allow max depth 4 for now */
};


/* wolfSSL session type */
struct WOLFSSL_SESSION {
    word32             bornOn;                    /* create time in seconds   */
    word32             timeout;                   /* timeout in seconds       */
    byte               sessionID[ID_LEN];         /* id for protocol          */
    byte               sessionIDSz;
    byte               masterSecret[SECRET_LEN];  /* stored secret            */
    word16             haveEMS;                   /* ext master secret flag   */
#ifdef SESSION_CERTS
#ifdef OPENSSL_EXTRA
    WOLFSSL_X509*      peer;                      /* peer cert */
#endif
    WOLFSSL_X509_CHAIN chain;                     /* peer cert chain, static  */
    #ifdef WOLFSSL_ALT_CERT_CHAINS
    WOLFSSL_X509_CHAIN altChain;                  /* peer alt cert chain, static */
    #endif
#endif
#if defined(SESSION_CERTS) || (defined(WOLFSSL_TLS13) && \
                               defined(HAVE_SESSION_TICKET))
    ProtocolVersion    version;                   /* which version was used   */
#endif
#if defined(SESSION_CERTS) || !defined(NO_RESUME_SUITE_CHECK) || \
                        (defined(WOLFSSL_TLS13) && defined(HAVE_SESSION_TICKET))
    byte               cipherSuite0;              /* first byte, normally 0   */
    byte               cipherSuite;               /* 2nd byte, actual suite   */
#endif
#ifndef NO_CLIENT_CACHE
    word16             idLen;                     /* serverID length          */
    byte               serverID[SERVER_ID_LEN];   /* for easier client lookup */
#endif
#ifdef OPENSSL_EXTRA
    byte               sessionCtxSz;              /* sessionCtx length        */
    byte               sessionCtx[ID_LEN];        /* app specific context id  */
    wolfSSL_Mutex      refMutex;                  /* ref count mutex */
    int                refCount;                  /* reference count */
#endif
#ifdef WOLFSSL_TLS13
    word16             namedGroup;
#endif
#if defined(HAVE_SESSION_TICKET) || !defined(NO_PSK)
    #ifdef WOLFSSL_TLS13
    word32             ticketSeen;                /* Time ticket seen (ms) */
    word32             ticketAdd;                 /* Added by client */
    TicketNonce        ticketNonce;               /* Nonce used to derive PSK */
    #endif
    #ifdef WOLFSSL_EARLY_DATA
    word32             maxEarlyDataSz;
    #endif
#endif
#ifdef HAVE_SESSION_TICKET
    byte*              ticket;
    word16             ticketLen;
    byte               staticTicket[SESSION_TICKET_LEN];
    byte               isDynamic;
#endif
#if defined(HAVE_EXT_CACHE) || defined(OPENSSL_EXTRA)
    byte               isAlloced;
#endif
#ifdef HAVE_EX_DATA
    WOLFSSL_CRYPTO_EX_DATA ex_data;
#endif
};


WOLFSSL_LOCAL
WOLFSSL_SESSION* GetSession(WOLFSSL*, byte*, byte);
WOLFSSL_LOCAL
int          SetSession(WOLFSSL*, WOLFSSL_SESSION*);

typedef int (*hmacfp) (WOLFSSL*, byte*, const byte*, word32, int, int, int, int);

#ifndef NO_CLIENT_CACHE
    WOLFSSL_SESSION* GetSessionClient(WOLFSSL*, const byte*, int);
#endif

/* client connect state for nonblocking restart */
enum ConnectState {
    CONNECT_BEGIN = 0,
    CLIENT_HELLO_SENT,
    HELLO_AGAIN,               /* HELLO_AGAIN s for DTLS case */
    HELLO_AGAIN_REPLY,
    FIRST_REPLY_DONE,
    FIRST_REPLY_FIRST,
    FIRST_REPLY_SECOND,
    FIRST_REPLY_THIRD,
    FIRST_REPLY_FOURTH,
    FINISHED_DONE,
    SECOND_REPLY_DONE
};


/* server accept state for nonblocking restart */
enum AcceptState {
    ACCEPT_BEGIN = 0,
    ACCEPT_BEGIN_RENEG,
    ACCEPT_CLIENT_HELLO_DONE,
    ACCEPT_HELLO_RETRY_REQUEST_DONE,
    ACCEPT_FIRST_REPLY_DONE,
    SERVER_HELLO_SENT,
    SERVER_EXTENSIONS_SENT,
    CERT_SENT,
    CERT_VERIFY_SENT,
    CERT_STATUS_SENT,
    KEY_EXCHANGE_SENT,
    CERT_REQ_SENT,
    SERVER_HELLO_DONE,
    ACCEPT_SECOND_REPLY_DONE,
    TICKET_SENT,
    CHANGE_CIPHER_SENT,
    ACCEPT_FINISHED_DONE,
    ACCEPT_THIRD_REPLY_DONE
};

/* TLS 1.3 server accept state for nonblocking restart */
enum AcceptStateTls13 {
    TLS13_ACCEPT_BEGIN = 0,
    TLS13_ACCEPT_BEGIN_RENEG,
    TLS13_ACCEPT_CLIENT_HELLO_DONE,
    TLS13_ACCEPT_HELLO_RETRY_REQUEST_DONE,
    TLS13_ACCEPT_FIRST_REPLY_DONE,
    TLS13_ACCEPT_SECOND_REPLY_DONE,
    TLS13_SERVER_HELLO_SENT,
    TLS13_ACCEPT_THIRD_REPLY_DONE,
    TLS13_SERVER_EXTENSIONS_SENT,
    TLS13_CERT_REQ_SENT,
    TLS13_CERT_SENT,
    TLS13_CERT_VERIFY_SENT,
    TLS13_ACCEPT_FINISHED_SENT,
    TLS13_PRE_TICKET_SENT,
    TLS13_ACCEPT_FINISHED_DONE,
    TLS13_TICKET_SENT
};

/* buffers for struct WOLFSSL */
typedef struct Buffers {
    bufferStatic    inputBuffer;
    bufferStatic    outputBuffer;
    buffer          domainName;            /* for client check */
    buffer          clearOutputBuffer;
    buffer          sig;                   /* signature data */
    buffer          digest;                /* digest data */
    int             prevSent;              /* previous plain text bytes sent
                                              when got WANT_WRITE            */
    int             plainSz;               /* plain text bytes in buffer to send
                                              when got WANT_WRITE            */
    byte            weOwnCert;             /* SSL own cert flag */
    byte            weOwnCertChain;        /* SSL own cert chain flag */
    byte            weOwnKey;              /* SSL own key  flag */
    byte            weOwnDH;               /* SSL own dh (p,g)  flag */
#ifndef NO_DH
    buffer          serverDH_P;            /* WOLFSSL_CTX owns, unless we own */
    buffer          serverDH_G;            /* WOLFSSL_CTX owns, unless we own */
    buffer          serverDH_Pub;
    buffer          serverDH_Priv;
    DhKey*          serverDH_Key;
#endif
#ifndef NO_CERTS
    DerBuffer*      certificate;           /* WOLFSSL_CTX owns, unless we own */
    DerBuffer*      key;                   /* WOLFSSL_CTX owns, unless we own */
    byte            keyType:7;             /* Type of key: RSA, ECC, Ed25519 */
    byte            keyId:1;               /* Key data is an id not data */
    int             keySz;                 /* Size of RSA key */
    int             keyDevId;              /* Device Id for key */
    DerBuffer*      certChain;             /* WOLFSSL_CTX owns, unless we own */
                 /* chain after self, in DER, with leading size for each cert */
#ifdef WOLFSSL_TLS13
    int             certChainCnt;
    DerBuffer*      certExts;
#endif
#endif
#ifdef WOLFSSL_SEND_HRR_COOKIE
    buffer          tls13CookieSecret;     /* HRR cookie secret */
#endif
#ifdef WOLFSSL_DTLS
    WOLFSSL_DTLS_CTX dtlsCtx;              /* DTLS connection context */
    #ifndef NO_WOLFSSL_SERVER
        buffer       dtlsCookieSecret;     /* DTLS cookie secret */
    #endif /* NO_WOLFSSL_SERVER */
#endif
#ifdef HAVE_PK_CALLBACKS
    #ifdef HAVE_ECC
        buffer peerEccDsaKey;              /* we own for Ecc Verify Callbacks */
    #endif /* HAVE_ECC */
    #ifdef HAVE_ED25519
        buffer peerEd25519Key;             /* for Ed25519 Verify Callbacks */
    #endif /* HAVE_ED25519 */
    #ifdef HAVE_ED448
        buffer peerEd448Key;             /* for Ed448 Verify Callbacks */
    #endif /* HAVE_ED448 */
    #ifndef NO_RSA
        buffer peerRsaKey;                 /* we own for Rsa Verify Callbacks */
    #endif /* NO_RSA */
#endif /* HAVE_PK_CALLBACKS */
} Buffers;

/* sub-states for send/do key share (key exchange) */
enum asyncState {
    TLS_ASYNC_BEGIN = 0,
    TLS_ASYNC_BUILD,
    TLS_ASYNC_DO,
    TLS_ASYNC_VERIFY,
    TLS_ASYNC_FINALIZE,
    TLS_ASYNC_END
};

/* sub-states for build message */
enum buildMsgState {
    BUILD_MSG_BEGIN = 0,
    BUILD_MSG_SIZE,
    BUILD_MSG_HASH,
    BUILD_MSG_VERIFY_MAC,
    BUILD_MSG_ENCRYPT,
    BUILD_MSG_ENCRYPTED_VERIFY_MAC,
};

/* sub-states for cipher operations */
enum cipherState {
    CIPHER_STATE_BEGIN = 0,
    CIPHER_STATE_DO,
    CIPHER_STATE_END,
};

typedef struct Options {
#ifndef NO_PSK
    wc_psk_client_callback client_psk_cb;
    wc_psk_server_callback server_psk_cb;
#ifdef WOLFSSL_TLS13
    wc_psk_client_tls13_callback client_psk_tls13_cb;  /* client callback */
    wc_psk_server_tls13_callback server_psk_tls13_cb;  /* server callback */
#endif
    void*             psk_ctx;
#endif /* NO_PSK */
#if defined(OPENSSL_EXTRA) || defined(HAVE_WEBSERVER) || defined(WOLFSSL_WPAS_SMALL)
    unsigned long     mask; /* store SSL_OP_ flags */
#endif

    /* on/off or small bit flags, optimize layout */
#if defined(HAVE_SESSION_TICKET) || !defined(NO_PSK)
    word16            havePSK:1;            /* psk key set by user */
#endif /* HAVE_SESSION_TICKET || !NO_PSK */
    word16            sendVerify:2;     /* false = 0, true = 1, sendBlank = 2 */
    word16            sessionCacheOff:1;
    word16            sessionCacheFlushOff:1;
#ifdef HAVE_EXT_CACHE
    word16            internalCacheOff:1;
#endif
    word16            side:2;             /* client, server or neither end */
    word16            verifyPeer:1;
    word16            verifyNone:1;
    word16            failNoCert:1;
    word16            failNoCertxPSK:1;   /* fail for no cert except with PSK */
    word16            downgrade:1;        /* allow downgrade of versions */
    word16            resuming:1;
    word16            haveSessionId:1;    /* server may not send */
    word16            tls:1;              /* using TLS ? */
    word16            tls1_1:1;           /* using TLSv1.1+ ? */
    word16            tls1_3:1;           /* using TLSv1.3+ ? */
    word16            dtls:1;             /* using datagrams ? */
    word16            connReset:1;        /* has the peer reset */
    word16            isClosed:1;         /* if we consider conn closed */
    word16            closeNotify:1;      /* we've received a close notify */
    word16            sentNotify:1;       /* we've sent a close notify */
    word16            usingCompression:1; /* are we using compression */
    word16            haveRSA:1;          /* RSA available */
    word16            haveECC:1;          /* ECC available */
    word16            haveDH:1;           /* server DH parms set by user */
    word16            haveNTRU:1;         /* server NTRU  private key loaded */
    word16            haveQSH:1;          /* have QSH ability */
    word16            haveECDSAsig:1;     /* server ECDSA signed cert */
    word16            haveStaticECC:1;    /* static server ECC private key */
    word16            havePeerCert:1;     /* do we have peer's cert */
    word16            havePeerVerify:1;   /* and peer's cert verify */
    word16            usingPSK_cipher:1;  /* are using psk as cipher */
    word16            usingAnon_cipher:1; /* are we using an anon cipher */
    word16            noPskDheKe:1;       /* Don't use (EC)DHE with PSK */
    word16            sendAlertState:1;   /* nonblocking resume */
    word16            partialWrite:1;     /* only one msg per write call */
    word16            quietShutdown:1;    /* don't send close notify */
    word16            certOnly:1;         /* stop once we get cert */
    word16            groupMessages:1;    /* group handshake messages */
    word16            saveArrays:1;       /* save array Memory for user get keys
                                           or psk */
    word16            weOwnRng:1;         /* will be true unless CTX owns */
    word16            haveEMS:1;          /* using extended master secret */
#ifdef HAVE_POLY1305
    word16            oldPoly:1;        /* set when to use old rfc way of poly*/
#endif
#ifdef HAVE_ANON
    word16            haveAnon:1;       /* User wants to allow Anon suites */
#endif
#ifdef HAVE_SESSION_TICKET
    word16            createTicket:1;     /* Server to create new Ticket */
    word16            useTicket:1;        /* Use Ticket not session cache */
    word16            rejectTicket:1;     /* Callback rejected ticket */
#ifdef WOLFSSL_TLS13
    word16            noTicketTls13:1;    /* Server won't create new Ticket */
#endif
#endif
#ifdef WOLFSSL_DTLS
    word16            dtlsUseNonblock:1;  /* are we using nonblocking socket */
    word16            dtlsHsRetain:1;     /* DTLS retaining HS data */
    word16            haveMcast:1;        /* using multicast ? */
#ifdef WOLFSSL_SCTP
    word16            dtlsSctp:1;         /* DTLS-over-SCTP mode */
#endif
#endif
#if defined(HAVE_TLS_EXTENSIONS) && defined(HAVE_SUPPORTED_CURVES)
    word16            userCurves:1;       /* indicates user called wolfSSL_UseSupportedCurve */
#endif
    word16            keepResources:1;    /* Keep resources after handshake */
    word16            useClientOrder:1;   /* Use client's cipher order */
    word16            mutualAuth:1;       /* Mutual authentication is rquired */
#if defined(WOLFSSL_TLS13) && defined(WOLFSSL_POST_HANDSHAKE_AUTH)
    word16            postHandshakeAuth:1;/* Client send post_handshake_auth
                                           * extension */
#endif
#if defined(WOLFSSL_TLS13) && !defined(NO_WOLFSSL_SERVER)
    word16            sendCookie:1;       /* Server creates a Cookie in HRR */
#endif
#ifdef WOLFSSL_ALT_CERT_CHAINS
    word16            usingAltCertChain:1;/* Alternate cert chain was used */
#endif
#if defined(WOLFSSL_TLS13) && defined(WOLFSSL_TLS13_MIDDLEBOX_COMPAT)
    word16            sentChangeCipher:1; /* Change Cipher Spec sent */
#endif
#if !defined(WOLFSSL_NO_CLIENT_AUTH) && \
               ((defined(HAVE_ED25519) && !defined(NO_ED25519_CLIENT_AUTH)) || \
                (defined(HAVE_ED448) && !defined(NO_ED448_CLIENT_AUTH)))
    word16            cacheMessages:1;    /* Cache messages for sign/verify */
#endif
#ifndef NO_DH
    #if !defined(WOLFSSL_OLD_PRIME_CHECK) && \
        !defined(HAVE_FIPS) && !defined(HAVE_SELFTEST)
        word16        dhDoKeyTest:1;      /* Need to do the DH Key prime test */
        word16        dhKeyTested:1;      /* Set when key has been tested. */
    #endif
#endif
#ifdef SINGLE_THREADED
    word16            ownSuites:1;        /* if suites are malloced in ssl object */
#endif
#ifdef HAVE_ENCRYPT_THEN_MAC
    word16            disallowEncThenMac:1;   /* Don't do Encrypt-Then-MAC */
    word16            encThenMac:1;           /* Doing Encrypt-Then-MAC */
    word16            startedETMRead:1;       /* Doing Encrypt-Then-MAC read */
    word16            startedETMWrite:1;      /* Doing Encrypt-Then-MAC write */
#endif

    /* need full byte values for this section */
    byte            processReply;           /* nonblocking resume */
    byte            cipherSuite0;           /* first byte, normally 0 */
    byte            cipherSuite;            /* second byte, actual suite */
    byte            serverState;
    byte            clientState;
    byte            handShakeState;
    byte            handShakeDone;      /* at least one handshake complete */
    byte            minDowngrade;       /* minimum downgrade version */
    byte            connectState;       /* nonblocking resume */
    byte            acceptState;        /* nonblocking resume */
    byte            asyncState;         /* sub-state for enum asyncState */
    byte            buildMsgState;      /* sub-state for enum buildMsgState */
    byte            alertCount;         /* detect warning dos attempt */
#ifdef WOLFSSL_MULTICAST
    word16          mcastID;            /* Multicast group ID */
#endif
#ifndef NO_DH
    word16          minDhKeySz;         /* minimum DH key size */
    word16          maxDhKeySz;         /* minimum DH key size */
    word16          dhKeySz;            /* actual DH key size */
#endif
#ifndef NO_RSA
    short           minRsaKeySz;      /* minimum RSA key size */
#endif
#if defined(HAVE_ECC) || defined(HAVE_ED25519) || defined(HAVE_ED448)
    short           minEccKeySz;      /* minimum ECC key size */
#endif
#if defined(OPENSSL_EXTRA) || defined(OPENSSL_EXTRA_X509_SMALL)
    byte            verifyDepth;      /* maximum verification depth */
#endif
#ifdef WOLFSSL_EARLY_DATA
    word16          pskIdIndex;
    word32          maxEarlyDataSz;
#endif
#ifdef WOLFSSL_TLS13
    byte            oldMinor;          /* client preferred version < TLS 1.3 */
#endif
} Options;

typedef struct Arrays {
    byte*           pendingMsg;         /* defrag buffer */
    byte*           preMasterSecret;
    word32          preMasterSz;        /* differs for DH, actual size */
    word32          pendingMsgSz;       /* defrag buffer size */
    word32          pendingMsgOffset;   /* current offset into defrag buffer */
#if defined(HAVE_SESSION_TICKET) || !defined(NO_PSK)
    word32          psk_keySz;          /* actual size */
    char            client_identity[MAX_PSK_ID_LEN + NULL_TERM_LEN];
    char            server_hint[MAX_PSK_ID_LEN + NULL_TERM_LEN];
    byte            psk_key[MAX_PSK_KEY_LEN];
#endif
    byte            clientRandom[RAN_LEN];
    byte            serverRandom[RAN_LEN];
    byte            sessionID[ID_LEN];
    byte            sessionIDSz;
#ifdef WOLFSSL_TLS13
    byte            secret[SECRET_LEN];
#endif
    byte            masterSecret[SECRET_LEN];
#if defined(WOLFSSL_RENESAS_TSIP_TLS) && \
   !defined(NO_WOLFSSL_RENESAS_TSIP_TLS_SESSION)
    byte            tsip_masterSecret[TSIP_TLS_MASTERSECRET_SIZE];
#endif
#ifdef WOLFSSL_DTLS
    byte            cookie[MAX_COOKIE_LEN];
    byte            cookieSz;
#endif
    byte            pendingMsgType;    /* defrag buffer message type */
} Arrays;

#ifndef ASN_NAME_MAX
#define ASN_NAME_MAX 256
#endif

#ifndef MAX_DATE_SZ
#define MAX_DATE_SZ 32
#endif

#define STACK_TYPE_X509               0
#define STACK_TYPE_GEN_NAME           1
#define STACK_TYPE_BIO                2
#define STACK_TYPE_OBJ                3
#define STACK_TYPE_STRING             4
#define STACK_TYPE_CIPHER             5
#define STACK_TYPE_ACCESS_DESCRIPTION 6
#define STACK_TYPE_X509_EXT           7
#define STACK_TYPE_NULL               8
#define STACK_TYPE_X509_NAME          9
#define STACK_TYPE_CONF_VALUE         10
#define STACK_TYPE_X509_INFO          11

struct WOLFSSL_STACK {
    unsigned long num; /* number of nodes in stack
                        * (safety measure for freeing and shortcut for count) */
    #if defined(OPENSSL_ALL)
    wolf_sk_compare_cb comp;
    #endif

    union {
        WOLFSSL_X509*          x509;
        WOLFSSL_X509_NAME*     name;
        WOLFSSL_X509_INFO*     info;
        WOLFSSL_BIO*           bio;
        WOLFSSL_ASN1_OBJECT*   obj;
        WOLFSSL_CIPHER         cipher;
        WOLFSSL_ACCESS_DESCRIPTION* access;
        WOLFSSL_X509_EXTENSION* ext;
        WOLFSSL_CONF_VALUE*    conf;
        void*                  generic;
        char*                  string;
        WOLFSSL_GENERAL_NAME*  gn;
    } data;
    void* heap; /* memory heap hint */
    WOLFSSL_STACK* next;
    byte type;     /* Identifies type of stack. */
};

struct WOLFSSL_X509_NAME {
    char  *name;
    int   dynamicName;
    int   sz;
    char  staticName[ASN_NAME_MAX];
#if (defined(OPENSSL_EXTRA) || defined(OPENSSL_EXTRA_X509_SMALL)) && \
    !defined(NO_ASN)
    int   entrySz; /* number of entries */
    WOLFSSL_X509_NAME_ENTRY entry[MAX_NAME_ENTRIES]; /* all entries i.e. CN */
    WOLFSSL_X509*           x509;   /* x509 that struct belongs to */
#endif /* OPENSSL_EXTRA */
#if defined(OPENSSL_ALL) || defined(WOLFSSL_NGINX)
    byte  raw[ASN_NAME_MAX];
    int   rawLen;
#endif
    void* heap;
};

#ifndef EXTERNAL_SERIAL_SIZE
    #define EXTERNAL_SERIAL_SIZE 32
#endif

#ifdef NO_ASN
    typedef struct DNS_entry DNS_entry;
#endif

struct WOLFSSL_X509 {
    int              version;
    int              serialSz;
#ifdef WOLFSSL_SEP
    int              deviceTypeSz;
    int              hwTypeSz;
    byte             deviceType[EXTERNAL_SERIAL_SIZE];
    byte             hwType[EXTERNAL_SERIAL_SIZE];
    int              hwSerialNumSz;
    byte             hwSerialNum[EXTERNAL_SERIAL_SIZE];
#endif /* WOLFSSL_SEP */
#if (defined(WOLFSSL_SEP) || defined(WOLFSSL_QT) || defined (OPENSSL_ALL)) && \
    (defined(OPENSSL_EXTRA) || defined(OPENSSL_EXTRA_X509_SMALL))
    byte             certPolicySet;
    byte             certPolicyCrit;
#endif /* (WOLFSSL_SEP || WOLFSSL_QT) && (OPENSSL_EXTRA || OPENSSL_EXTRA_X509_SMALL) */
#if defined(WOLFSSL_QT) || defined(OPENSSL_ALL)
    WOLFSSL_STACK* ext_sk; /* Store X509_EXTENSIONS from wolfSSL_X509_get_ext */
    WOLFSSL_STACK* ext_d2i;/* Store d2i extensions from wolfSSL_X509_get_ext_d2i */
#endif /* WOLFSSL_QT || OPENSSL_ALL */
#ifdef OPENSSL_EXTRA
    WOLFSSL_ASN1_INTEGER* serialNumber; /* Stores SN from wolfSSL_X509_get_serialNumber */
#endif
    WOLFSSL_ASN1_TIME notBefore;
    WOLFSSL_ASN1_TIME notAfter;
    buffer           sig;
    int              sigOID;
    DNS_entry*       altNames;                       /* alt names list */
    buffer           pubKey;
    int              pubKeyOID;
    DNS_entry*       altNamesNext;                   /* hint for retrieval */
#if defined(HAVE_ECC) || defined(HAVE_ED25519) || defined(HAVE_ED448)
    word32       pkCurveOID;
#endif /* HAVE_ECC */
#ifndef NO_CERTS
    DerBuffer*   derCert;                            /* may need  */
#endif
    void*            heap;                           /* heap hint */
    byte             dynamicMemory;                  /* dynamic memory flag */
    byte             isCa:1;
#ifdef WOLFSSL_CERT_EXT
    char             certPolicies[MAX_CERTPOL_NB][MAX_CERTPOL_SZ];
    int              certPoliciesNb;
#endif /* WOLFSSL_CERT_EXT */
#if defined(OPENSSL_EXTRA) || defined(OPENSSL_ALL)
    wolfSSL_Mutex    refMutex;                       /* ref count mutex */
    int              refCount;                       /* reference count */
#endif
#if defined(OPENSSL_EXTRA) || defined(OPENSSL_EXTRA_X509_SMALL)
#ifdef HAVE_EX_DATA
    WOLFSSL_CRYPTO_EX_DATA ex_data;
#endif
    byte*            authKeyId;
    byte*            subjKeyId;
    byte*            extKeyUsageSrc;
    const byte*      CRLInfo;
    byte*            authInfo;
#if defined(OPENSSL_ALL) || defined(WOLFSSL_QT)
    byte*            authInfoCaIssuer;
    int              authInfoCaIssuerSz;
#endif
    word32           pathLength;
    word16           keyUsage;
    int              CRLInfoSz;
    int              authInfoSz;
    word32           authKeyIdSz;
    word32           subjKeyIdSz;
    word32           extKeyUsageSz;
    word32           extKeyUsageCount;

    byte             CRLdistSet:1;
    byte             CRLdistCrit:1;
    byte             authInfoSet:1;
    byte             authInfoCrit:1;
    byte             keyUsageSet:1;
    byte             keyUsageCrit:1;
    byte             extKeyUsageCrit:1;
    byte             subjKeyIdSet:1;

    byte             subjKeyIdCrit:1;
    byte             basicConstSet:1;
    byte             basicConstCrit:1;
    byte             basicConstPlSet:1;
    byte             subjAltNameSet:1;
    byte             subjAltNameCrit:1;
    byte             authKeyIdSet:1;
    byte             authKeyIdCrit:1;
#endif /* OPENSSL_EXTRA || OPENSSL_EXTRA_X509_SMALL */
    byte             serial[EXTERNAL_SERIAL_SIZE];
    char             subjectCN[ASN_NAME_MAX];        /* common name short cut */
#ifdef WOLFSSL_CERT_REQ
    char             challengePw[CTC_NAME_SIZE]; /* for REQ certs */
#endif
    WOLFSSL_X509_NAME issuer;
    WOLFSSL_X509_NAME subject;
#if defined(OPENSSL_ALL) || defined(WOLFSSL_HAPROXY) || defined(WOLFSSL_WPAS)
    WOLFSSL_X509_ALGOR algor;
    WOLFSSL_X509_PUBKEY key;
#endif
    byte issuerSet:1;
};


/* record layer header for PlainText, Compressed, and CipherText */
typedef struct RecordLayerHeader {
    byte            type;
    byte            pvMajor;
    byte            pvMinor;
    byte            length[2];
} RecordLayerHeader;


/* record layer header for DTLS PlainText, Compressed, and CipherText */
typedef struct DtlsRecordLayerHeader {
    byte            type;
    byte            pvMajor;
    byte            pvMinor;
    byte            sequence_number[8];   /* per record */
    byte            length[2];
} DtlsRecordLayerHeader;


typedef struct DtlsFrag {
    word32 begin;
    word32 end;
    struct DtlsFrag* next;
} DtlsFrag;


typedef struct DtlsMsg {
    struct DtlsMsg* next;
    byte*           buf;
    byte*           msg;
    DtlsFrag*       fragList;
    word32          fragSz;    /* Length of fragments received */
    word16          epoch;     /* Epoch that this message belongs to */
    word32          seq;       /* Handshake sequence number    */
    word32          sz;        /* Length of whole message      */
    byte            type;
} DtlsMsg;


#ifdef HAVE_NETX

    /* NETX I/O Callback default */
    typedef struct NetX_Ctx {
        NX_TCP_SOCKET* nxSocket;    /* send/recv socket handle */
        NX_PACKET*     nxPacket;    /* incoming packet handle for short reads */
        ULONG          nxOffset;    /* offset already read from nxPacket */
        ULONG          nxWait;      /* wait option flag */
    } NetX_Ctx;

#endif

/* Handshake messages received from peer (plus change cipher */
typedef struct MsgsReceived {
    word16 got_hello_request:1;
    word16 got_client_hello:2;
    word16 got_server_hello:2;
    word16 got_hello_verify_request:1;
    word16 got_session_ticket:1;
    word16 got_end_of_early_data:1;
    word16 got_hello_retry_request:1;
    word16 got_encrypted_extensions:1;
    word16 got_certificate:1;
    word16 got_certificate_status:1;
    word16 got_server_key_exchange:1;
    word16 got_certificate_request:1;
    word16 got_server_hello_done:1;
    word16 got_certificate_verify:1;
    word16 got_client_key_exchange:1;
    word16 got_finished:1;
    word16 got_key_update:1;
    word16 got_change_cipher:1;
} MsgsReceived;


/* Handshake hashes */
typedef struct HS_Hashes {
    Hashes          verifyHashes;
    Hashes          certHashes;         /* for cert verify */
#ifndef NO_SHA
    wc_Sha          hashSha;            /* sha hash of handshake msgs */
#endif
#if !defined(NO_MD5) && !defined(NO_OLD_TLS)
    wc_Md5          hashMd5;            /* md5 hash of handshake msgs */
#endif
#ifndef NO_SHA256
    wc_Sha256       hashSha256;         /* sha256 hash of handshake msgs */
#endif
#ifdef WOLFSSL_SHA384
    wc_Sha384       hashSha384;         /* sha384 hash of handshake msgs */
#endif
#ifdef WOLFSSL_SHA512
    wc_Sha512       hashSha512;         /* sha512 hash of handshake msgs */
#endif
#if (defined(HAVE_ED25519) || defined(HAVE_ED448)) && \
                                                !defined(WOLFSSL_NO_CLIENT_AUTH)
    byte*           messages;           /* handshake messages */
    int             length;             /* length of handshake messages' data */
    int             prevLen;            /* length of messages but last */
#endif
} HS_Hashes;


#ifndef WOLFSSL_NO_TLS12
/* Persistable BuildMessage arguments */
typedef struct BuildMsgArgs {
    word32 digestSz;
    word32 sz;
    word32 pad;
    word32 idx;
    word32 headerSz;
    word16 size;
    word32 ivSz;      /* TLSv1.1  IV */
    byte*  iv;
} BuildMsgArgs;
#endif

#ifdef WOLFSSL_ASYNC_CRYPT
    #define MAX_ASYNC_ARGS 18
    typedef void (*FreeArgsCb)(struct WOLFSSL* ssl, void* pArgs);

    struct WOLFSSL_ASYNC {
        WC_ASYNC_DEV* dev;
        FreeArgsCb    freeArgs; /* function pointer to cleanup args */
        word32        args[MAX_ASYNC_ARGS]; /* holder for current args */
        BuildMsgArgs  buildArgs; /* holder for current BuildMessage args */
    };
#endif

#ifdef HAVE_WRITE_DUP

    #define WRITE_DUP_SIDE 1
    #define READ_DUP_SIDE 2

    typedef struct WriteDup {
        wolfSSL_Mutex   dupMutex;       /* reference count mutex */
        int             dupCount;       /* reference count */
        int             dupErr;         /* under dupMutex, pass to other side */
    } WriteDup;

    WOLFSSL_LOCAL void FreeWriteDup(WOLFSSL* ssl);
    WOLFSSL_LOCAL int  NotifyWriteSide(WOLFSSL* ssl, int err);
#endif /* HAVE_WRITE_DUP */

#if defined(WOLFSSL_TLS13) && defined(WOLFSSL_POST_HANDSHAKE_AUTH)
typedef struct CertReqCtx CertReqCtx;

struct CertReqCtx {
    CertReqCtx* next;
    byte        len;
    byte        ctx;
};
#endif

#ifdef WOLFSSL_EARLY_DATA
typedef enum EarlyDataState {
    no_early_data,
    early_data_ext,
    expecting_early_data,
    process_early_data,
    done_early_data
} EarlyDataState;
#endif

/* wolfSSL ssl type */
struct WOLFSSL {
    WOLFSSL_CTX*    ctx;
    Suites*         suites;             /* only need during handshake */
    Arrays*         arrays;
#ifdef WOLFSSL_TLS13
    byte            clientSecret[SECRET_LEN];
    byte            serverSecret[SECRET_LEN];
#endif
    HS_Hashes*      hsHashes;
    void*           IOCB_ReadCtx;
    void*           IOCB_WriteCtx;
    WC_RNG*         rng;
    void*           verifyCbCtx;        /* cert verify callback user ctx*/
    VerifyCallback  verifyCallback;     /* cert verification callback */
    void*           heap;               /* for user overrides */
#ifdef HAVE_WRITE_DUP
    WriteDup*       dupWrite;           /* valid pointer indicates ON */
             /* side that decrements dupCount to zero frees overall structure */
    byte            dupSide;            /* write side or read side */
#endif
#ifdef OPENSSL_EXTRA
    byte              cbioFlag;  /* WOLFSSL_CBIO_RECV/SEND: CBIORecv/Send is set */
#endif
    CallbackIORecv  CBIORecv;
    CallbackIOSend  CBIOSend;
#ifdef WOLFSSL_STATIC_MEMORY
    WOLFSSL_HEAP_HINT heap_hint;
#endif
#ifndef NO_HANDSHAKE_DONE_CB
    HandShakeDoneCb hsDoneCb;          /*  notify user handshake done */
    void*           hsDoneCtx;         /*  user handshake cb context  */
#endif
#ifdef WOLFSSL_ASYNC_CRYPT
    struct WOLFSSL_ASYNC async;
#elif defined(WOLFSSL_NONBLOCK_OCSP)
    void*           nonblockarg;        /* dynamic arg for handling non-block resume */
#endif
    void*           hsKey;              /* Handshake key (RsaKey or ecc_key) allocated from heap */
    word32          hsType;             /* Type of Handshake key (hsKey) */
    WOLFSSL_CIPHER  cipher;
#ifndef WOLFSSL_AEAD_ONLY
    hmacfp          hmac;
#endif
    Ciphers         encrypt;
    Ciphers         decrypt;
    Buffers         buffers;
    WOLFSSL_SESSION session;
#ifdef HAVE_EXT_CACHE
    WOLFSSL_SESSION* extSession;
#endif
    WOLFSSL_ALERT_HISTORY alert_history;
    int             error;
    int             rfd;                /* read  file descriptor */
    int             wfd;                /* write file descriptor */
    int             rflags;             /* user read  flags */
    int             wflags;             /* user write flags */
    word32          timeout;            /* session timeout */
    word32          fragOffset;         /* fragment offset */
    word16          curSize;
    byte            verifyDepth;
    RecordLayerHeader curRL;
    MsgsReceived    msgsReceived;       /* peer messages received */
    ProtocolVersion version;            /* negotiated version */
    ProtocolVersion chVersion;          /* client hello version */
    CipherSpecs     specs;
    Keys            keys;
    Options         options;
#ifdef OPENSSL_EXTRA
    CallbackInfoState* CBIS;             /* used to get info about SSL state */
    int              cbmode;             /* read or write on info callback */
    int              cbtype;             /* event type in info callback */
    WOLFSSL_BIO*     biord;              /* socket bio read  to free/close */
    WOLFSSL_BIO*     biowr;              /* socket bio write to free/close */
    byte             sessionCtx[ID_LEN]; /* app session context ID */
    WOLFSSL_X509_VERIFY_PARAM* param;    /* verification parameters*/
#endif
#if defined(OPENSSL_EXTRA) || defined(OPENSSL_EXTRA_X509_SMALL)
    unsigned long    peerVerifyRet;
#endif
#ifdef OPENSSL_EXTRA
    byte             readAhead;
    byte             sessionCtxSz;       /* size of sessionCtx stored */
#ifdef HAVE_PK_CALLBACKS
    void*            loggingCtx;         /* logging callback argument */
#endif
#endif /* OPENSSL_EXTRA */
#ifndef NO_RSA
    RsaKey*         peerRsaKey;
#ifdef WOLFSSL_RENESAS_TSIP_TLS
    byte            *peerTsipEncRsaKeyIndex;
#endif
    byte            peerRsaKeyPresent;
#endif
#ifdef HAVE_QSH
    QSHKey*         QSH_Key;
    QSHKey*         peerQSHKey;
    QSHSecret*      QSH_secret;
    byte            isQSH;             /* is the handshake a QSH? */
    byte            sendQSHKeys;       /* flag for if the client should sen
                                          public keys */
    byte            peerQSHKeyPresent;
    byte            minRequest;
    byte            maxRequest;
    byte            user_set_QSHSchemes;
#endif
#if defined(WOLFSSL_TLS13) || defined(HAVE_FFDHE)
    word16          namedGroup;
#endif
#ifdef WOLFSSL_TLS13
    word16          group[WOLFSSL_MAX_GROUP_COUNT];
    byte            numGroups;
#endif
    word16          pssAlgo;
#ifdef WOLFSSL_TLS13
    word16          certHashSigAlgoSz;  /* SigAlgoCert ext length in bytes */
    byte            certHashSigAlgo[WOLFSSL_MAX_SIGALGO]; /* cert sig/algo to
                                                           * offer */
#endif
#ifdef HAVE_NTRU
    word16          peerNtruKeyLen;
    byte            peerNtruKey[MAX_NTRU_PUB_KEY_SZ];
    byte            peerNtruKeyPresent;
#endif
#if defined(HAVE_ECC) || defined(HAVE_ED25519) || defined(HAVE_ED448)
    int             eccVerifyRes;
#endif
#if defined(HAVE_ECC) || defined(HAVE_CURVE25519) || defined(HAVE_CURVE448)
    word32          ecdhCurveOID;            /* curve Ecc_Sum     */
    ecc_key*        eccTempKey;              /* private ECDHE key */
    byte            eccTempKeyPresent;       /* also holds type */
    byte            peerEccKeyPresent;
#endif
#ifdef HAVE_ECC
    ecc_key*        peerEccKey;              /* peer's  ECDHE key */
    ecc_key*        peerEccDsaKey;           /* peer's  ECDSA key */
    word16          eccTempKeySz;            /* in octets 20 - 66 */
    byte            peerEccDsaKeyPresent;
#endif
#if defined(HAVE_ECC) || defined(HAVE_ED25519) || defined(HAVE_CURVE448)
    word32          pkCurveOID;              /* curve Ecc_Sum     */
#endif
#ifdef HAVE_ED25519
    ed25519_key*    peerEd25519Key;
    byte            peerEd25519KeyPresent;
#endif
#ifdef HAVE_CURVE25519
    curve25519_key* peerX25519Key;
    byte            peerX25519KeyPresent;
#endif
#ifdef HAVE_ED448
    ed448_key*      peerEd448Key;
    byte            peerEd448KeyPresent;
#endif
#ifdef HAVE_CURVE448
    curve448_key*   peerX448Key;
    byte            peerX448KeyPresent;
#endif
#ifdef HAVE_LIBZ
    z_stream        c_stream;           /* compression   stream */
    z_stream        d_stream;           /* decompression stream */
    byte            didStreamInit;      /* for stream init and end */
#endif
#ifdef WOLFSSL_DTLS
    int             dtls_timeout_init;  /* starting timeout value */
    int             dtls_timeout_max;   /* maximum timeout value */
    int             dtls_timeout;       /* current timeout value, changes */
    word32          dtls_tx_msg_list_sz;
    word32          dtls_rx_msg_list_sz;
    DtlsMsg*        dtls_tx_msg_list;
    DtlsMsg*        dtls_tx_msg;
    DtlsMsg*        dtls_rx_msg_list;
    void*           IOCB_CookieCtx;     /* gen cookie ctx */
    word32          dtls_expected_rx;
#ifdef WOLFSSL_SESSION_EXPORT
    wc_dtls_export  dtls_export;        /* export function for session */
#endif
#if defined(WOLFSSL_SCTP) || defined(WOLFSSL_DTLS_MTU)
    word16          dtlsMtuSz;
#endif /* WOLFSSL_SCTP || WOLFSSL_DTLS_MTU */
#ifdef WOLFSSL_MULTICAST
    void*           mcastHwCbCtx;       /* Multicast highwater callback ctx */
#endif /* WOLFSSL_MULTICAST */
#ifdef WOLFSSL_DTLS_DROP_STATS
    word32 macDropCount;
    word32 replayDropCount;
#endif /* WOLFSSL_DTLS_DROP_STATS */
#endif /* WOLFSSL_DTLS */
#ifdef WOLFSSL_CALLBACKS
    TimeoutInfo     timeoutInfo;        /* info saved during handshake */
    HandShakeInfo   handShakeInfo;      /* info saved during handshake */
#endif
#ifdef OPENSSL_EXTRA
    SSL_Msg_Cb      protoMsgCb;         /* inspect protocol message callback */
    void*           protoMsgCtx;        /* user set context with msg callback */
#endif
#if defined(WOLFSSL_CALLBACKS) || defined(OPENSSL_EXTRA)
    byte            hsInfoOn;           /* track handshake info        */
    byte            toInfoOn;           /* track timeout   info        */
#endif
#ifdef HAVE_FUZZER
    CallbackFuzzer  fuzzerCb;           /* for testing with using fuzzer */
    void*           fuzzerCtx;          /* user defined pointer */
#endif
#if defined(WOLFSSL_TLS13) && defined(WOLFSSL_POST_HANDSHAKE_AUTH)
    CertReqCtx*     certReqCtx;
#endif
#ifdef KEEP_PEER_CERT
    WOLFSSL_X509     peerCert;           /* X509 peer cert */
#endif
#ifdef KEEP_OUR_CERT
    WOLFSSL_X509*    ourCert;            /* keep alive a X509 struct of cert.
                                            points to ctx if not owned (owned
                                            flag found in buffers.weOwnCert) */
#endif
    byte             keepCert;           /* keep certificate after handshake */
#if defined(HAVE_EX_DATA) || defined(FORTRESS)
    WOLFSSL_CRYPTO_EX_DATA ex_data; /* external data, for Fortress */
#endif
    int              devId;             /* async device id to use */
#ifdef HAVE_ONE_TIME_AUTH
    OneTimeAuth     auth;
#endif
#ifdef HAVE_TLS_EXTENSIONS
    TLSX* extensions;                  /* RFC 6066 TLS Extensions data */
    #ifdef HAVE_MAX_FRAGMENT
        word16 max_fragment;
    #endif
    #ifdef HAVE_TRUNCATED_HMAC
        byte truncated_hmac;
    #endif
    #ifdef HAVE_CERTIFICATE_STATUS_REQUEST
        byte status_request;
    #endif
    #ifdef HAVE_CERTIFICATE_STATUS_REQUEST_V2
        byte status_request_v2;
    #endif
    #if defined(HAVE_SECURE_RENEGOTIATION) \
        || defined(HAVE_SERVER_RENEGOTIATION_INFO)
        int                  secure_rene_count;    /* how many times */
        SecureRenegotiation* secure_renegotiation; /* valid pointer indicates */
    #endif                                         /* user turned on */
    #ifdef HAVE_ALPN
        char*   alpn_client_list;  /* keep the client's list */
        #if defined(OPENSSL_ALL) || defined(WOLFSSL_NGINX)  || defined(WOLFSSL_HAPROXY)
            CallbackALPNSelect alpnSelect;
            void*              alpnSelectArg;
        #endif
    #endif                         /* of accepted protocols */
    #if !defined(NO_WOLFSSL_CLIENT) && defined(HAVE_SESSION_TICKET)
        CallbackSessionTicket session_ticket_cb;
        void*                 session_ticket_ctx;
        byte                  expect_session_ticket;
    #endif
#endif /* HAVE_TLS_EXTENSIONS */
#ifdef HAVE_OCSP
        void*       ocspIOCtx;
    #ifdef OPENSSL_EXTRA
        byte*       ocspResp;
        int         ocspRespSz;
        #if defined(OPENSSL_ALL) || defined(WOLFSSL_NGINX) || defined(WOLFSSL_HAPROXY)
            char*   url;
        #endif
    #endif
#endif
#ifdef HAVE_NETX
    NetX_Ctx        nxCtx;             /* NetX IO Context */
#endif
#if defined(WOLFSSL_APACHE_MYNEWT) && !defined(WOLFSSL_LWIP)
    void*           mnCtx;             /* mynewt mn_socket IO Context */
#endif /* defined(WOLFSSL_APACHE_MYNEWT) && !defined(WOLFSSL_LWIP) */
#ifdef WOLFSSL_GNRC
    struct gnrc_wolfssl_ctx *gnrcCtx;  /* Riot-OS GNRC UDP/IP context */
#endif
#ifdef SESSION_INDEX
    int sessionIndex;                  /* Session's location in the cache. */
#endif
#ifdef ATOMIC_USER
    void*    MacEncryptCtx;    /* Atomic User Mac/Encrypt Callback Context */
    void*    DecryptVerifyCtx; /* Atomic User Decrypt/Verify Callback Context */
    #ifdef HAVE_ENCRYPT_THEN_MAC
        void*    EncryptMacCtx;    /* Atomic User Encrypt/Mac Callback Ctx */
        void*    VerifyDecryptCtx; /* Atomic User Verify/Decrypt Callback Ctx */
    #endif
#endif
#ifdef HAVE_PK_CALLBACKS
    #ifdef HAVE_ECC
        void* EccKeyGenCtx;              /* EccKeyGen  Callback Context */
        void* EccSignCtx;                /* Ecc Sign   Callback Context */
        void* EccVerifyCtx;              /* Ecc Verify Callback Context */
        void* EccSharedSecretCtx;        /* Ecc Pms    Callback Context */
        #ifdef HAVE_ED25519
            void* Ed25519SignCtx;        /* ED25519 Sign   Callback Context */
            void* Ed25519VerifyCtx;      /* ED25519 Verify Callback Context */
        #endif
        #ifdef HAVE_CURVE25519
            void* X25519KeyGenCtx;       /* X25519 KeyGen Callback Context */
            void* X25519SharedSecretCtx; /* X25519 Pms    Callback Context */
        #endif
        #ifdef HAVE_ED448
            void* Ed448SignCtx;          /* ED448 Sign   Callback Context */
            void* Ed448VerifyCtx;        /* ED448 Verify Callback Context */
        #endif
        #ifdef HAVE_CURVE448
            void* X448KeyGenCtx;         /* X448 KeyGen Callback Context */
            void* X448SharedSecretCtx;   /* X448 Pms    Callback Context */
        #endif
    #endif /* HAVE_ECC */
    #ifndef NO_DH
        void* DhAgreeCtx; /* DH Pms Callback Context */
    #endif /* !NO_DH */
    #ifndef NO_RSA
        void* RsaSignCtx;     /* Rsa Sign   Callback Context */
        void* RsaVerifyCtx;   /* Rsa Verify Callback Context */
        #ifdef WC_RSA_PSS
            void* RsaPssSignCtx;     /* Rsa PSS Sign   Callback Context */
            void* RsaPssVerifyCtx;   /* Rsa PSS Verify Callback Context */
        #endif
        void* RsaEncCtx;      /* Rsa Public  Encrypt   Callback Context */
        void* RsaDecCtx;      /* Rsa Private Decrypt   Callback Context */
    #endif /* NO_RSA */
#endif /* HAVE_PK_CALLBACKS */
#ifdef HAVE_SECRET_CALLBACK
        SessionSecretCb sessionSecretCb;
        void*           sessionSecretCtx;
    #ifdef WOLFSSL_TLS13
        Tls13SecretCb   tls13SecretCb;
        void*           tls13SecretCtx;
    #endif
#endif /* HAVE_SECRET_CALLBACK */
#ifdef WOLFSSL_JNI
        void* jObjectRef;     /* reference to WolfSSLSession in JNI wrapper */
#endif /* WOLFSSL_JNI */
#ifdef WOLFSSL_EARLY_DATA
    EarlyDataState earlyData;
    word32 earlyDataSz;
#endif
#ifdef OPENSSL_ALL
    long verifyCallbackResult;
#endif
#if defined(OPENSSL_ALL) || defined(WOLFSSL_QT)
    WOLFSSL_STACK* supportedCiphers; /* Used in wolfSSL_get_ciphers_compat */
    WOLFSSL_STACK* peerCertChain;    /* Used in wolfSSL_get_peer_cert_chain */
#endif
#ifdef WOLFSSL_STATIC_EPHEMERAL
    StaticKeyExchangeInfo_t staticKE;
#endif
};


WOLFSSL_LOCAL int  SSL_CTX_RefCount(WOLFSSL_CTX* ctx, int incr);
WOLFSSL_LOCAL int  SetSSL_CTX(WOLFSSL*, WOLFSSL_CTX*, int);
WOLFSSL_LOCAL int  InitSSL(WOLFSSL*, WOLFSSL_CTX*, int);
WOLFSSL_LOCAL void FreeSSL(WOLFSSL*, void* heap);
WOLFSSL_API   void SSL_ResourceFree(WOLFSSL*);   /* Micrium uses */


#ifndef NO_CERTS

    WOLFSSL_LOCAL int ProcessBuffer(WOLFSSL_CTX* ctx, const unsigned char* buff,
                                    long sz, int format, int type, WOLFSSL* ssl,
                                    long* used, int userChain, int verify);
    WOLFSSL_LOCAL int ProcessFile(WOLFSSL_CTX* ctx, const char* fname, int format,
                                 int type, WOLFSSL* ssl, int userChain,
                                WOLFSSL_CRL* crl, int verify);

    WOLFSSL_LOCAL int CheckHostName(DecodedCert* dCert, const char *domainName,
                                    size_t domainNameLen);
#endif


#if defined(WOLFSSL_CALLBACKS) || defined(OPENSSL_EXTRA)
    WOLFSSL_LOCAL
    void InitHandShakeInfo(HandShakeInfo*, WOLFSSL*);
    WOLFSSL_LOCAL
    void FinishHandShakeInfo(HandShakeInfo*);
    WOLFSSL_LOCAL
    void AddPacketName(WOLFSSL* ssl, const char* name);

    WOLFSSL_LOCAL
    void InitTimeoutInfo(TimeoutInfo*);
    WOLFSSL_LOCAL
    void FreeTimeoutInfo(TimeoutInfo*, void*);
    WOLFSSL_LOCAL
    void AddPacketInfo(WOLFSSL* ssl, const char* name, int type,
                               const byte* data, int sz, int write, void* heap);
    WOLFSSL_LOCAL
    void AddLateName(const char*, TimeoutInfo*);
    WOLFSSL_LOCAL
    void AddLateRecordHeader(const RecordLayerHeader* rl, TimeoutInfo* info);
#endif


/* Record Layer Header identifier from page 12 */
enum ContentType {
    no_type            = 0,
    change_cipher_spec = 20,
    alert              = 21,
    handshake          = 22,
    application_data   = 23
};


/* handshake header, same for each message type, pgs 20/21 */
typedef struct HandShakeHeader {
    byte            type;
    word24          length;
} HandShakeHeader;


/* DTLS handshake header, same for each message type */
typedef struct DtlsHandShakeHeader {
    byte            type;
    word24          length;
    byte            message_seq[2];    /* start at 0, retransmit gets same # */
    word24          fragment_offset;   /* bytes in previous fragments */
    word24          fragment_length;   /* length of this fragment */
} DtlsHandShakeHeader;


enum HandShakeType {
    hello_request        =   0,
    client_hello         =   1,
    server_hello         =   2,
    hello_verify_request =   3,    /* DTLS addition */
    session_ticket       =   4,
    end_of_early_data    =   5,
    hello_retry_request  =   6,
    encrypted_extensions =   8,
    certificate          =  11,
    server_key_exchange  =  12,
    certificate_request  =  13,
    server_hello_done    =  14,
    certificate_verify   =  15,
    client_key_exchange  =  16,
    finished             =  20,
    certificate_status   =  22,
    key_update           =  24,
    change_cipher_hs     =  55,    /* simulate unique handshake type for sanity
                                      checks.  record layer change_cipher
                                      conflicts with handshake finished */
    message_hash         = 254,    /* synthetic message type for TLS v1.3 */
    no_shake             = 255     /* used to initialize the DtlsMsg record */
};

enum ProvisionSide {
    PROVISION_CLIENT = 1,
    PROVISION_SERVER = 2,
    PROVISION_CLIENT_SERVER = 3
};


static const byte client[SIZEOF_SENDER+1] = { 0x43, 0x4C, 0x4E, 0x54, 0x00 }; /* CLNT */
static const byte server[SIZEOF_SENDER+1] = { 0x53, 0x52, 0x56, 0x52, 0x00 }; /* SRVR */

static const byte tls_client[FINISHED_LABEL_SZ + 1] = "client finished";
static const byte tls_server[FINISHED_LABEL_SZ + 1] = "server finished";

#ifdef OPENSSL_EXTRA
typedef struct {
    int name_len;
    const char *name;
    int nid;
} WOLF_EC_NIST_NAME;
extern const WOLF_EC_NIST_NAME kNistCurves[];
/* This is the longest and shortest curve name in the kNistCurves list */
#define kNistCurves_MIN_NAME_LEN 5
#define kNistCurves_MAX_NAME_LEN 7
#endif

/* internal functions */
WOLFSSL_LOCAL int SendChangeCipher(WOLFSSL*);
WOLFSSL_LOCAL int SendTicket(WOLFSSL*);
WOLFSSL_LOCAL int DoClientTicket(WOLFSSL*, const byte*, word32);
WOLFSSL_LOCAL int SendData(WOLFSSL*, const void*, int);
#ifdef WOLFSSL_TLS13
WOLFSSL_LOCAL int SendTls13ServerHello(WOLFSSL*, byte);
#endif
WOLFSSL_LOCAL int SendCertificate(WOLFSSL*);
WOLFSSL_LOCAL int SendCertificateRequest(WOLFSSL*);
#if defined(HAVE_CERTIFICATE_STATUS_REQUEST) \
 || defined(HAVE_CERTIFICATE_STATUS_REQUEST_V2)
WOLFSSL_LOCAL int CreateOcspResponse(WOLFSSL*, OcspRequest**, buffer*);
#endif
#if defined(HAVE_SECURE_RENEGOTIATION) && \
    defined(HAVE_SERVER_RENEGOTIATION_INFO)
WOLFSSL_LOCAL int SendHelloRequest(WOLFSSL*);
#endif
WOLFSSL_LOCAL int SendCertificateStatus(WOLFSSL*);
WOLFSSL_LOCAL int SendServerKeyExchange(WOLFSSL*);
WOLFSSL_LOCAL int SendBuffered(WOLFSSL*);
WOLFSSL_LOCAL int ReceiveData(WOLFSSL*, byte*, int, int);
WOLFSSL_LOCAL int SendFinished(WOLFSSL*);
WOLFSSL_LOCAL int SendAlert(WOLFSSL*, int, int);
WOLFSSL_LOCAL int ProcessReply(WOLFSSL*);

WOLFSSL_LOCAL int SetCipherSpecs(WOLFSSL*);
WOLFSSL_LOCAL int MakeMasterSecret(WOLFSSL*);

WOLFSSL_LOCAL int AddSession(WOLFSSL*);
WOLFSSL_LOCAL int DeriveKeys(WOLFSSL* ssl);
WOLFSSL_LOCAL int StoreKeys(WOLFSSL* ssl, const byte* keyData, int side);

WOLFSSL_LOCAL int IsTLS(const WOLFSSL* ssl);
WOLFSSL_LOCAL int IsAtLeastTLSv1_2(const WOLFSSL* ssl);
WOLFSSL_LOCAL int IsAtLeastTLSv1_3(const ProtocolVersion pv);

WOLFSSL_LOCAL void FreeHandshakeResources(WOLFSSL* ssl);
WOLFSSL_LOCAL void ShrinkInputBuffer(WOLFSSL* ssl, int forcedFree);
WOLFSSL_LOCAL void ShrinkOutputBuffer(WOLFSSL* ssl);

WOLFSSL_LOCAL int VerifyClientSuite(WOLFSSL* ssl);

WOLFSSL_LOCAL int SetTicket(WOLFSSL*, const byte*, word32);
WOLFSSL_LOCAL int wolfSSL_GetMaxRecordSize(WOLFSSL* ssl, int maxFragment);

#if defined(OPENSSL_EXTRA) && defined(HAVE_ECC)
WOLFSSL_LOCAL int SetECKeyInternal(WOLFSSL_EC_KEY* eckey);
WOLFSSL_LOCAL int SetECKeyExternal(WOLFSSL_EC_KEY* eckey);
#endif

WOLFSSL_LOCAL WC_RNG* WOLFSSL_RSA_GetRNG(WOLFSSL_RSA *rsa, WC_RNG **tmpRNG,
                                         int *initTmpRng);

#ifndef NO_CERTS
    #ifndef NO_RSA
        #ifdef WC_RSA_PSS
            WOLFSSL_LOCAL int CheckRsaPssPadding(const byte* plain, word32 plainSz,
                byte* out, word32 sigSz, enum wc_HashType hashType);
            WOLFSSL_LOCAL int ConvertHashPss(int hashAlgo,
                enum wc_HashType* hashType, int* mgf);
        #endif
        WOLFSSL_LOCAL int VerifyRsaSign(WOLFSSL* ssl, byte* verifySig,
            word32 sigSz, const byte* plain, word32 plainSz, int sigAlgo,
            int hashAlgo, RsaKey* key, DerBuffer* keyBufInfo);
        WOLFSSL_LOCAL int RsaSign(WOLFSSL* ssl, const byte* in, word32 inSz,
            byte* out, word32* outSz, int sigAlgo, int hashAlgo, RsaKey* key,
            DerBuffer* keyBufInfo);
        WOLFSSL_LOCAL int RsaVerify(WOLFSSL* ssl, byte* in, word32 inSz,
            byte** out, int sigAlgo, int hashAlgo, RsaKey* key,
            buffer* keyBufInfo);
        WOLFSSL_LOCAL int RsaDec(WOLFSSL* ssl, byte* in, word32 inSz, byte** out,
            word32* outSz, RsaKey* key, DerBuffer* keyBufInfo);
        WOLFSSL_LOCAL int RsaEnc(WOLFSSL* ssl, const byte* in, word32 inSz, byte* out,
            word32* outSz, RsaKey* key, buffer* keyBufInfo);
    #endif /* !NO_RSA */

    #ifdef HAVE_ECC
        WOLFSSL_LOCAL int EccSign(WOLFSSL* ssl, const byte* in, word32 inSz,
            byte* out, word32* outSz, ecc_key* key, DerBuffer* keyBufInfo);
        WOLFSSL_LOCAL int EccVerify(WOLFSSL* ssl, const byte* in, word32 inSz,
            const byte* out, word32 outSz, ecc_key* key, buffer* keyBufInfo);
        WOLFSSL_LOCAL int EccSharedSecret(WOLFSSL* ssl, ecc_key* priv_key,
            ecc_key* pub_key, byte* pubKeyDer, word32* pubKeySz, byte* out,
            word32* outlen, int side);
    #endif /* HAVE_ECC */
    #ifdef HAVE_ED25519
        WOLFSSL_LOCAL int Ed25519CheckPubKey(WOLFSSL* ssl);
        WOLFSSL_LOCAL int Ed25519Sign(WOLFSSL* ssl, const byte* in, word32 inSz,
            byte* out, word32* outSz, ed25519_key* key, DerBuffer* keyBufInfo);
        WOLFSSL_LOCAL int Ed25519Verify(WOLFSSL* ssl, const byte* in,
            word32 inSz, const byte* msg, word32 msgSz, ed25519_key* key,
            buffer* keyBufInfo);
    #endif /* HAVE_ED25519 */
    #ifdef HAVE_ED448
        WOLFSSL_LOCAL int Ed448CheckPubKey(WOLFSSL* ssl);
        WOLFSSL_LOCAL int Ed448Sign(WOLFSSL* ssl, const byte* in, word32 inSz,
            byte* out, word32* outSz, ed448_key* key, DerBuffer* keyBufInfo);
        WOLFSSL_LOCAL int Ed448Verify(WOLFSSL* ssl, const byte* in,
            word32 inSz, const byte* msg, word32 msgSz, ed448_key* key,
            buffer* keyBufInfo);
    #endif /* HAVE_ED448 */


    #ifdef WOLFSSL_TRUST_PEER_CERT

        /* options for searching hash table for a matching trusted peer cert */
        #define WC_MATCH_SKID 0
        #define WC_MATCH_NAME 1

        WOLFSSL_LOCAL TrustedPeerCert* GetTrustedPeer(void* vp, byte* hash,
                                                                      int type);
        WOLFSSL_LOCAL int MatchTrustedPeer(TrustedPeerCert* tp,
                                                             DecodedCert* cert);
    #endif

    WOLFSSL_LOCAL Signer* GetCA(void* cm, byte* hash);
    #ifndef NO_SKID
        WOLFSSL_LOCAL Signer* GetCAByName(void* cm, byte* hash);
    #endif
#endif /* !NO_CERTS */
WOLFSSL_LOCAL int  BuildTlsHandshakeHash(WOLFSSL* ssl, byte* hash,
                                   word32* hashLen);
WOLFSSL_LOCAL int  BuildTlsFinished(WOLFSSL* ssl, Hashes* hashes,
                                   const byte* sender);
WOLFSSL_LOCAL void FreeArrays(WOLFSSL* ssl, int keep);
WOLFSSL_LOCAL  int CheckAvailableSize(WOLFSSL *ssl, int size);
WOLFSSL_LOCAL  int GrowInputBuffer(WOLFSSL* ssl, int size, int usedLength);

#ifndef NO_TLS
    WOLFSSL_LOCAL int  MakeTlsMasterSecret(WOLFSSL*);
#ifndef WOLFSSL_AEAD_ONLY
    WOLFSSL_LOCAL int  TLS_hmac(WOLFSSL* ssl, byte* digest, const byte* in,
                                word32 sz, int padSz, int content, int verify, int epochOrder);
#endif
#endif

#ifndef NO_WOLFSSL_CLIENT
    WOLFSSL_LOCAL int SendClientHello(WOLFSSL*);
    #ifdef WOLFSSL_TLS13
    WOLFSSL_LOCAL int SendTls13ClientHello(WOLFSSL*);
    #endif
    WOLFSSL_LOCAL int SendClientKeyExchange(WOLFSSL*);
    WOLFSSL_LOCAL int SendCertificateVerify(WOLFSSL*);
#endif /* NO_WOLFSSL_CLIENT */

#ifndef NO_WOLFSSL_SERVER
    WOLFSSL_LOCAL int SendServerHello(WOLFSSL*);
    WOLFSSL_LOCAL int SendServerHelloDone(WOLFSSL*);
#endif /* NO_WOLFSSL_SERVER */

#ifdef WOLFSSL_DTLS
    WOLFSSL_LOCAL DtlsMsg* DtlsMsgNew(word32, void*);
    WOLFSSL_LOCAL void DtlsMsgDelete(DtlsMsg*, void*);
    WOLFSSL_LOCAL void DtlsMsgListDelete(DtlsMsg*, void*);
    WOLFSSL_LOCAL void DtlsTxMsgListClean(WOLFSSL* ssl);
    WOLFSSL_LOCAL int  DtlsMsgSet(DtlsMsg*, word32, word16, const byte*, byte,
                                                       word32, word32, void*);
    WOLFSSL_LOCAL DtlsMsg* DtlsMsgFind(DtlsMsg*, word32, word32);
    WOLFSSL_LOCAL void DtlsMsgStore(WOLFSSL*, word32, word32, const byte*, word32,
                                                byte, word32, word32, void*);
    WOLFSSL_LOCAL DtlsMsg* DtlsMsgInsert(DtlsMsg*, DtlsMsg*);

    WOLFSSL_LOCAL int  DtlsMsgPoolSave(WOLFSSL*, const byte*, word32, enum HandShakeType);
    WOLFSSL_LOCAL int  DtlsMsgPoolTimeout(WOLFSSL*);
    WOLFSSL_LOCAL int  VerifyForDtlsMsgPoolSend(WOLFSSL*, byte, word32);
    WOLFSSL_LOCAL int  VerifyForTxDtlsMsgDelete(WOLFSSL* ssl, DtlsMsg* head);
    WOLFSSL_LOCAL void DtlsMsgPoolReset(WOLFSSL*);
    WOLFSSL_LOCAL int  DtlsMsgPoolSend(WOLFSSL*, int);
#endif /* WOLFSSL_DTLS */

#if defined(HAVE_SECURE_RENEGOTIATION) && defined(WOLFSSL_DTLS)
    WOLFSSL_LOCAL int DtlsSCRKeysSet(WOLFSSL* ssl);
    WOLFSSL_LOCAL int IsDtlsMsgSCRKeys(WOLFSSL* ssl);
    WOLFSSL_LOCAL int DtlsUseSCRKeys(WOLFSSL* ssl);
    WOLFSSL_LOCAL int DtlsCheckOrder(WOLFSSL* ssl, int order);
#endif

    WOLFSSL_LOCAL void WriteSEQ(WOLFSSL* ssl, int verifyOrder, byte* out);

#if defined(WOLFSSL_TLS13) && (defined(HAVE_SESSION_TICKET) || !defined(NO_PSK))
    WOLFSSL_LOCAL word32 TimeNowInMilliseconds(void);
#endif
WOLFSSL_LOCAL word32  LowResTimer(void);

#ifndef NO_CERTS
    WOLFSSL_LOCAL void InitX509Name(WOLFSSL_X509_NAME*, int, void*);
    WOLFSSL_LOCAL void FreeX509Name(WOLFSSL_X509_NAME* name);
    WOLFSSL_LOCAL void InitX509(WOLFSSL_X509*, int, void* heap);
    WOLFSSL_LOCAL void FreeX509(WOLFSSL_X509*);
    WOLFSSL_LOCAL int  CopyDecodedToX509(WOLFSSL_X509*, DecodedCert*);
#endif

#ifndef MAX_CIPHER_NAME
#define MAX_CIPHER_NAME 50
#endif

#ifdef WOLFSSL_NAMES_STATIC
typedef char cipher_name[MAX_CIPHER_NAME];
#else
typedef const char* cipher_name;
#endif

typedef struct CipherSuiteInfo {
    cipher_name name;
#ifndef NO_ERROR_STRINGS
    cipher_name name_iana;
#endif
    byte cipherSuite0;
    byte cipherSuite;
#if defined(OPENSSL_ALL) || defined(WOLFSSL_QT)
    byte minor;
    byte major;
#endif
} CipherSuiteInfo;

WOLFSSL_LOCAL const CipherSuiteInfo* GetCipherNames(void);
WOLFSSL_LOCAL int GetCipherNamesSize(void);
WOLFSSL_LOCAL const char* GetCipherNameInternal(const byte cipherSuite0, const byte cipherSuite);
#if defined(OPENSSL_ALL) || defined(WOLFSSL_QT)
/* used in wolfSSL_sk_CIPHER_description */
#define MAX_SEGMENTS    5
#define MAX_SEGMENT_SZ 20
WOLFSSL_LOCAL int wolfSSL_sk_CIPHER_description(WOLFSSL_CIPHER*);
WOLFSSL_LOCAL const char* GetCipherProtocol(const byte minor);
WOLFSSL_LOCAL const char* GetCipherKeaStr(char n[][MAX_SEGMENT_SZ]);
WOLFSSL_LOCAL const char* GetCipherAuthStr(char n[][MAX_SEGMENT_SZ]);
WOLFSSL_LOCAL const char* GetCipherEncStr(char n[][MAX_SEGMENT_SZ]);
WOLFSSL_LOCAL const char* GetCipherMacStr(char n[][MAX_SEGMENT_SZ]);
WOLFSSL_LOCAL int SetCipherBits(const char* enc);
#endif
WOLFSSL_LOCAL const char* GetCipherNameIana(const byte cipherSuite0, const byte cipherSuite);
WOLFSSL_LOCAL const char* wolfSSL_get_cipher_name_internal(WOLFSSL* ssl);
WOLFSSL_LOCAL const char* wolfSSL_get_cipher_name_iana(WOLFSSL* ssl);
WOLFSSL_LOCAL int GetCipherSuiteFromName(const char* name, byte* cipherSuite0,
                                         byte* cipherSuite);

enum encrypt_side {
    ENCRYPT_SIDE_ONLY = 1,
    DECRYPT_SIDE_ONLY,
    ENCRYPT_AND_DECRYPT_SIDE
};

WOLFSSL_LOCAL int SetKeysSide(WOLFSSL*, enum encrypt_side);

/* Set*Internal and Set*External functions */
WOLFSSL_LOCAL int SetDsaInternal(WOLFSSL_DSA* dsa);
WOLFSSL_LOCAL int SetDsaExternal(WOLFSSL_DSA* dsa);
#ifndef HAVE_USER_RSA
WOLFSSL_LOCAL int SetRsaExternal(WOLFSSL_RSA* rsa);
WOLFSSL_LOCAL int SetRsaInternal(WOLFSSL_RSA* rsa);
#endif
WOLFSSL_LOCAL int SetDhInternal(WOLFSSL_DH* dh);
WOLFSSL_LOCAL int SetDhExternal(WOLFSSL_DH *dh);

#ifndef NO_DH
    WOLFSSL_LOCAL int DhGenKeyPair(WOLFSSL* ssl, DhKey* dhKey,
        byte* priv, word32* privSz,
        byte* pub, word32* pubSz);
    WOLFSSL_LOCAL int DhAgree(WOLFSSL* ssl, DhKey* dhKey,
        const byte* priv, word32 privSz,
        const byte* otherPub, word32 otherPubSz,
        byte* agree, word32* agreeSz);
#endif /* !NO_DH */

#ifdef HAVE_ECC
    WOLFSSL_LOCAL int EccMakeKey(WOLFSSL* ssl, ecc_key* key, ecc_key* peer);
    WOLFSSL_LOCAL word16 GetCurveByOID(int oidSum);
#endif

WOLFSSL_LOCAL int InitHandshakeHashes(WOLFSSL* ssl);
WOLFSSL_LOCAL void FreeHandshakeHashes(WOLFSSL* ssl);


#ifndef WOLFSSL_NO_TLS12
WOLFSSL_LOCAL void FreeBuildMsgArgs(WOLFSSL* ssl, BuildMsgArgs* args);
#endif
WOLFSSL_LOCAL int BuildMessage(WOLFSSL* ssl, byte* output, int outSz,
                        const byte* input, int inSz, int type, int hashOutput,
                        int sizeOnly, int asyncOkay, int epochOrder);

#ifdef WOLFSSL_TLS13
int BuildTls13Message(WOLFSSL* ssl, byte* output, int outSz, const byte* input,
               int inSz, int type, int hashOutput, int sizeOnly, int asyncOkay);
#endif

WOLFSSL_LOCAL int AllocKey(WOLFSSL* ssl, int type, void** pKey);
WOLFSSL_LOCAL void FreeKey(WOLFSSL* ssl, int type, void** pKey);

#ifdef WOLFSSL_ASYNC_CRYPT
    WOLFSSL_LOCAL int wolfSSL_AsyncInit(WOLFSSL* ssl, WC_ASYNC_DEV* asyncDev, word32 flags);
    WOLFSSL_LOCAL int wolfSSL_AsyncPop(WOLFSSL* ssl, byte* state);
    WOLFSSL_LOCAL int wolfSSL_AsyncPush(WOLFSSL* ssl, WC_ASYNC_DEV* asyncDev);
#endif


#ifdef __cplusplus
    }  /* extern "C" */
#endif

#endif /* wolfSSL_INT_H */
