/* internal.h
 *
 * Copyright (C) 2006-2015 wolfSSL Inc.
 *
 * This file is part of wolfSSL. (formerly known as wolfSSL)
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
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301, USA
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
#ifdef HAVE_ECC
    #include <wolfssl/wolfcrypt/ecc.h>
#endif
#ifndef NO_SHA256
    #include <wolfssl/wolfcrypt/sha256.h>
#endif
#ifdef HAVE_OCSP
    #include <wolfssl/ocsp.h>
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

#include <wolfssl/wolfcrypt/hash.h>

#ifdef WOLFSSL_CALLBACKS
    #include <wolfssl/callbacks.h>
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
#elif defined(MICRIUM)
    /* do nothing, just don't pick Unix */
#elif defined(FREERTOS) || defined(WOLFSSL_SAFERTOS)
    /* do nothing */
#elif defined(EBSNET)
    /* do nothing */
#elif defined(FREESCALE_MQX)
    /* do nothing */
#elif defined(WOLFSSL_MDK_ARM)
    #if defined(WOLFSSL_MDK5)
         #include "cmsis_os.h"
    #else
        #include <rtl.h>
    #endif
#elif defined(MBED)
#elif defined(WOLFSSL_TIRTOS)
    /* do nothing */
#else
    #ifndef SINGLE_THREADED
        #define WOLFSSL_PTHREADS
        #include <pthread.h>
    #endif
    #if defined(OPENSSL_EXTRA) || defined(GOAHEAD_WS)
        #include <unistd.h>      /* for close of BIO */
    #endif
#endif


#ifdef HAVE_LIBZ
    #include "zlib.h"
#endif

#ifdef _MSC_VER
    /* 4996 warning to use MS extensions e.g., strcpy_s instead of strncpy */
    #pragma warning(disable: 4996)
#endif

#ifdef NO_AES
    #if !defined (ALIGN16)
        #define ALIGN16
    #endif
#endif

#ifdef NO_SHA
    #define SHA_DIGEST_SIZE 20
#endif

#ifdef NO_SHA256
    #define SHA256_DIGEST_SIZE 32
#endif

#ifdef NO_MD5
    #define MD5_DIGEST_SIZE 16
#endif


#ifdef __cplusplus
    extern "C" {
#endif


#ifdef USE_WINDOWS_API
    typedef unsigned int SOCKET_T;
#else
    typedef int SOCKET_T;
#endif


typedef byte word24[3];

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

#ifndef WOLFSSL_MAX_STRENGTH

    #if !defined(NO_RSA) && !defined(NO_RC4)
        #if !defined(NO_SHA)
            #define BUILD_SSL_RSA_WITH_RC4_128_SHA
        #endif
        #if !defined(NO_MD5)
            #define BUILD_SSL_RSA_WITH_RC4_128_MD5
        #endif
        #if !defined(NO_TLS) && defined(HAVE_NTRU) && !defined(NO_SHA)
            #define BUILD_TLS_NTRU_RSA_WITH_RC4_128_SHA
        #endif
    #endif

    #if !defined(NO_RSA) && !defined(NO_DES3)
        #if !defined(NO_SHA)
            #define BUILD_SSL_RSA_WITH_3DES_EDE_CBC_SHA
            #if !defined(NO_TLS) && defined(HAVE_NTRU)
                    #define BUILD_TLS_NTRU_RSA_WITH_3DES_EDE_CBC_SHA
            #endif
        #endif
    #endif

    #if !defined(NO_RSA) && !defined(NO_AES) && !defined(NO_TLS)
        #if !defined(NO_SHA)
            #define BUILD_TLS_RSA_WITH_AES_128_CBC_SHA
            #define BUILD_TLS_RSA_WITH_AES_256_CBC_SHA
            #if defined(HAVE_NTRU)
                    #define BUILD_TLS_NTRU_RSA_WITH_AES_128_CBC_SHA
                    #define BUILD_TLS_NTRU_RSA_WITH_AES_256_CBC_SHA
            #endif
        #endif
        #if !defined (NO_SHA256)
            #define BUILD_TLS_RSA_WITH_AES_128_CBC_SHA256
            #define BUILD_TLS_RSA_WITH_AES_256_CBC_SHA256
        #endif
        #if defined (HAVE_AESGCM)
            #define BUILD_TLS_RSA_WITH_AES_128_GCM_SHA256
            #if defined (WOLFSSL_SHA384)
                #define BUILD_TLS_RSA_WITH_AES_256_GCM_SHA384
            #endif
        #endif
        #if defined (HAVE_AESCCM)
            #define BUILD_TLS_RSA_WITH_AES_128_CCM_8
            #define BUILD_TLS_RSA_WITH_AES_256_CCM_8
        #endif
        #if defined(HAVE_BLAKE2)
            #define BUILD_TLS_RSA_WITH_AES_128_CBC_B2B256
            #define BUILD_TLS_RSA_WITH_AES_256_CBC_B2B256
        #endif
    #endif

    #if defined(HAVE_CAMELLIA) && !defined(NO_TLS)
        #ifndef NO_RSA
          #if !defined(NO_SHA)
            #define BUILD_TLS_RSA_WITH_CAMELLIA_128_CBC_SHA
            #define BUILD_TLS_RSA_WITH_CAMELLIA_256_CBC_SHA
          #endif
            #ifndef NO_SHA256
                #define BUILD_TLS_RSA_WITH_CAMELLIA_128_CBC_SHA256
                #define BUILD_TLS_RSA_WITH_CAMELLIA_256_CBC_SHA256
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

    #if !defined(NO_PSK) && !defined(NO_AES) && !defined(NO_TLS)
        #if !defined(NO_SHA)
            #define BUILD_TLS_PSK_WITH_AES_128_CBC_SHA
            #define BUILD_TLS_PSK_WITH_AES_256_CBC_SHA
        #endif
        #ifndef NO_SHA256
            #define BUILD_TLS_PSK_WITH_AES_128_CBC_SHA256
            #ifdef HAVE_AESGCM
                #define BUILD_TLS_PSK_WITH_AES_128_GCM_SHA256
            #endif
            #ifdef HAVE_AESCCM
                #define BUILD_TLS_PSK_WITH_AES_128_CCM_8
                #define BUILD_TLS_PSK_WITH_AES_256_CCM_8
                #define BUILD_TLS_PSK_WITH_AES_128_CCM
                #define BUILD_TLS_PSK_WITH_AES_256_CCM
            #endif
        #endif
        #ifdef WOLFSSL_SHA384
            #define BUILD_TLS_PSK_WITH_AES_256_CBC_SHA384
            #ifdef HAVE_AESGCM
                #define BUILD_TLS_PSK_WITH_AES_256_GCM_SHA384
            #endif
        #endif
    #endif

    #if !defined(NO_TLS) && defined(HAVE_NULL_CIPHER)
        #if !defined(NO_RSA)
            #if !defined(NO_SHA)
                #define BUILD_TLS_RSA_WITH_NULL_SHA
            #endif
            #ifndef NO_SHA256
                #define BUILD_TLS_RSA_WITH_NULL_SHA256
            #endif
        #endif
        #if !defined(NO_PSK)
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

    #if !defined(NO_HC128) && !defined(NO_RSA) && !defined(NO_TLS)
        #define BUILD_TLS_RSA_WITH_HC_128_MD5
        #if !defined(NO_SHA)
            #define BUILD_TLS_RSA_WITH_HC_128_SHA
        #endif
        #if defined(HAVE_BLAKE2)
            #define BUILD_TLS_RSA_WITH_HC_128_B2B256
        #endif
    #endif

    #if !defined(NO_RABBIT) && !defined(NO_TLS) && !defined(NO_RSA)
        #if !defined(NO_SHA)
            #define BUILD_TLS_RSA_WITH_RABBIT_SHA
        #endif
    #endif

    #if !defined(NO_DH) && !defined(NO_AES) && !defined(NO_TLS) && \
        !defined(NO_RSA)

        #if !defined(NO_SHA)
            #define BUILD_TLS_DHE_RSA_WITH_AES_128_CBC_SHA
            #define BUILD_TLS_DHE_RSA_WITH_AES_256_CBC_SHA
        #endif
        #if !defined(NO_SHA256)
            #define BUILD_TLS_DHE_RSA_WITH_AES_128_CBC_SHA256
            #define BUILD_TLS_DHE_RSA_WITH_AES_256_CBC_SHA256
        #endif
    #endif

    #if defined(HAVE_ANON) && !defined(NO_TLS) && !defined(NO_DH) && \
        !defined(NO_AES) && !defined(NO_SHA)
        #define BUILD_TLS_DH_anon_WITH_AES_128_CBC_SHA
    #endif

    #if !defined(NO_DH) && !defined(NO_PSK) && !defined(NO_TLS)
        #ifndef NO_SHA256
            #define BUILD_TLS_DHE_PSK_WITH_AES_128_CBC_SHA256
            #ifdef HAVE_NULL_CIPHER
                #define BUILD_TLS_DHE_PSK_WITH_NULL_SHA256
            #endif
        #endif
        #ifdef WOLFSSL_SHA384
            #define BUILD_TLS_DHE_PSK_WITH_AES_256_CBC_SHA384
            #ifdef HAVE_NULL_CIPHER
                #define BUILD_TLS_DHE_PSK_WITH_NULL_SHA384
            #endif
        #endif
    #endif

    #if defined(HAVE_ECC) && !defined(NO_TLS)
        #if !defined(NO_AES)
            #if !defined(NO_SHA)
                #if !defined(NO_RSA)
                    #define BUILD_TLS_ECDHE_RSA_WITH_AES_128_CBC_SHA
                    #define BUILD_TLS_ECDHE_RSA_WITH_AES_256_CBC_SHA
                    #define BUILD_TLS_ECDH_RSA_WITH_AES_128_CBC_SHA
                    #define BUILD_TLS_ECDH_RSA_WITH_AES_256_CBC_SHA
                #endif

                #define BUILD_TLS_ECDHE_ECDSA_WITH_AES_128_CBC_SHA
                #define BUILD_TLS_ECDHE_ECDSA_WITH_AES_256_CBC_SHA

                #define BUILD_TLS_ECDH_ECDSA_WITH_AES_128_CBC_SHA
                #define BUILD_TLS_ECDH_ECDSA_WITH_AES_256_CBC_SHA
            #endif /* NO_SHA */
            #ifndef NO_SHA256
                #if !defined(NO_RSA)
                    #define BUILD_TLS_ECDHE_RSA_WITH_AES_128_CBC_SHA256
                    #define BUILD_TLS_ECDH_RSA_WITH_AES_128_CBC_SHA256
                #endif
                #define BUILD_TLS_ECDHE_ECDSA_WITH_AES_128_CBC_SHA256
                #define BUILD_TLS_ECDH_ECDSA_WITH_AES_128_CBC_SHA256
            #endif

            #ifdef WOLFSSL_SHA384
                #if !defined(NO_RSA)
                    #define BUILD_TLS_ECDHE_RSA_WITH_AES_256_CBC_SHA384
                    #define BUILD_TLS_ECDH_RSA_WITH_AES_256_CBC_SHA384
                #endif
                #define BUILD_TLS_ECDHE_ECDSA_WITH_AES_256_CBC_SHA384
                #define BUILD_TLS_ECDH_ECDSA_WITH_AES_256_CBC_SHA384
            #endif

            #if defined (HAVE_AESGCM)
                #if !defined(NO_RSA)
                    #define BUILD_TLS_ECDH_RSA_WITH_AES_128_GCM_SHA256
                    #if defined(WOLFSSL_SHA384)
                        #define BUILD_TLS_ECDH_RSA_WITH_AES_256_GCM_SHA384
                    #endif
                #endif

                #define BUILD_TLS_ECDH_ECDSA_WITH_AES_128_GCM_SHA256

                #if defined(WOLFSSL_SHA384)
                    #define BUILD_TLS_ECDH_ECDSA_WITH_AES_256_GCM_SHA384
                #endif
            #endif
        #endif /* NO_AES */
        #if !defined(NO_RC4)
            #if !defined(NO_SHA)
                #if !defined(NO_RSA)
                    #define BUILD_TLS_ECDHE_RSA_WITH_RC4_128_SHA
                    #define BUILD_TLS_ECDH_RSA_WITH_RC4_128_SHA
                #endif

                #define BUILD_TLS_ECDHE_ECDSA_WITH_RC4_128_SHA
                #define BUILD_TLS_ECDH_ECDSA_WITH_RC4_128_SHA
            #endif
        #endif
        #if !defined(NO_DES3)
            #ifndef NO_SHA
                #if !defined(NO_RSA)
                    #define BUILD_TLS_ECDHE_RSA_WITH_3DES_EDE_CBC_SHA
                    #define BUILD_TLS_ECDH_RSA_WITH_3DES_EDE_CBC_SHA
                #endif

                #define BUILD_TLS_ECDHE_ECDSA_WITH_3DES_EDE_CBC_SHA
                #define BUILD_TLS_ECDH_ECDSA_WITH_3DES_EDE_CBC_SHA
            #endif /* NO_SHA */
        #endif
    #endif

#endif /* !WOLFSSL_MAX_STRENGTH */

#if !defined(NO_DH) && !defined(NO_AES) && !defined(NO_TLS) && \
    !defined(NO_RSA) && defined(HAVE_AESGCM)

    #ifndef NO_SHA256
        #define BUILD_TLS_DHE_RSA_WITH_AES_128_GCM_SHA256
    #endif

    #ifdef WOLFSSL_SHA384
        #define BUILD_TLS_DHE_RSA_WITH_AES_256_GCM_SHA384
    #endif
#endif

#if !defined(NO_DH) && !defined(NO_PSK) && !defined(NO_TLS)
    #ifndef NO_SHA256
        #ifdef HAVE_AESGCM
            #define BUILD_TLS_DHE_PSK_WITH_AES_128_GCM_SHA256
        #endif
        #ifdef HAVE_AESCCM
            #define BUILD_TLS_DHE_PSK_WITH_AES_128_CCM
            #define BUILD_TLS_DHE_PSK_WITH_AES_256_CCM
        #endif
    #endif
    #if defined(WOLFSSL_SHA384) && defined(HAVE_AESGCM)
        #define BUILD_TLS_DHE_PSK_WITH_AES_256_GCM_SHA384
    #endif
#endif

#if defined(HAVE_ECC) && !defined(NO_TLS) && !defined(NO_AES)
    #ifdef HAVE_AESGCM
        #ifndef NO_SHA256
            #define BUILD_TLS_ECDHE_ECDSA_WITH_AES_128_GCM_SHA256
            #ifndef NO_RSA
                #define BUILD_TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256
            #endif
        #endif
        #ifdef WOLFSSL_SHA384
            #define BUILD_TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384
            #ifndef NO_RSA
                #define BUILD_TLS_ECDHE_RSA_WITH_AES_256_GCM_SHA384
            #endif
        #endif
    #endif
    #if defined(HAVE_AESCCM) && !defined(NO_SHA256)
        #define BUILD_TLS_ECDHE_ECDSA_WITH_AES_128_CCM_8
        #define BUILD_TLS_ECDHE_ECDSA_WITH_AES_256_CCM_8
    #endif
#endif

#if defined(HAVE_CHACHA) && defined(HAVE_POLY1305) && !defined(NO_SHA256)
    #ifdef HAVE_ECC
        #define BUILD_TLS_ECDHE_ECDSA_WITH_CHACHA20_POLY1305_SHA256
        #ifndef NO_RSA
            #define BUILD_TLS_ECDHE_RSA_WITH_CHACHA20_POLY1305_SHA256
        #endif
    #endif
    #if !defined(NO_DH) && !defined(NO_RSA)
        #define BUILD_TLS_DHE_RSA_WITH_CHACHA20_POLY1305_SHA256
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
    defined(BUILD_TLS_ECDHE_ECDSA_WITH_AES_128_GCM_SHA256)
    #undef  BUILD_AES
    #define BUILD_AES
#endif

#if defined(BUILD_TLS_RSA_WITH_AES_128_GCM_SHA256) || \
    defined(BUILD_TLS_DHE_RSA_WITH_AES_128_GCM_SHA256) || \
    defined(BUILD_TLS_ECDHE_ECDSA_WITH_AES_128_GCM_SHA256) || \
    defined(BUILD_TLS_PSK_WITH_AES_128_GCM_SHA256)
    #define BUILD_AESGCM
#endif

#if defined(BUILD_TLS_RSA_WITH_HC_128_SHA) || \
    defined(BUILD_TLS_RSA_WITH_HC_128_MD5) || \
    defined(BUILD_TLS_RSA_WITH_HC_128_B2B256)
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

#ifdef NO_AES
    #define AES_BLOCK_SIZE 16
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
    defined(HAVE_AESGCM) || defined(HAVE_AESCCM) || \
    (defined(HAVE_CHACHA) && defined(HAVE_POLY1305))

    #define HAVE_AEAD
#endif

#if defined(WOLFSSL_MAX_STRENGTH) || \
    defined(HAVE_ECC) || !defined(NO_DH)

    #define HAVE_PFS
#endif


/* actual cipher values, 2nd byte */
enum {
    TLS_DHE_RSA_WITH_AES_256_CBC_SHA  = 0x39,
    TLS_DHE_RSA_WITH_AES_128_CBC_SHA  = 0x33,
    TLS_DH_anon_WITH_AES_128_CBC_SHA  = 0x34,
    TLS_RSA_WITH_AES_256_CBC_SHA      = 0x35,
    TLS_RSA_WITH_AES_128_CBC_SHA      = 0x2F,
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

    /* wolfSSL extension - Blake2b 256 */
    TLS_RSA_WITH_AES_128_CBC_B2B256   = 0xF8,
    TLS_RSA_WITH_AES_256_CBC_B2B256   = 0xF9,
    TLS_RSA_WITH_HC_128_B2B256        = 0xFA,   /* eSTREAM too */

    /* wolfSSL extension - NTRU */
    TLS_NTRU_RSA_WITH_RC4_128_SHA      = 0xe5,
    TLS_NTRU_RSA_WITH_3DES_EDE_CBC_SHA = 0xe6,
    TLS_NTRU_RSA_WITH_AES_128_CBC_SHA  = 0xe7,  /* clashes w/official SHA-256 */
    TLS_NTRU_RSA_WITH_AES_256_CBC_SHA  = 0xe8,

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

    TLS_ECDHE_RSA_WITH_CHACHA20_POLY1305_SHA256   = 0x13,
    TLS_ECDHE_ECDSA_WITH_CHACHA20_POLY1305_SHA256 = 0x14,
    TLS_DHE_RSA_WITH_CHACHA20_POLY1305_SHA256     = 0x15,

    /* Renegotiation Indication Extension Special Suite */
    TLS_EMPTY_RENEGOTIATION_INFO_SCSV        = 0xff
};


#ifndef WOLFSSL_SESSION_TIMEOUT
    #define WOLFSSL_SESSION_TIMEOUT 500
    /* default session resumption cache timeout in seconds */
#endif


enum Misc {
    ECC_BYTE    =  0xC0,           /* ECC first cipher suite byte */
    CHACHA_BYTE = 0xCC,            /* ChaCha first cipher suite */

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
    OLD_HELLO_ID    = 0x01,     /* SSLv2 Client Hello Indicator */
    INVALID_BYTE    = 0xff,     /* Used to initialize cipher specs values */
    NO_COMPRESSION  =  0,
    ZLIB_COMPRESSION = 221,     /* wolfSSL zlib compression */
    HELLO_EXT_SIG_ALGO = 13,    /* ID for the sig_algo hello extension */
    SECRET_LEN      = 48,       /* pre RSA and all master */
    ENCRYPT_LEN     = 512,      /* allow 4096 bit static buffer */
    SIZEOF_SENDER   =  4,       /* clnt or srvr           */
    FINISHED_SZ     = 36,       /* MD5_DIGEST_SIZE + SHA_DIGEST_SIZE */
    MAX_RECORD_SIZE = 16384,    /* 2^14, max size by standard */
    MAX_MSG_EXTRA   = 38 + MAX_DIGEST_SIZE,
                                /* max added to msg, mac + pad  from */
                                /* RECORD_HEADER_SZ + BLOCK_SZ (pad) + Max
                                   digest sz + BLOC_SZ (iv) + pad byte (1) */
    MAX_COMP_EXTRA  = 1024,     /* max compression extra */
    MAX_MTU         = 1500,     /* max expected MTU */
    MAX_UDP_SIZE    = 8192 - 100, /* was MAX_MTU - 100 */
    MAX_DH_SZ       = 1036,     /* 4096 p, pub, g + 2 byte size for each */
    MAX_STR_VERSION = 8,        /* string rep of protocol version */

    PAD_MD5        = 48,       /* pad length for finished */
    PAD_SHA        = 40,       /* pad length for finished */
    MAX_PAD_SIZE   = 256,      /* maximum length of padding */
    COMPRESS_DUMMY_SIZE = 64,  /* compression dummy round size */
    COMPRESS_CONSTANT   = 13,  /* compression calc constant */
    COMPRESS_UPPER      = 55,  /* compression calc numerator */
    COMPRESS_LOWER      = 64,  /* compression calc denominator */

    PEM_LINE_LEN   = 80,       /* PEM line max + fudge */
    LENGTH_SZ      =  2,       /* length field for HMAC, data only */
    VERSION_SZ     =  2,       /* length of proctocol version */
    SEQ_SZ         =  8,       /* 64 bit sequence number  */
    BYTE3_LEN      =  3,       /* up to 24 bit byte lengths */
    ALERT_SIZE     =  2,       /* level + description     */
    VERIFY_HEADER  =  2,       /* always use 2 bytes      */
    EXT_ID_SZ      =  2,       /* always use 2 bytes      */
    MAX_DH_SIZE    = 513,      /* 4096 bit plus possible leading 0 */
    SESSION_HINT_SZ = 4,       /* session timeout hint */

    MAX_SUITE_SZ = 200,        /* 100 suites for now! */
    RAN_LEN      = 32,         /* random length           */
    SEED_LEN     = RAN_LEN * 2, /* tls prf seed length    */
    ID_LEN       = 32,         /* session id length       */
    MAX_COOKIE_LEN = 32,       /* max dtls cookie size    */
    COOKIE_SZ    = 20,         /* use a 20 byte cookie    */
    SUITE_LEN    =  2,         /* cipher suite sz length  */
    ENUM_LEN     =  1,         /* always a byte           */
    OPAQUE8_LEN  =  1,         /* 1 byte                  */
    OPAQUE16_LEN =  2,         /* 2 bytes                 */
    OPAQUE24_LEN =  3,         /* 3 bytes                 */
    OPAQUE32_LEN =  4,         /* 4 bytes                 */
    COMP_LEN     =  1,         /* compression length      */
    CURVE_LEN    =  2,         /* ecc named curve length  */
    SERVER_ID_LEN = 20,        /* server session id length  */
    
    HANDSHAKE_HEADER_SZ   = 4,  /* type + length(3)        */
    RECORD_HEADER_SZ      = 5,  /* type + version + len(2) */
    CERT_HEADER_SZ        = 3,  /* always 3 bytes          */
    REQ_HEADER_SZ         = 2,  /* cert request header sz  */
    HINT_LEN_SZ           = 2,  /* length of hint size field */
    TRUNCATED_HMAC_SZ     = 10, /* length of hmac w/ truncated hmac extension */
    HELLO_EXT_TYPE_SZ     = 2,  /* length of a hello extension type */
    HELLO_EXT_SZ          = 8,  /* total length of the lazy hello extensions */
    HELLO_EXT_LEN         = 6,  /* length of the lazy hello extensions */
    HELLO_EXT_SIGALGO_SZ  = 2,  /* length of signature algo extension  */
    HELLO_EXT_SIGALGO_MAX = 32, /* number of items in the signature algo list */

    DTLS_HANDSHAKE_HEADER_SZ = 12, /* normal + seq(2) + offset(3) + length(3) */
    DTLS_RECORD_HEADER_SZ    = 13, /* normal + epoch(2) + seq_num(6) */
    DTLS_HANDSHAKE_EXTRA     = 8,  /* diff from normal */
    DTLS_RECORD_EXTRA        = 8,  /* diff from normal */
    DTLS_HANDSHAKE_SEQ_SZ    = 2,  /* handshake header sequence number */
    DTLS_HANDSHAKE_FRAG_SZ   = 3,  /* fragment offset and length are 24 bit */
    DTLS_POOL_SZ             = 5,  /* buffers to hold in the retry pool */

    FINISHED_LABEL_SZ   = 15,  /* TLS finished label size */
    TLS_FINISHED_SZ     = 12,  /* TLS has a shorter size  */
    MASTER_LABEL_SZ     = 13,  /* TLS master secret label sz */
    KEY_LABEL_SZ        = 13,  /* TLS key block expansion sz */
    MAX_PRF_HALF        = 256, /* Maximum half secret len */
    MAX_PRF_LABSEED     = 128, /* Maximum label + seed len */
    MAX_PRF_DIG         = 224, /* Maximum digest len      */
    MAX_REQUEST_SZ      = 256, /* Maximum cert req len (no auth yet */
    SESSION_FLUSH_COUNT = 256, /* Flush session cache unless user turns off */ 

    RC4_KEY_SIZE        = 16,  /* always 128bit           */
    DES_KEY_SIZE        =  8,  /* des                     */
    DES3_KEY_SIZE       = 24,  /* 3 des ede               */
    DES_IV_SIZE         = DES_BLOCK_SIZE,
    AES_256_KEY_SIZE    = 32,  /* for 256 bit             */
    AES_192_KEY_SIZE    = 24,  /* for 192 bit             */
    AES_IV_SIZE         = 16,  /* always block size       */
    AES_128_KEY_SIZE    = 16,  /* for 128 bit             */

    AEAD_SEQ_OFFSET     = 4,        /* Auth Data: Sequence number */
    AEAD_TYPE_OFFSET    = 8,        /* Auth Data: Type            */
    AEAD_VMAJ_OFFSET    = 9,        /* Auth Data: Major Version   */
    AEAD_VMIN_OFFSET    = 10,       /* Auth Data: Minor Version   */
    AEAD_LEN_OFFSET     = 11,       /* Auth Data: Length          */
    AEAD_AUTH_DATA_SZ   = 13,       /* Size of the data to authenticate */
    AEAD_IMP_IV_SZ      = 4,        /* Size of the implicit IV     */
    AEAD_EXP_IV_SZ      = 8,        /* Size of the explicit IV     */
    AEAD_NONCE_SZ       = AEAD_EXP_IV_SZ + AEAD_IMP_IV_SZ,

    AES_GCM_AUTH_SZ     = 16, /* AES-GCM Auth Tag length    */
    AES_CCM_16_AUTH_SZ  = 16, /* AES-CCM-16 Auth Tag length */
    AES_CCM_8_AUTH_SZ   = 8,  /* AES-CCM-8 Auth Tag Length  */

    CAMELLIA_128_KEY_SIZE = 16, /* for 128 bit */
    CAMELLIA_192_KEY_SIZE = 24, /* for 192 bit */
    CAMELLIA_256_KEY_SIZE = 32, /* for 256 bit */
    CAMELLIA_IV_SIZE      = 16, /* always block size */

    CHACHA20_256_KEY_SIZE = 32,  /* for 256 bit             */
    CHACHA20_128_KEY_SIZE = 16,  /* for 128 bit             */
    CHACHA20_IV_SIZE      =  8,  /* 64 bits for iv          */

    POLY1305_AUTH_SZ    = 16,  /* 128 bits                */

    HC_128_KEY_SIZE     = 16,  /* 128 bits                */
    HC_128_IV_SIZE      = 16,  /* also 128 bits           */

    RABBIT_KEY_SIZE     = 16,  /* 128 bits                */
    RABBIT_IV_SIZE      =  8,  /* 64 bits for iv          */

    EVP_SALT_SIZE       =  8,  /* evp salt size 64 bits   */

    ECDHE_SIZE          = 32,  /* ECHDE server size defaults to 256 bit */
    MAX_EXPORT_ECC_SZ   = 256, /* Export ANS X9.62 max future size */

    MAX_HELLO_SZ       = 128,  /* max client or server hello */
    MAX_CERT_VERIFY_SZ = 1024, /* max   */
    CLIENT_HELLO_FIRST =  35,  /* Protocol + RAN_LEN + sizeof(id_len) */
    MAX_SUITE_NAME     =  48,  /* maximum length of cipher suite string */

    DTLS_TIMEOUT_INIT       =  1, /* default timeout init for DTLS receive  */
    DTLS_TIMEOUT_MAX        = 64, /* default max timeout for DTLS receive */
    DTLS_TIMEOUT_MULTIPLIER =  2, /* default timeout multiplier for DTLS recv */

    MAX_PSK_ID_LEN     = 128,  /* max psk identity/hint supported */
    MAX_PSK_KEY_LEN    =  64,  /* max psk key supported */

    MAX_WOLFSSL_FILE_SIZE = 1024 * 1024 * 4,  /* 4 mb file size alloc limit */

#ifdef FORTRESS
    MAX_EX_DATA        =   3,  /* allow for three items of ex_data */
#endif

    MAX_X509_SIZE      = 2048, /* max static x509 buffer size */
    CERT_MIN_SIZE      =  256, /* min PEM cert size with header/footer */
    MAX_FILENAME_SZ    =  256, /* max file name length */
    FILE_BUFFER_SIZE   = 1024, /* default static file buffer size for input,
                                  will use dynamic buffer if not big enough */

    MAX_NTRU_PUB_KEY_SZ = 1027, /* NTRU max for now */
    MAX_NTRU_ENCRYPT_SZ = 1027, /* NTRU max for now */
    MAX_NTRU_BITS       =  256, /* max symmetric bit strength */
    NO_SNIFF           =   0,  /* not sniffing */
    SNIFF              =   1,  /* currently sniffing */

    HASH_SIG_SIZE      =   2,  /* default SHA1 RSA */

    NO_CAVIUM_DEVICE   =  -2,  /* invalid cavium device id */

    NO_COPY            =   0,  /* should we copy static buffer for write */
    COPY               =   1   /* should we copy static buffer for write */
};


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


#ifdef SESSION_INDEX
/* Shift values for making a session index */
#define SESSIDX_ROW_SHIFT 4
#define SESSIDX_IDX_MASK  0x0F
#endif


/* max cert chain peer depth */
#ifndef MAX_CHAIN_DEPTH
    #define MAX_CHAIN_DEPTH 9
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
    SERVER_HELLO_COMPLETE,
    SERVER_CERT_COMPLETE,
    SERVER_KEYEXCHANGE_COMPLETE,
    SERVER_HELLODONE_COMPLETE,
    SERVER_FINISHED_COMPLETE,

    CLIENT_HELLO_COMPLETE,
    CLIENT_KEYEXCHANGE_COMPLETE,
    CLIENT_FINISHED_COMPLETE,

    HANDSHAKE_DONE
};


#if defined(__GNUC__)
    #define WOLFSSL_PACK __attribute__ ((packed))
#else
    #define WOLFSSL_PACK
#endif

/* SSL Version */
typedef struct ProtocolVersion {
    byte major;
    byte minor;
} WOLFSSL_PACK ProtocolVersion;


WOLFSSL_LOCAL ProtocolVersion MakeSSLv3(void);
WOLFSSL_LOCAL ProtocolVersion MakeTLSv1(void);
WOLFSSL_LOCAL ProtocolVersion MakeTLSv1_1(void);
WOLFSSL_LOCAL ProtocolVersion MakeTLSv1_2(void);

#ifdef WOLFSSL_DTLS
    WOLFSSL_LOCAL ProtocolVersion MakeDTLSv1(void);
    WOLFSSL_LOCAL ProtocolVersion MakeDTLSv1_2(void);
#endif


enum BIO_TYPE {
    BIO_BUFFER = 1,
    BIO_SOCKET = 2,
    BIO_SSL    = 3,
    BIO_MEMORY = 4
};


/* wolfSSL BIO_METHOD type */
struct WOLFSSL_BIO_METHOD {
    byte type;               /* method type */
};


/* wolfSSL BIO type */
struct WOLFSSL_BIO {
    byte        type;          /* method type */
    byte        close;         /* close flag */
    byte        eof;           /* eof flag */
    WOLFSSL*     ssl;           /* possible associated ssl */
    byte*       mem;           /* memory buffer */
    int         memLen;        /* memory buffer length */
    int         fd;            /* possible file descriptor */
    WOLFSSL_BIO* prev;          /* previous in chain */
    WOLFSSL_BIO* next;          /* next in chain */
};


/* wolfSSL method type */
struct WOLFSSL_METHOD {
    ProtocolVersion version;
    byte            side;         /* connection side, server or client */
    byte            downgrade;    /* whether to downgrade version, default no */
};


/* defautls to client */
WOLFSSL_LOCAL void InitSSL_Method(WOLFSSL_METHOD*, ProtocolVersion);

/* for sniffer */
WOLFSSL_LOCAL int DoFinished(WOLFSSL* ssl, const byte* input, word32* inOutIdx,
                            word32 size, word32 totalSz, int sniff);
WOLFSSL_LOCAL int DoApplicationData(WOLFSSL* ssl, byte* input, word32* inOutIdx);


/* wolfSSL buffer type */
typedef struct buffer {
    byte*  buffer;
    word32 length;
} buffer;


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
   write in static buffer chuncks  */
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
typedef struct Suites {
    word16 suiteSz;                 /* suite length in bytes        */
    word16 hashSigAlgoSz;           /* SigAlgo extension length in bytes */
    byte   suites[MAX_SUITE_SZ];
    byte   hashSigAlgo[HELLO_EXT_SIGALGO_MAX]; /* sig/algo to offer */
    byte   setSuites;               /* user set suites from default */
    byte   hashAlgo;                /* selected hash algorithm */
    byte   sigAlgo;                 /* selected sig algorithm */
} Suites;


WOLFSSL_LOCAL
void InitSuites(Suites*, ProtocolVersion, word16, word16, word16, word16,
                word16, word16, int);
WOLFSSL_LOCAL
int  SetCipherList(Suites*, const char* list);

#ifndef PSK_TYPES_DEFINED
    typedef unsigned int (*psk_client_callback)(WOLFSSL*, const char*, char*,
                          unsigned int, unsigned char*, unsigned int);
    typedef unsigned int (*psk_server_callback)(WOLFSSL*, const char*,
                          unsigned char*, unsigned int);
#endif /* PSK_TYPES_DEFINED */


#ifdef HAVE_NETX
    WOLFSSL_LOCAL int NetX_Receive(WOLFSSL *ssl, char *buf, int sz, void *ctx);
    WOLFSSL_LOCAL int NetX_Send(WOLFSSL *ssl, char *buf, int sz, void *ctx);
#endif /* HAVE_NETX */


/* wolfSSL Cipher type just points back to SSL */
struct WOLFSSL_CIPHER {
    WOLFSSL* ssl;
};


typedef struct OCSP_Entry OCSP_Entry;

#ifdef NO_SHA
    #define OCSP_DIGEST_SIZE SHA256_DIGEST_SIZE
#else
    #define OCSP_DIGEST_SIZE SHA_DIGEST_SIZE
#endif

#ifdef NO_ASN 
    /* no_asn won't have */
    typedef struct CertStatus CertStatus;
#endif

struct OCSP_Entry {
    OCSP_Entry* next;                        /* next entry             */
    byte    issuerHash[OCSP_DIGEST_SIZE];    /* issuer hash            */ 
    byte    issuerKeyHash[OCSP_DIGEST_SIZE]; /* issuer public key hash */
    CertStatus* status;                      /* OCSP response list     */
    int         totalStatus;                 /* number on list         */
};


#ifndef HAVE_OCSP
    typedef struct WOLFSSL_OCSP WOLFSSL_OCSP;
#endif

/* wolfSSL OCSP controller */
struct WOLFSSL_OCSP {
    WOLFSSL_CERT_MANAGER* cm;            /* pointer back to cert manager */
    OCSP_Entry*          ocspList;      /* OCSP response list */
    wolfSSL_Mutex         ocspLock;      /* OCSP list lock */
};

#ifndef MAX_DATE_SIZE
#define MAX_DATE_SIZE 32
#endif

typedef struct CRL_Entry CRL_Entry;

#ifdef NO_SHA
    #define CRL_DIGEST_SIZE SHA256_DIGEST_SIZE
#else
    #define CRL_DIGEST_SIZE SHA_DIGEST_SIZE
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
};


typedef struct CRL_Monitor CRL_Monitor;

/* CRL directory monitor */
struct CRL_Monitor {
    char* path;      /* full dir path, if valid pointer we're using */
    int   type;      /* PEM or ASN1 type */
};


#ifndef HAVE_CRL
    typedef struct WOLFSSL_CRL WOLFSSL_CRL;
#endif

/* wolfSSL CRL controller */
struct WOLFSSL_CRL {
    WOLFSSL_CERT_MANAGER* cm;            /* pointer back to cert manager */
    CRL_Entry*           crlList;       /* our CRL list */
    wolfSSL_Mutex         crlLock;       /* CRL list lock */
    CRL_Monitor          monitors[2];   /* PEM and DER possible */
#ifdef HAVE_CRL_MONITOR
    pthread_t            tid;           /* monitoring thread */
    int                  mfd;           /* monitor fd, -1 if no init yet */
#endif
};


#ifdef NO_ASN 
    typedef struct Signer Signer;
#endif


#ifndef CA_TABLE_SIZE
    #define CA_TABLE_SIZE 11
#endif

/* wolfSSL Certificate Manager */
struct WOLFSSL_CERT_MANAGER {
    Signer*         caTable[CA_TABLE_SIZE]; /* the CA signer table */
    void*           heap;               /* heap helper */
    WOLFSSL_CRL*    crl;                /* CRL checker */
    WOLFSSL_OCSP*   ocsp;               /* OCSP checker */
    char*           ocspOverrideURL;    /* use this responder */
    void*           ocspIOCtx;          /* I/O callback CTX */
    CallbackCACache caCacheCallback;    /* CA cache addition callback */
    CbMissingCRL    cbMissingCRL;       /* notify through cb of missing crl */
    CbOCSPIO        ocspIOCb;           /* I/O callback for OCSP lookup */
    CbOCSPRespFree  ocspRespFreeCb;     /* Frees OCSP Response from IO Cb */
    wolfSSL_Mutex   caLock;             /* CA list lock */
    byte            crlEnabled;         /* is CRL on ? */
    byte            crlCheckAll;        /* always leaf, but all ? */
    byte            ocspEnabled;        /* is OCSP on ? */
    byte            ocspCheckAll;       /* always leaf, but all ? */
    byte            ocspSendNonce;      /* send the OCSP nonce ? */
    byte            ocspUseOverrideURL; /* ignore cert's responder, override */
};

WOLFSSL_LOCAL int CM_SaveCertCache(WOLFSSL_CERT_MANAGER*, const char*);
WOLFSSL_LOCAL int CM_RestoreCertCache(WOLFSSL_CERT_MANAGER*, const char*);
WOLFSSL_LOCAL int CM_MemSaveCertCache(WOLFSSL_CERT_MANAGER*, void*, int, int*);
WOLFSSL_LOCAL int CM_MemRestoreCertCache(WOLFSSL_CERT_MANAGER*, const void*, int);
WOLFSSL_LOCAL int CM_GetCertCacheMemSize(WOLFSSL_CERT_MANAGER*);

/* wolfSSL Sock Addr */
struct WOLFSSL_SOCKADDR {
    unsigned int sz; /* sockaddr size */
    void*        sa; /* pointer to the sockaddr_in or sockaddr_in6 */
};

typedef struct WOLFSSL_DTLS_CTX {
    WOLFSSL_SOCKADDR peer;
    int fd;
} WOLFSSL_DTLS_CTX;


#ifdef WOLFSSL_DTLS

    #ifdef WORD64_AVAILABLE
        typedef word64 DtlsSeq;
    #else
        typedef word32 DtlsSeq;
    #endif
    #define DTLS_SEQ_BITS (sizeof(DtlsSeq) * CHAR_BIT)

    typedef struct DtlsState {
        DtlsSeq window;     /* Sliding window for current epoch    */
        word16 nextEpoch;   /* Expected epoch in next record       */
        word32 nextSeq;     /* Expected sequence in next record    */

        word16 curEpoch;    /* Received epoch in current record    */
        word32 curSeq;      /* Received sequence in current record */

        DtlsSeq prevWindow; /* Sliding window for old epoch        */
        word32 prevSeq;     /* Next sequence in allowed old epoch  */
    } DtlsState;

#endif /* WOLFSSL_DTLS */


/* keys and secrets */
typedef struct Keys {
    byte client_write_MAC_secret[MAX_DIGEST_SIZE];   /* max sizes */
    byte server_write_MAC_secret[MAX_DIGEST_SIZE];
    byte client_write_key[AES_256_KEY_SIZE];         /* max sizes */
    byte server_write_key[AES_256_KEY_SIZE];
    byte client_write_IV[AES_IV_SIZE];               /* max sizes */
    byte server_write_IV[AES_IV_SIZE];
#ifdef HAVE_AEAD
    byte aead_exp_IV[AEAD_EXP_IV_SZ];
    byte aead_enc_imp_IV[AEAD_IMP_IV_SZ];
    byte aead_dec_imp_IV[AEAD_IMP_IV_SZ];
#endif

    word32 peer_sequence_number;
    word32 sequence_number;

#ifdef WOLFSSL_DTLS
    DtlsState dtls_state;                       /* Peer's state */
    word16 dtls_peer_handshake_number;
    word16 dtls_expected_peer_handshake_number;

    word16 dtls_epoch;                          /* Current tx epoch    */
    word32 dtls_sequence_number;                /* Current tx sequence */
    word16 dtls_handshake_number;               /* Current tx handshake seq */
#endif

    word32 encryptSz;             /* last size of encrypted data   */
    word32 padSz;                 /* how much to advance after decrypt part */
    byte   encryptionOn;          /* true after change cipher spec */
    byte   decryptedCur;          /* only decrypt current record once */
} Keys;



/* RFC 6066 TLS Extensions */
#ifdef HAVE_TLS_EXTENSIONS

typedef enum {
    SERVER_NAME_INDICATION = 0x0000,
    MAX_FRAGMENT_LENGTH    = 0x0001,
    TRUNCATED_HMAC         = 0x0004,
    ELLIPTIC_CURVES        = 0x000a,
    SESSION_TICKET         = 0x0023,
    SECURE_RENEGOTIATION   = 0xff01
} TLSX_Type;

typedef struct TLSX {
    TLSX_Type    type; /* Extension Type  */
    void*        data; /* Extension Data  */
    byte         resp; /* IsResponse Flag */
    struct TLSX* next; /* List Behavior   */
} TLSX;

WOLFSSL_LOCAL TLSX*  TLSX_Find(TLSX* list, TLSX_Type type);
WOLFSSL_LOCAL void   TLSX_FreeAll(TLSX* list);
WOLFSSL_LOCAL int    TLSX_SupportExtensions(WOLFSSL* ssl);

#ifndef NO_WOLFSSL_CLIENT
WOLFSSL_LOCAL word16 TLSX_GetRequestSize(WOLFSSL* ssl);
WOLFSSL_LOCAL word16 TLSX_WriteRequest(WOLFSSL* ssl, byte* output);
#endif

#ifndef NO_WOLFSSL_SERVER
WOLFSSL_LOCAL word16 TLSX_GetResponseSize(WOLFSSL* ssl);
WOLFSSL_LOCAL word16 TLSX_WriteResponse(WOLFSSL* ssl, byte* output);
#endif

WOLFSSL_LOCAL int    TLSX_Parse(WOLFSSL* ssl, byte* input, word16 length,
                                                byte isRequest, Suites *suites);
                                                
#elif defined(HAVE_SNI)                  \
   || defined(HAVE_MAX_FRAGMENT)         \
   || defined(HAVE_TRUNCATED_HMAC)       \
   || defined(HAVE_SUPPORTED_CURVES)     \
   || defined(HAVE_SECURE_RENEGOTIATION) \
   || defined(HAVE_SESSION_TICKET)

#error Using TLS extensions requires HAVE_TLS_EXTENSIONS to be defined.

#endif /* HAVE_TLS_EXTENSIONS */

/* Server Name Indication */
#ifdef HAVE_SNI

typedef struct SNI {
    byte                       type;    /* SNI Type          */
    union { char* host_name; } data;    /* SNI Data          */
    struct SNI*                next;    /* List Behavior     */
#ifndef NO_WOLFSSL_SERVER
    byte                       options; /* Behaviour options */
    byte                       status;  /* Matching result   */
#endif
} SNI;

WOLFSSL_LOCAL int TLSX_UseSNI(TLSX** extensions, byte type, const void* data,
                                                                   word16 size);

#ifndef NO_WOLFSSL_SERVER
WOLFSSL_LOCAL void   TLSX_SNI_SetOptions(TLSX* extensions, byte type,
                                                                  byte options);
WOLFSSL_LOCAL byte   TLSX_SNI_Status(TLSX* extensions, byte type);
WOLFSSL_LOCAL word16 TLSX_SNI_GetRequest(TLSX* extensions, byte type,
                                                                   void** data);
WOLFSSL_LOCAL int    TLSX_SNI_GetFromBuffer(const byte* buffer, word32 bufferSz,
                                         byte type, byte* sni, word32* inOutSz);
#endif

#endif /* HAVE_SNI */

/* Maximum Fragment Length */
#ifdef HAVE_MAX_FRAGMENT

WOLFSSL_LOCAL int TLSX_UseMaxFragment(TLSX** extensions, byte mfl);

#endif /* HAVE_MAX_FRAGMENT */

#ifdef HAVE_TRUNCATED_HMAC

WOLFSSL_LOCAL int TLSX_UseTruncatedHMAC(TLSX** extensions);

#endif /* HAVE_TRUNCATED_HMAC */

#ifdef HAVE_SUPPORTED_CURVES

typedef struct EllipticCurve {
    word16                name; /* CurveNames    */
    struct EllipticCurve* next; /* List Behavior */
} EllipticCurve;

WOLFSSL_LOCAL int TLSX_UseSupportedCurve(TLSX** extensions, word16 name);

#ifndef NO_WOLFSSL_SERVER
WOLFSSL_LOCAL int TLSX_ValidateEllipticCurves(WOLFSSL* ssl, byte first,
                                                                   byte second);
#endif

#endif /* HAVE_SUPPORTED_CURVES */

#ifdef HAVE_SECURE_RENEGOTIATION

enum key_cache_state {
    SCR_CACHE_NULL   = 0,       /* empty / begin state */
    SCR_CACHE_NEEDED,           /* need to cache keys */
    SCR_CACHE_COPY,             /* we have a cached copy */
    SCR_CACHE_PARTIAL,          /* partial restore to real keys */
    SCR_CACHE_COMPLETE          /* complete restore to real keys */
};


/* Additional Conection State according to rfc5746 section 3.1 */
typedef struct SecureRenegotiation {
   byte                 enabled;  /* secure_renegotiation flag in rfc */
   byte                 startScr; /* server requested client to start scr */
   enum key_cache_state cache_status;  /* track key cache state */
   byte                 client_verify_data[TLS_FINISHED_SZ];  /* cached */
   byte                 server_verify_data[TLS_FINISHED_SZ];  /* cached */
   byte                 subject_hash[SHA_DIGEST_SIZE];  /* peer cert hash */
   Keys                 tmp_keys;  /* can't overwrite real keys yet */
} SecureRenegotiation;

WOLFSSL_LOCAL int TLSX_UseSecureRenegotiation(TLSX** extensions);

#endif /* HAVE_SECURE_RENEGOTIATION */

#ifdef HAVE_SESSION_TICKET

typedef struct SessionTicket {
    word32 lifetime;
    byte*  data;
    word16 size;
} SessionTicket;

WOLFSSL_LOCAL int  TLSX_UseSessionTicket(TLSX** extensions, 
                                                         SessionTicket* ticket);
WOLFSSL_LOCAL SessionTicket* TLSX_SessionTicket_Create(word32 lifetime,
                                                       byte* data, word16 size);
WOLFSSL_LOCAL void TLSX_SessionTicket_Free(SessionTicket* ticket);
#endif /* HAVE_SESSION_TICKET */

/* wolfSSL context type */
struct WOLFSSL_CTX {
    WOLFSSL_METHOD* method;
    wolfSSL_Mutex   countMutex;    /* reference count mutex */
    int         refCount;         /* reference count */
#ifndef NO_DH
    buffer      serverDH_P;
    buffer      serverDH_G;
#endif
#ifndef NO_CERTS
    buffer      certificate;
    buffer      certChain;
                 /* chain after self, in DER, with leading size for each cert */
    buffer      privateKey;
    WOLFSSL_CERT_MANAGER* cm;      /* our cert manager, ctx owns SSL will use */
#endif
    Suites*     suites;           /* make dynamic, user may not need/set */
    void*       heap;             /* for user memory overrides */
    byte        verifyPeer;
    byte        verifyNone;
    byte        failNoCert;
    byte        sessionCacheOff;
    byte        sessionCacheFlushOff;
    byte        sendVerify;       /* for client side */
    byte        haveRSA;          /* RSA available */
    byte        haveDH;           /* server DH parms set by user */
    byte        haveNTRU;         /* server private NTRU  key loaded */
    byte        haveECDSAsig;     /* server cert signed w/ ECDSA */
    byte        haveStaticECC;    /* static server ECC private key */
    byte        partialWrite;     /* only one msg per write call */
    byte        quietShutdown;    /* don't send close notify */
    byte        groupMessages;    /* group handshake messages before sending */
    byte        minDowngrade;     /* minimum downgrade version */
#ifndef NO_DH
    word16      minDhKeySz;       /* minimum DH key size */
#endif
    CallbackIORecv CBIORecv;
    CallbackIOSend CBIOSend;
#ifdef WOLFSSL_DTLS
    CallbackGenCookie CBIOCookie;       /* gen cookie callback */
#endif
    VerifyCallback  verifyCallback;     /* cert verification callback */
    word32          timeout;            /* session timeout */
#ifdef HAVE_ECC
    word16          eccTempKeySz;       /* in octets 20 - 66 */
    word32          pkCurveOID;         /* curve Ecc_Sum */
#endif
#ifndef NO_PSK
    byte        havePSK;                /* psk key set by user */
    psk_client_callback client_psk_cb;  /* client callback */
    psk_server_callback server_psk_cb;  /* server callback */
    char        server_hint[MAX_PSK_ID_LEN];
#endif /* NO_PSK */
#ifdef HAVE_ANON
    byte        haveAnon;               /* User wants to allow Anon suites */
#endif /* HAVE_ANON */
#if defined(OPENSSL_EXTRA) || defined(HAVE_WEBSERVER)
    pem_password_cb passwd_cb;
    void*            userdata;
#endif /* OPENSSL_EXTRA */
#ifdef HAVE_OCSP
    WOLFSSL_OCSP      ocsp;
#endif
#ifdef HAVE_CAVIUM
    int              devId;            /* cavium device id to use */
#endif
#ifdef HAVE_TLS_EXTENSIONS
    TLSX* extensions;                  /* RFC 6066 TLS Extensions data */
    #if defined(HAVE_SESSION_TICKET) && !defined(NO_WOLFSSL_SEVER)
        SessionTicketEncCb ticketEncCb;   /* enc/dec session ticket Cb */
        void*              ticketEncCtx;  /* session encrypt context */
        int                ticketHint;    /* ticket hint in seconds */
    #endif
#endif
#ifdef ATOMIC_USER
    CallbackMacEncrypt    MacEncryptCb;    /* Atomic User Mac/Encrypt Cb */
    CallbackDecryptVerify DecryptVerifyCb; /* Atomic User Decrypt/Verify Cb */
#endif
#ifdef HAVE_PK_CALLBACKS
    #ifdef HAVE_ECC
        CallbackEccSign   EccSignCb;    /* User EccSign   Callback handler */
        CallbackEccVerify EccVerifyCb;  /* User EccVerify Callback handler */
    #endif /* HAVE_ECC */
    #ifndef NO_RSA 
        CallbackRsaSign   RsaSignCb;    /* User RsaSign   Callback handler */
        CallbackRsaVerify RsaVerifyCb;  /* User RsaVerify Callback handler */
        CallbackRsaEnc    RsaEncCb;     /* User Rsa Public Encrypt  handler */
        CallbackRsaDec    RsaDecCb;     /* User Rsa Private Decrypt handler */
    #endif /* NO_RSA */
#endif /* HAVE_PK_CALLBACKS */
};


WOLFSSL_LOCAL
int InitSSL_Ctx(WOLFSSL_CTX*, WOLFSSL_METHOD*);
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
    int AddCA(WOLFSSL_CERT_MANAGER* ctx, buffer der, int type, int verify);
    WOLFSSL_LOCAL
    int AlreadySigner(WOLFSSL_CERT_MANAGER* cm, byte* hash);
#endif

/* All cipher suite related info */
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


/* Supported Message Authentication Codes from page 43 */
enum MACAlgorithm { 
    no_mac,
    md5_mac,
    sha_mac,
    sha224_mac,
    sha256_mac,     /* needs to match external KDF_MacAlgorithm */
    sha384_mac,
    sha512_mac,
    rmd_mac,
    blake2b_mac
};


/* Supported Key Exchange Protocols */
enum KeyExchangeAlgorithm { 
    no_kea,
    rsa_kea, 
    diffie_hellman_kea, 
    fortezza_kea,
    psk_kea,
    dhe_psk_kea,
    ntru_kea,
    ecc_diffie_hellman_kea,
    ecc_static_diffie_hellman_kea       /* for verify suite only */
};


/* Supported Authentication Schemes */
enum SignatureAlgorithm {
    anonymous_sa_algo,
    rsa_sa_algo,
    dsa_sa_algo,
    ecc_dsa_sa_algo
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


enum CipherType { stream, block, aead };






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
    byte    setup;       /* have we set it up flag for detection */
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
    #ifndef NO_OLD_TLS
        byte md5[MD5_DIGEST_SIZE];
    #endif
    byte sha[SHA_DIGEST_SIZE];
    #ifndef NO_SHA256
        byte sha256[SHA256_DIGEST_SIZE];
    #endif
    #ifdef WOLFSSL_SHA384
        byte sha384[SHA384_DIGEST_SIZE];
    #endif
    #ifdef WOLFSSL_SHA512
        byte sha512[SHA512_DIGEST_SIZE];
    #endif
} Hashes;


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
    word32       bornOn;                        /* create time in seconds   */
    word32       timeout;                       /* timeout in seconds       */
    byte         sessionID[ID_LEN];             /* id for protocol */
    byte         sessionIDSz;
    byte         masterSecret[SECRET_LEN];      /* stored secret */
#ifdef SESSION_CERTS
    WOLFSSL_X509_CHAIN chain;                    /* peer cert chain, static  */
    ProtocolVersion version;                    /* which version was used */
    byte            cipherSuite0;               /* first byte, normally 0 */
    byte            cipherSuite;                /* 2nd byte, actual suite */
#endif
#ifndef NO_CLIENT_CACHE
    word16       idLen;                         /* serverID length */
    byte         serverID[SERVER_ID_LEN];       /* for easier client lookup */
#endif
#ifdef HAVE_SESSION_TICKET
    word16       ticketLen;
    byte         ticket[SESSION_TICKET_LEN];
#endif
};


WOLFSSL_LOCAL
WOLFSSL_SESSION* GetSession(WOLFSSL*, byte*);
WOLFSSL_LOCAL
int          SetSession(WOLFSSL*, WOLFSSL_SESSION*);

typedef int (*hmacfp) (WOLFSSL*, byte*, const byte*, word32, int, int);

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
    ACCEPT_CLIENT_HELLO_DONE,
    HELLO_VERIFY_SENT,
    ACCEPT_FIRST_REPLY_DONE,
    SERVER_HELLO_SENT,
    CERT_SENT,
    KEY_EXCHANGE_SENT,
    CERT_REQ_SENT,
    SERVER_HELLO_DONE,
    ACCEPT_SECOND_REPLY_DONE,
    TICKET_SENT,
    CHANGE_CIPHER_SENT,
    ACCEPT_FINISHED_DONE,
    ACCEPT_THIRD_REPLY_DONE
};


typedef struct Buffers {
    bufferStatic    inputBuffer;
    bufferStatic    outputBuffer;
    buffer          domainName;             /* for client check */
    buffer          clearOutputBuffer;
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
#endif
#ifndef NO_CERTS
    buffer          certificate;           /* WOLFSSL_CTX owns, unless we own */
    buffer          key;                   /* WOLFSSL_CTX owns, unless we own */
    buffer          certChain;             /* WOLFSSL_CTX owns, unless we own */
                 /* chain after self, in DER, with leading size for each cert */
#endif
#ifdef WOLFSSL_DTLS
    WOLFSSL_DTLS_CTX dtlsCtx;               /* DTLS connection context */
#endif
#ifdef HAVE_PK_CALLBACKS
    #ifdef HAVE_ECC
        buffer peerEccDsaKey;              /* we own for Ecc Verify Callbacks */
    #endif /* HAVE_ECC */
    #ifndef NO_RSA
        buffer peerRsaKey;                 /* we own for Rsa Verify Callbacks */
    #endif /* NO_RSA */
#endif /* HAVE_PK_CALLBACKS */
} Buffers;

typedef struct Options {
#ifndef NO_PSK
    psk_client_callback client_psk_cb;
    psk_server_callback server_psk_cb;
    word16            havePSK:1;            /* psk key set by user */
#endif /* NO_PSK */

    /* on/off or small bit flags, optimize layout */
    word16            sendVerify:2;     /* false = 0, true = 1, sendBlank = 2 */
    word16            sessionCacheOff:1;
    word16            sessionCacheFlushOff:1;
    word16            side:1;             /* client or server end */
    word16            verifyPeer:1;
    word16            verifyNone:1;
    word16            failNoCert:1;
    word16            downgrade:1;        /* allow downgrade of versions */
    word16            resuming:1;
    word16            haveSessionId:1;    /* server may not send */
    word16            tls:1;              /* using TLS ? */
    word16            tls1_1:1;           /* using TLSv1.1+ ? */
    word16            dtls:1;             /* using datagrams ? */
    word16            connReset:1;        /* has the peer reset */
    word16            isClosed:1;         /* if we consider conn closed */
    word16            closeNotify:1;      /* we've recieved a close notify */
    word16            sentNotify:1;       /* we've sent a close notify */
    word16            usingCompression:1; /* are we using compression */
    word16            haveRSA:1;          /* RSA available */
    word16            haveDH:1;           /* server DH parms set by user */
    word16            haveNTRU:1;         /* server NTRU  private key loaded */
    word16            haveECDSAsig:1;     /* server ECDSA signed cert */
    word16            haveStaticECC:1;    /* static server ECC private key */
    word16            havePeerCert:1;     /* do we have peer's cert */
    word16            havePeerVerify:1;   /* and peer's cert verify */
    word16            usingPSK_cipher:1;  /* are using psk as cipher */
    word16            usingAnon_cipher:1; /* are we using an anon cipher */
    word16            sendAlertState:1;   /* nonblocking resume */
    word16            partialWrite:1;     /* only one msg per write call */
    word16            quietShutdown:1;    /* don't send close notify */
    word16            certOnly:1;         /* stop once we get cert */
    word16            groupMessages:1;    /* group handshake messages */
    word16            usingNonblock:1;    /* are we using nonblocking socket */
    word16            saveArrays:1;       /* save array Memory for user get keys
                                           or psk */
#ifdef HAVE_POLY1305
    word16            oldPoly:1;        /* set when to use old rfc way of poly*/
#endif
#ifdef HAVE_ANON
    word16            haveAnon:1;       /* User wants to allow Anon suites */
#endif
#ifdef HAVE_SESSION_TICKET
    word16            createTicket:1;     /* Server to create new Ticket */
    word16            useTicket:1;        /* Use Ticket not session cache */
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
#ifndef NO_DH
    word16          minDhKeySz;         /* minimum DH key size */
    word16          dhKeySz;            /* actual DH key size */
#endif

} Options;

typedef struct Arrays {
    word32          preMasterSz;        /* differs for DH, actual size */
#ifndef NO_PSK
    word32          psk_keySz;          /* acutal size */
    char            client_identity[MAX_PSK_ID_LEN];
    char            server_hint[MAX_PSK_ID_LEN];
    byte            psk_key[MAX_PSK_KEY_LEN];
#endif
    byte            clientRandom[RAN_LEN];
    byte            serverRandom[RAN_LEN];
    byte            sessionID[ID_LEN];
    byte            sessionIDSz;
    byte            preMasterSecret[ENCRYPT_LEN];
    byte            masterSecret[SECRET_LEN];
#ifdef WOLFSSL_DTLS
    byte            cookie[MAX_COOKIE_LEN];
    byte            cookieSz;
#endif
} Arrays;

#ifndef ASN_NAME_MAX
#define ASN_NAME_MAX 256
#endif

#ifndef MAX_DATE_SZ
#define MAX_DATE_SZ 32
#endif

struct WOLFSSL_X509_NAME {
    char  *name;
    char  staticName[ASN_NAME_MAX];
    int   dynamicName;
    int   sz;
#ifdef OPENSSL_EXTRA
    DecodedName fullName;
#endif /* OPENSSL_EXTRA */
};

#ifndef EXTERNAL_SERIAL_SIZE
    #define EXTERNAL_SERIAL_SIZE 32
#endif

#ifdef NO_ASN 
    typedef struct DNS_entry DNS_entry;
#endif

struct WOLFSSL_X509 {
    int              version;
    WOLFSSL_X509_NAME issuer;
    WOLFSSL_X509_NAME subject;
    int              serialSz;
    byte             serial[EXTERNAL_SERIAL_SIZE];
    char             subjectCN[ASN_NAME_MAX];        /* common name short cut */
#ifdef WOLFSSL_SEP
    int              deviceTypeSz;
    byte             deviceType[EXTERNAL_SERIAL_SIZE];
    int              hwTypeSz;
    byte             hwType[EXTERNAL_SERIAL_SIZE];
    int              hwSerialNumSz;
    byte             hwSerialNum[EXTERNAL_SERIAL_SIZE];
    #ifdef OPENSSL_EXTRA
        byte             certPolicySet;
        byte             certPolicyCrit;
    #endif /* OPENSSL_EXTRA */
#endif
    int              notBeforeSz;
    byte             notBefore[MAX_DATE_SZ];
    int              notAfterSz;
    byte             notAfter[MAX_DATE_SZ];
    int              sigOID;
    buffer           sig;
    int              pubKeyOID;
    buffer           pubKey;
    #ifdef HAVE_ECC
        word32       pkCurveOID;
    #endif /* HAVE_ECC */
    buffer           derCert;                        /* may need  */
    DNS_entry*       altNames;                       /* alt names list */
    DNS_entry*       altNamesNext;                   /* hint for retrieval */
    byte             dynamicMemory;                  /* dynamic memory flag */
    byte             isCa;
#ifdef OPENSSL_EXTRA
    word32           pathLength;
    word16           keyUsage;
    byte             basicConstSet;
    byte             basicConstCrit;
    byte             basicConstPlSet;
    byte             subjAltNameSet;
    byte             subjAltNameCrit;
    byte             authKeyIdSet;
    byte             authKeyIdCrit;
    byte*            authKeyId;
    word32           authKeyIdSz;
    byte             subjKeyIdSet;
    byte             subjKeyIdCrit;
    byte*            subjKeyId;
    word32           subjKeyIdSz;
    byte             keyUsageSet;
    byte             keyUsageCrit;
#endif /* OPENSSL_EXTRA */
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
    byte            epoch[2];             /* increment on cipher state change */
    byte            sequence_number[6];   /* per record */
    byte            length[2];
} DtlsRecordLayerHeader;


typedef struct DtlsPool {
    buffer          buf[DTLS_POOL_SZ];
    int             used;
} DtlsPool;

typedef struct DtlsMsg {
    struct DtlsMsg* next;
    word32          seq;       /* Handshake sequence number    */
    word32          sz;        /* Length of whole mesage       */
    word32          fragSz;    /* Length of fragments received */
    byte            type;
    byte*           buf;
    byte*           msg;
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


/* Handshake messages recevied from peer (plus change cipher */
typedef struct MsgsReceived {
    word16 got_hello_request:1;
    word16 got_client_hello:1;
    word16 got_server_hello:1;
    word16 got_hello_verify_request:1;
    word16 got_session_ticket:1;
    word16 got_certificate:1;
    word16 got_server_key_exchange:1;
    word16 got_certificate_request:1;
    word16 got_server_hello_done:1;
    word16 got_certificate_verify:1;
    word16 got_client_key_exchange:1;
    word16 got_finished:1;
    word16 got_change_cipher:1;
} MsgsReceived;


/* Handshake hashes */
typedef struct HS_Hashes {
    Hashes          verifyHashes;
    Hashes          certHashes;         /* for cert verify */
#ifndef NO_OLD_TLS
#ifndef NO_SHA
    Sha             hashSha;            /* sha hash of handshake msgs */
#endif
#ifndef NO_MD5
    Md5             hashMd5;            /* md5 hash of handshake msgs */
#endif
#endif /* NO_OLD_TLS */
#ifndef NO_SHA256
    Sha256          hashSha256;         /* sha256 hash of handshake msgs */
#endif
#ifdef WOLFSSL_SHA384
    Sha384          hashSha384;         /* sha384 hash of handshake msgs */
#endif
#ifdef WOLFSSL_SHA512
    Sha512          hashSha512;         /* sha512 hash of handshake msgs */
#endif
} HS_Hashes;


/* wolfSSL ssl type */
struct WOLFSSL {
    WOLFSSL_CTX*    ctx;
    Suites*         suites;             /* only need during handshake */
    Arrays*         arrays;
    HS_Hashes*      hsHashes;
    void*           IOCB_ReadCtx;
    void*           IOCB_WriteCtx;
    RNG*            rng;
    void*           verifyCbCtx;        /* cert verify callback user ctx*/
    VerifyCallback  verifyCallback;     /* cert verification callback */
    void*           heap;               /* for user overrides */
#ifndef NO_HANDSHAKE_DONE_CB
    HandShakeDoneCb hsDoneCb;          /*  notify user handshake done */
    void*           hsDoneCtx;         /*  user handshake cb context  */
#endif
    WOLFSSL_CIPHER  cipher;
    hmacfp          hmac;
    Ciphers         encrypt;
    Ciphers         decrypt;
    Buffers         buffers;
    WOLFSSL_SESSION session;
    WOLFSSL_ALERT_HISTORY alert_history;
    int             error;
    int             rfd;                /* read  file descriptor */
    int             wfd;                /* write file descriptor */
    int             rflags;             /* user read  flags */
    int             wflags;             /* user write flags */
    word32          timeout;            /* session timeout */
    word16          curSize;
    RecordLayerHeader curRL;
    MsgsReceived    msgsReceived;       /* peer messages received */
    ProtocolVersion version;            /* negotiated version */
    ProtocolVersion chVersion;          /* client hello version */
    CipherSpecs     specs;
    Keys            keys;
    Options         options;
#ifdef OPENSSL_EXTRA
    WOLFSSL_BIO*     biord;              /* socket bio read  to free/close */
    WOLFSSL_BIO*     biowr;              /* socket bio write to free/close */
#endif
#ifndef NO_RSA
    RsaKey*         peerRsaKey;
    byte            peerRsaKeyPresent;
#endif
#ifdef HAVE_NTRU
    word16          peerNtruKeyLen;
    byte            peerNtruKey[MAX_NTRU_PUB_KEY_SZ];
    byte            peerNtruKeyPresent;
#endif
#ifdef HAVE_ECC
    ecc_key*        peerEccKey;              /* peer's  ECDHE key */
    ecc_key*        peerEccDsaKey;           /* peer's  ECDSA key */
    ecc_key*        eccTempKey;              /* private ECDHE key */
    word32          pkCurveOID;              /* curve Ecc_Sum     */
    word16          eccTempKeySz;            /* in octets 20 - 66 */
    byte            peerEccKeyPresent;
    byte            peerEccDsaKeyPresent;
    byte            eccTempKeyPresent;
#endif
#ifdef HAVE_LIBZ
    z_stream        c_stream;           /* compression   stream */
    z_stream        d_stream;           /* decompression stream */
    byte            didStreamInit;      /* for stream init and end */
#endif
#ifdef WOLFSSL_DTLS
    int             dtls_timeout_init;  /* starting timeout vaule */
    int             dtls_timeout_max;   /* maximum timeout value */
    int             dtls_timeout;       /* current timeout value, changes */
    DtlsPool*       dtls_pool;
    DtlsMsg*        dtls_msg_list;
    void*           IOCB_CookieCtx;     /* gen cookie ctx */
    word32          dtls_expected_rx;
#endif
#ifdef WOLFSSL_CALLBACKS
    HandShakeInfo   handShakeInfo;      /* info saved during handshake */
    TimeoutInfo     timeoutInfo;        /* info saved during handshake */
    byte            hsInfoOn;           /* track handshake info        */
    byte            toInfoOn;           /* track timeout   info        */
#endif
#ifdef HAVE_FUZZER
    CallbackFuzzer  fuzzerCb;           /* for testing with using fuzzer */
    void*           fuzzerCtx;          /* user defined pointer */
#endif
#ifdef KEEP_PEER_CERT
    WOLFSSL_X509     peerCert;           /* X509 peer cert */
#endif
#ifdef FORTRESS
    void*           ex_data[MAX_EX_DATA]; /* external data, for Fortress */
#endif
#ifdef HAVE_CAVIUM
    int              devId;            /* cavium device id to use */
#endif
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
    #ifdef HAVE_SECURE_RENEGOTIATION
        SecureRenegotiation* secure_renegotiation; /* valid pointer indicates */
    #endif                                         /* user turned on */
    #if !defined(NO_WOLFSSL_CLIENT) && defined(HAVE_SESSION_TICKET)
        CallbackSessionTicket session_ticket_cb;
        void*                 session_ticket_ctx;
        byte                  expect_session_ticket;
    #endif
#endif /* HAVE_TLS_EXTENSIONS */
#ifdef HAVE_NETX
    NetX_Ctx        nxCtx;             /* NetX IO Context */
#endif
#ifdef SESSION_INDEX
    int sessionIndex;                  /* Session's location in the cache. */
#endif
#ifdef ATOMIC_USER
    void*    MacEncryptCtx;    /* Atomic User Mac/Encrypt Callback Context */
    void*    DecryptVerifyCtx; /* Atomic User Decrypt/Verify Callback Context */
#endif
#ifdef HAVE_PK_CALLBACKS
    #ifdef HAVE_ECC
        void* EccSignCtx;     /* Ecc Sign   Callback Context */
        void* EccVerifyCtx;   /* Ecc Verify Callback Context */
    #endif /* HAVE_ECC */
    #ifndef NO_RSA
        void* RsaSignCtx;     /* Rsa Sign   Callback Context */
        void* RsaVerifyCtx;   /* Rsa Verify Callback Context */
        void* RsaEncCtx;      /* Rsa Public  Encrypt   Callback Context */
        void* RsaDecCtx;      /* Rsa Private Decrypt   Callback Context */
    #endif /* NO_RSA */
#endif /* HAVE_PK_CALLBACKS */
#ifdef HAVE_SECRET_CALLBACK
        SessionSecretCb sessionSecretCb;
        void*           sessionSecretCtx;
#endif /* HAVE_SECRET_CALLBACK */
};


WOLFSSL_LOCAL
int  InitSSL(WOLFSSL*, WOLFSSL_CTX*);
WOLFSSL_LOCAL
void FreeSSL(WOLFSSL*);
WOLFSSL_API void SSL_ResourceFree(WOLFSSL*);   /* Micrium uses */


enum {
    IV_SZ   = 32,          /* max iv sz */
    NAME_SZ = 80          /* max one line */
};


typedef struct EncryptedInfo {
    char     name[NAME_SZ];    /* encryption name */
    byte     iv[IV_SZ];        /* encrypted IV */
    word32   ivSz;             /* encrypted IV size */
    long     consumed;         /* tracks PEM bytes consumed */
    byte     set;              /* if encryption set */
    WOLFSSL_CTX* ctx;              /* CTX owner */
} EncryptedInfo;


#ifndef NO_CERTS
    WOLFSSL_LOCAL int PemToDer(const unsigned char* buff, long sz, int type,
                              buffer* der, void* heap, EncryptedInfo* info,
                              int* eccKey);

    WOLFSSL_LOCAL int ProcessFile(WOLFSSL_CTX* ctx, const char* fname, int format,
                                 int type, WOLFSSL* ssl, int userChain,
                                WOLFSSL_CRL* crl);
#endif


#ifdef WOLFSSL_CALLBACKS
    WOLFSSL_LOCAL
    void InitHandShakeInfo(HandShakeInfo*);
    WOLFSSL_LOCAL 
    void FinishHandShakeInfo(HandShakeInfo*, const WOLFSSL*);
    WOLFSSL_LOCAL 
    void AddPacketName(const char*, HandShakeInfo*);

    WOLFSSL_LOCAL
    void InitTimeoutInfo(TimeoutInfo*);
    WOLFSSL_LOCAL 
    void FreeTimeoutInfo(TimeoutInfo*, void*);
    WOLFSSL_LOCAL 
    void AddPacketInfo(const char*, TimeoutInfo*, const byte*, int, void*);
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
    byte            message_seq[2];    /* start at 0, restransmit gets same # */
    word24          fragment_offset;   /* bytes in previous fragments */
    word24          fragment_length;   /* length of this fragment */
} DtlsHandShakeHeader;


enum HandShakeType {
    no_shake            = -1,
    hello_request       = 0, 
    client_hello        = 1, 
    server_hello        = 2,
    hello_verify_request = 3,       /* DTLS addition */
    session_ticket      =  4,
    certificate         = 11, 
    server_key_exchange = 12,
    certificate_request = 13, 
    server_hello_done   = 14,
    certificate_verify  = 15, 
    client_key_exchange = 16,
    finished            = 20,
    certificate_status  = 22,
    change_cipher_hs    = 55      /* simulate unique handshake type for sanity
                                     checks.  record layer change_cipher
                                     conflicts with handshake finished */
};


static const byte client[SIZEOF_SENDER] = { 0x43, 0x4C, 0x4E, 0x54 };
static const byte server[SIZEOF_SENDER] = { 0x53, 0x52, 0x56, 0x52 };

static const byte tls_client[FINISHED_LABEL_SZ + 1] = "client finished";
static const byte tls_server[FINISHED_LABEL_SZ + 1] = "server finished";


/* internal functions */
WOLFSSL_LOCAL int SendChangeCipher(WOLFSSL*);
WOLFSSL_LOCAL int SendTicket(WOLFSSL*);
WOLFSSL_LOCAL int DoClientTicket(WOLFSSL*, const byte*, word32);
WOLFSSL_LOCAL int SendData(WOLFSSL*, const void*, int);
WOLFSSL_LOCAL int SendCertificate(WOLFSSL*);
WOLFSSL_LOCAL int SendCertificateRequest(WOLFSSL*);
WOLFSSL_LOCAL int SendServerKeyExchange(WOLFSSL*);
WOLFSSL_LOCAL int SendBuffered(WOLFSSL*);
WOLFSSL_LOCAL int ReceiveData(WOLFSSL*, byte*, int, int);
WOLFSSL_LOCAL int SendFinished(WOLFSSL*);
WOLFSSL_LOCAL int SendAlert(WOLFSSL*, int, int);
WOLFSSL_LOCAL int ProcessReply(WOLFSSL*);

WOLFSSL_LOCAL int SetCipherSpecs(WOLFSSL*);
WOLFSSL_LOCAL int MakeMasterSecret(WOLFSSL*);

WOLFSSL_LOCAL int  AddSession(WOLFSSL*);
WOLFSSL_LOCAL int  DeriveKeys(WOLFSSL* ssl);
WOLFSSL_LOCAL int  StoreKeys(WOLFSSL* ssl, const byte* keyData);

WOLFSSL_LOCAL int IsTLS(const WOLFSSL* ssl);
WOLFSSL_LOCAL int IsAtLeastTLSv1_2(const WOLFSSL* ssl);

WOLFSSL_LOCAL void FreeHandshakeResources(WOLFSSL* ssl);
WOLFSSL_LOCAL void ShrinkInputBuffer(WOLFSSL* ssl, int forcedFree);
WOLFSSL_LOCAL void ShrinkOutputBuffer(WOLFSSL* ssl);

WOLFSSL_LOCAL int VerifyClientSuite(WOLFSSL* ssl);
#ifndef NO_CERTS
    WOLFSSL_LOCAL Signer* GetCA(void* cm, byte* hash);
    #ifndef NO_SKID
        WOLFSSL_LOCAL Signer* GetCAByName(void* cm, byte* hash);
    #endif
#endif
WOLFSSL_LOCAL int  BuildTlsFinished(WOLFSSL* ssl, Hashes* hashes,
                                   const byte* sender);
WOLFSSL_LOCAL void FreeArrays(WOLFSSL* ssl, int keep);
WOLFSSL_LOCAL  int CheckAvailableSize(WOLFSSL *ssl, int size);
WOLFSSL_LOCAL  int GrowInputBuffer(WOLFSSL* ssl, int size, int usedLength);

#ifndef NO_TLS
    WOLFSSL_LOCAL int  MakeTlsMasterSecret(WOLFSSL*);
    WOLFSSL_LOCAL int  TLS_hmac(WOLFSSL* ssl, byte* digest, const byte* in,
                               word32 sz, int content, int verify);
#endif

#ifndef NO_WOLFSSL_CLIENT
    WOLFSSL_LOCAL int SendClientHello(WOLFSSL*);
    WOLFSSL_LOCAL int SendClientKeyExchange(WOLFSSL*);
    WOLFSSL_LOCAL int SendCertificateVerify(WOLFSSL*);
#endif /* NO_WOLFSSL_CLIENT */

#ifndef NO_WOLFSSL_SERVER
    WOLFSSL_LOCAL int SendServerHello(WOLFSSL*);
    WOLFSSL_LOCAL int SendServerHelloDone(WOLFSSL*);
    #ifdef WOLFSSL_DTLS
        WOLFSSL_LOCAL int SendHelloVerifyRequest(WOLFSSL*);
    #endif
#endif /* NO_WOLFSSL_SERVER */

#ifdef WOLFSSL_DTLS
    WOLFSSL_LOCAL int  DtlsPoolInit(WOLFSSL*);
    WOLFSSL_LOCAL int  DtlsPoolSave(WOLFSSL*, const byte*, int);
    WOLFSSL_LOCAL int  DtlsPoolTimeout(WOLFSSL*);
    WOLFSSL_LOCAL int  DtlsPoolSend(WOLFSSL*);
    WOLFSSL_LOCAL void DtlsPoolReset(WOLFSSL*);

    WOLFSSL_LOCAL DtlsMsg* DtlsMsgNew(word32, void*);
    WOLFSSL_LOCAL void DtlsMsgDelete(DtlsMsg*, void*);
    WOLFSSL_LOCAL void DtlsMsgListDelete(DtlsMsg*, void*);
    WOLFSSL_LOCAL void DtlsMsgSet(DtlsMsg*, word32, const byte*, byte,
                                                             word32, word32);
    WOLFSSL_LOCAL DtlsMsg* DtlsMsgFind(DtlsMsg*, word32);
    WOLFSSL_LOCAL DtlsMsg* DtlsMsgStore(DtlsMsg*, word32, const byte*, word32,
                                                byte, word32, word32, void*);
    WOLFSSL_LOCAL DtlsMsg* DtlsMsgInsert(DtlsMsg*, DtlsMsg*);
#endif /* WOLFSSL_DTLS */

#ifndef NO_TLS
    

#endif /* NO_TLS */


WOLFSSL_LOCAL word32  LowResTimer(void);

WOLFSSL_LOCAL void InitX509Name(WOLFSSL_X509_NAME*, int);
WOLFSSL_LOCAL void FreeX509Name(WOLFSSL_X509_NAME* name);
WOLFSSL_LOCAL void InitX509(WOLFSSL_X509*, int);
WOLFSSL_LOCAL void FreeX509(WOLFSSL_X509*);
#ifndef NO_CERTS
    WOLFSSL_LOCAL int  CopyDecodedToX509(WOLFSSL_X509*, DecodedCert*);
#endif

/* used by ssl.c and wolfssl_int.c */
WOLFSSL_LOCAL void c32to24(word32 in, word24 out);

WOLFSSL_LOCAL const char* const* GetCipherNames(void);
WOLFSSL_LOCAL int GetCipherNamesSize(void);


enum encrypt_side {
    ENCRYPT_SIDE_ONLY = 1,
    DECRYPT_SIDE_ONLY,
    ENCRYPT_AND_DECRYPT_SIDE
};

WOLFSSL_LOCAL int SetKeysSide(WOLFSSL*, enum encrypt_side);


#ifdef __cplusplus
    }  /* extern "C" */
#endif

#endif /* wolfSSL_INT_H */

