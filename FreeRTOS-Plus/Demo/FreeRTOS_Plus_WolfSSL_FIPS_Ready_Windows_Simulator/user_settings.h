/*
 * FreeRTOS V202112.00
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 * https://www.FreeRTOS.org
 * https://github.com/FreeRTOS
 *
 */

#ifndef USER_SETTINGS_H_
#define USER_SETTINGS_H_
/*-- Cipher related definitions  -----------------------------------------------
 *
 *
 *----------------------------------------------------------------------------*/

#define HAVE_FIPS
#define HAVE_FIPS_VERSION 3
#define WOLFSSL_TLS13
#define HAVE_TLS_EXTENSIONS

#define HAVE_SUPPORTED_CURVES
#define HAVE_FFDHE_2048

#ifndef WOLFSSL_OPTIONS_IGNORE_SYS
#undef  _POSIX_THREADS
#define _POSIX_THREADS
#endif

#define HAVE_THREAD_LS
#define TFM_TIMING_RESISTANT
#define ECC_TIMING_RESISTANT
#define WC_RSA_BLINDING
#define HAVE_AESGCM
#define WOLFSSL_SHA512
#define WOLFSSL_SHA384
#define HAVE_HKDF
#define NO_DSA
#define HAVE_ECC
#define TFM_ECC256
#define ECC_SHAMIR
#define WC_RSA_PSS
#define WOLFSSL_BASE64_ENCODE
#define NO_RC4
#define NO_HC128
#define NO_RABBIT
#define WOLFSSL_KEY_GEN
#define WOLFSSL_SHA224
#define WOLFSSL_AES_DIRECT
#define HAVE_AES_ECB
#define HAVE_ECC_CDH
#define WC_RSA_NO_PADDING
#define WOLFSSL_VALIDATE_FFC_IMPORT
#define HAVE_FFDHE_Q
#define WOLFSSL_NO_SHAKE256
#define HAVE_AESCCM
#define WOLFSSL_VALIDATE_ECC_IMPORT
#define WOLFSSL_AES_COUNTER
#define WOLFSSL_CMAC
#define WOLFSSL_SHA224
#define WOLFSSL_SHA3
#define WOLFSSL_SHAKE256
#define HAVE_HASHDRBG
#define HAVE_TLS_EXTENSIONS
#define HAVE_SUPPORTED_CURVES
#define HAVE_EXTENDED_MASTER
#define NO_RC4
#define HAVE_ENCRYPT_THEN_MAC
#define NO_PSK
#define NO_MD4
#define NO_PWDBASED
#define USE_FAST_MATH
#define WOLFSSL_X86_64_BUILD
#define WC_NO_ASYNC_THREADING
#define HAVE_DH_DEFAULT_PARAMS
#define HAVE___UINT128_T 1



/*-- Debugging options  ------------------------------------------------------
 *
 * "DEBUG_WOLFSSL" definition enables log to output into stdout.
 * Note: wolfSSL_Debugging_ON() must be called just after wolfSSL_Init().
 *----------------------------------------------------------------------------*/

/*#define DEBUG_WOLFSSL*/

#endif /* ifndef USER_SETTINGS_H_ */
