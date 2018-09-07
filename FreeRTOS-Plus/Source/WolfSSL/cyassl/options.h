/* cyassl options.h
 * generated from wolfssl/options.h
 */
/* wolfssl options.h
* generated from configure options
*
* Copyright (C) 2006-2015 wolfSSL Inc.
*
* This file is part of wolfSSL. (formerly known as CyaSSL)
*
*/

#pragma once

#ifdef __cplusplus
extern "C" {
#endif

#ifndef WOLFSSL_OPTIONS_IGNORE_SYS
#undef  _POSIX_THREADS
#define _POSIX_THREADS
#endif

#undef  HAVE_THREAD_LS
#define HAVE_THREAD_LS

#ifndef WOLFSSL_OPTIONS_IGNORE_SYS
#undef  _THREAD_SAFE
#define _THREAD_SAFE
#endif

#undef  HAVE_AESGCM
#define HAVE_AESGCM

#undef  WOLFSSL_SHA512
#define WOLFSSL_SHA512

#undef  WOLFSSL_SHA384
#define WOLFSSL_SHA384

#undef  NO_DSA
#define NO_DSA

#undef  HAVE_ECC
#define HAVE_ECC

#undef  TFM_ECC256
#define TFM_ECC256

#undef  ECC_SHAMIR
#define ECC_SHAMIR

#undef  NO_PSK
#define NO_PSK

#undef  NO_RC4
#define NO_RC4

#undef  NO_MD4
#define NO_MD4

#undef  NO_HC128
#define NO_HC128

#undef  NO_RABBIT
#define NO_RABBIT

#undef  HAVE_POLY1305
#define HAVE_POLY1305

#undef  HAVE_ONE_TIME_AUTH
#define HAVE_ONE_TIME_AUTH

#undef  HAVE_CHACHA
#define HAVE_CHACHA

#undef  HAVE_HASHDRBG
#define HAVE_HASHDRBG

#undef  NO_PWDBASED
#define NO_PWDBASED

#undef  USE_FAST_MATH
#define USE_FAST_MATH

#undef  WOLFSSL_X86_64_BUILD
#define WOLFSSL_X86_64_BUILD


#ifdef __cplusplus
}
#endif

