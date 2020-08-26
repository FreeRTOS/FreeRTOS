/* user_settings.h
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
	

