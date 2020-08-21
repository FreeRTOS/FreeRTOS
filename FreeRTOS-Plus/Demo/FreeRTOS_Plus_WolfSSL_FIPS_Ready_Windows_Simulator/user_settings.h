/* user_settings.h
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




/*-- Cipher related definitions  -----------------------------------------------
 *
 *
 *----------------------------------------------------------------------------*/

   	#define HAVE_FIPS
	#define HAVE_FIPS_VERSION 2


	#define HAVE_FORCE_FIPS_FAILURE
	#define HAVE_HASHDRBG
	#define WOLFSSL_KEY_GEN	
	#define OPENSSL_EXTRA
	#define HAVE_THREAD_LS
	#define WOLFSSL_SHA3
	#define WOLFSSL_SHA224
	#define WOLFSSL_SHA384
	#define WOLFSSL_SHA512
	#define WOLFSSL_NO_SHAKE256	
	#define WOLFSSL_AES_COUNTER
	#define WOLFSSL_AES_DIRECT
	#define HAVE_AESCCM
	#define HAVE_AES_ECB
	#define HAVE_AESGCM
 
	#define WOLFSSL_CMAC
	#define HAVE_ECC
	#define HAVE_ECC_CDH
	#define ECC_SHAMIR
	#define HAVE_FFDHE_Q
	#define WC_RSA_PSS
	#define WC_RSA_NO_PADDING
	#define TFM_ECC256
	#define WOLFSSL_VALIDATE_ECC_IMPORT
	#define WOLFSSL_VALIDATE_FFC_IMPORT	
	#define HAVE_HKDF

	#define FORCE_FAILURE_RDSEED
	#define WOLFCRYPT_FIPS_RAND
	
	#define NO_PSK
	#define NO_RABIT
	#define NO_DSA
	#define NO_MD4

	#define HAVE_TLS_EXTENSIONS
	#define HAVE_SUPPORTED_CURVES
	#define HAVE_CURVE25519
	#define CURVE25519_SMALL
	#define HAVE_ED25519

	#define WC_RSA_BLINDING
	#define ECC_TIMING_RESISTANT
	#define TFM_TIMING_RESISTANT


/*-- Debugging options  ------------------------------------------------------
 *
 * "DEBUG_WOLFSSL" definition enables log to output into stdout.
 * Note: wolfSSL_Debugging_ON() must be called just after wolfSSL_Init().
 *----------------------------------------------------------------------------*/

/*#define DEBUG_WOLFSSL*/
	

