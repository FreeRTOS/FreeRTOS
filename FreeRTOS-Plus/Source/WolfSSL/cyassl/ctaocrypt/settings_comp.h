/* settings_comp.h
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


#ifndef CTAO_CRYPT_SETTINGS_C_H
#define CTAO_CRYPT_SETTINGS_C_H


/* since fips overrides rsa.h map compatibility here */
#if !defined(NO_RSA)
	#ifdef WOLFSSL_KEY_GEN
	    #define RsaKeyToDer wc_RsaKeyToDer
	#endif

	#define RsaPrivateKeyDecode   wc_RsaPrivateKeyDecode
	#define RsaPublicKeyDecode    wc_RsaPublicKeyDecode
	#define RsaPublicKeyDecodeRaw wc_RsaPublicKeyDecodeRaw
#endif /* have rsa and HAVE_FIPS */

/* Macro redefinitions for compatibility */
#ifdef HAVE_NTRU
    #define MakeNtruCert wc_MakeNtruCert
#endif
#if defined(WOLFSSL_SHA512) && !defined(CYASSL_SHA512)
    #define CYASSL_SHA512
#endif
#if defined(WOLFSSL_SHA384) && !defined(CYASSL_SHA384)
    #define CYASSL_SHA384
#endif
#if defined(WOLFSSL_LEANPSK) && !defined(CYASSL_LEANPSK)
    #define CYASSL_LEANPSK
#endif
#if defined(NO_WOLFSSL_MEMORY) && !defined(NO_CYASSL_MEMORY)
    #define NO_CYASSL_MEMORY
#endif
#if defined(WOLFSSL_KEY_GEN) && !defined(CYASSL_KEY_GEN)
    #define CYASSL_KEY_GEN
#endif

/* AES */
#if defined(WOLFSSL_AES_DIRECT) && !defined(CYASSL_AES_DIRECT)
    #define CYASSL_AES_DIRECT
#endif
#if defined(WOLFSSL_AES_COUNTER) && !defined(CYASSL_AES_COUNTER)
    #define CYASSL_AES_COUNTER
#endif

/* DES */
#if defined(WOLFSSL_DES_ECB) && !defined(CYASSL_DES_ECB)
    #define CYASSL_DES_ECB
#endif

#endif /* CTAO_CRYPT_SETTINGS_C_H */

