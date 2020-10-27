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
  #define WOLFSSL_TLS13
  #define HAVE_FFDHE_2048
  #define WC_RSA_PSS
  #define HAVE_HKDF

  
  #define HAVE_AESGCM
  #define WOLFSSL_AES_128
  #define HAVE_AES_CBC
  #define WOLFSSL_SHA512

  #define HAVE_TLS_EXTENSIONS
  #define HAVE_SUPPORTED_CURVES
  #define HAVE_ECC
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

