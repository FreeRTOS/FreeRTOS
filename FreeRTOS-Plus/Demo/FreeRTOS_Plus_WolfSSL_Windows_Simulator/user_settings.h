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


#endif /* ifndef USER_SETTINGS_H_ */