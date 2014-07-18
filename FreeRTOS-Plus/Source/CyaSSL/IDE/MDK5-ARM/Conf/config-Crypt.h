/* config-FS.h
 *
 * Copyright (C) 2006-2013 wolfSSL Inc.
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
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA
 */


// <<< Use Configuration Wizard in Context Menu >>>

// <h> wolfCrypt Configuration

//  <h>Cert/Key Strage
//        <o>Cert Storage <0=> SD Card <1=> Mem Buff (1024bytes) <2=> Mem Buff (2048bytes)
#define MDK_CONF_CERT_BUFF 0
#if MDK_CONF_CERT_BUFF== 1
#define USE_CERT_BUFFERS_1024
#elif MDK_CONF_CERT_BUFF == 2
#define USE_CERT_BUFFERS_2048
#endif
//</h>

//  <h>Crypt Algrithm

//       <h>MD5, SHA, SHA-256, AES, RC4, ASN, RSA
//        </h>

//      <e>MD2
#define MDK_CONF_MD2 0
#if MDK_CONF_MD2 == 1
#define CYASSL_MD2
#endif
//  </e>
//      <e>MD4
#define MDK_CONF_MD4 1
#if MDK_CONF_MD4 == 0
#define NO_MD4
#endif
//  </e>
//      <e>SHA-384
//          <i>This has to be with SHA512
#define MDK_CONF_SHA384 0
#if MDK_CONF_SHA384 == 1
#define CYASSL_SHA384
#endif
//  </e>
//      <e>SHA-512          
#define MDK_CONF_SHA512     0
#if MDK_CONF_SHA512     == 1
#define CYASSL_SHA512   
#endif
//  </e>
//      <e>RIPEMD
#define MDK_CONF_RIPEMD 0
#if MDK_CONF_RIPEMD == 1
#define CYASSL_RIPEMD
#endif
//  </e>
//      <e>HMAC
#define MDK_CONF_HMAC 1
#if MDK_CONF_HMAC == 0
#define NO_HMAC
#endif
//  </e>
//      <e>HC128
#define MDK_CONF_HC128 0
#if MDK_CONF_HC128 == 1
#define HAVE_HC128
#endif
//  </e>
//  <e>RABBIT
#define MDK_CONF_RABBIT 1
#if MDK_CONF_RABBI == 0
#define NO_RABBIT
#endif
//  </e>

//      <e>AEAD     
#define MDK_CONF_AEAD 0
#if MDK_CONF_AEAD == 1
#define HAVE_AEAD
#endif
//  </e>
//      <e>DES3
#define MDK_CONF_DES3 1
#if MDK_CONF_DES3 == 0
#define NO_DES3
#endif
//  </e>
//      <e>CAMELLIA
#define MDK_CONF_CAMELLIA 0
#if MDK_CONF_CAMELLIA == 1
#define HAVE_CAMELLIA
#endif
//  </e>

//      <e>DH
//              <i>need this for CYASSL_SERVER, OPENSSL_EXTRA
#define MDK_CONF_DH 1
#if MDK_CONF_DH == 0
#define NO_DH
#endif
//  </e>
//      <e>DSA
#define MDK_CONF_DSA 1 
#if MDK_CONF_DSA == 0
#define NO_DSA
#endif
//  </e>
//      <e>PWDBASED
#define MDK_CONF_PWDBASED 1
#if MDK_CONF_PWDBASED == 0
#define NO_PWDBASED
#endif
//  </e>

//      <e>ECC
#define MDK_CONF_ECC 0
#if MDK_CONF_ECC == 1
#define HAVE_ECC
#endif
//  </e>
//      <e>PSK
#define MDK_CONF_PSK 1
#if MDK_CONF_PSK == 0
#define NO_PSK
#endif
//  </e>
//      <e>AESCCM (Turn off Hardware Crypt)
#define MDK_CONF_AESCCM 0
#if MDK_CONF_AESCCM == 1
#define HAVE_AESCCM
#endif
//  </e>
//      <e>AESGCM (Turn off Hardware Crypt)
#define MDK_CONF_AESGCM 0
#if MDK_CONF_AESGCM == 1
#define HAVE_AESGCM
#define BUILD_AESGCM
#endif
//  </e>
//      <e>NTRU (need License, "crypto_ntru.h")
#define MDK_CONF_NTRU 0
#if MDK_CONF_NTRU == 1
#define HAVE_NTRU
#endif
//  </e>
//  </h>

//  <h>Hardware Crypt (See document for usage)
//      <e>Hardware RNG
#define MDK_CONF_STM32F2_RNG 0
#if MDK_CONF_STM32F2_RNG == 1
#define STM32F2_RNG
#else

#endif
//  </e>
//      <e>Hardware Crypt
#define MDK_CONF_STM32F2_CRYPTO 0
#if MDK_CONF_STM32F2_CRYPTO == 1
#define STM32F2_CRYPTO
#endif
//  </e>

// </h>



//</h>
// <<< end of configuration section >>>
