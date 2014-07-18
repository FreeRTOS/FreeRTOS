/* config-RTX-TCP-FS.h
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


/**** CyaSSL for KEIL-RL Configuration ****/

#define __CORTEX_M3__
#define CYASSL_MDK_ARM
#define NO_WRITEV
#define NO_CYASSL_DIR
#define NO_MAIN_DRIVER


#define CYASSL_DER_LOAD
#define HAVE_NULL_CIPHER

#define HAVE_KEIL_RTX
#define CYASSL_CMSIS_RTOS
#define CYASSL_KEIL_TCP_NET


// <<< Use Configuration Wizard in Context Menu >>>
// <h> CyaSSL Configuration

//     <h>SSL (Included by default)
//     </h>

//      <e>TLS 
#define MDK_CONF_TLS 1
#if MDK_CONF_TLS == 0
#define NO_TLS
#endif
//  </e>

//      <e>CRL
#define MDK_CONF_DER_LOAD 0
#if MDK_CONF_DER_LOAD == 1
#define CYASSL_DER_LOAD
#endif
//  </e>
//      <e>OpenSSL Extra
#define MDK_CONF_OPENSSL_EXTRA 1
#if MDK_CONF_OPENSSL_EXTRA == 1
#define OPENSSL_EXTRA
#endif
//  </e>
//</h>

//  <h>Cert/Key Generation
//      <e>CertGen
#define MDK_CONF_CERT_GEN 0
#if MDK_CONF_CERT_GEN == 1
#define CYASSL_CERT_GEN
#endif
//  </e>
//      <e>KeyGen
#define MDK_CONF_KEY_GEN 0
#if MDK_CONF_KEY_GEN == 1
#define CYASSL_KEY_GEN
#endif
//  </e>
//</h>

//  <h>Others

//      <e>Inline
#define MDK_CONF_INLINE 0
#if MDK_CONF_INLINE == 0
#define NO_INLINE
#endif
//  </e>
//      <h>Debug
//              <e>Debug Message
#define MDK_CONF_DebugMessage 0
#if MDK_CONF_DebugMessage == 1
#define DEBUG_CYASSL
#endif
//         </e>
//              <e>Check malloc
#define MDK_CONF_CheckMalloc 1
#if MDK_CONF_CheckMalloc == 1
#define CYASSL_MALLOC_CHECK
#endif
//         </e>


//  </h>
//      <e>ErrNo.h
#define MDK_CONF_ErrNo 0
#if MDK_CONF_ErrNo == 1
#define HAVE_ERRNO
#endif
//  </e>
//      <e>Error Strings
#define MDK_CONF_ErrorStrings 1
#if MDK_CONF_ErrorStrings == 0
#define NO_ERROR_STRINGS
#endif
//  </e>
//      <e>zlib (need "zlib.h")
#define MDK_CONF_LIBZ 0
#if MDK_CONF_LIBZ == 1
#define HAVE_LIBZ
#endif
//  </e>
//      <e>CAVIUM (need CAVIUM headers)
#define MDK_CONF_CAVIUM 0
#if MDK_CONF_CAVIUM == 1
#define HAVE_CAVIUM
#endif
//  </e>
//      <e>Small Stack
#define MDK_CONF_SmallStack 1
#if MDK_CONF_SmallStack == 0
#define NO_CYASSL_SMALL_STACK
#endif
//  </e>
//      <e>Use Fast Math
#define MDK_CONF_FASTMATH 0
#if MDK_CONF_FASTMATH == 1
#define USE_FAST_MATH
#endif
//  </e>
//  </h>

// <<< end of configuration section >>>
