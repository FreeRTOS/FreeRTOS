/* settings.h
 *
 * Copyright (C) 2006-2012 Sawtooth Consulting Ltd.
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

/* Place OS specific preprocessor flags, defines, includes here, will be
   included into every file because types.h includes it */


#ifndef CTAO_CRYPT_SETTINGS_H
#define CTAO_CRYPT_SETTINGS_H

#ifdef __cplusplus
    extern "C" {
#endif

/* Uncomment next line if using IPHONE */
/* #define IPHONE */

/* Uncomment next line if using ThreadX */
/* #define THREADX */

/* Uncomment next line if using Micrium ucOS */
/* #define MICRIUM */

/* Uncomment next line if using Mbed */
/* #define MBED */

/* Uncomment next line if using Microchip PIC32 ethernet starter kit */
/* #define MICROCHIP_PIC32 */

/* Uncomment next line if using FreeRTOS */
/* #define FREERTOS */

/* Uncomment next line if using FreeRTOS Windows Simulator */
/* #define FREERTOS_WINSIM */

/* Uncomment next line if using lwip */
/* #define CYASSL_LWIP */

/* Uncomment next line if building CyaSSL for a game console */
/* #define CYASSL_GAME_BUILD */


#include <cyassl/ctaocrypt/visibility.h>

#ifdef IPHONE
    #define SIZEOF_LONG_LONG 8
#endif

#ifdef THREADX 
    #define SIZEOF_LONG_LONG 8
#endif

#ifdef MICROCHIP_PIC32
    /* use MBED plus no filesystem */
    #define MBED
    #define NO_FILESYSTEM
#endif

#ifdef MBED
    #define SINGLE_THREADED
    #define CYASSL_USER_IO
    #define NO_WRITEV
    #define NO_DEV_RANDOM
    #define NO_SHA512
    #define NO_DH
    #define NO_DSA
    #define NO_HC128
#endif /* MBED */

#ifdef FREERTOS_WINSIM
    #define FREERTOS
    #define USE_WINDOWS_API
#endif

#ifdef FREERTOS
    #define NO_WRITEV
    #define NO_SHA512
    #define NO_DH
    #define NO_DSA
    #define NO_HC128

    #ifndef SINGLE_THREADED
        #include "FreeRTOS.h"
        #include "semphr.h"
    #endif
#endif

#ifdef CYASSL_GAME_BUILD
    #define SIZEOF_LONG_LONG 8
    #if defined(__PPU) || defined(__XENON)
        #define BIG_ENDIAN_ORDER
    #endif
#endif

#ifdef MICRIUM

    #include "stdlib.h"
    #include "net_cfg.h"
    #include "ssl_cfg.h"
    #include "net_secure_os.h"

    #define CYASSL_TYPES

    typedef CPU_INT08U byte;
    typedef CPU_INT16U word16;
    typedef CPU_INT32U word32;

    #if (NET_SECURE_MGR_CFG_WORD_SIZE == CPU_WORD_SIZE_32)
        #define SIZEOF_LONG        4
        #undef  SIZEOF_LONG_LONG
    #else
        #undef  SIZEOF_LONG
        #define SIZEOF_LONG_LONG   8
    #endif

    #define STRING_USER

    #define XSTRLEN(pstr) ((CPU_SIZE_T)Str_Len((CPU_CHAR *)(pstr)))
    #define XSTRNCPY(pstr_dest, pstr_src, len_max) \
                    ((CPU_CHAR *)Str_Copy_N((CPU_CHAR *)(pstr_dest), \
                     (CPU_CHAR *)(pstr_src), (CPU_SIZE_T)(len_max)))
    #define XSTRNCMP(pstr_1, pstr_2, len_max) \
                    ((CPU_INT16S)Str_Cmp_N((CPU_CHAR *)(pstr_1), \
                     (CPU_CHAR *)(pstr_2), (CPU_SIZE_T)(len_max)))  
    #define XSTRSTR(pstr, pstr_srch) \
                    ((CPU_CHAR *)Str_Str((CPU_CHAR *)(pstr), \
                     (CPU_CHAR *)(pstr_srch)))
    #define XMEMSET(pmem, data_val, size) \
                    ((void)Mem_Set((void *)(pmem), (CPU_INT08U) (data_val), \
                    (CPU_SIZE_T)(size)))
    #define XMEMCPY(pdest, psrc, size) ((void)Mem_Copy((void *)(pdest), \
                     (void *)(psrc), (CPU_SIZE_T)(size)))
    #define XMEMCMP(pmem_1, pmem_2, size) \
                   (((CPU_BOOLEAN)Mem_Cmp((void *)(pmem_1), (void *)(pmem_2), \
                     (CPU_SIZE_T)(size))) ? DEF_NO : DEF_YES)
    #define XMEMMOVE XMEMCPY

#if (NET_SECURE_MGR_CFG_EN == DEF_ENABLED)
    #define MICRIUM_MALLOC    
    #define XMALLOC(s, h, type) ((void *)NetSecure_BlkGet((CPU_INT08U)(type), \
                                 (CPU_SIZE_T)(s), (void *)0))
    #define XFREE(p, h, type)   (NetSecure_BlkFree((CPU_INT08U)(type), \
                                 (p), (void *)0))
    #define XREALLOC(p, n, h, t) realloc((p), (n))
#endif

    #if (NET_SECURE_MGR_CFG_FS_EN == DEF_ENABLED)
        #undef  NO_FILESYSTEM
    #else
        #define NO_FILESYSTEM
    #endif

    #if (SSL_CFG_TRACE_LEVEL == CYASSL_TRACE_LEVEL_DBG)
        #define DEBUG_CYASSL
    #else
        #undef  DEBUG_CYASSL
    #endif

    #if (SSL_CFG_OPENSSL_EN == DEF_ENABLED)
        #define OPENSSL_EXTRA
    #else
        #undef  OPENSSL_EXTRA
    #endif

    #if (SSL_CFG_MULTI_THREAD_EN == DEF_ENABLED)
        #undef  SINGLE_THREADED
    #else
        #define SINGLE_THREADED
    #endif

    #if (SSL_CFG_DH_EN == DEF_ENABLED)
        #undef  NO_DH
    #else
        #define NO_DH
    #endif

    #if (SSL_CFG_DSA_EN == DEF_ENABLED)
        #undef  NO_DSA
    #else
        #define NO_DSA
    #endif

    #if (SSL_CFG_PSK_EN == DEF_ENABLED)
        #undef  NO_PSK
    #else
        #define NO_PSK
    #endif

    #if (SSL_CFG_3DES_EN == DEF_ENABLED)
        #undef  NO_DES
    #else
        #define NO_DES
    #endif

    #if (SSL_CFG_AES_EN == DEF_ENABLED)
        #undef  NO_AES
    #else
        #define NO_AES
    #endif

    #if (SSL_CFG_RC4_EN == DEF_ENABLED)
        #undef  NO_RC4
    #else
        #define NO_RC4
    #endif

    #if (SSL_CFG_RABBIT_EN == DEF_ENABLED)
        #undef  NO_RABBIT
    #else
        #define NO_RABBIT
    #endif

    #if (SSL_CFG_HC128_EN == DEF_ENABLED)
        #undef  NO_HC128
    #else
        #define NO_HC128
    #endif

    #if (CPU_CFG_ENDIAN_TYPE == CPU_ENDIAN_TYPE_BIG)
        #define BIG_ENDIAN_ORDER
    #else
        #undef  BIG_ENDIAN_ORDER
        #define LITTLE_ENDIAN_ORDER
    #endif

    #if (SSL_CFG_MD4_EN == DEF_ENABLED)
        #undef  NO_MD4
    #else
        #define NO_MD4
    #endif

    #if (SSL_CFG_WRITEV_EN == DEF_ENABLED)
        #undef  NO_WRITEV
    #else
        #define NO_WRITEV
    #endif

    #if (SSL_CFG_USER_RNG_SEED_EN == DEF_ENABLED)
        #define NO_DEV_RANDOM   
    #else
        #undef  NO_DEV_RANDOM
    #endif

    #if (SSL_CFG_USER_IO_EN == DEF_ENABLED)
        #define CYASSL_USER_IO   
    #else
        #undef  CYASSL_USER_IO
    #endif

    #if (SSL_CFG_DYNAMIC_BUFFERS_EN == DEF_ENABLED)
        #undef  LARGE_STATIC_BUFFERS
        #undef  STATIC_CHUNKS_ONLY
    #else
        #define LARGE_STATIC_BUFFERS
        #define STATIC_CHUNKS_ONLY
    #endif

    #if (SSL_CFG_DER_LOAD_EN == DEF_ENABLED)
        #define  CYASSL_DER_LOAD
    #else
        #undef   CYASSL_DER_LOAD
    #endif

    #if (SSL_CFG_DTLS_EN == DEF_ENABLED)
        #define  CYASSL_DTLS
    #else
        #undef   CYASSL_DTLS
    #endif

    #if (SSL_CFG_CALLBACKS_EN == DEF_ENABLED)
         #define CYASSL_CALLBACKS
    #else
         #undef  CYASSL_CALLBACKS
    #endif

    #if (SSL_CFG_FAST_MATH_EN == DEF_ENABLED)
         #define USE_FAST_MATH
    #else
         #undef  USE_FAST_MATH
    #endif

    #if (SSL_CFG_TFM_TIMING_RESISTANT_EN == DEF_ENABLED)
         #define TFM_TIMING_RESISTANT
    #else
         #undef  TFM_TIMING_RESISTANT
    #endif

#endif /* MICRIUM */


#if !defined(XMALLOC_USER) && !defined(MICRIUM_MALLOC)
    #define USE_CYASSL_MEMORY
#endif

/* Place any other flags or defines here */


#ifdef __cplusplus
    }   /* extern "C" */
#endif


#endif /* CTAO_CRYPT_SETTINGS_H */

