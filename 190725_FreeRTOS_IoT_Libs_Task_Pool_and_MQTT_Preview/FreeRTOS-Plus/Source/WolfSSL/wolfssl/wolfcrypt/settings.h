/* settings.h
 *
 * Copyright (C) 2006-2015 wolfSSL Inc.
 *
 * This file is part of wolfSSL. (formerly known as CyaSSL)
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
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301, USA
 */

/* Place OS specific preprocessor flags, defines, includes here, will be
   included into every file because types.h includes it */


#ifndef WOLF_CRYPT_SETTINGS_H
#define WOLF_CRYPT_SETTINGS_H

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

/* Uncomment next line if using Microchip TCP/IP stack, version 5 */
/* #define MICROCHIP_TCPIP_V5 */

/* Uncomment next line if using Microchip TCP/IP stack, version 6 or later */
/* #define MICROCHIP_TCPIP */

/* Uncomment next line if using PIC32MZ Crypto Engine */
/* #define WOLFSSL_MICROCHIP_PIC32MZ */

/* Uncomment next line if using FreeRTOS */
/* #define FREERTOS */

/* Uncomment next line if using FreeRTOS Windows Simulator */
/* #define FREERTOS_WINSIM */

/* Uncomment next line if using RTIP */
/* #define EBSNET */

/* Uncomment next line if using lwip */
/* #define WOLFSSL_LWIP */

/* Uncomment next line if building wolfSSL for a game console */
/* #define WOLFSSL_GAME_BUILD */

/* Uncomment next line if building wolfSSL for LSR */
/* #define WOLFSSL_LSR */

/* Uncomment next line if building wolfSSL for Freescale MQX/RTCS/MFS */
/* #define FREESCALE_MQX */

/* Uncomment next line if using STM32F2 */
/* #define WOLFSSL_STM32F2 */

/* Uncomment next line if using Comverge settings */
/* #define COMVERGE */

/* Uncomment next line if using QL SEP settings */
/* #define WOLFSSL_QL */

/* Uncomment next line if building for EROAD */
/* #define WOLFSSL_EROAD */

/* Uncomment next line if building for IAR EWARM */
/* #define WOLFSSL_IAR_ARM */

/* Uncomment next line if using TI-RTOS settings */
/* #define WOLFSSL_TIRTOS */

/* Uncomment next line if building with PicoTCP */
/* #define WOLFSSL_PICOTCP */

/* Uncomment next line if building for PicoTCP demo bundle */
/* #define WOLFSSL_PICOTCP_DEMO */

/* Uncomment next line if building for uITRON4  */
/* #define WOLFSSL_uITRON4 */

/* Uncomment next line if building for uT-Kernel */
/* #define WOLFSSL_uTKERNEL2 */

/* Uncomment next line if using Max Strength build */
/* #define WOLFSSL_MAX_STRENGTH */

/* Uncomment next line if building for VxWorks */
/* #define WOLFSSL_VXWORKS */

#include <wolfssl/wolfcrypt/visibility.h>

#ifdef WOLFSSL_USER_SETTINGS
    #include <user_settings.h>
#endif


#ifdef IPHONE
    #define SIZEOF_LONG_LONG 8
#endif


#ifdef COMVERGE
    #define THREADX
    #define HAVE_NETX
    #define WOLFSSL_USER_IO
    #define NO_WRITEV
    #define NO_DEV_RANDOM
    #define NO_FILESYSTEM
    #define NO_SHA512
    #define NO_DH
    #define NO_DSA
    #define NO_HC128
    #define NO_RSA
    #define NO_SESSION_CACHE
    #define HAVE_ECC
#endif


#ifdef THREADX
    #define SIZEOF_LONG_LONG 8
#endif

#ifdef HAVE_NETX
    #include "nx_api.h"
#endif

#if defined(HAVE_LWIP_NATIVE) /* using LwIP native TCP socket */
    #define WOLFSSL_LWIP
    #define NO_WRITEV
    #define SINGLE_THREADED
    #define WOLFSSL_USER_IO
    #define NO_FILESYSTEM
#endif

#if defined(WOLFSSL_IAR_ARM)
    #define NO_MAIN_DRIVER
    #define SINGLE_THREADED
    #define USE_CERT_BUFFERS_1024
    #define BENCH_EMBEDDED
    #define NO_FILESYSTEM
    #define NO_WRITEV
    #define WOLFSSL_USER_IO
    #define  BENCH_EMBEDDED
#endif

#ifdef MICROCHIP_PIC32
    /* #define WOLFSSL_MICROCHIP_PIC32MZ */
    #define SIZEOF_LONG_LONG 8
    #define SINGLE_THREADED
    #define WOLFSSL_USER_IO
    #define NO_WRITEV
    #define NO_DEV_RANDOM
    #define NO_FILESYSTEM
    #define USE_FAST_MATH
    #define TFM_TIMING_RESISTANT
    #define NEED_AES_TABLES
#endif

#ifdef WOLFSSL_MICROCHIP_PIC32MZ
    #define WOLFSSL_PIC32MZ_CE
    #define WOLFSSL_PIC32MZ_CRYPT
    #define HAVE_AES_ENGINE
    #define WOLFSSL_PIC32MZ_RNG
    /* #define WOLFSSL_PIC32MZ_HASH */
    #define WOLFSSL_AES_COUNTER
    #define HAVE_AESGCM
    #define NO_BIG_INT
#endif

#ifdef MICROCHIP_TCPIP_V5
    /* include timer functions */
    #include "TCPIP Stack/TCPIP.h"
#endif

#ifdef MICROCHIP_TCPIP
    /* include timer, NTP functions */
    #ifdef MICROCHIP_MPLAB_HARMONY
        #include "tcpip/tcpip.h"
    #else
        #include "system/system_services.h"
        #include "tcpip/sntp.h"
    #endif
#endif

#ifdef MBED
    #define WOLFSSL_USER_IO
    #define NO_FILESYSTEM
    #define NO_CERT
    #define USE_CERT_BUFFERS_1024
    #define NO_WRITEV
    #define NO_DEV_RANDOM
    #define NO_SHA512
    #define NO_DH
    #define NO_DSA
    #define NO_HC128
    #define HAVE_ECC
    #define NO_SESSION_CACHE
    #define WOLFSSL_CMSIS_RTOS
#endif


#ifdef WOLFSSL_EROAD
    #define FREESCALE_MQX
    #define FREESCALE_MMCAU
    #define SINGLE_THREADED
    #define NO_STDIO_FILESYSTEM
    #define WOLFSSL_LEANPSK
    #define HAVE_NULL_CIPHER
    #define NO_OLD_TLS
    #define NO_ASN
    #define NO_BIG_INT
    #define NO_RSA
    #define NO_DSA
    #define NO_DH
    #define NO_CERTS
    #define NO_PWDBASED
    #define NO_DES3
    #define NO_MD4
    #define NO_RC4
    #define NO_MD5
    #define NO_SESSION_CACHE
    #define NO_MAIN_DRIVER
#endif

#ifdef WOLFSSL_PICOTCP
    #ifndef errno
        #define errno pico_err
    #endif
    #include "pico_defines.h"
    #include "pico_stack.h"
    #include "pico_constants.h"
    #include "pico_protocol.h"
    #define CUSTOM_RAND_GENERATE pico_rand
#endif

#ifdef WOLFSSL_PICOTCP_DEMO
    #define WOLFSSL_STM32
    #define USE_FAST_MATH
    #define TFM_TIMING_RESISTANT
    #define XMALLOC(s, h, type)  PICO_ZALLOC((s))
    #define XFREE(p, h, type)    PICO_FREE((p))
    #define SINGLE_THREADED
    #define NO_WRITEV
    #define WOLFSSL_USER_IO
    #define NO_DEV_RANDOM
    #define NO_FILESYSTEM
#endif

#ifdef FREERTOS_WINSIM
    #define FREERTOS
    #define USE_WINDOWS_API
#endif


#ifdef WOLFSSL_VXWORKS
    #define NO_DEV_RANDOM
    #define NO_WRITEV
#endif


/* Micrium will use Visual Studio for compilation but not the Win32 API */
#if defined(_WIN32) && !defined(MICRIUM) && !defined(FREERTOS) \
        && !defined(EBSNET) && !defined(WOLFSSL_EROAD)
    #define USE_WINDOWS_API
#endif


#if defined(WOLFSSL_LEANPSK) && !defined(XMALLOC_USER)
    #include <stdlib.h>
    #define XMALLOC(s, h, type)  malloc((s))
    #define XFREE(p, h, type)    free((p))
    #define XREALLOC(p, n, h, t) realloc((p), (n))
#endif

#if defined(XMALLOC_USER) && defined(SSN_BUILDING_LIBYASSL)
    #undef  XMALLOC
    #define XMALLOC     yaXMALLOC
    #undef  XFREE
    #define XFREE       yaXFREE
    #undef  XREALLOC
    #define XREALLOC    yaXREALLOC
#endif


#ifdef FREERTOS
    #ifndef NO_WRITEV
        #define NO_WRITEV
    #endif
    #ifndef HAVE_SHA512
        #ifndef NO_SHA512
            #define NO_SHA512
        #endif
    #endif
    #ifndef HAVE_DH
        #ifndef NO_DH
            #define NO_DH
        #endif
    #endif
    #ifndef NO_DSA
        #define NO_DSA
    #endif
    #ifndef NO_HC128
        #define NO_HC128
    #endif

    #ifndef SINGLE_THREADED
        #include "FreeRTOS.h"
        #include "semphr.h"
    #endif
#endif

#ifdef WOLFSSL_TIRTOS
    #define SIZEOF_LONG_LONG 8
    #define NO_WRITEV
    #define NO_WOLFSSL_DIR
    #define USE_FAST_MATH
    #define TFM_TIMING_RESISTANT
    #define NO_DEV_RANDOM
    #define NO_FILESYSTEM
    #define USE_CERT_BUFFERS_2048
    #define NO_ERROR_STRINGS
    #define USER_TIME

    #ifdef __IAR_SYSTEMS_ICC__
        #pragma diag_suppress=Pa089
    #elif !defined(__GNUC__)
        /* Suppress the sslpro warning */
        #pragma diag_suppress=11
    #endif

    #include <ti/sysbios/hal/Seconds.h>
#endif

#ifdef EBSNET
    #include "rtip.h"

    /* #define DEBUG_WOLFSSL */
    #define NO_WOLFSSL_DIR  /* tbd */

    #if (POLLOS)
        #define SINGLE_THREADED
    #endif

    #if (RTPLATFORM)
        #if (!RTP_LITTLE_ENDIAN)
            #define BIG_ENDIAN_ORDER
        #endif
    #else
        #if (!KS_LITTLE_ENDIAN)
            #define BIG_ENDIAN_ORDER
        #endif
    #endif

    #if (WINMSP3)
        #undef SIZEOF_LONG
        #define SIZEOF_LONG_LONG 8
    #else
        #sslpro: settings.h - please implement SIZEOF_LONG and SIZEOF_LONG_LONG
    #endif

    #define XMALLOC(s, h, type) ((void *)rtp_malloc((s), SSL_PRO_MALLOC))
    #define XFREE(p, h, type) (rtp_free(p))
    #define XREALLOC(p, n, h, t) realloc((p), (n))

#endif /* EBSNET */

#ifdef WOLFSSL_GAME_BUILD
    #define SIZEOF_LONG_LONG 8
    #if defined(__PPU) || defined(__XENON)
        #define BIG_ENDIAN_ORDER
    #endif
#endif

#ifdef WOLFSSL_LSR
    #define HAVE_WEBSERVER
    #define SIZEOF_LONG_LONG 8
    #define WOLFSSL_LOW_MEMORY
    #define NO_WRITEV
    #define NO_SHA512
    #define NO_DH
    #define NO_DSA
    #define NO_HC128
    #define NO_DEV_RANDOM
    #define NO_WOLFSSL_DIR
    #define NO_RABBIT
    #ifndef NO_FILESYSTEM
        #define LSR_FS
        #include "inc/hw_types.h"
        #include "fs.h"
    #endif
    #define WOLFSSL_LWIP
    #include <errno.h>  /* for tcp errno */
    #define WOLFSSL_SAFERTOS
    #if defined(__IAR_SYSTEMS_ICC__)
        /* enum uses enum */
        #pragma diag_suppress=Pa089
    #endif
#endif

#ifdef WOLFSSL_SAFERTOS
    #ifndef SINGLE_THREADED
        #include "SafeRTOS/semphr.h"
    #endif

    #include "SafeRTOS/heap.h"
    #define XMALLOC(s, h, type)  pvPortMalloc((s))
    #define XFREE(p, h, type)    vPortFree((p))
    #define XREALLOC(p, n, h, t) pvPortRealloc((p), (n))
#endif

#ifdef WOLFSSL_LOW_MEMORY
    #undef  RSA_LOW_MEM
    #define RSA_LOW_MEM
    #undef  WOLFSSL_SMALL_STACK
    #define WOLFSSL_SMALL_STACK
    #undef  TFM_TIMING_RESISTANT
    #define TFM_TIMING_RESISTANT
#endif

#ifdef FREESCALE_MQX
    #define SIZEOF_LONG_LONG 8
    #define NO_WRITEV
    #define NO_DEV_RANDOM
    #define NO_RABBIT
    #define NO_WOLFSSL_DIR
    #define USE_FAST_MATH
    #define TFM_TIMING_RESISTANT
    #define FREESCALE_K70_RNGA
    /* #define FREESCALE_K53_RNGB */
    #include "mqx.h"
    #ifndef NO_FILESYSTEM
        #include "mfs.h"
        #include "fio.h"
    #endif
    #ifndef SINGLE_THREADED
        #include "mutex.h"
    #endif

    #define XMALLOC(s, h, t)    (void *)_mem_alloc_system((s))
    #define XFREE(p, h, t)      {void* xp = (p); if ((xp)) _mem_free((xp));}
    /* Note: MQX has no realloc, using fastmath above */
#endif

#ifdef WOLFSSL_STM32F2
    #define SIZEOF_LONG_LONG 8
    #define NO_DEV_RANDOM
    #define NO_WOLFSSL_DIR
    #define NO_RABBIT
    #define STM32F2_RNG
    #define STM32F2_CRYPTO
    #define KEIL_INTRINSICS
#endif

#ifdef MICRIUM

    #include "stdlib.h"
    #include "net_cfg.h"
    #include "ssl_cfg.h"
    #include "net_secure_os.h"

    #define WOLFSSL_TYPES

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

    #if (SSL_CFG_TRACE_LEVEL == WOLFSSL_TRACE_LEVEL_DBG)
        #define DEBUG_WOLFSSL
    #else
        #undef  DEBUG_WOLFSSL
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
        #define WOLFSSL_USER_IO
    #else
        #undef  WOLFSSL_USER_IO
    #endif

    #if (SSL_CFG_DYNAMIC_BUFFERS_EN == DEF_ENABLED)
        #undef  LARGE_STATIC_BUFFERS
        #undef  STATIC_CHUNKS_ONLY
    #else
        #define LARGE_STATIC_BUFFERS
        #define STATIC_CHUNKS_ONLY
    #endif

    #if (SSL_CFG_DER_LOAD_EN == DEF_ENABLED)
        #define  WOLFSSL_DER_LOAD
    #else
        #undef   WOLFSSL_DER_LOAD
    #endif

    #if (SSL_CFG_DTLS_EN == DEF_ENABLED)
        #define  WOLFSSL_DTLS
    #else
        #undef   WOLFSSL_DTLS
    #endif

    #if (SSL_CFG_CALLBACKS_EN == DEF_ENABLED)
         #define WOLFSSL_CALLBACKS
    #else
         #undef  WOLFSSL_CALLBACKS
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


#ifdef WOLFSSL_QL
    #ifndef WOLFSSL_SEP
        #define WOLFSSL_SEP
    #endif
    #ifndef OPENSSL_EXTRA
        #define OPENSSL_EXTRA
    #endif
    #ifndef SESSION_CERTS
        #define SESSION_CERTS
    #endif
    #ifndef HAVE_AESCCM
        #define HAVE_AESCCM
    #endif
    #ifndef ATOMIC_USER
        #define ATOMIC_USER
    #endif
    #ifndef WOLFSSL_DER_LOAD
        #define WOLFSSL_DER_LOAD
    #endif
    #ifndef KEEP_PEER_CERT
        #define KEEP_PEER_CERT
    #endif
    #ifndef HAVE_ECC
        #define HAVE_ECC
    #endif
    #ifndef SESSION_INDEX
        #define SESSION_INDEX
    #endif
#endif /* WOLFSSL_QL */


#if !defined(XMALLOC_USER) && !defined(MICRIUM_MALLOC) && \
    !defined(WOLFSSL_LEANPSK) && !defined(NO_WOLFSSL_MEMORY)
    #define USE_WOLFSSL_MEMORY
#endif


#if defined(OPENSSL_EXTRA) && !defined(NO_CERTS)
    #undef  KEEP_PEER_CERT
    #define KEEP_PEER_CERT
#endif


/* stream ciphers except arc4 need 32bit alignment, intel ok without */
#ifndef XSTREAM_ALIGN
    #if defined(__x86_64__) || defined(__ia64__) || defined(__i386__)
        #define NO_XSTREAM_ALIGN
    #else
        #define XSTREAM_ALIGN
    #endif
#endif


/* FreeScale MMCAU hardware crypto has 4 byte alignment */
#ifdef FREESCALE_MMCAU
    #define WOLFSSL_MMCAU_ALIGNMENT 4
#endif

/* if using hardware crypto and have alignment requirements, specify the
   requirement here.  The record header of SSL/TLS will prvent easy alignment.
   This hint tries to help as much as possible.  */
#ifndef WOLFSSL_GENERAL_ALIGNMENT
    #ifdef WOLFSSL_AESNI
        #define WOLFSSL_GENERAL_ALIGNMENT 16
    #elif defined(XSTREAM_ALIGN)
        #define WOLFSSL_GENERAL_ALIGNMENT  4
    #elif defined(FREESCALE_MMCAU)
        #define WOLFSSL_GENERAL_ALIGNMENT  WOLFSSL_MMCAU_ALIGNMENT
    #else
        #define WOLFSSL_GENERAL_ALIGNMENT  0
    #endif
#endif

#if defined(WOLFSSL_GENERAL_ALIGNMENT) && (WOLFSSL_GENERAL_ALIGNMENT > 0)
    #if defined(_MSC_VER)
        #define XGEN_ALIGN __declspec(align(WOLFSSL_GENERAL_ALIGNMENT))
    #elif defined(__GNUC__)
        #define XGEN_ALIGN __attribute__((aligned(WOLFSSL_GENERAL_ALIGNMENT)))
    #else
        #define XGEN_ALIGN
    #endif
#else
    #define XGEN_ALIGN
#endif

#ifdef HAVE_CRL
    /* not widely supported yet */
    #undef NO_SKID
    #define NO_SKID
#endif


#ifdef __INTEL_COMPILER
    #pragma warning(disable:2259) /* explicit casts to smaller sizes, disable */
#endif

/* user can specify what curves they want with ECC_USER_CURVES otherwise
 * all curves are on by default for now */
#ifndef ECC_USER_CURVES
    #ifndef HAVE_ALL_CURVES
        #define HAVE_ALL_CURVES
    #endif
#endif

/* if desktop type system and fastmath increase default max bits */
#ifdef WOLFSSL_X86_64_BUILD
    #ifdef USE_FAST_MATH
        #ifndef FP_MAX_BITS
            #define FP_MAX_BITS 8192
        #endif
    #endif
#endif

/* If using the max strength build, ensure OLD TLS is disabled. */
#ifdef WOLFSSL_MAX_STRENGTH
    #undef NO_OLD_TLS
    #define NO_OLD_TLS
#endif

/* Place any other flags or defines here */


#ifdef __cplusplus
    }   /* extern "C" */
#endif

#endif
