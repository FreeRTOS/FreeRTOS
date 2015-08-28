/* types.h
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


#ifndef WOLF_CRYPT_TYPES_H
#define WOLF_CRYPT_TYPES_H

	#include <wolfssl/wolfcrypt/settings.h>
	#include <wolfssl/wolfcrypt/wc_port.h>

	#ifdef __cplusplus
	    extern "C" {
	#endif


	#if defined(WORDS_BIGENDIAN)
	    #define BIG_ENDIAN_ORDER
	#endif

	#ifndef BIG_ENDIAN_ORDER
	    #define LITTLE_ENDIAN_ORDER
	#endif

	#ifndef WOLFSSL_TYPES
	    #ifndef byte
	        typedef unsigned char  byte;
	    #endif
	    typedef unsigned short word16;
	    typedef unsigned int   word32;
	#endif


	/* try to set SIZEOF_LONG or LONG_LONG if user didn't */
	#if !defined(_MSC_VER) && !defined(__BCPLUSPLUS__)
	    #if !defined(SIZEOF_LONG_LONG) && !defined(SIZEOF_LONG)
	        #if (defined(__alpha__) || defined(__ia64__) || defined(_ARCH_PPC64) \
	                || defined(__mips64)  || defined(__x86_64__))
	            /* long should be 64bit */
	            #define SIZEOF_LONG 8
	        #elif defined(__i386__) || defined(__CORTEX_M3__)
	            /* long long should be 64bit */
	            #define SIZEOF_LONG_LONG 8
	        #endif
	    #endif
	#endif


	#if defined(_MSC_VER) || defined(__BCPLUSPLUS__)
	    #define WORD64_AVAILABLE
	    #define W64LIT(x) x##ui64
	    typedef unsigned __int64 word64;
	#elif defined(SIZEOF_LONG) && SIZEOF_LONG == 8
	    #define WORD64_AVAILABLE
	    #define W64LIT(x) x##LL
	    typedef unsigned long word64;
	#elif defined(SIZEOF_LONG_LONG) && SIZEOF_LONG_LONG == 8
	    #define WORD64_AVAILABLE
	    #define W64LIT(x) x##LL
	    typedef unsigned long long word64;
	#elif defined(__SIZEOF_LONG_LONG__) && __SIZEOF_LONG_LONG__ == 8
	    #define WORD64_AVAILABLE
	    #define W64LIT(x) x##LL
	    typedef unsigned long long word64;
	#else
	    #define MP_16BIT  /* for mp_int, mp_word needs to be twice as big as
	                         mp_digit, no 64 bit type so make mp_digit 16 bit */
	#endif


	/* These platforms have 64-bit CPU registers.  */
	#if (defined(__alpha__) || defined(__ia64__) || defined(_ARCH_PPC64) || \
	     defined(__mips64)  || defined(__x86_64__) || defined(_M_X64))
	    typedef word64 wolfssl_word;
	#else
	    typedef word32 wolfssl_word;
	    #ifdef WORD64_AVAILABLE
	        #define WOLFCRYPT_SLOW_WORD64
	    #endif
	#endif


	enum {
	    WOLFSSL_WORD_SIZE  = sizeof(wolfssl_word),
	    WOLFSSL_BIT_SIZE   = 8,
	    WOLFSSL_WORD_BITS  = WOLFSSL_WORD_SIZE * WOLFSSL_BIT_SIZE
	};

	#define WOLFSSL_MAX_16BIT 0xffffU

	/* use inlining if compiler allows */
	#ifndef INLINE
	#ifndef NO_INLINE
	    #ifdef _MSC_VER
	        #define INLINE __inline
	    #elif defined(__GNUC__)
	        #define INLINE inline
	    #elif defined(__IAR_SYSTEMS_ICC__)
	        #define INLINE inline
	    #elif defined(THREADX)
	        #define INLINE _Inline
	    #else
	        #define INLINE
	    #endif
	#else
	    #define INLINE
	#endif
	#endif


	/* set up rotate style */
	#if defined(_MSC_VER) || defined(__BCPLUSPLUS__)
	    #define INTEL_INTRINSICS
	    #define FAST_ROTATE
	#elif defined(__MWERKS__) && TARGET_CPU_PPC
	    #define PPC_INTRINSICS
	    #define FAST_ROTATE
	#elif defined(__GNUC__) && defined(__i386__)
	        /* GCC does peephole optimizations which should result in using rotate
	           instructions  */
	    #define FAST_ROTATE
	#endif


	/* set up thread local storage if available */
	#ifdef HAVE_THREAD_LS
	    #if defined(_MSC_VER)
	        #define THREAD_LS_T __declspec(thread)
	    #else
	        #define THREAD_LS_T __thread
	    #endif
	#else
	    #define THREAD_LS_T
	#endif


	/* Micrium will use Visual Studio for compilation but not the Win32 API */
	#if defined(_WIN32) && !defined(MICRIUM) && !defined(FREERTOS) \
	        && !defined(EBSNET)
	    #define USE_WINDOWS_API
	#endif


	/* idea to add global alloc override by Moisés Guimarães  */
	/* default to libc stuff */
	/* XREALLOC is used once in normal math lib, not in fast math lib */
	/* XFREE on some embeded systems doesn't like free(0) so test  */
	#if defined(XMALLOC_USER)
	    /* prototypes for user heap override functions */
	    #include <stddef.h>  /* for size_t */
	    extern void *XMALLOC(size_t n, void* heap, int type);
	    extern void *XREALLOC(void *p, size_t n, void* heap, int type);
	    extern void XFREE(void *p, void* heap, int type);
	#elif defined(NO_WOLFSSL_MEMORY)
	    /* just use plain C stdlib stuff if desired */
	    #include <stdlib.h>
	    #define XMALLOC(s, h, t)     ((void)h, (void)t, malloc((s)))
	    #define XFREE(p, h, t)       {void* xp = (p); if((xp)) free((xp));}
	    #define XREALLOC(p, n, h, t) realloc((p), (n))
	#elif !defined(MICRIUM_MALLOC) && !defined(EBSNET) \
	        && !defined(WOLFSSL_SAFERTOS) && !defined(FREESCALE_MQX) \
	        && !defined(WOLFSSL_LEANPSK)
	    /* default C runtime, can install different routines at runtime via cbs */
	    #include <wolfssl/wolfcrypt/memory.h>
	    #define XMALLOC(s, h, t)     ((void)h, (void)t, wolfSSL_Malloc((s)))
	    #define XFREE(p, h, t)       {void* xp = (p); if((xp)) wolfSSL_Free((xp));}
	    #define XREALLOC(p, n, h, t) wolfSSL_Realloc((p), (n))
	#endif

	#ifndef STRING_USER
	    #include <string.h>
	    char* mystrnstr(const char* s1, const char* s2, unsigned int n);

	    #define XMEMCPY(d,s,l)    memcpy((d),(s),(l))
	    #define XMEMSET(b,c,l)    memset((b),(c),(l))
	    #define XMEMCMP(s1,s2,n)  memcmp((s1),(s2),(n))
	    #define XMEMMOVE(d,s,l)   memmove((d),(s),(l))

	    #define XSTRLEN(s1)       strlen((s1))
	    #define XSTRNCPY(s1,s2,n) strncpy((s1),(s2),(n))
	    /* strstr, strncmp, and strncat only used by wolfSSL proper, not required for
	       CTaoCrypt only */
	    #define XSTRSTR(s1,s2)    strstr((s1),(s2))
	    #define XSTRNSTR(s1,s2,n) mystrnstr((s1),(s2),(n))
	    #define XSTRNCMP(s1,s2,n) strncmp((s1),(s2),(n))
	    #define XSTRNCAT(s1,s2,n) strncat((s1),(s2),(n))
	    #ifndef USE_WINDOWS_API
	        #define XSTRNCASECMP(s1,s2,n) strncasecmp((s1),(s2),(n))
	        #define XSNPRINTF snprintf
	    #else
	        #define XSTRNCASECMP(s1,s2,n) _strnicmp((s1),(s2),(n))
	        #define XSNPRINTF _snprintf
	    #endif
	#endif

	#ifndef CTYPE_USER
	    #include <ctype.h>
	    #if defined(HAVE_ECC) || defined(HAVE_OCSP)
	        #define XTOUPPER(c)     toupper((c))
	        #define XISALPHA(c)     isalpha((c))
	    #endif
	    /* needed by wolfSSL_check_domain_name() */
	    #define XTOLOWER(c)      tolower((c))
	#endif


	/* memory allocation types for user hints */
	enum {
	    DYNAMIC_TYPE_CA           = 1,
	    DYNAMIC_TYPE_CERT         = 2,
	    DYNAMIC_TYPE_KEY          = 3,
	    DYNAMIC_TYPE_FILE         = 4,
	    DYNAMIC_TYPE_SUBJECT_CN   = 5,
	    DYNAMIC_TYPE_PUBLIC_KEY   = 6,
	    DYNAMIC_TYPE_SIGNER       = 7,
	    DYNAMIC_TYPE_NONE         = 8,
	    DYNAMIC_TYPE_BIGINT       = 9,
	    DYNAMIC_TYPE_RSA          = 10,
	    DYNAMIC_TYPE_METHOD       = 11,
	    DYNAMIC_TYPE_OUT_BUFFER   = 12,
	    DYNAMIC_TYPE_IN_BUFFER    = 13,
	    DYNAMIC_TYPE_INFO         = 14,
	    DYNAMIC_TYPE_DH           = 15,
	    DYNAMIC_TYPE_DOMAIN       = 16,
	    DYNAMIC_TYPE_SSL          = 17,
	    DYNAMIC_TYPE_CTX          = 18,
	    DYNAMIC_TYPE_WRITEV       = 19,
	    DYNAMIC_TYPE_OPENSSL      = 20,
	    DYNAMIC_TYPE_DSA          = 21,
	    DYNAMIC_TYPE_CRL          = 22,
	    DYNAMIC_TYPE_REVOKED      = 23,
	    DYNAMIC_TYPE_CRL_ENTRY    = 24,
	    DYNAMIC_TYPE_CERT_MANAGER = 25,
	    DYNAMIC_TYPE_CRL_MONITOR  = 26,
	    DYNAMIC_TYPE_OCSP_STATUS  = 27,
	    DYNAMIC_TYPE_OCSP_ENTRY   = 28,
	    DYNAMIC_TYPE_ALTNAME      = 29,
	    DYNAMIC_TYPE_SUITES       = 30,
	    DYNAMIC_TYPE_CIPHER       = 31,
	    DYNAMIC_TYPE_RNG          = 32,
	    DYNAMIC_TYPE_ARRAYS       = 33,
	    DYNAMIC_TYPE_DTLS_POOL    = 34,
	    DYNAMIC_TYPE_SOCKADDR     = 35,
	    DYNAMIC_TYPE_LIBZ         = 36,
	    DYNAMIC_TYPE_ECC          = 37,
	    DYNAMIC_TYPE_TMP_BUFFER   = 38,
	    DYNAMIC_TYPE_DTLS_MSG     = 39,
	    DYNAMIC_TYPE_CAVIUM_TMP   = 40,
	    DYNAMIC_TYPE_CAVIUM_RSA   = 41,
	    DYNAMIC_TYPE_X509         = 42,
	    DYNAMIC_TYPE_TLSX         = 43,
	    DYNAMIC_TYPE_OCSP         = 44,
	    DYNAMIC_TYPE_SIGNATURE    = 45,
	    DYNAMIC_TYPE_HASHES       = 46
	};

	/* max error buffer string size */
	enum {
	    WOLFSSL_MAX_ERROR_SZ = 80
	};

	/* stack protection */
	enum {
	    MIN_STACK_BUFFER = 8
	};



	/* settings detection for compile vs runtime math incombatibilities */
	enum {
	#if !defined(USE_FAST_MATH) && !defined(SIZEOF_LONG) && !defined(SIZEOF_LONG_LONG)
	    CTC_SETTINGS = 0x0
	#elif !defined(USE_FAST_MATH) && defined(SIZEOF_LONG) && (SIZEOF_LONG == 8)
	    CTC_SETTINGS = 0x1
	#elif !defined(USE_FAST_MATH) && defined(SIZEOF_LONG_LONG) && (SIZEOF_LONG_LONG == 8)
	    CTC_SETTINGS = 0x2
	#elif !defined(USE_FAST_MATH) && defined(SIZEOF_LONG_LONG) && (SIZEOF_LONG_LONG == 4)
	    CTC_SETTINGS = 0x4
	#elif defined(USE_FAST_MATH) && !defined(SIZEOF_LONG) && !defined(SIZEOF_LONG_LONG)
	    CTC_SETTINGS = 0x8
	#elif defined(USE_FAST_MATH) && defined(SIZEOF_LONG) && (SIZEOF_LONG == 8)
	    CTC_SETTINGS = 0x10
	#elif defined(USE_FAST_MATH) && defined(SIZEOF_LONG_LONG) && (SIZEOF_LONG_LONG == 8)
	    CTC_SETTINGS = 0x20
	#elif defined(USE_FAST_MATH) && defined(SIZEOF_LONG_LONG) && (SIZEOF_LONG_LONG == 4)
	    CTC_SETTINGS = 0x40
	#else
	    #error "bad math long / long long settings"
	#endif
	};


	WOLFSSL_API word32 CheckRunTimeSettings(void);

	/* If user uses RSA, DH, DSA, or ECC math lib directly then fast math and long
	   types need to match at compile time and run time, CheckCtcSettings will
	   return 1 if a match otherwise 0 */
	#define CheckCtcSettings() (CTC_SETTINGS == CheckRunTimeSettings())


	#ifdef __cplusplus
	    }   /* extern "C" */
	#endif

#endif /* WOLF_CRYPT_TYPES_H */
