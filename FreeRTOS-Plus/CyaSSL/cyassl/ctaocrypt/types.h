/* types.h
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


#ifndef CTAO_CRYPT_TYPES_H
#define CTAO_CRYPT_TYPES_H

#include <cyassl/ctaocrypt/settings.h>

#ifdef __cplusplus
    extern "C" {
#endif


#if defined(WORDS_BIGENDIAN) || (defined(__MWERKS__) && !defined(__INTEL__))
    #define BIG_ENDIAN_ORDER
#endif

#ifndef BIG_ENDIAN_ORDER
    #define LITTLE_ENDIAN_ORDER
#endif

#ifndef CYASSL_TYPES
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
        #elif (defined__i386__) 
            /* long long should be 64bit */
            #define SIZEOF_LONG_LONG 8
        #endif
    #endif
#endif


#if defined(_MSC_VER) || defined(__BCPLUSPLUS__)
    #define WORD64_AVAILABLE
    #define W64LIT(x) x##ui64
    typedef unsigned __int64 word64;
#elif SIZEOF_LONG == 8
    #define WORD64_AVAILABLE
    #define W64LIT(x) x##LL
    typedef unsigned long word64;
#elif SIZEOF_LONG_LONG == 8 
    #define WORD64_AVAILABLE
    #define W64LIT(x) x##LL
    typedef unsigned long long word64;
#else
    #define MP_16BIT  /* for mp_int, mp_word needs to be twice as big as
                         mp_digit, no 64 bit type so make mp_digit 16 bit */
#endif


/* These platforms have 64-bit CPU registers.  */
#if (defined(__alpha__) || defined(__ia64__) || defined(_ARCH_PPC64) || \
     defined(__mips64)  || defined(__x86_64__)) 
    typedef word64 word;
#else
    typedef word32 word;
    #ifdef WORD64_AVAILABLE
        #define CTAOCRYPT_SLOW_WORD64
    #endif
#endif


enum {
    WORD_SIZE  = sizeof(word),
    BIT_SIZE   = 8,
    WORD_BITS  = WORD_SIZE * BIT_SIZE
};


/* use inlining if compiler allows */
#ifndef INLINE
#ifndef NO_INLINE
    #ifdef _MSC_VER
        #define INLINE __inline
    #elif defined(__GNUC__)
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


/* Micrium will use Visual Studio for compilation but not the Win32 API */
#if defined(_WIN32) && !defined(MICRIUM) && !defined(FREERTOS)
    #define USE_WINDOWS_API
#endif


/* idea to add global alloc override by Moisés Guimarães  */
/* default to libc stuff */
/* XREALLOC is used once in normal math lib, not in fast math lib */
/* XFREE on some embeded systems doesn't like free(0) so test  */
#ifdef XMALLOC_USER
    /* prototypes for user heap override functions */
    #include <stddef.h>  /* for size_t */
    extern void *XMALLOC(size_t n, void* heap, int type);
    extern void *XREALLOC(void *p, size_t n, void* heap, int type);
    extern void XFREE(void *p, void* heap, int type);
#elif !defined(MICRIUM_MALLOC)
    /* default C runtime, can install different routines at runtime */
    #include <cyassl/ctaocrypt/memory.h>
    #define XMALLOC(s, h, t)     CyaSSL_Malloc((s))
    #define XFREE(p, h, t)       {void* xp = (p); if((xp)) CyaSSL_Free((xp));}
    #define XREALLOC(p, n, h, t) CyaSSL_Realloc((p), (n))
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
    /* strstr, strncmp, and strncat only used by CyaSSL proper, not required for
       CTaoCrypt only */
    #define XSTRSTR(s1,s2)    strstr((s1),(s2))
    #define XSTRNSTR(s1,s2,n) mystrnstr((s1),(s2),(n))
    #define XSTRNCMP(s1,s2,n) strncmp((s1),(s2),(n))
    #define XSTRNCAT(s1,s2,n) strncat((s1),(s2),(n))
#endif

#ifdef HAVE_ECC
    #ifndef CTYPE_USER
        #include <ctype.h>
        #define XTOUPPER(c)     toupper((c))
    #endif
#endif


/* memory allocation types for user hints */
enum {
    DYNAMIC_TYPE_CA         = 1,
    DYNAMIC_TYPE_CERT       = 2,
    DYNAMIC_TYPE_KEY        = 3,
    DYNAMIC_TYPE_FILE       = 4,
    DYNAMIC_TYPE_SUBJECT_CN = 5,
    DYNAMIC_TYPE_PUBLIC_KEY = 6,
    DYNAMIC_TYPE_SIGNER     = 7,
    DYNAMIC_TYPE_NONE       = 8,
    DYNAMIC_TYPE_BIGINT     = 9,
    DYNAMIC_TYPE_RSA        = 10,
    DYNAMIC_TYPE_METHOD     = 11,
    DYNAMIC_TYPE_OUT_BUFFER = 12,
    DYNAMIC_TYPE_IN_BUFFER  = 13,
    DYNAMIC_TYPE_INFO       = 14,
    DYNAMIC_TYPE_DH         = 15,
    DYNAMIC_TYPE_DOMAIN     = 16,
    DYNAMIC_TYPE_SSL        = 17,
    DYNAMIC_TYPE_CTX        = 18,
    DYNAMIC_TYPE_WRITEV     = 19,
    DYNAMIC_TYPE_OPENSSL    = 20,
    DYNAMIC_TYPE_DSA        = 21,
    DYNAMIC_TYPE_CRL        = 22,
    DYNAMIC_TYPE_REVOKED    = 23,
    DYNAMIC_TYPE_CRL_ENTRY  = 24,
    DYNAMIC_TYPE_CERT_MANAGER = 25,
    DYNAMIC_TYPE_CRL_MONITOR  = 26,
    DYNAMIC_TYPE_OCSP_STATUS  = 27,
    DYNAMIC_TYPE_OCSP_ENTRY   = 28,
    DYNAMIC_TYPE_ALTNAME      = 29
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


CYASSL_API word32 CheckRunTimeSettings(void);

/* If user uses RSA, DH, DSA, or ECC math lib directly then fast math and long
   types need to match at compile time and run time, CheckCtcSettings will
   return 1 if a match otherwise 0 */
#define CheckCtcSettings() (CTC_SETTINGS == CheckRunTimeSettings())


#ifdef __cplusplus
    }   /* extern "C" */
#endif


#endif /* CTAO_CRYPT_TYPES_H */

