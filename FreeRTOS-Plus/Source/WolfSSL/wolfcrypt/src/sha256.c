/* sha256.c
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

/* code submitted by raphael.huck@efixo.com */

#ifdef HAVE_CONFIG_H
    #include <config.h>
#endif

#include <wolfssl/wolfcrypt/settings.h>
#include <wolfssl/wolfcrypt/sha256.h>

#if !defined(NO_SHA256)
#ifdef HAVE_FIPS

int wc_InitSha256(Sha256* sha)
{
    return InitSha256_fips(sha);
}


int wc_Sha256Update(Sha256* sha, const byte* data, word32 len)
{
    return Sha256Update_fips(sha, data, len);
}


int wc_Sha256Final(Sha256* sha, byte* out)
{
    return Sha256Final_fips(sha, out);
}


int wc_Sha256Hash(const byte* data, word32 len, byte* out)
{
    return Sha256Hash(data, len, out);
}

#else /* else build without fips */

#if !defined(NO_SHA256) && defined(WOLFSSL_TI_HASH)
    /* #include <wolfcrypt/src/port/ti/ti-hash.c> included by wc_port.c */
#else

#if !defined (ALIGN32)
    #if defined (__GNUC__)
        #define ALIGN32 __attribute__ ( (aligned (32)))
    #elif defined(_MSC_VER)
        /* disable align warning, we want alignment ! */
        #pragma warning(disable: 4324)
        #define ALIGN32 __declspec (align (32))
    #else
        #define ALIGN32
    #endif
#endif

#ifdef WOLFSSL_PIC32MZ_HASH
#define wc_InitSha256   wc_InitSha256_sw
#define wc_Sha256Update wc_Sha256Update_sw
#define wc_Sha256Final  wc_Sha256Final_sw
#endif

#ifdef HAVE_FIPS
    /* set NO_WRAPPERS before headers, use direct internal f()s not wrappers */
    #define FIPS_NO_WRAPPERS
#endif

#if defined(USE_INTEL_SPEEDUP)
#define HAVE_INTEL_AVX1
#define HAVE_INTEL_AVX2

#if defined(DEBUG_XMM)
#include "stdio.h"
#endif

#endif

#if defined(HAVE_INTEL_AVX2)
#define HAVE_INTEL_RORX
#endif
 

/*****
Intel AVX1/AVX2 Macro Control Structure

#define HAVE_INTEL_AVX1
#define HAVE_INTEL_AVX2

#define HAVE_INTEL_RORX


int InitSha256(Sha256* sha256) { 
     Save/Recover XMM, YMM
     ...
}

#if defined(HAVE_INTEL_AVX1)|| defined(HAVE_INTEL_AVX2)
  Transform() ; Function prototype 
#else
  Transform() {   }
  int Sha256Final() { 
     Save/Recover XMM, YMM
     ...
  }
#endif

#if defined(HAVE_INTEL_AVX1)|| defined(HAVE_INTEL_AVX2)
    #if defined(HAVE_INTEL_RORX
         #define RND with rorx instuction
    #else
        #define RND
    #endif
#endif

#if defined(HAVE_INTEL_AVX1)
   
   #define XMM Instructions/inline asm
   
   int Transform() {
       Stitched Message Sched/Round
    } 
   
#elif defined(HAVE_INTEL_AVX2)
  
  #define YMM Instructions/inline asm
  
  int Transform() {
      More granural Stitched Message Sched/Round
  }
  
*/


#if defined(HAVE_INTEL_AVX1) || defined(HAVE_INTEL_AVX2)

/* Each platform needs to query info type 1 from cpuid to see if aesni is
 * supported. Also, let's setup a macro for proper linkage w/o ABI conflicts
 */

#ifndef _MSC_VER
    #define cpuid(reg, leaf, sub)\
            __asm__ __volatile__ ("cpuid":\
             "=a" (reg[0]), "=b" (reg[1]), "=c" (reg[2]), "=d" (reg[3]) :\
             "a" (leaf), "c"(sub));

    #define XASM_LINK(f) asm(f)
#else

    #include <intrin.h>
    #define cpuid(a,b) __cpuid((int*)a,b)

    #define XASM_LINK(f)

#endif /* _MSC_VER */

#define EAX 0
#define EBX 1
#define ECX 2 
#define EDX 3
    
#define CPUID_AVX1   0x1
#define CPUID_AVX2   0x2
#define CPUID_RDRAND 0x4
#define CPUID_RDSEED 0x8
#define CPUID_BMI2   0x10   /* MULX, RORX */

#define IS_INTEL_AVX1       (cpuid_flags&CPUID_AVX1)
#define IS_INTEL_AVX2       (cpuid_flags&CPUID_AVX2)
#define IS_INTEL_BMI2       (cpuid_flags&CPUID_BMI2)
#define IS_INTEL_RDRAND     (cpuid_flags&CPUID_RDRAND)
#define IS_INTEL_RDSEED     (cpuid_flags&CPUID_RDSEED)

static word32 cpuid_check = 0 ;
static word32 cpuid_flags = 0 ;

static word32 cpuid_flag(word32 leaf, word32 sub, word32 num, word32 bit) {
    int got_intel_cpu=0;
    unsigned int reg[5]; 
    
    reg[4] = '\0' ;
    cpuid(reg, 0, 0);  
    if(memcmp((char *)&(reg[EBX]), "Genu", 4) == 0 &&  
                memcmp((char *)&(reg[EDX]), "ineI", 4) == 0 &&  
                memcmp((char *)&(reg[ECX]), "ntel", 4) == 0) {  
        got_intel_cpu = 1;  
    }    
    if (got_intel_cpu) {
        cpuid(reg, leaf, sub);
        return((reg[num]>>bit)&0x1) ;
    }
    return 0 ;
}

static int set_cpuid_flags(void) {  
    if(cpuid_check==0) {
        if(cpuid_flag(1, 0, ECX, 28)){ cpuid_flags |= CPUID_AVX1 ;}
        if(cpuid_flag(7, 0, EBX, 5)){  cpuid_flags |= CPUID_AVX2 ; }
        if(cpuid_flag(7, 0, EBX, 8)) { cpuid_flags |= CPUID_BMI2 ; }
        if(cpuid_flag(1, 0, ECX, 30)){ cpuid_flags |= CPUID_RDRAND ;  } 
        if(cpuid_flag(7, 0, EBX, 18)){ cpuid_flags |= CPUID_RDSEED ;  }
        cpuid_check = 1 ;
        return 0 ;
    }
    return 1 ;
}


/* #if defined(HAVE_INTEL_AVX1/2) at the tail of sha512 */
static int Transform(Sha256* sha256);

#if defined(HAVE_INTEL_AVX1)
static int Transform_AVX1(Sha256 *sha256) ;
#endif
#if defined(HAVE_INTEL_AVX2)
static int Transform_AVX2(Sha256 *sha256) ; 
static int Transform_AVX1_RORX(Sha256 *sha256) ; 
#endif

static int (*Transform_p)(Sha256* sha256) /* = _Transform */;

#define XTRANSFORM(sha256, B)  (*Transform_p)(sha256)

static void set_Transform(void) {
     if(set_cpuid_flags())return ;

#if defined(HAVE_INTEL_AVX2)
     if(IS_INTEL_AVX2 && IS_INTEL_BMI2){ 
         Transform_p = Transform_AVX1_RORX; return ; 
         Transform_p = Transform_AVX2      ; 
                  /* for avoiding warning,"not used" */
     }
#endif
#if defined(HAVE_INTEL_AVX1)
     Transform_p = ((IS_INTEL_AVX1) ? Transform_AVX1 : Transform) ; return ;
#endif
     Transform_p = Transform ; return ;
}

#else
   #if defined(FREESCALE_MMCAU)
      #define XTRANSFORM(sha256, B) Transform(sha256, B)
   #else
      #define XTRANSFORM(sha256, B) Transform(sha256)
   #endif
#endif

/* Dummy for saving MM_REGs on behalf of Transform */
#if defined(HAVE_INTEL_AVX2)&& !defined(HAVE_INTEL_AVX1)
#define  SAVE_XMM_YMM   __asm__ volatile("or %%r8d, %%r8d":::\
  "%ymm4","%ymm5","%ymm6","%ymm7","%ymm8","%ymm9","%ymm10","%ymm11","%ymm12","%ymm13","%ymm14","%ymm15")
#elif defined(HAVE_INTEL_AVX1)
#define  SAVE_XMM_YMM   __asm__ volatile("or %%r8d, %%r8d":::\
    "xmm0","xmm1","xmm2","xmm3","xmm4","xmm5","xmm6","xmm7","xmm8","xmm9","xmm10",\
    "xmm11","xmm12","xmm13","xmm14","xmm15")
#else
#define  SAVE_XMM_YMM
#endif

#ifdef WOLFSSL_PIC32MZ_HASH
#define InitSha256   InitSha256_sw
#define Sha256Update Sha256Update_sw
#define Sha256Final  Sha256Final_sw
#endif

#include <wolfssl/wolfcrypt/logging.h>
#include <wolfssl/wolfcrypt/error-crypt.h>

#ifdef NO_INLINE
    #include <wolfssl/wolfcrypt/misc.h>
#else
    #include <wolfcrypt/src/misc.c>
#endif

#ifdef FREESCALE_MMCAU
    #include "cau_api.h"
#endif

#ifndef WOLFSSL_HAVE_MIN
#define WOLFSSL_HAVE_MIN

    static INLINE word32 min(word32 a, word32 b)
    {
        return a > b ? b : a;
    }

#endif /* WOLFSSL_HAVE_MIN */


int wc_InitSha256(Sha256* sha256)
{
    #ifdef FREESCALE_MMCAU
        cau_sha256_initialize_output(sha256->digest);
    #else
        sha256->digest[0] = 0x6A09E667L;
        sha256->digest[1] = 0xBB67AE85L;
        sha256->digest[2] = 0x3C6EF372L;
        sha256->digest[3] = 0xA54FF53AL;
        sha256->digest[4] = 0x510E527FL;
        sha256->digest[5] = 0x9B05688CL;
        sha256->digest[6] = 0x1F83D9ABL;
        sha256->digest[7] = 0x5BE0CD19L;
    #endif

    sha256->buffLen = 0;
    sha256->loLen   = 0;
    sha256->hiLen   = 0;
    
#if defined(HAVE_INTEL_AVX1)|| defined(HAVE_INTEL_AVX2)
    set_Transform() ; /* choose best Transform function under this runtime environment */
#endif

    return 0;
}


#if !defined(FREESCALE_MMCAU)
static const ALIGN32 word32 K[64] = {
    0x428A2F98L, 0x71374491L, 0xB5C0FBCFL, 0xE9B5DBA5L, 0x3956C25BL,
    0x59F111F1L, 0x923F82A4L, 0xAB1C5ED5L, 0xD807AA98L, 0x12835B01L,
    0x243185BEL, 0x550C7DC3L, 0x72BE5D74L, 0x80DEB1FEL, 0x9BDC06A7L,
    0xC19BF174L, 0xE49B69C1L, 0xEFBE4786L, 0x0FC19DC6L, 0x240CA1CCL,
    0x2DE92C6FL, 0x4A7484AAL, 0x5CB0A9DCL, 0x76F988DAL, 0x983E5152L,
    0xA831C66DL, 0xB00327C8L, 0xBF597FC7L, 0xC6E00BF3L, 0xD5A79147L,
    0x06CA6351L, 0x14292967L, 0x27B70A85L, 0x2E1B2138L, 0x4D2C6DFCL,
    0x53380D13L, 0x650A7354L, 0x766A0ABBL, 0x81C2C92EL, 0x92722C85L,
    0xA2BFE8A1L, 0xA81A664BL, 0xC24B8B70L, 0xC76C51A3L, 0xD192E819L,
    0xD6990624L, 0xF40E3585L, 0x106AA070L, 0x19A4C116L, 0x1E376C08L,
    0x2748774CL, 0x34B0BCB5L, 0x391C0CB3L, 0x4ED8AA4AL, 0x5B9CCA4FL,
    0x682E6FF3L, 0x748F82EEL, 0x78A5636FL, 0x84C87814L, 0x8CC70208L,
    0x90BEFFFAL, 0xA4506CEBL, 0xBEF9A3F7L, 0xC67178F2L
};

#endif

#if defined(FREESCALE_MMCAU)

static int Transform(Sha256* sha256, byte* buf)
{
    cau_sha256_hash_n(buf, 1, sha256->digest);

    return 0;
}

#endif /* FREESCALE_MMCAU */

#define Ch(x,y,z)       ((z) ^ ((x) & ((y) ^ (z))))
#define Maj(x,y,z)      ((((x) | (y)) & (z)) | ((x) & (y)))
#define R(x, n)         (((x)&0xFFFFFFFFU)>>(n))

#define S(x, n)         rotrFixed(x, n)
#define Sigma0(x)       (S(x, 2) ^ S(x, 13) ^ S(x, 22))
#define Sigma1(x)       (S(x, 6) ^ S(x, 11) ^ S(x, 25))
#define Gamma0(x)       (S(x, 7) ^ S(x, 18) ^ R(x, 3))
#define Gamma1(x)       (S(x, 17) ^ S(x, 19) ^ R(x, 10))

#define RND(a,b,c,d,e,f,g,h,i) \
     t0 = (h) + Sigma1((e)) + Ch((e), (f), (g)) + K[(i)] + W[(i)]; \
     t1 = Sigma0((a)) + Maj((a), (b), (c)); \
     (d) += t0; \
     (h)  = t0 + t1;

#if !defined(FREESCALE_MMCAU)
static int Transform(Sha256* sha256)
{
    word32 S[8], t0, t1;
    int i;

#ifdef WOLFSSL_SMALL_STACK
    word32* W;

    W = (word32*) XMALLOC(sizeof(word32) * 64, NULL, DYNAMIC_TYPE_TMP_BUFFER);
    if (W == NULL)
        return MEMORY_E;
#else
    word32 W[64];
#endif

    /* Copy context->state[] to working vars */
    for (i = 0; i < 8; i++)
        S[i] = sha256->digest[i];

    for (i = 0; i < 16; i++)
        W[i] = sha256->buffer[i];

    for (i = 16; i < 64; i++)
        W[i] = Gamma1(W[i-2]) + W[i-7] + Gamma0(W[i-15]) + W[i-16];

    for (i = 0; i < 64; i += 8) {
        RND(S[0],S[1],S[2],S[3],S[4],S[5],S[6],S[7],i+0);
        RND(S[7],S[0],S[1],S[2],S[3],S[4],S[5],S[6],i+1);
        RND(S[6],S[7],S[0],S[1],S[2],S[3],S[4],S[5],i+2);
        RND(S[5],S[6],S[7],S[0],S[1],S[2],S[3],S[4],i+3);
        RND(S[4],S[5],S[6],S[7],S[0],S[1],S[2],S[3],i+4);
        RND(S[3],S[4],S[5],S[6],S[7],S[0],S[1],S[2],i+5);
        RND(S[2],S[3],S[4],S[5],S[6],S[7],S[0],S[1],i+6);
        RND(S[1],S[2],S[3],S[4],S[5],S[6],S[7],S[0],i+7);
    }

    /* Add the working vars back into digest state[] */
    for (i = 0; i < 8; i++) {
        sha256->digest[i] += S[i];
    }

#ifdef WOLFSSL_SMALL_STACK
    XFREE(W, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif

    return 0;
}

#endif /* #if !defined(FREESCALE_MMCAU) */

static INLINE void AddLength(Sha256* sha256, word32 len)
{
    word32 tmp = sha256->loLen;
    if ( (sha256->loLen += len) < tmp)
        sha256->hiLen++;                       /* carry low to high */
}

int wc_Sha256Update(Sha256* sha256, const byte* data, word32 len)
{

    /* do block size increments */
    byte* local = (byte*)sha256->buffer;

    SAVE_XMM_YMM ; /* for Intel AVX */

    while (len) {
        word32 add = min(len, SHA256_BLOCK_SIZE - sha256->buffLen);
        XMEMCPY(&local[sha256->buffLen], data, add);

        sha256->buffLen += add;
        data            += add;
        len             -= add;

        if (sha256->buffLen == SHA256_BLOCK_SIZE) {
            int ret;

            #if defined(LITTLE_ENDIAN_ORDER) && !defined(FREESCALE_MMCAU)
                #if defined(HAVE_INTEL_AVX1) || defined(HAVE_INTEL_AVX2)
                if(!IS_INTEL_AVX1 && !IS_INTEL_AVX2)
                #endif
                ByteReverseWords(sha256->buffer, sha256->buffer,
                                 SHA256_BLOCK_SIZE);
            #endif
            ret = XTRANSFORM(sha256, local);
            if (ret != 0)
                return ret;

            AddLength(sha256, SHA256_BLOCK_SIZE);
            sha256->buffLen = 0;
        }
    }

    return 0;
}

int wc_Sha256Final(Sha256* sha256, byte* hash)
{
    byte* local = (byte*)sha256->buffer;
    int ret;
    
    SAVE_XMM_YMM ; /* for Intel AVX */

    AddLength(sha256, sha256->buffLen);  /* before adding pads */

    local[sha256->buffLen++] = 0x80;     /* add 1 */

    /* pad with zeros */
    if (sha256->buffLen > SHA256_PAD_SIZE) {
        XMEMSET(&local[sha256->buffLen], 0, SHA256_BLOCK_SIZE - sha256->buffLen);
        sha256->buffLen += SHA256_BLOCK_SIZE - sha256->buffLen;

        #if defined(LITTLE_ENDIAN_ORDER) && !defined(FREESCALE_MMCAU)
            #if defined(HAVE_INTEL_AVX1) || defined(HAVE_INTEL_AVX2)
            if(!IS_INTEL_AVX1 && !IS_INTEL_AVX2)
            #endif
            ByteReverseWords(sha256->buffer, sha256->buffer, SHA256_BLOCK_SIZE);
        #endif

        ret = XTRANSFORM(sha256, local);
        if (ret != 0)
            return ret;

        sha256->buffLen = 0;
    }
    XMEMSET(&local[sha256->buffLen], 0, SHA256_PAD_SIZE - sha256->buffLen);

    /* put lengths in bits */
    sha256->hiLen = (sha256->loLen >> (8*sizeof(sha256->loLen) - 3)) +
                 (sha256->hiLen << 3);
    sha256->loLen = sha256->loLen << 3;

    /* store lengths */
    #if defined(LITTLE_ENDIAN_ORDER) && !defined(FREESCALE_MMCAU)
        #if defined(HAVE_INTEL_AVX1) || defined(HAVE_INTEL_AVX2)
        if(!IS_INTEL_AVX1 && !IS_INTEL_AVX2)
        #endif
            ByteReverseWords(sha256->buffer, sha256->buffer, SHA256_BLOCK_SIZE);
    #endif
    /* ! length ordering dependent on digest endian type ! */
    XMEMCPY(&local[SHA256_PAD_SIZE], &sha256->hiLen, sizeof(word32));
    XMEMCPY(&local[SHA256_PAD_SIZE + sizeof(word32)], &sha256->loLen,
            sizeof(word32));

    #if defined(FREESCALE_MMCAU) || defined(HAVE_INTEL_AVX1) || defined(HAVE_INTEL_AVX2)
        /* Kinetis requires only these bytes reversed */
        #if defined(HAVE_INTEL_AVX1) || defined(HAVE_INTEL_AVX2)
        if(IS_INTEL_AVX1 || IS_INTEL_AVX2)
        #endif
        ByteReverseWords(&sha256->buffer[SHA256_PAD_SIZE/sizeof(word32)],
                         &sha256->buffer[SHA256_PAD_SIZE/sizeof(word32)],
                         2 * sizeof(word32));
    #endif

    ret = XTRANSFORM(sha256, local);
    if (ret != 0)
        return ret;

    #if defined(LITTLE_ENDIAN_ORDER)
        ByteReverseWords(sha256->digest, sha256->digest, SHA256_DIGEST_SIZE);
    #endif
    XMEMCPY(hash, sha256->digest, SHA256_DIGEST_SIZE);

    return wc_InitSha256(sha256);  /* reset state */
}



int wc_Sha256Hash(const byte* data, word32 len, byte* hash)
{
    int ret = 0;
#ifdef WOLFSSL_SMALL_STACK
    Sha256* sha256;
#else
    Sha256 sha256[1];
#endif

#ifdef WOLFSSL_SMALL_STACK
    sha256 = (Sha256*)XMALLOC(sizeof(Sha256), NULL, DYNAMIC_TYPE_TMP_BUFFER);
    if (sha256 == NULL)
        return MEMORY_E;
#endif

    if ((ret = wc_InitSha256(sha256)) != 0) {
        WOLFSSL_MSG("InitSha256 failed");
    }
    else if ((ret = wc_Sha256Update(sha256, data, len)) != 0) {
        WOLFSSL_MSG("Sha256Update failed");
    }
    else if ((ret = wc_Sha256Final(sha256, hash)) != 0) {
        WOLFSSL_MSG("Sha256Final failed");
    }

#ifdef WOLFSSL_SMALL_STACK
    XFREE(sha256, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif

    return ret;
}

#if defined(HAVE_INTEL_AVX1) || defined(HAVE_INTEL_AVX2)

#define _DigestToReg(S_0, S_1, S_2, S_3, S_4, S_5, S_6, S_7 )\
    { word32 d ;\
    d = sha256->digest[0]; __asm__ volatile("movl %0, %"#S_0::"r"(d):SSE_REGs) ;\
    d = sha256->digest[1]; __asm__ volatile("movl %0, %"#S_1::"r"(d):SSE_REGs) ;\
    d = sha256->digest[2]; __asm__ volatile("movl %0, %"#S_2::"r"(d):SSE_REGs) ;\
    d = sha256->digest[3]; __asm__ volatile("movl %0, %"#S_3::"r"(d):SSE_REGs) ;\
    d = sha256->digest[4]; __asm__ volatile("movl %0, %"#S_4::"r"(d):SSE_REGs) ;\
    d = sha256->digest[5]; __asm__ volatile("movl %0, %"#S_5::"r"(d):SSE_REGs) ;\
    d = sha256->digest[6]; __asm__ volatile("movl %0, %"#S_6::"r"(d):SSE_REGs) ;\
    d = sha256->digest[7]; __asm__ volatile("movl %0, %"#S_7::"r"(d):SSE_REGs) ;\
}

#define _RegToDigest(S_0, S_1, S_2, S_3, S_4, S_5, S_6, S_7 )\
    { word32 d ; \
    __asm__ volatile("movl %"#S_0", %0":"=r"(d)::SSE_REGs) ; sha256->digest[0] += d;\
    __asm__ volatile("movl %"#S_1", %0":"=r"(d)::SSE_REGs) ; sha256->digest[1] += d;\
    __asm__ volatile("movl %"#S_2", %0":"=r"(d)::SSE_REGs) ; sha256->digest[2] += d;\
    __asm__ volatile("movl %"#S_3", %0":"=r"(d)::SSE_REGs) ; sha256->digest[3] += d;\
    __asm__ volatile("movl %"#S_4", %0":"=r"(d)::SSE_REGs) ; sha256->digest[4] += d;\
    __asm__ volatile("movl %"#S_5", %0":"=r"(d)::SSE_REGs) ; sha256->digest[5] += d;\
    __asm__ volatile("movl %"#S_6", %0":"=r"(d)::SSE_REGs) ; sha256->digest[6] += d;\
    __asm__ volatile("movl %"#S_7", %0":"=r"(d)::SSE_REGs) ; sha256->digest[7] += d;\
}


#define DigestToReg(S_0, S_1, S_2, S_3, S_4, S_5, S_6, S_7 )\
    _DigestToReg(S_0, S_1, S_2, S_3, S_4, S_5, S_6, S_7 )

#define RegToDigest(S_0, S_1, S_2, S_3, S_4, S_5, S_6, S_7 )\
    _RegToDigest(S_0, S_1, S_2, S_3, S_4, S_5, S_6, S_7 )




#define S_0 %r15d 
#define S_1 %r10d
#define S_2 %r11d       
#define S_3 %r12d
#define S_4 %r13d
#define S_5 %r14d
#define S_6 %ebx
#define S_7 %r9d

#define SSE_REGs "%edi", "%ecx", "%esi", "%edx", "%ebx","%r8","%r9","%r10","%r11","%r12","%r13","%r14","%r15"

#if defined(HAVE_INTEL_RORX)
#define RND_STEP_RORX_1(a,b,c,d,e,f,g,h,i)\
__asm__ volatile("rorx  $6, %"#e", %%edx\n\t":::"%edx",SSE_REGs);  /* edx = e>>6 */\

#define RND_STEP_RORX_2(a,b,c,d,e,f,g,h,i)\
__asm__ volatile("rorx  $11, %"#e",%%edi\n\t":::"%edi",SSE_REGs); /* edi = e>>11  */\
__asm__ volatile("xorl  %%edx, %%edi\n\t":::"%edx","%edi",SSE_REGs); /* edi = (e>>11) ^ (e>>6)  */\
__asm__ volatile("rorx  $25, %"#e", %%edx\n\t":::"%edx",SSE_REGs);   /* edx = e>>25             */\

#define RND_STEP_RORX_3(a,b,c,d,e,f,g,h,i)\
__asm__ volatile("movl  %"#f", %%esi\n\t":::"%esi",SSE_REGs);  /* esi = f   */\
__asm__ volatile("xorl  %"#g", %%esi\n\t":::"%esi",SSE_REGs);  /* esi = f ^ g  */\
__asm__ volatile("xorl  %%edi, %%edx\n\t":::"%edi","%edx",SSE_REGs);  /* edx = Sigma1(e)  */\
__asm__ volatile("andl  %"#e", %%esi\n\t":::"%esi",SSE_REGs);  /* esi = (f ^ g) & e       */\
__asm__ volatile("xorl  %"#g", %%esi\n\t":::"%esi",SSE_REGs);  /* esi = Ch(e,f,g)         */\

#define RND_STEP_RORX_4(a,b,c,d,e,f,g,h,i)\
/*__asm__ volatile("movl    %0, %%edx\n\t"::"m"(w_k):"%edx");*/\
__asm__ volatile("addl  %0, %"#h"\n\t"::"r"(W_K[i]):SSE_REGs);    /* h += w_k  */\
__asm__ volatile("addl  %%edx, %"#h"\n\t":::"%edx",SSE_REGs);     /* h = h + w_k + Sigma1(e) */\
__asm__ volatile("rorx  $2, %"#a", %%r8d\n\t":::"%r8",SSE_REGs);  /* r8d = a>>2   */\
__asm__ volatile("rorx  $13, %"#a", %%edi\n\t":::"%edi",SSE_REGs);/* edi = a>>13  */\

#define RND_STEP_RORX_5(a,b,c,d,e,f,g,h,i)\
__asm__ volatile("rorx  $22, %"#a", %%edx\n\t":::"%edx",SSE_REGs); /* edx = a>>22 */\
__asm__ volatile("xorl  %%r8d, %%edi\n\t":::"%edi","%r8",SSE_REGs);/* edi = (a>>2) ^ (a>>13)  */\
__asm__ volatile("xorl  %%edi, %%edx\n\t":::"%edi","%edx",SSE_REGs);  /* edx = Sigma0(a)      */\
 
#define RND_STEP_RORX_6(a,b,c,d,e,f,g,h,i)\
__asm__ volatile("movl  %"#b", %%edi\n\t":::"%edi",SSE_REGs);  /* edi = b          */\
__asm__ volatile("orl   %"#a", %%edi\n\t":::"%edi",SSE_REGs);  /* edi = a | b      */\
__asm__ volatile("andl  %"#c", %%edi\n\t":::"%edi",SSE_REGs);  /* edi = (a | b) & c*/\
__asm__ volatile("movl  %"#b", %%r8d\n\t":::"%r8",SSE_REGs);  /* r8d = b           */\

#define RND_STEP_RORX_7(a,b,c,d,e,f,g,h,i)\
__asm__ volatile("addl  %%esi, %"#h"\n\t":::"%esi",SSE_REGs);  /* h += Ch(e,f,g)   */\
__asm__ volatile("andl  %"#a", %%r8d\n\t":::"%r8",SSE_REGs);  /* r8d = b & a       */\
__asm__ volatile("orl   %%edi, %%r8d\n\t":::"%edi","%r8",SSE_REGs); /* r8d = Maj(a,b,c) */\

#define RND_STEP_RORX_8(a,b,c,d,e,f,g,h,i)\
__asm__ volatile("addl  "#h", "#d"\n\t");  /* d += h + w_k + Sigma1(e) + Ch(e,f,g) */\
__asm__ volatile("addl  %"#h", %%r8d\n\t":::"%r8",SSE_REGs); \
__asm__ volatile("addl  %%edx, %%r8d\n\t":::"%edx","%r8",SSE_REGs); \
__asm__ volatile("movl  %r8d, "#h"\n\t");   

#endif

#define RND_STEP_1(a,b,c,d,e,f,g,h,i)\
__asm__ volatile("movl  %"#e", %%edx\n\t":::"%edx",SSE_REGs);\
__asm__ volatile("roll  $26, %%edx\n\t":::"%edx",SSE_REGs);  /* edx = e>>6     */\
__asm__ volatile("movl  %"#e", %%edi\n\t":::"%edi",SSE_REGs);\

#define RND_STEP_2(a,b,c,d,e,f,g,h,i)\
__asm__ volatile("roll  $21, %%edi\n\t":::"%edi",SSE_REGs);         /* edi = e>>11 */\
__asm__ volatile("xorl  %%edx, %%edi\n\t":::"%edx","%edi",SSE_REGs); /* edi = (e>>11) ^ (e>>6)  */\
__asm__ volatile("movl  %"#e", %%edx\n\t":::"%edx",SSE_REGs);   /* edx = e      */\
__asm__ volatile("roll  $7, %%edx\n\t":::"%edx",SSE_REGs);      /* edx = e>>25  */\

#define RND_STEP_3(a,b,c,d,e,f,g,h,i)\
__asm__ volatile("movl  %"#f", %%esi\n\t":::"%esi",SSE_REGs);  /* esi = f       */\
__asm__ volatile("xorl  %"#g", %%esi\n\t":::"%esi",SSE_REGs);  /* esi = f ^ g   */\
__asm__ volatile("xorl  %%edi, %%edx\n\t":::"%edi","%edx",SSE_REGs); /* edx = Sigma1(e) */\
__asm__ volatile("andl  %"#e", %%esi\n\t":::"%esi",SSE_REGs);  /* esi = (f ^ g) & e  */\
__asm__ volatile("xorl  %"#g", %%esi\n\t":::"%esi",SSE_REGs);  /* esi = Ch(e,f,g)    */\

#define RND_STEP_4(a,b,c,d,e,f,g,h,i)\
__asm__ volatile("addl  %0, %"#h"\n\t"::"r"(W_K[i]):SSE_REGs); /* h += w_k  */\
__asm__ volatile("addl  %%edx, %"#h"\n\t":::"%edx",SSE_REGs); /* h = h + w_k + Sigma1(e) */\
__asm__ volatile("movl  %"#a", %%r8d\n\t":::"%r8",SSE_REGs);  /* r8d = a    */\
__asm__ volatile("roll  $30, %%r8d\n\t":::"%r8",SSE_REGs);    /* r8d = a>>2 */\
__asm__ volatile("movl  %"#a", %%edi\n\t":::"%edi",SSE_REGs);  /* edi = a   */\
__asm__ volatile("roll  $19, %%edi\n\t":::"%edi",SSE_REGs);    /* edi = a>>13 */\
__asm__ volatile("movl  %"#a", %%edx\n\t":::"%edx",SSE_REGs);  /* edx = a     */\

#define RND_STEP_5(a,b,c,d,e,f,g,h,i)\
__asm__ volatile("roll  $10, %%edx\n\t":::"%edx",SSE_REGs);    /* edx = a>>22 */\
__asm__ volatile("xorl  %%r8d, %%edi\n\t":::"%edi","%r8",SSE_REGs); /* edi = (a>>2) ^ (a>>13)  */\
__asm__ volatile("xorl  %%edi, %%edx\n\t":::"%edi","%edx",SSE_REGs);/* edx = Sigma0(a)         */\

#define RND_STEP_6(a,b,c,d,e,f,g,h,i)\
__asm__ volatile("movl  %"#b", %%edi\n\t":::"%edi",SSE_REGs);  /* edi = b      */\
__asm__ volatile("orl   %"#a", %%edi\n\t":::"%edi",SSE_REGs);  /* edi = a | b  */\
__asm__ volatile("andl  %"#c", %%edi\n\t":::"%edi",SSE_REGs);  /* edi = (a | b) & c */\
__asm__ volatile("movl  %"#b", %%r8d\n\t":::"%r8",SSE_REGs);  /* r8d = b       */\

#define RND_STEP_7(a,b,c,d,e,f,g,h,i)\
__asm__ volatile("addl  %%esi, %"#h"\n\t":::"%esi",SSE_REGs);  /* h += Ch(e,f,g)        */\
__asm__ volatile("andl  %"#a", %%r8d\n\t":::"%r8",SSE_REGs);  /* r8d = b & a            */\
__asm__ volatile("orl   %%edi, %%r8d\n\t":::"%edi","%r8",SSE_REGs); /* r8d = Maj(a,b,c) */\

#define RND_STEP_8(a,b,c,d,e,f,g,h,i)\
__asm__ volatile("addl  "#h", "#d"\n\t");  /* d += h + w_k + Sigma1(e) + Ch(e,f,g) */\
__asm__ volatile("addl  %"#h", %%r8d\n\t":::"%r8",SSE_REGs); \
                 /* r8b = h + w_k + Sigma1(e) + Ch(e,f,g) + Maj(a,b,c) */\
__asm__ volatile("addl  %%edx, %%r8d\n\t":::"%edx","%r8",SSE_REGs);\
                 /* r8b = h + w_k + Sigma1(e) Sigma0(a) + Ch(e,f,g) + Maj(a,b,c)     */\
__asm__ volatile("movl  %%r8d, %"#h"\n\t":::"%r8", SSE_REGs); \
                 /* h = h + w_k + Sigma1(e) + Sigma0(a) + Ch(e,f,g) + Maj(a,b,c) */ \

#define RND_X(a,b,c,d,e,f,g,h,i) \
       RND_STEP_1(a,b,c,d,e,f,g,h,i); \
       RND_STEP_2(a,b,c,d,e,f,g,h,i); \
       RND_STEP_3(a,b,c,d,e,f,g,h,i); \
       RND_STEP_4(a,b,c,d,e,f,g,h,i); \
       RND_STEP_5(a,b,c,d,e,f,g,h,i); \
       RND_STEP_6(a,b,c,d,e,f,g,h,i); \
       RND_STEP_7(a,b,c,d,e,f,g,h,i); \
       RND_STEP_8(a,b,c,d,e,f,g,h,i); 

#define RND_0(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,_i) RND_X(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,_i);
#define RND_7(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,_i) RND_X(S_7,S_0,S_1,S_2,S_3,S_4,S_5,S_6,_i);
#define RND_6(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,_i) RND_X(S_6,S_7,S_0,S_1,S_2,S_3,S_4,S_5,_i);
#define RND_5(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,_i) RND_X(S_5,S_6,S_7,S_0,S_1,S_2,S_3,S_4,_i);
#define RND_4(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,_i) RND_X(S_4,S_5,S_6,S_7,S_0,S_1,S_2,S_3,_i);
#define RND_3(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,_i) RND_X(S_3,S_4,S_5,S_6,S_7,S_0,S_1,S_2,_i);
#define RND_2(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,_i) RND_X(S_2,S_3,S_4,S_5,S_6,S_7,S_0,S_1,_i);
#define RND_1(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,_i) RND_X(S_1,S_2,S_3,S_4,S_5,S_6,S_7,S_0,_i);


#define RND_1_3(a,b,c,d,e,f,g,h,i) {\
       RND_STEP_1(a,b,c,d,e,f,g,h,i); \
       RND_STEP_2(a,b,c,d,e,f,g,h,i); \
       RND_STEP_3(a,b,c,d,e,f,g,h,i); \
}

#define RND_4_6(a,b,c,d,e,f,g,h,i) {\
       RND_STEP_4(a,b,c,d,e,f,g,h,i); \
       RND_STEP_5(a,b,c,d,e,f,g,h,i); \
       RND_STEP_6(a,b,c,d,e,f,g,h,i); \
}

#define RND_7_8(a,b,c,d,e,f,g,h,i) {\
       RND_STEP_7(a,b,c,d,e,f,g,h,i); \
       RND_STEP_8(a,b,c,d,e,f,g,h,i); \
}

#define RND_0(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,_i) RND_X(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,_i);
#define RND_7(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,_i) RND_X(S_7,S_0,S_1,S_2,S_3,S_4,S_5,S_6,_i);
#define RND_6(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,_i) RND_X(S_6,S_7,S_0,S_1,S_2,S_3,S_4,S_5,_i);
#define RND_5(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,_i) RND_X(S_5,S_6,S_7,S_0,S_1,S_2,S_3,S_4,_i);
#define RND_4(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,_i) RND_X(S_4,S_5,S_6,S_7,S_0,S_1,S_2,S_3,_i);
#define RND_3(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,_i) RND_X(S_3,S_4,S_5,S_6,S_7,S_0,S_1,S_2,_i);
#define RND_2(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,_i) RND_X(S_2,S_3,S_4,S_5,S_6,S_7,S_0,S_1,_i);
#define RND_1(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,_i) RND_X(S_1,S_2,S_3,S_4,S_5,S_6,S_7,S_0,_i);


#define RND_0_0(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,_i) RND_1_3(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,_i);
#define RND_7_0(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,_i) RND_1_3(S_7,S_0,S_1,S_2,S_3,S_4,S_5,S_6,_i);
#define RND_6_0(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,_i) RND_1_3(S_6,S_7,S_0,S_1,S_2,S_3,S_4,S_5,_i);
#define RND_5_0(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,_i) RND_1_3(S_5,S_6,S_7,S_0,S_1,S_2,S_3,S_4,_i);
#define RND_4_0(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,_i) RND_1_3(S_4,S_5,S_6,S_7,S_0,S_1,S_2,S_3,_i);
#define RND_3_0(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,_i) RND_1_3(S_3,S_4,S_5,S_6,S_7,S_0,S_1,S_2,_i);
#define RND_2_0(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,_i) RND_1_3(S_2,S_3,S_4,S_5,S_6,S_7,S_0,S_1,_i);
#define RND_1_0(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,_i) RND_1_3(S_1,S_2,S_3,S_4,S_5,S_6,S_7,S_0,_i);

#define RND_0_1(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,_i) RND_4_6(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,_i);
#define RND_7_1(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,_i) RND_4_6(S_7,S_0,S_1,S_2,S_3,S_4,S_5,S_6,_i);
#define RND_6_1(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,_i) RND_4_6(S_6,S_7,S_0,S_1,S_2,S_3,S_4,S_5,_i);
#define RND_5_1(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,_i) RND_4_6(S_5,S_6,S_7,S_0,S_1,S_2,S_3,S_4,_i);
#define RND_4_1(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,_i) RND_4_6(S_4,S_5,S_6,S_7,S_0,S_1,S_2,S_3,_i);
#define RND_3_1(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,_i) RND_4_6(S_3,S_4,S_5,S_6,S_7,S_0,S_1,S_2,_i);
#define RND_2_1(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,_i) RND_4_6(S_2,S_3,S_4,S_5,S_6,S_7,S_0,S_1,_i);
#define RND_1_1(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,_i) RND_4_6(S_1,S_2,S_3,S_4,S_5,S_6,S_7,S_0,_i);

#define RND_0_2(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,_i) RND_7_8(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,_i);
#define RND_7_2(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,_i) RND_7_8(S_7,S_0,S_1,S_2,S_3,S_4,S_5,S_6,_i);
#define RND_6_2(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,_i) RND_7_8(S_6,S_7,S_0,S_1,S_2,S_3,S_4,S_5,_i);
#define RND_5_2(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,_i) RND_7_8(S_5,S_6,S_7,S_0,S_1,S_2,S_3,S_4,_i);
#define RND_4_2(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,_i) RND_7_8(S_4,S_5,S_6,S_7,S_0,S_1,S_2,S_3,_i);
#define RND_3_2(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,_i) RND_7_8(S_3,S_4,S_5,S_6,S_7,S_0,S_1,S_2,_i);
#define RND_2_2(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,_i) RND_7_8(S_2,S_3,S_4,S_5,S_6,S_7,S_0,S_1,_i);
#define RND_1_2(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,_i) RND_7_8(S_1,S_2,S_3,S_4,S_5,S_6,S_7,S_0,_i);

#define FOR(cnt, init, max, inc, loop)  \
    __asm__ volatile("movl $"#init", %0\n\t"#loop":"::"m"(cnt):) 
#define END(cnt, init, max, inc, loop)  \
    __asm__ volatile("addl $"#inc", %0\n\tcmpl $"#max", %0\n\tjle "#loop"\n\t":"=m"(cnt)::) ;

#endif  /* defined(HAVE_INTEL_AVX1) ||  defined(HAVE_INTEL_AVX2) */

#if defined(HAVE_INTEL_AVX1) /* inline Assember for Intel AVX1 instructions */

#define VPALIGNR(op1,op2,op3,op4) __asm__ volatile("vpalignr $"#op4", %"#op3", %"#op2", %"#op1:::XMM_REGs) 
#define VPADDD(op1,op2,op3)       __asm__ volatile("vpaddd %"#op3", %"#op2", %"#op1:::XMM_REGs)
#define VPSRLD(op1,op2,op3)       __asm__ volatile("vpsrld $"#op3", %"#op2", %"#op1:::XMM_REGs)
#define VPSRLQ(op1,op2,op3)       __asm__ volatile("vpsrlq $"#op3", %"#op2", %"#op1:::XMM_REGs)
#define VPSLLD(op1,op2,op3)       __asm__ volatile("vpslld $"#op3", %"#op2", %"#op1:::XMM_REGs)
#define VPOR(op1,op2,op3)         __asm__ volatile("vpor   %"#op3", %"#op2", %"#op1:::XMM_REGs)
#define VPXOR(op1,op2,op3)        __asm__ volatile("vpxor  %"#op3", %"#op2", %"#op1:::XMM_REGs)
#define VPSHUFD(op1,op2,op3)      __asm__ volatile("vpshufd $"#op3", %"#op2", %"#op1:::XMM_REGs)
#define VPSHUFB(op1,op2,op3)      __asm__ volatile("vpshufb %"#op3", %"#op2", %"#op1:::XMM_REGs)

#define MessageSched(X0, X1, X2, X3, XTMP0, XTMP1, XTMP2, XTMP3, XTMP4, XTMP5, XFER, SHUF_00BA, SHUF_DC00,\
     a,b,c,d,e,f,g,h,_i)\
            RND_STEP_1(a,b,c,d,e,f,g,h,_i);\
    VPALIGNR (XTMP0, X3, X2, 4) ;\
            RND_STEP_2(a,b,c,d,e,f,g,h,_i);\
    VPADDD   (XTMP0, XTMP0, X0) ;\
            RND_STEP_3(a,b,c,d,e,f,g,h,_i);\
    VPALIGNR (XTMP1, X1, X0, 4) ;   /* XTMP1 = W[-15] */\
            RND_STEP_4(a,b,c,d,e,f,g,h,_i);\
    VPSRLD   (XTMP2, XTMP1, 7) ;\
            RND_STEP_5(a,b,c,d,e,f,g,h,_i);\
    VPSLLD   (XTMP3, XTMP1, 25) ; /* VPSLLD   (XTMP3, XTMP1, (32-7)) */\
            RND_STEP_6(a,b,c,d,e,f,g,h,_i);\
    VPOR     (XTMP3, XTMP3, XTMP2)  ;  /* XTMP1 = W[-15] MY_ROR 7 */\
            RND_STEP_7(a,b,c,d,e,f,g,h,_i);\
    VPSRLD   (XTMP2, XTMP1,18) ;\
            RND_STEP_8(a,b,c,d,e,f,g,h,_i);\
\
            RND_STEP_1(h,a,b,c,d,e,f,g,_i+1);\
    VPSRLD   (XTMP4, XTMP1, 3)      ;  /* XTMP4 = W[-15] >> 3 */\
            RND_STEP_2(h,a,b,c,d,e,f,g,_i+1);\
    VPSLLD   (XTMP1, XTMP1, 14) ; /* VPSLLD   (XTMP1, XTMP1, (32-18)) */\
            RND_STEP_3(h,a,b,c,d,e,f,g,_i+1);\
    VPXOR    (XTMP3, XTMP3, XTMP1)  ;\
            RND_STEP_4(h,a,b,c,d,e,f,g,_i+1);\
    VPXOR    (XTMP3, XTMP3, XTMP2)  ;  /* XTMP1 = W[-15] MY_ROR 7 ^ W[-15] MY_ROR 18 */\
            RND_STEP_5(h,a,b,c,d,e,f,g,_i+1);\
    VPXOR    (XTMP1, XTMP3, XTMP4)  ;  /* XTMP1 = s0 */\
            RND_STEP_6(h,a,b,c,d,e,f,g,_i+1);\
    VPSHUFD(XTMP2, X3, 0b11111010)  ;  /* XTMP2 = W[-2] {BBAA}*/\
            RND_STEP_7(h,a,b,c,d,e,f,g,_i+1);\
    VPADDD   (XTMP0, XTMP0, XTMP1)  ;  /* XTMP0 = W[-16] + W[-7] + s0 */\
            RND_STEP_8(h,a,b,c,d,e,f,g,_i+1);\
\
            RND_STEP_1(g,h,a,b,c,d,e,f,_i+2);\
    VPSRLD   (XTMP4, XTMP2, 10) ;      /* XTMP4 = W[-2] >> 10 {BBAA} */\
            RND_STEP_2(g,h,a,b,c,d,e,f,_i+2);\
    VPSRLQ   (XTMP3, XTMP2, 19) ;      /* XTMP3 = W[-2] MY_ROR 19 {xBxA} */\
            RND_STEP_3(g,h,a,b,c,d,e,f,_i+2);\
    VPSRLQ   (XTMP2, XTMP2, 17) ;      /* XTMP2 = W[-2] MY_ROR 17 {xBxA} */\
            RND_STEP_4(g,h,a,b,c,d,e,f,_i+2);\
    VPXOR    (XTMP2, XTMP2, XTMP3) ;\
            RND_STEP_5(g,h,a,b,c,d,e,f,_i+2);\
    VPXOR    (XTMP4, XTMP4, XTMP2) ;   /* XTMP4 = s1 {xBxA} */\
            RND_STEP_6(g,h,a,b,c,d,e,f,_i+2);\
    VPSHUFB  (XTMP4, XTMP4, SHUF_00BA)  ;  /* XTMP4 = s1 {00BA} */\
            RND_STEP_7(g,h,a,b,c,d,e,f,_i+2);\
    VPADDD   (XTMP0, XTMP0, XTMP4)  ;  /* XTMP0 = {..., ..., W[1], W[0]} */\
            RND_STEP_8(g,h,a,b,c,d,e,f,_i+2);\
\
            RND_STEP_1(f,g,h,a,b,c,d,e,_i+3);\
    VPSHUFD  (XTMP2, XTMP0, 0b01010000) ; /* XTMP2 = W[-2] {DDCC} */\
            RND_STEP_2(f,g,h,a,b,c,d,e,_i+3);\
    VPSRLD   (XTMP5, XTMP2, 10);       /* XTMP5 = W[-2] >> 10 {DDCC} */\
            RND_STEP_3(f,g,h,a,b,c,d,e,_i+3);\
    VPSRLQ   (XTMP3, XTMP2, 19);       /* XTMP3 = W[-2] MY_ROR 19 {xDxC} */\
            RND_STEP_4(f,g,h,a,b,c,d,e,_i+3);\
    VPSRLQ   (XTMP2, XTMP2, 17) ;      /* XTMP2 = W[-2] MY_ROR 17 {xDxC} */\
            RND_STEP_5(f,g,h,a,b,c,d,e,_i+3);\
    VPXOR    (XTMP2, XTMP2, XTMP3) ;\
            RND_STEP_6(f,g,h,a,b,c,d,e,_i+3);\
    VPXOR    (XTMP5, XTMP5, XTMP2) ;   /* XTMP5 = s1 {xDxC} */\
            RND_STEP_7(f,g,h,a,b,c,d,e,_i+3);\
    VPSHUFB  (XTMP5, XTMP5, SHUF_DC00) ; /* XTMP5 = s1 {DC00} */\
            RND_STEP_8(f,g,h,a,b,c,d,e,_i+3);\
    VPADDD   (X0, XTMP5, XTMP0) ;      /* X0 = {W[3], W[2], W[1], W[0]} */\

#if defined(HAVE_INTEL_RORX)

#define MessageSched_RORX(X0, X1, X2, X3, XTMP0, XTMP1, XTMP2, XTMP3, XTMP4, XTMP5, \
                          XFER, SHUF_00BA, SHUF_DC00,a,b,c,d,e,f,g,h,_i)\
            RND_STEP_RORX_1(a,b,c,d,e,f,g,h,_i);\
    VPALIGNR (XTMP0, X3, X2, 4) ;\
            RND_STEP_RORX_2(a,b,c,d,e,f,g,h,_i);\
    VPADDD   (XTMP0, XTMP0, X0) ;\
            RND_STEP_RORX_3(a,b,c,d,e,f,g,h,_i);\
    VPALIGNR (XTMP1, X1, X0, 4) ;   /* XTMP1 = W[-15] */\
            RND_STEP_RORX_4(a,b,c,d,e,f,g,h,_i);\
    VPSRLD   (XTMP2, XTMP1, 7) ;\
            RND_STEP_RORX_5(a,b,c,d,e,f,g,h,_i);\
    VPSLLD   (XTMP3, XTMP1, 25) ; /* VPSLLD   (XTMP3, XTMP1, (32-7)) */\
            RND_STEP_RORX_6(a,b,c,d,e,f,g,h,_i);\
    VPOR     (XTMP3, XTMP3, XTMP2)  ;  /* XTMP1 = W[-15] MY_ROR 7 */\
            RND_STEP_RORX_7(a,b,c,d,e,f,g,h,_i);\
    VPSRLD   (XTMP2, XTMP1,18) ;\
            RND_STEP_RORX_8(a,b,c,d,e,f,g,h,_i);\
\
            RND_STEP_RORX_1(h,a,b,c,d,e,f,g,_i+1);\
    VPSRLD   (XTMP4, XTMP1, 3)      ;  /* XTMP4 = W[-15] >> 3 */\
            RND_STEP_RORX_2(h,a,b,c,d,e,f,g,_i+1);\
    VPSLLD   (XTMP1, XTMP1, 14) ; /* VPSLLD   (XTMP1, XTMP1, (32-18)) */\
            RND_STEP_RORX_3(h,a,b,c,d,e,f,g,_i+1);\
    VPXOR    (XTMP3, XTMP3, XTMP1)  ;\
            RND_STEP_RORX_4(h,a,b,c,d,e,f,g,_i+1);\
    VPXOR    (XTMP3, XTMP3, XTMP2)  ;  /* XTMP1 = W[-15] MY_ROR 7 ^ W[-15] MY_ROR 18 */\
            RND_STEP_RORX_5(h,a,b,c,d,e,f,g,_i+1);\
    VPXOR    (XTMP1, XTMP3, XTMP4)  ;  /* XTMP1 = s0 */\
            RND_STEP_RORX_6(h,a,b,c,d,e,f,g,_i+1);\
    VPSHUFD(XTMP2, X3, 0b11111010)  ;  /* XTMP2 = W[-2] {BBAA}*/\
            RND_STEP_RORX_7(h,a,b,c,d,e,f,g,_i+1);\
    VPADDD   (XTMP0, XTMP0, XTMP1)  ;  /* XTMP0 = W[-16] + W[-7] + s0 */\
            RND_STEP_RORX_8(h,a,b,c,d,e,f,g,_i+1);\
\
            RND_STEP_RORX_1(g,h,a,b,c,d,e,f,_i+2);\
    VPSRLD   (XTMP4, XTMP2, 10) ;      /* XTMP4 = W[-2] >> 10 {BBAA} */\
            RND_STEP_RORX_2(g,h,a,b,c,d,e,f,_i+2);\
    VPSRLQ   (XTMP3, XTMP2, 19) ;      /* XTMP3 = W[-2] MY_ROR 19 {xBxA} */\
            RND_STEP_RORX_3(g,h,a,b,c,d,e,f,_i+2);\
    VPSRLQ   (XTMP2, XTMP2, 17) ;      /* XTMP2 = W[-2] MY_ROR 17 {xBxA} */\
            RND_STEP_RORX_4(g,h,a,b,c,d,e,f,_i+2);\
    VPXOR    (XTMP2, XTMP2, XTMP3) ;\
            RND_STEP_RORX_5(g,h,a,b,c,d,e,f,_i+2);\
    VPXOR    (XTMP4, XTMP4, XTMP2) ;   /* XTMP4 = s1 {xBxA} */\
            RND_STEP_RORX_6(g,h,a,b,c,d,e,f,_i+2);\
    VPSHUFB  (XTMP4, XTMP4, SHUF_00BA)  ;  /* XTMP4 = s1 {00BA} */\
            RND_STEP_RORX_7(g,h,a,b,c,d,e,f,_i+2);\
    VPADDD   (XTMP0, XTMP0, XTMP4)  ;  /* XTMP0 = {..., ..., W[1], W[0]} */\
            RND_STEP_RORX_8(g,h,a,b,c,d,e,f,_i+2);\
\
            RND_STEP_RORX_1(f,g,h,a,b,c,d,e,_i+3);\
    VPSHUFD  (XTMP2, XTMP0, 0b01010000) ; /* XTMP2 = W[-2] {DDCC} */\
            RND_STEP_RORX_2(f,g,h,a,b,c,d,e,_i+3);\
    VPSRLD   (XTMP5, XTMP2, 10);       /* XTMP5 = W[-2] >> 10 {DDCC} */\
            RND_STEP_RORX_3(f,g,h,a,b,c,d,e,_i+3);\
    VPSRLQ   (XTMP3, XTMP2, 19);       /* XTMP3 = W[-2] MY_ROR 19 {xDxC} */\
            RND_STEP_RORX_4(f,g,h,a,b,c,d,e,_i+3);\
    VPSRLQ   (XTMP2, XTMP2, 17) ;      /* XTMP2 = W[-2] MY_ROR 17 {xDxC} */\
            RND_STEP_RORX_5(f,g,h,a,b,c,d,e,_i+3);\
    VPXOR    (XTMP2, XTMP2, XTMP3) ;\
            RND_STEP_RORX_6(f,g,h,a,b,c,d,e,_i+3);\
    VPXOR    (XTMP5, XTMP5, XTMP2) ;   /* XTMP5 = s1 {xDxC} */\
            RND_STEP_RORX_7(f,g,h,a,b,c,d,e,_i+3);\
    VPSHUFB  (XTMP5, XTMP5, SHUF_DC00) ; /* XTMP5 = s1 {DC00} */\
            RND_STEP_RORX_8(f,g,h,a,b,c,d,e,_i+3);\
    VPADDD   (X0, XTMP5, XTMP0) ;      /* X0 = {W[3], W[2], W[1], W[0]} */\

#endif


#define W_K_from_buff\
         __asm__ volatile("vmovdqu %0, %%xmm4\n\t"\
                          "vpshufb %%xmm13, %%xmm4, %%xmm4\n\t"\
                          :: "m"(sha256->buffer[0]):"%xmm4") ;\
         __asm__ volatile("vmovdqu %0, %%xmm5\n\t"\
                          "vpshufb %%xmm13, %%xmm5, %%xmm5\n\t"\
                          ::"m"(sha256->buffer[4]):"%xmm5") ;\
         __asm__ volatile("vmovdqu %0, %%xmm6\n\t"\
                          "vpshufb %%xmm13, %%xmm6, %%xmm6\n\t"\
                          ::"m"(sha256->buffer[8]):"%xmm6") ;\
         __asm__ volatile("vmovdqu %0, %%xmm7\n\t"\
                          "vpshufb %%xmm13, %%xmm7, %%xmm7\n\t"\
                          ::"m"(sha256->buffer[12]):"%xmm7") ;\

#define _SET_W_K_XFER(reg, i)\
    __asm__ volatile("vpaddd %0, %"#reg", %%xmm9"::"m"(K[i]):XMM_REGs) ;\
    __asm__ volatile("vmovdqa %%xmm9, %0":"=m"(W_K[i])::XMM_REGs) ;

#define SET_W_K_XFER(reg, i) _SET_W_K_XFER(reg, i)

static const ALIGN32 word64 mSHUF_00BA[] = { 0x0b0a090803020100, 0xFFFFFFFFFFFFFFFF } ; /* shuffle xBxA -> 00BA */
static const ALIGN32 word64 mSHUF_DC00[] = { 0xFFFFFFFFFFFFFFFF, 0x0b0a090803020100 } ; /* shuffle xDxC -> DC00 */
static const ALIGN32 word64 mBYTE_FLIP_MASK[] =  { 0x0405060700010203, 0x0c0d0e0f08090a0b } ;


#define _Init_Masks(mask1, mask2, mask3)\
__asm__ volatile("vmovdqu %0, %"#mask1 ::"m"(mBYTE_FLIP_MASK[0])) ;\
__asm__ volatile("vmovdqu %0, %"#mask2 ::"m"(mSHUF_00BA[0])) ;\
__asm__ volatile("vmovdqu %0, %"#mask3 ::"m"(mSHUF_DC00[0])) ;

#define Init_Masks(BYTE_FLIP_MASK, SHUF_00BA, SHUF_DC00)\
    _Init_Masks(BYTE_FLIP_MASK, SHUF_00BA, SHUF_DC00)

#define X0 %xmm4
#define X1 %xmm5
#define X2 %xmm6
#define X3 %xmm7
#define X_ X0

#define XTMP0 %xmm0
#define XTMP1 %xmm1
#define XTMP2 %xmm2
#define XTMP3 %xmm3
#define XTMP4 %xmm8
#define XTMP5 %xmm9
#define XFER  %xmm10

#define SHUF_00BA   %xmm11 /* shuffle xBxA -> 00BA */
#define SHUF_DC00   %xmm12 /* shuffle xDxC -> DC00 */
#define BYTE_FLIP_MASK  %xmm13

#define XMM_REGs   /* Registers are saved in Sha256Update/Finel */
                   /*"xmm4","xmm5","xmm6","xmm7","xmm8","xmm9","xmm10","xmm11","xmm12","xmm13" */

static int Transform_AVX1(Sha256* sha256)
{

    word32 W_K[64] ;  /* temp for W+K */

    #if defined(DEBUG_XMM)
    int i, j ;
    word32 xmm[29][4*15] ;
    #endif

    Init_Masks(BYTE_FLIP_MASK, SHUF_00BA, SHUF_DC00) ;
    W_K_from_buff ; /* X0, X1, X2, X3 = W[0..15] ; */

    DigestToReg(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7) ;
  
    SET_W_K_XFER(X0, 0) ;
    MessageSched(X0, X1, X2, X3, XTMP0, XTMP1, XTMP2, XTMP3, XTMP4, XTMP5, XFER, 
            SHUF_00BA, SHUF_DC00, S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,0) ;
    SET_W_K_XFER(X1, 4) ;
    MessageSched(X1, X2, X3, X0, XTMP0, XTMP1, XTMP2, XTMP3, XTMP4, XTMP5, XFER,
            SHUF_00BA, SHUF_DC00, S_4,S_5,S_6,S_7,S_0,S_1,S_2,S_3,4) ;
    SET_W_K_XFER(X2, 8) ;
    MessageSched(X2, X3, X0, X1, XTMP0, XTMP1, XTMP2, XTMP3, XTMP4, XTMP5, XFER, 
            SHUF_00BA, SHUF_DC00, S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,8) ;
    SET_W_K_XFER(X3, 12) ;
    MessageSched(X3, X0, X1, X2, XTMP0, XTMP1, XTMP2, XTMP3, XTMP4, XTMP5, XFER, 
            SHUF_00BA, SHUF_DC00, S_4,S_5,S_6,S_7,S_0,S_1,S_2,S_3,12) ;
    SET_W_K_XFER(X0, 16) ;
    MessageSched(X0, X1, X2, X3, XTMP0, XTMP1, XTMP2, XTMP3, XTMP4, XTMP5, XFER, 
            SHUF_00BA, SHUF_DC00, S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,16) ;
    SET_W_K_XFER(X1, 20) ;
    MessageSched(X1, X2, X3, X0, XTMP0, XTMP1, XTMP2, XTMP3, XTMP4, XTMP5, XFER, 
            SHUF_00BA, SHUF_DC00, S_4,S_5,S_6,S_7,S_0,S_1,S_2,S_3,20) ;
    SET_W_K_XFER(X2, 24) ;
    MessageSched(X2, X3, X0, X1, XTMP0, XTMP1, XTMP2, XTMP3, XTMP4, XTMP5, XFER, 
            SHUF_00BA, SHUF_DC00, S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,24) ;
    SET_W_K_XFER(X3, 28) ;
    MessageSched(X3, X0, X1, X2, XTMP0, XTMP1, XTMP2, XTMP3, XTMP4, XTMP5, XFER, 
            SHUF_00BA, SHUF_DC00, S_4,S_5,S_6,S_7,S_0,S_1,S_2,S_3,28) ;
    SET_W_K_XFER(X0, 32) ;
    MessageSched(X0, X1, X2, X3, XTMP0, XTMP1, XTMP2, XTMP3, XTMP4, XTMP5, XFER, 
            SHUF_00BA, SHUF_DC00, S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,32) ;
    SET_W_K_XFER(X1, 36) ;
    MessageSched(X1, X2, X3, X0, XTMP0, XTMP1, XTMP2, XTMP3, XTMP4, XTMP5, XFER, 
            SHUF_00BA, SHUF_DC00, S_4,S_5,S_6,S_7,S_0,S_1,S_2,S_3,36) ;
    SET_W_K_XFER(X2, 40) ;
    MessageSched(X2, X3, X0, X1, XTMP0, XTMP1, XTMP2, XTMP3, XTMP4, XTMP5, XFER, 
            SHUF_00BA, SHUF_DC00, S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,40) ;
    SET_W_K_XFER(X3, 44) ;
    MessageSched(X3, X0, X1, X2, XTMP0, XTMP1, XTMP2, XTMP3, XTMP4, XTMP5, XFER, 
            SHUF_00BA, SHUF_DC00, S_4,S_5,S_6,S_7,S_0,S_1,S_2,S_3,44) ;

    SET_W_K_XFER(X0, 48) ;
    SET_W_K_XFER(X1, 52) ;
    SET_W_K_XFER(X2, 56) ;
    SET_W_K_XFER(X3, 60) ;
    
    RND_0(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,48) ;
    RND_7(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,49) ;
    RND_6(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,50) ;
    RND_5(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,51) ;

    RND_4(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,52) ;
    RND_3(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,53) ;
    RND_2(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,54) ;
    RND_1(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,55) ;

    RND_0(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,56) ;     
    RND_7(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,57) ;
    RND_6(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,58) ;
    RND_5(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,59) ;

    RND_4(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,60) ;
    RND_3(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,61) ;
    RND_2(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,62) ;
    RND_1(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,63) ;
        
    RegToDigest(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7) ;  
        
    #if defined(DEBUG_XMM)
    for(i=0; i<29; i++) {
        for(j=0; j<4*14; j+=4)
            printf("xmm%d[%d]=%08x,%08x,%08x,%08x\n", j/4, i, 
                   xmm[i][j],xmm[i][j+1],xmm[i][j+2],xmm[i][j+3]) ;
        printf("\n") ;
    }
        
    for(i=0; i<64; i++)printf("W_K[%d]%08x\n", i, W_K[i]) ;
    #endif

    return 0;
}

#if defined(HAVE_INTEL_RORX)
static int Transform_AVX1_RORX(Sha256* sha256)
{

    word32 W_K[64] ;  /* temp for W+K */

    #if defined(DEBUG_XMM)
    int i, j ;
    word32 xmm[29][4*15] ;
    #endif

    Init_Masks(BYTE_FLIP_MASK, SHUF_00BA, SHUF_DC00) ;
    W_K_from_buff ; /* X0, X1, X2, X3 = W[0..15] ; */

    DigestToReg(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7) ;
    SET_W_K_XFER(X0, 0) ;
    MessageSched_RORX(X0, X1, X2, X3, XTMP0, XTMP1, XTMP2, XTMP3, XTMP4, XTMP5, 
            XFER, SHUF_00BA, SHUF_DC00, S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,0) ;
    SET_W_K_XFER(X1, 4) ;
    MessageSched_RORX(X1, X2, X3, X0, XTMP0, XTMP1, XTMP2, XTMP3, XTMP4, XTMP5, 
            XFER, SHUF_00BA, SHUF_DC00, S_4,S_5,S_6,S_7,S_0,S_1,S_2,S_3,4) ;
    SET_W_K_XFER(X2, 8) ;
    MessageSched_RORX(X2, X3, X0, X1, XTMP0, XTMP1, XTMP2, XTMP3, XTMP4, XTMP5, 
            XFER, SHUF_00BA, SHUF_DC00, S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,8) ;
    SET_W_K_XFER(X3, 12) ;
    MessageSched_RORX(X3, X0, X1, X2, XTMP0, XTMP1, XTMP2, XTMP3, XTMP4, XTMP5, 
            XFER, SHUF_00BA, SHUF_DC00, S_4,S_5,S_6,S_7,S_0,S_1,S_2,S_3,12) ;
    SET_W_K_XFER(X0, 16) ;
    MessageSched_RORX(X0, X1, X2, X3, XTMP0, XTMP1, XTMP2, XTMP3, XTMP4, XTMP5, 
            XFER, SHUF_00BA, SHUF_DC00, S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,16) ;
    SET_W_K_XFER(X1, 20) ;
    MessageSched_RORX(X1, X2, X3, X0, XTMP0, XTMP1, XTMP2, XTMP3, XTMP4, XTMP5, 
            XFER, SHUF_00BA, SHUF_DC00, S_4,S_5,S_6,S_7,S_0,S_1,S_2,S_3,20) ;
    SET_W_K_XFER(X2, 24) ;
    MessageSched_RORX(X2, X3, X0, X1, XTMP0, XTMP1, XTMP2, XTMP3, XTMP4, XTMP5, 
            XFER, SHUF_00BA, SHUF_DC00, S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,24) ;
    SET_W_K_XFER(X3, 28) ;
    MessageSched_RORX(X3, X0, X1, X2, XTMP0, XTMP1, XTMP2, XTMP3, XTMP4, XTMP5, 
            XFER, SHUF_00BA, SHUF_DC00, S_4,S_5,S_6,S_7,S_0,S_1,S_2,S_3,28) ;
    SET_W_K_XFER(X0, 32) ;
    MessageSched_RORX(X0, X1, X2, X3, XTMP0, XTMP1, XTMP2, XTMP3, XTMP4, XTMP5, 
            XFER, SHUF_00BA, SHUF_DC00, S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,32) ;
    SET_W_K_XFER(X1, 36) ;
    MessageSched_RORX(X1, X2, X3, X0, XTMP0, XTMP1, XTMP2, XTMP3, XTMP4, XTMP5, 
            XFER, SHUF_00BA, SHUF_DC00, S_4,S_5,S_6,S_7,S_0,S_1,S_2,S_3,36) ;
    SET_W_K_XFER(X2, 40) ;
    MessageSched_RORX(X2, X3, X0, X1, XTMP0, XTMP1, XTMP2, XTMP3, XTMP4, XTMP5,
            XFER, SHUF_00BA, SHUF_DC00, S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,40) ;
    SET_W_K_XFER(X3, 44) ;
    MessageSched_RORX(X3, X0, X1, X2, XTMP0, XTMP1, XTMP2, XTMP3, XTMP4, XTMP5,
            XFER, SHUF_00BA, SHUF_DC00, S_4,S_5,S_6,S_7,S_0,S_1,S_2,S_3,44) ;

    SET_W_K_XFER(X0, 48) ;
    SET_W_K_XFER(X1, 52) ;
    SET_W_K_XFER(X2, 56) ;
    SET_W_K_XFER(X3, 60) ;
    
    RND_0(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,48) ;
    RND_7(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,49) ;
    RND_6(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,50) ;
    RND_5(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,51) ;

    RND_4(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,52) ;
    RND_3(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,53) ;
    RND_2(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,54) ;
    RND_1(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,55) ;

    RND_0(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,56) ;     
    RND_7(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,57) ;
    RND_6(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,58) ;
    RND_5(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,59) ;

    RND_4(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,60) ;
    RND_3(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,61) ;
    RND_2(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,62) ;
    RND_1(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,63) ;
        
    RegToDigest(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7) ;  
        
    #if defined(DEBUG_XMM)
    for(i=0; i<29; i++) {
        for(j=0; j<4*14; j+=4)
            printf("xmm%d[%d]=%08x,%08x,%08x,%08x\n", j/4, i, 
                    xmm[i][j],xmm[i][j+1],xmm[i][j+2],xmm[i][j+3]) ;
        printf("\n") ;
    }
        
    for(i=0; i<64; i++)printf("W_K[%d]%08x\n", i, W_K[i]) ;
    #endif

    return 0;
}
#endif  /* HAVE_INTEL_RORX */

#endif  /* HAVE_INTEL_AVX1 */


#if defined(HAVE_INTEL_AVX2)

#define _MOVE_to_REG(ymm, mem)       __asm__ volatile("vmovdqu %0, %%"#ymm" ":: "m"(mem):YMM_REGs) ;
#define _MOVE_to_MEM(mem, ymm)       __asm__ volatile("vmovdqu %%"#ymm", %0" : "=m"(mem)::YMM_REGs) ;
#define _BYTE_SWAP(ymm, map)              __asm__ volatile("vpshufb %0, %%"#ymm", %%"#ymm"\n\t"\
                                                       :: "m"(map):YMM_REGs) ;
#define _MOVE_128(ymm0, ymm1, ymm2, map)   __asm__ volatile("vperm2i128  $"#map", %%"\
                                  #ymm2", %%"#ymm1", %%"#ymm0" ":::YMM_REGs) ;
#define _MOVE_BYTE(ymm0, ymm1, map)  __asm__ volatile("vpshufb %0, %%"#ymm1", %%"\
                                  #ymm0"\n\t":: "m"(map):YMM_REGs) ;
#define _S_TEMP(dest, src, bits, temp)    __asm__ volatile("vpsrld  $"#bits", %%"\
         #src", %%"#dest"\n\tvpslld  $32-"#bits", %%"#src", %%"#temp"\n\tvpor %%"\
         #temp",%%"#dest", %%"#dest" ":::YMM_REGs) ;
#define _AVX2_R(dest, src, bits)          __asm__ volatile("vpsrld  $"#bits", %%"\
                                  #src", %%"#dest" ":::YMM_REGs) ;
#define _XOR(dest, src1, src2)       __asm__ volatile("vpxor   %%"#src1", %%"\
         #src2", %%"#dest" ":::YMM_REGs) ;
#define _OR(dest, src1, src2)       __asm__ volatile("vpor    %%"#src1", %%"\
         #src2", %%"#dest" ":::YMM_REGs) ;
#define _ADD(dest, src1, src2)       __asm__ volatile("vpaddd   %%"#src1", %%"\
         #src2", %%"#dest" ":::YMM_REGs) ;
#define _ADD_MEM(dest, src1, mem)    __asm__ volatile("vpaddd   %0, %%"#src1", %%"\
         #dest" "::"m"(mem):YMM_REGs) ;
#define _BLEND(map, dest, src1, src2)    __asm__ volatile("vpblendd    $"#map", %%"\
         #src1",   %%"#src2", %%"#dest" ":::YMM_REGs) ;

#define    _EXTRACT_XMM_0(xmm, mem)  __asm__ volatile("vpextrd $0, %%"#xmm", %0 ":"=r"(mem)::YMM_REGs) ;
#define    _EXTRACT_XMM_1(xmm, mem)  __asm__ volatile("vpextrd $1, %%"#xmm", %0 ":"=r"(mem)::YMM_REGs) ;
#define    _EXTRACT_XMM_2(xmm, mem)  __asm__ volatile("vpextrd $2, %%"#xmm", %0 ":"=r"(mem)::YMM_REGs) ;
#define    _EXTRACT_XMM_3(xmm, mem)  __asm__ volatile("vpextrd $3, %%"#xmm", %0 ":"=r"(mem)::YMM_REGs) ;
#define    _EXTRACT_XMM_4(ymm, xmm, mem)\
      __asm__ volatile("vperm2i128 $0x1, %%"#ymm", %%"#ymm", %%"#ymm" ":::YMM_REGs) ;\
      __asm__ volatile("vpextrd $0, %%"#xmm", %0 ":"=r"(mem)::YMM_REGs) ;
#define    _EXTRACT_XMM_5(xmm, mem)  __asm__ volatile("vpextrd $1, %%"#xmm", %0 ":"=r"(mem)::YMM_REGs) ;
#define    _EXTRACT_XMM_6(xmm, mem)  __asm__ volatile("vpextrd $2, %%"#xmm", %0 ":"=r"(mem)::YMM_REGs) ;
#define    _EXTRACT_XMM_7(xmm, mem)  __asm__ volatile("vpextrd $3, %%"#xmm", %0 ":"=r"(mem)::YMM_REGs) ;

#define    _SWAP_YMM_HL(ymm)   __asm__ volatile("vperm2i128 $0x1, %%"#ymm", %%"#ymm", %%"#ymm" ":::YMM_REGs) ;
#define     SWAP_YMM_HL(ymm)   _SWAP_YMM_HL(ymm) 

#define MOVE_to_REG(ymm, mem)      _MOVE_to_REG(ymm, mem)
#define MOVE_to_MEM(mem, ymm)      _MOVE_to_MEM(mem, ymm)
#define BYTE_SWAP(ymm, map)        _BYTE_SWAP(ymm, map)
#define MOVE_128(ymm0, ymm1, ymm2, map) _MOVE_128(ymm0, ymm1, ymm2, map) 
#define MOVE_BYTE(ymm0, ymm1, map) _MOVE_BYTE(ymm0, ymm1, map)
#define XOR(dest, src1, src2)      _XOR(dest, src1, src2)
#define OR(dest, src1, src2)       _OR(dest, src1, src2)
#define ADD(dest, src1, src2)      _ADD(dest, src1, src2)
#define ADD_MEM(dest, src1, mem)  _ADD_MEM(dest, src1, mem)
#define BLEND(map, dest, src1, src2) _BLEND(map, dest, src1, src2)

#define S_TMP(dest, src, bits, temp) _S_TEMP(dest, src, bits, temp); 
#define AVX2_S(dest, src, bits)      S_TMP(dest, src, bits, S_TEMP)
#define AVX2_R(dest, src, bits)      _AVX2_R(dest, src, bits)

#define GAMMA0(dest, src)      AVX2_S(dest, src, 7);  AVX2_S(G_TEMP, src, 18); \
    XOR(dest, G_TEMP, dest) ; AVX2_R(G_TEMP, src, 3);  XOR(dest, G_TEMP, dest) ;
#define GAMMA0_1(dest, src)    AVX2_S(dest, src, 7);  AVX2_S(G_TEMP, src, 18); 
#define GAMMA0_2(dest, src)    XOR(dest, G_TEMP, dest) ; AVX2_R(G_TEMP, src, 3);  \
    XOR(dest, G_TEMP, dest) ;

#define GAMMA1(dest, src)      AVX2_S(dest, src, 17); AVX2_S(G_TEMP, src, 19); \
    XOR(dest, G_TEMP, dest) ; AVX2_R(G_TEMP, src, 10); XOR(dest, G_TEMP, dest) ;
#define GAMMA1_1(dest, src)    AVX2_S(dest, src, 17); AVX2_S(G_TEMP, src, 19); 
#define GAMMA1_2(dest, src)    XOR(dest, G_TEMP, dest) ; AVX2_R(G_TEMP, src, 10); \
    XOR(dest, G_TEMP, dest) ;

#define    FEEDBACK1_to_W_I_2    MOVE_BYTE(YMM_TEMP0, W_I, mMAP1toW_I_2[0]) ; \
    BLEND(0x0c, W_I_2, YMM_TEMP0, W_I_2) ;
#define    FEEDBACK2_to_W_I_2    MOVE_128(YMM_TEMP0, W_I, W_I, 0x08) ;  \
    MOVE_BYTE(YMM_TEMP0, YMM_TEMP0, mMAP2toW_I_2[0]) ; BLEND(0x30, W_I_2, YMM_TEMP0, W_I_2) ; 
#define    FEEDBACK3_to_W_I_2    MOVE_BYTE(YMM_TEMP0, W_I, mMAP3toW_I_2[0]) ; \
    BLEND(0xc0, W_I_2, YMM_TEMP0, W_I_2) ; 

#define    FEEDBACK_to_W_I_7     MOVE_128(YMM_TEMP0, W_I, W_I, 0x08) ;\
    MOVE_BYTE(YMM_TEMP0, YMM_TEMP0, mMAPtoW_I_7[0]) ; BLEND(0x80, W_I_7, YMM_TEMP0, W_I_7) ;

#undef voitle

#define W_I_16  ymm8
#define W_I_15  ymm9
#define W_I_7  ymm10
#define W_I_2  ymm11
#define W_I    ymm12
#define G_TEMP     ymm13
#define S_TEMP     ymm14
#define YMM_TEMP0  ymm15
#define YMM_TEMP0x xmm15
#define W_I_TEMP   ymm7
#define W_K_TEMP   ymm15
#define W_K_TEMPx  xmm15

#define YMM_REGs /* Registers are saved in Sha256Update/Finel */
 /* "%ymm7","%ymm8","%ymm9","%ymm10","%ymm11","%ymm12","%ymm13","%ymm14","%ymm15"*/


#define MOVE_15_to_16(w_i_16, w_i_15, w_i_7)\
    __asm__ volatile("vperm2i128  $0x01, %%"#w_i_15", %%"#w_i_15", %%"#w_i_15" ":::YMM_REGs) ;\
    __asm__ volatile("vpblendd    $0x08, %%"#w_i_15", %%"#w_i_7", %%"#w_i_16" ":::YMM_REGs) ;\
    __asm__ volatile("vperm2i128 $0x01,  %%"#w_i_7",  %%"#w_i_7", %%"#w_i_15" ":::YMM_REGs) ;\
    __asm__ volatile("vpblendd    $0x80, %%"#w_i_15", %%"#w_i_16", %%"#w_i_16" ":::YMM_REGs) ;\
    __asm__ volatile("vpshufd    $0x93,  %%"#w_i_16", %%"#w_i_16" ":::YMM_REGs) ;\

#define MOVE_7_to_15(w_i_15, w_i_7)\
    __asm__ volatile("vmovdqu                 %%"#w_i_7",  %%"#w_i_15" ":::YMM_REGs) ;\

#define MOVE_I_to_7(w_i_7, w_i)\
    __asm__ volatile("vperm2i128 $0x01,       %%"#w_i",   %%"#w_i",   %%"#w_i_7" ":::YMM_REGs) ;\
    __asm__ volatile("vpblendd    $0x01,       %%"#w_i_7",   %%"#w_i", %%"#w_i_7" ":::YMM_REGs) ;\
    __asm__ volatile("vpshufd    $0x39, %%"#w_i_7", %%"#w_i_7" ":::YMM_REGs) ;\

#define MOVE_I_to_2(w_i_2, w_i)\
    __asm__ volatile("vperm2i128 $0x01,       %%"#w_i", %%"#w_i", %%"#w_i_2" ":::YMM_REGs) ;\
    __asm__ volatile("vpshufd    $0x0e, %%"#w_i_2", %%"#w_i_2" ":::YMM_REGs) ;\

#define ROTATE_W(w_i_16, w_i_15, w_i_7, w_i_2, w_i)\
    MOVE_15_to_16(w_i_16, w_i_15, w_i_7) ; \
    MOVE_7_to_15(w_i_15, w_i_7) ; \
    MOVE_I_to_7(w_i_7, w_i) ; \
    MOVE_I_to_2(w_i_2, w_i) ;\

#define _RegToDigest(S_0, S_1, S_2, S_3, S_4, S_5, S_6, S_7 )\
    { word32 d ;\
    __asm__ volatile("movl %"#S_0", %0":"=r"(d)::SSE_REGs) ;\
    sha256->digest[0] += d;\
    __asm__ volatile("movl %"#S_1", %0":"=r"(d)::SSE_REGs) ;\
    sha256->digest[1] += d;\
    __asm__ volatile("movl %"#S_2", %0":"=r"(d)::SSE_REGs) ;\
    sha256->digest[2] += d;\
    __asm__ volatile("movl %"#S_3", %0":"=r"(d)::SSE_REGs) ;\
    sha256->digest[3] += d;\
    __asm__ volatile("movl %"#S_4", %0":"=r"(d)::SSE_REGs) ;\
    sha256->digest[4] += d;\
    __asm__ volatile("movl %"#S_5", %0":"=r"(d)::SSE_REGs) ;\
    sha256->digest[5] += d;\
    __asm__ volatile("movl %"#S_6", %0":"=r"(d)::SSE_REGs) ;\
    sha256->digest[6] += d;\
    __asm__ volatile("movl %"#S_7", %0":"=r"(d)::SSE_REGs) ;\
    sha256->digest[7] += d;\
}

#define _DumpS(S_0, S_1, S_2, S_3, S_4, S_5, S_6, S_7 )\
  { word32 d[8] ;\
    __asm__ volatile("movl %"#S_0", %0":"=r"(d[0])::SSE_REGs) ;\
    __asm__ volatile("movl %"#S_1", %0":"=r"(d[1])::SSE_REGs) ;\
    __asm__ volatile("movl %"#S_2", %0":"=r"(d[2])::SSE_REGs) ;\
    __asm__ volatile("movl %"#S_3", %0":"=r"(d[3])::SSE_REGs) ;\
    __asm__ volatile("movl %"#S_4", %0":"=r"(d[4])::SSE_REGs) ;\
    __asm__ volatile("movl %"#S_5", %0":"=r"(d[5])::SSE_REGs) ;\
    __asm__ volatile("movl %"#S_6", %0":"=r"(d[6])::SSE_REGs) ;\
    __asm__ volatile("movl %"#S_7", %0":"=r"(d[7])::SSE_REGs) ;\
        printf("S[0..7]=%08x,%08x,%08x,%08x,%08x,%08x,%08x,%08x\n", d[0],d[1],d[2],d[3],d[4],d[5],d[6],d[7]);\
    __asm__ volatile("movl %0, %"#S_0::"r"(d[0]):SSE_REGs) ;\
    __asm__ volatile("movl %0, %"#S_1::"r"(d[1]):SSE_REGs) ;\
    __asm__ volatile("movl %0, %"#S_2::"r"(d[2]):SSE_REGs) ;\
    __asm__ volatile("movl %0, %"#S_3::"r"(d[3]):SSE_REGs) ;\
    __asm__ volatile("movl %0, %"#S_4::"r"(d[4]):SSE_REGs) ;\
    __asm__ volatile("movl %0, %"#S_5::"r"(d[5]):SSE_REGs) ;\
    __asm__ volatile("movl %0, %"#S_6::"r"(d[6]):SSE_REGs) ;\
    __asm__ volatile("movl %0, %"#S_7::"r"(d[7]):SSE_REGs) ;\
}


#define DigestToReg(S_0, S_1, S_2, S_3, S_4, S_5, S_6, S_7 )\
    _DigestToReg(S_0, S_1, S_2, S_3, S_4, S_5, S_6, S_7 )

#define RegToDigest(S_0, S_1, S_2, S_3, S_4, S_5, S_6, S_7 )\
    _RegToDigest(S_0, S_1, S_2, S_3, S_4, S_5, S_6, S_7 )

#define DumS(S_0, S_1, S_2, S_3, S_4, S_5, S_6, S_7 )\
    _DumpS(S_0, S_1, S_2, S_3, S_4, S_5, S_6, S_7 )

        
    /* Byte swap Masks to ensure that rest of the words are filled with zero's. */
    static const unsigned long mBYTE_FLIP_MASK_16[] =  
        { 0x0405060700010203, 0x0c0d0e0f08090a0b, 0x0405060700010203, 0x0c0d0e0f08090a0b } ;
    static const unsigned long mBYTE_FLIP_MASK_15[] =  
        { 0x0405060700010203, 0x0c0d0e0f08090a0b, 0x0405060700010203, 0x0c0d0e0f08090a0b } ;
    static const unsigned long mBYTE_FLIP_MASK_7 [] =  
        { 0x0405060700010203, 0x0c0d0e0f08090a0b, 0x0405060700010203, 0x8080808008090a0b } ;
    static const unsigned long mBYTE_FLIP_MASK_2 [] =  
        { 0x0405060700010203, 0x8080808080808080, 0x8080808080808080, 0x8080808080808080 } ;

    static const unsigned long mMAPtoW_I_7[] =  
        { 0x8080808080808080, 0x8080808080808080, 0x8080808080808080, 0x0302010080808080 } ;
    static const unsigned long mMAP1toW_I_2[] = 
        { 0x8080808080808080, 0x0706050403020100, 0x8080808080808080, 0x8080808080808080 } ;
    static const unsigned long mMAP2toW_I_2[] = 
        { 0x8080808080808080, 0x8080808080808080, 0x0f0e0d0c0b0a0908, 0x8080808080808080 } ;
    static const unsigned long mMAP3toW_I_2[] = 
        { 0x8080808080808080, 0x8080808080808080, 0x8080808080808080, 0x0706050403020100 } ;
 
static int Transform_AVX2(Sha256* sha256)
{

    #ifdef WOLFSSL_SMALL_STACK
        word32* W_K;
        W_K = (word32*) XMALLOC(sizeof(word32) * 64, NULL, DYNAMIC_TYPE_TMP_BUFFER);
        if (W_K == NULL)
            return MEMORY_E;
    #else
        word32 W_K[64]  ;
    #endif

    MOVE_to_REG(W_I_16, sha256->buffer[0]);     BYTE_SWAP(W_I_16, mBYTE_FLIP_MASK_16[0]) ;
    MOVE_to_REG(W_I_15, sha256->buffer[1]);     BYTE_SWAP(W_I_15, mBYTE_FLIP_MASK_15[0]) ;
    MOVE_to_REG(W_I,    sha256->buffer[8]) ;    BYTE_SWAP(W_I,    mBYTE_FLIP_MASK_16[0]) ;
    MOVE_to_REG(W_I_7,  sha256->buffer[16-7]) ; BYTE_SWAP(W_I_7,  mBYTE_FLIP_MASK_7[0])  ;
    MOVE_to_REG(W_I_2,  sha256->buffer[16-2]) ; BYTE_SWAP(W_I_2,  mBYTE_FLIP_MASK_2[0])  ;

    DigestToReg(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7) ;

    ADD_MEM(W_K_TEMP, W_I_16, K[0]) ;
    MOVE_to_MEM(W_K[0], W_K_TEMP) ; 

    RND_0(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,0) ;
    RND_7(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,1) ;
    RND_6(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,2) ;
    RND_5(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,3) ;  
    RND_4(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,4) ;
    RND_3(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,5) ;
    RND_2(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,6) ;
    RND_1(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,7) ;

    ADD_MEM(YMM_TEMP0, W_I, K[8]) ;
    MOVE_to_MEM(W_K[8], YMM_TEMP0) ; 

        /* W[i] = Gamma1(W[i-2]) + W[i-7] + Gamma0(W[i-15] + W[i-16]) */
                RND_0_0(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,8) ;
        GAMMA0_1(W_I_TEMP, W_I_15) ;
                RND_0_1(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,8) ;
        GAMMA0_2(W_I_TEMP, W_I_15) ;
                RND_0_2(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,8) ;
        ADD(W_I_TEMP, W_I_16, W_I_TEMP) ;/* for saving W_I before adding incomplete W_I_7 */
                RND_7_0(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,9) ;
        ADD(W_I, W_I_7, W_I_TEMP);
                RND_7_1(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,9) ;
        GAMMA1_1(YMM_TEMP0, W_I_2) ; 
                RND_7_2(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,9) ;
        GAMMA1_2(YMM_TEMP0, W_I_2) ; 
                RND_6_0(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,10) ;
        ADD(W_I, W_I, YMM_TEMP0) ;/* now W[16..17] are completed */
                RND_6_1(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,10) ;
        FEEDBACK1_to_W_I_2 ;
                RND_6_2(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,10) ;
        FEEDBACK_to_W_I_7 ; 
                RND_5_0(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,11) ;
        ADD(W_I_TEMP, W_I_7, W_I_TEMP);
                RND_5_1(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,11) ;
        GAMMA1_1(YMM_TEMP0, W_I_2) ; 
                RND_5_2(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,11) ;
        GAMMA1_2(YMM_TEMP0, W_I_2) ; 
                RND_4_0(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,12) ;
        ADD(W_I, W_I_TEMP, YMM_TEMP0) ;/* now W[16..19] are completed */
                RND_4_1(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,12) ;
        FEEDBACK2_to_W_I_2 ;
                RND_4_2(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,12) ;
        GAMMA1_1(YMM_TEMP0, W_I_2) ;
                RND_3_0(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,13) ;
        GAMMA1_2(YMM_TEMP0, W_I_2) ; 
                RND_3_1(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,13) ;
        ADD(W_I, W_I_TEMP, YMM_TEMP0) ; /* now W[16..21] are completed */
                RND_3_2(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,13) ;
        FEEDBACK3_to_W_I_2 ;
                RND_2_0(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,14) ;
        GAMMA1(YMM_TEMP0, W_I_2) ;
                RND_2_1(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,14) ;
                RND_2_2(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,14) ;
        ADD(W_I, W_I_TEMP, YMM_TEMP0) ; /* now W[16..23] are completed */
                RND_1_0(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,15) ;

        MOVE_to_REG(YMM_TEMP0, K[16]) ;    
                RND_1_1(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,15) ;
        ROTATE_W(W_I_16, W_I_15, W_I_7, W_I_2, W_I) ;
                RND_1_2(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,15) ;
        ADD(YMM_TEMP0, YMM_TEMP0, W_I) ;
        MOVE_to_MEM(W_K[16], YMM_TEMP0) ;

        /* W[i] = Gamma1(W[i-2]) + W[i-7] + Gamma0(W[i-15] + W[i-16]) */
                RND_0_0(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,16) ;
        GAMMA0_1(W_I_TEMP, W_I_15) ;
                RND_0_1(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,16) ;
        GAMMA0_2(W_I_TEMP, W_I_15) ;
                RND_0_2(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,16) ;
        ADD(W_I_TEMP, W_I_16, W_I_TEMP) ;/* for saving W_I before adding incomplete W_I_7 */
                RND_7_0(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,17) ;
        ADD(W_I, W_I_7, W_I_TEMP);
                RND_7_1(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,17) ;
        GAMMA1_1(YMM_TEMP0, W_I_2) ; 
                RND_7_2(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,17) ;
        GAMMA1_2(YMM_TEMP0, W_I_2) ; 
                RND_6_0(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,18) ;
        ADD(W_I, W_I, YMM_TEMP0) ;/* now W[16..17] are completed */
                RND_6_1(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,18) ;
        FEEDBACK1_to_W_I_2 ;
                RND_6_2(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,18) ;
        FEEDBACK_to_W_I_7 ; 
                RND_5_0(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,19) ;
        ADD(W_I_TEMP, W_I_7, W_I_TEMP);
                RND_5_1(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,19) ;
        GAMMA1(YMM_TEMP0, W_I_2) ; 
                RND_5_2(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,19) ;
        GAMMA1_2(YMM_TEMP0, W_I_2) ; 
                RND_4_0(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,20) ;
        ADD(W_I, W_I_TEMP, YMM_TEMP0) ;/* now W[16..19] are completed */
                RND_4_1(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,20) ;
        FEEDBACK2_to_W_I_2 ;
                RND_4_2(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,20) ;
        GAMMA1_1(YMM_TEMP0, W_I_2) ;
                RND_3_0(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,21) ;
        GAMMA1_2(YMM_TEMP0, W_I_2) ; 
                RND_3_1(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,21) ;
        ADD(W_I, W_I_TEMP, YMM_TEMP0) ; /* now W[16..21] are completed */
                RND_3_2(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,21) ;
        FEEDBACK3_to_W_I_2 ;
                RND_2_0(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,22) ;
        GAMMA1_1(YMM_TEMP0, W_I_2) ;
                RND_2_1(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,22) ;
        GAMMA1_2(YMM_TEMP0, W_I_2) ; 
                RND_2_2(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,22) ;
        ADD(W_I, W_I_TEMP, YMM_TEMP0) ; /* now W[16..23] are completed */
                RND_1_0(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,23) ;

        MOVE_to_REG(YMM_TEMP0, K[24]) ;    
                RND_1_1(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,23) ;
        ROTATE_W(W_I_16, W_I_15, W_I_7, W_I_2, W_I) ;
                RND_1_2(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,23) ;
        ADD(YMM_TEMP0, YMM_TEMP0, W_I) ;
        MOVE_to_MEM(W_K[24], YMM_TEMP0) ;

                /* W[i] = Gamma1(W[i-2]) + W[i-7] + Gamma0(W[i-15] + W[i-16]) */
                RND_0_0(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,24) ;
        GAMMA0_1(W_I_TEMP, W_I_15) ;
                RND_0_1(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,24) ;
        GAMMA0_2(W_I_TEMP, W_I_15) ;
                RND_0_2(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,24) ;
        ADD(W_I_TEMP, W_I_16, W_I_TEMP) ;/* for saving W_I before adding incomplete W_I_7 */
                RND_7_0(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,25) ;
        ADD(W_I, W_I_7, W_I_TEMP);
                RND_7_1(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,25) ;
        GAMMA1_1(YMM_TEMP0, W_I_2) ; 
                RND_7_2(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,25) ;
        GAMMA1_2(YMM_TEMP0, W_I_2) ; 
                RND_6_0(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,26) ;
        ADD(W_I, W_I, YMM_TEMP0) ;/* now W[16..17] are completed */
                RND_6_1(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,26) ;
        FEEDBACK1_to_W_I_2 ;
                RND_6_2(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,26) ;
        FEEDBACK_to_W_I_7 ; 
                RND_5_0(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,27) ;
        ADD(W_I_TEMP, W_I_7, W_I_TEMP);
                RND_5_1(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,27) ;
        GAMMA1_1(YMM_TEMP0, W_I_2) ; 
                RND_5_2(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,27) ;
        GAMMA1_2(YMM_TEMP0, W_I_2) ; 
                RND_4_0(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,28) ;
        ADD(W_I, W_I_TEMP, YMM_TEMP0) ;/* now W[16..19] are completed */
                RND_4_1(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,28) ;
        FEEDBACK2_to_W_I_2 ;
                RND_4_2(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,28) ;
        GAMMA1_1(YMM_TEMP0, W_I_2) ;
                RND_3_0(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,29) ;
        GAMMA1_2(YMM_TEMP0, W_I_2) ; 
                RND_3_1(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,29) ;
        ADD(W_I, W_I_TEMP, YMM_TEMP0) ; /* now W[16..21] are completed */
                RND_3_2(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,29) ;
        FEEDBACK3_to_W_I_2 ;
                RND_2_0(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,30) ;
        GAMMA1(YMM_TEMP0, W_I_2) ;
                RND_2_1(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,30) ;
                RND_2_2(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,30) ;
        ADD(W_I, W_I_TEMP, YMM_TEMP0) ; /* now W[16..23] are completed */
                RND_1_0(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,31) ;

        MOVE_to_REG(YMM_TEMP0, K[32]) ;    
                RND_1_1(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,31) ;
        ROTATE_W(W_I_16, W_I_15, W_I_7, W_I_2, W_I) ;
                RND_1_2(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,31) ;
        ADD(YMM_TEMP0, YMM_TEMP0, W_I) ;
        MOVE_to_MEM(W_K[32], YMM_TEMP0) ;

        
                /* W[i] = Gamma1(W[i-2]) + W[i-7] + Gamma0(W[i-15] + W[i-16]) */
                RND_0_0(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,32) ;
        GAMMA0_1(W_I_TEMP, W_I_15) ;
                RND_0_1(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,32) ;
        GAMMA0_2(W_I_TEMP, W_I_15) ;
                RND_0_2(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,32) ;
        ADD(W_I_TEMP, W_I_16, W_I_TEMP) ;/* for saving W_I before adding incomplete W_I_7 */
                RND_7_0(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,33) ;
        ADD(W_I, W_I_7, W_I_TEMP);
                RND_7_1(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,33) ;
        GAMMA1_1(YMM_TEMP0, W_I_2) ;
                RND_7_2(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,33) ;
        GAMMA1_2(YMM_TEMP0, W_I_2) ; 
                RND_6_0(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,34) ;
        ADD(W_I, W_I, YMM_TEMP0) ;/* now W[16..17] are completed */
                RND_6_1(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,34) ;
        FEEDBACK1_to_W_I_2 ;
                RND_6_2(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,34) ;
        FEEDBACK_to_W_I_7 ; 
                RND_5_0(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,35) ;
        ADD(W_I_TEMP, W_I_7, W_I_TEMP);
                RND_5_1(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,35) ;
        GAMMA1_1(YMM_TEMP0, W_I_2) ;
                RND_5_2(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,35) ;
        GAMMA1_2(YMM_TEMP0, W_I_2) ;
                RND_4_0(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,36) ;
        ADD(W_I, W_I_TEMP, YMM_TEMP0) ;/* now W[16..19] are completed */
                RND_4_1(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,36) ;
        FEEDBACK2_to_W_I_2 ;
                RND_4_2(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,36) ;
        GAMMA1_1(YMM_TEMP0, W_I_2) ;
                RND_3_0(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,37) ;
        GAMMA1_2(YMM_TEMP0, W_I_2) ;
                RND_3_1(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,37) ;
        ADD(W_I, W_I_TEMP, YMM_TEMP0) ; /* now W[16..21] are completed */
                RND_3_2(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,37) ;
        FEEDBACK3_to_W_I_2 ;
                RND_2_0(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,38) ;
        GAMMA1_1(YMM_TEMP0, W_I_2) ;
                RND_2_1(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,38) ;
        GAMMA1_2(YMM_TEMP0, W_I_2) ;
                RND_2_2(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,38) ;
        ADD(W_I, W_I_TEMP, YMM_TEMP0) ; /* now W[16..23] are completed */
                RND_1_0(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,39) ;

        MOVE_to_REG(YMM_TEMP0, K[40]) ;    
                RND_1_1(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,39) ;
        ROTATE_W(W_I_16, W_I_15, W_I_7, W_I_2, W_I) ;
                RND_1_2(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,39) ;
        ADD(YMM_TEMP0, YMM_TEMP0, W_I) ;
        MOVE_to_MEM(W_K[40], YMM_TEMP0) ;

                /* W[i] = Gamma1(W[i-2]) + W[i-7] + Gamma0(W[i-15] + W[i-16]) */
                RND_0_0(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,40) ;
        GAMMA0_1(W_I_TEMP, W_I_15) ;
                RND_0_1(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,40) ;
        GAMMA0_2(W_I_TEMP, W_I_15) ;
                RND_0_2(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,40) ;
        ADD(W_I_TEMP, W_I_16, W_I_TEMP) ;/* for saving W_I before adding incomplete W_I_7 */
                RND_7_0(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,41) ;
        ADD(W_I, W_I_7, W_I_TEMP);
                RND_7_1(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,41) ;
        GAMMA1_1(YMM_TEMP0, W_I_2) ;
                RND_7_2(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,41) ;
        GAMMA1_2(YMM_TEMP0, W_I_2) ;
                RND_6_0(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,42) ;
        ADD(W_I, W_I, YMM_TEMP0) ;/* now W[16..17] are completed */
                RND_6_1(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,42) ;
        FEEDBACK1_to_W_I_2 ;
                RND_6_2(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,42) ;
        FEEDBACK_to_W_I_7 ; 
                RND_5_0(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,43) ;
        ADD(W_I_TEMP, W_I_7, W_I_TEMP);
                RND_5_1(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,43) ;
        GAMMA1_1(YMM_TEMP0, W_I_2) ; 
                RND_5_2(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,43) ;
        GAMMA1_2(YMM_TEMP0, W_I_2) ;
                RND_4_0(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,44) ;
        ADD(W_I, W_I_TEMP, YMM_TEMP0) ;/* now W[16..19] are completed */
                RND_4_1(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,44) ;
        FEEDBACK2_to_W_I_2 ;
                RND_4_2(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,44) ;
        GAMMA1_1(YMM_TEMP0, W_I_2) ;
                RND_3_0(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,45) ;
        GAMMA1_2(YMM_TEMP0, W_I_2) ;
                RND_3_1(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,45) ;
        ADD(W_I, W_I_TEMP, YMM_TEMP0) ; /* now W[16..21] are completed */
                RND_3_2(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,45) ;
        FEEDBACK3_to_W_I_2 ;
                RND_2_0(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,46) ;
        GAMMA1_1(YMM_TEMP0, W_I_2) ;
                RND_2_1(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,46) ;
        GAMMA1_2(YMM_TEMP0, W_I_2) ;
                RND_2_2(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,46) ;
        ADD(W_I, W_I_TEMP, YMM_TEMP0) ; /* now W[16..23] are completed */
                RND_1_0(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,47) ;

        MOVE_to_REG(YMM_TEMP0, K[48]) ;    
                RND_1_1(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,47) ;
        ROTATE_W(W_I_16, W_I_15, W_I_7, W_I_2, W_I) ;
                RND_1_2(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,47) ;
        ADD(YMM_TEMP0, YMM_TEMP0, W_I) ;
        MOVE_to_MEM(W_K[48], YMM_TEMP0) ;
        
                /* W[i] = Gamma1(W[i-2]) + W[i-7] + Gamma0(W[i-15] + W[i-16]) */
                RND_0_0(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,48) ;
        GAMMA0_1(W_I_TEMP, W_I_15) ;
                RND_0_1(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,48) ;
        GAMMA0_2(W_I_TEMP, W_I_15) ;
                RND_0_2(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,48) ;
        ADD(W_I_TEMP, W_I_16, W_I_TEMP) ;/* for saving W_I before adding incomplete W_I_7 */
                RND_7_0(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,49) ;
        ADD(W_I, W_I_7, W_I_TEMP);
                RND_7_1(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,49) ;
        GAMMA1_1(YMM_TEMP0, W_I_2) ; 
                RND_7_2(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,49) ;
        GAMMA1_2(YMM_TEMP0, W_I_2) ;
                RND_6_0(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,50) ;
        ADD(W_I, W_I, YMM_TEMP0) ;/* now W[16..17] are completed */
                RND_6_1(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,50) ;
        FEEDBACK1_to_W_I_2 ;
                RND_6_2(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,50) ;
        FEEDBACK_to_W_I_7 ; 
                RND_5_0(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,51) ;
        ADD(W_I_TEMP, W_I_7, W_I_TEMP);
                RND_5_1(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,51) ;
        GAMMA1_1(YMM_TEMP0, W_I_2) ;
                RND_5_2(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,51) ;
        GAMMA1_2(YMM_TEMP0, W_I_2) ;
                RND_4_0(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,52) ;
        ADD(W_I, W_I_TEMP, YMM_TEMP0) ;/* now W[16..19] are completed */
                RND_4_1(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,52) ;
        FEEDBACK2_to_W_I_2 ;
                RND_4_2(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,52) ;
        GAMMA1_1(YMM_TEMP0, W_I_2) ;
                RND_3_0(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,53) ;
        GAMMA1_2(YMM_TEMP0, W_I_2) ;
                RND_3_1(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,53) ;
        ADD(W_I, W_I_TEMP, YMM_TEMP0) ; /* now W[16..21] are completed */
                RND_3_2(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,53) ;
        FEEDBACK3_to_W_I_2 ;
                RND_2_0(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,54) ;
        GAMMA1_1(YMM_TEMP0, W_I_2) ;
                RND_2_1(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,54) ;
        GAMMA1_2(YMM_TEMP0, W_I_2) ;
                RND_2_2(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,54) ;
        ADD(W_I, W_I_TEMP, YMM_TEMP0) ; /* now W[16..23] are completed */
                RND_1_0(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,55) ;

        MOVE_to_REG(YMM_TEMP0, K[56]) ;    
                RND_1_1(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,55) ;
        ROTATE_W(W_I_16, W_I_15, W_I_7, W_I_2, W_I) ;
                RND_1_2(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,55) ;
        ADD(YMM_TEMP0, YMM_TEMP0, W_I) ;
        MOVE_to_MEM(W_K[56], YMM_TEMP0) ;        
        
        RND_0(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,56) ;
        RND_7(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,57) ;
        RND_6(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,58) ;
        RND_5(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,59) ;

        RND_4(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,60) ;
        RND_3(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,61) ;
        RND_2(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,62) ;
        RND_1(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7,63) ;

    RegToDigest(S_0,S_1,S_2,S_3,S_4,S_5,S_6,S_7) ;  

    #ifdef WOLFSSL_SMALL_STACK
        XFREE(W, NULL, DYNAMIC_TYPE_TMP_BUFFER);
    #endif
    
    return 0;
}

#endif   /* HAVE_INTEL_AVX2 */

#endif   /* HAVE_FIPS */

#endif   /* WOLFSSL_TI_HAHS */

#endif /* NO_SHA256 */

