/* sha512.c
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

#ifdef HAVE_CONFIG_H
    #include <config.h>
#endif

#include <wolfssl/wolfcrypt/settings.h>
#include <wolfssl/wolfcrypt/sha512.h>

#ifdef WOLFSSL_SHA512

#ifdef HAVE_FIPS
int wc_InitSha512(Sha512* sha)
{
    return InitSha512_fips(sha);
}


int wc_Sha512Update(Sha512* sha, const byte* data, word32 len)
{
    return Sha512Update_fips(sha, data, len);
}


int wc_Sha512Final(Sha512* sha, byte* out)
{
    return Sha512Final_fips(sha, out);
}


int wc_Sha512Hash(const byte* data, word32 len, byte* out)
{
    return Sha512Hash(data, len, out);
}

#if defined(WOLFSSL_SHA384) || defined(HAVE_AESGCM)

int wc_InitSha384(Sha384* sha)
{
    return InitSha384_fips(sha);
}


int wc_Sha384Update(Sha384* sha, const byte* data, word32 len)
{
    return Sha384Update_fips(sha, data, len);
}


int wc_Sha384Final(Sha384* sha, byte* out)
{
    return Sha384Final_fips(sha, out);
}


int wc_Sha384Hash(const byte* data, word32 len, byte* out)
{
    return Sha384Hash(data, len, out);
}
#endif /* WOLFSSL_SHA384 */
#else /* else build without using fips */
#include <wolfssl/wolfcrypt/logging.h>
#include <wolfssl/wolfcrypt/error-crypt.h>

#ifdef NO_INLINE
    #include <wolfssl/wolfcrypt/misc.h>
#else
    #include <wolfcrypt/src/misc.c>
#endif


#ifndef WOLFSSL_HAVE_MIN
#define WOLFSSL_HAVE_MIN

    static INLINE word32 min(word32 a, word32 b)
    {
        return a > b ? b : a;
    }

#endif /* WOLFSSL_HAVE_MIN */

#if defined(USE_INTEL_SPEEDUP)
  #define HAVE_INTEL_AVX1
  #define HAVE_INTEL_AVX2
#endif

#if defined(HAVE_INTEL_AVX1)
/* #define DEBUG_XMM  */
#endif

#if defined(HAVE_INTEL_AVX2)
#define HAVE_INTEL_RORX
/* #define DEBUG_YMM  */
#endif

/*****
Intel AVX1/AVX2 Macro Control Structure

#if defined(HAVE_INteL_SPEEDUP)
    #define HAVE_INTEL_AVX1
    #define HAVE_INTEL_AVX2
#endif

int InitSha512(Sha512* sha512) { 
     Save/Recover XMM, YMM
     ...

     Check Intel AVX cpuid flags
}

#if defined(HAVE_INTEL_AVX1)|| defined(HAVE_INTEL_AVX2)
  Transform_AVX1() ; # Function prototype 
  Transform_AVX2() ; #
#endif

  _Transform() {     # Native Transform Function body
  
  }
  
  int Sha512Update() { 
     Save/Recover XMM, YMM
     ...
  }
  
  int Sha512Final() { 
     Save/Recover XMM, YMM
     ...
  }


#if defined(HAVE_INTEL_AVX1)
   
   XMM Instructions/inline asm Definitions

#endif

#if defined(HAVE_INTEL_AVX2)

   YMM Instructions/inline asm Definitions

#endif

#if defnied(HAVE_INTEL_AVX1)
  
  int Transform_AVX1() {
      Stitched Message Sched/Round
  }

#endif

#if defnied(HAVE_INTEL_AVX2)
  
  int Transform_AVX2() {
      Stitched Message Sched/Round
  }
#endif


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

#define CHECK_SHA512 0x1
#define CHECK_SHA384 0x2

static int set_cpuid_flags(int sha) {  
    if((cpuid_check & sha) ==0) {
        if(cpuid_flag(1, 0, ECX, 28)){ cpuid_flags |= CPUID_AVX1 ;}
        if(cpuid_flag(7, 0, EBX, 5)){  cpuid_flags |= CPUID_AVX2 ; }
        if(cpuid_flag(7, 0, EBX, 8)) { cpuid_flags |= CPUID_BMI2 ; }
        if(cpuid_flag(1, 0, ECX, 30)){ cpuid_flags |= CPUID_RDRAND ;  } 
        if(cpuid_flag(7, 0, EBX, 18)){ cpuid_flags |= CPUID_RDSEED ;  }
		cpuid_check |= sha ;
		return 0 ;
    }
    return 1 ;
}


/* #if defined(HAVE_INTEL_AVX1/2) at the tail of sha512 */

#if defined(HAVE_INTEL_AVX1)
static int Transform_AVX1(Sha512 *sha512) ;
#endif

#if defined(HAVE_INTEL_AVX2)
static int Transform_AVX2(Sha512 *sha512) ; 

#if defined(HAVE_INTEL_AVX1) && defined(HAVE_INTEL_AVX2) && defined(HAVE_INTEL_RORX)
static int Transform_AVX1_RORX(Sha512 *sha512) ;
#endif

#endif

static int _Transform(Sha512 *sha512) ; 
    
static int (*Transform_p)(Sha512* sha512) = _Transform ;

#define Transform(sha512) (*Transform_p)(sha512)

static void set_Transform(void) {
     if(set_cpuid_flags(CHECK_SHA512)) return ;

#if defined(HAVE_INTEL_AVX2)
     if(IS_INTEL_AVX2 && IS_INTEL_BMI2){ 
         Transform_p = Transform_AVX1_RORX; return ; 
         Transform_p = Transform_AVX2      ; 
                  /* for avoiding warning,"not used" */
     }
#endif
#if defined(HAVE_INTEL_AVX1)
     Transform_p = ((IS_INTEL_AVX1) ? Transform_AVX1 : _Transform) ; return ;
#endif
     Transform_p = _Transform ; return ;
}

#else
   #define Transform(sha512) _Transform(sha512)
#endif

/* Dummy for saving MM_REGs on behalf of Transform */
/* #if defined(HAVE_INTEL_AVX2)
 #define  SAVE_XMM_YMM   __asm__ volatile("orq %%r8, %%r8":::\
   "%ymm0","%ymm1","%ymm2","%ymm3","%ymm4","%ymm5","%ymm6","%ymm7","%ymm8","%ymm9","%ymm10","%ymm11",\
   "%ymm12","%ymm13","%ymm14","%ymm15")
*/
#if defined(HAVE_INTEL_AVX1)
   #define  SAVE_XMM_YMM   __asm__ volatile("orq %%r8, %%r8":::\
    "xmm0","xmm1","xmm2","xmm3","xmm4","xmm5","xmm6","xmm7","xmm8","xmm9","xmm10","xmm11","xmm12","xmm13","xmm14","xmm15")
#else
#define  SAVE_XMM_YMM
#endif

#if defined(HAVE_INTEL_AVX1)|| defined(HAVE_INTEL_AVX2)

#include <string.h>

#endif /* defined(HAVE_INTEL_AVX1)|| defined(HAVE_INTEL_AVX2) */


#if defined(HAVE_INTEL_RORX)
#define ROTR(func, bits, x) \
word64 func(word64 x) {  word64 ret ;\
    __asm__ ("rorx $"#bits", %1, %0\n\t":"=r"(ret):"r"(x):) ;\
    return ret ;\
}

static INLINE ROTR(rotrFixed64_28, 28, x)
static INLINE ROTR(rotrFixed64_34, 34, x)
static INLINE ROTR(rotrFixed64_39, 39, x)
static INLINE ROTR(rotrFixed64_14, 14, x)
static INLINE ROTR(rotrFixed64_18, 18, x)
static INLINE ROTR(rotrFixed64_41, 41, x)

#define S0_RORX(x) (rotrFixed64_28(x)^rotrFixed64_34(x)^rotrFixed64_39(x))
#define S1_RORX(x) (rotrFixed64_14(x)^rotrFixed64_18(x)^rotrFixed64_41(x))
#endif

#if defined(HAVE_BYTEREVERSE64) && !defined(HAVE_INTEL_AVX1) && !defined(HAVE_INTEL_AVX2)
#define ByteReverseWords64(out, in, size) ByteReverseWords64_1(out, size)
#define ByteReverseWords64_1(buf, size)\
 { unsigned int i ;\
   for(i=0; i< size/sizeof(word64); i++){\
       __asm__ volatile("bswapq %0":"+r"(buf[i])::) ;\
   }\
}
#endif


int wc_InitSha512(Sha512* sha512)
{
    sha512->digest[0] = W64LIT(0x6a09e667f3bcc908);
    sha512->digest[1] = W64LIT(0xbb67ae8584caa73b);
    sha512->digest[2] = W64LIT(0x3c6ef372fe94f82b);
    sha512->digest[3] = W64LIT(0xa54ff53a5f1d36f1);
    sha512->digest[4] = W64LIT(0x510e527fade682d1);
    sha512->digest[5] = W64LIT(0x9b05688c2b3e6c1f);
    sha512->digest[6] = W64LIT(0x1f83d9abfb41bd6b);
    sha512->digest[7] = W64LIT(0x5be0cd19137e2179);

    sha512->buffLen = 0;
    sha512->loLen   = 0;
    sha512->hiLen   = 0;
    
#if defined(HAVE_INTEL_AVX1)|| defined(HAVE_INTEL_AVX2)
    set_Transform() ; /* choose best Transform function under this runtime environment */
#endif
    
    return 0 ;
}


static const word64 K512[80] = {
	W64LIT(0x428a2f98d728ae22), W64LIT(0x7137449123ef65cd),
	W64LIT(0xb5c0fbcfec4d3b2f), W64LIT(0xe9b5dba58189dbbc),
	W64LIT(0x3956c25bf348b538), W64LIT(0x59f111f1b605d019),
	W64LIT(0x923f82a4af194f9b), W64LIT(0xab1c5ed5da6d8118),
	W64LIT(0xd807aa98a3030242), W64LIT(0x12835b0145706fbe),
	W64LIT(0x243185be4ee4b28c), W64LIT(0x550c7dc3d5ffb4e2),
	W64LIT(0x72be5d74f27b896f), W64LIT(0x80deb1fe3b1696b1),
	W64LIT(0x9bdc06a725c71235), W64LIT(0xc19bf174cf692694),
	W64LIT(0xe49b69c19ef14ad2), W64LIT(0xefbe4786384f25e3),
	W64LIT(0x0fc19dc68b8cd5b5), W64LIT(0x240ca1cc77ac9c65),
	W64LIT(0x2de92c6f592b0275), W64LIT(0x4a7484aa6ea6e483),
	W64LIT(0x5cb0a9dcbd41fbd4), W64LIT(0x76f988da831153b5),
	W64LIT(0x983e5152ee66dfab), W64LIT(0xa831c66d2db43210),
	W64LIT(0xb00327c898fb213f), W64LIT(0xbf597fc7beef0ee4),
	W64LIT(0xc6e00bf33da88fc2), W64LIT(0xd5a79147930aa725),
	W64LIT(0x06ca6351e003826f), W64LIT(0x142929670a0e6e70),
	W64LIT(0x27b70a8546d22ffc), W64LIT(0x2e1b21385c26c926),
	W64LIT(0x4d2c6dfc5ac42aed), W64LIT(0x53380d139d95b3df),
	W64LIT(0x650a73548baf63de), W64LIT(0x766a0abb3c77b2a8),
	W64LIT(0x81c2c92e47edaee6), W64LIT(0x92722c851482353b),
	W64LIT(0xa2bfe8a14cf10364), W64LIT(0xa81a664bbc423001),
	W64LIT(0xc24b8b70d0f89791), W64LIT(0xc76c51a30654be30),
	W64LIT(0xd192e819d6ef5218), W64LIT(0xd69906245565a910),
	W64LIT(0xf40e35855771202a), W64LIT(0x106aa07032bbd1b8),
	W64LIT(0x19a4c116b8d2d0c8), W64LIT(0x1e376c085141ab53),
	W64LIT(0x2748774cdf8eeb99), W64LIT(0x34b0bcb5e19b48a8),
	W64LIT(0x391c0cb3c5c95a63), W64LIT(0x4ed8aa4ae3418acb),
	W64LIT(0x5b9cca4f7763e373), W64LIT(0x682e6ff3d6b2b8a3),
	W64LIT(0x748f82ee5defb2fc), W64LIT(0x78a5636f43172f60),
	W64LIT(0x84c87814a1f0ab72), W64LIT(0x8cc702081a6439ec),
	W64LIT(0x90befffa23631e28), W64LIT(0xa4506cebde82bde9),
	W64LIT(0xbef9a3f7b2c67915), W64LIT(0xc67178f2e372532b),
	W64LIT(0xca273eceea26619c), W64LIT(0xd186b8c721c0c207),
	W64LIT(0xeada7dd6cde0eb1e), W64LIT(0xf57d4f7fee6ed178),
	W64LIT(0x06f067aa72176fba), W64LIT(0x0a637dc5a2c898a6),
	W64LIT(0x113f9804bef90dae), W64LIT(0x1b710b35131c471b),
	W64LIT(0x28db77f523047d84), W64LIT(0x32caab7b40c72493),
	W64LIT(0x3c9ebe0a15c9bebc), W64LIT(0x431d67c49c100d4c),
	W64LIT(0x4cc5d4becb3e42b6), W64LIT(0x597f299cfc657e2a),
	W64LIT(0x5fcb6fab3ad6faec), W64LIT(0x6c44198c4a475817)
};



#define blk0(i) (W[i] = sha512->buffer[i])

#define blk2(i) (W[i&15]+=s1(W[(i-2)&15])+W[(i-7)&15]+s0(W[(i-15)&15]))

#define Ch(x,y,z) (z^(x&(y^z)))
#define Maj(x,y,z) ((x&y)|(z&(x|y)))

#define a(i) T[(0-i)&7]
#define b(i) T[(1-i)&7]
#define c(i) T[(2-i)&7]
#define d(i) T[(3-i)&7]
#define e(i) T[(4-i)&7]
#define f(i) T[(5-i)&7]
#define g(i) T[(6-i)&7]
#define h(i) T[(7-i)&7]

#define S0(x) (rotrFixed64(x,28)^rotrFixed64(x,34)^rotrFixed64(x,39))
#define S1(x) (rotrFixed64(x,14)^rotrFixed64(x,18)^rotrFixed64(x,41))
#define s0(x) (rotrFixed64(x,1)^rotrFixed64(x,8)^(x>>7))
#define s1(x) (rotrFixed64(x,19)^rotrFixed64(x,61)^(x>>6))

#define R(i) h(i)+=S1(e(i))+Ch(e(i),f(i),g(i))+K[i+j]+(j?blk2(i):blk0(i));\
    d(i)+=h(i);h(i)+=S0(a(i))+Maj(a(i),b(i),c(i))

#define blk384(i) (W[i] = sha384->buffer[i])

#define R2(i) h(i)+=S1(e(i))+Ch(e(i),f(i),g(i))+K[i+j]+(j?blk2(i):blk384(i));\
    d(i)+=h(i);h(i)+=S0(a(i))+Maj(a(i),b(i),c(i))

static int _Transform(Sha512* sha512)
{
    const word64* K = K512;

    word32 j;
    word64 T[8];


#ifdef WOLFSSL_SMALL_STACK
    word64* W;
    W = (word64*) XMALLOC(sizeof(word64) * 16, NULL, DYNAMIC_TYPE_TMP_BUFFER);
    if (W == NULL)
        return MEMORY_E;
#else
    word64 W[16];
#endif

    /* Copy digest to working vars */
    XMEMCPY(T, sha512->digest, sizeof(T));

#ifdef USE_SLOW_SHA2
    /* over twice as small, but 50% slower */
    /* 80 operations, not unrolled */
    for (j = 0; j < 80; j += 16) {
        int m; 
        for (m = 0; m < 16; m++) { /* braces needed here for macros {} */
            R(m);
        }
    }
#else
    /* 80 operations, partially loop unrolled */
    for (j = 0; j < 80; j += 16) {
        R( 0); R( 1); R( 2); R( 3);
        R( 4); R( 5); R( 6); R( 7);
        R( 8); R( 9); R(10); R(11);
        R(12); R(13); R(14); R(15);
    }
#endif /* USE_SLOW_SHA2 */

    /* Add the working vars back into digest */

    sha512->digest[0] += a(0);
    sha512->digest[1] += b(0);
    sha512->digest[2] += c(0);
    sha512->digest[3] += d(0);
    sha512->digest[4] += e(0);
    sha512->digest[5] += f(0);
    sha512->digest[6] += g(0);
    sha512->digest[7] += h(0);

    /* Wipe variables */
    ForceZero(W, sizeof(word64) * 16);
    ForceZero(T, sizeof(T));

#ifdef WOLFSSL_SMALL_STACK
    XFREE(W, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif

    return 0;
}


static INLINE void AddLength(Sha512* sha512, word32 len)
{
    word32 tmp = sha512->loLen;
    if ( (sha512->loLen += len) < tmp)
        sha512->hiLen++;                       /* carry low to high */
}

int wc_Sha512Update(Sha512* sha512, const byte* data, word32 len)
{
    /* do block size increments */
    byte* local = (byte*)sha512->buffer;
    SAVE_XMM_YMM ; /* for Intel AVX */

    while (len) {
        word32 add = min(len, SHA512_BLOCK_SIZE - sha512->buffLen);
        XMEMCPY(&local[sha512->buffLen], data, add);

        sha512->buffLen += add;
        data         += add;
        len          -= add;

        if (sha512->buffLen == SHA512_BLOCK_SIZE) {
            int ret;
            #if defined(LITTLE_ENDIAN_ORDER)
                #if defined(HAVE_INTEL_AVX1) || defined(HAVE_INTEL_AVX2)
                if(!IS_INTEL_AVX1 && !IS_INTEL_AVX2) 
                #endif
                    ByteReverseWords64(sha512->buffer, sha512->buffer,
                                   SHA512_BLOCK_SIZE);
            #endif
            ret = Transform(sha512);
            if (ret != 0)
                return ret;

            AddLength(sha512, SHA512_BLOCK_SIZE);
            sha512->buffLen = 0;
        }
    }
    return 0;
}


int wc_Sha512Final(Sha512* sha512, byte* hash)
{
    byte* local = (byte*)sha512->buffer;
    int ret;

    SAVE_XMM_YMM ; /* for Intel AVX */
    AddLength(sha512, sha512->buffLen);               /* before adding pads */

    local[sha512->buffLen++] = 0x80;  /* add 1 */

    /* pad with zeros */
    if (sha512->buffLen > SHA512_PAD_SIZE) {
        XMEMSET(&local[sha512->buffLen], 0, SHA512_BLOCK_SIZE -sha512->buffLen);
        sha512->buffLen += SHA512_BLOCK_SIZE - sha512->buffLen;
        #if defined(LITTLE_ENDIAN_ORDER) 
            #if defined(HAVE_INTEL_AVX1) || defined(HAVE_INTEL_AVX2)
            if(!IS_INTEL_AVX1 && !IS_INTEL_AVX2)
            #endif
            ByteReverseWords64(sha512->buffer,sha512->buffer,SHA512_BLOCK_SIZE);
        #endif
        ret = Transform(sha512);
        if (ret != 0)
            return ret;

        sha512->buffLen = 0;
    }
    XMEMSET(&local[sha512->buffLen], 0, SHA512_PAD_SIZE - sha512->buffLen);
   
    /* put lengths in bits */
    sha512->hiLen = (sha512->loLen >> (8*sizeof(sha512->loLen) - 3)) + 
                 (sha512->hiLen << 3);
    sha512->loLen = sha512->loLen << 3;

    /* store lengths */
    #if defined(LITTLE_ENDIAN_ORDER)
        #if defined(HAVE_INTEL_AVX1) || defined(HAVE_INTEL_AVX2)
        if(!IS_INTEL_AVX1 && !IS_INTEL_AVX2)
        #endif
        ByteReverseWords64(sha512->buffer, sha512->buffer, SHA512_PAD_SIZE);
    #endif
    /* ! length ordering dependent on digest endian type ! */

    sha512->buffer[SHA512_BLOCK_SIZE / sizeof(word64) - 2] = sha512->hiLen;
    sha512->buffer[SHA512_BLOCK_SIZE / sizeof(word64) - 1] = sha512->loLen;
    #if defined(HAVE_INTEL_AVX1) || defined(HAVE_INTEL_AVX2)
    if(IS_INTEL_AVX1 || IS_INTEL_AVX2)
        ByteReverseWords64(&(sha512->buffer[SHA512_BLOCK_SIZE / sizeof(word64) - 2]),
                           &(sha512->buffer[SHA512_BLOCK_SIZE / sizeof(word64) - 2]),
                           SHA512_BLOCK_SIZE - SHA512_PAD_SIZE);
    #endif
    ret = Transform(sha512);
    if (ret != 0)
        return ret;

    #ifdef LITTLE_ENDIAN_ORDER
        ByteReverseWords64(sha512->digest, sha512->digest, SHA512_DIGEST_SIZE);
    #endif
    XMEMCPY(hash, sha512->digest, SHA512_DIGEST_SIZE);

    return wc_InitSha512(sha512);  /* reset state */
}


int wc_Sha512Hash(const byte* data, word32 len, byte* hash)
{
    int ret = 0;
#ifdef WOLFSSL_SMALL_STACK
    Sha512* sha512;
#else
    Sha512 sha512[1];
#endif

#ifdef WOLFSSL_SMALL_STACK
    sha512 = (Sha512*)XMALLOC(sizeof(Sha512), NULL, DYNAMIC_TYPE_TMP_BUFFER);
    if (sha512 == NULL)
        return MEMORY_E;
#endif
    
    if ((ret = wc_InitSha512(sha512)) != 0) {
        WOLFSSL_MSG("InitSha512 failed");
    }
    else if ((ret = wc_Sha512Update(sha512, data, len)) != 0) {
        WOLFSSL_MSG("Sha512Update failed");
    }
    else if ((ret = wc_Sha512Final(sha512, hash)) != 0) {
        WOLFSSL_MSG("Sha512Final failed");
    }
    
#ifdef WOLFSSL_SMALL_STACK
    XFREE(sha512, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif
    
    return ret;
}

#if defined(HAVE_INTEL_AVX1)

#define Rx_1(i) h(i)+=S1(e(i))+Ch(e(i),f(i),g(i))+K[i+j] + W_X[i] ;
#define Rx_2(i) d(i)+=h(i);
#define Rx_3(i) h(i)+=S0(a(i))+Maj(a(i),b(i),c(i));

#if defined(HAVE_INTEL_RORX)
#define Rx_RORX_1(i) h(i)+=S1_RORX(e(i))+Ch(e(i),f(i),g(i))+K[i+j] + W_X[i] ;
#define Rx_RORX_2(i) d(i)+=h(i);
#define Rx_RORX_3(i) h(i)+=S0_RORX(a(i))+Maj(a(i),b(i),c(i));
#endif

#endif

#if defined(HAVE_INTEL_AVX2) 
#define Ry_1(i, w) h(i)+=S1(e(i))+Ch(e(i),f(i),g(i))+K[i+j] + w ; 
#define Ry_2(i, w) d(i)+=h(i);
#define Ry_3(i, w) h(i)+=S0(a(i))+Maj(a(i),b(i),c(i));
#endif

#if defined(HAVE_INTEL_AVX1) /* inline Assember for Intel AVX1 instructions */
#if defined(DEBUG_XMM)

#define SAVE_REG(i)     __asm__ volatile("vmovdqu %%xmm"#i", %0 \n\t":"=m"(reg[i][0])::XMM_REGs);
#define RECV_REG(i)     __asm__ volatile("vmovdqu %0, %%xmm"#i" \n\t"::"m"(reg[i][0]):XMM_REGs);

#define _DUMP_REG(REG, name)\
    { word64 buf[16] ;word64 reg[16][2];int k ;\
      SAVE_REG(0); SAVE_REG(1); SAVE_REG(2);  SAVE_REG(3);  SAVE_REG(4);  \
      SAVE_REG(5);   SAVE_REG(6); SAVE_REG(7);SAVE_REG(8); SAVE_REG(9); SAVE_REG(10);\
       SAVE_REG(11); SAVE_REG(12); SAVE_REG(13); SAVE_REG(14); SAVE_REG(15); \
      __asm__ volatile("vmovdqu %%"#REG", %0 \n\t":"=m"(buf[0])::XMM_REGs);\
      printf(" "#name":\t") ; for(k=0; k<2; k++) printf("%016lx.", (word64)(buf[k])); printf("\n") ; \
      RECV_REG(0); RECV_REG(1); RECV_REG(2);  RECV_REG(3);  RECV_REG(4);\
      RECV_REG(5);   RECV_REG(6); RECV_REG(7); RECV_REG(8); RECV_REG(9);\
      RECV_REG(10); RECV_REG(11); RECV_REG(12); RECV_REG(13); RECV_REG(14); RECV_REG(15);\
    }

#define DUMP_REG(REG) _DUMP_REG(REG, #REG) 
#define PRINTF(fmt, ...) 

#else

#define DUMP_REG(REG) 
#define PRINTF(fmt, ...) 

#endif

#define _MOVE_to_REG(xymm, mem)       __asm__ volatile("vmovdqu %0, %%"#xymm" "\
        :: "m"(mem):XMM_REGs) ;
#define _MOVE_to_MEM(mem,i, xymm)     __asm__ volatile("vmovdqu %%"#xymm", %0" :\
         "=m"(mem[i]),"=m"(mem[i+1]),"=m"(mem[i+2]),"=m"(mem[i+3])::XMM_REGs) ;
#define _MOVE(dest, src)              __asm__ volatile("vmovdqu %%"#src",  %%"\
        #dest" ":::XMM_REGs) ;

#define _S_TEMP(dest, src, bits, temp)  __asm__ volatile("vpsrlq  $"#bits", %%"\
        #src", %%"#dest"\n\tvpsllq  $64-"#bits", %%"#src", %%"#temp"\n\tvpor %%"\
        #temp",%%"#dest", %%"#dest" ":::XMM_REGs) ;
#define _AVX1_R(dest, src, bits)      __asm__ volatile("vpsrlq  $"#bits", %%"\
        #src", %%"#dest" ":::XMM_REGs) ;
#define _XOR(dest, src1, src2)        __asm__ volatile("vpxor   %%"#src1", %%"\
        #src2", %%"#dest" ":::XMM_REGs) ;
#define _OR(dest, src1, src2)         __asm__ volatile("vpor    %%"#src1", %%"\
        #src2", %%"#dest" ":::XMM_REGs) ;
#define _ADD(dest, src1, src2)        __asm__ volatile("vpaddq   %%"#src1", %%"\
        #src2", %%"#dest" ":::XMM_REGs) ;
#define _ADD_MEM(dest, src1, mem)     __asm__ volatile("vpaddq   %0, %%"#src1", %%"\
        #dest" "::"m"(mem):XMM_REGs) ;

#define MOVE_to_REG(xymm, mem)      _MOVE_to_REG(xymm, mem)
#define MOVE_to_MEM(mem, i, xymm)   _MOVE_to_MEM(mem, i, xymm)
#define MOVE(dest, src)             _MOVE(dest, src)  

#define XOR(dest, src1, src2)      _XOR(dest, src1, src2)
#define OR(dest, src1, src2)       _OR(dest, src1, src2)
#define ADD(dest, src1, src2)      _ADD(dest, src1, src2)

#define S_TMP(dest, src, bits, temp) _S_TEMP(dest, src, bits, temp);
#define AVX1_S(dest, src, bits)      S_TMP(dest, src, bits, S_TEMP)
#define AVX1_R(dest, src, bits)      _AVX1_R(dest, src, bits)

#define Init_Mask(mask) \
     __asm__ volatile("vmovdqu %0, %%xmm1\n\t"::"m"(mask):"%xmm1") ;
     
#define _W_from_buff1(w, buff, xmm) \
    /* X0..3(xmm4..7), W[0..15] = sha512->buffer[0.15];  */\
     __asm__ volatile("vmovdqu %1, %%"#xmm"\n\t"\
                      "vpshufb %%xmm1, %%"#xmm", %%"#xmm"\n\t"\
                      "vmovdqu %%"#xmm", %0"\
                      :"=m"(w): "m"(buff):"%xmm0") ;

#define W_from_buff1(w, buff, xmm) _W_from_buff1(w, buff, xmm) 

#define W_from_buff(w, buff)\
     Init_Mask(mBYTE_FLIP_MASK[0]) ;\
     W_from_buff1(w[0], buff[0], W_0);\
     W_from_buff1(w[2], buff[2], W_2);\
     W_from_buff1(w[4], buff[4], W_4);\
     W_from_buff1(w[6], buff[6], W_6);\
     W_from_buff1(w[8], buff[8], W_8);\
     W_from_buff1(w[10],buff[10],W_10);\
     W_from_buff1(w[12],buff[12],W_12);\
     W_from_buff1(w[14],buff[14],W_14);
                          
static word64 mBYTE_FLIP_MASK[] =  { 0x0001020304050607, 0x08090a0b0c0d0e0f } ;

#define W_I_15  xmm14
#define W_I_7   xmm11
#define W_I_2   xmm13
#define W_I     xmm12
#define G_TEMP  xmm0
#define S_TEMP  xmm1
#define XMM_TEMP0  xmm2

#define W_0     xmm12
#define W_2     xmm3
#define W_4     xmm4
#define W_6     xmm5
#define W_8     xmm6
#define W_10    xmm7
#define W_12    xmm8
#define W_14    xmm9

#define XMM_REGs

#define s0_1(dest, src)      AVX1_S(dest, src, 1); 
#define s0_2(dest, src)      AVX1_S(G_TEMP, src, 8); XOR(dest, G_TEMP, dest) ; 
#define s0_3(dest, src)      AVX1_R(G_TEMP, src, 7);  XOR(dest, G_TEMP, dest) ;

#define s1_1(dest, src)      AVX1_S(dest, src, 19);
#define s1_2(dest, src)      AVX1_S(G_TEMP, src, 61); XOR(dest, G_TEMP, dest) ; 
#define s1_3(dest, src)      AVX1_R(G_TEMP, src, 6); XOR(dest, G_TEMP, dest) ;

#define s0_(dest, src)       s0_1(dest, src) ; s0_2(dest, src) ; s0_3(dest, src)
#define s1_(dest, src)       s1_1(dest, src) ; s1_2(dest, src) ; s1_3(dest, src)
        
#define Block_xx_1(i) \
    MOVE_to_REG(W_I_15, W_X[(i-15)&15]) ;\
    MOVE_to_REG(W_I_7,  W_X[(i- 7)&15]) ;\
        
#define Block_xx_2(i) \
    MOVE_to_REG(W_I_2,  W_X[(i- 2)&15]) ;\
    MOVE_to_REG(W_I,    W_X[(i)]) ;\
        
#define Block_xx_3(i) \
    s0_ (XMM_TEMP0, W_I_15) ;\
        
#define Block_xx_4(i) \
    ADD(W_I, W_I, XMM_TEMP0) ;\
    ADD(W_I, W_I, W_I_7) ;\
        
#define Block_xx_5(i) \
    s1_ (XMM_TEMP0, W_I_2) ;\
    
#define Block_xx_6(i) \
    ADD(W_I, W_I, XMM_TEMP0) ;\
    MOVE_to_MEM(W_X,i, W_I) ;\
    if(i==0)\
        MOVE_to_MEM(W_X,16, W_I) ;\

#define Block_xx_7(i) \
    MOVE_to_REG(W_I_15, W_X[(i-15)&15]) ;\
    MOVE_to_REG(W_I_7,  W_X[(i- 7)&15]) ;\
            
#define Block_xx_8(i) \
    MOVE_to_REG(W_I_2,  W_X[(i- 2)&15]) ;\
    MOVE_to_REG(W_I,    W_X[(i)]) ;\

#define Block_xx_9(i) \
    s0_ (XMM_TEMP0, W_I_15) ;\

#define Block_xx_10(i) \
    ADD(W_I, W_I, XMM_TEMP0) ;\
    ADD(W_I, W_I, W_I_7) ;\

#define Block_xx_11(i) \
    s1_ (XMM_TEMP0, W_I_2) ;\

#define Block_xx_12(i) \
    ADD(W_I, W_I, XMM_TEMP0) ;\
    MOVE_to_MEM(W_X,i, W_I) ;\
    if((i)==0)\
        MOVE_to_MEM(W_X,16, W_I) ;\

static inline void Block_0_1(word64 *W_X) { Block_xx_1(0) ; }
static inline void Block_0_2(word64 *W_X) { Block_xx_2(0) ; }
static inline void Block_0_3(void) { Block_xx_3(0) ; }
static inline void Block_0_4(void) { Block_xx_4(0) ; }
static inline void Block_0_5(void) { Block_xx_5(0) ; }
static inline void Block_0_6(word64 *W_X) { Block_xx_6(0) ; }
static inline void Block_0_7(word64 *W_X) { Block_xx_7(2) ; }
static inline void Block_0_8(word64 *W_X) { Block_xx_8(2) ; }
static inline void Block_0_9(void) { Block_xx_9(2) ; }
static inline void Block_0_10(void){ Block_xx_10(2) ; }
static inline void Block_0_11(void){ Block_xx_11(2) ; }
static inline void Block_0_12(word64 *W_X){ Block_xx_12(2) ; }

static inline void Block_4_1(word64 *W_X) { Block_xx_1(4) ; }
static inline void Block_4_2(word64 *W_X) { Block_xx_2(4) ; }
static inline void Block_4_3(void) { Block_xx_3(4) ; }
static inline void Block_4_4(void) { Block_xx_4(4) ; }
static inline void Block_4_5(void) { Block_xx_5(4) ; }
static inline void Block_4_6(word64 *W_X) { Block_xx_6(4) ; }
static inline void Block_4_7(word64 *W_X) { Block_xx_7(6) ; }
static inline void Block_4_8(word64 *W_X) { Block_xx_8(6) ; }
static inline void Block_4_9(void) { Block_xx_9(6) ; }
static inline void Block_4_10(void){ Block_xx_10(6) ; }
static inline void Block_4_11(void){ Block_xx_11(6) ; }
static inline void Block_4_12(word64 *W_X){ Block_xx_12(6) ; }

static inline void Block_8_1(word64 *W_X) { Block_xx_1(8) ; }
static inline void Block_8_2(word64 *W_X) { Block_xx_2(8) ; }
static inline void Block_8_3(void) { Block_xx_3(8) ; }
static inline void Block_8_4(void) { Block_xx_4(8) ; }
static inline void Block_8_5(void) { Block_xx_5(8) ; }
static inline void Block_8_6(word64 *W_X) { Block_xx_6(8) ; }
static inline void Block_8_7(word64 *W_X) { Block_xx_7(10) ; }
static inline void Block_8_8(word64 *W_X) { Block_xx_8(10) ; }
static inline void Block_8_9(void) { Block_xx_9(10) ; }
static inline void Block_8_10(void){ Block_xx_10(10) ; }
static inline void Block_8_11(void){ Block_xx_11(10) ; }
static inline void Block_8_12(word64 *W_X){ Block_xx_12(10) ; }

static inline void Block_12_1(word64 *W_X) { Block_xx_1(12) ; }
static inline void Block_12_2(word64 *W_X) { Block_xx_2(12) ; }
static inline void Block_12_3(void) { Block_xx_3(12) ; }
static inline void Block_12_4(void) { Block_xx_4(12) ; }
static inline void Block_12_5(void) { Block_xx_5(12) ; }
static inline void Block_12_6(word64 *W_X) { Block_xx_6(12) ; }
static inline void Block_12_7(word64 *W_X) { Block_xx_7(14) ; }
static inline void Block_12_8(word64 *W_X) { Block_xx_8(14) ; }
static inline void Block_12_9(void) { Block_xx_9(14) ; }
static inline void Block_12_10(void){ Block_xx_10(14) ; }
static inline void Block_12_11(void){ Block_xx_11(14) ; }
static inline void Block_12_12(word64 *W_X){ Block_xx_12(14) ; }

#endif

#if defined(HAVE_INTEL_AVX2)
static const unsigned long mBYTE_FLIP_MASK_Y[] =
   { 0x0001020304050607, 0x08090a0b0c0d0e0f, 0x0001020304050607, 0x08090a0b0c0d0e0f } ;

#define W_from_buff_Y(buff)\
    { /* X0..3(ymm9..12), W_X[0..15] = sha512->buffer[0.15];  */\
     __asm__ volatile("vmovdqu %0, %%ymm8\n\t"::"m"(mBYTE_FLIP_MASK_Y[0]):YMM_REGs) ;\
     __asm__ volatile("vmovdqu %0, %%ymm12\n\t"\
                      "vmovdqu %1, %%ymm4\n\t"\
                      "vpshufb %%ymm8, %%ymm12, %%ymm12\n\t"\
                      "vpshufb %%ymm8, %%ymm4, %%ymm4\n\t"\
                      :: "m"(buff[0]),  "m"(buff[4]):YMM_REGs) ;\
     __asm__ volatile("vmovdqu %0, %%ymm5\n\t"\
                      "vmovdqu %1, %%ymm6\n\t"\
                      "vpshufb %%ymm8, %%ymm5, %%ymm5\n\t"\
                      "vpshufb %%ymm8, %%ymm6, %%ymm6\n\t"\
                      :: "m"(buff[8]),  "m"(buff[12]):YMM_REGs) ;\
    }

#if defined(DEBUG_YMM)

#define SAVE_REG_Y(i) __asm__ volatile("vmovdqu %%ymm"#i", %0 \n\t":"=m"(reg[i-4][0])::YMM_REGs);
#define RECV_REG_Y(i) __asm__ volatile("vmovdqu %0, %%ymm"#i" \n\t"::"m"(reg[i-4][0]):YMM_REGs);

#define _DUMP_REG_Y(REG, name)\
    { word64 buf[16] ;word64 reg[16][2];int k ;\
      SAVE_REG_Y(4);  SAVE_REG_Y(5);   SAVE_REG_Y(6); SAVE_REG_Y(7); \
      SAVE_REG_Y(8); SAVE_REG_Y(9); SAVE_REG_Y(10); SAVE_REG_Y(11); SAVE_REG_Y(12);\
      SAVE_REG_Y(13); SAVE_REG_Y(14); SAVE_REG_Y(15); \
      __asm__ volatile("vmovdqu %%"#REG", %0 \n\t":"=m"(buf[0])::YMM_REGs);\
      printf(" "#name":\t") ; for(k=0; k<4; k++) printf("%016lx.", (word64)buf[k]) ; printf("\n") ; \
      RECV_REG_Y(4);  RECV_REG_Y(5);   RECV_REG_Y(6); RECV_REG_Y(7); \
      RECV_REG_Y(8); RECV_REG_Y(9); RECV_REG_Y(10); RECV_REG_Y(11); RECV_REG_Y(12); \
      RECV_REG_Y(13); RECV_REG_Y(14); RECV_REG_Y(15);\
    }

#define DUMP_REG_Y(REG) _DUMP_REG_Y(REG, #REG) 
#define DUMP_REG2_Y(REG) _DUMP_REG_Y(REG, #REG) 
#define PRINTF_Y(fmt, ...) 

#else

#define DUMP_REG_Y(REG) 
#define DUMP_REG2_Y(REG)
#define PRINTF_Y(fmt, ...) 

#endif

#define _MOVE_to_REGy(ymm, mem)         __asm__ volatile("vmovdqu %0, %%"#ymm" "\
                                        :: "m"(mem):YMM_REGs) ;
#define _MOVE_to_MEMy(mem,i, ymm)       __asm__ volatile("vmovdqu %%"#ymm", %0" \
        : "=m"(mem[i]),"=m"(mem[i+1]),"=m"(mem[i+2]),"=m"(mem[i+3])::YMM_REGs) ;
#define _MOVE_128y(ymm0, ymm1, ymm2, map)  __asm__ volatile("vperm2i128  $"\
        #map", %%"#ymm2", %%"#ymm1", %%"#ymm0" ":::YMM_REGs) ;
#define _S_TEMPy(dest, src, bits, temp) \
         __asm__ volatile("vpsrlq  $"#bits", %%"#src", %%"#dest"\n\tvpsllq  $64-"#bits\
        ", %%"#src", %%"#temp"\n\tvpor %%"#temp",%%"#dest", %%"#dest" ":::YMM_REGs) ;
#define _AVX2_R(dest, src, bits)        __asm__ volatile("vpsrlq  $"#bits", %%"\
         #src", %%"#dest" ":::YMM_REGs) ;
#define _XORy(dest, src1, src2)         __asm__ volatile("vpxor   %%"#src1", %%"\
         #src2", %%"#dest" ":::YMM_REGs) ;
#define _ADDy(dest, src1, src2)         __asm__ volatile("vpaddq   %%"#src1", %%"\
         #src2", %%"#dest" ":::YMM_REGs) ;
#define _BLENDy(map, dest, src1, src2)  __asm__ volatile("vpblendd    $"#map", %%"\
         #src1",   %%"#src2", %%"#dest" ":::YMM_REGs) ;
#define _BLENDQy(map, dest, src1, src2) __asm__ volatile("vblendpd   $"#map", %%"\
         #src1",   %%"#src2", %%"#dest" ":::YMM_REGs) ;
#define _PERMQy(map, dest, src)         __asm__ volatile("vpermq  $"#map", %%"\
         #src", %%"#dest" ":::YMM_REGs) ;

#define MOVE_to_REGy(ymm, mem)      _MOVE_to_REGy(ymm, mem)
#define MOVE_to_MEMy(mem, i, ymm)   _MOVE_to_MEMy(mem, i, ymm)

#define MOVE_128y(ymm0, ymm1, ymm2, map) _MOVE_128y(ymm0, ymm1, ymm2, map) 
#define XORy(dest, src1, src2)      _XORy(dest, src1, src2)
#define ADDy(dest, src1, src2)      _ADDy(dest, src1, src2)
#define BLENDy(map, dest, src1, src2) _BLENDy(map, dest, src1, src2)
#define BLENDQy(map, dest, src1, src2) _BLENDQy(map, dest, src1, src2)
#define PERMQy(map, dest, src)      _PERMQy(map, dest, src)


#define S_TMPy(dest, src, bits, temp) _S_TEMPy(dest, src, bits, temp);
#define AVX2_S(dest, src, bits)      S_TMPy(dest, src, bits, S_TEMPy)
#define AVX2_R(dest, src, bits)      _AVX2_R(dest, src, bits)


#define    FEEDBACK1_to_W_I_2(w_i_2, w_i)    MOVE_128y(YMM_TEMP0, w_i, w_i, 0x08) ;\
                                       BLENDy(0xf0, w_i_2, YMM_TEMP0, w_i_2) ; 

#define    MOVE_W_to_W_I_15(w_i_15, w_0, w_4)  BLENDQy(0x1, w_i_15, w_4, w_0) ;\
                                       PERMQy(0x39, w_i_15, w_i_15) ;
#define    MOVE_W_to_W_I_7(w_i_7,  w_8, w_12)  BLENDQy(0x1, w_i_7, w_12, w_8) ;\
                                       PERMQy(0x39, w_i_7, w_i_7) ; 
#define    MOVE_W_to_W_I_2(w_i_2,  w_12)       BLENDQy(0xc, w_i_2, w_12, w_i_2) ;\
                                       PERMQy(0x0e, w_i_2, w_i_2) ;


#define W_I_16y  ymm8
#define W_I_15y  ymm9
#define W_I_7y  ymm10
#define W_I_2y  ymm11
#define W_Iy    ymm12
#define G_TEMPy     ymm13
#define S_TEMPy     ymm14
#define YMM_TEMP0  ymm15
#define YMM_TEMP0x xmm15
#define W_I_TEMPy   ymm7
#define W_K_TEMPy   ymm15
#define W_K_TEMPx  xmm15
#define W_0y     ymm12
#define W_4y     ymm4
#define W_8y     ymm5
#define W_12y    ymm6

#define YMM_REGs
/* Registers are saved in Sha512Update/Final */
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

#endif


/***  Transform Body ***/
#if defined(HAVE_INTEL_AVX1)

static int Transform_AVX1(Sha512* sha512)
{
    const word64* K = K512;
    word64 W_X[16+4];
    word32 j;
    word64 T[8];
    /* Copy digest to working vars */
    XMEMCPY(T, sha512->digest, sizeof(T));

    W_from_buff(W_X, sha512->buffer) ;
    for (j = 0; j < 80; j += 16) {
        Rx_1( 0); Block_0_1(W_X); Rx_2( 0); Block_0_2(W_X); Rx_3( 0); Block_0_3(); 
        Rx_1( 1); Block_0_4(); Rx_2( 1); Block_0_5(); Rx_3( 1); Block_0_6(W_X); 
        Rx_1( 2); Block_0_7(W_X); Rx_2( 2); Block_0_8(W_X); Rx_3( 2); Block_0_9();
        Rx_1( 3); Block_0_10();Rx_2( 3); Block_0_11();Rx_3( 3); Block_0_12(W_X);   
        
        Rx_1( 4); Block_4_1(W_X); Rx_2( 4); Block_4_2(W_X); Rx_3( 4); Block_4_3(); 
        Rx_1( 5); Block_4_4(); Rx_2( 5); Block_4_5(); Rx_3( 5); Block_4_6(W_X); 
        Rx_1( 6); Block_4_7(W_X); Rx_2( 6); Block_4_8(W_X); Rx_3( 6); Block_4_9();
        Rx_1( 7); Block_4_10();Rx_2( 7); Block_4_11();Rx_3( 7); Block_4_12(W_X);   
        
        Rx_1( 8); Block_8_1(W_X); Rx_2( 8); Block_8_2(W_X); Rx_3( 8); Block_8_3(); 
        Rx_1( 9); Block_8_4(); Rx_2( 9); Block_8_5(); Rx_3( 9); Block_8_6(W_X); 
        Rx_1(10); Block_8_7(W_X); Rx_2(10); Block_8_8(W_X); Rx_3(10); Block_8_9();
        Rx_1(11); Block_8_10();Rx_2(11); Block_8_11();Rx_3(11); Block_8_12(W_X);   
        
        Rx_1(12); Block_12_1(W_X); Rx_2(12); Block_12_2(W_X); Rx_3(12); Block_12_3(); 
        Rx_1(13); Block_12_4(); Rx_2(13); Block_12_5(); Rx_3(13); Block_12_6(W_X); 
        Rx_1(14); Block_12_7(W_X); Rx_2(14); Block_12_8(W_X); Rx_3(14); Block_12_9();
        Rx_1(15); Block_12_10();Rx_2(15); Block_12_11();Rx_3(15); Block_12_12(W_X);     
    }

    /* Add the working vars back into digest */

    sha512->digest[0] += a(0);
    sha512->digest[1] += b(0);
    sha512->digest[2] += c(0);
    sha512->digest[3] += d(0);
    sha512->digest[4] += e(0);
    sha512->digest[5] += f(0);
    sha512->digest[6] += g(0);
    sha512->digest[7] += h(0);

    /* Wipe variables */
    #if !defined(HAVE_INTEL_AVX1)&&!defined(HAVE_INTEL_AVX2)
    XMEMSET(W_X, 0, sizeof(word64) * 16);
    #endif
    XMEMSET(T, 0, sizeof(T));

    return 0;
}

#endif

#if defined(HAVE_INTEL_AVX2) && defined(HAVE_INTEL_AVX1) && defined(HAVE_INTEL_RORX)

static int Transform_AVX1_RORX(Sha512* sha512)
{
    const word64* K = K512;
    word64 W_X[16+4];
    word32 j;
    word64 T[8];
    /* Copy digest to working vars */
    XMEMCPY(T, sha512->digest, sizeof(T));

    W_from_buff(W_X, sha512->buffer) ;
    for (j = 0; j < 80; j += 16) {
        Rx_RORX_1( 0); Block_0_1(W_X); Rx_RORX_2( 0); Block_0_2(W_X); 
                                    Rx_RORX_3( 0); Block_0_3(); 
        Rx_RORX_1( 1); Block_0_4(); Rx_RORX_2( 1); Block_0_5(); 
                                    Rx_RORX_3( 1); Block_0_6(W_X); 
        Rx_RORX_1( 2); Block_0_7(W_X); Rx_RORX_2( 2); Block_0_8(W_X); 
                                    Rx_RORX_3( 2); Block_0_9();
        Rx_RORX_1( 3); Block_0_10();Rx_RORX_2( 3); Block_0_11();
                                    Rx_RORX_3( 3); Block_0_12(W_X);   
        
        Rx_RORX_1( 4); Block_4_1(W_X); Rx_RORX_2( 4); Block_4_2(W_X); 
                                    Rx_RORX_3( 4); Block_4_3(); 
        Rx_RORX_1( 5); Block_4_4(); Rx_RORX_2( 5); Block_4_5(); 
                                    Rx_RORX_3( 5); Block_4_6(W_X); 
        Rx_RORX_1( 6); Block_4_7(W_X); Rx_RORX_2( 6); Block_4_8(W_X); 
                                    Rx_RORX_3( 6); Block_4_9();
        Rx_RORX_1( 7); Block_4_10();Rx_RORX_2( 7); Block_4_11();
                                    Rx_RORX_3( 7); Block_4_12(W_X);   
        
        Rx_RORX_1( 8); Block_8_1(W_X); Rx_RORX_2( 8); Block_8_2(W_X); 
                                    Rx_RORX_3( 8); Block_8_3(); 
        Rx_RORX_1( 9); Block_8_4(); Rx_RORX_2( 9); Block_8_5(); 
                                    Rx_RORX_3( 9); Block_8_6(W_X); 
        Rx_RORX_1(10); Block_8_7(W_X); Rx_RORX_2(10); Block_8_8(W_X); 
                                    Rx_RORX_3(10); Block_8_9();
        Rx_RORX_1(11); Block_8_10();Rx_RORX_2(11); Block_8_11();
                                    Rx_RORX_3(11); Block_8_12(W_X);   
        
        Rx_RORX_1(12); Block_12_1(W_X); Rx_RORX_2(12); Block_12_2(W_X); 
                                     Rx_RORX_3(12); Block_12_3(); 
        Rx_RORX_1(13); Block_12_4(); Rx_RORX_2(13); Block_12_5(); 
                                     Rx_RORX_3(13); Block_12_6(W_X); 
        Rx_RORX_1(14); Block_12_7(W_X); Rx_RORX_2(14); Block_12_8(W_X); 
                                     Rx_RORX_3(14); Block_12_9();
        Rx_RORX_1(15); Block_12_10();Rx_RORX_2(15); Block_12_11();
                                     Rx_RORX_3(15); Block_12_12(W_X);     
    }
    /* Add the working vars back into digest */

    sha512->digest[0] += a(0);
    sha512->digest[1] += b(0);
    sha512->digest[2] += c(0);
    sha512->digest[3] += d(0);
    sha512->digest[4] += e(0);
    sha512->digest[5] += f(0);
    sha512->digest[6] += g(0);
    sha512->digest[7] += h(0);

    /* Wipe variables */
    #if !defined(HAVE_INTEL_AVX1)&&!defined(HAVE_INTEL_AVX2)
    XMEMSET(W_X, 0, sizeof(word64) * 16);
    #endif
    XMEMSET(T, 0, sizeof(T));

    return 0;
}
#endif

#if defined(HAVE_INTEL_AVX2)

#define s0_1y(dest, src)      AVX2_S(dest, src, 1); 
#define s0_2y(dest, src)      AVX2_S(G_TEMPy, src, 8); XORy(dest, G_TEMPy, dest) ; 
#define s0_3y(dest, src)      AVX2_R(G_TEMPy, src, 7);  XORy(dest, G_TEMPy, dest) ;

#define s1_1y(dest, src)      AVX2_S(dest, src, 19);
#define s1_2y(dest, src)      AVX2_S(G_TEMPy, src, 61); XORy(dest, G_TEMPy, dest) ; 
#define s1_3y(dest, src)      AVX2_R(G_TEMPy, src, 6); XORy(dest, G_TEMPy, dest) ;

#define s0_y(dest, src)       s0_1y(dest, src) ; s0_2y(dest, src) ; s0_3y(dest, src)
#define s1_y(dest, src)       s1_1y(dest, src) ; s1_2y(dest, src) ; s1_3y(dest, src)

#define blk384(i) (W[i] = sha384->buffer[i])


#define Block_Y_xx_1(i, w_0, w_4, w_8, w_12)\
    MOVE_W_to_W_I_15(W_I_15y, w_0, w_4) ;\
    MOVE_W_to_W_I_7 (W_I_7y,  w_8, w_12) ;\
    MOVE_W_to_W_I_2 (W_I_2y,  w_12) ;\

#define Block_Y_xx_2(i, w_0, w_4, w_8, w_12)\
    s0_1y (YMM_TEMP0, W_I_15y) ;\

#define Block_Y_xx_3(i, w_0, w_4, w_8, w_12)\
    s0_2y (YMM_TEMP0, W_I_15y) ;\

#define Block_Y_xx_4(i, w_0, w_4, w_8, w_12)\
    s0_3y (YMM_TEMP0, W_I_15y) ;\

#define Block_Y_xx_5(i, w_0, w_4, w_8, w_12)\
    ADDy(W_I_TEMPy, w_0, YMM_TEMP0) ;\

#define Block_Y_xx_6(i, w_0, w_4, w_8, w_12)\
    ADDy(W_I_TEMPy, W_I_TEMPy, W_I_7y) ;\
    s1_1y (YMM_TEMP0, W_I_2y) ;\

#define Block_Y_xx_7(i, w_0, w_4, w_8, w_12)\
    s1_2y (YMM_TEMP0, W_I_2y) ;\

#define Block_Y_xx_8(i, w_0, w_4, w_8, w_12)\
    s1_3y (YMM_TEMP0, W_I_2y) ;\
    ADDy(w_0, W_I_TEMPy, YMM_TEMP0) ;\

#define Block_Y_xx_9(i, w_0, w_4, w_8, w_12)\
    FEEDBACK1_to_W_I_2(W_I_2y, w_0) ;\

#define Block_Y_xx_10(i, w_0, w_4, w_8, w_12) \
    s1_1y (YMM_TEMP0, W_I_2y) ;\

#define Block_Y_xx_11(i, w_0, w_4, w_8, w_12) \
    s1_2y (YMM_TEMP0, W_I_2y) ;\

#define Block_Y_xx_12(i, w_0, w_4, w_8, w_12)\
    s1_3y (YMM_TEMP0, W_I_2y) ;\
    ADDy(w_0, W_I_TEMPy, YMM_TEMP0) ;\
    MOVE_to_MEMy(w,0, w_4) ;\


static inline void Block_Y_0_1(void) { Block_Y_xx_1(0, W_0y, W_4y, W_8y, W_12y) ; }
static inline void Block_Y_0_2(void) { Block_Y_xx_2(0, W_0y, W_4y, W_8y, W_12y) ; }
static inline void Block_Y_0_3(void) { Block_Y_xx_3(0, W_0y, W_4y, W_8y, W_12y) ; }
static inline void Block_Y_0_4(void) { Block_Y_xx_4(0, W_0y, W_4y, W_8y, W_12y) ; }
static inline void Block_Y_0_5(void) { Block_Y_xx_5(0, W_0y, W_4y, W_8y, W_12y) ; }
static inline void Block_Y_0_6(void) { Block_Y_xx_6(0, W_0y, W_4y, W_8y, W_12y) ; }
static inline void Block_Y_0_7(void) { Block_Y_xx_7(0, W_0y, W_4y, W_8y, W_12y) ; }
static inline void Block_Y_0_8(void) { Block_Y_xx_8(0, W_0y, W_4y, W_8y, W_12y) ; }
static inline void Block_Y_0_9(void) { Block_Y_xx_9(0, W_0y, W_4y, W_8y, W_12y) ; }
static inline void Block_Y_0_10(void){ Block_Y_xx_10(0, W_0y, W_4y, W_8y, W_12y) ; }
static inline void Block_Y_0_11(void){ Block_Y_xx_11(0, W_0y, W_4y, W_8y, W_12y) ; }
static inline void Block_Y_0_12(word64 *w){ Block_Y_xx_12(0, W_0y, W_4y, W_8y, W_12y) ; }

static inline void Block_Y_4_1(void) { Block_Y_xx_1(4, W_4y, W_8y, W_12y, W_0y) ; }
static inline void Block_Y_4_2(void) { Block_Y_xx_2(4, W_4y, W_8y, W_12y, W_0y) ; }
static inline void Block_Y_4_3(void) { Block_Y_xx_3(4, W_4y, W_8y, W_12y, W_0y) ; }
static inline void Block_Y_4_4(void) { Block_Y_xx_4(4, W_4y, W_8y, W_12y, W_0y) ; }
static inline void Block_Y_4_5(void) { Block_Y_xx_5(4, W_4y, W_8y, W_12y, W_0y) ; }
static inline void Block_Y_4_6(void) { Block_Y_xx_6(4, W_4y, W_8y, W_12y, W_0y) ; }
static inline void Block_Y_4_7(void) { Block_Y_xx_7(4, W_4y, W_8y, W_12y, W_0y) ; }
static inline void Block_Y_4_8(void) { Block_Y_xx_8(4, W_4y, W_8y, W_12y, W_0y) ; }
static inline void Block_Y_4_9(void) { Block_Y_xx_9(4, W_4y, W_8y, W_12y, W_0y) ; }
static inline void Block_Y_4_10(void) { Block_Y_xx_10(4, W_4y, W_8y, W_12y, W_0y) ; }
static inline void Block_Y_4_11(void) { Block_Y_xx_11(4, W_4y, W_8y, W_12y, W_0y) ; }
static inline void Block_Y_4_12(word64 *w) { Block_Y_xx_12(4, W_4y, W_8y, W_12y, W_0y) ; }

static inline void Block_Y_8_1(void) { Block_Y_xx_1(8, W_8y, W_12y, W_0y, W_4y) ; }
static inline void Block_Y_8_2(void) { Block_Y_xx_2(8, W_8y, W_12y, W_0y, W_4y) ; }
static inline void Block_Y_8_3(void) { Block_Y_xx_3(8, W_8y, W_12y, W_0y, W_4y) ; }
static inline void Block_Y_8_4(void) { Block_Y_xx_4(8, W_8y, W_12y, W_0y, W_4y) ; }
static inline void Block_Y_8_5(void) { Block_Y_xx_5(8, W_8y, W_12y, W_0y, W_4y) ; }
static inline void Block_Y_8_6(void) { Block_Y_xx_6(8, W_8y, W_12y, W_0y, W_4y) ; }
static inline void Block_Y_8_7(void) { Block_Y_xx_7(8, W_8y, W_12y, W_0y, W_4y) ; }
static inline void Block_Y_8_8(void) { Block_Y_xx_8(8, W_8y, W_12y, W_0y, W_4y) ; }
static inline void Block_Y_8_9(void) { Block_Y_xx_9(8, W_8y, W_12y, W_0y, W_4y) ; }
static inline void Block_Y_8_10(void) { Block_Y_xx_10(8, W_8y, W_12y, W_0y, W_4y) ; }
static inline void Block_Y_8_11(void) { Block_Y_xx_11(8, W_8y, W_12y, W_0y, W_4y) ; }
static inline void Block_Y_8_12(word64 *w) { Block_Y_xx_12(8, W_8y, W_12y, W_0y, W_4y) ; }

static inline void Block_Y_12_1(void) { Block_Y_xx_1(12, W_12y, W_0y, W_4y, W_8y) ; }
static inline void Block_Y_12_2(void) { Block_Y_xx_2(12, W_12y, W_0y, W_4y, W_8y) ; }
static inline void Block_Y_12_3(void) { Block_Y_xx_3(12, W_12y, W_0y, W_4y, W_8y) ; }
static inline void Block_Y_12_4(void) { Block_Y_xx_4(12, W_12y, W_0y, W_4y, W_8y) ; }
static inline void Block_Y_12_5(void) { Block_Y_xx_5(12, W_12y, W_0y, W_4y, W_8y) ; }
static inline void Block_Y_12_6(void) { Block_Y_xx_6(12, W_12y, W_0y, W_4y, W_8y) ; }
static inline void Block_Y_12_7(void) { Block_Y_xx_7(12, W_12y, W_0y, W_4y, W_8y) ; }
static inline void Block_Y_12_8(void) { Block_Y_xx_8(12, W_12y, W_0y, W_4y, W_8y) ; }
static inline void Block_Y_12_9(void) { Block_Y_xx_9(12, W_12y, W_0y, W_4y, W_8y) ; }
static inline void Block_Y_12_10(void) { Block_Y_xx_10(12, W_12y, W_0y, W_4y, W_8y) ; }
static inline void Block_Y_12_11(void) { Block_Y_xx_11(12, W_12y, W_0y, W_4y, W_8y) ; }
static inline void Block_Y_12_12(word64 *w) { Block_Y_xx_12(12, W_12y, W_0y, W_4y, W_8y) ; }


static int Transform_AVX2(Sha512* sha512)
{
    const word64* K = K512;
    word64 w[4] ;
    word32 j /*, k*/;
    word64 T[8];
    /* Copy digest to working vars */
    XMEMCPY(T, sha512->digest, sizeof(T));

    W_from_buff_Y(sha512->buffer) ;
    MOVE_to_MEMy(w,0, W_0y) ; 
    for (j = 0; j < 80; j += 16) {
        Ry_1( 0, w[0]); Block_Y_0_1(); Ry_2( 0, w[0]); Block_Y_0_2(); 
                                       Ry_3( 0, w[0]); Block_Y_0_3(); 
        Ry_1( 1, w[1]); Block_Y_0_4(); Ry_2( 1, w[1]); Block_Y_0_5(); 
                                       Ry_3( 1, w[1]); Block_Y_0_6();  
        Ry_1( 2, w[2]); Block_Y_0_7(); Ry_2( 2, w[2]); Block_Y_0_8(); 
                                       Ry_3( 2, w[2]); Block_Y_0_9();
        Ry_1( 3, w[3]); Block_Y_0_10();Ry_2( 3, w[3]); Block_Y_0_11();
                                       Ry_3( 3, w[3]); Block_Y_0_12(w);
        
        Ry_1( 4, w[0]); Block_Y_4_1(); Ry_2( 4, w[0]); Block_Y_4_2(); 
                                       Ry_3( 4, w[0]); Block_Y_4_3(); 
        Ry_1( 5, w[1]); Block_Y_4_4(); Ry_2( 5, w[1]); Block_Y_4_5(); 
                                       Ry_3( 5, w[1]); Block_Y_4_6();
        Ry_1( 6, w[2]); Block_Y_4_7(); Ry_2( 6, w[2]); Block_Y_4_8(); 
                                       Ry_3( 6, w[2]); Block_Y_4_9();
        Ry_1( 7, w[3]); Block_Y_4_10(); Ry_2( 7, w[3]);Block_Y_4_11(); 
                                        Ry_3( 7, w[3]);Block_Y_4_12(w);  
        
        Ry_1( 8, w[0]); Block_Y_8_1(); Ry_2( 8, w[0]); Block_Y_8_2(); 
                                       Ry_3( 8, w[0]); Block_Y_8_3();
        Ry_1( 9, w[1]); Block_Y_8_4(); Ry_2( 9, w[1]); Block_Y_8_5(); 
                                       Ry_3( 9, w[1]); Block_Y_8_6();
        Ry_1(10, w[2]); Block_Y_8_7(); Ry_2(10, w[2]); Block_Y_8_8(); 
                                       Ry_3(10, w[2]); Block_Y_8_9(); 
        Ry_1(11, w[3]); Block_Y_8_10();Ry_2(11, w[3]); Block_Y_8_11();
                                       Ry_3(11, w[3]); Block_Y_8_12(w);
                 
        Ry_1(12, w[0]); Block_Y_12_1(); Ry_2(12, w[0]); Block_Y_12_2(); 
                                        Ry_3(12, w[0]); Block_Y_12_3();
        Ry_1(13, w[1]); Block_Y_12_4(); Ry_2(13, w[1]); Block_Y_12_5(); 
                                        Ry_3(13, w[1]); Block_Y_12_6(); 
        Ry_1(14, w[2]); Block_Y_12_7(); Ry_2(14, w[2]); Block_Y_12_8(); 
                                        Ry_3(14, w[2]); Block_Y_12_9();
        Ry_1(15, w[3]); Block_Y_12_10();Ry_2(15, w[3]); Block_Y_12_11();
                                        Ry_3(15, w[3]);Block_Y_12_12(w);
    }
 
    /* Add the working vars back into digest */

    sha512->digest[0] += a(0);
    sha512->digest[1] += b(0);
    sha512->digest[2] += c(0);
    sha512->digest[3] += d(0);
    sha512->digest[4] += e(0);
    sha512->digest[5] += f(0);
    sha512->digest[6] += g(0);
    sha512->digest[7] += h(0);

    /* Wipe variables */
    #if !defined(HAVE_INTEL_AVX1)&&!defined(HAVE_INTEL_AVX2)
    XMEMSET(W, 0, sizeof(word64) * 16);
    #endif
    XMEMSET(T, 0, sizeof(T));

    return 0;
}

#endif


#ifdef WOLFSSL_SHA384

#if defined(HAVE_INTEL_AVX1) ||  defined(HAVE_INTEL_AVX2) 

#if defined(HAVE_INTEL_AVX1)
static int Transform384_AVX1(Sha384 *sha384) ;
#endif
#if defined(HAVE_INTEL_AVX2)
static int Transform384_AVX2(Sha384 *sha384) ; 
#endif

#if defined(HAVE_INTEL_AVX1) &&  defined(HAVE_INTEL_AVX2) &&defined(HAVE_INTEL_RORX)
static int Transform384_AVX1_RORX(Sha384 *sha384) ; 
#endif

static int _Transform384(Sha384 *sha384) ; 
static int (*Transform384_p)(Sha384* sha384) = _Transform384 ;

#define Transform384(sha384) (*Transform384_p)(sha384)
static void set_Transform384(void) {
     if(set_cpuid_flags(CHECK_SHA384))return ;

#if defined(HAVE_INTEL_AVX1) && !defined(HAVE_INTEL_AVX2)
     Transform384_p = ((IS_INTEL_AVX1) ? Transform384_AVX1 : _Transform384) ;
#elif defined(HAVE_INTEL_AVX2)
     #if defined(HAVE_INTEL_AVX1) && defined(HAVE_INTEL_RORX)
     if(IS_INTEL_AVX2 && IS_INTEL_BMI2) { Transform384_p = Transform384_AVX1_RORX ; return ; }
     #endif
     if(IS_INTEL_AVX2) { Transform384_p = Transform384_AVX2 ; return ; }
     #if defined(HAVE_INTEL_AVX1)
     Transform384_p = ((IS_INTEL_AVX1) ? Transform384_AVX1 : _Transform384) ;
     #endif
#else
     Transform384_p = ((IS_INTEL_AVX1) ? Transform384_AVX1 : _Transform384) ;
#endif
}

#else
   #define Transform384(sha512) _Transform384(sha512)
#endif

int wc_InitSha384(Sha384* sha384)
{
    sha384->digest[0] = W64LIT(0xcbbb9d5dc1059ed8);
    sha384->digest[1] = W64LIT(0x629a292a367cd507);
    sha384->digest[2] = W64LIT(0x9159015a3070dd17);
    sha384->digest[3] = W64LIT(0x152fecd8f70e5939);
    sha384->digest[4] = W64LIT(0x67332667ffc00b31);
    sha384->digest[5] = W64LIT(0x8eb44a8768581511);
    sha384->digest[6] = W64LIT(0xdb0c2e0d64f98fa7);
    sha384->digest[7] = W64LIT(0x47b5481dbefa4fa4);

    sha384->buffLen = 0;
    sha384->loLen   = 0;
    sha384->hiLen   = 0;

#if defined(HAVE_INTEL_AVX1)|| defined(HAVE_INTEL_AVX2)
    set_Transform384() ;
#endif
    
    return 0;
}

static int _Transform384(Sha384* sha384)
{
    const word64* K = K512;

    word32 j;
    word64 T[8];

#ifdef WOLFSSL_SMALL_STACK
    word64* W;

    W = (word64*) XMALLOC(sizeof(word64) * 16, NULL, DYNAMIC_TYPE_TMP_BUFFER);
    if (W == NULL)
        return MEMORY_E;
#else
    word64 W[16];
#endif

    /* Copy digest to working vars */
    XMEMCPY(T, sha384->digest, sizeof(T));

#ifdef USE_SLOW_SHA2
    /* over twice as small, but 50% slower */
    /* 80 operations, not unrolled */
    for (j = 0; j < 80; j += 16) {
        int m;
        for (m = 0; m < 16; m++) {  /* braces needed for macros {} */
            R2(m);
        }
    }
#else
    /* 80 operations, partially loop unrolled */
    for (j = 0; j < 80; j += 16) {
        R2( 0); R2( 1); R2( 2); R2( 3);
        R2( 4); R2( 5); R2( 6); R2( 7);
        R2( 8); R2( 9); R2(10); R2(11);
        R2(12); R2(13); R2(14); R2(15);
    }
#endif /* USE_SLOW_SHA2 */

    /* Add the working vars back into digest */

    sha384->digest[0] += a(0);
    sha384->digest[1] += b(0);
    sha384->digest[2] += c(0);
    sha384->digest[3] += d(0);
    sha384->digest[4] += e(0);
    sha384->digest[5] += f(0);
    sha384->digest[6] += g(0);
    sha384->digest[7] += h(0);

    /* Wipe variables */
    XMEMSET(W, 0, sizeof(word64) * 16);
    XMEMSET(T, 0, sizeof(T));

#ifdef WOLFSSL_SMALL_STACK
    XFREE(W, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif

    return 0;
}

static INLINE void AddLength384(Sha384* sha384, word32 len)
{
    word32 tmp = sha384->loLen;
    if ( (sha384->loLen += len) < tmp)
        sha384->hiLen++;                       /* carry low to high */
}

int wc_Sha384Update(Sha384* sha384, const byte* data, word32 len)
{
    /* do block size increments */
    byte* local = (byte*)sha384->buffer;
	
    SAVE_XMM_YMM ; /* for Intel AVX */
    
    while (len) {
        word32 add = min(len, SHA384_BLOCK_SIZE - sha384->buffLen);
        XMEMCPY(&local[sha384->buffLen], data, add);

        sha384->buffLen += add;
        data         += add;
        len          -= add;

        if (sha384->buffLen == SHA384_BLOCK_SIZE) {
            int ret;

            #if defined(LITTLE_ENDIAN_ORDER)
                #if defined(HAVE_INTEL_AVX1) || defined(HAVE_INTEL_AVX2)
                if(!IS_INTEL_AVX1 && !IS_INTEL_AVX2) 
                #endif
                    ByteReverseWords64(sha384->buffer, sha384->buffer,
                                   SHA384_BLOCK_SIZE);
            #endif
            ret = Transform384(sha384);
            if (ret != 0)
                return ret;

            AddLength384(sha384, SHA384_BLOCK_SIZE);
            sha384->buffLen = 0;
        }
    }
    return 0;
}


int wc_Sha384Final(Sha384* sha384, byte* hash)
{
    byte* local = (byte*)sha384->buffer;
    int ret;

    SAVE_XMM_YMM ; /* for Intel AVX */
    AddLength384(sha384, sha384->buffLen);              /* before adding pads */

    local[sha384->buffLen++] = 0x80;  /* add 1 */

    /* pad with zeros */
    if (sha384->buffLen > SHA384_PAD_SIZE) {
        XMEMSET(&local[sha384->buffLen], 0, SHA384_BLOCK_SIZE -sha384->buffLen);
        sha384->buffLen += SHA384_BLOCK_SIZE - sha384->buffLen;

        #if defined(LITTLE_ENDIAN_ORDER)
            #if defined(HAVE_INTEL_AVX1) || defined(HAVE_INTEL_AVX2)
            if(!IS_INTEL_AVX1 && !IS_INTEL_AVX2) 
            #endif
                 ByteReverseWords64(sha384->buffer, sha384->buffer,
                               SHA384_BLOCK_SIZE);
        #endif
        ret = Transform384(sha384);
        if (ret !=  0)
            return ret;

        sha384->buffLen = 0;
    }
    XMEMSET(&local[sha384->buffLen], 0, SHA384_PAD_SIZE - sha384->buffLen);
   
    /* put lengths in bits */
    sha384->hiLen = (sha384->loLen >> (8*sizeof(sha384->loLen) - 3)) + 
                 (sha384->hiLen << 3);
    sha384->loLen = sha384->loLen << 3;

    /* store lengths */
    #if defined(LITTLE_ENDIAN_ORDER)
        #if defined(HAVE_INTEL_AVX1) || defined(HAVE_INTEL_AVX2)
        if(!IS_INTEL_AVX1 && !IS_INTEL_AVX2) 
        #endif
             ByteReverseWords64(sha384->buffer, sha384->buffer,
                           SHA384_BLOCK_SIZE);
    #endif
    /* ! length ordering dependent on digest endian type ! */
    sha384->buffer[SHA384_BLOCK_SIZE / sizeof(word64) - 2] = sha384->hiLen;
    sha384->buffer[SHA384_BLOCK_SIZE / sizeof(word64) - 1] = sha384->loLen;
    #if defined(HAVE_INTEL_AVX1) || defined(HAVE_INTEL_AVX2)
    if(IS_INTEL_AVX1 || IS_INTEL_AVX2)
        ByteReverseWords64(&(sha384->buffer[SHA384_BLOCK_SIZE / sizeof(word64) - 2]),
                           &(sha384->buffer[SHA384_BLOCK_SIZE / sizeof(word64) - 2]),
                           SHA384_BLOCK_SIZE - SHA384_PAD_SIZE);
    #endif
    ret = Transform384(sha384);
    if (ret != 0)
        return ret;

    #ifdef LITTLE_ENDIAN_ORDER
        ByteReverseWords64(sha384->digest, sha384->digest, SHA384_DIGEST_SIZE);
    #endif
    XMEMCPY(hash, sha384->digest, SHA384_DIGEST_SIZE);

    return wc_InitSha384(sha384);  /* reset state */
}


int wc_Sha384Hash(const byte* data, word32 len, byte* hash)
{
    int ret = 0;
#ifdef WOLFSSL_SMALL_STACK
    Sha384* sha384;
#else
    Sha384 sha384[1];
#endif

#ifdef WOLFSSL_SMALL_STACK
    sha384 = (Sha384*)XMALLOC(sizeof(Sha384), NULL, DYNAMIC_TYPE_TMP_BUFFER);
    if (sha384 == NULL)
        return MEMORY_E;
#endif

    if ((ret = wc_InitSha384(sha384)) != 0) {
        WOLFSSL_MSG("InitSha384 failed");
    }
    else if ((ret = wc_Sha384Update(sha384, data, len)) != 0) {
        WOLFSSL_MSG("Sha384Update failed");
    }
    else if ((ret = wc_Sha384Final(sha384, hash)) != 0) {
        WOLFSSL_MSG("Sha384Final failed");
    }

#ifdef WOLFSSL_SMALL_STACK
    XFREE(sha384, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif

    return ret;
}

#if defined(HAVE_INTEL_AVX1)
 
static int Transform384_AVX1(Sha384* sha384)
{
    const word64* K = K512;
    word64 W_X[16+4];
    word32 j;
    word64 T[8];

    /* Copy digest to working vars */
    XMEMCPY(T, sha384->digest, sizeof(T));
    W_from_buff(W_X, sha384->buffer) ;
    for (j = 0; j < 80; j += 16) {
        Rx_1( 0); Block_0_1(W_X); Rx_2( 0); Block_0_2(W_X); Rx_3( 0); Block_0_3(); 
        Rx_1( 1); Block_0_4(); Rx_2( 1); Block_0_5(); Rx_3( 1); Block_0_6(W_X); 
        Rx_1( 2); Block_0_7(W_X); Rx_2( 2); Block_0_8(W_X); Rx_3( 2); Block_0_9();
        Rx_1( 3); Block_0_10();Rx_2( 3); Block_0_11();Rx_3( 3); Block_0_12(W_X);   
        
        Rx_1( 4); Block_4_1(W_X); Rx_2( 4); Block_4_2(W_X); Rx_3( 4); Block_4_3(); 
        Rx_1( 5); Block_4_4(); Rx_2( 5); Block_4_5(); Rx_3( 5); Block_4_6(W_X); 
        Rx_1( 6); Block_4_7(W_X); Rx_2( 6); Block_4_8(W_X); Rx_3( 6); Block_4_9();
        Rx_1( 7); Block_4_10();Rx_2( 7); Block_4_11();Rx_3( 7); Block_4_12(W_X);   
        
        Rx_1( 8); Block_8_1(W_X); Rx_2( 8); Block_8_2(W_X); Rx_3( 8); Block_8_3(); 
        Rx_1( 9); Block_8_4(); Rx_2( 9); Block_8_5(); Rx_3( 9); Block_8_6(W_X); 
        Rx_1(10); Block_8_7(W_X); Rx_2(10); Block_8_8(W_X); Rx_3(10); Block_8_9();
        Rx_1(11); Block_8_10();Rx_2(11); Block_8_11();Rx_3(11); Block_8_12(W_X);   
        
        Rx_1(12); Block_12_1(W_X); Rx_2(12); Block_12_2(W_X); Rx_3(12); Block_12_3(); 
        Rx_1(13); Block_12_4(); Rx_2(13); Block_12_5(); Rx_3(13); Block_12_6(W_X); 
        Rx_1(14); Block_12_7(W_X); Rx_2(14); Block_12_8(W_X); Rx_3(14); Block_12_9();
        Rx_1(15); Block_12_10();Rx_2(15); Block_12_11();Rx_3(15); Block_12_12(W_X);     
    }

    /* Add the working vars back into digest */

    sha384->digest[0] += a(0);
    sha384->digest[1] += b(0);
    sha384->digest[2] += c(0);
    sha384->digest[3] += d(0);
    sha384->digest[4] += e(0);
    sha384->digest[5] += f(0);
    sha384->digest[6] += g(0);
    sha384->digest[7] += h(0);

    /* Wipe variables */
    #if !defined(HAVE_INTEL_AVX1)&&!defined(HAVE_INTEL_AVX2)
    XMEMSET(W, 0, sizeof(word64) * 16);
    #endif
    XMEMSET(T, 0, sizeof(T));

    return 0;
}

#endif

#if defined(HAVE_INTEL_AVX1) && defined(HAVE_INTEL_AVX2) && defined(HAVE_INTEL_RORX)
static int Transform384_AVX1_RORX(Sha384* sha384)
{
    const word64* K = K512;
    word64 W_X[16+4];
    word32 j;
    word64 T[8];

    /* Copy digest to working vars */
    XMEMCPY(T, sha384->digest, sizeof(T));

    W_from_buff(W_X, sha384->buffer) ;
    for (j = 0; j < 80; j += 16) {
        Rx_RORX_1( 0); Block_0_1(W_X); Rx_RORX_2( 0); 
            Block_0_2(W_X); Rx_RORX_3( 0); Block_0_3(); 
        Rx_RORX_1( 1); Block_0_4(); Rx_RORX_2( 1); 
            Block_0_5(); Rx_RORX_3( 1); Block_0_6(W_X); 
        Rx_RORX_1( 2); Block_0_7(W_X); Rx_RORX_2( 2); 
            Block_0_8(W_X); Rx_RORX_3( 2); Block_0_9();
        Rx_RORX_1( 3); Block_0_10();Rx_RORX_2( 3); 
            Block_0_11();Rx_RORX_3( 3); Block_0_12(W_X);   
        
        Rx_RORX_1( 4); Block_4_1(W_X); Rx_RORX_2( 4); 
            Block_4_2(W_X); Rx_RORX_3( 4); Block_4_3(); 
        Rx_RORX_1( 5); Block_4_4(); Rx_RORX_2( 5); 
            Block_4_5(); Rx_RORX_3( 5); Block_4_6(W_X); 
        Rx_RORX_1( 6); Block_4_7(W_X); Rx_RORX_2( 6); 
            Block_4_8(W_X); Rx_RORX_3( 6); Block_4_9();
        Rx_RORX_1( 7); Block_4_10();Rx_RORX_2( 7); 
            Block_4_11();Rx_RORX_3( 7); Block_4_12(W_X);   
        
        Rx_RORX_1( 8); Block_8_1(W_X); Rx_RORX_2( 8); 
            Block_8_2(W_X); Rx_RORX_3( 8); Block_8_3(); 
        Rx_RORX_1( 9); Block_8_4(); Rx_RORX_2( 9); 
            Block_8_5(); Rx_RORX_3( 9); Block_8_6(W_X); 
        Rx_RORX_1(10); Block_8_7(W_X); Rx_RORX_2(10); 
            Block_8_8(W_X); Rx_RORX_3(10); Block_8_9();
        Rx_RORX_1(11); Block_8_10();Rx_RORX_2(11); 
            Block_8_11();Rx_RORX_3(11); Block_8_12(W_X);   
        
        Rx_RORX_1(12); Block_12_1(W_X); Rx_RORX_2(12);
            Block_12_2(W_X); Rx_RORX_3(12); Block_12_3(); 
        Rx_RORX_1(13); Block_12_4(); Rx_RORX_2(13); 
            Block_12_5(); Rx_RORX_3(13); Block_12_6(W_X); 
        Rx_RORX_1(14); Block_12_7(W_X); Rx_RORX_2(14); 
            Block_12_8(W_X); Rx_RORX_3(14); Block_12_9();
        Rx_RORX_1(15); Block_12_10();Rx_RORX_2(15); 
            Block_12_11();Rx_RORX_3(15); Block_12_12(W_X);     
    }

    /* Add the working vars back into digest */

    sha384->digest[0] += a(0);
    sha384->digest[1] += b(0);
    sha384->digest[2] += c(0);
    sha384->digest[3] += d(0);
    sha384->digest[4] += e(0);
    sha384->digest[5] += f(0);
    sha384->digest[6] += g(0);
    sha384->digest[7] += h(0);

    /* Wipe variables */
    #if !defined(HAVE_INTEL_AVX1)&&!defined(HAVE_INTEL_AVX2)
    XMEMSET(W, 0, sizeof(word64) * 16);
    #endif
    XMEMSET(T, 0, sizeof(T));

    return 0;
}
#endif

#if defined(HAVE_INTEL_AVX2)

static int Transform384_AVX2(Sha384* sha384)
{
    const word64* K = K512;
    word64 w[4] ;
    word32 j;
    word64 T[8];

    /* Copy digest to working vars */
    XMEMCPY(T, sha384->digest, sizeof(T));

    /* over twice as small, but 50% slower */
    /* 80 operations, not unrolled */

    W_from_buff_Y(sha384->buffer) ;

    MOVE_to_MEMy(w,0, W_0y) ;
    for (j = 0; j < 80; j += 16) {
        Ry_1( 0, w[0]); Block_Y_0_1(); Ry_2( 0, w[0]); 
            Block_Y_0_2(); Ry_3( 0, w[0]); Block_Y_0_3(); 
        Ry_1( 1, w[1]); Block_Y_0_4(); Ry_2( 1, w[1]); 
            Block_Y_0_5(); Ry_3( 1, w[1]); Block_Y_0_6();  
        Ry_1( 2, w[2]); Block_Y_0_7(); Ry_2( 2, w[2]); 
            Block_Y_0_8(); Ry_3( 2, w[2]); Block_Y_0_9();
        Ry_1( 3, w[3]); Block_Y_0_10();Ry_2( 3, w[3]); 
            Block_Y_0_11();Ry_3( 3, w[3]); Block_Y_0_12(w);
        
        Ry_1( 4, w[0]); Block_Y_4_1(); Ry_2( 4, w[0]); 
            Block_Y_4_2(); Ry_3( 4, w[0]); Block_Y_4_3(); 
        Ry_1( 5, w[1]); Block_Y_4_4(); Ry_2( 5, w[1]);   
            Block_Y_4_5(); Ry_3( 5, w[1]); Block_Y_4_6();
        Ry_1( 6, w[2]); Block_Y_4_7(); Ry_2( 6, w[2]); 
            Block_Y_4_8(); Ry_3( 6, w[2]); Block_Y_4_9();
        Ry_1( 7, w[3]); Block_Y_4_10(); Ry_2( 7, w[3]);
            Block_Y_4_11(); Ry_3( 7, w[3]);Block_Y_4_12(w);  
        
        Ry_1( 8, w[0]); Block_Y_8_1(); Ry_2( 8, w[0]); 
            Block_Y_8_2(); Ry_3( 8, w[0]); Block_Y_8_3();
        Ry_1( 9, w[1]); Block_Y_8_4(); Ry_2( 9, w[1]);
            Block_Y_8_5(); Ry_3( 9, w[1]); Block_Y_8_6();
        Ry_1(10, w[2]); Block_Y_8_7(); Ry_2(10, w[2]); 
            Block_Y_8_8(); Ry_3(10, w[2]); Block_Y_8_9(); 
        Ry_1(11, w[3]); Block_Y_8_10();Ry_2(11, w[3]); 
           Block_Y_8_11();Ry_3(11, w[3]); Block_Y_8_12(w);
                 
        Ry_1(12, w[0]); Block_Y_12_1(); Ry_2(12, w[0]); 
            Block_Y_12_2(); Ry_3(12, w[0]); Block_Y_12_3();
        Ry_1(13, w[1]); Block_Y_12_4(); Ry_2(13, w[1]); 
            Block_Y_12_5(); Ry_3(13, w[1]); Block_Y_12_6(); 
        Ry_1(14, w[2]); Block_Y_12_7(); Ry_2(14, w[2]); 
            Block_Y_12_8(); Ry_3(14, w[2]); Block_Y_12_9();
        Ry_1(15, w[3]); Block_Y_12_10();Ry_2(15, w[3]); 
            Block_Y_12_11();Ry_3(15, w[3]); Block_Y_12_12(w);
    }

    /* Add the working vars back into digest */

    sha384->digest[0] += a(0);
    sha384->digest[1] += b(0);
    sha384->digest[2] += c(0);
    sha384->digest[3] += d(0);
    sha384->digest[4] += e(0);
    sha384->digest[5] += f(0);
    sha384->digest[6] += g(0);
    sha384->digest[7] += h(0);

    /* Wipe variables */
    XMEMSET(T, 0, sizeof(T));

    return 0;
}

#endif

#endif /* WOLFSSL_SHA384 */

#endif /* HAVE_FIPS */

#endif /* WOLFSSL_SHA512 */

