/* asm.c
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

#ifdef HAVE_CONFIG_H
    #include <config.h>
#endif

/*
 * Based on public domain TomsFastMath 0.10 by Tom St Denis, tomstdenis@iahu.ca,
 * http://math.libtomcrypt.com
 */


/******************************************************************/
/* fp_montgomery_reduce.c asm or generic */
#if defined(TFM_X86) && !defined(TFM_SSE2) 
/* x86-32 code */

#define MONT_START 
#define MONT_FINI
#define LOOP_END
#define LOOP_START \
   mu = c[x] * mp

#define INNERMUL                                          \
asm(                                                      \
   "movl %5,%%eax \n\t"                                   \
   "mull %4       \n\t"                                   \
   "addl %1,%%eax \n\t"                                   \
   "adcl $0,%%edx \n\t"                                   \
   "addl %%eax,%0 \n\t"                                   \
   "adcl $0,%%edx \n\t"                                   \
   "movl %%edx,%1 \n\t"                                   \
:"=g"(_c[LO]), "=r"(cy)                                   \
:"0"(_c[LO]), "1"(cy), "g"(mu), "g"(*tmpm++)              \
: "%eax", "%edx", "%cc")

#define PROPCARRY                           \
asm(                                        \
   "addl   %1,%0    \n\t"                   \
   "setb   %%al     \n\t"                   \
   "movzbl %%al,%1 \n\t"                    \
:"=g"(_c[LO]), "=r"(cy)                     \
:"0"(_c[LO]), "1"(cy)                       \
: "%eax", "%cc")

/******************************************************************/
#elif defined(TFM_X86_64)
/* x86-64 code */

#define MONT_START 
#define MONT_FINI
#define LOOP_END
#define LOOP_START \
   mu = c[x] * mp

#define INNERMUL                                          \
asm(                                                      \
   "movq %5,%%rax \n\t"                                   \
   "mulq %4       \n\t"                                   \
   "addq %1,%%rax \n\t"                                   \
   "adcq $0,%%rdx \n\t"                                   \
   "addq %%rax,%0 \n\t"                                   \
   "adcq $0,%%rdx \n\t"                                   \
   "movq %%rdx,%1 \n\t"                                   \
:"=g"(_c[LO]), "=r"(cy)                                   \
:"0"(_c[LO]), "1"(cy), "r"(mu), "r"(*tmpm++)              \
: "%rax", "%rdx", "%cc")

#define INNERMUL8 \
 asm(                  \
 "movq 0(%5),%%rax    \n\t"  \
 "movq 0(%2),%%r10    \n\t"  \
 "movq 0x8(%5),%%r11  \n\t"  \
 "mulq %4             \n\t"  \
 "addq %%r10,%%rax    \n\t"  \
 "adcq $0,%%rdx       \n\t"  \
 "movq 0x8(%2),%%r10  \n\t"  \
 "addq %3,%%rax       \n\t"  \
 "adcq $0,%%rdx       \n\t"  \
 "movq %%rax,0(%0)    \n\t"  \
 "movq %%rdx,%1       \n\t"  \
 \
 "movq %%r11,%%rax    \n\t"  \
 "movq 0x10(%5),%%r11 \n\t"  \
 "mulq %4             \n\t"  \
 "addq %%r10,%%rax    \n\t"  \
 "adcq $0,%%rdx       \n\t"  \
 "movq 0x10(%2),%%r10 \n\t"  \
 "addq %3,%%rax       \n\t"  \
 "adcq $0,%%rdx       \n\t"  \
 "movq %%rax,0x8(%0)  \n\t"  \
 "movq %%rdx,%1       \n\t"  \
 \
 "movq %%r11,%%rax    \n\t"  \
 "movq 0x18(%5),%%r11 \n\t"  \
 "mulq %4             \n\t"  \
 "addq %%r10,%%rax    \n\t"  \
 "adcq $0,%%rdx       \n\t"  \
 "movq 0x18(%2),%%r10 \n\t"  \
 "addq %3,%%rax       \n\t"  \
 "adcq $0,%%rdx       \n\t"  \
 "movq %%rax,0x10(%0) \n\t"  \
 "movq %%rdx,%1       \n\t"  \
 \
 "movq %%r11,%%rax    \n\t"  \
 "movq 0x20(%5),%%r11 \n\t"  \
 "mulq %4             \n\t"  \
 "addq %%r10,%%rax    \n\t"  \
 "adcq $0,%%rdx       \n\t"  \
 "movq 0x20(%2),%%r10 \n\t"  \
 "addq %3,%%rax       \n\t"  \
 "adcq $0,%%rdx       \n\t"  \
 "movq %%rax,0x18(%0) \n\t"  \
 "movq %%rdx,%1       \n\t"  \
 \
 "movq %%r11,%%rax    \n\t"  \
 "movq 0x28(%5),%%r11 \n\t"  \
 "mulq %4             \n\t"  \
 "addq %%r10,%%rax    \n\t"  \
 "adcq $0,%%rdx       \n\t"  \
 "movq 0x28(%2),%%r10 \n\t"  \
 "addq %3,%%rax       \n\t"  \
 "adcq $0,%%rdx       \n\t"  \
 "movq %%rax,0x20(%0) \n\t"  \
 "movq %%rdx,%1       \n\t"  \
 \
 "movq %%r11,%%rax    \n\t"  \
 "movq 0x30(%5),%%r11 \n\t"  \
 "mulq %4             \n\t"  \
 "addq %%r10,%%rax    \n\t"  \
 "adcq $0,%%rdx       \n\t"  \
 "movq 0x30(%2),%%r10 \n\t"  \
 "addq %3,%%rax       \n\t"  \
 "adcq $0,%%rdx       \n\t"  \
 "movq %%rax,0x28(%0) \n\t"  \
 "movq %%rdx,%1       \n\t"  \
 \
 "movq %%r11,%%rax    \n\t"  \
 "movq 0x38(%5),%%r11 \n\t"  \
 "mulq %4             \n\t"  \
 "addq %%r10,%%rax    \n\t"  \
 "adcq $0,%%rdx       \n\t"  \
 "movq 0x38(%2),%%r10 \n\t"  \
 "addq %3,%%rax       \n\t"  \
 "adcq $0,%%rdx       \n\t"  \
 "movq %%rax,0x30(%0) \n\t"  \
 "movq %%rdx,%1       \n\t"  \
 \
 "movq %%r11,%%rax    \n\t"  \
 "mulq %4             \n\t"  \
 "addq %%r10,%%rax    \n\t"  \
 "adcq $0,%%rdx       \n\t"  \
 "addq %3,%%rax       \n\t"  \
 "adcq $0,%%rdx       \n\t"  \
 "movq %%rax,0x38(%0) \n\t"  \
 "movq %%rdx,%1       \n\t"  \
 \
:"=r"(_c), "=r"(cy)                    \
: "0"(_c),  "1"(cy), "g"(mu), "r"(tmpm)\
: "%rax", "%rdx", "%r10", "%r11", "%cc")


#define PROPCARRY                           \
asm(                                        \
   "addq   %1,%0    \n\t"                   \
   "setb   %%al     \n\t"                   \
   "movzbq %%al,%1 \n\t"                    \
:"=g"(_c[LO]), "=r"(cy)                     \
:"0"(_c[LO]), "1"(cy)                       \
: "%rax", "%cc")

/******************************************************************/
#elif defined(TFM_SSE2)  
/* SSE2 code (assumes 32-bit fp_digits) */
/* XMM register assignments:
 * xmm0  *tmpm++, then Mu * (*tmpm++)
 * xmm1  c[x], then Mu
 * xmm2  mp
 * xmm3  cy
 * xmm4  _c[LO]
 */

#define MONT_START \
   asm("movd %0,%%mm2"::"g"(mp))

#define MONT_FINI \
   asm("emms")

#define LOOP_START          \
asm(                        \
"movd %0,%%mm1        \n\t" \
"pxor %%mm3,%%mm3     \n\t" \
"pmuludq %%mm2,%%mm1  \n\t" \
:: "g"(c[x]))

/* pmuludq on mmx registers does a 32x32->64 multiply. */
#define INNERMUL               \
asm(                           \
   "movd %1,%%mm4        \n\t" \
   "movd %2,%%mm0        \n\t" \
   "paddq %%mm4,%%mm3    \n\t" \
   "pmuludq %%mm1,%%mm0  \n\t" \
   "paddq %%mm0,%%mm3    \n\t" \
   "movd %%mm3,%0        \n\t" \
   "psrlq $32, %%mm3     \n\t" \
:"=g"(_c[LO]) : "0"(_c[LO]), "g"(*tmpm++) );

#define INNERMUL8 \
asm(                           \
   "movd 0(%1),%%mm4     \n\t" \
   "movd 0(%2),%%mm0     \n\t" \
   "paddq %%mm4,%%mm3    \n\t" \
   "pmuludq %%mm1,%%mm0  \n\t" \
   "movd 4(%2),%%mm5     \n\t" \
   "paddq %%mm0,%%mm3    \n\t" \
   "movd 4(%1),%%mm6     \n\t" \
   "movd %%mm3,0(%0)     \n\t" \
   "psrlq $32, %%mm3     \n\t" \
\
   "paddq %%mm6,%%mm3    \n\t" \
   "pmuludq %%mm1,%%mm5  \n\t" \
   "movd 8(%2),%%mm6     \n\t" \
   "paddq %%mm5,%%mm3    \n\t" \
   "movd 8(%1),%%mm7     \n\t" \
   "movd %%mm3,4(%0)     \n\t" \
   "psrlq $32, %%mm3     \n\t" \
\
   "paddq %%mm7,%%mm3    \n\t" \
   "pmuludq %%mm1,%%mm6  \n\t" \
   "movd 12(%2),%%mm7    \n\t" \
   "paddq %%mm6,%%mm3    \n\t" \
   "movd 12(%1),%%mm5     \n\t" \
   "movd %%mm3,8(%0)     \n\t" \
   "psrlq $32, %%mm3     \n\t" \
\
   "paddq %%mm5,%%mm3    \n\t" \
   "pmuludq %%mm1,%%mm7  \n\t" \
   "movd 16(%2),%%mm5    \n\t" \
   "paddq %%mm7,%%mm3    \n\t" \
   "movd 16(%1),%%mm6    \n\t" \
   "movd %%mm3,12(%0)    \n\t" \
   "psrlq $32, %%mm3     \n\t" \
\
   "paddq %%mm6,%%mm3    \n\t" \
   "pmuludq %%mm1,%%mm5  \n\t" \
   "movd 20(%2),%%mm6    \n\t" \
   "paddq %%mm5,%%mm3    \n\t" \
   "movd 20(%1),%%mm7    \n\t" \
   "movd %%mm3,16(%0)    \n\t" \
   "psrlq $32, %%mm3     \n\t" \
\
   "paddq %%mm7,%%mm3    \n\t" \
   "pmuludq %%mm1,%%mm6  \n\t" \
   "movd 24(%2),%%mm7    \n\t" \
   "paddq %%mm6,%%mm3    \n\t" \
   "movd 24(%1),%%mm5     \n\t" \
   "movd %%mm3,20(%0)    \n\t" \
   "psrlq $32, %%mm3     \n\t" \
\
   "paddq %%mm5,%%mm3    \n\t" \
   "pmuludq %%mm1,%%mm7  \n\t" \
   "movd 28(%2),%%mm5    \n\t" \
   "paddq %%mm7,%%mm3    \n\t" \
   "movd 28(%1),%%mm6    \n\t" \
   "movd %%mm3,24(%0)    \n\t" \
   "psrlq $32, %%mm3     \n\t" \
\
   "paddq %%mm6,%%mm3    \n\t" \
   "pmuludq %%mm1,%%mm5  \n\t" \
   "paddq %%mm5,%%mm3    \n\t" \
   "movd %%mm3,28(%0)    \n\t" \
   "psrlq $32, %%mm3     \n\t" \
:"=r"(_c) : "0"(_c), "r"(tmpm) );

/* TAO switched tmpm from "g" to "r" after gcc tried to index the indexed stack
   pointer */

#define LOOP_END \
asm( "movd %%mm3,%0  \n" :"=r"(cy))

#define PROPCARRY                           \
asm(                                        \
   "addl   %1,%0    \n\t"                   \
   "setb   %%al     \n\t"                   \
   "movzbl %%al,%1 \n\t"                    \
:"=g"(_c[LO]), "=r"(cy)                     \
:"0"(_c[LO]), "1"(cy)                       \
: "%eax", "%cc")

/******************************************************************/
#elif defined(TFM_ARM)
   /* ARMv4 code */

#define MONT_START 
#define MONT_FINI
#define LOOP_END
#define LOOP_START \
   mu = c[x] * mp

#define INNERMUL                    \
asm(                                \
    " LDR    r0,%1            \n\t" \
    " ADDS   r0,r0,%0         \n\t" \
    " MOVCS  %0,#1            \n\t" \
    " MOVCC  %0,#0            \n\t" \
    " UMLAL  r0,%0,%3,%4      \n\t" \
    " STR    r0,%1            \n\t" \
:"=r"(cy),"=m"(_c[0]):"0"(cy),"r"(mu),"r"(*tmpm++),"1"(_c[0]):"r0","%cc");

#define PROPCARRY                  \
asm(                               \
    " LDR   r0,%1            \n\t" \
    " ADDS  r0,r0,%0         \n\t" \
    " STR   r0,%1            \n\t" \
    " MOVCS %0,#1            \n\t" \
    " MOVCC %0,#0            \n\t" \
:"=r"(cy),"=m"(_c[0]):"0"(cy),"1"(_c[0]):"r0","%cc");

#elif defined(TFM_PPC32)

/* PPC32 */
#define MONT_START 
#define MONT_FINI
#define LOOP_END
#define LOOP_START \
   mu = c[x] * mp

#define INNERMUL                     \
asm(                                 \
   " mullw    16,%3,%4       \n\t"   \
   " mulhwu   17,%3,%4       \n\t"   \
   " addc     16,16,%0       \n\t"   \
   " addze    17,17          \n\t"   \
   " lwz      18,%1          \n\t"   \
   " addc     16,16,18       \n\t"   \
   " addze    %0,17          \n\t"   \
   " stw      16,%1          \n\t"   \
:"=r"(cy),"=m"(_c[0]):"0"(cy),"r"(mu),"r"(tmpm[0]),"1"(_c[0]):"16", "17", "18","%cc"); ++tmpm;

#define PROPCARRY                    \
asm(                                 \
   " lwz      16,%1         \n\t"    \
   " addc     16,16,%0      \n\t"    \
   " stw      16,%1         \n\t"    \
   " xor      %0,%0,%0      \n\t"    \
   " addze    %0,%0         \n\t"    \
:"=r"(cy),"=m"(_c[0]):"0"(cy),"1"(_c[0]):"16","%cc");

#elif defined(TFM_PPC64)

/* PPC64 */
#define MONT_START 
#define MONT_FINI
#define LOOP_END
#define LOOP_START \
   mu = c[x] * mp

#define INNERMUL                     \
asm(                                 \
   " mulld    16,%3,%4       \n\t"   \
   " mulhdu   17,%3,%4       \n\t"   \
   " addc     16,16,%0       \n\t"   \
   " addze    17,17          \n\t"   \
   " ldx      18,0,%1        \n\t"   \
   " addc     16,16,18       \n\t"   \
   " addze    %0,17          \n\t"   \
   " sdx      16,0,%1        \n\t"   \
:"=r"(cy),"=m"(_c[0]):"0"(cy),"r"(mu),"r"(tmpm[0]),"1"(_c[0]):"16", "17", "18","%cc"); ++tmpm;

#define PROPCARRY                    \
asm(                                 \
   " ldx      16,0,%1       \n\t"    \
   " addc     16,16,%0      \n\t"    \
   " sdx      16,0,%1       \n\t"    \
   " xor      %0,%0,%0      \n\t"    \
   " addze    %0,%0         \n\t"    \
:"=r"(cy),"=m"(_c[0]):"0"(cy),"1"(_c[0]):"16","%cc");

/******************************************************************/

#elif defined(TFM_AVR32)

/* AVR32 */
#define MONT_START 
#define MONT_FINI
#define LOOP_END
#define LOOP_START \
   mu = c[x] * mp

#define INNERMUL                    \
asm(                                \
    " ld.w   r2,%1            \n\t" \
    " add    r2,%0            \n\t" \
    " eor    r3,r3            \n\t" \
    " acr    r3               \n\t" \
    " macu.d r2,%3,%4         \n\t" \
    " st.w   %1,r2            \n\t" \
    " mov    %0,r3            \n\t" \
:"=r"(cy),"=r"(_c):"0"(cy),"r"(mu),"r"(*tmpm++),"1"(_c):"r2","r3");

#define PROPCARRY                    \
asm(                                 \
   " ld.w     r2,%1         \n\t"    \
   " add      r2,%0         \n\t"    \
   " st.w     %1,r2         \n\t"    \
   " eor      %0,%0         \n\t"    \
   " acr      %0            \n\t"    \
:"=r"(cy),"=r"(&_c[0]):"0"(cy),"1"(&_c[0]):"r2","%cc");

#else

/* ISO C code */
#define MONT_START 
#define MONT_FINI
#define LOOP_END
#define LOOP_START \
   mu = c[x] * mp

#define INNERMUL                                      \
   do { fp_word t;                                    \
   _c[0] = t  = ((fp_word)_c[0] + (fp_word)cy) +      \
                (((fp_word)mu) * ((fp_word)*tmpm++)); \
   cy = (t >> DIGIT_BIT);                             \
   } while (0)

#define PROPCARRY \
   do { fp_digit t = _c[0] += cy; cy = (t < cy); } while (0)

#endif
/******************************************************************/


#define LO  0
/* end fp_montogomery_reduce.c asm */


/* start fp_sqr_comba.c asm */
#if defined(TFM_X86)

/* x86-32 optimized */

#define COMBA_START

#define CLEAR_CARRY \
   c0 = c1 = c2 = 0;

#define COMBA_STORE(x) \
   x = c0;

#define COMBA_STORE2(x) \
   x = c1;

#define CARRY_FORWARD \
   do { c0 = c1; c1 = c2; c2 = 0; } while (0);

#define COMBA_FINI

#define SQRADD(i, j)                                      \
asm(                                            \
     "movl  %6,%%eax     \n\t"                            \
     "mull  %%eax        \n\t"                            \
     "addl  %%eax,%0     \n\t"                            \
     "adcl  %%edx,%1     \n\t"                            \
     "adcl  $0,%2        \n\t"                            \
     :"=r"(c0), "=r"(c1), "=r"(c2): "0"(c0), "1"(c1), "2"(c2), "m"(i) :"%eax","%edx","%cc");

#define SQRADD2(i, j)                                     \
asm(                                            \
     "movl  %6,%%eax     \n\t"                            \
     "mull  %7           \n\t"                            \
     "addl  %%eax,%0     \n\t"                            \
     "adcl  %%edx,%1     \n\t"                            \
     "adcl  $0,%2        \n\t"                            \
     "addl  %%eax,%0     \n\t"                            \
     "adcl  %%edx,%1     \n\t"                            \
     "adcl  $0,%2        \n\t"                            \
     :"=r"(c0), "=r"(c1), "=r"(c2): "0"(c0), "1"(c1), "2"(c2), "m"(i), "m"(j)  :"%eax","%edx", "%cc");

#define SQRADDSC(i, j)                                    \
asm(                                                     \
     "movl  %3,%%eax     \n\t"                            \
     "mull  %4           \n\t"                            \
     "movl  %%eax,%0     \n\t"                            \
     "movl  %%edx,%1     \n\t"                            \
     "xorl  %2,%2        \n\t"                            \
     :"=r"(sc0), "=r"(sc1), "=r"(sc2): "g"(i), "g"(j) :"%eax","%edx","%cc");

/* TAO removed sc0,1,2 as input to remove warning so %6,%7 become %3,%4 */

#define SQRADDAC(i, j)                                    \
asm(                                                     \
     "movl  %6,%%eax     \n\t"                            \
     "mull  %7           \n\t"                            \
     "addl  %%eax,%0     \n\t"                            \
     "adcl  %%edx,%1     \n\t"                            \
     "adcl  $0,%2        \n\t"                            \
     :"=r"(sc0), "=r"(sc1), "=r"(sc2): "0"(sc0), "1"(sc1), "2"(sc2), "g"(i), "g"(j) :"%eax","%edx","%cc");

#define SQRADDDB                                          \
asm(                                                     \
     "addl %6,%0         \n\t"                            \
     "adcl %7,%1         \n\t"                            \
     "adcl %8,%2         \n\t"                            \
     "addl %6,%0         \n\t"                            \
     "adcl %7,%1         \n\t"                            \
     "adcl %8,%2         \n\t"                            \
     :"=r"(c0), "=r"(c1), "=r"(c2) : "0"(c0), "1"(c1), "2"(c2), "r"(sc0), "r"(sc1), "r"(sc2) : "%cc");

#elif defined(TFM_X86_64)
/* x86-64 optimized */

#define COMBA_START

#define CLEAR_CARRY \
   c0 = c1 = c2 = 0;

#define COMBA_STORE(x) \
   x = c0;

#define COMBA_STORE2(x) \
   x = c1;

#define CARRY_FORWARD \
   do { c0 = c1; c1 = c2; c2 = 0; } while (0);

#define COMBA_FINI

#define SQRADD(i, j)                                      \
asm(                                                     \
     "movq  %6,%%rax     \n\t"                            \
     "mulq  %%rax        \n\t"                            \
     "addq  %%rax,%0     \n\t"                            \
     "adcq  %%rdx,%1     \n\t"                            \
     "adcq  $0,%2        \n\t"                            \
     :"=r"(c0), "=r"(c1), "=r"(c2): "0"(c0), "1"(c1), "2"(c2), "g"(i) :"%rax","%rdx","%cc");

#define SQRADD2(i, j)                                     \
asm(                                                     \
     "movq  %6,%%rax     \n\t"                            \
     "mulq  %7           \n\t"                            \
     "addq  %%rax,%0     \n\t"                            \
     "adcq  %%rdx,%1     \n\t"                            \
     "adcq  $0,%2        \n\t"                            \
     "addq  %%rax,%0     \n\t"                            \
     "adcq  %%rdx,%1     \n\t"                            \
     "adcq  $0,%2        \n\t"                            \
     :"=r"(c0), "=r"(c1), "=r"(c2): "0"(c0), "1"(c1), "2"(c2), "g"(i), "g"(j)  :"%rax","%rdx","%cc");

#define SQRADDSC(i, j)                                    \
asm(                                                     \
     "movq  %3,%%rax     \n\t"                            \
     "mulq  %4           \n\t"                            \
     "movq  %%rax,%0     \n\t"                            \
     "movq  %%rdx,%1     \n\t"                            \
     "xorq  %2,%2        \n\t"                            \
     :"=r"(sc0), "=r"(sc1), "=r"(sc2): "g"(i), "g"(j) :"%rax","%rdx","%cc");

/* TAO removed sc0,1,2 as input to remove warning so %6,%7 become %3,%4 */

#define SQRADDAC(i, j)                                                         \
asm(                                                     \
     "movq  %6,%%rax     \n\t"                            \
     "mulq  %7           \n\t"                            \
     "addq  %%rax,%0     \n\t"                            \
     "adcq  %%rdx,%1     \n\t"                            \
     "adcq  $0,%2        \n\t"                            \
     :"=r"(sc0), "=r"(sc1), "=r"(sc2): "0"(sc0), "1"(sc1), "2"(sc2), "g"(i), "g"(j) :"%rax","%rdx","%cc");

#define SQRADDDB                                          \
asm(                                                     \
     "addq %6,%0         \n\t"                            \
     "adcq %7,%1         \n\t"                            \
     "adcq %8,%2         \n\t"                            \
     "addq %6,%0         \n\t"                            \
     "adcq %7,%1         \n\t"                            \
     "adcq %8,%2         \n\t"                            \
     :"=r"(c0), "=r"(c1), "=r"(c2) : "0"(c0), "1"(c1), "2"(c2), "r"(sc0), "r"(sc1), "r"(sc2) : "%cc");

#elif defined(TFM_SSE2)

/* SSE2 Optimized */
#define COMBA_START

#define CLEAR_CARRY \
   c0 = c1 = c2 = 0;

#define COMBA_STORE(x) \
   x = c0;

#define COMBA_STORE2(x) \
   x = c1;

#define CARRY_FORWARD \
   do { c0 = c1; c1 = c2; c2 = 0; } while (0);

#define COMBA_FINI \
   asm("emms");

#define SQRADD(i, j)                                      \
asm(                                            \
     "movd  %6,%%mm0     \n\t"                            \
     "pmuludq %%mm0,%%mm0\n\t"                            \
     "movd  %%mm0,%%eax  \n\t"                            \
     "psrlq $32,%%mm0    \n\t"                            \
     "addl  %%eax,%0     \n\t"                            \
     "movd  %%mm0,%%eax  \n\t"                            \
     "adcl  %%eax,%1     \n\t"                            \
     "adcl  $0,%2        \n\t"                            \
     :"=r"(c0), "=r"(c1), "=r"(c2): "0"(c0), "1"(c1), "2"(c2), "m"(i) :"%eax","%cc");

#define SQRADD2(i, j)                                     \
asm(                                            \
     "movd  %6,%%mm0     \n\t"                            \
     "movd  %7,%%mm1     \n\t"                            \
     "pmuludq %%mm1,%%mm0\n\t"                            \
     "movd  %%mm0,%%eax  \n\t"                            \
     "psrlq $32,%%mm0    \n\t"                            \
     "movd  %%mm0,%%edx  \n\t"                            \
     "addl  %%eax,%0     \n\t"                            \
     "adcl  %%edx,%1     \n\t"                            \
     "adcl  $0,%2        \n\t"                            \
     "addl  %%eax,%0     \n\t"                            \
     "adcl  %%edx,%1     \n\t"                            \
     "adcl  $0,%2        \n\t"                            \
     :"=r"(c0), "=r"(c1), "=r"(c2): "0"(c0), "1"(c1), "2"(c2), "m"(i), "m"(j)  :"%eax","%edx","%cc");

#define SQRADDSC(i, j)                                                         \
asm(                                            \
     "movd  %3,%%mm0     \n\t"                            \
     "movd  %4,%%mm1     \n\t"                            \
     "pmuludq %%mm1,%%mm0\n\t"                            \
     "movd  %%mm0,%0     \n\t"                            \
     "psrlq $32,%%mm0    \n\t"                            \
     "movd  %%mm0,%1     \n\t"                            \
     "xorl  %2,%2        \n\t"                            \
     :"=r"(sc0), "=r"(sc1), "=r"(sc2): "m"(i), "m"(j));

/* TAO removed sc0,1,2 as input to remove warning so %6,%7 become %3,%4 */

#define SQRADDAC(i, j)                                                         \
asm(                                            \
     "movd  %6,%%mm0     \n\t"                            \
     "movd  %7,%%mm1     \n\t"                            \
     "pmuludq %%mm1,%%mm0\n\t"                            \
     "movd  %%mm0,%%eax  \n\t"                            \
     "psrlq $32,%%mm0    \n\t"                            \
     "movd  %%mm0,%%edx  \n\t"                            \
     "addl  %%eax,%0     \n\t"                            \
     "adcl  %%edx,%1     \n\t"                            \
     "adcl  $0,%2        \n\t"                            \
     :"=r"(sc0), "=r"(sc1), "=r"(sc2): "0"(sc0), "1"(sc1), "2"(sc2), "m"(i), "m"(j)  :"%eax","%edx","%cc");

#define SQRADDDB                                          \
asm(                                                     \
     "addl %6,%0         \n\t"                            \
     "adcl %7,%1         \n\t"                            \
     "adcl %8,%2         \n\t"                            \
     "addl %6,%0         \n\t"                            \
     "adcl %7,%1         \n\t"                            \
     "adcl %8,%2         \n\t"                            \
     :"=r"(c0), "=r"(c1), "=r"(c2) : "0"(c0), "1"(c1), "2"(c2), "r"(sc0), "r"(sc1), "r"(sc2) : "%cc");

#elif defined(TFM_ARM)

/* ARM code */

#define COMBA_START

#define CLEAR_CARRY \
   c0 = c1 = c2 = 0;

#define COMBA_STORE(x) \
   x = c0;

#define COMBA_STORE2(x) \
   x = c1;

#define CARRY_FORWARD \
   do { c0 = c1; c1 = c2; c2 = 0; } while (0);

#define COMBA_FINI

/* multiplies point i and j, updates carry "c1" and digit c2 */
#define SQRADD(i, j)                                             \
asm(                                                             \
"  UMULL  r0,r1,%6,%6              \n\t"                         \
"  ADDS   %0,%0,r0                 \n\t"                         \
"  ADCS   %1,%1,r1                 \n\t"                         \
"  ADC    %2,%2,#0                 \n\t"                         \
:"=r"(c0), "=r"(c1), "=r"(c2) : "0"(c0), "1"(c1), "2"(c2), "r"(i) : "r0", "r1", "%cc");
	
/* for squaring some of the terms are doubled... */
#define SQRADD2(i, j)                                            \
asm(                                                             \
"  UMULL  r0,r1,%6,%7              \n\t"                         \
"  ADDS   %0,%0,r0                 \n\t"                         \
"  ADCS   %1,%1,r1                 \n\t"                         \
"  ADC    %2,%2,#0                 \n\t"                         \
"  ADDS   %0,%0,r0                 \n\t"                         \
"  ADCS   %1,%1,r1                 \n\t"                         \
"  ADC    %2,%2,#0                 \n\t"                         \
:"=r"(c0), "=r"(c1), "=r"(c2) : "0"(c0), "1"(c1), "2"(c2), "r"(i), "r"(j) : "r0", "r1", "%cc");

#define SQRADDSC(i, j)                                           \
asm(                                                             \
"  UMULL  %0,%1,%6,%7              \n\t"                         \
"  SUB    %2,%2,%2                 \n\t"                         \
:"=r"(sc0), "=r"(sc1), "=r"(sc2) : "0"(sc0), "1"(sc1), "2"(sc2), "r"(i), "r"(j) : "%cc");

#define SQRADDAC(i, j)                                           \
asm(                                                             \
"  UMULL  r0,r1,%6,%7              \n\t"                         \
"  ADDS   %0,%0,r0                 \n\t"                         \
"  ADCS   %1,%1,r1                 \n\t"                         \
"  ADC    %2,%2,#0                 \n\t"                         \
:"=r"(sc0), "=r"(sc1), "=r"(sc2) : "0"(sc0), "1"(sc1), "2"(sc2), "r"(i), "r"(j) : "r0", "r1", "%cc");

#define SQRADDDB                                                 \
asm(                                                             \
"  ADDS  %0,%0,%3                     \n\t"                      \
"  ADCS  %1,%1,%4                     \n\t"                      \
"  ADC   %2,%2,%5                     \n\t"                      \
"  ADDS  %0,%0,%3                     \n\t"                      \
"  ADCS  %1,%1,%4                     \n\t"                      \
"  ADC   %2,%2,%5                     \n\t"                      \
:"=r"(c0), "=r"(c1), "=r"(c2) : "r"(sc0), "r"(sc1), "r"(sc2), "0"(c0), "1"(c1), "2"(c2) : "%cc");

#elif defined(TFM_PPC32)

/* PPC32 */

#define COMBA_START

#define CLEAR_CARRY \
   c0 = c1 = c2 = 0;

#define COMBA_STORE(x) \
   x = c0;

#define COMBA_STORE2(x) \
   x = c1;

#define CARRY_FORWARD \
   do { c0 = c1; c1 = c2; c2 = 0; } while (0);

#define COMBA_FINI

/* multiplies point i and j, updates carry "c1" and digit c2 */
#define SQRADD(i, j)             \
asm(                             \
   " mullw  16,%6,%6       \n\t" \
   " addc   %0,%0,16       \n\t" \
   " mulhwu 16,%6,%6       \n\t" \
   " adde   %1,%1,16       \n\t" \
   " addze  %2,%2          \n\t" \
:"=r"(c0), "=r"(c1), "=r"(c2):"0"(c0), "1"(c1), "2"(c2), "r"(i):"16","%cc");

/* for squaring some of the terms are doubled... */
#define SQRADD2(i, j)            \
asm(                             \
   " mullw  16,%6,%7       \n\t" \
   " mulhwu 17,%6,%7       \n\t" \
   " addc   %0,%0,16       \n\t" \
   " adde   %1,%1,17       \n\t" \
   " addze  %2,%2          \n\t" \
   " addc   %0,%0,16       \n\t" \
   " adde   %1,%1,17       \n\t" \
   " addze  %2,%2          \n\t" \
:"=r"(c0), "=r"(c1), "=r"(c2):"0"(c0), "1"(c1), "2"(c2), "r"(i), "r"(j):"16", "17","%cc");

#define SQRADDSC(i, j)            \
asm(                              \
   " mullw  %0,%6,%7        \n\t" \
   " mulhwu %1,%6,%7        \n\t" \
   " xor    %2,%2,%2        \n\t" \
:"=r"(sc0), "=r"(sc1), "=r"(sc2):"0"(sc0), "1"(sc1), "2"(sc2), "r"(i),"r"(j) : "%cc");

#define SQRADDAC(i, j)           \
asm(                             \
   " mullw  16,%6,%7       \n\t" \
   " addc   %0,%0,16       \n\t" \
   " mulhwu 16,%6,%7       \n\t" \
   " adde   %1,%1,16       \n\t" \
   " addze  %2,%2          \n\t" \
:"=r"(sc0), "=r"(sc1), "=r"(sc2):"0"(sc0), "1"(sc1), "2"(sc2), "r"(i), "r"(j):"16", "%cc");

#define SQRADDDB                  \
asm(                              \
   " addc   %0,%0,%3        \n\t" \
   " adde   %1,%1,%4        \n\t" \
   " adde   %2,%2,%5        \n\t" \
   " addc   %0,%0,%3        \n\t" \
   " adde   %1,%1,%4        \n\t" \
   " adde   %2,%2,%5        \n\t" \
:"=r"(c0), "=r"(c1), "=r"(c2) : "r"(sc0), "r"(sc1), "r"(sc2), "0"(c0), "1"(c1), "2"(c2) : "%cc");

#elif defined(TFM_PPC64)
/* PPC64 */

#define COMBA_START

#define CLEAR_CARRY \
   c0 = c1 = c2 = 0;

#define COMBA_STORE(x) \
   x = c0;

#define COMBA_STORE2(x) \
   x = c1;

#define CARRY_FORWARD \
   do { c0 = c1; c1 = c2; c2 = 0; } while (0);

#define COMBA_FINI

/* multiplies point i and j, updates carry "c1" and digit c2 */
#define SQRADD(i, j)             \
asm(                             \
   " mulld  16,%6,%6       \n\t" \
   " addc   %0,%0,16       \n\t" \
   " mulhdu 16,%6,%6       \n\t" \
   " adde   %1,%1,16       \n\t" \
   " addze  %2,%2          \n\t" \
:"=r"(c0), "=r"(c1), "=r"(c2):"0"(c0), "1"(c1), "2"(c2), "r"(i):"16","%cc");

/* for squaring some of the terms are doubled... */
#define SQRADD2(i, j)            \
asm(                             \
   " mulld  16,%6,%7       \n\t" \
   " mulhdu 17,%6,%7       \n\t" \
   " addc   %0,%0,16       \n\t" \
   " adde   %1,%1,17       \n\t" \
   " addze  %2,%2          \n\t" \
   " addc   %0,%0,16       \n\t" \
   " adde   %1,%1,17       \n\t" \
   " addze  %2,%2          \n\t" \
:"=r"(c0), "=r"(c1), "=r"(c2):"0"(c0), "1"(c1), "2"(c2), "r"(i), "r"(j):"16", "17","%cc");

#define SQRADDSC(i, j)            \
asm(                              \
   " mulld  %0,%6,%7        \n\t" \
   " mulhdu %1,%6,%7        \n\t" \
   " xor    %2,%2,%2        \n\t" \
:"=r"(sc0), "=r"(sc1), "=r"(sc2):"0"(sc0), "1"(sc1), "2"(sc2), "r"(i),"r"(j) : "%cc");

#define SQRADDAC(i, j)           \
asm(                             \
   " mulld  16,%6,%7       \n\t" \
   " addc   %0,%0,16       \n\t" \
   " mulhdu 16,%6,%7       \n\t" \
   " adde   %1,%1,16       \n\t" \
   " addze  %2,%2          \n\t" \
:"=r"(sc0), "=r"(sc1), "=r"(sc2):"0"(sc0), "1"(sc1), "2"(sc2), "r"(i), "r"(j):"16", "%cc");

#define SQRADDDB                  \
asm(                              \
   " addc   %0,%0,%3        \n\t" \
   " adde   %1,%1,%4        \n\t" \
   " adde   %2,%2,%5        \n\t" \
   " addc   %0,%0,%3        \n\t" \
   " adde   %1,%1,%4        \n\t" \
   " adde   %2,%2,%5        \n\t" \
:"=r"(c0), "=r"(c1), "=r"(c2) : "r"(sc0), "r"(sc1), "r"(sc2), "0"(c0), "1"(c1), "2"(c2) : "%cc");


#elif defined(TFM_AVR32)

/* AVR32 */

#define COMBA_START

#define CLEAR_CARRY \
   c0 = c1 = c2 = 0;

#define COMBA_STORE(x) \
   x = c0;

#define COMBA_STORE2(x) \
   x = c1;

#define CARRY_FORWARD \
   do { c0 = c1; c1 = c2; c2 = 0; } while (0);

#define COMBA_FINI

/* multiplies point i and j, updates carry "c1" and digit c2 */
#define SQRADD(i, j)             \
asm(                             \
   " mulu.d r2,%6,%6       \n\t" \
   " add    %0,%0,r2       \n\t" \
   " adc    %1,%1,r3       \n\t" \
   " acr    %2             \n\t" \
:"=r"(c0), "=r"(c1), "=r"(c2):"0"(c0), "1"(c1), "2"(c2), "r"(i):"r2","r3");

/* for squaring some of the terms are doubled... */
#define SQRADD2(i, j)            \
asm(                             \
   " mulu.d r2,%6,%7       \n\t" \
   " add    %0,%0,r2       \n\t" \
   " adc    %1,%1,r3       \n\t" \
   " acr    %2,            \n\t" \
   " add    %0,%0,r2       \n\t" \
   " adc    %1,%1,r3       \n\t" \
   " acr    %2,            \n\t" \
:"=r"(c0), "=r"(c1), "=r"(c2):"0"(c0), "1"(c1), "2"(c2), "r"(i), "r"(j):"r2", "r3");

#define SQRADDSC(i, j)            \
asm(                              \
   " mulu.d r2,%6,%7        \n\t" \
   " mov    %0,r2           \n\t" \
   " mov    %1,r3           \n\t" \
   " eor    %2,%2           \n\t" \
:"=r"(sc0), "=r"(sc1), "=r"(sc2):"0"(sc0), "1"(sc1), "2"(sc2), "r"(i),"r"(j) : "r2", "r3");

#define SQRADDAC(i, j)           \
asm(                             \
   " mulu.d r2,%6,%7       \n\t" \
   " add    %0,%0,r2       \n\t" \
   " adc    %1,%1,r3       \n\t" \
   " acr    %2             \n\t" \
:"=r"(sc0), "=r"(sc1), "=r"(sc2):"0"(sc0), "1"(sc1), "2"(sc2), "r"(i), "r"(j):"r2", "r3");

#define SQRADDDB                  \
asm(                              \
   " add    %0,%0,%3        \n\t" \
   " adc    %1,%1,%4        \n\t" \
   " adc    %2,%2,%5        \n\t" \
   " add    %0,%0,%3        \n\t" \
   " adc    %1,%1,%4        \n\t" \
   " adc    %2,%2,%5        \n\t" \
:"=r"(c0), "=r"(c1), "=r"(c2) : "r"(sc0), "r"(sc1), "r"(sc2), "0"(c0), "1"(c1), "2"(c2) : "%cc");


#else

#define TFM_ISO

/* ISO C portable code */

#define COMBA_START

#define CLEAR_CARRY \
   c0 = c1 = c2 = 0;

#define COMBA_STORE(x) \
   x = c0;

#define COMBA_STORE2(x) \
   x = c1;

#define CARRY_FORWARD \
   do { c0 = c1; c1 = c2; c2 = 0; } while (0);

#define COMBA_FINI

/* multiplies point i and j, updates carry "c1" and digit c2 */
#define SQRADD(i, j)                                 \
   do { fp_word t;                                   \
   t = c0 + ((fp_word)i) * ((fp_word)j);  c0 = t;    \
   t = c1 + (t >> DIGIT_BIT);             c1 = t; c2 += t >> DIGIT_BIT; \
   } while (0);
  

/* for squaring some of the terms are doubled... */
#define SQRADD2(i, j)                                                 \
   do { fp_word t;                                                    \
   t  = ((fp_word)i) * ((fp_word)j);                                  \
   tt = (fp_word)c0 + t;                 c0 = tt;                              \
   tt = (fp_word)c1 + (tt >> DIGIT_BIT); c1 = tt; c2 += tt >> DIGIT_BIT;       \
   tt = (fp_word)c0 + t;                 c0 = tt;                              \
   tt = (fp_word)c1 + (tt >> DIGIT_BIT); c1 = tt; c2 += tt >> DIGIT_BIT;       \
   } while (0);

#define SQRADDSC(i, j)                                                         \
   do { fp_word t;                                                             \
      t =  ((fp_word)i) * ((fp_word)j);                                        \
      sc0 = (fp_digit)t; sc1 = (t >> DIGIT_BIT); sc2 = 0;                      \
   } while (0);

#define SQRADDAC(i, j)                                                         \
   do { fp_word t;                                                             \
   t = sc0 + ((fp_word)i) * ((fp_word)j);  sc0 = t;                            \
   t = sc1 + (t >> DIGIT_BIT);             sc1 = t; sc2 += t >> DIGIT_BIT;     \
   } while (0);

#define SQRADDDB                                                               \
   do { fp_word t;                                                             \
   t = ((fp_word)sc0) + ((fp_word)sc0) + c0; c0 = t;                                                 \
   t = ((fp_word)sc1) + ((fp_word)sc1) + c1 + (t >> DIGIT_BIT); c1 = t;                              \
   c2 = c2 + ((fp_word)sc2) + ((fp_word)sc2) + (t >> DIGIT_BIT);                                     \
   } while (0);

#endif

#ifdef TFM_SMALL_SET
#include "fp_sqr_comba_small_set.i"
#include "fp_sqr_comba_3.i"
#include "fp_sqr_comba_4.i"
#include "fp_sqr_comba_6.i"
#include "fp_sqr_comba_7.i"
#include "fp_sqr_comba_8.i"
#include "fp_sqr_comba_9.i"
#include "fp_sqr_comba_12.i"
#include "fp_sqr_comba_17.i"
#include "fp_sqr_comba_20.i"
#include "fp_sqr_comba_24.i"
#include "fp_sqr_comba_28.i"
#include "fp_sqr_comba_32.i"
#include "fp_sqr_comba_48.i"
#include "fp_sqr_comba_64.i"
#endif
/* end fp_sqr_comba.c asm */

/* start fp_mul_comba.c asm */
/* these are the combas.  Worship them. */
#if defined(TFM_X86)
/* Generic x86 optimized code */

/* anything you need at the start */
#define COMBA_START

/* clear the chaining variables */
#define COMBA_CLEAR \
   c0 = c1 = c2 = 0;

/* forward the carry to the next digit */
#define COMBA_FORWARD \
   do { c0 = c1; c1 = c2; c2 = 0; } while (0);

/* store the first sum */
#define COMBA_STORE(x) \
   x = c0;

/* store the second sum [carry] */
#define COMBA_STORE2(x) \
   x = c1;

/* anything you need at the end */
#define COMBA_FINI

/* this should multiply i and j  */
#define MULADD(i, j)                                      \
asm(                                                      \
     "movl  %6,%%eax     \n\t"                            \
     "mull  %7           \n\t"                            \
     "addl  %%eax,%0     \n\t"                            \
     "adcl  %%edx,%1     \n\t"                            \
     "adcl  $0,%2        \n\t"                            \
     :"=r"(c0), "=r"(c1), "=r"(c2): "0"(c0), "1"(c1), "2"(c2), "m"(i), "m"(j)  :"%eax","%edx","%cc");

#elif defined(TFM_X86_64)
/* x86-64 optimized */

/* anything you need at the start */
#define COMBA_START

/* clear the chaining variables */
#define COMBA_CLEAR \
   c0 = c1 = c2 = 0;

/* forward the carry to the next digit */
#define COMBA_FORWARD \
   do { c0 = c1; c1 = c2; c2 = 0; } while (0);

/* store the first sum */
#define COMBA_STORE(x) \
   x = c0;

/* store the second sum [carry] */
#define COMBA_STORE2(x) \
   x = c1;

/* anything you need at the end */
#define COMBA_FINI

/* this should multiply i and j  */
#define MULADD(i, j)                                      \
asm  (                                                    \
     "movq  %6,%%rax     \n\t"                            \
     "mulq  %7           \n\t"                            \
     "addq  %%rax,%0     \n\t"                            \
     "adcq  %%rdx,%1     \n\t"                            \
     "adcq  $0,%2        \n\t"                            \
     :"=r"(c0), "=r"(c1), "=r"(c2): "0"(c0), "1"(c1), "2"(c2), "g"(i), "g"(j)  :"%rax","%rdx","%cc");

#elif defined(TFM_SSE2)
/* use SSE2 optimizations */

/* anything you need at the start */
#define COMBA_START

/* clear the chaining variables */
#define COMBA_CLEAR \
   c0 = c1 = c2 = 0;

/* forward the carry to the next digit */
#define COMBA_FORWARD \
   do { c0 = c1; c1 = c2; c2 = 0; } while (0);

/* store the first sum */
#define COMBA_STORE(x) \
   x = c0;

/* store the second sum [carry] */
#define COMBA_STORE2(x) \
   x = c1;

/* anything you need at the end */
#define COMBA_FINI \
   asm("emms");

/* this should multiply i and j  */
#define MULADD(i, j)                                     \
asm(                                                     \
    "movd  %6,%%mm0     \n\t"                            \
    "movd  %7,%%mm1     \n\t"                            \
    "pmuludq %%mm1,%%mm0\n\t"                            \
    "movd  %%mm0,%%eax  \n\t"                            \
    "psrlq $32,%%mm0    \n\t"                            \
    "addl  %%eax,%0     \n\t"                            \
    "movd  %%mm0,%%eax  \n\t"                            \
    "adcl  %%eax,%1     \n\t"                            \
    "adcl  $0,%2        \n\t"                            \
    :"=r"(c0), "=r"(c1), "=r"(c2): "0"(c0), "1"(c1), "2"(c2), "m"(i), "m"(j)  :"%eax","%cc");

#elif defined(TFM_ARM)
/* ARM code */

#define COMBA_START 

#define COMBA_CLEAR \
   c0 = c1 = c2 = 0;

#define COMBA_FORWARD \
   do { c0 = c1; c1 = c2; c2 = 0; } while (0);

#define COMBA_STORE(x) \
   x = c0;

#define COMBA_STORE2(x) \
   x = c1;

#define COMBA_FINI

#define MULADD(i, j)                                          \
asm(                                                          \
"  UMULL  r0,r1,%6,%7           \n\t"                         \
"  ADDS   %0,%0,r0              \n\t"                         \
"  ADCS   %1,%1,r1              \n\t"                         \
"  ADC    %2,%2,#0              \n\t"                         \
:"=r"(c0), "=r"(c1), "=r"(c2) : "0"(c0), "1"(c1), "2"(c2), "r"(i), "r"(j) : "r0", "r1", "%cc");

#elif defined(TFM_PPC32)
/* For 32-bit PPC */

#define COMBA_START

#define COMBA_CLEAR \
   c0 = c1 = c2 = 0;

#define COMBA_FORWARD \
   do { c0 = c1; c1 = c2; c2 = 0; } while (0);

#define COMBA_STORE(x) \
   x = c0;

#define COMBA_STORE2(x) \
   x = c1;

#define COMBA_FINI 
   
/* untested: will mulhwu change the flags?  Docs say no */
#define MULADD(i, j)              \
asm(                              \
   " mullw  16,%6,%7       \n\t" \
   " addc   %0,%0,16       \n\t" \
   " mulhwu 16,%6,%7       \n\t" \
   " adde   %1,%1,16       \n\t" \
   " addze  %2,%2          \n\t" \
:"=r"(c0), "=r"(c1), "=r"(c2):"0"(c0), "1"(c1), "2"(c2), "r"(i), "r"(j):"16");

#elif defined(TFM_PPC64)
/* For 64-bit PPC */

#define COMBA_START

#define COMBA_CLEAR \
   c0 = c1 = c2 = 0;

#define COMBA_FORWARD \
   do { c0 = c1; c1 = c2; c2 = 0; } while (0);

#define COMBA_STORE(x) \
   x = c0;

#define COMBA_STORE2(x) \
   x = c1;

#define COMBA_FINI 
   
/* untested: will mulhwu change the flags?  Docs say no */
#define MULADD(i, j)              \
asm(                              \
   " mulld  16,%6,%7       \n\t" \
   " addc   %0,%0,16       \n\t" \
   " mulhdu 16,%6,%7       \n\t" \
   " adde   %1,%1,16       \n\t" \
   " addze  %2,%2          \n\t" \
:"=r"(c0), "=r"(c1), "=r"(c2):"0"(c0), "1"(c1), "2"(c2), "r"(i), "r"(j):"16");

#elif defined(TFM_AVR32)

/* ISO C code */

#define COMBA_START

#define COMBA_CLEAR \
   c0 = c1 = c2 = 0;

#define COMBA_FORWARD \
   do { c0 = c1; c1 = c2; c2 = 0; } while (0);

#define COMBA_STORE(x) \
   x = c0;

#define COMBA_STORE2(x) \
   x = c1;

#define COMBA_FINI 
   
#define MULADD(i, j)             \
asm(                             \
   " mulu.d r2,%6,%7        \n\t"\
   " add    %0,r2           \n\t"\
   " adc    %1,%1,r3        \n\t"\
   " acr    %2              \n\t"\
:"=r"(c0), "=r"(c1), "=r"(c2):"0"(c0), "1"(c1), "2"(c2), "r"(i), "r"(j):"r2","r3");

#else
/* ISO C code */

#define COMBA_START

#define COMBA_CLEAR \
   c0 = c1 = c2 = 0;

#define COMBA_FORWARD \
   do { c0 = c1; c1 = c2; c2 = 0; } while (0);

#define COMBA_STORE(x) \
   x = c0;

#define COMBA_STORE2(x) \
   x = c1;

#define COMBA_FINI 
   
#define MULADD(i, j)                                                              \
   do { fp_word t;                                                                \
   t = (fp_word)c0 + ((fp_word)i) * ((fp_word)j); c0 = t;                         \
   t = (fp_word)c1 + (t >> DIGIT_BIT);            c1 = t; c2 += t >> DIGIT_BIT;   \
   } while (0);

#endif


#ifdef TFM_SMALL_SET
#include "fp_mul_comba_small_set.i"
#include "fp_mul_comba_3.i"
#include "fp_mul_comba_4.i"
#include "fp_mul_comba_6.i"
#include "fp_mul_comba_7.i"
#include "fp_mul_comba_8.i"
#include "fp_mul_comba_9.i"
#include "fp_mul_comba_12.i"
#include "fp_mul_comba_17.i"
#include "fp_mul_comba_20.i"
#include "fp_mul_comba_24.i"
#include "fp_mul_comba_28.i"
#include "fp_mul_comba_32.i"
#include "fp_mul_comba_48.i"
#include "fp_mul_comba_64.i"
#endif

/* end fp_mul_comba.c asm */

