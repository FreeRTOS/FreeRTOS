/* integer.h
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

/*
 * Based on public domain LibTomMath 0.38 by Tom St Denis, tomstdenis@iahu.ca,
 * http://math.libtomcrypt.com
 */


#ifndef CTAO_CRYPT_INTEGER_H
#define CTAO_CRYPT_INTEGER_H

/* may optionally use fast math instead, not yet supported on all platforms and
   may not be faster on all
*/
#include <cyassl/ctaocrypt/types.h>       /* will set MP_xxBIT if not default */
#ifdef USE_FAST_MATH
    #include <cyassl/ctaocrypt/tfm.h>
#else

#ifndef CHAR_BIT
    #include <limits.h>
#endif

#include <cyassl/ctaocrypt/mpi_class.h>

#ifndef MIN
   #define MIN(x,y) ((x)<(y)?(x):(y))
#endif

#ifndef MAX
   #define MAX(x,y) ((x)>(y)?(x):(y))
#endif

#ifdef __cplusplus
extern "C" {

/* C++ compilers don't like assigning void * to mp_digit * */
#define  OPT_CAST(x)  (x *)

#else

/* C on the other hand doesn't care */
#define  OPT_CAST(x)

#endif


/* detect 64-bit mode if possible */
#if defined(__x86_64__) 
   #if !(defined(MP_64BIT) && defined(MP_16BIT) && defined(MP_8BIT))
      #define MP_64BIT
   #endif
#endif

/* some default configurations.
 *
 * A "mp_digit" must be able to hold DIGIT_BIT + 1 bits
 * A "mp_word" must be able to hold 2*DIGIT_BIT + 1 bits
 *
 * At the very least a mp_digit must be able to hold 7 bits
 * [any size beyond that is ok provided it doesn't overflow the data type]
 */
#ifdef MP_8BIT
   typedef unsigned char      mp_digit;
   typedef unsigned short     mp_word;
#elif defined(MP_16BIT)
   typedef unsigned short     mp_digit;
   typedef unsigned long      mp_word;
#elif defined(MP_64BIT)
   /* for GCC only on supported platforms */
#ifndef CRYPT
   typedef unsigned long long ulong64;
   typedef signed long long   long64;
#endif

   typedef unsigned long      mp_digit;
   typedef unsigned long      mp_word __attribute__ ((mode(TI)));

   #define DIGIT_BIT          60
#else
   /* this is the default case, 28-bit digits */
   
   /* this is to make porting into LibTomCrypt easier :-) */
#ifndef CRYPT
   #if defined(_MSC_VER) || defined(__BORLANDC__) 
      typedef unsigned __int64   ulong64;
      typedef signed __int64     long64;
   #else
      typedef unsigned long long ulong64;
      typedef signed long long   long64;
   #endif
#endif

   typedef unsigned int       mp_digit;  /* long could be 64 now, changed TAO */
   typedef ulong64            mp_word;

#ifdef MP_31BIT   
   /* this is an extension that uses 31-bit digits */
   #define DIGIT_BIT          31
#else
   /* default case is 28-bit digits, defines MP_28BIT as a handy test macro */
   #define DIGIT_BIT          28
   #define MP_28BIT
#endif   
#endif


/* otherwise the bits per digit is calculated automatically from the size of
   a mp_digit */
#ifndef DIGIT_BIT
   #define DIGIT_BIT ((int)((CHAR_BIT * sizeof(mp_digit) - 1)))
      /* bits per digit */
#endif

#define MP_DIGIT_BIT     DIGIT_BIT
#define MP_MASK          ((((mp_digit)1)<<((mp_digit)DIGIT_BIT))-((mp_digit)1))
#define MP_DIGIT_MAX     MP_MASK

/* equalities */
#define MP_LT        -1   /* less than */
#define MP_EQ         0   /* equal to */
#define MP_GT         1   /* greater than */

#define MP_ZPOS       0   /* positive integer */
#define MP_NEG        1   /* negative */

#define MP_OKAY       0   /* ok result */
#define MP_MEM        -2  /* out of mem */
#define MP_VAL        -3  /* invalid input */
#define MP_RANGE      MP_VAL

#define MP_YES        1   /* yes response */
#define MP_NO         0   /* no response */

/* Primality generation flags */
#define LTM_PRIME_BBS      0x0001 /* BBS style prime */
#define LTM_PRIME_SAFE     0x0002 /* Safe prime (p-1)/2 == prime */
#define LTM_PRIME_2MSB_ON  0x0008 /* force 2nd MSB to 1 */

typedef int           mp_err;

/* define this to use lower memory usage routines (exptmods mostly) */
#define MP_LOW_MEM

/* default precision */
#ifndef MP_PREC
   #ifndef MP_LOW_MEM
      #define MP_PREC                 32     /* default digits of precision */
   #else
      #define MP_PREC                 1      /* default digits of precision */
   #endif   
#endif

/* size of comba arrays, should be at least 2 * 2**(BITS_PER_WORD - 
   BITS_PER_DIGIT*2) */
#define MP_WARRAY  (1 << (sizeof(mp_word) * CHAR_BIT - 2 * DIGIT_BIT + 1))

/* the infamous mp_int structure */
typedef struct  {
    int used, alloc, sign;
    mp_digit *dp;
} mp_int;

/* callback for mp_prime_random, should fill dst with random bytes and return
   how many read [upto len] */
typedef int ltm_prime_callback(unsigned char *dst, int len, void *dat);


#define USED(m)    ((m)->used)
#define DIGIT(m,k) ((m)->dp[(k)])
#define SIGN(m)    ((m)->sign)


/* ---> Basic Manipulations <--- */
#define mp_iszero(a) (((a)->used == 0) ? MP_YES : MP_NO)
#define mp_iseven(a) \
    (((a)->used > 0 && (((a)->dp[0] & 1) == 0)) ? MP_YES : MP_NO)
#define mp_isodd(a) \
    (((a)->used > 0 && (((a)->dp[0] & 1) == 1)) ? MP_YES : MP_NO)


/* number of primes */
#ifdef MP_8BIT
   #define PRIME_SIZE      31
#else
   #define PRIME_SIZE      256
#endif

#define mp_prime_random(a, t, size, bbs, cb, dat) \
   mp_prime_random_ex(a, t, ((size) * 8) + 1, (bbs==1)?LTM_PRIME_BBS:0, cb, dat)

#define mp_read_raw(mp, str, len) mp_read_signed_bin((mp), (str), (len))
#define mp_raw_size(mp)           mp_signed_bin_size(mp)
#define mp_toraw(mp, str)         mp_to_signed_bin((mp), (str))
#define mp_read_mag(mp, str, len) mp_read_unsigned_bin((mp), (str), (len))
#define mp_mag_size(mp)           mp_unsigned_bin_size(mp)
#define mp_tomag(mp, str)         mp_to_unsigned_bin((mp), (str))

#define mp_tobinary(M, S)  mp_toradix((M), (S), 2)
#define mp_tooctal(M, S)   mp_toradix((M), (S), 8)
#define mp_todecimal(M, S) mp_toradix((M), (S), 10)
#define mp_tohex(M, S)     mp_toradix((M), (S), 16)

#define s_mp_mul(a, b, c) s_mp_mul_digs(a, b, c, (a)->used + (b)->used + 1)

extern const char *mp_s_rmap;

/* 6 functions needed by Rsa */
int  mp_init (mp_int * a);
void mp_clear (mp_int * a);
int  mp_unsigned_bin_size(mp_int * a);
int  mp_read_unsigned_bin (mp_int * a, const unsigned char *b, int c);
int  mp_to_unsigned_bin (mp_int * a, unsigned char *b);
int  mp_exptmod (mp_int * G, mp_int * X, mp_int * P, mp_int * Y);
/* end functions needed by Rsa */

/* functions added to support above needed, removed TOOM and KARATSUBA */
int  mp_count_bits (mp_int * a);
int  mp_init_copy (mp_int * a, mp_int * b);
int  mp_copy (mp_int * a, mp_int * b);
int  mp_grow (mp_int * a, int size);
void bn_reverse (unsigned char *s, int len);
int  mp_div_2d (mp_int * a, int b, mp_int * c, mp_int * d);
void mp_zero (mp_int * a);
void mp_clamp (mp_int * a);
void mp_exch (mp_int * a, mp_int * b);
void mp_rshd (mp_int * a, int b);
int  mp_mod_2d (mp_int * a, int b, mp_int * c);
int  mp_mul_2d (mp_int * a, int b, mp_int * c);
int  mp_lshd (mp_int * a, int b);
int  mp_abs (mp_int * a, mp_int * b);
int  mp_invmod (mp_int * a, mp_int * b, mp_int * c);
int  fast_mp_invmod (mp_int * a, mp_int * b, mp_int * c);
int  mp_invmod_slow (mp_int * a, mp_int * b, mp_int * c);
int  mp_cmp_mag (mp_int * a, mp_int * b);
int  mp_cmp (mp_int * a, mp_int * b);
int  mp_cmp_d(mp_int * a, mp_digit b);
void mp_set (mp_int * a, mp_digit b);
int  mp_mod (mp_int * a, mp_int * b, mp_int * c);
int  mp_div(mp_int * a, mp_int * b, mp_int * c, mp_int * d);
int  mp_div_2(mp_int * a, mp_int * b);
int  mp_add (mp_int * a, mp_int * b, mp_int * c);
int  s_mp_add (mp_int * a, mp_int * b, mp_int * c);
int  s_mp_sub (mp_int * a, mp_int * b, mp_int * c);
int  mp_sub (mp_int * a, mp_int * b, mp_int * c);
int  mp_reduce_is_2k_l(mp_int *a);
int  mp_reduce_is_2k(mp_int *a);
int  mp_dr_is_modulus(mp_int *a);
int  mp_exptmod_fast (mp_int * G, mp_int * X, mp_int * P, mp_int * Y, int);
int  mp_montgomery_setup (mp_int * n, mp_digit * rho);
int  fast_mp_montgomery_reduce (mp_int * x, mp_int * n, mp_digit rho);
int  mp_montgomery_reduce (mp_int * x, mp_int * n, mp_digit rho);
void mp_dr_setup(mp_int *a, mp_digit *d);
int  mp_dr_reduce (mp_int * x, mp_int * n, mp_digit k);
int  mp_reduce_2k(mp_int *a, mp_int *n, mp_digit d);
int  fast_s_mp_mul_high_digs (mp_int * a, mp_int * b, mp_int * c, int digs);
int  s_mp_mul_high_digs (mp_int * a, mp_int * b, mp_int * c, int digs);
int  mp_reduce_2k_setup_l(mp_int *a, mp_int *d);
int  mp_reduce_2k_l(mp_int *a, mp_int *n, mp_int *d);
int  mp_reduce (mp_int * x, mp_int * m, mp_int * mu);
int  mp_reduce_setup (mp_int * a, mp_int * b);
int  s_mp_exptmod (mp_int * G, mp_int * X, mp_int * P, mp_int * Y, int redmode);
int  mp_montgomery_calc_normalization (mp_int * a, mp_int * b);
int  s_mp_mul_digs (mp_int * a, mp_int * b, mp_int * c, int digs);
int  s_mp_sqr (mp_int * a, mp_int * b);
int  fast_s_mp_mul_digs (mp_int * a, mp_int * b, mp_int * c, int digs);
int  fast_s_mp_sqr (mp_int * a, mp_int * b);
int  mp_init_size (mp_int * a, int size);
int  mp_div_3 (mp_int * a, mp_int *c, mp_digit * d);
int  mp_mul_2(mp_int * a, mp_int * b);
int  mp_mul (mp_int * a, mp_int * b, mp_int * c);
int  mp_sqr (mp_int * a, mp_int * b);
int  mp_mulmod (mp_int * a, mp_int * b, mp_int * c, mp_int * d);
int  mp_mul_d (mp_int * a, mp_digit b, mp_int * c);
int  mp_2expt (mp_int * a, int b);
int  mp_reduce_2k_setup(mp_int *a, mp_digit *d);
int  mp_add_d (mp_int* a, mp_digit b, mp_int* c);
int mp_set_int (mp_int * a, unsigned long b);
/* end support added functions */

/* added */
int mp_init_multi(mp_int* a, mp_int* b, mp_int* c, mp_int* d, mp_int* e,
                  mp_int* f);

#if defined(HAVE_ECC) || defined(CYASSL_KEY_GEN)
    int mp_sqrmod(mp_int* a, mp_int* b, mp_int* c);
#endif
#ifdef HAVE_ECC
    int mp_read_radix(mp_int* a, const char* str, int radix);
#endif

#ifdef CYASSL_KEY_GEN
    int mp_prime_is_prime (mp_int * a, int t, int *result);
    int mp_gcd (mp_int * a, mp_int * b, mp_int * c);
    int mp_lcm (mp_int * a, mp_int * b, mp_int * c);
#endif

#if defined(CYASSL_KEY_GEN) || defined(HAVE_ECC) || !defined(NO_PWDBASED)
    int mp_sub_d (mp_int * a, mp_digit b, mp_int * c);
#endif

#ifdef __cplusplus
   }
#endif


#endif /* USE_FAST_MATH */

#endif  /* CTAO_CRYPT_INTEGER_H */

