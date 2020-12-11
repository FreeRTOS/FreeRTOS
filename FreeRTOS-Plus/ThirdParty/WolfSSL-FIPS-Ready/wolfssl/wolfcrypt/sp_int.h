/* sp_int.h
 *
 * Copyright (C) 2006-2020 wolfSSL Inc.
 *
 * This file is part of wolfSSL.
 *
 * wolfSSL is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 3 of the License, or
 * (at your option) any later version.
 *
 * wolfSSL is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1335, USA
 */

/*
DESCRIPTION
This library provides single precision (SP) integer math functions.

*/
#ifndef WOLF_CRYPT_SP_INT_H
#define WOLF_CRYPT_SP_INT_H

#include <stdint.h>
#include <limits.h>

/* Make sure WOLFSSL_SP_ASM build option defined when requested */
#if !defined(WOLFSSL_SP_ASM) && ( \
      defined(WOLFSSL_SP_X86_64_ASM) || defined(WOLFSSL_SP_ARM32_ASM) || \
      defined(WOLFSSL_SP_ARM64_ASM)  || defined(WOLFSSL_SP_ARM_THUMB_ASM) || \
      defined(WOLFSSL_SP_ARM_CORTEX_M_ASM))
    #define WOLFSSL_SP_ASM
#endif


#ifdef WOLFSSL_SP_X86_64_ASM
    #define SP_WORD_SIZE 64

    #define HAVE_INTEL_AVX1
    #define HAVE_INTEL_AVX2
#elif defined(WOLFSSL_SP_ARM64_ASM)
    #define SP_WORD_SIZE 64
#elif defined(WOLFSSL_SP_ARM32_ASM)
    #define SP_WORD_SIZE 32
#elif defined(WOLFSSL_SP_ARM_THUMB_ASM)
    #define SP_WORD_SIZE 32
#endif

#ifndef SP_WORD_SIZE
    #if defined(NO_64BIT) || !defined(HAVE___UINT128_T)
        #define SP_WORD_SIZE 32
    #else
        #define SP_WORD_SIZE 64
    #endif
#endif

#ifdef WOLFSSL_DSP_BUILD
    typedef int32 sp_digit;
    typedef uint32 sp_int_digit;
    typedef uint64 sp_int_word;
    typedef int64 sp_int_sword;
    #undef SP_WORD_SIZE
    #define SP_WORD_SIZE 32
#elif !defined(WOLFSSL_SP_ASM)
  #if SP_WORD_SIZE == 32
    typedef int32_t sp_digit;
    typedef uint32_t sp_int_digit;
    typedef uint64_t sp_int_word;
    typedef int64_t sp_int_sword;
  #elif SP_WORD_SIZE == 64
    typedef int64_t sp_digit;
    typedef uint64_t sp_int_digit;
    #ifdef __SIZEOF_INT128__
      typedef __uint128_t uint128_t;
      typedef __int128_t int128_t;
    #else
      typedef unsigned long uint128_t __attribute__ ((mode(TI)));
      typedef long int128_t __attribute__ ((mode(TI)));
    #endif
    typedef uint128_t sp_int_word;
    typedef int128_t sp_int_sword;
  #else
    #error Word size not defined
  #endif
#else
  #if SP_WORD_SIZE == 32
    typedef uint32_t sp_digit;
    typedef uint32_t sp_int_digit;
    typedef uint64_t sp_int_word;
    typedef int64_t sp_int_sword;
  #elif SP_WORD_SIZE == 64
    typedef uint64_t sp_digit;
    typedef uint64_t sp_int_digit;
    #ifdef __SIZEOF_INT128__
      typedef __uint128_t uint128_t;
      typedef __int128_t int128_t;
    #else
      typedef unsigned long uint128_t __attribute__ ((mode(TI)));
      typedef long int128_t __attribute__ ((mode(TI)));
    #endif
    typedef uint128_t sp_int_word;
    typedef int128_t sp_int_sword;
  #else
    #error Word size not defined
  #endif
#endif

#define SP_MASK    (sp_digit)(-1)


#if defined(WOLFSSL_HAVE_SP_ECC) && defined(WOLFSSL_SP_NONBLOCK)
typedef struct sp_ecc_ctx {
    #ifdef WOLFSSL_SP_384
    byte data[48*80]; /* stack data */
    #else
    byte data[32*80]; /* stack data */
    #endif
} sp_ecc_ctx_t;
#endif

#ifdef WOLFSSL_SP_MATH
#include <wolfssl/wolfcrypt/random.h>

#if !defined(WOLFSSL_HAVE_SP_RSA) && !defined(WOLFSSL_HAVE_SP_DH)
    #if !defined(NO_PWDBASED) && defined(WOLFSSL_SHA512)
        #define SP_INT_DIGITS        ((512 + SP_WORD_SIZE) / SP_WORD_SIZE)
    #elif defined(WOLFSSL_SP_384)
        #define SP_INT_DIGITS        ((384 + SP_WORD_SIZE) / SP_WORD_SIZE)
    #else
        #define SP_INT_DIGITS        ((256 + SP_WORD_SIZE) / SP_WORD_SIZE)
    #endif
#elif defined(WOLFSSL_SP_4096)
    #if defined(WOLFSSL_HAVE_SP_DH)
        #define SP_INT_DIGITS        ((8192 + SP_WORD_SIZE) / SP_WORD_SIZE)
    #else
        #define SP_INT_DIGITS        ((4096 + SP_WORD_SIZE) / SP_WORD_SIZE)
    #endif
#elif !defined(WOLFSSL_SP_NO_3072)
    #if defined(WOLFSSL_HAVE_SP_DH)
        #define SP_INT_DIGITS        ((6144 + SP_WORD_SIZE) / SP_WORD_SIZE)
    #else
        #define SP_INT_DIGITS        ((3072 + SP_WORD_SIZE) / SP_WORD_SIZE)
    #endif
#else
    #if defined(WOLFSSL_HAVE_SP_DH)
        #define SP_INT_DIGITS        ((4096 + SP_WORD_SIZE) / SP_WORD_SIZE)
    #else
        #define SP_INT_DIGITS        ((2048 + SP_WORD_SIZE) / SP_WORD_SIZE)
    #endif
#endif

#define sp_isodd(a)  ((a)->used != 0 && ((a)->dp[0] & 1))
#define sp_iseven(a) ((a)->used != 0 && ((a)->dp[0] & 1) == 0)
#define sp_iszero(a) ((a)->used == 0)
#define sp_isone(a)  ((a)->used == 1 && (a)->dp[0] == 1)
#define sp_abs(a, b)  sp_copy(a, b)

#ifdef HAVE_WOLF_BIGINT
    /* raw big integer */
    typedef struct WC_BIGINT {
        byte*   buf;
        word32  len;
        void*   heap;
    } WC_BIGINT;
    #define WOLF_BIGINT_DEFINED
#endif

typedef struct sp_int {
    int used;
    int size;
    sp_int_digit dp[SP_INT_DIGITS];
#ifdef HAVE_WOLF_BIGINT
    struct WC_BIGINT raw; /* unsigned binary (big endian) */
#endif
} sp_int;

typedef sp_int       mp_int;
typedef sp_int_digit mp_digit;

#include <wolfssl/wolfcrypt/wolfmath.h>


MP_API int sp_init(sp_int* a);
MP_API int sp_init_multi(sp_int* a, sp_int* b, sp_int* c, sp_int* d,
                         sp_int* e, sp_int* f);
MP_API void sp_clear(sp_int* a);
MP_API int sp_unsigned_bin_size(sp_int* a);
MP_API int sp_read_unsigned_bin(sp_int* a, const byte* in, word32 inSz);
MP_API int sp_read_radix(sp_int* a, const char* in, int radix);
MP_API int sp_cmp(sp_int* a, sp_int* b);
MP_API int sp_count_bits(sp_int* a);
MP_API int sp_leading_bit(sp_int* a);
MP_API int sp_to_unsigned_bin(sp_int* a, byte* out);
MP_API int sp_to_unsigned_bin_len(sp_int* a, byte* out, int outSz);
MP_API void sp_forcezero(sp_int* a);
MP_API int sp_copy(sp_int* a, sp_int* r);
MP_API int sp_set(sp_int* a, sp_int_digit d);
MP_API void sp_clamp(sp_int* a);
MP_API int sp_grow(sp_int* a, int l);
MP_API int sp_sub_d(sp_int* a, sp_int_digit d, sp_int* r);
MP_API int sp_cmp_d(sp_int* a, sp_int_digit d);
MP_API int sp_sub(sp_int* a, sp_int* b, sp_int* r);
MP_API int sp_mod(sp_int* a, sp_int* m, sp_int* r);
MP_API void sp_zero(sp_int* a);
MP_API int sp_add_d(sp_int* a, sp_int_digit d, sp_int* r);
MP_API int sp_lshd(sp_int* a, int s);
MP_API int sp_add(sp_int* a, sp_int* b, sp_int* r);
MP_API int sp_set_int(sp_int* a, unsigned long b);
MP_API int sp_tohex(sp_int* a, char* str);
MP_API int sp_set_bit(sp_int* a, int i);
MP_API int sp_2expt(sp_int* a, int e);
MP_API int sp_rand_prime(sp_int* r, int len, WC_RNG* rng, void* heap);
MP_API int sp_mul(sp_int* a, sp_int* b, sp_int* r);
MP_API int sp_mulmod(sp_int* a, sp_int* b, sp_int* m, sp_int* r);
MP_API int sp_gcd(sp_int* a, sp_int* b, sp_int* r);
MP_API int sp_invmod(sp_int* a, sp_int* m, sp_int* r);
MP_API int sp_lcm(sp_int* a, sp_int* b, sp_int* r);
MP_API int sp_exptmod(sp_int* b, sp_int* e, sp_int* m, sp_int* r);
MP_API int sp_prime_is_prime(mp_int* a, int t, int* result);
MP_API int sp_prime_is_prime_ex(mp_int* a, int t, int* result, WC_RNG* rng);
MP_API int sp_exch(sp_int* a, sp_int* b);
MP_API int sp_get_digit_count(sp_int *a);
MP_API int sp_init_copy (sp_int * a, sp_int * b);
MP_API void sp_rshb(sp_int* a, int n, sp_int* r);
MP_API int sp_mul_d(sp_int* a, sp_int_digit n, sp_int* r);


#define MP_NO      0
#define MP_YES     1

#define MP_RADIX_HEX     16

#define MP_GT    1
#define MP_EQ    0
#define MP_LT    -1

#define MP_OKAY   0
#define MP_MEM   -2
#define MP_VAL   -3
#define FP_WOULDBLOCK -4

#define DIGIT_BIT  SP_WORD_SIZE
#define MP_MASK    SP_MASK

#define CheckFastMathSettings() 1

#define mp_free(a)

#define mp_isodd                    sp_isodd
#define mp_iseven                   sp_iseven
#define mp_iszero                   sp_iszero
#define mp_isone                    sp_isone
#define mp_abs                      sp_abs

#define mp_init                     sp_init
#define mp_init_multi               sp_init_multi
#define mp_clear                    sp_clear
#define mp_read_unsigned_bin        sp_read_unsigned_bin
#define mp_unsigned_bin_size        sp_unsigned_bin_size
#define mp_read_radix               sp_read_radix
#define mp_cmp                      sp_cmp
#define mp_count_bits               sp_count_bits
#define mp_leading_bit              sp_leading_bit
#define mp_to_unsigned_bin          sp_to_unsigned_bin
#define mp_to_unsigned_bin_len      sp_to_unsigned_bin_len
#define mp_forcezero                sp_forcezero
#define mp_copy                     sp_copy
#define mp_set                      sp_set
#define mp_clamp                    sp_clamp
#define mp_grow                     sp_grow
#define mp_sub_d                    sp_sub_d
#define mp_cmp_d                    sp_cmp_d
#define mp_sub                      sp_sub
#define mp_mod                      sp_mod
#define mp_zero                     sp_zero
#define mp_add_d                    sp_add_d
#define mp_lshd                     sp_lshd
#define mp_add                      sp_add
#define mp_set_int                  sp_set_int
#define mp_tohex                    sp_tohex
#define mp_set_bit                  sp_set_bit
#define mp_2expt                    sp_2expt
#define mp_rand_prime               sp_rand_prime
#define mp_mul                      sp_mul
#define mp_mulmod                   sp_mulmod
#define mp_gcd                      sp_gcd
#define mp_invmod                   sp_invmod
#define mp_lcm                      sp_lcm
#define mp_exptmod                  sp_exptmod
#define mp_exptmod_nct              sp_exptmod
#define mp_prime_is_prime           sp_prime_is_prime
#define mp_prime_is_prime_ex        sp_prime_is_prime_ex
#define mp_exch                     sp_exch
#define get_digit_count             sp_get_digit_count
#define mp_init_copy                sp_init_copy
#define mp_rshb(A,x)                sp_rshb(A,x,A)
#define mp_mul_d                    sp_mul_d

#endif

#endif /* WOLF_CRYPT_SP_H */

