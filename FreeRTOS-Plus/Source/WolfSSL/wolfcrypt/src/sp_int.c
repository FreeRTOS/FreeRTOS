/* sp_int.c
 *
 * Copyright (C) 2006-2020 wolfSSL Inc.
 *
 * This file is part of wolfSSL.
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
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1335, USA
 */

/* Implementation by Sean Parkinson. */

/*
DESCRIPTION
This library provides single precision (SP) integer math functions.

*/
#ifdef HAVE_CONFIG_H
    #include <config.h>
#endif

#include <wolfssl/wolfcrypt/settings.h>
#include <wolfssl/wolfcrypt/error-crypt.h>
#ifdef NO_INLINE
    #include <wolfssl/wolfcrypt/misc.h>
#else
    #define WOLFSSL_MISC_INCLUDED
    #include <wolfcrypt/src/misc.c>
#endif

/* SP Build Options:
 * WOLFSSL_HAVE_SP_RSA:         Enable SP RSA support
 * WOLFSSL_HAVE_SP_DH:          Enable SP DH support
 * WOLFSSL_HAVE_SP_ECC:         Enable SP ECC support
 * WOLFSSL_SP_MATH:             Use only single precision math and algorithms
 *      it supports (no fastmath tfm.c or normal integer.c)
 * WOLFSSL_SP_SMALL:            Use smaller version of code and avoid large
 *      stack variables
 * WOLFSSL_SP_NO_MALLOC:        Always use stack, no heap XMALLOC/XFREE allowed
 * WOLFSSL_SP_NO_2048:          Disable RSA/DH 2048-bit support
 * WOLFSSL_SP_NO_3072:          Disable RSA/DH 3072-bit support
 * WOLFSSL_SP_4096:             Enable RSA/RH 4096-bit support
 * WOLFSSL_SP_384               Enable ECC 384-bit SECP384R1 support
 * WOLFSSL_SP_NO_256            Disable ECC 256-bit SECP256R1 support
 * WOLFSSL_SP_ASM               Enable assembly speedups (detect platform)
 * WOLFSSL_SP_X86_64_ASM        Enable Intel x86 assembly speedups like AVX/AVX2
 * WOLFSSL_SP_ARM32_ASM         Enable Aarch32 assembly speedups
 * WOLFSSL_SP_ARM64_ASM         Enable Aarch64 assembly speedups
 * WOLFSSL_SP_ARM_CORTEX_M_ASM  Enable Cortex-M assembly speedups
 * WOLFSSL_SP_ARM_THUMB_ASM     Enable ARM Thumb assembly speedups
 *      (used with -mthumb)
 * SP_WORD_SIZE                 Force 32 or 64 bit mode
 * WOLFSSL_SP_NONBLOCK          Enables "non blocking" mode for SP math, which
 *      will return FP_WOULDBLOCK for long operations and function must be
 *      called again until complete.
 */

#ifdef WOLFSSL_SP_MATH

#include <wolfssl/wolfcrypt/sp_int.h>

#if defined(WOLFSSL_HAVE_SP_DH) || defined(WOLFSSL_HAVE_SP_RSA)

WOLFSSL_LOCAL int sp_ModExp_1024(sp_int* base, sp_int* exp, sp_int* mod,
    sp_int* res);
WOLFSSL_LOCAL int sp_ModExp_1536(sp_int* base, sp_int* exp, sp_int* mod,
    sp_int* res);
WOLFSSL_LOCAL int sp_ModExp_2048(sp_int* base, sp_int* exp, sp_int* mod,
    sp_int* res);
WOLFSSL_LOCAL int sp_ModExp_3072(sp_int* base, sp_int* exp, sp_int* mod,
    sp_int* res);
WOLFSSL_LOCAL int sp_ModExp_4096(sp_int* base, sp_int* exp, sp_int* mod,
    sp_int* res);

#endif

int sp_get_digit_count(sp_int *a)
{
    int ret;
    if (!a)
        ret = 0;
    else
        ret = a->used;
    return ret;
}

/* Initialize the big number to be zero.
 *
 * a  SP integer.
 * returns MP_OKAY always.
 */
int sp_init(sp_int* a)
{
    a->used = 0;
    a->size = SP_INT_DIGITS;

    return MP_OKAY;
}

#if !defined(WOLFSSL_RSA_PUBLIC_ONLY) || (!defined(NO_DH) || defined(HAVE_ECC))
/* Initialize up to six big numbers to be zero.
 *
 * a  SP integer.
 * b  SP integer.
 * c  SP integer.
 * d  SP integer.
 * e  SP integer.
 * f  SP integer.
 * returns MP_OKAY always.
 */
int sp_init_multi(sp_int* a, sp_int* b, sp_int* c, sp_int* d, sp_int* e,
                  sp_int* f)
{
    if (a != NULL) {
        a->used = 0;
        a->size = SP_INT_DIGITS;
    }
    if (b != NULL) {
        b->used = 0;
        b->size = SP_INT_DIGITS;
    }
    if (c != NULL) {
        c->used = 0;
        c->size = SP_INT_DIGITS;
    }
    if (d != NULL) {
        d->used = 0;
        d->size = SP_INT_DIGITS;
    }
    if (e != NULL) {
        e->used = 0;
        e->size = SP_INT_DIGITS;
    }
    if (f != NULL) {
        f->used = 0;
        f->size = SP_INT_DIGITS;
    }

    return MP_OKAY;
}
#endif

/* Clear the data from the big number and set to zero.
 *
 * a  SP integer.
 */
void sp_clear(sp_int* a)
{
    if (a != NULL) {
        int i;

        for (i=0; i<a->used; i++)
            a->dp[i] = 0;
        a->used = 0;
    }
}

/* Calculate the number of 8-bit values required to represent the big number.
 *
 * a  SP integer.
 * returns the count.
 */
int sp_unsigned_bin_size(sp_int* a)
{
    int size = sp_count_bits(a);
    return (size + 7) / 8;
}

/* Convert a number as an array of bytes in big-endian format to a big number.
 *
 * a     SP integer.
 * in    Array of bytes.
 * inSz  Number of data bytes in array.
 * returns MP_VAL when the number is too big to fit in an SP and
           MP_OKAY otherwise.
 */
int sp_read_unsigned_bin(sp_int* a, const byte* in, word32 inSz)
{
    int err = MP_OKAY;
    int i, j = 0, k;

    /* Extra digit added to SP_INT_DIGITS to be used in calculations. */
    if (inSz > (SP_INT_DIGITS - 1) * (int)sizeof(a->dp[0])) {
        err = MP_VAL;
    }
    else if (inSz == 0) {
        XMEMSET(a->dp, 0, a->size * sizeof(*a->dp));
        a->used = 0;
    }
    else {
        for (i = inSz-1; i >= (SP_WORD_SIZE/8); i -= (SP_WORD_SIZE/8), j++) {
            a->dp[j]  = (((sp_int_digit)in[i-0]) << (0*8))
                     |  (((sp_int_digit)in[i-1]) << (1*8))
                     |  (((sp_int_digit)in[i-2]) << (2*8))
                     |  (((sp_int_digit)in[i-3]) << (3*8));
    #if SP_WORD_SIZE == 64
            a->dp[j] |= (((sp_int_digit)in[i-4]) << (4*8))
                     |  (((sp_int_digit)in[i-5]) << (5*8))
                     |  (((sp_int_digit)in[i-6]) << (6*8))
                     |  (((sp_int_digit)in[i-7]) << (7*8));
    #endif
        }
        if (i >= 0) {
            a->dp[j] = 0;
            for (k = 0; k <= i; k++) {
                a->dp[j] <<= 8;
                a->dp[j] |= in[k];
            }
        }
        a->used = j + 1;

        sp_clamp(a);
    }

    return err;
}

#ifdef HAVE_ECC
/* Convert a number as string in big-endian format to a big number.
 * Only supports base-16 (hexadecimal).
 * Negative values not supported.
 *
 * a      SP integer.
 * in     NUL terminated string.
 * radix  Number of values in a digit.
 * returns BAD_FUNC_ARG when radix not supported or value is negative, MP_VAL
 * when a character is not valid and MP_OKAY otherwise.
 */
int sp_read_radix(sp_int* a, const char* in, int radix)
{
    int  err = MP_OKAY;
    int  i, j = 0, k = 0;
    char ch;

    if ((radix != 16) || (*in == '-')) {
        err = BAD_FUNC_ARG;
    }

    while (*in == '0') {
        in++;
    }

    if (err == MP_OKAY) {
        a->dp[0] = 0;
        for (i = (int)(XSTRLEN(in) - 1); i >= 0; i--) {
            ch = in[i];
            if (ch >= '0' && ch <= '9')
                ch -= '0';
            else if (ch >= 'A' && ch <= 'F')
                ch -= 'A' - 10;
            else if (ch >= 'a' && ch <= 'f')
                ch -= 'a' - 10;
            else {
                err = MP_VAL;
                break;
            }

            a->dp[k] |= ((sp_int_digit)ch) << j;
            j += 4;
            if (k >= SP_INT_DIGITS - 1) {
                err = MP_VAL;
                break;
            }
            if (j == DIGIT_BIT)
                a->dp[++k] = 0;
            j &= SP_WORD_SIZE - 1;
        }
    }

    if (err == MP_OKAY) {
        a->used = k + 1;
        if (a->dp[k] == 0)
            a->used--;

        for (k++; k < a->size; k++)
            a->dp[k] = 0;

        sp_clamp(a);
    }

    return err;
}
#endif

/* Compare two big numbers.
 *
 * a  SP integer.
 * b  SP integer.
 * returns MP_GT if a is greater than b, MP_LT if a is less than b and MP_EQ
 * when a equals b.
 */
int sp_cmp(sp_int* a, sp_int* b)
{
    int ret = MP_EQ;
    int i;

    if (a->used > b->used)
        ret = MP_GT;
    else if (a->used < b->used)
        ret = MP_LT;
    else {
        for (i = a->used - 1; i >= 0; i--) {
            if (a->dp[i] > b->dp[i]) {
                ret = MP_GT;
                break;
            }
            else if (a->dp[i] < b->dp[i]) {
                ret = MP_LT;
                break;
            }
        }
    }
    return ret;
}

/* Count the number of bits in the big number.
 *
 * a  SP integer.
 * returns the number of bits.
 */
int sp_count_bits(sp_int* a)
{
    int r = 0;
    sp_int_digit d;

    r = a->used - 1;
    while (r >= 0 && a->dp[r] == 0)
        r--;
    if (r < 0)
        r = 0;
    else {
        d = a->dp[r];
        r *= SP_WORD_SIZE;
        if (d >= (1L << (SP_WORD_SIZE / 2))) {
            r += SP_WORD_SIZE;
            while ((d & (1UL << (SP_WORD_SIZE - 1))) == 0) {
                r--;
                d <<= 1;
            }
        }
        else {
            while (d != 0) {
                r++;
                d >>= 1;
            }
        }
    }

    return r;
}

/* Determine if the most significant byte of the encoded big number as the top
 * bit set.
 *
 * a  SP integer.
 * returns 1 when the top bit is set and 0 otherwise.
 */
int sp_leading_bit(sp_int* a)
{
    int bit = 0;
    sp_int_digit d;

    if (a->used > 0) {
        d = a->dp[a->used - 1];
        while (d > (sp_int_digit)0xff)
            d >>= 8;
        bit = (int)(d >> 7);
    }

    return bit;
}

#if !defined(NO_DH) || defined(HAVE_ECC) || defined(WC_RSA_BLINDING) || \
    !defined(WOLFSSL_RSA_VERIFY_ONLY)
/* Convert the big number to an array of bytes in big-endian format.
 * The array must be large enough for encoded number - use mp_unsigned_bin_size
 * to calculate the number of bytes required.
 *
 * a    SP integer.
 * out  Array to put encoding into.
 * returns MP_OKAY always.
 */
int sp_to_unsigned_bin(sp_int* a, byte* out)
{
    int i, j, b;
    sp_int_digit d;

    j = sp_unsigned_bin_size(a) - 1;
    for (i=0; j>=0; i++) {
        d = a->dp[i];
        for (b = 0; b < SP_WORD_SIZE / 8; b++) {
            out[j] = d;
            if (--j < 0) {
                break;
            }
            d >>= 8;
        }
    }

    return MP_OKAY;
}
#endif

/* Convert the big number to an array of bytes in big-endian format.
 * The array must be large enough for encoded number - use mp_unsigned_bin_size
 * to calculate the number of bytes required.
 * Front-pads the output array with zeros make number the size of the array.
 *
 * a      SP integer.
 * out    Array to put encoding into.
 * outSz  Size of the array.
 * returns MP_OKAY always.
 */
int sp_to_unsigned_bin_len(sp_int* a, byte* out, int outSz)
{
    int i, j, b;

    j = outSz - 1;
    for (i=0; j>=0; i++) {
        for (b = 0; b < SP_WORD_SIZE; b += 8) {
            out[j--] = a->dp[i] >> b;
            if (j < 0)
                break;
        }
    }

    return MP_OKAY;
}

#if !defined(WOLFSSL_RSA_PUBLIC_ONLY) || (!defined(NO_DH) || defined(HAVE_ECC))
/* Ensure the data in the big number is zeroed.
 *
 * a  SP integer.
 */
void sp_forcezero(sp_int* a)
{
    ForceZero(a->dp, a->used * sizeof(sp_int_digit));
    a->used = 0;
}
#endif

#if !defined(WOLFSSL_RSA_VERIFY_ONLY) || (!defined(NO_DH) || defined(HAVE_ECC))
/* Copy value of big number a into r.
 *
 * a  SP integer.
 * r  SP integer.
 * returns MP_OKAY always.
 */
int sp_copy(sp_int* a, sp_int* r)
{
    if (a != r) {
        XMEMCPY(r->dp, a->dp, a->used * sizeof(sp_int_digit));
        r->used = a->used;
    }
    return MP_OKAY;
}

/* creates "a" then copies b into it */
int sp_init_copy (sp_int * a, sp_int * b)
{
  int err;
  if ((err = sp_init(a)) == MP_OKAY) {
      if((err = sp_copy (b, a)) != MP_OKAY) {
          sp_clear(a);
      }
  }
  return err;
}
#endif

/* Set the big number to be the value of the digit.
 *
 * a  SP integer.
 * d  Digit to be set.
 * returns MP_OKAY always.
 */
int sp_set(sp_int* a, sp_int_digit d)
{
    if (d == 0) {
      a->dp[0] = d;
      a->used = 0;
    }
    else {
      a->dp[0] = d;
      a->used = 1;
    }
    return MP_OKAY;
}

/* Recalculate the number of digits used.
 *
 * a  SP integer.
 */
void sp_clamp(sp_int* a)
{
    int i;

    for (i = a->used - 1; i >= 0 && a->dp[i] == 0; i--) {
    }
    a->used = i + 1;
}

#if defined(WOLFSSL_RSA_VERIFY_ONLY) || (!defined(NO_DH) || defined(HAVE_ECC))
/* Grow big number to be able to hold l digits.
 * This function does nothing as the number of digits is fixed.
 *
 * a  SP integer.
 * l  Number of digits.
 * returns MP_MEM if the number of digits requested is more than available and
 * MP_OKAY otherwise.
 */
int sp_grow(sp_int* a, int l)
{
    int err = MP_OKAY;

    if (l > a->size)
        err = MP_MEM;

    return err;
}
#endif

#if !defined(WOLFSSL_RSA_VERIFY_ONLY) || (!defined(NO_DH) || defined(HAVE_ECC))
/* Sub a one digit number from the big number.
 *
 * a  SP integer.
 * d  Digit to subtract.
 * r  SP integer - result.
 * returns MP_OKAY always.
 */
int sp_sub_d(sp_int* a, sp_int_digit d, sp_int* r)
{
    int i = 0;
    sp_int_digit t;

    r->used = a->used;
    t = a->dp[0] - d;
    if (t > a->dp[0]) {
        for (++i; i < a->used; i++) {
            r->dp[i] = a->dp[i] - 1;
            if (r->dp[i] != (sp_int_digit)-1)
               break;
        }
    }
    r->dp[0] = t;
    if (r != a) {
        for (++i; i < a->used; i++)
            r->dp[i] = a->dp[i];
    }
    sp_clamp(r);

    return MP_OKAY;
}
#endif

/* Compare a one digit number with a big number.
 *
 * a  SP integer.
 * d  Digit to compare with.
 * returns MP_GT if a is greater than d, MP_LT if a is less than d and MP_EQ
 * when a equals d.
 */
int sp_cmp_d(sp_int *a, sp_int_digit d)
{
    int ret = MP_EQ;

    /* special case for zero*/
    if (a->used == 0) {
        if (d == 0)
            ret = MP_EQ;
        else
            ret = MP_LT;
    }
    else if (a->used > 1)
        ret = MP_GT;
    else {
        /* compare the only digit of a to d */
        if (a->dp[0] > d)
            ret = MP_GT;
        else if (a->dp[0] < d)
            ret = MP_LT;
    }

    return ret;
}

#if !defined(NO_DH) || defined(HAVE_ECC) || !defined(WOLFSSL_RSA_VERIFY_ONLY)
/* Left shift the number by number of bits.
 * Bits may be larger than the word size.
 *
 * a  SP integer.
 * n  Number of bits to shift.
 * returns MP_OKAY always.
 */
static int sp_lshb(sp_int* a, int n)
{
    int i;
    sp_digit v;

    if (n >= SP_WORD_SIZE) {
        sp_lshd(a, n / SP_WORD_SIZE);
        n %= SP_WORD_SIZE;
    }

    if ((n != 0) && (a->used != 0)) {
        v = a->dp[a->used - 1] >> (SP_WORD_SIZE - n);
        if (v != 0) {
            a->dp[a->used] = v;
        }
        a->dp[a->used - 1] = a->dp[a->used - 1] << n;
        for (i = a->used - 2; i >= 0; i--) {
            a->dp[i+1] |= a->dp[i] >> (SP_WORD_SIZE - n);
            a->dp[i] = a->dp[i] << n;
        }
        if (v != 0) {
            a->used++;
        }
    }

    return MP_OKAY;
}

/* Subtract two large numbers into result: r = a - b
 * a must be greater than b.
 *
 * a  SP integer.
 * b  SP integer.
 * r  SP integer.
 * returns MP_OKAY always.
 */
int sp_sub(sp_int* a, sp_int* b, sp_int* r)
{
    int i;
    sp_int_digit c = 0;
    sp_int_digit t;

    for (i = 0; i < a->used && i < b->used; i++) {
        t = a->dp[i] - b->dp[i] - c;
        if (c == 0)
            c = t > a->dp[i];
        else
            c = t >= a->dp[i];
        r->dp[i] = t;
    }
    for (; i < a->used; i++) {
        r->dp[i] = a->dp[i] - c;
        c &= (r->dp[i] == (sp_int_digit)-1);
    }
    r->used = i;
    sp_clamp(r);

    return MP_OKAY;
}

/* Shift a right by n bits into r: r = a >> n
 *
 * a    SP integer operand.
 * n    Number of bits to shift.
 * r    SP integer result.
 */
void sp_rshb(sp_int* a, int n, sp_int* r)
{
    int i = n / SP_WORD_SIZE;
    int j;

    if (i >= a->used) {
       r->dp[0] = 0;
       r->used = 0;
    }
    else {
        n %= SP_WORD_SIZE;
        if (n == 0) {
            for (j = 0; i < a->used; i++, j++)
                r->dp[j] = a->dp[i];
            r->used = j;
        }
        if (n > 0) {
            for (j = 0; i < a->used-1; i++, j++)
                r->dp[j] = (a->dp[i] >> n) | (a->dp[i+1] << (SP_WORD_SIZE - n));
            r->dp[j] = a->dp[i] >> n;
            r->used = j + 1;
            sp_clamp(r);
        }
    }
}

#if defined(WOLFSSL_SP_SMALL) || (defined(WOLFSSL_KEY_GEN) || \
                                         !defined(NO_DH) && !defined(WC_NO_RNG))
/* Multiply a by digit n and put result into r shifting up o digits.
 *   r = (a * n) << (o * SP_WORD_SIZE)
 *
 * a  SP integer to be multiplied.
 * n  Number to multiply by.
 * r  SP integer result.
 * o  Number of digits to move result up by.
 */
static void _sp_mul_d(sp_int* a, sp_int_digit n, sp_int* r, int o)
{
    int i;
    sp_int_word t = 0;

    for (i = 0; i < o; i++)
        r->dp[i] = 0;

    for (i = 0; i < a->used; i++) {
        t += (sp_int_word)n * a->dp[i];
        r->dp[i + o] = (sp_int_digit)t;
        t >>= SP_WORD_SIZE;
    }

    r->dp[i+o] = (sp_int_digit)t;
    r->used = i+o+1;
    sp_clamp(r);
}
#endif

/* Divide a two digit number by a digit number and return. (hi | lo) / d
 *
 * hi  SP integer digit. High digit.
 * lo  SP integer digit. Lower digit.
 * d   SP integer digit. Number to divide by.
 * returns the division result.
 */
static WC_INLINE sp_int_digit sp_div_word(sp_int_digit hi, sp_int_digit lo,
                                          sp_int_digit d)
{
#ifdef WOLFSSL_SP_DIV_WORD_HALF
    sp_int_digit div = d >> SP_HALF_SIZE;
    sp_int_digit r;
    sp_int_digit r2;
    sp_int_word w = ((sp_int_word)hi << SP_WORD_SIZE) | lo;
    sp_int_word trial;

    r = hi / div;
    if (r > SP_HALF_MAX) {
        r = SP_HALF_MAX;
    }
    r <<= SP_HALF_SIZE;
    trial = r * (sp_int_word)d;
    while (trial > w) {
        r -= (sp_int_digit)1 << SP_HALF_SIZE;
        trial -= (sp_int_word)d << SP_HALF_SIZE;
    }
    w -= trial;
    r2 = ((sp_int_digit)(w >> SP_HALF_SIZE)) / div;
    trial = r2 * (sp_int_word)d;
    while (trial > w) {
        r2--;
        trial -= d;
    }
    w -= trial;
    r += r2;
    r2 = ((sp_int_digit)w) / d;
    r += r2;

    return r;
#else
    sp_int_word w;
    sp_int_digit r;

    w = ((sp_int_word)hi << SP_WORD_SIZE) | lo;
    w /= d;
    r = (sp_int_digit)w;

    return r;
#endif
}


/* Divide a by d and return the quotient in r and the remainder in rem.
 *   r = a / d; rem = a % d
 *
 * a    SP integer to be divided.
 * d    SP integer to divide by.
 * r    SP integer of quotient.
 * rem  SP integer of remainder.
 * returns MP_VAL when d is 0, MP_MEM when dynamic memory allocation fails and
 *         MP_OKAY otherwise.
 */
static int sp_div(sp_int* a, sp_int* d, sp_int* r, sp_int* rem)
{
    int err = MP_OKAY;
    int ret;
    int done = 0;
    int i;
    int s;
    sp_int_digit dt;
    sp_int_digit t;
#ifdef WOLFSSL_SMALL_STACK
    sp_int* sa = NULL;
    sp_int* sd;
    sp_int* tr;
    sp_int* trial;
#else
    sp_int sa[1];
    sp_int sd[1];
    sp_int tr[1];
    sp_int trial[1];
#endif
    int o;
#ifdef WOLFSSL_SP_SMALL
    int c;
#else
    int j;
    sp_int_word tw;
    sp_int_sword sw;
#endif

    if (sp_iszero(d))
        err = MP_VAL;

    if (err == MP_OKAY) {
        ret = sp_cmp(a, d);
        if (ret == MP_LT) {
            if (rem != NULL) {
                sp_copy(a, rem);
            }
            if (r != NULL) {
                sp_set(r, 0);
            }
            done = 1;
        }
        else if (ret == MP_EQ) {
            if (rem != NULL) {
                sp_set(rem, 0);
            }
            if (r != NULL) {
                sp_set(r, 1);
            #ifdef WOLFSSL_SP_INT_NEGATIVE
                r->sign = aSign;
            #endif
            }
            done = 1;
        }
        else if (sp_count_bits(a) == sp_count_bits(d)) {
            /* a is greater than d but same bit length */
            if (rem != NULL) {
                sp_sub(a, d, rem);
            }
            if (r != NULL) {
                sp_set(r, 1);
            #ifdef WOLFSSL_SP_INT_NEGATIVE
                r->sign = aSign;
            #endif
            }
            done = 1;
        }
    }

#ifdef WOLFSSL_SMALL_STACK
    if (!done && err == MP_OKAY) {
        sa = (sp_int*)XMALLOC(sizeof(sp_int) * 4, NULL, DYNAMIC_TYPE_BIGINT);
        if (sa == NULL) {
            err = MP_MEM;
        }
    }
#endif

    if (!done && err == MP_OKAY) {
#ifdef WOLFSSL_SMALL_STACK
        sd    = &sa[1];
        tr    = &sa[2];
        trial = &sa[3];
#endif

        sp_init(sa);
        sp_init(sd);
        sp_init(tr);
        sp_init(trial);

        s = sp_count_bits(d);
        s = SP_WORD_SIZE - (s % SP_WORD_SIZE);
        sp_copy(a, sa);
        if (s != SP_WORD_SIZE) {
            sp_lshb(sa, s);
            sp_copy(d, sd);
            sp_lshb(sd, s);
            d = sd;
        }

        tr->used = sa->used - d->used + 1;
        sp_clear(tr);
        tr->used = sa->used - d->used + 1;
        dt = d->dp[d->used-1];

        for (i = d->used - 1; i > 0; i--) {
            if (sa->dp[sa->used - d->used + i] != d->dp[i]) {
                break;
            }
        }
        if (sa->dp[sa->used - d->used + i] >= d->dp[i]) {
            i = sa->used;
            o = sa->used - d->used;
            sp_lshb(d, o * SP_WORD_SIZE);
            sp_sub(sa, d, sa);
            sp_rshb(d, o * SP_WORD_SIZE, d);
            sa->used = i;
            if (r != NULL) {
                tr->dp[o] = 1;
            }
        }
        for (i = sa->used - 1; i >= d->used; i--) {
            if (sa->dp[i] == dt) {
                t = (sp_digit)-1;
            }
            else {
                t = sp_div_word(sa->dp[i], sa->dp[i-1], dt);
            }

#ifdef WOLFSSL_SP_SMALL
            do {
                _sp_mul_d(d, t, trial, i - d->used);
                c = sp_cmp(trial, sa);
                if (c == MP_GT) {
                    t--;
                }
            }
            while (c == MP_GT);

            sp_sub(sa, trial, sa);
            tr->dp[i - d->used] += t;
            if (tr->dp[i - d->used] < t) {
                tr->dp[i + 1 - d->used]++;
            }
#else
            o = i - d->used;
            do {
                tw = 0;
                for (j = 0; j < d->used; j++) {
                    tw += (sp_int_word)d->dp[j] * t;
                    trial->dp[j] = (sp_int_digit)tw;
                    tw >>= SP_WORD_SIZE;
                }
                trial->dp[j] = (sp_int_digit)tw;

                for (j = d->used; j > 0; j--) {
                    if (trial->dp[j] != sa->dp[j + o]) {
                        break;
                    }
                }
                if (trial->dp[j] > sa->dp[j + o]) {
                    t--;
                }
            }
            while (trial->dp[j] > sa->dp[j + o]);

            sw = 0;
            for (j = 0; j <= d->used; j++) {
                sw += sa->dp[j + o];
                sw -= trial->dp[j];
                sa->dp[j + o] = (sp_digit)sw;
                sw >>= SP_WORD_SIZE;
            }

            tr->dp[o] += t;
            if (tr->dp[o] < t) {
                tr->dp[o + 1]++;
            }
#endif
        }
        sa->used = i + 1;

        if (rem != NULL) {
            if (s != SP_WORD_SIZE)
                sp_rshb(sa, s, sa);
            sp_copy(sa, rem);
            sp_clamp(rem);
        }
        if (r != NULL) {
            sp_copy(tr, r);
            sp_clamp(r);
        }
    }

#ifdef WOLFSSL_SMALL_STACK
    if (sa != NULL)
        XFREE(sa, NULL, DYNAMIC_TYPE_BIGINT);
#endif

    return err;
}


#ifndef FREESCALE_LTC_TFM
/* Calculate the remainder of dividing a by m: r = a mod m.
 *
 * a  SP integer.
 * m  SP integer.
 * r  SP integer.
 * returns MP_VAL when m is 0 and MP_OKAY otherwise.
 */
int sp_mod(sp_int* a, sp_int* m, sp_int* r)
{
    return sp_div(a, m, NULL, r);
}
#endif
#endif

/* Clear all data in the big number and sets value to zero.
 *
 * a  SP integer.
 */
void sp_zero(sp_int* a)
{
    XMEMSET(a->dp, 0, a->size * sizeof(*a->dp));
    a->used = 0;
}

/* Add a one digit number to the big number.
 *
 * a  SP integer.
 * d  Digit to add.
 * r  SP integer - result.
 * returns MP_OKAY always.
 */
int sp_add_d(sp_int* a, sp_int_digit d, sp_int* r)
{
    int i = 0;
    sp_int_digit t;

    if (a == NULL || r == NULL || a->used > SP_INT_DIGITS)
        return BAD_FUNC_ARG;

    r->used = a->used;

    if (d == 0) {
        /*copy the content of <a> to <r>*/
        for (; i < a->used; i++)
            r->dp[i] = a->dp[i];

        return MP_OKAY;
    }

    if (a->used == 0) {
        r->used = 1;
        t = d;
    }
    else
        t = a->dp[0] + d;

    if (a->used != 0 && t < a->dp[0]) {
        for (++i; i < a->used; i++) {
            r->dp[i] = a->dp[i] + 1;
            if (r->dp[i] != 0) {
               break;
            }
        }
        if (i == a->used) {
            r->used++;
            if (i < SP_INT_DIGITS)
                r->dp[i] = 1;
            else
                return MP_VAL;
        }
    }
    r->dp[0] = t;
    if (r != a) {
        for (++i; i < a->used; i++)
            r->dp[i] = a->dp[i];
    }

    return MP_OKAY;
}


#if !defined(NO_DH) || defined(HAVE_ECC) || defined(WC_RSA_BLINDING) || \
    !defined(WOLFSSL_RSA_VERIFY_ONLY)
/* Left shift the big number by a number of digits.
 * WIll chop off digits overflowing maximum size.
 *
 * a  SP integer.
 * s  Number of digits to shift.
 * returns MP_OKAY always.
 */
int sp_lshd(sp_int* a, int s)
{
    if (a->used + s > a->size)
        a->used = a->size - s;

    XMEMMOVE(a->dp + s, a->dp, a->used * sizeof(sp_int_digit));
    a->used += s;
    XMEMSET(a->dp, 0, s * sizeof(sp_int_digit));
    sp_clamp(a);

    return MP_OKAY;
}
#endif

#if !defined(NO_PWDBASED) || defined(WOLFSSL_KEY_GEN) || !defined(NO_DH)
/* Add two large numbers into result: r = a + b
 *
 * a  SP integer.
 * b  SP integer.
 * r  SP integer.
 * returns MP_OKAY always.
 */
int sp_add(sp_int* a, sp_int* b, sp_int* r)
{
    int i;
    sp_int_digit c = 0;
    sp_int_digit t;

    for (i = 0; i < a->used && i < b->used; i++) {
        t = a->dp[i] + b->dp[i] + c;
        if (c == 0)
            c = t < a->dp[i];
        else
            c = t <= a->dp[i];
        r->dp[i] = t;
    }
    for (; i < a->used; i++) {
        r->dp[i] = a->dp[i] + c;
        c = (a->dp[i] != 0) && (r->dp[i] == 0);
    }
    for (; i < b->used; i++) {
        r->dp[i] = b->dp[i] + c;
        c = (b->dp[i] != 0) && (r->dp[i] == 0);
    }
    if (c != 0) {
        r->dp[i] = c;
    }
    r->used = (int)(i + c);

    return MP_OKAY;
}
#endif /* !NO_PWDBASED || WOLFSSL_KEY_GEN || !NO_DH */

#ifndef NO_RSA
/* Set a number into the big number.
 *
 * a  SP integer.
 * b  Value to set.
 * returns MP_OKAY always.
 */
int sp_set_int(sp_int* a, unsigned long b)
{
    if (b == 0) {
        a->used = 0;
        a->dp[0] = 0;
    }
    else {
        a->used = 1;
        a->dp[0] = (sp_int_digit)b;
    }

    return MP_OKAY;
}
#endif /* !NO_RSA */

#ifdef WC_MP_TO_RADIX
/* Hex string characters. */
static const char sp_hex_char[16] = {
    '0', '1', '2', '3', '4', '5', '6', '7',
    '8', '9', 'a', 'b', 'c', 'd', 'e', 'f'
};

/* Put the hex string version, big-endian, of a in str.
 *
 * a    SP integer.
 * str  Hex string is stored here.
 * returns MP_OKAY always.
 */
int sp_tohex(sp_int* a, char* str)
{
    int i, j;

    /* quick out if its zero */
    if (sp_iszero(a) == MP_YES) {
        *str++ = '0';
        *str = '\0';
    }
    else {
        i = a->used - 1;
        for (j = SP_WORD_SIZE - 4; j >= 0; j -= 4) {
            if (((a->dp[i] >> j) & 0xf) != 0)
                break;
        }
        for (; j >= 0; j -= 4)
            *(str++) = sp_hex_char[(a->dp[i] >> j) & 0xf];
        for (--i; i >= 0; i--) {
            for (j = SP_WORD_SIZE - 4; j >= 0; j -= 4)
                *(str++) = sp_hex_char[(a->dp[i] >> j) & 0xf];
        }
        *str = '\0';
    }

    return MP_OKAY;
}
#endif /* WC_MP_TO_RADIX */

#if defined(WOLFSSL_KEY_GEN) || !defined(NO_DH) && !defined(WC_NO_RNG)
/* Set a bit of a: a |= 1 << i
 * The field 'used' is updated in a.
 *
 * a  SP integer to modify.
 * i  Index of bit to set.
 * returns MP_OKAY always.
 */
int sp_set_bit(sp_int* a, int i)
{
    int ret = MP_OKAY;

    if ((a == NULL) ||  (i / SP_WORD_SIZE >= SP_INT_DIGITS)) {
        ret = BAD_FUNC_ARG;
    }
    else {
        a->dp[i/SP_WORD_SIZE] |= (sp_int_digit)1 << (i % SP_WORD_SIZE);
        if (a->used <= i / SP_WORD_SIZE)
            a->used = (i / SP_WORD_SIZE) + 1;
    }
    return ret;
}

/* Exponentiate 2 to the power of e: a = 2^e
 * This is done by setting the 'e'th bit.
 *
 * a  SP integer.
 * e  Exponent.
 * returns MP_OKAY always.
 */
int sp_2expt(sp_int* a, int e)
{
    sp_zero(a);
    return sp_set_bit(a, e);
}

/* Generate a random prime for RSA only.
 *
 * r     SP integer
 * len   Number of bytes to prime.
 * rng   Random number generator.
 * heap  Unused
 * returns MP_OKAY on success and MP_VAL when length is not supported or random
 *         number genrator fails.
 */
int sp_rand_prime(sp_int* r, int len, WC_RNG* rng, void* heap)
{
    static const int USE_BBS = 1;
    int   err = 0, type;
    int   isPrime = MP_NO;

    (void)heap;

    /* get type */
    if (len < 0) {
        type = USE_BBS;
        len = -len;
    }
    else {
        type = 0;
    }

#if defined(WOLFSSL_HAVE_SP_DH) && defined(WOLFSSL_KEY_GEN)
    if (len == 32) {
    }
    else
#endif
    /* Generate RSA primes that are half the modulus length. */
#ifndef WOLFSSL_SP_NO_3072
    if (len != 128 && len != 192)
#else
    if (len != 128)
#endif
    {
        err = MP_VAL;
    }

    r->used = len / (SP_WORD_SIZE / 8);

    /* Assume the candidate is probably prime and then test until
     * it is proven composite. */
    while (err == 0 && isPrime == MP_NO) {
#ifdef SHOW_GEN
        printf(".");
        fflush(stdout);
#endif
        /* generate value */
        err = wc_RNG_GenerateBlock(rng, (byte*)r->dp, len);
        if (err != 0) {
            err = MP_VAL;
            break;
        }

        /* munge bits */
        ((byte*)r->dp)[len-1] |= 0x80 | 0x40;
        r->dp[0]              |= 0x01 | ((type & USE_BBS) ? 0x02 : 0x00);

        /* test */
        /* Running Miller-Rabin up to 3 times gives us a 2^{-80} chance
         * of a 1024-bit candidate being a false positive, when it is our
         * prime candidate. (Note 4.49 of Handbook of Applied Cryptography.)
         * Using 8 because we've always used 8 */
        sp_prime_is_prime_ex(r, 8, &isPrime, rng);
    }

    return err;
}

/* Multiply a by b and store in r: r = a * b
 *
 * a  SP integer to multiply.
 * b  SP integer to multiply.
 * r  SP integer result.
 * returns MP_OKAY always.
 */
int sp_mul(sp_int* a, sp_int* b, sp_int* r)
{
    int err = MP_OKAY;
    int i;
#ifdef WOLFSSL_SMALL_STACK
    sp_int* t = NULL;
    sp_int* tr;
#else
    sp_int t[1];
    sp_int tr[1];
#endif

    /* Need extra digit during calculation. */
    if (a->used + b->used > (SP_INT_DIGITS - 1))
        err = MP_VAL;

#ifdef WOLFSSL_SMALL_STACK
    if (err == MP_OKAY) {
        t = (sp_int*)XMALLOC(sizeof(sp_int) * 2, NULL, DYNAMIC_TYPE_BIGINT);
        if (t == NULL)
            err = MP_MEM;
        else
            tr = &t[1];
    }
#endif

    if (err == MP_OKAY) {
        sp_init(t);
        sp_init(tr);

        for (i = 0; i < b->used; i++) {
            _sp_mul_d(a, b->dp[i], t, i);
            sp_add(tr, t, tr);
        }
        sp_copy(tr, r);
    }

#ifdef WOLFSSL_SMALL_STACK
    if (t != NULL)
        XFREE(t, NULL, DYNAMIC_TYPE_BIGINT);
#endif

    return err;
}

/* Square a mod m and store in r: r = (a * a) mod m
 *
 * a  SP integer to square.
 * m  SP integer modulus.
 * r  SP integer result.
 * returns MP_VAL when m is 0, MP_MEM when dynamic memory allocation fails,
 *         BAD_FUNC_ARG when a is to big and MP_OKAY otherwise.
 */
static int sp_sqrmod(sp_int* a, sp_int* m, sp_int* r)
{
    int err = MP_OKAY;

    /* Need extra digit during calculation. */
    if (a->used * 2 > (SP_INT_DIGITS - 1))
        err = MP_VAL;

    if (err == MP_OKAY)
        err = sp_mul(a, a, r);
    if (err == MP_OKAY)
        err = sp_mod(r, m, r);

    return err;
}

#if defined(WOLFSSL_HAVE_SP_DH) || defined(WOLFSSL_KEY_GEN)
/* Multiply a by b mod m and store in r: r = (a * b) mod m
 *
 * a  SP integer to multiply.
 * b  SP integer to multiply.
 * m  SP integer modulus.
 * r  SP integer result.
 * returns MP_VAL when m is 0, MP_MEM when dynamic memory allocation fails and
 *         MP_OKAY otherwise.
 */
int sp_mulmod(sp_int* a, sp_int* b, sp_int* m, sp_int* r)
{
    int err = MP_OKAY;
#ifdef WOLFSSL_SMALL_STACK
    sp_int* t = NULL;
#else
    sp_int t[1];
#endif

    /* Need extra digit during calculation. */
    if (a->used + b->used > (SP_INT_DIGITS - 1))
        err = MP_VAL;

#ifdef WOLFSSL_SMALL_STACK
    if (err == MP_OKAY) {
        t = (sp_int*)XMALLOC(sizeof(sp_int), NULL, DYNAMIC_TYPE_BIGINT);
        if (t == NULL) {
            err = MP_MEM;
        }
    }
#endif
    if (err == MP_OKAY) {
        err = sp_mul(a, b, t);
    }
    if (err == MP_OKAY) {
        err = sp_mod(t, m, r);
    }

#ifdef WOLFSSL_SMALL_STACK
    if (t != NULL)
        XFREE(t, NULL, DYNAMIC_TYPE_BIGINT);
#endif
    return err;
}
#endif

/* Calculate a modulo the digit d into r: r = a mod d
 *
 * a  SP integer to square.
 * d  SP integer digit, modulus.
 * r  SP integer digit, result.
 * returns MP_VAL when d is 0 and MP_OKAY otherwise.
 */
static int sp_mod_d(sp_int* a, const sp_int_digit d, sp_int_digit* r)
{
    int err = MP_OKAY;
    int i;
    sp_int_word w = 0;
    sp_int_digit t;

    if (d == 0)
        err = MP_VAL;

    if (err == MP_OKAY) {
        for (i = a->used - 1; i >= 0; i--) {
            w = (w << SP_WORD_SIZE) | a->dp[i];
            t = (sp_int_digit)(w / d);
            w -= (sp_int_word)t * d;
        }

        *r = (sp_int_digit)w;
    }

    return err;
}

/* Calculates the Greatest Common Denominator (GCD) of a and b into r.
 *
 * a  SP integer operand.
 * b  SP integer operand.
 * r  SP integer result.
 * returns MP_MEM when dynamic memory allocation fails and MP_OKAY otherwise.
 */
int sp_gcd(sp_int* a, sp_int* b, sp_int* r)
{
    int err = MP_OKAY;
#ifdef WOLFSSL_SMALL_STACK
    sp_int* u = NULL;
    sp_int* v;
    sp_int* t;
#else
    sp_int u[1], v[1], t[1];
#endif

    if (sp_iszero(a))
        sp_copy(b, r);
    else if (sp_iszero(b))
        sp_copy(a, r);
    else {
#ifdef WOLFSSL_SMALL_STACK
        u = (sp_int*)XMALLOC(sizeof(sp_int) * 3, NULL, DYNAMIC_TYPE_BIGINT);
        if (u == NULL)
            err = MP_MEM;
        else {
            v = &u[1];
            t = &u[2];
        }
#endif

        if (err == MP_OKAY) {
            sp_init(u);
            sp_init(v);
            sp_init(t);

            if (sp_cmp(a, b) != MP_LT) {
                sp_copy(b, u);
                /* First iteration - u = a, v = b */
                if (b->used == 1) {
                    err = sp_mod_d(a, b->dp[0], &v->dp[0]);
                    if (err == MP_OKAY)
                        v->used = (v->dp[0] != 0);
                }
                else
                    err = sp_mod(a, b, v);
            }
            else {
                sp_copy(a, u);
                /* First iteration - u = b, v = a */
                if (a->used == 1) {
                    err = sp_mod_d(b, a->dp[0], &v->dp[0]);
                    if (err == MP_OKAY)
                        v->used = (v->dp[0] != 0);
                }
                else
                    err = sp_mod(b, a, v);
            }
        }

        if (err == MP_OKAY) {
            while (!sp_iszero(v)) {
                if (v->used == 1) {
                    sp_mod_d(u, v->dp[0], &t->dp[0]);
                    t->used = (t->dp[0] != 0);
                }
                else
                    sp_mod(u, v, t);
                sp_copy(v, u);
                sp_copy(t, v);
            }
            sp_copy(u, r);
        }
    }

#ifdef WOLFSSL_SMALL_STACK
    if (u != NULL)
        XFREE(u, NULL, DYNAMIC_TYPE_BIGINT);
#endif

    return err;
}

/* Divides a by 2 and stores in r: r = a >> 1
 *
 * a  SP integer to divide.
 * r  SP integer result.
 * returns MP_OKAY always.
 */
static int sp_div_2(sp_int* a, sp_int* r)
{
    int i;

    for (i = 0; i < a->used-1; i++)
        r->dp[i] = (a->dp[i] >> 1) | (a->dp[i+1] << (SP_WORD_SIZE - 1));
    r->dp[i] = a->dp[i] >> 1;
    r->used = i + 1;
    sp_clamp(r);

    return MP_OKAY;
}


/* Calculates the multiplicative inverse in the field.
 *
 * a  SP integer to invert.
 * m  SP integer that is the modulus of the field.
 * r  SP integer result.
 * returns MP_VAL when a or m is 0, MP_MEM when dynamic memory allocation fails
 *         and MP_OKAY otherwise.
 */
int sp_invmod(sp_int* a, sp_int* m, sp_int* r)
{
    int err = MP_OKAY;
#ifdef WOLFSSL_SMALL_STACK
    sp_int* u = NULL;
    sp_int* v;
    sp_int* b;
    sp_int* c;
#else
    sp_int u[1], v[1], b[1], c[1];
#endif

#ifdef WOLFSSL_SMALL_STACK
    u = (sp_int*)XMALLOC(sizeof(sp_int) * 4, NULL, DYNAMIC_TYPE_BIGINT);
    if (u == NULL) {
        err = MP_MEM;
    }
#endif

    if (err == MP_OKAY) {
#ifdef WOLFSSL_SMALL_STACK
        v = &u[1];
        b = &u[2];
        c = &u[3];
#endif
        sp_init(v);

        if (sp_cmp(a, m) != MP_LT) {
            err = sp_mod(a, m, v);
            a = v;
        }
    }

    /* 0 != n*m + 1 (+ve m), r*a mod 0 is always 0 (never 1)  */
    if ((err == MP_OKAY) && (sp_iszero(a) || sp_iszero(m))) {
        err = MP_VAL;
    }
    /* r*2*x != n*2*y + 1  */
    if ((err == MP_OKAY) && sp_iseven(a) && sp_iseven(m)) {
        err = MP_VAL;
    }

    /* 1*1 = 0*m + 1  */
    if ((err == MP_OKAY) && sp_isone(a)) {
        sp_set(r, 1);
    }
    else if (err != MP_OKAY) {
    }
    else if (sp_iseven(m)) {
        /* a^-1 mod m = m + (1 - m*(m^-1 % a)) / a
         *            = m - (m*(m^-1 % a) - 1) / a
         */
        err = sp_invmod(m, a, r);
        if (err == MP_OKAY) {
            err = sp_mul(r, m, r);
        }
        if (err == MP_OKAY) {
            sp_sub_d(r, 1, r);
            sp_div(r, a, r, NULL);
            sp_sub(m, r, r);
        }
    }
    else {
        if (err == MP_OKAY) {
            sp_init(u);
            sp_init(b);
            sp_init(c);

            sp_copy(m, u);
            sp_copy(a, v);
            sp_zero(b);
            sp_set(c, 1);

            while (!sp_isone(v) && !sp_iszero(u)) {
                if (sp_iseven(u)) {
                    sp_div_2(u, u);
                    if (sp_isodd(b)) {
                        sp_add(b, m, b);
                    }
                    sp_div_2(b, b);
                }
                else if (sp_iseven(v)) {
                    sp_div_2(v, v);
                    if (sp_isodd(c)) {
                        sp_add(c, m, c);
                    }
                    sp_div_2(c, c);
                }
                else if (sp_cmp(u, v) != MP_LT) {
                    sp_sub(u, v, u);
                    if (sp_cmp(b, c) == MP_LT) {
                        sp_add(b, m, b);
                    }
                    sp_sub(b, c, b);
                }
                else {
                    sp_sub(v, u, v);
                    if (sp_cmp(c, b) == MP_LT) {
                        sp_add(c, m, c);
                    }
                    sp_sub(c, b, c);
                }
            }
            if  (sp_iszero(u)) {
                err = MP_VAL;
            }
            else {
                sp_copy(c, r);
            }
        }
    }

#ifdef WOLFSSL_SMALL_STACK
    if (u != NULL) {
        XFREE(u, NULL, DYNAMIC_TYPE_BIGINT);
    }
#endif

    return err;
}

/* Calculates the Lowest Common Multiple (LCM) of a and b and stores in r.
 *
 * a  SP integer operand.
 * b  SP integer operand.
 * r  SP integer result.
 * returns MP_MEM when dynamic memory allocation fails and MP_OKAY otherwise.
 */
int sp_lcm(sp_int* a, sp_int* b, sp_int* r)
{
    int     err = MP_OKAY;
#ifndef WOLFSSL_SMALL_STACK
    sp_int  t[2];
#else
    sp_int  *t = NULL;
#endif

#ifdef WOLFSSL_SMALL_STACK
    t = (sp_int*)XMALLOC(sizeof(sp_int) * 2, NULL, DYNAMIC_TYPE_BIGINT);
    if (t == NULL) {
        err = MP_MEM;
    }
#endif

    if (err == MP_OKAY) {
        sp_init(&t[0]);
        sp_init(&t[1]);
        err = sp_gcd(a, b, &t[0]);
        if (err == MP_OKAY) {
            if (sp_cmp(a, b) == MP_GT) {
                err = sp_div(a, &t[0], &t[1], NULL);
                if (err == MP_OKAY)
                    err = sp_mul(b, &t[1], r);
            }
            else {
                err = sp_div(b, &t[0], &t[1], NULL);
                if (err == MP_OKAY)
                    err = sp_mul(a, &t[1], r);
            }
        }
    }

#ifdef WOLFSSL_SMALL_STACK
    if (t != NULL)
        XFREE(t, NULL, DYNAMIC_TYPE_BIGINT);
#endif
    return err;
}

/* Exponentiates b to the power of e modulo m into r: r = b ^ e mod m
 *
 * b  SP integer base.
 * e  SP integer exponent.
 * m  SP integer modulus.
 * r  SP integer result.
 * returns MP_VAL when m is not 1024, 2048, 1536 or 3072 bits and otherwise
 *         MP_OKAY.
 */
int sp_exptmod(sp_int* b, sp_int* e, sp_int* m, sp_int* r)
{
    int err = MP_OKAY;
    int done = 0;
    int mBits = sp_count_bits(m);
    int bBits = sp_count_bits(b);
    int eBits = sp_count_bits(e);

    if (sp_iszero(m)) {
        err = MP_VAL;
    }
    else if (sp_isone(m)) {
        sp_set(r, 0);
        done = 1;
    }
    else if (sp_iszero(e)) {
        sp_set(r, 1);
        done = 1;
    }
    else if (sp_iszero(b)) {
        sp_set(r, 0);
        done = 1;
    }
    /* Ensure SP integers have space for intermediate values. */
    else if (m->used * 2 > (SP_INT_DIGITS - 1)) {
        err = BAD_FUNC_ARG;
    }

    if (!done && (err == MP_OKAY)) {
#ifndef WOLFSSL_SP_NO_2048
        if ((mBits == 1024) && sp_isodd(m) && (bBits <= 1024) &&
            (eBits <= 1024)) {
            err = sp_ModExp_1024(b, e, m, r);
            done = 1;
        }
        else if ((mBits == 2048) && sp_isodd(m) && (bBits <= 2048) &&
                 (eBits <= 2048)) {
            err = sp_ModExp_2048(b, e, m, r);
            done = 1;
        }
        else
#endif
#ifndef WOLFSSL_SP_NO_3072
        if ((mBits == 1536) && sp_isodd(m) && (bBits <= 1536) &&
            (eBits <= 1536)) {
            err = sp_ModExp_1536(b, e, m, r);
            done = 1;
        }
        else if ((mBits == 3072) && sp_isodd(m) && (bBits <= 3072) &&
                 (eBits <= 3072)) {
            err = sp_ModExp_3072(b, e, m, r);
            done = 1;
        }
        else
#endif
#ifdef WOLFSSL_SP_4096
        if ((mBits == 4096) && sp_isodd(m) && (bBits <= 4096) &&
            (eBits <= 4096)) {
            err = sp_ModExp_4096(b, e, m, r);
            done = 1;
        }
        else
#endif
        {
        }
    }
#if defined(WOLFSSL_HAVE_SP_DH) && defined(WOLFSSL_KEY_GEN)
    if (!done && (err == MP_OKAY)) {
        int i;

    #ifdef WOLFSSL_SMALL_STACK
        sp_int* t = NULL;
    #else
        sp_int t[1];
    #endif

    #ifdef WOLFSSL_SMALL_STACK
        if (!done && (err == MP_OKAY)) {
            t = (sp_int*)XMALLOC(sizeof(sp_int), NULL, DYNAMIC_TYPE_BIGINT);
            if (t == NULL) {
                err = MP_MEM;
            }
        }
    #endif
        if (!done && (err == MP_OKAY)) {
            sp_init(t);

            if (sp_cmp(b, m) != MP_LT) {
                err = sp_mod(b, m, t);
                if (err == MP_OKAY && sp_iszero(t)) {
                    sp_set(r, 0);
                    done = 1;
                }
            }
            else {
                sp_copy(b, t);
            }

            if (!done && (err == MP_OKAY)) {
                for (i = eBits-2; err == MP_OKAY && i >= 0; i--) {
                     err = sp_sqrmod(t, m, t);
                     if (err == MP_OKAY && (e->dp[i / SP_WORD_SIZE] >>
                                                      (i % SP_WORD_SIZE)) & 1) {
                         err = sp_mulmod(t, b, m, t);
                     }
                 }
             }
        }
        if (!done && (err == MP_OKAY)) {
            sp_copy(t, r);
        }

    #ifdef WOLFSSL_SMALL_STACK
        if (t != NULL) {
            XFREE(t, NULL, DYNAMIC_TYPE_BIGINT);
        }
    #endif
    }
#else
    if (!done && (err == MP_OKAY)) {
        err = MP_VAL;
    }
#endif

    (void)mBits;
    (void)bBits;
    (void)eBits;

    return err;
}


/* Number of entries in array of number of least significant zero bits. */
#define SP_LNZ_CNT      16
/* Number of bits the array checks. */
#define SP_LNZ_BITS     4
/* Mask to apply to check with array. */
#define SP_LNZ_MASK     0xf
/* Number of least significant zero bits in first SP_LNZ_CNT numbers. */
static const int lnz[SP_LNZ_CNT] = {
   4, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0
};

/* Count the number of least significant zero bits.
 *
 * a  Number to check
 * returns the count of least significant zero bits.
 */
static int sp_cnt_lsb(sp_int* a)
{
    int i, j;
    int cnt = 0;
    int bc = 0;

    if (!sp_iszero(a)) {
        for (i = 0; i < a->used && a->dp[i] == 0; i++, cnt += SP_WORD_SIZE) {
        }

        for (j = 0; j < SP_WORD_SIZE; j += SP_LNZ_BITS) {
            bc = lnz[(a->dp[i] >> j) & SP_LNZ_MASK];
            if (bc != 4) {
                bc += cnt + j;
                break;
            }
        }
    }

    return bc;
}

/* Miller-Rabin test of "a" to the base of "b" as described in
 * HAC pp. 139 Algorithm 4.24
 *
 * Sets result to 0 if definitely composite or 1 if probably prime.
 * Randomly the chance of error is no more than 1/4 and often
 * very much lower.
 *
 * a       SP integer to check.
 * b       SP integer small prime.
 * result  Whether a is likely prime: MP_YES or MP_NO.
 * n1      SP integer operand.
 * y       SP integer operand.
 * r       SP integer operand.
 * returns MP_VAL when a is not 1024, 2048, 1536 or 3072 and MP_OKAY otherwise.
 */
static int sp_prime_miller_rabin_ex(sp_int * a, sp_int * b, int *result,
  sp_int *n1, sp_int *y, sp_int *r)
{
    int s, j;
    int err = MP_OKAY;

    /* default */
    *result = MP_NO;

    /* ensure b > 1 */
    if (sp_cmp_d(b, 1) == MP_GT) {
        /* get n1 = a - 1 */
        sp_copy(a, n1);
        sp_sub_d(n1, 1, n1);
        /* set 2**s * r = n1 */
        sp_copy(n1, r);

        /* count the number of least significant bits
         * which are zero
         */
        s = sp_cnt_lsb(r);

        /* now divide n - 1 by 2**s */
        sp_rshb(r, s, r);

        /* compute y = b**r mod a */
        sp_zero(y);

        err = sp_exptmod(b, r, a, y);

        if (err == MP_OKAY) {
            /* probably prime until shown otherwise */
            *result = MP_YES;

            /* if y != 1 and y != n1 do */
            if (sp_cmp_d(y, 1) != MP_EQ && sp_cmp(y, n1) != MP_EQ) {
                j = 1;
                /* while j <= s-1 and y != n1 */
                while ((j <= (s - 1)) && sp_cmp(y, n1) != MP_EQ) {
                    sp_sqrmod(y, a, y);

                    /* if y == 1 then composite */
                    if (sp_cmp_d(y, 1) == MP_EQ) {
                        *result = MP_NO;
                        break;
                    }
                    ++j;
                }

                /* if y != n1 then composite */
                if (*result == MP_YES && sp_cmp(y, n1) != MP_EQ)
                    *result = MP_NO;
            }
        }
    }

    return err;
}

/* Miller-Rabin test of "a" to the base of "b" as described in
 * HAC pp. 139 Algorithm 4.24
 *
 * Sets result to 0 if definitely composite or 1 if probably prime.
 * Randomly the chance of error is no more than 1/4 and often
 * very much lower.
 *
 * a       SP integer to check.
 * b       SP integer small prime.
 * result  Whether a is likely prime: MP_YES or MP_NO.
 * returns MP_MEM when dynamic memory allocation fails, MP_VAL when a is not
 *         1024, 2048, 1536 or 3072 and MP_OKAY otherwise.
 */
static int sp_prime_miller_rabin(sp_int * a, sp_int * b, int *result)
{
    int err = MP_OKAY;
#ifndef WOLFSSL_SMALL_STACK
    sp_int  n1[1], y[1], r[1];
#else
    sp_int *n1 = NULL, *y, *r;
#endif

#ifdef WOLFSSL_SMALL_STACK
    n1 = (sp_int*)XMALLOC(sizeof(sp_int) * 3, NULL, DYNAMIC_TYPE_BIGINT);
    if (n1 == NULL)
        err = MP_MEM;
    else {
        y = &n1[1];
        r = &n1[2];
    }
#endif

    if (err == MP_OKAY) {
        sp_init(n1);
        sp_init(y);
        sp_init(r);

        err = sp_prime_miller_rabin_ex(a, b, result, n1, y, r);

        sp_clear(n1);
        sp_clear(y);
        sp_clear(r);
    }

#ifdef WOLFSSL_SMALL_STACK
    if (n1 != NULL)
        XFREE(n1, NULL, DYNAMIC_TYPE_BIGINT);
#endif

    return err;
}

/* Number of pre-computed primes. First n primes. */
#define SP_PRIME_SIZE      256

/* a few primes */
static const sp_int_digit primes[SP_PRIME_SIZE] = {
    0x0002, 0x0003, 0x0005, 0x0007, 0x000B, 0x000D, 0x0011, 0x0013,
    0x0017, 0x001D, 0x001F, 0x0025, 0x0029, 0x002B, 0x002F, 0x0035,
    0x003B, 0x003D, 0x0043, 0x0047, 0x0049, 0x004F, 0x0053, 0x0059,
    0x0061, 0x0065, 0x0067, 0x006B, 0x006D, 0x0071, 0x007F, 0x0083,
    0x0089, 0x008B, 0x0095, 0x0097, 0x009D, 0x00A3, 0x00A7, 0x00AD,
    0x00B3, 0x00B5, 0x00BF, 0x00C1, 0x00C5, 0x00C7, 0x00D3, 0x00DF,
    0x00E3, 0x00E5, 0x00E9, 0x00EF, 0x00F1, 0x00FB, 0x0101, 0x0107,
    0x010D, 0x010F, 0x0115, 0x0119, 0x011B, 0x0125, 0x0133, 0x0137,

    0x0139, 0x013D, 0x014B, 0x0151, 0x015B, 0x015D, 0x0161, 0x0167,
    0x016F, 0x0175, 0x017B, 0x017F, 0x0185, 0x018D, 0x0191, 0x0199,
    0x01A3, 0x01A5, 0x01AF, 0x01B1, 0x01B7, 0x01BB, 0x01C1, 0x01C9,
    0x01CD, 0x01CF, 0x01D3, 0x01DF, 0x01E7, 0x01EB, 0x01F3, 0x01F7,
    0x01FD, 0x0209, 0x020B, 0x021D, 0x0223, 0x022D, 0x0233, 0x0239,
    0x023B, 0x0241, 0x024B, 0x0251, 0x0257, 0x0259, 0x025F, 0x0265,
    0x0269, 0x026B, 0x0277, 0x0281, 0x0283, 0x0287, 0x028D, 0x0293,
    0x0295, 0x02A1, 0x02A5, 0x02AB, 0x02B3, 0x02BD, 0x02C5, 0x02CF,

    0x02D7, 0x02DD, 0x02E3, 0x02E7, 0x02EF, 0x02F5, 0x02F9, 0x0301,
    0x0305, 0x0313, 0x031D, 0x0329, 0x032B, 0x0335, 0x0337, 0x033B,
    0x033D, 0x0347, 0x0355, 0x0359, 0x035B, 0x035F, 0x036D, 0x0371,
    0x0373, 0x0377, 0x038B, 0x038F, 0x0397, 0x03A1, 0x03A9, 0x03AD,
    0x03B3, 0x03B9, 0x03C7, 0x03CB, 0x03D1, 0x03D7, 0x03DF, 0x03E5,
    0x03F1, 0x03F5, 0x03FB, 0x03FD, 0x0407, 0x0409, 0x040F, 0x0419,
    0x041B, 0x0425, 0x0427, 0x042D, 0x043F, 0x0443, 0x0445, 0x0449,
    0x044F, 0x0455, 0x045D, 0x0463, 0x0469, 0x047F, 0x0481, 0x048B,

    0x0493, 0x049D, 0x04A3, 0x04A9, 0x04B1, 0x04BD, 0x04C1, 0x04C7,
    0x04CD, 0x04CF, 0x04D5, 0x04E1, 0x04EB, 0x04FD, 0x04FF, 0x0503,
    0x0509, 0x050B, 0x0511, 0x0515, 0x0517, 0x051B, 0x0527, 0x0529,
    0x052F, 0x0551, 0x0557, 0x055D, 0x0565, 0x0577, 0x0581, 0x058F,
    0x0593, 0x0595, 0x0599, 0x059F, 0x05A7, 0x05AB, 0x05AD, 0x05B3,
    0x05BF, 0x05C9, 0x05CB, 0x05CF, 0x05D1, 0x05D5, 0x05DB, 0x05E7,
    0x05F3, 0x05FB, 0x0607, 0x060D, 0x0611, 0x0617, 0x061F, 0x0623,
    0x062B, 0x062F, 0x063D, 0x0641, 0x0647, 0x0649, 0x064D, 0x0653
};


/* Check whether a is prime.
 * Checks against a number of small primes and does t iterations of
 * Miller-Rabin.
 *
 * a       SP integer to check.
 * t       Number of iterations of Muller-Rabin to perform.
 * result  MP_YES when prime.
 *         MP_NO when not prime.
 * returns MP_VAL when t is out of range, MP_MEM when dynamic memory allocation
 *         fails and otherwise MP_OKAY.
 */
int sp_prime_is_prime(sp_int *a, int t, int* result)
{
    int         err = MP_OKAY;
    int         i;
    int         haveRes = 0;
#ifndef WOLFSSL_SMALL_STACK
    sp_int      b[1];
#else
    sp_int      *b = NULL;
#endif
    sp_int_digit d;

    if (t <= 0 || t > SP_PRIME_SIZE) {
        *result = MP_NO;
        err = MP_VAL;
    }

    if (sp_isone(a)) {
        *result = MP_NO;
        return MP_OKAY;
    }

    if (err == MP_OKAY && a->used == 1) {
        /* check against primes table */
        for (i = 0; i < SP_PRIME_SIZE; i++) {
            if (sp_cmp_d(a, primes[i]) == MP_EQ) {
                *result = MP_YES;
                haveRes = 1;
                break;
            }
        }
    }

    if (err == MP_OKAY && !haveRes) {
        /* do trial division */
        for (i = 0; i < SP_PRIME_SIZE; i++) {
            err = sp_mod_d(a, primes[i], &d);
            if (err != MP_OKAY || d == 0) {
                *result = MP_NO;
                haveRes = 1;
                break;
            }
        }
    }

#ifdef WOLFSSL_SMALL_STACK
    if (err == MP_OKAY && !haveRes) {
        b = (sp_int*)XMALLOC(sizeof(sp_int), NULL, DYNAMIC_TYPE_BIGINT);
        if (b == NULL)
            err = MP_MEM;
    }
#endif

    if (err == MP_OKAY && !haveRes) {
        /* now do 't' miller rabins */
        sp_init(b);
        for (i = 0; i < t; i++) {
            sp_set(b, primes[i]);
            err = sp_prime_miller_rabin(a, b, result);
            if (err != MP_OKAY || *result == MP_NO)
                break;
        }
    }

#ifdef WOLFSSL_SMALL_STACK
     if (b != NULL)
         XFREE(b, NULL, DYNAMIC_TYPE_BIGINT);
#endif

     return err;
}

/* Check whether a is prime.
 * Checks against a number of small primes and does t iterations of
 * Miller-Rabin.
 *
 * a       SP integer to check.
 * t       Number of iterations of Muller-Rabin to perform.
 * result  MP_YES when prime.
 *         MP_NO when not prime.
 * rng     Random number generator.
 * returns MP_VAL when t is out of range, MP_MEM when dynamic memory allocation
 *         fails and otherwise MP_OKAY.
 */
int sp_prime_is_prime_ex(sp_int* a, int t, int* result, WC_RNG* rng)
{
    int err = MP_OKAY;
    int ret = MP_YES;
    int haveRes = 0;
    int i;
#ifndef WC_NO_RNG
    #ifndef WOLFSSL_SMALL_STACK
        sp_int b[1], c[1], n1[1], y[1], r[1];
    #else
        sp_int *b = NULL, *c = NULL, *n1 = NULL, *y = NULL, *r = NULL;
    #endif
    word32 baseSz;
#endif

    if (a == NULL || result == NULL || rng == NULL)
        err = MP_VAL;

    if (sp_isone(a)) {
        *result = MP_NO;
        return MP_OKAY;
    }

    if (err == MP_OKAY && a->used == 1) {
        /* check against primes table */
        for (i = 0; i < SP_PRIME_SIZE; i++) {
            if (sp_cmp_d(a, primes[i]) == MP_EQ) {
                ret = MP_YES;
                haveRes = 1;
                break;
            }
        }
    }

    if (err == MP_OKAY && !haveRes) {
        sp_int_digit d;

        /* do trial division */
        for (i = 0; i < SP_PRIME_SIZE; i++) {
            err = sp_mod_d(a, primes[i], &d);
            if (err != MP_OKAY || d == 0) {
                ret = MP_NO;
                haveRes = 1;
                break;
            }
        }
    }

#ifndef WC_NO_RNG
    /* now do a miller rabin with up to t random numbers, this should
     * give a (1/4)^t chance of a false prime. */
    #ifdef WOLFSSL_SMALL_STACK
    if (err == MP_OKAY && !haveRes) {
        b = (sp_int*)XMALLOC(sizeof(sp_int) * 5, NULL, DYNAMIC_TYPE_BIGINT);
        if (b == NULL) {
            err = MP_MEM;
        }
        else {
            c = &b[1]; n1 = &b[2]; y= &b[3]; r = &b[4];
        }
    }
    #endif

    if (err == MP_OKAY && !haveRes) {
        sp_init(b);
        sp_init(c);
        sp_init(n1);
        sp_init(y);
        sp_init(r);

        err = sp_sub_d(a, 2, c);
    }

    if (err == MP_OKAY && !haveRes) {
        baseSz = (sp_count_bits(a) + 7) / 8;

        while (t > 0) {
            err = wc_RNG_GenerateBlock(rng, (byte*)b->dp, baseSz);
            if (err != MP_OKAY)
                break;
            b->used = a->used;

            if (sp_cmp_d(b, 2) != MP_GT || sp_cmp(b, c) != MP_LT)
                continue;

            err = sp_prime_miller_rabin_ex(a, b, &ret, n1, y, r);
            if (err != MP_OKAY || ret == MP_NO)
                break;

            t--;
        }

        sp_clear(n1);
        sp_clear(y);
        sp_clear(r);
        sp_clear(b);
        sp_clear(c);
    }

    #ifdef WOLFSSL_SMALL_STACK
    if (b != NULL)
        XFREE(b, NULL, DYNAMIC_TYPE_BIGINT);
    #endif
#else
    (void)t;
#endif /* !WC_NO_RNG */

    *result = ret;
    return err;
}

#ifndef NO_DH
int sp_exch(sp_int* a, sp_int* b)
{
    int err = MP_OKAY;
#ifndef WOLFSSL_SMALL_STACK
    sp_int  t[1];
#else
    sp_int *t = NULL;
#endif

#ifdef WOLFSSL_SMALL_STACK
   t = (sp_int*)XMALLOC(sizeof(sp_int), NULL, DYNAMIC_TYPE_BIGINT);
   if (t == NULL)
       err = MP_MEM;
#endif

    if (err == MP_OKAY) {
        *t = *a;
        *a = *b;
        *b = *t;
    }

#ifdef WOLFSSL_SMALL_STACK
    if (t != NULL)
        XFREE(t, NULL, DYNAMIC_TYPE_BIGINT);
#endif
    return MP_OKAY;
}
#endif
#endif

#if defined(WOLFSSL_KEY_GEN) && !defined(NO_RSA)
/* Multiply a by digit n and put result into r. r = a * n
 *
 * a  SP integer to be multiplied.
 * n  Number to multiply by.
 * r  SP integer result.
 * returns MP_OKAY always.
 */
int sp_mul_d(sp_int* a, sp_int_digit n, sp_int* r)
{
    _sp_mul_d(a, n, r, 0);
    return MP_OKAY;
}
#endif

/* Returns the run time settings.
 *
 * returns the settings value.
 */
word32 CheckRunTimeSettings(void)
{
    return CTC_SETTINGS;
}

#endif /* WOLFSSL_SP_MATH */
