/* sp.c
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

#ifdef HAVE_CONFIG_H
    #include <config.h>
#endif

#include <wolfssl/wolfcrypt/settings.h>
#include <wolfssl/wolfcrypt/error-crypt.h>
#include <wolfssl/wolfcrypt/cpuid.h>
#ifdef NO_INLINE
    #include <wolfssl/wolfcrypt/misc.h>
#else
    #define WOLFSSL_MISC_INCLUDED
    #include <wolfcrypt/src/misc.c>
#endif

#if defined(WOLFSSL_HAVE_SP_RSA) || defined(WOLFSSL_HAVE_SP_DH) || \
                                    defined(WOLFSSL_HAVE_SP_ECC)

#ifdef RSA_LOW_MEM
#ifndef SP_RSA_PRIVATE_EXP_D
#define SP_RSA_PRIVATE_EXP_D
#endif

#ifndef WOLFSSL_SP_SMALL
#define WOLFSSL_SP_SMALL
#endif
#endif

#include <wolfssl/wolfcrypt/sp.h>

#ifndef WOLFSSL_SP_ASM
#if SP_WORD_SIZE == 64
#if ((!defined(WC_NO_CACHE_RESISTANT) && \
      (defined(WOLFSSL_HAVE_SP_RSA) || defined(WOLFSSL_HAVE_SP_DH))) || \
     defined(WOLFSSL_SP_SMALL)) && \
    (defined(WOLFSSL_HAVE_SP_ECC) || !defined(WOLFSSL_RSA_PUBLIC_ONLY))
/* Mask for address to obfuscate which of the two address will be used. */
static const size_t addr_mask[2] = { 0, (size_t)-1 };
#endif

#if defined(WOLFSSL_SP_NONBLOCK) && (!defined(WOLFSSL_SP_NO_MALLOC) || !defined(WOLFSSL_SP_SMALL))
    #error SP non-blocking requires small and no-malloc (WOLFSSL_SP_SMALL and WOLFSSL_SP_NO_MALLOC)
#endif

#if defined(WOLFSSL_HAVE_SP_RSA) || defined(WOLFSSL_HAVE_SP_DH)
#ifndef WOLFSSL_SP_NO_2048
/* Read big endian unsigned byte array into r.
 *
 * r  A single precision integer.
 * size  Maximum number of bytes to convert
 * a  Byte array.
 * n  Number of bytes in array to read.
 */
static void sp_2048_from_bin(sp_digit* r, int size, const byte* a, int n)
{
    int i, j = 0;
    word32 s = 0;

    r[0] = 0;
    for (i = n-1; i >= 0; i--) {
        r[j] |= (((sp_digit)a[i]) << s);
        if (s >= 49U) {
            r[j] &= 0x1ffffffffffffffL;
            s = 57U - s;
            if (j + 1 >= size) {
                break;
            }
            r[++j] = (sp_digit)a[i] >> s;
            s = 8U - s;
        }
        else {
            s += 8U;
        }
    }

    for (j++; j < size; j++) {
        r[j] = 0;
    }
}

/* Convert an mp_int to an array of sp_digit.
 *
 * r  A single precision integer.
 * size  Maximum number of bytes to convert
 * a  A multi-precision integer.
 */
static void sp_2048_from_mp(sp_digit* r, int size, const mp_int* a)
{
#if DIGIT_BIT == 57
    int j;

    XMEMCPY(r, a->dp, sizeof(sp_digit) * a->used);

    for (j = a->used; j < size; j++) {
        r[j] = 0;
    }
#elif DIGIT_BIT > 57
    int i, j = 0;
    word32 s = 0;

    r[0] = 0;
    for (i = 0; i < a->used && j < size; i++) {
        r[j] |= ((sp_digit)a->dp[i] << s);
        r[j] &= 0x1ffffffffffffffL;
        s = 57U - s;
        if (j + 1 >= size) {
            break;
        }
        /* lint allow cast of mismatch word32 and mp_digit */
        r[++j] = (sp_digit)(a->dp[i] >> s); /*lint !e9033*/
        while ((s + 57U) <= (word32)DIGIT_BIT) {
            s += 57U;
            r[j] &= 0x1ffffffffffffffL;
            if (j + 1 >= size) {
                break;
            }
            if (s < (word32)DIGIT_BIT) {
                /* lint allow cast of mismatch word32 and mp_digit */
                r[++j] = (sp_digit)(a->dp[i] >> s); /*lint !e9033*/
            }
            else {
                r[++j] = 0L;
            }
        }
        s = (word32)DIGIT_BIT - s;
    }

    for (j++; j < size; j++) {
        r[j] = 0;
    }
#else
    int i, j = 0, s = 0;

    r[0] = 0;
    for (i = 0; i < a->used && j < size; i++) {
        r[j] |= ((sp_digit)a->dp[i]) << s;
        if (s + DIGIT_BIT >= 57) {
            r[j] &= 0x1ffffffffffffffL;
            if (j + 1 >= size) {
                break;
            }
            s = 57 - s;
            if (s == DIGIT_BIT) {
                r[++j] = 0;
                s = 0;
            }
            else {
                r[++j] = a->dp[i] >> s;
                s = DIGIT_BIT - s;
            }
        }
        else {
            s += DIGIT_BIT;
        }
    }

    for (j++; j < size; j++) {
        r[j] = 0;
    }
#endif
}

/* Write r as big endian to byte array.
 * Fixed length number of bytes written: 256
 *
 * r  A single precision integer.
 * a  Byte array.
 */
static void sp_2048_to_bin(sp_digit* r, byte* a)
{
    int i, j, s = 0, b;

    for (i=0; i<35; i++) {
        r[i+1] += r[i] >> 57;
        r[i] &= 0x1ffffffffffffffL;
    }
    j = 2048 / 8 - 1;
    a[j] = 0;
    for (i=0; i<36 && j>=0; i++) {
        b = 0;
        /* lint allow cast of mismatch sp_digit and int */
        a[j--] |= (byte)(r[i] << s); /*lint !e9033*/
        b += 8 - s;
        if (j < 0) {
            break;
        }
        while (b < 57) {
            a[j--] = (byte)(r[i] >> b);
            b += 8;
            if (j < 0) {
                break;
            }
        }
        s = 8 - (b - 57);
        if (j >= 0) {
            a[j] = 0;
        }
        if (s != 0) {
            j++;
        }
    }
}

#ifndef WOLFSSL_SP_SMALL
/* Multiply a and b into r. (r = a * b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A single precision integer.
 */
SP_NOINLINE static void sp_2048_mul_9(sp_digit* r, const sp_digit* a,
    const sp_digit* b)
{
    int128_t t0   = ((int128_t)a[ 0]) * b[ 0];
    int128_t t1   = ((int128_t)a[ 0]) * b[ 1]
                 + ((int128_t)a[ 1]) * b[ 0];
    int128_t t2   = ((int128_t)a[ 0]) * b[ 2]
                 + ((int128_t)a[ 1]) * b[ 1]
                 + ((int128_t)a[ 2]) * b[ 0];
    int128_t t3   = ((int128_t)a[ 0]) * b[ 3]
                 + ((int128_t)a[ 1]) * b[ 2]
                 + ((int128_t)a[ 2]) * b[ 1]
                 + ((int128_t)a[ 3]) * b[ 0];
    int128_t t4   = ((int128_t)a[ 0]) * b[ 4]
                 + ((int128_t)a[ 1]) * b[ 3]
                 + ((int128_t)a[ 2]) * b[ 2]
                 + ((int128_t)a[ 3]) * b[ 1]
                 + ((int128_t)a[ 4]) * b[ 0];
    int128_t t5   = ((int128_t)a[ 0]) * b[ 5]
                 + ((int128_t)a[ 1]) * b[ 4]
                 + ((int128_t)a[ 2]) * b[ 3]
                 + ((int128_t)a[ 3]) * b[ 2]
                 + ((int128_t)a[ 4]) * b[ 1]
                 + ((int128_t)a[ 5]) * b[ 0];
    int128_t t6   = ((int128_t)a[ 0]) * b[ 6]
                 + ((int128_t)a[ 1]) * b[ 5]
                 + ((int128_t)a[ 2]) * b[ 4]
                 + ((int128_t)a[ 3]) * b[ 3]
                 + ((int128_t)a[ 4]) * b[ 2]
                 + ((int128_t)a[ 5]) * b[ 1]
                 + ((int128_t)a[ 6]) * b[ 0];
    int128_t t7   = ((int128_t)a[ 0]) * b[ 7]
                 + ((int128_t)a[ 1]) * b[ 6]
                 + ((int128_t)a[ 2]) * b[ 5]
                 + ((int128_t)a[ 3]) * b[ 4]
                 + ((int128_t)a[ 4]) * b[ 3]
                 + ((int128_t)a[ 5]) * b[ 2]
                 + ((int128_t)a[ 6]) * b[ 1]
                 + ((int128_t)a[ 7]) * b[ 0];
    int128_t t8   = ((int128_t)a[ 0]) * b[ 8]
                 + ((int128_t)a[ 1]) * b[ 7]
                 + ((int128_t)a[ 2]) * b[ 6]
                 + ((int128_t)a[ 3]) * b[ 5]
                 + ((int128_t)a[ 4]) * b[ 4]
                 + ((int128_t)a[ 5]) * b[ 3]
                 + ((int128_t)a[ 6]) * b[ 2]
                 + ((int128_t)a[ 7]) * b[ 1]
                 + ((int128_t)a[ 8]) * b[ 0];
    int128_t t9   = ((int128_t)a[ 1]) * b[ 8]
                 + ((int128_t)a[ 2]) * b[ 7]
                 + ((int128_t)a[ 3]) * b[ 6]
                 + ((int128_t)a[ 4]) * b[ 5]
                 + ((int128_t)a[ 5]) * b[ 4]
                 + ((int128_t)a[ 6]) * b[ 3]
                 + ((int128_t)a[ 7]) * b[ 2]
                 + ((int128_t)a[ 8]) * b[ 1];
    int128_t t10  = ((int128_t)a[ 2]) * b[ 8]
                 + ((int128_t)a[ 3]) * b[ 7]
                 + ((int128_t)a[ 4]) * b[ 6]
                 + ((int128_t)a[ 5]) * b[ 5]
                 + ((int128_t)a[ 6]) * b[ 4]
                 + ((int128_t)a[ 7]) * b[ 3]
                 + ((int128_t)a[ 8]) * b[ 2];
    int128_t t11  = ((int128_t)a[ 3]) * b[ 8]
                 + ((int128_t)a[ 4]) * b[ 7]
                 + ((int128_t)a[ 5]) * b[ 6]
                 + ((int128_t)a[ 6]) * b[ 5]
                 + ((int128_t)a[ 7]) * b[ 4]
                 + ((int128_t)a[ 8]) * b[ 3];
    int128_t t12  = ((int128_t)a[ 4]) * b[ 8]
                 + ((int128_t)a[ 5]) * b[ 7]
                 + ((int128_t)a[ 6]) * b[ 6]
                 + ((int128_t)a[ 7]) * b[ 5]
                 + ((int128_t)a[ 8]) * b[ 4];
    int128_t t13  = ((int128_t)a[ 5]) * b[ 8]
                 + ((int128_t)a[ 6]) * b[ 7]
                 + ((int128_t)a[ 7]) * b[ 6]
                 + ((int128_t)a[ 8]) * b[ 5];
    int128_t t14  = ((int128_t)a[ 6]) * b[ 8]
                 + ((int128_t)a[ 7]) * b[ 7]
                 + ((int128_t)a[ 8]) * b[ 6];
    int128_t t15  = ((int128_t)a[ 7]) * b[ 8]
                 + ((int128_t)a[ 8]) * b[ 7];
    int128_t t16  = ((int128_t)a[ 8]) * b[ 8];

    t1   += t0  >> 57; r[ 0] = t0  & 0x1ffffffffffffffL;
    t2   += t1  >> 57; r[ 1] = t1  & 0x1ffffffffffffffL;
    t3   += t2  >> 57; r[ 2] = t2  & 0x1ffffffffffffffL;
    t4   += t3  >> 57; r[ 3] = t3  & 0x1ffffffffffffffL;
    t5   += t4  >> 57; r[ 4] = t4  & 0x1ffffffffffffffL;
    t6   += t5  >> 57; r[ 5] = t5  & 0x1ffffffffffffffL;
    t7   += t6  >> 57; r[ 6] = t6  & 0x1ffffffffffffffL;
    t8   += t7  >> 57; r[ 7] = t7  & 0x1ffffffffffffffL;
    t9   += t8  >> 57; r[ 8] = t8  & 0x1ffffffffffffffL;
    t10  += t9  >> 57; r[ 9] = t9  & 0x1ffffffffffffffL;
    t11  += t10 >> 57; r[10] = t10 & 0x1ffffffffffffffL;
    t12  += t11 >> 57; r[11] = t11 & 0x1ffffffffffffffL;
    t13  += t12 >> 57; r[12] = t12 & 0x1ffffffffffffffL;
    t14  += t13 >> 57; r[13] = t13 & 0x1ffffffffffffffL;
    t15  += t14 >> 57; r[14] = t14 & 0x1ffffffffffffffL;
    t16  += t15 >> 57; r[15] = t15 & 0x1ffffffffffffffL;
    r[17] = (sp_digit)(t16 >> 57);
                       r[16] = t16 & 0x1ffffffffffffffL;
}

/* Square a and put result in r. (r = a * a)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 */
SP_NOINLINE static void sp_2048_sqr_9(sp_digit* r, const sp_digit* a)
{
    int128_t t0   =  ((int128_t)a[ 0]) * a[ 0];
    int128_t t1   = (((int128_t)a[ 0]) * a[ 1]) * 2;
    int128_t t2   = (((int128_t)a[ 0]) * a[ 2]) * 2
                 +  ((int128_t)a[ 1]) * a[ 1];
    int128_t t3   = (((int128_t)a[ 0]) * a[ 3]
                 +  ((int128_t)a[ 1]) * a[ 2]) * 2;
    int128_t t4   = (((int128_t)a[ 0]) * a[ 4]
                 +  ((int128_t)a[ 1]) * a[ 3]) * 2
                 +  ((int128_t)a[ 2]) * a[ 2];
    int128_t t5   = (((int128_t)a[ 0]) * a[ 5]
                 +  ((int128_t)a[ 1]) * a[ 4]
                 +  ((int128_t)a[ 2]) * a[ 3]) * 2;
    int128_t t6   = (((int128_t)a[ 0]) * a[ 6]
                 +  ((int128_t)a[ 1]) * a[ 5]
                 +  ((int128_t)a[ 2]) * a[ 4]) * 2
                 +  ((int128_t)a[ 3]) * a[ 3];
    int128_t t7   = (((int128_t)a[ 0]) * a[ 7]
                 +  ((int128_t)a[ 1]) * a[ 6]
                 +  ((int128_t)a[ 2]) * a[ 5]
                 +  ((int128_t)a[ 3]) * a[ 4]) * 2;
    int128_t t8   = (((int128_t)a[ 0]) * a[ 8]
                 +  ((int128_t)a[ 1]) * a[ 7]
                 +  ((int128_t)a[ 2]) * a[ 6]
                 +  ((int128_t)a[ 3]) * a[ 5]) * 2
                 +  ((int128_t)a[ 4]) * a[ 4];
    int128_t t9   = (((int128_t)a[ 1]) * a[ 8]
                 +  ((int128_t)a[ 2]) * a[ 7]
                 +  ((int128_t)a[ 3]) * a[ 6]
                 +  ((int128_t)a[ 4]) * a[ 5]) * 2;
    int128_t t10  = (((int128_t)a[ 2]) * a[ 8]
                 +  ((int128_t)a[ 3]) * a[ 7]
                 +  ((int128_t)a[ 4]) * a[ 6]) * 2
                 +  ((int128_t)a[ 5]) * a[ 5];
    int128_t t11  = (((int128_t)a[ 3]) * a[ 8]
                 +  ((int128_t)a[ 4]) * a[ 7]
                 +  ((int128_t)a[ 5]) * a[ 6]) * 2;
    int128_t t12  = (((int128_t)a[ 4]) * a[ 8]
                 +  ((int128_t)a[ 5]) * a[ 7]) * 2
                 +  ((int128_t)a[ 6]) * a[ 6];
    int128_t t13  = (((int128_t)a[ 5]) * a[ 8]
                 +  ((int128_t)a[ 6]) * a[ 7]) * 2;
    int128_t t14  = (((int128_t)a[ 6]) * a[ 8]) * 2
                 +  ((int128_t)a[ 7]) * a[ 7];
    int128_t t15  = (((int128_t)a[ 7]) * a[ 8]) * 2;
    int128_t t16  =  ((int128_t)a[ 8]) * a[ 8];

    t1   += t0  >> 57; r[ 0] = t0  & 0x1ffffffffffffffL;
    t2   += t1  >> 57; r[ 1] = t1  & 0x1ffffffffffffffL;
    t3   += t2  >> 57; r[ 2] = t2  & 0x1ffffffffffffffL;
    t4   += t3  >> 57; r[ 3] = t3  & 0x1ffffffffffffffL;
    t5   += t4  >> 57; r[ 4] = t4  & 0x1ffffffffffffffL;
    t6   += t5  >> 57; r[ 5] = t5  & 0x1ffffffffffffffL;
    t7   += t6  >> 57; r[ 6] = t6  & 0x1ffffffffffffffL;
    t8   += t7  >> 57; r[ 7] = t7  & 0x1ffffffffffffffL;
    t9   += t8  >> 57; r[ 8] = t8  & 0x1ffffffffffffffL;
    t10  += t9  >> 57; r[ 9] = t9  & 0x1ffffffffffffffL;
    t11  += t10 >> 57; r[10] = t10 & 0x1ffffffffffffffL;
    t12  += t11 >> 57; r[11] = t11 & 0x1ffffffffffffffL;
    t13  += t12 >> 57; r[12] = t12 & 0x1ffffffffffffffL;
    t14  += t13 >> 57; r[13] = t13 & 0x1ffffffffffffffL;
    t15  += t14 >> 57; r[14] = t14 & 0x1ffffffffffffffL;
    t16  += t15 >> 57; r[15] = t15 & 0x1ffffffffffffffL;
    r[17] = (sp_digit)(t16 >> 57);
                       r[16] = t16 & 0x1ffffffffffffffL;
}

/* Add b to a into r. (r = a + b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A single precision integer.
 */
SP_NOINLINE static int sp_2048_add_9(sp_digit* r, const sp_digit* a,
        const sp_digit* b)
{
    r[ 0] = a[ 0] + b[ 0];
    r[ 1] = a[ 1] + b[ 1];
    r[ 2] = a[ 2] + b[ 2];
    r[ 3] = a[ 3] + b[ 3];
    r[ 4] = a[ 4] + b[ 4];
    r[ 5] = a[ 5] + b[ 5];
    r[ 6] = a[ 6] + b[ 6];
    r[ 7] = a[ 7] + b[ 7];
    r[ 8] = a[ 8] + b[ 8];

    return 0;
}

/* Add b to a into r. (r = a + b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A single precision integer.
 */
SP_NOINLINE static int sp_2048_add_18(sp_digit* r, const sp_digit* a,
        const sp_digit* b)
{
    int i;

    for (i = 0; i < 16; i += 8) {
        r[i + 0] = a[i + 0] + b[i + 0];
        r[i + 1] = a[i + 1] + b[i + 1];
        r[i + 2] = a[i + 2] + b[i + 2];
        r[i + 3] = a[i + 3] + b[i + 3];
        r[i + 4] = a[i + 4] + b[i + 4];
        r[i + 5] = a[i + 5] + b[i + 5];
        r[i + 6] = a[i + 6] + b[i + 6];
        r[i + 7] = a[i + 7] + b[i + 7];
    }
    r[16] = a[16] + b[16];
    r[17] = a[17] + b[17];

    return 0;
}

/* Sub b from a into r. (r = a - b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A single precision integer.
 */
SP_NOINLINE static int sp_2048_sub_18(sp_digit* r, const sp_digit* a,
        const sp_digit* b)
{
    int i;

    for (i = 0; i < 16; i += 8) {
        r[i + 0] = a[i + 0] - b[i + 0];
        r[i + 1] = a[i + 1] - b[i + 1];
        r[i + 2] = a[i + 2] - b[i + 2];
        r[i + 3] = a[i + 3] - b[i + 3];
        r[i + 4] = a[i + 4] - b[i + 4];
        r[i + 5] = a[i + 5] - b[i + 5];
        r[i + 6] = a[i + 6] - b[i + 6];
        r[i + 7] = a[i + 7] - b[i + 7];
    }
    r[16] = a[16] - b[16];
    r[17] = a[17] - b[17];

    return 0;
}

/* Multiply a and b into r. (r = a * b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A single precision integer.
 */
SP_NOINLINE static void sp_2048_mul_18(sp_digit* r, const sp_digit* a,
    const sp_digit* b)
{
    sp_digit* z0 = r;
    sp_digit z1[18];
    sp_digit* a1 = z1;
    sp_digit b1[9];
    sp_digit* z2 = r + 18;
    (void)sp_2048_add_9(a1, a, &a[9]);
    (void)sp_2048_add_9(b1, b, &b[9]);
    sp_2048_mul_9(z2, &a[9], &b[9]);
    sp_2048_mul_9(z0, a, b);
    sp_2048_mul_9(z1, a1, b1);
    (void)sp_2048_sub_18(z1, z1, z2);
    (void)sp_2048_sub_18(z1, z1, z0);
    (void)sp_2048_add_18(r + 9, r + 9, z1);
}

/* Square a and put result in r. (r = a * a)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 */
SP_NOINLINE static void sp_2048_sqr_18(sp_digit* r, const sp_digit* a)
{
    sp_digit* z0 = r;
    sp_digit z1[18];
    sp_digit* a1 = z1;
    sp_digit* z2 = r + 18;
    (void)sp_2048_add_9(a1, a, &a[9]);
    sp_2048_sqr_9(z2, &a[9]);
    sp_2048_sqr_9(z0, a);
    sp_2048_sqr_9(z1, a1);
    (void)sp_2048_sub_18(z1, z1, z2);
    (void)sp_2048_sub_18(z1, z1, z0);
    (void)sp_2048_add_18(r + 9, r + 9, z1);
}

/* Add b to a into r. (r = a + b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A single precision integer.
 */
SP_NOINLINE static int sp_2048_add_36(sp_digit* r, const sp_digit* a,
        const sp_digit* b)
{
    int i;

    for (i = 0; i < 32; i += 8) {
        r[i + 0] = a[i + 0] + b[i + 0];
        r[i + 1] = a[i + 1] + b[i + 1];
        r[i + 2] = a[i + 2] + b[i + 2];
        r[i + 3] = a[i + 3] + b[i + 3];
        r[i + 4] = a[i + 4] + b[i + 4];
        r[i + 5] = a[i + 5] + b[i + 5];
        r[i + 6] = a[i + 6] + b[i + 6];
        r[i + 7] = a[i + 7] + b[i + 7];
    }
    r[32] = a[32] + b[32];
    r[33] = a[33] + b[33];
    r[34] = a[34] + b[34];
    r[35] = a[35] + b[35];

    return 0;
}

/* Sub b from a into r. (r = a - b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A single precision integer.
 */
SP_NOINLINE static int sp_2048_sub_36(sp_digit* r, const sp_digit* a,
        const sp_digit* b)
{
    int i;

    for (i = 0; i < 32; i += 8) {
        r[i + 0] = a[i + 0] - b[i + 0];
        r[i + 1] = a[i + 1] - b[i + 1];
        r[i + 2] = a[i + 2] - b[i + 2];
        r[i + 3] = a[i + 3] - b[i + 3];
        r[i + 4] = a[i + 4] - b[i + 4];
        r[i + 5] = a[i + 5] - b[i + 5];
        r[i + 6] = a[i + 6] - b[i + 6];
        r[i + 7] = a[i + 7] - b[i + 7];
    }
    r[32] = a[32] - b[32];
    r[33] = a[33] - b[33];
    r[34] = a[34] - b[34];
    r[35] = a[35] - b[35];

    return 0;
}

/* Multiply a and b into r. (r = a * b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A single precision integer.
 */
SP_NOINLINE static void sp_2048_mul_36(sp_digit* r, const sp_digit* a,
    const sp_digit* b)
{
    sp_digit* z0 = r;
    sp_digit z1[36];
    sp_digit* a1 = z1;
    sp_digit b1[18];
    sp_digit* z2 = r + 36;
    (void)sp_2048_add_18(a1, a, &a[18]);
    (void)sp_2048_add_18(b1, b, &b[18]);
    sp_2048_mul_18(z2, &a[18], &b[18]);
    sp_2048_mul_18(z0, a, b);
    sp_2048_mul_18(z1, a1, b1);
    (void)sp_2048_sub_36(z1, z1, z2);
    (void)sp_2048_sub_36(z1, z1, z0);
    (void)sp_2048_add_36(r + 18, r + 18, z1);
}

/* Square a and put result in r. (r = a * a)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 */
SP_NOINLINE static void sp_2048_sqr_36(sp_digit* r, const sp_digit* a)
{
    sp_digit* z0 = r;
    sp_digit z1[36];
    sp_digit* a1 = z1;
    sp_digit* z2 = r + 36;
    (void)sp_2048_add_18(a1, a, &a[18]);
    sp_2048_sqr_18(z2, &a[18]);
    sp_2048_sqr_18(z0, a);
    sp_2048_sqr_18(z1, a1);
    (void)sp_2048_sub_36(z1, z1, z2);
    (void)sp_2048_sub_36(z1, z1, z0);
    (void)sp_2048_add_36(r + 18, r + 18, z1);
}

#endif /* !WOLFSSL_SP_SMALL */
#ifdef WOLFSSL_SP_SMALL
/* Add b to a into r. (r = a + b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A single precision integer.
 */
SP_NOINLINE static int sp_2048_add_36(sp_digit* r, const sp_digit* a,
        const sp_digit* b)
{
    int i;

    for (i = 0; i < 36; i++) {
        r[i] = a[i] + b[i];
    }

    return 0;
}
#endif /* WOLFSSL_SP_SMALL */
#ifdef WOLFSSL_SP_SMALL
/* Sub b from a into r. (r = a - b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A single precision integer.
 */
SP_NOINLINE static int sp_2048_sub_36(sp_digit* r, const sp_digit* a,
        const sp_digit* b)
{
    int i;

    for (i = 0; i < 36; i++) {
        r[i] = a[i] - b[i];
    }

    return 0;
}

#endif /* WOLFSSL_SP_SMALL */
#ifdef WOLFSSL_SP_SMALL
/* Multiply a and b into r. (r = a * b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A single precision integer.
 */
SP_NOINLINE static void sp_2048_mul_36(sp_digit* r, const sp_digit* a,
    const sp_digit* b)
{
    int i, j, k;
    int128_t c;

    c = ((int128_t)a[35]) * b[35];
    r[71] = (sp_digit)(c >> 57);
    c = (c & 0x1ffffffffffffffL) << 57;
    for (k = 69; k >= 0; k--) {
        for (i = 35; i >= 0; i--) {
            j = k - i;
            if (j >= 36) {
                break;
            }
            if (j < 0) {
                continue;
            }

            c += ((int128_t)a[i]) * b[j];
        }
        r[k + 2] += c >> 114;
        r[k + 1] = (c >> 57) & 0x1ffffffffffffffL;
        c = (c & 0x1ffffffffffffffL) << 57;
    }
    r[0] = (sp_digit)(c >> 57);
}

/* Square a and put result in r. (r = a * a)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 */
SP_NOINLINE static void sp_2048_sqr_36(sp_digit* r, const sp_digit* a)
{
    int i, j, k;
    int128_t c;

    c = ((int128_t)a[35]) * a[35];
    r[71] = (sp_digit)(c >> 57);
    c = (c & 0x1ffffffffffffffL) << 57;
    for (k = 69; k >= 0; k--) {
        for (i = 35; i >= 0; i--) {
            j = k - i;
            if (j >= 36 || i <= j) {
                break;
            }
            if (j < 0) {
                continue;
            }

            c += ((int128_t)a[i]) * a[j] * 2;
        }
        if (i == j) {
           c += ((int128_t)a[i]) * a[i];
        }

        r[k + 2] += c >> 114;
        r[k + 1] = (c >> 57) & 0x1ffffffffffffffL;
        c = (c & 0x1ffffffffffffffL) << 57;
    }
    r[0] = (sp_digit)(c >> 57);
}

#endif /* WOLFSSL_SP_SMALL */
#if (defined(WOLFSSL_HAVE_SP_RSA) || defined(WOLFSSL_HAVE_SP_DH)) && !defined(WOLFSSL_RSA_PUBLIC_ONLY)
#ifdef WOLFSSL_SP_SMALL
/* Add b to a into r. (r = a + b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A single precision integer.
 */
SP_NOINLINE static int sp_2048_add_18(sp_digit* r, const sp_digit* a,
        const sp_digit* b)
{
    int i;

    for (i = 0; i < 18; i++) {
        r[i] = a[i] + b[i];
    }

    return 0;
}
#endif /* WOLFSSL_SP_SMALL */
#ifdef WOLFSSL_SP_SMALL
/* Sub b from a into r. (r = a - b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A single precision integer.
 */
SP_NOINLINE static int sp_2048_sub_18(sp_digit* r, const sp_digit* a,
        const sp_digit* b)
{
    int i;

    for (i = 0; i < 18; i++) {
        r[i] = a[i] - b[i];
    }

    return 0;
}

#endif /* WOLFSSL_SP_SMALL */
#ifdef WOLFSSL_SP_SMALL
/* Multiply a and b into r. (r = a * b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A single precision integer.
 */
SP_NOINLINE static void sp_2048_mul_18(sp_digit* r, const sp_digit* a,
    const sp_digit* b)
{
    int i, j, k;
    int128_t c;

    c = ((int128_t)a[17]) * b[17];
    r[35] = (sp_digit)(c >> 57);
    c = (c & 0x1ffffffffffffffL) << 57;
    for (k = 33; k >= 0; k--) {
        for (i = 17; i >= 0; i--) {
            j = k - i;
            if (j >= 18) {
                break;
            }
            if (j < 0) {
                continue;
            }

            c += ((int128_t)a[i]) * b[j];
        }
        r[k + 2] += c >> 114;
        r[k + 1] = (c >> 57) & 0x1ffffffffffffffL;
        c = (c & 0x1ffffffffffffffL) << 57;
    }
    r[0] = (sp_digit)(c >> 57);
}

/* Square a and put result in r. (r = a * a)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 */
SP_NOINLINE static void sp_2048_sqr_18(sp_digit* r, const sp_digit* a)
{
    int i, j, k;
    int128_t c;

    c = ((int128_t)a[17]) * a[17];
    r[35] = (sp_digit)(c >> 57);
    c = (c & 0x1ffffffffffffffL) << 57;
    for (k = 33; k >= 0; k--) {
        for (i = 17; i >= 0; i--) {
            j = k - i;
            if (j >= 18 || i <= j) {
                break;
            }
            if (j < 0) {
                continue;
            }

            c += ((int128_t)a[i]) * a[j] * 2;
        }
        if (i == j) {
           c += ((int128_t)a[i]) * a[i];
        }

        r[k + 2] += c >> 114;
        r[k + 1] = (c >> 57) & 0x1ffffffffffffffL;
        c = (c & 0x1ffffffffffffffL) << 57;
    }
    r[0] = (sp_digit)(c >> 57);
}

#endif /* WOLFSSL_SP_SMALL */
#endif /* (WOLFSSL_HAVE_SP_RSA || WOLFSSL_HAVE_SP_DH) && !WOLFSSL_RSA_PUBLIC_ONLY */

/* Caclulate the bottom digit of -1/a mod 2^n.
 *
 * a    A single precision number.
 * rho  Bottom word of inverse.
 */
static void sp_2048_mont_setup(const sp_digit* a, sp_digit* rho)
{
    sp_digit x, b;

    b = a[0];
    x = (((b + 2) & 4) << 1) + b; /* here x*a==1 mod 2**4 */
    x *= 2 - b * x;               /* here x*a==1 mod 2**8 */
    x *= 2 - b * x;               /* here x*a==1 mod 2**16 */
    x *= 2 - b * x;               /* here x*a==1 mod 2**32 */
    x *= 2 - b * x;               /* here x*a==1 mod 2**64 */
    x &= 0x1ffffffffffffffL;

    /* rho = -1/m mod b */
    *rho = (1L << 57) - x;
}

/* Multiply a by scalar b into r. (r = a * b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A scalar.
 */
SP_NOINLINE static void sp_2048_mul_d_36(sp_digit* r, const sp_digit* a,
    sp_digit b)
{
#ifdef WOLFSSL_SP_SMALL
    int128_t tb = b;
    int128_t t = 0;
    int i;

    for (i = 0; i < 36; i++) {
        t += tb * a[i];
        r[i] = t & 0x1ffffffffffffffL;
        t >>= 57;
    }
    r[36] = (sp_digit)t;
#else
    int128_t tb = b;
    int128_t t[8];
    int i;

    t[0] = tb * a[0]; r[0] = t[0] & 0x1ffffffffffffffL;
    for (i = 0; i < 32; i += 8) {
        t[1] = tb * a[i+1];
        r[i+1] = (sp_digit)(t[0] >> 57) + (t[1] & 0x1ffffffffffffffL);
        t[2] = tb * a[i+2];
        r[i+2] = (sp_digit)(t[1] >> 57) + (t[2] & 0x1ffffffffffffffL);
        t[3] = tb * a[i+3];
        r[i+3] = (sp_digit)(t[2] >> 57) + (t[3] & 0x1ffffffffffffffL);
        t[4] = tb * a[i+4];
        r[i+4] = (sp_digit)(t[3] >> 57) + (t[4] & 0x1ffffffffffffffL);
        t[5] = tb * a[i+5];
        r[i+5] = (sp_digit)(t[4] >> 57) + (t[5] & 0x1ffffffffffffffL);
        t[6] = tb * a[i+6];
        r[i+6] = (sp_digit)(t[5] >> 57) + (t[6] & 0x1ffffffffffffffL);
        t[7] = tb * a[i+7];
        r[i+7] = (sp_digit)(t[6] >> 57) + (t[7] & 0x1ffffffffffffffL);
        t[0] = tb * a[i+8];
        r[i+8] = (sp_digit)(t[7] >> 57) + (t[0] & 0x1ffffffffffffffL);
    }
    t[1] = tb * a[33];
    r[33] = (sp_digit)(t[0] >> 57) + (t[1] & 0x1ffffffffffffffL);
    t[2] = tb * a[34];
    r[34] = (sp_digit)(t[1] >> 57) + (t[2] & 0x1ffffffffffffffL);
    t[3] = tb * a[35];
    r[35] = (sp_digit)(t[2] >> 57) + (t[3] & 0x1ffffffffffffffL);
    r[36] =  (sp_digit)(t[3] >> 57);
#endif /* WOLFSSL_SP_SMALL */
}

#if (defined(WOLFSSL_HAVE_SP_RSA) || defined(WOLFSSL_HAVE_SP_DH)) && !defined(WOLFSSL_RSA_PUBLIC_ONLY)
/* r = 2^n mod m where n is the number of bits to reduce by.
 * Given m must be 2048 bits, just need to subtract.
 *
 * r  A single precision number.
 * m  A single precision number.
 */
static void sp_2048_mont_norm_18(sp_digit* r, const sp_digit* m)
{
    /* Set r = 2^n - 1. */
#ifdef WOLFSSL_SP_SMALL
    int i;

    for (i=0; i<17; i++) {
        r[i] = 0x1ffffffffffffffL;
    }
#else
    int i;

    for (i = 0; i < 16; i += 8) {
        r[i + 0] = 0x1ffffffffffffffL;
        r[i + 1] = 0x1ffffffffffffffL;
        r[i + 2] = 0x1ffffffffffffffL;
        r[i + 3] = 0x1ffffffffffffffL;
        r[i + 4] = 0x1ffffffffffffffL;
        r[i + 5] = 0x1ffffffffffffffL;
        r[i + 6] = 0x1ffffffffffffffL;
        r[i + 7] = 0x1ffffffffffffffL;
    }
    r[16] = 0x1ffffffffffffffL;
#endif
    r[17] = 0x7fffffffffffffL;

    /* r = (2^n - 1) mod n */
    (void)sp_2048_sub_18(r, r, m);

    /* Add one so r = 2^n mod m */
    r[0] += 1;
}

/* Compare a with b in constant time.
 *
 * a  A single precision integer.
 * b  A single precision integer.
 * return -ve, 0 or +ve if a is less than, equal to or greater than b
 * respectively.
 */
static sp_digit sp_2048_cmp_18(const sp_digit* a, const sp_digit* b)
{
    sp_digit r = 0;
#ifdef WOLFSSL_SP_SMALL
    int i;

    for (i=17; i>=0; i--) {
        r |= (a[i] - b[i]) & (0 - ((r == 0) ? (sp_digit)1 : (sp_digit)0));
    }
#else
    int i;

    r |= (a[17] - b[17]) & (0 - ((r == 0) ? (sp_digit)1 : (sp_digit)0));
    r |= (a[16] - b[16]) & (0 - ((r == 0) ? (sp_digit)1 : (sp_digit)0));
    for (i = 8; i >= 0; i -= 8) {
        r |= (a[i + 7] - b[i + 7]) & (0 - ((r == 0) ? (sp_digit)1 : (sp_digit)0));
        r |= (a[i + 6] - b[i + 6]) & (0 - ((r == 0) ? (sp_digit)1 : (sp_digit)0));
        r |= (a[i + 5] - b[i + 5]) & (0 - ((r == 0) ? (sp_digit)1 : (sp_digit)0));
        r |= (a[i + 4] - b[i + 4]) & (0 - ((r == 0) ? (sp_digit)1 : (sp_digit)0));
        r |= (a[i + 3] - b[i + 3]) & (0 - ((r == 0) ? (sp_digit)1 : (sp_digit)0));
        r |= (a[i + 2] - b[i + 2]) & (0 - ((r == 0) ? (sp_digit)1 : (sp_digit)0));
        r |= (a[i + 1] - b[i + 1]) & (0 - ((r == 0) ? (sp_digit)1 : (sp_digit)0));
        r |= (a[i + 0] - b[i + 0]) & (0 - ((r == 0) ? (sp_digit)1 : (sp_digit)0));
    }
#endif /* WOLFSSL_SP_SMALL */

    return r;
}

/* Conditionally subtract b from a using the mask m.
 * m is -1 to subtract and 0 when not.
 *
 * r  A single precision number representing condition subtract result.
 * a  A single precision number to subtract from.
 * b  A single precision number to subtract.
 * m  Mask value to apply.
 */
static void sp_2048_cond_sub_18(sp_digit* r, const sp_digit* a,
        const sp_digit* b, const sp_digit m)
{
#ifdef WOLFSSL_SP_SMALL
    int i;

    for (i = 0; i < 18; i++) {
        r[i] = a[i] - (b[i] & m);
    }
#else
    int i;

    for (i = 0; i < 16; i += 8) {
        r[i + 0] = a[i + 0] - (b[i + 0] & m);
        r[i + 1] = a[i + 1] - (b[i + 1] & m);
        r[i + 2] = a[i + 2] - (b[i + 2] & m);
        r[i + 3] = a[i + 3] - (b[i + 3] & m);
        r[i + 4] = a[i + 4] - (b[i + 4] & m);
        r[i + 5] = a[i + 5] - (b[i + 5] & m);
        r[i + 6] = a[i + 6] - (b[i + 6] & m);
        r[i + 7] = a[i + 7] - (b[i + 7] & m);
    }
    r[16] = a[16] - (b[16] & m);
    r[17] = a[17] - (b[17] & m);
#endif /* WOLFSSL_SP_SMALL */
}

/* Mul a by scalar b and add into r. (r += a * b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A scalar.
 */
SP_NOINLINE static void sp_2048_mul_add_18(sp_digit* r, const sp_digit* a,
        const sp_digit b)
{
#ifdef WOLFSSL_SP_SMALL
    int128_t tb = b;
    int128_t t = 0;
    int i;

    for (i = 0; i < 18; i++) {
        t += (tb * a[i]) + r[i];
        r[i] = t & 0x1ffffffffffffffL;
        t >>= 57;
    }
    r[18] += t;
#else
    int128_t tb = b;
    int128_t t[8];
    int i;

    t[0] = tb * a[0]; r[0] += (sp_digit)(t[0] & 0x1ffffffffffffffL);
    for (i = 0; i < 16; i += 8) {
        t[1] = tb * a[i+1];
        r[i+1] += (sp_digit)((t[0] >> 57) + (t[1] & 0x1ffffffffffffffL));
        t[2] = tb * a[i+2];
        r[i+2] += (sp_digit)((t[1] >> 57) + (t[2] & 0x1ffffffffffffffL));
        t[3] = tb * a[i+3];
        r[i+3] += (sp_digit)((t[2] >> 57) + (t[3] & 0x1ffffffffffffffL));
        t[4] = tb * a[i+4];
        r[i+4] += (sp_digit)((t[3] >> 57) + (t[4] & 0x1ffffffffffffffL));
        t[5] = tb * a[i+5];
        r[i+5] += (sp_digit)((t[4] >> 57) + (t[5] & 0x1ffffffffffffffL));
        t[6] = tb * a[i+6];
        r[i+6] += (sp_digit)((t[5] >> 57) + (t[6] & 0x1ffffffffffffffL));
        t[7] = tb * a[i+7];
        r[i+7] += (sp_digit)((t[6] >> 57) + (t[7] & 0x1ffffffffffffffL));
        t[0] = tb * a[i+8];
        r[i+8] += (sp_digit)((t[7] >> 57) + (t[0] & 0x1ffffffffffffffL));
    }
    t[1] = tb * a[17]; r[17] += (sp_digit)((t[0] >> 57) + (t[1] & 0x1ffffffffffffffL));
    r[18] +=  (sp_digit)(t[1] >> 57);
#endif /* WOLFSSL_SP_SMALL */
}

/* Normalize the values in each word to 57.
 *
 * a  Array of sp_digit to normalize.
 */
static void sp_2048_norm_18(sp_digit* a)
{
#ifdef WOLFSSL_SP_SMALL
    int i;
    for (i = 0; i < 17; i++) {
        a[i+1] += a[i] >> 57;
        a[i] &= 0x1ffffffffffffffL;
    }
#else
    int i;
    for (i = 0; i < 16; i += 8) {
        a[i+1] += a[i+0] >> 57; a[i+0] &= 0x1ffffffffffffffL;
        a[i+2] += a[i+1] >> 57; a[i+1] &= 0x1ffffffffffffffL;
        a[i+3] += a[i+2] >> 57; a[i+2] &= 0x1ffffffffffffffL;
        a[i+4] += a[i+3] >> 57; a[i+3] &= 0x1ffffffffffffffL;
        a[i+5] += a[i+4] >> 57; a[i+4] &= 0x1ffffffffffffffL;
        a[i+6] += a[i+5] >> 57; a[i+5] &= 0x1ffffffffffffffL;
        a[i+7] += a[i+6] >> 57; a[i+6] &= 0x1ffffffffffffffL;
        a[i+8] += a[i+7] >> 57; a[i+7] &= 0x1ffffffffffffffL;
        a[i+9] += a[i+8] >> 57; a[i+8] &= 0x1ffffffffffffffL;
    }
    a[16+1] += a[16] >> 57;
    a[16] &= 0x1ffffffffffffffL;
#endif
}

/* Shift the result in the high 1024 bits down to the bottom.
 *
 * r  A single precision number.
 * a  A single precision number.
 */
static void sp_2048_mont_shift_18(sp_digit* r, const sp_digit* a)
{
#ifdef WOLFSSL_SP_SMALL
    int i;
    word64 n;

    n = a[17] >> 55;
    for (i = 0; i < 17; i++) {
        n += (word64)a[18 + i] << 2;
        r[i] = n & 0x1ffffffffffffffL;
        n >>= 57;
    }
    n += (word64)a[35] << 2;
    r[17] = n;
#else
    word64 n;
    int i;

    n  = (word64)a[17];
    n  = n >> 55U;
    for (i = 0; i < 16; i += 8) {
        n += (word64)a[i+18] << 2U; r[i+0] = n & 0x1ffffffffffffffUL; n >>= 57U;
        n += (word64)a[i+19] << 2U; r[i+1] = n & 0x1ffffffffffffffUL; n >>= 57U;
        n += (word64)a[i+20] << 2U; r[i+2] = n & 0x1ffffffffffffffUL; n >>= 57U;
        n += (word64)a[i+21] << 2U; r[i+3] = n & 0x1ffffffffffffffUL; n >>= 57U;
        n += (word64)a[i+22] << 2U; r[i+4] = n & 0x1ffffffffffffffUL; n >>= 57U;
        n += (word64)a[i+23] << 2U; r[i+5] = n & 0x1ffffffffffffffUL; n >>= 57U;
        n += (word64)a[i+24] << 2U; r[i+6] = n & 0x1ffffffffffffffUL; n >>= 57U;
        n += (word64)a[i+25] << 2U; r[i+7] = n & 0x1ffffffffffffffUL; n >>= 57U;
    }
    n += (word64)a[34] << 2U; r[16] = n & 0x1ffffffffffffffUL; n >>= 57U;
    n += (word64)a[35] << 2U; r[17] = n;
#endif /* WOLFSSL_SP_SMALL */
    XMEMSET(&r[18], 0, sizeof(*r) * 18U);
}

/* Reduce the number back to 2048 bits using Montgomery reduction.
 *
 * a   A single precision number to reduce in place.
 * m   The single precision number representing the modulus.
 * mp  The digit representing the negative inverse of m mod 2^n.
 */
static void sp_2048_mont_reduce_18(sp_digit* a, const sp_digit* m, sp_digit mp)
{
    int i;
    sp_digit mu;

    sp_2048_norm_18(a + 18);

    for (i=0; i<17; i++) {
        mu = (a[i] * mp) & 0x1ffffffffffffffL;
        sp_2048_mul_add_18(a+i, m, mu);
        a[i+1] += a[i] >> 57;
    }
    mu = (a[i] * mp) & 0x7fffffffffffffL;
    sp_2048_mul_add_18(a+i, m, mu);
    a[i+1] += a[i] >> 57;
    a[i] &= 0x1ffffffffffffffL;

    sp_2048_mont_shift_18(a, a);
    sp_2048_cond_sub_18(a, a, m, 0 - (((a[17] >> 55) > 0) ?
            (sp_digit)1 : (sp_digit)0));
    sp_2048_norm_18(a);
}

/* Multiply two Montogmery form numbers mod the modulus (prime).
 * (r = a * b mod m)
 *
 * r   Result of multiplication.
 * a   First number to multiply in Montogmery form.
 * b   Second number to multiply in Montogmery form.
 * m   Modulus (prime).
 * mp  Montogmery mulitplier.
 */
static void sp_2048_mont_mul_18(sp_digit* r, const sp_digit* a, const sp_digit* b,
        const sp_digit* m, sp_digit mp)
{
    sp_2048_mul_18(r, a, b);
    sp_2048_mont_reduce_18(r, m, mp);
}

/* Square the Montgomery form number. (r = a * a mod m)
 *
 * r   Result of squaring.
 * a   Number to square in Montogmery form.
 * m   Modulus (prime).
 * mp  Montogmery mulitplier.
 */
static void sp_2048_mont_sqr_18(sp_digit* r, const sp_digit* a, const sp_digit* m,
        sp_digit mp)
{
    sp_2048_sqr_18(r, a);
    sp_2048_mont_reduce_18(r, m, mp);
}

/* Multiply a by scalar b into r. (r = a * b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A scalar.
 */
SP_NOINLINE static void sp_2048_mul_d_18(sp_digit* r, const sp_digit* a,
    sp_digit b)
{
#ifdef WOLFSSL_SP_SMALL
    int128_t tb = b;
    int128_t t = 0;
    int i;

    for (i = 0; i < 18; i++) {
        t += tb * a[i];
        r[i] = t & 0x1ffffffffffffffL;
        t >>= 57;
    }
    r[18] = (sp_digit)t;
#else
    int128_t tb = b;
    int128_t t[8];
    int i;

    t[0] = tb * a[0]; r[0] = t[0] & 0x1ffffffffffffffL;
    for (i = 0; i < 16; i += 8) {
        t[1] = tb * a[i+1];
        r[i+1] = (sp_digit)(t[0] >> 57) + (t[1] & 0x1ffffffffffffffL);
        t[2] = tb * a[i+2];
        r[i+2] = (sp_digit)(t[1] >> 57) + (t[2] & 0x1ffffffffffffffL);
        t[3] = tb * a[i+3];
        r[i+3] = (sp_digit)(t[2] >> 57) + (t[3] & 0x1ffffffffffffffL);
        t[4] = tb * a[i+4];
        r[i+4] = (sp_digit)(t[3] >> 57) + (t[4] & 0x1ffffffffffffffL);
        t[5] = tb * a[i+5];
        r[i+5] = (sp_digit)(t[4] >> 57) + (t[5] & 0x1ffffffffffffffL);
        t[6] = tb * a[i+6];
        r[i+6] = (sp_digit)(t[5] >> 57) + (t[6] & 0x1ffffffffffffffL);
        t[7] = tb * a[i+7];
        r[i+7] = (sp_digit)(t[6] >> 57) + (t[7] & 0x1ffffffffffffffL);
        t[0] = tb * a[i+8];
        r[i+8] = (sp_digit)(t[7] >> 57) + (t[0] & 0x1ffffffffffffffL);
    }
    t[1] = tb * a[17];
    r[17] = (sp_digit)(t[0] >> 57) + (t[1] & 0x1ffffffffffffffL);
    r[18] =  (sp_digit)(t[1] >> 57);
#endif /* WOLFSSL_SP_SMALL */
}

/* Conditionally add a and b using the mask m.
 * m is -1 to add and 0 when not.
 *
 * r  A single precision number representing conditional add result.
 * a  A single precision number to add with.
 * b  A single precision number to add.
 * m  Mask value to apply.
 */
static void sp_2048_cond_add_18(sp_digit* r, const sp_digit* a,
        const sp_digit* b, const sp_digit m)
{
#ifdef WOLFSSL_SP_SMALL
    int i;

    for (i = 0; i < 18; i++) {
        r[i] = a[i] + (b[i] & m);
    }
#else
    int i;

    for (i = 0; i < 16; i += 8) {
        r[i + 0] = a[i + 0] + (b[i + 0] & m);
        r[i + 1] = a[i + 1] + (b[i + 1] & m);
        r[i + 2] = a[i + 2] + (b[i + 2] & m);
        r[i + 3] = a[i + 3] + (b[i + 3] & m);
        r[i + 4] = a[i + 4] + (b[i + 4] & m);
        r[i + 5] = a[i + 5] + (b[i + 5] & m);
        r[i + 6] = a[i + 6] + (b[i + 6] & m);
        r[i + 7] = a[i + 7] + (b[i + 7] & m);
    }
    r[16] = a[16] + (b[16] & m);
    r[17] = a[17] + (b[17] & m);
#endif /* WOLFSSL_SP_SMALL */
}

#ifdef WOLFSSL_SMALL
/* Sub b from a into r. (r = a - b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A single precision integer.
 */
SP_NOINLINE static int sp_2048_sub_18(sp_digit* r, const sp_digit* a,
        const sp_digit* b)
{
    int i;

    for (i = 0; i < 18; i++) {
        r[i] = a[i] - b[i];
    }

    return 0;
}

#endif
#ifdef WOLFSSL_SMALL
/* Add b to a into r. (r = a + b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A single precision integer.
 */
SP_NOINLINE static int sp_2048_add_18(sp_digit* r, const sp_digit* a,
        const sp_digit* b)
{
    int i;

    for (i = 0; i < 18; i++) {
        r[i] = a[i] + b[i];
    }

    return 0;
}
#endif
#ifdef WOLFSSL_SP_DIV_64
static WC_INLINE sp_digit sp_2048_div_word_18(sp_digit d1, sp_digit d0,
    sp_digit dv)
{
    sp_digit d, r, t;

    /* All 57 bits from d1 and top 6 bits from d0. */
    d = (d1 << 6) | (d0 >> 51);
    r = d / dv;
    d -= r * dv;
    /* Up to 7 bits in r */
    /* Next 6 bits from d0. */
    r <<= 6;
    d <<= 6;
    d |= (d0 >> 45) & ((1 << 6) - 1);
    t = d / dv;
    d -= t * dv;
    r += t;
    /* Up to 13 bits in r */
    /* Next 6 bits from d0. */
    r <<= 6;
    d <<= 6;
    d |= (d0 >> 39) & ((1 << 6) - 1);
    t = d / dv;
    d -= t * dv;
    r += t;
    /* Up to 19 bits in r */
    /* Next 6 bits from d0. */
    r <<= 6;
    d <<= 6;
    d |= (d0 >> 33) & ((1 << 6) - 1);
    t = d / dv;
    d -= t * dv;
    r += t;
    /* Up to 25 bits in r */
    /* Next 6 bits from d0. */
    r <<= 6;
    d <<= 6;
    d |= (d0 >> 27) & ((1 << 6) - 1);
    t = d / dv;
    d -= t * dv;
    r += t;
    /* Up to 31 bits in r */
    /* Next 6 bits from d0. */
    r <<= 6;
    d <<= 6;
    d |= (d0 >> 21) & ((1 << 6) - 1);
    t = d / dv;
    d -= t * dv;
    r += t;
    /* Up to 37 bits in r */
    /* Next 6 bits from d0. */
    r <<= 6;
    d <<= 6;
    d |= (d0 >> 15) & ((1 << 6) - 1);
    t = d / dv;
    d -= t * dv;
    r += t;
    /* Up to 43 bits in r */
    /* Next 6 bits from d0. */
    r <<= 6;
    d <<= 6;
    d |= (d0 >> 9) & ((1 << 6) - 1);
    t = d / dv;
    d -= t * dv;
    r += t;
    /* Up to 49 bits in r */
    /* Next 6 bits from d0. */
    r <<= 6;
    d <<= 6;
    d |= (d0 >> 3) & ((1 << 6) - 1);
    t = d / dv;
    d -= t * dv;
    r += t;
    /* Up to 55 bits in r */
    /* Remaining 3 bits from d0. */
    r <<= 3;
    d <<= 3;
    d |= d0 & ((1 << 3) - 1);
    t = d / dv;
    r += t;

    return r;
}
#endif /* WOLFSSL_SP_DIV_64 */

/* Divide d in a and put remainder into r (m*d + r = a)
 * m is not calculated as it is not needed at this time.
 *
 * a  Number to be divided.
 * d  Number to divide with.
 * m  Multiplier result.
 * r  Remainder from the division.
 * returns MEMORY_E when unable to allocate memory and MP_OKAY otherwise.
 */
static int sp_2048_div_18(const sp_digit* a, const sp_digit* d, sp_digit* m,
        sp_digit* r)
{
    int i;
#ifndef WOLFSSL_SP_DIV_64
    int128_t d1;
#endif
    sp_digit dv, r1;
#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    sp_digit* td;
#else
    sp_digit t1d[36], t2d[18 + 1];
#endif
    sp_digit* t1;
    sp_digit* t2;
    int err = MP_OKAY;

    (void)m;

#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    td = (sp_digit*)XMALLOC(sizeof(sp_digit) * (3 * 18 + 1), NULL,
                                                       DYNAMIC_TYPE_TMP_BUFFER);
    if (td == NULL) {
        err = MEMORY_E;
    }
#endif

    if (err == MP_OKAY) {
#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
        t1 = td;
        t2 = td + 2 * 18;
#else
        t1 = t1d;
        t2 = t2d;
#endif

        dv = d[17];
        XMEMCPY(t1, a, sizeof(*t1) * 2U * 18U);
        for (i=17; i>=0; i--) {
            t1[18 + i] += t1[18 + i - 1] >> 57;
            t1[18 + i - 1] &= 0x1ffffffffffffffL;
#ifndef WOLFSSL_SP_DIV_64
            d1 = t1[18 + i];
            d1 <<= 57;
            d1 += t1[18 + i - 1];
            r1 = (sp_digit)(d1 / dv);
#else
            r1 = sp_2048_div_word_18(t1[18 + i], t1[18 + i - 1], dv);
#endif

            sp_2048_mul_d_18(t2, d, r1);
            (void)sp_2048_sub_18(&t1[i], &t1[i], t2);
            t1[18 + i] -= t2[18];
            t1[18 + i] += t1[18 + i - 1] >> 57;
            t1[18 + i - 1] &= 0x1ffffffffffffffL;
            r1 = (((-t1[18 + i]) << 57) - t1[18 + i - 1]) / dv;
            r1++;
            sp_2048_mul_d_18(t2, d, r1);
            (void)sp_2048_add_18(&t1[i], &t1[i], t2);
            t1[18 + i] += t1[18 + i - 1] >> 57;
            t1[18 + i - 1] &= 0x1ffffffffffffffL;
        }
        t1[18 - 1] += t1[18 - 2] >> 57;
        t1[18 - 2] &= 0x1ffffffffffffffL;
        r1 = t1[18 - 1] / dv;

        sp_2048_mul_d_18(t2, d, r1);
        (void)sp_2048_sub_18(t1, t1, t2);
        XMEMCPY(r, t1, sizeof(*r) * 2U * 18U);
        for (i=0; i<17; i++) {
            r[i+1] += r[i] >> 57;
            r[i] &= 0x1ffffffffffffffL;
        }
        sp_2048_cond_add_18(r, r, d, 0 - ((r[17] < 0) ?
                    (sp_digit)1 : (sp_digit)0));
    }

#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (td != NULL) {
        XFREE(td, NULL, DYNAMIC_TYPE_TMP_BUFFER);
    }
#endif

    return err;
}

/* Reduce a modulo m into r. (r = a mod m)
 *
 * r  A single precision number that is the reduced result.
 * a  A single precision number that is to be reduced.
 * m  A single precision number that is the modulus to reduce with.
 * returns MEMORY_E when unable to allocate memory and MP_OKAY otherwise.
 */
static int sp_2048_mod_18(sp_digit* r, const sp_digit* a, const sp_digit* m)
{
    return sp_2048_div_18(a, m, NULL, r);
}

/* Modular exponentiate a to the e mod m. (r = a^e mod m)
 *
 * r     A single precision number that is the result of the operation.
 * a     A single precision number being exponentiated.
 * e     A single precision number that is the exponent.
 * bits  The number of bits in the exponent.
 * m     A single precision number that is the modulus.
 * returns 0 on success and MEMORY_E on dynamic memory allocation failure.
 */
static int sp_2048_mod_exp_18(sp_digit* r, const sp_digit* a, const sp_digit* e, int bits,
    const sp_digit* m, int reduceA)
{
#ifdef WOLFSSL_SP_SMALL
#if !defined(WOLFSSL_SP_NO_MALLOC)
    sp_digit* td;
#else
    sp_digit td[3 * 36];
#endif
    sp_digit* t[3];
    sp_digit* norm;
    sp_digit mp = 1;
    sp_digit n;
    int i;
    int c, y;
    int err = MP_OKAY;

#if !defined(WOLFSSL_SP_NO_MALLOC)
    td = (sp_digit*)XMALLOC(sizeof(sp_digit) * 3 * 18 * 2, NULL,
                            DYNAMIC_TYPE_TMP_BUFFER);
    if (td == NULL) {
        err = MEMORY_E;
    }
#endif

    if (err == MP_OKAY) {
        norm = td;
        for (i=0; i<3; i++) {
#if !defined(WOLFSSL_SP_NO_MALLOC)
            t[i] = td + (i * 18 * 2);
#else
            t[i] = &td[i * 18 * 2];
#endif
            XMEMSET(t[i], 0, sizeof(sp_digit) * 18U * 2U);
        }

        sp_2048_mont_setup(m, &mp);
        sp_2048_mont_norm_18(norm, m);

        if (reduceA != 0) {
            err = sp_2048_mod_18(t[1], a, m);
        }
        else {
            XMEMCPY(t[1], a, sizeof(sp_digit) * 18U);
        }
    }
    if (err == MP_OKAY) {
        sp_2048_mul_18(t[1], t[1], norm);
        err = sp_2048_mod_18(t[1], t[1], m);
    }

    if (err == MP_OKAY) {
        i = bits / 57;
        c = bits % 57;
        n = e[i--] << (57 - c);
        for (; ; c--) {
            if (c == 0) {
                if (i == -1) {
                    break;
                }

                n = e[i--];
                c = 57;
            }

            y = (n >> 56) & 1;
            n <<= 1;

            sp_2048_mont_mul_18(t[y^1], t[0], t[1], m, mp);

            XMEMCPY(t[2], (void*)(((size_t)t[0] & addr_mask[y^1]) +
                                  ((size_t)t[1] & addr_mask[y])),
                                  sizeof(*t[2]) * 18 * 2);
            sp_2048_mont_sqr_18(t[2], t[2], m, mp);
            XMEMCPY((void*)(((size_t)t[0] & addr_mask[y^1]) +
                            ((size_t)t[1] & addr_mask[y])), t[2],
                            sizeof(*t[2]) * 18 * 2);
        }

        sp_2048_mont_reduce_18(t[0], m, mp);
        n = sp_2048_cmp_18(t[0], m);
        sp_2048_cond_sub_18(t[0], t[0], m, ((n < 0) ?
                    (sp_digit)1 : (sp_digit)0) - 1);
        XMEMCPY(r, t[0], sizeof(*r) * 18 * 2);

    }

#if !defined(WOLFSSL_SP_NO_MALLOC)
    if (td != NULL) {
        XFREE(td, NULL, DYNAMIC_TYPE_TMP_BUFFER);
    }
#endif

    return err;
#elif !defined(WC_NO_CACHE_RESISTANT)
#if defined(WOLFSSL_SMALL_STACK) && !defined(WOLFSSL_SP_NO_MALLOC)
    sp_digit* td;
#else
    sp_digit td[3 * 36];
#endif
    sp_digit* t[3];
    sp_digit* norm;
    sp_digit mp = 1;
    sp_digit n;
    int i;
    int c, y;
    int err = MP_OKAY;

#ifdef WOLFSSL_SMALL_STACK
    td = (sp_digit*)XMALLOC(sizeof(sp_digit) * 3 * 18 * 2, NULL,
                            DYNAMIC_TYPE_TMP_BUFFER);
    if (td == NULL) {
        err = MEMORY_E;
    }
#endif

    if (err == MP_OKAY) {
        norm = td;
        for (i=0; i<3; i++) {
#if defined(WOLFSSL_SMALL_STACK) && !defined(WOLFSSL_SP_NO_MALLOC)
            t[i] = td + (i * 18 * 2);
#else
            t[i] = &td[i * 18 * 2];
#endif
        }

        sp_2048_mont_setup(m, &mp);
        sp_2048_mont_norm_18(norm, m);

        if (reduceA != 0) {
            err = sp_2048_mod_18(t[1], a, m);
            if (err == MP_OKAY) {
                sp_2048_mul_18(t[1], t[1], norm);
                err = sp_2048_mod_18(t[1], t[1], m);
            }
        }
        else {
            sp_2048_mul_18(t[1], a, norm);
            err = sp_2048_mod_18(t[1], t[1], m);
        }
    }

    if (err == MP_OKAY) {
        i = bits / 57;
        c = bits % 57;
        n = e[i--] << (57 - c);
        for (; ; c--) {
            if (c == 0) {
                if (i == -1) {
                    break;
                }

                n = e[i--];
                c = 57;
            }

            y = (n >> 56) & 1;
            n <<= 1;

            sp_2048_mont_mul_18(t[y^1], t[0], t[1], m, mp);

            XMEMCPY(t[2], (void*)(((size_t)t[0] & addr_mask[y^1]) +
                                  ((size_t)t[1] & addr_mask[y])), 
                                  sizeof(*t[2]) * 18 * 2);
            sp_2048_mont_sqr_18(t[2], t[2], m, mp);
            XMEMCPY((void*)(((size_t)t[0] & addr_mask[y^1]) +
                            ((size_t)t[1] & addr_mask[y])), t[2], 
                            sizeof(*t[2]) * 18 * 2);
        }

        sp_2048_mont_reduce_18(t[0], m, mp);
        n = sp_2048_cmp_18(t[0], m);
        sp_2048_cond_sub_18(t[0], t[0], m, ((n < 0) ?
                    (sp_digit)1 : (sp_digit)0) - 1);
        XMEMCPY(r, t[0], sizeof(*r) * 18 * 2);
    }

#ifdef WOLFSSL_SMALL_STACK
    if (td != NULL) {
        XFREE(td, NULL, DYNAMIC_TYPE_TMP_BUFFER);
    }
#endif

    return err;
#else
#if defined(WOLFSSL_SMALL_STACK) && !defined(WOLFSSL_SP_NO_MALLOC)
    sp_digit* td;
#else
    sp_digit td[(32 * 36) + 36];
#endif
    sp_digit* t[32];
    sp_digit* rt;
    sp_digit* norm;
    sp_digit mp = 1;
    sp_digit n;
    int i;
    int c, y;
    int err = MP_OKAY;

#if defined(WOLFSSL_SMALL_STACK) && !defined(WOLFSSL_SP_NO_MALLOC)
    td = (sp_digit*)XMALLOC(sizeof(sp_digit) * ((32 * 36) + 36), NULL,
                            DYNAMIC_TYPE_TMP_BUFFER);
    if (td == NULL) {
        err = MEMORY_E;
    }
#endif

    if (err == MP_OKAY) {
        norm = td;
#if defined(WOLFSSL_SMALL_STACK) && !defined(WOLFSSL_SP_NO_MALLOC)
        for (i=0; i<32; i++)
            t[i] = td + i * 36;
        rt = td + 1152;
#else
        for (i=0; i<32; i++)
            t[i] = &td[i * 36];
        rt = &td[1152];
#endif

        sp_2048_mont_setup(m, &mp);
        sp_2048_mont_norm_18(norm, m);

        if (reduceA != 0) {
            err = sp_2048_mod_18(t[1], a, m);
            if (err == MP_OKAY) {
                sp_2048_mul_18(t[1], t[1], norm);
                err = sp_2048_mod_18(t[1], t[1], m);
            }
        }
        else {
            sp_2048_mul_18(t[1], a, norm);
            err = sp_2048_mod_18(t[1], t[1], m);
        }
    }

    if (err == MP_OKAY) {
        sp_2048_mont_sqr_18(t[ 2], t[ 1], m, mp);
        sp_2048_mont_mul_18(t[ 3], t[ 2], t[ 1], m, mp);
        sp_2048_mont_sqr_18(t[ 4], t[ 2], m, mp);
        sp_2048_mont_mul_18(t[ 5], t[ 3], t[ 2], m, mp);
        sp_2048_mont_sqr_18(t[ 6], t[ 3], m, mp);
        sp_2048_mont_mul_18(t[ 7], t[ 4], t[ 3], m, mp);
        sp_2048_mont_sqr_18(t[ 8], t[ 4], m, mp);
        sp_2048_mont_mul_18(t[ 9], t[ 5], t[ 4], m, mp);
        sp_2048_mont_sqr_18(t[10], t[ 5], m, mp);
        sp_2048_mont_mul_18(t[11], t[ 6], t[ 5], m, mp);
        sp_2048_mont_sqr_18(t[12], t[ 6], m, mp);
        sp_2048_mont_mul_18(t[13], t[ 7], t[ 6], m, mp);
        sp_2048_mont_sqr_18(t[14], t[ 7], m, mp);
        sp_2048_mont_mul_18(t[15], t[ 8], t[ 7], m, mp);
        sp_2048_mont_sqr_18(t[16], t[ 8], m, mp);
        sp_2048_mont_mul_18(t[17], t[ 9], t[ 8], m, mp);
        sp_2048_mont_sqr_18(t[18], t[ 9], m, mp);
        sp_2048_mont_mul_18(t[19], t[10], t[ 9], m, mp);
        sp_2048_mont_sqr_18(t[20], t[10], m, mp);
        sp_2048_mont_mul_18(t[21], t[11], t[10], m, mp);
        sp_2048_mont_sqr_18(t[22], t[11], m, mp);
        sp_2048_mont_mul_18(t[23], t[12], t[11], m, mp);
        sp_2048_mont_sqr_18(t[24], t[12], m, mp);
        sp_2048_mont_mul_18(t[25], t[13], t[12], m, mp);
        sp_2048_mont_sqr_18(t[26], t[13], m, mp);
        sp_2048_mont_mul_18(t[27], t[14], t[13], m, mp);
        sp_2048_mont_sqr_18(t[28], t[14], m, mp);
        sp_2048_mont_mul_18(t[29], t[15], t[14], m, mp);
        sp_2048_mont_sqr_18(t[30], t[15], m, mp);
        sp_2048_mont_mul_18(t[31], t[16], t[15], m, mp);

        bits = ((bits + 4) / 5) * 5;
        i = ((bits + 56) / 57) - 1;
        c = bits % 57;
        if (c == 0) {
            c = 57;
        }
        if (i < 18) {
            n = e[i--] << (64 - c);
        }
        else {
            n = 0;
            i--;
        }
        if (c < 5) {
            n |= e[i--] << (7 - c);
            c += 57;
        }
        y = (n >> 59) & 0x1f;
        n <<= 5;
        c -= 5;
        XMEMCPY(rt, t[y], sizeof(sp_digit) * 36);
        for (; i>=0 || c>=5; ) {
            if (c < 5) {
                n |= e[i--] << (7 - c);
                c += 57;
            }
            y = (n >> 59) & 0x1f;
            n <<= 5;
            c -= 5;

            sp_2048_mont_sqr_18(rt, rt, m, mp);
            sp_2048_mont_sqr_18(rt, rt, m, mp);
            sp_2048_mont_sqr_18(rt, rt, m, mp);
            sp_2048_mont_sqr_18(rt, rt, m, mp);
            sp_2048_mont_sqr_18(rt, rt, m, mp);

            sp_2048_mont_mul_18(rt, rt, t[y], m, mp);
        }

        sp_2048_mont_reduce_18(rt, m, mp);
        n = sp_2048_cmp_18(rt, m);
        sp_2048_cond_sub_18(rt, rt, m, ((n < 0) ?
                   (sp_digit)1 : (sp_digit)0) - 1);
        XMEMCPY(r, rt, sizeof(sp_digit) * 36);
    }

#if defined(WOLFSSL_SMALL_STACK) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (td != NULL) {
        XFREE(td, NULL, DYNAMIC_TYPE_TMP_BUFFER);
    }
#endif

    return err;
#endif
}

#endif /* (WOLFSSL_HAVE_SP_RSA || WOLFSSL_HAVE_SP_DH) && !WOLFSSL_RSA_PUBLIC_ONLY */

/* r = 2^n mod m where n is the number of bits to reduce by.
 * Given m must be 2048 bits, just need to subtract.
 *
 * r  A single precision number.
 * m  A single precision number.
 */
static void sp_2048_mont_norm_36(sp_digit* r, const sp_digit* m)
{
    /* Set r = 2^n - 1. */
#ifdef WOLFSSL_SP_SMALL
    int i;

    for (i=0; i<35; i++) {
        r[i] = 0x1ffffffffffffffL;
    }
#else
    int i;

    for (i = 0; i < 32; i += 8) {
        r[i + 0] = 0x1ffffffffffffffL;
        r[i + 1] = 0x1ffffffffffffffL;
        r[i + 2] = 0x1ffffffffffffffL;
        r[i + 3] = 0x1ffffffffffffffL;
        r[i + 4] = 0x1ffffffffffffffL;
        r[i + 5] = 0x1ffffffffffffffL;
        r[i + 6] = 0x1ffffffffffffffL;
        r[i + 7] = 0x1ffffffffffffffL;
    }
    r[32] = 0x1ffffffffffffffL;
    r[33] = 0x1ffffffffffffffL;
    r[34] = 0x1ffffffffffffffL;
#endif
    r[35] = 0x1fffffffffffffL;

    /* r = (2^n - 1) mod n */
    (void)sp_2048_sub_36(r, r, m);

    /* Add one so r = 2^n mod m */
    r[0] += 1;
}

/* Compare a with b in constant time.
 *
 * a  A single precision integer.
 * b  A single precision integer.
 * return -ve, 0 or +ve if a is less than, equal to or greater than b
 * respectively.
 */
static sp_digit sp_2048_cmp_36(const sp_digit* a, const sp_digit* b)
{
    sp_digit r = 0;
#ifdef WOLFSSL_SP_SMALL
    int i;

    for (i=35; i>=0; i--) {
        r |= (a[i] - b[i]) & (0 - ((r == 0) ? (sp_digit)1 : (sp_digit)0));
    }
#else
    int i;

    r |= (a[35] - b[35]) & (0 - ((r == 0) ? (sp_digit)1 : (sp_digit)0));
    r |= (a[34] - b[34]) & (0 - ((r == 0) ? (sp_digit)1 : (sp_digit)0));
    r |= (a[33] - b[33]) & (0 - ((r == 0) ? (sp_digit)1 : (sp_digit)0));
    r |= (a[32] - b[32]) & (0 - ((r == 0) ? (sp_digit)1 : (sp_digit)0));
    for (i = 24; i >= 0; i -= 8) {
        r |= (a[i + 7] - b[i + 7]) & (0 - ((r == 0) ? (sp_digit)1 : (sp_digit)0));
        r |= (a[i + 6] - b[i + 6]) & (0 - ((r == 0) ? (sp_digit)1 : (sp_digit)0));
        r |= (a[i + 5] - b[i + 5]) & (0 - ((r == 0) ? (sp_digit)1 : (sp_digit)0));
        r |= (a[i + 4] - b[i + 4]) & (0 - ((r == 0) ? (sp_digit)1 : (sp_digit)0));
        r |= (a[i + 3] - b[i + 3]) & (0 - ((r == 0) ? (sp_digit)1 : (sp_digit)0));
        r |= (a[i + 2] - b[i + 2]) & (0 - ((r == 0) ? (sp_digit)1 : (sp_digit)0));
        r |= (a[i + 1] - b[i + 1]) & (0 - ((r == 0) ? (sp_digit)1 : (sp_digit)0));
        r |= (a[i + 0] - b[i + 0]) & (0 - ((r == 0) ? (sp_digit)1 : (sp_digit)0));
    }
#endif /* WOLFSSL_SP_SMALL */

    return r;
}

/* Conditionally subtract b from a using the mask m.
 * m is -1 to subtract and 0 when not.
 *
 * r  A single precision number representing condition subtract result.
 * a  A single precision number to subtract from.
 * b  A single precision number to subtract.
 * m  Mask value to apply.
 */
static void sp_2048_cond_sub_36(sp_digit* r, const sp_digit* a,
        const sp_digit* b, const sp_digit m)
{
#ifdef WOLFSSL_SP_SMALL
    int i;

    for (i = 0; i < 36; i++) {
        r[i] = a[i] - (b[i] & m);
    }
#else
    int i;

    for (i = 0; i < 32; i += 8) {
        r[i + 0] = a[i + 0] - (b[i + 0] & m);
        r[i + 1] = a[i + 1] - (b[i + 1] & m);
        r[i + 2] = a[i + 2] - (b[i + 2] & m);
        r[i + 3] = a[i + 3] - (b[i + 3] & m);
        r[i + 4] = a[i + 4] - (b[i + 4] & m);
        r[i + 5] = a[i + 5] - (b[i + 5] & m);
        r[i + 6] = a[i + 6] - (b[i + 6] & m);
        r[i + 7] = a[i + 7] - (b[i + 7] & m);
    }
    r[32] = a[32] - (b[32] & m);
    r[33] = a[33] - (b[33] & m);
    r[34] = a[34] - (b[34] & m);
    r[35] = a[35] - (b[35] & m);
#endif /* WOLFSSL_SP_SMALL */
}

/* Mul a by scalar b and add into r. (r += a * b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A scalar.
 */
SP_NOINLINE static void sp_2048_mul_add_36(sp_digit* r, const sp_digit* a,
        const sp_digit b)
{
#ifdef WOLFSSL_SP_SMALL
    int128_t tb = b;
    int128_t t = 0;
    int i;

    for (i = 0; i < 36; i++) {
        t += (tb * a[i]) + r[i];
        r[i] = t & 0x1ffffffffffffffL;
        t >>= 57;
    }
    r[36] += t;
#else
    int128_t tb = b;
    int128_t t[8];
    int i;

    t[0] = tb * a[0]; r[0] += (sp_digit)(t[0] & 0x1ffffffffffffffL);
    for (i = 0; i < 32; i += 8) {
        t[1] = tb * a[i+1];
        r[i+1] += (sp_digit)((t[0] >> 57) + (t[1] & 0x1ffffffffffffffL));
        t[2] = tb * a[i+2];
        r[i+2] += (sp_digit)((t[1] >> 57) + (t[2] & 0x1ffffffffffffffL));
        t[3] = tb * a[i+3];
        r[i+3] += (sp_digit)((t[2] >> 57) + (t[3] & 0x1ffffffffffffffL));
        t[4] = tb * a[i+4];
        r[i+4] += (sp_digit)((t[3] >> 57) + (t[4] & 0x1ffffffffffffffL));
        t[5] = tb * a[i+5];
        r[i+5] += (sp_digit)((t[4] >> 57) + (t[5] & 0x1ffffffffffffffL));
        t[6] = tb * a[i+6];
        r[i+6] += (sp_digit)((t[5] >> 57) + (t[6] & 0x1ffffffffffffffL));
        t[7] = tb * a[i+7];
        r[i+7] += (sp_digit)((t[6] >> 57) + (t[7] & 0x1ffffffffffffffL));
        t[0] = tb * a[i+8];
        r[i+8] += (sp_digit)((t[7] >> 57) + (t[0] & 0x1ffffffffffffffL));
    }
    t[1] = tb * a[33]; r[33] += (sp_digit)((t[0] >> 57) + (t[1] & 0x1ffffffffffffffL));
    t[2] = tb * a[34]; r[34] += (sp_digit)((t[1] >> 57) + (t[2] & 0x1ffffffffffffffL));
    t[3] = tb * a[35]; r[35] += (sp_digit)((t[2] >> 57) + (t[3] & 0x1ffffffffffffffL));
    r[36] +=  (sp_digit)(t[3] >> 57);
#endif /* WOLFSSL_SP_SMALL */
}

/* Normalize the values in each word to 57.
 *
 * a  Array of sp_digit to normalize.
 */
static void sp_2048_norm_36(sp_digit* a)
{
#ifdef WOLFSSL_SP_SMALL
    int i;
    for (i = 0; i < 35; i++) {
        a[i+1] += a[i] >> 57;
        a[i] &= 0x1ffffffffffffffL;
    }
#else
    int i;
    for (i = 0; i < 32; i += 8) {
        a[i+1] += a[i+0] >> 57; a[i+0] &= 0x1ffffffffffffffL;
        a[i+2] += a[i+1] >> 57; a[i+1] &= 0x1ffffffffffffffL;
        a[i+3] += a[i+2] >> 57; a[i+2] &= 0x1ffffffffffffffL;
        a[i+4] += a[i+3] >> 57; a[i+3] &= 0x1ffffffffffffffL;
        a[i+5] += a[i+4] >> 57; a[i+4] &= 0x1ffffffffffffffL;
        a[i+6] += a[i+5] >> 57; a[i+5] &= 0x1ffffffffffffffL;
        a[i+7] += a[i+6] >> 57; a[i+6] &= 0x1ffffffffffffffL;
        a[i+8] += a[i+7] >> 57; a[i+7] &= 0x1ffffffffffffffL;
        a[i+9] += a[i+8] >> 57; a[i+8] &= 0x1ffffffffffffffL;
    }
    a[32+1] += a[32] >> 57;
    a[32] &= 0x1ffffffffffffffL;
    a[33+1] += a[33] >> 57;
    a[33] &= 0x1ffffffffffffffL;
    a[34+1] += a[34] >> 57;
    a[34] &= 0x1ffffffffffffffL;
#endif
}

/* Shift the result in the high 2048 bits down to the bottom.
 *
 * r  A single precision number.
 * a  A single precision number.
 */
static void sp_2048_mont_shift_36(sp_digit* r, const sp_digit* a)
{
#ifdef WOLFSSL_SP_SMALL
    int i;
    sp_digit n, s;

    s = a[36];
    n = a[35] >> 53;
    for (i = 0; i < 35; i++) {
        n += (s & 0x1ffffffffffffffL) << 4;
        r[i] = n & 0x1ffffffffffffffL;
        n >>= 57;
        s = a[37 + i] + (s >> 57);
    }
    n += s << 4;
    r[35] = n;
#else
    sp_digit n, s;
    int i;

    s = a[36]; n = a[35] >> 53;
    for (i = 0; i < 32; i += 8) {
        n += (s & 0x1ffffffffffffffL) << 4; r[i+0] = n & 0x1ffffffffffffffL;
        n >>= 57; s = a[i+37] + (s >> 57);
        n += (s & 0x1ffffffffffffffL) << 4; r[i+1] = n & 0x1ffffffffffffffL;
        n >>= 57; s = a[i+38] + (s >> 57);
        n += (s & 0x1ffffffffffffffL) << 4; r[i+2] = n & 0x1ffffffffffffffL;
        n >>= 57; s = a[i+39] + (s >> 57);
        n += (s & 0x1ffffffffffffffL) << 4; r[i+3] = n & 0x1ffffffffffffffL;
        n >>= 57; s = a[i+40] + (s >> 57);
        n += (s & 0x1ffffffffffffffL) << 4; r[i+4] = n & 0x1ffffffffffffffL;
        n >>= 57; s = a[i+41] + (s >> 57);
        n += (s & 0x1ffffffffffffffL) << 4; r[i+5] = n & 0x1ffffffffffffffL;
        n >>= 57; s = a[i+42] + (s >> 57);
        n += (s & 0x1ffffffffffffffL) << 4; r[i+6] = n & 0x1ffffffffffffffL;
        n >>= 57; s = a[i+43] + (s >> 57);
        n += (s & 0x1ffffffffffffffL) << 4; r[i+7] = n & 0x1ffffffffffffffL;
        n >>= 57; s = a[i+44] + (s >> 57);
    }
    n += (s & 0x1ffffffffffffffL) << 4; r[32] = n & 0x1ffffffffffffffL;
    n >>= 57; s = a[69] + (s >> 57);
    n += (s & 0x1ffffffffffffffL) << 4; r[33] = n & 0x1ffffffffffffffL;
    n >>= 57; s = a[70] + (s >> 57);
    n += (s & 0x1ffffffffffffffL) << 4; r[34] = n & 0x1ffffffffffffffL;
    n >>= 57; s = a[71] + (s >> 57);
    n += s << 4;              r[35] = n;
#endif /* WOLFSSL_SP_SMALL */
    XMEMSET(&r[36], 0, sizeof(*r) * 36U);
}

/* Reduce the number back to 2048 bits using Montgomery reduction.
 *
 * a   A single precision number to reduce in place.
 * m   The single precision number representing the modulus.
 * mp  The digit representing the negative inverse of m mod 2^n.
 */
static void sp_2048_mont_reduce_36(sp_digit* a, const sp_digit* m, sp_digit mp)
{
    int i;
    sp_digit mu;

    sp_2048_norm_36(a + 36);

#ifdef WOLFSSL_SP_DH
    if (mp != 1) {
        for (i=0; i<35; i++) {
            mu = (a[i] * mp) & 0x1ffffffffffffffL;
            sp_2048_mul_add_36(a+i, m, mu);
            a[i+1] += a[i] >> 57;
        }
        mu = (a[i] * mp) & 0x1fffffffffffffL;
        sp_2048_mul_add_36(a+i, m, mu);
        a[i+1] += a[i] >> 57;
        a[i] &= 0x1ffffffffffffffL;
    }
    else {
        for (i=0; i<35; i++) {
            mu = a[i] & 0x1ffffffffffffffL;
            sp_2048_mul_add_36(a+i, m, mu);
            a[i+1] += a[i] >> 57;
        }
        mu = a[i] & 0x1fffffffffffffL;
        sp_2048_mul_add_36(a+i, m, mu);
        a[i+1] += a[i] >> 57;
        a[i] &= 0x1ffffffffffffffL;
    }
#else
    for (i=0; i<35; i++) {
        mu = (a[i] * mp) & 0x1ffffffffffffffL;
        sp_2048_mul_add_36(a+i, m, mu);
        a[i+1] += a[i] >> 57;
    }
    mu = (a[i] * mp) & 0x1fffffffffffffL;
    sp_2048_mul_add_36(a+i, m, mu);
    a[i+1] += a[i] >> 57;
    a[i] &= 0x1ffffffffffffffL;
#endif

    sp_2048_mont_shift_36(a, a);
    sp_2048_cond_sub_36(a, a, m, 0 - (((a[35] >> 53) > 0) ?
            (sp_digit)1 : (sp_digit)0));
    sp_2048_norm_36(a);
}

/* Multiply two Montogmery form numbers mod the modulus (prime).
 * (r = a * b mod m)
 *
 * r   Result of multiplication.
 * a   First number to multiply in Montogmery form.
 * b   Second number to multiply in Montogmery form.
 * m   Modulus (prime).
 * mp  Montogmery mulitplier.
 */
static void sp_2048_mont_mul_36(sp_digit* r, const sp_digit* a, const sp_digit* b,
        const sp_digit* m, sp_digit mp)
{
    sp_2048_mul_36(r, a, b);
    sp_2048_mont_reduce_36(r, m, mp);
}

/* Square the Montgomery form number. (r = a * a mod m)
 *
 * r   Result of squaring.
 * a   Number to square in Montogmery form.
 * m   Modulus (prime).
 * mp  Montogmery mulitplier.
 */
static void sp_2048_mont_sqr_36(sp_digit* r, const sp_digit* a, const sp_digit* m,
        sp_digit mp)
{
    sp_2048_sqr_36(r, a);
    sp_2048_mont_reduce_36(r, m, mp);
}

/* Conditionally add a and b using the mask m.
 * m is -1 to add and 0 when not.
 *
 * r  A single precision number representing conditional add result.
 * a  A single precision number to add with.
 * b  A single precision number to add.
 * m  Mask value to apply.
 */
static void sp_2048_cond_add_36(sp_digit* r, const sp_digit* a,
        const sp_digit* b, const sp_digit m)
{
#ifdef WOLFSSL_SP_SMALL
    int i;

    for (i = 0; i < 36; i++) {
        r[i] = a[i] + (b[i] & m);
    }
#else
    int i;

    for (i = 0; i < 32; i += 8) {
        r[i + 0] = a[i + 0] + (b[i + 0] & m);
        r[i + 1] = a[i + 1] + (b[i + 1] & m);
        r[i + 2] = a[i + 2] + (b[i + 2] & m);
        r[i + 3] = a[i + 3] + (b[i + 3] & m);
        r[i + 4] = a[i + 4] + (b[i + 4] & m);
        r[i + 5] = a[i + 5] + (b[i + 5] & m);
        r[i + 6] = a[i + 6] + (b[i + 6] & m);
        r[i + 7] = a[i + 7] + (b[i + 7] & m);
    }
    r[32] = a[32] + (b[32] & m);
    r[33] = a[33] + (b[33] & m);
    r[34] = a[34] + (b[34] & m);
    r[35] = a[35] + (b[35] & m);
#endif /* WOLFSSL_SP_SMALL */
}

#ifdef WOLFSSL_SMALL
/* Sub b from a into r. (r = a - b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A single precision integer.
 */
SP_NOINLINE static int sp_2048_sub_36(sp_digit* r, const sp_digit* a,
        const sp_digit* b)
{
    int i;

    for (i = 0; i < 36; i++) {
        r[i] = a[i] - b[i];
    }

    return 0;
}

#endif
#ifdef WOLFSSL_SMALL
/* Add b to a into r. (r = a + b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A single precision integer.
 */
SP_NOINLINE static int sp_2048_add_36(sp_digit* r, const sp_digit* a,
        const sp_digit* b)
{
    int i;

    for (i = 0; i < 36; i++) {
        r[i] = a[i] + b[i];
    }

    return 0;
}
#endif
#ifdef WOLFSSL_SP_DIV_64
static WC_INLINE sp_digit sp_2048_div_word_36(sp_digit d1, sp_digit d0,
    sp_digit dv)
{
    sp_digit d, r, t;

    /* All 57 bits from d1 and top 6 bits from d0. */
    d = (d1 << 6) | (d0 >> 51);
    r = d / dv;
    d -= r * dv;
    /* Up to 7 bits in r */
    /* Next 6 bits from d0. */
    r <<= 6;
    d <<= 6;
    d |= (d0 >> 45) & ((1 << 6) - 1);
    t = d / dv;
    d -= t * dv;
    r += t;
    /* Up to 13 bits in r */
    /* Next 6 bits from d0. */
    r <<= 6;
    d <<= 6;
    d |= (d0 >> 39) & ((1 << 6) - 1);
    t = d / dv;
    d -= t * dv;
    r += t;
    /* Up to 19 bits in r */
    /* Next 6 bits from d0. */
    r <<= 6;
    d <<= 6;
    d |= (d0 >> 33) & ((1 << 6) - 1);
    t = d / dv;
    d -= t * dv;
    r += t;
    /* Up to 25 bits in r */
    /* Next 6 bits from d0. */
    r <<= 6;
    d <<= 6;
    d |= (d0 >> 27) & ((1 << 6) - 1);
    t = d / dv;
    d -= t * dv;
    r += t;
    /* Up to 31 bits in r */
    /* Next 6 bits from d0. */
    r <<= 6;
    d <<= 6;
    d |= (d0 >> 21) & ((1 << 6) - 1);
    t = d / dv;
    d -= t * dv;
    r += t;
    /* Up to 37 bits in r */
    /* Next 6 bits from d0. */
    r <<= 6;
    d <<= 6;
    d |= (d0 >> 15) & ((1 << 6) - 1);
    t = d / dv;
    d -= t * dv;
    r += t;
    /* Up to 43 bits in r */
    /* Next 6 bits from d0. */
    r <<= 6;
    d <<= 6;
    d |= (d0 >> 9) & ((1 << 6) - 1);
    t = d / dv;
    d -= t * dv;
    r += t;
    /* Up to 49 bits in r */
    /* Next 6 bits from d0. */
    r <<= 6;
    d <<= 6;
    d |= (d0 >> 3) & ((1 << 6) - 1);
    t = d / dv;
    d -= t * dv;
    r += t;
    /* Up to 55 bits in r */
    /* Remaining 3 bits from d0. */
    r <<= 3;
    d <<= 3;
    d |= d0 & ((1 << 3) - 1);
    t = d / dv;
    r += t;

    return r;
}
#endif /* WOLFSSL_SP_DIV_64 */

/* Divide d in a and put remainder into r (m*d + r = a)
 * m is not calculated as it is not needed at this time.
 *
 * a  Number to be divided.
 * d  Number to divide with.
 * m  Multiplier result.
 * r  Remainder from the division.
 * returns MEMORY_E when unable to allocate memory and MP_OKAY otherwise.
 */
static int sp_2048_div_36(const sp_digit* a, const sp_digit* d, sp_digit* m,
        sp_digit* r)
{
    int i;
#ifndef WOLFSSL_SP_DIV_64
    int128_t d1;
#endif
    sp_digit dv, r1;
#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    sp_digit* td;
#else
    sp_digit t1d[72], t2d[36 + 1];
#endif
    sp_digit* t1;
    sp_digit* t2;
    int err = MP_OKAY;

    (void)m;

#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    td = (sp_digit*)XMALLOC(sizeof(sp_digit) * (3 * 36 + 1), NULL,
                                                       DYNAMIC_TYPE_TMP_BUFFER);
    if (td == NULL) {
        err = MEMORY_E;
    }
#endif

    if (err == MP_OKAY) {
#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
        t1 = td;
        t2 = td + 2 * 36;
#else
        t1 = t1d;
        t2 = t2d;
#endif

        dv = d[35];
        XMEMCPY(t1, a, sizeof(*t1) * 2U * 36U);
        for (i=35; i>=0; i--) {
            t1[36 + i] += t1[36 + i - 1] >> 57;
            t1[36 + i - 1] &= 0x1ffffffffffffffL;
#ifndef WOLFSSL_SP_DIV_64
            d1 = t1[36 + i];
            d1 <<= 57;
            d1 += t1[36 + i - 1];
            r1 = (sp_digit)(d1 / dv);
#else
            r1 = sp_2048_div_word_36(t1[36 + i], t1[36 + i - 1], dv);
#endif

            sp_2048_mul_d_36(t2, d, r1);
            (void)sp_2048_sub_36(&t1[i], &t1[i], t2);
            t1[36 + i] -= t2[36];
            t1[36 + i] += t1[36 + i - 1] >> 57;
            t1[36 + i - 1] &= 0x1ffffffffffffffL;
            r1 = (((-t1[36 + i]) << 57) - t1[36 + i - 1]) / dv;
            r1++;
            sp_2048_mul_d_36(t2, d, r1);
            (void)sp_2048_add_36(&t1[i], &t1[i], t2);
            t1[36 + i] += t1[36 + i - 1] >> 57;
            t1[36 + i - 1] &= 0x1ffffffffffffffL;
        }
        t1[36 - 1] += t1[36 - 2] >> 57;
        t1[36 - 2] &= 0x1ffffffffffffffL;
        r1 = t1[36 - 1] / dv;

        sp_2048_mul_d_36(t2, d, r1);
        (void)sp_2048_sub_36(t1, t1, t2);
        XMEMCPY(r, t1, sizeof(*r) * 2U * 36U);
        for (i=0; i<35; i++) {
            r[i+1] += r[i] >> 57;
            r[i] &= 0x1ffffffffffffffL;
        }
        sp_2048_cond_add_36(r, r, d, 0 - ((r[35] < 0) ?
                    (sp_digit)1 : (sp_digit)0));
    }

#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (td != NULL) {
        XFREE(td, NULL, DYNAMIC_TYPE_TMP_BUFFER);
    }
#endif

    return err;
}

/* Reduce a modulo m into r. (r = a mod m)
 *
 * r  A single precision number that is the reduced result.
 * a  A single precision number that is to be reduced.
 * m  A single precision number that is the modulus to reduce with.
 * returns MEMORY_E when unable to allocate memory and MP_OKAY otherwise.
 */
static int sp_2048_mod_36(sp_digit* r, const sp_digit* a, const sp_digit* m)
{
    return sp_2048_div_36(a, m, NULL, r);
}

#if (defined(WOLFSSL_HAVE_SP_RSA) && !defined(WOLFSSL_RSA_PUBLIC_ONLY)) || \
                                                     defined(WOLFSSL_HAVE_SP_DH)
/* Modular exponentiate a to the e mod m. (r = a^e mod m)
 *
 * r     A single precision number that is the result of the operation.
 * a     A single precision number being exponentiated.
 * e     A single precision number that is the exponent.
 * bits  The number of bits in the exponent.
 * m     A single precision number that is the modulus.
 * returns 0 on success and MEMORY_E on dynamic memory allocation failure.
 */
static int sp_2048_mod_exp_36(sp_digit* r, const sp_digit* a, const sp_digit* e, int bits,
    const sp_digit* m, int reduceA)
{
#ifdef WOLFSSL_SP_SMALL
#if !defined(WOLFSSL_SP_NO_MALLOC)
    sp_digit* td;
#else
    sp_digit td[3 * 72];
#endif
    sp_digit* t[3];
    sp_digit* norm;
    sp_digit mp = 1;
    sp_digit n;
    int i;
    int c, y;
    int err = MP_OKAY;

#if !defined(WOLFSSL_SP_NO_MALLOC)
    td = (sp_digit*)XMALLOC(sizeof(sp_digit) * 3 * 36 * 2, NULL,
                            DYNAMIC_TYPE_TMP_BUFFER);
    if (td == NULL) {
        err = MEMORY_E;
    }
#endif

    if (err == MP_OKAY) {
        norm = td;
        for (i=0; i<3; i++) {
#if !defined(WOLFSSL_SP_NO_MALLOC)
            t[i] = td + (i * 36 * 2);
#else
            t[i] = &td[i * 36 * 2];
#endif
            XMEMSET(t[i], 0, sizeof(sp_digit) * 36U * 2U);
        }

        sp_2048_mont_setup(m, &mp);
        sp_2048_mont_norm_36(norm, m);

        if (reduceA != 0) {
            err = sp_2048_mod_36(t[1], a, m);
        }
        else {
            XMEMCPY(t[1], a, sizeof(sp_digit) * 36U);
        }
    }
    if (err == MP_OKAY) {
        sp_2048_mul_36(t[1], t[1], norm);
        err = sp_2048_mod_36(t[1], t[1], m);
    }

    if (err == MP_OKAY) {
        i = bits / 57;
        c = bits % 57;
        n = e[i--] << (57 - c);
        for (; ; c--) {
            if (c == 0) {
                if (i == -1) {
                    break;
                }

                n = e[i--];
                c = 57;
            }

            y = (n >> 56) & 1;
            n <<= 1;

            sp_2048_mont_mul_36(t[y^1], t[0], t[1], m, mp);

            XMEMCPY(t[2], (void*)(((size_t)t[0] & addr_mask[y^1]) +
                                  ((size_t)t[1] & addr_mask[y])),
                                  sizeof(*t[2]) * 36 * 2);
            sp_2048_mont_sqr_36(t[2], t[2], m, mp);
            XMEMCPY((void*)(((size_t)t[0] & addr_mask[y^1]) +
                            ((size_t)t[1] & addr_mask[y])), t[2],
                            sizeof(*t[2]) * 36 * 2);
        }

        sp_2048_mont_reduce_36(t[0], m, mp);
        n = sp_2048_cmp_36(t[0], m);
        sp_2048_cond_sub_36(t[0], t[0], m, ((n < 0) ?
                    (sp_digit)1 : (sp_digit)0) - 1);
        XMEMCPY(r, t[0], sizeof(*r) * 36 * 2);

    }

#if !defined(WOLFSSL_SP_NO_MALLOC)
    if (td != NULL) {
        XFREE(td, NULL, DYNAMIC_TYPE_TMP_BUFFER);
    }
#endif

    return err;
#elif !defined(WC_NO_CACHE_RESISTANT)
#if defined(WOLFSSL_SMALL_STACK) && !defined(WOLFSSL_SP_NO_MALLOC)
    sp_digit* td;
#else
    sp_digit td[3 * 72];
#endif
    sp_digit* t[3];
    sp_digit* norm;
    sp_digit mp = 1;
    sp_digit n;
    int i;
    int c, y;
    int err = MP_OKAY;

#ifdef WOLFSSL_SMALL_STACK
    td = (sp_digit*)XMALLOC(sizeof(sp_digit) * 3 * 36 * 2, NULL,
                            DYNAMIC_TYPE_TMP_BUFFER);
    if (td == NULL) {
        err = MEMORY_E;
    }
#endif

    if (err == MP_OKAY) {
        norm = td;
        for (i=0; i<3; i++) {
#if defined(WOLFSSL_SMALL_STACK) && !defined(WOLFSSL_SP_NO_MALLOC)
            t[i] = td + (i * 36 * 2);
#else
            t[i] = &td[i * 36 * 2];
#endif
        }

        sp_2048_mont_setup(m, &mp);
        sp_2048_mont_norm_36(norm, m);

        if (reduceA != 0) {
            err = sp_2048_mod_36(t[1], a, m);
            if (err == MP_OKAY) {
                sp_2048_mul_36(t[1], t[1], norm);
                err = sp_2048_mod_36(t[1], t[1], m);
            }
        }
        else {
            sp_2048_mul_36(t[1], a, norm);
            err = sp_2048_mod_36(t[1], t[1], m);
        }
    }

    if (err == MP_OKAY) {
        i = bits / 57;
        c = bits % 57;
        n = e[i--] << (57 - c);
        for (; ; c--) {
            if (c == 0) {
                if (i == -1) {
                    break;
                }

                n = e[i--];
                c = 57;
            }

            y = (n >> 56) & 1;
            n <<= 1;

            sp_2048_mont_mul_36(t[y^1], t[0], t[1], m, mp);

            XMEMCPY(t[2], (void*)(((size_t)t[0] & addr_mask[y^1]) +
                                  ((size_t)t[1] & addr_mask[y])), 
                                  sizeof(*t[2]) * 36 * 2);
            sp_2048_mont_sqr_36(t[2], t[2], m, mp);
            XMEMCPY((void*)(((size_t)t[0] & addr_mask[y^1]) +
                            ((size_t)t[1] & addr_mask[y])), t[2], 
                            sizeof(*t[2]) * 36 * 2);
        }

        sp_2048_mont_reduce_36(t[0], m, mp);
        n = sp_2048_cmp_36(t[0], m);
        sp_2048_cond_sub_36(t[0], t[0], m, ((n < 0) ?
                    (sp_digit)1 : (sp_digit)0) - 1);
        XMEMCPY(r, t[0], sizeof(*r) * 36 * 2);
    }

#ifdef WOLFSSL_SMALL_STACK
    if (td != NULL) {
        XFREE(td, NULL, DYNAMIC_TYPE_TMP_BUFFER);
    }
#endif

    return err;
#else
#if defined(WOLFSSL_SMALL_STACK) && !defined(WOLFSSL_SP_NO_MALLOC)
    sp_digit* td;
#else
    sp_digit td[(32 * 72) + 72];
#endif
    sp_digit* t[32];
    sp_digit* rt;
    sp_digit* norm;
    sp_digit mp = 1;
    sp_digit n;
    int i;
    int c, y;
    int err = MP_OKAY;

#if defined(WOLFSSL_SMALL_STACK) && !defined(WOLFSSL_SP_NO_MALLOC)
    td = (sp_digit*)XMALLOC(sizeof(sp_digit) * ((32 * 72) + 72), NULL,
                            DYNAMIC_TYPE_TMP_BUFFER);
    if (td == NULL) {
        err = MEMORY_E;
    }
#endif

    if (err == MP_OKAY) {
        norm = td;
#if defined(WOLFSSL_SMALL_STACK) && !defined(WOLFSSL_SP_NO_MALLOC)
        for (i=0; i<32; i++)
            t[i] = td + i * 72;
        rt = td + 2304;
#else
        for (i=0; i<32; i++)
            t[i] = &td[i * 72];
        rt = &td[2304];
#endif

        sp_2048_mont_setup(m, &mp);
        sp_2048_mont_norm_36(norm, m);

        if (reduceA != 0) {
            err = sp_2048_mod_36(t[1], a, m);
            if (err == MP_OKAY) {
                sp_2048_mul_36(t[1], t[1], norm);
                err = sp_2048_mod_36(t[1], t[1], m);
            }
        }
        else {
            sp_2048_mul_36(t[1], a, norm);
            err = sp_2048_mod_36(t[1], t[1], m);
        }
    }

    if (err == MP_OKAY) {
        sp_2048_mont_sqr_36(t[ 2], t[ 1], m, mp);
        sp_2048_mont_mul_36(t[ 3], t[ 2], t[ 1], m, mp);
        sp_2048_mont_sqr_36(t[ 4], t[ 2], m, mp);
        sp_2048_mont_mul_36(t[ 5], t[ 3], t[ 2], m, mp);
        sp_2048_mont_sqr_36(t[ 6], t[ 3], m, mp);
        sp_2048_mont_mul_36(t[ 7], t[ 4], t[ 3], m, mp);
        sp_2048_mont_sqr_36(t[ 8], t[ 4], m, mp);
        sp_2048_mont_mul_36(t[ 9], t[ 5], t[ 4], m, mp);
        sp_2048_mont_sqr_36(t[10], t[ 5], m, mp);
        sp_2048_mont_mul_36(t[11], t[ 6], t[ 5], m, mp);
        sp_2048_mont_sqr_36(t[12], t[ 6], m, mp);
        sp_2048_mont_mul_36(t[13], t[ 7], t[ 6], m, mp);
        sp_2048_mont_sqr_36(t[14], t[ 7], m, mp);
        sp_2048_mont_mul_36(t[15], t[ 8], t[ 7], m, mp);
        sp_2048_mont_sqr_36(t[16], t[ 8], m, mp);
        sp_2048_mont_mul_36(t[17], t[ 9], t[ 8], m, mp);
        sp_2048_mont_sqr_36(t[18], t[ 9], m, mp);
        sp_2048_mont_mul_36(t[19], t[10], t[ 9], m, mp);
        sp_2048_mont_sqr_36(t[20], t[10], m, mp);
        sp_2048_mont_mul_36(t[21], t[11], t[10], m, mp);
        sp_2048_mont_sqr_36(t[22], t[11], m, mp);
        sp_2048_mont_mul_36(t[23], t[12], t[11], m, mp);
        sp_2048_mont_sqr_36(t[24], t[12], m, mp);
        sp_2048_mont_mul_36(t[25], t[13], t[12], m, mp);
        sp_2048_mont_sqr_36(t[26], t[13], m, mp);
        sp_2048_mont_mul_36(t[27], t[14], t[13], m, mp);
        sp_2048_mont_sqr_36(t[28], t[14], m, mp);
        sp_2048_mont_mul_36(t[29], t[15], t[14], m, mp);
        sp_2048_mont_sqr_36(t[30], t[15], m, mp);
        sp_2048_mont_mul_36(t[31], t[16], t[15], m, mp);

        bits = ((bits + 4) / 5) * 5;
        i = ((bits + 56) / 57) - 1;
        c = bits % 57;
        if (c == 0) {
            c = 57;
        }
        if (i < 36) {
            n = e[i--] << (64 - c);
        }
        else {
            n = 0;
            i--;
        }
        if (c < 5) {
            n |= e[i--] << (7 - c);
            c += 57;
        }
        y = (n >> 59) & 0x1f;
        n <<= 5;
        c -= 5;
        XMEMCPY(rt, t[y], sizeof(sp_digit) * 72);
        for (; i>=0 || c>=5; ) {
            if (c < 5) {
                n |= e[i--] << (7 - c);
                c += 57;
            }
            y = (n >> 59) & 0x1f;
            n <<= 5;
            c -= 5;

            sp_2048_mont_sqr_36(rt, rt, m, mp);
            sp_2048_mont_sqr_36(rt, rt, m, mp);
            sp_2048_mont_sqr_36(rt, rt, m, mp);
            sp_2048_mont_sqr_36(rt, rt, m, mp);
            sp_2048_mont_sqr_36(rt, rt, m, mp);

            sp_2048_mont_mul_36(rt, rt, t[y], m, mp);
        }

        sp_2048_mont_reduce_36(rt, m, mp);
        n = sp_2048_cmp_36(rt, m);
        sp_2048_cond_sub_36(rt, rt, m, ((n < 0) ?
                   (sp_digit)1 : (sp_digit)0) - 1);
        XMEMCPY(r, rt, sizeof(sp_digit) * 72);
    }

#if defined(WOLFSSL_SMALL_STACK) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (td != NULL) {
        XFREE(td, NULL, DYNAMIC_TYPE_TMP_BUFFER);
    }
#endif

    return err;
#endif
}
#endif /* (WOLFSSL_HAVE_SP_RSA && !WOLFSSL_RSA_PUBLIC_ONLY) || */
       /* WOLFSSL_HAVE_SP_DH */

#ifdef WOLFSSL_HAVE_SP_RSA
/* RSA public key operation.
 *
 * in      Array of bytes representing the number to exponentiate, base.
 * inLen   Number of bytes in base.
 * em      Public exponent.
 * mm      Modulus.
 * out     Buffer to hold big-endian bytes of exponentiation result.
 *         Must be at least 256 bytes long.
 * outLen  Number of bytes in result.
 * returns 0 on success, MP_TO_E when the outLen is too small, MP_READ_E when
 * an array is too long and MEMORY_E when dynamic memory allocation fails.
 */
int sp_RsaPublic_2048(const byte* in, word32 inLen, mp_int* em, mp_int* mm,
    byte* out, word32* outLen)
{
#ifdef WOLFSSL_SP_SMALL
    sp_digit* d = NULL;
    sp_digit* a;
    sp_digit* m;
    sp_digit* r;
    sp_digit* norm;
    sp_digit e[1] = {0};
    sp_digit mp;
    int i;
    int err = MP_OKAY;

    if (*outLen < 256U) {
        err = MP_TO_E;
    }

    if (err == MP_OKAY) {
        if (mp_count_bits(em) > 57) {
            err = MP_READ_E;
        }
        if (inLen > 256U) {
            err = MP_READ_E;
        }
        if (mp_count_bits(mm) != 2048) {
            err = MP_READ_E;
        }
    }

    if (err == MP_OKAY) {
        d = (sp_digit*)XMALLOC(sizeof(sp_digit) * 36 * 5, NULL,
                                                              DYNAMIC_TYPE_RSA);
        if (d == NULL)
            err = MEMORY_E;
    }

    if (err == MP_OKAY) {
        a = d;
        r = a + 36 * 2;
        m = r + 36 * 2;
        norm = r;

        sp_2048_from_bin(a, 36, in, inLen);
#if DIGIT_BIT >= 57
        e[0] = (sp_digit)em->dp[0];
#else
        e[0] = (sp_digit)em->dp[0];
        if (em->used > 1) {
            e[0] |= ((sp_digit)em->dp[1]) << DIGIT_BIT;
        }
#endif
        if (e[0] == 0) {
            err = MP_EXPTMOD_E;
        }
    }

    if (err == MP_OKAY) {
        sp_2048_from_mp(m, 36, mm);

        sp_2048_mont_setup(m, &mp);
        sp_2048_mont_norm_36(norm, m);
    }
    if (err == MP_OKAY) {
        sp_2048_mul_36(a, a, norm);
        err = sp_2048_mod_36(a, a, m);
    }
    if (err == MP_OKAY) {
        for (i=56; i>=0; i--) {
            if ((e[0] >> i) != 0) {
                break;
            }
        }

        XMEMCPY(r, a, sizeof(sp_digit) * 36 * 2);
        for (i--; i>=0; i--) {
            sp_2048_mont_sqr_36(r, r, m, mp);

            if (((e[0] >> i) & 1) == 1) {
                sp_2048_mont_mul_36(r, r, a, m, mp);
            }
        }
        sp_2048_mont_reduce_36(r, m, mp);
        mp = sp_2048_cmp_36(r, m);
        sp_2048_cond_sub_36(r, r, m, ((mp < 0) ?
                    (sp_digit)1 : (sp_digit)0)- 1);

        sp_2048_to_bin(r, out);
        *outLen = 256;
    }

    if (d != NULL) {
        XFREE(d, NULL, DYNAMIC_TYPE_RSA);
    }

    return err;
#else
#if (!defined(WOLFSSL_SP_SMALL) && !defined(WOLFSSL_SMALL_STACK)) || defined(WOLFSSL_SP_NO_MALLOC)
    sp_digit ad[72], md[36], rd[72];
#else
    sp_digit* d = NULL;
#endif
    sp_digit* a;
    sp_digit* m;
    sp_digit* r;
    sp_digit e[1] = {0};
    int err = MP_OKAY;

    if (*outLen < 256U) {
        err = MP_TO_E;
    }
    if (err == MP_OKAY) {
        if (mp_count_bits(em) > 57) {
            err = MP_READ_E;
        }
        if (inLen > 256U) {
            err = MP_READ_E;
        }
        if (mp_count_bits(mm) != 2048) {
            err = MP_READ_E;
        }
    }

#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (err == MP_OKAY) {
        d = (sp_digit*)XMALLOC(sizeof(sp_digit) * 36 * 5, NULL,
                                                              DYNAMIC_TYPE_RSA);
        if (d == NULL) {
            err = MEMORY_E;
        }
    }

    if (err == MP_OKAY) {
        a = d;
        r = a + 36 * 2;
        m = r + 36 * 2;
    }
#else
    a = ad;
    m = md;
    r = rd;
#endif

    if (err == MP_OKAY) {
        sp_2048_from_bin(a, 36, in, inLen);
#if DIGIT_BIT >= 57
        e[0] = (sp_digit)em->dp[0];
#else
        e[0] = (sp_digit)em->dp[0];
        if (em->used > 1) {
            e[0] |= ((sp_digit)em->dp[1]) << DIGIT_BIT;
        }
#endif
        if (e[0] == 0) {
            err = MP_EXPTMOD_E;
        }
    }
    if (err == MP_OKAY) {
        sp_2048_from_mp(m, 36, mm);

        if (e[0] == 0x3) {
            sp_2048_sqr_36(r, a);
            err = sp_2048_mod_36(r, r, m);
            if (err == MP_OKAY) {
                sp_2048_mul_36(r, a, r);
                err = sp_2048_mod_36(r, r, m);
            }
        }
        else {
            sp_digit* norm = r;
            int i;
            sp_digit mp;

            sp_2048_mont_setup(m, &mp);
            sp_2048_mont_norm_36(norm, m);

            sp_2048_mul_36(a, a, norm);
            err = sp_2048_mod_36(a, a, m);

            if (err == MP_OKAY) {
                for (i=56; i>=0; i--) {
                    if ((e[0] >> i) != 0) {
                        break;
                    }
                }

                XMEMCPY(r, a, sizeof(sp_digit) * 72U);
                for (i--; i>=0; i--) {
                    sp_2048_mont_sqr_36(r, r, m, mp);

                    if (((e[0] >> i) & 1) == 1) {
                        sp_2048_mont_mul_36(r, r, a, m, mp);
                    }
                }
                sp_2048_mont_reduce_36(r, m, mp);
                mp = sp_2048_cmp_36(r, m);
                sp_2048_cond_sub_36(r, r, m, ((mp < 0) ?
                           (sp_digit)1 : (sp_digit)0) - 1);
            }
        }
    }

    if (err == MP_OKAY) {
        sp_2048_to_bin(r, out);
        *outLen = 256;
    }

#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (d != NULL) {
        XFREE(d, NULL, DYNAMIC_TYPE_RSA);
    }
#endif

    return err;
#endif /* WOLFSSL_SP_SMALL */
}

#ifndef WOLFSSL_RSA_PUBLIC_ONLY
#if !defined(SP_RSA_PRIVATE_EXP_D) && !defined(RSA_LOW_MEM)
#endif /* !SP_RSA_PRIVATE_EXP_D && !RSA_LOW_MEM */
/* RSA private key operation.
 *
 * in      Array of bytes representing the number to exponentiate, base.
 * inLen   Number of bytes in base.
 * dm      Private exponent.
 * pm      First prime.
 * qm      Second prime.
 * dpm     First prime's CRT exponent.
 * dqm     Second prime's CRT exponent.
 * qim     Inverse of second prime mod p.
 * mm      Modulus.
 * out     Buffer to hold big-endian bytes of exponentiation result.
 *         Must be at least 256 bytes long.
 * outLen  Number of bytes in result.
 * returns 0 on success, MP_TO_E when the outLen is too small, MP_READ_E when
 * an array is too long and MEMORY_E when dynamic memory allocation fails.
 */
int sp_RsaPrivate_2048(const byte* in, word32 inLen, mp_int* dm,
    mp_int* pm, mp_int* qm, mp_int* dpm, mp_int* dqm, mp_int* qim, mp_int* mm,
    byte* out, word32* outLen)
{
#if defined(SP_RSA_PRIVATE_EXP_D) || defined(RSA_LOW_MEM)
#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    sp_digit* a = NULL;
    sp_digit* d = NULL;
    sp_digit* m = NULL;
    sp_digit* r = NULL;
    int err = MP_OKAY;

    (void)pm;
    (void)qm;
    (void)dpm;
    (void)dqm;
    (void)qim;

    if (*outLen < 256U) {
        err = MP_TO_E;
    }
    if (err == MP_OKAY) {
        if (mp_count_bits(dm) > 2048) {
           err = MP_READ_E;
        }
        if (inLen > 256) {
            err = MP_READ_E;
        }
        if (mp_count_bits(mm) != 2048) {
            err = MP_READ_E;
        }
    }

    if (err == MP_OKAY) {
        d = (sp_digit*)XMALLOC(sizeof(sp_digit) * 36 * 4, NULL,
                                                              DYNAMIC_TYPE_RSA);
        if (d == NULL) {
            err = MEMORY_E;
        }
    }
    if (err == MP_OKAY) {
        a = d + 36;
        m = a + 72;
        r = a;

        sp_2048_from_bin(a, 36, in, inLen);
        sp_2048_from_mp(d, 36, dm);
        sp_2048_from_mp(m, 36, mm);
        err = sp_2048_mod_exp_36(r, a, d, 2048, m, 0);
    }
    if (err == MP_OKAY) {
        sp_2048_to_bin(r, out);
        *outLen = 256;
    }

    if (d != NULL) {
        XMEMSET(d, 0, sizeof(sp_digit) * 36);
        XFREE(d, NULL, DYNAMIC_TYPE_RSA);
    }

    return err;
#else
    sp_digit a[72], d[36], m[36];
    sp_digit* r = a;
    int err = MP_OKAY;

    (void)pm;
    (void)qm;
    (void)dpm;
    (void)dqm;
    (void)qim;

    if (*outLen < 256U) {
        err = MP_TO_E;
    }
    if (err == MP_OKAY) {
        if (mp_count_bits(dm) > 2048) {
            err = MP_READ_E;
        }
        if (inLen > 256U) {
            err = MP_READ_E;
        }
        if (mp_count_bits(mm) != 2048) {
            err = MP_READ_E;
        }
    }

    if (err == MP_OKAY) {
        sp_2048_from_bin(a, 36, in, inLen);
        sp_2048_from_mp(d, 36, dm);
        sp_2048_from_mp(m, 36, mm);
        err = sp_2048_mod_exp_36(r, a, d, 2048, m, 0);
    }

    if (err == MP_OKAY) {
        sp_2048_to_bin(r, out);
        *outLen = 256;
    }

    XMEMSET(d, 0, sizeof(sp_digit) * 36);

    return err;
#endif /* WOLFSSL_SP_SMALL || defined(WOLFSSL_SMALL_STACK) */
#else
#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    sp_digit* t = NULL;
    sp_digit* a;
    sp_digit* p;
    sp_digit* q;
    sp_digit* dp;
    sp_digit* dq;
    sp_digit* qi;
    sp_digit* tmpa;
    sp_digit* tmpb;
    sp_digit* r;
    int err = MP_OKAY;

    (void)dm;
    (void)mm;

    if (*outLen < 256U) {
        err = MP_TO_E;
    }
    if (err == MP_OKAY) {
        if (inLen > 256) {
            err = MP_READ_E;
        }
        if (mp_count_bits(mm) != 2048) {
            err = MP_READ_E;
        }
    }

    if (err == MP_OKAY) {
        t = (sp_digit*)XMALLOC(sizeof(sp_digit) * 18 * 11, NULL,
                                                              DYNAMIC_TYPE_RSA);
        if (t == NULL) {
            err = MEMORY_E;
        }
    }
    if (err == MP_OKAY) {
        a = t;
        p = a + 36 * 2;
        q = p + 18;
        qi = dq = dp = q + 18;
        tmpa = qi + 18;
        tmpb = tmpa + 36;

        r = t + 36;

        sp_2048_from_bin(a, 36, in, inLen);
        sp_2048_from_mp(p, 18, pm);
        sp_2048_from_mp(q, 18, qm);
        sp_2048_from_mp(dp, 18, dpm);
        err = sp_2048_mod_exp_18(tmpa, a, dp, 1024, p, 1);
    }
    if (err == MP_OKAY) {
        sp_2048_from_mp(dq, 18, dqm);
        err = sp_2048_mod_exp_18(tmpb, a, dq, 1024, q, 1);
    }
    if (err == MP_OKAY) {
        (void)sp_2048_sub_18(tmpa, tmpa, tmpb);
        sp_2048_cond_add_18(tmpa, tmpa, p, 0 - ((sp_int_digit)tmpa[17] >> 63));
        sp_2048_cond_add_18(tmpa, tmpa, p, 0 - ((sp_int_digit)tmpa[17] >> 63));

        sp_2048_from_mp(qi, 18, qim);
        sp_2048_mul_18(tmpa, tmpa, qi);
        err = sp_2048_mod_18(tmpa, tmpa, p);
    }

    if (err == MP_OKAY) {
        sp_2048_mul_18(tmpa, q, tmpa);
        (void)sp_2048_add_36(r, tmpb, tmpa);
        sp_2048_norm_36(r);

        sp_2048_to_bin(r, out);
        *outLen = 256;
    }

    if (t != NULL) {
        XMEMSET(t, 0, sizeof(sp_digit) * 18 * 11);
        XFREE(t, NULL, DYNAMIC_TYPE_RSA);
    }

    return err;
#else
    sp_digit a[36 * 2];
    sp_digit p[18], q[18], dp[18], dq[18], qi[18];
    sp_digit tmpa[36], tmpb[36];
    sp_digit* r = a;
    int err = MP_OKAY;

    (void)dm;
    (void)mm;

    if (*outLen < 256U) {
        err = MP_TO_E;
    }
    if (err == MP_OKAY) {
        if (inLen > 256U) {
            err = MP_READ_E;
        }
        if (mp_count_bits(mm) != 2048) {
            err = MP_READ_E;
        }
    }

    if (err == MP_OKAY) {
        sp_2048_from_bin(a, 36, in, inLen);
        sp_2048_from_mp(p, 18, pm);
        sp_2048_from_mp(q, 18, qm);
        sp_2048_from_mp(dp, 18, dpm);
        sp_2048_from_mp(dq, 18, dqm);
        sp_2048_from_mp(qi, 18, qim);

        err = sp_2048_mod_exp_18(tmpa, a, dp, 1024, p, 1);
    }
    if (err == MP_OKAY) {
        err = sp_2048_mod_exp_18(tmpb, a, dq, 1024, q, 1);
    }

    if (err == MP_OKAY) {
        (void)sp_2048_sub_18(tmpa, tmpa, tmpb);
        sp_2048_cond_add_18(tmpa, tmpa, p, 0 - ((sp_int_digit)tmpa[17] >> 63));
        sp_2048_cond_add_18(tmpa, tmpa, p, 0 - ((sp_int_digit)tmpa[17] >> 63));
        sp_2048_mul_18(tmpa, tmpa, qi);
        err = sp_2048_mod_18(tmpa, tmpa, p);
    }

    if (err == MP_OKAY) {
        sp_2048_mul_18(tmpa, tmpa, q);
        (void)sp_2048_add_36(r, tmpb, tmpa);
        sp_2048_norm_36(r);

        sp_2048_to_bin(r, out);
        *outLen = 256;
    }

    XMEMSET(tmpa, 0, sizeof(tmpa));
    XMEMSET(tmpb, 0, sizeof(tmpb));
    XMEMSET(p, 0, sizeof(p));
    XMEMSET(q, 0, sizeof(q));
    XMEMSET(dp, 0, sizeof(dp));
    XMEMSET(dq, 0, sizeof(dq));
    XMEMSET(qi, 0, sizeof(qi));

    return err;
#endif /* WOLFSSL_SP_SMALL || defined(WOLFSSL_SMALL_STACK) */
#endif /* SP_RSA_PRIVATE_EXP_D || RSA_LOW_MEM */
}

#endif /* !WOLFSSL_RSA_PUBLIC_ONLY */
#endif /* WOLFSSL_HAVE_SP_RSA */
#if defined(WOLFSSL_HAVE_SP_DH) || (defined(WOLFSSL_HAVE_SP_RSA) && \
                                              !defined(WOLFSSL_RSA_PUBLIC_ONLY))
/* Convert an array of sp_digit to an mp_int.
 *
 * a  A single precision integer.
 * r  A multi-precision integer.
 */
static int sp_2048_to_mp(const sp_digit* a, mp_int* r)
{
    int err;

    err = mp_grow(r, (2048 + DIGIT_BIT - 1) / DIGIT_BIT);
    if (err == MP_OKAY) { /*lint !e774 case where err is always MP_OKAY*/
#if DIGIT_BIT == 57
        XMEMCPY(r->dp, a, sizeof(sp_digit) * 36);
        r->used = 36;
        mp_clamp(r);
#elif DIGIT_BIT < 57
        int i, j = 0, s = 0;

        r->dp[0] = 0;
        for (i = 0; i < 36; i++) {
            r->dp[j] |= (mp_digit)(a[i] << s);
            r->dp[j] &= (1L << DIGIT_BIT) - 1;
            s = DIGIT_BIT - s;
            r->dp[++j] = (mp_digit)(a[i] >> s);
            while (s + DIGIT_BIT <= 57) {
                s += DIGIT_BIT;
                r->dp[j++] &= (1L << DIGIT_BIT) - 1;
                if (s == SP_WORD_SIZE) {
                    r->dp[j] = 0;
                }
                else {
                    r->dp[j] = (mp_digit)(a[i] >> s);
                }
            }
            s = 57 - s;
        }
        r->used = (2048 + DIGIT_BIT - 1) / DIGIT_BIT;
        mp_clamp(r);
#else
        int i, j = 0, s = 0;

        r->dp[0] = 0;
        for (i = 0; i < 36; i++) {
            r->dp[j] |= ((mp_digit)a[i]) << s;
            if (s + 57 >= DIGIT_BIT) {
    #if DIGIT_BIT != 32 && DIGIT_BIT != 64
                r->dp[j] &= (1L << DIGIT_BIT) - 1;
    #endif
                s = DIGIT_BIT - s;
                r->dp[++j] = a[i] >> s;
                s = 57 - s;
            }
            else {
                s += 57;
            }
        }
        r->used = (2048 + DIGIT_BIT - 1) / DIGIT_BIT;
        mp_clamp(r);
#endif
    }

    return err;
}

/* Perform the modular exponentiation for Diffie-Hellman.
 *
 * base  Base. MP integer.
 * exp   Exponent. MP integer.
 * mod   Modulus. MP integer.
 * res   Result. MP integer.
 * returns 0 on success, MP_READ_E if there are too many bytes in an array
 * and MEMORY_E if memory allocation fails.
 */
int sp_ModExp_2048(mp_int* base, mp_int* exp, mp_int* mod, mp_int* res)
{
#ifdef WOLFSSL_SP_SMALL
    int err = MP_OKAY;
    sp_digit* d = NULL;
    sp_digit* b;
    sp_digit* e;
    sp_digit* m;
    sp_digit* r;
    int expBits = mp_count_bits(exp);

    if (mp_count_bits(base) > 2048) {
        err = MP_READ_E;
    }

    if (err == MP_OKAY) {
        if (expBits > 2048) {
            err = MP_READ_E;
        }
    }

    if (err == MP_OKAY) {
        if (mp_count_bits(mod) != 2048) {
            err = MP_READ_E;
        }
    }

    if (err == MP_OKAY) {
        d = (sp_digit*)XMALLOC(sizeof(*d) * 36 * 4, NULL, DYNAMIC_TYPE_DH);
        if (d == NULL) {
            err = MEMORY_E;
        }
    }

    if (err == MP_OKAY) {
        b = d;
        e = b + 36 * 2;
        m = e + 36;
        r = b;

        sp_2048_from_mp(b, 36, base);
        sp_2048_from_mp(e, 36, exp);
        sp_2048_from_mp(m, 36, mod);

        err = sp_2048_mod_exp_36(r, b, e, mp_count_bits(exp), m, 0);
    }

    if (err == MP_OKAY) {
        err = sp_2048_to_mp(r, res);
    }

    if (d != NULL) {
        XMEMSET(e, 0, sizeof(sp_digit) * 36U);
        XFREE(d, NULL, DYNAMIC_TYPE_DH);
    }
    return err;
#else
#ifndef WOLFSSL_SMALL_STACK
    sp_digit bd[72], ed[36], md[36];
#else
    sp_digit* d = NULL;
#endif
    sp_digit* b;
    sp_digit* e;
    sp_digit* m;
    sp_digit* r;
    int err = MP_OKAY;
    int expBits = mp_count_bits(exp);

    if (mp_count_bits(base) > 2048) {
        err = MP_READ_E;
    }

    if (err == MP_OKAY) {
        if (expBits > 2048) {
            err = MP_READ_E;
        }
    }
    
    if (err == MP_OKAY) {
        if (mp_count_bits(mod) != 2048) {
            err = MP_READ_E;
        }
    }

#ifdef WOLFSSL_SMALL_STACK
    if (err == MP_OKAY) {
        d = (sp_digit*)XMALLOC(sizeof(*d) * 36 * 4, NULL, DYNAMIC_TYPE_DH);
        if (d == NULL)
            err = MEMORY_E;
    }

    if (err == MP_OKAY) {
        b = d;
        e = b + 36 * 2;
        m = e + 36;
        r = b;
    }
#else
    r = b = bd;
    e = ed;
    m = md;
#endif

    if (err == MP_OKAY) {
        sp_2048_from_mp(b, 36, base);
        sp_2048_from_mp(e, 36, exp);
        sp_2048_from_mp(m, 36, mod);

        err = sp_2048_mod_exp_36(r, b, e, expBits, m, 0);
    }

    if (err == MP_OKAY) {
        err = sp_2048_to_mp(r, res);
    }


#ifdef WOLFSSL_SMALL_STACK
    if (d != NULL) {
        XMEMSET(e, 0, sizeof(sp_digit) * 36U);
        XFREE(d, NULL, DYNAMIC_TYPE_DH);
    }
#else
    XMEMSET(e, 0, sizeof(sp_digit) * 36U);
#endif

    return err;
#endif
}

#ifdef WOLFSSL_HAVE_SP_DH

#ifdef HAVE_FFDHE_2048
SP_NOINLINE static void sp_2048_lshift_36(sp_digit* r, sp_digit* a, byte n)
{
#ifdef WOLFSSL_SP_SMALL
    int i;

    r[36] = a[35] >> (57 - n);
    for (i=35; i>0; i--) {
        r[i] = ((a[i] << n) | (a[i-1] >> (57 - n))) & 0x1ffffffffffffffL;
    }
#else
    sp_int_digit s, t;

    s = (sp_int_digit)a[35];
    r[36] = s >> (57U - n);
    s = (sp_int_digit)(a[35]); t = (sp_int_digit)(a[34]);
    r[35] = ((s << n) | (t >> (57U - n))) & 0x1ffffffffffffffUL;
    s = (sp_int_digit)(a[34]); t = (sp_int_digit)(a[33]);
    r[34] = ((s << n) | (t >> (57U - n))) & 0x1ffffffffffffffUL;
    s = (sp_int_digit)(a[33]); t = (sp_int_digit)(a[32]);
    r[33] = ((s << n) | (t >> (57U - n))) & 0x1ffffffffffffffUL;
    s = (sp_int_digit)(a[32]); t = (sp_int_digit)(a[31]);
    r[32] = ((s << n) | (t >> (57U - n))) & 0x1ffffffffffffffUL;
    s = (sp_int_digit)(a[31]); t = (sp_int_digit)(a[30]);
    r[31] = ((s << n) | (t >> (57U - n))) & 0x1ffffffffffffffUL;
    s = (sp_int_digit)(a[30]); t = (sp_int_digit)(a[29]);
    r[30] = ((s << n) | (t >> (57U - n))) & 0x1ffffffffffffffUL;
    s = (sp_int_digit)(a[29]); t = (sp_int_digit)(a[28]);
    r[29] = ((s << n) | (t >> (57U - n))) & 0x1ffffffffffffffUL;
    s = (sp_int_digit)(a[28]); t = (sp_int_digit)(a[27]);
    r[28] = ((s << n) | (t >> (57U - n))) & 0x1ffffffffffffffUL;
    s = (sp_int_digit)(a[27]); t = (sp_int_digit)(a[26]);
    r[27] = ((s << n) | (t >> (57U - n))) & 0x1ffffffffffffffUL;
    s = (sp_int_digit)(a[26]); t = (sp_int_digit)(a[25]);
    r[26] = ((s << n) | (t >> (57U - n))) & 0x1ffffffffffffffUL;
    s = (sp_int_digit)(a[25]); t = (sp_int_digit)(a[24]);
    r[25] = ((s << n) | (t >> (57U - n))) & 0x1ffffffffffffffUL;
    s = (sp_int_digit)(a[24]); t = (sp_int_digit)(a[23]);
    r[24] = ((s << n) | (t >> (57U - n))) & 0x1ffffffffffffffUL;
    s = (sp_int_digit)(a[23]); t = (sp_int_digit)(a[22]);
    r[23] = ((s << n) | (t >> (57U - n))) & 0x1ffffffffffffffUL;
    s = (sp_int_digit)(a[22]); t = (sp_int_digit)(a[21]);
    r[22] = ((s << n) | (t >> (57U - n))) & 0x1ffffffffffffffUL;
    s = (sp_int_digit)(a[21]); t = (sp_int_digit)(a[20]);
    r[21] = ((s << n) | (t >> (57U - n))) & 0x1ffffffffffffffUL;
    s = (sp_int_digit)(a[20]); t = (sp_int_digit)(a[19]);
    r[20] = ((s << n) | (t >> (57U - n))) & 0x1ffffffffffffffUL;
    s = (sp_int_digit)(a[19]); t = (sp_int_digit)(a[18]);
    r[19] = ((s << n) | (t >> (57U - n))) & 0x1ffffffffffffffUL;
    s = (sp_int_digit)(a[18]); t = (sp_int_digit)(a[17]);
    r[18] = ((s << n) | (t >> (57U - n))) & 0x1ffffffffffffffUL;
    s = (sp_int_digit)(a[17]); t = (sp_int_digit)(a[16]);
    r[17] = ((s << n) | (t >> (57U - n))) & 0x1ffffffffffffffUL;
    s = (sp_int_digit)(a[16]); t = (sp_int_digit)(a[15]);
    r[16] = ((s << n) | (t >> (57U - n))) & 0x1ffffffffffffffUL;
    s = (sp_int_digit)(a[15]); t = (sp_int_digit)(a[14]);
    r[15] = ((s << n) | (t >> (57U - n))) & 0x1ffffffffffffffUL;
    s = (sp_int_digit)(a[14]); t = (sp_int_digit)(a[13]);
    r[14] = ((s << n) | (t >> (57U - n))) & 0x1ffffffffffffffUL;
    s = (sp_int_digit)(a[13]); t = (sp_int_digit)(a[12]);
    r[13] = ((s << n) | (t >> (57U - n))) & 0x1ffffffffffffffUL;
    s = (sp_int_digit)(a[12]); t = (sp_int_digit)(a[11]);
    r[12] = ((s << n) | (t >> (57U - n))) & 0x1ffffffffffffffUL;
    s = (sp_int_digit)(a[11]); t = (sp_int_digit)(a[10]);
    r[11] = ((s << n) | (t >> (57U - n))) & 0x1ffffffffffffffUL;
    s = (sp_int_digit)(a[10]); t = (sp_int_digit)(a[9]);
    r[10] = ((s << n) | (t >> (57U - n))) & 0x1ffffffffffffffUL;
    s = (sp_int_digit)(a[9]); t = (sp_int_digit)(a[8]);
    r[9] = ((s << n) | (t >> (57U - n))) & 0x1ffffffffffffffUL;
    s = (sp_int_digit)(a[8]); t = (sp_int_digit)(a[7]);
    r[8] = ((s << n) | (t >> (57U - n))) & 0x1ffffffffffffffUL;
    s = (sp_int_digit)(a[7]); t = (sp_int_digit)(a[6]);
    r[7] = ((s << n) | (t >> (57U - n))) & 0x1ffffffffffffffUL;
    s = (sp_int_digit)(a[6]); t = (sp_int_digit)(a[5]);
    r[6] = ((s << n) | (t >> (57U - n))) & 0x1ffffffffffffffUL;
    s = (sp_int_digit)(a[5]); t = (sp_int_digit)(a[4]);
    r[5] = ((s << n) | (t >> (57U - n))) & 0x1ffffffffffffffUL;
    s = (sp_int_digit)(a[4]); t = (sp_int_digit)(a[3]);
    r[4] = ((s << n) | (t >> (57U - n))) & 0x1ffffffffffffffUL;
    s = (sp_int_digit)(a[3]); t = (sp_int_digit)(a[2]);
    r[3] = ((s << n) | (t >> (57U - n))) & 0x1ffffffffffffffUL;
    s = (sp_int_digit)(a[2]); t = (sp_int_digit)(a[1]);
    r[2] = ((s << n) | (t >> (57U - n))) & 0x1ffffffffffffffUL;
    s = (sp_int_digit)(a[1]); t = (sp_int_digit)(a[0]);
    r[1] = ((s << n) | (t >> (57U - n))) & 0x1ffffffffffffffUL;
#endif
    r[0] = (a[0] << n) & 0x1ffffffffffffffL;
}

/* Modular exponentiate 2 to the e mod m. (r = 2^e mod m)
 *
 * r     A single precision number that is the result of the operation.
 * e     A single precision number that is the exponent.
 * bits  The number of bits in the exponent.
 * m     A single precision number that is the modulus.
 * returns 0 on success and MEMORY_E on dynamic memory allocation failure.
 */
static int sp_2048_mod_exp_2_36(sp_digit* r, const sp_digit* e, int bits, const sp_digit* m)
{
#if defined(WOLFSSL_SMALL_STACK) && !defined(WOLFSSL_SP_NO_MALLOC)
    sp_digit* td;
#else
    sp_digit td[109];
#endif
    sp_digit* norm;
    sp_digit* tmp;
    sp_digit mp = 1;
    sp_digit n, o;
    int i;
    int c, y;
    int err = MP_OKAY;

#if defined(WOLFSSL_SMALL_STACK) && !defined(WOLFSSL_SP_NO_MALLOC)
    td = (sp_digit*)XMALLOC(sizeof(sp_digit) * 109, NULL,
                            DYNAMIC_TYPE_TMP_BUFFER);
    if (td == NULL) {
        err = MEMORY_E;
    }
#endif

    if (err == MP_OKAY) {
        norm = td;
#if defined(WOLFSSL_SMALL_STACK) && !defined(WOLFSSL_SP_NO_MALLOC)
        tmp  = td + 72;
        XMEMSET(td, 0, sizeof(sp_digit) * 109);
#else
        tmp  = &td[72];
        XMEMSET(td, 0, sizeof(td));
#endif

        sp_2048_mont_setup(m, &mp);
        sp_2048_mont_norm_36(norm, m);

        bits = ((bits + 4) / 5) * 5;
        i = ((bits + 56) / 57) - 1;
        c = bits % 57;
        if (c == 0) {
            c = 57;
        }
        if (i < 36) {
            n = e[i--] << (64 - c);
        }
        else {
            n = 0;
            i--;
        }
        if (c < 5) {
            n |= e[i--] << (7 - c);
            c += 57;
        }
        y = (n >> 59) & 0x1f;
        n <<= 5;
        c -= 5;
        sp_2048_lshift_36(r, norm, y);
        for (; i>=0 || c>=5; ) {
            if (c < 5) {
                n |= e[i--] << (7 - c);
                c += 57;
            }
            y = (n >> 59) & 0x1f;
            n <<= 5;
            c -= 5;

            sp_2048_mont_sqr_36(r, r, m, mp);
            sp_2048_mont_sqr_36(r, r, m, mp);
            sp_2048_mont_sqr_36(r, r, m, mp);
            sp_2048_mont_sqr_36(r, r, m, mp);
            sp_2048_mont_sqr_36(r, r, m, mp);

            sp_2048_lshift_36(r, r, y);
            sp_2048_mul_d_36(tmp, norm, (r[36] << 4) + (r[35] >> 53));
            r[36] = 0;
            r[35] &= 0x1fffffffffffffL;
            (void)sp_2048_add_36(r, r, tmp);
            sp_2048_norm_36(r);
            o = sp_2048_cmp_36(r, m);
            sp_2048_cond_sub_36(r, r, m, ((o < 0) ?
                                          (sp_digit)1 : (sp_digit)0) - 1);
        }

        sp_2048_mont_reduce_36(r, m, mp);
        n = sp_2048_cmp_36(r, m);
        sp_2048_cond_sub_36(r, r, m, ((n < 0) ?
                                                (sp_digit)1 : (sp_digit)0) - 1);
    }

#if defined(WOLFSSL_SMALL_STACK) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (td != NULL) {
        XFREE(td, NULL, DYNAMIC_TYPE_TMP_BUFFER);
    }
#endif

    return err;
}

#endif /* HAVE_FFDHE_2048 */

/* Perform the modular exponentiation for Diffie-Hellman.
 *
 * base     Base.
 * exp      Array of bytes that is the exponent.
 * expLen   Length of data, in bytes, in exponent.
 * mod      Modulus.
 * out      Buffer to hold big-endian bytes of exponentiation result.
 *          Must be at least 256 bytes long.
 * outLen   Length, in bytes, of exponentiation result.
 * returns 0 on success, MP_READ_E if there are too many bytes in an array
 * and MEMORY_E if memory allocation fails.
 */
int sp_DhExp_2048(mp_int* base, const byte* exp, word32 expLen,
    mp_int* mod, byte* out, word32* outLen)
{
#ifdef WOLFSSL_SP_SMALL
    int err = MP_OKAY;
    sp_digit* d = NULL;
    sp_digit* b;
    sp_digit* e;
    sp_digit* m;
    sp_digit* r;
    word32 i;

    if (mp_count_bits(base) > 2048) {
        err = MP_READ_E;
    }

    if (err == MP_OKAY) {
        if (expLen > 256) {
            err = MP_READ_E;
        }
    }

    if (err == MP_OKAY) {
        if (mp_count_bits(mod) != 2048) {
            err = MP_READ_E;
        }
    }

    if (err == MP_OKAY) {
        d = (sp_digit*)XMALLOC(sizeof(*d) * 36 * 4, NULL, DYNAMIC_TYPE_DH);
        if (d == NULL) {
            err = MEMORY_E;
        }
    }

    if (err == MP_OKAY) {
        b = d;
        e = b + 36 * 2;
        m = e + 36;
        r = b;

        sp_2048_from_mp(b, 36, base);
        sp_2048_from_bin(e, 36, exp, expLen);
        sp_2048_from_mp(m, 36, mod);

    #ifdef HAVE_FFDHE_2048
        if (base->used == 1 && base->dp[0] == 2 &&
                (m[35] >> 21) == 0xffffffffL) {
            err = sp_2048_mod_exp_2_36(r, e, expLen * 8, m);
        }
        else
    #endif
            err = sp_2048_mod_exp_36(r, b, e, expLen * 8, m, 0);
    }

    if (err == MP_OKAY) {
        sp_2048_to_bin(r, out);
        *outLen = 256;
        for (i=0; i<256 && out[i] == 0; i++) {
        }
        *outLen -= i;
        XMEMMOVE(out, out + i, *outLen);
    }

    if (d != NULL) {
        XMEMSET(e, 0, sizeof(sp_digit) * 36U);
        XFREE(d, NULL, DYNAMIC_TYPE_DH);
    }
    return err;
#else
#ifndef WOLFSSL_SMALL_STACK
    sp_digit bd[72], ed[36], md[36];
#else
    sp_digit* d = NULL;
#endif
    sp_digit* b;
    sp_digit* e;
    sp_digit* m;
    sp_digit* r;
    word32 i;
    int err = MP_OKAY;

    if (mp_count_bits(base) > 2048) {
        err = MP_READ_E;
    }

    if (err == MP_OKAY) {
        if (expLen > 256U) {
            err = MP_READ_E;
        }
    }

    if (err == MP_OKAY) {
        if (mp_count_bits(mod) != 2048) {
            err = MP_READ_E;
        }
    }
#ifdef WOLFSSL_SMALL_STACK
    if (err == MP_OKAY) {
        d = (sp_digit*)XMALLOC(sizeof(*d) * 36 * 4, NULL, DYNAMIC_TYPE_DH);
        if (d == NULL)
            err = MEMORY_E;
    }

    if (err == MP_OKAY) {
        b = d;
        e = b + 36 * 2;
        m = e + 36;
        r = b;
    }
#else
    r = b = bd;
    e = ed;
    m = md;
#endif

    if (err == MP_OKAY) {
        sp_2048_from_mp(b, 36, base);
        sp_2048_from_bin(e, 36, exp, expLen);
        sp_2048_from_mp(m, 36, mod);

    #ifdef HAVE_FFDHE_2048
        if (base->used == 1 && base->dp[0] == 2U &&
                (m[35] >> 21) == 0xffffffffL) {
            err = sp_2048_mod_exp_2_36(r, e, expLen * 8U, m);
        }
        else {
    #endif
            err = sp_2048_mod_exp_36(r, b, e, expLen * 8U, m, 0);
    #ifdef HAVE_FFDHE_2048
        }
    #endif
    }

    if (err == MP_OKAY) {
        sp_2048_to_bin(r, out);
        *outLen = 256;
        for (i=0; i<256U && out[i] == 0U; i++) {
        }
        *outLen -= i;
        XMEMMOVE(out, out + i, *outLen);
    }

#ifdef WOLFSSL_SMALL_STACK
    if (d != NULL) {
        XMEMSET(e, 0, sizeof(sp_digit) * 36U);
        XFREE(d, NULL, DYNAMIC_TYPE_DH);
    }
#else
    XMEMSET(e, 0, sizeof(sp_digit) * 36U);
#endif

    return err;
#endif
}
#endif /* WOLFSSL_HAVE_SP_DH */

/* Perform the modular exponentiation for Diffie-Hellman.
 *
 * base  Base. MP integer.
 * exp   Exponent. MP integer.
 * mod   Modulus. MP integer.
 * res   Result. MP integer.
 * returns 0 on success, MP_READ_E if there are too many bytes in an array
 * and MEMORY_E if memory allocation fails.
 */
int sp_ModExp_1024(mp_int* base, mp_int* exp, mp_int* mod, mp_int* res)
{
#ifdef WOLFSSL_SP_SMALL
    int err = MP_OKAY;
    sp_digit* d = NULL;
    sp_digit* b;
    sp_digit* e;
    sp_digit* m;
    sp_digit* r;
    int expBits = mp_count_bits(exp);

    if (mp_count_bits(base) > 1024) {
        err = MP_READ_E;
    }

    if (err == MP_OKAY) {
        if (expBits > 1024) {
            err = MP_READ_E;
        }
    }

    if (err == MP_OKAY) {
        if (mp_count_bits(mod) != 1024) {
            err = MP_READ_E;
        }
    }

    if (err == MP_OKAY) {
        d = (sp_digit*)XMALLOC(sizeof(*d) * 18 * 4, NULL, DYNAMIC_TYPE_DH);
        if (d == NULL) {
            err = MEMORY_E;
        }
    }

    if (err == MP_OKAY) {
        b = d;
        e = b + 18 * 2;
        m = e + 18;
        r = b;

        sp_2048_from_mp(b, 18, base);
        sp_2048_from_mp(e, 18, exp);
        sp_2048_from_mp(m, 18, mod);

        err = sp_2048_mod_exp_18(r, b, e, mp_count_bits(exp), m, 0);
    }

    if (err == MP_OKAY) {
        XMEMSET(r + 18, 0, sizeof(*r) * 18U);
        err = sp_2048_to_mp(r, res);
    }

    if (d != NULL) {
        XMEMSET(e, 0, sizeof(sp_digit) * 18U);
        XFREE(d, NULL, DYNAMIC_TYPE_DH);
    }
    return err;
#else
#ifndef WOLFSSL_SMALL_STACK
    sp_digit bd[36], ed[18], md[18];
#else
    sp_digit* d = NULL;
#endif
    sp_digit* b;
    sp_digit* e;
    sp_digit* m;
    sp_digit* r;
    int err = MP_OKAY;
    int expBits = mp_count_bits(exp);

    if (mp_count_bits(base) > 1024) {
        err = MP_READ_E;
    }

    if (err == MP_OKAY) {
        if (expBits > 1024) {
            err = MP_READ_E;
        }
    }
    
    if (err == MP_OKAY) {
        if (mp_count_bits(mod) != 1024) {
            err = MP_READ_E;
        }
    }

#ifdef WOLFSSL_SMALL_STACK
    if (err == MP_OKAY) {
        d = (sp_digit*)XMALLOC(sizeof(*d) * 18 * 4, NULL, DYNAMIC_TYPE_DH);
        if (d == NULL)
            err = MEMORY_E;
    }

    if (err == MP_OKAY) {
        b = d;
        e = b + 18 * 2;
        m = e + 18;
        r = b;
    }
#else
    r = b = bd;
    e = ed;
    m = md;
#endif

    if (err == MP_OKAY) {
        sp_2048_from_mp(b, 18, base);
        sp_2048_from_mp(e, 18, exp);
        sp_2048_from_mp(m, 18, mod);

        err = sp_2048_mod_exp_18(r, b, e, expBits, m, 0);
    }

    if (err == MP_OKAY) {
        XMEMSET(r + 18, 0, sizeof(*r) * 18U);
        err = sp_2048_to_mp(r, res);
    }


#ifdef WOLFSSL_SMALL_STACK
    if (d != NULL) {
        XMEMSET(e, 0, sizeof(sp_digit) * 18U);
        XFREE(d, NULL, DYNAMIC_TYPE_DH);
    }
#else
    XMEMSET(e, 0, sizeof(sp_digit) * 18U);
#endif

    return err;
#endif
}

#endif /* WOLFSSL_HAVE_SP_DH || (WOLFSSL_HAVE_SP_RSA && !WOLFSSL_RSA_PUBLIC_ONLY) */

#endif /* !WOLFSSL_SP_NO_2048 */

#ifndef WOLFSSL_SP_NO_3072
/* Read big endian unsigned byte array into r.
 *
 * r  A single precision integer.
 * size  Maximum number of bytes to convert
 * a  Byte array.
 * n  Number of bytes in array to read.
 */
static void sp_3072_from_bin(sp_digit* r, int size, const byte* a, int n)
{
    int i, j = 0;
    word32 s = 0;

    r[0] = 0;
    for (i = n-1; i >= 0; i--) {
        r[j] |= (((sp_digit)a[i]) << s);
        if (s >= 49U) {
            r[j] &= 0x1ffffffffffffffL;
            s = 57U - s;
            if (j + 1 >= size) {
                break;
            }
            r[++j] = (sp_digit)a[i] >> s;
            s = 8U - s;
        }
        else {
            s += 8U;
        }
    }

    for (j++; j < size; j++) {
        r[j] = 0;
    }
}

/* Convert an mp_int to an array of sp_digit.
 *
 * r  A single precision integer.
 * size  Maximum number of bytes to convert
 * a  A multi-precision integer.
 */
static void sp_3072_from_mp(sp_digit* r, int size, const mp_int* a)
{
#if DIGIT_BIT == 57
    int j;

    XMEMCPY(r, a->dp, sizeof(sp_digit) * a->used);

    for (j = a->used; j < size; j++) {
        r[j] = 0;
    }
#elif DIGIT_BIT > 57
    int i, j = 0;
    word32 s = 0;

    r[0] = 0;
    for (i = 0; i < a->used && j < size; i++) {
        r[j] |= ((sp_digit)a->dp[i] << s);
        r[j] &= 0x1ffffffffffffffL;
        s = 57U - s;
        if (j + 1 >= size) {
            break;
        }
        /* lint allow cast of mismatch word32 and mp_digit */
        r[++j] = (sp_digit)(a->dp[i] >> s); /*lint !e9033*/
        while ((s + 57U) <= (word32)DIGIT_BIT) {
            s += 57U;
            r[j] &= 0x1ffffffffffffffL;
            if (j + 1 >= size) {
                break;
            }
            if (s < (word32)DIGIT_BIT) {
                /* lint allow cast of mismatch word32 and mp_digit */
                r[++j] = (sp_digit)(a->dp[i] >> s); /*lint !e9033*/
            }
            else {
                r[++j] = 0L;
            }
        }
        s = (word32)DIGIT_BIT - s;
    }

    for (j++; j < size; j++) {
        r[j] = 0;
    }
#else
    int i, j = 0, s = 0;

    r[0] = 0;
    for (i = 0; i < a->used && j < size; i++) {
        r[j] |= ((sp_digit)a->dp[i]) << s;
        if (s + DIGIT_BIT >= 57) {
            r[j] &= 0x1ffffffffffffffL;
            if (j + 1 >= size) {
                break;
            }
            s = 57 - s;
            if (s == DIGIT_BIT) {
                r[++j] = 0;
                s = 0;
            }
            else {
                r[++j] = a->dp[i] >> s;
                s = DIGIT_BIT - s;
            }
        }
        else {
            s += DIGIT_BIT;
        }
    }

    for (j++; j < size; j++) {
        r[j] = 0;
    }
#endif
}

/* Write r as big endian to byte array.
 * Fixed length number of bytes written: 384
 *
 * r  A single precision integer.
 * a  Byte array.
 */
static void sp_3072_to_bin(sp_digit* r, byte* a)
{
    int i, j, s = 0, b;

    for (i=0; i<53; i++) {
        r[i+1] += r[i] >> 57;
        r[i] &= 0x1ffffffffffffffL;
    }
    j = 3072 / 8 - 1;
    a[j] = 0;
    for (i=0; i<54 && j>=0; i++) {
        b = 0;
        /* lint allow cast of mismatch sp_digit and int */
        a[j--] |= (byte)(r[i] << s); /*lint !e9033*/
        b += 8 - s;
        if (j < 0) {
            break;
        }
        while (b < 57) {
            a[j--] = (byte)(r[i] >> b);
            b += 8;
            if (j < 0) {
                break;
            }
        }
        s = 8 - (b - 57);
        if (j >= 0) {
            a[j] = 0;
        }
        if (s != 0) {
            j++;
        }
    }
}

#ifndef WOLFSSL_SP_SMALL
/* Multiply a and b into r. (r = a * b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A single precision integer.
 */
SP_NOINLINE static void sp_3072_mul_9(sp_digit* r, const sp_digit* a,
    const sp_digit* b)
{
    int128_t t0   = ((int128_t)a[ 0]) * b[ 0];
    int128_t t1   = ((int128_t)a[ 0]) * b[ 1]
                 + ((int128_t)a[ 1]) * b[ 0];
    int128_t t2   = ((int128_t)a[ 0]) * b[ 2]
                 + ((int128_t)a[ 1]) * b[ 1]
                 + ((int128_t)a[ 2]) * b[ 0];
    int128_t t3   = ((int128_t)a[ 0]) * b[ 3]
                 + ((int128_t)a[ 1]) * b[ 2]
                 + ((int128_t)a[ 2]) * b[ 1]
                 + ((int128_t)a[ 3]) * b[ 0];
    int128_t t4   = ((int128_t)a[ 0]) * b[ 4]
                 + ((int128_t)a[ 1]) * b[ 3]
                 + ((int128_t)a[ 2]) * b[ 2]
                 + ((int128_t)a[ 3]) * b[ 1]
                 + ((int128_t)a[ 4]) * b[ 0];
    int128_t t5   = ((int128_t)a[ 0]) * b[ 5]
                 + ((int128_t)a[ 1]) * b[ 4]
                 + ((int128_t)a[ 2]) * b[ 3]
                 + ((int128_t)a[ 3]) * b[ 2]
                 + ((int128_t)a[ 4]) * b[ 1]
                 + ((int128_t)a[ 5]) * b[ 0];
    int128_t t6   = ((int128_t)a[ 0]) * b[ 6]
                 + ((int128_t)a[ 1]) * b[ 5]
                 + ((int128_t)a[ 2]) * b[ 4]
                 + ((int128_t)a[ 3]) * b[ 3]
                 + ((int128_t)a[ 4]) * b[ 2]
                 + ((int128_t)a[ 5]) * b[ 1]
                 + ((int128_t)a[ 6]) * b[ 0];
    int128_t t7   = ((int128_t)a[ 0]) * b[ 7]
                 + ((int128_t)a[ 1]) * b[ 6]
                 + ((int128_t)a[ 2]) * b[ 5]
                 + ((int128_t)a[ 3]) * b[ 4]
                 + ((int128_t)a[ 4]) * b[ 3]
                 + ((int128_t)a[ 5]) * b[ 2]
                 + ((int128_t)a[ 6]) * b[ 1]
                 + ((int128_t)a[ 7]) * b[ 0];
    int128_t t8   = ((int128_t)a[ 0]) * b[ 8]
                 + ((int128_t)a[ 1]) * b[ 7]
                 + ((int128_t)a[ 2]) * b[ 6]
                 + ((int128_t)a[ 3]) * b[ 5]
                 + ((int128_t)a[ 4]) * b[ 4]
                 + ((int128_t)a[ 5]) * b[ 3]
                 + ((int128_t)a[ 6]) * b[ 2]
                 + ((int128_t)a[ 7]) * b[ 1]
                 + ((int128_t)a[ 8]) * b[ 0];
    int128_t t9   = ((int128_t)a[ 1]) * b[ 8]
                 + ((int128_t)a[ 2]) * b[ 7]
                 + ((int128_t)a[ 3]) * b[ 6]
                 + ((int128_t)a[ 4]) * b[ 5]
                 + ((int128_t)a[ 5]) * b[ 4]
                 + ((int128_t)a[ 6]) * b[ 3]
                 + ((int128_t)a[ 7]) * b[ 2]
                 + ((int128_t)a[ 8]) * b[ 1];
    int128_t t10  = ((int128_t)a[ 2]) * b[ 8]
                 + ((int128_t)a[ 3]) * b[ 7]
                 + ((int128_t)a[ 4]) * b[ 6]
                 + ((int128_t)a[ 5]) * b[ 5]
                 + ((int128_t)a[ 6]) * b[ 4]
                 + ((int128_t)a[ 7]) * b[ 3]
                 + ((int128_t)a[ 8]) * b[ 2];
    int128_t t11  = ((int128_t)a[ 3]) * b[ 8]
                 + ((int128_t)a[ 4]) * b[ 7]
                 + ((int128_t)a[ 5]) * b[ 6]
                 + ((int128_t)a[ 6]) * b[ 5]
                 + ((int128_t)a[ 7]) * b[ 4]
                 + ((int128_t)a[ 8]) * b[ 3];
    int128_t t12  = ((int128_t)a[ 4]) * b[ 8]
                 + ((int128_t)a[ 5]) * b[ 7]
                 + ((int128_t)a[ 6]) * b[ 6]
                 + ((int128_t)a[ 7]) * b[ 5]
                 + ((int128_t)a[ 8]) * b[ 4];
    int128_t t13  = ((int128_t)a[ 5]) * b[ 8]
                 + ((int128_t)a[ 6]) * b[ 7]
                 + ((int128_t)a[ 7]) * b[ 6]
                 + ((int128_t)a[ 8]) * b[ 5];
    int128_t t14  = ((int128_t)a[ 6]) * b[ 8]
                 + ((int128_t)a[ 7]) * b[ 7]
                 + ((int128_t)a[ 8]) * b[ 6];
    int128_t t15  = ((int128_t)a[ 7]) * b[ 8]
                 + ((int128_t)a[ 8]) * b[ 7];
    int128_t t16  = ((int128_t)a[ 8]) * b[ 8];

    t1   += t0  >> 57; r[ 0] = t0  & 0x1ffffffffffffffL;
    t2   += t1  >> 57; r[ 1] = t1  & 0x1ffffffffffffffL;
    t3   += t2  >> 57; r[ 2] = t2  & 0x1ffffffffffffffL;
    t4   += t3  >> 57; r[ 3] = t3  & 0x1ffffffffffffffL;
    t5   += t4  >> 57; r[ 4] = t4  & 0x1ffffffffffffffL;
    t6   += t5  >> 57; r[ 5] = t5  & 0x1ffffffffffffffL;
    t7   += t6  >> 57; r[ 6] = t6  & 0x1ffffffffffffffL;
    t8   += t7  >> 57; r[ 7] = t7  & 0x1ffffffffffffffL;
    t9   += t8  >> 57; r[ 8] = t8  & 0x1ffffffffffffffL;
    t10  += t9  >> 57; r[ 9] = t9  & 0x1ffffffffffffffL;
    t11  += t10 >> 57; r[10] = t10 & 0x1ffffffffffffffL;
    t12  += t11 >> 57; r[11] = t11 & 0x1ffffffffffffffL;
    t13  += t12 >> 57; r[12] = t12 & 0x1ffffffffffffffL;
    t14  += t13 >> 57; r[13] = t13 & 0x1ffffffffffffffL;
    t15  += t14 >> 57; r[14] = t14 & 0x1ffffffffffffffL;
    t16  += t15 >> 57; r[15] = t15 & 0x1ffffffffffffffL;
    r[17] = (sp_digit)(t16 >> 57);
                       r[16] = t16 & 0x1ffffffffffffffL;
}

/* Square a and put result in r. (r = a * a)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 */
SP_NOINLINE static void sp_3072_sqr_9(sp_digit* r, const sp_digit* a)
{
    int128_t t0   =  ((int128_t)a[ 0]) * a[ 0];
    int128_t t1   = (((int128_t)a[ 0]) * a[ 1]) * 2;
    int128_t t2   = (((int128_t)a[ 0]) * a[ 2]) * 2
                 +  ((int128_t)a[ 1]) * a[ 1];
    int128_t t3   = (((int128_t)a[ 0]) * a[ 3]
                 +  ((int128_t)a[ 1]) * a[ 2]) * 2;
    int128_t t4   = (((int128_t)a[ 0]) * a[ 4]
                 +  ((int128_t)a[ 1]) * a[ 3]) * 2
                 +  ((int128_t)a[ 2]) * a[ 2];
    int128_t t5   = (((int128_t)a[ 0]) * a[ 5]
                 +  ((int128_t)a[ 1]) * a[ 4]
                 +  ((int128_t)a[ 2]) * a[ 3]) * 2;
    int128_t t6   = (((int128_t)a[ 0]) * a[ 6]
                 +  ((int128_t)a[ 1]) * a[ 5]
                 +  ((int128_t)a[ 2]) * a[ 4]) * 2
                 +  ((int128_t)a[ 3]) * a[ 3];
    int128_t t7   = (((int128_t)a[ 0]) * a[ 7]
                 +  ((int128_t)a[ 1]) * a[ 6]
                 +  ((int128_t)a[ 2]) * a[ 5]
                 +  ((int128_t)a[ 3]) * a[ 4]) * 2;
    int128_t t8   = (((int128_t)a[ 0]) * a[ 8]
                 +  ((int128_t)a[ 1]) * a[ 7]
                 +  ((int128_t)a[ 2]) * a[ 6]
                 +  ((int128_t)a[ 3]) * a[ 5]) * 2
                 +  ((int128_t)a[ 4]) * a[ 4];
    int128_t t9   = (((int128_t)a[ 1]) * a[ 8]
                 +  ((int128_t)a[ 2]) * a[ 7]
                 +  ((int128_t)a[ 3]) * a[ 6]
                 +  ((int128_t)a[ 4]) * a[ 5]) * 2;
    int128_t t10  = (((int128_t)a[ 2]) * a[ 8]
                 +  ((int128_t)a[ 3]) * a[ 7]
                 +  ((int128_t)a[ 4]) * a[ 6]) * 2
                 +  ((int128_t)a[ 5]) * a[ 5];
    int128_t t11  = (((int128_t)a[ 3]) * a[ 8]
                 +  ((int128_t)a[ 4]) * a[ 7]
                 +  ((int128_t)a[ 5]) * a[ 6]) * 2;
    int128_t t12  = (((int128_t)a[ 4]) * a[ 8]
                 +  ((int128_t)a[ 5]) * a[ 7]) * 2
                 +  ((int128_t)a[ 6]) * a[ 6];
    int128_t t13  = (((int128_t)a[ 5]) * a[ 8]
                 +  ((int128_t)a[ 6]) * a[ 7]) * 2;
    int128_t t14  = (((int128_t)a[ 6]) * a[ 8]) * 2
                 +  ((int128_t)a[ 7]) * a[ 7];
    int128_t t15  = (((int128_t)a[ 7]) * a[ 8]) * 2;
    int128_t t16  =  ((int128_t)a[ 8]) * a[ 8];

    t1   += t0  >> 57; r[ 0] = t0  & 0x1ffffffffffffffL;
    t2   += t1  >> 57; r[ 1] = t1  & 0x1ffffffffffffffL;
    t3   += t2  >> 57; r[ 2] = t2  & 0x1ffffffffffffffL;
    t4   += t3  >> 57; r[ 3] = t3  & 0x1ffffffffffffffL;
    t5   += t4  >> 57; r[ 4] = t4  & 0x1ffffffffffffffL;
    t6   += t5  >> 57; r[ 5] = t5  & 0x1ffffffffffffffL;
    t7   += t6  >> 57; r[ 6] = t6  & 0x1ffffffffffffffL;
    t8   += t7  >> 57; r[ 7] = t7  & 0x1ffffffffffffffL;
    t9   += t8  >> 57; r[ 8] = t8  & 0x1ffffffffffffffL;
    t10  += t9  >> 57; r[ 9] = t9  & 0x1ffffffffffffffL;
    t11  += t10 >> 57; r[10] = t10 & 0x1ffffffffffffffL;
    t12  += t11 >> 57; r[11] = t11 & 0x1ffffffffffffffL;
    t13  += t12 >> 57; r[12] = t12 & 0x1ffffffffffffffL;
    t14  += t13 >> 57; r[13] = t13 & 0x1ffffffffffffffL;
    t15  += t14 >> 57; r[14] = t14 & 0x1ffffffffffffffL;
    t16  += t15 >> 57; r[15] = t15 & 0x1ffffffffffffffL;
    r[17] = (sp_digit)(t16 >> 57);
                       r[16] = t16 & 0x1ffffffffffffffL;
}

/* Add b to a into r. (r = a + b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A single precision integer.
 */
SP_NOINLINE static int sp_3072_add_9(sp_digit* r, const sp_digit* a,
        const sp_digit* b)
{
    r[ 0] = a[ 0] + b[ 0];
    r[ 1] = a[ 1] + b[ 1];
    r[ 2] = a[ 2] + b[ 2];
    r[ 3] = a[ 3] + b[ 3];
    r[ 4] = a[ 4] + b[ 4];
    r[ 5] = a[ 5] + b[ 5];
    r[ 6] = a[ 6] + b[ 6];
    r[ 7] = a[ 7] + b[ 7];
    r[ 8] = a[ 8] + b[ 8];

    return 0;
}

/* Add b to a into r. (r = a + b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A single precision integer.
 */
SP_NOINLINE static int sp_3072_add_18(sp_digit* r, const sp_digit* a,
        const sp_digit* b)
{
    int i;

    for (i = 0; i < 16; i += 8) {
        r[i + 0] = a[i + 0] + b[i + 0];
        r[i + 1] = a[i + 1] + b[i + 1];
        r[i + 2] = a[i + 2] + b[i + 2];
        r[i + 3] = a[i + 3] + b[i + 3];
        r[i + 4] = a[i + 4] + b[i + 4];
        r[i + 5] = a[i + 5] + b[i + 5];
        r[i + 6] = a[i + 6] + b[i + 6];
        r[i + 7] = a[i + 7] + b[i + 7];
    }
    r[16] = a[16] + b[16];
    r[17] = a[17] + b[17];

    return 0;
}

/* Sub b from a into r. (r = a - b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A single precision integer.
 */
SP_NOINLINE static int sp_3072_sub_18(sp_digit* r, const sp_digit* a,
        const sp_digit* b)
{
    int i;

    for (i = 0; i < 16; i += 8) {
        r[i + 0] = a[i + 0] - b[i + 0];
        r[i + 1] = a[i + 1] - b[i + 1];
        r[i + 2] = a[i + 2] - b[i + 2];
        r[i + 3] = a[i + 3] - b[i + 3];
        r[i + 4] = a[i + 4] - b[i + 4];
        r[i + 5] = a[i + 5] - b[i + 5];
        r[i + 6] = a[i + 6] - b[i + 6];
        r[i + 7] = a[i + 7] - b[i + 7];
    }
    r[16] = a[16] - b[16];
    r[17] = a[17] - b[17];

    return 0;
}

/* Multiply a and b into r. (r = a * b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A single precision integer.
 */
SP_NOINLINE static void sp_3072_mul_18(sp_digit* r, const sp_digit* a,
    const sp_digit* b)
{
    sp_digit* z0 = r;
    sp_digit z1[18];
    sp_digit* a1 = z1;
    sp_digit b1[9];
    sp_digit* z2 = r + 18;
    (void)sp_3072_add_9(a1, a, &a[9]);
    (void)sp_3072_add_9(b1, b, &b[9]);
    sp_3072_mul_9(z2, &a[9], &b[9]);
    sp_3072_mul_9(z0, a, b);
    sp_3072_mul_9(z1, a1, b1);
    (void)sp_3072_sub_18(z1, z1, z2);
    (void)sp_3072_sub_18(z1, z1, z0);
    (void)sp_3072_add_18(r + 9, r + 9, z1);
}

/* Square a and put result in r. (r = a * a)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 */
SP_NOINLINE static void sp_3072_sqr_18(sp_digit* r, const sp_digit* a)
{
    sp_digit* z0 = r;
    sp_digit z1[18];
    sp_digit* a1 = z1;
    sp_digit* z2 = r + 18;
    (void)sp_3072_add_9(a1, a, &a[9]);
    sp_3072_sqr_9(z2, &a[9]);
    sp_3072_sqr_9(z0, a);
    sp_3072_sqr_9(z1, a1);
    (void)sp_3072_sub_18(z1, z1, z2);
    (void)sp_3072_sub_18(z1, z1, z0);
    (void)sp_3072_add_18(r + 9, r + 9, z1);
}

/* Sub b from a into r. (r = a - b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A single precision integer.
 */
SP_NOINLINE static int sp_3072_sub_36(sp_digit* r, const sp_digit* a,
        const sp_digit* b)
{
    int i;

    for (i = 0; i < 32; i += 8) {
        r[i + 0] = a[i + 0] - b[i + 0];
        r[i + 1] = a[i + 1] - b[i + 1];
        r[i + 2] = a[i + 2] - b[i + 2];
        r[i + 3] = a[i + 3] - b[i + 3];
        r[i + 4] = a[i + 4] - b[i + 4];
        r[i + 5] = a[i + 5] - b[i + 5];
        r[i + 6] = a[i + 6] - b[i + 6];
        r[i + 7] = a[i + 7] - b[i + 7];
    }
    r[32] = a[32] - b[32];
    r[33] = a[33] - b[33];
    r[34] = a[34] - b[34];
    r[35] = a[35] - b[35];

    return 0;
}

/* Add b to a into r. (r = a + b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A single precision integer.
 */
SP_NOINLINE static int sp_3072_add_36(sp_digit* r, const sp_digit* a,
        const sp_digit* b)
{
    int i;

    for (i = 0; i < 32; i += 8) {
        r[i + 0] = a[i + 0] + b[i + 0];
        r[i + 1] = a[i + 1] + b[i + 1];
        r[i + 2] = a[i + 2] + b[i + 2];
        r[i + 3] = a[i + 3] + b[i + 3];
        r[i + 4] = a[i + 4] + b[i + 4];
        r[i + 5] = a[i + 5] + b[i + 5];
        r[i + 6] = a[i + 6] + b[i + 6];
        r[i + 7] = a[i + 7] + b[i + 7];
    }
    r[32] = a[32] + b[32];
    r[33] = a[33] + b[33];
    r[34] = a[34] + b[34];
    r[35] = a[35] + b[35];

    return 0;
}

/* Multiply a and b into r. (r = a * b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A single precision integer.
 */
SP_NOINLINE static void sp_3072_mul_54(sp_digit* r, const sp_digit* a,
    const sp_digit* b)
{
    sp_digit p0[36];
    sp_digit p1[36];
    sp_digit p2[36];
    sp_digit p3[36];
    sp_digit p4[36];
    sp_digit p5[36];
    sp_digit t0[36];
    sp_digit t1[36];
    sp_digit t2[36];
    sp_digit a0[18];
    sp_digit a1[18];
    sp_digit a2[18];
    sp_digit b0[18];
    sp_digit b1[18];
    sp_digit b2[18];
    (void)sp_3072_add_18(a0, a, &a[18]);
    (void)sp_3072_add_18(b0, b, &b[18]);
    (void)sp_3072_add_18(a1, &a[18], &a[36]);
    (void)sp_3072_add_18(b1, &b[18], &b[36]);
    (void)sp_3072_add_18(a2, a0, &a[36]);
    (void)sp_3072_add_18(b2, b0, &b[36]);
    sp_3072_mul_18(p0, a, b);
    sp_3072_mul_18(p2, &a[18], &b[18]);
    sp_3072_mul_18(p4, &a[36], &b[36]);
    sp_3072_mul_18(p1, a0, b0);
    sp_3072_mul_18(p3, a1, b1);
    sp_3072_mul_18(p5, a2, b2);
    XMEMSET(r, 0, sizeof(*r)*2U*54U);
    (void)sp_3072_sub_36(t0, p3, p2);
    (void)sp_3072_sub_36(t1, p1, p2);
    (void)sp_3072_sub_36(t2, p5, t0);
    (void)sp_3072_sub_36(t2, t2, t1);
    (void)sp_3072_sub_36(t0, t0, p4);
    (void)sp_3072_sub_36(t1, t1, p0);
    (void)sp_3072_add_36(r, r, p0);
    (void)sp_3072_add_36(&r[18], &r[18], t1);
    (void)sp_3072_add_36(&r[36], &r[36], t2);
    (void)sp_3072_add_36(&r[54], &r[54], t0);
    (void)sp_3072_add_36(&r[72], &r[72], p4);
}

/* Square a into r. (r = a * a)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 */
SP_NOINLINE static void sp_3072_sqr_54(sp_digit* r, const sp_digit* a)
{
    sp_digit p0[36];
    sp_digit p1[36];
    sp_digit p2[36];
    sp_digit p3[36];
    sp_digit p4[36];
    sp_digit p5[36];
    sp_digit t0[36];
    sp_digit t1[36];
    sp_digit t2[36];
    sp_digit a0[18];
    sp_digit a1[18];
    sp_digit a2[18];
    (void)sp_3072_add_18(a0, a, &a[18]);
    (void)sp_3072_add_18(a1, &a[18], &a[36]);
    (void)sp_3072_add_18(a2, a0, &a[36]);
    sp_3072_sqr_18(p0, a);
    sp_3072_sqr_18(p2, &a[18]);
    sp_3072_sqr_18(p4, &a[36]);
    sp_3072_sqr_18(p1, a0);
    sp_3072_sqr_18(p3, a1);
    sp_3072_sqr_18(p5, a2);
    XMEMSET(r, 0, sizeof(*r)*2U*54U);
    (void)sp_3072_sub_36(t0, p3, p2);
    (void)sp_3072_sub_36(t1, p1, p2);
    (void)sp_3072_sub_36(t2, p5, t0);
    (void)sp_3072_sub_36(t2, t2, t1);
    (void)sp_3072_sub_36(t0, t0, p4);
    (void)sp_3072_sub_36(t1, t1, p0);
    (void)sp_3072_add_36(r, r, p0);
    (void)sp_3072_add_36(&r[18], &r[18], t1);
    (void)sp_3072_add_36(&r[36], &r[36], t2);
    (void)sp_3072_add_36(&r[54], &r[54], t0);
    (void)sp_3072_add_36(&r[72], &r[72], p4);
}

#endif /* !WOLFSSL_SP_SMALL */
#ifdef WOLFSSL_SP_SMALL
/* Add b to a into r. (r = a + b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A single precision integer.
 */
SP_NOINLINE static int sp_3072_add_54(sp_digit* r, const sp_digit* a,
        const sp_digit* b)
{
    int i;

    for (i = 0; i < 54; i++) {
        r[i] = a[i] + b[i];
    }

    return 0;
}
#else
/* Add b to a into r. (r = a + b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A single precision integer.
 */
SP_NOINLINE static int sp_3072_add_54(sp_digit* r, const sp_digit* a,
        const sp_digit* b)
{
    int i;

    for (i = 0; i < 48; i += 8) {
        r[i + 0] = a[i + 0] + b[i + 0];
        r[i + 1] = a[i + 1] + b[i + 1];
        r[i + 2] = a[i + 2] + b[i + 2];
        r[i + 3] = a[i + 3] + b[i + 3];
        r[i + 4] = a[i + 4] + b[i + 4];
        r[i + 5] = a[i + 5] + b[i + 5];
        r[i + 6] = a[i + 6] + b[i + 6];
        r[i + 7] = a[i + 7] + b[i + 7];
    }
    r[48] = a[48] + b[48];
    r[49] = a[49] + b[49];
    r[50] = a[50] + b[50];
    r[51] = a[51] + b[51];
    r[52] = a[52] + b[52];
    r[53] = a[53] + b[53];

    return 0;
}

#endif /* WOLFSSL_SP_SMALL */
#ifdef WOLFSSL_SP_SMALL
/* Sub b from a into r. (r = a - b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A single precision integer.
 */
SP_NOINLINE static int sp_3072_sub_54(sp_digit* r, const sp_digit* a,
        const sp_digit* b)
{
    int i;

    for (i = 0; i < 54; i++) {
        r[i] = a[i] - b[i];
    }

    return 0;
}

#else
/* Sub b from a into r. (r = a - b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A single precision integer.
 */
SP_NOINLINE static int sp_3072_sub_54(sp_digit* r, const sp_digit* a,
        const sp_digit* b)
{
    int i;

    for (i = 0; i < 48; i += 8) {
        r[i + 0] = a[i + 0] - b[i + 0];
        r[i + 1] = a[i + 1] - b[i + 1];
        r[i + 2] = a[i + 2] - b[i + 2];
        r[i + 3] = a[i + 3] - b[i + 3];
        r[i + 4] = a[i + 4] - b[i + 4];
        r[i + 5] = a[i + 5] - b[i + 5];
        r[i + 6] = a[i + 6] - b[i + 6];
        r[i + 7] = a[i + 7] - b[i + 7];
    }
    r[48] = a[48] - b[48];
    r[49] = a[49] - b[49];
    r[50] = a[50] - b[50];
    r[51] = a[51] - b[51];
    r[52] = a[52] - b[52];
    r[53] = a[53] - b[53];

    return 0;
}

#endif /* WOLFSSL_SP_SMALL */
#ifdef WOLFSSL_SP_SMALL
/* Multiply a and b into r. (r = a * b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A single precision integer.
 */
SP_NOINLINE static void sp_3072_mul_54(sp_digit* r, const sp_digit* a,
    const sp_digit* b)
{
    int i, j, k;
    int128_t c;

    c = ((int128_t)a[53]) * b[53];
    r[107] = (sp_digit)(c >> 57);
    c = (c & 0x1ffffffffffffffL) << 57;
    for (k = 105; k >= 0; k--) {
        for (i = 53; i >= 0; i--) {
            j = k - i;
            if (j >= 54) {
                break;
            }
            if (j < 0) {
                continue;
            }

            c += ((int128_t)a[i]) * b[j];
        }
        r[k + 2] += c >> 114;
        r[k + 1] = (c >> 57) & 0x1ffffffffffffffL;
        c = (c & 0x1ffffffffffffffL) << 57;
    }
    r[0] = (sp_digit)(c >> 57);
}

/* Square a and put result in r. (r = a * a)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 */
SP_NOINLINE static void sp_3072_sqr_54(sp_digit* r, const sp_digit* a)
{
    int i, j, k;
    int128_t c;

    c = ((int128_t)a[53]) * a[53];
    r[107] = (sp_digit)(c >> 57);
    c = (c & 0x1ffffffffffffffL) << 57;
    for (k = 105; k >= 0; k--) {
        for (i = 53; i >= 0; i--) {
            j = k - i;
            if (j >= 54 || i <= j) {
                break;
            }
            if (j < 0) {
                continue;
            }

            c += ((int128_t)a[i]) * a[j] * 2;
        }
        if (i == j) {
           c += ((int128_t)a[i]) * a[i];
        }

        r[k + 2] += c >> 114;
        r[k + 1] = (c >> 57) & 0x1ffffffffffffffL;
        c = (c & 0x1ffffffffffffffL) << 57;
    }
    r[0] = (sp_digit)(c >> 57);
}

#endif /* WOLFSSL_SP_SMALL */
#if (defined(WOLFSSL_HAVE_SP_RSA) || defined(WOLFSSL_HAVE_SP_DH)) && !defined(WOLFSSL_RSA_PUBLIC_ONLY)
#ifdef WOLFSSL_SP_SMALL
/* Add b to a into r. (r = a + b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A single precision integer.
 */
SP_NOINLINE static int sp_3072_add_27(sp_digit* r, const sp_digit* a,
        const sp_digit* b)
{
    int i;

    for (i = 0; i < 27; i++) {
        r[i] = a[i] + b[i];
    }

    return 0;
}
#else
/* Add b to a into r. (r = a + b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A single precision integer.
 */
SP_NOINLINE static int sp_3072_add_27(sp_digit* r, const sp_digit* a,
        const sp_digit* b)
{
    int i;

    for (i = 0; i < 24; i += 8) {
        r[i + 0] = a[i + 0] + b[i + 0];
        r[i + 1] = a[i + 1] + b[i + 1];
        r[i + 2] = a[i + 2] + b[i + 2];
        r[i + 3] = a[i + 3] + b[i + 3];
        r[i + 4] = a[i + 4] + b[i + 4];
        r[i + 5] = a[i + 5] + b[i + 5];
        r[i + 6] = a[i + 6] + b[i + 6];
        r[i + 7] = a[i + 7] + b[i + 7];
    }
    r[24] = a[24] + b[24];
    r[25] = a[25] + b[25];
    r[26] = a[26] + b[26];

    return 0;
}

#endif /* WOLFSSL_SP_SMALL */
#ifdef WOLFSSL_SP_SMALL
/* Sub b from a into r. (r = a - b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A single precision integer.
 */
SP_NOINLINE static int sp_3072_sub_27(sp_digit* r, const sp_digit* a,
        const sp_digit* b)
{
    int i;

    for (i = 0; i < 27; i++) {
        r[i] = a[i] - b[i];
    }

    return 0;
}

#else
/* Sub b from a into r. (r = a - b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A single precision integer.
 */
SP_NOINLINE static int sp_3072_sub_27(sp_digit* r, const sp_digit* a,
        const sp_digit* b)
{
    int i;

    for (i = 0; i < 24; i += 8) {
        r[i + 0] = a[i + 0] - b[i + 0];
        r[i + 1] = a[i + 1] - b[i + 1];
        r[i + 2] = a[i + 2] - b[i + 2];
        r[i + 3] = a[i + 3] - b[i + 3];
        r[i + 4] = a[i + 4] - b[i + 4];
        r[i + 5] = a[i + 5] - b[i + 5];
        r[i + 6] = a[i + 6] - b[i + 6];
        r[i + 7] = a[i + 7] - b[i + 7];
    }
    r[24] = a[24] - b[24];
    r[25] = a[25] - b[25];
    r[26] = a[26] - b[26];

    return 0;
}

#endif /* WOLFSSL_SP_SMALL */
#ifdef WOLFSSL_SP_SMALL
/* Multiply a and b into r. (r = a * b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A single precision integer.
 */
SP_NOINLINE static void sp_3072_mul_27(sp_digit* r, const sp_digit* a,
    const sp_digit* b)
{
    int i, j, k;
    int128_t c;

    c = ((int128_t)a[26]) * b[26];
    r[53] = (sp_digit)(c >> 57);
    c = (c & 0x1ffffffffffffffL) << 57;
    for (k = 51; k >= 0; k--) {
        for (i = 26; i >= 0; i--) {
            j = k - i;
            if (j >= 27) {
                break;
            }
            if (j < 0) {
                continue;
            }

            c += ((int128_t)a[i]) * b[j];
        }
        r[k + 2] += c >> 114;
        r[k + 1] = (c >> 57) & 0x1ffffffffffffffL;
        c = (c & 0x1ffffffffffffffL) << 57;
    }
    r[0] = (sp_digit)(c >> 57);
}

#else
/* Multiply a and b into r. (r = a * b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A single precision integer.
 */
SP_NOINLINE static void sp_3072_mul_27(sp_digit* r, const sp_digit* a,
    const sp_digit* b)
{
    int i, j;
    int128_t t[54];

    XMEMSET(t, 0, sizeof(t));
    for (i=0; i<27; i++) {
        for (j=0; j<27; j++) {
            t[i+j] += ((int128_t)a[i]) * b[j];
        }
    }
    for (i=0; i<53; i++) {
        r[i] = t[i] & 0x1ffffffffffffffL;
        t[i+1] += t[i] >> 57;
    }
    r[53] = (sp_digit)t[53];
}

#endif /* WOLFSSL_SP_SMALL */
#ifdef WOLFSSL_SP_SMALL
/* Square a and put result in r. (r = a * a)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 */
SP_NOINLINE static void sp_3072_sqr_27(sp_digit* r, const sp_digit* a)
{
    int i, j, k;
    int128_t c;

    c = ((int128_t)a[26]) * a[26];
    r[53] = (sp_digit)(c >> 57);
    c = (c & 0x1ffffffffffffffL) << 57;
    for (k = 51; k >= 0; k--) {
        for (i = 26; i >= 0; i--) {
            j = k - i;
            if (j >= 27 || i <= j) {
                break;
            }
            if (j < 0) {
                continue;
            }

            c += ((int128_t)a[i]) * a[j] * 2;
        }
        if (i == j) {
           c += ((int128_t)a[i]) * a[i];
        }

        r[k + 2] += c >> 114;
        r[k + 1] = (c >> 57) & 0x1ffffffffffffffL;
        c = (c & 0x1ffffffffffffffL) << 57;
    }
    r[0] = (sp_digit)(c >> 57);
}

#else
/* Square a and put result in r. (r = a * a)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 */
SP_NOINLINE static void sp_3072_sqr_27(sp_digit* r, const sp_digit* a)
{
    int i, j;
    int128_t t[54];

    XMEMSET(t, 0, sizeof(t));
    for (i=0; i<27; i++) {
        for (j=0; j<i; j++) {
            t[i+j] += (((int128_t)a[i]) * a[j]) * 2;
        }
        t[i+i] += ((int128_t)a[i]) * a[i];
    }
    for (i=0; i<53; i++) {
        r[i] = t[i] & 0x1ffffffffffffffL;
        t[i+1] += t[i] >> 57;
    }
    r[53] = (sp_digit)t[53];
}

#endif /* WOLFSSL_SP_SMALL */
#endif /* (WOLFSSL_HAVE_SP_RSA || WOLFSSL_HAVE_SP_DH) && !WOLFSSL_RSA_PUBLIC_ONLY */

/* Caclulate the bottom digit of -1/a mod 2^n.
 *
 * a    A single precision number.
 * rho  Bottom word of inverse.
 */
static void sp_3072_mont_setup(const sp_digit* a, sp_digit* rho)
{
    sp_digit x, b;

    b = a[0];
    x = (((b + 2) & 4) << 1) + b; /* here x*a==1 mod 2**4 */
    x *= 2 - b * x;               /* here x*a==1 mod 2**8 */
    x *= 2 - b * x;               /* here x*a==1 mod 2**16 */
    x *= 2 - b * x;               /* here x*a==1 mod 2**32 */
    x *= 2 - b * x;               /* here x*a==1 mod 2**64 */
    x &= 0x1ffffffffffffffL;

    /* rho = -1/m mod b */
    *rho = (1L << 57) - x;
}

/* Multiply a by scalar b into r. (r = a * b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A scalar.
 */
SP_NOINLINE static void sp_3072_mul_d_54(sp_digit* r, const sp_digit* a,
    sp_digit b)
{
#ifdef WOLFSSL_SP_SMALL
    int128_t tb = b;
    int128_t t = 0;
    int i;

    for (i = 0; i < 54; i++) {
        t += tb * a[i];
        r[i] = t & 0x1ffffffffffffffL;
        t >>= 57;
    }
    r[54] = (sp_digit)t;
#else
    int128_t tb = b;
    int128_t t[8];
    int i;

    t[0] = tb * a[0]; r[0] = t[0] & 0x1ffffffffffffffL;
    for (i = 0; i < 48; i += 8) {
        t[1] = tb * a[i+1];
        r[i+1] = (sp_digit)(t[0] >> 57) + (t[1] & 0x1ffffffffffffffL);
        t[2] = tb * a[i+2];
        r[i+2] = (sp_digit)(t[1] >> 57) + (t[2] & 0x1ffffffffffffffL);
        t[3] = tb * a[i+3];
        r[i+3] = (sp_digit)(t[2] >> 57) + (t[3] & 0x1ffffffffffffffL);
        t[4] = tb * a[i+4];
        r[i+4] = (sp_digit)(t[3] >> 57) + (t[4] & 0x1ffffffffffffffL);
        t[5] = tb * a[i+5];
        r[i+5] = (sp_digit)(t[4] >> 57) + (t[5] & 0x1ffffffffffffffL);
        t[6] = tb * a[i+6];
        r[i+6] = (sp_digit)(t[5] >> 57) + (t[6] & 0x1ffffffffffffffL);
        t[7] = tb * a[i+7];
        r[i+7] = (sp_digit)(t[6] >> 57) + (t[7] & 0x1ffffffffffffffL);
        t[0] = tb * a[i+8];
        r[i+8] = (sp_digit)(t[7] >> 57) + (t[0] & 0x1ffffffffffffffL);
    }
    t[1] = tb * a[49];
    r[49] = (sp_digit)(t[0] >> 57) + (t[1] & 0x1ffffffffffffffL);
    t[2] = tb * a[50];
    r[50] = (sp_digit)(t[1] >> 57) + (t[2] & 0x1ffffffffffffffL);
    t[3] = tb * a[51];
    r[51] = (sp_digit)(t[2] >> 57) + (t[3] & 0x1ffffffffffffffL);
    t[4] = tb * a[52];
    r[52] = (sp_digit)(t[3] >> 57) + (t[4] & 0x1ffffffffffffffL);
    t[5] = tb * a[53];
    r[53] = (sp_digit)(t[4] >> 57) + (t[5] & 0x1ffffffffffffffL);
    r[54] =  (sp_digit)(t[5] >> 57);
#endif /* WOLFSSL_SP_SMALL */
}

#if (defined(WOLFSSL_HAVE_SP_RSA) || defined(WOLFSSL_HAVE_SP_DH)) && !defined(WOLFSSL_RSA_PUBLIC_ONLY)
/* r = 2^n mod m where n is the number of bits to reduce by.
 * Given m must be 3072 bits, just need to subtract.
 *
 * r  A single precision number.
 * m  A single precision number.
 */
static void sp_3072_mont_norm_27(sp_digit* r, const sp_digit* m)
{
    /* Set r = 2^n - 1. */
#ifdef WOLFSSL_SP_SMALL
    int i;

    for (i=0; i<26; i++) {
        r[i] = 0x1ffffffffffffffL;
    }
#else
    int i;

    for (i = 0; i < 24; i += 8) {
        r[i + 0] = 0x1ffffffffffffffL;
        r[i + 1] = 0x1ffffffffffffffL;
        r[i + 2] = 0x1ffffffffffffffL;
        r[i + 3] = 0x1ffffffffffffffL;
        r[i + 4] = 0x1ffffffffffffffL;
        r[i + 5] = 0x1ffffffffffffffL;
        r[i + 6] = 0x1ffffffffffffffL;
        r[i + 7] = 0x1ffffffffffffffL;
    }
    r[24] = 0x1ffffffffffffffL;
    r[25] = 0x1ffffffffffffffL;
#endif
    r[26] = 0x3fffffffffffffL;

    /* r = (2^n - 1) mod n */
    (void)sp_3072_sub_27(r, r, m);

    /* Add one so r = 2^n mod m */
    r[0] += 1;
}

/* Compare a with b in constant time.
 *
 * a  A single precision integer.
 * b  A single precision integer.
 * return -ve, 0 or +ve if a is less than, equal to or greater than b
 * respectively.
 */
static sp_digit sp_3072_cmp_27(const sp_digit* a, const sp_digit* b)
{
    sp_digit r = 0;
#ifdef WOLFSSL_SP_SMALL
    int i;

    for (i=26; i>=0; i--) {
        r |= (a[i] - b[i]) & (0 - ((r == 0) ? (sp_digit)1 : (sp_digit)0));
    }
#else
    int i;

    r |= (a[26] - b[26]) & (0 - ((r == 0) ? (sp_digit)1 : (sp_digit)0));
    r |= (a[25] - b[25]) & (0 - ((r == 0) ? (sp_digit)1 : (sp_digit)0));
    r |= (a[24] - b[24]) & (0 - ((r == 0) ? (sp_digit)1 : (sp_digit)0));
    for (i = 16; i >= 0; i -= 8) {
        r |= (a[i + 7] - b[i + 7]) & (0 - ((r == 0) ? (sp_digit)1 : (sp_digit)0));
        r |= (a[i + 6] - b[i + 6]) & (0 - ((r == 0) ? (sp_digit)1 : (sp_digit)0));
        r |= (a[i + 5] - b[i + 5]) & (0 - ((r == 0) ? (sp_digit)1 : (sp_digit)0));
        r |= (a[i + 4] - b[i + 4]) & (0 - ((r == 0) ? (sp_digit)1 : (sp_digit)0));
        r |= (a[i + 3] - b[i + 3]) & (0 - ((r == 0) ? (sp_digit)1 : (sp_digit)0));
        r |= (a[i + 2] - b[i + 2]) & (0 - ((r == 0) ? (sp_digit)1 : (sp_digit)0));
        r |= (a[i + 1] - b[i + 1]) & (0 - ((r == 0) ? (sp_digit)1 : (sp_digit)0));
        r |= (a[i + 0] - b[i + 0]) & (0 - ((r == 0) ? (sp_digit)1 : (sp_digit)0));
    }
#endif /* WOLFSSL_SP_SMALL */

    return r;
}

/* Conditionally subtract b from a using the mask m.
 * m is -1 to subtract and 0 when not.
 *
 * r  A single precision number representing condition subtract result.
 * a  A single precision number to subtract from.
 * b  A single precision number to subtract.
 * m  Mask value to apply.
 */
static void sp_3072_cond_sub_27(sp_digit* r, const sp_digit* a,
        const sp_digit* b, const sp_digit m)
{
#ifdef WOLFSSL_SP_SMALL
    int i;

    for (i = 0; i < 27; i++) {
        r[i] = a[i] - (b[i] & m);
    }
#else
    int i;

    for (i = 0; i < 24; i += 8) {
        r[i + 0] = a[i + 0] - (b[i + 0] & m);
        r[i + 1] = a[i + 1] - (b[i + 1] & m);
        r[i + 2] = a[i + 2] - (b[i + 2] & m);
        r[i + 3] = a[i + 3] - (b[i + 3] & m);
        r[i + 4] = a[i + 4] - (b[i + 4] & m);
        r[i + 5] = a[i + 5] - (b[i + 5] & m);
        r[i + 6] = a[i + 6] - (b[i + 6] & m);
        r[i + 7] = a[i + 7] - (b[i + 7] & m);
    }
    r[24] = a[24] - (b[24] & m);
    r[25] = a[25] - (b[25] & m);
    r[26] = a[26] - (b[26] & m);
#endif /* WOLFSSL_SP_SMALL */
}

/* Mul a by scalar b and add into r. (r += a * b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A scalar.
 */
SP_NOINLINE static void sp_3072_mul_add_27(sp_digit* r, const sp_digit* a,
        const sp_digit b)
{
#ifdef WOLFSSL_SP_SMALL
    int128_t tb = b;
    int128_t t = 0;
    int i;

    for (i = 0; i < 27; i++) {
        t += (tb * a[i]) + r[i];
        r[i] = t & 0x1ffffffffffffffL;
        t >>= 57;
    }
    r[27] += t;
#else
    int128_t tb = b;
    int128_t t[8];
    int i;

    t[0] = tb * a[0]; r[0] += (sp_digit)(t[0] & 0x1ffffffffffffffL);
    for (i = 0; i < 24; i += 8) {
        t[1] = tb * a[i+1];
        r[i+1] += (sp_digit)((t[0] >> 57) + (t[1] & 0x1ffffffffffffffL));
        t[2] = tb * a[i+2];
        r[i+2] += (sp_digit)((t[1] >> 57) + (t[2] & 0x1ffffffffffffffL));
        t[3] = tb * a[i+3];
        r[i+3] += (sp_digit)((t[2] >> 57) + (t[3] & 0x1ffffffffffffffL));
        t[4] = tb * a[i+4];
        r[i+4] += (sp_digit)((t[3] >> 57) + (t[4] & 0x1ffffffffffffffL));
        t[5] = tb * a[i+5];
        r[i+5] += (sp_digit)((t[4] >> 57) + (t[5] & 0x1ffffffffffffffL));
        t[6] = tb * a[i+6];
        r[i+6] += (sp_digit)((t[5] >> 57) + (t[6] & 0x1ffffffffffffffL));
        t[7] = tb * a[i+7];
        r[i+7] += (sp_digit)((t[6] >> 57) + (t[7] & 0x1ffffffffffffffL));
        t[0] = tb * a[i+8];
        r[i+8] += (sp_digit)((t[7] >> 57) + (t[0] & 0x1ffffffffffffffL));
    }
    t[1] = tb * a[25]; r[25] += (sp_digit)((t[0] >> 57) + (t[1] & 0x1ffffffffffffffL));
    t[2] = tb * a[26]; r[26] += (sp_digit)((t[1] >> 57) + (t[2] & 0x1ffffffffffffffL));
    r[27] +=  (sp_digit)(t[2] >> 57);
#endif /* WOLFSSL_SP_SMALL */
}

/* Normalize the values in each word to 57.
 *
 * a  Array of sp_digit to normalize.
 */
static void sp_3072_norm_27(sp_digit* a)
{
#ifdef WOLFSSL_SP_SMALL
    int i;
    for (i = 0; i < 26; i++) {
        a[i+1] += a[i] >> 57;
        a[i] &= 0x1ffffffffffffffL;
    }
#else
    int i;
    for (i = 0; i < 24; i += 8) {
        a[i+1] += a[i+0] >> 57; a[i+0] &= 0x1ffffffffffffffL;
        a[i+2] += a[i+1] >> 57; a[i+1] &= 0x1ffffffffffffffL;
        a[i+3] += a[i+2] >> 57; a[i+2] &= 0x1ffffffffffffffL;
        a[i+4] += a[i+3] >> 57; a[i+3] &= 0x1ffffffffffffffL;
        a[i+5] += a[i+4] >> 57; a[i+4] &= 0x1ffffffffffffffL;
        a[i+6] += a[i+5] >> 57; a[i+5] &= 0x1ffffffffffffffL;
        a[i+7] += a[i+6] >> 57; a[i+6] &= 0x1ffffffffffffffL;
        a[i+8] += a[i+7] >> 57; a[i+7] &= 0x1ffffffffffffffL;
        a[i+9] += a[i+8] >> 57; a[i+8] &= 0x1ffffffffffffffL;
    }
    a[24+1] += a[24] >> 57;
    a[24] &= 0x1ffffffffffffffL;
    a[25+1] += a[25] >> 57;
    a[25] &= 0x1ffffffffffffffL;
#endif
}

/* Shift the result in the high 1536 bits down to the bottom.
 *
 * r  A single precision number.
 * a  A single precision number.
 */
static void sp_3072_mont_shift_27(sp_digit* r, const sp_digit* a)
{
#ifdef WOLFSSL_SP_SMALL
    int i;
    sp_digit n, s;

    s = a[27];
    n = a[26] >> 54;
    for (i = 0; i < 26; i++) {
        n += (s & 0x1ffffffffffffffL) << 3;
        r[i] = n & 0x1ffffffffffffffL;
        n >>= 57;
        s = a[28 + i] + (s >> 57);
    }
    n += s << 3;
    r[26] = n;
#else
    sp_digit n, s;
    int i;

    s = a[27]; n = a[26] >> 54;
    for (i = 0; i < 24; i += 8) {
        n += (s & 0x1ffffffffffffffL) << 3; r[i+0] = n & 0x1ffffffffffffffL;
        n >>= 57; s = a[i+28] + (s >> 57);
        n += (s & 0x1ffffffffffffffL) << 3; r[i+1] = n & 0x1ffffffffffffffL;
        n >>= 57; s = a[i+29] + (s >> 57);
        n += (s & 0x1ffffffffffffffL) << 3; r[i+2] = n & 0x1ffffffffffffffL;
        n >>= 57; s = a[i+30] + (s >> 57);
        n += (s & 0x1ffffffffffffffL) << 3; r[i+3] = n & 0x1ffffffffffffffL;
        n >>= 57; s = a[i+31] + (s >> 57);
        n += (s & 0x1ffffffffffffffL) << 3; r[i+4] = n & 0x1ffffffffffffffL;
        n >>= 57; s = a[i+32] + (s >> 57);
        n += (s & 0x1ffffffffffffffL) << 3; r[i+5] = n & 0x1ffffffffffffffL;
        n >>= 57; s = a[i+33] + (s >> 57);
        n += (s & 0x1ffffffffffffffL) << 3; r[i+6] = n & 0x1ffffffffffffffL;
        n >>= 57; s = a[i+34] + (s >> 57);
        n += (s & 0x1ffffffffffffffL) << 3; r[i+7] = n & 0x1ffffffffffffffL;
        n >>= 57; s = a[i+35] + (s >> 57);
    }
    n += (s & 0x1ffffffffffffffL) << 3; r[24] = n & 0x1ffffffffffffffL;
    n >>= 57; s = a[52] + (s >> 57);
    n += (s & 0x1ffffffffffffffL) << 3; r[25] = n & 0x1ffffffffffffffL;
    n >>= 57; s = a[53] + (s >> 57);
    n += s << 3;              r[26] = n;
#endif /* WOLFSSL_SP_SMALL */
    XMEMSET(&r[27], 0, sizeof(*r) * 27U);
}

/* Reduce the number back to 3072 bits using Montgomery reduction.
 *
 * a   A single precision number to reduce in place.
 * m   The single precision number representing the modulus.
 * mp  The digit representing the negative inverse of m mod 2^n.
 */
static void sp_3072_mont_reduce_27(sp_digit* a, const sp_digit* m, sp_digit mp)
{
    int i;
    sp_digit mu;

    sp_3072_norm_27(a + 27);

    for (i=0; i<26; i++) {
        mu = (a[i] * mp) & 0x1ffffffffffffffL;
        sp_3072_mul_add_27(a+i, m, mu);
        a[i+1] += a[i] >> 57;
    }
    mu = (a[i] * mp) & 0x3fffffffffffffL;
    sp_3072_mul_add_27(a+i, m, mu);
    a[i+1] += a[i] >> 57;
    a[i] &= 0x1ffffffffffffffL;

    sp_3072_mont_shift_27(a, a);
    sp_3072_cond_sub_27(a, a, m, 0 - (((a[26] >> 54) > 0) ?
            (sp_digit)1 : (sp_digit)0));
    sp_3072_norm_27(a);
}

/* Multiply two Montogmery form numbers mod the modulus (prime).
 * (r = a * b mod m)
 *
 * r   Result of multiplication.
 * a   First number to multiply in Montogmery form.
 * b   Second number to multiply in Montogmery form.
 * m   Modulus (prime).
 * mp  Montogmery mulitplier.
 */
static void sp_3072_mont_mul_27(sp_digit* r, const sp_digit* a, const sp_digit* b,
        const sp_digit* m, sp_digit mp)
{
    sp_3072_mul_27(r, a, b);
    sp_3072_mont_reduce_27(r, m, mp);
}

/* Square the Montgomery form number. (r = a * a mod m)
 *
 * r   Result of squaring.
 * a   Number to square in Montogmery form.
 * m   Modulus (prime).
 * mp  Montogmery mulitplier.
 */
static void sp_3072_mont_sqr_27(sp_digit* r, const sp_digit* a, const sp_digit* m,
        sp_digit mp)
{
    sp_3072_sqr_27(r, a);
    sp_3072_mont_reduce_27(r, m, mp);
}

/* Multiply a by scalar b into r. (r = a * b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A scalar.
 */
SP_NOINLINE static void sp_3072_mul_d_27(sp_digit* r, const sp_digit* a,
    sp_digit b)
{
#ifdef WOLFSSL_SP_SMALL
    int128_t tb = b;
    int128_t t = 0;
    int i;

    for (i = 0; i < 27; i++) {
        t += tb * a[i];
        r[i] = t & 0x1ffffffffffffffL;
        t >>= 57;
    }
    r[27] = (sp_digit)t;
#else
    int128_t tb = b;
    int128_t t[8];
    int i;

    t[0] = tb * a[0]; r[0] = t[0] & 0x1ffffffffffffffL;
    for (i = 0; i < 24; i += 8) {
        t[1] = tb * a[i+1];
        r[i+1] = (sp_digit)(t[0] >> 57) + (t[1] & 0x1ffffffffffffffL);
        t[2] = tb * a[i+2];
        r[i+2] = (sp_digit)(t[1] >> 57) + (t[2] & 0x1ffffffffffffffL);
        t[3] = tb * a[i+3];
        r[i+3] = (sp_digit)(t[2] >> 57) + (t[3] & 0x1ffffffffffffffL);
        t[4] = tb * a[i+4];
        r[i+4] = (sp_digit)(t[3] >> 57) + (t[4] & 0x1ffffffffffffffL);
        t[5] = tb * a[i+5];
        r[i+5] = (sp_digit)(t[4] >> 57) + (t[5] & 0x1ffffffffffffffL);
        t[6] = tb * a[i+6];
        r[i+6] = (sp_digit)(t[5] >> 57) + (t[6] & 0x1ffffffffffffffL);
        t[7] = tb * a[i+7];
        r[i+7] = (sp_digit)(t[6] >> 57) + (t[7] & 0x1ffffffffffffffL);
        t[0] = tb * a[i+8];
        r[i+8] = (sp_digit)(t[7] >> 57) + (t[0] & 0x1ffffffffffffffL);
    }
    t[1] = tb * a[25];
    r[25] = (sp_digit)(t[0] >> 57) + (t[1] & 0x1ffffffffffffffL);
    t[2] = tb * a[26];
    r[26] = (sp_digit)(t[1] >> 57) + (t[2] & 0x1ffffffffffffffL);
    r[27] =  (sp_digit)(t[2] >> 57);
#endif /* WOLFSSL_SP_SMALL */
}

/* Conditionally add a and b using the mask m.
 * m is -1 to add and 0 when not.
 *
 * r  A single precision number representing conditional add result.
 * a  A single precision number to add with.
 * b  A single precision number to add.
 * m  Mask value to apply.
 */
static void sp_3072_cond_add_27(sp_digit* r, const sp_digit* a,
        const sp_digit* b, const sp_digit m)
{
#ifdef WOLFSSL_SP_SMALL
    int i;

    for (i = 0; i < 27; i++) {
        r[i] = a[i] + (b[i] & m);
    }
#else
    int i;

    for (i = 0; i < 24; i += 8) {
        r[i + 0] = a[i + 0] + (b[i + 0] & m);
        r[i + 1] = a[i + 1] + (b[i + 1] & m);
        r[i + 2] = a[i + 2] + (b[i + 2] & m);
        r[i + 3] = a[i + 3] + (b[i + 3] & m);
        r[i + 4] = a[i + 4] + (b[i + 4] & m);
        r[i + 5] = a[i + 5] + (b[i + 5] & m);
        r[i + 6] = a[i + 6] + (b[i + 6] & m);
        r[i + 7] = a[i + 7] + (b[i + 7] & m);
    }
    r[24] = a[24] + (b[24] & m);
    r[25] = a[25] + (b[25] & m);
    r[26] = a[26] + (b[26] & m);
#endif /* WOLFSSL_SP_SMALL */
}

#ifdef WOLFSSL_SP_DIV_64
static WC_INLINE sp_digit sp_3072_div_word_27(sp_digit d1, sp_digit d0,
    sp_digit dv)
{
    sp_digit d, r, t;

    /* All 57 bits from d1 and top 6 bits from d0. */
    d = (d1 << 6) | (d0 >> 51);
    r = d / dv;
    d -= r * dv;
    /* Up to 7 bits in r */
    /* Next 6 bits from d0. */
    r <<= 6;
    d <<= 6;
    d |= (d0 >> 45) & ((1 << 6) - 1);
    t = d / dv;
    d -= t * dv;
    r += t;
    /* Up to 13 bits in r */
    /* Next 6 bits from d0. */
    r <<= 6;
    d <<= 6;
    d |= (d0 >> 39) & ((1 << 6) - 1);
    t = d / dv;
    d -= t * dv;
    r += t;
    /* Up to 19 bits in r */
    /* Next 6 bits from d0. */
    r <<= 6;
    d <<= 6;
    d |= (d0 >> 33) & ((1 << 6) - 1);
    t = d / dv;
    d -= t * dv;
    r += t;
    /* Up to 25 bits in r */
    /* Next 6 bits from d0. */
    r <<= 6;
    d <<= 6;
    d |= (d0 >> 27) & ((1 << 6) - 1);
    t = d / dv;
    d -= t * dv;
    r += t;
    /* Up to 31 bits in r */
    /* Next 6 bits from d0. */
    r <<= 6;
    d <<= 6;
    d |= (d0 >> 21) & ((1 << 6) - 1);
    t = d / dv;
    d -= t * dv;
    r += t;
    /* Up to 37 bits in r */
    /* Next 6 bits from d0. */
    r <<= 6;
    d <<= 6;
    d |= (d0 >> 15) & ((1 << 6) - 1);
    t = d / dv;
    d -= t * dv;
    r += t;
    /* Up to 43 bits in r */
    /* Next 6 bits from d0. */
    r <<= 6;
    d <<= 6;
    d |= (d0 >> 9) & ((1 << 6) - 1);
    t = d / dv;
    d -= t * dv;
    r += t;
    /* Up to 49 bits in r */
    /* Next 6 bits from d0. */
    r <<= 6;
    d <<= 6;
    d |= (d0 >> 3) & ((1 << 6) - 1);
    t = d / dv;
    d -= t * dv;
    r += t;
    /* Up to 55 bits in r */
    /* Remaining 3 bits from d0. */
    r <<= 3;
    d <<= 3;
    d |= d0 & ((1 << 3) - 1);
    t = d / dv;
    r += t;

    return r;
}
#endif /* WOLFSSL_SP_DIV_64 */

/* Divide d in a and put remainder into r (m*d + r = a)
 * m is not calculated as it is not needed at this time.
 *
 * a  Number to be divided.
 * d  Number to divide with.
 * m  Multiplier result.
 * r  Remainder from the division.
 * returns MEMORY_E when unable to allocate memory and MP_OKAY otherwise.
 */
static int sp_3072_div_27(const sp_digit* a, const sp_digit* d, sp_digit* m,
        sp_digit* r)
{
    int i;
#ifndef WOLFSSL_SP_DIV_64
    int128_t d1;
#endif
    sp_digit dv, r1;
#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    sp_digit* td;
#else
    sp_digit t1d[54], t2d[27 + 1];
#endif
    sp_digit* t1;
    sp_digit* t2;
    int err = MP_OKAY;

    (void)m;

#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    td = (sp_digit*)XMALLOC(sizeof(sp_digit) * (3 * 27 + 1), NULL,
                                                       DYNAMIC_TYPE_TMP_BUFFER);
    if (td == NULL) {
        err = MEMORY_E;
    }
#endif

    if (err == MP_OKAY) {
#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
        t1 = td;
        t2 = td + 2 * 27;
#else
        t1 = t1d;
        t2 = t2d;
#endif

        dv = d[26];
        XMEMCPY(t1, a, sizeof(*t1) * 2U * 27U);
        for (i=26; i>=0; i--) {
            t1[27 + i] += t1[27 + i - 1] >> 57;
            t1[27 + i - 1] &= 0x1ffffffffffffffL;
#ifndef WOLFSSL_SP_DIV_64
            d1 = t1[27 + i];
            d1 <<= 57;
            d1 += t1[27 + i - 1];
            r1 = (sp_digit)(d1 / dv);
#else
            r1 = sp_3072_div_word_27(t1[27 + i], t1[27 + i - 1], dv);
#endif

            sp_3072_mul_d_27(t2, d, r1);
            (void)sp_3072_sub_27(&t1[i], &t1[i], t2);
            t1[27 + i] -= t2[27];
            t1[27 + i] += t1[27 + i - 1] >> 57;
            t1[27 + i - 1] &= 0x1ffffffffffffffL;
            r1 = (((-t1[27 + i]) << 57) - t1[27 + i - 1]) / dv;
            r1++;
            sp_3072_mul_d_27(t2, d, r1);
            (void)sp_3072_add_27(&t1[i], &t1[i], t2);
            t1[27 + i] += t1[27 + i - 1] >> 57;
            t1[27 + i - 1] &= 0x1ffffffffffffffL;
        }
        t1[27 - 1] += t1[27 - 2] >> 57;
        t1[27 - 2] &= 0x1ffffffffffffffL;
        r1 = t1[27 - 1] / dv;

        sp_3072_mul_d_27(t2, d, r1);
        (void)sp_3072_sub_27(t1, t1, t2);
        XMEMCPY(r, t1, sizeof(*r) * 2U * 27U);
        for (i=0; i<26; i++) {
            r[i+1] += r[i] >> 57;
            r[i] &= 0x1ffffffffffffffL;
        }
        sp_3072_cond_add_27(r, r, d, 0 - ((r[26] < 0) ?
                    (sp_digit)1 : (sp_digit)0));
    }

#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (td != NULL) {
        XFREE(td, NULL, DYNAMIC_TYPE_TMP_BUFFER);
    }
#endif

    return err;
}

/* Reduce a modulo m into r. (r = a mod m)
 *
 * r  A single precision number that is the reduced result.
 * a  A single precision number that is to be reduced.
 * m  A single precision number that is the modulus to reduce with.
 * returns MEMORY_E when unable to allocate memory and MP_OKAY otherwise.
 */
static int sp_3072_mod_27(sp_digit* r, const sp_digit* a, const sp_digit* m)
{
    return sp_3072_div_27(a, m, NULL, r);
}

/* Modular exponentiate a to the e mod m. (r = a^e mod m)
 *
 * r     A single precision number that is the result of the operation.
 * a     A single precision number being exponentiated.
 * e     A single precision number that is the exponent.
 * bits  The number of bits in the exponent.
 * m     A single precision number that is the modulus.
 * returns 0 on success and MEMORY_E on dynamic memory allocation failure.
 */
static int sp_3072_mod_exp_27(sp_digit* r, const sp_digit* a, const sp_digit* e, int bits,
    const sp_digit* m, int reduceA)
{
#ifdef WOLFSSL_SP_SMALL
#if !defined(WOLFSSL_SP_NO_MALLOC)
    sp_digit* td;
#else
    sp_digit td[3 * 54];
#endif
    sp_digit* t[3];
    sp_digit* norm;
    sp_digit mp = 1;
    sp_digit n;
    int i;
    int c, y;
    int err = MP_OKAY;

#if !defined(WOLFSSL_SP_NO_MALLOC)
    td = (sp_digit*)XMALLOC(sizeof(sp_digit) * 3 * 27 * 2, NULL,
                            DYNAMIC_TYPE_TMP_BUFFER);
    if (td == NULL) {
        err = MEMORY_E;
    }
#endif

    if (err == MP_OKAY) {
        norm = td;
        for (i=0; i<3; i++) {
#if !defined(WOLFSSL_SP_NO_MALLOC)
            t[i] = td + (i * 27 * 2);
#else
            t[i] = &td[i * 27 * 2];
#endif
            XMEMSET(t[i], 0, sizeof(sp_digit) * 27U * 2U);
        }

        sp_3072_mont_setup(m, &mp);
        sp_3072_mont_norm_27(norm, m);

        if (reduceA != 0) {
            err = sp_3072_mod_27(t[1], a, m);
        }
        else {
            XMEMCPY(t[1], a, sizeof(sp_digit) * 27U);
        }
    }
    if (err == MP_OKAY) {
        sp_3072_mul_27(t[1], t[1], norm);
        err = sp_3072_mod_27(t[1], t[1], m);
    }

    if (err == MP_OKAY) {
        i = bits / 57;
        c = bits % 57;
        n = e[i--] << (57 - c);
        for (; ; c--) {
            if (c == 0) {
                if (i == -1) {
                    break;
                }

                n = e[i--];
                c = 57;
            }

            y = (n >> 56) & 1;
            n <<= 1;

            sp_3072_mont_mul_27(t[y^1], t[0], t[1], m, mp);

            XMEMCPY(t[2], (void*)(((size_t)t[0] & addr_mask[y^1]) +
                                  ((size_t)t[1] & addr_mask[y])),
                                  sizeof(*t[2]) * 27 * 2);
            sp_3072_mont_sqr_27(t[2], t[2], m, mp);
            XMEMCPY((void*)(((size_t)t[0] & addr_mask[y^1]) +
                            ((size_t)t[1] & addr_mask[y])), t[2],
                            sizeof(*t[2]) * 27 * 2);
        }

        sp_3072_mont_reduce_27(t[0], m, mp);
        n = sp_3072_cmp_27(t[0], m);
        sp_3072_cond_sub_27(t[0], t[0], m, ((n < 0) ?
                    (sp_digit)1 : (sp_digit)0) - 1);
        XMEMCPY(r, t[0], sizeof(*r) * 27 * 2);

    }

#if !defined(WOLFSSL_SP_NO_MALLOC)
    if (td != NULL) {
        XFREE(td, NULL, DYNAMIC_TYPE_TMP_BUFFER);
    }
#endif

    return err;
#elif !defined(WC_NO_CACHE_RESISTANT)
#if defined(WOLFSSL_SMALL_STACK) && !defined(WOLFSSL_SP_NO_MALLOC)
    sp_digit* td;
#else
    sp_digit td[3 * 54];
#endif
    sp_digit* t[3];
    sp_digit* norm;
    sp_digit mp = 1;
    sp_digit n;
    int i;
    int c, y;
    int err = MP_OKAY;

#ifdef WOLFSSL_SMALL_STACK
    td = (sp_digit*)XMALLOC(sizeof(sp_digit) * 3 * 27 * 2, NULL,
                            DYNAMIC_TYPE_TMP_BUFFER);
    if (td == NULL) {
        err = MEMORY_E;
    }
#endif

    if (err == MP_OKAY) {
        norm = td;
        for (i=0; i<3; i++) {
#if defined(WOLFSSL_SMALL_STACK) && !defined(WOLFSSL_SP_NO_MALLOC)
            t[i] = td + (i * 27 * 2);
#else
            t[i] = &td[i * 27 * 2];
#endif
        }

        sp_3072_mont_setup(m, &mp);
        sp_3072_mont_norm_27(norm, m);

        if (reduceA != 0) {
            err = sp_3072_mod_27(t[1], a, m);
            if (err == MP_OKAY) {
                sp_3072_mul_27(t[1], t[1], norm);
                err = sp_3072_mod_27(t[1], t[1], m);
            }
        }
        else {
            sp_3072_mul_27(t[1], a, norm);
            err = sp_3072_mod_27(t[1], t[1], m);
        }
    }

    if (err == MP_OKAY) {
        i = bits / 57;
        c = bits % 57;
        n = e[i--] << (57 - c);
        for (; ; c--) {
            if (c == 0) {
                if (i == -1) {
                    break;
                }

                n = e[i--];
                c = 57;
            }

            y = (n >> 56) & 1;
            n <<= 1;

            sp_3072_mont_mul_27(t[y^1], t[0], t[1], m, mp);

            XMEMCPY(t[2], (void*)(((size_t)t[0] & addr_mask[y^1]) +
                                  ((size_t)t[1] & addr_mask[y])), 
                                  sizeof(*t[2]) * 27 * 2);
            sp_3072_mont_sqr_27(t[2], t[2], m, mp);
            XMEMCPY((void*)(((size_t)t[0] & addr_mask[y^1]) +
                            ((size_t)t[1] & addr_mask[y])), t[2], 
                            sizeof(*t[2]) * 27 * 2);
        }

        sp_3072_mont_reduce_27(t[0], m, mp);
        n = sp_3072_cmp_27(t[0], m);
        sp_3072_cond_sub_27(t[0], t[0], m, ((n < 0) ?
                    (sp_digit)1 : (sp_digit)0) - 1);
        XMEMCPY(r, t[0], sizeof(*r) * 27 * 2);
    }

#ifdef WOLFSSL_SMALL_STACK
    if (td != NULL) {
        XFREE(td, NULL, DYNAMIC_TYPE_TMP_BUFFER);
    }
#endif

    return err;
#else
#if defined(WOLFSSL_SMALL_STACK) && !defined(WOLFSSL_SP_NO_MALLOC)
    sp_digit* td;
#else
    sp_digit td[(32 * 54) + 54];
#endif
    sp_digit* t[32];
    sp_digit* rt;
    sp_digit* norm;
    sp_digit mp = 1;
    sp_digit n;
    int i;
    int c, y;
    int err = MP_OKAY;

#if defined(WOLFSSL_SMALL_STACK) && !defined(WOLFSSL_SP_NO_MALLOC)
    td = (sp_digit*)XMALLOC(sizeof(sp_digit) * ((32 * 54) + 54), NULL,
                            DYNAMIC_TYPE_TMP_BUFFER);
    if (td == NULL) {
        err = MEMORY_E;
    }
#endif

    if (err == MP_OKAY) {
        norm = td;
#if defined(WOLFSSL_SMALL_STACK) && !defined(WOLFSSL_SP_NO_MALLOC)
        for (i=0; i<32; i++)
            t[i] = td + i * 54;
        rt = td + 1728;
#else
        for (i=0; i<32; i++)
            t[i] = &td[i * 54];
        rt = &td[1728];
#endif

        sp_3072_mont_setup(m, &mp);
        sp_3072_mont_norm_27(norm, m);

        if (reduceA != 0) {
            err = sp_3072_mod_27(t[1], a, m);
            if (err == MP_OKAY) {
                sp_3072_mul_27(t[1], t[1], norm);
                err = sp_3072_mod_27(t[1], t[1], m);
            }
        }
        else {
            sp_3072_mul_27(t[1], a, norm);
            err = sp_3072_mod_27(t[1], t[1], m);
        }
    }

    if (err == MP_OKAY) {
        sp_3072_mont_sqr_27(t[ 2], t[ 1], m, mp);
        sp_3072_mont_mul_27(t[ 3], t[ 2], t[ 1], m, mp);
        sp_3072_mont_sqr_27(t[ 4], t[ 2], m, mp);
        sp_3072_mont_mul_27(t[ 5], t[ 3], t[ 2], m, mp);
        sp_3072_mont_sqr_27(t[ 6], t[ 3], m, mp);
        sp_3072_mont_mul_27(t[ 7], t[ 4], t[ 3], m, mp);
        sp_3072_mont_sqr_27(t[ 8], t[ 4], m, mp);
        sp_3072_mont_mul_27(t[ 9], t[ 5], t[ 4], m, mp);
        sp_3072_mont_sqr_27(t[10], t[ 5], m, mp);
        sp_3072_mont_mul_27(t[11], t[ 6], t[ 5], m, mp);
        sp_3072_mont_sqr_27(t[12], t[ 6], m, mp);
        sp_3072_mont_mul_27(t[13], t[ 7], t[ 6], m, mp);
        sp_3072_mont_sqr_27(t[14], t[ 7], m, mp);
        sp_3072_mont_mul_27(t[15], t[ 8], t[ 7], m, mp);
        sp_3072_mont_sqr_27(t[16], t[ 8], m, mp);
        sp_3072_mont_mul_27(t[17], t[ 9], t[ 8], m, mp);
        sp_3072_mont_sqr_27(t[18], t[ 9], m, mp);
        sp_3072_mont_mul_27(t[19], t[10], t[ 9], m, mp);
        sp_3072_mont_sqr_27(t[20], t[10], m, mp);
        sp_3072_mont_mul_27(t[21], t[11], t[10], m, mp);
        sp_3072_mont_sqr_27(t[22], t[11], m, mp);
        sp_3072_mont_mul_27(t[23], t[12], t[11], m, mp);
        sp_3072_mont_sqr_27(t[24], t[12], m, mp);
        sp_3072_mont_mul_27(t[25], t[13], t[12], m, mp);
        sp_3072_mont_sqr_27(t[26], t[13], m, mp);
        sp_3072_mont_mul_27(t[27], t[14], t[13], m, mp);
        sp_3072_mont_sqr_27(t[28], t[14], m, mp);
        sp_3072_mont_mul_27(t[29], t[15], t[14], m, mp);
        sp_3072_mont_sqr_27(t[30], t[15], m, mp);
        sp_3072_mont_mul_27(t[31], t[16], t[15], m, mp);

        bits = ((bits + 4) / 5) * 5;
        i = ((bits + 56) / 57) - 1;
        c = bits % 57;
        if (c == 0) {
            c = 57;
        }
        if (i < 27) {
            n = e[i--] << (64 - c);
        }
        else {
            n = 0;
            i--;
        }
        if (c < 5) {
            n |= e[i--] << (7 - c);
            c += 57;
        }
        y = (n >> 59) & 0x1f;
        n <<= 5;
        c -= 5;
        XMEMCPY(rt, t[y], sizeof(sp_digit) * 54);
        for (; i>=0 || c>=5; ) {
            if (c < 5) {
                n |= e[i--] << (7 - c);
                c += 57;
            }
            y = (n >> 59) & 0x1f;
            n <<= 5;
            c -= 5;

            sp_3072_mont_sqr_27(rt, rt, m, mp);
            sp_3072_mont_sqr_27(rt, rt, m, mp);
            sp_3072_mont_sqr_27(rt, rt, m, mp);
            sp_3072_mont_sqr_27(rt, rt, m, mp);
            sp_3072_mont_sqr_27(rt, rt, m, mp);

            sp_3072_mont_mul_27(rt, rt, t[y], m, mp);
        }

        sp_3072_mont_reduce_27(rt, m, mp);
        n = sp_3072_cmp_27(rt, m);
        sp_3072_cond_sub_27(rt, rt, m, ((n < 0) ?
                   (sp_digit)1 : (sp_digit)0) - 1);
        XMEMCPY(r, rt, sizeof(sp_digit) * 54);
    }

#if defined(WOLFSSL_SMALL_STACK) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (td != NULL) {
        XFREE(td, NULL, DYNAMIC_TYPE_TMP_BUFFER);
    }
#endif

    return err;
#endif
}

#endif /* (WOLFSSL_HAVE_SP_RSA || WOLFSSL_HAVE_SP_DH) && !WOLFSSL_RSA_PUBLIC_ONLY */

/* r = 2^n mod m where n is the number of bits to reduce by.
 * Given m must be 3072 bits, just need to subtract.
 *
 * r  A single precision number.
 * m  A single precision number.
 */
static void sp_3072_mont_norm_54(sp_digit* r, const sp_digit* m)
{
    /* Set r = 2^n - 1. */
#ifdef WOLFSSL_SP_SMALL
    int i;

    for (i=0; i<53; i++) {
        r[i] = 0x1ffffffffffffffL;
    }
#else
    int i;

    for (i = 0; i < 48; i += 8) {
        r[i + 0] = 0x1ffffffffffffffL;
        r[i + 1] = 0x1ffffffffffffffL;
        r[i + 2] = 0x1ffffffffffffffL;
        r[i + 3] = 0x1ffffffffffffffL;
        r[i + 4] = 0x1ffffffffffffffL;
        r[i + 5] = 0x1ffffffffffffffL;
        r[i + 6] = 0x1ffffffffffffffL;
        r[i + 7] = 0x1ffffffffffffffL;
    }
    r[48] = 0x1ffffffffffffffL;
    r[49] = 0x1ffffffffffffffL;
    r[50] = 0x1ffffffffffffffL;
    r[51] = 0x1ffffffffffffffL;
    r[52] = 0x1ffffffffffffffL;
#endif
    r[53] = 0x7ffffffffffffL;

    /* r = (2^n - 1) mod n */
    (void)sp_3072_sub_54(r, r, m);

    /* Add one so r = 2^n mod m */
    r[0] += 1;
}

/* Compare a with b in constant time.
 *
 * a  A single precision integer.
 * b  A single precision integer.
 * return -ve, 0 or +ve if a is less than, equal to or greater than b
 * respectively.
 */
static sp_digit sp_3072_cmp_54(const sp_digit* a, const sp_digit* b)
{
    sp_digit r = 0;
#ifdef WOLFSSL_SP_SMALL
    int i;

    for (i=53; i>=0; i--) {
        r |= (a[i] - b[i]) & (0 - ((r == 0) ? (sp_digit)1 : (sp_digit)0));
    }
#else
    int i;

    r |= (a[53] - b[53]) & (0 - ((r == 0) ? (sp_digit)1 : (sp_digit)0));
    r |= (a[52] - b[52]) & (0 - ((r == 0) ? (sp_digit)1 : (sp_digit)0));
    r |= (a[51] - b[51]) & (0 - ((r == 0) ? (sp_digit)1 : (sp_digit)0));
    r |= (a[50] - b[50]) & (0 - ((r == 0) ? (sp_digit)1 : (sp_digit)0));
    r |= (a[49] - b[49]) & (0 - ((r == 0) ? (sp_digit)1 : (sp_digit)0));
    r |= (a[48] - b[48]) & (0 - ((r == 0) ? (sp_digit)1 : (sp_digit)0));
    for (i = 40; i >= 0; i -= 8) {
        r |= (a[i + 7] - b[i + 7]) & (0 - ((r == 0) ? (sp_digit)1 : (sp_digit)0));
        r |= (a[i + 6] - b[i + 6]) & (0 - ((r == 0) ? (sp_digit)1 : (sp_digit)0));
        r |= (a[i + 5] - b[i + 5]) & (0 - ((r == 0) ? (sp_digit)1 : (sp_digit)0));
        r |= (a[i + 4] - b[i + 4]) & (0 - ((r == 0) ? (sp_digit)1 : (sp_digit)0));
        r |= (a[i + 3] - b[i + 3]) & (0 - ((r == 0) ? (sp_digit)1 : (sp_digit)0));
        r |= (a[i + 2] - b[i + 2]) & (0 - ((r == 0) ? (sp_digit)1 : (sp_digit)0));
        r |= (a[i + 1] - b[i + 1]) & (0 - ((r == 0) ? (sp_digit)1 : (sp_digit)0));
        r |= (a[i + 0] - b[i + 0]) & (0 - ((r == 0) ? (sp_digit)1 : (sp_digit)0));
    }
#endif /* WOLFSSL_SP_SMALL */

    return r;
}

/* Conditionally subtract b from a using the mask m.
 * m is -1 to subtract and 0 when not.
 *
 * r  A single precision number representing condition subtract result.
 * a  A single precision number to subtract from.
 * b  A single precision number to subtract.
 * m  Mask value to apply.
 */
static void sp_3072_cond_sub_54(sp_digit* r, const sp_digit* a,
        const sp_digit* b, const sp_digit m)
{
#ifdef WOLFSSL_SP_SMALL
    int i;

    for (i = 0; i < 54; i++) {
        r[i] = a[i] - (b[i] & m);
    }
#else
    int i;

    for (i = 0; i < 48; i += 8) {
        r[i + 0] = a[i + 0] - (b[i + 0] & m);
        r[i + 1] = a[i + 1] - (b[i + 1] & m);
        r[i + 2] = a[i + 2] - (b[i + 2] & m);
        r[i + 3] = a[i + 3] - (b[i + 3] & m);
        r[i + 4] = a[i + 4] - (b[i + 4] & m);
        r[i + 5] = a[i + 5] - (b[i + 5] & m);
        r[i + 6] = a[i + 6] - (b[i + 6] & m);
        r[i + 7] = a[i + 7] - (b[i + 7] & m);
    }
    r[48] = a[48] - (b[48] & m);
    r[49] = a[49] - (b[49] & m);
    r[50] = a[50] - (b[50] & m);
    r[51] = a[51] - (b[51] & m);
    r[52] = a[52] - (b[52] & m);
    r[53] = a[53] - (b[53] & m);
#endif /* WOLFSSL_SP_SMALL */
}

/* Mul a by scalar b and add into r. (r += a * b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A scalar.
 */
SP_NOINLINE static void sp_3072_mul_add_54(sp_digit* r, const sp_digit* a,
        const sp_digit b)
{
#ifdef WOLFSSL_SP_SMALL
    int128_t tb = b;
    int128_t t = 0;
    int i;

    for (i = 0; i < 54; i++) {
        t += (tb * a[i]) + r[i];
        r[i] = t & 0x1ffffffffffffffL;
        t >>= 57;
    }
    r[54] += t;
#else
    int128_t tb = b;
    int128_t t[8];
    int i;

    t[0] = tb * a[0]; r[0] += (sp_digit)(t[0] & 0x1ffffffffffffffL);
    for (i = 0; i < 48; i += 8) {
        t[1] = tb * a[i+1];
        r[i+1] += (sp_digit)((t[0] >> 57) + (t[1] & 0x1ffffffffffffffL));
        t[2] = tb * a[i+2];
        r[i+2] += (sp_digit)((t[1] >> 57) + (t[2] & 0x1ffffffffffffffL));
        t[3] = tb * a[i+3];
        r[i+3] += (sp_digit)((t[2] >> 57) + (t[3] & 0x1ffffffffffffffL));
        t[4] = tb * a[i+4];
        r[i+4] += (sp_digit)((t[3] >> 57) + (t[4] & 0x1ffffffffffffffL));
        t[5] = tb * a[i+5];
        r[i+5] += (sp_digit)((t[4] >> 57) + (t[5] & 0x1ffffffffffffffL));
        t[6] = tb * a[i+6];
        r[i+6] += (sp_digit)((t[5] >> 57) + (t[6] & 0x1ffffffffffffffL));
        t[7] = tb * a[i+7];
        r[i+7] += (sp_digit)((t[6] >> 57) + (t[7] & 0x1ffffffffffffffL));
        t[0] = tb * a[i+8];
        r[i+8] += (sp_digit)((t[7] >> 57) + (t[0] & 0x1ffffffffffffffL));
    }
    t[1] = tb * a[49]; r[49] += (sp_digit)((t[0] >> 57) + (t[1] & 0x1ffffffffffffffL));
    t[2] = tb * a[50]; r[50] += (sp_digit)((t[1] >> 57) + (t[2] & 0x1ffffffffffffffL));
    t[3] = tb * a[51]; r[51] += (sp_digit)((t[2] >> 57) + (t[3] & 0x1ffffffffffffffL));
    t[4] = tb * a[52]; r[52] += (sp_digit)((t[3] >> 57) + (t[4] & 0x1ffffffffffffffL));
    t[5] = tb * a[53]; r[53] += (sp_digit)((t[4] >> 57) + (t[5] & 0x1ffffffffffffffL));
    r[54] +=  (sp_digit)(t[5] >> 57);
#endif /* WOLFSSL_SP_SMALL */
}

/* Normalize the values in each word to 57.
 *
 * a  Array of sp_digit to normalize.
 */
static void sp_3072_norm_54(sp_digit* a)
{
#ifdef WOLFSSL_SP_SMALL
    int i;
    for (i = 0; i < 53; i++) {
        a[i+1] += a[i] >> 57;
        a[i] &= 0x1ffffffffffffffL;
    }
#else
    int i;
    for (i = 0; i < 48; i += 8) {
        a[i+1] += a[i+0] >> 57; a[i+0] &= 0x1ffffffffffffffL;
        a[i+2] += a[i+1] >> 57; a[i+1] &= 0x1ffffffffffffffL;
        a[i+3] += a[i+2] >> 57; a[i+2] &= 0x1ffffffffffffffL;
        a[i+4] += a[i+3] >> 57; a[i+3] &= 0x1ffffffffffffffL;
        a[i+5] += a[i+4] >> 57; a[i+4] &= 0x1ffffffffffffffL;
        a[i+6] += a[i+5] >> 57; a[i+5] &= 0x1ffffffffffffffL;
        a[i+7] += a[i+6] >> 57; a[i+6] &= 0x1ffffffffffffffL;
        a[i+8] += a[i+7] >> 57; a[i+7] &= 0x1ffffffffffffffL;
        a[i+9] += a[i+8] >> 57; a[i+8] &= 0x1ffffffffffffffL;
    }
    a[48+1] += a[48] >> 57;
    a[48] &= 0x1ffffffffffffffL;
    a[49+1] += a[49] >> 57;
    a[49] &= 0x1ffffffffffffffL;
    a[50+1] += a[50] >> 57;
    a[50] &= 0x1ffffffffffffffL;
    a[51+1] += a[51] >> 57;
    a[51] &= 0x1ffffffffffffffL;
    a[52+1] += a[52] >> 57;
    a[52] &= 0x1ffffffffffffffL;
#endif
}

/* Shift the result in the high 3072 bits down to the bottom.
 *
 * r  A single precision number.
 * a  A single precision number.
 */
static void sp_3072_mont_shift_54(sp_digit* r, const sp_digit* a)
{
#ifdef WOLFSSL_SP_SMALL
    int i;
    int128_t n = a[53] >> 51;
    n += ((int128_t)a[54]) << 6;

    for (i = 0; i < 53; i++) {
        r[i] = n & 0x1ffffffffffffffL;
        n >>= 57;
        n += ((int128_t)a[55 + i]) << 6;
    }
    r[53] = (sp_digit)n;
#else
    int i;
    int128_t n = a[53] >> 51;
    n += ((int128_t)a[54]) << 6;
    for (i = 0; i < 48; i += 8) {
        r[i + 0] = n & 0x1ffffffffffffffL;
        n >>= 57; n += ((int128_t)a[i + 55]) << 6;
        r[i + 1] = n & 0x1ffffffffffffffL;
        n >>= 57; n += ((int128_t)a[i + 56]) << 6;
        r[i + 2] = n & 0x1ffffffffffffffL;
        n >>= 57; n += ((int128_t)a[i + 57]) << 6;
        r[i + 3] = n & 0x1ffffffffffffffL;
        n >>= 57; n += ((int128_t)a[i + 58]) << 6;
        r[i + 4] = n & 0x1ffffffffffffffL;
        n >>= 57; n += ((int128_t)a[i + 59]) << 6;
        r[i + 5] = n & 0x1ffffffffffffffL;
        n >>= 57; n += ((int128_t)a[i + 60]) << 6;
        r[i + 6] = n & 0x1ffffffffffffffL;
        n >>= 57; n += ((int128_t)a[i + 61]) << 6;
        r[i + 7] = n & 0x1ffffffffffffffL;
        n >>= 57; n += ((int128_t)a[i + 62]) << 6;
    }
    r[48] = n & 0x1ffffffffffffffL; n >>= 57; n += ((int128_t)a[103]) << 6;
    r[49] = n & 0x1ffffffffffffffL; n >>= 57; n += ((int128_t)a[104]) << 6;
    r[50] = n & 0x1ffffffffffffffL; n >>= 57; n += ((int128_t)a[105]) << 6;
    r[51] = n & 0x1ffffffffffffffL; n >>= 57; n += ((int128_t)a[106]) << 6;
    r[52] = n & 0x1ffffffffffffffL; n >>= 57; n += ((int128_t)a[107]) << 6;
    r[53] = (sp_digit)n;
#endif /* WOLFSSL_SP_SMALL */
    XMEMSET(&r[54], 0, sizeof(*r) * 54U);
}

/* Reduce the number back to 3072 bits using Montgomery reduction.
 *
 * a   A single precision number to reduce in place.
 * m   The single precision number representing the modulus.
 * mp  The digit representing the negative inverse of m mod 2^n.
 */
static void sp_3072_mont_reduce_54(sp_digit* a, const sp_digit* m, sp_digit mp)
{
    int i;
    sp_digit mu;

    sp_3072_norm_54(a + 54);

#ifdef WOLFSSL_SP_DH
    if (mp != 1) {
        for (i=0; i<53; i++) {
            mu = (a[i] * mp) & 0x1ffffffffffffffL;
            sp_3072_mul_add_54(a+i, m, mu);
            a[i+1] += a[i] >> 57;
        }
        mu = (a[i] * mp) & 0x7ffffffffffffL;
        sp_3072_mul_add_54(a+i, m, mu);
        a[i+1] += a[i] >> 57;
        a[i] &= 0x1ffffffffffffffL;
    }
    else {
        for (i=0; i<53; i++) {
            mu = a[i] & 0x1ffffffffffffffL;
            sp_3072_mul_add_54(a+i, m, mu);
            a[i+1] += a[i] >> 57;
        }
        mu = a[i] & 0x7ffffffffffffL;
        sp_3072_mul_add_54(a+i, m, mu);
        a[i+1] += a[i] >> 57;
        a[i] &= 0x1ffffffffffffffL;
    }
#else
    for (i=0; i<53; i++) {
        mu = (a[i] * mp) & 0x1ffffffffffffffL;
        sp_3072_mul_add_54(a+i, m, mu);
        a[i+1] += a[i] >> 57;
    }
    mu = (a[i] * mp) & 0x7ffffffffffffL;
    sp_3072_mul_add_54(a+i, m, mu);
    a[i+1] += a[i] >> 57;
    a[i] &= 0x1ffffffffffffffL;
#endif

    sp_3072_mont_shift_54(a, a);
    sp_3072_cond_sub_54(a, a, m, 0 - (((a[53] >> 51) > 0) ?
            (sp_digit)1 : (sp_digit)0));
    sp_3072_norm_54(a);
}

/* Multiply two Montogmery form numbers mod the modulus (prime).
 * (r = a * b mod m)
 *
 * r   Result of multiplication.
 * a   First number to multiply in Montogmery form.
 * b   Second number to multiply in Montogmery form.
 * m   Modulus (prime).
 * mp  Montogmery mulitplier.
 */
static void sp_3072_mont_mul_54(sp_digit* r, const sp_digit* a, const sp_digit* b,
        const sp_digit* m, sp_digit mp)
{
    sp_3072_mul_54(r, a, b);
    sp_3072_mont_reduce_54(r, m, mp);
}

/* Square the Montgomery form number. (r = a * a mod m)
 *
 * r   Result of squaring.
 * a   Number to square in Montogmery form.
 * m   Modulus (prime).
 * mp  Montogmery mulitplier.
 */
static void sp_3072_mont_sqr_54(sp_digit* r, const sp_digit* a, const sp_digit* m,
        sp_digit mp)
{
    sp_3072_sqr_54(r, a);
    sp_3072_mont_reduce_54(r, m, mp);
}

/* Conditionally add a and b using the mask m.
 * m is -1 to add and 0 when not.
 *
 * r  A single precision number representing conditional add result.
 * a  A single precision number to add with.
 * b  A single precision number to add.
 * m  Mask value to apply.
 */
static void sp_3072_cond_add_54(sp_digit* r, const sp_digit* a,
        const sp_digit* b, const sp_digit m)
{
#ifdef WOLFSSL_SP_SMALL
    int i;

    for (i = 0; i < 54; i++) {
        r[i] = a[i] + (b[i] & m);
    }
#else
    int i;

    for (i = 0; i < 48; i += 8) {
        r[i + 0] = a[i + 0] + (b[i + 0] & m);
        r[i + 1] = a[i + 1] + (b[i + 1] & m);
        r[i + 2] = a[i + 2] + (b[i + 2] & m);
        r[i + 3] = a[i + 3] + (b[i + 3] & m);
        r[i + 4] = a[i + 4] + (b[i + 4] & m);
        r[i + 5] = a[i + 5] + (b[i + 5] & m);
        r[i + 6] = a[i + 6] + (b[i + 6] & m);
        r[i + 7] = a[i + 7] + (b[i + 7] & m);
    }
    r[48] = a[48] + (b[48] & m);
    r[49] = a[49] + (b[49] & m);
    r[50] = a[50] + (b[50] & m);
    r[51] = a[51] + (b[51] & m);
    r[52] = a[52] + (b[52] & m);
    r[53] = a[53] + (b[53] & m);
#endif /* WOLFSSL_SP_SMALL */
}

#ifdef WOLFSSL_SP_DIV_64
static WC_INLINE sp_digit sp_3072_div_word_54(sp_digit d1, sp_digit d0,
    sp_digit dv)
{
    sp_digit d, r, t;

    /* All 57 bits from d1 and top 6 bits from d0. */
    d = (d1 << 6) | (d0 >> 51);
    r = d / dv;
    d -= r * dv;
    /* Up to 7 bits in r */
    /* Next 6 bits from d0. */
    r <<= 6;
    d <<= 6;
    d |= (d0 >> 45) & ((1 << 6) - 1);
    t = d / dv;
    d -= t * dv;
    r += t;
    /* Up to 13 bits in r */
    /* Next 6 bits from d0. */
    r <<= 6;
    d <<= 6;
    d |= (d0 >> 39) & ((1 << 6) - 1);
    t = d / dv;
    d -= t * dv;
    r += t;
    /* Up to 19 bits in r */
    /* Next 6 bits from d0. */
    r <<= 6;
    d <<= 6;
    d |= (d0 >> 33) & ((1 << 6) - 1);
    t = d / dv;
    d -= t * dv;
    r += t;
    /* Up to 25 bits in r */
    /* Next 6 bits from d0. */
    r <<= 6;
    d <<= 6;
    d |= (d0 >> 27) & ((1 << 6) - 1);
    t = d / dv;
    d -= t * dv;
    r += t;
    /* Up to 31 bits in r */
    /* Next 6 bits from d0. */
    r <<= 6;
    d <<= 6;
    d |= (d0 >> 21) & ((1 << 6) - 1);
    t = d / dv;
    d -= t * dv;
    r += t;
    /* Up to 37 bits in r */
    /* Next 6 bits from d0. */
    r <<= 6;
    d <<= 6;
    d |= (d0 >> 15) & ((1 << 6) - 1);
    t = d / dv;
    d -= t * dv;
    r += t;
    /* Up to 43 bits in r */
    /* Next 6 bits from d0. */
    r <<= 6;
    d <<= 6;
    d |= (d0 >> 9) & ((1 << 6) - 1);
    t = d / dv;
    d -= t * dv;
    r += t;
    /* Up to 49 bits in r */
    /* Next 6 bits from d0. */
    r <<= 6;
    d <<= 6;
    d |= (d0 >> 3) & ((1 << 6) - 1);
    t = d / dv;
    d -= t * dv;
    r += t;
    /* Up to 55 bits in r */
    /* Remaining 3 bits from d0. */
    r <<= 3;
    d <<= 3;
    d |= d0 & ((1 << 3) - 1);
    t = d / dv;
    r += t;

    return r;
}
#endif /* WOLFSSL_SP_DIV_64 */

/* Divide d in a and put remainder into r (m*d + r = a)
 * m is not calculated as it is not needed at this time.
 *
 * a  Number to be divided.
 * d  Number to divide with.
 * m  Multiplier result.
 * r  Remainder from the division.
 * returns MEMORY_E when unable to allocate memory and MP_OKAY otherwise.
 */
static int sp_3072_div_54(const sp_digit* a, const sp_digit* d, sp_digit* m,
        sp_digit* r)
{
    int i;
#ifndef WOLFSSL_SP_DIV_64
    int128_t d1;
#endif
    sp_digit dv, r1;
#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    sp_digit* td;
#else
    sp_digit t1d[108], t2d[54 + 1];
#endif
    sp_digit* t1;
    sp_digit* t2;
    int err = MP_OKAY;

    (void)m;

#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    td = (sp_digit*)XMALLOC(sizeof(sp_digit) * (3 * 54 + 1), NULL,
                                                       DYNAMIC_TYPE_TMP_BUFFER);
    if (td == NULL) {
        err = MEMORY_E;
    }
#endif

    if (err == MP_OKAY) {
#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
        t1 = td;
        t2 = td + 2 * 54;
#else
        t1 = t1d;
        t2 = t2d;
#endif

        dv = d[53];
        XMEMCPY(t1, a, sizeof(*t1) * 2U * 54U);
        for (i=53; i>=0; i--) {
            t1[54 + i] += t1[54 + i - 1] >> 57;
            t1[54 + i - 1] &= 0x1ffffffffffffffL;
#ifndef WOLFSSL_SP_DIV_64
            d1 = t1[54 + i];
            d1 <<= 57;
            d1 += t1[54 + i - 1];
            r1 = (sp_digit)(d1 / dv);
#else
            r1 = sp_3072_div_word_54(t1[54 + i], t1[54 + i - 1], dv);
#endif

            sp_3072_mul_d_54(t2, d, r1);
            (void)sp_3072_sub_54(&t1[i], &t1[i], t2);
            t1[54 + i] -= t2[54];
            t1[54 + i] += t1[54 + i - 1] >> 57;
            t1[54 + i - 1] &= 0x1ffffffffffffffL;
            r1 = (((-t1[54 + i]) << 57) - t1[54 + i - 1]) / dv;
            r1++;
            sp_3072_mul_d_54(t2, d, r1);
            (void)sp_3072_add_54(&t1[i], &t1[i], t2);
            t1[54 + i] += t1[54 + i - 1] >> 57;
            t1[54 + i - 1] &= 0x1ffffffffffffffL;
        }
        t1[54 - 1] += t1[54 - 2] >> 57;
        t1[54 - 2] &= 0x1ffffffffffffffL;
        r1 = t1[54 - 1] / dv;

        sp_3072_mul_d_54(t2, d, r1);
        (void)sp_3072_sub_54(t1, t1, t2);
        XMEMCPY(r, t1, sizeof(*r) * 2U * 54U);
        for (i=0; i<53; i++) {
            r[i+1] += r[i] >> 57;
            r[i] &= 0x1ffffffffffffffL;
        }
        sp_3072_cond_add_54(r, r, d, 0 - ((r[53] < 0) ?
                    (sp_digit)1 : (sp_digit)0));
    }

#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (td != NULL) {
        XFREE(td, NULL, DYNAMIC_TYPE_TMP_BUFFER);
    }
#endif

    return err;
}

/* Reduce a modulo m into r. (r = a mod m)
 *
 * r  A single precision number that is the reduced result.
 * a  A single precision number that is to be reduced.
 * m  A single precision number that is the modulus to reduce with.
 * returns MEMORY_E when unable to allocate memory and MP_OKAY otherwise.
 */
static int sp_3072_mod_54(sp_digit* r, const sp_digit* a, const sp_digit* m)
{
    return sp_3072_div_54(a, m, NULL, r);
}

#if (defined(WOLFSSL_HAVE_SP_RSA) && !defined(WOLFSSL_RSA_PUBLIC_ONLY)) || \
                                                     defined(WOLFSSL_HAVE_SP_DH)
/* Modular exponentiate a to the e mod m. (r = a^e mod m)
 *
 * r     A single precision number that is the result of the operation.
 * a     A single precision number being exponentiated.
 * e     A single precision number that is the exponent.
 * bits  The number of bits in the exponent.
 * m     A single precision number that is the modulus.
 * returns 0 on success and MEMORY_E on dynamic memory allocation failure.
 */
static int sp_3072_mod_exp_54(sp_digit* r, const sp_digit* a, const sp_digit* e, int bits,
    const sp_digit* m, int reduceA)
{
#ifdef WOLFSSL_SP_SMALL
#if !defined(WOLFSSL_SP_NO_MALLOC)
    sp_digit* td;
#else
    sp_digit td[3 * 108];
#endif
    sp_digit* t[3];
    sp_digit* norm;
    sp_digit mp = 1;
    sp_digit n;
    int i;
    int c, y;
    int err = MP_OKAY;

#if !defined(WOLFSSL_SP_NO_MALLOC)
    td = (sp_digit*)XMALLOC(sizeof(sp_digit) * 3 * 54 * 2, NULL,
                            DYNAMIC_TYPE_TMP_BUFFER);
    if (td == NULL) {
        err = MEMORY_E;
    }
#endif

    if (err == MP_OKAY) {
        norm = td;
        for (i=0; i<3; i++) {
#if !defined(WOLFSSL_SP_NO_MALLOC)
            t[i] = td + (i * 54 * 2);
#else
            t[i] = &td[i * 54 * 2];
#endif
            XMEMSET(t[i], 0, sizeof(sp_digit) * 54U * 2U);
        }

        sp_3072_mont_setup(m, &mp);
        sp_3072_mont_norm_54(norm, m);

        if (reduceA != 0) {
            err = sp_3072_mod_54(t[1], a, m);
        }
        else {
            XMEMCPY(t[1], a, sizeof(sp_digit) * 54U);
        }
    }
    if (err == MP_OKAY) {
        sp_3072_mul_54(t[1], t[1], norm);
        err = sp_3072_mod_54(t[1], t[1], m);
    }

    if (err == MP_OKAY) {
        i = bits / 57;
        c = bits % 57;
        n = e[i--] << (57 - c);
        for (; ; c--) {
            if (c == 0) {
                if (i == -1) {
                    break;
                }

                n = e[i--];
                c = 57;
            }

            y = (n >> 56) & 1;
            n <<= 1;

            sp_3072_mont_mul_54(t[y^1], t[0], t[1], m, mp);

            XMEMCPY(t[2], (void*)(((size_t)t[0] & addr_mask[y^1]) +
                                  ((size_t)t[1] & addr_mask[y])),
                                  sizeof(*t[2]) * 54 * 2);
            sp_3072_mont_sqr_54(t[2], t[2], m, mp);
            XMEMCPY((void*)(((size_t)t[0] & addr_mask[y^1]) +
                            ((size_t)t[1] & addr_mask[y])), t[2],
                            sizeof(*t[2]) * 54 * 2);
        }

        sp_3072_mont_reduce_54(t[0], m, mp);
        n = sp_3072_cmp_54(t[0], m);
        sp_3072_cond_sub_54(t[0], t[0], m, ((n < 0) ?
                    (sp_digit)1 : (sp_digit)0) - 1);
        XMEMCPY(r, t[0], sizeof(*r) * 54 * 2);

    }

#if !defined(WOLFSSL_SP_NO_MALLOC)
    if (td != NULL) {
        XFREE(td, NULL, DYNAMIC_TYPE_TMP_BUFFER);
    }
#endif

    return err;
#elif !defined(WC_NO_CACHE_RESISTANT)
#if defined(WOLFSSL_SMALL_STACK) && !defined(WOLFSSL_SP_NO_MALLOC)
    sp_digit* td;
#else
    sp_digit td[3 * 108];
#endif
    sp_digit* t[3];
    sp_digit* norm;
    sp_digit mp = 1;
    sp_digit n;
    int i;
    int c, y;
    int err = MP_OKAY;

#ifdef WOLFSSL_SMALL_STACK
    td = (sp_digit*)XMALLOC(sizeof(sp_digit) * 3 * 54 * 2, NULL,
                            DYNAMIC_TYPE_TMP_BUFFER);
    if (td == NULL) {
        err = MEMORY_E;
    }
#endif

    if (err == MP_OKAY) {
        norm = td;
        for (i=0; i<3; i++) {
#if defined(WOLFSSL_SMALL_STACK) && !defined(WOLFSSL_SP_NO_MALLOC)
            t[i] = td + (i * 54 * 2);
#else
            t[i] = &td[i * 54 * 2];
#endif
        }

        sp_3072_mont_setup(m, &mp);
        sp_3072_mont_norm_54(norm, m);

        if (reduceA != 0) {
            err = sp_3072_mod_54(t[1], a, m);
            if (err == MP_OKAY) {
                sp_3072_mul_54(t[1], t[1], norm);
                err = sp_3072_mod_54(t[1], t[1], m);
            }
        }
        else {
            sp_3072_mul_54(t[1], a, norm);
            err = sp_3072_mod_54(t[1], t[1], m);
        }
    }

    if (err == MP_OKAY) {
        i = bits / 57;
        c = bits % 57;
        n = e[i--] << (57 - c);
        for (; ; c--) {
            if (c == 0) {
                if (i == -1) {
                    break;
                }

                n = e[i--];
                c = 57;
            }

            y = (n >> 56) & 1;
            n <<= 1;

            sp_3072_mont_mul_54(t[y^1], t[0], t[1], m, mp);

            XMEMCPY(t[2], (void*)(((size_t)t[0] & addr_mask[y^1]) +
                                  ((size_t)t[1] & addr_mask[y])), 
                                  sizeof(*t[2]) * 54 * 2);
            sp_3072_mont_sqr_54(t[2], t[2], m, mp);
            XMEMCPY((void*)(((size_t)t[0] & addr_mask[y^1]) +
                            ((size_t)t[1] & addr_mask[y])), t[2], 
                            sizeof(*t[2]) * 54 * 2);
        }

        sp_3072_mont_reduce_54(t[0], m, mp);
        n = sp_3072_cmp_54(t[0], m);
        sp_3072_cond_sub_54(t[0], t[0], m, ((n < 0) ?
                    (sp_digit)1 : (sp_digit)0) - 1);
        XMEMCPY(r, t[0], sizeof(*r) * 54 * 2);
    }

#ifdef WOLFSSL_SMALL_STACK
    if (td != NULL) {
        XFREE(td, NULL, DYNAMIC_TYPE_TMP_BUFFER);
    }
#endif

    return err;
#else
#if defined(WOLFSSL_SMALL_STACK) && !defined(WOLFSSL_SP_NO_MALLOC)
    sp_digit* td;
#else
    sp_digit td[(32 * 108) + 108];
#endif
    sp_digit* t[32];
    sp_digit* rt;
    sp_digit* norm;
    sp_digit mp = 1;
    sp_digit n;
    int i;
    int c, y;
    int err = MP_OKAY;

#if defined(WOLFSSL_SMALL_STACK) && !defined(WOLFSSL_SP_NO_MALLOC)
    td = (sp_digit*)XMALLOC(sizeof(sp_digit) * ((32 * 108) + 108), NULL,
                            DYNAMIC_TYPE_TMP_BUFFER);
    if (td == NULL) {
        err = MEMORY_E;
    }
#endif

    if (err == MP_OKAY) {
        norm = td;
#if defined(WOLFSSL_SMALL_STACK) && !defined(WOLFSSL_SP_NO_MALLOC)
        for (i=0; i<32; i++)
            t[i] = td + i * 108;
        rt = td + 3456;
#else
        for (i=0; i<32; i++)
            t[i] = &td[i * 108];
        rt = &td[3456];
#endif

        sp_3072_mont_setup(m, &mp);
        sp_3072_mont_norm_54(norm, m);

        if (reduceA != 0) {
            err = sp_3072_mod_54(t[1], a, m);
            if (err == MP_OKAY) {
                sp_3072_mul_54(t[1], t[1], norm);
                err = sp_3072_mod_54(t[1], t[1], m);
            }
        }
        else {
            sp_3072_mul_54(t[1], a, norm);
            err = sp_3072_mod_54(t[1], t[1], m);
        }
    }

    if (err == MP_OKAY) {
        sp_3072_mont_sqr_54(t[ 2], t[ 1], m, mp);
        sp_3072_mont_mul_54(t[ 3], t[ 2], t[ 1], m, mp);
        sp_3072_mont_sqr_54(t[ 4], t[ 2], m, mp);
        sp_3072_mont_mul_54(t[ 5], t[ 3], t[ 2], m, mp);
        sp_3072_mont_sqr_54(t[ 6], t[ 3], m, mp);
        sp_3072_mont_mul_54(t[ 7], t[ 4], t[ 3], m, mp);
        sp_3072_mont_sqr_54(t[ 8], t[ 4], m, mp);
        sp_3072_mont_mul_54(t[ 9], t[ 5], t[ 4], m, mp);
        sp_3072_mont_sqr_54(t[10], t[ 5], m, mp);
        sp_3072_mont_mul_54(t[11], t[ 6], t[ 5], m, mp);
        sp_3072_mont_sqr_54(t[12], t[ 6], m, mp);
        sp_3072_mont_mul_54(t[13], t[ 7], t[ 6], m, mp);
        sp_3072_mont_sqr_54(t[14], t[ 7], m, mp);
        sp_3072_mont_mul_54(t[15], t[ 8], t[ 7], m, mp);
        sp_3072_mont_sqr_54(t[16], t[ 8], m, mp);
        sp_3072_mont_mul_54(t[17], t[ 9], t[ 8], m, mp);
        sp_3072_mont_sqr_54(t[18], t[ 9], m, mp);
        sp_3072_mont_mul_54(t[19], t[10], t[ 9], m, mp);
        sp_3072_mont_sqr_54(t[20], t[10], m, mp);
        sp_3072_mont_mul_54(t[21], t[11], t[10], m, mp);
        sp_3072_mont_sqr_54(t[22], t[11], m, mp);
        sp_3072_mont_mul_54(t[23], t[12], t[11], m, mp);
        sp_3072_mont_sqr_54(t[24], t[12], m, mp);
        sp_3072_mont_mul_54(t[25], t[13], t[12], m, mp);
        sp_3072_mont_sqr_54(t[26], t[13], m, mp);
        sp_3072_mont_mul_54(t[27], t[14], t[13], m, mp);
        sp_3072_mont_sqr_54(t[28], t[14], m, mp);
        sp_3072_mont_mul_54(t[29], t[15], t[14], m, mp);
        sp_3072_mont_sqr_54(t[30], t[15], m, mp);
        sp_3072_mont_mul_54(t[31], t[16], t[15], m, mp);

        bits = ((bits + 4) / 5) * 5;
        i = ((bits + 56) / 57) - 1;
        c = bits % 57;
        if (c == 0) {
            c = 57;
        }
        if (i < 54) {
            n = e[i--] << (64 - c);
        }
        else {
            n = 0;
            i--;
        }
        if (c < 5) {
            n |= e[i--] << (7 - c);
            c += 57;
        }
        y = (n >> 59) & 0x1f;
        n <<= 5;
        c -= 5;
        XMEMCPY(rt, t[y], sizeof(sp_digit) * 108);
        for (; i>=0 || c>=5; ) {
            if (c < 5) {
                n |= e[i--] << (7 - c);
                c += 57;
            }
            y = (n >> 59) & 0x1f;
            n <<= 5;
            c -= 5;

            sp_3072_mont_sqr_54(rt, rt, m, mp);
            sp_3072_mont_sqr_54(rt, rt, m, mp);
            sp_3072_mont_sqr_54(rt, rt, m, mp);
            sp_3072_mont_sqr_54(rt, rt, m, mp);
            sp_3072_mont_sqr_54(rt, rt, m, mp);

            sp_3072_mont_mul_54(rt, rt, t[y], m, mp);
        }

        sp_3072_mont_reduce_54(rt, m, mp);
        n = sp_3072_cmp_54(rt, m);
        sp_3072_cond_sub_54(rt, rt, m, ((n < 0) ?
                   (sp_digit)1 : (sp_digit)0) - 1);
        XMEMCPY(r, rt, sizeof(sp_digit) * 108);
    }

#if defined(WOLFSSL_SMALL_STACK) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (td != NULL) {
        XFREE(td, NULL, DYNAMIC_TYPE_TMP_BUFFER);
    }
#endif

    return err;
#endif
}
#endif /* (WOLFSSL_HAVE_SP_RSA && !WOLFSSL_RSA_PUBLIC_ONLY) || */
       /* WOLFSSL_HAVE_SP_DH */

#ifdef WOLFSSL_HAVE_SP_RSA
/* RSA public key operation.
 *
 * in      Array of bytes representing the number to exponentiate, base.
 * inLen   Number of bytes in base.
 * em      Public exponent.
 * mm      Modulus.
 * out     Buffer to hold big-endian bytes of exponentiation result.
 *         Must be at least 384 bytes long.
 * outLen  Number of bytes in result.
 * returns 0 on success, MP_TO_E when the outLen is too small, MP_READ_E when
 * an array is too long and MEMORY_E when dynamic memory allocation fails.
 */
int sp_RsaPublic_3072(const byte* in, word32 inLen, mp_int* em, mp_int* mm,
    byte* out, word32* outLen)
{
#ifdef WOLFSSL_SP_SMALL
    sp_digit* d = NULL;
    sp_digit* a;
    sp_digit* m;
    sp_digit* r;
    sp_digit* norm;
    sp_digit e[1] = {0};
    sp_digit mp;
    int i;
    int err = MP_OKAY;

    if (*outLen < 384U) {
        err = MP_TO_E;
    }

    if (err == MP_OKAY) {
        if (mp_count_bits(em) > 57) {
            err = MP_READ_E;
        }
        if (inLen > 384U) {
            err = MP_READ_E;
        }
        if (mp_count_bits(mm) != 3072) {
            err = MP_READ_E;
        }
    }

    if (err == MP_OKAY) {
        d = (sp_digit*)XMALLOC(sizeof(sp_digit) * 54 * 5, NULL,
                                                              DYNAMIC_TYPE_RSA);
        if (d == NULL)
            err = MEMORY_E;
    }

    if (err == MP_OKAY) {
        a = d;
        r = a + 54 * 2;
        m = r + 54 * 2;
        norm = r;

        sp_3072_from_bin(a, 54, in, inLen);
#if DIGIT_BIT >= 57
        e[0] = (sp_digit)em->dp[0];
#else
        e[0] = (sp_digit)em->dp[0];
        if (em->used > 1) {
            e[0] |= ((sp_digit)em->dp[1]) << DIGIT_BIT;
        }
#endif
        if (e[0] == 0) {
            err = MP_EXPTMOD_E;
        }
    }

    if (err == MP_OKAY) {
        sp_3072_from_mp(m, 54, mm);

        sp_3072_mont_setup(m, &mp);
        sp_3072_mont_norm_54(norm, m);
    }
    if (err == MP_OKAY) {
        sp_3072_mul_54(a, a, norm);
        err = sp_3072_mod_54(a, a, m);
    }
    if (err == MP_OKAY) {
        for (i=56; i>=0; i--) {
            if ((e[0] >> i) != 0) {
                break;
            }
        }

        XMEMCPY(r, a, sizeof(sp_digit) * 54 * 2);
        for (i--; i>=0; i--) {
            sp_3072_mont_sqr_54(r, r, m, mp);

            if (((e[0] >> i) & 1) == 1) {
                sp_3072_mont_mul_54(r, r, a, m, mp);
            }
        }
        sp_3072_mont_reduce_54(r, m, mp);
        mp = sp_3072_cmp_54(r, m);
        sp_3072_cond_sub_54(r, r, m, ((mp < 0) ?
                    (sp_digit)1 : (sp_digit)0)- 1);

        sp_3072_to_bin(r, out);
        *outLen = 384;
    }

    if (d != NULL) {
        XFREE(d, NULL, DYNAMIC_TYPE_RSA);
    }

    return err;
#else
#if (!defined(WOLFSSL_SP_SMALL) && !defined(WOLFSSL_SMALL_STACK)) || defined(WOLFSSL_SP_NO_MALLOC)
    sp_digit ad[108], md[54], rd[108];
#else
    sp_digit* d = NULL;
#endif
    sp_digit* a;
    sp_digit* m;
    sp_digit* r;
    sp_digit e[1] = {0};
    int err = MP_OKAY;

    if (*outLen < 384U) {
        err = MP_TO_E;
    }
    if (err == MP_OKAY) {
        if (mp_count_bits(em) > 57) {
            err = MP_READ_E;
        }
        if (inLen > 384U) {
            err = MP_READ_E;
        }
        if (mp_count_bits(mm) != 3072) {
            err = MP_READ_E;
        }
    }

#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (err == MP_OKAY) {
        d = (sp_digit*)XMALLOC(sizeof(sp_digit) * 54 * 5, NULL,
                                                              DYNAMIC_TYPE_RSA);
        if (d == NULL) {
            err = MEMORY_E;
        }
    }

    if (err == MP_OKAY) {
        a = d;
        r = a + 54 * 2;
        m = r + 54 * 2;
    }
#else
    a = ad;
    m = md;
    r = rd;
#endif

    if (err == MP_OKAY) {
        sp_3072_from_bin(a, 54, in, inLen);
#if DIGIT_BIT >= 57
        e[0] = (sp_digit)em->dp[0];
#else
        e[0] = (sp_digit)em->dp[0];
        if (em->used > 1) {
            e[0] |= ((sp_digit)em->dp[1]) << DIGIT_BIT;
        }
#endif
        if (e[0] == 0) {
            err = MP_EXPTMOD_E;
        }
    }
    if (err == MP_OKAY) {
        sp_3072_from_mp(m, 54, mm);

        if (e[0] == 0x3) {
            sp_3072_sqr_54(r, a);
            err = sp_3072_mod_54(r, r, m);
            if (err == MP_OKAY) {
                sp_3072_mul_54(r, a, r);
                err = sp_3072_mod_54(r, r, m);
            }
        }
        else {
            sp_digit* norm = r;
            int i;
            sp_digit mp;

            sp_3072_mont_setup(m, &mp);
            sp_3072_mont_norm_54(norm, m);

            sp_3072_mul_54(a, a, norm);
            err = sp_3072_mod_54(a, a, m);

            if (err == MP_OKAY) {
                for (i=56; i>=0; i--) {
                    if ((e[0] >> i) != 0) {
                        break;
                    }
                }

                XMEMCPY(r, a, sizeof(sp_digit) * 108U);
                for (i--; i>=0; i--) {
                    sp_3072_mont_sqr_54(r, r, m, mp);

                    if (((e[0] >> i) & 1) == 1) {
                        sp_3072_mont_mul_54(r, r, a, m, mp);
                    }
                }
                sp_3072_mont_reduce_54(r, m, mp);
                mp = sp_3072_cmp_54(r, m);
                sp_3072_cond_sub_54(r, r, m, ((mp < 0) ?
                           (sp_digit)1 : (sp_digit)0) - 1);
            }
        }
    }

    if (err == MP_OKAY) {
        sp_3072_to_bin(r, out);
        *outLen = 384;
    }

#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (d != NULL) {
        XFREE(d, NULL, DYNAMIC_TYPE_RSA);
    }
#endif

    return err;
#endif /* WOLFSSL_SP_SMALL */
}

#ifndef WOLFSSL_RSA_PUBLIC_ONLY
#if !defined(SP_RSA_PRIVATE_EXP_D) && !defined(RSA_LOW_MEM)
#endif /* !SP_RSA_PRIVATE_EXP_D && !RSA_LOW_MEM */
/* RSA private key operation.
 *
 * in      Array of bytes representing the number to exponentiate, base.
 * inLen   Number of bytes in base.
 * dm      Private exponent.
 * pm      First prime.
 * qm      Second prime.
 * dpm     First prime's CRT exponent.
 * dqm     Second prime's CRT exponent.
 * qim     Inverse of second prime mod p.
 * mm      Modulus.
 * out     Buffer to hold big-endian bytes of exponentiation result.
 *         Must be at least 384 bytes long.
 * outLen  Number of bytes in result.
 * returns 0 on success, MP_TO_E when the outLen is too small, MP_READ_E when
 * an array is too long and MEMORY_E when dynamic memory allocation fails.
 */
int sp_RsaPrivate_3072(const byte* in, word32 inLen, mp_int* dm,
    mp_int* pm, mp_int* qm, mp_int* dpm, mp_int* dqm, mp_int* qim, mp_int* mm,
    byte* out, word32* outLen)
{
#if defined(SP_RSA_PRIVATE_EXP_D) || defined(RSA_LOW_MEM)
#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    sp_digit* a = NULL;
    sp_digit* d = NULL;
    sp_digit* m = NULL;
    sp_digit* r = NULL;
    int err = MP_OKAY;

    (void)pm;
    (void)qm;
    (void)dpm;
    (void)dqm;
    (void)qim;

    if (*outLen < 384U) {
        err = MP_TO_E;
    }
    if (err == MP_OKAY) {
        if (mp_count_bits(dm) > 3072) {
           err = MP_READ_E;
        }
        if (inLen > 384) {
            err = MP_READ_E;
        }
        if (mp_count_bits(mm) != 3072) {
            err = MP_READ_E;
        }
    }

    if (err == MP_OKAY) {
        d = (sp_digit*)XMALLOC(sizeof(sp_digit) * 54 * 4, NULL,
                                                              DYNAMIC_TYPE_RSA);
        if (d == NULL) {
            err = MEMORY_E;
        }
    }
    if (err == MP_OKAY) {
        a = d + 54;
        m = a + 108;
        r = a;

        sp_3072_from_bin(a, 54, in, inLen);
        sp_3072_from_mp(d, 54, dm);
        sp_3072_from_mp(m, 54, mm);
        err = sp_3072_mod_exp_54(r, a, d, 3072, m, 0);
    }
    if (err == MP_OKAY) {
        sp_3072_to_bin(r, out);
        *outLen = 384;
    }

    if (d != NULL) {
        XMEMSET(d, 0, sizeof(sp_digit) * 54);
        XFREE(d, NULL, DYNAMIC_TYPE_RSA);
    }

    return err;
#else
    sp_digit a[108], d[54], m[54];
    sp_digit* r = a;
    int err = MP_OKAY;

    (void)pm;
    (void)qm;
    (void)dpm;
    (void)dqm;
    (void)qim;

    if (*outLen < 384U) {
        err = MP_TO_E;
    }
    if (err == MP_OKAY) {
        if (mp_count_bits(dm) > 3072) {
            err = MP_READ_E;
        }
        if (inLen > 384U) {
            err = MP_READ_E;
        }
        if (mp_count_bits(mm) != 3072) {
            err = MP_READ_E;
        }
    }

    if (err == MP_OKAY) {
        sp_3072_from_bin(a, 54, in, inLen);
        sp_3072_from_mp(d, 54, dm);
        sp_3072_from_mp(m, 54, mm);
        err = sp_3072_mod_exp_54(r, a, d, 3072, m, 0);
    }

    if (err == MP_OKAY) {
        sp_3072_to_bin(r, out);
        *outLen = 384;
    }

    XMEMSET(d, 0, sizeof(sp_digit) * 54);

    return err;
#endif /* WOLFSSL_SP_SMALL || defined(WOLFSSL_SMALL_STACK) */
#else
#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    sp_digit* t = NULL;
    sp_digit* a;
    sp_digit* p;
    sp_digit* q;
    sp_digit* dp;
    sp_digit* dq;
    sp_digit* qi;
    sp_digit* tmpa;
    sp_digit* tmpb;
    sp_digit* r;
    int err = MP_OKAY;

    (void)dm;
    (void)mm;

    if (*outLen < 384U) {
        err = MP_TO_E;
    }
    if (err == MP_OKAY) {
        if (inLen > 384) {
            err = MP_READ_E;
        }
        if (mp_count_bits(mm) != 3072) {
            err = MP_READ_E;
        }
    }

    if (err == MP_OKAY) {
        t = (sp_digit*)XMALLOC(sizeof(sp_digit) * 27 * 11, NULL,
                                                              DYNAMIC_TYPE_RSA);
        if (t == NULL) {
            err = MEMORY_E;
        }
    }
    if (err == MP_OKAY) {
        a = t;
        p = a + 54 * 2;
        q = p + 27;
        qi = dq = dp = q + 27;
        tmpa = qi + 27;
        tmpb = tmpa + 54;

        r = t + 54;

        sp_3072_from_bin(a, 54, in, inLen);
        sp_3072_from_mp(p, 27, pm);
        sp_3072_from_mp(q, 27, qm);
        sp_3072_from_mp(dp, 27, dpm);
        err = sp_3072_mod_exp_27(tmpa, a, dp, 1536, p, 1);
    }
    if (err == MP_OKAY) {
        sp_3072_from_mp(dq, 27, dqm);
        err = sp_3072_mod_exp_27(tmpb, a, dq, 1536, q, 1);
    }
    if (err == MP_OKAY) {
        (void)sp_3072_sub_27(tmpa, tmpa, tmpb);
        sp_3072_cond_add_27(tmpa, tmpa, p, 0 - ((sp_int_digit)tmpa[26] >> 63));
        sp_3072_cond_add_27(tmpa, tmpa, p, 0 - ((sp_int_digit)tmpa[26] >> 63));

        sp_3072_from_mp(qi, 27, qim);
        sp_3072_mul_27(tmpa, tmpa, qi);
        err = sp_3072_mod_27(tmpa, tmpa, p);
    }

    if (err == MP_OKAY) {
        sp_3072_mul_27(tmpa, q, tmpa);
        (void)sp_3072_add_54(r, tmpb, tmpa);
        sp_3072_norm_54(r);

        sp_3072_to_bin(r, out);
        *outLen = 384;
    }

    if (t != NULL) {
        XMEMSET(t, 0, sizeof(sp_digit) * 27 * 11);
        XFREE(t, NULL, DYNAMIC_TYPE_RSA);
    }

    return err;
#else
    sp_digit a[54 * 2];
    sp_digit p[27], q[27], dp[27], dq[27], qi[27];
    sp_digit tmpa[54], tmpb[54];
    sp_digit* r = a;
    int err = MP_OKAY;

    (void)dm;
    (void)mm;

    if (*outLen < 384U) {
        err = MP_TO_E;
    }
    if (err == MP_OKAY) {
        if (inLen > 384U) {
            err = MP_READ_E;
        }
        if (mp_count_bits(mm) != 3072) {
            err = MP_READ_E;
        }
    }

    if (err == MP_OKAY) {
        sp_3072_from_bin(a, 54, in, inLen);
        sp_3072_from_mp(p, 27, pm);
        sp_3072_from_mp(q, 27, qm);
        sp_3072_from_mp(dp, 27, dpm);
        sp_3072_from_mp(dq, 27, dqm);
        sp_3072_from_mp(qi, 27, qim);

        err = sp_3072_mod_exp_27(tmpa, a, dp, 1536, p, 1);
    }
    if (err == MP_OKAY) {
        err = sp_3072_mod_exp_27(tmpb, a, dq, 1536, q, 1);
    }

    if (err == MP_OKAY) {
        (void)sp_3072_sub_27(tmpa, tmpa, tmpb);
        sp_3072_cond_add_27(tmpa, tmpa, p, 0 - ((sp_int_digit)tmpa[26] >> 63));
        sp_3072_cond_add_27(tmpa, tmpa, p, 0 - ((sp_int_digit)tmpa[26] >> 63));
        sp_3072_mul_27(tmpa, tmpa, qi);
        err = sp_3072_mod_27(tmpa, tmpa, p);
    }

    if (err == MP_OKAY) {
        sp_3072_mul_27(tmpa, tmpa, q);
        (void)sp_3072_add_54(r, tmpb, tmpa);
        sp_3072_norm_54(r);

        sp_3072_to_bin(r, out);
        *outLen = 384;
    }

    XMEMSET(tmpa, 0, sizeof(tmpa));
    XMEMSET(tmpb, 0, sizeof(tmpb));
    XMEMSET(p, 0, sizeof(p));
    XMEMSET(q, 0, sizeof(q));
    XMEMSET(dp, 0, sizeof(dp));
    XMEMSET(dq, 0, sizeof(dq));
    XMEMSET(qi, 0, sizeof(qi));

    return err;
#endif /* WOLFSSL_SP_SMALL || defined(WOLFSSL_SMALL_STACK) */
#endif /* SP_RSA_PRIVATE_EXP_D || RSA_LOW_MEM */
}

#endif /* !WOLFSSL_RSA_PUBLIC_ONLY */
#endif /* WOLFSSL_HAVE_SP_RSA */
#if defined(WOLFSSL_HAVE_SP_DH) || (defined(WOLFSSL_HAVE_SP_RSA) && \
                                              !defined(WOLFSSL_RSA_PUBLIC_ONLY))
/* Convert an array of sp_digit to an mp_int.
 *
 * a  A single precision integer.
 * r  A multi-precision integer.
 */
static int sp_3072_to_mp(const sp_digit* a, mp_int* r)
{
    int err;

    err = mp_grow(r, (3072 + DIGIT_BIT - 1) / DIGIT_BIT);
    if (err == MP_OKAY) { /*lint !e774 case where err is always MP_OKAY*/
#if DIGIT_BIT == 57
        XMEMCPY(r->dp, a, sizeof(sp_digit) * 54);
        r->used = 54;
        mp_clamp(r);
#elif DIGIT_BIT < 57
        int i, j = 0, s = 0;

        r->dp[0] = 0;
        for (i = 0; i < 54; i++) {
            r->dp[j] |= (mp_digit)(a[i] << s);
            r->dp[j] &= (1L << DIGIT_BIT) - 1;
            s = DIGIT_BIT - s;
            r->dp[++j] = (mp_digit)(a[i] >> s);
            while (s + DIGIT_BIT <= 57) {
                s += DIGIT_BIT;
                r->dp[j++] &= (1L << DIGIT_BIT) - 1;
                if (s == SP_WORD_SIZE) {
                    r->dp[j] = 0;
                }
                else {
                    r->dp[j] = (mp_digit)(a[i] >> s);
                }
            }
            s = 57 - s;
        }
        r->used = (3072 + DIGIT_BIT - 1) / DIGIT_BIT;
        mp_clamp(r);
#else
        int i, j = 0, s = 0;

        r->dp[0] = 0;
        for (i = 0; i < 54; i++) {
            r->dp[j] |= ((mp_digit)a[i]) << s;
            if (s + 57 >= DIGIT_BIT) {
    #if DIGIT_BIT != 32 && DIGIT_BIT != 64
                r->dp[j] &= (1L << DIGIT_BIT) - 1;
    #endif
                s = DIGIT_BIT - s;
                r->dp[++j] = a[i] >> s;
                s = 57 - s;
            }
            else {
                s += 57;
            }
        }
        r->used = (3072 + DIGIT_BIT - 1) / DIGIT_BIT;
        mp_clamp(r);
#endif
    }

    return err;
}

/* Perform the modular exponentiation for Diffie-Hellman.
 *
 * base  Base. MP integer.
 * exp   Exponent. MP integer.
 * mod   Modulus. MP integer.
 * res   Result. MP integer.
 * returns 0 on success, MP_READ_E if there are too many bytes in an array
 * and MEMORY_E if memory allocation fails.
 */
int sp_ModExp_3072(mp_int* base, mp_int* exp, mp_int* mod, mp_int* res)
{
#ifdef WOLFSSL_SP_SMALL
    int err = MP_OKAY;
    sp_digit* d = NULL;
    sp_digit* b;
    sp_digit* e;
    sp_digit* m;
    sp_digit* r;
    int expBits = mp_count_bits(exp);

    if (mp_count_bits(base) > 3072) {
        err = MP_READ_E;
    }

    if (err == MP_OKAY) {
        if (expBits > 3072) {
            err = MP_READ_E;
        }
    }

    if (err == MP_OKAY) {
        if (mp_count_bits(mod) != 3072) {
            err = MP_READ_E;
        }
    }

    if (err == MP_OKAY) {
        d = (sp_digit*)XMALLOC(sizeof(*d) * 54 * 4, NULL, DYNAMIC_TYPE_DH);
        if (d == NULL) {
            err = MEMORY_E;
        }
    }

    if (err == MP_OKAY) {
        b = d;
        e = b + 54 * 2;
        m = e + 54;
        r = b;

        sp_3072_from_mp(b, 54, base);
        sp_3072_from_mp(e, 54, exp);
        sp_3072_from_mp(m, 54, mod);

        err = sp_3072_mod_exp_54(r, b, e, mp_count_bits(exp), m, 0);
    }

    if (err == MP_OKAY) {
        err = sp_3072_to_mp(r, res);
    }

    if (d != NULL) {
        XMEMSET(e, 0, sizeof(sp_digit) * 54U);
        XFREE(d, NULL, DYNAMIC_TYPE_DH);
    }
    return err;
#else
#ifndef WOLFSSL_SMALL_STACK
    sp_digit bd[108], ed[54], md[54];
#else
    sp_digit* d = NULL;
#endif
    sp_digit* b;
    sp_digit* e;
    sp_digit* m;
    sp_digit* r;
    int err = MP_OKAY;
    int expBits = mp_count_bits(exp);

    if (mp_count_bits(base) > 3072) {
        err = MP_READ_E;
    }

    if (err == MP_OKAY) {
        if (expBits > 3072) {
            err = MP_READ_E;
        }
    }
    
    if (err == MP_OKAY) {
        if (mp_count_bits(mod) != 3072) {
            err = MP_READ_E;
        }
    }

#ifdef WOLFSSL_SMALL_STACK
    if (err == MP_OKAY) {
        d = (sp_digit*)XMALLOC(sizeof(*d) * 54 * 4, NULL, DYNAMIC_TYPE_DH);
        if (d == NULL)
            err = MEMORY_E;
    }

    if (err == MP_OKAY) {
        b = d;
        e = b + 54 * 2;
        m = e + 54;
        r = b;
    }
#else
    r = b = bd;
    e = ed;
    m = md;
#endif

    if (err == MP_OKAY) {
        sp_3072_from_mp(b, 54, base);
        sp_3072_from_mp(e, 54, exp);
        sp_3072_from_mp(m, 54, mod);

        err = sp_3072_mod_exp_54(r, b, e, expBits, m, 0);
    }

    if (err == MP_OKAY) {
        err = sp_3072_to_mp(r, res);
    }


#ifdef WOLFSSL_SMALL_STACK
    if (d != NULL) {
        XMEMSET(e, 0, sizeof(sp_digit) * 54U);
        XFREE(d, NULL, DYNAMIC_TYPE_DH);
    }
#else
    XMEMSET(e, 0, sizeof(sp_digit) * 54U);
#endif

    return err;
#endif
}

#ifdef WOLFSSL_HAVE_SP_DH

#ifdef HAVE_FFDHE_3072
SP_NOINLINE static void sp_3072_lshift_54(sp_digit* r, sp_digit* a, byte n)
{
#ifdef WOLFSSL_SP_SMALL
    int i;

    r[54] = a[53] >> (57 - n);
    for (i=53; i>0; i--) {
        r[i] = ((a[i] << n) | (a[i-1] >> (57 - n))) & 0x1ffffffffffffffL;
    }
#else
    sp_int_digit s, t;

    s = (sp_int_digit)a[53];
    r[54] = s >> (57U - n);
    s = (sp_int_digit)(a[53]); t = (sp_int_digit)(a[52]);
    r[53] = ((s << n) | (t >> (57U - n))) & 0x1ffffffffffffffUL;
    s = (sp_int_digit)(a[52]); t = (sp_int_digit)(a[51]);
    r[52] = ((s << n) | (t >> (57U - n))) & 0x1ffffffffffffffUL;
    s = (sp_int_digit)(a[51]); t = (sp_int_digit)(a[50]);
    r[51] = ((s << n) | (t >> (57U - n))) & 0x1ffffffffffffffUL;
    s = (sp_int_digit)(a[50]); t = (sp_int_digit)(a[49]);
    r[50] = ((s << n) | (t >> (57U - n))) & 0x1ffffffffffffffUL;
    s = (sp_int_digit)(a[49]); t = (sp_int_digit)(a[48]);
    r[49] = ((s << n) | (t >> (57U - n))) & 0x1ffffffffffffffUL;
    s = (sp_int_digit)(a[48]); t = (sp_int_digit)(a[47]);
    r[48] = ((s << n) | (t >> (57U - n))) & 0x1ffffffffffffffUL;
    s = (sp_int_digit)(a[47]); t = (sp_int_digit)(a[46]);
    r[47] = ((s << n) | (t >> (57U - n))) & 0x1ffffffffffffffUL;
    s = (sp_int_digit)(a[46]); t = (sp_int_digit)(a[45]);
    r[46] = ((s << n) | (t >> (57U - n))) & 0x1ffffffffffffffUL;
    s = (sp_int_digit)(a[45]); t = (sp_int_digit)(a[44]);
    r[45] = ((s << n) | (t >> (57U - n))) & 0x1ffffffffffffffUL;
    s = (sp_int_digit)(a[44]); t = (sp_int_digit)(a[43]);
    r[44] = ((s << n) | (t >> (57U - n))) & 0x1ffffffffffffffUL;
    s = (sp_int_digit)(a[43]); t = (sp_int_digit)(a[42]);
    r[43] = ((s << n) | (t >> (57U - n))) & 0x1ffffffffffffffUL;
    s = (sp_int_digit)(a[42]); t = (sp_int_digit)(a[41]);
    r[42] = ((s << n) | (t >> (57U - n))) & 0x1ffffffffffffffUL;
    s = (sp_int_digit)(a[41]); t = (sp_int_digit)(a[40]);
    r[41] = ((s << n) | (t >> (57U - n))) & 0x1ffffffffffffffUL;
    s = (sp_int_digit)(a[40]); t = (sp_int_digit)(a[39]);
    r[40] = ((s << n) | (t >> (57U - n))) & 0x1ffffffffffffffUL;
    s = (sp_int_digit)(a[39]); t = (sp_int_digit)(a[38]);
    r[39] = ((s << n) | (t >> (57U - n))) & 0x1ffffffffffffffUL;
    s = (sp_int_digit)(a[38]); t = (sp_int_digit)(a[37]);
    r[38] = ((s << n) | (t >> (57U - n))) & 0x1ffffffffffffffUL;
    s = (sp_int_digit)(a[37]); t = (sp_int_digit)(a[36]);
    r[37] = ((s << n) | (t >> (57U - n))) & 0x1ffffffffffffffUL;
    s = (sp_int_digit)(a[36]); t = (sp_int_digit)(a[35]);
    r[36] = ((s << n) | (t >> (57U - n))) & 0x1ffffffffffffffUL;
    s = (sp_int_digit)(a[35]); t = (sp_int_digit)(a[34]);
    r[35] = ((s << n) | (t >> (57U - n))) & 0x1ffffffffffffffUL;
    s = (sp_int_digit)(a[34]); t = (sp_int_digit)(a[33]);
    r[34] = ((s << n) | (t >> (57U - n))) & 0x1ffffffffffffffUL;
    s = (sp_int_digit)(a[33]); t = (sp_int_digit)(a[32]);
    r[33] = ((s << n) | (t >> (57U - n))) & 0x1ffffffffffffffUL;
    s = (sp_int_digit)(a[32]); t = (sp_int_digit)(a[31]);
    r[32] = ((s << n) | (t >> (57U - n))) & 0x1ffffffffffffffUL;
    s = (sp_int_digit)(a[31]); t = (sp_int_digit)(a[30]);
    r[31] = ((s << n) | (t >> (57U - n))) & 0x1ffffffffffffffUL;
    s = (sp_int_digit)(a[30]); t = (sp_int_digit)(a[29]);
    r[30] = ((s << n) | (t >> (57U - n))) & 0x1ffffffffffffffUL;
    s = (sp_int_digit)(a[29]); t = (sp_int_digit)(a[28]);
    r[29] = ((s << n) | (t >> (57U - n))) & 0x1ffffffffffffffUL;
    s = (sp_int_digit)(a[28]); t = (sp_int_digit)(a[27]);
    r[28] = ((s << n) | (t >> (57U - n))) & 0x1ffffffffffffffUL;
    s = (sp_int_digit)(a[27]); t = (sp_int_digit)(a[26]);
    r[27] = ((s << n) | (t >> (57U - n))) & 0x1ffffffffffffffUL;
    s = (sp_int_digit)(a[26]); t = (sp_int_digit)(a[25]);
    r[26] = ((s << n) | (t >> (57U - n))) & 0x1ffffffffffffffUL;
    s = (sp_int_digit)(a[25]); t = (sp_int_digit)(a[24]);
    r[25] = ((s << n) | (t >> (57U - n))) & 0x1ffffffffffffffUL;
    s = (sp_int_digit)(a[24]); t = (sp_int_digit)(a[23]);
    r[24] = ((s << n) | (t >> (57U - n))) & 0x1ffffffffffffffUL;
    s = (sp_int_digit)(a[23]); t = (sp_int_digit)(a[22]);
    r[23] = ((s << n) | (t >> (57U - n))) & 0x1ffffffffffffffUL;
    s = (sp_int_digit)(a[22]); t = (sp_int_digit)(a[21]);
    r[22] = ((s << n) | (t >> (57U - n))) & 0x1ffffffffffffffUL;
    s = (sp_int_digit)(a[21]); t = (sp_int_digit)(a[20]);
    r[21] = ((s << n) | (t >> (57U - n))) & 0x1ffffffffffffffUL;
    s = (sp_int_digit)(a[20]); t = (sp_int_digit)(a[19]);
    r[20] = ((s << n) | (t >> (57U - n))) & 0x1ffffffffffffffUL;
    s = (sp_int_digit)(a[19]); t = (sp_int_digit)(a[18]);
    r[19] = ((s << n) | (t >> (57U - n))) & 0x1ffffffffffffffUL;
    s = (sp_int_digit)(a[18]); t = (sp_int_digit)(a[17]);
    r[18] = ((s << n) | (t >> (57U - n))) & 0x1ffffffffffffffUL;
    s = (sp_int_digit)(a[17]); t = (sp_int_digit)(a[16]);
    r[17] = ((s << n) | (t >> (57U - n))) & 0x1ffffffffffffffUL;
    s = (sp_int_digit)(a[16]); t = (sp_int_digit)(a[15]);
    r[16] = ((s << n) | (t >> (57U - n))) & 0x1ffffffffffffffUL;
    s = (sp_int_digit)(a[15]); t = (sp_int_digit)(a[14]);
    r[15] = ((s << n) | (t >> (57U - n))) & 0x1ffffffffffffffUL;
    s = (sp_int_digit)(a[14]); t = (sp_int_digit)(a[13]);
    r[14] = ((s << n) | (t >> (57U - n))) & 0x1ffffffffffffffUL;
    s = (sp_int_digit)(a[13]); t = (sp_int_digit)(a[12]);
    r[13] = ((s << n) | (t >> (57U - n))) & 0x1ffffffffffffffUL;
    s = (sp_int_digit)(a[12]); t = (sp_int_digit)(a[11]);
    r[12] = ((s << n) | (t >> (57U - n))) & 0x1ffffffffffffffUL;
    s = (sp_int_digit)(a[11]); t = (sp_int_digit)(a[10]);
    r[11] = ((s << n) | (t >> (57U - n))) & 0x1ffffffffffffffUL;
    s = (sp_int_digit)(a[10]); t = (sp_int_digit)(a[9]);
    r[10] = ((s << n) | (t >> (57U - n))) & 0x1ffffffffffffffUL;
    s = (sp_int_digit)(a[9]); t = (sp_int_digit)(a[8]);
    r[9] = ((s << n) | (t >> (57U - n))) & 0x1ffffffffffffffUL;
    s = (sp_int_digit)(a[8]); t = (sp_int_digit)(a[7]);
    r[8] = ((s << n) | (t >> (57U - n))) & 0x1ffffffffffffffUL;
    s = (sp_int_digit)(a[7]); t = (sp_int_digit)(a[6]);
    r[7] = ((s << n) | (t >> (57U - n))) & 0x1ffffffffffffffUL;
    s = (sp_int_digit)(a[6]); t = (sp_int_digit)(a[5]);
    r[6] = ((s << n) | (t >> (57U - n))) & 0x1ffffffffffffffUL;
    s = (sp_int_digit)(a[5]); t = (sp_int_digit)(a[4]);
    r[5] = ((s << n) | (t >> (57U - n))) & 0x1ffffffffffffffUL;
    s = (sp_int_digit)(a[4]); t = (sp_int_digit)(a[3]);
    r[4] = ((s << n) | (t >> (57U - n))) & 0x1ffffffffffffffUL;
    s = (sp_int_digit)(a[3]); t = (sp_int_digit)(a[2]);
    r[3] = ((s << n) | (t >> (57U - n))) & 0x1ffffffffffffffUL;
    s = (sp_int_digit)(a[2]); t = (sp_int_digit)(a[1]);
    r[2] = ((s << n) | (t >> (57U - n))) & 0x1ffffffffffffffUL;
    s = (sp_int_digit)(a[1]); t = (sp_int_digit)(a[0]);
    r[1] = ((s << n) | (t >> (57U - n))) & 0x1ffffffffffffffUL;
#endif
    r[0] = (a[0] << n) & 0x1ffffffffffffffL;
}

/* Modular exponentiate 2 to the e mod m. (r = 2^e mod m)
 *
 * r     A single precision number that is the result of the operation.
 * e     A single precision number that is the exponent.
 * bits  The number of bits in the exponent.
 * m     A single precision number that is the modulus.
 * returns 0 on success and MEMORY_E on dynamic memory allocation failure.
 */
static int sp_3072_mod_exp_2_54(sp_digit* r, const sp_digit* e, int bits, const sp_digit* m)
{
#if defined(WOLFSSL_SMALL_STACK) && !defined(WOLFSSL_SP_NO_MALLOC)
    sp_digit* td;
#else
    sp_digit td[163];
#endif
    sp_digit* norm;
    sp_digit* tmp;
    sp_digit mp = 1;
    sp_digit n, o;
    int i;
    int c, y;
    int err = MP_OKAY;

#if defined(WOLFSSL_SMALL_STACK) && !defined(WOLFSSL_SP_NO_MALLOC)
    td = (sp_digit*)XMALLOC(sizeof(sp_digit) * 163, NULL,
                            DYNAMIC_TYPE_TMP_BUFFER);
    if (td == NULL) {
        err = MEMORY_E;
    }
#endif

    if (err == MP_OKAY) {
        norm = td;
#if defined(WOLFSSL_SMALL_STACK) && !defined(WOLFSSL_SP_NO_MALLOC)
        tmp  = td + 108;
        XMEMSET(td, 0, sizeof(sp_digit) * 163);
#else
        tmp  = &td[108];
        XMEMSET(td, 0, sizeof(td));
#endif

        sp_3072_mont_setup(m, &mp);
        sp_3072_mont_norm_54(norm, m);

        bits = ((bits + 4) / 5) * 5;
        i = ((bits + 56) / 57) - 1;
        c = bits % 57;
        if (c == 0) {
            c = 57;
        }
        if (i < 54) {
            n = e[i--] << (64 - c);
        }
        else {
            n = 0;
            i--;
        }
        if (c < 5) {
            n |= e[i--] << (7 - c);
            c += 57;
        }
        y = (n >> 59) & 0x1f;
        n <<= 5;
        c -= 5;
        sp_3072_lshift_54(r, norm, y);
        for (; i>=0 || c>=5; ) {
            if (c < 5) {
                n |= e[i--] << (7 - c);
                c += 57;
            }
            y = (n >> 59) & 0x1f;
            n <<= 5;
            c -= 5;

            sp_3072_mont_sqr_54(r, r, m, mp);
            sp_3072_mont_sqr_54(r, r, m, mp);
            sp_3072_mont_sqr_54(r, r, m, mp);
            sp_3072_mont_sqr_54(r, r, m, mp);
            sp_3072_mont_sqr_54(r, r, m, mp);

            sp_3072_lshift_54(r, r, y);
            sp_3072_mul_d_54(tmp, norm, (r[54] << 6) + (r[53] >> 51));
            r[54] = 0;
            r[53] &= 0x7ffffffffffffL;
            (void)sp_3072_add_54(r, r, tmp);
            sp_3072_norm_54(r);
            o = sp_3072_cmp_54(r, m);
            sp_3072_cond_sub_54(r, r, m, ((o < 0) ?
                                          (sp_digit)1 : (sp_digit)0) - 1);
        }

        sp_3072_mont_reduce_54(r, m, mp);
        n = sp_3072_cmp_54(r, m);
        sp_3072_cond_sub_54(r, r, m, ((n < 0) ?
                                                (sp_digit)1 : (sp_digit)0) - 1);
    }

#if defined(WOLFSSL_SMALL_STACK) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (td != NULL) {
        XFREE(td, NULL, DYNAMIC_TYPE_TMP_BUFFER);
    }
#endif

    return err;
}

#endif /* HAVE_FFDHE_3072 */

/* Perform the modular exponentiation for Diffie-Hellman.
 *
 * base     Base.
 * exp      Array of bytes that is the exponent.
 * expLen   Length of data, in bytes, in exponent.
 * mod      Modulus.
 * out      Buffer to hold big-endian bytes of exponentiation result.
 *          Must be at least 384 bytes long.
 * outLen   Length, in bytes, of exponentiation result.
 * returns 0 on success, MP_READ_E if there are too many bytes in an array
 * and MEMORY_E if memory allocation fails.
 */
int sp_DhExp_3072(mp_int* base, const byte* exp, word32 expLen,
    mp_int* mod, byte* out, word32* outLen)
{
#ifdef WOLFSSL_SP_SMALL
    int err = MP_OKAY;
    sp_digit* d = NULL;
    sp_digit* b;
    sp_digit* e;
    sp_digit* m;
    sp_digit* r;
    word32 i;

    if (mp_count_bits(base) > 3072) {
        err = MP_READ_E;
    }

    if (err == MP_OKAY) {
        if (expLen > 384) {
            err = MP_READ_E;
        }
    }

    if (err == MP_OKAY) {
        if (mp_count_bits(mod) != 3072) {
            err = MP_READ_E;
        }
    }

    if (err == MP_OKAY) {
        d = (sp_digit*)XMALLOC(sizeof(*d) * 54 * 4, NULL, DYNAMIC_TYPE_DH);
        if (d == NULL) {
            err = MEMORY_E;
        }
    }

    if (err == MP_OKAY) {
        b = d;
        e = b + 54 * 2;
        m = e + 54;
        r = b;

        sp_3072_from_mp(b, 54, base);
        sp_3072_from_bin(e, 54, exp, expLen);
        sp_3072_from_mp(m, 54, mod);

    #ifdef HAVE_FFDHE_3072
        if (base->used == 1 && base->dp[0] == 2 &&
                (m[53] >> 19) == 0xffffffffL) {
            err = sp_3072_mod_exp_2_54(r, e, expLen * 8, m);
        }
        else
    #endif
            err = sp_3072_mod_exp_54(r, b, e, expLen * 8, m, 0);
    }

    if (err == MP_OKAY) {
        sp_3072_to_bin(r, out);
        *outLen = 384;
        for (i=0; i<384 && out[i] == 0; i++) {
        }
        *outLen -= i;
        XMEMMOVE(out, out + i, *outLen);
    }

    if (d != NULL) {
        XMEMSET(e, 0, sizeof(sp_digit) * 54U);
        XFREE(d, NULL, DYNAMIC_TYPE_DH);
    }
    return err;
#else
#ifndef WOLFSSL_SMALL_STACK
    sp_digit bd[108], ed[54], md[54];
#else
    sp_digit* d = NULL;
#endif
    sp_digit* b;
    sp_digit* e;
    sp_digit* m;
    sp_digit* r;
    word32 i;
    int err = MP_OKAY;

    if (mp_count_bits(base) > 3072) {
        err = MP_READ_E;
    }

    if (err == MP_OKAY) {
        if (expLen > 384U) {
            err = MP_READ_E;
        }
    }

    if (err == MP_OKAY) {
        if (mp_count_bits(mod) != 3072) {
            err = MP_READ_E;
        }
    }
#ifdef WOLFSSL_SMALL_STACK
    if (err == MP_OKAY) {
        d = (sp_digit*)XMALLOC(sizeof(*d) * 54 * 4, NULL, DYNAMIC_TYPE_DH);
        if (d == NULL)
            err = MEMORY_E;
    }

    if (err == MP_OKAY) {
        b = d;
        e = b + 54 * 2;
        m = e + 54;
        r = b;
    }
#else
    r = b = bd;
    e = ed;
    m = md;
#endif

    if (err == MP_OKAY) {
        sp_3072_from_mp(b, 54, base);
        sp_3072_from_bin(e, 54, exp, expLen);
        sp_3072_from_mp(m, 54, mod);

    #ifdef HAVE_FFDHE_3072
        if (base->used == 1 && base->dp[0] == 2U &&
                (m[53] >> 19) == 0xffffffffL) {
            err = sp_3072_mod_exp_2_54(r, e, expLen * 8U, m);
        }
        else {
    #endif
            err = sp_3072_mod_exp_54(r, b, e, expLen * 8U, m, 0);
    #ifdef HAVE_FFDHE_3072
        }
    #endif
    }

    if (err == MP_OKAY) {
        sp_3072_to_bin(r, out);
        *outLen = 384;
        for (i=0; i<384U && out[i] == 0U; i++) {
        }
        *outLen -= i;
        XMEMMOVE(out, out + i, *outLen);
    }

#ifdef WOLFSSL_SMALL_STACK
    if (d != NULL) {
        XMEMSET(e, 0, sizeof(sp_digit) * 54U);
        XFREE(d, NULL, DYNAMIC_TYPE_DH);
    }
#else
    XMEMSET(e, 0, sizeof(sp_digit) * 54U);
#endif

    return err;
#endif
}
#endif /* WOLFSSL_HAVE_SP_DH */

/* Perform the modular exponentiation for Diffie-Hellman.
 *
 * base  Base. MP integer.
 * exp   Exponent. MP integer.
 * mod   Modulus. MP integer.
 * res   Result. MP integer.
 * returns 0 on success, MP_READ_E if there are too many bytes in an array
 * and MEMORY_E if memory allocation fails.
 */
int sp_ModExp_1536(mp_int* base, mp_int* exp, mp_int* mod, mp_int* res)
{
#ifdef WOLFSSL_SP_SMALL
    int err = MP_OKAY;
    sp_digit* d = NULL;
    sp_digit* b;
    sp_digit* e;
    sp_digit* m;
    sp_digit* r;
    int expBits = mp_count_bits(exp);

    if (mp_count_bits(base) > 1536) {
        err = MP_READ_E;
    }

    if (err == MP_OKAY) {
        if (expBits > 1536) {
            err = MP_READ_E;
        }
    }

    if (err == MP_OKAY) {
        if (mp_count_bits(mod) != 1536) {
            err = MP_READ_E;
        }
    }

    if (err == MP_OKAY) {
        d = (sp_digit*)XMALLOC(sizeof(*d) * 27 * 4, NULL, DYNAMIC_TYPE_DH);
        if (d == NULL) {
            err = MEMORY_E;
        }
    }

    if (err == MP_OKAY) {
        b = d;
        e = b + 27 * 2;
        m = e + 27;
        r = b;

        sp_3072_from_mp(b, 27, base);
        sp_3072_from_mp(e, 27, exp);
        sp_3072_from_mp(m, 27, mod);

        err = sp_3072_mod_exp_27(r, b, e, mp_count_bits(exp), m, 0);
    }

    if (err == MP_OKAY) {
        XMEMSET(r + 27, 0, sizeof(*r) * 27U);
        err = sp_3072_to_mp(r, res);
    }

    if (d != NULL) {
        XMEMSET(e, 0, sizeof(sp_digit) * 27U);
        XFREE(d, NULL, DYNAMIC_TYPE_DH);
    }
    return err;
#else
#ifndef WOLFSSL_SMALL_STACK
    sp_digit bd[54], ed[27], md[27];
#else
    sp_digit* d = NULL;
#endif
    sp_digit* b;
    sp_digit* e;
    sp_digit* m;
    sp_digit* r;
    int err = MP_OKAY;
    int expBits = mp_count_bits(exp);

    if (mp_count_bits(base) > 1536) {
        err = MP_READ_E;
    }

    if (err == MP_OKAY) {
        if (expBits > 1536) {
            err = MP_READ_E;
        }
    }
    
    if (err == MP_OKAY) {
        if (mp_count_bits(mod) != 1536) {
            err = MP_READ_E;
        }
    }

#ifdef WOLFSSL_SMALL_STACK
    if (err == MP_OKAY) {
        d = (sp_digit*)XMALLOC(sizeof(*d) * 27 * 4, NULL, DYNAMIC_TYPE_DH);
        if (d == NULL)
            err = MEMORY_E;
    }

    if (err == MP_OKAY) {
        b = d;
        e = b + 27 * 2;
        m = e + 27;
        r = b;
    }
#else
    r = b = bd;
    e = ed;
    m = md;
#endif

    if (err == MP_OKAY) {
        sp_3072_from_mp(b, 27, base);
        sp_3072_from_mp(e, 27, exp);
        sp_3072_from_mp(m, 27, mod);

        err = sp_3072_mod_exp_27(r, b, e, expBits, m, 0);
    }

    if (err == MP_OKAY) {
        XMEMSET(r + 27, 0, sizeof(*r) * 27U);
        err = sp_3072_to_mp(r, res);
    }


#ifdef WOLFSSL_SMALL_STACK
    if (d != NULL) {
        XMEMSET(e, 0, sizeof(sp_digit) * 27U);
        XFREE(d, NULL, DYNAMIC_TYPE_DH);
    }
#else
    XMEMSET(e, 0, sizeof(sp_digit) * 27U);
#endif

    return err;
#endif
}

#endif /* WOLFSSL_HAVE_SP_DH || (WOLFSSL_HAVE_SP_RSA && !WOLFSSL_RSA_PUBLIC_ONLY) */

#endif /* !WOLFSSL_SP_NO_3072 */

#ifdef WOLFSSL_SP_4096
/* Read big endian unsigned byte array into r.
 *
 * r  A single precision integer.
 * size  Maximum number of bytes to convert
 * a  Byte array.
 * n  Number of bytes in array to read.
 */
static void sp_4096_from_bin(sp_digit* r, int size, const byte* a, int n)
{
    int i, j = 0;
    word32 s = 0;

    r[0] = 0;
    for (i = n-1; i >= 0; i--) {
        r[j] |= (((sp_digit)a[i]) << s);
        if (s >= 45U) {
            r[j] &= 0x1fffffffffffffL;
            s = 53U - s;
            if (j + 1 >= size) {
                break;
            }
            r[++j] = (sp_digit)a[i] >> s;
            s = 8U - s;
        }
        else {
            s += 8U;
        }
    }

    for (j++; j < size; j++) {
        r[j] = 0;
    }
}

/* Convert an mp_int to an array of sp_digit.
 *
 * r  A single precision integer.
 * size  Maximum number of bytes to convert
 * a  A multi-precision integer.
 */
static void sp_4096_from_mp(sp_digit* r, int size, const mp_int* a)
{
#if DIGIT_BIT == 53
    int j;

    XMEMCPY(r, a->dp, sizeof(sp_digit) * a->used);

    for (j = a->used; j < size; j++) {
        r[j] = 0;
    }
#elif DIGIT_BIT > 53
    int i, j = 0;
    word32 s = 0;

    r[0] = 0;
    for (i = 0; i < a->used && j < size; i++) {
        r[j] |= ((sp_digit)a->dp[i] << s);
        r[j] &= 0x1fffffffffffffL;
        s = 53U - s;
        if (j + 1 >= size) {
            break;
        }
        /* lint allow cast of mismatch word32 and mp_digit */
        r[++j] = (sp_digit)(a->dp[i] >> s); /*lint !e9033*/
        while ((s + 53U) <= (word32)DIGIT_BIT) {
            s += 53U;
            r[j] &= 0x1fffffffffffffL;
            if (j + 1 >= size) {
                break;
            }
            if (s < (word32)DIGIT_BIT) {
                /* lint allow cast of mismatch word32 and mp_digit */
                r[++j] = (sp_digit)(a->dp[i] >> s); /*lint !e9033*/
            }
            else {
                r[++j] = 0L;
            }
        }
        s = (word32)DIGIT_BIT - s;
    }

    for (j++; j < size; j++) {
        r[j] = 0;
    }
#else
    int i, j = 0, s = 0;

    r[0] = 0;
    for (i = 0; i < a->used && j < size; i++) {
        r[j] |= ((sp_digit)a->dp[i]) << s;
        if (s + DIGIT_BIT >= 53) {
            r[j] &= 0x1fffffffffffffL;
            if (j + 1 >= size) {
                break;
            }
            s = 53 - s;
            if (s == DIGIT_BIT) {
                r[++j] = 0;
                s = 0;
            }
            else {
                r[++j] = a->dp[i] >> s;
                s = DIGIT_BIT - s;
            }
        }
        else {
            s += DIGIT_BIT;
        }
    }

    for (j++; j < size; j++) {
        r[j] = 0;
    }
#endif
}

/* Write r as big endian to byte array.
 * Fixed length number of bytes written: 512
 *
 * r  A single precision integer.
 * a  Byte array.
 */
static void sp_4096_to_bin(sp_digit* r, byte* a)
{
    int i, j, s = 0, b;

    for (i=0; i<77; i++) {
        r[i+1] += r[i] >> 53;
        r[i] &= 0x1fffffffffffffL;
    }
    j = 4096 / 8 - 1;
    a[j] = 0;
    for (i=0; i<78 && j>=0; i++) {
        b = 0;
        /* lint allow cast of mismatch sp_digit and int */
        a[j--] |= (byte)(r[i] << s); /*lint !e9033*/
        b += 8 - s;
        if (j < 0) {
            break;
        }
        while (b < 53) {
            a[j--] = (byte)(r[i] >> b);
            b += 8;
            if (j < 0) {
                break;
            }
        }
        s = 8 - (b - 53);
        if (j >= 0) {
            a[j] = 0;
        }
        if (s != 0) {
            j++;
        }
    }
}

#ifndef WOLFSSL_SP_SMALL
/* Multiply a and b into r. (r = a * b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A single precision integer.
 */
SP_NOINLINE static void sp_4096_mul_13(sp_digit* r, const sp_digit* a,
    const sp_digit* b)
{
    int128_t t0   = ((int128_t)a[ 0]) * b[ 0];
    int128_t t1   = ((int128_t)a[ 0]) * b[ 1]
                 + ((int128_t)a[ 1]) * b[ 0];
    int128_t t2   = ((int128_t)a[ 0]) * b[ 2]
                 + ((int128_t)a[ 1]) * b[ 1]
                 + ((int128_t)a[ 2]) * b[ 0];
    int128_t t3   = ((int128_t)a[ 0]) * b[ 3]
                 + ((int128_t)a[ 1]) * b[ 2]
                 + ((int128_t)a[ 2]) * b[ 1]
                 + ((int128_t)a[ 3]) * b[ 0];
    int128_t t4   = ((int128_t)a[ 0]) * b[ 4]
                 + ((int128_t)a[ 1]) * b[ 3]
                 + ((int128_t)a[ 2]) * b[ 2]
                 + ((int128_t)a[ 3]) * b[ 1]
                 + ((int128_t)a[ 4]) * b[ 0];
    int128_t t5   = ((int128_t)a[ 0]) * b[ 5]
                 + ((int128_t)a[ 1]) * b[ 4]
                 + ((int128_t)a[ 2]) * b[ 3]
                 + ((int128_t)a[ 3]) * b[ 2]
                 + ((int128_t)a[ 4]) * b[ 1]
                 + ((int128_t)a[ 5]) * b[ 0];
    int128_t t6   = ((int128_t)a[ 0]) * b[ 6]
                 + ((int128_t)a[ 1]) * b[ 5]
                 + ((int128_t)a[ 2]) * b[ 4]
                 + ((int128_t)a[ 3]) * b[ 3]
                 + ((int128_t)a[ 4]) * b[ 2]
                 + ((int128_t)a[ 5]) * b[ 1]
                 + ((int128_t)a[ 6]) * b[ 0];
    int128_t t7   = ((int128_t)a[ 0]) * b[ 7]
                 + ((int128_t)a[ 1]) * b[ 6]
                 + ((int128_t)a[ 2]) * b[ 5]
                 + ((int128_t)a[ 3]) * b[ 4]
                 + ((int128_t)a[ 4]) * b[ 3]
                 + ((int128_t)a[ 5]) * b[ 2]
                 + ((int128_t)a[ 6]) * b[ 1]
                 + ((int128_t)a[ 7]) * b[ 0];
    int128_t t8   = ((int128_t)a[ 0]) * b[ 8]
                 + ((int128_t)a[ 1]) * b[ 7]
                 + ((int128_t)a[ 2]) * b[ 6]
                 + ((int128_t)a[ 3]) * b[ 5]
                 + ((int128_t)a[ 4]) * b[ 4]
                 + ((int128_t)a[ 5]) * b[ 3]
                 + ((int128_t)a[ 6]) * b[ 2]
                 + ((int128_t)a[ 7]) * b[ 1]
                 + ((int128_t)a[ 8]) * b[ 0];
    int128_t t9   = ((int128_t)a[ 0]) * b[ 9]
                 + ((int128_t)a[ 1]) * b[ 8]
                 + ((int128_t)a[ 2]) * b[ 7]
                 + ((int128_t)a[ 3]) * b[ 6]
                 + ((int128_t)a[ 4]) * b[ 5]
                 + ((int128_t)a[ 5]) * b[ 4]
                 + ((int128_t)a[ 6]) * b[ 3]
                 + ((int128_t)a[ 7]) * b[ 2]
                 + ((int128_t)a[ 8]) * b[ 1]
                 + ((int128_t)a[ 9]) * b[ 0];
    int128_t t10  = ((int128_t)a[ 0]) * b[10]
                 + ((int128_t)a[ 1]) * b[ 9]
                 + ((int128_t)a[ 2]) * b[ 8]
                 + ((int128_t)a[ 3]) * b[ 7]
                 + ((int128_t)a[ 4]) * b[ 6]
                 + ((int128_t)a[ 5]) * b[ 5]
                 + ((int128_t)a[ 6]) * b[ 4]
                 + ((int128_t)a[ 7]) * b[ 3]
                 + ((int128_t)a[ 8]) * b[ 2]
                 + ((int128_t)a[ 9]) * b[ 1]
                 + ((int128_t)a[10]) * b[ 0];
    int128_t t11  = ((int128_t)a[ 0]) * b[11]
                 + ((int128_t)a[ 1]) * b[10]
                 + ((int128_t)a[ 2]) * b[ 9]
                 + ((int128_t)a[ 3]) * b[ 8]
                 + ((int128_t)a[ 4]) * b[ 7]
                 + ((int128_t)a[ 5]) * b[ 6]
                 + ((int128_t)a[ 6]) * b[ 5]
                 + ((int128_t)a[ 7]) * b[ 4]
                 + ((int128_t)a[ 8]) * b[ 3]
                 + ((int128_t)a[ 9]) * b[ 2]
                 + ((int128_t)a[10]) * b[ 1]
                 + ((int128_t)a[11]) * b[ 0];
    int128_t t12  = ((int128_t)a[ 0]) * b[12]
                 + ((int128_t)a[ 1]) * b[11]
                 + ((int128_t)a[ 2]) * b[10]
                 + ((int128_t)a[ 3]) * b[ 9]
                 + ((int128_t)a[ 4]) * b[ 8]
                 + ((int128_t)a[ 5]) * b[ 7]
                 + ((int128_t)a[ 6]) * b[ 6]
                 + ((int128_t)a[ 7]) * b[ 5]
                 + ((int128_t)a[ 8]) * b[ 4]
                 + ((int128_t)a[ 9]) * b[ 3]
                 + ((int128_t)a[10]) * b[ 2]
                 + ((int128_t)a[11]) * b[ 1]
                 + ((int128_t)a[12]) * b[ 0];
    int128_t t13  = ((int128_t)a[ 1]) * b[12]
                 + ((int128_t)a[ 2]) * b[11]
                 + ((int128_t)a[ 3]) * b[10]
                 + ((int128_t)a[ 4]) * b[ 9]
                 + ((int128_t)a[ 5]) * b[ 8]
                 + ((int128_t)a[ 6]) * b[ 7]
                 + ((int128_t)a[ 7]) * b[ 6]
                 + ((int128_t)a[ 8]) * b[ 5]
                 + ((int128_t)a[ 9]) * b[ 4]
                 + ((int128_t)a[10]) * b[ 3]
                 + ((int128_t)a[11]) * b[ 2]
                 + ((int128_t)a[12]) * b[ 1];
    int128_t t14  = ((int128_t)a[ 2]) * b[12]
                 + ((int128_t)a[ 3]) * b[11]
                 + ((int128_t)a[ 4]) * b[10]
                 + ((int128_t)a[ 5]) * b[ 9]
                 + ((int128_t)a[ 6]) * b[ 8]
                 + ((int128_t)a[ 7]) * b[ 7]
                 + ((int128_t)a[ 8]) * b[ 6]
                 + ((int128_t)a[ 9]) * b[ 5]
                 + ((int128_t)a[10]) * b[ 4]
                 + ((int128_t)a[11]) * b[ 3]
                 + ((int128_t)a[12]) * b[ 2];
    int128_t t15  = ((int128_t)a[ 3]) * b[12]
                 + ((int128_t)a[ 4]) * b[11]
                 + ((int128_t)a[ 5]) * b[10]
                 + ((int128_t)a[ 6]) * b[ 9]
                 + ((int128_t)a[ 7]) * b[ 8]
                 + ((int128_t)a[ 8]) * b[ 7]
                 + ((int128_t)a[ 9]) * b[ 6]
                 + ((int128_t)a[10]) * b[ 5]
                 + ((int128_t)a[11]) * b[ 4]
                 + ((int128_t)a[12]) * b[ 3];
    int128_t t16  = ((int128_t)a[ 4]) * b[12]
                 + ((int128_t)a[ 5]) * b[11]
                 + ((int128_t)a[ 6]) * b[10]
                 + ((int128_t)a[ 7]) * b[ 9]
                 + ((int128_t)a[ 8]) * b[ 8]
                 + ((int128_t)a[ 9]) * b[ 7]
                 + ((int128_t)a[10]) * b[ 6]
                 + ((int128_t)a[11]) * b[ 5]
                 + ((int128_t)a[12]) * b[ 4];
    int128_t t17  = ((int128_t)a[ 5]) * b[12]
                 + ((int128_t)a[ 6]) * b[11]
                 + ((int128_t)a[ 7]) * b[10]
                 + ((int128_t)a[ 8]) * b[ 9]
                 + ((int128_t)a[ 9]) * b[ 8]
                 + ((int128_t)a[10]) * b[ 7]
                 + ((int128_t)a[11]) * b[ 6]
                 + ((int128_t)a[12]) * b[ 5];
    int128_t t18  = ((int128_t)a[ 6]) * b[12]
                 + ((int128_t)a[ 7]) * b[11]
                 + ((int128_t)a[ 8]) * b[10]
                 + ((int128_t)a[ 9]) * b[ 9]
                 + ((int128_t)a[10]) * b[ 8]
                 + ((int128_t)a[11]) * b[ 7]
                 + ((int128_t)a[12]) * b[ 6];
    int128_t t19  = ((int128_t)a[ 7]) * b[12]
                 + ((int128_t)a[ 8]) * b[11]
                 + ((int128_t)a[ 9]) * b[10]
                 + ((int128_t)a[10]) * b[ 9]
                 + ((int128_t)a[11]) * b[ 8]
                 + ((int128_t)a[12]) * b[ 7];
    int128_t t20  = ((int128_t)a[ 8]) * b[12]
                 + ((int128_t)a[ 9]) * b[11]
                 + ((int128_t)a[10]) * b[10]
                 + ((int128_t)a[11]) * b[ 9]
                 + ((int128_t)a[12]) * b[ 8];
    int128_t t21  = ((int128_t)a[ 9]) * b[12]
                 + ((int128_t)a[10]) * b[11]
                 + ((int128_t)a[11]) * b[10]
                 + ((int128_t)a[12]) * b[ 9];
    int128_t t22  = ((int128_t)a[10]) * b[12]
                 + ((int128_t)a[11]) * b[11]
                 + ((int128_t)a[12]) * b[10];
    int128_t t23  = ((int128_t)a[11]) * b[12]
                 + ((int128_t)a[12]) * b[11];
    int128_t t24  = ((int128_t)a[12]) * b[12];

    t1   += t0  >> 53; r[ 0] = t0  & 0x1fffffffffffffL;
    t2   += t1  >> 53; r[ 1] = t1  & 0x1fffffffffffffL;
    t3   += t2  >> 53; r[ 2] = t2  & 0x1fffffffffffffL;
    t4   += t3  >> 53; r[ 3] = t3  & 0x1fffffffffffffL;
    t5   += t4  >> 53; r[ 4] = t4  & 0x1fffffffffffffL;
    t6   += t5  >> 53; r[ 5] = t5  & 0x1fffffffffffffL;
    t7   += t6  >> 53; r[ 6] = t6  & 0x1fffffffffffffL;
    t8   += t7  >> 53; r[ 7] = t7  & 0x1fffffffffffffL;
    t9   += t8  >> 53; r[ 8] = t8  & 0x1fffffffffffffL;
    t10  += t9  >> 53; r[ 9] = t9  & 0x1fffffffffffffL;
    t11  += t10 >> 53; r[10] = t10 & 0x1fffffffffffffL;
    t12  += t11 >> 53; r[11] = t11 & 0x1fffffffffffffL;
    t13  += t12 >> 53; r[12] = t12 & 0x1fffffffffffffL;
    t14  += t13 >> 53; r[13] = t13 & 0x1fffffffffffffL;
    t15  += t14 >> 53; r[14] = t14 & 0x1fffffffffffffL;
    t16  += t15 >> 53; r[15] = t15 & 0x1fffffffffffffL;
    t17  += t16 >> 53; r[16] = t16 & 0x1fffffffffffffL;
    t18  += t17 >> 53; r[17] = t17 & 0x1fffffffffffffL;
    t19  += t18 >> 53; r[18] = t18 & 0x1fffffffffffffL;
    t20  += t19 >> 53; r[19] = t19 & 0x1fffffffffffffL;
    t21  += t20 >> 53; r[20] = t20 & 0x1fffffffffffffL;
    t22  += t21 >> 53; r[21] = t21 & 0x1fffffffffffffL;
    t23  += t22 >> 53; r[22] = t22 & 0x1fffffffffffffL;
    t24  += t23 >> 53; r[23] = t23 & 0x1fffffffffffffL;
    r[25] = (sp_digit)(t24 >> 53);
                       r[24] = t24 & 0x1fffffffffffffL;
}

/* Square a and put result in r. (r = a * a)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 */
SP_NOINLINE static void sp_4096_sqr_13(sp_digit* r, const sp_digit* a)
{
    int128_t t0   =  ((int128_t)a[ 0]) * a[ 0];
    int128_t t1   = (((int128_t)a[ 0]) * a[ 1]) * 2;
    int128_t t2   = (((int128_t)a[ 0]) * a[ 2]) * 2
                 +  ((int128_t)a[ 1]) * a[ 1];
    int128_t t3   = (((int128_t)a[ 0]) * a[ 3]
                 +  ((int128_t)a[ 1]) * a[ 2]) * 2;
    int128_t t4   = (((int128_t)a[ 0]) * a[ 4]
                 +  ((int128_t)a[ 1]) * a[ 3]) * 2
                 +  ((int128_t)a[ 2]) * a[ 2];
    int128_t t5   = (((int128_t)a[ 0]) * a[ 5]
                 +  ((int128_t)a[ 1]) * a[ 4]
                 +  ((int128_t)a[ 2]) * a[ 3]) * 2;
    int128_t t6   = (((int128_t)a[ 0]) * a[ 6]
                 +  ((int128_t)a[ 1]) * a[ 5]
                 +  ((int128_t)a[ 2]) * a[ 4]) * 2
                 +  ((int128_t)a[ 3]) * a[ 3];
    int128_t t7   = (((int128_t)a[ 0]) * a[ 7]
                 +  ((int128_t)a[ 1]) * a[ 6]
                 +  ((int128_t)a[ 2]) * a[ 5]
                 +  ((int128_t)a[ 3]) * a[ 4]) * 2;
    int128_t t8   = (((int128_t)a[ 0]) * a[ 8]
                 +  ((int128_t)a[ 1]) * a[ 7]
                 +  ((int128_t)a[ 2]) * a[ 6]
                 +  ((int128_t)a[ 3]) * a[ 5]) * 2
                 +  ((int128_t)a[ 4]) * a[ 4];
    int128_t t9   = (((int128_t)a[ 0]) * a[ 9]
                 +  ((int128_t)a[ 1]) * a[ 8]
                 +  ((int128_t)a[ 2]) * a[ 7]
                 +  ((int128_t)a[ 3]) * a[ 6]
                 +  ((int128_t)a[ 4]) * a[ 5]) * 2;
    int128_t t10  = (((int128_t)a[ 0]) * a[10]
                 +  ((int128_t)a[ 1]) * a[ 9]
                 +  ((int128_t)a[ 2]) * a[ 8]
                 +  ((int128_t)a[ 3]) * a[ 7]
                 +  ((int128_t)a[ 4]) * a[ 6]) * 2
                 +  ((int128_t)a[ 5]) * a[ 5];
    int128_t t11  = (((int128_t)a[ 0]) * a[11]
                 +  ((int128_t)a[ 1]) * a[10]
                 +  ((int128_t)a[ 2]) * a[ 9]
                 +  ((int128_t)a[ 3]) * a[ 8]
                 +  ((int128_t)a[ 4]) * a[ 7]
                 +  ((int128_t)a[ 5]) * a[ 6]) * 2;
    int128_t t12  = (((int128_t)a[ 0]) * a[12]
                 +  ((int128_t)a[ 1]) * a[11]
                 +  ((int128_t)a[ 2]) * a[10]
                 +  ((int128_t)a[ 3]) * a[ 9]
                 +  ((int128_t)a[ 4]) * a[ 8]
                 +  ((int128_t)a[ 5]) * a[ 7]) * 2
                 +  ((int128_t)a[ 6]) * a[ 6];
    int128_t t13  = (((int128_t)a[ 1]) * a[12]
                 +  ((int128_t)a[ 2]) * a[11]
                 +  ((int128_t)a[ 3]) * a[10]
                 +  ((int128_t)a[ 4]) * a[ 9]
                 +  ((int128_t)a[ 5]) * a[ 8]
                 +  ((int128_t)a[ 6]) * a[ 7]) * 2;
    int128_t t14  = (((int128_t)a[ 2]) * a[12]
                 +  ((int128_t)a[ 3]) * a[11]
                 +  ((int128_t)a[ 4]) * a[10]
                 +  ((int128_t)a[ 5]) * a[ 9]
                 +  ((int128_t)a[ 6]) * a[ 8]) * 2
                 +  ((int128_t)a[ 7]) * a[ 7];
    int128_t t15  = (((int128_t)a[ 3]) * a[12]
                 +  ((int128_t)a[ 4]) * a[11]
                 +  ((int128_t)a[ 5]) * a[10]
                 +  ((int128_t)a[ 6]) * a[ 9]
                 +  ((int128_t)a[ 7]) * a[ 8]) * 2;
    int128_t t16  = (((int128_t)a[ 4]) * a[12]
                 +  ((int128_t)a[ 5]) * a[11]
                 +  ((int128_t)a[ 6]) * a[10]
                 +  ((int128_t)a[ 7]) * a[ 9]) * 2
                 +  ((int128_t)a[ 8]) * a[ 8];
    int128_t t17  = (((int128_t)a[ 5]) * a[12]
                 +  ((int128_t)a[ 6]) * a[11]
                 +  ((int128_t)a[ 7]) * a[10]
                 +  ((int128_t)a[ 8]) * a[ 9]) * 2;
    int128_t t18  = (((int128_t)a[ 6]) * a[12]
                 +  ((int128_t)a[ 7]) * a[11]
                 +  ((int128_t)a[ 8]) * a[10]) * 2
                 +  ((int128_t)a[ 9]) * a[ 9];
    int128_t t19  = (((int128_t)a[ 7]) * a[12]
                 +  ((int128_t)a[ 8]) * a[11]
                 +  ((int128_t)a[ 9]) * a[10]) * 2;
    int128_t t20  = (((int128_t)a[ 8]) * a[12]
                 +  ((int128_t)a[ 9]) * a[11]) * 2
                 +  ((int128_t)a[10]) * a[10];
    int128_t t21  = (((int128_t)a[ 9]) * a[12]
                 +  ((int128_t)a[10]) * a[11]) * 2;
    int128_t t22  = (((int128_t)a[10]) * a[12]) * 2
                 +  ((int128_t)a[11]) * a[11];
    int128_t t23  = (((int128_t)a[11]) * a[12]) * 2;
    int128_t t24  =  ((int128_t)a[12]) * a[12];

    t1   += t0  >> 53; r[ 0] = t0  & 0x1fffffffffffffL;
    t2   += t1  >> 53; r[ 1] = t1  & 0x1fffffffffffffL;
    t3   += t2  >> 53; r[ 2] = t2  & 0x1fffffffffffffL;
    t4   += t3  >> 53; r[ 3] = t3  & 0x1fffffffffffffL;
    t5   += t4  >> 53; r[ 4] = t4  & 0x1fffffffffffffL;
    t6   += t5  >> 53; r[ 5] = t5  & 0x1fffffffffffffL;
    t7   += t6  >> 53; r[ 6] = t6  & 0x1fffffffffffffL;
    t8   += t7  >> 53; r[ 7] = t7  & 0x1fffffffffffffL;
    t9   += t8  >> 53; r[ 8] = t8  & 0x1fffffffffffffL;
    t10  += t9  >> 53; r[ 9] = t9  & 0x1fffffffffffffL;
    t11  += t10 >> 53; r[10] = t10 & 0x1fffffffffffffL;
    t12  += t11 >> 53; r[11] = t11 & 0x1fffffffffffffL;
    t13  += t12 >> 53; r[12] = t12 & 0x1fffffffffffffL;
    t14  += t13 >> 53; r[13] = t13 & 0x1fffffffffffffL;
    t15  += t14 >> 53; r[14] = t14 & 0x1fffffffffffffL;
    t16  += t15 >> 53; r[15] = t15 & 0x1fffffffffffffL;
    t17  += t16 >> 53; r[16] = t16 & 0x1fffffffffffffL;
    t18  += t17 >> 53; r[17] = t17 & 0x1fffffffffffffL;
    t19  += t18 >> 53; r[18] = t18 & 0x1fffffffffffffL;
    t20  += t19 >> 53; r[19] = t19 & 0x1fffffffffffffL;
    t21  += t20 >> 53; r[20] = t20 & 0x1fffffffffffffL;
    t22  += t21 >> 53; r[21] = t21 & 0x1fffffffffffffL;
    t23  += t22 >> 53; r[22] = t22 & 0x1fffffffffffffL;
    t24  += t23 >> 53; r[23] = t23 & 0x1fffffffffffffL;
    r[25] = (sp_digit)(t24 >> 53);
                       r[24] = t24 & 0x1fffffffffffffL;
}

/* Add b to a into r. (r = a + b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A single precision integer.
 */
SP_NOINLINE static int sp_4096_add_13(sp_digit* r, const sp_digit* a,
        const sp_digit* b)
{
    r[ 0] = a[ 0] + b[ 0];
    r[ 1] = a[ 1] + b[ 1];
    r[ 2] = a[ 2] + b[ 2];
    r[ 3] = a[ 3] + b[ 3];
    r[ 4] = a[ 4] + b[ 4];
    r[ 5] = a[ 5] + b[ 5];
    r[ 6] = a[ 6] + b[ 6];
    r[ 7] = a[ 7] + b[ 7];
    r[ 8] = a[ 8] + b[ 8];
    r[ 9] = a[ 9] + b[ 9];
    r[10] = a[10] + b[10];
    r[11] = a[11] + b[11];
    r[12] = a[12] + b[12];

    return 0;
}

/* Sub b from a into r. (r = a - b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A single precision integer.
 */
SP_NOINLINE static int sp_4096_sub_26(sp_digit* r, const sp_digit* a,
        const sp_digit* b)
{
    int i;

    for (i = 0; i < 24; i += 8) {
        r[i + 0] = a[i + 0] - b[i + 0];
        r[i + 1] = a[i + 1] - b[i + 1];
        r[i + 2] = a[i + 2] - b[i + 2];
        r[i + 3] = a[i + 3] - b[i + 3];
        r[i + 4] = a[i + 4] - b[i + 4];
        r[i + 5] = a[i + 5] - b[i + 5];
        r[i + 6] = a[i + 6] - b[i + 6];
        r[i + 7] = a[i + 7] - b[i + 7];
    }
    r[24] = a[24] - b[24];
    r[25] = a[25] - b[25];

    return 0;
}

/* Add b to a into r. (r = a + b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A single precision integer.
 */
SP_NOINLINE static int sp_4096_add_26(sp_digit* r, const sp_digit* a,
        const sp_digit* b)
{
    int i;

    for (i = 0; i < 24; i += 8) {
        r[i + 0] = a[i + 0] + b[i + 0];
        r[i + 1] = a[i + 1] + b[i + 1];
        r[i + 2] = a[i + 2] + b[i + 2];
        r[i + 3] = a[i + 3] + b[i + 3];
        r[i + 4] = a[i + 4] + b[i + 4];
        r[i + 5] = a[i + 5] + b[i + 5];
        r[i + 6] = a[i + 6] + b[i + 6];
        r[i + 7] = a[i + 7] + b[i + 7];
    }
    r[24] = a[24] + b[24];
    r[25] = a[25] + b[25];

    return 0;
}

/* Multiply a and b into r. (r = a * b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A single precision integer.
 */
SP_NOINLINE static void sp_4096_mul_39(sp_digit* r, const sp_digit* a,
    const sp_digit* b)
{
    sp_digit p0[26];
    sp_digit p1[26];
    sp_digit p2[26];
    sp_digit p3[26];
    sp_digit p4[26];
    sp_digit p5[26];
    sp_digit t0[26];
    sp_digit t1[26];
    sp_digit t2[26];
    sp_digit a0[13];
    sp_digit a1[13];
    sp_digit a2[13];
    sp_digit b0[13];
    sp_digit b1[13];
    sp_digit b2[13];
    (void)sp_4096_add_13(a0, a, &a[13]);
    (void)sp_4096_add_13(b0, b, &b[13]);
    (void)sp_4096_add_13(a1, &a[13], &a[26]);
    (void)sp_4096_add_13(b1, &b[13], &b[26]);
    (void)sp_4096_add_13(a2, a0, &a[26]);
    (void)sp_4096_add_13(b2, b0, &b[26]);
    sp_4096_mul_13(p0, a, b);
    sp_4096_mul_13(p2, &a[13], &b[13]);
    sp_4096_mul_13(p4, &a[26], &b[26]);
    sp_4096_mul_13(p1, a0, b0);
    sp_4096_mul_13(p3, a1, b1);
    sp_4096_mul_13(p5, a2, b2);
    XMEMSET(r, 0, sizeof(*r)*2U*39U);
    (void)sp_4096_sub_26(t0, p3, p2);
    (void)sp_4096_sub_26(t1, p1, p2);
    (void)sp_4096_sub_26(t2, p5, t0);
    (void)sp_4096_sub_26(t2, t2, t1);
    (void)sp_4096_sub_26(t0, t0, p4);
    (void)sp_4096_sub_26(t1, t1, p0);
    (void)sp_4096_add_26(r, r, p0);
    (void)sp_4096_add_26(&r[13], &r[13], t1);
    (void)sp_4096_add_26(&r[26], &r[26], t2);
    (void)sp_4096_add_26(&r[39], &r[39], t0);
    (void)sp_4096_add_26(&r[52], &r[52], p4);
}

/* Square a into r. (r = a * a)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 */
SP_NOINLINE static void sp_4096_sqr_39(sp_digit* r, const sp_digit* a)
{
    sp_digit p0[26];
    sp_digit p1[26];
    sp_digit p2[26];
    sp_digit p3[26];
    sp_digit p4[26];
    sp_digit p5[26];
    sp_digit t0[26];
    sp_digit t1[26];
    sp_digit t2[26];
    sp_digit a0[13];
    sp_digit a1[13];
    sp_digit a2[13];
    (void)sp_4096_add_13(a0, a, &a[13]);
    (void)sp_4096_add_13(a1, &a[13], &a[26]);
    (void)sp_4096_add_13(a2, a0, &a[26]);
    sp_4096_sqr_13(p0, a);
    sp_4096_sqr_13(p2, &a[13]);
    sp_4096_sqr_13(p4, &a[26]);
    sp_4096_sqr_13(p1, a0);
    sp_4096_sqr_13(p3, a1);
    sp_4096_sqr_13(p5, a2);
    XMEMSET(r, 0, sizeof(*r)*2U*39U);
    (void)sp_4096_sub_26(t0, p3, p2);
    (void)sp_4096_sub_26(t1, p1, p2);
    (void)sp_4096_sub_26(t2, p5, t0);
    (void)sp_4096_sub_26(t2, t2, t1);
    (void)sp_4096_sub_26(t0, t0, p4);
    (void)sp_4096_sub_26(t1, t1, p0);
    (void)sp_4096_add_26(r, r, p0);
    (void)sp_4096_add_26(&r[13], &r[13], t1);
    (void)sp_4096_add_26(&r[26], &r[26], t2);
    (void)sp_4096_add_26(&r[39], &r[39], t0);
    (void)sp_4096_add_26(&r[52], &r[52], p4);
}

/* Add b to a into r. (r = a + b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A single precision integer.
 */
SP_NOINLINE static int sp_4096_add_39(sp_digit* r, const sp_digit* a,
        const sp_digit* b)
{
    int i;

    for (i = 0; i < 32; i += 8) {
        r[i + 0] = a[i + 0] + b[i + 0];
        r[i + 1] = a[i + 1] + b[i + 1];
        r[i + 2] = a[i + 2] + b[i + 2];
        r[i + 3] = a[i + 3] + b[i + 3];
        r[i + 4] = a[i + 4] + b[i + 4];
        r[i + 5] = a[i + 5] + b[i + 5];
        r[i + 6] = a[i + 6] + b[i + 6];
        r[i + 7] = a[i + 7] + b[i + 7];
    }
    r[32] = a[32] + b[32];
    r[33] = a[33] + b[33];
    r[34] = a[34] + b[34];
    r[35] = a[35] + b[35];
    r[36] = a[36] + b[36];
    r[37] = a[37] + b[37];
    r[38] = a[38] + b[38];

    return 0;
}

/* Add b to a into r. (r = a + b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A single precision integer.
 */
SP_NOINLINE static int sp_4096_add_78(sp_digit* r, const sp_digit* a,
        const sp_digit* b)
{
    int i;

    for (i = 0; i < 72; i += 8) {
        r[i + 0] = a[i + 0] + b[i + 0];
        r[i + 1] = a[i + 1] + b[i + 1];
        r[i + 2] = a[i + 2] + b[i + 2];
        r[i + 3] = a[i + 3] + b[i + 3];
        r[i + 4] = a[i + 4] + b[i + 4];
        r[i + 5] = a[i + 5] + b[i + 5];
        r[i + 6] = a[i + 6] + b[i + 6];
        r[i + 7] = a[i + 7] + b[i + 7];
    }
    r[72] = a[72] + b[72];
    r[73] = a[73] + b[73];
    r[74] = a[74] + b[74];
    r[75] = a[75] + b[75];
    r[76] = a[76] + b[76];
    r[77] = a[77] + b[77];

    return 0;
}

/* Sub b from a into r. (r = a - b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A single precision integer.
 */
SP_NOINLINE static int sp_4096_sub_78(sp_digit* r, const sp_digit* a,
        const sp_digit* b)
{
    int i;

    for (i = 0; i < 72; i += 8) {
        r[i + 0] = a[i + 0] - b[i + 0];
        r[i + 1] = a[i + 1] - b[i + 1];
        r[i + 2] = a[i + 2] - b[i + 2];
        r[i + 3] = a[i + 3] - b[i + 3];
        r[i + 4] = a[i + 4] - b[i + 4];
        r[i + 5] = a[i + 5] - b[i + 5];
        r[i + 6] = a[i + 6] - b[i + 6];
        r[i + 7] = a[i + 7] - b[i + 7];
    }
    r[72] = a[72] - b[72];
    r[73] = a[73] - b[73];
    r[74] = a[74] - b[74];
    r[75] = a[75] - b[75];
    r[76] = a[76] - b[76];
    r[77] = a[77] - b[77];

    return 0;
}

/* Multiply a and b into r. (r = a * b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A single precision integer.
 */
SP_NOINLINE static void sp_4096_mul_78(sp_digit* r, const sp_digit* a,
    const sp_digit* b)
{
    sp_digit* z0 = r;
    sp_digit z1[78];
    sp_digit* a1 = z1;
    sp_digit b1[39];
    sp_digit* z2 = r + 78;
    (void)sp_4096_add_39(a1, a, &a[39]);
    (void)sp_4096_add_39(b1, b, &b[39]);
    sp_4096_mul_39(z2, &a[39], &b[39]);
    sp_4096_mul_39(z0, a, b);
    sp_4096_mul_39(z1, a1, b1);
    (void)sp_4096_sub_78(z1, z1, z2);
    (void)sp_4096_sub_78(z1, z1, z0);
    (void)sp_4096_add_78(r + 39, r + 39, z1);
}

/* Square a and put result in r. (r = a * a)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 */
SP_NOINLINE static void sp_4096_sqr_78(sp_digit* r, const sp_digit* a)
{
    sp_digit* z0 = r;
    sp_digit z1[78];
    sp_digit* a1 = z1;
    sp_digit* z2 = r + 78;
    (void)sp_4096_add_39(a1, a, &a[39]);
    sp_4096_sqr_39(z2, &a[39]);
    sp_4096_sqr_39(z0, a);
    sp_4096_sqr_39(z1, a1);
    (void)sp_4096_sub_78(z1, z1, z2);
    (void)sp_4096_sub_78(z1, z1, z0);
    (void)sp_4096_add_78(r + 39, r + 39, z1);
}

#endif /* !WOLFSSL_SP_SMALL */
#ifdef WOLFSSL_SP_SMALL
/* Add b to a into r. (r = a + b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A single precision integer.
 */
SP_NOINLINE static int sp_4096_add_78(sp_digit* r, const sp_digit* a,
        const sp_digit* b)
{
    int i;

    for (i = 0; i < 78; i++) {
        r[i] = a[i] + b[i];
    }

    return 0;
}
#endif /* WOLFSSL_SP_SMALL */
#ifdef WOLFSSL_SP_SMALL
/* Sub b from a into r. (r = a - b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A single precision integer.
 */
SP_NOINLINE static int sp_4096_sub_78(sp_digit* r, const sp_digit* a,
        const sp_digit* b)
{
    int i;

    for (i = 0; i < 78; i++) {
        r[i] = a[i] - b[i];
    }

    return 0;
}

#endif /* WOLFSSL_SP_SMALL */
#ifdef WOLFSSL_SP_SMALL
/* Multiply a and b into r. (r = a * b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A single precision integer.
 */
SP_NOINLINE static void sp_4096_mul_78(sp_digit* r, const sp_digit* a,
    const sp_digit* b)
{
    int i, j, k;
    int128_t c;

    c = ((int128_t)a[77]) * b[77];
    r[155] = (sp_digit)(c >> 53);
    c = (c & 0x1fffffffffffffL) << 53;
    for (k = 153; k >= 0; k--) {
        for (i = 77; i >= 0; i--) {
            j = k - i;
            if (j >= 78) {
                break;
            }
            if (j < 0) {
                continue;
            }

            c += ((int128_t)a[i]) * b[j];
        }
        r[k + 2] += c >> 106;
        r[k + 1] = (c >> 53) & 0x1fffffffffffffL;
        c = (c & 0x1fffffffffffffL) << 53;
    }
    r[0] = (sp_digit)(c >> 53);
}

/* Square a and put result in r. (r = a * a)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 */
SP_NOINLINE static void sp_4096_sqr_78(sp_digit* r, const sp_digit* a)
{
    int i, j, k;
    int128_t c;

    c = ((int128_t)a[77]) * a[77];
    r[155] = (sp_digit)(c >> 53);
    c = (c & 0x1fffffffffffffL) << 53;
    for (k = 153; k >= 0; k--) {
        for (i = 77; i >= 0; i--) {
            j = k - i;
            if (j >= 78 || i <= j) {
                break;
            }
            if (j < 0) {
                continue;
            }

            c += ((int128_t)a[i]) * a[j] * 2;
        }
        if (i == j) {
           c += ((int128_t)a[i]) * a[i];
        }

        r[k + 2] += c >> 106;
        r[k + 1] = (c >> 53) & 0x1fffffffffffffL;
        c = (c & 0x1fffffffffffffL) << 53;
    }
    r[0] = (sp_digit)(c >> 53);
}

#endif /* WOLFSSL_SP_SMALL */
#if (defined(WOLFSSL_HAVE_SP_RSA) || defined(WOLFSSL_HAVE_SP_DH)) && !defined(WOLFSSL_RSA_PUBLIC_ONLY)
#if defined(WOLFSSL_HAVE_SP_RSA) && !defined(SP_RSA_PRIVATE_EXP_D)
#ifdef WOLFSSL_SP_SMALL
/* Add b to a into r. (r = a + b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A single precision integer.
 */
SP_NOINLINE static int sp_4096_add_39(sp_digit* r, const sp_digit* a,
        const sp_digit* b)
{
    int i;

    for (i = 0; i < 39; i++) {
        r[i] = a[i] + b[i];
    }

    return 0;
}
#endif /* WOLFSSL_SP_SMALL */
#ifdef WOLFSSL_SP_SMALL
/* Sub b from a into r. (r = a - b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A single precision integer.
 */
SP_NOINLINE static int sp_4096_sub_39(sp_digit* r, const sp_digit* a,
        const sp_digit* b)
{
    int i;

    for (i = 0; i < 39; i++) {
        r[i] = a[i] - b[i];
    }

    return 0;
}

#else
/* Sub b from a into r. (r = a - b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A single precision integer.
 */
SP_NOINLINE static int sp_4096_sub_39(sp_digit* r, const sp_digit* a,
        const sp_digit* b)
{
    int i;

    for (i = 0; i < 32; i += 8) {
        r[i + 0] = a[i + 0] - b[i + 0];
        r[i + 1] = a[i + 1] - b[i + 1];
        r[i + 2] = a[i + 2] - b[i + 2];
        r[i + 3] = a[i + 3] - b[i + 3];
        r[i + 4] = a[i + 4] - b[i + 4];
        r[i + 5] = a[i + 5] - b[i + 5];
        r[i + 6] = a[i + 6] - b[i + 6];
        r[i + 7] = a[i + 7] - b[i + 7];
    }
    r[32] = a[32] - b[32];
    r[33] = a[33] - b[33];
    r[34] = a[34] - b[34];
    r[35] = a[35] - b[35];
    r[36] = a[36] - b[36];
    r[37] = a[37] - b[37];
    r[38] = a[38] - b[38];

    return 0;
}

#endif /* WOLFSSL_SP_SMALL */
#ifdef WOLFSSL_SP_SMALL
/* Multiply a and b into r. (r = a * b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A single precision integer.
 */
SP_NOINLINE static void sp_4096_mul_39(sp_digit* r, const sp_digit* a,
    const sp_digit* b)
{
    int i, j, k;
    int128_t c;

    c = ((int128_t)a[38]) * b[38];
    r[77] = (sp_digit)(c >> 53);
    c = (c & 0x1fffffffffffffL) << 53;
    for (k = 75; k >= 0; k--) {
        for (i = 38; i >= 0; i--) {
            j = k - i;
            if (j >= 39) {
                break;
            }
            if (j < 0) {
                continue;
            }

            c += ((int128_t)a[i]) * b[j];
        }
        r[k + 2] += c >> 106;
        r[k + 1] = (c >> 53) & 0x1fffffffffffffL;
        c = (c & 0x1fffffffffffffL) << 53;
    }
    r[0] = (sp_digit)(c >> 53);
}

/* Square a and put result in r. (r = a * a)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 */
SP_NOINLINE static void sp_4096_sqr_39(sp_digit* r, const sp_digit* a)
{
    int i, j, k;
    int128_t c;

    c = ((int128_t)a[38]) * a[38];
    r[77] = (sp_digit)(c >> 53);
    c = (c & 0x1fffffffffffffL) << 53;
    for (k = 75; k >= 0; k--) {
        for (i = 38; i >= 0; i--) {
            j = k - i;
            if (j >= 39 || i <= j) {
                break;
            }
            if (j < 0) {
                continue;
            }

            c += ((int128_t)a[i]) * a[j] * 2;
        }
        if (i == j) {
           c += ((int128_t)a[i]) * a[i];
        }

        r[k + 2] += c >> 106;
        r[k + 1] = (c >> 53) & 0x1fffffffffffffL;
        c = (c & 0x1fffffffffffffL) << 53;
    }
    r[0] = (sp_digit)(c >> 53);
}

#endif /* WOLFSSL_SP_SMALL */
#endif /* WOLFSSL_HAVE_SP_RSA && !SP_RSA_PRIVATE_EXP_D */
#endif /* (WOLFSSL_HAVE_SP_RSA || WOLFSSL_HAVE_SP_DH) && !WOLFSSL_RSA_PUBLIC_ONLY */

/* Caclulate the bottom digit of -1/a mod 2^n.
 *
 * a    A single precision number.
 * rho  Bottom word of inverse.
 */
static void sp_4096_mont_setup(const sp_digit* a, sp_digit* rho)
{
    sp_digit x, b;

    b = a[0];
    x = (((b + 2) & 4) << 1) + b; /* here x*a==1 mod 2**4 */
    x *= 2 - b * x;               /* here x*a==1 mod 2**8 */
    x *= 2 - b * x;               /* here x*a==1 mod 2**16 */
    x *= 2 - b * x;               /* here x*a==1 mod 2**32 */
    x *= 2 - b * x;               /* here x*a==1 mod 2**64 */
    x &= 0x1fffffffffffffL;

    /* rho = -1/m mod b */
    *rho = (1L << 53) - x;
}

/* Multiply a by scalar b into r. (r = a * b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A scalar.
 */
SP_NOINLINE static void sp_4096_mul_d_78(sp_digit* r, const sp_digit* a,
    sp_digit b)
{
#ifdef WOLFSSL_SP_SMALL
    int128_t tb = b;
    int128_t t = 0;
    int i;

    for (i = 0; i < 78; i++) {
        t += tb * a[i];
        r[i] = t & 0x1fffffffffffffL;
        t >>= 53;
    }
    r[78] = (sp_digit)t;
#else
    int128_t tb = b;
    int128_t t[8];
    int i;

    t[0] = tb * a[0]; r[0] = t[0] & 0x1fffffffffffffL;
    for (i = 0; i < 72; i += 8) {
        t[1] = tb * a[i+1];
        r[i+1] = (sp_digit)(t[0] >> 53) + (t[1] & 0x1fffffffffffffL);
        t[2] = tb * a[i+2];
        r[i+2] = (sp_digit)(t[1] >> 53) + (t[2] & 0x1fffffffffffffL);
        t[3] = tb * a[i+3];
        r[i+3] = (sp_digit)(t[2] >> 53) + (t[3] & 0x1fffffffffffffL);
        t[4] = tb * a[i+4];
        r[i+4] = (sp_digit)(t[3] >> 53) + (t[4] & 0x1fffffffffffffL);
        t[5] = tb * a[i+5];
        r[i+5] = (sp_digit)(t[4] >> 53) + (t[5] & 0x1fffffffffffffL);
        t[6] = tb * a[i+6];
        r[i+6] = (sp_digit)(t[5] >> 53) + (t[6] & 0x1fffffffffffffL);
        t[7] = tb * a[i+7];
        r[i+7] = (sp_digit)(t[6] >> 53) + (t[7] & 0x1fffffffffffffL);
        t[0] = tb * a[i+8];
        r[i+8] = (sp_digit)(t[7] >> 53) + (t[0] & 0x1fffffffffffffL);
    }
    t[1] = tb * a[73];
    r[73] = (sp_digit)(t[0] >> 53) + (t[1] & 0x1fffffffffffffL);
    t[2] = tb * a[74];
    r[74] = (sp_digit)(t[1] >> 53) + (t[2] & 0x1fffffffffffffL);
    t[3] = tb * a[75];
    r[75] = (sp_digit)(t[2] >> 53) + (t[3] & 0x1fffffffffffffL);
    t[4] = tb * a[76];
    r[76] = (sp_digit)(t[3] >> 53) + (t[4] & 0x1fffffffffffffL);
    t[5] = tb * a[77];
    r[77] = (sp_digit)(t[4] >> 53) + (t[5] & 0x1fffffffffffffL);
    r[78] =  (sp_digit)(t[5] >> 53);
#endif /* WOLFSSL_SP_SMALL */
}

#if (defined(WOLFSSL_HAVE_SP_RSA) || defined(WOLFSSL_HAVE_SP_DH)) && !defined(WOLFSSL_RSA_PUBLIC_ONLY)
#if defined(WOLFSSL_HAVE_SP_RSA) && !defined(SP_RSA_PRIVATE_EXP_D)
/* r = 2^n mod m where n is the number of bits to reduce by.
 * Given m must be 4096 bits, just need to subtract.
 *
 * r  A single precision number.
 * m  A single precision number.
 */
static void sp_4096_mont_norm_39(sp_digit* r, const sp_digit* m)
{
    /* Set r = 2^n - 1. */
#ifdef WOLFSSL_SP_SMALL
    int i;

    for (i=0; i<38; i++) {
        r[i] = 0x1fffffffffffffL;
    }
#else
    int i;

    for (i = 0; i < 32; i += 8) {
        r[i + 0] = 0x1fffffffffffffL;
        r[i + 1] = 0x1fffffffffffffL;
        r[i + 2] = 0x1fffffffffffffL;
        r[i + 3] = 0x1fffffffffffffL;
        r[i + 4] = 0x1fffffffffffffL;
        r[i + 5] = 0x1fffffffffffffL;
        r[i + 6] = 0x1fffffffffffffL;
        r[i + 7] = 0x1fffffffffffffL;
    }
    r[32] = 0x1fffffffffffffL;
    r[33] = 0x1fffffffffffffL;
    r[34] = 0x1fffffffffffffL;
    r[35] = 0x1fffffffffffffL;
    r[36] = 0x1fffffffffffffL;
    r[37] = 0x1fffffffffffffL;
#endif
    r[38] = 0x3ffffffffL;

    /* r = (2^n - 1) mod n */
    (void)sp_4096_sub_39(r, r, m);

    /* Add one so r = 2^n mod m */
    r[0] += 1;
}

/* Compare a with b in constant time.
 *
 * a  A single precision integer.
 * b  A single precision integer.
 * return -ve, 0 or +ve if a is less than, equal to or greater than b
 * respectively.
 */
static sp_digit sp_4096_cmp_39(const sp_digit* a, const sp_digit* b)
{
    sp_digit r = 0;
#ifdef WOLFSSL_SP_SMALL
    int i;

    for (i=38; i>=0; i--) {
        r |= (a[i] - b[i]) & (0 - ((r == 0) ? (sp_digit)1 : (sp_digit)0));
    }
#else
    int i;

    r |= (a[38] - b[38]) & (0 - ((r == 0) ? (sp_digit)1 : (sp_digit)0));
    r |= (a[37] - b[37]) & (0 - ((r == 0) ? (sp_digit)1 : (sp_digit)0));
    r |= (a[36] - b[36]) & (0 - ((r == 0) ? (sp_digit)1 : (sp_digit)0));
    r |= (a[35] - b[35]) & (0 - ((r == 0) ? (sp_digit)1 : (sp_digit)0));
    r |= (a[34] - b[34]) & (0 - ((r == 0) ? (sp_digit)1 : (sp_digit)0));
    r |= (a[33] - b[33]) & (0 - ((r == 0) ? (sp_digit)1 : (sp_digit)0));
    r |= (a[32] - b[32]) & (0 - ((r == 0) ? (sp_digit)1 : (sp_digit)0));
    for (i = 24; i >= 0; i -= 8) {
        r |= (a[i + 7] - b[i + 7]) & (0 - ((r == 0) ? (sp_digit)1 : (sp_digit)0));
        r |= (a[i + 6] - b[i + 6]) & (0 - ((r == 0) ? (sp_digit)1 : (sp_digit)0));
        r |= (a[i + 5] - b[i + 5]) & (0 - ((r == 0) ? (sp_digit)1 : (sp_digit)0));
        r |= (a[i + 4] - b[i + 4]) & (0 - ((r == 0) ? (sp_digit)1 : (sp_digit)0));
        r |= (a[i + 3] - b[i + 3]) & (0 - ((r == 0) ? (sp_digit)1 : (sp_digit)0));
        r |= (a[i + 2] - b[i + 2]) & (0 - ((r == 0) ? (sp_digit)1 : (sp_digit)0));
        r |= (a[i + 1] - b[i + 1]) & (0 - ((r == 0) ? (sp_digit)1 : (sp_digit)0));
        r |= (a[i + 0] - b[i + 0]) & (0 - ((r == 0) ? (sp_digit)1 : (sp_digit)0));
    }
#endif /* WOLFSSL_SP_SMALL */

    return r;
}

/* Conditionally subtract b from a using the mask m.
 * m is -1 to subtract and 0 when not.
 *
 * r  A single precision number representing condition subtract result.
 * a  A single precision number to subtract from.
 * b  A single precision number to subtract.
 * m  Mask value to apply.
 */
static void sp_4096_cond_sub_39(sp_digit* r, const sp_digit* a,
        const sp_digit* b, const sp_digit m)
{
#ifdef WOLFSSL_SP_SMALL
    int i;

    for (i = 0; i < 39; i++) {
        r[i] = a[i] - (b[i] & m);
    }
#else
    int i;

    for (i = 0; i < 32; i += 8) {
        r[i + 0] = a[i + 0] - (b[i + 0] & m);
        r[i + 1] = a[i + 1] - (b[i + 1] & m);
        r[i + 2] = a[i + 2] - (b[i + 2] & m);
        r[i + 3] = a[i + 3] - (b[i + 3] & m);
        r[i + 4] = a[i + 4] - (b[i + 4] & m);
        r[i + 5] = a[i + 5] - (b[i + 5] & m);
        r[i + 6] = a[i + 6] - (b[i + 6] & m);
        r[i + 7] = a[i + 7] - (b[i + 7] & m);
    }
    r[32] = a[32] - (b[32] & m);
    r[33] = a[33] - (b[33] & m);
    r[34] = a[34] - (b[34] & m);
    r[35] = a[35] - (b[35] & m);
    r[36] = a[36] - (b[36] & m);
    r[37] = a[37] - (b[37] & m);
    r[38] = a[38] - (b[38] & m);
#endif /* WOLFSSL_SP_SMALL */
}

/* Mul a by scalar b and add into r. (r += a * b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A scalar.
 */
SP_NOINLINE static void sp_4096_mul_add_39(sp_digit* r, const sp_digit* a,
        const sp_digit b)
{
#ifdef WOLFSSL_SP_SMALL
    int128_t tb = b;
    int128_t t = 0;
    int i;

    for (i = 0; i < 39; i++) {
        t += (tb * a[i]) + r[i];
        r[i] = t & 0x1fffffffffffffL;
        t >>= 53;
    }
    r[39] += t;
#else
    int128_t tb = b;
    int128_t t[8];
    int i;

    t[0] = tb * a[0]; r[0] += (sp_digit)(t[0] & 0x1fffffffffffffL);
    for (i = 0; i < 32; i += 8) {
        t[1] = tb * a[i+1];
        r[i+1] += (sp_digit)((t[0] >> 53) + (t[1] & 0x1fffffffffffffL));
        t[2] = tb * a[i+2];
        r[i+2] += (sp_digit)((t[1] >> 53) + (t[2] & 0x1fffffffffffffL));
        t[3] = tb * a[i+3];
        r[i+3] += (sp_digit)((t[2] >> 53) + (t[3] & 0x1fffffffffffffL));
        t[4] = tb * a[i+4];
        r[i+4] += (sp_digit)((t[3] >> 53) + (t[4] & 0x1fffffffffffffL));
        t[5] = tb * a[i+5];
        r[i+5] += (sp_digit)((t[4] >> 53) + (t[5] & 0x1fffffffffffffL));
        t[6] = tb * a[i+6];
        r[i+6] += (sp_digit)((t[5] >> 53) + (t[6] & 0x1fffffffffffffL));
        t[7] = tb * a[i+7];
        r[i+7] += (sp_digit)((t[6] >> 53) + (t[7] & 0x1fffffffffffffL));
        t[0] = tb * a[i+8];
        r[i+8] += (sp_digit)((t[7] >> 53) + (t[0] & 0x1fffffffffffffL));
    }
    t[1] = tb * a[33]; r[33] += (sp_digit)((t[0] >> 53) + (t[1] & 0x1fffffffffffffL));
    t[2] = tb * a[34]; r[34] += (sp_digit)((t[1] >> 53) + (t[2] & 0x1fffffffffffffL));
    t[3] = tb * a[35]; r[35] += (sp_digit)((t[2] >> 53) + (t[3] & 0x1fffffffffffffL));
    t[4] = tb * a[36]; r[36] += (sp_digit)((t[3] >> 53) + (t[4] & 0x1fffffffffffffL));
    t[5] = tb * a[37]; r[37] += (sp_digit)((t[4] >> 53) + (t[5] & 0x1fffffffffffffL));
    t[6] = tb * a[38]; r[38] += (sp_digit)((t[5] >> 53) + (t[6] & 0x1fffffffffffffL));
    r[39] +=  (sp_digit)(t[6] >> 53);
#endif /* WOLFSSL_SP_SMALL */
}

/* Normalize the values in each word to 53.
 *
 * a  Array of sp_digit to normalize.
 */
static void sp_4096_norm_39(sp_digit* a)
{
#ifdef WOLFSSL_SP_SMALL
    int i;
    for (i = 0; i < 38; i++) {
        a[i+1] += a[i] >> 53;
        a[i] &= 0x1fffffffffffffL;
    }
#else
    int i;
    for (i = 0; i < 32; i += 8) {
        a[i+1] += a[i+0] >> 53; a[i+0] &= 0x1fffffffffffffL;
        a[i+2] += a[i+1] >> 53; a[i+1] &= 0x1fffffffffffffL;
        a[i+3] += a[i+2] >> 53; a[i+2] &= 0x1fffffffffffffL;
        a[i+4] += a[i+3] >> 53; a[i+3] &= 0x1fffffffffffffL;
        a[i+5] += a[i+4] >> 53; a[i+4] &= 0x1fffffffffffffL;
        a[i+6] += a[i+5] >> 53; a[i+5] &= 0x1fffffffffffffL;
        a[i+7] += a[i+6] >> 53; a[i+6] &= 0x1fffffffffffffL;
        a[i+8] += a[i+7] >> 53; a[i+7] &= 0x1fffffffffffffL;
        a[i+9] += a[i+8] >> 53; a[i+8] &= 0x1fffffffffffffL;
    }
    a[32+1] += a[32] >> 53;
    a[32] &= 0x1fffffffffffffL;
    a[33+1] += a[33] >> 53;
    a[33] &= 0x1fffffffffffffL;
    a[34+1] += a[34] >> 53;
    a[34] &= 0x1fffffffffffffL;
    a[35+1] += a[35] >> 53;
    a[35] &= 0x1fffffffffffffL;
    a[36+1] += a[36] >> 53;
    a[36] &= 0x1fffffffffffffL;
    a[37+1] += a[37] >> 53;
    a[37] &= 0x1fffffffffffffL;
#endif
}

/* Shift the result in the high 2048 bits down to the bottom.
 *
 * r  A single precision number.
 * a  A single precision number.
 */
static void sp_4096_mont_shift_39(sp_digit* r, const sp_digit* a)
{
#ifdef WOLFSSL_SP_SMALL
    int i;
    int128_t n = a[38] >> 34;
    n += ((int128_t)a[39]) << 19;

    for (i = 0; i < 38; i++) {
        r[i] = n & 0x1fffffffffffffL;
        n >>= 53;
        n += ((int128_t)a[40 + i]) << 19;
    }
    r[38] = (sp_digit)n;
#else
    int i;
    int128_t n = a[38] >> 34;
    n += ((int128_t)a[39]) << 19;
    for (i = 0; i < 32; i += 8) {
        r[i + 0] = n & 0x1fffffffffffffL;
        n >>= 53; n += ((int128_t)a[i + 40]) << 19;
        r[i + 1] = n & 0x1fffffffffffffL;
        n >>= 53; n += ((int128_t)a[i + 41]) << 19;
        r[i + 2] = n & 0x1fffffffffffffL;
        n >>= 53; n += ((int128_t)a[i + 42]) << 19;
        r[i + 3] = n & 0x1fffffffffffffL;
        n >>= 53; n += ((int128_t)a[i + 43]) << 19;
        r[i + 4] = n & 0x1fffffffffffffL;
        n >>= 53; n += ((int128_t)a[i + 44]) << 19;
        r[i + 5] = n & 0x1fffffffffffffL;
        n >>= 53; n += ((int128_t)a[i + 45]) << 19;
        r[i + 6] = n & 0x1fffffffffffffL;
        n >>= 53; n += ((int128_t)a[i + 46]) << 19;
        r[i + 7] = n & 0x1fffffffffffffL;
        n >>= 53; n += ((int128_t)a[i + 47]) << 19;
    }
    r[32] = n & 0x1fffffffffffffL; n >>= 53; n += ((int128_t)a[72]) << 19;
    r[33] = n & 0x1fffffffffffffL; n >>= 53; n += ((int128_t)a[73]) << 19;
    r[34] = n & 0x1fffffffffffffL; n >>= 53; n += ((int128_t)a[74]) << 19;
    r[35] = n & 0x1fffffffffffffL; n >>= 53; n += ((int128_t)a[75]) << 19;
    r[36] = n & 0x1fffffffffffffL; n >>= 53; n += ((int128_t)a[76]) << 19;
    r[37] = n & 0x1fffffffffffffL; n >>= 53; n += ((int128_t)a[77]) << 19;
    r[38] = (sp_digit)n;
#endif /* WOLFSSL_SP_SMALL */
    XMEMSET(&r[39], 0, sizeof(*r) * 39U);
}

/* Reduce the number back to 4096 bits using Montgomery reduction.
 *
 * a   A single precision number to reduce in place.
 * m   The single precision number representing the modulus.
 * mp  The digit representing the negative inverse of m mod 2^n.
 */
static void sp_4096_mont_reduce_39(sp_digit* a, const sp_digit* m, sp_digit mp)
{
    int i;
    sp_digit mu;

    sp_4096_norm_39(a + 39);

    for (i=0; i<38; i++) {
        mu = (a[i] * mp) & 0x1fffffffffffffL;
        sp_4096_mul_add_39(a+i, m, mu);
        a[i+1] += a[i] >> 53;
    }
    mu = (a[i] * mp) & 0x3ffffffffL;
    sp_4096_mul_add_39(a+i, m, mu);
    a[i+1] += a[i] >> 53;
    a[i] &= 0x1fffffffffffffL;

    sp_4096_mont_shift_39(a, a);
    sp_4096_cond_sub_39(a, a, m, 0 - (((a[38] >> 34) > 0) ?
            (sp_digit)1 : (sp_digit)0));
    sp_4096_norm_39(a);
}

/* Multiply two Montogmery form numbers mod the modulus (prime).
 * (r = a * b mod m)
 *
 * r   Result of multiplication.
 * a   First number to multiply in Montogmery form.
 * b   Second number to multiply in Montogmery form.
 * m   Modulus (prime).
 * mp  Montogmery mulitplier.
 */
static void sp_4096_mont_mul_39(sp_digit* r, const sp_digit* a, const sp_digit* b,
        const sp_digit* m, sp_digit mp)
{
    sp_4096_mul_39(r, a, b);
    sp_4096_mont_reduce_39(r, m, mp);
}

/* Square the Montgomery form number. (r = a * a mod m)
 *
 * r   Result of squaring.
 * a   Number to square in Montogmery form.
 * m   Modulus (prime).
 * mp  Montogmery mulitplier.
 */
static void sp_4096_mont_sqr_39(sp_digit* r, const sp_digit* a, const sp_digit* m,
        sp_digit mp)
{
    sp_4096_sqr_39(r, a);
    sp_4096_mont_reduce_39(r, m, mp);
}

/* Multiply a by scalar b into r. (r = a * b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A scalar.
 */
SP_NOINLINE static void sp_4096_mul_d_39(sp_digit* r, const sp_digit* a,
    sp_digit b)
{
#ifdef WOLFSSL_SP_SMALL
    int128_t tb = b;
    int128_t t = 0;
    int i;

    for (i = 0; i < 39; i++) {
        t += tb * a[i];
        r[i] = t & 0x1fffffffffffffL;
        t >>= 53;
    }
    r[39] = (sp_digit)t;
#else
    int128_t tb = b;
    int128_t t[8];
    int i;

    t[0] = tb * a[0]; r[0] = t[0] & 0x1fffffffffffffL;
    for (i = 0; i < 32; i += 8) {
        t[1] = tb * a[i+1];
        r[i+1] = (sp_digit)(t[0] >> 53) + (t[1] & 0x1fffffffffffffL);
        t[2] = tb * a[i+2];
        r[i+2] = (sp_digit)(t[1] >> 53) + (t[2] & 0x1fffffffffffffL);
        t[3] = tb * a[i+3];
        r[i+3] = (sp_digit)(t[2] >> 53) + (t[3] & 0x1fffffffffffffL);
        t[4] = tb * a[i+4];
        r[i+4] = (sp_digit)(t[3] >> 53) + (t[4] & 0x1fffffffffffffL);
        t[5] = tb * a[i+5];
        r[i+5] = (sp_digit)(t[4] >> 53) + (t[5] & 0x1fffffffffffffL);
        t[6] = tb * a[i+6];
        r[i+6] = (sp_digit)(t[5] >> 53) + (t[6] & 0x1fffffffffffffL);
        t[7] = tb * a[i+7];
        r[i+7] = (sp_digit)(t[6] >> 53) + (t[7] & 0x1fffffffffffffL);
        t[0] = tb * a[i+8];
        r[i+8] = (sp_digit)(t[7] >> 53) + (t[0] & 0x1fffffffffffffL);
    }
    t[1] = tb * a[33];
    r[33] = (sp_digit)(t[0] >> 53) + (t[1] & 0x1fffffffffffffL);
    t[2] = tb * a[34];
    r[34] = (sp_digit)(t[1] >> 53) + (t[2] & 0x1fffffffffffffL);
    t[3] = tb * a[35];
    r[35] = (sp_digit)(t[2] >> 53) + (t[3] & 0x1fffffffffffffL);
    t[4] = tb * a[36];
    r[36] = (sp_digit)(t[3] >> 53) + (t[4] & 0x1fffffffffffffL);
    t[5] = tb * a[37];
    r[37] = (sp_digit)(t[4] >> 53) + (t[5] & 0x1fffffffffffffL);
    t[6] = tb * a[38];
    r[38] = (sp_digit)(t[5] >> 53) + (t[6] & 0x1fffffffffffffL);
    r[39] =  (sp_digit)(t[6] >> 53);
#endif /* WOLFSSL_SP_SMALL */
}

/* Conditionally add a and b using the mask m.
 * m is -1 to add and 0 when not.
 *
 * r  A single precision number representing conditional add result.
 * a  A single precision number to add with.
 * b  A single precision number to add.
 * m  Mask value to apply.
 */
static void sp_4096_cond_add_39(sp_digit* r, const sp_digit* a,
        const sp_digit* b, const sp_digit m)
{
#ifdef WOLFSSL_SP_SMALL
    int i;

    for (i = 0; i < 39; i++) {
        r[i] = a[i] + (b[i] & m);
    }
#else
    int i;

    for (i = 0; i < 32; i += 8) {
        r[i + 0] = a[i + 0] + (b[i + 0] & m);
        r[i + 1] = a[i + 1] + (b[i + 1] & m);
        r[i + 2] = a[i + 2] + (b[i + 2] & m);
        r[i + 3] = a[i + 3] + (b[i + 3] & m);
        r[i + 4] = a[i + 4] + (b[i + 4] & m);
        r[i + 5] = a[i + 5] + (b[i + 5] & m);
        r[i + 6] = a[i + 6] + (b[i + 6] & m);
        r[i + 7] = a[i + 7] + (b[i + 7] & m);
    }
    r[32] = a[32] + (b[32] & m);
    r[33] = a[33] + (b[33] & m);
    r[34] = a[34] + (b[34] & m);
    r[35] = a[35] + (b[35] & m);
    r[36] = a[36] + (b[36] & m);
    r[37] = a[37] + (b[37] & m);
    r[38] = a[38] + (b[38] & m);
#endif /* WOLFSSL_SP_SMALL */
}

#ifdef WOLFSSL_SMALL
/* Add b to a into r. (r = a + b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A single precision integer.
 */
SP_NOINLINE static int sp_4096_add_39(sp_digit* r, const sp_digit* a,
        const sp_digit* b)
{
    int i;

    for (i = 0; i < 39; i++) {
        r[i] = a[i] + b[i];
    }

    return 0;
}
#endif
SP_NOINLINE static void sp_4096_rshift_39(sp_digit* r, sp_digit* a, byte n)
{
    int i;

#ifdef WOLFSSL_SP_SMALL
    for (i=0; i<38; i++) {
        r[i] = ((a[i] >> n) | (a[i + 1] << (53 - n))) & 0x1fffffffffffffL;
    }
#else
    for (i=0; i<32; i += 8) {
        r[i+0] = ((a[i+0] >> n) | (a[i+1] << (53 - n))) & 0x1fffffffffffffL;
        r[i+1] = ((a[i+1] >> n) | (a[i+2] << (53 - n))) & 0x1fffffffffffffL;
        r[i+2] = ((a[i+2] >> n) | (a[i+3] << (53 - n))) & 0x1fffffffffffffL;
        r[i+3] = ((a[i+3] >> n) | (a[i+4] << (53 - n))) & 0x1fffffffffffffL;
        r[i+4] = ((a[i+4] >> n) | (a[i+5] << (53 - n))) & 0x1fffffffffffffL;
        r[i+5] = ((a[i+5] >> n) | (a[i+6] << (53 - n))) & 0x1fffffffffffffL;
        r[i+6] = ((a[i+6] >> n) | (a[i+7] << (53 - n))) & 0x1fffffffffffffL;
        r[i+7] = ((a[i+7] >> n) | (a[i+8] << (53 - n))) & 0x1fffffffffffffL;
    }
    r[32] = ((a[32] >> n) | (a[33] << (53 - n))) & 0x1fffffffffffffL;
    r[33] = ((a[33] >> n) | (a[34] << (53 - n))) & 0x1fffffffffffffL;
    r[34] = ((a[34] >> n) | (a[35] << (53 - n))) & 0x1fffffffffffffL;
    r[35] = ((a[35] >> n) | (a[36] << (53 - n))) & 0x1fffffffffffffL;
    r[36] = ((a[36] >> n) | (a[37] << (53 - n))) & 0x1fffffffffffffL;
    r[37] = ((a[37] >> n) | (a[38] << (53 - n))) & 0x1fffffffffffffL;
#endif
    r[38] = a[38] >> n;
}

#ifdef WOLFSSL_SP_DIV_64
static WC_INLINE sp_digit sp_4096_div_word_39(sp_digit d1, sp_digit d0,
    sp_digit dv)
{
    sp_digit d, r, t;

    /* All 53 bits from d1 and top 10 bits from d0. */
    d = (d1 << 10) | (d0 >> 43);
    r = d / dv;
    d -= r * dv;
    /* Up to 11 bits in r */
    /* Next 10 bits from d0. */
    r <<= 10;
    d <<= 10;
    d |= (d0 >> 33) & ((1 << 10) - 1);
    t = d / dv;
    d -= t * dv;
    r += t;
    /* Up to 21 bits in r */
    /* Next 10 bits from d0. */
    r <<= 10;
    d <<= 10;
    d |= (d0 >> 23) & ((1 << 10) - 1);
    t = d / dv;
    d -= t * dv;
    r += t;
    /* Up to 31 bits in r */
    /* Next 10 bits from d0. */
    r <<= 10;
    d <<= 10;
    d |= (d0 >> 13) & ((1 << 10) - 1);
    t = d / dv;
    d -= t * dv;
    r += t;
    /* Up to 41 bits in r */
    /* Next 10 bits from d0. */
    r <<= 10;
    d <<= 10;
    d |= (d0 >> 3) & ((1 << 10) - 1);
    t = d / dv;
    d -= t * dv;
    r += t;
    /* Up to 51 bits in r */
    /* Remaining 3 bits from d0. */
    r <<= 3;
    d <<= 3;
    d |= d0 & ((1 << 3) - 1);
    t = d / dv;
    r += t;

    return r;
}
#endif /* WOLFSSL_SP_DIV_64 */

/* Divide d in a and put remainder into r (m*d + r = a)
 * m is not calculated as it is not needed at this time.
 *
 * a  Nmber to be divided.
 * d  Number to divide with.
 * m  Multiplier result.
 * r  Remainder from the division.
 * returns MEMORY_E when unable to allocate memory and MP_OKAY otherwise.
 */
static int sp_4096_div_39(const sp_digit* a, const sp_digit* d, sp_digit* m,
        sp_digit* r)
{
    int i;
#ifndef WOLFSSL_SP_DIV_64
    int128_t d1;
#endif
    sp_digit dv, r1;
#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    sp_digit* td;
#else
    sp_digit t1d[78 + 1], t2d[39 + 1], sdd[39 + 1];
#endif
    sp_digit* t1;
    sp_digit* t2;
    sp_digit* sd;
    int err = MP_OKAY;

    (void)m;

#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    td = (sp_digit*)XMALLOC(sizeof(sp_digit) * (4 * 39 + 3), NULL,
                                                       DYNAMIC_TYPE_TMP_BUFFER);
    if (td == NULL) {
        err = MEMORY_E;
    }
#endif

    (void)m;

    if (err == MP_OKAY) {
#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
        t1 = td;
        t2 = td + 78 + 1;
        sd = t2 + 39 + 1;
#else
        t1 = t1d;
        t2 = t2d;
        sd = sdd;
#endif

        sp_4096_mul_d_39(sd, d, 1L << 19);
        sp_4096_mul_d_78(t1, a, 1L << 19);
        dv = sd[38];
        for (i=39; i>=0; i--) {
            t1[39 + i] += t1[39 + i - 1] >> 53;
            t1[39 + i - 1] &= 0x1fffffffffffffL;
#ifndef WOLFSSL_SP_DIV_64
            d1 = t1[39 + i];
            d1 <<= 53;
            d1 += t1[39 + i - 1];
            r1 = (sp_digit)(d1 / dv);
#else
            r1 = sp_4096_div_word_39(t1[39 + i], t1[39 + i - 1], dv);
#endif

            sp_4096_mul_d_39(t2, sd, r1);
            (void)sp_4096_sub_39(&t1[i], &t1[i], t2);
            t1[39 + i] -= t2[39];
            t1[39 + i] += t1[39 + i - 1] >> 53;
            t1[39 + i - 1] &= 0x1fffffffffffffL;
            r1 = (((-t1[39 + i]) << 53) - t1[39 + i - 1]) / dv;
            r1 -= t1[39 + i];
            sp_4096_mul_d_39(t2, sd, r1);
            (void)sp_4096_add_39(&t1[i], &t1[i], t2);
            t1[39 + i] += t1[39 + i - 1] >> 53;
            t1[39 + i - 1] &= 0x1fffffffffffffL;
        }
        t1[39 - 1] += t1[39 - 2] >> 53;
        t1[39 - 2] &= 0x1fffffffffffffL;
        r1 = t1[39 - 1] / dv;

        sp_4096_mul_d_39(t2, sd, r1);
        sp_4096_sub_39(t1, t1, t2);
        XMEMCPY(r, t1, sizeof(*r) * 2U * 39U);
        for (i=0; i<38; i++) {
            r[i+1] += r[i] >> 53;
            r[i] &= 0x1fffffffffffffL;
        }
        sp_4096_cond_add_39(r, r, sd, 0 - ((r[38] < 0) ?
                    (sp_digit)1 : (sp_digit)0));

        sp_4096_norm_39(r);
        sp_4096_rshift_39(r, r, 19);
    }

#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (td != NULL) {
        XFREE(td, NULL, DYNAMIC_TYPE_TMP_BUFFER);
    }
#endif

    return err;
}

/* Reduce a modulo m into r. (r = a mod m)
 *
 * r  A single precision number that is the reduced result.
 * a  A single precision number that is to be reduced.
 * m  A single precision number that is the modulus to reduce with.
 * returns MEMORY_E when unable to allocate memory and MP_OKAY otherwise.
 */
static int sp_4096_mod_39(sp_digit* r, const sp_digit* a, const sp_digit* m)
{
    return sp_4096_div_39(a, m, NULL, r);
}

/* Modular exponentiate a to the e mod m. (r = a^e mod m)
 *
 * r     A single precision number that is the result of the operation.
 * a     A single precision number being exponentiated.
 * e     A single precision number that is the exponent.
 * bits  The number of bits in the exponent.
 * m     A single precision number that is the modulus.
 * returns 0 on success and MEMORY_E on dynamic memory allocation failure.
 */
static int sp_4096_mod_exp_39(sp_digit* r, const sp_digit* a, const sp_digit* e, int bits,
    const sp_digit* m, int reduceA)
{
#ifdef WOLFSSL_SP_SMALL
#if !defined(WOLFSSL_SP_NO_MALLOC)
    sp_digit* td;
#else
    sp_digit td[3 * 78];
#endif
    sp_digit* t[3];
    sp_digit* norm;
    sp_digit mp = 1;
    sp_digit n;
    int i;
    int c, y;
    int err = MP_OKAY;

#if !defined(WOLFSSL_SP_NO_MALLOC)
    td = (sp_digit*)XMALLOC(sizeof(sp_digit) * 3 * 39 * 2, NULL,
                            DYNAMIC_TYPE_TMP_BUFFER);
    if (td == NULL) {
        err = MEMORY_E;
    }
#endif

    if (err == MP_OKAY) {
        norm = td;
        for (i=0; i<3; i++) {
#if !defined(WOLFSSL_SP_NO_MALLOC)
            t[i] = td + (i * 39 * 2);
#else
            t[i] = &td[i * 39 * 2];
#endif
            XMEMSET(t[i], 0, sizeof(sp_digit) * 39U * 2U);
        }

        sp_4096_mont_setup(m, &mp);
        sp_4096_mont_norm_39(norm, m);

        if (reduceA != 0) {
            err = sp_4096_mod_39(t[1], a, m);
        }
        else {
            XMEMCPY(t[1], a, sizeof(sp_digit) * 39U);
        }
    }
    if (err == MP_OKAY) {
        sp_4096_mul_39(t[1], t[1], norm);
        err = sp_4096_mod_39(t[1], t[1], m);
    }

    if (err == MP_OKAY) {
        i = bits / 53;
        c = bits % 53;
        n = e[i--] << (53 - c);
        for (; ; c--) {
            if (c == 0) {
                if (i == -1) {
                    break;
                }

                n = e[i--];
                c = 53;
            }

            y = (n >> 52) & 1;
            n <<= 1;

            sp_4096_mont_mul_39(t[y^1], t[0], t[1], m, mp);

            XMEMCPY(t[2], (void*)(((size_t)t[0] & addr_mask[y^1]) +
                                  ((size_t)t[1] & addr_mask[y])),
                                  sizeof(*t[2]) * 39 * 2);
            sp_4096_mont_sqr_39(t[2], t[2], m, mp);
            XMEMCPY((void*)(((size_t)t[0] & addr_mask[y^1]) +
                            ((size_t)t[1] & addr_mask[y])), t[2],
                            sizeof(*t[2]) * 39 * 2);
        }

        sp_4096_mont_reduce_39(t[0], m, mp);
        n = sp_4096_cmp_39(t[0], m);
        sp_4096_cond_sub_39(t[0], t[0], m, ((n < 0) ?
                    (sp_digit)1 : (sp_digit)0) - 1);
        XMEMCPY(r, t[0], sizeof(*r) * 39 * 2);

    }

#if !defined(WOLFSSL_SP_NO_MALLOC)
    if (td != NULL) {
        XFREE(td, NULL, DYNAMIC_TYPE_TMP_BUFFER);
    }
#endif

    return err;
#elif !defined(WC_NO_CACHE_RESISTANT)
#if defined(WOLFSSL_SMALL_STACK) && !defined(WOLFSSL_SP_NO_MALLOC)
    sp_digit* td;
#else
    sp_digit td[3 * 78];
#endif
    sp_digit* t[3];
    sp_digit* norm;
    sp_digit mp = 1;
    sp_digit n;
    int i;
    int c, y;
    int err = MP_OKAY;

#ifdef WOLFSSL_SMALL_STACK
    td = (sp_digit*)XMALLOC(sizeof(sp_digit) * 3 * 39 * 2, NULL,
                            DYNAMIC_TYPE_TMP_BUFFER);
    if (td == NULL) {
        err = MEMORY_E;
    }
#endif

    if (err == MP_OKAY) {
        norm = td;
        for (i=0; i<3; i++) {
#if defined(WOLFSSL_SMALL_STACK) && !defined(WOLFSSL_SP_NO_MALLOC)
            t[i] = td + (i * 39 * 2);
#else
            t[i] = &td[i * 39 * 2];
#endif
        }

        sp_4096_mont_setup(m, &mp);
        sp_4096_mont_norm_39(norm, m);

        if (reduceA != 0) {
            err = sp_4096_mod_39(t[1], a, m);
            if (err == MP_OKAY) {
                sp_4096_mul_39(t[1], t[1], norm);
                err = sp_4096_mod_39(t[1], t[1], m);
            }
        }
        else {
            sp_4096_mul_39(t[1], a, norm);
            err = sp_4096_mod_39(t[1], t[1], m);
        }
    }

    if (err == MP_OKAY) {
        i = bits / 53;
        c = bits % 53;
        n = e[i--] << (53 - c);
        for (; ; c--) {
            if (c == 0) {
                if (i == -1) {
                    break;
                }

                n = e[i--];
                c = 53;
            }

            y = (n >> 52) & 1;
            n <<= 1;

            sp_4096_mont_mul_39(t[y^1], t[0], t[1], m, mp);

            XMEMCPY(t[2], (void*)(((size_t)t[0] & addr_mask[y^1]) +
                                  ((size_t)t[1] & addr_mask[y])), 
                                  sizeof(*t[2]) * 39 * 2);
            sp_4096_mont_sqr_39(t[2], t[2], m, mp);
            XMEMCPY((void*)(((size_t)t[0] & addr_mask[y^1]) +
                            ((size_t)t[1] & addr_mask[y])), t[2], 
                            sizeof(*t[2]) * 39 * 2);
        }

        sp_4096_mont_reduce_39(t[0], m, mp);
        n = sp_4096_cmp_39(t[0], m);
        sp_4096_cond_sub_39(t[0], t[0], m, ((n < 0) ?
                    (sp_digit)1 : (sp_digit)0) - 1);
        XMEMCPY(r, t[0], sizeof(*r) * 39 * 2);
    }

#ifdef WOLFSSL_SMALL_STACK
    if (td != NULL) {
        XFREE(td, NULL, DYNAMIC_TYPE_TMP_BUFFER);
    }
#endif

    return err;
#else
#if defined(WOLFSSL_SMALL_STACK) && !defined(WOLFSSL_SP_NO_MALLOC)
    sp_digit* td;
#else
    sp_digit td[(32 * 78) + 78];
#endif
    sp_digit* t[32];
    sp_digit* rt;
    sp_digit* norm;
    sp_digit mp = 1;
    sp_digit n;
    int i;
    int c, y;
    int err = MP_OKAY;

#if defined(WOLFSSL_SMALL_STACK) && !defined(WOLFSSL_SP_NO_MALLOC)
    td = (sp_digit*)XMALLOC(sizeof(sp_digit) * ((32 * 78) + 78), NULL,
                            DYNAMIC_TYPE_TMP_BUFFER);
    if (td == NULL) {
        err = MEMORY_E;
    }
#endif

    if (err == MP_OKAY) {
        norm = td;
#if defined(WOLFSSL_SMALL_STACK) && !defined(WOLFSSL_SP_NO_MALLOC)
        for (i=0; i<32; i++)
            t[i] = td + i * 78;
        rt = td + 2496;
#else
        for (i=0; i<32; i++)
            t[i] = &td[i * 78];
        rt = &td[2496];
#endif

        sp_4096_mont_setup(m, &mp);
        sp_4096_mont_norm_39(norm, m);

        if (reduceA != 0) {
            err = sp_4096_mod_39(t[1], a, m);
            if (err == MP_OKAY) {
                sp_4096_mul_39(t[1], t[1], norm);
                err = sp_4096_mod_39(t[1], t[1], m);
            }
        }
        else {
            sp_4096_mul_39(t[1], a, norm);
            err = sp_4096_mod_39(t[1], t[1], m);
        }
    }

    if (err == MP_OKAY) {
        sp_4096_mont_sqr_39(t[ 2], t[ 1], m, mp);
        sp_4096_mont_mul_39(t[ 3], t[ 2], t[ 1], m, mp);
        sp_4096_mont_sqr_39(t[ 4], t[ 2], m, mp);
        sp_4096_mont_mul_39(t[ 5], t[ 3], t[ 2], m, mp);
        sp_4096_mont_sqr_39(t[ 6], t[ 3], m, mp);
        sp_4096_mont_mul_39(t[ 7], t[ 4], t[ 3], m, mp);
        sp_4096_mont_sqr_39(t[ 8], t[ 4], m, mp);
        sp_4096_mont_mul_39(t[ 9], t[ 5], t[ 4], m, mp);
        sp_4096_mont_sqr_39(t[10], t[ 5], m, mp);
        sp_4096_mont_mul_39(t[11], t[ 6], t[ 5], m, mp);
        sp_4096_mont_sqr_39(t[12], t[ 6], m, mp);
        sp_4096_mont_mul_39(t[13], t[ 7], t[ 6], m, mp);
        sp_4096_mont_sqr_39(t[14], t[ 7], m, mp);
        sp_4096_mont_mul_39(t[15], t[ 8], t[ 7], m, mp);
        sp_4096_mont_sqr_39(t[16], t[ 8], m, mp);
        sp_4096_mont_mul_39(t[17], t[ 9], t[ 8], m, mp);
        sp_4096_mont_sqr_39(t[18], t[ 9], m, mp);
        sp_4096_mont_mul_39(t[19], t[10], t[ 9], m, mp);
        sp_4096_mont_sqr_39(t[20], t[10], m, mp);
        sp_4096_mont_mul_39(t[21], t[11], t[10], m, mp);
        sp_4096_mont_sqr_39(t[22], t[11], m, mp);
        sp_4096_mont_mul_39(t[23], t[12], t[11], m, mp);
        sp_4096_mont_sqr_39(t[24], t[12], m, mp);
        sp_4096_mont_mul_39(t[25], t[13], t[12], m, mp);
        sp_4096_mont_sqr_39(t[26], t[13], m, mp);
        sp_4096_mont_mul_39(t[27], t[14], t[13], m, mp);
        sp_4096_mont_sqr_39(t[28], t[14], m, mp);
        sp_4096_mont_mul_39(t[29], t[15], t[14], m, mp);
        sp_4096_mont_sqr_39(t[30], t[15], m, mp);
        sp_4096_mont_mul_39(t[31], t[16], t[15], m, mp);

        bits = ((bits + 4) / 5) * 5;
        i = ((bits + 52) / 53) - 1;
        c = bits % 53;
        if (c == 0) {
            c = 53;
        }
        if (i < 39) {
            n = e[i--] << (64 - c);
        }
        else {
            n = 0;
            i--;
        }
        if (c < 5) {
            n |= e[i--] << (11 - c);
            c += 53;
        }
        y = (n >> 59) & 0x1f;
        n <<= 5;
        c -= 5;
        XMEMCPY(rt, t[y], sizeof(sp_digit) * 78);
        for (; i>=0 || c>=5; ) {
            if (c < 5) {
                n |= e[i--] << (11 - c);
                c += 53;
            }
            y = (n >> 59) & 0x1f;
            n <<= 5;
            c -= 5;

            sp_4096_mont_sqr_39(rt, rt, m, mp);
            sp_4096_mont_sqr_39(rt, rt, m, mp);
            sp_4096_mont_sqr_39(rt, rt, m, mp);
            sp_4096_mont_sqr_39(rt, rt, m, mp);
            sp_4096_mont_sqr_39(rt, rt, m, mp);

            sp_4096_mont_mul_39(rt, rt, t[y], m, mp);
        }

        sp_4096_mont_reduce_39(rt, m, mp);
        n = sp_4096_cmp_39(rt, m);
        sp_4096_cond_sub_39(rt, rt, m, ((n < 0) ?
                   (sp_digit)1 : (sp_digit)0) - 1);
        XMEMCPY(r, rt, sizeof(sp_digit) * 78);
    }

#if defined(WOLFSSL_SMALL_STACK) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (td != NULL) {
        XFREE(td, NULL, DYNAMIC_TYPE_TMP_BUFFER);
    }
#endif

    return err;
#endif
}

#endif /* WOLFSSL_HAVE_SP_RSA && !SP_RSA_PRIVATE_EXP_D */
#endif /* (WOLFSSL_HAVE_SP_RSA || WOLFSSL_HAVE_SP_DH) && !WOLFSSL_RSA_PUBLIC_ONLY */

/* r = 2^n mod m where n is the number of bits to reduce by.
 * Given m must be 4096 bits, just need to subtract.
 *
 * r  A single precision number.
 * m  A single precision number.
 */
static void sp_4096_mont_norm_78(sp_digit* r, const sp_digit* m)
{
    /* Set r = 2^n - 1. */
#ifdef WOLFSSL_SP_SMALL
    int i;

    for (i=0; i<77; i++) {
        r[i] = 0x1fffffffffffffL;
    }
#else
    int i;

    for (i = 0; i < 72; i += 8) {
        r[i + 0] = 0x1fffffffffffffL;
        r[i + 1] = 0x1fffffffffffffL;
        r[i + 2] = 0x1fffffffffffffL;
        r[i + 3] = 0x1fffffffffffffL;
        r[i + 4] = 0x1fffffffffffffL;
        r[i + 5] = 0x1fffffffffffffL;
        r[i + 6] = 0x1fffffffffffffL;
        r[i + 7] = 0x1fffffffffffffL;
    }
    r[72] = 0x1fffffffffffffL;
    r[73] = 0x1fffffffffffffL;
    r[74] = 0x1fffffffffffffL;
    r[75] = 0x1fffffffffffffL;
    r[76] = 0x1fffffffffffffL;
#endif
    r[77] = 0x7fffL;

    /* r = (2^n - 1) mod n */
    (void)sp_4096_sub_78(r, r, m);

    /* Add one so r = 2^n mod m */
    r[0] += 1;
}

/* Compare a with b in constant time.
 *
 * a  A single precision integer.
 * b  A single precision integer.
 * return -ve, 0 or +ve if a is less than, equal to or greater than b
 * respectively.
 */
static sp_digit sp_4096_cmp_78(const sp_digit* a, const sp_digit* b)
{
    sp_digit r = 0;
#ifdef WOLFSSL_SP_SMALL
    int i;

    for (i=77; i>=0; i--) {
        r |= (a[i] - b[i]) & (0 - ((r == 0) ? (sp_digit)1 : (sp_digit)0));
    }
#else
    int i;

    r |= (a[77] - b[77]) & (0 - ((r == 0) ? (sp_digit)1 : (sp_digit)0));
    r |= (a[76] - b[76]) & (0 - ((r == 0) ? (sp_digit)1 : (sp_digit)0));
    r |= (a[75] - b[75]) & (0 - ((r == 0) ? (sp_digit)1 : (sp_digit)0));
    r |= (a[74] - b[74]) & (0 - ((r == 0) ? (sp_digit)1 : (sp_digit)0));
    r |= (a[73] - b[73]) & (0 - ((r == 0) ? (sp_digit)1 : (sp_digit)0));
    r |= (a[72] - b[72]) & (0 - ((r == 0) ? (sp_digit)1 : (sp_digit)0));
    for (i = 64; i >= 0; i -= 8) {
        r |= (a[i + 7] - b[i + 7]) & (0 - ((r == 0) ? (sp_digit)1 : (sp_digit)0));
        r |= (a[i + 6] - b[i + 6]) & (0 - ((r == 0) ? (sp_digit)1 : (sp_digit)0));
        r |= (a[i + 5] - b[i + 5]) & (0 - ((r == 0) ? (sp_digit)1 : (sp_digit)0));
        r |= (a[i + 4] - b[i + 4]) & (0 - ((r == 0) ? (sp_digit)1 : (sp_digit)0));
        r |= (a[i + 3] - b[i + 3]) & (0 - ((r == 0) ? (sp_digit)1 : (sp_digit)0));
        r |= (a[i + 2] - b[i + 2]) & (0 - ((r == 0) ? (sp_digit)1 : (sp_digit)0));
        r |= (a[i + 1] - b[i + 1]) & (0 - ((r == 0) ? (sp_digit)1 : (sp_digit)0));
        r |= (a[i + 0] - b[i + 0]) & (0 - ((r == 0) ? (sp_digit)1 : (sp_digit)0));
    }
#endif /* WOLFSSL_SP_SMALL */

    return r;
}

/* Conditionally subtract b from a using the mask m.
 * m is -1 to subtract and 0 when not.
 *
 * r  A single precision number representing condition subtract result.
 * a  A single precision number to subtract from.
 * b  A single precision number to subtract.
 * m  Mask value to apply.
 */
static void sp_4096_cond_sub_78(sp_digit* r, const sp_digit* a,
        const sp_digit* b, const sp_digit m)
{
#ifdef WOLFSSL_SP_SMALL
    int i;

    for (i = 0; i < 78; i++) {
        r[i] = a[i] - (b[i] & m);
    }
#else
    int i;

    for (i = 0; i < 72; i += 8) {
        r[i + 0] = a[i + 0] - (b[i + 0] & m);
        r[i + 1] = a[i + 1] - (b[i + 1] & m);
        r[i + 2] = a[i + 2] - (b[i + 2] & m);
        r[i + 3] = a[i + 3] - (b[i + 3] & m);
        r[i + 4] = a[i + 4] - (b[i + 4] & m);
        r[i + 5] = a[i + 5] - (b[i + 5] & m);
        r[i + 6] = a[i + 6] - (b[i + 6] & m);
        r[i + 7] = a[i + 7] - (b[i + 7] & m);
    }
    r[72] = a[72] - (b[72] & m);
    r[73] = a[73] - (b[73] & m);
    r[74] = a[74] - (b[74] & m);
    r[75] = a[75] - (b[75] & m);
    r[76] = a[76] - (b[76] & m);
    r[77] = a[77] - (b[77] & m);
#endif /* WOLFSSL_SP_SMALL */
}

/* Mul a by scalar b and add into r. (r += a * b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A scalar.
 */
SP_NOINLINE static void sp_4096_mul_add_78(sp_digit* r, const sp_digit* a,
        const sp_digit b)
{
#ifdef WOLFSSL_SP_SMALL
    int128_t tb = b;
    int128_t t = 0;
    int i;

    for (i = 0; i < 78; i++) {
        t += (tb * a[i]) + r[i];
        r[i] = t & 0x1fffffffffffffL;
        t >>= 53;
    }
    r[78] += t;
#else
    int128_t tb = b;
    int128_t t[8];
    int i;

    t[0] = tb * a[0]; r[0] += (sp_digit)(t[0] & 0x1fffffffffffffL);
    for (i = 0; i < 72; i += 8) {
        t[1] = tb * a[i+1];
        r[i+1] += (sp_digit)((t[0] >> 53) + (t[1] & 0x1fffffffffffffL));
        t[2] = tb * a[i+2];
        r[i+2] += (sp_digit)((t[1] >> 53) + (t[2] & 0x1fffffffffffffL));
        t[3] = tb * a[i+3];
        r[i+3] += (sp_digit)((t[2] >> 53) + (t[3] & 0x1fffffffffffffL));
        t[4] = tb * a[i+4];
        r[i+4] += (sp_digit)((t[3] >> 53) + (t[4] & 0x1fffffffffffffL));
        t[5] = tb * a[i+5];
        r[i+5] += (sp_digit)((t[4] >> 53) + (t[5] & 0x1fffffffffffffL));
        t[6] = tb * a[i+6];
        r[i+6] += (sp_digit)((t[5] >> 53) + (t[6] & 0x1fffffffffffffL));
        t[7] = tb * a[i+7];
        r[i+7] += (sp_digit)((t[6] >> 53) + (t[7] & 0x1fffffffffffffL));
        t[0] = tb * a[i+8];
        r[i+8] += (sp_digit)((t[7] >> 53) + (t[0] & 0x1fffffffffffffL));
    }
    t[1] = tb * a[73]; r[73] += (sp_digit)((t[0] >> 53) + (t[1] & 0x1fffffffffffffL));
    t[2] = tb * a[74]; r[74] += (sp_digit)((t[1] >> 53) + (t[2] & 0x1fffffffffffffL));
    t[3] = tb * a[75]; r[75] += (sp_digit)((t[2] >> 53) + (t[3] & 0x1fffffffffffffL));
    t[4] = tb * a[76]; r[76] += (sp_digit)((t[3] >> 53) + (t[4] & 0x1fffffffffffffL));
    t[5] = tb * a[77]; r[77] += (sp_digit)((t[4] >> 53) + (t[5] & 0x1fffffffffffffL));
    r[78] +=  (sp_digit)(t[5] >> 53);
#endif /* WOLFSSL_SP_SMALL */
}

/* Normalize the values in each word to 53.
 *
 * a  Array of sp_digit to normalize.
 */
static void sp_4096_norm_78(sp_digit* a)
{
#ifdef WOLFSSL_SP_SMALL
    int i;
    for (i = 0; i < 77; i++) {
        a[i+1] += a[i] >> 53;
        a[i] &= 0x1fffffffffffffL;
    }
#else
    int i;
    for (i = 0; i < 72; i += 8) {
        a[i+1] += a[i+0] >> 53; a[i+0] &= 0x1fffffffffffffL;
        a[i+2] += a[i+1] >> 53; a[i+1] &= 0x1fffffffffffffL;
        a[i+3] += a[i+2] >> 53; a[i+2] &= 0x1fffffffffffffL;
        a[i+4] += a[i+3] >> 53; a[i+3] &= 0x1fffffffffffffL;
        a[i+5] += a[i+4] >> 53; a[i+4] &= 0x1fffffffffffffL;
        a[i+6] += a[i+5] >> 53; a[i+5] &= 0x1fffffffffffffL;
        a[i+7] += a[i+6] >> 53; a[i+6] &= 0x1fffffffffffffL;
        a[i+8] += a[i+7] >> 53; a[i+7] &= 0x1fffffffffffffL;
        a[i+9] += a[i+8] >> 53; a[i+8] &= 0x1fffffffffffffL;
    }
    a[72+1] += a[72] >> 53;
    a[72] &= 0x1fffffffffffffL;
    a[73+1] += a[73] >> 53;
    a[73] &= 0x1fffffffffffffL;
    a[74+1] += a[74] >> 53;
    a[74] &= 0x1fffffffffffffL;
    a[75+1] += a[75] >> 53;
    a[75] &= 0x1fffffffffffffL;
    a[76+1] += a[76] >> 53;
    a[76] &= 0x1fffffffffffffL;
#endif
}

/* Shift the result in the high 4096 bits down to the bottom.
 *
 * r  A single precision number.
 * a  A single precision number.
 */
static void sp_4096_mont_shift_78(sp_digit* r, const sp_digit* a)
{
#ifdef WOLFSSL_SP_SMALL
    int i;
    int128_t n = a[77] >> 15;
    n += ((int128_t)a[78]) << 38;

    for (i = 0; i < 77; i++) {
        r[i] = n & 0x1fffffffffffffL;
        n >>= 53;
        n += ((int128_t)a[79 + i]) << 38;
    }
    r[77] = (sp_digit)n;
#else
    int i;
    int128_t n = a[77] >> 15;
    n += ((int128_t)a[78]) << 38;
    for (i = 0; i < 72; i += 8) {
        r[i + 0] = n & 0x1fffffffffffffL;
        n >>= 53; n += ((int128_t)a[i + 79]) << 38;
        r[i + 1] = n & 0x1fffffffffffffL;
        n >>= 53; n += ((int128_t)a[i + 80]) << 38;
        r[i + 2] = n & 0x1fffffffffffffL;
        n >>= 53; n += ((int128_t)a[i + 81]) << 38;
        r[i + 3] = n & 0x1fffffffffffffL;
        n >>= 53; n += ((int128_t)a[i + 82]) << 38;
        r[i + 4] = n & 0x1fffffffffffffL;
        n >>= 53; n += ((int128_t)a[i + 83]) << 38;
        r[i + 5] = n & 0x1fffffffffffffL;
        n >>= 53; n += ((int128_t)a[i + 84]) << 38;
        r[i + 6] = n & 0x1fffffffffffffL;
        n >>= 53; n += ((int128_t)a[i + 85]) << 38;
        r[i + 7] = n & 0x1fffffffffffffL;
        n >>= 53; n += ((int128_t)a[i + 86]) << 38;
    }
    r[72] = n & 0x1fffffffffffffL; n >>= 53; n += ((int128_t)a[151]) << 38;
    r[73] = n & 0x1fffffffffffffL; n >>= 53; n += ((int128_t)a[152]) << 38;
    r[74] = n & 0x1fffffffffffffL; n >>= 53; n += ((int128_t)a[153]) << 38;
    r[75] = n & 0x1fffffffffffffL; n >>= 53; n += ((int128_t)a[154]) << 38;
    r[76] = n & 0x1fffffffffffffL; n >>= 53; n += ((int128_t)a[155]) << 38;
    r[77] = (sp_digit)n;
#endif /* WOLFSSL_SP_SMALL */
    XMEMSET(&r[78], 0, sizeof(*r) * 78U);
}

/* Reduce the number back to 4096 bits using Montgomery reduction.
 *
 * a   A single precision number to reduce in place.
 * m   The single precision number representing the modulus.
 * mp  The digit representing the negative inverse of m mod 2^n.
 */
static void sp_4096_mont_reduce_78(sp_digit* a, const sp_digit* m, sp_digit mp)
{
    int i;
    sp_digit mu;

    sp_4096_norm_78(a + 78);

#ifdef WOLFSSL_SP_DH
    if (mp != 1) {
        for (i=0; i<77; i++) {
            mu = (a[i] * mp) & 0x1fffffffffffffL;
            sp_4096_mul_add_78(a+i, m, mu);
            a[i+1] += a[i] >> 53;
        }
        mu = (a[i] * mp) & 0x7fffL;
        sp_4096_mul_add_78(a+i, m, mu);
        a[i+1] += a[i] >> 53;
        a[i] &= 0x1fffffffffffffL;
    }
    else {
        for (i=0; i<77; i++) {
            mu = a[i] & 0x1fffffffffffffL;
            sp_4096_mul_add_78(a+i, m, mu);
            a[i+1] += a[i] >> 53;
        }
        mu = a[i] & 0x7fffL;
        sp_4096_mul_add_78(a+i, m, mu);
        a[i+1] += a[i] >> 53;
        a[i] &= 0x1fffffffffffffL;
    }
#else
    for (i=0; i<77; i++) {
        mu = (a[i] * mp) & 0x1fffffffffffffL;
        sp_4096_mul_add_78(a+i, m, mu);
        a[i+1] += a[i] >> 53;
    }
    mu = (a[i] * mp) & 0x7fffL;
    sp_4096_mul_add_78(a+i, m, mu);
    a[i+1] += a[i] >> 53;
    a[i] &= 0x1fffffffffffffL;
#endif

    sp_4096_mont_shift_78(a, a);
    sp_4096_cond_sub_78(a, a, m, 0 - (((a[77] >> 15) > 0) ?
            (sp_digit)1 : (sp_digit)0));
    sp_4096_norm_78(a);
}

/* Multiply two Montogmery form numbers mod the modulus (prime).
 * (r = a * b mod m)
 *
 * r   Result of multiplication.
 * a   First number to multiply in Montogmery form.
 * b   Second number to multiply in Montogmery form.
 * m   Modulus (prime).
 * mp  Montogmery mulitplier.
 */
static void sp_4096_mont_mul_78(sp_digit* r, const sp_digit* a, const sp_digit* b,
        const sp_digit* m, sp_digit mp)
{
    sp_4096_mul_78(r, a, b);
    sp_4096_mont_reduce_78(r, m, mp);
}

/* Square the Montgomery form number. (r = a * a mod m)
 *
 * r   Result of squaring.
 * a   Number to square in Montogmery form.
 * m   Modulus (prime).
 * mp  Montogmery mulitplier.
 */
static void sp_4096_mont_sqr_78(sp_digit* r, const sp_digit* a, const sp_digit* m,
        sp_digit mp)
{
    sp_4096_sqr_78(r, a);
    sp_4096_mont_reduce_78(r, m, mp);
}

/* Multiply a by scalar b into r. (r = a * b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A scalar.
 */
SP_NOINLINE static void sp_4096_mul_d_156(sp_digit* r, const sp_digit* a,
    sp_digit b)
{
#ifdef WOLFSSL_SP_SMALL
    int128_t tb = b;
    int128_t t = 0;
    int i;

    for (i = 0; i < 156; i++) {
        t += tb * a[i];
        r[i] = t & 0x1fffffffffffffL;
        t >>= 53;
    }
    r[156] = (sp_digit)t;
#else
    int128_t tb = b;
    int128_t t[8];
    int i;

    t[0] = tb * a[0]; r[0] = t[0] & 0x1fffffffffffffL;
    for (i = 0; i < 152; i += 8) {
        t[1] = tb * a[i+1];
        r[i+1] = (sp_digit)(t[0] >> 53) + (t[1] & 0x1fffffffffffffL);
        t[2] = tb * a[i+2];
        r[i+2] = (sp_digit)(t[1] >> 53) + (t[2] & 0x1fffffffffffffL);
        t[3] = tb * a[i+3];
        r[i+3] = (sp_digit)(t[2] >> 53) + (t[3] & 0x1fffffffffffffL);
        t[4] = tb * a[i+4];
        r[i+4] = (sp_digit)(t[3] >> 53) + (t[4] & 0x1fffffffffffffL);
        t[5] = tb * a[i+5];
        r[i+5] = (sp_digit)(t[4] >> 53) + (t[5] & 0x1fffffffffffffL);
        t[6] = tb * a[i+6];
        r[i+6] = (sp_digit)(t[5] >> 53) + (t[6] & 0x1fffffffffffffL);
        t[7] = tb * a[i+7];
        r[i+7] = (sp_digit)(t[6] >> 53) + (t[7] & 0x1fffffffffffffL);
        t[0] = tb * a[i+8];
        r[i+8] = (sp_digit)(t[7] >> 53) + (t[0] & 0x1fffffffffffffL);
    }
    t[1] = tb * a[153];
    r[153] = (sp_digit)(t[0] >> 53) + (t[1] & 0x1fffffffffffffL);
    t[2] = tb * a[154];
    r[154] = (sp_digit)(t[1] >> 53) + (t[2] & 0x1fffffffffffffL);
    t[3] = tb * a[155];
    r[155] = (sp_digit)(t[2] >> 53) + (t[3] & 0x1fffffffffffffL);
    r[156] =  (sp_digit)(t[3] >> 53);
#endif /* WOLFSSL_SP_SMALL */
}

/* Conditionally add a and b using the mask m.
 * m is -1 to add and 0 when not.
 *
 * r  A single precision number representing conditional add result.
 * a  A single precision number to add with.
 * b  A single precision number to add.
 * m  Mask value to apply.
 */
static void sp_4096_cond_add_78(sp_digit* r, const sp_digit* a,
        const sp_digit* b, const sp_digit m)
{
#ifdef WOLFSSL_SP_SMALL
    int i;

    for (i = 0; i < 78; i++) {
        r[i] = a[i] + (b[i] & m);
    }
#else
    int i;

    for (i = 0; i < 72; i += 8) {
        r[i + 0] = a[i + 0] + (b[i + 0] & m);
        r[i + 1] = a[i + 1] + (b[i + 1] & m);
        r[i + 2] = a[i + 2] + (b[i + 2] & m);
        r[i + 3] = a[i + 3] + (b[i + 3] & m);
        r[i + 4] = a[i + 4] + (b[i + 4] & m);
        r[i + 5] = a[i + 5] + (b[i + 5] & m);
        r[i + 6] = a[i + 6] + (b[i + 6] & m);
        r[i + 7] = a[i + 7] + (b[i + 7] & m);
    }
    r[72] = a[72] + (b[72] & m);
    r[73] = a[73] + (b[73] & m);
    r[74] = a[74] + (b[74] & m);
    r[75] = a[75] + (b[75] & m);
    r[76] = a[76] + (b[76] & m);
    r[77] = a[77] + (b[77] & m);
#endif /* WOLFSSL_SP_SMALL */
}

#ifdef WOLFSSL_SMALL
/* Sub b from a into r. (r = a - b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A single precision integer.
 */
SP_NOINLINE static int sp_4096_sub_78(sp_digit* r, const sp_digit* a,
        const sp_digit* b)
{
    int i;

    for (i = 0; i < 78; i++) {
        r[i] = a[i] - b[i];
    }

    return 0;
}

#endif
#ifdef WOLFSSL_SMALL
/* Add b to a into r. (r = a + b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A single precision integer.
 */
SP_NOINLINE static int sp_4096_add_78(sp_digit* r, const sp_digit* a,
        const sp_digit* b)
{
    int i;

    for (i = 0; i < 78; i++) {
        r[i] = a[i] + b[i];
    }

    return 0;
}
#endif
SP_NOINLINE static void sp_4096_rshift_78(sp_digit* r, sp_digit* a, byte n)
{
    int i;

#ifdef WOLFSSL_SP_SMALL
    for (i=0; i<77; i++) {
        r[i] = ((a[i] >> n) | (a[i + 1] << (53 - n))) & 0x1fffffffffffffL;
    }
#else
    for (i=0; i<72; i += 8) {
        r[i+0] = ((a[i+0] >> n) | (a[i+1] << (53 - n))) & 0x1fffffffffffffL;
        r[i+1] = ((a[i+1] >> n) | (a[i+2] << (53 - n))) & 0x1fffffffffffffL;
        r[i+2] = ((a[i+2] >> n) | (a[i+3] << (53 - n))) & 0x1fffffffffffffL;
        r[i+3] = ((a[i+3] >> n) | (a[i+4] << (53 - n))) & 0x1fffffffffffffL;
        r[i+4] = ((a[i+4] >> n) | (a[i+5] << (53 - n))) & 0x1fffffffffffffL;
        r[i+5] = ((a[i+5] >> n) | (a[i+6] << (53 - n))) & 0x1fffffffffffffL;
        r[i+6] = ((a[i+6] >> n) | (a[i+7] << (53 - n))) & 0x1fffffffffffffL;
        r[i+7] = ((a[i+7] >> n) | (a[i+8] << (53 - n))) & 0x1fffffffffffffL;
    }
    r[72] = ((a[72] >> n) | (a[73] << (53 - n))) & 0x1fffffffffffffL;
    r[73] = ((a[73] >> n) | (a[74] << (53 - n))) & 0x1fffffffffffffL;
    r[74] = ((a[74] >> n) | (a[75] << (53 - n))) & 0x1fffffffffffffL;
    r[75] = ((a[75] >> n) | (a[76] << (53 - n))) & 0x1fffffffffffffL;
    r[76] = ((a[76] >> n) | (a[77] << (53 - n))) & 0x1fffffffffffffL;
#endif
    r[77] = a[77] >> n;
}

#ifdef WOLFSSL_SP_DIV_64
static WC_INLINE sp_digit sp_4096_div_word_78(sp_digit d1, sp_digit d0,
    sp_digit dv)
{
    sp_digit d, r, t;

    /* All 53 bits from d1 and top 10 bits from d0. */
    d = (d1 << 10) | (d0 >> 43);
    r = d / dv;
    d -= r * dv;
    /* Up to 11 bits in r */
    /* Next 10 bits from d0. */
    r <<= 10;
    d <<= 10;
    d |= (d0 >> 33) & ((1 << 10) - 1);
    t = d / dv;
    d -= t * dv;
    r += t;
    /* Up to 21 bits in r */
    /* Next 10 bits from d0. */
    r <<= 10;
    d <<= 10;
    d |= (d0 >> 23) & ((1 << 10) - 1);
    t = d / dv;
    d -= t * dv;
    r += t;
    /* Up to 31 bits in r */
    /* Next 10 bits from d0. */
    r <<= 10;
    d <<= 10;
    d |= (d0 >> 13) & ((1 << 10) - 1);
    t = d / dv;
    d -= t * dv;
    r += t;
    /* Up to 41 bits in r */
    /* Next 10 bits from d0. */
    r <<= 10;
    d <<= 10;
    d |= (d0 >> 3) & ((1 << 10) - 1);
    t = d / dv;
    d -= t * dv;
    r += t;
    /* Up to 51 bits in r */
    /* Remaining 3 bits from d0. */
    r <<= 3;
    d <<= 3;
    d |= d0 & ((1 << 3) - 1);
    t = d / dv;
    r += t;

    return r;
}
#endif /* WOLFSSL_SP_DIV_64 */

/* Divide d in a and put remainder into r (m*d + r = a)
 * m is not calculated as it is not needed at this time.
 *
 * a  Nmber to be divided.
 * d  Number to divide with.
 * m  Multiplier result.
 * r  Remainder from the division.
 * returns MEMORY_E when unable to allocate memory and MP_OKAY otherwise.
 */
static int sp_4096_div_78(const sp_digit* a, const sp_digit* d, sp_digit* m,
        sp_digit* r)
{
    int i;
#ifndef WOLFSSL_SP_DIV_64
    int128_t d1;
#endif
    sp_digit dv, r1;
#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    sp_digit* td;
#else
    sp_digit t1d[156 + 1], t2d[78 + 1], sdd[78 + 1];
#endif
    sp_digit* t1;
    sp_digit* t2;
    sp_digit* sd;
    int err = MP_OKAY;

    (void)m;

#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    td = (sp_digit*)XMALLOC(sizeof(sp_digit) * (4 * 78 + 3), NULL,
                                                       DYNAMIC_TYPE_TMP_BUFFER);
    if (td == NULL) {
        err = MEMORY_E;
    }
#endif

    (void)m;

    if (err == MP_OKAY) {
#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
        t1 = td;
        t2 = td + 156 + 1;
        sd = t2 + 78 + 1;
#else
        t1 = t1d;
        t2 = t2d;
        sd = sdd;
#endif

        sp_4096_mul_d_78(sd, d, 1L << 38);
        sp_4096_mul_d_156(t1, a, 1L << 38);
        dv = sd[77];
        for (i=78; i>=0; i--) {
            t1[78 + i] += t1[78 + i - 1] >> 53;
            t1[78 + i - 1] &= 0x1fffffffffffffL;
#ifndef WOLFSSL_SP_DIV_64
            d1 = t1[78 + i];
            d1 <<= 53;
            d1 += t1[78 + i - 1];
            r1 = (sp_digit)(d1 / dv);
#else
            r1 = sp_4096_div_word_78(t1[78 + i], t1[78 + i - 1], dv);
#endif

            sp_4096_mul_d_78(t2, sd, r1);
            (void)sp_4096_sub_78(&t1[i], &t1[i], t2);
            t1[78 + i] -= t2[78];
            t1[78 + i] += t1[78 + i - 1] >> 53;
            t1[78 + i - 1] &= 0x1fffffffffffffL;
            r1 = (((-t1[78 + i]) << 53) - t1[78 + i - 1]) / dv;
            r1 -= t1[78 + i];
            sp_4096_mul_d_78(t2, sd, r1);
            (void)sp_4096_add_78(&t1[i], &t1[i], t2);
            t1[78 + i] += t1[78 + i - 1] >> 53;
            t1[78 + i - 1] &= 0x1fffffffffffffL;
        }
        t1[78 - 1] += t1[78 - 2] >> 53;
        t1[78 - 2] &= 0x1fffffffffffffL;
        r1 = t1[78 - 1] / dv;

        sp_4096_mul_d_78(t2, sd, r1);
        sp_4096_sub_78(t1, t1, t2);
        XMEMCPY(r, t1, sizeof(*r) * 2U * 78U);
        for (i=0; i<77; i++) {
            r[i+1] += r[i] >> 53;
            r[i] &= 0x1fffffffffffffL;
        }
        sp_4096_cond_add_78(r, r, sd, 0 - ((r[77] < 0) ?
                    (sp_digit)1 : (sp_digit)0));

        sp_4096_norm_78(r);
        sp_4096_rshift_78(r, r, 38);
    }

#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (td != NULL) {
        XFREE(td, NULL, DYNAMIC_TYPE_TMP_BUFFER);
    }
#endif

    return err;
}

/* Reduce a modulo m into r. (r = a mod m)
 *
 * r  A single precision number that is the reduced result.
 * a  A single precision number that is to be reduced.
 * m  A single precision number that is the modulus to reduce with.
 * returns MEMORY_E when unable to allocate memory and MP_OKAY otherwise.
 */
static int sp_4096_mod_78(sp_digit* r, const sp_digit* a, const sp_digit* m)
{
    return sp_4096_div_78(a, m, NULL, r);
}

#if (defined(WOLFSSL_HAVE_SP_RSA) && !defined(WOLFSSL_RSA_PUBLIC_ONLY)) || \
                                                     defined(WOLFSSL_HAVE_SP_DH)
/* Modular exponentiate a to the e mod m. (r = a^e mod m)
 *
 * r     A single precision number that is the result of the operation.
 * a     A single precision number being exponentiated.
 * e     A single precision number that is the exponent.
 * bits  The number of bits in the exponent.
 * m     A single precision number that is the modulus.
 * returns 0 on success and MEMORY_E on dynamic memory allocation failure.
 */
static int sp_4096_mod_exp_78(sp_digit* r, const sp_digit* a, const sp_digit* e, int bits,
    const sp_digit* m, int reduceA)
{
#ifdef WOLFSSL_SP_SMALL
#if !defined(WOLFSSL_SP_NO_MALLOC)
    sp_digit* td;
#else
    sp_digit td[3 * 156];
#endif
    sp_digit* t[3];
    sp_digit* norm;
    sp_digit mp = 1;
    sp_digit n;
    int i;
    int c, y;
    int err = MP_OKAY;

#if !defined(WOLFSSL_SP_NO_MALLOC)
    td = (sp_digit*)XMALLOC(sizeof(sp_digit) * 3 * 78 * 2, NULL,
                            DYNAMIC_TYPE_TMP_BUFFER);
    if (td == NULL) {
        err = MEMORY_E;
    }
#endif

    if (err == MP_OKAY) {
        norm = td;
        for (i=0; i<3; i++) {
#if !defined(WOLFSSL_SP_NO_MALLOC)
            t[i] = td + (i * 78 * 2);
#else
            t[i] = &td[i * 78 * 2];
#endif
            XMEMSET(t[i], 0, sizeof(sp_digit) * 78U * 2U);
        }

        sp_4096_mont_setup(m, &mp);
        sp_4096_mont_norm_78(norm, m);

        if (reduceA != 0) {
            err = sp_4096_mod_78(t[1], a, m);
        }
        else {
            XMEMCPY(t[1], a, sizeof(sp_digit) * 78U);
        }
    }
    if (err == MP_OKAY) {
        sp_4096_mul_78(t[1], t[1], norm);
        err = sp_4096_mod_78(t[1], t[1], m);
    }

    if (err == MP_OKAY) {
        i = bits / 53;
        c = bits % 53;
        n = e[i--] << (53 - c);
        for (; ; c--) {
            if (c == 0) {
                if (i == -1) {
                    break;
                }

                n = e[i--];
                c = 53;
            }

            y = (n >> 52) & 1;
            n <<= 1;

            sp_4096_mont_mul_78(t[y^1], t[0], t[1], m, mp);

            XMEMCPY(t[2], (void*)(((size_t)t[0] & addr_mask[y^1]) +
                                  ((size_t)t[1] & addr_mask[y])),
                                  sizeof(*t[2]) * 78 * 2);
            sp_4096_mont_sqr_78(t[2], t[2], m, mp);
            XMEMCPY((void*)(((size_t)t[0] & addr_mask[y^1]) +
                            ((size_t)t[1] & addr_mask[y])), t[2],
                            sizeof(*t[2]) * 78 * 2);
        }

        sp_4096_mont_reduce_78(t[0], m, mp);
        n = sp_4096_cmp_78(t[0], m);
        sp_4096_cond_sub_78(t[0], t[0], m, ((n < 0) ?
                    (sp_digit)1 : (sp_digit)0) - 1);
        XMEMCPY(r, t[0], sizeof(*r) * 78 * 2);

    }

#if !defined(WOLFSSL_SP_NO_MALLOC)
    if (td != NULL) {
        XFREE(td, NULL, DYNAMIC_TYPE_TMP_BUFFER);
    }
#endif

    return err;
#elif !defined(WC_NO_CACHE_RESISTANT)
#if defined(WOLFSSL_SMALL_STACK) && !defined(WOLFSSL_SP_NO_MALLOC)
    sp_digit* td;
#else
    sp_digit td[3 * 156];
#endif
    sp_digit* t[3];
    sp_digit* norm;
    sp_digit mp = 1;
    sp_digit n;
    int i;
    int c, y;
    int err = MP_OKAY;

#ifdef WOLFSSL_SMALL_STACK
    td = (sp_digit*)XMALLOC(sizeof(sp_digit) * 3 * 78 * 2, NULL,
                            DYNAMIC_TYPE_TMP_BUFFER);
    if (td == NULL) {
        err = MEMORY_E;
    }
#endif

    if (err == MP_OKAY) {
        norm = td;
        for (i=0; i<3; i++) {
#if defined(WOLFSSL_SMALL_STACK) && !defined(WOLFSSL_SP_NO_MALLOC)
            t[i] = td + (i * 78 * 2);
#else
            t[i] = &td[i * 78 * 2];
#endif
        }

        sp_4096_mont_setup(m, &mp);
        sp_4096_mont_norm_78(norm, m);

        if (reduceA != 0) {
            err = sp_4096_mod_78(t[1], a, m);
            if (err == MP_OKAY) {
                sp_4096_mul_78(t[1], t[1], norm);
                err = sp_4096_mod_78(t[1], t[1], m);
            }
        }
        else {
            sp_4096_mul_78(t[1], a, norm);
            err = sp_4096_mod_78(t[1], t[1], m);
        }
    }

    if (err == MP_OKAY) {
        i = bits / 53;
        c = bits % 53;
        n = e[i--] << (53 - c);
        for (; ; c--) {
            if (c == 0) {
                if (i == -1) {
                    break;
                }

                n = e[i--];
                c = 53;
            }

            y = (n >> 52) & 1;
            n <<= 1;

            sp_4096_mont_mul_78(t[y^1], t[0], t[1], m, mp);

            XMEMCPY(t[2], (void*)(((size_t)t[0] & addr_mask[y^1]) +
                                  ((size_t)t[1] & addr_mask[y])), 
                                  sizeof(*t[2]) * 78 * 2);
            sp_4096_mont_sqr_78(t[2], t[2], m, mp);
            XMEMCPY((void*)(((size_t)t[0] & addr_mask[y^1]) +
                            ((size_t)t[1] & addr_mask[y])), t[2], 
                            sizeof(*t[2]) * 78 * 2);
        }

        sp_4096_mont_reduce_78(t[0], m, mp);
        n = sp_4096_cmp_78(t[0], m);
        sp_4096_cond_sub_78(t[0], t[0], m, ((n < 0) ?
                    (sp_digit)1 : (sp_digit)0) - 1);
        XMEMCPY(r, t[0], sizeof(*r) * 78 * 2);
    }

#ifdef WOLFSSL_SMALL_STACK
    if (td != NULL) {
        XFREE(td, NULL, DYNAMIC_TYPE_TMP_BUFFER);
    }
#endif

    return err;
#else
#if defined(WOLFSSL_SMALL_STACK) && !defined(WOLFSSL_SP_NO_MALLOC)
    sp_digit* td;
#else
    sp_digit td[(32 * 156) + 156];
#endif
    sp_digit* t[32];
    sp_digit* rt;
    sp_digit* norm;
    sp_digit mp = 1;
    sp_digit n;
    int i;
    int c, y;
    int err = MP_OKAY;

#if defined(WOLFSSL_SMALL_STACK) && !defined(WOLFSSL_SP_NO_MALLOC)
    td = (sp_digit*)XMALLOC(sizeof(sp_digit) * ((32 * 156) + 156), NULL,
                            DYNAMIC_TYPE_TMP_BUFFER);
    if (td == NULL) {
        err = MEMORY_E;
    }
#endif

    if (err == MP_OKAY) {
        norm = td;
#if defined(WOLFSSL_SMALL_STACK) && !defined(WOLFSSL_SP_NO_MALLOC)
        for (i=0; i<32; i++)
            t[i] = td + i * 156;
        rt = td + 4992;
#else
        for (i=0; i<32; i++)
            t[i] = &td[i * 156];
        rt = &td[4992];
#endif

        sp_4096_mont_setup(m, &mp);
        sp_4096_mont_norm_78(norm, m);

        if (reduceA != 0) {
            err = sp_4096_mod_78(t[1], a, m);
            if (err == MP_OKAY) {
                sp_4096_mul_78(t[1], t[1], norm);
                err = sp_4096_mod_78(t[1], t[1], m);
            }
        }
        else {
            sp_4096_mul_78(t[1], a, norm);
            err = sp_4096_mod_78(t[1], t[1], m);
        }
    }

    if (err == MP_OKAY) {
        sp_4096_mont_sqr_78(t[ 2], t[ 1], m, mp);
        sp_4096_mont_mul_78(t[ 3], t[ 2], t[ 1], m, mp);
        sp_4096_mont_sqr_78(t[ 4], t[ 2], m, mp);
        sp_4096_mont_mul_78(t[ 5], t[ 3], t[ 2], m, mp);
        sp_4096_mont_sqr_78(t[ 6], t[ 3], m, mp);
        sp_4096_mont_mul_78(t[ 7], t[ 4], t[ 3], m, mp);
        sp_4096_mont_sqr_78(t[ 8], t[ 4], m, mp);
        sp_4096_mont_mul_78(t[ 9], t[ 5], t[ 4], m, mp);
        sp_4096_mont_sqr_78(t[10], t[ 5], m, mp);
        sp_4096_mont_mul_78(t[11], t[ 6], t[ 5], m, mp);
        sp_4096_mont_sqr_78(t[12], t[ 6], m, mp);
        sp_4096_mont_mul_78(t[13], t[ 7], t[ 6], m, mp);
        sp_4096_mont_sqr_78(t[14], t[ 7], m, mp);
        sp_4096_mont_mul_78(t[15], t[ 8], t[ 7], m, mp);
        sp_4096_mont_sqr_78(t[16], t[ 8], m, mp);
        sp_4096_mont_mul_78(t[17], t[ 9], t[ 8], m, mp);
        sp_4096_mont_sqr_78(t[18], t[ 9], m, mp);
        sp_4096_mont_mul_78(t[19], t[10], t[ 9], m, mp);
        sp_4096_mont_sqr_78(t[20], t[10], m, mp);
        sp_4096_mont_mul_78(t[21], t[11], t[10], m, mp);
        sp_4096_mont_sqr_78(t[22], t[11], m, mp);
        sp_4096_mont_mul_78(t[23], t[12], t[11], m, mp);
        sp_4096_mont_sqr_78(t[24], t[12], m, mp);
        sp_4096_mont_mul_78(t[25], t[13], t[12], m, mp);
        sp_4096_mont_sqr_78(t[26], t[13], m, mp);
        sp_4096_mont_mul_78(t[27], t[14], t[13], m, mp);
        sp_4096_mont_sqr_78(t[28], t[14], m, mp);
        sp_4096_mont_mul_78(t[29], t[15], t[14], m, mp);
        sp_4096_mont_sqr_78(t[30], t[15], m, mp);
        sp_4096_mont_mul_78(t[31], t[16], t[15], m, mp);

        bits = ((bits + 4) / 5) * 5;
        i = ((bits + 52) / 53) - 1;
        c = bits % 53;
        if (c == 0) {
            c = 53;
        }
        if (i < 78) {
            n = e[i--] << (64 - c);
        }
        else {
            n = 0;
            i--;
        }
        if (c < 5) {
            n |= e[i--] << (11 - c);
            c += 53;
        }
        y = (n >> 59) & 0x1f;
        n <<= 5;
        c -= 5;
        XMEMCPY(rt, t[y], sizeof(sp_digit) * 156);
        for (; i>=0 || c>=5; ) {
            if (c < 5) {
                n |= e[i--] << (11 - c);
                c += 53;
            }
            y = (n >> 59) & 0x1f;
            n <<= 5;
            c -= 5;

            sp_4096_mont_sqr_78(rt, rt, m, mp);
            sp_4096_mont_sqr_78(rt, rt, m, mp);
            sp_4096_mont_sqr_78(rt, rt, m, mp);
            sp_4096_mont_sqr_78(rt, rt, m, mp);
            sp_4096_mont_sqr_78(rt, rt, m, mp);

            sp_4096_mont_mul_78(rt, rt, t[y], m, mp);
        }

        sp_4096_mont_reduce_78(rt, m, mp);
        n = sp_4096_cmp_78(rt, m);
        sp_4096_cond_sub_78(rt, rt, m, ((n < 0) ?
                   (sp_digit)1 : (sp_digit)0) - 1);
        XMEMCPY(r, rt, sizeof(sp_digit) * 156);
    }

#if defined(WOLFSSL_SMALL_STACK) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (td != NULL) {
        XFREE(td, NULL, DYNAMIC_TYPE_TMP_BUFFER);
    }
#endif

    return err;
#endif
}
#endif /* (WOLFSSL_HAVE_SP_RSA && !WOLFSSL_RSA_PUBLIC_ONLY) || */
       /* WOLFSSL_HAVE_SP_DH */

#ifdef WOLFSSL_HAVE_SP_RSA
/* RSA public key operation.
 *
 * in      Array of bytes representing the number to exponentiate, base.
 * inLen   Number of bytes in base.
 * em      Public exponent.
 * mm      Modulus.
 * out     Buffer to hold big-endian bytes of exponentiation result.
 *         Must be at least 512 bytes long.
 * outLen  Number of bytes in result.
 * returns 0 on success, MP_TO_E when the outLen is too small, MP_READ_E when
 * an array is too long and MEMORY_E when dynamic memory allocation fails.
 */
int sp_RsaPublic_4096(const byte* in, word32 inLen, mp_int* em, mp_int* mm,
    byte* out, word32* outLen)
{
#ifdef WOLFSSL_SP_SMALL
    sp_digit* d = NULL;
    sp_digit* a;
    sp_digit* m;
    sp_digit* r;
    sp_digit* norm;
    sp_digit e[1] = {0};
    sp_digit mp;
    int i;
    int err = MP_OKAY;

    if (*outLen < 512U) {
        err = MP_TO_E;
    }

    if (err == MP_OKAY) {
        if (mp_count_bits(em) > 53) {
            err = MP_READ_E;
        }
        if (inLen > 512U) {
            err = MP_READ_E;
        }
        if (mp_count_bits(mm) != 4096) {
            err = MP_READ_E;
        }
    }

    if (err == MP_OKAY) {
        d = (sp_digit*)XMALLOC(sizeof(sp_digit) * 78 * 5, NULL,
                                                              DYNAMIC_TYPE_RSA);
        if (d == NULL)
            err = MEMORY_E;
    }

    if (err == MP_OKAY) {
        a = d;
        r = a + 78 * 2;
        m = r + 78 * 2;
        norm = r;

        sp_4096_from_bin(a, 78, in, inLen);
#if DIGIT_BIT >= 53
        e[0] = (sp_digit)em->dp[0];
#else
        e[0] = (sp_digit)em->dp[0];
        if (em->used > 1) {
            e[0] |= ((sp_digit)em->dp[1]) << DIGIT_BIT;
        }
#endif
        if (e[0] == 0) {
            err = MP_EXPTMOD_E;
        }
    }

    if (err == MP_OKAY) {
        sp_4096_from_mp(m, 78, mm);

        sp_4096_mont_setup(m, &mp);
        sp_4096_mont_norm_78(norm, m);
    }
    if (err == MP_OKAY) {
        sp_4096_mul_78(a, a, norm);
        err = sp_4096_mod_78(a, a, m);
    }
    if (err == MP_OKAY) {
        for (i=52; i>=0; i--) {
            if ((e[0] >> i) != 0) {
                break;
            }
        }

        XMEMCPY(r, a, sizeof(sp_digit) * 78 * 2);
        for (i--; i>=0; i--) {
            sp_4096_mont_sqr_78(r, r, m, mp);

            if (((e[0] >> i) & 1) == 1) {
                sp_4096_mont_mul_78(r, r, a, m, mp);
            }
        }
        sp_4096_mont_reduce_78(r, m, mp);
        mp = sp_4096_cmp_78(r, m);
        sp_4096_cond_sub_78(r, r, m, ((mp < 0) ?
                    (sp_digit)1 : (sp_digit)0)- 1);

        sp_4096_to_bin(r, out);
        *outLen = 512;
    }

    if (d != NULL) {
        XFREE(d, NULL, DYNAMIC_TYPE_RSA);
    }

    return err;
#else
#if (!defined(WOLFSSL_SP_SMALL) && !defined(WOLFSSL_SMALL_STACK)) || defined(WOLFSSL_SP_NO_MALLOC)
    sp_digit ad[156], md[78], rd[156];
#else
    sp_digit* d = NULL;
#endif
    sp_digit* a;
    sp_digit* m;
    sp_digit* r;
    sp_digit e[1] = {0};
    int err = MP_OKAY;

    if (*outLen < 512U) {
        err = MP_TO_E;
    }
    if (err == MP_OKAY) {
        if (mp_count_bits(em) > 53) {
            err = MP_READ_E;
        }
        if (inLen > 512U) {
            err = MP_READ_E;
        }
        if (mp_count_bits(mm) != 4096) {
            err = MP_READ_E;
        }
    }

#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (err == MP_OKAY) {
        d = (sp_digit*)XMALLOC(sizeof(sp_digit) * 78 * 5, NULL,
                                                              DYNAMIC_TYPE_RSA);
        if (d == NULL) {
            err = MEMORY_E;
        }
    }

    if (err == MP_OKAY) {
        a = d;
        r = a + 78 * 2;
        m = r + 78 * 2;
    }
#else
    a = ad;
    m = md;
    r = rd;
#endif

    if (err == MP_OKAY) {
        sp_4096_from_bin(a, 78, in, inLen);
#if DIGIT_BIT >= 53
        e[0] = (sp_digit)em->dp[0];
#else
        e[0] = (sp_digit)em->dp[0];
        if (em->used > 1) {
            e[0] |= ((sp_digit)em->dp[1]) << DIGIT_BIT;
        }
#endif
        if (e[0] == 0) {
            err = MP_EXPTMOD_E;
        }
    }
    if (err == MP_OKAY) {
        sp_4096_from_mp(m, 78, mm);

        if (e[0] == 0x3) {
            sp_4096_sqr_78(r, a);
            err = sp_4096_mod_78(r, r, m);
            if (err == MP_OKAY) {
                sp_4096_mul_78(r, a, r);
                err = sp_4096_mod_78(r, r, m);
            }
        }
        else {
            sp_digit* norm = r;
            int i;
            sp_digit mp;

            sp_4096_mont_setup(m, &mp);
            sp_4096_mont_norm_78(norm, m);

            sp_4096_mul_78(a, a, norm);
            err = sp_4096_mod_78(a, a, m);

            if (err == MP_OKAY) {
                for (i=52; i>=0; i--) {
                    if ((e[0] >> i) != 0) {
                        break;
                    }
                }

                XMEMCPY(r, a, sizeof(sp_digit) * 156U);
                for (i--; i>=0; i--) {
                    sp_4096_mont_sqr_78(r, r, m, mp);

                    if (((e[0] >> i) & 1) == 1) {
                        sp_4096_mont_mul_78(r, r, a, m, mp);
                    }
                }
                sp_4096_mont_reduce_78(r, m, mp);
                mp = sp_4096_cmp_78(r, m);
                sp_4096_cond_sub_78(r, r, m, ((mp < 0) ?
                           (sp_digit)1 : (sp_digit)0) - 1);
            }
        }
    }

    if (err == MP_OKAY) {
        sp_4096_to_bin(r, out);
        *outLen = 512;
    }

#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (d != NULL) {
        XFREE(d, NULL, DYNAMIC_TYPE_RSA);
    }
#endif

    return err;
#endif /* WOLFSSL_SP_SMALL */
}

#ifndef WOLFSSL_RSA_PUBLIC_ONLY
#if !defined(SP_RSA_PRIVATE_EXP_D) && !defined(RSA_LOW_MEM)
#endif /* !SP_RSA_PRIVATE_EXP_D && !RSA_LOW_MEM */
/* RSA private key operation.
 *
 * in      Array of bytes representing the number to exponentiate, base.
 * inLen   Number of bytes in base.
 * dm      Private exponent.
 * pm      First prime.
 * qm      Second prime.
 * dpm     First prime's CRT exponent.
 * dqm     Second prime's CRT exponent.
 * qim     Inverse of second prime mod p.
 * mm      Modulus.
 * out     Buffer to hold big-endian bytes of exponentiation result.
 *         Must be at least 512 bytes long.
 * outLen  Number of bytes in result.
 * returns 0 on success, MP_TO_E when the outLen is too small, MP_READ_E when
 * an array is too long and MEMORY_E when dynamic memory allocation fails.
 */
int sp_RsaPrivate_4096(const byte* in, word32 inLen, mp_int* dm,
    mp_int* pm, mp_int* qm, mp_int* dpm, mp_int* dqm, mp_int* qim, mp_int* mm,
    byte* out, word32* outLen)
{
#if defined(SP_RSA_PRIVATE_EXP_D) || defined(RSA_LOW_MEM)
#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    sp_digit* a = NULL;
    sp_digit* d = NULL;
    sp_digit* m = NULL;
    sp_digit* r = NULL;
    int err = MP_OKAY;

    (void)pm;
    (void)qm;
    (void)dpm;
    (void)dqm;
    (void)qim;

    if (*outLen < 512U) {
        err = MP_TO_E;
    }
    if (err == MP_OKAY) {
        if (mp_count_bits(dm) > 4096) {
           err = MP_READ_E;
        }
        if (inLen > 512) {
            err = MP_READ_E;
        }
        if (mp_count_bits(mm) != 4096) {
            err = MP_READ_E;
        }
    }

    if (err == MP_OKAY) {
        d = (sp_digit*)XMALLOC(sizeof(sp_digit) * 78 * 4, NULL,
                                                              DYNAMIC_TYPE_RSA);
        if (d == NULL) {
            err = MEMORY_E;
        }
    }
    if (err == MP_OKAY) {
        a = d + 78;
        m = a + 156;
        r = a;

        sp_4096_from_bin(a, 78, in, inLen);
        sp_4096_from_mp(d, 78, dm);
        sp_4096_from_mp(m, 78, mm);
        err = sp_4096_mod_exp_78(r, a, d, 4096, m, 0);
    }
    if (err == MP_OKAY) {
        sp_4096_to_bin(r, out);
        *outLen = 512;
    }

    if (d != NULL) {
        XMEMSET(d, 0, sizeof(sp_digit) * 78);
        XFREE(d, NULL, DYNAMIC_TYPE_RSA);
    }

    return err;
#else
    sp_digit a[156], d[78], m[78];
    sp_digit* r = a;
    int err = MP_OKAY;

    (void)pm;
    (void)qm;
    (void)dpm;
    (void)dqm;
    (void)qim;

    if (*outLen < 512U) {
        err = MP_TO_E;
    }
    if (err == MP_OKAY) {
        if (mp_count_bits(dm) > 4096) {
            err = MP_READ_E;
        }
        if (inLen > 512U) {
            err = MP_READ_E;
        }
        if (mp_count_bits(mm) != 4096) {
            err = MP_READ_E;
        }
    }

    if (err == MP_OKAY) {
        sp_4096_from_bin(a, 78, in, inLen);
        sp_4096_from_mp(d, 78, dm);
        sp_4096_from_mp(m, 78, mm);
        err = sp_4096_mod_exp_78(r, a, d, 4096, m, 0);
    }

    if (err == MP_OKAY) {
        sp_4096_to_bin(r, out);
        *outLen = 512;
    }

    XMEMSET(d, 0, sizeof(sp_digit) * 78);

    return err;
#endif /* WOLFSSL_SP_SMALL || defined(WOLFSSL_SMALL_STACK) */
#else
#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    sp_digit* t = NULL;
    sp_digit* a;
    sp_digit* p;
    sp_digit* q;
    sp_digit* dp;
    sp_digit* dq;
    sp_digit* qi;
    sp_digit* tmpa;
    sp_digit* tmpb;
    sp_digit* r;
    int err = MP_OKAY;

    (void)dm;
    (void)mm;

    if (*outLen < 512U) {
        err = MP_TO_E;
    }
    if (err == MP_OKAY) {
        if (inLen > 512) {
            err = MP_READ_E;
        }
        if (mp_count_bits(mm) != 4096) {
            err = MP_READ_E;
        }
    }

    if (err == MP_OKAY) {
        t = (sp_digit*)XMALLOC(sizeof(sp_digit) * 39 * 11, NULL,
                                                              DYNAMIC_TYPE_RSA);
        if (t == NULL) {
            err = MEMORY_E;
        }
    }
    if (err == MP_OKAY) {
        a = t;
        p = a + 78 * 2;
        q = p + 39;
        qi = dq = dp = q + 39;
        tmpa = qi + 39;
        tmpb = tmpa + 78;

        r = t + 78;

        sp_4096_from_bin(a, 78, in, inLen);
        sp_4096_from_mp(p, 39, pm);
        sp_4096_from_mp(q, 39, qm);
        sp_4096_from_mp(dp, 39, dpm);
        err = sp_4096_mod_exp_39(tmpa, a, dp, 2048, p, 1);
    }
    if (err == MP_OKAY) {
        sp_4096_from_mp(dq, 39, dqm);
        err = sp_4096_mod_exp_39(tmpb, a, dq, 2048, q, 1);
    }
    if (err == MP_OKAY) {
        (void)sp_4096_sub_39(tmpa, tmpa, tmpb);
        sp_4096_cond_add_39(tmpa, tmpa, p, 0 - ((sp_int_digit)tmpa[38] >> 63));
        sp_4096_cond_add_39(tmpa, tmpa, p, 0 - ((sp_int_digit)tmpa[38] >> 63));

        sp_4096_from_mp(qi, 39, qim);
        sp_4096_mul_39(tmpa, tmpa, qi);
        err = sp_4096_mod_39(tmpa, tmpa, p);
    }

    if (err == MP_OKAY) {
        sp_4096_mul_39(tmpa, q, tmpa);
        (void)sp_4096_add_78(r, tmpb, tmpa);
        sp_4096_norm_78(r);

        sp_4096_to_bin(r, out);
        *outLen = 512;
    }

    if (t != NULL) {
        XMEMSET(t, 0, sizeof(sp_digit) * 39 * 11);
        XFREE(t, NULL, DYNAMIC_TYPE_RSA);
    }

    return err;
#else
    sp_digit a[78 * 2];
    sp_digit p[39], q[39], dp[39], dq[39], qi[39];
    sp_digit tmpa[78], tmpb[78];
    sp_digit* r = a;
    int err = MP_OKAY;

    (void)dm;
    (void)mm;

    if (*outLen < 512U) {
        err = MP_TO_E;
    }
    if (err == MP_OKAY) {
        if (inLen > 512U) {
            err = MP_READ_E;
        }
        if (mp_count_bits(mm) != 4096) {
            err = MP_READ_E;
        }
    }

    if (err == MP_OKAY) {
        sp_4096_from_bin(a, 78, in, inLen);
        sp_4096_from_mp(p, 39, pm);
        sp_4096_from_mp(q, 39, qm);
        sp_4096_from_mp(dp, 39, dpm);
        sp_4096_from_mp(dq, 39, dqm);
        sp_4096_from_mp(qi, 39, qim);

        err = sp_4096_mod_exp_39(tmpa, a, dp, 2048, p, 1);
    }
    if (err == MP_OKAY) {
        err = sp_4096_mod_exp_39(tmpb, a, dq, 2048, q, 1);
    }

    if (err == MP_OKAY) {
        (void)sp_4096_sub_39(tmpa, tmpa, tmpb);
        sp_4096_cond_add_39(tmpa, tmpa, p, 0 - ((sp_int_digit)tmpa[38] >> 63));
        sp_4096_cond_add_39(tmpa, tmpa, p, 0 - ((sp_int_digit)tmpa[38] >> 63));
        sp_4096_mul_39(tmpa, tmpa, qi);
        err = sp_4096_mod_39(tmpa, tmpa, p);
    }

    if (err == MP_OKAY) {
        sp_4096_mul_39(tmpa, tmpa, q);
        (void)sp_4096_add_78(r, tmpb, tmpa);
        sp_4096_norm_78(r);

        sp_4096_to_bin(r, out);
        *outLen = 512;
    }

    XMEMSET(tmpa, 0, sizeof(tmpa));
    XMEMSET(tmpb, 0, sizeof(tmpb));
    XMEMSET(p, 0, sizeof(p));
    XMEMSET(q, 0, sizeof(q));
    XMEMSET(dp, 0, sizeof(dp));
    XMEMSET(dq, 0, sizeof(dq));
    XMEMSET(qi, 0, sizeof(qi));

    return err;
#endif /* WOLFSSL_SP_SMALL || defined(WOLFSSL_SMALL_STACK) */
#endif /* SP_RSA_PRIVATE_EXP_D || RSA_LOW_MEM */
}

#endif /* !WOLFSSL_RSA_PUBLIC_ONLY */
#endif /* WOLFSSL_HAVE_SP_RSA */
#if defined(WOLFSSL_HAVE_SP_DH) || (defined(WOLFSSL_HAVE_SP_RSA) && \
                                              !defined(WOLFSSL_RSA_PUBLIC_ONLY))
/* Convert an array of sp_digit to an mp_int.
 *
 * a  A single precision integer.
 * r  A multi-precision integer.
 */
static int sp_4096_to_mp(const sp_digit* a, mp_int* r)
{
    int err;

    err = mp_grow(r, (4096 + DIGIT_BIT - 1) / DIGIT_BIT);
    if (err == MP_OKAY) { /*lint !e774 case where err is always MP_OKAY*/
#if DIGIT_BIT == 53
        XMEMCPY(r->dp, a, sizeof(sp_digit) * 78);
        r->used = 78;
        mp_clamp(r);
#elif DIGIT_BIT < 53
        int i, j = 0, s = 0;

        r->dp[0] = 0;
        for (i = 0; i < 78; i++) {
            r->dp[j] |= (mp_digit)(a[i] << s);
            r->dp[j] &= (1L << DIGIT_BIT) - 1;
            s = DIGIT_BIT - s;
            r->dp[++j] = (mp_digit)(a[i] >> s);
            while (s + DIGIT_BIT <= 53) {
                s += DIGIT_BIT;
                r->dp[j++] &= (1L << DIGIT_BIT) - 1;
                if (s == SP_WORD_SIZE) {
                    r->dp[j] = 0;
                }
                else {
                    r->dp[j] = (mp_digit)(a[i] >> s);
                }
            }
            s = 53 - s;
        }
        r->used = (4096 + DIGIT_BIT - 1) / DIGIT_BIT;
        mp_clamp(r);
#else
        int i, j = 0, s = 0;

        r->dp[0] = 0;
        for (i = 0; i < 78; i++) {
            r->dp[j] |= ((mp_digit)a[i]) << s;
            if (s + 53 >= DIGIT_BIT) {
    #if DIGIT_BIT != 32 && DIGIT_BIT != 64
                r->dp[j] &= (1L << DIGIT_BIT) - 1;
    #endif
                s = DIGIT_BIT - s;
                r->dp[++j] = a[i] >> s;
                s = 53 - s;
            }
            else {
                s += 53;
            }
        }
        r->used = (4096 + DIGIT_BIT - 1) / DIGIT_BIT;
        mp_clamp(r);
#endif
    }

    return err;
}

/* Perform the modular exponentiation for Diffie-Hellman.
 *
 * base  Base. MP integer.
 * exp   Exponent. MP integer.
 * mod   Modulus. MP integer.
 * res   Result. MP integer.
 * returns 0 on success, MP_READ_E if there are too many bytes in an array
 * and MEMORY_E if memory allocation fails.
 */
int sp_ModExp_4096(mp_int* base, mp_int* exp, mp_int* mod, mp_int* res)
{
#ifdef WOLFSSL_SP_SMALL
    int err = MP_OKAY;
    sp_digit* d = NULL;
    sp_digit* b;
    sp_digit* e;
    sp_digit* m;
    sp_digit* r;
    int expBits = mp_count_bits(exp);

    if (mp_count_bits(base) > 4096) {
        err = MP_READ_E;
    }

    if (err == MP_OKAY) {
        if (expBits > 4096) {
            err = MP_READ_E;
        }
    }

    if (err == MP_OKAY) {
        if (mp_count_bits(mod) != 4096) {
            err = MP_READ_E;
        }
    }

    if (err == MP_OKAY) {
        d = (sp_digit*)XMALLOC(sizeof(*d) * 78 * 4, NULL, DYNAMIC_TYPE_DH);
        if (d == NULL) {
            err = MEMORY_E;
        }
    }

    if (err == MP_OKAY) {
        b = d;
        e = b + 78 * 2;
        m = e + 78;
        r = b;

        sp_4096_from_mp(b, 78, base);
        sp_4096_from_mp(e, 78, exp);
        sp_4096_from_mp(m, 78, mod);

        err = sp_4096_mod_exp_78(r, b, e, mp_count_bits(exp), m, 0);
    }

    if (err == MP_OKAY) {
        err = sp_4096_to_mp(r, res);
    }

    if (d != NULL) {
        XMEMSET(e, 0, sizeof(sp_digit) * 78U);
        XFREE(d, NULL, DYNAMIC_TYPE_DH);
    }
    return err;
#else
#ifndef WOLFSSL_SMALL_STACK
    sp_digit bd[156], ed[78], md[78];
#else
    sp_digit* d = NULL;
#endif
    sp_digit* b;
    sp_digit* e;
    sp_digit* m;
    sp_digit* r;
    int err = MP_OKAY;
    int expBits = mp_count_bits(exp);

    if (mp_count_bits(base) > 4096) {
        err = MP_READ_E;
    }

    if (err == MP_OKAY) {
        if (expBits > 4096) {
            err = MP_READ_E;
        }
    }
    
    if (err == MP_OKAY) {
        if (mp_count_bits(mod) != 4096) {
            err = MP_READ_E;
        }
    }

#ifdef WOLFSSL_SMALL_STACK
    if (err == MP_OKAY) {
        d = (sp_digit*)XMALLOC(sizeof(*d) * 78 * 4, NULL, DYNAMIC_TYPE_DH);
        if (d == NULL)
            err = MEMORY_E;
    }

    if (err == MP_OKAY) {
        b = d;
        e = b + 78 * 2;
        m = e + 78;
        r = b;
    }
#else
    r = b = bd;
    e = ed;
    m = md;
#endif

    if (err == MP_OKAY) {
        sp_4096_from_mp(b, 78, base);
        sp_4096_from_mp(e, 78, exp);
        sp_4096_from_mp(m, 78, mod);

        err = sp_4096_mod_exp_78(r, b, e, expBits, m, 0);
    }

    if (err == MP_OKAY) {
        err = sp_4096_to_mp(r, res);
    }


#ifdef WOLFSSL_SMALL_STACK
    if (d != NULL) {
        XMEMSET(e, 0, sizeof(sp_digit) * 78U);
        XFREE(d, NULL, DYNAMIC_TYPE_DH);
    }
#else
    XMEMSET(e, 0, sizeof(sp_digit) * 78U);
#endif

    return err;
#endif
}

#ifdef WOLFSSL_HAVE_SP_DH

#ifdef HAVE_FFDHE_4096
SP_NOINLINE static void sp_4096_lshift_78(sp_digit* r, sp_digit* a, byte n)
{
#ifdef WOLFSSL_SP_SMALL
    int i;

    r[78] = a[77] >> (53 - n);
    for (i=77; i>0; i--) {
        r[i] = ((a[i] << n) | (a[i-1] >> (53 - n))) & 0x1fffffffffffffL;
    }
#else
    sp_int_digit s, t;

    s = (sp_int_digit)a[77];
    r[78] = s >> (53U - n);
    s = (sp_int_digit)(a[77]); t = (sp_int_digit)(a[76]);
    r[77] = ((s << n) | (t >> (53U - n))) & 0x1fffffffffffffUL;
    s = (sp_int_digit)(a[76]); t = (sp_int_digit)(a[75]);
    r[76] = ((s << n) | (t >> (53U - n))) & 0x1fffffffffffffUL;
    s = (sp_int_digit)(a[75]); t = (sp_int_digit)(a[74]);
    r[75] = ((s << n) | (t >> (53U - n))) & 0x1fffffffffffffUL;
    s = (sp_int_digit)(a[74]); t = (sp_int_digit)(a[73]);
    r[74] = ((s << n) | (t >> (53U - n))) & 0x1fffffffffffffUL;
    s = (sp_int_digit)(a[73]); t = (sp_int_digit)(a[72]);
    r[73] = ((s << n) | (t >> (53U - n))) & 0x1fffffffffffffUL;
    s = (sp_int_digit)(a[72]); t = (sp_int_digit)(a[71]);
    r[72] = ((s << n) | (t >> (53U - n))) & 0x1fffffffffffffUL;
    s = (sp_int_digit)(a[71]); t = (sp_int_digit)(a[70]);
    r[71] = ((s << n) | (t >> (53U - n))) & 0x1fffffffffffffUL;
    s = (sp_int_digit)(a[70]); t = (sp_int_digit)(a[69]);
    r[70] = ((s << n) | (t >> (53U - n))) & 0x1fffffffffffffUL;
    s = (sp_int_digit)(a[69]); t = (sp_int_digit)(a[68]);
    r[69] = ((s << n) | (t >> (53U - n))) & 0x1fffffffffffffUL;
    s = (sp_int_digit)(a[68]); t = (sp_int_digit)(a[67]);
    r[68] = ((s << n) | (t >> (53U - n))) & 0x1fffffffffffffUL;
    s = (sp_int_digit)(a[67]); t = (sp_int_digit)(a[66]);
    r[67] = ((s << n) | (t >> (53U - n))) & 0x1fffffffffffffUL;
    s = (sp_int_digit)(a[66]); t = (sp_int_digit)(a[65]);
    r[66] = ((s << n) | (t >> (53U - n))) & 0x1fffffffffffffUL;
    s = (sp_int_digit)(a[65]); t = (sp_int_digit)(a[64]);
    r[65] = ((s << n) | (t >> (53U - n))) & 0x1fffffffffffffUL;
    s = (sp_int_digit)(a[64]); t = (sp_int_digit)(a[63]);
    r[64] = ((s << n) | (t >> (53U - n))) & 0x1fffffffffffffUL;
    s = (sp_int_digit)(a[63]); t = (sp_int_digit)(a[62]);
    r[63] = ((s << n) | (t >> (53U - n))) & 0x1fffffffffffffUL;
    s = (sp_int_digit)(a[62]); t = (sp_int_digit)(a[61]);
    r[62] = ((s << n) | (t >> (53U - n))) & 0x1fffffffffffffUL;
    s = (sp_int_digit)(a[61]); t = (sp_int_digit)(a[60]);
    r[61] = ((s << n) | (t >> (53U - n))) & 0x1fffffffffffffUL;
    s = (sp_int_digit)(a[60]); t = (sp_int_digit)(a[59]);
    r[60] = ((s << n) | (t >> (53U - n))) & 0x1fffffffffffffUL;
    s = (sp_int_digit)(a[59]); t = (sp_int_digit)(a[58]);
    r[59] = ((s << n) | (t >> (53U - n))) & 0x1fffffffffffffUL;
    s = (sp_int_digit)(a[58]); t = (sp_int_digit)(a[57]);
    r[58] = ((s << n) | (t >> (53U - n))) & 0x1fffffffffffffUL;
    s = (sp_int_digit)(a[57]); t = (sp_int_digit)(a[56]);
    r[57] = ((s << n) | (t >> (53U - n))) & 0x1fffffffffffffUL;
    s = (sp_int_digit)(a[56]); t = (sp_int_digit)(a[55]);
    r[56] = ((s << n) | (t >> (53U - n))) & 0x1fffffffffffffUL;
    s = (sp_int_digit)(a[55]); t = (sp_int_digit)(a[54]);
    r[55] = ((s << n) | (t >> (53U - n))) & 0x1fffffffffffffUL;
    s = (sp_int_digit)(a[54]); t = (sp_int_digit)(a[53]);
    r[54] = ((s << n) | (t >> (53U - n))) & 0x1fffffffffffffUL;
    s = (sp_int_digit)(a[53]); t = (sp_int_digit)(a[52]);
    r[53] = ((s << n) | (t >> (53U - n))) & 0x1fffffffffffffUL;
    s = (sp_int_digit)(a[52]); t = (sp_int_digit)(a[51]);
    r[52] = ((s << n) | (t >> (53U - n))) & 0x1fffffffffffffUL;
    s = (sp_int_digit)(a[51]); t = (sp_int_digit)(a[50]);
    r[51] = ((s << n) | (t >> (53U - n))) & 0x1fffffffffffffUL;
    s = (sp_int_digit)(a[50]); t = (sp_int_digit)(a[49]);
    r[50] = ((s << n) | (t >> (53U - n))) & 0x1fffffffffffffUL;
    s = (sp_int_digit)(a[49]); t = (sp_int_digit)(a[48]);
    r[49] = ((s << n) | (t >> (53U - n))) & 0x1fffffffffffffUL;
    s = (sp_int_digit)(a[48]); t = (sp_int_digit)(a[47]);
    r[48] = ((s << n) | (t >> (53U - n))) & 0x1fffffffffffffUL;
    s = (sp_int_digit)(a[47]); t = (sp_int_digit)(a[46]);
    r[47] = ((s << n) | (t >> (53U - n))) & 0x1fffffffffffffUL;
    s = (sp_int_digit)(a[46]); t = (sp_int_digit)(a[45]);
    r[46] = ((s << n) | (t >> (53U - n))) & 0x1fffffffffffffUL;
    s = (sp_int_digit)(a[45]); t = (sp_int_digit)(a[44]);
    r[45] = ((s << n) | (t >> (53U - n))) & 0x1fffffffffffffUL;
    s = (sp_int_digit)(a[44]); t = (sp_int_digit)(a[43]);
    r[44] = ((s << n) | (t >> (53U - n))) & 0x1fffffffffffffUL;
    s = (sp_int_digit)(a[43]); t = (sp_int_digit)(a[42]);
    r[43] = ((s << n) | (t >> (53U - n))) & 0x1fffffffffffffUL;
    s = (sp_int_digit)(a[42]); t = (sp_int_digit)(a[41]);
    r[42] = ((s << n) | (t >> (53U - n))) & 0x1fffffffffffffUL;
    s = (sp_int_digit)(a[41]); t = (sp_int_digit)(a[40]);
    r[41] = ((s << n) | (t >> (53U - n))) & 0x1fffffffffffffUL;
    s = (sp_int_digit)(a[40]); t = (sp_int_digit)(a[39]);
    r[40] = ((s << n) | (t >> (53U - n))) & 0x1fffffffffffffUL;
    s = (sp_int_digit)(a[39]); t = (sp_int_digit)(a[38]);
    r[39] = ((s << n) | (t >> (53U - n))) & 0x1fffffffffffffUL;
    s = (sp_int_digit)(a[38]); t = (sp_int_digit)(a[37]);
    r[38] = ((s << n) | (t >> (53U - n))) & 0x1fffffffffffffUL;
    s = (sp_int_digit)(a[37]); t = (sp_int_digit)(a[36]);
    r[37] = ((s << n) | (t >> (53U - n))) & 0x1fffffffffffffUL;
    s = (sp_int_digit)(a[36]); t = (sp_int_digit)(a[35]);
    r[36] = ((s << n) | (t >> (53U - n))) & 0x1fffffffffffffUL;
    s = (sp_int_digit)(a[35]); t = (sp_int_digit)(a[34]);
    r[35] = ((s << n) | (t >> (53U - n))) & 0x1fffffffffffffUL;
    s = (sp_int_digit)(a[34]); t = (sp_int_digit)(a[33]);
    r[34] = ((s << n) | (t >> (53U - n))) & 0x1fffffffffffffUL;
    s = (sp_int_digit)(a[33]); t = (sp_int_digit)(a[32]);
    r[33] = ((s << n) | (t >> (53U - n))) & 0x1fffffffffffffUL;
    s = (sp_int_digit)(a[32]); t = (sp_int_digit)(a[31]);
    r[32] = ((s << n) | (t >> (53U - n))) & 0x1fffffffffffffUL;
    s = (sp_int_digit)(a[31]); t = (sp_int_digit)(a[30]);
    r[31] = ((s << n) | (t >> (53U - n))) & 0x1fffffffffffffUL;
    s = (sp_int_digit)(a[30]); t = (sp_int_digit)(a[29]);
    r[30] = ((s << n) | (t >> (53U - n))) & 0x1fffffffffffffUL;
    s = (sp_int_digit)(a[29]); t = (sp_int_digit)(a[28]);
    r[29] = ((s << n) | (t >> (53U - n))) & 0x1fffffffffffffUL;
    s = (sp_int_digit)(a[28]); t = (sp_int_digit)(a[27]);
    r[28] = ((s << n) | (t >> (53U - n))) & 0x1fffffffffffffUL;
    s = (sp_int_digit)(a[27]); t = (sp_int_digit)(a[26]);
    r[27] = ((s << n) | (t >> (53U - n))) & 0x1fffffffffffffUL;
    s = (sp_int_digit)(a[26]); t = (sp_int_digit)(a[25]);
    r[26] = ((s << n) | (t >> (53U - n))) & 0x1fffffffffffffUL;
    s = (sp_int_digit)(a[25]); t = (sp_int_digit)(a[24]);
    r[25] = ((s << n) | (t >> (53U - n))) & 0x1fffffffffffffUL;
    s = (sp_int_digit)(a[24]); t = (sp_int_digit)(a[23]);
    r[24] = ((s << n) | (t >> (53U - n))) & 0x1fffffffffffffUL;
    s = (sp_int_digit)(a[23]); t = (sp_int_digit)(a[22]);
    r[23] = ((s << n) | (t >> (53U - n))) & 0x1fffffffffffffUL;
    s = (sp_int_digit)(a[22]); t = (sp_int_digit)(a[21]);
    r[22] = ((s << n) | (t >> (53U - n))) & 0x1fffffffffffffUL;
    s = (sp_int_digit)(a[21]); t = (sp_int_digit)(a[20]);
    r[21] = ((s << n) | (t >> (53U - n))) & 0x1fffffffffffffUL;
    s = (sp_int_digit)(a[20]); t = (sp_int_digit)(a[19]);
    r[20] = ((s << n) | (t >> (53U - n))) & 0x1fffffffffffffUL;
    s = (sp_int_digit)(a[19]); t = (sp_int_digit)(a[18]);
    r[19] = ((s << n) | (t >> (53U - n))) & 0x1fffffffffffffUL;
    s = (sp_int_digit)(a[18]); t = (sp_int_digit)(a[17]);
    r[18] = ((s << n) | (t >> (53U - n))) & 0x1fffffffffffffUL;
    s = (sp_int_digit)(a[17]); t = (sp_int_digit)(a[16]);
    r[17] = ((s << n) | (t >> (53U - n))) & 0x1fffffffffffffUL;
    s = (sp_int_digit)(a[16]); t = (sp_int_digit)(a[15]);
    r[16] = ((s << n) | (t >> (53U - n))) & 0x1fffffffffffffUL;
    s = (sp_int_digit)(a[15]); t = (sp_int_digit)(a[14]);
    r[15] = ((s << n) | (t >> (53U - n))) & 0x1fffffffffffffUL;
    s = (sp_int_digit)(a[14]); t = (sp_int_digit)(a[13]);
    r[14] = ((s << n) | (t >> (53U - n))) & 0x1fffffffffffffUL;
    s = (sp_int_digit)(a[13]); t = (sp_int_digit)(a[12]);
    r[13] = ((s << n) | (t >> (53U - n))) & 0x1fffffffffffffUL;
    s = (sp_int_digit)(a[12]); t = (sp_int_digit)(a[11]);
    r[12] = ((s << n) | (t >> (53U - n))) & 0x1fffffffffffffUL;
    s = (sp_int_digit)(a[11]); t = (sp_int_digit)(a[10]);
    r[11] = ((s << n) | (t >> (53U - n))) & 0x1fffffffffffffUL;
    s = (sp_int_digit)(a[10]); t = (sp_int_digit)(a[9]);
    r[10] = ((s << n) | (t >> (53U - n))) & 0x1fffffffffffffUL;
    s = (sp_int_digit)(a[9]); t = (sp_int_digit)(a[8]);
    r[9] = ((s << n) | (t >> (53U - n))) & 0x1fffffffffffffUL;
    s = (sp_int_digit)(a[8]); t = (sp_int_digit)(a[7]);
    r[8] = ((s << n) | (t >> (53U - n))) & 0x1fffffffffffffUL;
    s = (sp_int_digit)(a[7]); t = (sp_int_digit)(a[6]);
    r[7] = ((s << n) | (t >> (53U - n))) & 0x1fffffffffffffUL;
    s = (sp_int_digit)(a[6]); t = (sp_int_digit)(a[5]);
    r[6] = ((s << n) | (t >> (53U - n))) & 0x1fffffffffffffUL;
    s = (sp_int_digit)(a[5]); t = (sp_int_digit)(a[4]);
    r[5] = ((s << n) | (t >> (53U - n))) & 0x1fffffffffffffUL;
    s = (sp_int_digit)(a[4]); t = (sp_int_digit)(a[3]);
    r[4] = ((s << n) | (t >> (53U - n))) & 0x1fffffffffffffUL;
    s = (sp_int_digit)(a[3]); t = (sp_int_digit)(a[2]);
    r[3] = ((s << n) | (t >> (53U - n))) & 0x1fffffffffffffUL;
    s = (sp_int_digit)(a[2]); t = (sp_int_digit)(a[1]);
    r[2] = ((s << n) | (t >> (53U - n))) & 0x1fffffffffffffUL;
    s = (sp_int_digit)(a[1]); t = (sp_int_digit)(a[0]);
    r[1] = ((s << n) | (t >> (53U - n))) & 0x1fffffffffffffUL;
#endif
    r[0] = (a[0] << n) & 0x1fffffffffffffL;
}

/* Modular exponentiate 2 to the e mod m. (r = 2^e mod m)
 *
 * r     A single precision number that is the result of the operation.
 * e     A single precision number that is the exponent.
 * bits  The number of bits in the exponent.
 * m     A single precision number that is the modulus.
 * returns 0 on success and MEMORY_E on dynamic memory allocation failure.
 */
static int sp_4096_mod_exp_2_78(sp_digit* r, const sp_digit* e, int bits, const sp_digit* m)
{
#if defined(WOLFSSL_SMALL_STACK) && !defined(WOLFSSL_SP_NO_MALLOC)
    sp_digit* td;
#else
    sp_digit td[235];
#endif
    sp_digit* norm;
    sp_digit* tmp;
    sp_digit mp = 1;
    sp_digit n, o;
    int i;
    int c, y;
    int err = MP_OKAY;

#if defined(WOLFSSL_SMALL_STACK) && !defined(WOLFSSL_SP_NO_MALLOC)
    td = (sp_digit*)XMALLOC(sizeof(sp_digit) * 235, NULL,
                            DYNAMIC_TYPE_TMP_BUFFER);
    if (td == NULL) {
        err = MEMORY_E;
    }
#endif

    if (err == MP_OKAY) {
        norm = td;
#if defined(WOLFSSL_SMALL_STACK) && !defined(WOLFSSL_SP_NO_MALLOC)
        tmp  = td + 156;
        XMEMSET(td, 0, sizeof(sp_digit) * 235);
#else
        tmp  = &td[156];
        XMEMSET(td, 0, sizeof(td));
#endif

        sp_4096_mont_setup(m, &mp);
        sp_4096_mont_norm_78(norm, m);

        bits = ((bits + 4) / 5) * 5;
        i = ((bits + 52) / 53) - 1;
        c = bits % 53;
        if (c == 0) {
            c = 53;
        }
        if (i < 78) {
            n = e[i--] << (64 - c);
        }
        else {
            n = 0;
            i--;
        }
        if (c < 5) {
            n |= e[i--] << (11 - c);
            c += 53;
        }
        y = (n >> 59) & 0x1f;
        n <<= 5;
        c -= 5;
        sp_4096_lshift_78(r, norm, y);
        for (; i>=0 || c>=5; ) {
            if (c < 5) {
                n |= e[i--] << (11 - c);
                c += 53;
            }
            y = (n >> 59) & 0x1f;
            n <<= 5;
            c -= 5;

            sp_4096_mont_sqr_78(r, r, m, mp);
            sp_4096_mont_sqr_78(r, r, m, mp);
            sp_4096_mont_sqr_78(r, r, m, mp);
            sp_4096_mont_sqr_78(r, r, m, mp);
            sp_4096_mont_sqr_78(r, r, m, mp);

            sp_4096_lshift_78(r, r, y);
            sp_4096_mul_d_78(tmp, norm, (r[78] << 38) + (r[77] >> 15));
            r[78] = 0;
            r[77] &= 0x7fffL;
            (void)sp_4096_add_78(r, r, tmp);
            sp_4096_norm_78(r);
            o = sp_4096_cmp_78(r, m);
            sp_4096_cond_sub_78(r, r, m, ((o < 0) ?
                                          (sp_digit)1 : (sp_digit)0) - 1);
        }

        sp_4096_mont_reduce_78(r, m, mp);
        n = sp_4096_cmp_78(r, m);
        sp_4096_cond_sub_78(r, r, m, ((n < 0) ?
                                                (sp_digit)1 : (sp_digit)0) - 1);
    }

#if defined(WOLFSSL_SMALL_STACK) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (td != NULL) {
        XFREE(td, NULL, DYNAMIC_TYPE_TMP_BUFFER);
    }
#endif

    return err;
}

#endif /* HAVE_FFDHE_4096 */

/* Perform the modular exponentiation for Diffie-Hellman.
 *
 * base     Base.
 * exp      Array of bytes that is the exponent.
 * expLen   Length of data, in bytes, in exponent.
 * mod      Modulus.
 * out      Buffer to hold big-endian bytes of exponentiation result.
 *          Must be at least 512 bytes long.
 * outLen   Length, in bytes, of exponentiation result.
 * returns 0 on success, MP_READ_E if there are too many bytes in an array
 * and MEMORY_E if memory allocation fails.
 */
int sp_DhExp_4096(mp_int* base, const byte* exp, word32 expLen,
    mp_int* mod, byte* out, word32* outLen)
{
#ifdef WOLFSSL_SP_SMALL
    int err = MP_OKAY;
    sp_digit* d = NULL;
    sp_digit* b;
    sp_digit* e;
    sp_digit* m;
    sp_digit* r;
    word32 i;

    if (mp_count_bits(base) > 4096) {
        err = MP_READ_E;
    }

    if (err == MP_OKAY) {
        if (expLen > 512) {
            err = MP_READ_E;
        }
    }

    if (err == MP_OKAY) {
        if (mp_count_bits(mod) != 4096) {
            err = MP_READ_E;
        }
    }

    if (err == MP_OKAY) {
        d = (sp_digit*)XMALLOC(sizeof(*d) * 78 * 4, NULL, DYNAMIC_TYPE_DH);
        if (d == NULL) {
            err = MEMORY_E;
        }
    }

    if (err == MP_OKAY) {
        b = d;
        e = b + 78 * 2;
        m = e + 78;
        r = b;

        sp_4096_from_mp(b, 78, base);
        sp_4096_from_bin(e, 78, exp, expLen);
        sp_4096_from_mp(m, 78, mod);

    #ifdef HAVE_FFDHE_4096
        if (base->used == 1 && base->dp[0] == 2 &&
                ((m[77] << 17) | (m[76] >> 36)) == 0xffffffffL) {
            err = sp_4096_mod_exp_2_78(r, e, expLen * 8, m);
        }
        else
    #endif
            err = sp_4096_mod_exp_78(r, b, e, expLen * 8, m, 0);
    }

    if (err == MP_OKAY) {
        sp_4096_to_bin(r, out);
        *outLen = 512;
        for (i=0; i<512 && out[i] == 0; i++) {
        }
        *outLen -= i;
        XMEMMOVE(out, out + i, *outLen);
    }

    if (d != NULL) {
        XMEMSET(e, 0, sizeof(sp_digit) * 78U);
        XFREE(d, NULL, DYNAMIC_TYPE_DH);
    }
    return err;
#else
#ifndef WOLFSSL_SMALL_STACK
    sp_digit bd[156], ed[78], md[78];
#else
    sp_digit* d = NULL;
#endif
    sp_digit* b;
    sp_digit* e;
    sp_digit* m;
    sp_digit* r;
    word32 i;
    int err = MP_OKAY;

    if (mp_count_bits(base) > 4096) {
        err = MP_READ_E;
    }

    if (err == MP_OKAY) {
        if (expLen > 512U) {
            err = MP_READ_E;
        }
    }

    if (err == MP_OKAY) {
        if (mp_count_bits(mod) != 4096) {
            err = MP_READ_E;
        }
    }
#ifdef WOLFSSL_SMALL_STACK
    if (err == MP_OKAY) {
        d = (sp_digit*)XMALLOC(sizeof(*d) * 78 * 4, NULL, DYNAMIC_TYPE_DH);
        if (d == NULL)
            err = MEMORY_E;
    }

    if (err == MP_OKAY) {
        b = d;
        e = b + 78 * 2;
        m = e + 78;
        r = b;
    }
#else
    r = b = bd;
    e = ed;
    m = md;
#endif

    if (err == MP_OKAY) {
        sp_4096_from_mp(b, 78, base);
        sp_4096_from_bin(e, 78, exp, expLen);
        sp_4096_from_mp(m, 78, mod);

    #ifdef HAVE_FFDHE_4096
        if (base->used == 1 && base->dp[0] == 2U &&
                ((m[77] << 17) | (m[76] >> 36)) == 0xffffffffL) {
            err = sp_4096_mod_exp_2_78(r, e, expLen * 8U, m);
        }
        else {
    #endif
            err = sp_4096_mod_exp_78(r, b, e, expLen * 8U, m, 0);
    #ifdef HAVE_FFDHE_4096
        }
    #endif
    }

    if (err == MP_OKAY) {
        sp_4096_to_bin(r, out);
        *outLen = 512;
        for (i=0; i<512U && out[i] == 0U; i++) {
        }
        *outLen -= i;
        XMEMMOVE(out, out + i, *outLen);
    }

#ifdef WOLFSSL_SMALL_STACK
    if (d != NULL) {
        XMEMSET(e, 0, sizeof(sp_digit) * 78U);
        XFREE(d, NULL, DYNAMIC_TYPE_DH);
    }
#else
    XMEMSET(e, 0, sizeof(sp_digit) * 78U);
#endif

    return err;
#endif
}
#endif /* WOLFSSL_HAVE_SP_DH */

#endif /* WOLFSSL_HAVE_SP_DH || (WOLFSSL_HAVE_SP_RSA && !WOLFSSL_RSA_PUBLIC_ONLY) */

#endif /* WOLFSSL_SP_4096 */

#endif /* WOLFSSL_HAVE_SP_RSA || WOLFSSL_HAVE_SP_DH */
#ifdef WOLFSSL_HAVE_SP_ECC
#ifndef WOLFSSL_SP_NO_256

/* Point structure to use. */
typedef struct sp_point_256 {
    sp_digit x[2 * 5];
    sp_digit y[2 * 5];
    sp_digit z[2 * 5];
    int infinity;
} sp_point_256;

/* The modulus (prime) of the curve P256. */
static const sp_digit p256_mod[5] = {
    0xfffffffffffffL,0x00fffffffffffL,0x0000000000000L,0x0001000000000L,
    0x0ffffffff0000L
};
/* The Montogmery normalizer for modulus of the curve P256. */
static const sp_digit p256_norm_mod[5] = {
    0x0000000000001L,0xff00000000000L,0xfffffffffffffL,0xfffefffffffffL,
    0x000000000ffffL
};
/* The Montogmery multiplier for modulus of the curve P256. */
static const sp_digit p256_mp_mod = 0x0000000000001;
#if defined(WOLFSSL_VALIDATE_ECC_KEYGEN) || defined(HAVE_ECC_SIGN) || \
                                            defined(HAVE_ECC_VERIFY)
/* The order of the curve P256. */
static const sp_digit p256_order[5] = {
    0x9cac2fc632551L,0xada7179e84f3bL,0xfffffffbce6faL,0x0000fffffffffL,
    0x0ffffffff0000L
};
#endif
/* The order of the curve P256 minus 2. */
static const sp_digit p256_order2[5] = {
    0x9cac2fc63254fL,0xada7179e84f3bL,0xfffffffbce6faL,0x0000fffffffffL,
    0x0ffffffff0000L
};
#if defined(HAVE_ECC_SIGN) || defined(HAVE_ECC_VERIFY)
/* The Montogmery normalizer for order of the curve P256. */
static const sp_digit p256_norm_order[5] = {
    0x6353d039cdaafL,0x5258e8617b0c4L,0x0000000431905L,0xffff000000000L,
    0x000000000ffffL
};
#endif
#if defined(HAVE_ECC_SIGN) || defined(HAVE_ECC_VERIFY)
/* The Montogmery multiplier for order of the curve P256. */
static const sp_digit p256_mp_order = 0x1c8aaee00bc4fL;
#endif
/* The base point of curve P256. */
static const sp_point_256 p256_base = {
    /* X ordinate */
    {
        0x13945d898c296L,0x812deb33a0f4aL,0x3a440f277037dL,0x4247f8bce6e56L,
        0x06b17d1f2e12cL,
        0L, 0L, 0L, 0L, 0L
    },
    /* Y ordinate */
    {
        0x6406837bf51f5L,0x576b315ececbbL,0xc0f9e162bce33L,0x7f9b8ee7eb4a7L,
        0x04fe342e2fe1aL,
        0L, 0L, 0L, 0L, 0L
    },
    /* Z ordinate */
    {
        0x0000000000001L,0x0000000000000L,0x0000000000000L,0x0000000000000L,
        0x0000000000000L,
        0L, 0L, 0L, 0L, 0L
    },
    /* infinity */
    0
};
#if defined(HAVE_ECC_CHECK_KEY) || defined(HAVE_COMP_KEY)
static const sp_digit p256_b[5] = {
    0xe3c3e27d2604bL,0xb0cc53b0f63bcL,0x69886bc651d06L,0x93e7b3ebbd557L,
    0x05ac635d8aa3aL
};
#endif

static int sp_256_point_new_ex_5(void* heap, sp_point_256* sp, sp_point_256** p)
{
    int ret = MP_OKAY;
    (void)heap;
#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    (void)sp;
    *p = (sp_point_256*)XMALLOC(sizeof(sp_point_256), heap, DYNAMIC_TYPE_ECC);
#else
    *p = sp;
#endif
    if (*p == NULL) {
        ret = MEMORY_E;
    }
    return ret;
}

#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
/* Allocate memory for point and return error. */
#define sp_256_point_new_5(heap, sp, p) sp_256_point_new_ex_5((heap), NULL, &(p))
#else
/* Set pointer to data and return no error. */
#define sp_256_point_new_5(heap, sp, p) sp_256_point_new_ex_5((heap), &(sp), &(p))
#endif


static void sp_256_point_free_5(sp_point_256* p, int clear, void* heap)
{
#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
/* If valid pointer then clear point data if requested and free data. */
    if (p != NULL) {
        if (clear != 0) {
            XMEMSET(p, 0, sizeof(*p));
        }
        XFREE(p, heap, DYNAMIC_TYPE_ECC);
    }
#else
/* Clear point data if requested. */
    if (clear != 0) {
        XMEMSET(p, 0, sizeof(*p));
    }
#endif
    (void)heap;
}

/* Multiply a number by Montogmery normalizer mod modulus (prime).
 *
 * r  The resulting Montgomery form number.
 * a  The number to convert.
 * m  The modulus (prime).
 * returns MEMORY_E when memory allocation fails and MP_OKAY otherwise.
 */
static int sp_256_mod_mul_norm_5(sp_digit* r, const sp_digit* a, const sp_digit* m)
{
#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    int64_t* td;
#else
    int64_t td[8];
    int64_t a32d[8];
#endif
    int64_t* t;
    int64_t* a32;
    int64_t o;
    int err = MP_OKAY;

    (void)m;

#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    td = (int64_t*)XMALLOC(sizeof(int64_t) * 2 * 8, NULL, DYNAMIC_TYPE_ECC);
    if (td == NULL) {
        return MEMORY_E;
    }
#endif

    if (err == MP_OKAY) {
#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
        t = td;
        a32 = td + 8;
#else
        t = td;
        a32 = a32d;
#endif

        a32[0] = (sp_digit)(a[0]) & 0xffffffffL;
        a32[1] = (sp_digit)(a[0] >> 32U);
        a32[1] |= a[1] << 20U;
        a32[1] &= 0xffffffffL;
        a32[2] = (sp_digit)(a[1] >> 12U) & 0xffffffffL;
        a32[3] = (sp_digit)(a[1] >> 44U);
        a32[3] |= a[2] << 8U;
        a32[3] &= 0xffffffffL;
        a32[4] = (sp_digit)(a[2] >> 24U);
        a32[4] |= a[3] << 28U;
        a32[4] &= 0xffffffffL;
        a32[5] = (sp_digit)(a[3] >> 4U) & 0xffffffffL;
        a32[6] = (sp_digit)(a[3] >> 36U);
        a32[6] |= a[4] << 16U;
        a32[6] &= 0xffffffffL;
        a32[7] = (sp_digit)(a[4] >> 16U) & 0xffffffffL;

        /*  1  1  0 -1 -1 -1 -1  0 */
            t[0] = 0 + a32[0] + a32[1] - a32[3] - a32[4] - a32[5] - a32[6];
        /*  0  1  1  0 -1 -1 -1 -1 */
            t[1] = 0 + a32[1] + a32[2] - a32[4] - a32[5] - a32[6] - a32[7];
        /*  0  0  1  1  0 -1 -1 -1 */
            t[2] = 0 + a32[2] + a32[3] - a32[5] - a32[6] - a32[7];
        /* -1 -1  0  2  2  1  0 -1 */
            t[3] = 0 - a32[0] - a32[1] + 2 * a32[3] + 2 * a32[4] + a32[5] - a32[7];
        /*  0 -1 -1  0  2  2  1  0 */
            t[4] = 0 - a32[1] - a32[2] + 2 * a32[4] + 2 * a32[5] + a32[6];
        /*  0  0 -1 -1  0  2  2  1 */
            t[5] = 0 - a32[2] - a32[3] + 2 * a32[5] + 2 * a32[6] + a32[7];
        /* -1 -1  0  0  0  1  3  2 */
            t[6] = 0 - a32[0] - a32[1] + a32[5] + 3 * a32[6] + 2 * a32[7];
        /*  1  0 -1 -1 -1 -1  0  3 */
            t[7] = 0 + a32[0] - a32[2] - a32[3] - a32[4] - a32[5] + 3 * a32[7];

            t[1] += t[0] >> 32U; t[0] &= 0xffffffffL;
            t[2] += t[1] >> 32U; t[1] &= 0xffffffffL;
            t[3] += t[2] >> 32U; t[2] &= 0xffffffffL;
            t[4] += t[3] >> 32U; t[3] &= 0xffffffffL;
            t[5] += t[4] >> 32U; t[4] &= 0xffffffffL;
            t[6] += t[5] >> 32U; t[5] &= 0xffffffffL;
            t[7] += t[6] >> 32U; t[6] &= 0xffffffffL;
            o     = t[7] >> 32U; t[7] &= 0xffffffffL;
            t[0] += o;
            t[3] -= o;
            t[6] -= o;
            t[7] += o;
            t[1] += t[0] >> 32U; t[0] &= 0xffffffffL;
            t[2] += t[1] >> 32U; t[1] &= 0xffffffffL;
            t[3] += t[2] >> 32U; t[2] &= 0xffffffffL;
            t[4] += t[3] >> 32U; t[3] &= 0xffffffffL;
            t[5] += t[4] >> 32U; t[4] &= 0xffffffffL;
            t[6] += t[5] >> 32U; t[5] &= 0xffffffffL;
            t[7] += t[6] >> 32U; t[6] &= 0xffffffffL;

        r[0] = t[0];
        r[0] |= t[1] << 32U;
        r[0] &= 0xfffffffffffffLL;
        r[1] = (sp_digit)(t[1] >> 20);
        r[1] |= t[2] << 12U;
        r[1] |= t[3] << 44U;
        r[1] &= 0xfffffffffffffLL;
        r[2] = (sp_digit)(t[3] >> 8);
        r[2] |= t[4] << 24U;
        r[2] &= 0xfffffffffffffLL;
        r[3] = (sp_digit)(t[4] >> 28);
        r[3] |= t[5] << 4U;
        r[3] |= t[6] << 36U;
        r[3] &= 0xfffffffffffffLL;
        r[4] = (sp_digit)(t[6] >> 16);
        r[4] |= t[7] << 16U;
    }

#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (td != NULL) {
        XFREE(td, NULL, DYNAMIC_TYPE_ECC);
    }
#endif

    return err;
}

/* Convert an mp_int to an array of sp_digit.
 *
 * r  A single precision integer.
 * size  Maximum number of bytes to convert
 * a  A multi-precision integer.
 */
static void sp_256_from_mp(sp_digit* r, int size, const mp_int* a)
{
#if DIGIT_BIT == 52
    int j;

    XMEMCPY(r, a->dp, sizeof(sp_digit) * a->used);

    for (j = a->used; j < size; j++) {
        r[j] = 0;
    }
#elif DIGIT_BIT > 52
    int i, j = 0;
    word32 s = 0;

    r[0] = 0;
    for (i = 0; i < a->used && j < size; i++) {
        r[j] |= ((sp_digit)a->dp[i] << s);
        r[j] &= 0xfffffffffffffL;
        s = 52U - s;
        if (j + 1 >= size) {
            break;
        }
        /* lint allow cast of mismatch word32 and mp_digit */
        r[++j] = (sp_digit)(a->dp[i] >> s); /*lint !e9033*/
        while ((s + 52U) <= (word32)DIGIT_BIT) {
            s += 52U;
            r[j] &= 0xfffffffffffffL;
            if (j + 1 >= size) {
                break;
            }
            if (s < (word32)DIGIT_BIT) {
                /* lint allow cast of mismatch word32 and mp_digit */
                r[++j] = (sp_digit)(a->dp[i] >> s); /*lint !e9033*/
            }
            else {
                r[++j] = 0L;
            }
        }
        s = (word32)DIGIT_BIT - s;
    }

    for (j++; j < size; j++) {
        r[j] = 0;
    }
#else
    int i, j = 0, s = 0;

    r[0] = 0;
    for (i = 0; i < a->used && j < size; i++) {
        r[j] |= ((sp_digit)a->dp[i]) << s;
        if (s + DIGIT_BIT >= 52) {
            r[j] &= 0xfffffffffffffL;
            if (j + 1 >= size) {
                break;
            }
            s = 52 - s;
            if (s == DIGIT_BIT) {
                r[++j] = 0;
                s = 0;
            }
            else {
                r[++j] = a->dp[i] >> s;
                s = DIGIT_BIT - s;
            }
        }
        else {
            s += DIGIT_BIT;
        }
    }

    for (j++; j < size; j++) {
        r[j] = 0;
    }
#endif
}

/* Convert a point of type ecc_point to type sp_point_256.
 *
 * p   Point of type sp_point_256 (result).
 * pm  Point of type ecc_point.
 */
static void sp_256_point_from_ecc_point_5(sp_point_256* p, const ecc_point* pm)
{
    XMEMSET(p->x, 0, sizeof(p->x));
    XMEMSET(p->y, 0, sizeof(p->y));
    XMEMSET(p->z, 0, sizeof(p->z));
    sp_256_from_mp(p->x, 5, pm->x);
    sp_256_from_mp(p->y, 5, pm->y);
    sp_256_from_mp(p->z, 5, pm->z);
    p->infinity = 0;
}

/* Convert an array of sp_digit to an mp_int.
 *
 * a  A single precision integer.
 * r  A multi-precision integer.
 */
static int sp_256_to_mp(const sp_digit* a, mp_int* r)
{
    int err;

    err = mp_grow(r, (256 + DIGIT_BIT - 1) / DIGIT_BIT);
    if (err == MP_OKAY) { /*lint !e774 case where err is always MP_OKAY*/
#if DIGIT_BIT == 52
        XMEMCPY(r->dp, a, sizeof(sp_digit) * 5);
        r->used = 5;
        mp_clamp(r);
#elif DIGIT_BIT < 52
        int i, j = 0, s = 0;

        r->dp[0] = 0;
        for (i = 0; i < 5; i++) {
            r->dp[j] |= (mp_digit)(a[i] << s);
            r->dp[j] &= (1L << DIGIT_BIT) - 1;
            s = DIGIT_BIT - s;
            r->dp[++j] = (mp_digit)(a[i] >> s);
            while (s + DIGIT_BIT <= 52) {
                s += DIGIT_BIT;
                r->dp[j++] &= (1L << DIGIT_BIT) - 1;
                if (s == SP_WORD_SIZE) {
                    r->dp[j] = 0;
                }
                else {
                    r->dp[j] = (mp_digit)(a[i] >> s);
                }
            }
            s = 52 - s;
        }
        r->used = (256 + DIGIT_BIT - 1) / DIGIT_BIT;
        mp_clamp(r);
#else
        int i, j = 0, s = 0;

        r->dp[0] = 0;
        for (i = 0; i < 5; i++) {
            r->dp[j] |= ((mp_digit)a[i]) << s;
            if (s + 52 >= DIGIT_BIT) {
    #if DIGIT_BIT != 32 && DIGIT_BIT != 64
                r->dp[j] &= (1L << DIGIT_BIT) - 1;
    #endif
                s = DIGIT_BIT - s;
                r->dp[++j] = a[i] >> s;
                s = 52 - s;
            }
            else {
                s += 52;
            }
        }
        r->used = (256 + DIGIT_BIT - 1) / DIGIT_BIT;
        mp_clamp(r);
#endif
    }

    return err;
}

/* Convert a point of type sp_point_256 to type ecc_point.
 *
 * p   Point of type sp_point_256.
 * pm  Point of type ecc_point (result).
 * returns MEMORY_E when allocation of memory in ecc_point fails otherwise
 * MP_OKAY.
 */
static int sp_256_point_to_ecc_point_5(const sp_point_256* p, ecc_point* pm)
{
    int err;

    err = sp_256_to_mp(p->x, pm->x);
    if (err == MP_OKAY) {
        err = sp_256_to_mp(p->y, pm->y);
    }
    if (err == MP_OKAY) {
        err = sp_256_to_mp(p->z, pm->z);
    }

    return err;
}

#ifdef WOLFSSL_SP_SMALL
/* Multiply a and b into r. (r = a * b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A single precision integer.
 */
SP_NOINLINE static void sp_256_mul_5(sp_digit* r, const sp_digit* a,
    const sp_digit* b)
{
    int i, j, k;
    int128_t c;

    c = ((int128_t)a[4]) * b[4];
    r[9] = (sp_digit)(c >> 52);
    c = (c & 0xfffffffffffffL) << 52;
    for (k = 7; k >= 0; k--) {
        for (i = 4; i >= 0; i--) {
            j = k - i;
            if (j >= 5) {
                break;
            }
            if (j < 0) {
                continue;
            }

            c += ((int128_t)a[i]) * b[j];
        }
        r[k + 2] += c >> 104;
        r[k + 1] = (c >> 52) & 0xfffffffffffffL;
        c = (c & 0xfffffffffffffL) << 52;
    }
    r[0] = (sp_digit)(c >> 52);
}

#else
/* Multiply a and b into r. (r = a * b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A single precision integer.
 */
SP_NOINLINE static void sp_256_mul_5(sp_digit* r, const sp_digit* a,
    const sp_digit* b)
{
    int128_t t0   = ((int128_t)a[ 0]) * b[ 0];
    int128_t t1   = ((int128_t)a[ 0]) * b[ 1]
                 + ((int128_t)a[ 1]) * b[ 0];
    int128_t t2   = ((int128_t)a[ 0]) * b[ 2]
                 + ((int128_t)a[ 1]) * b[ 1]
                 + ((int128_t)a[ 2]) * b[ 0];
    int128_t t3   = ((int128_t)a[ 0]) * b[ 3]
                 + ((int128_t)a[ 1]) * b[ 2]
                 + ((int128_t)a[ 2]) * b[ 1]
                 + ((int128_t)a[ 3]) * b[ 0];
    int128_t t4   = ((int128_t)a[ 0]) * b[ 4]
                 + ((int128_t)a[ 1]) * b[ 3]
                 + ((int128_t)a[ 2]) * b[ 2]
                 + ((int128_t)a[ 3]) * b[ 1]
                 + ((int128_t)a[ 4]) * b[ 0];
    int128_t t5   = ((int128_t)a[ 1]) * b[ 4]
                 + ((int128_t)a[ 2]) * b[ 3]
                 + ((int128_t)a[ 3]) * b[ 2]
                 + ((int128_t)a[ 4]) * b[ 1];
    int128_t t6   = ((int128_t)a[ 2]) * b[ 4]
                 + ((int128_t)a[ 3]) * b[ 3]
                 + ((int128_t)a[ 4]) * b[ 2];
    int128_t t7   = ((int128_t)a[ 3]) * b[ 4]
                 + ((int128_t)a[ 4]) * b[ 3];
    int128_t t8   = ((int128_t)a[ 4]) * b[ 4];

    t1   += t0  >> 52; r[ 0] = t0  & 0xfffffffffffffL;
    t2   += t1  >> 52; r[ 1] = t1  & 0xfffffffffffffL;
    t3   += t2  >> 52; r[ 2] = t2  & 0xfffffffffffffL;
    t4   += t3  >> 52; r[ 3] = t3  & 0xfffffffffffffL;
    t5   += t4  >> 52; r[ 4] = t4  & 0xfffffffffffffL;
    t6   += t5  >> 52; r[ 5] = t5  & 0xfffffffffffffL;
    t7   += t6  >> 52; r[ 6] = t6  & 0xfffffffffffffL;
    t8   += t7  >> 52; r[ 7] = t7  & 0xfffffffffffffL;
    r[9] = (sp_digit)(t8 >> 52);
                       r[8] = t8 & 0xfffffffffffffL;
}

#endif /* WOLFSSL_SP_SMALL */
#define sp_256_mont_reduce_order_5         sp_256_mont_reduce_5

/* Compare a with b in constant time.
 *
 * a  A single precision integer.
 * b  A single precision integer.
 * return -ve, 0 or +ve if a is less than, equal to or greater than b
 * respectively.
 */
static sp_digit sp_256_cmp_5(const sp_digit* a, const sp_digit* b)
{
    sp_digit r = 0;
#ifdef WOLFSSL_SP_SMALL
    int i;

    for (i=4; i>=0; i--) {
        r |= (a[i] - b[i]) & (0 - ((r == 0) ? (sp_digit)1 : (sp_digit)0));
    }
#else
    r |= (a[ 4] - b[ 4]) & (0 - ((r == 0) ? (sp_digit)1 : (sp_digit)0));
    r |= (a[ 3] - b[ 3]) & (0 - ((r == 0) ? (sp_digit)1 : (sp_digit)0));
    r |= (a[ 2] - b[ 2]) & (0 - ((r == 0) ? (sp_digit)1 : (sp_digit)0));
    r |= (a[ 1] - b[ 1]) & (0 - ((r == 0) ? (sp_digit)1 : (sp_digit)0));
    r |= (a[ 0] - b[ 0]) & (0 - ((r == 0) ? (sp_digit)1 : (sp_digit)0));
#endif /* WOLFSSL_SP_SMALL */

    return r;
}

/* Conditionally subtract b from a using the mask m.
 * m is -1 to subtract and 0 when not.
 *
 * r  A single precision number representing condition subtract result.
 * a  A single precision number to subtract from.
 * b  A single precision number to subtract.
 * m  Mask value to apply.
 */
static void sp_256_cond_sub_5(sp_digit* r, const sp_digit* a,
        const sp_digit* b, const sp_digit m)
{
#ifdef WOLFSSL_SP_SMALL
    int i;

    for (i = 0; i < 5; i++) {
        r[i] = a[i] - (b[i] & m);
    }
#else
    r[ 0] = a[ 0] - (b[ 0] & m);
    r[ 1] = a[ 1] - (b[ 1] & m);
    r[ 2] = a[ 2] - (b[ 2] & m);
    r[ 3] = a[ 3] - (b[ 3] & m);
    r[ 4] = a[ 4] - (b[ 4] & m);
#endif /* WOLFSSL_SP_SMALL */
}

/* Mul a by scalar b and add into r. (r += a * b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A scalar.
 */
SP_NOINLINE static void sp_256_mul_add_5(sp_digit* r, const sp_digit* a,
        const sp_digit b)
{
#ifdef WOLFSSL_SP_SMALL
    int128_t tb = b;
    int128_t t = 0;
    int i;

    for (i = 0; i < 5; i++) {
        t += (tb * a[i]) + r[i];
        r[i] = t & 0xfffffffffffffL;
        t >>= 52;
    }
    r[5] += t;
#else
    int128_t tb = b;
    int128_t t[5];

    t[ 0] = tb * a[ 0];
    t[ 1] = tb * a[ 1];
    t[ 2] = tb * a[ 2];
    t[ 3] = tb * a[ 3];
    t[ 4] = tb * a[ 4];
    r[ 0] += (sp_digit)                 (t[ 0] & 0xfffffffffffffL);
    r[ 1] += (sp_digit)((t[ 0] >> 52) + (t[ 1] & 0xfffffffffffffL));
    r[ 2] += (sp_digit)((t[ 1] >> 52) + (t[ 2] & 0xfffffffffffffL));
    r[ 3] += (sp_digit)((t[ 2] >> 52) + (t[ 3] & 0xfffffffffffffL));
    r[ 4] += (sp_digit)((t[ 3] >> 52) + (t[ 4] & 0xfffffffffffffL));
    r[ 5] += (sp_digit) (t[ 4] >> 52);
#endif /* WOLFSSL_SP_SMALL */
}

/* Normalize the values in each word to 52.
 *
 * a  Array of sp_digit to normalize.
 */
static void sp_256_norm_5(sp_digit* a)
{
#ifdef WOLFSSL_SP_SMALL
    int i;
    for (i = 0; i < 4; i++) {
        a[i+1] += a[i] >> 52;
        a[i] &= 0xfffffffffffffL;
    }
#else
    a[1] += a[0] >> 52; a[0] &= 0xfffffffffffffL;
    a[2] += a[1] >> 52; a[1] &= 0xfffffffffffffL;
    a[3] += a[2] >> 52; a[2] &= 0xfffffffffffffL;
    a[4] += a[3] >> 52; a[3] &= 0xfffffffffffffL;
#endif
}

/* Shift the result in the high 256 bits down to the bottom.
 *
 * r  A single precision number.
 * a  A single precision number.
 */
static void sp_256_mont_shift_5(sp_digit* r, const sp_digit* a)
{
#ifdef WOLFSSL_SP_SMALL
    int i;
    word64 n;

    n = a[4] >> 48;
    for (i = 0; i < 4; i++) {
        n += (word64)a[5 + i] << 4;
        r[i] = n & 0xfffffffffffffL;
        n >>= 52;
    }
    n += (word64)a[9] << 4;
    r[4] = n;
#else
    word64 n;

    n  = a[4] >> 48;
    n += (word64)a[ 5] << 4U; r[ 0] = n & 0xfffffffffffffUL; n >>= 52U;
    n += (word64)a[ 6] << 4U; r[ 1] = n & 0xfffffffffffffUL; n >>= 52U;
    n += (word64)a[ 7] << 4U; r[ 2] = n & 0xfffffffffffffUL; n >>= 52U;
    n += (word64)a[ 8] << 4U; r[ 3] = n & 0xfffffffffffffUL; n >>= 52U;
    n += (word64)a[ 9] << 4U; r[ 4] = n;
#endif /* WOLFSSL_SP_SMALL */
    XMEMSET(&r[5], 0, sizeof(*r) * 5U);
}

/* Reduce the number back to 256 bits using Montgomery reduction.
 *
 * a   A single precision number to reduce in place.
 * m   The single precision number representing the modulus.
 * mp  The digit representing the negative inverse of m mod 2^n.
 */
static void sp_256_mont_reduce_5(sp_digit* a, const sp_digit* m, sp_digit mp)
{
    int i;
    sp_digit mu;

    if (mp != 1) {
        for (i=0; i<4; i++) {
            mu = (a[i] * mp) & 0xfffffffffffffL;
            sp_256_mul_add_5(a+i, m, mu);
            a[i+1] += a[i] >> 52;
        }
        mu = (a[i] * mp) & 0xffffffffffffL;
        sp_256_mul_add_5(a+i, m, mu);
        a[i+1] += a[i] >> 52;
        a[i] &= 0xfffffffffffffL;
    }
    else {
        for (i=0; i<4; i++) {
            mu = a[i] & 0xfffffffffffffL;
            sp_256_mul_add_5(a+i, p256_mod, mu);
            a[i+1] += a[i] >> 52;
        }
        mu = a[i] & 0xffffffffffffL;
        sp_256_mul_add_5(a+i, p256_mod, mu);
        a[i+1] += a[i] >> 52;
        a[i] &= 0xfffffffffffffL;
    }

    sp_256_mont_shift_5(a, a);
    sp_256_cond_sub_5(a, a, m, 0 - (((a[4] >> 48) > 0) ?
            (sp_digit)1 : (sp_digit)0));
    sp_256_norm_5(a);
}

/* Multiply two Montogmery form numbers mod the modulus (prime).
 * (r = a * b mod m)
 *
 * r   Result of multiplication.
 * a   First number to multiply in Montogmery form.
 * b   Second number to multiply in Montogmery form.
 * m   Modulus (prime).
 * mp  Montogmery mulitplier.
 */
static void sp_256_mont_mul_5(sp_digit* r, const sp_digit* a, const sp_digit* b,
        const sp_digit* m, sp_digit mp)
{
    sp_256_mul_5(r, a, b);
    sp_256_mont_reduce_5(r, m, mp);
}

#ifdef WOLFSSL_SP_SMALL
/* Square a and put result in r. (r = a * a)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 */
SP_NOINLINE static void sp_256_sqr_5(sp_digit* r, const sp_digit* a)
{
    int i, j, k;
    int128_t c;

    c = ((int128_t)a[4]) * a[4];
    r[9] = (sp_digit)(c >> 52);
    c = (c & 0xfffffffffffffL) << 52;
    for (k = 7; k >= 0; k--) {
        for (i = 4; i >= 0; i--) {
            j = k - i;
            if (j >= 5 || i <= j) {
                break;
            }
            if (j < 0) {
                continue;
            }

            c += ((int128_t)a[i]) * a[j] * 2;
        }
        if (i == j) {
           c += ((int128_t)a[i]) * a[i];
        }

        r[k + 2] += c >> 104;
        r[k + 1] = (c >> 52) & 0xfffffffffffffL;
        c = (c & 0xfffffffffffffL) << 52;
    }
    r[0] = (sp_digit)(c >> 52);
}

#else
/* Square a and put result in r. (r = a * a)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 */
SP_NOINLINE static void sp_256_sqr_5(sp_digit* r, const sp_digit* a)
{
    int128_t t0   =  ((int128_t)a[ 0]) * a[ 0];
    int128_t t1   = (((int128_t)a[ 0]) * a[ 1]) * 2;
    int128_t t2   = (((int128_t)a[ 0]) * a[ 2]) * 2
                 +  ((int128_t)a[ 1]) * a[ 1];
    int128_t t3   = (((int128_t)a[ 0]) * a[ 3]
                 +  ((int128_t)a[ 1]) * a[ 2]) * 2;
    int128_t t4   = (((int128_t)a[ 0]) * a[ 4]
                 +  ((int128_t)a[ 1]) * a[ 3]) * 2
                 +  ((int128_t)a[ 2]) * a[ 2];
    int128_t t5   = (((int128_t)a[ 1]) * a[ 4]
                 +  ((int128_t)a[ 2]) * a[ 3]) * 2;
    int128_t t6   = (((int128_t)a[ 2]) * a[ 4]) * 2
                 +  ((int128_t)a[ 3]) * a[ 3];
    int128_t t7   = (((int128_t)a[ 3]) * a[ 4]) * 2;
    int128_t t8   =  ((int128_t)a[ 4]) * a[ 4];

    t1   += t0  >> 52; r[ 0] = t0  & 0xfffffffffffffL;
    t2   += t1  >> 52; r[ 1] = t1  & 0xfffffffffffffL;
    t3   += t2  >> 52; r[ 2] = t2  & 0xfffffffffffffL;
    t4   += t3  >> 52; r[ 3] = t3  & 0xfffffffffffffL;
    t5   += t4  >> 52; r[ 4] = t4  & 0xfffffffffffffL;
    t6   += t5  >> 52; r[ 5] = t5  & 0xfffffffffffffL;
    t7   += t6  >> 52; r[ 6] = t6  & 0xfffffffffffffL;
    t8   += t7  >> 52; r[ 7] = t7  & 0xfffffffffffffL;
    r[9] = (sp_digit)(t8 >> 52);
                       r[8] = t8 & 0xfffffffffffffL;
}

#endif /* WOLFSSL_SP_SMALL */
/* Square the Montgomery form number. (r = a * a mod m)
 *
 * r   Result of squaring.
 * a   Number to square in Montogmery form.
 * m   Modulus (prime).
 * mp  Montogmery mulitplier.
 */
static void sp_256_mont_sqr_5(sp_digit* r, const sp_digit* a, const sp_digit* m,
        sp_digit mp)
{
    sp_256_sqr_5(r, a);
    sp_256_mont_reduce_5(r, m, mp);
}

#if !defined(WOLFSSL_SP_SMALL) || defined(HAVE_COMP_KEY)
/* Square the Montgomery form number a number of times. (r = a ^ n mod m)
 *
 * r   Result of squaring.
 * a   Number to square in Montogmery form.
 * n   Number of times to square.
 * m   Modulus (prime).
 * mp  Montogmery mulitplier.
 */
static void sp_256_mont_sqr_n_5(sp_digit* r, const sp_digit* a, int n,
        const sp_digit* m, sp_digit mp)
{
    sp_256_mont_sqr_5(r, a, m, mp);
    for (; n > 1; n--) {
        sp_256_mont_sqr_5(r, r, m, mp);
    }
}

#endif /* !WOLFSSL_SP_SMALL || HAVE_COMP_KEY */
#ifdef WOLFSSL_SP_SMALL
/* Mod-2 for the P256 curve. */
static const uint64_t p256_mod_minus_2[4] = {
    0xfffffffffffffffdU,0x00000000ffffffffU,0x0000000000000000U,
    0xffffffff00000001U
};
#endif /* !WOLFSSL_SP_SMALL */

/* Invert the number, in Montgomery form, modulo the modulus (prime) of the
 * P256 curve. (r = 1 / a mod m)
 *
 * r   Inverse result.
 * a   Number to invert.
 * td  Temporary data.
 */
static void sp_256_mont_inv_5(sp_digit* r, const sp_digit* a, sp_digit* td)
{
#ifdef WOLFSSL_SP_SMALL
    sp_digit* t = td;
    int i;

    XMEMCPY(t, a, sizeof(sp_digit) * 5);
    for (i=254; i>=0; i--) {
        sp_256_mont_sqr_5(t, t, p256_mod, p256_mp_mod);
        if (p256_mod_minus_2[i / 64] & ((sp_digit)1 << (i % 64)))
            sp_256_mont_mul_5(t, t, a, p256_mod, p256_mp_mod);
    }
    XMEMCPY(r, t, sizeof(sp_digit) * 5);
#else
    sp_digit* t1 = td;
    sp_digit* t2 = td + 2 * 5;
    sp_digit* t3 = td + 4 * 5;
    /* 0x2 */
    sp_256_mont_sqr_5(t1, a, p256_mod, p256_mp_mod);
    /* 0x3 */
    sp_256_mont_mul_5(t2, t1, a, p256_mod, p256_mp_mod);
    /* 0xc */
    sp_256_mont_sqr_n_5(t1, t2, 2, p256_mod, p256_mp_mod);
    /* 0xd */
    sp_256_mont_mul_5(t3, t1, a, p256_mod, p256_mp_mod);
    /* 0xf */
    sp_256_mont_mul_5(t2, t2, t1, p256_mod, p256_mp_mod);
    /* 0xf0 */
    sp_256_mont_sqr_n_5(t1, t2, 4, p256_mod, p256_mp_mod);
    /* 0xfd */
    sp_256_mont_mul_5(t3, t3, t1, p256_mod, p256_mp_mod);
    /* 0xff */
    sp_256_mont_mul_5(t2, t2, t1, p256_mod, p256_mp_mod);
    /* 0xff00 */
    sp_256_mont_sqr_n_5(t1, t2, 8, p256_mod, p256_mp_mod);
    /* 0xfffd */
    sp_256_mont_mul_5(t3, t3, t1, p256_mod, p256_mp_mod);
    /* 0xffff */
    sp_256_mont_mul_5(t2, t2, t1, p256_mod, p256_mp_mod);
    /* 0xffff0000 */
    sp_256_mont_sqr_n_5(t1, t2, 16, p256_mod, p256_mp_mod);
    /* 0xfffffffd */
    sp_256_mont_mul_5(t3, t3, t1, p256_mod, p256_mp_mod);
    /* 0xffffffff */
    sp_256_mont_mul_5(t2, t2, t1, p256_mod, p256_mp_mod);
    /* 0xffffffff00000000 */
    sp_256_mont_sqr_n_5(t1, t2, 32, p256_mod, p256_mp_mod);
    /* 0xffffffffffffffff */
    sp_256_mont_mul_5(t2, t2, t1, p256_mod, p256_mp_mod);
    /* 0xffffffff00000001 */
    sp_256_mont_mul_5(r, t1, a, p256_mod, p256_mp_mod);
    /* 0xffffffff000000010000000000000000000000000000000000000000 */
    sp_256_mont_sqr_n_5(r, r, 160, p256_mod, p256_mp_mod);
    /* 0xffffffff00000001000000000000000000000000ffffffffffffffff */
    sp_256_mont_mul_5(r, r, t2, p256_mod, p256_mp_mod);
    /* 0xffffffff00000001000000000000000000000000ffffffffffffffff00000000 */
    sp_256_mont_sqr_n_5(r, r, 32, p256_mod, p256_mp_mod);
    /* 0xffffffff00000001000000000000000000000000fffffffffffffffffffffffd */
    sp_256_mont_mul_5(r, r, t3, p256_mod, p256_mp_mod);
#endif /* WOLFSSL_SP_SMALL */
}

/* Map the Montgomery form projective coordinate point to an affine point.
 *
 * r  Resulting affine coordinate point.
 * p  Montgomery form projective coordinate point.
 * t  Temporary ordinate data.
 */
static void sp_256_map_5(sp_point_256* r, const sp_point_256* p, sp_digit* t)
{
    sp_digit* t1 = t;
    sp_digit* t2 = t + 2*5;
    int64_t n;

    sp_256_mont_inv_5(t1, p->z, t + 2*5);

    sp_256_mont_sqr_5(t2, t1, p256_mod, p256_mp_mod);
    sp_256_mont_mul_5(t1, t2, t1, p256_mod, p256_mp_mod);

    /* x /= z^2 */
    sp_256_mont_mul_5(r->x, p->x, t2, p256_mod, p256_mp_mod);
    XMEMSET(r->x + 5, 0, sizeof(r->x) / 2U);
    sp_256_mont_reduce_5(r->x, p256_mod, p256_mp_mod);
    /* Reduce x to less than modulus */
    n = sp_256_cmp_5(r->x, p256_mod);
    sp_256_cond_sub_5(r->x, r->x, p256_mod, 0 - ((n >= 0) ?
                (sp_digit)1 : (sp_digit)0));
    sp_256_norm_5(r->x);

    /* y /= z^3 */
    sp_256_mont_mul_5(r->y, p->y, t1, p256_mod, p256_mp_mod);
    XMEMSET(r->y + 5, 0, sizeof(r->y) / 2U);
    sp_256_mont_reduce_5(r->y, p256_mod, p256_mp_mod);
    /* Reduce y to less than modulus */
    n = sp_256_cmp_5(r->y, p256_mod);
    sp_256_cond_sub_5(r->y, r->y, p256_mod, 0 - ((n >= 0) ?
                (sp_digit)1 : (sp_digit)0));
    sp_256_norm_5(r->y);

    XMEMSET(r->z, 0, sizeof(r->z));
    r->z[0] = 1;

}

#ifdef WOLFSSL_SP_SMALL
/* Add b to a into r. (r = a + b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A single precision integer.
 */
SP_NOINLINE static int sp_256_add_5(sp_digit* r, const sp_digit* a,
        const sp_digit* b)
{
    int i;

    for (i = 0; i < 5; i++) {
        r[i] = a[i] + b[i];
    }

    return 0;
}
#else
/* Add b to a into r. (r = a + b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A single precision integer.
 */
SP_NOINLINE static int sp_256_add_5(sp_digit* r, const sp_digit* a,
        const sp_digit* b)
{
    r[ 0] = a[ 0] + b[ 0];
    r[ 1] = a[ 1] + b[ 1];
    r[ 2] = a[ 2] + b[ 2];
    r[ 3] = a[ 3] + b[ 3];
    r[ 4] = a[ 4] + b[ 4];

    return 0;
}

#endif /* WOLFSSL_SP_SMALL */
/* Add two Montgomery form numbers (r = a + b % m).
 *
 * r   Result of addition.
 * a   First number to add in Montogmery form.
 * b   Second number to add in Montogmery form.
 * m   Modulus (prime).
 */
static void sp_256_mont_add_5(sp_digit* r, const sp_digit* a, const sp_digit* b,
        const sp_digit* m)
{
    (void)sp_256_add_5(r, a, b);
    sp_256_norm_5(r);
    sp_256_cond_sub_5(r, r, m, 0 - (((r[4] >> 48) > 0) ?
                (sp_digit)1 : (sp_digit)0));
    sp_256_norm_5(r);
}

/* Double a Montgomery form number (r = a + a % m).
 *
 * r   Result of doubling.
 * a   Number to double in Montogmery form.
 * m   Modulus (prime).
 */
static void sp_256_mont_dbl_5(sp_digit* r, const sp_digit* a, const sp_digit* m)
{
    (void)sp_256_add_5(r, a, a);
    sp_256_norm_5(r);
    sp_256_cond_sub_5(r, r, m, 0 - (((r[4] >> 48) > 0) ?
                (sp_digit)1 : (sp_digit)0));
    sp_256_norm_5(r);
}

/* Triple a Montgomery form number (r = a + a + a % m).
 *
 * r   Result of Tripling.
 * a   Number to triple in Montogmery form.
 * m   Modulus (prime).
 */
static void sp_256_mont_tpl_5(sp_digit* r, const sp_digit* a, const sp_digit* m)
{
    (void)sp_256_add_5(r, a, a);
    sp_256_norm_5(r);
    sp_256_cond_sub_5(r, r, m, 0 - (((r[4] >> 48) > 0) ?
                (sp_digit)1 : (sp_digit)0));
    sp_256_norm_5(r);
    (void)sp_256_add_5(r, r, a);
    sp_256_norm_5(r);
    sp_256_cond_sub_5(r, r, m, 0 - (((r[4] >> 48) > 0) ?
                (sp_digit)1 : (sp_digit)0));
    sp_256_norm_5(r);
}

#ifdef WOLFSSL_SP_SMALL
/* Sub b from a into r. (r = a - b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A single precision integer.
 */
SP_NOINLINE static int sp_256_sub_5(sp_digit* r, const sp_digit* a,
        const sp_digit* b)
{
    int i;

    for (i = 0; i < 5; i++) {
        r[i] = a[i] - b[i];
    }

    return 0;
}

#else
/* Sub b from a into r. (r = a - b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A single precision integer.
 */
SP_NOINLINE static int sp_256_sub_5(sp_digit* r, const sp_digit* a,
        const sp_digit* b)
{
    r[ 0] = a[ 0] - b[ 0];
    r[ 1] = a[ 1] - b[ 1];
    r[ 2] = a[ 2] - b[ 2];
    r[ 3] = a[ 3] - b[ 3];
    r[ 4] = a[ 4] - b[ 4];

    return 0;
}

#endif /* WOLFSSL_SP_SMALL */
/* Conditionally add a and b using the mask m.
 * m is -1 to add and 0 when not.
 *
 * r  A single precision number representing conditional add result.
 * a  A single precision number to add with.
 * b  A single precision number to add.
 * m  Mask value to apply.
 */
static void sp_256_cond_add_5(sp_digit* r, const sp_digit* a,
        const sp_digit* b, const sp_digit m)
{
#ifdef WOLFSSL_SP_SMALL
    int i;

    for (i = 0; i < 5; i++) {
        r[i] = a[i] + (b[i] & m);
    }
#else
    r[ 0] = a[ 0] + (b[ 0] & m);
    r[ 1] = a[ 1] + (b[ 1] & m);
    r[ 2] = a[ 2] + (b[ 2] & m);
    r[ 3] = a[ 3] + (b[ 3] & m);
    r[ 4] = a[ 4] + (b[ 4] & m);
#endif /* WOLFSSL_SP_SMALL */
}

/* Subtract two Montgomery form numbers (r = a - b % m).
 *
 * r   Result of subtration.
 * a   Number to subtract from in Montogmery form.
 * b   Number to subtract with in Montogmery form.
 * m   Modulus (prime).
 */
static void sp_256_mont_sub_5(sp_digit* r, const sp_digit* a, const sp_digit* b,
        const sp_digit* m)
{
    (void)sp_256_sub_5(r, a, b);
    sp_256_cond_add_5(r, r, m, r[4] >> 48);
    sp_256_norm_5(r);
}

/* Shift number left one bit.
 * Bottom bit is lost.
 *
 * r  Result of shift.
 * a  Number to shift.
 */
SP_NOINLINE static void sp_256_rshift1_5(sp_digit* r, sp_digit* a)
{
#ifdef WOLFSSL_SP_SMALL
    int i;

    for (i=0; i<4; i++) {
        r[i] = ((a[i] >> 1) | (a[i + 1] << 51)) & 0xfffffffffffffL;
    }
#else
    r[0] = ((a[0] >> 1) | (a[1] << 51)) & 0xfffffffffffffL;
    r[1] = ((a[1] >> 1) | (a[2] << 51)) & 0xfffffffffffffL;
    r[2] = ((a[2] >> 1) | (a[3] << 51)) & 0xfffffffffffffL;
    r[3] = ((a[3] >> 1) | (a[4] << 51)) & 0xfffffffffffffL;
#endif
    r[4] = a[4] >> 1;
}

/* Divide the number by 2 mod the modulus (prime). (r = a / 2 % m)
 *
 * r  Result of division by 2.
 * a  Number to divide.
 * m  Modulus (prime).
 */
static void sp_256_div2_5(sp_digit* r, const sp_digit* a, const sp_digit* m)
{
    sp_256_cond_add_5(r, a, m, 0 - (a[0] & 1));
    sp_256_norm_5(r);
    sp_256_rshift1_5(r, r);
}

/* Double the Montgomery form projective point p.
 *
 * r  Result of doubling point.
 * p  Point to double.
 * t  Temporary ordinate data.
 */
#ifdef WOLFSSL_SP_NONBLOCK
typedef struct sp_256_proj_point_dbl_5_ctx {
    int state;
    sp_digit* t1;
    sp_digit* t2;
    sp_digit* x;
    sp_digit* y;
    sp_digit* z;
} sp_256_proj_point_dbl_5_ctx;

static int sp_256_proj_point_dbl_5_nb(sp_ecc_ctx_t* sp_ctx, sp_point_256* r, const sp_point_256* p, sp_digit* t)
{
    int err = FP_WOULDBLOCK;
    sp_256_proj_point_dbl_5_ctx* ctx = (sp_256_proj_point_dbl_5_ctx*)sp_ctx->data;

    typedef char ctx_size_test[sizeof(sp_256_proj_point_dbl_5_ctx) >= sizeof(*sp_ctx) ? -1 : 1];
    (void)sizeof(ctx_size_test);

    switch (ctx->state) {
    case 0:
        ctx->t1 = t;
        ctx->t2 = t + 2*5;
        ctx->x = r->x;
        ctx->y = r->y;
        ctx->z = r->z;

        /* Put infinity into result. */
        if (r != p) {
            r->infinity = p->infinity;
        }
        ctx->state = 1;
        break;
    case 1:
        /* T1 = Z * Z */
        sp_256_mont_sqr_5(ctx->t1, p->z, p256_mod, p256_mp_mod);
        ctx->state = 2;
        break;
    case 2:
        /* Z = Y * Z */
        sp_256_mont_mul_5(ctx->z, p->y, p->z, p256_mod, p256_mp_mod);
        ctx->state = 3;
        break;
    case 3:
        /* Z = 2Z */
        sp_256_mont_dbl_5(ctx->z, ctx->z, p256_mod);
        ctx->state = 4;
        break;
    case 4:
        /* T2 = X - T1 */
        sp_256_mont_sub_5(ctx->t2, p->x, ctx->t1, p256_mod);
        ctx->state = 5;
        break;
    case 5:
        /* T1 = X + T1 */
        sp_256_mont_add_5(ctx->t1, p->x, ctx->t1, p256_mod);
        ctx->state = 6;
        break;
    case 6:
        /* T2 = T1 * T2 */
        sp_256_mont_mul_5(ctx->t2, ctx->t1, ctx->t2, p256_mod, p256_mp_mod);
        ctx->state = 7;
        break;
    case 7:
        /* T1 = 3T2 */
        sp_256_mont_tpl_5(ctx->t1, ctx->t2, p256_mod);
        ctx->state = 8;
        break;
    case 8:
        /* Y = 2Y */
        sp_256_mont_dbl_5(ctx->y, p->y, p256_mod);
        ctx->state = 9;
        break;
    case 9:
        /* Y = Y * Y */
        sp_256_mont_sqr_5(ctx->y, ctx->y, p256_mod, p256_mp_mod);
        ctx->state = 10;
        break;
    case 10:
        /* T2 = Y * Y */
        sp_256_mont_sqr_5(ctx->t2, ctx->y, p256_mod, p256_mp_mod);
        ctx->state = 11;
        break;
    case 11:
        /* T2 = T2/2 */
        sp_256_div2_5(ctx->t2, ctx->t2, p256_mod);
        ctx->state = 12;
        break;
    case 12:
        /* Y = Y * X */
        sp_256_mont_mul_5(ctx->y, ctx->y, p->x, p256_mod, p256_mp_mod);
        ctx->state = 13;
        break;
    case 13:
        /* X = T1 * T1 */
        sp_256_mont_sqr_5(ctx->x, ctx->t1, p256_mod, p256_mp_mod);
        ctx->state = 14;
        break;
    case 14:
        /* X = X - Y */
        sp_256_mont_sub_5(ctx->x, ctx->x, ctx->y, p256_mod);
        ctx->state = 15;
        break;
    case 15:
        /* X = X - Y */
        sp_256_mont_sub_5(ctx->x, ctx->x, ctx->y, p256_mod);
        ctx->state = 16;
        break;
    case 16:
        /* Y = Y - X */
        sp_256_mont_sub_5(ctx->y, ctx->y, ctx->x, p256_mod);
        ctx->state = 17;
        break;
    case 17:
        /* Y = Y * T1 */
        sp_256_mont_mul_5(ctx->y, ctx->y, ctx->t1, p256_mod, p256_mp_mod);
        ctx->state = 18;
        break;
    case 18:
        /* Y = Y - T2 */
        sp_256_mont_sub_5(ctx->y, ctx->y, ctx->t2, p256_mod);
        ctx->state = 19;
        /* fall-through */
    case 19:
        err = MP_OKAY;
        break;
    }

    if (err == MP_OKAY && ctx->state != 19) {
        err = FP_WOULDBLOCK;
    }

    return err;
}
#endif /* WOLFSSL_SP_NONBLOCK */

static void sp_256_proj_point_dbl_5(sp_point_256* r, const sp_point_256* p, sp_digit* t)
{
    sp_digit* t1 = t;
    sp_digit* t2 = t + 2*5;
    sp_digit* x;
    sp_digit* y;
    sp_digit* z;

    x = r->x;
    y = r->y;
    z = r->z;
    /* Put infinity into result. */
    if (r != p) {
        r->infinity = p->infinity;
    }

    /* T1 = Z * Z */
    sp_256_mont_sqr_5(t1, p->z, p256_mod, p256_mp_mod);
    /* Z = Y * Z */
    sp_256_mont_mul_5(z, p->y, p->z, p256_mod, p256_mp_mod);
    /* Z = 2Z */
    sp_256_mont_dbl_5(z, z, p256_mod);
    /* T2 = X - T1 */
    sp_256_mont_sub_5(t2, p->x, t1, p256_mod);
    /* T1 = X + T1 */
    sp_256_mont_add_5(t1, p->x, t1, p256_mod);
    /* T2 = T1 * T2 */
    sp_256_mont_mul_5(t2, t1, t2, p256_mod, p256_mp_mod);
    /* T1 = 3T2 */
    sp_256_mont_tpl_5(t1, t2, p256_mod);
    /* Y = 2Y */
    sp_256_mont_dbl_5(y, p->y, p256_mod);
    /* Y = Y * Y */
    sp_256_mont_sqr_5(y, y, p256_mod, p256_mp_mod);
    /* T2 = Y * Y */
    sp_256_mont_sqr_5(t2, y, p256_mod, p256_mp_mod);
    /* T2 = T2/2 */
    sp_256_div2_5(t2, t2, p256_mod);
    /* Y = Y * X */
    sp_256_mont_mul_5(y, y, p->x, p256_mod, p256_mp_mod);
    /* X = T1 * T1 */
    sp_256_mont_sqr_5(x, t1, p256_mod, p256_mp_mod);
    /* X = X - Y */
    sp_256_mont_sub_5(x, x, y, p256_mod);
    /* X = X - Y */
    sp_256_mont_sub_5(x, x, y, p256_mod);
    /* Y = Y - X */
    sp_256_mont_sub_5(y, y, x, p256_mod);
    /* Y = Y * T1 */
    sp_256_mont_mul_5(y, y, t1, p256_mod, p256_mp_mod);
    /* Y = Y - T2 */
    sp_256_mont_sub_5(y, y, t2, p256_mod);
}

/* Compare two numbers to determine if they are equal.
 * Constant time implementation.
 *
 * a  First number to compare.
 * b  Second number to compare.
 * returns 1 when equal and 0 otherwise.
 */
static int sp_256_cmp_equal_5(const sp_digit* a, const sp_digit* b)
{
    return ((a[0] ^ b[0]) | (a[1] ^ b[1]) | (a[2] ^ b[2]) | (a[3] ^ b[3]) |
            (a[4] ^ b[4])) == 0;
}

/* Add two Montgomery form projective points.
 *
 * r  Result of addition.
 * p  First point to add.
 * q  Second point to add.
 * t  Temporary ordinate data.
 */

#ifdef WOLFSSL_SP_NONBLOCK
typedef struct sp_256_proj_point_add_5_ctx {
    int state;
    sp_256_proj_point_dbl_5_ctx dbl_ctx;
    const sp_point_256* ap[2];
    sp_point_256* rp[2];
    sp_digit* t1;
    sp_digit* t2;
    sp_digit* t3;
    sp_digit* t4;
    sp_digit* t5;
    sp_digit* x;
    sp_digit* y;
    sp_digit* z;
} sp_256_proj_point_add_5_ctx;

static int sp_256_proj_point_add_5_nb(sp_ecc_ctx_t* sp_ctx, sp_point_256* r, 
    const sp_point_256* p, const sp_point_256* q, sp_digit* t)
{
    int err = FP_WOULDBLOCK;
    sp_256_proj_point_add_5_ctx* ctx = (sp_256_proj_point_add_5_ctx*)sp_ctx->data;

    /* Ensure only the first point is the same as the result. */
    if (q == r) {
        const sp_point_256* a = p;
        p = q;
        q = a;
    }

    typedef char ctx_size_test[sizeof(sp_256_proj_point_add_5_ctx) >= sizeof(*sp_ctx) ? -1 : 1];
    (void)sizeof(ctx_size_test);

    switch (ctx->state) {
    case 0: /* INIT */
        ctx->t1 = t;
        ctx->t2 = t + 2*5;
        ctx->t3 = t + 4*5;
        ctx->t4 = t + 6*5;
        ctx->t5 = t + 8*5;

        ctx->state = 1;
        break;
    case 1:
        /* Check double */
        (void)sp_256_sub_5(ctx->t1, p256_mod, q->y);
        sp_256_norm_5(ctx->t1);
        if ((sp_256_cmp_equal_5(p->x, q->x) & sp_256_cmp_equal_5(p->z, q->z) &
            (sp_256_cmp_equal_5(p->y, q->y) | sp_256_cmp_equal_5(p->y, ctx->t1))) != 0)
        {
            XMEMSET(&ctx->dbl_ctx, 0, sizeof(ctx->dbl_ctx));
            ctx->state = 2;
        }
        else {
            ctx->state = 3;
        }
        break;
    case 2:
        err = sp_256_proj_point_dbl_5_nb((sp_ecc_ctx_t*)&ctx->dbl_ctx, r, p, t);
        if (err == MP_OKAY)
            ctx->state = 27; /* done */
        break;
    case 3:
    {
        int i;
        ctx->rp[0] = r;

        /*lint allow cast to different type of pointer*/
        ctx->rp[1] = (sp_point_256*)t; /*lint !e9087 !e740*/
        XMEMSET(ctx->rp[1], 0, sizeof(sp_point_256));
        ctx->x = ctx->rp[p->infinity | q->infinity]->x;
        ctx->y = ctx->rp[p->infinity | q->infinity]->y;
        ctx->z = ctx->rp[p->infinity | q->infinity]->z;

        ctx->ap[0] = p;
        ctx->ap[1] = q;
        for (i=0; i<5; i++) {
            r->x[i] = ctx->ap[p->infinity]->x[i];
        }
        for (i=0; i<5; i++) {
            r->y[i] = ctx->ap[p->infinity]->y[i];
        }
        for (i=0; i<5; i++) {
            r->z[i] = ctx->ap[p->infinity]->z[i];
        }
        r->infinity = ctx->ap[p->infinity]->infinity;

        ctx->state = 4;
        break;
    }
    case 4:
        /* U1 = X1*Z2^2 */
        sp_256_mont_sqr_5(ctx->t1, q->z, p256_mod, p256_mp_mod);
        ctx->state = 5;
        break;
    case 5:
        sp_256_mont_mul_5(ctx->t3, ctx->t1, q->z, p256_mod, p256_mp_mod);
        ctx->state = 6;
        break;
    case 6:
        sp_256_mont_mul_5(ctx->t1, ctx->t1, ctx->x, p256_mod, p256_mp_mod);
        ctx->state = 7;
        break;
    case 7:
        /* U2 = X2*Z1^2 */
        sp_256_mont_sqr_5(ctx->t2, ctx->z, p256_mod, p256_mp_mod);
        ctx->state = 8;
        break;
    case 8:
        sp_256_mont_mul_5(ctx->t4, ctx->t2, ctx->z, p256_mod, p256_mp_mod);
        ctx->state = 9;
        break;
    case 9:
        sp_256_mont_mul_5(ctx->t2, ctx->t2, q->x, p256_mod, p256_mp_mod);
        ctx->state = 10;
        break;
    case 10:
        /* S1 = Y1*Z2^3 */
        sp_256_mont_mul_5(ctx->t3, ctx->t3, ctx->y, p256_mod, p256_mp_mod);
        ctx->state = 11;
        break;
    case 11:
        /* S2 = Y2*Z1^3 */
        sp_256_mont_mul_5(ctx->t4, ctx->t4, q->y, p256_mod, p256_mp_mod);
        ctx->state = 12;
        break;
    case 12:
        /* H = U2 - U1 */
        sp_256_mont_sub_5(ctx->t2, ctx->t2, ctx->t1, p256_mod);
        ctx->state = 13;
        break;
    case 13:
        /* R = S2 - S1 */
        sp_256_mont_sub_5(ctx->t4, ctx->t4, ctx->t3, p256_mod);
        ctx->state = 14;
        break;
    case 14:
        /* Z3 = H*Z1*Z2 */
        sp_256_mont_mul_5(ctx->z, ctx->z, q->z, p256_mod, p256_mp_mod);
        ctx->state = 15;
        break;
    case 15:
        sp_256_mont_mul_5(ctx->z, ctx->z, ctx->t2, p256_mod, p256_mp_mod);
        ctx->state = 16;
        break;
    case 16:
        /* X3 = R^2 - H^3 - 2*U1*H^2 */
        sp_256_mont_sqr_5(ctx->x, ctx->t4, p256_mod, p256_mp_mod);
        ctx->state = 17;
        break;
    case 17:
        sp_256_mont_sqr_5(ctx->t5, ctx->t2, p256_mod, p256_mp_mod);
        ctx->state = 18;
        break;
    case 18:
        sp_256_mont_mul_5(ctx->y, ctx->t1, ctx->t5, p256_mod, p256_mp_mod);
        ctx->state = 19;
        break;
    case 19:
        sp_256_mont_mul_5(ctx->t5, ctx->t5, ctx->t2, p256_mod, p256_mp_mod);
        ctx->state = 20;
        break;
    case 20:
        sp_256_mont_sub_5(ctx->x, ctx->x, ctx->t5, p256_mod);
        ctx->state = 21;
        break;
    case 21:
        sp_256_mont_dbl_5(ctx->t1, ctx->y, p256_mod);
        ctx->state = 22;
        break;
    case 22:
        sp_256_mont_sub_5(ctx->x, ctx->x, ctx->t1, p256_mod);
        ctx->state = 23;
        break;
    case 23:
        /* Y3 = R*(U1*H^2 - X3) - S1*H^3 */
        sp_256_mont_sub_5(ctx->y, ctx->y, ctx->x, p256_mod);
        ctx->state = 24;
        break;
    case 24:
        sp_256_mont_mul_5(ctx->y, ctx->y, ctx->t4, p256_mod, p256_mp_mod);
        ctx->state = 25;
        break;
    case 25:
        sp_256_mont_mul_5(ctx->t5, ctx->t5, ctx->t3, p256_mod, p256_mp_mod);
        ctx->state = 26;
        break;
    case 26:
        sp_256_mont_sub_5(ctx->y, ctx->y, ctx->t5, p256_mod);
        ctx->state = 27;
        /* fall-through */
    case 27:
        err = MP_OKAY;
        break;
    }

    if (err == MP_OKAY && ctx->state != 27) {
        err = FP_WOULDBLOCK;
    }
    return err;
}
#endif /* WOLFSSL_SP_NONBLOCK */

static void sp_256_proj_point_add_5(sp_point_256* r, const sp_point_256* p, const sp_point_256* q,
        sp_digit* t)
{
    const sp_point_256* ap[2];
    sp_point_256* rp[2];
    sp_digit* t1 = t;
    sp_digit* t2 = t + 2*5;
    sp_digit* t3 = t + 4*5;
    sp_digit* t4 = t + 6*5;
    sp_digit* t5 = t + 8*5;
    sp_digit* x;
    sp_digit* y;
    sp_digit* z;
    int i;

    /* Ensure only the first point is the same as the result. */
    if (q == r) {
        const sp_point_256* a = p;
        p = q;
        q = a;
    }

    /* Check double */
    (void)sp_256_sub_5(t1, p256_mod, q->y);
    sp_256_norm_5(t1);
    if ((sp_256_cmp_equal_5(p->x, q->x) & sp_256_cmp_equal_5(p->z, q->z) &
        (sp_256_cmp_equal_5(p->y, q->y) | sp_256_cmp_equal_5(p->y, t1))) != 0) {
        sp_256_proj_point_dbl_5(r, p, t);
    }
    else {
        rp[0] = r;

        /*lint allow cast to different type of pointer*/
        rp[1] = (sp_point_256*)t; /*lint !e9087 !e740*/
        XMEMSET(rp[1], 0, sizeof(sp_point_256));
        x = rp[p->infinity | q->infinity]->x;
        y = rp[p->infinity | q->infinity]->y;
        z = rp[p->infinity | q->infinity]->z;

        ap[0] = p;
        ap[1] = q;
        for (i=0; i<5; i++) {
            r->x[i] = ap[p->infinity]->x[i];
        }
        for (i=0; i<5; i++) {
            r->y[i] = ap[p->infinity]->y[i];
        }
        for (i=0; i<5; i++) {
            r->z[i] = ap[p->infinity]->z[i];
        }
        r->infinity = ap[p->infinity]->infinity;

        /* U1 = X1*Z2^2 */
        sp_256_mont_sqr_5(t1, q->z, p256_mod, p256_mp_mod);
        sp_256_mont_mul_5(t3, t1, q->z, p256_mod, p256_mp_mod);
        sp_256_mont_mul_5(t1, t1, x, p256_mod, p256_mp_mod);
        /* U2 = X2*Z1^2 */
        sp_256_mont_sqr_5(t2, z, p256_mod, p256_mp_mod);
        sp_256_mont_mul_5(t4, t2, z, p256_mod, p256_mp_mod);
        sp_256_mont_mul_5(t2, t2, q->x, p256_mod, p256_mp_mod);
        /* S1 = Y1*Z2^3 */
        sp_256_mont_mul_5(t3, t3, y, p256_mod, p256_mp_mod);
        /* S2 = Y2*Z1^3 */
        sp_256_mont_mul_5(t4, t4, q->y, p256_mod, p256_mp_mod);
        /* H = U2 - U1 */
        sp_256_mont_sub_5(t2, t2, t1, p256_mod);
        /* R = S2 - S1 */
        sp_256_mont_sub_5(t4, t4, t3, p256_mod);
        /* Z3 = H*Z1*Z2 */
        sp_256_mont_mul_5(z, z, q->z, p256_mod, p256_mp_mod);
        sp_256_mont_mul_5(z, z, t2, p256_mod, p256_mp_mod);
        /* X3 = R^2 - H^3 - 2*U1*H^2 */
        sp_256_mont_sqr_5(x, t4, p256_mod, p256_mp_mod);
        sp_256_mont_sqr_5(t5, t2, p256_mod, p256_mp_mod);
        sp_256_mont_mul_5(y, t1, t5, p256_mod, p256_mp_mod);
        sp_256_mont_mul_5(t5, t5, t2, p256_mod, p256_mp_mod);
        sp_256_mont_sub_5(x, x, t5, p256_mod);
        sp_256_mont_dbl_5(t1, y, p256_mod);
        sp_256_mont_sub_5(x, x, t1, p256_mod);
        /* Y3 = R*(U1*H^2 - X3) - S1*H^3 */
        sp_256_mont_sub_5(y, y, x, p256_mod);
        sp_256_mont_mul_5(y, y, t4, p256_mod, p256_mp_mod);
        sp_256_mont_mul_5(t5, t5, t3, p256_mod, p256_mp_mod);
        sp_256_mont_sub_5(y, y, t5, p256_mod);
    }
}

#ifdef WOLFSSL_SP_SMALL
/* Multiply the point by the scalar and return the result.
 * If map is true then convert result to affine coordinates.
 *
 * r     Resulting point.
 * g     Point to multiply.
 * k     Scalar to multiply by.
 * map   Indicates whether to convert result to affine.
 * ct    Constant time required.
 * heap  Heap to use for allocation.
 * returns MEMORY_E when memory allocation fails and MP_OKAY on success.
 */

#ifdef WOLFSSL_SP_NONBLOCK
typedef struct sp_256_ecc_mulmod_5_ctx {
    int state;
    union {
        sp_256_proj_point_dbl_5_ctx dbl_ctx;
        sp_256_proj_point_add_5_ctx add_ctx;
    };
    sp_point_256 t[3];
    sp_digit tmp[2 * 5 * 5];
    sp_digit n;
    int i;
    int c;
    int y;
} sp_256_ecc_mulmod_5_ctx;

static int sp_256_ecc_mulmod_5_nb(sp_ecc_ctx_t* sp_ctx, sp_point_256* r, 
    const sp_point_256* g, const sp_digit* k, int map, int ct, void* heap)
{
    int err = FP_WOULDBLOCK;
    sp_256_ecc_mulmod_5_ctx* ctx = (sp_256_ecc_mulmod_5_ctx*)sp_ctx->data;

    typedef char ctx_size_test[sizeof(sp_256_ecc_mulmod_5_ctx) >= sizeof(*sp_ctx) ? -1 : 1];
    (void)sizeof(ctx_size_test);

    /* Implementation is constant time. */
    (void)ct;

    switch (ctx->state) {
    case 0: /* INIT */
        XMEMSET(ctx->t, 0, sizeof(sp_point_256) * 3);
        ctx->i = 4;
        ctx->c = 48;
        ctx->n = k[ctx->i--] << (52 - ctx->c);

        /* t[0] = {0, 0, 1} * norm */
        ctx->t[0].infinity = 1;
        ctx->state = 1;
        break;
    case 1: /* T1X */
        /* t[1] = {g->x, g->y, g->z} * norm */
        err = sp_256_mod_mul_norm_5(ctx->t[1].x, g->x, p256_mod);
        ctx->state = 2;
        break;
    case 2: /* T1Y */
        err = sp_256_mod_mul_norm_5(ctx->t[1].y, g->y, p256_mod);
        ctx->state = 3;
        break;
    case 3: /* T1Z */
        err = sp_256_mod_mul_norm_5(ctx->t[1].z, g->z, p256_mod);
        ctx->state = 4;
        break;
    case 4: /* ADDPREP */
        if (ctx->c == 0) {
            if (ctx->i == -1) {
                ctx->state = 7;
                break;
            }

            ctx->n = k[ctx->i--];
            ctx->c = 52;
        }
        ctx->y = (ctx->n >> 51) & 1;
        ctx->n <<= 1;
        XMEMSET(&ctx->add_ctx, 0, sizeof(ctx->add_ctx));
        ctx->state = 5;
        break;
    case 5: /* ADD */
        err = sp_256_proj_point_add_5_nb((sp_ecc_ctx_t*)&ctx->add_ctx, 
            &ctx->t[ctx->y^1], &ctx->t[0], &ctx->t[1], ctx->tmp);
        if (err == MP_OKAY) {
            XMEMCPY(&ctx->t[2], (void*)(((size_t)&ctx->t[0] & addr_mask[ctx->y^1]) +
                                        ((size_t)&ctx->t[1] & addr_mask[ctx->y])),
                    sizeof(sp_point_256));
            XMEMSET(&ctx->dbl_ctx, 0, sizeof(ctx->dbl_ctx));
            ctx->state = 6;
        }
        break;
    case 6: /* DBL */
        err = sp_256_proj_point_dbl_5_nb((sp_ecc_ctx_t*)&ctx->dbl_ctx, &ctx->t[2], 
            &ctx->t[2], ctx->tmp);
        if (err == MP_OKAY) {
            XMEMCPY((void*)(((size_t)&ctx->t[0] & addr_mask[ctx->y^1]) +
                            ((size_t)&ctx->t[1] & addr_mask[ctx->y])), &ctx->t[2],
                    sizeof(sp_point_256));
            ctx->state = 4;
            ctx->c--;
        }
        break;
    case 7: /* MAP */
        if (map != 0) {
            sp_256_map_5(r, &ctx->t[0], ctx->tmp);
        }
        else {
            XMEMCPY(r, &ctx->t[0], sizeof(sp_point_256));
        }
        err = MP_OKAY;
        break;
    }

    if (err == MP_OKAY && ctx->state != 7) {
        err = FP_WOULDBLOCK;
    }
    if (err != FP_WOULDBLOCK) {
        ForceZero(ctx->tmp, sizeof(ctx->tmp));
        ForceZero(ctx->t, sizeof(ctx->t));
    }

    (void)heap;

    return err;
}

#endif /* WOLFSSL_SP_NONBLOCK */

static int sp_256_ecc_mulmod_5(sp_point_256* r, const sp_point_256* g, const sp_digit* k,
        int map, int ct, void* heap)
{
#ifdef WOLFSSL_SP_NO_MALLOC
    sp_point_256 t[3];
    sp_digit tmp[2 * 5 * 5];
#else
    sp_point_256* t;
    sp_digit* tmp;
#endif
    sp_digit n;
    int i;
    int c, y;
    int err = MP_OKAY;

    /* Implementatio is constant time. */
    (void)ct;
    (void)heap;

#ifndef WOLFSSL_SP_NO_MALLOC
    t = (sp_point_256*)XMALLOC(sizeof(sp_point_256) * 3, heap, DYNAMIC_TYPE_ECC);
    if (t == NULL)
        err = MEMORY_E;
    tmp = (sp_digit*)XMALLOC(sizeof(sp_digit) * 2 * 5 * 5, heap,
                                                              DYNAMIC_TYPE_ECC);
    if (tmp == NULL)
        err = MEMORY_E;
#endif

    if (err == MP_OKAY) {
        XMEMSET(t, 0, sizeof(sp_point_256) * 3);

        /* t[0] = {0, 0, 1} * norm */
        t[0].infinity = 1;
        /* t[1] = {g->x, g->y, g->z} * norm */
        err = sp_256_mod_mul_norm_5(t[1].x, g->x, p256_mod);
    }
    if (err == MP_OKAY)
        err = sp_256_mod_mul_norm_5(t[1].y, g->y, p256_mod);
    if (err == MP_OKAY)
        err = sp_256_mod_mul_norm_5(t[1].z, g->z, p256_mod);

    if (err == MP_OKAY) {
        i = 4;
        c = 48;
        n = k[i--] << (52 - c);
        for (; ; c--) {
            if (c == 0) {
                if (i == -1)
                    break;

                n = k[i--];
                c = 52;
            }

            y = (n >> 51) & 1;
            n <<= 1;

            sp_256_proj_point_add_5(&t[y^1], &t[0], &t[1], tmp);

            XMEMCPY(&t[2], (void*)(((size_t)&t[0] & addr_mask[y^1]) +
                                   ((size_t)&t[1] & addr_mask[y])),
                    sizeof(sp_point_256));
            sp_256_proj_point_dbl_5(&t[2], &t[2], tmp);
            XMEMCPY((void*)(((size_t)&t[0] & addr_mask[y^1]) +
                            ((size_t)&t[1] & addr_mask[y])), &t[2],
                    sizeof(sp_point_256));
        }

        if (map != 0) {
            sp_256_map_5(r, &t[0], tmp);
        }
        else {
            XMEMCPY(r, &t[0], sizeof(sp_point_256));
        }
    }

#ifndef WOLFSSL_SP_NO_MALLOC
    if (tmp != NULL) {
        XMEMSET(tmp, 0, sizeof(sp_digit) * 2 * 5 * 5);
        XFREE(tmp, NULL, DYNAMIC_TYPE_ECC);
    }
    if (t != NULL) {
        XMEMSET(t, 0, sizeof(sp_point_256) * 3);
        XFREE(t, NULL, DYNAMIC_TYPE_ECC);
    }
#else
    ForceZero(tmp, sizeof(tmp));
    ForceZero(t, sizeof(t));
#endif

    return err;
}

#else
/* A table entry for pre-computed points. */
typedef struct sp_table_entry_256 {
    sp_digit x[5];
    sp_digit y[5];
} sp_table_entry_256;

/* Conditionally copy a into r using the mask m.
 * m is -1 to copy and 0 when not.
 *
 * r  A single precision number to copy over.
 * a  A single precision number to copy.
 * m  Mask value to apply.
 */
static void sp_256_cond_copy_5(sp_digit* r, const sp_digit* a, const sp_digit m)
{
    sp_digit t[5];
#ifdef WOLFSSL_SP_SMALL
    int i;

    for (i = 0; i < 5; i++) {
        t[i] = r[i] ^ a[i];
    }
    for (i = 0; i < 5; i++) {
        r[i] ^= t[i] & m;
    }
#else
    t[ 0] = r[ 0] ^ a[ 0];
    t[ 1] = r[ 1] ^ a[ 1];
    t[ 2] = r[ 2] ^ a[ 2];
    t[ 3] = r[ 3] ^ a[ 3];
    t[ 4] = r[ 4] ^ a[ 4];
    r[ 0] ^= t[ 0] & m;
    r[ 1] ^= t[ 1] & m;
    r[ 2] ^= t[ 2] & m;
    r[ 3] ^= t[ 3] & m;
    r[ 4] ^= t[ 4] & m;
#endif /* WOLFSSL_SP_SMALL */
}

/* Double the Montgomery form projective point p a number of times.
 *
 * r  Result of repeated doubling of point.
 * p  Point to double.
 * n  Number of times to double
 * t  Temporary ordinate data.
 */
static void sp_256_proj_point_dbl_n_5(sp_point_256* p, int n, sp_digit* t)
{
    sp_digit* w = t;
    sp_digit* a = t + 2*5;
    sp_digit* b = t + 4*5;
    sp_digit* t1 = t + 6*5;
    sp_digit* t2 = t + 8*5;
    sp_digit* x;
    sp_digit* y;
    sp_digit* z;

    x = p->x;
    y = p->y;
    z = p->z;

    /* Y = 2*Y */
    sp_256_mont_dbl_5(y, y, p256_mod);
    /* W = Z^4 */
    sp_256_mont_sqr_5(w, z, p256_mod, p256_mp_mod);
    sp_256_mont_sqr_5(w, w, p256_mod, p256_mp_mod);

#ifndef WOLFSSL_SP_SMALL
    while (--n > 0)
#else
    while (--n >= 0)
#endif
    {
        /* A = 3*(X^2 - W) */
        sp_256_mont_sqr_5(t1, x, p256_mod, p256_mp_mod);
        sp_256_mont_sub_5(t1, t1, w, p256_mod);
        sp_256_mont_tpl_5(a, t1, p256_mod);
        /* B = X*Y^2 */
        sp_256_mont_sqr_5(t1, y, p256_mod, p256_mp_mod);
        sp_256_mont_mul_5(b, t1, x, p256_mod, p256_mp_mod);
        /* X = A^2 - 2B */
        sp_256_mont_sqr_5(x, a, p256_mod, p256_mp_mod);
        sp_256_mont_dbl_5(t2, b, p256_mod);
        sp_256_mont_sub_5(x, x, t2, p256_mod);
        /* Z = Z*Y */
        sp_256_mont_mul_5(z, z, y, p256_mod, p256_mp_mod);
        /* t2 = Y^4 */
        sp_256_mont_sqr_5(t1, t1, p256_mod, p256_mp_mod);
#ifdef WOLFSSL_SP_SMALL
        if (n != 0)
#endif
        {
            /* W = W*Y^4 */
            sp_256_mont_mul_5(w, w, t1, p256_mod, p256_mp_mod);
        }
        /* y = 2*A*(B - X) - Y^4 */
        sp_256_mont_sub_5(y, b, x, p256_mod);
        sp_256_mont_mul_5(y, y, a, p256_mod, p256_mp_mod);
        sp_256_mont_dbl_5(y, y, p256_mod);
        sp_256_mont_sub_5(y, y, t1, p256_mod);
    }
#ifndef WOLFSSL_SP_SMALL
    /* A = 3*(X^2 - W) */
    sp_256_mont_sqr_5(t1, x, p256_mod, p256_mp_mod);
    sp_256_mont_sub_5(t1, t1, w, p256_mod);
    sp_256_mont_tpl_5(a, t1, p256_mod);
    /* B = X*Y^2 */
    sp_256_mont_sqr_5(t1, y, p256_mod, p256_mp_mod);
    sp_256_mont_mul_5(b, t1, x, p256_mod, p256_mp_mod);
    /* X = A^2 - 2B */
    sp_256_mont_sqr_5(x, a, p256_mod, p256_mp_mod);
    sp_256_mont_dbl_5(t2, b, p256_mod);
    sp_256_mont_sub_5(x, x, t2, p256_mod);
    /* Z = Z*Y */
    sp_256_mont_mul_5(z, z, y, p256_mod, p256_mp_mod);
    /* t2 = Y^4 */
    sp_256_mont_sqr_5(t1, t1, p256_mod, p256_mp_mod);
    /* y = 2*A*(B - X) - Y^4 */
    sp_256_mont_sub_5(y, b, x, p256_mod);
    sp_256_mont_mul_5(y, y, a, p256_mod, p256_mp_mod);
    sp_256_mont_dbl_5(y, y, p256_mod);
    sp_256_mont_sub_5(y, y, t1, p256_mod);
#endif
    /* Y = Y/2 */
    sp_256_div2_5(y, y, p256_mod);
}

/* Double the Montgomery form projective point p a number of times.
 *
 * r  Result of repeated doubling of point.
 * p  Point to double.
 * n  Number of times to double
 * t  Temporary ordinate data.
 */
static void sp_256_proj_point_dbl_n_store_5(sp_point_256* r, const sp_point_256* p,
        int n, int m, sp_digit* t)
{
    sp_digit* w = t;
    sp_digit* a = t + 2*5;
    sp_digit* b = t + 4*5;
    sp_digit* t1 = t + 6*5;
    sp_digit* t2 = t + 8*5;
    sp_digit* x = r[2*m].x;
    sp_digit* y = r[(1<<n)*m].y;
    sp_digit* z = r[2*m].z;
    int i;

    for (i=0; i<5; i++) {
        x[i] = p->x[i];
    }
    for (i=0; i<5; i++) {
        y[i] = p->y[i];
    }
    for (i=0; i<5; i++) {
        z[i] = p->z[i];
    }

    /* Y = 2*Y */
    sp_256_mont_dbl_5(y, y, p256_mod);
    /* W = Z^4 */
    sp_256_mont_sqr_5(w, z, p256_mod, p256_mp_mod);
    sp_256_mont_sqr_5(w, w, p256_mod, p256_mp_mod);
    for (i=1; i<=n; i++) {
        /* A = 3*(X^2 - W) */
        sp_256_mont_sqr_5(t1, x, p256_mod, p256_mp_mod);
        sp_256_mont_sub_5(t1, t1, w, p256_mod);
        sp_256_mont_tpl_5(a, t1, p256_mod);
        /* B = X*Y^2 */
        sp_256_mont_sqr_5(t2, y, p256_mod, p256_mp_mod);
        sp_256_mont_mul_5(b, t2, x, p256_mod, p256_mp_mod);
        x = r[(1<<i)*m].x;
        /* X = A^2 - 2B */
        sp_256_mont_sqr_5(x, a, p256_mod, p256_mp_mod);
        sp_256_mont_dbl_5(t1, b, p256_mod);
        sp_256_mont_sub_5(x, x, t1, p256_mod);
        /* Z = Z*Y */
        sp_256_mont_mul_5(r[(1<<i)*m].z, z, y, p256_mod, p256_mp_mod);
        z = r[(1<<i)*m].z;
        /* t2 = Y^4 */
        sp_256_mont_sqr_5(t2, t2, p256_mod, p256_mp_mod);
        if (i != n) {
            /* W = W*Y^4 */
            sp_256_mont_mul_5(w, w, t2, p256_mod, p256_mp_mod);
        }
        /* y = 2*A*(B - X) - Y^4 */
        sp_256_mont_sub_5(y, b, x, p256_mod);
        sp_256_mont_mul_5(y, y, a, p256_mod, p256_mp_mod);
        sp_256_mont_dbl_5(y, y, p256_mod);
        sp_256_mont_sub_5(y, y, t2, p256_mod);

        /* Y = Y/2 */
        sp_256_div2_5(r[(1<<i)*m].y, y, p256_mod);
        r[(1<<i)*m].infinity = 0;
    }
}

/* Add two Montgomery form projective points.
 *
 * ra  Result of addition.
 * rs  Result of subtraction.
 * p   First point to add.
 * q   Second point to add.
 * t   Temporary ordinate data.
 */
static void sp_256_proj_point_add_sub_5(sp_point_256* ra, sp_point_256* rs,
        const sp_point_256* p, const sp_point_256* q, sp_digit* t)
{
    sp_digit* t1 = t;
    sp_digit* t2 = t + 2*5;
    sp_digit* t3 = t + 4*5;
    sp_digit* t4 = t + 6*5;
    sp_digit* t5 = t + 8*5;
    sp_digit* t6 = t + 10*5;
    sp_digit* x = ra->x;
    sp_digit* y = ra->y;
    sp_digit* z = ra->z;
    sp_digit* xs = rs->x;
    sp_digit* ys = rs->y;
    sp_digit* zs = rs->z;


    XMEMCPY(x, p->x, sizeof(p->x) / 2);
    XMEMCPY(y, p->y, sizeof(p->y) / 2);
    XMEMCPY(z, p->z, sizeof(p->z) / 2);
    ra->infinity = 0;
    rs->infinity = 0;

    /* U1 = X1*Z2^2 */
    sp_256_mont_sqr_5(t1, q->z, p256_mod, p256_mp_mod);
    sp_256_mont_mul_5(t3, t1, q->z, p256_mod, p256_mp_mod);
    sp_256_mont_mul_5(t1, t1, x, p256_mod, p256_mp_mod);
    /* U2 = X2*Z1^2 */
    sp_256_mont_sqr_5(t2, z, p256_mod, p256_mp_mod);
    sp_256_mont_mul_5(t4, t2, z, p256_mod, p256_mp_mod);
    sp_256_mont_mul_5(t2, t2, q->x, p256_mod, p256_mp_mod);
    /* S1 = Y1*Z2^3 */
    sp_256_mont_mul_5(t3, t3, y, p256_mod, p256_mp_mod);
    /* S2 = Y2*Z1^3 */
    sp_256_mont_mul_5(t4, t4, q->y, p256_mod, p256_mp_mod);
    /* H = U2 - U1 */
    sp_256_mont_sub_5(t2, t2, t1, p256_mod);
    /* RS = S2 + S1 */
    sp_256_mont_add_5(t6, t4, t3, p256_mod);
    /* R = S2 - S1 */
    sp_256_mont_sub_5(t4, t4, t3, p256_mod);
    /* Z3 = H*Z1*Z2 */
    /* ZS = H*Z1*Z2 */
    sp_256_mont_mul_5(z, z, q->z, p256_mod, p256_mp_mod);
    sp_256_mont_mul_5(z, z, t2, p256_mod, p256_mp_mod);
    XMEMCPY(zs, z, sizeof(p->z)/2);
    /* X3 = R^2 - H^3 - 2*U1*H^2 */
    /* XS = RS^2 - H^3 - 2*U1*H^2 */
    sp_256_mont_sqr_5(x, t4, p256_mod, p256_mp_mod);
    sp_256_mont_sqr_5(xs, t6, p256_mod, p256_mp_mod);
    sp_256_mont_sqr_5(t5, t2, p256_mod, p256_mp_mod);
    sp_256_mont_mul_5(y, t1, t5, p256_mod, p256_mp_mod);
    sp_256_mont_mul_5(t5, t5, t2, p256_mod, p256_mp_mod);
    sp_256_mont_sub_5(x, x, t5, p256_mod);
    sp_256_mont_sub_5(xs, xs, t5, p256_mod);
    sp_256_mont_dbl_5(t1, y, p256_mod);
    sp_256_mont_sub_5(x, x, t1, p256_mod);
    sp_256_mont_sub_5(xs, xs, t1, p256_mod);
    /* Y3 = R*(U1*H^2 - X3) - S1*H^3 */
    /* YS = -RS*(U1*H^2 - XS) - S1*H^3 */
    sp_256_mont_sub_5(ys, y, xs, p256_mod);
    sp_256_mont_sub_5(y, y, x, p256_mod);
    sp_256_mont_mul_5(y, y, t4, p256_mod, p256_mp_mod);
    sp_256_sub_5(t6, p256_mod, t6);
    sp_256_mont_mul_5(ys, ys, t6, p256_mod, p256_mp_mod);
    sp_256_mont_mul_5(t5, t5, t3, p256_mod, p256_mp_mod);
    sp_256_mont_sub_5(y, y, t5, p256_mod);
    sp_256_mont_sub_5(ys, ys, t5, p256_mod);
}

/* Structure used to describe recoding of scalar multiplication. */
typedef struct ecc_recode_256 {
    /* Index into pre-computation table. */
    uint8_t i;
    /* Use the negative of the point. */
    uint8_t neg;
} ecc_recode_256;

/* The index into pre-computation table to use. */
static const uint8_t recode_index_5_6[66] = {
     0,  1,  2,  3,  4,  5,  6,  7,  8,  9, 10, 11, 12, 13, 14, 15,
    16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31,
    32, 31, 30, 29, 28, 27, 26, 25, 24, 23, 22, 21, 20, 19, 18, 17,
    16, 15, 14, 13, 12, 11, 10,  9,  8,  7,  6,  5,  4,  3,  2,  1,
     0,  1,
};

/* Whether to negate y-ordinate. */
static const uint8_t recode_neg_5_6[66] = {
     0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,
     0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,
     1,  1,  1,  1,  1,  1,  1,  1,  1,  1,  1,  1,  1,  1,  1,  1,
     1,  1,  1,  1,  1,  1,  1,  1,  1,  1,  1,  1,  1,  1,  1,  1,
     0,  0,
};

/* Recode the scalar for multiplication using pre-computed values and
 * subtraction.
 *
 * k  Scalar to multiply by.
 * v  Vector of operations to perform.
 */
static void sp_256_ecc_recode_6_5(const sp_digit* k, ecc_recode_256* v)
{
    int i, j;
    uint8_t y;
    int carry = 0;
    int o;
    sp_digit n;

    j = 0;
    n = k[j];
    o = 0;
    for (i=0; i<43; i++) {
        y = n;
        if (o + 6 < 52) {
            y &= 0x3f;
            n >>= 6;
            o += 6;
        }
        else if (o + 6 == 52) {
            n >>= 6;
            if (++j < 5)
                n = k[j];
            o = 0;
        }
        else if (++j < 5) {
            n = k[j];
            y |= (n << (52 - o)) & 0x3f;
            o -= 46;
            n >>= o;
        }

        y += carry;
        v[i].i = recode_index_5_6[y];
        v[i].neg = recode_neg_5_6[y];
        carry = (y >> 6) + v[i].neg;
    }
}

#ifndef WC_NO_CACHE_RESISTANT
/* Touch each possible point that could be being copied.
 *
 * r      Point to copy into.
 * table  Table - start of the entires to access
 * idx    Index of entry to retrieve.
 */
static void sp_256_get_point_33_5(sp_point_256* r, const sp_point_256* table,
    int idx)
{
    int i;
    sp_digit mask;

    r->x[0] = 0;
    r->x[1] = 0;
    r->x[2] = 0;
    r->x[3] = 0;
    r->x[4] = 0;
    r->y[0] = 0;
    r->y[1] = 0;
    r->y[2] = 0;
    r->y[3] = 0;
    r->y[4] = 0;
    r->z[0] = 0;
    r->z[1] = 0;
    r->z[2] = 0;
    r->z[3] = 0;
    r->z[4] = 0;
    for (i = 1; i < 33; i++) {
        mask = 0 - (i == idx);
        r->x[0] |= mask & table[i].x[0];
        r->x[1] |= mask & table[i].x[1];
        r->x[2] |= mask & table[i].x[2];
        r->x[3] |= mask & table[i].x[3];
        r->x[4] |= mask & table[i].x[4];
        r->y[0] |= mask & table[i].y[0];
        r->y[1] |= mask & table[i].y[1];
        r->y[2] |= mask & table[i].y[2];
        r->y[3] |= mask & table[i].y[3];
        r->y[4] |= mask & table[i].y[4];
        r->z[0] |= mask & table[i].z[0];
        r->z[1] |= mask & table[i].z[1];
        r->z[2] |= mask & table[i].z[2];
        r->z[3] |= mask & table[i].z[3];
        r->z[4] |= mask & table[i].z[4];
    }
}
#endif /* !WC_NO_CACHE_RESISTANT */
/* Multiply the point by the scalar and return the result.
 * If map is true then convert result to affine coordinates.
 *
 * Window technique of 6 bits. (Add-Sub variation.)
 * Calculate 0..32 times the point. Use function that adds and
 * subtracts the same two points.
 * Recode to add or subtract one of the computed points.
 * Double to push up.
 * NOT a sliding window.
 *
 * r     Resulting point.
 * g     Point to multiply.
 * k     Scalar to multiply by.
 * map   Indicates whether to convert result to affine.
 * ct    Constant time required.
 * heap  Heap to use for allocation.
 * returns MEMORY_E when memory allocation fails and MP_OKAY on success.
 */
static int sp_256_ecc_mulmod_win_add_sub_5(sp_point_256* r, const sp_point_256* g,
        const sp_digit* k, int map, int ct, void* heap)
{
#if (!defined(WOLFSSL_SP_SMALL) && !defined(WOLFSSL_SMALL_STACK)) || defined(WOLFSSL_SP_NO_MALLOC)
    sp_point_256 td[33];
    sp_point_256 rtd, pd;
    sp_digit tmpd[2 * 5 * 6];
#endif
    sp_point_256* t;
    sp_point_256* rt;
    sp_point_256* p = NULL;
    sp_digit* tmp;
    sp_digit* negy;
    int i;
    ecc_recode_256 v[43];
    int err;

    /* Constant time used for cache attack resistance implementation. */
    (void)ct;
    (void)heap;

    err = sp_256_point_new_5(heap, rtd, rt);
    if (err == MP_OKAY)
        err = sp_256_point_new_5(heap, pd, p);
#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    t = (sp_point_256*)XMALLOC(sizeof(sp_point_256) * 33, heap, DYNAMIC_TYPE_ECC);
    if (t == NULL)
        err = MEMORY_E;
    tmp = (sp_digit*)XMALLOC(sizeof(sp_digit) * 2 * 5 * 6, heap,
                             DYNAMIC_TYPE_ECC);
    if (tmp == NULL)
        err = MEMORY_E;
#else
    t = td;
    tmp = tmpd;
#endif


    if (err == MP_OKAY) {
        /* t[0] = {0, 0, 1} * norm */
        XMEMSET(&t[0], 0, sizeof(t[0]));
        t[0].infinity = 1;
        /* t[1] = {g->x, g->y, g->z} * norm */
        err = sp_256_mod_mul_norm_5(t[1].x, g->x, p256_mod);
    }
    if (err == MP_OKAY) {
        err = sp_256_mod_mul_norm_5(t[1].y, g->y, p256_mod);
    }
    if (err == MP_OKAY) {
        err = sp_256_mod_mul_norm_5(t[1].z, g->z, p256_mod);
    }

    if (err == MP_OKAY) {
        t[1].infinity = 0;
        /* t[2] ... t[32]  */
        sp_256_proj_point_dbl_n_store_5(t, &t[ 1], 5, 1, tmp);
        sp_256_proj_point_add_5(&t[ 3], &t[ 2], &t[ 1], tmp);
        sp_256_proj_point_dbl_5(&t[ 6], &t[ 3], tmp);
        sp_256_proj_point_add_sub_5(&t[ 7], &t[ 5], &t[ 6], &t[ 1], tmp);
        sp_256_proj_point_dbl_5(&t[10], &t[ 5], tmp);
        sp_256_proj_point_add_sub_5(&t[11], &t[ 9], &t[10], &t[ 1], tmp);
        sp_256_proj_point_dbl_5(&t[12], &t[ 6], tmp);
        sp_256_proj_point_dbl_5(&t[14], &t[ 7], tmp);
        sp_256_proj_point_add_sub_5(&t[15], &t[13], &t[14], &t[ 1], tmp);
        sp_256_proj_point_dbl_5(&t[18], &t[ 9], tmp);
        sp_256_proj_point_add_sub_5(&t[19], &t[17], &t[18], &t[ 1], tmp);
        sp_256_proj_point_dbl_5(&t[20], &t[10], tmp);
        sp_256_proj_point_dbl_5(&t[22], &t[11], tmp);
        sp_256_proj_point_add_sub_5(&t[23], &t[21], &t[22], &t[ 1], tmp);
        sp_256_proj_point_dbl_5(&t[24], &t[12], tmp);
        sp_256_proj_point_dbl_5(&t[26], &t[13], tmp);
        sp_256_proj_point_add_sub_5(&t[27], &t[25], &t[26], &t[ 1], tmp);
        sp_256_proj_point_dbl_5(&t[28], &t[14], tmp);
        sp_256_proj_point_dbl_5(&t[30], &t[15], tmp);
        sp_256_proj_point_add_sub_5(&t[31], &t[29], &t[30], &t[ 1], tmp);

        negy = t[0].y;

        sp_256_ecc_recode_6_5(k, v);

        i = 42;
    #ifndef WC_NO_CACHE_RESISTANT
        if (ct) {
            sp_256_get_point_33_5(rt, t, v[i].i);
            rt->infinity = !v[i].i;
        }
        else
    #endif
        {
            XMEMCPY(rt, &t[v[i].i], sizeof(sp_point_256));
        }
        for (--i; i>=0; i--) {
            sp_256_proj_point_dbl_n_5(rt, 6, tmp);

        #ifndef WC_NO_CACHE_RESISTANT
            if (ct) {
                sp_256_get_point_33_5(p, t, v[i].i);
                p->infinity = !v[i].i;
            }
            else
        #endif
            {
                XMEMCPY(p, &t[v[i].i], sizeof(sp_point_256));
            }
            sp_256_sub_5(negy, p256_mod, p->y);
            sp_256_cond_copy_5(p->y, negy, (sp_digit)0 - v[i].neg);
            sp_256_proj_point_add_5(rt, rt, p, tmp);
        }

        if (map != 0) {
            sp_256_map_5(r, rt, tmp);
        }
        else {
            XMEMCPY(r, rt, sizeof(sp_point_256));
        }
    }

#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (t != NULL)
        XFREE(t, heap, DYNAMIC_TYPE_ECC);
    if (tmp != NULL)
        XFREE(tmp, heap, DYNAMIC_TYPE_ECC);
#endif
    sp_256_point_free_5(p, 0, heap);
    sp_256_point_free_5(rt, 0, heap);

    return err;
}

#ifdef FP_ECC
#endif /* FP_ECC */
/* Add two Montgomery form projective points. The second point has a q value of
 * one.
 * Only the first point can be the same pointer as the result point.
 *
 * r  Result of addition.
 * p  First point to add.
 * q  Second point to add.
 * t  Temporary ordinate data.
 */
static void sp_256_proj_point_add_qz1_5(sp_point_256* r, const sp_point_256* p,
        const sp_point_256* q, sp_digit* t)
{
    const sp_point_256* ap[2];
    sp_point_256* rp[2];
    sp_digit* t1 = t;
    sp_digit* t2 = t + 2*5;
    sp_digit* t3 = t + 4*5;
    sp_digit* t4 = t + 6*5;
    sp_digit* t5 = t + 8*5;
    sp_digit* x;
    sp_digit* y;
    sp_digit* z;
    int i;

    /* Check double */
    (void)sp_256_sub_5(t1, p256_mod, q->y);
    sp_256_norm_5(t1);
    if ((sp_256_cmp_equal_5(p->x, q->x) & sp_256_cmp_equal_5(p->z, q->z) &
        (sp_256_cmp_equal_5(p->y, q->y) | sp_256_cmp_equal_5(p->y, t1))) != 0) {
        sp_256_proj_point_dbl_5(r, p, t);
    }
    else {
        rp[0] = r;

        /*lint allow cast to different type of pointer*/
        rp[1] = (sp_point_256*)t; /*lint !e9087 !e740*/
        XMEMSET(rp[1], 0, sizeof(sp_point_256));
        x = rp[p->infinity | q->infinity]->x;
        y = rp[p->infinity | q->infinity]->y;
        z = rp[p->infinity | q->infinity]->z;

        ap[0] = p;
        ap[1] = q;
        for (i=0; i<5; i++) {
            r->x[i] = ap[p->infinity]->x[i];
        }
        for (i=0; i<5; i++) {
            r->y[i] = ap[p->infinity]->y[i];
        }
        for (i=0; i<5; i++) {
            r->z[i] = ap[p->infinity]->z[i];
        }
        r->infinity = ap[p->infinity]->infinity;

        /* U2 = X2*Z1^2 */
        sp_256_mont_sqr_5(t2, z, p256_mod, p256_mp_mod);
        sp_256_mont_mul_5(t4, t2, z, p256_mod, p256_mp_mod);
        sp_256_mont_mul_5(t2, t2, q->x, p256_mod, p256_mp_mod);
        /* S2 = Y2*Z1^3 */
        sp_256_mont_mul_5(t4, t4, q->y, p256_mod, p256_mp_mod);
        /* H = U2 - X1 */
        sp_256_mont_sub_5(t2, t2, x, p256_mod);
        /* R = S2 - Y1 */
        sp_256_mont_sub_5(t4, t4, y, p256_mod);
        /* Z3 = H*Z1 */
        sp_256_mont_mul_5(z, z, t2, p256_mod, p256_mp_mod);
        /* X3 = R^2 - H^3 - 2*X1*H^2 */
        sp_256_mont_sqr_5(t1, t4, p256_mod, p256_mp_mod);
        sp_256_mont_sqr_5(t5, t2, p256_mod, p256_mp_mod);
        sp_256_mont_mul_5(t3, x, t5, p256_mod, p256_mp_mod);
        sp_256_mont_mul_5(t5, t5, t2, p256_mod, p256_mp_mod);
        sp_256_mont_sub_5(x, t1, t5, p256_mod);
        sp_256_mont_dbl_5(t1, t3, p256_mod);
        sp_256_mont_sub_5(x, x, t1, p256_mod);
        /* Y3 = R*(X1*H^2 - X3) - Y1*H^3 */
        sp_256_mont_sub_5(t3, t3, x, p256_mod);
        sp_256_mont_mul_5(t3, t3, t4, p256_mod, p256_mp_mod);
        sp_256_mont_mul_5(t5, t5, y, p256_mod, p256_mp_mod);
        sp_256_mont_sub_5(y, t3, t5, p256_mod);
    }
}

#ifdef FP_ECC
/* Convert the projective point to affine.
 * Ordinates are in Montgomery form.
 *
 * a  Point to convert.
 * t  Temporary data.
 */
static void sp_256_proj_to_affine_5(sp_point_256* a, sp_digit* t)
{
    sp_digit* t1 = t;
    sp_digit* t2 = t + 2 * 5;
    sp_digit* tmp = t + 4 * 5;

    sp_256_mont_inv_5(t1, a->z, tmp);

    sp_256_mont_sqr_5(t2, t1, p256_mod, p256_mp_mod);
    sp_256_mont_mul_5(t1, t2, t1, p256_mod, p256_mp_mod);

    sp_256_mont_mul_5(a->x, a->x, t2, p256_mod, p256_mp_mod);
    sp_256_mont_mul_5(a->y, a->y, t1, p256_mod, p256_mp_mod);
    XMEMCPY(a->z, p256_norm_mod, sizeof(p256_norm_mod));
}

/* Generate the pre-computed table of points for the base point.
 *
 * a      The base point.
 * table  Place to store generated point data.
 * tmp    Temporary data.
 * heap  Heap to use for allocation.
 */
static int sp_256_gen_stripe_table_5(const sp_point_256* a,
        sp_table_entry_256* table, sp_digit* tmp, void* heap)
{
#if (!defined(WOLFSSL_SP_SMALL) && !defined(WOLFSSL_SMALL_STACK)) || defined(WOLFSSL_SP_NO_MALLOC)
    sp_point_256 td, s1d, s2d;
#endif
    sp_point_256* t;
    sp_point_256* s1 = NULL;
    sp_point_256* s2 = NULL;
    int i, j;
    int err;

    (void)heap;

    err = sp_256_point_new_5(heap, td, t);
    if (err == MP_OKAY) {
        err = sp_256_point_new_5(heap, s1d, s1);
    }
    if (err == MP_OKAY) {
        err = sp_256_point_new_5(heap, s2d, s2);
    }

    if (err == MP_OKAY) {
        err = sp_256_mod_mul_norm_5(t->x, a->x, p256_mod);
    }
    if (err == MP_OKAY) {
        err = sp_256_mod_mul_norm_5(t->y, a->y, p256_mod);
    }
    if (err == MP_OKAY) {
        err = sp_256_mod_mul_norm_5(t->z, a->z, p256_mod);
    }
    if (err == MP_OKAY) {
        t->infinity = 0;
        sp_256_proj_to_affine_5(t, tmp);

        XMEMCPY(s1->z, p256_norm_mod, sizeof(p256_norm_mod));
        s1->infinity = 0;
        XMEMCPY(s2->z, p256_norm_mod, sizeof(p256_norm_mod));
        s2->infinity = 0;

        /* table[0] = {0, 0, infinity} */
        XMEMSET(&table[0], 0, sizeof(sp_table_entry_256));
        /* table[1] = Affine version of 'a' in Montgomery form */
        XMEMCPY(table[1].x, t->x, sizeof(table->x));
        XMEMCPY(table[1].y, t->y, sizeof(table->y));

        for (i=1; i<8; i++) {
            sp_256_proj_point_dbl_n_5(t, 32, tmp);
            sp_256_proj_to_affine_5(t, tmp);
            XMEMCPY(table[1<<i].x, t->x, sizeof(table->x));
            XMEMCPY(table[1<<i].y, t->y, sizeof(table->y));
        }

        for (i=1; i<8; i++) {
            XMEMCPY(s1->x, table[1<<i].x, sizeof(table->x));
            XMEMCPY(s1->y, table[1<<i].y, sizeof(table->y));
            for (j=(1<<i)+1; j<(1<<(i+1)); j++) {
                XMEMCPY(s2->x, table[j-(1<<i)].x, sizeof(table->x));
                XMEMCPY(s2->y, table[j-(1<<i)].y, sizeof(table->y));
                sp_256_proj_point_add_qz1_5(t, s1, s2, tmp);
                sp_256_proj_to_affine_5(t, tmp);
                XMEMCPY(table[j].x, t->x, sizeof(table->x));
                XMEMCPY(table[j].y, t->y, sizeof(table->y));
            }
        }
    }

    sp_256_point_free_5(s2, 0, heap);
    sp_256_point_free_5(s1, 0, heap);
    sp_256_point_free_5( t, 0, heap);

    return err;
}

#endif /* FP_ECC */
#ifndef WC_NO_CACHE_RESISTANT
/* Touch each possible entry that could be being copied.
 *
 * r      Point to copy into.
 * table  Table - start of the entires to access
 * idx    Index of entry to retrieve.
 */
static void sp_256_get_entry_256_5(sp_point_256* r,
    const sp_table_entry_256* table, int idx)
{
    int i;
    sp_digit mask;

    r->x[0] = 0;
    r->x[1] = 0;
    r->x[2] = 0;
    r->x[3] = 0;
    r->x[4] = 0;
    r->y[0] = 0;
    r->y[1] = 0;
    r->y[2] = 0;
    r->y[3] = 0;
    r->y[4] = 0;
    for (i = 1; i < 256; i++) {
        mask = 0 - (i == idx);
        r->x[0] |= mask & table[i].x[0];
        r->x[1] |= mask & table[i].x[1];
        r->x[2] |= mask & table[i].x[2];
        r->x[3] |= mask & table[i].x[3];
        r->x[4] |= mask & table[i].x[4];
        r->y[0] |= mask & table[i].y[0];
        r->y[1] |= mask & table[i].y[1];
        r->y[2] |= mask & table[i].y[2];
        r->y[3] |= mask & table[i].y[3];
        r->y[4] |= mask & table[i].y[4];
    }
}
#endif /* !WC_NO_CACHE_RESISTANT */
/* Multiply the point by the scalar and return the result.
 * If map is true then convert result to affine coordinates.
 *
 * Implementation uses striping of bits.
 * Choose bits 8 bits apart.
 *
 * r      Resulting point.
 * k      Scalar to multiply by.
 * table  Pre-computed table.
 * map    Indicates whether to convert result to affine.
 * ct     Constant time required.
 * heap   Heap to use for allocation.
 * returns MEMORY_E when memory allocation fails and MP_OKAY on success.
 */
static int sp_256_ecc_mulmod_stripe_5(sp_point_256* r, const sp_point_256* g,
        const sp_table_entry_256* table, const sp_digit* k, int map,
        int ct, void* heap)
{
#if (!defined(WOLFSSL_SP_SMALL) && !defined(WOLFSSL_SMALL_STACK)) || defined(WOLFSSL_SP_NO_MALLOC)
    sp_point_256 rtd;
    sp_point_256 pd;
    sp_digit td[2 * 5 * 5];
#endif
    sp_point_256* rt;
    sp_point_256* p = NULL;
    sp_digit* t;
    int i, j;
    int y, x;
    int err;

    (void)g;
    /* Constant time used for cache attack resistance implementation. */
    (void)ct;
    (void)heap;


    err = sp_256_point_new_5(heap, rtd, rt);
    if (err == MP_OKAY) {
        err = sp_256_point_new_5(heap, pd, p);
    }
#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    t = (sp_digit*)XMALLOC(sizeof(sp_digit) * 2 * 5 * 5, heap,
                           DYNAMIC_TYPE_ECC);
    if (t == NULL) {
        err = MEMORY_E;
    }
#else
    t = td;
#endif

    if (err == MP_OKAY) {
        XMEMCPY(p->z, p256_norm_mod, sizeof(p256_norm_mod));
        XMEMCPY(rt->z, p256_norm_mod, sizeof(p256_norm_mod));

        y = 0;
        for (j=0,x=31; j<8; j++,x+=32) {
            y |= ((k[x / 52] >> (x % 52)) & 1) << j;
        }
    #ifndef WC_NO_CACHE_RESISTANT
        if (ct) {
            sp_256_get_entry_256_5(rt, table, y);
        } else
    #endif
        {
            XMEMCPY(rt->x, table[y].x, sizeof(table[y].x));
            XMEMCPY(rt->y, table[y].y, sizeof(table[y].y));
        }
        rt->infinity = !y;
        for (i=30; i>=0; i--) {
            y = 0;
            for (j=0,x=i; j<8; j++,x+=32) {
                y |= ((k[x / 52] >> (x % 52)) & 1) << j;
            }

            sp_256_proj_point_dbl_5(rt, rt, t);
        #ifndef WC_NO_CACHE_RESISTANT
            if (ct) {
                sp_256_get_entry_256_5(p, table, y);
            }
            else
        #endif
            {
                XMEMCPY(p->x, table[y].x, sizeof(table[y].x));
                XMEMCPY(p->y, table[y].y, sizeof(table[y].y));
            }
            p->infinity = !y;
            sp_256_proj_point_add_qz1_5(rt, rt, p, t);
        }

        if (map != 0) {
            sp_256_map_5(r, rt, t);
        }
        else {
            XMEMCPY(r, rt, sizeof(sp_point_256));
        }
    }

#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (t != NULL) {
        XFREE(t, heap, DYNAMIC_TYPE_ECC);
    }
#endif
    sp_256_point_free_5(p, 0, heap);
    sp_256_point_free_5(rt, 0, heap);

    return err;
}

#ifdef FP_ECC
#ifndef FP_ENTRIES
    #define FP_ENTRIES 16
#endif

typedef struct sp_cache_256_t {
    sp_digit x[5];
    sp_digit y[5];
    sp_table_entry_256 table[256];
    uint32_t cnt;
    int set;
} sp_cache_256_t;

static THREAD_LS_T sp_cache_256_t sp_cache_256[FP_ENTRIES];
static THREAD_LS_T int sp_cache_256_last = -1;
static THREAD_LS_T int sp_cache_256_inited = 0;

#ifndef HAVE_THREAD_LS
    static volatile int initCacheMutex_256 = 0;
    static wolfSSL_Mutex sp_cache_256_lock;
#endif

static void sp_ecc_get_cache_256(const sp_point_256* g, sp_cache_256_t** cache)
{
    int i, j;
    uint32_t least;

    if (sp_cache_256_inited == 0) {
        for (i=0; i<FP_ENTRIES; i++) {
            sp_cache_256[i].set = 0;
        }
        sp_cache_256_inited = 1;
    }

    /* Compare point with those in cache. */
    for (i=0; i<FP_ENTRIES; i++) {
        if (!sp_cache_256[i].set)
            continue;

        if (sp_256_cmp_equal_5(g->x, sp_cache_256[i].x) &
                           sp_256_cmp_equal_5(g->y, sp_cache_256[i].y)) {
            sp_cache_256[i].cnt++;
            break;
        }
    }

    /* No match. */
    if (i == FP_ENTRIES) {
        /* Find empty entry. */
        i = (sp_cache_256_last + 1) % FP_ENTRIES;
        for (; i != sp_cache_256_last; i=(i+1)%FP_ENTRIES) {
            if (!sp_cache_256[i].set) {
                break;
            }
        }

        /* Evict least used. */
        if (i == sp_cache_256_last) {
            least = sp_cache_256[0].cnt;
            for (j=1; j<FP_ENTRIES; j++) {
                if (sp_cache_256[j].cnt < least) {
                    i = j;
                    least = sp_cache_256[i].cnt;
                }
            }
        }

        XMEMCPY(sp_cache_256[i].x, g->x, sizeof(sp_cache_256[i].x));
        XMEMCPY(sp_cache_256[i].y, g->y, sizeof(sp_cache_256[i].y));
        sp_cache_256[i].set = 1;
        sp_cache_256[i].cnt = 1;
    }

    *cache = &sp_cache_256[i];
    sp_cache_256_last = i;
}
#endif /* FP_ECC */

/* Multiply the base point of P256 by the scalar and return the result.
 * If map is true then convert result to affine coordinates.
 *
 * r     Resulting point.
 * g     Point to multiply.
 * k     Scalar to multiply by.
 * map   Indicates whether to convert result to affine.
 * ct    Constant time required.
 * heap  Heap to use for allocation.
 * returns MEMORY_E when memory allocation fails and MP_OKAY on success.
 */
static int sp_256_ecc_mulmod_5(sp_point_256* r, const sp_point_256* g, const sp_digit* k,
        int map, int ct, void* heap)
{
#ifndef FP_ECC
    return sp_256_ecc_mulmod_win_add_sub_5(r, g, k, map, ct, heap);
#else
    sp_digit tmp[2 * 5 * 5];
    sp_cache_256_t* cache;
    int err = MP_OKAY;

#ifndef HAVE_THREAD_LS
    if (initCacheMutex_256 == 0) {
         wc_InitMutex(&sp_cache_256_lock);
         initCacheMutex_256 = 1;
    }
    if (wc_LockMutex(&sp_cache_256_lock) != 0)
       err = BAD_MUTEX_E;
#endif /* HAVE_THREAD_LS */

    if (err == MP_OKAY) {
        sp_ecc_get_cache_256(g, &cache);
        if (cache->cnt == 2)
            sp_256_gen_stripe_table_5(g, cache->table, tmp, heap);

#ifndef HAVE_THREAD_LS
        wc_UnLockMutex(&sp_cache_256_lock);
#endif /* HAVE_THREAD_LS */

        if (cache->cnt < 2) {
            err = sp_256_ecc_mulmod_win_add_sub_5(r, g, k, map, ct, heap);
        }
        else {
            err = sp_256_ecc_mulmod_stripe_5(r, g, cache->table, k,
                    map, ct, heap);
        }
    }

    return err;
#endif
}

#endif
/* Multiply the point by the scalar and return the result.
 * If map is true then convert result to affine coordinates.
 *
 * km    Scalar to multiply by.
 * p     Point to multiply.
 * r     Resulting point.
 * map   Indicates whether to convert result to affine.
 * heap  Heap to use for allocation.
 * returns MEMORY_E when memory allocation fails and MP_OKAY on success.
 */
int sp_ecc_mulmod_256(mp_int* km, ecc_point* gm, ecc_point* r, int map,
        void* heap)
{
#if (!defined(WOLFSSL_SP_SMALL) && !defined(WOLFSSL_SMALL_STACK)) || defined(WOLFSSL_SP_NO_MALLOC)
    sp_point_256 p;
    sp_digit kd[5];
#endif
    sp_point_256* point;
    sp_digit* k = NULL;
    int err = MP_OKAY;

    err = sp_256_point_new_5(heap, p, point);
#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (err == MP_OKAY) {
        k = (sp_digit*)XMALLOC(sizeof(sp_digit) * 5, heap,
                                                              DYNAMIC_TYPE_ECC);
        if (k == NULL)
            err = MEMORY_E;
    }
#else
    k = kd;
#endif
    if (err == MP_OKAY) {
        sp_256_from_mp(k, 5, km);
        sp_256_point_from_ecc_point_5(point, gm);

            err = sp_256_ecc_mulmod_5(point, point, k, map, 1, heap);
    }
    if (err == MP_OKAY) {
        err = sp_256_point_to_ecc_point_5(point, r);
    }

#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (k != NULL) {
        XFREE(k, heap, DYNAMIC_TYPE_ECC);
    }
#endif
    sp_256_point_free_5(point, 0, heap);

    return err;
}

#ifdef WOLFSSL_SP_SMALL
/* Multiply the base point of P256 by the scalar and return the result.
 * If map is true then convert result to affine coordinates.
 *
 * r     Resulting point.
 * k     Scalar to multiply by.
 * map   Indicates whether to convert result to affine.
 * heap  Heap to use for allocation.
 * returns MEMORY_E when memory allocation fails and MP_OKAY on success.
 */
static int sp_256_ecc_mulmod_base_5(sp_point_256* r, const sp_digit* k,
        int map, int ct, void* heap)
{
    /* No pre-computed values. */
    return sp_256_ecc_mulmod_5(r, &p256_base, k, map, ct, heap);
}

#else
static const sp_table_entry_256 p256_table[256] = {
    /* 0 */
    { { 0x00, 0x00, 0x00, 0x00, 0x00 },
      { 0x00, 0x00, 0x00, 0x00, 0x00 } },
    /* 1 */
    { { 0x730d418a9143cL,0xfc5fedb60179eL,0x762251075ba95L,0x55c679fb732b7L,
        0x018905f76a537L },
      { 0x25357ce95560aL,0xe4ba19e45cddfL,0xd21f3258b4ab8L,0x5d85d2e88688dL,
        0x08571ff182588L } },
    /* 2 */
    { { 0x886024147519aL,0xac26b372f0202L,0x785ebc8d0981eL,0x58e9a9d4a7caaL,
        0x0d953c50ddbdfL },
      { 0x361ccfd590f8fL,0x6b44e6c9179d6L,0x2eb64cf72e962L,0x88f37fd961102L,
        0x0863ebb7e9eb2L } },
    /* 3 */
    { { 0x6b6235cdb6485L,0xa22f0a2f97785L,0xf7e300b808f0eL,0x80a03e68d9544L,
        0x000076055b5ffL },
      { 0x4eb9b838d2010L,0xbb3243708a763L,0x42a660654014fL,0x3ee0e0e47d398L,
        0x0830877613437L } },
    /* 4 */
    { { 0x22fc516a0d2bbL,0x6c1a6234994f9L,0x7c62c8b0d5cc1L,0x667f9241cf3a5L,
        0x02f5e6961fd1bL },
      { 0x5c70bf5a01797L,0x4d609561925c1L,0x71fdb523d20b4L,0x0f7b04911b370L,
        0x0f648f9168d6fL } },
    /* 5 */
    { { 0x66847e137bbbcL,0x9e8a6a0bec9e5L,0x9d73463e43446L,0x0015b1c427617L,
        0x05abe0285133dL },
      { 0xa837cc04c7dabL,0x4c43260c0792aL,0x8e6cc37573d9fL,0x73830c9315627L,
        0x094bb725b6b6fL } },
    /* 6 */
    { { 0x9b48f720f141cL,0xcd2df5bc74bbfL,0x11045c46199b3L,0xc4efdc3f61294L,
        0x0cdd6bbcb2f7dL },
      { 0x6700beaf436fdL,0x6db99326beccaL,0x14f25226f647fL,0xe5f60c0fa7920L,
        0x0a361bebd4bdaL } },
    /* 7 */
    { { 0xa2558597c13c7L,0x5f50b7c3e128aL,0x3c09d1dc38d63L,0x292c07039aecfL,
        0x0ba12ca09c4b5L },
      { 0x08fa459f91dfdL,0x66ceea07fb9e4L,0xd780b293af43bL,0xef4b1eceb0899L,
        0x053ebb99d701fL } },
    /* 8 */
    { { 0x7ee31b0e63d34L,0x72a9e54fab4feL,0x5e7b5a4f46005L,0x4831c0493334dL,
        0x08589fb9206d5L },
      { 0x0f5cc6583553aL,0x4ae25649e5aa7L,0x0044652087909L,0x1c4fcc9045071L,
        0x0ebb0696d0254L } },
    /* 9 */
    { { 0x6ca15ac1647c5L,0x47c4cf5799461L,0x64dfbacb8127dL,0x7da3dc666aa37L,
        0x0eb2820cbd1b2L },
      { 0x6f8d86a87e008L,0x9d922378f3940L,0x0ccecb2d87dfaL,0xda1d56ed2e428L,
        0x01f28289b55a7L } },
    /* 10 */
    { { 0xaa0c03b89da99L,0x9eb8284022abbL,0x81c05e8a6f2d7L,0x4d6327847862bL,
        0x0337a4b5905e5L },
      { 0x7500d21f7794aL,0xb77d6d7f613c6L,0x4cfd6e8207005L,0xfbd60a5a37810L,
        0x00d65e0d5f4c2L } },
    /* 11 */
    { { 0x09bbeb5275d38L,0x450be0a358d9dL,0x73eb2654268a7L,0xa232f0762ff49L,
        0x0c23da24252f4L },
      { 0x1b84f0b94520cL,0x63b05bd78e5daL,0x4d29ea1096667L,0xcff13a4dcb869L,
        0x019de3b8cc790L } },
    /* 12 */
    { { 0xa716c26c5fe04L,0x0b3bba1bdb183L,0x4cb712c3b28deL,0xcbfd7432c586aL,
        0x0e34dcbd491fcL },
      { 0x8d46baaa58403L,0x8682e97a53b40L,0x6aaa8af9a6974L,0x0f7f9e3901273L,
        0x0e7641f447b4eL } },
    /* 13 */
    { { 0x53941df64ba59L,0xec0b0242fc7d7L,0x1581859d33f10L,0x57bf4f06dfc6aL,
        0x04a12df57052aL },
      { 0x6338f9439dbd0L,0xd4bde53e1fbfaL,0x1f1b314d3c24bL,0xea46fd5e4ffa2L,
        0x06af5aa93bb5bL } },
    /* 14 */
    { { 0x0b69910c91999L,0x402a580491da1L,0x8cc20900a24b4L,0x40133e0094b4bL,
        0x05fe3475a66a4L },
      { 0x8cabdf93e7b4bL,0x1a7c23f91ab0fL,0xd1e6263292b50L,0xa91642e889aecL,
        0x0b544e308ecfeL } },
    /* 15 */
    { { 0x8c6e916ddfdceL,0x66f89179e6647L,0xd4e67e12c3291L,0xc20b4e8d6e764L,
        0x0e0b6b2bda6b0L },
      { 0x12df2bb7efb57L,0xde790c40070d3L,0x79bc9441aac0dL,0x3774f90336ad6L,
        0x071c023de25a6L } },
    /* 16 */
    { { 0x8c244bfe20925L,0xc38fdce86762aL,0xd38706391c19aL,0x24f65a96a5d5dL,
        0x061d587d421d3L },
      { 0x673a2a37173eaL,0x0853778b65e87L,0x5bab43e238480L,0xefbe10f8441e0L,
        0x0fa11fe124621L } },
    /* 17 */
    { { 0x91f2b2cb19ffdL,0x5bb1923c231c8L,0xac5ca8e01ba8dL,0xbedcb6d03d678L,
        0x0586eb04c1f13L },
      { 0x5c6e527e8ed09L,0x3c1819ede20c3L,0x6c652fa1e81a3L,0x4f11278fd6c05L,
        0x019d5ac087086L } },
    /* 18 */
    { { 0x9f581309a4e1fL,0x1be92700741e9L,0xfd28d20ab7de7L,0x563f26a5ef0beL,
        0x0e7c0073f7f9cL },
      { 0xd663a0ef59f76L,0x5420fcb0501f6L,0xa6602d4669b3bL,0x3c0ac08c1f7a7L,
        0x0e08504fec65bL } },
    /* 19 */
    { { 0x8f68da031b3caL,0x9ee6da6d66f09L,0x4f246e86d1cabL,0x96b45bfd81fa9L,
        0x078f018825b09L },
      { 0xefde43a25787fL,0x0d1dccac9bb7eL,0x35bfc368016f8L,0x747a0cea4877bL,
        0x043a773b87e94L } },
    /* 20 */
    { { 0x77734d2b533d5L,0xf6a1bdddc0625L,0x79ec293673b8aL,0x66b1577e7c9aaL,
        0x0bb6de651c3b2L },
      { 0x9303ab65259b3L,0xd3d03a7480e7eL,0xb3cfc27d6a0afL,0xb99bc5ac83d19L,
        0x060b4619a5d18L } },
    /* 21 */
    { { 0xa38e11ae5aa1cL,0x2b49e73658bd6L,0xe5f87edb8b765L,0xffcd0b130014eL,
        0x09d0f27b2aeebL },
      { 0x246317a730a55L,0x2fddbbc83aca9L,0xc019a719c955bL,0xc48d07c1dfe0aL,
        0x0244a566d356eL } },
    /* 22 */
    { { 0x0394aeacf1f96L,0xa9024c271c6dbL,0x2cbd3b99f2122L,0xef692626ac1b8L,
        0x045e58c873581L },
      { 0xf479da38f9dbcL,0x46e888a040d3fL,0x6e0bed7a8aaf1L,0xb7a4945adfb24L,
        0x0c040e21cc1e4L } },
    /* 23 */
    { { 0xaf0006f8117b6L,0xff73a35433847L,0xd9475eb651969L,0x6ec7482b35761L,
        0x01cdf5c97682cL },
      { 0x775b411f04839L,0xf448de16987dbL,0x70b32197dbeacL,0xff3db2921dd1bL,
        0x0046755f8a92dL } },
    /* 24 */
    { { 0xac5d2bce8ffcdL,0x8b2fe61a82cc8L,0x202d6c70d53c4L,0xa5f3f6f161727L,
        0x0046e5e113b83L },
      { 0x8ff64d8007f01L,0x125af43183e7bL,0x5e1a03c7fb1efL,0x005b045c5ea63L,
        0x06e0106c3303dL } },
    /* 25 */
    { { 0x7358488dd73b1L,0x8f995ed0d948cL,0x56a2ab7767070L,0xcf1f38385ea8cL,
        0x0442594ede901L },
      { 0xaa2c912d4b65bL,0x3b96c90c37f8fL,0xe978d1f94c234L,0xe68ed326e4a15L,
        0x0a796fa514c2eL } },
    /* 26 */
    { { 0xfb604823addd7L,0x83e56693b3359L,0xcbf3c809e2a61L,0x66e9f885b78e3L,
        0x0e4ad2da9c697L },
      { 0xf7f428e048a61L,0x8cc092d9a0357L,0x03ed8ef082d19L,0x5143fc3a1af4cL,
        0x0c5e94046c37bL } },
    /* 27 */
    { { 0xa538c2be75f9eL,0xe8cb123a78476L,0x109c04b6fd1a9L,0x4747d85e4df0bL,
        0x063283dafdb46L },
      { 0x28cf7baf2df15L,0x550ad9a7f4ce7L,0x834bcc3e592c4L,0xa938fab226adeL,
        0x068bd19ab1981L } },
    /* 28 */
    { { 0xead511887d659L,0xf4b359305ac08L,0xfe74fe33374d5L,0xdfd696986981cL,
        0x0495292f53c6fL },
      { 0x78c9e1acec896L,0x10ec5b44844a8L,0x64d60a7d964b2L,0x68376696f7e26L,
        0x00ec7530d2603L } },
    /* 29 */
    { { 0x13a05ad2687bbL,0x6af32e21fa2daL,0xdd4607ba1f83bL,0x3f0b390f5ef51L,
        0x00f6207a66486L },
      { 0x7e3bb0f138233L,0x6c272aa718bd6L,0x6ec88aedd66b9L,0x6dcf8ed004072L,
        0x0ff0db07208edL } },
    /* 30 */
    { { 0xfa1014c95d553L,0xfd5d680a8a749L,0xf3b566fa44052L,0x0ea3183b4317fL,
        0x0313b513c8874L },
      { 0x2e2ac08d11549L,0x0bb4dee21cb40L,0x7f2320e071ee1L,0x9f8126b987dd4L,
        0x02d3abcf986f1L } },
    /* 31 */
    { { 0x88501815581a2L,0x56632211af4c2L,0xcab2e999a0a6dL,0x8cdf19ba7a0f0L,
        0x0c036fa10ded9L },
      { 0xe08bac1fbd009L,0x9006d1581629aL,0xb9e0d8f0b68b1L,0x0194c2eb32779L,
        0x0a6b2a2c4b6d4L } },
    /* 32 */
    { { 0x3e50f6d3549cfL,0x6ffacd665ed43L,0xe11fcb46f3369L,0x9860695bfdaccL,
        0x0810ee252af7cL },
      { 0x50fe17159bb2cL,0xbe758b357b654L,0x69fea72f7dfbeL,0x17452b057e74dL,
        0x0d485717a9273L } },
    /* 33 */
    { { 0x41a8af0cb5a98L,0x931f3110bf117L,0xb382adfd3da8fL,0x604e1994e2cbaL,
        0x06a6045a72f9aL },
      { 0xc0d3fa2b2411dL,0x3e510e96e0170L,0x865b3ccbe0eb8L,0x57903bcc9f738L,
        0x0d3e45cfaf9e1L } },
    /* 34 */
    { { 0xf69bbe83f7669L,0x8272877d6bce1L,0x244278d09f8aeL,0xc19c9548ae543L,
        0x0207755dee3c2L },
      { 0xd61d96fef1945L,0xefb12d28c387bL,0x2df64aa18813cL,0xb00d9fbcd1d67L,
        0x048dc5ee57154L } },
    /* 35 */
    { { 0x790bff7e5a199L,0xcf989ccbb7123L,0xa519c79e0efb8L,0xf445c27a2bfe0L,
        0x0f2fb0aeddff6L },
      { 0x09575f0b5025fL,0xd740fa9f2241cL,0x80bfbd0550543L,0xd5258fa3c8ad3L,
        0x0a13e9015db28L } },
    /* 36 */
    { { 0x7a350a2b65cbcL,0x722a464226f9fL,0x23f07a10b04b9L,0x526f265ce241eL,
        0x02bf0d6b01497L },
      { 0x4dd3f4b216fb7L,0x67fbdda26ad3dL,0x708505cf7d7b8L,0xe89faeb7b83f6L,
        0x042a94a5a162fL } },
    /* 37 */
    { { 0x6ad0beaadf191L,0x9025a268d7584L,0x94dc1f60f8a48L,0xde3de86030504L,
        0x02c2dd969c65eL },
      { 0x2171d93849c17L,0xba1da250dd6d0L,0xc3a5485460488L,0x6dbc4810c7063L,
        0x0f437fa1f42c5L } },
    /* 38 */
    { { 0x0d7144a0f7dabL,0x931776e9ac6aaL,0x5f397860f0497L,0x7aa852c0a050fL,
        0x0aaf45b335470L },
      { 0x37c33c18d364aL,0x063e49716585eL,0x5ec5444d40b9bL,0x72bcf41716811L,
        0x0cdf6310df4f2L } },
    /* 39 */
    { { 0x3c6238ea8b7efL,0x1885bc2287747L,0xbda8e3408e935L,0x2ff2419567722L,
        0x0f0d008bada9eL },
      { 0x2671d2414d3b1L,0x85b019ea76291L,0x53bcbdbb37549L,0x7b8b5c61b96d4L,
        0x05bd5c2f5ca88L } },
    /* 40 */
    { { 0xf469ef49a3154L,0x956e2b2e9aef0L,0xa924a9c3e85a5L,0x471945aaec1eaL,
        0x0aa12dfc8a09eL },
      { 0x272274df69f1dL,0x2ca2ff5e7326fL,0x7a9dd44e0e4c8L,0xa901b9d8ce73bL,
        0x06c036e73e48cL } },
    /* 41 */
    { { 0xae12a0f6e3138L,0x0025ad345a5cfL,0x5672bc56966efL,0xbe248993c64b4L,
        0x0292ff65896afL },
      { 0x50d445e213402L,0x274392c9fed52L,0xa1c72e8f6580eL,0x7276097b397fdL,
        0x0644e0c90311bL } },
    /* 42 */
    { { 0x421e1a47153f0L,0x79920418c9e1eL,0x05d7672b86c3bL,0x9a7793bdce877L,
        0x0f25ae793cab7L },
      { 0x194a36d869d0cL,0x824986c2641f3L,0x96e945e9d55c8L,0x0a3e49fb5ea30L,
        0x039b8e65313dbL } },
    /* 43 */
    { { 0x54200b6fd2e59L,0x669255c98f377L,0xe2a573935e2c0L,0xdb06d9dab21a0L,
        0x039122f2f0f19L },
      { 0xce1e003cad53cL,0x0fe65c17e3cfbL,0xaa13877225b2cL,0xff8d72baf1d29L,
        0x08de80af8ce80L } },
    /* 44 */
    { { 0xea8d9207bbb76L,0x7c21782758afbL,0xc0436b1921c7eL,0x8c04dfa2b74b1L,
        0x0871949062e36L },
      { 0x928bba3993df5L,0xb5f3b3d26ab5fL,0x5b55050639d75L,0xfde1011aa78a8L,
        0x0fc315e6a5b74L } },
    /* 45 */
    { { 0xfd41ae8d6ecfaL,0xf61aec7f86561L,0x924741d5f8c44L,0x908898452a7b4L,
        0x0e6d4a7adee38L },
      { 0x52ed14593c75dL,0xa4dd271162605L,0xba2c7db70a70dL,0xae57d2aede937L,
        0x035dfaf9a9be2L } },
    /* 46 */
    { { 0x56fcdaa736636L,0x97ae2cab7e6b9L,0xf34996609f51dL,0x0d2bfb10bf410L,
        0x01da5c7d71c83L },
      { 0x1e4833cce6825L,0x8ff9573c3b5c4L,0x23036b815ad11L,0xb9d6a28552c7fL,
        0x07077c0fddbf4L } },
    /* 47 */
    { { 0x3ff8d46b9661cL,0x6b0d2cfd71bf6L,0x847f8f7a1dfd3L,0xfe440373e140aL,
        0x053a8632ee50eL },
      { 0x6ff68696d8051L,0x95c74f468a097L,0xe4e26bddaec0cL,0xfcc162994dc35L,
        0x0028ca76d34e1L } },
    /* 48 */
    { { 0xd47dcfc9877eeL,0x10801d0002d11L,0x4c260b6c8b362L,0xf046d002c1175L,
        0x004c17cd86962L },
      { 0xbd094b0daddf5L,0x7524ce55c06d9L,0x2da03b5bea235L,0x7474663356e67L,
        0x0f7ba4de9fed9L } },
    /* 49 */
    { { 0xbfa34ebe1263fL,0x3571ae7ce6d0dL,0x2a6f523557637L,0x1c41d24405538L,
        0x0e31f96005213L },
      { 0xb9216ea6b6ec6L,0x2e73c2fc44d1bL,0x9d0a29437a1d1L,0xd47bc10e7eac8L,
        0x0aa3a6259ce34L } },
    /* 50 */
    { { 0xf9df536f3dcd3L,0x50d2bf7360fbcL,0xf504f5b6cededL,0xdaee491710fadL,
        0x02398dd627e79L },
      { 0x705a36d09569eL,0xbb5149f769cf4L,0x5f6034cea0619L,0x6210ff9c03773L,
        0x05717f5b21c04L } },
    /* 51 */
    { { 0x229c921dd895eL,0x0040c284519feL,0xd637ecd8e5185L,0x28defa13d2391L,
        0x0660a2c560e3cL },
      { 0xa88aed67fcbd0L,0x780ea9f0969ccL,0x2e92b4dc84724L,0x245332b2f4817L,
        0x0624ee54c4f52L } },
    /* 52 */
    { { 0x49ce4d897ecccL,0xd93f9880aa095L,0x43a7c204d49d1L,0xfbc0723c24230L,
        0x04f392afb92bdL },
      { 0x9f8fa7de44fd9L,0xe457b32156696L,0x68ebc3cb66cfbL,0x399cdb2fa8033L,
        0x08a3e7977ccdbL } },
    /* 53 */
    { { 0x1881f06c4b125L,0x00f6e3ca8cddeL,0xc7a13e9ae34e3L,0x4404ef6999de5L,
        0x03888d02370c2L },
      { 0x8035644f91081L,0x615f015504762L,0x32cd36e3d9fcfL,0x23361827edc86L,
        0x0a5e62e471810L } },
    /* 54 */
    { { 0x25ee32facd6c8L,0x5454bcbc661a8L,0x8df9931699c63L,0x5adc0ce3edf79L,
        0x02c4768e6466aL },
      { 0x6ff8c90a64bc9L,0x20e4779f5cb34L,0xc05e884630a60L,0x52a0d949d064bL,
        0x07b5e6441f9e6L } },
    /* 55 */
    { { 0x9422c1d28444aL,0xd8be136a39216L,0xb0c7fcee996c5L,0x744a2387afe5fL,
        0x0b8af73cb0c8dL },
      { 0xe83aa338b86fdL,0x58a58a5cff5fdL,0x0ac9433fee3f1L,0x0895c9ee8f6f2L,
        0x0a036395f7f3fL } },
    /* 56 */
    { { 0x3c6bba10f7770L,0x81a12a0e248c7L,0x1bc2b9fa6f16dL,0xb533100df6825L,
        0x04be36b01875fL },
      { 0x6086e9fb56dbbL,0x8b07e7a4f8922L,0x6d52f20306fefL,0x00c0eeaccc056L,
        0x08cbc9a871bdcL } },
    /* 57 */
    { { 0x1895cc0dac4abL,0x40712ff112e13L,0xa1cee57a874a4L,0x35f86332ae7c6L,
        0x044e7553e0c08L },
      { 0x03fff7734002dL,0x8b0b34425c6d5L,0xe8738b59d35cbL,0xfc1895f702760L,
        0x0470a683a5eb8L } },
    /* 58 */
    { { 0x761dc90513482L,0x2a01e9276a81bL,0xce73083028720L,0xc6efcda441ee0L,
        0x016410690c63dL },
      { 0x34a066d06a2edL,0x45189b100bf50L,0xb8218c9dd4d77L,0xbb4fd914ae72aL,
        0x0d73479fd7abcL } },
    /* 59 */
    { { 0xefb165ad4c6e5L,0x8f5b06d04d7edL,0x575cb14262cf0L,0x666b12ed5bb18L,
        0x0816469e30771L },
      { 0xb9d79561e291eL,0x22c1de1661d7aL,0x35e0513eb9dafL,0x3f9cf49827eb1L,
        0x00a36dd23f0ddL } },
    /* 60 */
    { { 0xd32c741d5533cL,0x9e8684628f098L,0x349bd117c5f5aL,0xb11839a228adeL,
        0x0e331dfd6fdbaL },
      { 0x0ab686bcc6ed8L,0xbdef7a260e510L,0xce850d77160c3L,0x33899063d9a7bL,
        0x0d3b4782a492eL } },
    /* 61 */
    { { 0x9b6e8f3821f90L,0xed66eb7aada14L,0xa01311692edd9L,0xa5bd0bb669531L,
        0x07281275a4c86L },
      { 0x858f7d3ff47e5L,0xbc61016441503L,0xdfd9bb15e1616L,0x505962b0f11a7L,
        0x02c062e7ece14L } },
    /* 62 */
    { { 0xf996f0159ac2eL,0x36cbdb2713a76L,0x8e46047281e77L,0x7ef12ad6d2880L,
        0x0282a35f92c4eL },
      { 0x54b1ec0ce5cd2L,0xc91379c2299c3L,0xe82c11ecf99efL,0x2abd992caf383L,
        0x0c71cd513554dL } },
    /* 63 */
    { { 0x5de9c09b578f4L,0x58e3affa7a488L,0x9182f1f1884e2L,0xf3a38f76b1b75L,
        0x0c50f6740cf47L },
      { 0x4adf3374b68eaL,0x2369965fe2a9cL,0x5a53050a406f3L,0x58dc2f86a2228L,
        0x0b9ecb3a72129L } },
    /* 64 */
    { { 0x8410ef4f8b16aL,0xfec47b266a56fL,0xd9c87c197241aL,0xab1b0a406b8e6L,
        0x0803f3e02cd42L },
      { 0x309a804dbec69L,0xf73bbad05f7f0L,0xd8e197fa83b85L,0xadc1c6097273aL,
        0x0c097440e5067L } },
    /* 65 */
    { { 0xa56f2c379ab34L,0x8b841df8d1846L,0x76c68efa8ee06L,0x1f30203144591L,
        0x0f1af32d5915fL },
      { 0x375315d75bd50L,0xbaf72f67bc99cL,0x8d7723f837cffL,0x1c8b0613a4184L,
        0x023d0f130e2d4L } },
    /* 66 */
    { { 0xab6edf41500d9L,0xe5fcbeada8857L,0x97259510d890aL,0xfadd52fe86488L,
        0x0b0288dd6c0a3L },
      { 0x20f30650bcb08L,0x13695d6e16853L,0x989aa7671af63L,0xc8d231f520a7bL,
        0x0ffd3724ff408L } },
    /* 67 */
    { { 0x68e64b458e6cbL,0x20317a5d28539L,0xaa75f56992dadL,0x26df3814ae0b7L,
        0x0f5590f4ad78cL },
      { 0x24bd3cf0ba55aL,0x4a0c778bae0fcL,0x83b674a0fc472L,0x4a201ce9864f6L,
        0x018d6da54f6f7L } },
    /* 68 */
    { { 0x3e225d5be5a2bL,0x835934f3c6ed9L,0x2626ffc6fe799L,0x216a431409262L,
        0x050bbb4d97990L },
      { 0x191c6e57ec63eL,0x40181dcdb2378L,0x236e0f665422cL,0x49c341a8099b0L,
        0x02b10011801feL } },
    /* 69 */
    { { 0x8b5c59b391593L,0xa2598270fcfc6L,0x19adcbbc385f5L,0xae0c7144f3aadL,
        0x0dd55899983fbL },
      { 0x88b8e74b82ff4L,0x4071e734c993bL,0x3c0322ad2e03cL,0x60419a7a9eaf4L,
        0x0e6e4c551149dL } },
    /* 70 */
    { { 0x655bb1e9af288L,0x64f7ada93155fL,0xb2820e5647e1aL,0x56ff43697e4bcL,
        0x051e00db107edL },
      { 0x169b8771c327eL,0x0b4a96c2ad43dL,0xdeb477929cdb2L,0x9177c07d51f53L,
        0x0e22f42414982L } },
    /* 71 */
    { { 0x5e8f4635f1abbL,0xb568538874cd4L,0x5a8034d7edc0cL,0x48c9c9472c1fbL,
        0x0f709373d52dcL },
      { 0x966bba8af30d6L,0x4af137b69c401L,0x361c47e95bf5fL,0x5b113966162a9L,
        0x0bd52d288e727L } },
    /* 72 */
    { { 0x55c7a9c5fa877L,0x727d3a3d48ab1L,0x3d189d817dad6L,0x77a643f43f9e7L,
        0x0a0d0f8e4c8aaL },
      { 0xeafd8cc94f92dL,0xbe0c4ddb3a0bbL,0x82eba14d818c8L,0x6a0022cc65f8bL,
        0x0a56c78c7946dL } },
    /* 73 */
    { { 0x2391b0dd09529L,0xa63daddfcf296L,0xb5bf481803e0eL,0x367a2c77351f5L,
        0x0d8befdf8731aL },
      { 0x19d42fc0157f4L,0xd7fec8e650ab9L,0x2d48b0af51caeL,0x6478cdf9cb400L,
        0x0854a68a5ce9fL } },
    /* 74 */
    { { 0x5f67b63506ea5L,0x89a4fe0d66dc3L,0xe95cd4d9286c4L,0x6a953f101d3bfL,
        0x05cacea0b9884L },
      { 0xdf60c9ceac44dL,0xf4354d1c3aa90L,0xd5dbabe3db29aL,0xefa908dd3de8aL,
        0x0e4982d1235e4L } },
    /* 75 */
    { { 0x04a22c34cd55eL,0xb32680d132231L,0xfa1d94358695bL,0x0499fb345afa1L,
        0x08046b7f616b2L },
      { 0x3581e38e7d098L,0x8df46f0b70b53L,0x4cb78c4d7f61eL,0xaf5530dea9ea4L,
        0x0eb17ca7b9082L } },
    /* 76 */
    { { 0x1b59876a145b9L,0x0fc1bc71ec175L,0x92715bba5cf6bL,0xe131d3e035653L,
        0x0097b00bafab5L },
      { 0x6c8e9565f69e1L,0x5ab5be5199aa6L,0xa4fd98477e8f7L,0xcc9e6033ba11dL,
        0x0f95c747bafdbL } },
    /* 77 */
    { { 0xf01d3bebae45eL,0xf0c4bc6955558L,0xbc64fc6a8ebe9L,0xd837aeb705b1dL,
        0x03512601e566eL },
      { 0x6f1e1fa1161cdL,0xd54c65ef87933L,0x24f21e5328ab8L,0xab6b4757eee27L,
        0x00ef971236068L } },
    /* 78 */
    { { 0x98cf754ca4226L,0x38f8642c8e025L,0x68e17905eede1L,0xbc9548963f744L,
        0x0fc16d9333b4fL },
      { 0x6fb31e7c800caL,0x312678adaabe9L,0xff3e8b5138063L,0x7a173d6244976L,
        0x014ca4af1b95dL } },
    /* 79 */
    { { 0x771babd2f81d5L,0x6901f7d1967a4L,0xad9c9071a5f9dL,0x231dd898bef7cL,
        0x04057b063f59cL },
      { 0xd82fe89c05c0aL,0x6f1dc0df85bffL,0x35a16dbe4911cL,0x0b133befccaeaL,
        0x01c3b5d64f133L } },
    /* 80 */
    { { 0x14bfe80ec21feL,0x6ac255be825feL,0xf4a5d67f6ce11L,0x63af98bc5a072L,
        0x0fad27148db7eL },
      { 0x0b6ac29ab05b3L,0x3c4e251ae690cL,0x2aade7d37a9a8L,0x1a840a7dc875cL,
        0x077387de39f0eL } },
    /* 81 */
    { { 0xecc49a56c0dd7L,0xd846086c741e9L,0x505aecea5cffcL,0xc47e8f7a1408fL,
        0x0b37b85c0bef0L },
      { 0x6b6e4cc0e6a8fL,0xbf6b388f23359L,0x39cef4efd6d4bL,0x28d5aba453facL,
        0x09c135ac8f9f6L } },
    /* 82 */
    { { 0xa320284e35743L,0xb185a3cdef32aL,0xdf19819320d6aL,0x851fb821b1761L,
        0x05721361fc433L },
      { 0xdb36a71fc9168L,0x735e5c403c1f0L,0x7bcd8f55f98baL,0x11bdf64ca87e3L,
        0x0dcbac3c9e6bbL } },
    /* 83 */
    { { 0xd99684518cbe2L,0x189c9eb04ef01L,0x47feebfd242fcL,0x6862727663c7eL,
        0x0b8c1c89e2d62L },
      { 0x58bddc8e1d569L,0xc8b7d88cd051aL,0x11f31eb563809L,0x22d426c27fd9fL,
        0x05d23bbda2f94L } },
    /* 84 */
    { { 0xc729495c8f8beL,0x803bf362bf0a1L,0xf63d4ac2961c4L,0xe9009e418403dL,
        0x0c109f9cb91ecL },
      { 0x095d058945705L,0x96ddeb85c0c2dL,0xa40449bb9083dL,0x1ee184692b8d7L,
        0x09bc3344f2eeeL } },
    /* 85 */
    { { 0xae35642913074L,0x2748a542b10d5L,0x310732a55491bL,0x4cc1469ca665bL,
        0x029591d525f1aL },
      { 0xf5b6bb84f983fL,0x419f5f84e1e76L,0x0baa189be7eefL,0x332c1200d4968L,
        0x06376551f18efL } },
    /* 86 */
    { { 0x5f14e562976ccL,0xe60ef12c38bdaL,0xcca985222bca3L,0x987abbfa30646L,
        0x0bdb79dc808e2L },
      { 0xcb5c9cb06a772L,0xaafe536dcefd2L,0xc2b5db838f475L,0xc14ac2a3e0227L,
        0x08ee86001add3L } },
    /* 87 */
    { { 0x96981a4ade873L,0x4dc4fba48ccbeL,0xa054ba57ee9aaL,0xaa4b2cee28995L,
        0x092e51d7a6f77L },
      { 0xbafa87190a34dL,0x5bf6bd1ed1948L,0xcaf1144d698f7L,0xaaaad00ee6e30L,
        0x05182f86f0a56L } },
    /* 88 */
    { { 0x6212c7a4cc99cL,0x683e6d9ca1fbaL,0xac98c5aff609bL,0xa6f25dbb27cb5L,
        0x091dcab5d4073L },
      { 0x6cc3d5f575a70L,0x396f8d87fa01bL,0x99817360cb361L,0x4f2b165d4e8c8L,
        0x017a0cedb9797L } },
    /* 89 */
    { { 0x61e2a076c8d3aL,0x39210f924b388L,0x3a835d9701aadL,0xdf4194d0eae41L,
        0x02e8ce36c7f4cL },
      { 0x73dab037a862bL,0xb760e4c8fa912L,0x3baf2dd01ba9bL,0x68f3f96453883L,
        0x0f4ccc6cb34f6L } },
    /* 90 */
    { { 0xf525cf1f79687L,0x9592efa81544eL,0x5c78d297c5954L,0xf3c9e1231741aL,
        0x0ac0db4889a0dL },
      { 0xfc711df01747fL,0x58ef17df1386bL,0xccb6bb5592b93L,0x74a2e5880e4f5L,
        0x095a64a6194c9L } },
    /* 91 */
    { { 0x1efdac15a4c93L,0x738258514172cL,0x6cb0bad40269bL,0x06776a8dfb1c1L,
        0x0231e54ba2921L },
      { 0xdf9178ae6d2dcL,0x3f39112918a70L,0xe5b72234d6aa6L,0x31e1f627726b5L,
        0x0ab0be032d8a7L } },
    /* 92 */
    { { 0xad0e98d131f2dL,0xe33b04f101097L,0x5e9a748637f09L,0xa6791ac86196dL,
        0x0f1bcc8802cf6L },
      { 0x69140e8daacb4L,0x5560f6500925cL,0x77937a63c4e40L,0xb271591cc8fc4L,
        0x0851694695aebL } },
    /* 93 */
    { { 0x5c143f1dcf593L,0x29b018be3bde3L,0xbdd9d3d78202bL,0x55d8e9cdadc29L,
        0x08f67d9d2daadL },
      { 0x116567481ea5fL,0xe9e34c590c841L,0x5053fa8e7d2ddL,0x8b5dffdd43f40L,
        0x0f84572b9c072L } },
    /* 94 */
    { { 0xa7a7197af71c9L,0x447a7365655e1L,0xe1d5063a14494L,0x2c19a1b4ae070L,
        0x0edee2710616bL },
      { 0x034f511734121L,0x554a25e9f0b2fL,0x40c2ecf1cac6eL,0xd7f48dc148f3aL,
        0x09fd27e9b44ebL } },
    /* 95 */
    { { 0x7658af6e2cb16L,0x2cfe5919b63ccL,0x68d5583e3eb7dL,0xf3875a8c58161L,
        0x0a40c2fb6958fL },
      { 0xec560fedcc158L,0xc655f230568c9L,0xa307e127ad804L,0xdecfd93967049L,
        0x099bc9bb87dc6L } },
    /* 96 */
    { { 0x9521d927dafc6L,0x695c09cd1984aL,0x9366dde52c1fbL,0x7e649d9581a0fL,
        0x09abe210ba16dL },
      { 0xaf84a48915220L,0x6a4dd816c6480L,0x681ca5afa7317L,0x44b0c7d539871L,
        0x07881c25787f3L } },
    /* 97 */
    { { 0x99b51e0bcf3ffL,0xc5127f74f6933L,0xd01d9680d02cbL,0x89408fb465a2dL,
        0x015e6e319a30eL },
      { 0xd6e0d3e0e05f4L,0xdc43588404646L,0x4f850d3fad7bdL,0x72cebe61c7d1cL,
        0x00e55facf1911L } },
    /* 98 */
    { { 0xd9806f8787564L,0x2131e85ce67e9L,0x819e8d61a3317L,0x65776b0158cabL,
        0x0d73d09766fe9L },
      { 0x834251eb7206eL,0x0fc618bb42424L,0xe30a520a51929L,0xa50b5dcbb8595L,
        0x09250a3748f15L } },
    /* 99 */
    { { 0xf08f8be577410L,0x035077a8c6cafL,0xc0a63a4fd408aL,0x8c0bf1f63289eL,
        0x077414082c1ccL },
      { 0x40fa6eb0991cdL,0x6649fdc29605aL,0x324fd40c1ca08L,0x20b93a68a3c7bL,
        0x08cb04f4d12ebL } },
    /* 100 */
    { { 0x2d0556906171cL,0xcdb0240c3fb1cL,0x89068419073e9L,0x3b51db8e6b4fdL,
        0x0e4e429ef4712L },
      { 0xdd53c38ec36f4L,0x01ff4b6a270b8L,0x79a9a48f9d2dcL,0x65525d066e078L,
        0x037bca2ff3c6eL } },
    /* 101 */
    { { 0x2e3c7df562470L,0xa2c0964ac94cdL,0x0c793be44f272L,0xb22a7c6d5df98L,
        0x059913edc3002L },
      { 0x39a835750592aL,0x80e783de027a1L,0xa05d64f99e01dL,0xe226cf8c0375eL,
        0x043786e4ab013L } },
    /* 102 */
    { { 0x2b0ed9e56b5a6L,0xa6d9fc68f9ff3L,0x97846a70750d9L,0x9e7aec15e8455L,
        0x08638ca98b7e7L },
      { 0xae0960afc24b2L,0xaf4dace8f22f5L,0xecba78f05398eL,0xa6f03b765dd0aL,
        0x01ecdd36a7b3aL } },
    /* 103 */
    { { 0xacd626c5ff2f3L,0xc02873a9785d3L,0x2110d54a2d516L,0xf32dad94c9fadL,
        0x0d85d0f85d459L },
      { 0x00b8d10b11da3L,0x30a78318c49f7L,0x208decdd2c22cL,0x3c62556988f49L,
        0x0a04f19c3b4edL } },
    /* 104 */
    { { 0x924c8ed7f93bdL,0x5d392f51f6087L,0x21b71afcb64acL,0x50b07cae330a8L,
        0x092b2eeea5c09L },
      { 0xc4c9485b6e235L,0xa92936c0f085aL,0x0508891ab2ca4L,0x276c80faa6b3eL,
        0x01ee782215834L } },
    /* 105 */
    { { 0xa2e00e63e79f7L,0xb2f399d906a60L,0x607c09df590e7L,0xe1509021054a6L,
        0x0f3f2ced857a6L },
      { 0x510f3f10d9b55L,0xacd8642648200L,0x8bd0e7c9d2fcfL,0xe210e5631aa7eL,
        0x00f56a4543da3L } },
    /* 106 */
    { { 0x1bffa1043e0dfL,0xcc9c007e6d5b2L,0x4a8517a6c74b6L,0xe2631a656ec0dL,
        0x0bd8f17411969L },
      { 0xbbb86beb7494aL,0x6f45f3b8388a9L,0x4e5a79a1567d4L,0xfa09df7a12a7aL,
        0x02d1a1c3530ccL } },
    /* 107 */
    { { 0xe3813506508daL,0xc4a1d795a7192L,0xa9944b3336180L,0xba46cddb59497L,
        0x0a107a65eb91fL },
      { 0x1d1c50f94d639L,0x758a58b7d7e6dL,0xd37ca1c8b4af3L,0x9af21a7c5584bL,
        0x0183d760af87aL } },
    /* 108 */
    { { 0x697110dde59a4L,0x070e8bef8729dL,0xf2ebe78f1ad8dL,0xd754229b49634L,
        0x01d44179dc269L },
      { 0xdc0cf8390d30eL,0x530de8110cb32L,0xbc0339a0a3b27L,0xd26231af1dc52L,
        0x0771f9cc29606L } },
    /* 109 */
    { { 0x93e7785040739L,0xb98026a939999L,0x5f8fc2644539dL,0x718ecf40f6f2fL,
        0x064427a310362L },
      { 0xf2d8785428aa8L,0x3febfb49a84f4L,0x23d01ac7b7adcL,0x0d6d201b2c6dfL,
        0x049d9b7496ae9L } },
    /* 110 */
    { { 0x8d8bc435d1099L,0x4e8e8d1a08cc7L,0xcb68a412adbcdL,0x544502c2e2a02L,
        0x09037d81b3f60L },
      { 0xbac27074c7b61L,0xab57bfd72e7cdL,0x96d5352fe2031L,0x639c61ccec965L,
        0x008c3de6a7cc0L } },
    /* 111 */
    { { 0xdd020f6d552abL,0x9805cd81f120fL,0x135129156baffL,0x6b2f06fb7c3e9L,
        0x0c69094424579L },
      { 0x3ae9c41231bd1L,0x875cc5820517bL,0x9d6a1221eac6eL,0x3ac0208837abfL,
        0x03fa3db02cafeL } },
    /* 112 */
    { { 0xa3e6505058880L,0xef643943f2d75L,0xab249257da365L,0x08ff4147861cfL,
        0x0c5c4bdb0fdb8L },
      { 0x13e34b272b56bL,0x9511b9043a735L,0x8844969c8327eL,0xb6b5fd8ce37dfL,
        0x02d56db9446c2L } },
    /* 113 */
    { { 0x1782fff46ac6bL,0x2607a2e425246L,0x9a48de1d19f79L,0xba42fafea3c40L,
        0x00f56bd9de503L },
      { 0xd4ed1345cda49L,0xfc816f299d137L,0xeb43402821158L,0xb5f1e7c6a54aaL,
        0x04003bb9d1173L } },
    /* 114 */
    { { 0xe8189a0803387L,0xf539cbd4043b8L,0x2877f21ece115L,0x2f9e4297208ddL,
        0x053765522a07fL },
      { 0x80a21a8a4182dL,0x7a3219df79a49L,0xa19a2d4a2bbd0L,0x4549674d0a2e1L,
        0x07a056f586c5dL } },
    /* 115 */
    { { 0xb25589d8a2a47L,0x48c3df2773646L,0xbf0d5395b5829L,0x267551ec000eaL,
        0x077d482f17a1aL },
      { 0x1bd9587853948L,0xbd6cfbffeeb8aL,0x0681e47a6f817L,0xb0e4ab6ec0578L,
        0x04115012b2b38L } },
    /* 116 */
    { { 0x3f0f46de28cedL,0x609b13ec473c7L,0xe5c63921d5da7L,0x094661b8ce9e6L,
        0x0cdf04572fbeaL },
      { 0x3c58b6c53c3b0L,0x10447b843c1cbL,0xcb9780e97fe3cL,0x3109fb2b8ae12L,
        0x0ee703dda9738L } },
    /* 117 */
    { { 0x15140ff57e43aL,0xd3b1b811b8345L,0xf42b986d44660L,0xce212b3b5dff8L,
        0x02a0ad89da162L },
      { 0x4a6946bc277baL,0x54c141c27664eL,0xabf6274c788c9L,0x4659141aa64ccL,
        0x0d62d0b67ac2bL } },
    /* 118 */
    { { 0x5d87b2c054ac4L,0x59f27df78839cL,0x18128d6570058L,0x2426edf7cbf3bL,
        0x0b39a23f2991cL },
      { 0x84a15f0b16ae5L,0xb1a136f51b952L,0x27007830c6a05L,0x4cc51d63c137fL,
        0x004ed0092c067L } },
    /* 119 */
    { { 0x185d19ae90393L,0x294a3d64e61f4L,0x854fc143047b4L,0xc387ae0001a69L,
        0x0a0a91fc10177L },
      { 0xa3f01ae2c831eL,0x822b727e16ff0L,0xa3075b4bb76aeL,0x0c418f12c8a15L,
        0x0084cf9889ed2L } },
    /* 120 */
    { { 0x509defca6becfL,0x807dffb328d98L,0x778e8b92fceaeL,0xf77e5d8a15c44L,
        0x0d57955b273abL },
      { 0xda79e31b5d4f1L,0x4b3cfa7a1c210L,0xc27c20baa52f0L,0x41f1d4d12089dL,
        0x08e14ea4202d1L } },
    /* 121 */
    { { 0x50345f2897042L,0x1f43402c4aeedL,0x8bdfb218d0533L,0xd158c8d9c194cL,
        0x0597e1a372aa4L },
      { 0x7ec1acf0bd68cL,0xdcab024945032L,0x9fe3e846d4be0L,0x4dea5b9c8d7acL,
        0x0ca3f0236199bL } },
    /* 122 */
    { { 0xa10b56170bd20L,0xf16d3f5de7592L,0x4b2ade20ea897L,0x07e4a3363ff14L,
        0x0bde7fd7e309cL },
      { 0xbb6d2b8f5432cL,0xcbe043444b516L,0x8f95b5a210dc1L,0xd1983db01e6ffL,
        0x0b623ad0e0a7dL } },
    /* 123 */
    { { 0xbd67560c7b65bL,0x9023a4a289a75L,0x7b26795ab8c55L,0x137bf8220fd0dL,
        0x0d6aa2e4658ecL },
      { 0xbc00b5138bb85L,0x21d833a95c10aL,0x702a32e8c31d1L,0x513ab24ff00b1L,
        0x0111662e02dccL } },
    /* 124 */
    { { 0x14015efb42b87L,0x701b6c4dff781L,0x7d7c129bd9f5dL,0x50f866ecccd7aL,
        0x0db3ee1cb94b7L },
      { 0xf3db0f34837cfL,0x8bb9578d4fb26L,0xc56657de7eed1L,0x6a595d2cdf937L,
        0x0886a64425220L } },
    /* 125 */
    { { 0x34cfb65b569eaL,0x41f72119c13c2L,0x15a619e200111L,0x17bc8badc85daL,
        0x0a70cf4eb018aL },
      { 0xf97ae8c4a6a65L,0x270134378f224L,0xf7e096036e5cfL,0x7b77be3a609e4L,
        0x0aa4772abd174L } },
    /* 126 */
    { { 0x761317aa60cc0L,0x610368115f676L,0xbc1bb5ac79163L,0xf974ded98bb4bL,
        0x0611a6ddc30faL },
      { 0x78cbcc15ee47aL,0x824e0d96a530eL,0xdd9ed882e8962L,0x9c8836f35adf3L,
        0x05cfffaf81642L } },
    /* 127 */
    { { 0x54cff9b7a99cdL,0x9d843c45a1c0dL,0x2c739e17bf3b9L,0x994c038a908f6L,
        0x06e5a6b237dc1L },
      { 0xb454e0ba5db77L,0x7facf60d63ef8L,0x6608378b7b880L,0xabcce591c0c67L,
        0x0481a238d242dL } },
    /* 128 */
    { { 0x17bc035d0b34aL,0x6b8327c0a7e34L,0xc0362d1440b38L,0xf9438fb7262daL,
        0x02c41114ce0cdL },
      { 0x5cef1ad95a0b1L,0xa867d543622baL,0x1e486c9c09b37L,0x929726d6cdd20L,
        0x020477abf42ffL } },
    /* 129 */
    { { 0x5173c18d65dbfL,0x0e339edad82f7L,0xcf1001c77bf94L,0x96b67022d26bdL,
        0x0ac66409ac773L },
      { 0xbb36fc6261cc3L,0xc9190e7e908b0L,0x45e6c10213f7bL,0x2f856541cebaaL,
        0x0ce8e6975cc12L } },
    /* 130 */
    { { 0x21b41bc0a67d2L,0x0a444d248a0f1L,0x59b473762d476L,0xb4a80e044f1d6L,
        0x008fde365250bL },
      { 0xec3da848bf287L,0x82d3369d6eaceL,0x2449482c2a621L,0x6cd73582dfdc9L,
        0x02f7e2fd2565dL } },
    /* 131 */
    { { 0xb92dbc3770fa7L,0x5c379043f9ae4L,0x7761171095e8dL,0x02ae54f34e9d1L,
        0x0c65be92e9077L },
      { 0x8a303f6fd0a40L,0xe3bcce784b275L,0xf9767bfe7d822L,0x3b3a7ae4f5854L,
        0x04bff8e47d119L } },
    /* 132 */
    { { 0x1d21f00ff1480L,0x7d0754db16cd4L,0xbe0f3ea2ab8fbL,0x967dac81d2efbL,
        0x03e4e4ae65772L },
      { 0x8f36d3c5303e6L,0x4b922623977e1L,0x324c3c03bd999L,0x60289ed70e261L,
        0x05388aefd58ecL } },
    /* 133 */
    { { 0x317eb5e5d7713L,0xee75de49daad1L,0x74fb26109b985L,0xbe0e32f5bc4fcL,
        0x05cf908d14f75L },
      { 0x435108e657b12L,0xa5b96ed9e6760L,0x970ccc2bfd421L,0x0ce20e29f51f8L,
        0x0a698ba4060f0L } },
    /* 134 */
    { { 0xb1686ef748fecL,0xa27e9d2cf973dL,0xe265effe6e755L,0xad8d630b6544cL,
        0x0b142ef8a7aebL },
      { 0x1af9f17d5770aL,0x672cb3412fad3L,0xf3359de66af3bL,0x50756bd60d1bdL,
        0x0d1896a965851L } },
    /* 135 */
    { { 0x957ab33c41c08L,0xac5468e2e1ec5L,0xc472f6c87de94L,0xda3918816b73aL,
        0x0267b0e0b7981L },
      { 0x54e5d8e62b988L,0x55116d21e76e5L,0xd2a6f99d8ddc7L,0x93934610faf03L,
        0x0b54e287aa111L } },
    /* 136 */
    { { 0x122b5178a876bL,0xff085104b40a0L,0x4f29f7651ff96L,0xd4e6050b31ab1L,
        0x084abb28b5f87L },
      { 0xd439f8270790aL,0x9d85e3f46bd5eL,0xc1e22122d6cb5L,0x564075f55c1b6L,
        0x0e5436f671765L } },
    /* 137 */
    { { 0x9025e2286e8d5L,0xb4864453be53fL,0x408e3a0353c95L,0xe99ed832f5bdeL,
        0x00404f68b5b9cL },
      { 0x33bdea781e8e5L,0x18163c2f5bcadL,0x119caa33cdf50L,0xc701575769600L,
        0x03a4263df0ac1L } },
    /* 138 */
    { { 0x65ecc9aeb596dL,0xe7023c92b4c29L,0xe01396101ea03L,0xa3674704b4b62L,
        0x00ca8fd3f905eL },
      { 0x23a42551b2b61L,0x9c390fcd06925L,0x392a63e1eb7a8L,0x0c33e7f1d2be0L,
        0x096dca2644ddbL } },
    /* 139 */
    { { 0xbb43a387510afL,0xa8a9a36a01203L,0xf950378846feaL,0x59dcd23a57702L,
        0x04363e2123aadL },
      { 0x3a1c740246a47L,0xd2e55dd24dca4L,0xd8faf96b362b8L,0x98c4f9b086045L,
        0x0840e115cd8bbL } },
    /* 140 */
    { { 0x205e21023e8a7L,0xcdd8dc7a0bf12L,0x63a5ddfc808a8L,0xd6d4e292a2721L,
        0x05e0d6abd30deL },
      { 0x721c27cfc0f64L,0x1d0e55ed8807aL,0xd1f9db242eec0L,0xa25a26a7bef91L,
        0x07dea48f42945L } },
    /* 141 */
    { { 0xf6f1ce5060a81L,0x72f8f95615abdL,0x6ac268be79f9cL,0x16d1cfd36c540L,
        0x0abc2a2beebfdL },
      { 0x66f91d3e2eac7L,0x63d2dd04668acL,0x282d31b6f10baL,0xefc16790e3770L,
        0x04ea353946c7eL } },
    /* 142 */
    { { 0xa2f8d5266309dL,0xc081945a3eed8L,0x78c5dc10a51c6L,0xffc3cecaf45a5L,
        0x03a76e6891c94L },
      { 0xce8a47d7b0d0fL,0x968f584a5f9aaL,0xe697fbe963aceL,0x646451a30c724L,
        0x08212a10a465eL } },
    /* 143 */
    { { 0xc61c3cfab8caaL,0x840e142390ef7L,0xe9733ca18eb8eL,0xb164cd1dff677L,
        0x0aa7cab71599cL },
      { 0xc9273bc837bd1L,0xd0c36af5d702fL,0x423da49c06407L,0x17c317621292fL,
        0x040e38073fe06L } },
    /* 144 */
    { { 0x80824a7bf9b7cL,0x203fbe30d0f4fL,0x7cf9ce3365d23L,0x5526bfbe53209L,
        0x0e3604700b305L },
      { 0xb99116cc6c2c7L,0x08ba4cbee64dcL,0x37ad9ec726837L,0xe15fdcded4346L,
        0x06542d677a3deL } },
    /* 145 */
    { { 0x2b6d07b6c377aL,0x47903448be3f3L,0x0da8af76cb038L,0x6f21d6fdd3a82L,
        0x0a6534aee09bbL },
      { 0x1780d1035facfL,0x339dcb47e630aL,0x447f39335e55aL,0xef226ea50fe1cL,
        0x0f3cb672fdc9aL } },
    /* 146 */
    { { 0x719fe3b55fd83L,0x6c875ddd10eb3L,0x5cea784e0d7a4L,0x70e733ac9fa90L,
        0x07cafaa2eaae8L },
      { 0x14d041d53b338L,0xa0ef87e6c69b8L,0x1672b0fe0acc0L,0x522efb93d1081L,
        0x00aab13c1b9bdL } },
    /* 147 */
    { { 0xce278d2681297L,0xb1b509546addcL,0x661aaf2cb350eL,0x12e92dc431737L,
        0x04b91a6028470L },
      { 0xf109572f8ddcfL,0x1e9a911af4dcfL,0x372430e08ebf6L,0x1cab48f4360acL,
        0x049534c537232L } },
    /* 148 */
    { { 0xf7d71f07b7e9dL,0xa313cd516f83dL,0xc047ee3a478efL,0xc5ee78ef264b6L,
        0x0caf46c4fd65aL },
      { 0xd0c7792aa8266L,0x66913684bba04L,0xe4b16b0edf454L,0x770f56e65168aL,
        0x014ce9e5704c6L } },
    /* 149 */
    { { 0x45e3e965e8f91L,0xbacb0f2492994L,0x0c8a0a0d3aca1L,0x9a71d31cc70f9L,
        0x01bb708a53e4cL },
      { 0xa9e69558bdd7aL,0x08018a26b1d5cL,0xc9cf1ec734a05L,0x0102b093aa714L,
        0x0f9d126f2da30L } },
    /* 150 */
    { { 0xbca7aaff9563eL,0xfeb49914a0749L,0xf5f1671dd077aL,0xcc69e27a0311bL,
        0x0807afcb9729eL },
      { 0xa9337c9b08b77L,0x85443c7e387f8L,0x76fd8ba86c3a7L,0xcd8c85fafa594L,
        0x0751adcd16568L } },
    /* 151 */
    { { 0xa38b410715c0dL,0x718f7697f78aeL,0x3fbf06dd113eaL,0x743f665eab149L,
        0x029ec44682537L },
      { 0x4719cb50bebbcL,0xbfe45054223d9L,0xd2dedb1399ee5L,0x077d90cd5b3a8L,
        0x0ff9370e392a4L } },
    /* 152 */
    { { 0x2d69bc6b75b65L,0xd5266651c559aL,0xde9d7d24188f8L,0xd01a28a9f33e3L,
        0x09776478ba2a9L },
      { 0x2622d929af2c7L,0x6d4e690923885L,0x89a51e9334f5dL,0x82face6cc7e5aL,
        0x074a6313fac2fL } },
    /* 153 */
    { { 0x4dfddb75f079cL,0x9518e36fbbb2fL,0x7cd36dd85b07cL,0x863d1b6cfcf0eL,
        0x0ab75be150ff4L },
      { 0x367c0173fc9b7L,0x20d2594fd081bL,0x4091236b90a74L,0x59f615fdbf03cL,
        0x04ebeac2e0b44L } },
    /* 154 */
    { { 0xc5fe75c9f2c53L,0x118eae9411eb6L,0x95ac5d8d25220L,0xaffcc8887633fL,
        0x0df99887b2c1bL },
      { 0x8eed2850aaecbL,0x1b01d6a272bb7L,0x1cdbcac9d4918L,0x4058978dd511bL,
        0x027b040a7779fL } },
    /* 155 */
    { { 0x05db7f73b2eb2L,0x088e1b2118904L,0x962327ee0df85L,0xa3f5501b71525L,
        0x0b393dd37e4cfL },
      { 0x30e7b3fd75165L,0xc2bcd33554a12L,0xf7b5022d66344L,0x34196c36f1be0L,
        0x009588c12d046L } },
    /* 156 */
    { { 0x6093f02601c3bL,0xf8cf5c335fe08L,0x94aff28fb0252L,0x648b955cf2808L,
        0x081c879a9db9fL },
      { 0xe687cc6f56c51L,0x693f17618c040L,0x059353bfed471L,0x1bc444f88a419L,
        0x0fa0d48f55fc1L } },
    /* 157 */
    { { 0xe1c9de1608e4dL,0x113582822cbc6L,0x57ec2d7010ddaL,0x67d6f6b7ddc11L,
        0x08ea0e156b6a3L },
      { 0x4e02f2383b3b4L,0x943f01f53ca35L,0xde03ca569966bL,0xb5ac4ff6632b2L,
        0x03f5ab924fa00L } },
    /* 158 */
    { { 0xbb0d959739efbL,0xf4e7ebec0d337L,0x11a67d1c751b0L,0x256e2da52dd64L,
        0x08bc768872b74L },
      { 0xe3b7282d3d253L,0xa1f58d779fa5bL,0x16767bba9f679L,0xf34fa1cac168eL,
        0x0b386f19060fcL } },
    /* 159 */
    { { 0x3c1352fedcfc2L,0x6262f8af0d31fL,0x57288c25396bfL,0x9c4d9a02b4eaeL,
        0x04cb460f71b06L },
      { 0x7b4d35b8095eaL,0x596fc07603ae6L,0x614a16592bbf8L,0x5223e1475f66bL,
        0x052c0d50895efL } },
    /* 160 */
    { { 0xc210e15339848L,0xe870778c8d231L,0x956e170e87a28L,0x9c0b9d1de6616L,
        0x04ac3c9382bb0L },
      { 0xe05516998987dL,0xc4ae09f4d619bL,0xa3f933d8b2376L,0x05f41de0b7651L,
        0x0380d94c7e397L } },
    /* 161 */
    { { 0x355aa81542e75L,0xa1ee01b9b701aL,0x24d708796c724L,0x37af6b3a29776L,
        0x02ce3e171de26L },
      { 0xfeb49f5d5bc1aL,0x7e2777e2b5cfeL,0x513756ca65560L,0x4e4d4feaac2f9L,
        0x02e6cd8520b62L } },
    /* 162 */
    { { 0x5954b8c31c31dL,0x005bf21a0c368L,0x5c79ec968533dL,0x9d540bd7626e7L,
        0x0ca17754742c6L },
      { 0xedafff6d2dbb2L,0xbd174a9d18cc6L,0xa4578e8fd0d8cL,0x2ce6875e8793aL,
        0x0a976a7139cabL } },
    /* 163 */
    { { 0x51f1b93fb353dL,0x8b57fcfa720a6L,0x1b15281d75cabL,0x4999aa88cfa73L,
        0x08720a7170a1fL },
      { 0xe8d37693e1b90L,0x0b16f6dfc38c3L,0x52a8742d345dcL,0x893c8ea8d00abL,
        0x09719ef29c769L } },
    /* 164 */
    { { 0xeed8d58e35909L,0xdc33ddc116820L,0xe2050269366d8L,0x04c1d7f999d06L,
        0x0a5072976e157L },
      { 0xa37eac4e70b2eL,0x576890aa8a002L,0x45b2a5c84dcf6L,0x7725cd71bf186L,
        0x099389c9df7b7L } },
    /* 165 */
    { { 0xc08f27ada7a4bL,0x03fd389366238L,0x66f512c3abe9dL,0x82e46b672e897L,
        0x0a88806aa202cL },
      { 0x2044ad380184eL,0xc4126a8b85660L,0xd844f17a8cb78L,0xdcfe79d670c0aL,
        0x00043bffb4738L } },
    /* 166 */
    { { 0x9b5dc36d5192eL,0xd34590b2af8d5L,0x1601781acf885L,0x486683566d0a1L,
        0x052f3ef01ba6cL },
      { 0x6732a0edcb64dL,0x238068379f398L,0x040f3090a482cL,0x7e7516cbe5fa7L,
        0x03296bd899ef2L } },
    /* 167 */
    { { 0xaba89454d81d7L,0xef51eb9b3c476L,0x1c579869eade7L,0x71e9619a21cd8L,
        0x03b90febfaee5L },
      { 0x3023e5496f7cbL,0xd87fb51bc4939L,0x9beb5ce55be41L,0x0b1803f1dd489L,
        0x06e88069d9f81L } },
    /* 168 */
    { { 0x7ab11b43ea1dbL,0xa95259d292ce3L,0xf84f1860a7ff1L,0xad13851b02218L,
        0x0a7222beadefaL },
      { 0xc78ec2b0a9144L,0x51f2fa59c5a2aL,0x147ce385a0240L,0xc69091d1eca56L,
        0x0be94d523bc2aL } },
    /* 169 */
    { { 0x4945e0b226ce7L,0x47967e8b7072fL,0x5a6c63eb8afd7L,0xc766edea46f18L,
        0x07782defe9be8L },
      { 0xd2aa43db38626L,0x8776f67ad1760L,0x4499cdb460ae7L,0x2e4b341b86fc5L,
        0x003838567a289L } },
    /* 170 */
    { { 0xdaefd79ec1a0fL,0xfdceb39c972d8L,0x8f61a953bbcd6L,0xb420f5575ffc5L,
        0x0dbd986c4adf7L },
      { 0xa881415f39eb7L,0xf5b98d976c81aL,0xf2f717d6ee2fcL,0xbbd05465475dcL,
        0x08e24d3c46860L } },
    /* 171 */
    { { 0xd8e549a587390L,0x4f0cbec588749L,0x25983c612bb19L,0xafc846e07da4bL,
        0x0541a99c4407bL },
      { 0x41692624c8842L,0x2ad86c05ffdb2L,0xf7fcf626044c1L,0x35d1c59d14b44L,
        0x0c0092c49f57dL } },
    /* 172 */
    { { 0xc75c3df2e61efL,0xc82e1b35cad3cL,0x09f29f47e8841L,0x944dc62d30d19L,
        0x075e406347286L },
      { 0x41fc5bbc237d0L,0xf0ec4f01c9e7dL,0x82bd534c9537bL,0x858691c51a162L,
        0x05b7cb658c784L } },
    /* 173 */
    { { 0xa70848a28ead1L,0x08fd3b47f6964L,0x67e5b39802dc5L,0x97a19ae4bfd17L,
        0x07ae13eba8df0L },
      { 0x16ef8eadd384eL,0xd9b6b2ff06fd2L,0xbcdb5f30361a2L,0xe3fd204b98784L,
        0x0787d8074e2a8L } },
    /* 174 */
    { { 0x25d6b757fbb1cL,0xb2ca201debc5eL,0xd2233ffe47bddL,0x84844a55e9a36L,
        0x05c2228199ef2L },
      { 0xd4a8588315250L,0x2b827097c1773L,0xef5d33f21b21aL,0xf2b0ab7c4ea1dL,
        0x0e45d37abbaf0L } },
    /* 175 */
    { { 0xf1e3428511c8aL,0xc8bdca6cd3d2dL,0x27c39a7ebb229L,0xb9d3578a71a76L,
        0x0ed7bc12284dfL },
      { 0x2a6df93dea561L,0x8dd48f0ed1cf2L,0xbad23e85443f1L,0x6d27d8b861405L,
        0x0aac97cc945caL } },
    /* 176 */
    { { 0x4ea74a16bd00aL,0xadf5c0bcc1eb5L,0xf9bfc06d839e9L,0xdc4e092bb7f11L,
        0x0318f97b31163L },
      { 0x0c5bec30d7138L,0x23abc30220eccL,0x022360644e8dfL,0xff4d2bb7972fbL,
        0x0fa41faa19a84L } },
    /* 177 */
    { { 0x2d974a6642269L,0xce9bb783bd440L,0x941e60bc81814L,0xe9e2398d38e47L,
        0x038bb6b2c1d26L },
      { 0xe4a256a577f87L,0x53dc11fe1cc64L,0x22807288b52d2L,0x01a5ff336abf6L,
        0x094dd0905ce76L } },
    /* 178 */
    { { 0xcf7dcde93f92aL,0xcb89b5f315156L,0x995e750a01333L,0x2ae902404df9cL,
        0x092077867d25cL },
      { 0x71e010bf39d44L,0x2096bb53d7e24L,0xc9c3d8f5f2c90L,0xeb514c44b7b35L,
        0x081e8428bd29bL } },
    /* 179 */
    { { 0x9c2bac477199fL,0xee6b5ecdd96ddL,0xe40fd0e8cb8eeL,0xa4b18af7db3feL,
        0x01b94ab62dbbfL },
      { 0x0d8b3ce47f143L,0xfc63f4616344fL,0xc59938351e623L,0x90eef18f270fcL,
        0x006a38e280555L } },
    /* 180 */
    { { 0xb0139b3355b49L,0x60b4ebf99b2e5L,0x269f3dc20e265L,0xd4f8c08ffa6bdL,
        0x0a7b36c2083d9L },
      { 0x15c3a1b3e8830L,0xe1a89f9c0b64dL,0x2d16930d5fceaL,0x2a20cfeee4a2eL,
        0x0be54c6b4a282L } },
    /* 181 */
    { { 0xdb3df8d91167cL,0x79e7a6625ed6cL,0x46ac7f4517c3fL,0x22bb7105648f3L,
        0x0bf30a5abeae0L },
      { 0x785be93828a68L,0x327f3ef0368e7L,0x92146b25161c3L,0xd13ae11b5feb5L,
        0x0d1c820de2732L } },
    /* 182 */
    { { 0xe13479038b363L,0x546b05e519043L,0x026cad158c11fL,0x8da34fe57abe6L,
        0x0b7d17bed68a1L },
      { 0xa5891e29c2559L,0x765bfffd8444cL,0x4e469484f7a03L,0xcc64498de4af7L,
        0x03997fd5e6412L } },
    /* 183 */
    { { 0x746828bd61507L,0xd534a64d2af20L,0xa8a15e329e132L,0x13e8ffeddfb08L,
        0x00eeb89293c6cL },
      { 0x69a3ea7e259f8L,0xe6d13e7e67e9bL,0xd1fa685ce1db7L,0xb6ef277318f6aL,
        0x0228916f8c922L } },
    /* 184 */
    { { 0xae25b0a12ab5bL,0x1f957bc136959L,0x16e2b0ccc1117L,0x097e8058429edL,
        0x0ec05ad1d6e93L },
      { 0xba5beac3f3708L,0x3530b59d77157L,0x18234e531baf9L,0x1b3747b552371L,
        0x07d3141567ff1L } },
    /* 185 */
    { { 0x9c05cf6dfefabL,0x68dcb377077bdL,0xa38bb95be2f22L,0xd7a3e53ead973L,
        0x0e9ce66fc9bc1L },
      { 0xa15766f6a02a1L,0xdf60e600ed75aL,0x8cdc1b938c087L,0x0651f8947f346L,
        0x0d9650b017228L } },
    /* 186 */
    { { 0xb4c4a5a057e60L,0xbe8def25e4504L,0x7c1ccbdcbccc3L,0xb7a2a63532081L,
        0x014d6699a804eL },
      { 0xa8415db1f411aL,0x0bf80d769c2c8L,0xc2f77ad09fbafL,0x598ab4deef901L,
        0x06f4c68410d43L } },
    /* 187 */
    { { 0x6df4e96c24a96L,0x85fcbd99a3872L,0xb2ae30a534dbcL,0x9abb3c466ef28L,
        0x04c4350fd6118L },
      { 0x7f716f855b8daL,0x94463c38a1296L,0xae9334341a423L,0x18b5c37e1413eL,
        0x0a726d2425a31L } },
    /* 188 */
    { { 0x6b3ee948c1086L,0x3dcbd3a2e1daeL,0x3d022f3f1de50L,0xf3923f35ed3f0L,
        0x013639e82cc6cL },
      { 0x938fbcdafaa86L,0xfb2654a2589acL,0x5051329f45bc5L,0x35a31963b26e4L,
        0x0ca9365e1c1a3L } },
    /* 189 */
    { { 0x5ac754c3b2d20L,0x17904e241b361L,0xc9d071d742a54L,0x72a5b08521c4cL,
        0x09ce29c34970bL },
      { 0x81f736d3e0ad6L,0x9ef2f8434c8ccL,0xce862d98060daL,0xaf9835ed1d1a6L,
        0x048c4abd7ab42L } },
    /* 190 */
    { { 0x1b0cc40c7485aL,0xbbe5274dbfd22L,0x263d2e8ead455L,0x33cb493c76989L,
        0x078017c32f67bL },
      { 0x35769930cb5eeL,0x940c408ed2b9dL,0x72f1a4dc0d14eL,0x1c04f8b7bf552L,
        0x053cd0454de5cL } },
    /* 191 */
    { { 0x585fa5d28ccacL,0x56005b746ebcdL,0xd0123aa5f823eL,0xfa8f7c79f0a1cL,
        0x0eea465c1d3d7L },
      { 0x0659f0551803bL,0x9f7ce6af70781L,0x9288e706c0b59L,0x91934195a7702L,
        0x01b6e42a47ae6L } },
    /* 192 */
    { { 0x0937cf67d04c3L,0xe289eeb8112e8L,0x2594d601e312bL,0xbd3d56b5d8879L,
        0x00224da14187fL },
      { 0xbb8630c5fe36fL,0x604ef51f5f87aL,0x3b429ec580f3cL,0xff33964fb1bfbL,
        0x060838ef042bfL } },
    /* 193 */
    { { 0xcb2f27e0bbe99L,0xf304aa39ee432L,0xfa939037bda44L,0x16435f497c7a9L,
        0x0636eb2022d33L },
      { 0xd0e6193ae00aaL,0xfe31ae6d2ffcfL,0xf93901c875a00L,0x8bacf43658a29L,
        0x08844eeb63921L } },
    /* 194 */
    { { 0x171d26b3bae58L,0x7117e39f3e114L,0x1a8eada7db3dfL,0x789ecd37bc7f8L,
        0x027ba83dc51fbL },
      { 0xf439ffbf54de5L,0x0bb5fe1a71a7dL,0xb297a48727703L,0xa4ab42ee8e35dL,
        0x0adb62d3487f3L } },
    /* 195 */
    { { 0x168a2a175df2aL,0x4f618c32e99b1L,0x46b0916082aa0L,0xc8b2c9e4f2e71L,
        0x0b990fd7675e7L },
      { 0x9d96b4df37313L,0x79d0b40789082L,0x80877111c2055L,0xd18d66c9ae4a7L,
        0x081707ef94d10L } },
    /* 196 */
    { { 0x7cab203d6ff96L,0xfc0d84336097dL,0x042db4b5b851bL,0xaa5c268823c4dL,
        0x03792daead5a8L },
      { 0x18865941afa0bL,0x4142d83671528L,0xbe4e0a7f3e9e7L,0x01ba17c825275L,
        0x05abd635e94b0L } },
    /* 197 */
    { { 0xfa84e0ac4927cL,0x35a7c8cf23727L,0xadca0dfe38860L,0xb610a4bcd5ea4L,
        0x05995bf21846aL },
      { 0xf860b829dfa33L,0xae958fc18be90L,0x8630366caafe2L,0x411e9b3baf447L,
        0x044c32ca2d483L } },
    /* 198 */
    { { 0xa97f1e40ed80cL,0xb131d2ca82a74L,0xc2d6ad95f938cL,0xa54c53f2124b7L,
        0x01f2162fb8082L },
      { 0x67cc5720b173eL,0x66085f12f97e4L,0xc9d65dc40e8a6L,0x07c98cebc20e4L,
        0x08f1d402bc3e9L } },
    /* 199 */
    { { 0x92f9cfbc4058aL,0xb6292f56704f5L,0xc1d8c57b15e14L,0xdbf9c55cfe37bL,
        0x0b1980f43926eL },
      { 0x33e0932c76b09L,0x9d33b07f7898cL,0x63bb4611df527L,0x8e456f08ead48L,
        0x02828ad9b3744L } },
    /* 200 */
    { { 0x722c4c4cf4ac5L,0x3fdde64afb696L,0x0890832f5ac1aL,0xb3900551baa2eL,
        0x04973f1275a14L },
      { 0xd8335322eac5dL,0xf50bd9b568e59L,0x25883935e07eeL,0x8ac7ab36720faL,
        0x06dac8ed0db16L } },
    /* 201 */
    { { 0x545aeeda835efL,0xd21d10ed51f7bL,0x3741b094aa113L,0xde4c035a65e01L,
        0x04b23ef5920b9L },
      { 0xbb6803c4c7341L,0x6d3f58bc37e82L,0x51e3ee8d45770L,0x9a4e73527863aL,
        0x04dd71534ddf4L } },
    /* 202 */
    { { 0x4467295476cd9L,0x2fe31a725bbf9L,0xc4b67e0648d07L,0x4dbb1441c8b8fL,
        0x0fd3170002f4aL },
      { 0x43ff48995d0e1L,0xd10ef729aa1cbL,0x179898276e695L,0xf365e0d5f9764L,
        0x014fac58c9569L } },
    /* 203 */
    { { 0xa0065f312ae18L,0xc0fcc93fc9ad9L,0xa7d284651958dL,0xda50d9a142408L,
        0x0ed7c765136abL },
      { 0x70f1a25d4abbcL,0xf3f1a113ea462L,0xb51952f9b5dd8L,0x9f53c609b0755L,
        0x0fefcb7f74d2eL } },
    /* 204 */
    { { 0x9497aba119185L,0x30aac45ba4bd0L,0xa521179d54e8cL,0xd80b492479deaL,
        0x01801a57e87e0L },
      { 0xd3f8dfcafffb0L,0x0bae255240073L,0xb5fdfbc6cf33cL,0x1064781d763b5L,
        0x09f8fc11e1eadL } },
    /* 205 */
    { { 0x3a1715e69544cL,0x67f04b7813158L,0x78a4c320eaf85L,0x69a91e22a8fd2L,
        0x0a9d3809d3d3aL },
      { 0xc2c2c59a2da3bL,0xf61895c847936L,0x3d5086938ccbcL,0x8ef75e65244e6L,
        0x03006b9aee117L } },
    /* 206 */
    { { 0x1f2b0c9eead28L,0x5d89f4dfbc0bbL,0x2ce89397eef63L,0xf761074757fdbL,
        0x00ab85fd745f8L },
      { 0xa7c933e5b4549L,0x5c97922f21ecdL,0x43b80404be2bbL,0x42c2261a1274bL,
        0x0b122d67511e9L } },
    /* 207 */
    { { 0x607be66a5ae7aL,0xfa76adcbe33beL,0xeb6e5c501e703L,0xbaecaf9043014L,
        0x09f599dc1097dL },
      { 0x5b7180ff250edL,0x74349a20dc6d7L,0x0b227a38eb915L,0x4b78425605a41L,
        0x07d5528e08a29L } },
    /* 208 */
    { { 0x58f6620c26defL,0xea582b2d1ef0fL,0x1ce3881025585L,0x1730fbe7d79b0L,
        0x028ccea01303fL },
      { 0xabcd179644ba5L,0xe806fff0b8d1dL,0x6b3e17b1fc643L,0x13bfa60a76fc6L,
        0x0c18baf48a1d0L } },
    /* 209 */
    { { 0x638c85dc4216dL,0x67206142ac34eL,0x5f5064a00c010L,0x596bd453a1719L,
        0x09def809db7a9L },
      { 0x8642e67ab8d2cL,0x336237a2b641eL,0x4c4218bb42404L,0x8ce57d506a6d6L,
        0x00357f8b06880L } },
    /* 210 */
    { { 0xdbe644cd2cc88L,0x8df0b8f39d8e9L,0xd30a0c8cc61c2L,0x98874a309874cL,
        0x0e4a01add1b48L },
      { 0x1eeacf57cd8f9L,0x3ebd594c482edL,0xbd2f7871b767dL,0xcc30a7295c717L,
        0x0466d7d79ce10L } },
    /* 211 */
    { { 0x318929dada2c7L,0xc38f9aa27d47dL,0x20a59e14fa0a6L,0xad1a90e4fd288L,
        0x0c672a522451eL },
      { 0x07cc85d86b655L,0x3bf9ad4af1306L,0x71172a6f0235dL,0x751399a086805L,
        0x05e3d64faf2a6L } },
    /* 212 */
    { { 0x410c79b3b4416L,0x85eab26d99aa6L,0xb656a74cd8fcfL,0x42fc5ebff74adL,
        0x06c8a7a95eb8eL },
      { 0x60ba7b02a63bdL,0x038b8f004710cL,0x12d90b06b2f23L,0xca918c6c37383L,
        0x0348ae422ad82L } },
    /* 213 */
    { { 0x746635ccda2fbL,0xa18e0726d27f4L,0x92b1f2022accaL,0x2d2e85adf7824L,
        0x0c1074de0d9efL },
      { 0x3ce44ae9a65b3L,0xac05d7151bfcfL,0xe6a9788fd71e4L,0x4ffcd4711f50cL,
        0x0fbadfbdbc9e5L } },
    /* 214 */
    { { 0x3f1cd20a99363L,0x8f6cf22775171L,0x4d359b2b91565L,0x6fcd968175cd2L,
        0x0b7f976b48371L },
      { 0x8e24d5d6dbf74L,0xfd71c3af36575L,0x243dfe38d23baL,0xc80548f477600L,
        0x0f4d41b2ecafcL } },
    /* 215 */
    { { 0x1cf28fdabd48dL,0x3632c078a451fL,0x17146e9ce81beL,0x0f106ace29741L,
        0x0180824eae016L },
      { 0x7698b66e58358L,0x52ce6ca358038L,0xe41e6c5635687L,0x6d2582380e345L,
        0x067e5f63983cfL } },
    /* 216 */
    { { 0xccb8dcf4899efL,0xf09ebb44c0f89L,0x2598ec9949015L,0x1fc6546f9276bL,
        0x09fef789a04c1L },
      { 0x67ecf53d2a071L,0x7fa4519b096d3L,0x11e2eefb10e1aL,0x4e20ca6b3fb06L,
        0x0bc80c181a99cL } },
    /* 217 */
    { { 0x536f8e5eb82e6L,0xc7f56cb920972L,0x0b5da5e1a484fL,0xdf10c78e21715L,
        0x049270e629f8cL },
      { 0x9b7bbea6b50adL,0xc1a2388ffc1a3L,0x107197b9a0284L,0x2f7f5403eb178L,
        0x0d2ee52f96137L } },
    /* 218 */
    { { 0xcd28588e0362aL,0xa78fa5d94dd37L,0x434a526442fa8L,0xb733aff836e5aL,
        0x0dfb478bee5abL },
      { 0xf1ce7673eede6L,0xd42b5b2f04a91L,0x530da2fa5390aL,0x473a5e66f7bf5L,
        0x0d9a140b408dfL } },
    /* 219 */
    { { 0x221b56e8ea498L,0x293563ee090e0L,0x35d2ade623478L,0x4b1ae06b83913L,
        0x0760c058d623fL },
      { 0x9b58cc198aa79L,0xd2f07aba7f0b8L,0xde2556af74890L,0x04094e204110fL,
        0x07141982d8f19L } },
    /* 220 */
    { { 0xa0e334d4b0f45L,0x38392a94e16f0L,0x3c61d5ed9280bL,0x4e473af324c6bL,
        0x03af9d1ce89d5L },
      { 0xf798120930371L,0x4c21c17097fd8L,0xc42309beda266L,0x7dd60e9545dcdL,
        0x0b1f815c37395L } },
    /* 221 */
    { { 0xaa78e89fec44aL,0x473caa4caf84fL,0x1b6a624c8c2aeL,0xf052691c807dcL,
        0x0a41aed141543L },
      { 0x353997d5ffe04L,0xdf625b6e20424L,0x78177758bacb2L,0x60ef85d660be8L,
        0x0d6e9c1dd86fbL } },
    /* 222 */
    { { 0x2e97ec6853264L,0xb7e2304a0b3aaL,0x8eae9be771533L,0xf8c21b912bb7bL,
        0x09c9c6e10ae9bL },
      { 0x09a59e030b74cL,0x4d6a631e90a23L,0x49b79f24ed749L,0x61b689f44b23aL,
        0x0566bd59640faL } },
    /* 223 */
    { { 0xc0118c18061f3L,0xd37c83fc70066L,0x7273245190b25L,0x345ef05fc8e02L,
        0x0cf2c7390f525L },
      { 0xbceb410eb30cfL,0xba0d77703aa09L,0x50ff255cfd2ebL,0x0979e842c43a1L,
        0x002f517558aa2L } },
    /* 224 */
    { { 0xef794addb7d07L,0x4224455500396L,0x78aa3ce0b4fc7L,0xd97dfaff8eaccL,
        0x014e9ada5e8d4L },
      { 0x480a12f7079e2L,0xcde4b0800edaaL,0x838157d45baa3L,0x9ae801765e2d7L,
        0x0a0ad4fab8e9dL } },
    /* 225 */
    { { 0xb76214a653618L,0x3c31eaaa5f0bfL,0x4949d5e187281L,0xed1e1553e7374L,
        0x0bcd530b86e56L },
      { 0xbe85332e9c47bL,0xfeb50059ab169L,0x92bfbb4dc2776L,0x341dcdba97611L,
        0x0909283cf6979L } },
    /* 226 */
    { { 0x0032476e81a13L,0x996217123967bL,0x32e19d69bee1aL,0x549a08ed361bdL,
        0x035eeb7c9ace1L },
      { 0x0ae5a7e4e5bdcL,0xd3b6ceec6e128L,0xe266bc12dcd2cL,0xe86452e4224c6L,
        0x09a8b2cf4448aL } },
    /* 227 */
    { { 0x71bf209d03b59L,0xa3b65af2abf64L,0xbd5eec9c90e62L,0x1379ff7ff168eL,
        0x06bdb60f4d449L },
      { 0xafebc8a55bc30L,0x1610097fe0dadL,0xc1e3bddc79eadL,0x08a942e197414L,
        0x001ec3cfd94baL } },
    /* 228 */
    { { 0x277ebdc9485c2L,0x7922fb10c7ba6L,0x0a28d8a48cc9aL,0x64f64f61d60f7L,
        0x0d1acb1c04754L },
      { 0x902b126f36612L,0x4ee0618d8bd26L,0x08357ee59c3a4L,0x26c24df8a8133L,
        0x07dcd079d4056L } },
    /* 229 */
    { { 0x7d4d3f05a4b48L,0x52372307725ceL,0x12a915aadcd29L,0x19b8d18f79718L,
        0x00bf53589377dL },
      { 0xcd95a6c68ea73L,0xca823a584d35eL,0x473a723c7f3bbL,0x86fc9fb674c6fL,
        0x0d28be4d9e166L } },
    /* 230 */
    { { 0xb990638fa8e4bL,0x6e893fd8fc5d2L,0x36fb6fc559f18L,0x88ce3a6de2aa4L,
        0x0d76007aa510fL },
      { 0x0aab6523a4988L,0x4474dd02732d1L,0x3407278b455cfL,0xbb017f467082aL,
        0x0f2b52f68b303L } },
    /* 231 */
    { { 0x7eafa9835b4caL,0xfcbb669cbc0d5L,0x66431982d2232L,0xed3a8eeeb680cL,
        0x0d8dbe98ecc5aL },
      { 0x9be3fc5a02709L,0xe5f5ba1fa8cbaL,0x10ea85230be68L,0x9705febd43cdfL,
        0x0e01593a3ee55L } },
    /* 232 */
    { { 0x5af50ea75a0a6L,0xac57858033d3eL,0x0176406512226L,0xef066fe6d50fdL,
        0x0afec07b1aeb8L },
      { 0x9956780bb0a31L,0xcc37309aae7fbL,0x1abf3896f1af3L,0xbfdd9153a15a0L,
        0x0a71b93546e2dL } },
    /* 233 */
    { { 0xe12e018f593d2L,0x28a078122bbf8L,0xba4f2add1a904L,0x23d9150505db0L,
        0x053a2005c6285L },
      { 0x8b639e7f2b935L,0x5ac182961a07cL,0x518ca2c2bff97L,0x8e3d86bceea77L,
        0x0bf47d19b3d58L } },
    /* 234 */
    { { 0x967a7dd7665d5L,0x572f2f4de5672L,0x0d4903f4e3030L,0xa1b6144005ae8L,
        0x0001c2c7f39c9L },
      { 0xa801469efc6d6L,0xaa7bc7a724143L,0x78150a4c810bdL,0xb99b5f65670baL,
        0x0fdadf8e786ffL } },
    /* 235 */
    { { 0x8cb88ffc00785L,0x913b48eb67fd3L,0xf368fbc77fa75L,0x3c940454d055bL,
        0x03a838e4d5aa4L },
      { 0x663293e97bb9aL,0x63441d94d9561L,0xadb2a839eb933L,0x1da3515591a60L,
        0x03cdb8257873eL } },
    /* 236 */
    { { 0x140a97de77eabL,0x0d41648109137L,0xeb1d0dff7e1c5L,0x7fba762dcad2cL,
        0x05a60cc89f1f5L },
      { 0x3638240d45673L,0x195913c65580bL,0xd64b7411b82beL,0x8fc0057284b8dL,
        0x0922ff56fdbfdL } },
    /* 237 */
    { { 0x65deec9a129a1L,0x57cc284e041b2L,0xebfbe3ca5b1ceL,0xcd6204380c46cL,
        0x072919a7df6c5L },
      { 0xf453a8fb90f9aL,0x0b88e4031b298L,0x96f1856d719c0L,0x089ae32c0e777L,
        0x05e7917803624L } },
    /* 238 */
    { { 0x6ec557f63cdfbL,0x71f1cae4fd5c1L,0x60597ca8e6a35L,0x2fabfce26bea5L,
        0x04e0a5371e24cL },
      { 0xa40d3a5765357L,0x440d73a2b4276L,0x1d11a323c89afL,0x04eeb8f370ae4L,
        0x0f5ff7818d566L } },
    /* 239 */
    { { 0x3e3fe1a09df21L,0x8ee66e8e47fbfL,0x9c8901526d5d2L,0x5e642096bd0a2L,
        0x0e41df0e9533fL },
      { 0xfda40b3ba9e3fL,0xeb2604d895305L,0xf0367c7f2340cL,0x155f0866e1927L,
        0x08edd7d6eac4fL } },
    /* 240 */
    { { 0x1dc0e0bfc8ff3L,0x2be936f42fc9aL,0xca381ef14efd8L,0xee9667016f7ccL,
        0x01432c1caed8aL },
      { 0x8482970b23c26L,0x730735b273ec6L,0xaef0f5aa64fe8L,0xd2c6e389f6e5eL,
        0x0caef480b5ac8L } },
    /* 241 */
    { { 0x5c97875315922L,0x713063cca5524L,0x64ef2cbd82951L,0xe236f3ce60d0bL,
        0x0d0ba177e8efaL },
      { 0x9ae8fb1b3af60L,0xe53d2da20e53aL,0xf9eef281a796aL,0xae1601d63605dL,
        0x0f31c957c1c54L } },
    /* 242 */
    { { 0x58d5249cc4597L,0xb0bae0a028c0fL,0x34a814adc5015L,0x7c3aefc5fc557L,
        0x0013404cb96e1L },
      { 0xe2585c9a824bfL,0x5e001eaed7b29L,0x1ef68acd59318L,0x3e6c8d6ee6826L,
        0x06f377c4b9193L } },
    /* 243 */
    { { 0x3bad1a8333fd2L,0x025a2a95b89f9L,0xaf75acea89302L,0x9506211e5037eL,
        0x06dba3e4ed2d0L },
      { 0xef98cd04399cdL,0x6ee6b73adea48L,0x17ecaf31811c6L,0xf4a772f60752cL,
        0x0f13cf3423becL } },
    /* 244 */
    { { 0xb9ec0a919e2ebL,0x95f62c0f68ceeL,0xaba229983a9a1L,0xbad3cfba3bb67L,
        0x0c83fa9a9274bL },
      { 0xd1b0b62fa1ce0L,0xf53418efbf0d7L,0x2706f04e58b60L,0x2683bfa8ef9e5L,
        0x0b49d70f45d70L } },
    /* 245 */
    { { 0xc7510fad5513bL,0xecb1751e2d914L,0x9fb9d5905f32eL,0xf1cf6d850418dL,
        0x059cfadbb0c30L },
      { 0x7ac2355cb7fd6L,0xb8820426a3e16L,0x0a78864249367L,0x4b67eaeec58c9L,
        0x05babf362354aL } },
    /* 246 */
    { { 0x981d1ee424865L,0x78f2e5577f37cL,0x9e0c0588b0028L,0xc8f0702970f1bL,
        0x06188c6a79026L },
      { 0x9a19bd0f244daL,0x5cfb08087306fL,0xf2136371eccedL,0xb9d935470f9b9L,
        0x0993fe475df50L } },
    /* 247 */
    { { 0x31cdf9b2c3609L,0xc02c46d4ea68eL,0xa77510184eb19L,0x616b7ac9ec1a9L,
        0x081f764664c80L },
      { 0xc2a5a75fbe978L,0xd3f183b3561d7L,0x01dd2bf6743feL,0x060d838d1f045L,
        0x0564a812a5fe9L } },
    /* 248 */
    { { 0xa64f4fa817d1dL,0x44bea82e0f7a5L,0xd57f9aa55f968L,0x1d6cb5ff5a0fcL,
        0x0226bf3cf00e5L },
      { 0x1a9f92f2833cfL,0x5a4f4f89a8d6dL,0xf3f7f7720a0a3L,0x783611536c498L,
        0x068779f47ff25L } },
    /* 249 */
    { { 0x0c1c173043d08L,0x741fc020fa79bL,0xa6d26d0a54467L,0x2e0bd3767e289L,
        0x097bcb0d1eb09L },
      { 0x6eaa8f32ed3c3L,0x51b281bc482abL,0xfa178f3c8a4f1L,0x46554d1bf4f3bL,
        0x0a872ffe80a78L } },
    /* 250 */
    { { 0xb7935a32b2086L,0x0e8160f486b1aL,0xb6ae6bee1eb71L,0xa36a9bd0cd913L,
        0x002812bfcb732L },
      { 0xfd7cacf605318L,0x50fdfd6d1da63L,0x102d619646e5dL,0x96afa1d683982L,
        0x007391cc9fe53L } },
    /* 251 */
    { { 0x157f08b80d02bL,0xd162877f7fc50L,0x8d542ae6b8333L,0x2a087aca1af87L,
        0x0355d2adc7e6dL },
      { 0xf335a287386e1L,0x94f8e43275b41L,0x79989eafd272aL,0x3a79286ca2cdeL,
        0x03dc2b1e37c2aL } },
    /* 252 */
    { { 0x9d21c04581352L,0x25376782bed68L,0xfed701f0a00c8L,0x846b203bd5909L,
        0x0c47869103ccdL },
      { 0xa770824c768edL,0x026841f6575dbL,0xaccce0e72feeaL,0x4d3273313ed56L,
        0x0ccc42968d5bbL } },
    /* 253 */
    { { 0x50de13d7620b9L,0x8a5992a56a94eL,0x75487c9d89a5cL,0x71cfdc0076406L,
        0x0e147eb42aa48L },
      { 0xab4eeacf3ae46L,0xfb50350fbe274L,0x8c840eafd4936L,0x96e3df2afe474L,
        0x0239ac047080eL } },
    /* 254 */
    { { 0xd1f352bfee8d4L,0xcffa7b0fec481L,0xce9af3cce80b5L,0xe59d105c4c9e2L,
        0x0c55fa1a3f5f7L },
      { 0x6f14e8257c227L,0x3f342be00b318L,0xa904fb2c5b165L,0xb69909afc998aL,
        0x0094cd99cd4f4L } },
    /* 255 */
    { { 0x81c84d703bebaL,0x5032ceb2918a9L,0x3bd49ec8631d1L,0xad33a445f2c9eL,
        0x0b90a30b642abL },
      { 0x5404fb4a5abf9L,0xc375db7603b46L,0xa35d89f004750L,0x24f76f9a42cccL,
        0x0019f8b9a1b79L } },
};

/* Multiply the base point of P256 by the scalar and return the result.
 * If map is true then convert result to affine coordinates.
 *
 * r     Resulting point.
 * k     Scalar to multiply by.
 * map   Indicates whether to convert result to affine.
 * ct    Constant time required.
 * heap  Heap to use for allocation.
 * returns MEMORY_E when memory allocation fails and MP_OKAY on success.
 */
static int sp_256_ecc_mulmod_base_5(sp_point_256* r, const sp_digit* k,
        int map, int ct, void* heap)
{
    return sp_256_ecc_mulmod_stripe_5(r, &p256_base, p256_table,
                                      k, map, ct, heap);
}

#endif

/* Multiply the base point of P256 by the scalar and return the result.
 * If map is true then convert result to affine coordinates.
 *
 * km    Scalar to multiply by.
 * r     Resulting point.
 * map   Indicates whether to convert result to affine.
 * heap  Heap to use for allocation.
 * returns MEMORY_E when memory allocation fails and MP_OKAY on success.
 */
int sp_ecc_mulmod_base_256(mp_int* km, ecc_point* r, int map, void* heap)
{
#if (!defined(WOLFSSL_SP_SMALL) && !defined(WOLFSSL_SMALL_STACK)) || defined(WOLFSSL_SP_NO_MALLOC)
    sp_point_256 p;
    sp_digit kd[5];
#endif
    sp_point_256* point;
    sp_digit* k = NULL;
    int err = MP_OKAY;

    err = sp_256_point_new_5(heap, p, point);
#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (err == MP_OKAY) {
        k = (sp_digit*)XMALLOC(sizeof(sp_digit) * 5, heap,
                                                              DYNAMIC_TYPE_ECC);
        if (k == NULL) {
            err = MEMORY_E;
        }
    }
#else
    k = kd;
#endif
    if (err == MP_OKAY) {
        sp_256_from_mp(k, 5, km);

            err = sp_256_ecc_mulmod_base_5(point, k, map, 1, heap);
    }
    if (err == MP_OKAY) {
        err = sp_256_point_to_ecc_point_5(point, r);
    }

#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (k != NULL) {
        XFREE(k, heap, DYNAMIC_TYPE_ECC);
    }
#endif
    sp_256_point_free_5(point, 0, heap);

    return err;
}

#if defined(WOLFSSL_VALIDATE_ECC_KEYGEN) || defined(HAVE_ECC_SIGN) || \
                                                        defined(HAVE_ECC_VERIFY)
/* Returns 1 if the number of zero.
 * Implementation is constant time.
 *
 * a  Number to check.
 * returns 1 if the number is zero and 0 otherwise.
 */
static int sp_256_iszero_5(const sp_digit* a)
{
    return (a[0] | a[1] | a[2] | a[3] | a[4]) == 0;
}

#endif /* WOLFSSL_VALIDATE_ECC_KEYGEN || HAVE_ECC_SIGN || HAVE_ECC_VERIFY */
/* Add 1 to a. (a = a + 1)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 */
SP_NOINLINE static void sp_256_add_one_5(sp_digit* a)
{
    a[0]++;
    sp_256_norm_5(a);
}

/* Read big endian unsigned byte array into r.
 *
 * r  A single precision integer.
 * size  Maximum number of bytes to convert
 * a  Byte array.
 * n  Number of bytes in array to read.
 */
static void sp_256_from_bin(sp_digit* r, int size, const byte* a, int n)
{
    int i, j = 0;
    word32 s = 0;

    r[0] = 0;
    for (i = n-1; i >= 0; i--) {
        r[j] |= (((sp_digit)a[i]) << s);
        if (s >= 44U) {
            r[j] &= 0xfffffffffffffL;
            s = 52U - s;
            if (j + 1 >= size) {
                break;
            }
            r[++j] = (sp_digit)a[i] >> s;
            s = 8U - s;
        }
        else {
            s += 8U;
        }
    }

    for (j++; j < size; j++) {
        r[j] = 0;
    }
}

/* Generates a scalar that is in the range 1..order-1.
 *
 * rng  Random number generator.
 * k    Scalar value.
 * returns RNG failures, MEMORY_E when memory allocation fails and
 * MP_OKAY on success.
 */
static int sp_256_ecc_gen_k_5(WC_RNG* rng, sp_digit* k)
{
    int err;
    byte buf[32];

    do {
        err = wc_RNG_GenerateBlock(rng, buf, sizeof(buf));
        if (err == 0) {
            sp_256_from_bin(k, 5, buf, (int)sizeof(buf));
            if (sp_256_cmp_5(k, p256_order2) < 0) {
                sp_256_add_one_5(k);
                break;
            }
        }
    }
    while (err == 0);

    return err;
}

/* Makes a random EC key pair.
 *
 * rng   Random number generator.
 * priv  Generated private value.
 * pub   Generated public point.
 * heap  Heap to use for allocation.
 * returns ECC_INF_E when the point does not have the correct order, RNG
 * failures, MEMORY_E when memory allocation fails and MP_OKAY on success.
 */
int sp_ecc_make_key_256(WC_RNG* rng, mp_int* priv, ecc_point* pub, void* heap)
{
#if (!defined(WOLFSSL_SP_SMALL) && !defined(WOLFSSL_SMALL_STACK)) || defined(WOLFSSL_SP_NO_MALLOC)
    sp_point_256 p;
    sp_digit kd[5];
#ifdef WOLFSSL_VALIDATE_ECC_KEYGEN
    sp_point_256 inf;
#endif
#endif
    sp_point_256* point;
    sp_digit* k = NULL;
#ifdef WOLFSSL_VALIDATE_ECC_KEYGEN
    sp_point_256* infinity = NULL;
#endif
    int err;

    (void)heap;

    err = sp_256_point_new_5(heap, p, point);
#ifdef WOLFSSL_VALIDATE_ECC_KEYGEN
    if (err == MP_OKAY) {
        err = sp_256_point_new_5(heap, inf, infinity);
    }
#endif
#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (err == MP_OKAY) {
        k = (sp_digit*)XMALLOC(sizeof(sp_digit) * 5, heap,
                                                              DYNAMIC_TYPE_ECC);
        if (k == NULL) {
            err = MEMORY_E;
        }
    }
#else
    k = kd;
#endif

    if (err == MP_OKAY) {
        err = sp_256_ecc_gen_k_5(rng, k);
    }
    if (err == MP_OKAY) {
            err = sp_256_ecc_mulmod_base_5(point, k, 1, 1, NULL);
    }

#ifdef WOLFSSL_VALIDATE_ECC_KEYGEN
    if (err == MP_OKAY) {
            err = sp_256_ecc_mulmod_5(infinity, point, p256_order, 1, 1, NULL);
    }
    if (err == MP_OKAY) {
        if (sp_256_iszero_5(point->x) || sp_256_iszero_5(point->y)) {
            err = ECC_INF_E;
        }
    }
#endif

    if (err == MP_OKAY) {
        err = sp_256_to_mp(k, priv);
    }
    if (err == MP_OKAY) {
        err = sp_256_point_to_ecc_point_5(point, pub);
    }

#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (k != NULL) {
        XFREE(k, heap, DYNAMIC_TYPE_ECC);
    }
#endif
#ifdef WOLFSSL_VALIDATE_ECC_KEYGEN
    sp_256_point_free_5(infinity, 1, heap);
#endif
    sp_256_point_free_5(point, 1, heap);

    return err;
}

#ifdef HAVE_ECC_DHE
/* Write r as big endian to byte array.
 * Fixed length number of bytes written: 32
 *
 * r  A single precision integer.
 * a  Byte array.
 */
static void sp_256_to_bin(sp_digit* r, byte* a)
{
    int i, j, s = 0, b;

    for (i=0; i<4; i++) {
        r[i+1] += r[i] >> 52;
        r[i] &= 0xfffffffffffffL;
    }
    j = 256 / 8 - 1;
    a[j] = 0;
    for (i=0; i<5 && j>=0; i++) {
        b = 0;
        /* lint allow cast of mismatch sp_digit and int */
        a[j--] |= (byte)(r[i] << s); /*lint !e9033*/
        b += 8 - s;
        if (j < 0) {
            break;
        }
        while (b < 52) {
            a[j--] = (byte)(r[i] >> b);
            b += 8;
            if (j < 0) {
                break;
            }
        }
        s = 8 - (b - 52);
        if (j >= 0) {
            a[j] = 0;
        }
        if (s != 0) {
            j++;
        }
    }
}

/* Multiply the point by the scalar and serialize the X ordinate.
 * The number is 0 padded to maximum size on output.
 *
 * priv    Scalar to multiply the point by.
 * pub     Point to multiply.
 * out     Buffer to hold X ordinate.
 * outLen  On entry, size of the buffer in bytes.
 *         On exit, length of data in buffer in bytes.
 * heap    Heap to use for allocation.
 * returns BUFFER_E if the buffer is to small for output size,
 * MEMORY_E when memory allocation fails and MP_OKAY on success.
 */
int sp_ecc_secret_gen_256(mp_int* priv, ecc_point* pub, byte* out,
                          word32* outLen, void* heap)
{
#if (!defined(WOLFSSL_SP_SMALL) && !defined(WOLFSSL_SMALL_STACK)) || defined(WOLFSSL_SP_NO_MALLOC)
    sp_point_256 p;
    sp_digit kd[5];
#endif
    sp_point_256* point = NULL;
    sp_digit* k = NULL;
    int err = MP_OKAY;

    if (*outLen < 32U) {
        err = BUFFER_E;
    }

    if (err == MP_OKAY) {
        err = sp_256_point_new_5(heap, p, point);
    }
#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (err == MP_OKAY) {
        k = (sp_digit*)XMALLOC(sizeof(sp_digit) * 5, heap,
                                                              DYNAMIC_TYPE_ECC);
        if (k == NULL)
            err = MEMORY_E;
    }
#else
    k = kd;
#endif

    if (err == MP_OKAY) {
        sp_256_from_mp(k, 5, priv);
        sp_256_point_from_ecc_point_5(point, pub);
            err = sp_256_ecc_mulmod_5(point, point, k, 1, 1, heap);
    }
    if (err == MP_OKAY) {
        sp_256_to_bin(point->x, out);
        *outLen = 32;
    }

#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (k != NULL) {
        XFREE(k, heap, DYNAMIC_TYPE_ECC);
    }
#endif
    sp_256_point_free_5(point, 0, heap);

    return err;
}
#endif /* HAVE_ECC_DHE */

#if defined(HAVE_ECC_SIGN) || defined(HAVE_ECC_VERIFY)
#endif
#if defined(HAVE_ECC_SIGN) || defined(HAVE_ECC_VERIFY)
/* Multiply a by scalar b into r. (r = a * b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A scalar.
 */
SP_NOINLINE static void sp_256_mul_d_5(sp_digit* r, const sp_digit* a,
    sp_digit b)
{
#ifdef WOLFSSL_SP_SMALL
    int128_t tb = b;
    int128_t t = 0;
    int i;

    for (i = 0; i < 5; i++) {
        t += tb * a[i];
        r[i] = t & 0xfffffffffffffL;
        t >>= 52;
    }
    r[5] = (sp_digit)t;
#else
    int128_t tb = b;
    int128_t t[5];

    t[ 0] = tb * a[ 0];
    t[ 1] = tb * a[ 1];
    t[ 2] = tb * a[ 2];
    t[ 3] = tb * a[ 3];
    t[ 4] = tb * a[ 4];
    r[ 0] =                           (t[ 0] & 0xfffffffffffffL);
    r[ 1] = (sp_digit)(t[ 0] >> 52) + (t[ 1] & 0xfffffffffffffL);
    r[ 2] = (sp_digit)(t[ 1] >> 52) + (t[ 2] & 0xfffffffffffffL);
    r[ 3] = (sp_digit)(t[ 2] >> 52) + (t[ 3] & 0xfffffffffffffL);
    r[ 4] = (sp_digit)(t[ 3] >> 52) + (t[ 4] & 0xfffffffffffffL);
    r[ 5] = (sp_digit)(t[ 4] >> 52);
#endif /* WOLFSSL_SP_SMALL */
}

#ifdef WOLFSSL_SP_DIV_64
static WC_INLINE sp_digit sp_256_div_word_5(sp_digit d1, sp_digit d0,
    sp_digit dv)
{
    sp_digit d, r, t;

    /* All 52 bits from d1 and top 11 bits from d0. */
    d = (d1 << 11) | (d0 >> 41);
    r = d / dv;
    d -= r * dv;
    /* Up to 12 bits in r */
    /* Next 11 bits from d0. */
    r <<= 11;
    d <<= 11;
    d |= (d0 >> 30) & ((1 << 11) - 1);
    t = d / dv;
    d -= t * dv;
    r += t;
    /* Up to 23 bits in r */
    /* Next 11 bits from d0. */
    r <<= 11;
    d <<= 11;
    d |= (d0 >> 19) & ((1 << 11) - 1);
    t = d / dv;
    d -= t * dv;
    r += t;
    /* Up to 34 bits in r */
    /* Next 11 bits from d0. */
    r <<= 11;
    d <<= 11;
    d |= (d0 >> 8) & ((1 << 11) - 1);
    t = d / dv;
    d -= t * dv;
    r += t;
    /* Up to 45 bits in r */
    /* Remaining 8 bits from d0. */
    r <<= 8;
    d <<= 8;
    d |= d0 & ((1 << 8) - 1);
    t = d / dv;
    r += t;

    return r;
}
#endif /* WOLFSSL_SP_DIV_64 */

/* Divide d in a and put remainder into r (m*d + r = a)
 * m is not calculated as it is not needed at this time.
 *
 * a  Number to be divided.
 * d  Number to divide with.
 * m  Multiplier result.
 * r  Remainder from the division.
 * returns MEMORY_E when unable to allocate memory and MP_OKAY otherwise.
 */
static int sp_256_div_5(const sp_digit* a, const sp_digit* d, sp_digit* m,
        sp_digit* r)
{
    int i;
#ifndef WOLFSSL_SP_DIV_64
    int128_t d1;
#endif
    sp_digit dv, r1;
#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    sp_digit* td;
#else
    sp_digit t1d[10], t2d[5 + 1];
#endif
    sp_digit* t1;
    sp_digit* t2;
    int err = MP_OKAY;

    (void)m;

#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    td = (sp_digit*)XMALLOC(sizeof(sp_digit) * (3 * 5 + 1), NULL,
                                                       DYNAMIC_TYPE_TMP_BUFFER);
    if (td == NULL) {
        err = MEMORY_E;
    }
#endif

    if (err == MP_OKAY) {
#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
        t1 = td;
        t2 = td + 2 * 5;
#else
        t1 = t1d;
        t2 = t2d;
#endif

        dv = d[4];
        XMEMCPY(t1, a, sizeof(*t1) * 2U * 5U);
        for (i=4; i>=0; i--) {
            t1[5 + i] += t1[5 + i - 1] >> 52;
            t1[5 + i - 1] &= 0xfffffffffffffL;
#ifndef WOLFSSL_SP_DIV_64
            d1 = t1[5 + i];
            d1 <<= 52;
            d1 += t1[5 + i - 1];
            r1 = (sp_digit)(d1 / dv);
#else
            r1 = sp_256_div_word_5(t1[5 + i], t1[5 + i - 1], dv);
#endif

            sp_256_mul_d_5(t2, d, r1);
            (void)sp_256_sub_5(&t1[i], &t1[i], t2);
            t1[5 + i] -= t2[5];
            t1[5 + i] += t1[5 + i - 1] >> 52;
            t1[5 + i - 1] &= 0xfffffffffffffL;
            r1 = (((-t1[5 + i]) << 52) - t1[5 + i - 1]) / dv;
            r1++;
            sp_256_mul_d_5(t2, d, r1);
            (void)sp_256_add_5(&t1[i], &t1[i], t2);
            t1[5 + i] += t1[5 + i - 1] >> 52;
            t1[5 + i - 1] &= 0xfffffffffffffL;
        }
        t1[5 - 1] += t1[5 - 2] >> 52;
        t1[5 - 2] &= 0xfffffffffffffL;
        r1 = t1[5 - 1] / dv;

        sp_256_mul_d_5(t2, d, r1);
        (void)sp_256_sub_5(t1, t1, t2);
        XMEMCPY(r, t1, sizeof(*r) * 2U * 5U);
        for (i=0; i<4; i++) {
            r[i+1] += r[i] >> 52;
            r[i] &= 0xfffffffffffffL;
        }
        sp_256_cond_add_5(r, r, d, 0 - ((r[4] < 0) ?
                    (sp_digit)1 : (sp_digit)0));
    }

#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (td != NULL) {
        XFREE(td, NULL, DYNAMIC_TYPE_TMP_BUFFER);
    }
#endif

    return err;
}

/* Reduce a modulo m into r. (r = a mod m)
 *
 * r  A single precision number that is the reduced result.
 * a  A single precision number that is to be reduced.
 * m  A single precision number that is the modulus to reduce with.
 * returns MEMORY_E when unable to allocate memory and MP_OKAY otherwise.
 */
static int sp_256_mod_5(sp_digit* r, const sp_digit* a, const sp_digit* m)
{
    return sp_256_div_5(a, m, NULL, r);
}

#endif
#if defined(HAVE_ECC_SIGN) || defined(HAVE_ECC_VERIFY)
#ifdef WOLFSSL_SP_SMALL
/* Order-2 for the P256 curve. */
static const uint64_t p256_order_minus_2[4] = {
    0xf3b9cac2fc63254fU,0xbce6faada7179e84U,0xffffffffffffffffU,
    0xffffffff00000000U
};
#else
/* The low half of the order-2 of the P256 curve. */
static const uint64_t p256_order_low[2] = {
    0xf3b9cac2fc63254fU,0xbce6faada7179e84U
};
#endif /* WOLFSSL_SP_SMALL */

/* Multiply two number mod the order of P256 curve. (r = a * b mod order)
 *
 * r  Result of the multiplication.
 * a  First operand of the multiplication.
 * b  Second operand of the multiplication.
 */
static void sp_256_mont_mul_order_5(sp_digit* r, const sp_digit* a, const sp_digit* b)
{
    sp_256_mul_5(r, a, b);
    sp_256_mont_reduce_order_5(r, p256_order, p256_mp_order);
}

/* Square number mod the order of P256 curve. (r = a * a mod order)
 *
 * r  Result of the squaring.
 * a  Number to square.
 */
static void sp_256_mont_sqr_order_5(sp_digit* r, const sp_digit* a)
{
    sp_256_sqr_5(r, a);
    sp_256_mont_reduce_order_5(r, p256_order, p256_mp_order);
}

#ifndef WOLFSSL_SP_SMALL
/* Square number mod the order of P256 curve a number of times.
 * (r = a ^ n mod order)
 *
 * r  Result of the squaring.
 * a  Number to square.
 */
static void sp_256_mont_sqr_n_order_5(sp_digit* r, const sp_digit* a, int n)
{
    int i;

    sp_256_mont_sqr_order_5(r, a);
    for (i=1; i<n; i++) {
        sp_256_mont_sqr_order_5(r, r);
    }
}
#endif /* !WOLFSSL_SP_SMALL */

/* Invert the number, in Montgomery form, modulo the order of the P256 curve.
 * (r = 1 / a mod order)
 *
 * r   Inverse result.
 * a   Number to invert.
 * td  Temporary data.
 */

#ifdef WOLFSSL_SP_NONBLOCK
typedef struct sp_256_mont_inv_order_5_ctx {
    int state;
    int i;
} sp_256_mont_inv_order_5_ctx;
static int sp_256_mont_inv_order_5_nb(sp_ecc_ctx_t* sp_ctx, sp_digit* r, const sp_digit* a,
        sp_digit* t)
{
    int err = FP_WOULDBLOCK;
    sp_256_mont_inv_order_5_ctx* ctx = (sp_256_mont_inv_order_5_ctx*)sp_ctx;
    
    typedef char ctx_size_test[sizeof(sp_256_mont_inv_order_5_ctx) >= sizeof(*sp_ctx) ? -1 : 1];
    (void)sizeof(ctx_size_test);

    switch (ctx->state) {
    case 0:
        XMEMCPY(t, a, sizeof(sp_digit) * 5);
        ctx->i = 254;
        ctx->state = 1;
        break;
    case 1:
        sp_256_mont_sqr_order_5(t, t);
        ctx->state = 2;
        break;
    case 2:
        if ((p256_order_minus_2[ctx->i / 64] & ((sp_int_digit)1 << (ctx->i % 64))) != 0) {
            sp_256_mont_mul_order_5(t, t, a);
        }
        ctx->i--;
        ctx->state = (ctx->i == 0) ? 3 : 1;
        break;
    case 3:
        XMEMCPY(r, t, sizeof(sp_digit) * 5U);
        err = MP_OKAY;
        break;
    }
    return err;
}
#endif /* WOLFSSL_SP_NONBLOCK */

static void sp_256_mont_inv_order_5(sp_digit* r, const sp_digit* a,
        sp_digit* td)
{
#ifdef WOLFSSL_SP_SMALL
    sp_digit* t = td;
    int i;

    XMEMCPY(t, a, sizeof(sp_digit) * 5);
    for (i=254; i>=0; i--) {
        sp_256_mont_sqr_order_5(t, t);
        if ((p256_order_minus_2[i / 64] & ((sp_int_digit)1 << (i % 64))) != 0) {
            sp_256_mont_mul_order_5(t, t, a);
        }
    }
    XMEMCPY(r, t, sizeof(sp_digit) * 5U);
#else
    sp_digit* t = td;
    sp_digit* t2 = td + 2 * 5;
    sp_digit* t3 = td + 4 * 5;
    int i;

    /* t = a^2 */
    sp_256_mont_sqr_order_5(t, a);
    /* t = a^3 = t * a */
    sp_256_mont_mul_order_5(t, t, a);
    /* t2= a^c = t ^ 2 ^ 2 */
    sp_256_mont_sqr_n_order_5(t2, t, 2);
    /* t3= a^f = t2 * t */
    sp_256_mont_mul_order_5(t3, t2, t);
    /* t2= a^f0 = t3 ^ 2 ^ 4 */
    sp_256_mont_sqr_n_order_5(t2, t3, 4);
    /* t = a^ff = t2 * t3 */
    sp_256_mont_mul_order_5(t, t2, t3);
    /* t3= a^ff00 = t ^ 2 ^ 8 */
    sp_256_mont_sqr_n_order_5(t2, t, 8);
    /* t = a^ffff = t2 * t */
    sp_256_mont_mul_order_5(t, t2, t);
    /* t2= a^ffff0000 = t ^ 2 ^ 16 */
    sp_256_mont_sqr_n_order_5(t2, t, 16);
    /* t = a^ffffffff = t2 * t */
    sp_256_mont_mul_order_5(t, t2, t);
    /* t2= a^ffffffff0000000000000000 = t ^ 2 ^ 64  */
    sp_256_mont_sqr_n_order_5(t2, t, 64);
    /* t2= a^ffffffff00000000ffffffff = t2 * t */
    sp_256_mont_mul_order_5(t2, t2, t);
    /* t2= a^ffffffff00000000ffffffff00000000 = t2 ^ 2 ^ 32  */
    sp_256_mont_sqr_n_order_5(t2, t2, 32);
    /* t2= a^ffffffff00000000ffffffffffffffff = t2 * t */
    sp_256_mont_mul_order_5(t2, t2, t);
    /* t2= a^ffffffff00000000ffffffffffffffffbce6 */
    for (i=127; i>=112; i--) {
        sp_256_mont_sqr_order_5(t2, t2);
        if (((sp_digit)p256_order_low[i / 64] & ((sp_int_digit)1 << (i % 64))) != 0) {
            sp_256_mont_mul_order_5(t2, t2, a);
        }
    }
    /* t2= a^ffffffff00000000ffffffffffffffffbce6f */
    sp_256_mont_sqr_n_order_5(t2, t2, 4);
    sp_256_mont_mul_order_5(t2, t2, t3);
    /* t2= a^ffffffff00000000ffffffffffffffffbce6faada7179e84 */
    for (i=107; i>=64; i--) {
        sp_256_mont_sqr_order_5(t2, t2);
        if (((sp_digit)p256_order_low[i / 64] & ((sp_int_digit)1 << (i % 64))) != 0) {
            sp_256_mont_mul_order_5(t2, t2, a);
        }
    }
    /* t2= a^ffffffff00000000ffffffffffffffffbce6faada7179e84f */
    sp_256_mont_sqr_n_order_5(t2, t2, 4);
    sp_256_mont_mul_order_5(t2, t2, t3);
    /* t2= a^ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2 */
    for (i=59; i>=32; i--) {
        sp_256_mont_sqr_order_5(t2, t2);
        if (((sp_digit)p256_order_low[i / 64] & ((sp_int_digit)1 << (i % 64))) != 0) {
            sp_256_mont_mul_order_5(t2, t2, a);
        }
    }
    /* t2= a^ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2f */
    sp_256_mont_sqr_n_order_5(t2, t2, 4);
    sp_256_mont_mul_order_5(t2, t2, t3);
    /* t2= a^ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc63254 */
    for (i=27; i>=0; i--) {
        sp_256_mont_sqr_order_5(t2, t2);
        if (((sp_digit)p256_order_low[i / 64] & ((sp_int_digit)1 << (i % 64))) != 0) {
            sp_256_mont_mul_order_5(t2, t2, a);
        }
    }
    /* t2= a^ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632540 */
    sp_256_mont_sqr_n_order_5(t2, t2, 4);
    /* r = a^ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc63254f */
    sp_256_mont_mul_order_5(r, t2, t3);
#endif /* WOLFSSL_SP_SMALL */
}

#endif /* HAVE_ECC_SIGN || HAVE_ECC_VERIFY */
#ifdef HAVE_ECC_SIGN
#ifndef SP_ECC_MAX_SIG_GEN
#define SP_ECC_MAX_SIG_GEN  64
#endif

/* Sign the hash using the private key.
 *   e = [hash, 256 bits] from binary
 *   r = (k.G)->x mod order
 *   s = (r * x + e) / k mod order
 * The hash is truncated to the first 256 bits.
 *
 * hash     Hash to sign.
 * hashLen  Length of the hash data.
 * rng      Random number generator.
 * priv     Private part of key - scalar.
 * rm       First part of result as an mp_int.
 * sm       Sirst part of result as an mp_int.
 * heap     Heap to use for allocation.
 * returns RNG failures, MEMORY_E when memory allocation fails and
 * MP_OKAY on success.
 */
#ifdef WOLFSSL_SP_NONBLOCK
typedef struct sp_ecc_sign_256_ctx {
    int state;
    union {
        sp_256_ecc_mulmod_5_ctx mulmod_ctx;
        sp_256_mont_inv_order_5_ctx mont_inv_order_ctx;
    };
    sp_digit e[2*5];
    sp_digit x[2*5];
    sp_digit k[2*5];
    sp_digit r[2*5];
    sp_digit tmp[3 * 2*5];
    sp_point_256 point;
    sp_digit* s;
    sp_digit* kInv;
    int i;
} sp_ecc_sign_256_ctx;

int sp_ecc_sign_256_nb(sp_ecc_ctx_t* sp_ctx, const byte* hash, word32 hashLen, WC_RNG* rng, mp_int* priv,
                    mp_int* rm, mp_int* sm, mp_int* km, void* heap)
{
    int err = FP_WOULDBLOCK;
    sp_ecc_sign_256_ctx* ctx = (sp_ecc_sign_256_ctx*)sp_ctx->data;

    typedef char ctx_size_test[sizeof(sp_ecc_sign_256_ctx) >= sizeof(*sp_ctx) ? -1 : 1];
    (void)sizeof(ctx_size_test);

    (void)heap;

    switch (ctx->state) {
    case 0: /* INIT */
        ctx->s = ctx->e;
        ctx->kInv = ctx->k;
        if (hashLen > 32U) {
            hashLen = 32U;
        }

        sp_256_from_bin(ctx->e, 5, hash, (int)hashLen);

        ctx->i = SP_ECC_MAX_SIG_GEN;
        ctx->state = 1;
        break;
    case 1: /* GEN */
        sp_256_from_mp(ctx->x, 5, priv);
        /* New random point. */
        if (km == NULL || mp_iszero(km)) {
            err = sp_256_ecc_gen_k_5(rng, ctx->k);
        }
        else {
            sp_256_from_mp(ctx->k, 5, km);
            mp_zero(km);
        }
        XMEMSET(&ctx->mulmod_ctx, 0, sizeof(ctx->mulmod_ctx));
        ctx->state = 2;
        break; 
    case 2: /* MULMOD */
        err = sp_256_ecc_mulmod_5_nb((sp_ecc_ctx_t*)&ctx->mulmod_ctx, 
            &ctx->point, &p256_base, ctx->k, 1, 1, heap);
        if (err == MP_OKAY) {
            ctx->state = 3;
        }
        break;
    case 3: /* MODORDER */
    {
        int64_t c;
        /* r = point->x mod order */
        XMEMCPY(ctx->r, ctx->point.x, sizeof(sp_digit) * 5U);
        sp_256_norm_5(ctx->r);
        c = sp_256_cmp_5(ctx->r, p256_order);
        sp_256_cond_sub_5(ctx->r, ctx->r, p256_order, 0L - (sp_digit)(c >= 0));
        sp_256_norm_5(ctx->r);
        ctx->state = 4;
        break;
    }
    case 4: /* KMODORDER */
        /* Conv k to Montgomery form (mod order) */
        sp_256_mul_5(ctx->k, ctx->k, p256_norm_order);
        err = sp_256_mod_5(ctx->k, ctx->k, p256_order);
        if (err == MP_OKAY) {
            sp_256_norm_5(ctx->k);
            XMEMSET(&ctx->mont_inv_order_ctx, 0, sizeof(ctx->mont_inv_order_ctx));
            ctx->state = 5;
        }
        break;
    case 5: /* KINV */
        /* kInv = 1/k mod order */
        err = sp_256_mont_inv_order_5_nb((sp_ecc_ctx_t*)&ctx->mont_inv_order_ctx, ctx->kInv, ctx->k, ctx->tmp);
        if (err == MP_OKAY) {
            XMEMSET(&ctx->mont_inv_order_ctx, 0, sizeof(ctx->mont_inv_order_ctx));
            ctx->state = 6;
        }
        break;
    case 6: /* KINVNORM */
        sp_256_norm_5(ctx->kInv);
        ctx->state = 7;
        break;
    case 7: /* R */
        /* s = r * x + e */
        sp_256_mul_5(ctx->x, ctx->x, ctx->r);
        ctx->state = 8;
        break;
    case 8: /* S1 */
        err = sp_256_mod_5(ctx->x, ctx->x, p256_order);
        if (err == MP_OKAY)
            ctx->state = 9;
        break;
    case 9: /* S2 */
    {
        sp_digit carry;
        int64_t c;
        sp_256_norm_5(ctx->x);
        carry = sp_256_add_5(ctx->s, ctx->e, ctx->x);
        sp_256_cond_sub_5(ctx->s, ctx->s, p256_order, 0 - carry);
        sp_256_norm_5(ctx->s);
        c = sp_256_cmp_5(ctx->s, p256_order);
        sp_256_cond_sub_5(ctx->s, ctx->s, p256_order, 0L - (sp_digit)(c >= 0));
        sp_256_norm_5(ctx->s);

        /* s = s * k^-1 mod order */
        sp_256_mont_mul_order_5(ctx->s, ctx->s, ctx->kInv);
        sp_256_norm_5(ctx->s);

        /* Check that signature is usable. */
        if (sp_256_iszero_5(ctx->s) == 0) {
            ctx->state = 10;
            break;
        }

        /* not usable gen, try again */
        ctx->i--;
        if (ctx->i == 0) {
            err = RNG_FAILURE_E;
        }
        ctx->state = 1;
        break;
    }
    case 10: /* RES */
        err = sp_256_to_mp(ctx->r, rm);
        if (err == MP_OKAY) {
            err = sp_256_to_mp(ctx->s, sm);
        }
        break;
    }

    if (err == MP_OKAY && ctx->state != 10) {
        err = FP_WOULDBLOCK;
    }
    if (err != FP_WOULDBLOCK) {
        XMEMSET(ctx->e, 0, sizeof(sp_digit) * 2U * 5U);
        XMEMSET(ctx->x, 0, sizeof(sp_digit) * 2U * 5U);
        XMEMSET(ctx->k, 0, sizeof(sp_digit) * 2U * 5U);
        XMEMSET(ctx->r, 0, sizeof(sp_digit) * 2U * 5U);
        XMEMSET(ctx->tmp, 0, sizeof(sp_digit) * 3U * 2U * 5U);
    }

    return err;
}
#endif /* WOLFSSL_SP_NONBLOCK */

int sp_ecc_sign_256(const byte* hash, word32 hashLen, WC_RNG* rng, mp_int* priv,
                    mp_int* rm, mp_int* sm, mp_int* km, void* heap)
{
#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    sp_digit* d = NULL;
#else
    sp_digit ed[2*5];
    sp_digit xd[2*5];
    sp_digit kd[2*5];
    sp_digit rd[2*5];
    sp_digit td[3 * 2*5];
    sp_point_256 p;
#endif
    sp_digit* e = NULL;
    sp_digit* x = NULL;
    sp_digit* k = NULL;
    sp_digit* r = NULL;
    sp_digit* tmp = NULL;
    sp_point_256* point = NULL;
    sp_digit carry;
    sp_digit* s = NULL;
    sp_digit* kInv = NULL;
    int err = MP_OKAY;
    int64_t c;
    int i;

    (void)heap;

    err = sp_256_point_new_5(heap, p, point);
#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (err == MP_OKAY) {
        d = (sp_digit*)XMALLOC(sizeof(sp_digit) * 7 * 2 * 5, heap,
                                                              DYNAMIC_TYPE_ECC);
        if (d == NULL) {
            err = MEMORY_E;
        }
    }
#endif

    if (err == MP_OKAY) {
#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
        e = d + 0 * 5;
        x = d + 2 * 5;
        k = d + 4 * 5;
        r = d + 6 * 5;
        tmp = d + 8 * 5;
#else
        e = ed;
        x = xd;
        k = kd;
        r = rd;
        tmp = td;
#endif
        s = e;
        kInv = k;

        if (hashLen > 32U) {
            hashLen = 32U;
        }

        sp_256_from_bin(e, 5, hash, (int)hashLen);
    }

    for (i = SP_ECC_MAX_SIG_GEN; err == MP_OKAY && i > 0; i--) {
        sp_256_from_mp(x, 5, priv);

        /* New random point. */
        if (km == NULL || mp_iszero(km)) {
            err = sp_256_ecc_gen_k_5(rng, k);
        }
        else {
            sp_256_from_mp(k, 5, km);
            mp_zero(km);
        }
        if (err == MP_OKAY) {
                err = sp_256_ecc_mulmod_base_5(point, k, 1, 1, NULL);
        }

        if (err == MP_OKAY) {
            /* r = point->x mod order */
            XMEMCPY(r, point->x, sizeof(sp_digit) * 5U);
            sp_256_norm_5(r);
            c = sp_256_cmp_5(r, p256_order);
            sp_256_cond_sub_5(r, r, p256_order, 0L - (sp_digit)(c >= 0));
            sp_256_norm_5(r);

            /* Conv k to Montgomery form (mod order) */
                sp_256_mul_5(k, k, p256_norm_order);
            err = sp_256_mod_5(k, k, p256_order);
        }
        if (err == MP_OKAY) {
            sp_256_norm_5(k);
            /* kInv = 1/k mod order */
                sp_256_mont_inv_order_5(kInv, k, tmp);
            sp_256_norm_5(kInv);

            /* s = r * x + e */
                sp_256_mul_5(x, x, r);
            err = sp_256_mod_5(x, x, p256_order);
        }
        if (err == MP_OKAY) {
            sp_256_norm_5(x);
            carry = sp_256_add_5(s, e, x);
            sp_256_cond_sub_5(s, s, p256_order, 0 - carry);
            sp_256_norm_5(s);
            c = sp_256_cmp_5(s, p256_order);
            sp_256_cond_sub_5(s, s, p256_order, 0L - (sp_digit)(c >= 0));
            sp_256_norm_5(s);

            /* s = s * k^-1 mod order */
                sp_256_mont_mul_order_5(s, s, kInv);
            sp_256_norm_5(s);

            /* Check that signature is usable. */
            if (sp_256_iszero_5(s) == 0) {
                break;
            }
        }
    }

    if (i == 0) {
        err = RNG_FAILURE_E;
    }

    if (err == MP_OKAY) {
        err = sp_256_to_mp(r, rm);
    }
    if (err == MP_OKAY) {
        err = sp_256_to_mp(s, sm);
    }

#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (d != NULL) {
        XMEMSET(d, 0, sizeof(sp_digit) * 8 * 5);
        XFREE(d, heap, DYNAMIC_TYPE_ECC);
    }
#else
    XMEMSET(e, 0, sizeof(sp_digit) * 2U * 5U);
    XMEMSET(x, 0, sizeof(sp_digit) * 2U * 5U);
    XMEMSET(k, 0, sizeof(sp_digit) * 2U * 5U);
    XMEMSET(r, 0, sizeof(sp_digit) * 2U * 5U);
    XMEMSET(r, 0, sizeof(sp_digit) * 2U * 5U);
    XMEMSET(tmp, 0, sizeof(sp_digit) * 3U * 2U * 5U);
#endif
    sp_256_point_free_5(point, 1, heap);

    return err;
}
#endif /* HAVE_ECC_SIGN */

#ifdef HAVE_ECC_VERIFY
/* Verify the signature values with the hash and public key.
 *   e = Truncate(hash, 256)
 *   u1 = e/s mod order
 *   u2 = r/s mod order
 *   r == (u1.G + u2.Q)->x mod order
 * Optimization: Leave point in projective form.
 *   (x, y, 1) == (x' / z'*z', y' / z'*z'*z', z' / z')
 *   (r + n*order).z'.z' mod prime == (u1.G + u2.Q)->x'
 * The hash is truncated to the first 256 bits.
 *
 * hash     Hash to sign.
 * hashLen  Length of the hash data.
 * rng      Random number generator.
 * priv     Private part of key - scalar.
 * rm       First part of result as an mp_int.
 * sm       Sirst part of result as an mp_int.
 * heap     Heap to use for allocation.
 * returns RNG failures, MEMORY_E when memory allocation fails and
 * MP_OKAY on success.
 */
#ifdef WOLFSSL_SP_NONBLOCK
typedef struct sp_ecc_verify_256_ctx {
    int state;
    union {
        sp_256_ecc_mulmod_5_ctx mulmod_ctx;
        sp_256_mont_inv_order_5_ctx mont_inv_order_ctx;
        sp_256_proj_point_dbl_5_ctx dbl_ctx;
        sp_256_proj_point_add_5_ctx add_ctx;
    };
    sp_digit u1[2*5];
    sp_digit u2[2*5];
    sp_digit s[2*5];
    sp_digit tmp[2*5 * 5];
    sp_point_256 p1;
    sp_point_256 p2;
} sp_ecc_verify_256_ctx;

int sp_ecc_verify_256_nb(sp_ecc_ctx_t* sp_ctx, const byte* hash, word32 hashLen, mp_int* pX,
    mp_int* pY, mp_int* pZ, mp_int* r, mp_int* sm, int* res, void* heap)
{
    int err = FP_WOULDBLOCK;
    sp_ecc_verify_256_ctx* ctx = (sp_ecc_verify_256_ctx*)sp_ctx->data;

    typedef char ctx_size_test[sizeof(sp_ecc_verify_256_ctx) >= sizeof(*sp_ctx) ? -1 : 1];
    (void)sizeof(ctx_size_test);

    switch (ctx->state) {
    case 0: /* INIT */
        if (hashLen > 32U) {
            hashLen = 32U;
        }

        sp_256_from_bin(ctx->u1, 5, hash, (int)hashLen);
        sp_256_from_mp(ctx->u2, 5, r);
        sp_256_from_mp(ctx->s, 5, sm);
        sp_256_from_mp(ctx->p2.x, 5, pX);
        sp_256_from_mp(ctx->p2.y, 5, pY);
        sp_256_from_mp(ctx->p2.z, 5, pZ);
        ctx->state = 1;
        break;
    case 1: /* NORMS0 */
        sp_256_mul_5(ctx->s, ctx->s, p256_norm_order);
        err = sp_256_mod_5(ctx->s, ctx->s, p256_order);
        if (err == MP_OKAY)
            ctx->state = 2;
        break;
    case 2: /* NORMS1 */
        sp_256_norm_5(ctx->s);
        XMEMSET(&ctx->mont_inv_order_ctx, 0, sizeof(ctx->mont_inv_order_ctx));
        ctx->state = 3;
        break;
    case 3: /* NORMS2 */
        err = sp_256_mont_inv_order_5_nb((sp_ecc_ctx_t*)&ctx->mont_inv_order_ctx, ctx->s, ctx->s, ctx->tmp);
        if (err == MP_OKAY) {
            ctx->state = 4;
        }
        break;
    case 4: /* NORMS3 */
        sp_256_mont_mul_order_5(ctx->u1, ctx->u1, ctx->s);
        ctx->state = 5;
        break;
    case 5: /* NORMS4 */
        sp_256_mont_mul_order_5(ctx->u2, ctx->u2, ctx->s);
        XMEMSET(&ctx->mulmod_ctx, 0, sizeof(ctx->mulmod_ctx));
        ctx->state = 6;
        break;
    case 6: /* MULBASE */
        err = sp_256_ecc_mulmod_5_nb((sp_ecc_ctx_t*)&ctx->mulmod_ctx, &ctx->p1, &p256_base, ctx->u1, 0, 0, heap);
        if (err == MP_OKAY) {
            XMEMSET(&ctx->mulmod_ctx, 0, sizeof(ctx->mulmod_ctx));
            ctx->state = 7;
        }
        break;
    case 7: /* MULMOD */
        err = sp_256_ecc_mulmod_5_nb((sp_ecc_ctx_t*)&ctx->mulmod_ctx, &ctx->p2, &ctx->p2, ctx->u2, 0, 0, heap);
        if (err == MP_OKAY) {
            XMEMSET(&ctx->add_ctx, 0, sizeof(ctx->add_ctx));
            ctx->state = 8;
        }
        break;
    case 8: /* ADD */
        err = sp_256_proj_point_add_5_nb((sp_ecc_ctx_t*)&ctx->add_ctx, &ctx->p1, &ctx->p1, &ctx->p2, ctx->tmp);
        if (err == MP_OKAY)
            ctx->state = 9;
        break;
    case 9: /* DBLPREP */
        if (sp_256_iszero_5(ctx->p1.z)) {
            if (sp_256_iszero_5(ctx->p1.x) && sp_256_iszero_5(ctx->p1.y)) {
                XMEMSET(&ctx->dbl_ctx, 0, sizeof(ctx->dbl_ctx));
                ctx->state = 10;
                break;
            }
            else {
                /* Y ordinate is not used from here - don't set. */
                int i;
                for (i=0; i<5; i++) {
                    ctx->p1.x[i] = 0;
                }
                XMEMCPY(ctx->p1.z, p256_norm_mod, sizeof(p256_norm_mod));
            }
        }
        ctx->state = 11;
        break;
    case 10: /* DBL */
        err = sp_256_proj_point_dbl_5_nb((sp_ecc_ctx_t*)&ctx->dbl_ctx, &ctx->p1, 
            &ctx->p2, ctx->tmp);
        if (err == MP_OKAY) {
            ctx->state = 11;
        }
        break;
    case 11: /* MONT */
        /* (r + n*order).z'.z' mod prime == (u1.G + u2.Q)->x' */
        /* Reload r and convert to Montgomery form. */
        sp_256_from_mp(ctx->u2, 5, r);
        err = sp_256_mod_mul_norm_5(ctx->u2, ctx->u2, p256_mod);
        if (err == MP_OKAY)
            ctx->state = 12;
        break;
    case 12: /* SQR */
        /* u1 = r.z'.z' mod prime */
        sp_256_mont_sqr_5(ctx->p1.z, ctx->p1.z, p256_mod, p256_mp_mod);
        ctx->state = 13;
        break;
    case 13: /* MUL */
        sp_256_mont_mul_5(ctx->u1, ctx->u2, ctx->p1.z, p256_mod, p256_mp_mod);
        ctx->state = 14;
        break;
    case 14: /* RES */
        err = MP_OKAY; /* math okay, now check result */
        *res = (int)(sp_256_cmp_5(ctx->p1.x, ctx->u1) == 0);
        if (*res == 0) {
            sp_digit carry;
            int64_t c;

            /* Reload r and add order. */
            sp_256_from_mp(ctx->u2, 5, r);
            carry = sp_256_add_5(ctx->u2, ctx->u2, p256_order);
            /* Carry means result is greater than mod and is not valid. */
            if (carry == 0) {
                sp_256_norm_5(ctx->u2);

                /* Compare with mod and if greater or equal then not valid. */
                c = sp_256_cmp_5(ctx->u2, p256_mod);
                if (c < 0) {
                    /* Convert to Montogomery form */
                    err = sp_256_mod_mul_norm_5(ctx->u2, ctx->u2, p256_mod);
                    if (err == MP_OKAY) {
                        /* u1 = (r + 1*order).z'.z' mod prime */
                        sp_256_mont_mul_5(ctx->u1, ctx->u2, ctx->p1.z, p256_mod,
                                                                  p256_mp_mod);
                        *res = (int)(sp_256_cmp_5(ctx->p1.x, ctx->u1) == 0);
                    }
                }
            }
        }
        break;
    }

    if (err == MP_OKAY && ctx->state != 14) {
        err = FP_WOULDBLOCK;
    }

    return err;
}
#endif /* WOLFSSL_SP_NONBLOCK */

int sp_ecc_verify_256(const byte* hash, word32 hashLen, mp_int* pX,
    mp_int* pY, mp_int* pZ, mp_int* r, mp_int* sm, int* res, void* heap)
{
#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    sp_digit* d = NULL;
#else
    sp_digit u1d[2*5];
    sp_digit u2d[2*5];
    sp_digit sd[2*5];
    sp_digit tmpd[2*5 * 5];
    sp_point_256 p1d;
    sp_point_256 p2d;
#endif
    sp_digit* u1 = NULL;
    sp_digit* u2 = NULL;
    sp_digit* s = NULL;
    sp_digit* tmp = NULL;
    sp_point_256* p1;
    sp_point_256* p2 = NULL;
    sp_digit carry;
    int64_t c;
    int err;

    err = sp_256_point_new_5(heap, p1d, p1);
    if (err == MP_OKAY) {
        err = sp_256_point_new_5(heap, p2d, p2);
    }
#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (err == MP_OKAY) {
        d = (sp_digit*)XMALLOC(sizeof(sp_digit) * 16 * 5, heap,
                                                              DYNAMIC_TYPE_ECC);
        if (d == NULL) {
            err = MEMORY_E;
        }
    }
#endif

    if (err == MP_OKAY) {
#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
        u1  = d + 0 * 5;
        u2  = d + 2 * 5;
        s   = d + 4 * 5;
        tmp = d + 6 * 5;
#else
        u1 = u1d;
        u2 = u2d;
        s  = sd;
        tmp = tmpd;
#endif

        if (hashLen > 32U) {
            hashLen = 32U;
        }

        sp_256_from_bin(u1, 5, hash, (int)hashLen);
        sp_256_from_mp(u2, 5, r);
        sp_256_from_mp(s, 5, sm);
        sp_256_from_mp(p2->x, 5, pX);
        sp_256_from_mp(p2->y, 5, pY);
        sp_256_from_mp(p2->z, 5, pZ);

        {
            sp_256_mul_5(s, s, p256_norm_order);
        }
        err = sp_256_mod_5(s, s, p256_order);
    }
    if (err == MP_OKAY) {
        sp_256_norm_5(s);
        {
            sp_256_mont_inv_order_5(s, s, tmp);
            sp_256_mont_mul_order_5(u1, u1, s);
            sp_256_mont_mul_order_5(u2, u2, s);
        }

            err = sp_256_ecc_mulmod_base_5(p1, u1, 0, 0, heap);
    }
    if (err == MP_OKAY) {
            err = sp_256_ecc_mulmod_5(p2, p2, u2, 0, 0, heap);
    }

    if (err == MP_OKAY) {
        {
            sp_256_proj_point_add_5(p1, p1, p2, tmp);
            if (sp_256_iszero_5(p1->z)) {
                if (sp_256_iszero_5(p1->x) && sp_256_iszero_5(p1->y)) {
                    sp_256_proj_point_dbl_5(p1, p2, tmp);
                }
                else {
                    /* Y ordinate is not used from here - don't set. */
                    p1->x[0] = 0;
                    p1->x[1] = 0;
                    p1->x[2] = 0;
                    p1->x[3] = 0;
                    p1->x[4] = 0;
                    XMEMCPY(p1->z, p256_norm_mod, sizeof(p256_norm_mod));
                }
            }
        }

        /* (r + n*order).z'.z' mod prime == (u1.G + u2.Q)->x' */
        /* Reload r and convert to Montgomery form. */
        sp_256_from_mp(u2, 5, r);
        err = sp_256_mod_mul_norm_5(u2, u2, p256_mod);
    }

    if (err == MP_OKAY) {
        /* u1 = r.z'.z' mod prime */
        sp_256_mont_sqr_5(p1->z, p1->z, p256_mod, p256_mp_mod);
        sp_256_mont_mul_5(u1, u2, p1->z, p256_mod, p256_mp_mod);
        *res = (int)(sp_256_cmp_5(p1->x, u1) == 0);
        if (*res == 0) {
            /* Reload r and add order. */
            sp_256_from_mp(u2, 5, r);
            carry = sp_256_add_5(u2, u2, p256_order);
            /* Carry means result is greater than mod and is not valid. */
            if (carry == 0) {
                sp_256_norm_5(u2);

                /* Compare with mod and if greater or equal then not valid. */
                c = sp_256_cmp_5(u2, p256_mod);
                if (c < 0) {
                    /* Convert to Montogomery form */
                    err = sp_256_mod_mul_norm_5(u2, u2, p256_mod);
                    if (err == MP_OKAY) {
                        /* u1 = (r + 1*order).z'.z' mod prime */
                        sp_256_mont_mul_5(u1, u2, p1->z, p256_mod,
                                                                  p256_mp_mod);
                        *res = (int)(sp_256_cmp_5(p1->x, u1) == 0);
                    }
                }
            }
        }
    }

#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (d != NULL)
        XFREE(d, heap, DYNAMIC_TYPE_ECC);
#endif
    sp_256_point_free_5(p1, 0, heap);
    sp_256_point_free_5(p2, 0, heap);

    return err;
}
#endif /* HAVE_ECC_VERIFY */

#ifdef HAVE_ECC_CHECK_KEY
/* Check that the x and y oridinates are a valid point on the curve.
 *
 * point  EC point.
 * heap   Heap to use if dynamically allocating.
 * returns MEMORY_E if dynamic memory allocation fails, MP_VAL if the point is
 * not on the curve and MP_OKAY otherwise.
 */
static int sp_256_ecc_is_point_5(sp_point_256* point, void* heap)
{
#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    sp_digit* d = NULL;
#else
    sp_digit t1d[2*5];
    sp_digit t2d[2*5];
#endif
    sp_digit* t1;
    sp_digit* t2;
    int err = MP_OKAY;

#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    d = (sp_digit*)XMALLOC(sizeof(sp_digit) * 5 * 4, heap, DYNAMIC_TYPE_ECC);
    if (d == NULL) {
        err = MEMORY_E;
    }
#endif
    (void)heap;

    if (err == MP_OKAY) {
#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
        t1 = d + 0 * 5;
        t2 = d + 2 * 5;
#else
        t1 = t1d;
        t2 = t2d;
#endif

        sp_256_sqr_5(t1, point->y);
        (void)sp_256_mod_5(t1, t1, p256_mod);
        sp_256_sqr_5(t2, point->x);
        (void)sp_256_mod_5(t2, t2, p256_mod);
        sp_256_mul_5(t2, t2, point->x);
        (void)sp_256_mod_5(t2, t2, p256_mod);
        (void)sp_256_sub_5(t2, p256_mod, t2);
        sp_256_mont_add_5(t1, t1, t2, p256_mod);

        sp_256_mont_add_5(t1, t1, point->x, p256_mod);
        sp_256_mont_add_5(t1, t1, point->x, p256_mod);
        sp_256_mont_add_5(t1, t1, point->x, p256_mod);

        if (sp_256_cmp_5(t1, p256_b) != 0) {
            err = MP_VAL;
        }
    }

#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (d != NULL) {
        XFREE(d, heap, DYNAMIC_TYPE_ECC);
    }
#endif

    return err;
}

/* Check that the x and y oridinates are a valid point on the curve.
 *
 * pX  X ordinate of EC point.
 * pY  Y ordinate of EC point.
 * returns MEMORY_E if dynamic memory allocation fails, MP_VAL if the point is
 * not on the curve and MP_OKAY otherwise.
 */
int sp_ecc_is_point_256(mp_int* pX, mp_int* pY)
{
#if (!defined(WOLFSSL_SP_SMALL) && !defined(WOLFSSL_SMALL_STACK)) || defined(WOLFSSL_SP_NO_MALLOC)
    sp_point_256 pubd;
#endif
    sp_point_256* pub;
    byte one[1] = { 1 };
    int err;

    err = sp_256_point_new_5(NULL, pubd, pub);
    if (err == MP_OKAY) {
        sp_256_from_mp(pub->x, 5, pX);
        sp_256_from_mp(pub->y, 5, pY);
        sp_256_from_bin(pub->z, 5, one, (int)sizeof(one));

        err = sp_256_ecc_is_point_5(pub, NULL);
    }

    sp_256_point_free_5(pub, 0, NULL);

    return err;
}

/* Check that the private scalar generates the EC point (px, py), the point is
 * on the curve and the point has the correct order.
 *
 * pX     X ordinate of EC point.
 * pY     Y ordinate of EC point.
 * privm  Private scalar that generates EC point.
 * returns MEMORY_E if dynamic memory allocation fails, MP_VAL if the point is
 * not on the curve, ECC_INF_E if the point does not have the correct order,
 * ECC_PRIV_KEY_E when the private scalar doesn't generate the EC point and
 * MP_OKAY otherwise.
 */
int sp_ecc_check_key_256(mp_int* pX, mp_int* pY, mp_int* privm, void* heap)
{
#if (!defined(WOLFSSL_SP_SMALL) && !defined(WOLFSSL_SMALL_STACK)) || defined(WOLFSSL_SP_NO_MALLOC)
    sp_digit privd[5];
    sp_point_256 pubd;
    sp_point_256 pd;
#endif
    sp_digit* priv = NULL;
    sp_point_256* pub;
    sp_point_256* p = NULL;
    byte one[1] = { 1 };
    int err;

    err = sp_256_point_new_5(heap, pubd, pub);
    if (err == MP_OKAY) {
        err = sp_256_point_new_5(heap, pd, p);
    }
#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (err == MP_OKAY) {
        priv = (sp_digit*)XMALLOC(sizeof(sp_digit) * 5, heap,
                                                              DYNAMIC_TYPE_ECC);
        if (priv == NULL) {
            err = MEMORY_E;
        }
    }
#endif

    if (err == MP_OKAY) {
#if (!defined(WOLFSSL_SP_SMALL) && !defined(WOLFSSL_SMALL_STACK)) || defined(WOLFSSL_SP_NO_MALLOC)
        priv = privd;
#endif

        sp_256_from_mp(pub->x, 5, pX);
        sp_256_from_mp(pub->y, 5, pY);
        sp_256_from_bin(pub->z, 5, one, (int)sizeof(one));
        sp_256_from_mp(priv, 5, privm);

        /* Check point at infinitiy. */
        if ((sp_256_iszero_5(pub->x) != 0) &&
            (sp_256_iszero_5(pub->y) != 0)) {
            err = ECC_INF_E;
        }
    }

    if (err == MP_OKAY) {
        /* Check range of X and Y */
        if (sp_256_cmp_5(pub->x, p256_mod) >= 0 ||
            sp_256_cmp_5(pub->y, p256_mod) >= 0) {
            err = ECC_OUT_OF_RANGE_E;
        }
    }

    if (err == MP_OKAY) {
        /* Check point is on curve */
        err = sp_256_ecc_is_point_5(pub, heap);
    }

    if (err == MP_OKAY) {
        /* Point * order = infinity */
            err = sp_256_ecc_mulmod_5(p, pub, p256_order, 1, 1, heap);
    }
    if (err == MP_OKAY) {
        /* Check result is infinity */
        if ((sp_256_iszero_5(p->x) == 0) ||
            (sp_256_iszero_5(p->y) == 0)) {
            err = ECC_INF_E;
        }
    }

    if (err == MP_OKAY) {
        /* Base * private = point */
            err = sp_256_ecc_mulmod_base_5(p, priv, 1, 1, heap);
    }
    if (err == MP_OKAY) {
        /* Check result is public key */
        if (sp_256_cmp_5(p->x, pub->x) != 0 ||
            sp_256_cmp_5(p->y, pub->y) != 0) {
            err = ECC_PRIV_KEY_E;
        }
    }

#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (priv != NULL) {
        XFREE(priv, heap, DYNAMIC_TYPE_ECC);
    }
#endif
    sp_256_point_free_5(p, 0, heap);
    sp_256_point_free_5(pub, 0, heap);

    return err;
}
#endif
#ifdef WOLFSSL_PUBLIC_ECC_ADD_DBL
/* Add two projective EC points together.
 * (pX, pY, pZ) + (qX, qY, qZ) = (rX, rY, rZ)
 *
 * pX   First EC point's X ordinate.
 * pY   First EC point's Y ordinate.
 * pZ   First EC point's Z ordinate.
 * qX   Second EC point's X ordinate.
 * qY   Second EC point's Y ordinate.
 * qZ   Second EC point's Z ordinate.
 * rX   Resultant EC point's X ordinate.
 * rY   Resultant EC point's Y ordinate.
 * rZ   Resultant EC point's Z ordinate.
 * returns MEMORY_E if dynamic memory allocation fails and MP_OKAY otherwise.
 */
int sp_ecc_proj_add_point_256(mp_int* pX, mp_int* pY, mp_int* pZ,
                              mp_int* qX, mp_int* qY, mp_int* qZ,
                              mp_int* rX, mp_int* rY, mp_int* rZ)
{
#if (!defined(WOLFSSL_SP_SMALL) && !defined(WOLFSSL_SMALL_STACK)) || defined(WOLFSSL_SP_NO_MALLOC)
    sp_digit tmpd[2 * 5 * 5];
    sp_point_256 pd;
    sp_point_256 qd;
#endif
    sp_digit* tmp;
    sp_point_256* p;
    sp_point_256* q = NULL;
    int err;

    err = sp_256_point_new_5(NULL, pd, p);
    if (err == MP_OKAY) {
        err = sp_256_point_new_5(NULL, qd, q);
    }
#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (err == MP_OKAY) {
        tmp = (sp_digit*)XMALLOC(sizeof(sp_digit) * 2 * 5 * 5, NULL,
                                                              DYNAMIC_TYPE_ECC);
        if (tmp == NULL) {
            err = MEMORY_E;
        }
    }
#else
    tmp = tmpd;
#endif

    if (err == MP_OKAY) {
        sp_256_from_mp(p->x, 5, pX);
        sp_256_from_mp(p->y, 5, pY);
        sp_256_from_mp(p->z, 5, pZ);
        sp_256_from_mp(q->x, 5, qX);
        sp_256_from_mp(q->y, 5, qY);
        sp_256_from_mp(q->z, 5, qZ);

            sp_256_proj_point_add_5(p, p, q, tmp);
    }

    if (err == MP_OKAY) {
        err = sp_256_to_mp(p->x, rX);
    }
    if (err == MP_OKAY) {
        err = sp_256_to_mp(p->y, rY);
    }
    if (err == MP_OKAY) {
        err = sp_256_to_mp(p->z, rZ);
    }

#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (tmp != NULL) {
        XFREE(tmp, NULL, DYNAMIC_TYPE_ECC);
    }
#endif
    sp_256_point_free_5(q, 0, NULL);
    sp_256_point_free_5(p, 0, NULL);

    return err;
}

/* Double a projective EC point.
 * (pX, pY, pZ) + (pX, pY, pZ) = (rX, rY, rZ)
 *
 * pX   EC point's X ordinate.
 * pY   EC point's Y ordinate.
 * pZ   EC point's Z ordinate.
 * rX   Resultant EC point's X ordinate.
 * rY   Resultant EC point's Y ordinate.
 * rZ   Resultant EC point's Z ordinate.
 * returns MEMORY_E if dynamic memory allocation fails and MP_OKAY otherwise.
 */
int sp_ecc_proj_dbl_point_256(mp_int* pX, mp_int* pY, mp_int* pZ,
                              mp_int* rX, mp_int* rY, mp_int* rZ)
{
#if (!defined(WOLFSSL_SP_SMALL) && !defined(WOLFSSL_SMALL_STACK)) || defined(WOLFSSL_SP_NO_MALLOC)
    sp_digit tmpd[2 * 5 * 2];
    sp_point_256 pd;
#endif
    sp_digit* tmp;
    sp_point_256* p;
    int err;

    err = sp_256_point_new_5(NULL, pd, p);
#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (err == MP_OKAY) {
        tmp = (sp_digit*)XMALLOC(sizeof(sp_digit) * 2 * 5 * 2, NULL,
                                                              DYNAMIC_TYPE_ECC);
        if (tmp == NULL) {
            err = MEMORY_E;
        }
    }
#else
    tmp = tmpd;
#endif

    if (err == MP_OKAY) {
        sp_256_from_mp(p->x, 5, pX);
        sp_256_from_mp(p->y, 5, pY);
        sp_256_from_mp(p->z, 5, pZ);

            sp_256_proj_point_dbl_5(p, p, tmp);
    }

    if (err == MP_OKAY) {
        err = sp_256_to_mp(p->x, rX);
    }
    if (err == MP_OKAY) {
        err = sp_256_to_mp(p->y, rY);
    }
    if (err == MP_OKAY) {
        err = sp_256_to_mp(p->z, rZ);
    }

#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (tmp != NULL) {
        XFREE(tmp, NULL, DYNAMIC_TYPE_ECC);
    }
#endif
    sp_256_point_free_5(p, 0, NULL);

    return err;
}

/* Map a projective EC point to affine in place.
 * pZ will be one.
 *
 * pX   EC point's X ordinate.
 * pY   EC point's Y ordinate.
 * pZ   EC point's Z ordinate.
 * returns MEMORY_E if dynamic memory allocation fails and MP_OKAY otherwise.
 */
int sp_ecc_map_256(mp_int* pX, mp_int* pY, mp_int* pZ)
{
#if (!defined(WOLFSSL_SP_SMALL) && !defined(WOLFSSL_SMALL_STACK)) || defined(WOLFSSL_SP_NO_MALLOC)
    sp_digit tmpd[2 * 5 * 4];
    sp_point_256 pd;
#endif
    sp_digit* tmp;
    sp_point_256* p;
    int err;

    err = sp_256_point_new_5(NULL, pd, p);
#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (err == MP_OKAY) {
        tmp = (sp_digit*)XMALLOC(sizeof(sp_digit) * 2 * 5 * 4, NULL,
                                                              DYNAMIC_TYPE_ECC);
        if (tmp == NULL) {
            err = MEMORY_E;
        }
    }
#else
    tmp = tmpd;
#endif
    if (err == MP_OKAY) {
        sp_256_from_mp(p->x, 5, pX);
        sp_256_from_mp(p->y, 5, pY);
        sp_256_from_mp(p->z, 5, pZ);

        sp_256_map_5(p, p, tmp);
    }

    if (err == MP_OKAY) {
        err = sp_256_to_mp(p->x, pX);
    }
    if (err == MP_OKAY) {
        err = sp_256_to_mp(p->y, pY);
    }
    if (err == MP_OKAY) {
        err = sp_256_to_mp(p->z, pZ);
    }

#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (tmp != NULL) {
        XFREE(tmp, NULL, DYNAMIC_TYPE_ECC);
    }
#endif
    sp_256_point_free_5(p, 0, NULL);

    return err;
}
#endif /* WOLFSSL_PUBLIC_ECC_ADD_DBL */
#ifdef HAVE_COMP_KEY
/* Find the square root of a number mod the prime of the curve.
 *
 * y  The number to operate on and the result.
 * returns MEMORY_E if dynamic memory allocation fails and MP_OKAY otherwise.
 */
static int sp_256_mont_sqrt_5(sp_digit* y)
{
#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    sp_digit* d;
#else
    sp_digit t1d[2 * 5];
    sp_digit t2d[2 * 5];
#endif
    sp_digit* t1;
    sp_digit* t2;
    int err = MP_OKAY;

#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    d = (sp_digit*)XMALLOC(sizeof(sp_digit) * 4 * 5, NULL, DYNAMIC_TYPE_ECC);
    if (d == NULL) {
        err = MEMORY_E;
    }
#endif

    if (err == MP_OKAY) {
#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
        t1 = d + 0 * 5;
        t2 = d + 2 * 5;
#else
        t1 = t1d;
        t2 = t2d;
#endif

        {
            /* t2 = y ^ 0x2 */
            sp_256_mont_sqr_5(t2, y, p256_mod, p256_mp_mod);
            /* t1 = y ^ 0x3 */
            sp_256_mont_mul_5(t1, t2, y, p256_mod, p256_mp_mod);
            /* t2 = y ^ 0xc */
            sp_256_mont_sqr_n_5(t2, t1, 2, p256_mod, p256_mp_mod);
            /* t1 = y ^ 0xf */
            sp_256_mont_mul_5(t1, t1, t2, p256_mod, p256_mp_mod);
            /* t2 = y ^ 0xf0 */
            sp_256_mont_sqr_n_5(t2, t1, 4, p256_mod, p256_mp_mod);
            /* t1 = y ^ 0xff */
            sp_256_mont_mul_5(t1, t1, t2, p256_mod, p256_mp_mod);
            /* t2 = y ^ 0xff00 */
            sp_256_mont_sqr_n_5(t2, t1, 8, p256_mod, p256_mp_mod);
            /* t1 = y ^ 0xffff */
            sp_256_mont_mul_5(t1, t1, t2, p256_mod, p256_mp_mod);
            /* t2 = y ^ 0xffff0000 */
            sp_256_mont_sqr_n_5(t2, t1, 16, p256_mod, p256_mp_mod);
            /* t1 = y ^ 0xffffffff */
            sp_256_mont_mul_5(t1, t1, t2, p256_mod, p256_mp_mod);
            /* t1 = y ^ 0xffffffff00000000 */
            sp_256_mont_sqr_n_5(t1, t1, 32, p256_mod, p256_mp_mod);
            /* t1 = y ^ 0xffffffff00000001 */
            sp_256_mont_mul_5(t1, t1, y, p256_mod, p256_mp_mod);
            /* t1 = y ^ 0xffffffff00000001000000000000000000000000 */
            sp_256_mont_sqr_n_5(t1, t1, 96, p256_mod, p256_mp_mod);
            /* t1 = y ^ 0xffffffff00000001000000000000000000000001 */
            sp_256_mont_mul_5(t1, t1, y, p256_mod, p256_mp_mod);
            sp_256_mont_sqr_n_5(y, t1, 94, p256_mod, p256_mp_mod);
        }
    }

#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (d != NULL) {
        XFREE(d, NULL, DYNAMIC_TYPE_ECC);
    }
#endif

    return err;
}


/* Uncompress the point given the X ordinate.
 *
 * xm    X ordinate.
 * odd   Whether the Y ordinate is odd.
 * ym    Calculated Y ordinate.
 * returns MEMORY_E if dynamic memory allocation fails and MP_OKAY otherwise.
 */
int sp_ecc_uncompress_256(mp_int* xm, int odd, mp_int* ym)
{
#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    sp_digit* d;
#else
    sp_digit xd[2 * 5];
    sp_digit yd[2 * 5];
#endif
    sp_digit* x = NULL;
    sp_digit* y = NULL;
    int err = MP_OKAY;

#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    d = (sp_digit*)XMALLOC(sizeof(sp_digit) * 4 * 5, NULL, DYNAMIC_TYPE_ECC);
    if (d == NULL) {
        err = MEMORY_E;
    }
#endif

    if (err == MP_OKAY) {
#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
        x = d + 0 * 5;
        y = d + 2 * 5;
#else
        x = xd;
        y = yd;
#endif

        sp_256_from_mp(x, 5, xm);
        err = sp_256_mod_mul_norm_5(x, x, p256_mod);
    }
    if (err == MP_OKAY) {
        /* y = x^3 */
        {
            sp_256_mont_sqr_5(y, x, p256_mod, p256_mp_mod);
            sp_256_mont_mul_5(y, y, x, p256_mod, p256_mp_mod);
        }
        /* y = x^3 - 3x */
        sp_256_mont_sub_5(y, y, x, p256_mod);
        sp_256_mont_sub_5(y, y, x, p256_mod);
        sp_256_mont_sub_5(y, y, x, p256_mod);
        /* y = x^3 - 3x + b */
        err = sp_256_mod_mul_norm_5(x, p256_b, p256_mod);
    }
    if (err == MP_OKAY) {
        sp_256_mont_add_5(y, y, x, p256_mod);
        /* y = sqrt(x^3 - 3x + b) */
        err = sp_256_mont_sqrt_5(y);
    }
    if (err == MP_OKAY) {
        XMEMSET(y + 5, 0, 5U * sizeof(sp_digit));
        sp_256_mont_reduce_5(y, p256_mod, p256_mp_mod);
        if ((((word32)y[0] ^ (word32)odd) & 1U) != 0U) {
            sp_256_mont_sub_5(y, p256_mod, y, p256_mod);
        }

        err = sp_256_to_mp(y, ym);
    }

#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (d != NULL) {
        XFREE(d, NULL, DYNAMIC_TYPE_ECC);
    }
#endif

    return err;
}
#endif
#endif /* !WOLFSSL_SP_NO_256 */
#ifdef WOLFSSL_SP_384

/* Point structure to use. */
typedef struct sp_point_384 {
    sp_digit x[2 * 7];
    sp_digit y[2 * 7];
    sp_digit z[2 * 7];
    int infinity;
} sp_point_384;

/* The modulus (prime) of the curve P384. */
static const sp_digit p384_mod[7] = {
    0x000000ffffffffL,0x7ffe0000000000L,0x7ffffffffbffffL,0x7fffffffffffffL,
    0x7fffffffffffffL,0x7fffffffffffffL,0x3fffffffffffffL
};
/* The Montogmery normalizer for modulus of the curve P384. */
static const sp_digit p384_norm_mod[7] = {
    0x7fffff00000001L,0x0001ffffffffffL,0x00000000040000L,0x00000000000000L,
    0x00000000000000L,0x00000000000000L,0x00000000000000L
};
/* The Montogmery multiplier for modulus of the curve P384. */
static sp_digit p384_mp_mod = 0x0000100000001;
#if defined(WOLFSSL_VALIDATE_ECC_KEYGEN) || defined(HAVE_ECC_SIGN) || \
                                            defined(HAVE_ECC_VERIFY)
/* The order of the curve P384. */
static const sp_digit p384_order[7] = {
    0x6c196accc52973L,0x1b6491614ef5d9L,0x07d0dcb77d6068L,0x7ffffffe3b1a6cL,
    0x7fffffffffffffL,0x7fffffffffffffL,0x3fffffffffffffL
};
#endif
/* The order of the curve P384 minus 2. */
static const sp_digit p384_order2[7] = {
    0x6c196accc52971L,0x1b6491614ef5d9L,0x07d0dcb77d6068L,0x7ffffffe3b1a6cL,
    0x7fffffffffffffL,0x7fffffffffffffL,0x3fffffffffffffL
};
#if defined(HAVE_ECC_SIGN) || defined(HAVE_ECC_VERIFY)
/* The Montogmery normalizer for order of the curve P384. */
static const sp_digit p384_norm_order[7] = {
    0x13e695333ad68dL,0x649b6e9eb10a26L,0x782f2348829f97L,0x00000001c4e593L,
    0x00000000000000L,0x00000000000000L,0x00000000000000L
};
#endif
#if defined(HAVE_ECC_SIGN) || defined(HAVE_ECC_VERIFY)
/* The Montogmery multiplier for order of the curve P384. */
static sp_digit p384_mp_order = 0x546089e88fdc45l;
#endif
/* The base point of curve P384. */
static const sp_point_384 p384_base = {
    /* X ordinate */
    {
        0x545e3872760ab7L,0x64bb7eaa52d874L,0x020950a8e1540bL,
        0x5d3cdcc2cfba0fL,0x0ad746e1d3b628L,0x26f1d638e3de64L,0x2aa1f288afa2c1L,
        0L, 0L, 0L, 0L, 0L, 0L, 0L
    },
    /* Y ordinate */
    {
        0x431d7c90ea0e5fL,0x639c3afd033af4L,0x4ed7c2e3002982L,
        0x44d0a3e74ed188L,0x2dc29f8f41dbd2L,0x0debb3d317f252L,0x0d85f792a5898bL,
        0L, 0L, 0L, 0L, 0L, 0L, 0L
    },
    /* Z ordinate */
    {
        0x00000000000001L,0x00000000000000L,0x00000000000000L,
        0x00000000000000L,0x00000000000000L,0x00000000000000L,0x00000000000000L,
        0L, 0L, 0L, 0L, 0L, 0L, 0L
    },
    /* infinity */
    0
};
#if defined(HAVE_ECC_CHECK_KEY) || defined(HAVE_COMP_KEY)
static const sp_digit p384_b[7] = {
    0x05c8edd3ec2aefL,0x731b145da33a55L,0x3d404e1d6b1958L,0x740a089018a044L,
    0x02d19181d9c6efL,0x7c9311c0ad7c7fL,0x2ccc4be9f88fb9L
};
#endif

static int sp_384_point_new_ex_7(void* heap, sp_point_384* sp, sp_point_384** p)
{
    int ret = MP_OKAY;
    (void)heap;
#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    (void)sp;
    *p = (sp_point_384*)XMALLOC(sizeof(sp_point_384), heap, DYNAMIC_TYPE_ECC);
#else
    *p = sp;
#endif
    if (*p == NULL) {
        ret = MEMORY_E;
    }
    return ret;
}

#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
/* Allocate memory for point and return error. */
#define sp_384_point_new_7(heap, sp, p) sp_384_point_new_ex_7((heap), NULL, &(p))
#else
/* Set pointer to data and return no error. */
#define sp_384_point_new_7(heap, sp, p) sp_384_point_new_ex_7((heap), &(sp), &(p))
#endif


static void sp_384_point_free_7(sp_point_384* p, int clear, void* heap)
{
#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
/* If valid pointer then clear point data if requested and free data. */
    if (p != NULL) {
        if (clear != 0) {
            XMEMSET(p, 0, sizeof(*p));
        }
        XFREE(p, heap, DYNAMIC_TYPE_ECC);
    }
#else
/* Clear point data if requested. */
    if (clear != 0) {
        XMEMSET(p, 0, sizeof(*p));
    }
#endif
    (void)heap;
}

/* Multiply a number by Montogmery normalizer mod modulus (prime).
 *
 * r  The resulting Montgomery form number.
 * a  The number to convert.
 * m  The modulus (prime).
 * returns MEMORY_E when memory allocation fails and MP_OKAY otherwise.
 */
static int sp_384_mod_mul_norm_7(sp_digit* r, const sp_digit* a, const sp_digit* m)
{
#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    int64_t* td;
#else
    int64_t td[12];
    int64_t a32d[12];
#endif
    int64_t* t;
    int64_t* a32;
    int64_t o;
    int err = MP_OKAY;

    (void)m;

#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    td = (int64_t*)XMALLOC(sizeof(int64_t) * 2 * 12, NULL, DYNAMIC_TYPE_ECC);
    if (td == NULL) {
        err = MEMORY_E;
    }
#endif

    if (err == MP_OKAY) {
#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
        t = td;
        a32 = td + 12;
#else
        t = td;
        a32 = a32d;
#endif

        a32[0] = (sp_digit)(a[0]) & 0xffffffffL;
        a32[1] = (sp_digit)(a[0] >> 32U);
        a32[1] |= a[1] << 23U;
        a32[1] &= 0xffffffffL;
        a32[2] = (sp_digit)(a[1] >> 9U) & 0xffffffffL;
        a32[3] = (sp_digit)(a[1] >> 41U);
        a32[3] |= a[2] << 14U;
        a32[3] &= 0xffffffffL;
        a32[4] = (sp_digit)(a[2] >> 18U) & 0xffffffffL;
        a32[5] = (sp_digit)(a[2] >> 50U);
        a32[5] |= a[3] << 5U;
        a32[5] &= 0xffffffffL;
        a32[6] = (sp_digit)(a[3] >> 27U);
        a32[6] |= a[4] << 28U;
        a32[6] &= 0xffffffffL;
        a32[7] = (sp_digit)(a[4] >> 4U) & 0xffffffffL;
        a32[8] = (sp_digit)(a[4] >> 36U);
        a32[8] |= a[5] << 19U;
        a32[8] &= 0xffffffffL;
        a32[9] = (sp_digit)(a[5] >> 13U) & 0xffffffffL;
        a32[10] = (sp_digit)(a[5] >> 45U);
        a32[10] |= a[6] << 10U;
        a32[10] &= 0xffffffffL;
        a32[11] = (sp_digit)(a[6] >> 22U) & 0xffffffffL;

        /*  1  0  0  0  0  0  0  0  1  1  0 -1 */
        t[0] = 0 + a32[0] + a32[8] + a32[9] - a32[11];
        /* -1  1  0  0  0  0  0  0 -1  0  1  1 */
        t[1] = 0 - a32[0] + a32[1] - a32[8] + a32[10] + a32[11];
        /*  0 -1  1  0  0  0  0  0  0 -1  0  1 */
        t[2] = 0 - a32[1] + a32[2] - a32[9] + a32[11];
        /*  1  0 -1  1  0  0  0  0  1  1 -1 -1 */
        t[3] = 0 + a32[0] - a32[2] + a32[3] + a32[8] + a32[9] - a32[10] - a32[11];
        /*  1  1  0 -1  1  0  0  0  1  2  1 -2 */
        t[4] = 0 + a32[0] + a32[1] - a32[3] + a32[4] + a32[8] + 2 * a32[9] + a32[10] -  2 * a32[11];
        /*  0  1  1  0 -1  1  0  0  0  1  2  1 */
        t[5] = 0 + a32[1] + a32[2] - a32[4] + a32[5] + a32[9] + 2 * a32[10] + a32[11];
        /*  0  0  1  1  0 -1  1  0  0  0  1  2 */
        t[6] = 0 + a32[2] + a32[3] - a32[5] + a32[6] + a32[10] + 2 * a32[11];
        /*  0  0  0  1  1  0 -1  1  0  0  0  1 */
        t[7] = 0 + a32[3] + a32[4] - a32[6] + a32[7] + a32[11];
        /*  0  0  0  0  1  1  0 -1  1  0  0  0 */
        t[8] = 0 + a32[4] + a32[5] - a32[7] + a32[8];
        /*  0  0  0  0  0  1  1  0 -1  1  0  0 */
        t[9] = 0 + a32[5] + a32[6] - a32[8] + a32[9];
        /*  0  0  0  0  0  0  1  1  0 -1  1  0 */
        t[10] = 0 + a32[6] + a32[7] - a32[9] + a32[10];
        /*  0  0  0  0  0  0  0  1  1  0 -1  1 */
        t[11] = 0 + a32[7] + a32[8] - a32[10] + a32[11];

        t[1] += t[0] >> 32; t[0] &= 0xffffffff;
        t[2] += t[1] >> 32; t[1] &= 0xffffffff;
        t[3] += t[2] >> 32; t[2] &= 0xffffffff;
        t[4] += t[3] >> 32; t[3] &= 0xffffffff;
        t[5] += t[4] >> 32; t[4] &= 0xffffffff;
        t[6] += t[5] >> 32; t[5] &= 0xffffffff;
        t[7] += t[6] >> 32; t[6] &= 0xffffffff;
        t[8] += t[7] >> 32; t[7] &= 0xffffffff;
        t[9] += t[8] >> 32; t[8] &= 0xffffffff;
        t[10] += t[9] >> 32; t[9] &= 0xffffffff;
        t[11] += t[10] >> 32; t[10] &= 0xffffffff;
        o     = t[11] >> 32; t[11] &= 0xffffffff;
        t[0] += o;
        t[1] -= o;
        t[3] += o;
        t[4] += o;
        t[1] += t[0] >> 32; t[0] &= 0xffffffff;
        t[2] += t[1] >> 32; t[1] &= 0xffffffff;
        t[3] += t[2] >> 32; t[2] &= 0xffffffff;
        t[4] += t[3] >> 32; t[3] &= 0xffffffff;
        t[5] += t[4] >> 32; t[4] &= 0xffffffff;
        t[6] += t[5] >> 32; t[5] &= 0xffffffff;
        t[7] += t[6] >> 32; t[6] &= 0xffffffff;
        t[8] += t[7] >> 32; t[7] &= 0xffffffff;
        t[9] += t[8] >> 32; t[8] &= 0xffffffff;
        t[10] += t[9] >> 32; t[9] &= 0xffffffff;
        t[11] += t[10] >> 32; t[10] &= 0xffffffff;

        r[0] = t[0];
        r[0] |= t[1] << 32U;
        r[0] &= 0x7fffffffffffffLL;
        r[1] = (sp_digit)(t[1] >> 23);
        r[1] |= t[2] << 9U;
        r[1] |= t[3] << 41U;
        r[1] &= 0x7fffffffffffffLL;
        r[2] = (sp_digit)(t[3] >> 14);
        r[2] |= t[4] << 18U;
        r[2] |= t[5] << 50U;
        r[2] &= 0x7fffffffffffffLL;
        r[3] = (sp_digit)(t[5] >> 5);
        r[3] |= t[6] << 27U;
        r[3] &= 0x7fffffffffffffLL;
        r[4] = (sp_digit)(t[6] >> 28);
        r[4] |= t[7] << 4U;
        r[4] |= t[8] << 36U;
        r[4] &= 0x7fffffffffffffLL;
        r[5] = (sp_digit)(t[8] >> 19);
        r[5] |= t[9] << 13U;
        r[5] |= t[10] << 45U;
        r[5] &= 0x7fffffffffffffLL;
        r[6] = (sp_digit)(t[10] >> 10);
        r[6] |= t[11] << 22U;
    }

#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (td != NULL)
        XFREE(td, NULL, DYNAMIC_TYPE_ECC);
#endif

    return err;
}

/* Convert an mp_int to an array of sp_digit.
 *
 * r  A single precision integer.
 * size  Maximum number of bytes to convert
 * a  A multi-precision integer.
 */
static void sp_384_from_mp(sp_digit* r, int size, const mp_int* a)
{
#if DIGIT_BIT == 55
    int j;

    XMEMCPY(r, a->dp, sizeof(sp_digit) * a->used);

    for (j = a->used; j < size; j++) {
        r[j] = 0;
    }
#elif DIGIT_BIT > 55
    int i, j = 0;
    word32 s = 0;

    r[0] = 0;
    for (i = 0; i < a->used && j < size; i++) {
        r[j] |= ((sp_digit)a->dp[i] << s);
        r[j] &= 0x7fffffffffffffL;
        s = 55U - s;
        if (j + 1 >= size) {
            break;
        }
        /* lint allow cast of mismatch word32 and mp_digit */
        r[++j] = (sp_digit)(a->dp[i] >> s); /*lint !e9033*/
        while ((s + 55U) <= (word32)DIGIT_BIT) {
            s += 55U;
            r[j] &= 0x7fffffffffffffL;
            if (j + 1 >= size) {
                break;
            }
            if (s < (word32)DIGIT_BIT) {
                /* lint allow cast of mismatch word32 and mp_digit */
                r[++j] = (sp_digit)(a->dp[i] >> s); /*lint !e9033*/
            }
            else {
                r[++j] = 0L;
            }
        }
        s = (word32)DIGIT_BIT - s;
    }

    for (j++; j < size; j++) {
        r[j] = 0;
    }
#else
    int i, j = 0, s = 0;

    r[0] = 0;
    for (i = 0; i < a->used && j < size; i++) {
        r[j] |= ((sp_digit)a->dp[i]) << s;
        if (s + DIGIT_BIT >= 55) {
            r[j] &= 0x7fffffffffffffL;
            if (j + 1 >= size) {
                break;
            }
            s = 55 - s;
            if (s == DIGIT_BIT) {
                r[++j] = 0;
                s = 0;
            }
            else {
                r[++j] = a->dp[i] >> s;
                s = DIGIT_BIT - s;
            }
        }
        else {
            s += DIGIT_BIT;
        }
    }

    for (j++; j < size; j++) {
        r[j] = 0;
    }
#endif
}

/* Convert a point of type ecc_point to type sp_point_384.
 *
 * p   Point of type sp_point_384 (result).
 * pm  Point of type ecc_point.
 */
static void sp_384_point_from_ecc_point_7(sp_point_384* p, const ecc_point* pm)
{
    XMEMSET(p->x, 0, sizeof(p->x));
    XMEMSET(p->y, 0, sizeof(p->y));
    XMEMSET(p->z, 0, sizeof(p->z));
    sp_384_from_mp(p->x, 7, pm->x);
    sp_384_from_mp(p->y, 7, pm->y);
    sp_384_from_mp(p->z, 7, pm->z);
    p->infinity = 0;
}

/* Convert an array of sp_digit to an mp_int.
 *
 * a  A single precision integer.
 * r  A multi-precision integer.
 */
static int sp_384_to_mp(const sp_digit* a, mp_int* r)
{
    int err;

    err = mp_grow(r, (384 + DIGIT_BIT - 1) / DIGIT_BIT);
    if (err == MP_OKAY) { /*lint !e774 case where err is always MP_OKAY*/
#if DIGIT_BIT == 55
        XMEMCPY(r->dp, a, sizeof(sp_digit) * 7);
        r->used = 7;
        mp_clamp(r);
#elif DIGIT_BIT < 55
        int i, j = 0, s = 0;

        r->dp[0] = 0;
        for (i = 0; i < 7; i++) {
            r->dp[j] |= (mp_digit)(a[i] << s);
            r->dp[j] &= (1L << DIGIT_BIT) - 1;
            s = DIGIT_BIT - s;
            r->dp[++j] = (mp_digit)(a[i] >> s);
            while (s + DIGIT_BIT <= 55) {
                s += DIGIT_BIT;
                r->dp[j++] &= (1L << DIGIT_BIT) - 1;
                if (s == SP_WORD_SIZE) {
                    r->dp[j] = 0;
                }
                else {
                    r->dp[j] = (mp_digit)(a[i] >> s);
                }
            }
            s = 55 - s;
        }
        r->used = (384 + DIGIT_BIT - 1) / DIGIT_BIT;
        mp_clamp(r);
#else
        int i, j = 0, s = 0;

        r->dp[0] = 0;
        for (i = 0; i < 7; i++) {
            r->dp[j] |= ((mp_digit)a[i]) << s;
            if (s + 55 >= DIGIT_BIT) {
    #if DIGIT_BIT != 32 && DIGIT_BIT != 64
                r->dp[j] &= (1L << DIGIT_BIT) - 1;
    #endif
                s = DIGIT_BIT - s;
                r->dp[++j] = a[i] >> s;
                s = 55 - s;
            }
            else {
                s += 55;
            }
        }
        r->used = (384 + DIGIT_BIT - 1) / DIGIT_BIT;
        mp_clamp(r);
#endif
    }

    return err;
}

/* Convert a point of type sp_point_384 to type ecc_point.
 *
 * p   Point of type sp_point_384.
 * pm  Point of type ecc_point (result).
 * returns MEMORY_E when allocation of memory in ecc_point fails otherwise
 * MP_OKAY.
 */
static int sp_384_point_to_ecc_point_7(const sp_point_384* p, ecc_point* pm)
{
    int err;

    err = sp_384_to_mp(p->x, pm->x);
    if (err == MP_OKAY) {
        err = sp_384_to_mp(p->y, pm->y);
    }
    if (err == MP_OKAY) {
        err = sp_384_to_mp(p->z, pm->z);
    }

    return err;
}

#ifdef WOLFSSL_SP_SMALL
/* Multiply a and b into r. (r = a * b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A single precision integer.
 */
SP_NOINLINE static void sp_384_mul_7(sp_digit* r, const sp_digit* a,
    const sp_digit* b)
{
    int i, j, k;
    int128_t c;

    c = ((int128_t)a[6]) * b[6];
    r[13] = (sp_digit)(c >> 55);
    c = (c & 0x7fffffffffffffL) << 55;
    for (k = 11; k >= 0; k--) {
        for (i = 6; i >= 0; i--) {
            j = k - i;
            if (j >= 7) {
                break;
            }
            if (j < 0) {
                continue;
            }

            c += ((int128_t)a[i]) * b[j];
        }
        r[k + 2] += c >> 110;
        r[k + 1] = (c >> 55) & 0x7fffffffffffffL;
        c = (c & 0x7fffffffffffffL) << 55;
    }
    r[0] = (sp_digit)(c >> 55);
}

#else
/* Multiply a and b into r. (r = a * b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A single precision integer.
 */
SP_NOINLINE static void sp_384_mul_7(sp_digit* r, const sp_digit* a,
    const sp_digit* b)
{
    int128_t t0   = ((int128_t)a[ 0]) * b[ 0];
    int128_t t1   = ((int128_t)a[ 0]) * b[ 1]
                 + ((int128_t)a[ 1]) * b[ 0];
    int128_t t2   = ((int128_t)a[ 0]) * b[ 2]
                 + ((int128_t)a[ 1]) * b[ 1]
                 + ((int128_t)a[ 2]) * b[ 0];
    int128_t t3   = ((int128_t)a[ 0]) * b[ 3]
                 + ((int128_t)a[ 1]) * b[ 2]
                 + ((int128_t)a[ 2]) * b[ 1]
                 + ((int128_t)a[ 3]) * b[ 0];
    int128_t t4   = ((int128_t)a[ 0]) * b[ 4]
                 + ((int128_t)a[ 1]) * b[ 3]
                 + ((int128_t)a[ 2]) * b[ 2]
                 + ((int128_t)a[ 3]) * b[ 1]
                 + ((int128_t)a[ 4]) * b[ 0];
    int128_t t5   = ((int128_t)a[ 0]) * b[ 5]
                 + ((int128_t)a[ 1]) * b[ 4]
                 + ((int128_t)a[ 2]) * b[ 3]
                 + ((int128_t)a[ 3]) * b[ 2]
                 + ((int128_t)a[ 4]) * b[ 1]
                 + ((int128_t)a[ 5]) * b[ 0];
    int128_t t6   = ((int128_t)a[ 0]) * b[ 6]
                 + ((int128_t)a[ 1]) * b[ 5]
                 + ((int128_t)a[ 2]) * b[ 4]
                 + ((int128_t)a[ 3]) * b[ 3]
                 + ((int128_t)a[ 4]) * b[ 2]
                 + ((int128_t)a[ 5]) * b[ 1]
                 + ((int128_t)a[ 6]) * b[ 0];
    int128_t t7   = ((int128_t)a[ 1]) * b[ 6]
                 + ((int128_t)a[ 2]) * b[ 5]
                 + ((int128_t)a[ 3]) * b[ 4]
                 + ((int128_t)a[ 4]) * b[ 3]
                 + ((int128_t)a[ 5]) * b[ 2]
                 + ((int128_t)a[ 6]) * b[ 1];
    int128_t t8   = ((int128_t)a[ 2]) * b[ 6]
                 + ((int128_t)a[ 3]) * b[ 5]
                 + ((int128_t)a[ 4]) * b[ 4]
                 + ((int128_t)a[ 5]) * b[ 3]
                 + ((int128_t)a[ 6]) * b[ 2];
    int128_t t9   = ((int128_t)a[ 3]) * b[ 6]
                 + ((int128_t)a[ 4]) * b[ 5]
                 + ((int128_t)a[ 5]) * b[ 4]
                 + ((int128_t)a[ 6]) * b[ 3];
    int128_t t10  = ((int128_t)a[ 4]) * b[ 6]
                 + ((int128_t)a[ 5]) * b[ 5]
                 + ((int128_t)a[ 6]) * b[ 4];
    int128_t t11  = ((int128_t)a[ 5]) * b[ 6]
                 + ((int128_t)a[ 6]) * b[ 5];
    int128_t t12  = ((int128_t)a[ 6]) * b[ 6];

    t1   += t0  >> 55; r[ 0] = t0  & 0x7fffffffffffffL;
    t2   += t1  >> 55; r[ 1] = t1  & 0x7fffffffffffffL;
    t3   += t2  >> 55; r[ 2] = t2  & 0x7fffffffffffffL;
    t4   += t3  >> 55; r[ 3] = t3  & 0x7fffffffffffffL;
    t5   += t4  >> 55; r[ 4] = t4  & 0x7fffffffffffffL;
    t6   += t5  >> 55; r[ 5] = t5  & 0x7fffffffffffffL;
    t7   += t6  >> 55; r[ 6] = t6  & 0x7fffffffffffffL;
    t8   += t7  >> 55; r[ 7] = t7  & 0x7fffffffffffffL;
    t9   += t8  >> 55; r[ 8] = t8  & 0x7fffffffffffffL;
    t10  += t9  >> 55; r[ 9] = t9  & 0x7fffffffffffffL;
    t11  += t10 >> 55; r[10] = t10 & 0x7fffffffffffffL;
    t12  += t11 >> 55; r[11] = t11 & 0x7fffffffffffffL;
    r[13] = (sp_digit)(t12 >> 55);
                       r[12] = t12 & 0x7fffffffffffffL;
}

#endif /* WOLFSSL_SP_SMALL */
#define sp_384_mont_reduce_order_7         sp_384_mont_reduce_7

/* Compare a with b in constant time.
 *
 * a  A single precision integer.
 * b  A single precision integer.
 * return -ve, 0 or +ve if a is less than, equal to or greater than b
 * respectively.
 */
static sp_digit sp_384_cmp_7(const sp_digit* a, const sp_digit* b)
{
    sp_digit r = 0;
#ifdef WOLFSSL_SP_SMALL
    int i;

    for (i=6; i>=0; i--) {
        r |= (a[i] - b[i]) & (0 - ((r == 0) ? (sp_digit)1 : (sp_digit)0));
    }
#else
    r |= (a[ 6] - b[ 6]) & (0 - ((r == 0) ? (sp_digit)1 : (sp_digit)0));
    r |= (a[ 5] - b[ 5]) & (0 - ((r == 0) ? (sp_digit)1 : (sp_digit)0));
    r |= (a[ 4] - b[ 4]) & (0 - ((r == 0) ? (sp_digit)1 : (sp_digit)0));
    r |= (a[ 3] - b[ 3]) & (0 - ((r == 0) ? (sp_digit)1 : (sp_digit)0));
    r |= (a[ 2] - b[ 2]) & (0 - ((r == 0) ? (sp_digit)1 : (sp_digit)0));
    r |= (a[ 1] - b[ 1]) & (0 - ((r == 0) ? (sp_digit)1 : (sp_digit)0));
    r |= (a[ 0] - b[ 0]) & (0 - ((r == 0) ? (sp_digit)1 : (sp_digit)0));
#endif /* WOLFSSL_SP_SMALL */

    return r;
}

/* Conditionally subtract b from a using the mask m.
 * m is -1 to subtract and 0 when not.
 *
 * r  A single precision number representing condition subtract result.
 * a  A single precision number to subtract from.
 * b  A single precision number to subtract.
 * m  Mask value to apply.
 */
static void sp_384_cond_sub_7(sp_digit* r, const sp_digit* a,
        const sp_digit* b, const sp_digit m)
{
#ifdef WOLFSSL_SP_SMALL
    int i;

    for (i = 0; i < 7; i++) {
        r[i] = a[i] - (b[i] & m);
    }
#else
    r[ 0] = a[ 0] - (b[ 0] & m);
    r[ 1] = a[ 1] - (b[ 1] & m);
    r[ 2] = a[ 2] - (b[ 2] & m);
    r[ 3] = a[ 3] - (b[ 3] & m);
    r[ 4] = a[ 4] - (b[ 4] & m);
    r[ 5] = a[ 5] - (b[ 5] & m);
    r[ 6] = a[ 6] - (b[ 6] & m);
#endif /* WOLFSSL_SP_SMALL */
}

/* Mul a by scalar b and add into r. (r += a * b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A scalar.
 */
SP_NOINLINE static void sp_384_mul_add_7(sp_digit* r, const sp_digit* a,
        const sp_digit b)
{
#ifdef WOLFSSL_SP_SMALL
    int128_t tb = b;
    int128_t t = 0;
    int i;

    for (i = 0; i < 7; i++) {
        t += (tb * a[i]) + r[i];
        r[i] = t & 0x7fffffffffffffL;
        t >>= 55;
    }
    r[7] += t;
#else
    int128_t tb = b;
    int128_t t[7];

    t[ 0] = tb * a[ 0];
    t[ 1] = tb * a[ 1];
    t[ 2] = tb * a[ 2];
    t[ 3] = tb * a[ 3];
    t[ 4] = tb * a[ 4];
    t[ 5] = tb * a[ 5];
    t[ 6] = tb * a[ 6];
    r[ 0] += (sp_digit)                 (t[ 0] & 0x7fffffffffffffL);
    r[ 1] += (sp_digit)((t[ 0] >> 55) + (t[ 1] & 0x7fffffffffffffL));
    r[ 2] += (sp_digit)((t[ 1] >> 55) + (t[ 2] & 0x7fffffffffffffL));
    r[ 3] += (sp_digit)((t[ 2] >> 55) + (t[ 3] & 0x7fffffffffffffL));
    r[ 4] += (sp_digit)((t[ 3] >> 55) + (t[ 4] & 0x7fffffffffffffL));
    r[ 5] += (sp_digit)((t[ 4] >> 55) + (t[ 5] & 0x7fffffffffffffL));
    r[ 6] += (sp_digit)((t[ 5] >> 55) + (t[ 6] & 0x7fffffffffffffL));
    r[ 7] += (sp_digit) (t[ 6] >> 55);
#endif /* WOLFSSL_SP_SMALL */
}

/* Normalize the values in each word to 55.
 *
 * a  Array of sp_digit to normalize.
 */
static void sp_384_norm_7(sp_digit* a)
{
#ifdef WOLFSSL_SP_SMALL
    int i;
    for (i = 0; i < 6; i++) {
        a[i+1] += a[i] >> 55;
        a[i] &= 0x7fffffffffffffL;
    }
#else
    a[1] += a[0] >> 55; a[0] &= 0x7fffffffffffffL;
    a[2] += a[1] >> 55; a[1] &= 0x7fffffffffffffL;
    a[3] += a[2] >> 55; a[2] &= 0x7fffffffffffffL;
    a[4] += a[3] >> 55; a[3] &= 0x7fffffffffffffL;
    a[5] += a[4] >> 55; a[4] &= 0x7fffffffffffffL;
    a[6] += a[5] >> 55; a[5] &= 0x7fffffffffffffL;
#endif
}

/* Shift the result in the high 384 bits down to the bottom.
 *
 * r  A single precision number.
 * a  A single precision number.
 */
static void sp_384_mont_shift_7(sp_digit* r, const sp_digit* a)
{
#ifdef WOLFSSL_SP_SMALL
    int i;
    word64 n;

    n = a[6] >> 54;
    for (i = 0; i < 6; i++) {
        n += (word64)a[7 + i] << 1;
        r[i] = n & 0x7fffffffffffffL;
        n >>= 55;
    }
    n += (word64)a[13] << 1;
    r[6] = n;
#else
    word64 n;

    n  = a[6] >> 54;
    n += (word64)a[ 7] << 1U; r[ 0] = n & 0x7fffffffffffffUL; n >>= 55U;
    n += (word64)a[ 8] << 1U; r[ 1] = n & 0x7fffffffffffffUL; n >>= 55U;
    n += (word64)a[ 9] << 1U; r[ 2] = n & 0x7fffffffffffffUL; n >>= 55U;
    n += (word64)a[10] << 1U; r[ 3] = n & 0x7fffffffffffffUL; n >>= 55U;
    n += (word64)a[11] << 1U; r[ 4] = n & 0x7fffffffffffffUL; n >>= 55U;
    n += (word64)a[12] << 1U; r[ 5] = n & 0x7fffffffffffffUL; n >>= 55U;
    n += (word64)a[13] << 1U; r[ 6] = n;
#endif /* WOLFSSL_SP_SMALL */
    XMEMSET(&r[7], 0, sizeof(*r) * 7U);
}

/* Reduce the number back to 384 bits using Montgomery reduction.
 *
 * a   A single precision number to reduce in place.
 * m   The single precision number representing the modulus.
 * mp  The digit representing the negative inverse of m mod 2^n.
 */
static void sp_384_mont_reduce_7(sp_digit* a, const sp_digit* m, sp_digit mp)
{
    int i;
    sp_digit mu;

    sp_384_norm_7(a + 7);

    for (i=0; i<6; i++) {
        mu = (a[i] * mp) & 0x7fffffffffffffL;
        sp_384_mul_add_7(a+i, m, mu);
        a[i+1] += a[i] >> 55;
    }
    mu = (a[i] * mp) & 0x3fffffffffffffL;
    sp_384_mul_add_7(a+i, m, mu);
    a[i+1] += a[i] >> 55;
    a[i] &= 0x7fffffffffffffL;

    sp_384_mont_shift_7(a, a);
    sp_384_cond_sub_7(a, a, m, 0 - (((a[6] >> 54) > 0) ?
            (sp_digit)1 : (sp_digit)0));
    sp_384_norm_7(a);
}

/* Multiply two Montogmery form numbers mod the modulus (prime).
 * (r = a * b mod m)
 *
 * r   Result of multiplication.
 * a   First number to multiply in Montogmery form.
 * b   Second number to multiply in Montogmery form.
 * m   Modulus (prime).
 * mp  Montogmery mulitplier.
 */
static void sp_384_mont_mul_7(sp_digit* r, const sp_digit* a, const sp_digit* b,
        const sp_digit* m, sp_digit mp)
{
    sp_384_mul_7(r, a, b);
    sp_384_mont_reduce_7(r, m, mp);
}

#ifdef WOLFSSL_SP_SMALL
/* Square a and put result in r. (r = a * a)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 */
SP_NOINLINE static void sp_384_sqr_7(sp_digit* r, const sp_digit* a)
{
    int i, j, k;
    int128_t c;

    c = ((int128_t)a[6]) * a[6];
    r[13] = (sp_digit)(c >> 55);
    c = (c & 0x7fffffffffffffL) << 55;
    for (k = 11; k >= 0; k--) {
        for (i = 6; i >= 0; i--) {
            j = k - i;
            if (j >= 7 || i <= j) {
                break;
            }
            if (j < 0) {
                continue;
            }

            c += ((int128_t)a[i]) * a[j] * 2;
        }
        if (i == j) {
           c += ((int128_t)a[i]) * a[i];
        }

        r[k + 2] += c >> 110;
        r[k + 1] = (c >> 55) & 0x7fffffffffffffL;
        c = (c & 0x7fffffffffffffL) << 55;
    }
    r[0] = (sp_digit)(c >> 55);
}

#else
/* Square a and put result in r. (r = a * a)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 */
SP_NOINLINE static void sp_384_sqr_7(sp_digit* r, const sp_digit* a)
{
    int128_t t0   =  ((int128_t)a[ 0]) * a[ 0];
    int128_t t1   = (((int128_t)a[ 0]) * a[ 1]) * 2;
    int128_t t2   = (((int128_t)a[ 0]) * a[ 2]) * 2
                 +  ((int128_t)a[ 1]) * a[ 1];
    int128_t t3   = (((int128_t)a[ 0]) * a[ 3]
                 +  ((int128_t)a[ 1]) * a[ 2]) * 2;
    int128_t t4   = (((int128_t)a[ 0]) * a[ 4]
                 +  ((int128_t)a[ 1]) * a[ 3]) * 2
                 +  ((int128_t)a[ 2]) * a[ 2];
    int128_t t5   = (((int128_t)a[ 0]) * a[ 5]
                 +  ((int128_t)a[ 1]) * a[ 4]
                 +  ((int128_t)a[ 2]) * a[ 3]) * 2;
    int128_t t6   = (((int128_t)a[ 0]) * a[ 6]
                 +  ((int128_t)a[ 1]) * a[ 5]
                 +  ((int128_t)a[ 2]) * a[ 4]) * 2
                 +  ((int128_t)a[ 3]) * a[ 3];
    int128_t t7   = (((int128_t)a[ 1]) * a[ 6]
                 +  ((int128_t)a[ 2]) * a[ 5]
                 +  ((int128_t)a[ 3]) * a[ 4]) * 2;
    int128_t t8   = (((int128_t)a[ 2]) * a[ 6]
                 +  ((int128_t)a[ 3]) * a[ 5]) * 2
                 +  ((int128_t)a[ 4]) * a[ 4];
    int128_t t9   = (((int128_t)a[ 3]) * a[ 6]
                 +  ((int128_t)a[ 4]) * a[ 5]) * 2;
    int128_t t10  = (((int128_t)a[ 4]) * a[ 6]) * 2
                 +  ((int128_t)a[ 5]) * a[ 5];
    int128_t t11  = (((int128_t)a[ 5]) * a[ 6]) * 2;
    int128_t t12  =  ((int128_t)a[ 6]) * a[ 6];

    t1   += t0  >> 55; r[ 0] = t0  & 0x7fffffffffffffL;
    t2   += t1  >> 55; r[ 1] = t1  & 0x7fffffffffffffL;
    t3   += t2  >> 55; r[ 2] = t2  & 0x7fffffffffffffL;
    t4   += t3  >> 55; r[ 3] = t3  & 0x7fffffffffffffL;
    t5   += t4  >> 55; r[ 4] = t4  & 0x7fffffffffffffL;
    t6   += t5  >> 55; r[ 5] = t5  & 0x7fffffffffffffL;
    t7   += t6  >> 55; r[ 6] = t6  & 0x7fffffffffffffL;
    t8   += t7  >> 55; r[ 7] = t7  & 0x7fffffffffffffL;
    t9   += t8  >> 55; r[ 8] = t8  & 0x7fffffffffffffL;
    t10  += t9  >> 55; r[ 9] = t9  & 0x7fffffffffffffL;
    t11  += t10 >> 55; r[10] = t10 & 0x7fffffffffffffL;
    t12  += t11 >> 55; r[11] = t11 & 0x7fffffffffffffL;
    r[13] = (sp_digit)(t12 >> 55);
                       r[12] = t12 & 0x7fffffffffffffL;
}

#endif /* WOLFSSL_SP_SMALL */
/* Square the Montgomery form number. (r = a * a mod m)
 *
 * r   Result of squaring.
 * a   Number to square in Montogmery form.
 * m   Modulus (prime).
 * mp  Montogmery mulitplier.
 */
static void sp_384_mont_sqr_7(sp_digit* r, const sp_digit* a, const sp_digit* m,
        sp_digit mp)
{
    sp_384_sqr_7(r, a);
    sp_384_mont_reduce_7(r, m, mp);
}

#if !defined(WOLFSSL_SP_SMALL) || defined(HAVE_COMP_KEY)
/* Square the Montgomery form number a number of times. (r = a ^ n mod m)
 *
 * r   Result of squaring.
 * a   Number to square in Montogmery form.
 * n   Number of times to square.
 * m   Modulus (prime).
 * mp  Montogmery mulitplier.
 */
static void sp_384_mont_sqr_n_7(sp_digit* r, const sp_digit* a, int n,
        const sp_digit* m, sp_digit mp)
{
    sp_384_mont_sqr_7(r, a, m, mp);
    for (; n > 1; n--) {
        sp_384_mont_sqr_7(r, r, m, mp);
    }
}

#endif /* !WOLFSSL_SP_SMALL || HAVE_COMP_KEY */
#ifdef WOLFSSL_SP_SMALL
/* Mod-2 for the P384 curve. */
static const uint64_t p384_mod_minus_2[6] = {
    0x00000000fffffffdU,0xffffffff00000000U,0xfffffffffffffffeU,
    0xffffffffffffffffU,0xffffffffffffffffU,0xffffffffffffffffU
};
#endif /* !WOLFSSL_SP_SMALL */

/* Invert the number, in Montgomery form, modulo the modulus (prime) of the
 * P384 curve. (r = 1 / a mod m)
 *
 * r   Inverse result.
 * a   Number to invert.
 * td  Temporary data.
 */
static void sp_384_mont_inv_7(sp_digit* r, const sp_digit* a, sp_digit* td)
{
#ifdef WOLFSSL_SP_SMALL
    sp_digit* t = td;
    int i;

    XMEMCPY(t, a, sizeof(sp_digit) * 7);
    for (i=382; i>=0; i--) {
        sp_384_mont_sqr_7(t, t, p384_mod, p384_mp_mod);
        if (p384_mod_minus_2[i / 64] & ((sp_digit)1 << (i % 64)))
            sp_384_mont_mul_7(t, t, a, p384_mod, p384_mp_mod);
    }
    XMEMCPY(r, t, sizeof(sp_digit) * 7);
#else
    sp_digit* t1 = td;
    sp_digit* t2 = td + 2 * 7;
    sp_digit* t3 = td + 4 * 7;
    sp_digit* t4 = td + 6 * 7;
    sp_digit* t5 = td + 8 * 7;

    /* 0x2 */
    sp_384_mont_sqr_7(t1, a, p384_mod, p384_mp_mod);
    /* 0x3 */
    sp_384_mont_mul_7(t5, t1, a, p384_mod, p384_mp_mod);
    /* 0xc */
    sp_384_mont_sqr_n_7(t1, t5, 2, p384_mod, p384_mp_mod);
    /* 0xf */
    sp_384_mont_mul_7(t2, t5, t1, p384_mod, p384_mp_mod);
    /* 0x1e */
    sp_384_mont_sqr_7(t1, t2, p384_mod, p384_mp_mod);
    /* 0x1f */
    sp_384_mont_mul_7(t4, t1, a, p384_mod, p384_mp_mod);
    /* 0x3e0 */
    sp_384_mont_sqr_n_7(t1, t4, 5, p384_mod, p384_mp_mod);
    /* 0x3ff */
    sp_384_mont_mul_7(t2, t4, t1, p384_mod, p384_mp_mod);
    /* 0x7fe0 */
    sp_384_mont_sqr_n_7(t1, t2, 5, p384_mod, p384_mp_mod);
    /* 0x7fff */
    sp_384_mont_mul_7(t4, t4, t1, p384_mod, p384_mp_mod);
    /* 0x3fff8000 */
    sp_384_mont_sqr_n_7(t1, t4, 15, p384_mod, p384_mp_mod);
    /* 0x3fffffff */
    sp_384_mont_mul_7(t2, t4, t1, p384_mod, p384_mp_mod);
    /* 0xfffffffc */
    sp_384_mont_sqr_n_7(t3, t2, 2, p384_mod, p384_mp_mod);
    /* 0xfffffffd */
    sp_384_mont_mul_7(r, t3, a, p384_mod, p384_mp_mod);
    /* 0xffffffff */
    sp_384_mont_mul_7(t3, t5, t3, p384_mod, p384_mp_mod);
    /* 0xfffffffc0000000 */
    sp_384_mont_sqr_n_7(t1, t2, 30, p384_mod, p384_mp_mod);
    /* 0xfffffffffffffff */
    sp_384_mont_mul_7(t2, t2, t1, p384_mod, p384_mp_mod);
    /* 0xfffffffffffffff000000000000000 */
    sp_384_mont_sqr_n_7(t1, t2, 60, p384_mod, p384_mp_mod);
    /* 0xffffffffffffffffffffffffffffff */
    sp_384_mont_mul_7(t2, t2, t1, p384_mod, p384_mp_mod);
    /* 0xffffffffffffffffffffffffffffff000000000000000000000000000000 */
    sp_384_mont_sqr_n_7(t1, t2, 120, p384_mod, p384_mp_mod);
    /* 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff */
    sp_384_mont_mul_7(t2, t2, t1, p384_mod, p384_mp_mod);
    /* 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8000 */
    sp_384_mont_sqr_n_7(t1, t2, 15, p384_mod, p384_mp_mod);
    /* 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff */
    sp_384_mont_mul_7(t2, t4, t1, p384_mod, p384_mp_mod);
    /* 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe00000000 */
    sp_384_mont_sqr_n_7(t1, t2, 33, p384_mod, p384_mp_mod);
    /* 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff */
    sp_384_mont_mul_7(t2, t3, t1, p384_mod, p384_mp_mod);
    /* 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff000000000000000000000000 */
    sp_384_mont_sqr_n_7(t1, t2, 96, p384_mod, p384_mp_mod);
    /* 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff0000000000000000fffffffd */
    sp_384_mont_mul_7(r, r, t1, p384_mod, p384_mp_mod);

#endif /* WOLFSSL_SP_SMALL */
}

/* Map the Montgomery form projective coordinate point to an affine point.
 *
 * r  Resulting affine coordinate point.
 * p  Montgomery form projective coordinate point.
 * t  Temporary ordinate data.
 */
static void sp_384_map_7(sp_point_384* r, const sp_point_384* p, sp_digit* t)
{
    sp_digit* t1 = t;
    sp_digit* t2 = t + 2*7;
    int64_t n;

    sp_384_mont_inv_7(t1, p->z, t + 2*7);

    sp_384_mont_sqr_7(t2, t1, p384_mod, p384_mp_mod);
    sp_384_mont_mul_7(t1, t2, t1, p384_mod, p384_mp_mod);

    /* x /= z^2 */
    sp_384_mont_mul_7(r->x, p->x, t2, p384_mod, p384_mp_mod);
    XMEMSET(r->x + 7, 0, sizeof(r->x) / 2U);
    sp_384_mont_reduce_7(r->x, p384_mod, p384_mp_mod);
    /* Reduce x to less than modulus */
    n = sp_384_cmp_7(r->x, p384_mod);
    sp_384_cond_sub_7(r->x, r->x, p384_mod, 0 - ((n >= 0) ?
                (sp_digit)1 : (sp_digit)0));
    sp_384_norm_7(r->x);

    /* y /= z^3 */
    sp_384_mont_mul_7(r->y, p->y, t1, p384_mod, p384_mp_mod);
    XMEMSET(r->y + 7, 0, sizeof(r->y) / 2U);
    sp_384_mont_reduce_7(r->y, p384_mod, p384_mp_mod);
    /* Reduce y to less than modulus */
    n = sp_384_cmp_7(r->y, p384_mod);
    sp_384_cond_sub_7(r->y, r->y, p384_mod, 0 - ((n >= 0) ?
                (sp_digit)1 : (sp_digit)0));
    sp_384_norm_7(r->y);

    XMEMSET(r->z, 0, sizeof(r->z));
    r->z[0] = 1;

}

#ifdef WOLFSSL_SP_SMALL
/* Add b to a into r. (r = a + b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A single precision integer.
 */
SP_NOINLINE static int sp_384_add_7(sp_digit* r, const sp_digit* a,
        const sp_digit* b)
{
    int i;

    for (i = 0; i < 7; i++) {
        r[i] = a[i] + b[i];
    }

    return 0;
}
#else
/* Add b to a into r. (r = a + b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A single precision integer.
 */
SP_NOINLINE static int sp_384_add_7(sp_digit* r, const sp_digit* a,
        const sp_digit* b)
{
    r[ 0] = a[ 0] + b[ 0];
    r[ 1] = a[ 1] + b[ 1];
    r[ 2] = a[ 2] + b[ 2];
    r[ 3] = a[ 3] + b[ 3];
    r[ 4] = a[ 4] + b[ 4];
    r[ 5] = a[ 5] + b[ 5];
    r[ 6] = a[ 6] + b[ 6];

    return 0;
}

#endif /* WOLFSSL_SP_SMALL */
/* Add two Montgomery form numbers (r = a + b % m).
 *
 * r   Result of addition.
 * a   First number to add in Montogmery form.
 * b   Second number to add in Montogmery form.
 * m   Modulus (prime).
 */
static void sp_384_mont_add_7(sp_digit* r, const sp_digit* a, const sp_digit* b,
        const sp_digit* m)
{
    (void)sp_384_add_7(r, a, b);
    sp_384_norm_7(r);
    sp_384_cond_sub_7(r, r, m, 0 - (((r[6] >> 54) > 0) ?
                (sp_digit)1 : (sp_digit)0));
    sp_384_norm_7(r);
}

/* Double a Montgomery form number (r = a + a % m).
 *
 * r   Result of doubling.
 * a   Number to double in Montogmery form.
 * m   Modulus (prime).
 */
static void sp_384_mont_dbl_7(sp_digit* r, const sp_digit* a, const sp_digit* m)
{
    (void)sp_384_add_7(r, a, a);
    sp_384_norm_7(r);
    sp_384_cond_sub_7(r, r, m, 0 - (((r[6] >> 54) > 0) ?
                (sp_digit)1 : (sp_digit)0));
    sp_384_norm_7(r);
}

/* Triple a Montgomery form number (r = a + a + a % m).
 *
 * r   Result of Tripling.
 * a   Number to triple in Montogmery form.
 * m   Modulus (prime).
 */
static void sp_384_mont_tpl_7(sp_digit* r, const sp_digit* a, const sp_digit* m)
{
    (void)sp_384_add_7(r, a, a);
    sp_384_norm_7(r);
    sp_384_cond_sub_7(r, r, m, 0 - (((r[6] >> 54) > 0) ?
                (sp_digit)1 : (sp_digit)0));
    sp_384_norm_7(r);
    (void)sp_384_add_7(r, r, a);
    sp_384_norm_7(r);
    sp_384_cond_sub_7(r, r, m, 0 - (((r[6] >> 54) > 0) ?
                (sp_digit)1 : (sp_digit)0));
    sp_384_norm_7(r);
}

#ifdef WOLFSSL_SP_SMALL
/* Sub b from a into r. (r = a - b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A single precision integer.
 */
SP_NOINLINE static int sp_384_sub_7(sp_digit* r, const sp_digit* a,
        const sp_digit* b)
{
    int i;

    for (i = 0; i < 7; i++) {
        r[i] = a[i] - b[i];
    }

    return 0;
}

#else
/* Sub b from a into r. (r = a - b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A single precision integer.
 */
SP_NOINLINE static int sp_384_sub_7(sp_digit* r, const sp_digit* a,
        const sp_digit* b)
{
    r[ 0] = a[ 0] - b[ 0];
    r[ 1] = a[ 1] - b[ 1];
    r[ 2] = a[ 2] - b[ 2];
    r[ 3] = a[ 3] - b[ 3];
    r[ 4] = a[ 4] - b[ 4];
    r[ 5] = a[ 5] - b[ 5];
    r[ 6] = a[ 6] - b[ 6];

    return 0;
}

#endif /* WOLFSSL_SP_SMALL */
/* Conditionally add a and b using the mask m.
 * m is -1 to add and 0 when not.
 *
 * r  A single precision number representing conditional add result.
 * a  A single precision number to add with.
 * b  A single precision number to add.
 * m  Mask value to apply.
 */
static void sp_384_cond_add_7(sp_digit* r, const sp_digit* a,
        const sp_digit* b, const sp_digit m)
{
#ifdef WOLFSSL_SP_SMALL
    int i;

    for (i = 0; i < 7; i++) {
        r[i] = a[i] + (b[i] & m);
    }
#else
    r[ 0] = a[ 0] + (b[ 0] & m);
    r[ 1] = a[ 1] + (b[ 1] & m);
    r[ 2] = a[ 2] + (b[ 2] & m);
    r[ 3] = a[ 3] + (b[ 3] & m);
    r[ 4] = a[ 4] + (b[ 4] & m);
    r[ 5] = a[ 5] + (b[ 5] & m);
    r[ 6] = a[ 6] + (b[ 6] & m);
#endif /* WOLFSSL_SP_SMALL */
}

/* Subtract two Montgomery form numbers (r = a - b % m).
 *
 * r   Result of subtration.
 * a   Number to subtract from in Montogmery form.
 * b   Number to subtract with in Montogmery form.
 * m   Modulus (prime).
 */
static void sp_384_mont_sub_7(sp_digit* r, const sp_digit* a, const sp_digit* b,
        const sp_digit* m)
{
    (void)sp_384_sub_7(r, a, b);
    sp_384_cond_add_7(r, r, m, r[6] >> 54);
    sp_384_norm_7(r);
}

/* Shift number left one bit.
 * Bottom bit is lost.
 *
 * r  Result of shift.
 * a  Number to shift.
 */
SP_NOINLINE static void sp_384_rshift1_7(sp_digit* r, sp_digit* a)
{
#ifdef WOLFSSL_SP_SMALL
    int i;

    for (i=0; i<6; i++) {
        r[i] = ((a[i] >> 1) | (a[i + 1] << 54)) & 0x7fffffffffffffL;
    }
#else
    r[0] = ((a[0] >> 1) | (a[1] << 54)) & 0x7fffffffffffffL;
    r[1] = ((a[1] >> 1) | (a[2] << 54)) & 0x7fffffffffffffL;
    r[2] = ((a[2] >> 1) | (a[3] << 54)) & 0x7fffffffffffffL;
    r[3] = ((a[3] >> 1) | (a[4] << 54)) & 0x7fffffffffffffL;
    r[4] = ((a[4] >> 1) | (a[5] << 54)) & 0x7fffffffffffffL;
    r[5] = ((a[5] >> 1) | (a[6] << 54)) & 0x7fffffffffffffL;
#endif
    r[6] = a[6] >> 1;
}

/* Divide the number by 2 mod the modulus (prime). (r = a / 2 % m)
 *
 * r  Result of division by 2.
 * a  Number to divide.
 * m  Modulus (prime).
 */
static void sp_384_div2_7(sp_digit* r, const sp_digit* a, const sp_digit* m)
{
    sp_384_cond_add_7(r, a, m, 0 - (a[0] & 1));
    sp_384_norm_7(r);
    sp_384_rshift1_7(r, r);
}

/* Double the Montgomery form projective point p.
 *
 * r  Result of doubling point.
 * p  Point to double.
 * t  Temporary ordinate data.
 */
#ifdef WOLFSSL_SP_NONBLOCK
typedef struct sp_384_proj_point_dbl_7_ctx {
    int state;
    sp_digit* t1;
    sp_digit* t2;
    sp_digit* x;
    sp_digit* y;
    sp_digit* z;
} sp_384_proj_point_dbl_7_ctx;

static int sp_384_proj_point_dbl_7_nb(sp_ecc_ctx_t* sp_ctx, sp_point_384* r, const sp_point_384* p, sp_digit* t)
{
    int err = FP_WOULDBLOCK;
    sp_384_proj_point_dbl_7_ctx* ctx = (sp_384_proj_point_dbl_7_ctx*)sp_ctx->data;

    typedef char ctx_size_test[sizeof(sp_384_proj_point_dbl_7_ctx) >= sizeof(*sp_ctx) ? -1 : 1];
    (void)sizeof(ctx_size_test);

    switch (ctx->state) {
    case 0:
        ctx->t1 = t;
        ctx->t2 = t + 2*7;
        ctx->x = r->x;
        ctx->y = r->y;
        ctx->z = r->z;

        /* Put infinity into result. */
        if (r != p) {
            r->infinity = p->infinity;
        }
        ctx->state = 1;
        break;
    case 1:
        /* T1 = Z * Z */
        sp_384_mont_sqr_7(ctx->t1, p->z, p384_mod, p384_mp_mod);
        ctx->state = 2;
        break;
    case 2:
        /* Z = Y * Z */
        sp_384_mont_mul_7(ctx->z, p->y, p->z, p384_mod, p384_mp_mod);
        ctx->state = 3;
        break;
    case 3:
        /* Z = 2Z */
        sp_384_mont_dbl_7(ctx->z, ctx->z, p384_mod);
        ctx->state = 4;
        break;
    case 4:
        /* T2 = X - T1 */
        sp_384_mont_sub_7(ctx->t2, p->x, ctx->t1, p384_mod);
        ctx->state = 5;
        break;
    case 5:
        /* T1 = X + T1 */
        sp_384_mont_add_7(ctx->t1, p->x, ctx->t1, p384_mod);
        ctx->state = 6;
        break;
    case 6:
        /* T2 = T1 * T2 */
        sp_384_mont_mul_7(ctx->t2, ctx->t1, ctx->t2, p384_mod, p384_mp_mod);
        ctx->state = 7;
        break;
    case 7:
        /* T1 = 3T2 */
        sp_384_mont_tpl_7(ctx->t1, ctx->t2, p384_mod);
        ctx->state = 8;
        break;
    case 8:
        /* Y = 2Y */
        sp_384_mont_dbl_7(ctx->y, p->y, p384_mod);
        ctx->state = 9;
        break;
    case 9:
        /* Y = Y * Y */
        sp_384_mont_sqr_7(ctx->y, ctx->y, p384_mod, p384_mp_mod);
        ctx->state = 10;
        break;
    case 10:
        /* T2 = Y * Y */
        sp_384_mont_sqr_7(ctx->t2, ctx->y, p384_mod, p384_mp_mod);
        ctx->state = 11;
        break;
    case 11:
        /* T2 = T2/2 */
        sp_384_div2_7(ctx->t2, ctx->t2, p384_mod);
        ctx->state = 12;
        break;
    case 12:
        /* Y = Y * X */
        sp_384_mont_mul_7(ctx->y, ctx->y, p->x, p384_mod, p384_mp_mod);
        ctx->state = 13;
        break;
    case 13:
        /* X = T1 * T1 */
        sp_384_mont_sqr_7(ctx->x, ctx->t1, p384_mod, p384_mp_mod);
        ctx->state = 14;
        break;
    case 14:
        /* X = X - Y */
        sp_384_mont_sub_7(ctx->x, ctx->x, ctx->y, p384_mod);
        ctx->state = 15;
        break;
    case 15:
        /* X = X - Y */
        sp_384_mont_sub_7(ctx->x, ctx->x, ctx->y, p384_mod);
        ctx->state = 16;
        break;
    case 16:
        /* Y = Y - X */
        sp_384_mont_sub_7(ctx->y, ctx->y, ctx->x, p384_mod);
        ctx->state = 17;
        break;
    case 17:
        /* Y = Y * T1 */
        sp_384_mont_mul_7(ctx->y, ctx->y, ctx->t1, p384_mod, p384_mp_mod);
        ctx->state = 18;
        break;
    case 18:
        /* Y = Y - T2 */
        sp_384_mont_sub_7(ctx->y, ctx->y, ctx->t2, p384_mod);
        ctx->state = 19;
        /* fall-through */
    case 19:
        err = MP_OKAY;
        break;
    }

    if (err == MP_OKAY && ctx->state != 19) {
        err = FP_WOULDBLOCK;
    }

    return err;
}
#endif /* WOLFSSL_SP_NONBLOCK */

static void sp_384_proj_point_dbl_7(sp_point_384* r, const sp_point_384* p, sp_digit* t)
{
    sp_digit* t1 = t;
    sp_digit* t2 = t + 2*7;
    sp_digit* x;
    sp_digit* y;
    sp_digit* z;

    x = r->x;
    y = r->y;
    z = r->z;
    /* Put infinity into result. */
    if (r != p) {
        r->infinity = p->infinity;
    }

    /* T1 = Z * Z */
    sp_384_mont_sqr_7(t1, p->z, p384_mod, p384_mp_mod);
    /* Z = Y * Z */
    sp_384_mont_mul_7(z, p->y, p->z, p384_mod, p384_mp_mod);
    /* Z = 2Z */
    sp_384_mont_dbl_7(z, z, p384_mod);
    /* T2 = X - T1 */
    sp_384_mont_sub_7(t2, p->x, t1, p384_mod);
    /* T1 = X + T1 */
    sp_384_mont_add_7(t1, p->x, t1, p384_mod);
    /* T2 = T1 * T2 */
    sp_384_mont_mul_7(t2, t1, t2, p384_mod, p384_mp_mod);
    /* T1 = 3T2 */
    sp_384_mont_tpl_7(t1, t2, p384_mod);
    /* Y = 2Y */
    sp_384_mont_dbl_7(y, p->y, p384_mod);
    /* Y = Y * Y */
    sp_384_mont_sqr_7(y, y, p384_mod, p384_mp_mod);
    /* T2 = Y * Y */
    sp_384_mont_sqr_7(t2, y, p384_mod, p384_mp_mod);
    /* T2 = T2/2 */
    sp_384_div2_7(t2, t2, p384_mod);
    /* Y = Y * X */
    sp_384_mont_mul_7(y, y, p->x, p384_mod, p384_mp_mod);
    /* X = T1 * T1 */
    sp_384_mont_sqr_7(x, t1, p384_mod, p384_mp_mod);
    /* X = X - Y */
    sp_384_mont_sub_7(x, x, y, p384_mod);
    /* X = X - Y */
    sp_384_mont_sub_7(x, x, y, p384_mod);
    /* Y = Y - X */
    sp_384_mont_sub_7(y, y, x, p384_mod);
    /* Y = Y * T1 */
    sp_384_mont_mul_7(y, y, t1, p384_mod, p384_mp_mod);
    /* Y = Y - T2 */
    sp_384_mont_sub_7(y, y, t2, p384_mod);
}

/* Compare two numbers to determine if they are equal.
 * Constant time implementation.
 *
 * a  First number to compare.
 * b  Second number to compare.
 * returns 1 when equal and 0 otherwise.
 */
static int sp_384_cmp_equal_7(const sp_digit* a, const sp_digit* b)
{
    return ((a[0] ^ b[0]) | (a[1] ^ b[1]) | (a[2] ^ b[2]) | (a[3] ^ b[3]) |
            (a[4] ^ b[4]) | (a[5] ^ b[5]) | (a[6] ^ b[6])) == 0;
}

/* Add two Montgomery form projective points.
 *
 * r  Result of addition.
 * p  First point to add.
 * q  Second point to add.
 * t  Temporary ordinate data.
 */

#ifdef WOLFSSL_SP_NONBLOCK
typedef struct sp_384_proj_point_add_7_ctx {
    int state;
    sp_384_proj_point_dbl_7_ctx dbl_ctx;
    const sp_point_384* ap[2];
    sp_point_384* rp[2];
    sp_digit* t1;
    sp_digit* t2;
    sp_digit* t3;
    sp_digit* t4;
    sp_digit* t5;
    sp_digit* x;
    sp_digit* y;
    sp_digit* z;
} sp_384_proj_point_add_7_ctx;

static int sp_384_proj_point_add_7_nb(sp_ecc_ctx_t* sp_ctx, sp_point_384* r, 
    const sp_point_384* p, const sp_point_384* q, sp_digit* t)
{
    int err = FP_WOULDBLOCK;
    sp_384_proj_point_add_7_ctx* ctx = (sp_384_proj_point_add_7_ctx*)sp_ctx->data;

    /* Ensure only the first point is the same as the result. */
    if (q == r) {
        const sp_point_384* a = p;
        p = q;
        q = a;
    }

    typedef char ctx_size_test[sizeof(sp_384_proj_point_add_7_ctx) >= sizeof(*sp_ctx) ? -1 : 1];
    (void)sizeof(ctx_size_test);

    switch (ctx->state) {
    case 0: /* INIT */
        ctx->t1 = t;
        ctx->t2 = t + 2*7;
        ctx->t3 = t + 4*7;
        ctx->t4 = t + 6*7;
        ctx->t5 = t + 8*7;

        ctx->state = 1;
        break;
    case 1:
        /* Check double */
        (void)sp_384_sub_7(ctx->t1, p384_mod, q->y);
        sp_384_norm_7(ctx->t1);
        if ((sp_384_cmp_equal_7(p->x, q->x) & sp_384_cmp_equal_7(p->z, q->z) &
            (sp_384_cmp_equal_7(p->y, q->y) | sp_384_cmp_equal_7(p->y, ctx->t1))) != 0)
        {
            XMEMSET(&ctx->dbl_ctx, 0, sizeof(ctx->dbl_ctx));
            ctx->state = 2;
        }
        else {
            ctx->state = 3;
        }
        break;
    case 2:
        err = sp_384_proj_point_dbl_7_nb((sp_ecc_ctx_t*)&ctx->dbl_ctx, r, p, t);
        if (err == MP_OKAY)
            ctx->state = 27; /* done */
        break;
    case 3:
    {
        int i;
        ctx->rp[0] = r;

        /*lint allow cast to different type of pointer*/
        ctx->rp[1] = (sp_point_384*)t; /*lint !e9087 !e740*/
        XMEMSET(ctx->rp[1], 0, sizeof(sp_point_384));
        ctx->x = ctx->rp[p->infinity | q->infinity]->x;
        ctx->y = ctx->rp[p->infinity | q->infinity]->y;
        ctx->z = ctx->rp[p->infinity | q->infinity]->z;

        ctx->ap[0] = p;
        ctx->ap[1] = q;
        for (i=0; i<7; i++) {
            r->x[i] = ctx->ap[p->infinity]->x[i];
        }
        for (i=0; i<7; i++) {
            r->y[i] = ctx->ap[p->infinity]->y[i];
        }
        for (i=0; i<7; i++) {
            r->z[i] = ctx->ap[p->infinity]->z[i];
        }
        r->infinity = ctx->ap[p->infinity]->infinity;

        ctx->state = 4;
        break;
    }
    case 4:
        /* U1 = X1*Z2^2 */
        sp_384_mont_sqr_7(ctx->t1, q->z, p384_mod, p384_mp_mod);
        ctx->state = 5;
        break;
    case 5:
        sp_384_mont_mul_7(ctx->t3, ctx->t1, q->z, p384_mod, p384_mp_mod);
        ctx->state = 6;
        break;
    case 6:
        sp_384_mont_mul_7(ctx->t1, ctx->t1, ctx->x, p384_mod, p384_mp_mod);
        ctx->state = 7;
        break;
    case 7:
        /* U2 = X2*Z1^2 */
        sp_384_mont_sqr_7(ctx->t2, ctx->z, p384_mod, p384_mp_mod);
        ctx->state = 8;
        break;
    case 8:
        sp_384_mont_mul_7(ctx->t4, ctx->t2, ctx->z, p384_mod, p384_mp_mod);
        ctx->state = 9;
        break;
    case 9:
        sp_384_mont_mul_7(ctx->t2, ctx->t2, q->x, p384_mod, p384_mp_mod);
        ctx->state = 10;
        break;
    case 10:
        /* S1 = Y1*Z2^3 */
        sp_384_mont_mul_7(ctx->t3, ctx->t3, ctx->y, p384_mod, p384_mp_mod);
        ctx->state = 11;
        break;
    case 11:
        /* S2 = Y2*Z1^3 */
        sp_384_mont_mul_7(ctx->t4, ctx->t4, q->y, p384_mod, p384_mp_mod);
        ctx->state = 12;
        break;
    case 12:
        /* H = U2 - U1 */
        sp_384_mont_sub_7(ctx->t2, ctx->t2, ctx->t1, p384_mod);
        ctx->state = 13;
        break;
    case 13:
        /* R = S2 - S1 */
        sp_384_mont_sub_7(ctx->t4, ctx->t4, ctx->t3, p384_mod);
        ctx->state = 14;
        break;
    case 14:
        /* Z3 = H*Z1*Z2 */
        sp_384_mont_mul_7(ctx->z, ctx->z, q->z, p384_mod, p384_mp_mod);
        ctx->state = 15;
        break;
    case 15:
        sp_384_mont_mul_7(ctx->z, ctx->z, ctx->t2, p384_mod, p384_mp_mod);
        ctx->state = 16;
        break;
    case 16:
        /* X3 = R^2 - H^3 - 2*U1*H^2 */
        sp_384_mont_sqr_7(ctx->x, ctx->t4, p384_mod, p384_mp_mod);
        ctx->state = 17;
        break;
    case 17:
        sp_384_mont_sqr_7(ctx->t5, ctx->t2, p384_mod, p384_mp_mod);
        ctx->state = 18;
        break;
    case 18:
        sp_384_mont_mul_7(ctx->y, ctx->t1, ctx->t5, p384_mod, p384_mp_mod);
        ctx->state = 19;
        break;
    case 19:
        sp_384_mont_mul_7(ctx->t5, ctx->t5, ctx->t2, p384_mod, p384_mp_mod);
        ctx->state = 20;
        break;
    case 20:
        sp_384_mont_sub_7(ctx->x, ctx->x, ctx->t5, p384_mod);
        ctx->state = 21;
        break;
    case 21:
        sp_384_mont_dbl_7(ctx->t1, ctx->y, p384_mod);
        ctx->state = 22;
        break;
    case 22:
        sp_384_mont_sub_7(ctx->x, ctx->x, ctx->t1, p384_mod);
        ctx->state = 23;
        break;
    case 23:
        /* Y3 = R*(U1*H^2 - X3) - S1*H^3 */
        sp_384_mont_sub_7(ctx->y, ctx->y, ctx->x, p384_mod);
        ctx->state = 24;
        break;
    case 24:
        sp_384_mont_mul_7(ctx->y, ctx->y, ctx->t4, p384_mod, p384_mp_mod);
        ctx->state = 25;
        break;
    case 25:
        sp_384_mont_mul_7(ctx->t5, ctx->t5, ctx->t3, p384_mod, p384_mp_mod);
        ctx->state = 26;
        break;
    case 26:
        sp_384_mont_sub_7(ctx->y, ctx->y, ctx->t5, p384_mod);
        ctx->state = 27;
        /* fall-through */
    case 27:
        err = MP_OKAY;
        break;
    }

    if (err == MP_OKAY && ctx->state != 27) {
        err = FP_WOULDBLOCK;
    }
    return err;
}
#endif /* WOLFSSL_SP_NONBLOCK */

static void sp_384_proj_point_add_7(sp_point_384* r, const sp_point_384* p, const sp_point_384* q,
        sp_digit* t)
{
    const sp_point_384* ap[2];
    sp_point_384* rp[2];
    sp_digit* t1 = t;
    sp_digit* t2 = t + 2*7;
    sp_digit* t3 = t + 4*7;
    sp_digit* t4 = t + 6*7;
    sp_digit* t5 = t + 8*7;
    sp_digit* x;
    sp_digit* y;
    sp_digit* z;
    int i;

    /* Ensure only the first point is the same as the result. */
    if (q == r) {
        const sp_point_384* a = p;
        p = q;
        q = a;
    }

    /* Check double */
    (void)sp_384_sub_7(t1, p384_mod, q->y);
    sp_384_norm_7(t1);
    if ((sp_384_cmp_equal_7(p->x, q->x) & sp_384_cmp_equal_7(p->z, q->z) &
        (sp_384_cmp_equal_7(p->y, q->y) | sp_384_cmp_equal_7(p->y, t1))) != 0) {
        sp_384_proj_point_dbl_7(r, p, t);
    }
    else {
        rp[0] = r;

        /*lint allow cast to different type of pointer*/
        rp[1] = (sp_point_384*)t; /*lint !e9087 !e740*/
        XMEMSET(rp[1], 0, sizeof(sp_point_384));
        x = rp[p->infinity | q->infinity]->x;
        y = rp[p->infinity | q->infinity]->y;
        z = rp[p->infinity | q->infinity]->z;

        ap[0] = p;
        ap[1] = q;
        for (i=0; i<7; i++) {
            r->x[i] = ap[p->infinity]->x[i];
        }
        for (i=0; i<7; i++) {
            r->y[i] = ap[p->infinity]->y[i];
        }
        for (i=0; i<7; i++) {
            r->z[i] = ap[p->infinity]->z[i];
        }
        r->infinity = ap[p->infinity]->infinity;

        /* U1 = X1*Z2^2 */
        sp_384_mont_sqr_7(t1, q->z, p384_mod, p384_mp_mod);
        sp_384_mont_mul_7(t3, t1, q->z, p384_mod, p384_mp_mod);
        sp_384_mont_mul_7(t1, t1, x, p384_mod, p384_mp_mod);
        /* U2 = X2*Z1^2 */
        sp_384_mont_sqr_7(t2, z, p384_mod, p384_mp_mod);
        sp_384_mont_mul_7(t4, t2, z, p384_mod, p384_mp_mod);
        sp_384_mont_mul_7(t2, t2, q->x, p384_mod, p384_mp_mod);
        /* S1 = Y1*Z2^3 */
        sp_384_mont_mul_7(t3, t3, y, p384_mod, p384_mp_mod);
        /* S2 = Y2*Z1^3 */
        sp_384_mont_mul_7(t4, t4, q->y, p384_mod, p384_mp_mod);
        /* H = U2 - U1 */
        sp_384_mont_sub_7(t2, t2, t1, p384_mod);
        /* R = S2 - S1 */
        sp_384_mont_sub_7(t4, t4, t3, p384_mod);
        /* Z3 = H*Z1*Z2 */
        sp_384_mont_mul_7(z, z, q->z, p384_mod, p384_mp_mod);
        sp_384_mont_mul_7(z, z, t2, p384_mod, p384_mp_mod);
        /* X3 = R^2 - H^3 - 2*U1*H^2 */
        sp_384_mont_sqr_7(x, t4, p384_mod, p384_mp_mod);
        sp_384_mont_sqr_7(t5, t2, p384_mod, p384_mp_mod);
        sp_384_mont_mul_7(y, t1, t5, p384_mod, p384_mp_mod);
        sp_384_mont_mul_7(t5, t5, t2, p384_mod, p384_mp_mod);
        sp_384_mont_sub_7(x, x, t5, p384_mod);
        sp_384_mont_dbl_7(t1, y, p384_mod);
        sp_384_mont_sub_7(x, x, t1, p384_mod);
        /* Y3 = R*(U1*H^2 - X3) - S1*H^3 */
        sp_384_mont_sub_7(y, y, x, p384_mod);
        sp_384_mont_mul_7(y, y, t4, p384_mod, p384_mp_mod);
        sp_384_mont_mul_7(t5, t5, t3, p384_mod, p384_mp_mod);
        sp_384_mont_sub_7(y, y, t5, p384_mod);
    }
}

#ifdef WOLFSSL_SP_SMALL
/* Multiply the point by the scalar and return the result.
 * If map is true then convert result to affine coordinates.
 *
 * r     Resulting point.
 * g     Point to multiply.
 * k     Scalar to multiply by.
 * map   Indicates whether to convert result to affine.
 * ct    Constant time required.
 * heap  Heap to use for allocation.
 * returns MEMORY_E when memory allocation fails and MP_OKAY on success.
 */

#ifdef WOLFSSL_SP_NONBLOCK
typedef struct sp_384_ecc_mulmod_7_ctx {
    int state;
    union {
        sp_384_proj_point_dbl_7_ctx dbl_ctx;
        sp_384_proj_point_add_7_ctx add_ctx;
    };
    sp_point_384 t[3];
    sp_digit tmp[2 * 7 * 6];
    sp_digit n;
    int i;
    int c;
    int y;
} sp_384_ecc_mulmod_7_ctx;

static int sp_384_ecc_mulmod_7_nb(sp_ecc_ctx_t* sp_ctx, sp_point_384* r, 
    const sp_point_384* g, const sp_digit* k, int map, int ct, void* heap)
{
    int err = FP_WOULDBLOCK;
    sp_384_ecc_mulmod_7_ctx* ctx = (sp_384_ecc_mulmod_7_ctx*)sp_ctx->data;

    typedef char ctx_size_test[sizeof(sp_384_ecc_mulmod_7_ctx) >= sizeof(*sp_ctx) ? -1 : 1];
    (void)sizeof(ctx_size_test);

    /* Implementation is constant time. */
    (void)ct;

    switch (ctx->state) {
    case 0: /* INIT */
        XMEMSET(ctx->t, 0, sizeof(sp_point_384) * 3);
        ctx->i = 6;
        ctx->c = 54;
        ctx->n = k[ctx->i--] << (55 - ctx->c);

        /* t[0] = {0, 0, 1} * norm */
        ctx->t[0].infinity = 1;
        ctx->state = 1;
        break;
    case 1: /* T1X */
        /* t[1] = {g->x, g->y, g->z} * norm */
        err = sp_384_mod_mul_norm_7(ctx->t[1].x, g->x, p384_mod);
        ctx->state = 2;
        break;
    case 2: /* T1Y */
        err = sp_384_mod_mul_norm_7(ctx->t[1].y, g->y, p384_mod);
        ctx->state = 3;
        break;
    case 3: /* T1Z */
        err = sp_384_mod_mul_norm_7(ctx->t[1].z, g->z, p384_mod);
        ctx->state = 4;
        break;
    case 4: /* ADDPREP */
        if (ctx->c == 0) {
            if (ctx->i == -1) {
                ctx->state = 7;
                break;
            }

            ctx->n = k[ctx->i--];
            ctx->c = 55;
        }
        ctx->y = (ctx->n >> 54) & 1;
        ctx->n <<= 1;
        XMEMSET(&ctx->add_ctx, 0, sizeof(ctx->add_ctx));
        ctx->state = 5;
        break;
    case 5: /* ADD */
        err = sp_384_proj_point_add_7_nb((sp_ecc_ctx_t*)&ctx->add_ctx, 
            &ctx->t[ctx->y^1], &ctx->t[0], &ctx->t[1], ctx->tmp);
        if (err == MP_OKAY) {
            XMEMCPY(&ctx->t[2], (void*)(((size_t)&ctx->t[0] & addr_mask[ctx->y^1]) +
                                        ((size_t)&ctx->t[1] & addr_mask[ctx->y])),
                    sizeof(sp_point_384));
            XMEMSET(&ctx->dbl_ctx, 0, sizeof(ctx->dbl_ctx));
            ctx->state = 6;
        }
        break;
    case 6: /* DBL */
        err = sp_384_proj_point_dbl_7_nb((sp_ecc_ctx_t*)&ctx->dbl_ctx, &ctx->t[2], 
            &ctx->t[2], ctx->tmp);
        if (err == MP_OKAY) {
            XMEMCPY((void*)(((size_t)&ctx->t[0] & addr_mask[ctx->y^1]) +
                            ((size_t)&ctx->t[1] & addr_mask[ctx->y])), &ctx->t[2],
                    sizeof(sp_point_384));
            ctx->state = 4;
            ctx->c--;
        }
        break;
    case 7: /* MAP */
        if (map != 0) {
            sp_384_map_7(r, &ctx->t[0], ctx->tmp);
        }
        else {
            XMEMCPY(r, &ctx->t[0], sizeof(sp_point_384));
        }
        err = MP_OKAY;
        break;
    }

    if (err == MP_OKAY && ctx->state != 7) {
        err = FP_WOULDBLOCK;
    }
    if (err != FP_WOULDBLOCK) {
        ForceZero(ctx->tmp, sizeof(ctx->tmp));
        ForceZero(ctx->t, sizeof(ctx->t));
    }

    (void)heap;

    return err;
}

#endif /* WOLFSSL_SP_NONBLOCK */

static int sp_384_ecc_mulmod_7(sp_point_384* r, const sp_point_384* g, const sp_digit* k,
        int map, int ct, void* heap)
{
#ifdef WOLFSSL_SP_NO_MALLOC
    sp_point_384 t[3];
    sp_digit tmp[2 * 7 * 6];
#else
    sp_point_384* t;
    sp_digit* tmp;
#endif
    sp_digit n;
    int i;
    int c, y;
    int err = MP_OKAY;

    /* Implementatio is constant time. */
    (void)ct;
    (void)heap;

#ifndef WOLFSSL_SP_NO_MALLOC
    t = (sp_point_384*)XMALLOC(sizeof(sp_point_384) * 3, heap, DYNAMIC_TYPE_ECC);
    if (t == NULL)
        err = MEMORY_E;
    tmp = (sp_digit*)XMALLOC(sizeof(sp_digit) * 2 * 7 * 6, heap,
                                                              DYNAMIC_TYPE_ECC);
    if (tmp == NULL)
        err = MEMORY_E;
#endif

    if (err == MP_OKAY) {
        XMEMSET(t, 0, sizeof(sp_point_384) * 3);

        /* t[0] = {0, 0, 1} * norm */
        t[0].infinity = 1;
        /* t[1] = {g->x, g->y, g->z} * norm */
        err = sp_384_mod_mul_norm_7(t[1].x, g->x, p384_mod);
    }
    if (err == MP_OKAY)
        err = sp_384_mod_mul_norm_7(t[1].y, g->y, p384_mod);
    if (err == MP_OKAY)
        err = sp_384_mod_mul_norm_7(t[1].z, g->z, p384_mod);

    if (err == MP_OKAY) {
        i = 6;
        c = 54;
        n = k[i--] << (55 - c);
        for (; ; c--) {
            if (c == 0) {
                if (i == -1)
                    break;

                n = k[i--];
                c = 55;
            }

            y = (n >> 54) & 1;
            n <<= 1;

            sp_384_proj_point_add_7(&t[y^1], &t[0], &t[1], tmp);

            XMEMCPY(&t[2], (void*)(((size_t)&t[0] & addr_mask[y^1]) +
                                   ((size_t)&t[1] & addr_mask[y])),
                    sizeof(sp_point_384));
            sp_384_proj_point_dbl_7(&t[2], &t[2], tmp);
            XMEMCPY((void*)(((size_t)&t[0] & addr_mask[y^1]) +
                            ((size_t)&t[1] & addr_mask[y])), &t[2],
                    sizeof(sp_point_384));
        }

        if (map != 0) {
            sp_384_map_7(r, &t[0], tmp);
        }
        else {
            XMEMCPY(r, &t[0], sizeof(sp_point_384));
        }
    }

#ifndef WOLFSSL_SP_NO_MALLOC
    if (tmp != NULL) {
        XMEMSET(tmp, 0, sizeof(sp_digit) * 2 * 7 * 6);
        XFREE(tmp, NULL, DYNAMIC_TYPE_ECC);
    }
    if (t != NULL) {
        XMEMSET(t, 0, sizeof(sp_point_384) * 3);
        XFREE(t, NULL, DYNAMIC_TYPE_ECC);
    }
#else
    ForceZero(tmp, sizeof(tmp));
    ForceZero(t, sizeof(t));
#endif

    return err;
}

#else
/* A table entry for pre-computed points. */
typedef struct sp_table_entry_384 {
    sp_digit x[7];
    sp_digit y[7];
} sp_table_entry_384;

/* Conditionally copy a into r using the mask m.
 * m is -1 to copy and 0 when not.
 *
 * r  A single precision number to copy over.
 * a  A single precision number to copy.
 * m  Mask value to apply.
 */
static void sp_384_cond_copy_7(sp_digit* r, const sp_digit* a, const sp_digit m)
{
    sp_digit t[7];
#ifdef WOLFSSL_SP_SMALL
    int i;

    for (i = 0; i < 7; i++) {
        t[i] = r[i] ^ a[i];
    }
    for (i = 0; i < 7; i++) {
        r[i] ^= t[i] & m;
    }
#else
    t[ 0] = r[ 0] ^ a[ 0];
    t[ 1] = r[ 1] ^ a[ 1];
    t[ 2] = r[ 2] ^ a[ 2];
    t[ 3] = r[ 3] ^ a[ 3];
    t[ 4] = r[ 4] ^ a[ 4];
    t[ 5] = r[ 5] ^ a[ 5];
    t[ 6] = r[ 6] ^ a[ 6];
    r[ 0] ^= t[ 0] & m;
    r[ 1] ^= t[ 1] & m;
    r[ 2] ^= t[ 2] & m;
    r[ 3] ^= t[ 3] & m;
    r[ 4] ^= t[ 4] & m;
    r[ 5] ^= t[ 5] & m;
    r[ 6] ^= t[ 6] & m;
#endif /* WOLFSSL_SP_SMALL */
}

/* Double the Montgomery form projective point p a number of times.
 *
 * r  Result of repeated doubling of point.
 * p  Point to double.
 * n  Number of times to double
 * t  Temporary ordinate data.
 */
static void sp_384_proj_point_dbl_n_7(sp_point_384* p, int n, sp_digit* t)
{
    sp_digit* w = t;
    sp_digit* a = t + 2*7;
    sp_digit* b = t + 4*7;
    sp_digit* t1 = t + 6*7;
    sp_digit* t2 = t + 8*7;
    sp_digit* x;
    sp_digit* y;
    sp_digit* z;

    x = p->x;
    y = p->y;
    z = p->z;

    /* Y = 2*Y */
    sp_384_mont_dbl_7(y, y, p384_mod);
    /* W = Z^4 */
    sp_384_mont_sqr_7(w, z, p384_mod, p384_mp_mod);
    sp_384_mont_sqr_7(w, w, p384_mod, p384_mp_mod);

#ifndef WOLFSSL_SP_SMALL
    while (--n > 0)
#else
    while (--n >= 0)
#endif
    {
        /* A = 3*(X^2 - W) */
        sp_384_mont_sqr_7(t1, x, p384_mod, p384_mp_mod);
        sp_384_mont_sub_7(t1, t1, w, p384_mod);
        sp_384_mont_tpl_7(a, t1, p384_mod);
        /* B = X*Y^2 */
        sp_384_mont_sqr_7(t1, y, p384_mod, p384_mp_mod);
        sp_384_mont_mul_7(b, t1, x, p384_mod, p384_mp_mod);
        /* X = A^2 - 2B */
        sp_384_mont_sqr_7(x, a, p384_mod, p384_mp_mod);
        sp_384_mont_dbl_7(t2, b, p384_mod);
        sp_384_mont_sub_7(x, x, t2, p384_mod);
        /* Z = Z*Y */
        sp_384_mont_mul_7(z, z, y, p384_mod, p384_mp_mod);
        /* t2 = Y^4 */
        sp_384_mont_sqr_7(t1, t1, p384_mod, p384_mp_mod);
#ifdef WOLFSSL_SP_SMALL
        if (n != 0)
#endif
        {
            /* W = W*Y^4 */
            sp_384_mont_mul_7(w, w, t1, p384_mod, p384_mp_mod);
        }
        /* y = 2*A*(B - X) - Y^4 */
        sp_384_mont_sub_7(y, b, x, p384_mod);
        sp_384_mont_mul_7(y, y, a, p384_mod, p384_mp_mod);
        sp_384_mont_dbl_7(y, y, p384_mod);
        sp_384_mont_sub_7(y, y, t1, p384_mod);
    }
#ifndef WOLFSSL_SP_SMALL
    /* A = 3*(X^2 - W) */
    sp_384_mont_sqr_7(t1, x, p384_mod, p384_mp_mod);
    sp_384_mont_sub_7(t1, t1, w, p384_mod);
    sp_384_mont_tpl_7(a, t1, p384_mod);
    /* B = X*Y^2 */
    sp_384_mont_sqr_7(t1, y, p384_mod, p384_mp_mod);
    sp_384_mont_mul_7(b, t1, x, p384_mod, p384_mp_mod);
    /* X = A^2 - 2B */
    sp_384_mont_sqr_7(x, a, p384_mod, p384_mp_mod);
    sp_384_mont_dbl_7(t2, b, p384_mod);
    sp_384_mont_sub_7(x, x, t2, p384_mod);
    /* Z = Z*Y */
    sp_384_mont_mul_7(z, z, y, p384_mod, p384_mp_mod);
    /* t2 = Y^4 */
    sp_384_mont_sqr_7(t1, t1, p384_mod, p384_mp_mod);
    /* y = 2*A*(B - X) - Y^4 */
    sp_384_mont_sub_7(y, b, x, p384_mod);
    sp_384_mont_mul_7(y, y, a, p384_mod, p384_mp_mod);
    sp_384_mont_dbl_7(y, y, p384_mod);
    sp_384_mont_sub_7(y, y, t1, p384_mod);
#endif
    /* Y = Y/2 */
    sp_384_div2_7(y, y, p384_mod);
}

/* Double the Montgomery form projective point p a number of times.
 *
 * r  Result of repeated doubling of point.
 * p  Point to double.
 * n  Number of times to double
 * t  Temporary ordinate data.
 */
static void sp_384_proj_point_dbl_n_store_7(sp_point_384* r, const sp_point_384* p,
        int n, int m, sp_digit* t)
{
    sp_digit* w = t;
    sp_digit* a = t + 2*7;
    sp_digit* b = t + 4*7;
    sp_digit* t1 = t + 6*7;
    sp_digit* t2 = t + 8*7;
    sp_digit* x = r[2*m].x;
    sp_digit* y = r[(1<<n)*m].y;
    sp_digit* z = r[2*m].z;
    int i;

    for (i=0; i<7; i++) {
        x[i] = p->x[i];
    }
    for (i=0; i<7; i++) {
        y[i] = p->y[i];
    }
    for (i=0; i<7; i++) {
        z[i] = p->z[i];
    }

    /* Y = 2*Y */
    sp_384_mont_dbl_7(y, y, p384_mod);
    /* W = Z^4 */
    sp_384_mont_sqr_7(w, z, p384_mod, p384_mp_mod);
    sp_384_mont_sqr_7(w, w, p384_mod, p384_mp_mod);
    for (i=1; i<=n; i++) {
        /* A = 3*(X^2 - W) */
        sp_384_mont_sqr_7(t1, x, p384_mod, p384_mp_mod);
        sp_384_mont_sub_7(t1, t1, w, p384_mod);
        sp_384_mont_tpl_7(a, t1, p384_mod);
        /* B = X*Y^2 */
        sp_384_mont_sqr_7(t2, y, p384_mod, p384_mp_mod);
        sp_384_mont_mul_7(b, t2, x, p384_mod, p384_mp_mod);
        x = r[(1<<i)*m].x;
        /* X = A^2 - 2B */
        sp_384_mont_sqr_7(x, a, p384_mod, p384_mp_mod);
        sp_384_mont_dbl_7(t1, b, p384_mod);
        sp_384_mont_sub_7(x, x, t1, p384_mod);
        /* Z = Z*Y */
        sp_384_mont_mul_7(r[(1<<i)*m].z, z, y, p384_mod, p384_mp_mod);
        z = r[(1<<i)*m].z;
        /* t2 = Y^4 */
        sp_384_mont_sqr_7(t2, t2, p384_mod, p384_mp_mod);
        if (i != n) {
            /* W = W*Y^4 */
            sp_384_mont_mul_7(w, w, t2, p384_mod, p384_mp_mod);
        }
        /* y = 2*A*(B - X) - Y^4 */
        sp_384_mont_sub_7(y, b, x, p384_mod);
        sp_384_mont_mul_7(y, y, a, p384_mod, p384_mp_mod);
        sp_384_mont_dbl_7(y, y, p384_mod);
        sp_384_mont_sub_7(y, y, t2, p384_mod);

        /* Y = Y/2 */
        sp_384_div2_7(r[(1<<i)*m].y, y, p384_mod);
        r[(1<<i)*m].infinity = 0;
    }
}

/* Add two Montgomery form projective points.
 *
 * ra  Result of addition.
 * rs  Result of subtraction.
 * p   First point to add.
 * q   Second point to add.
 * t   Temporary ordinate data.
 */
static void sp_384_proj_point_add_sub_7(sp_point_384* ra, sp_point_384* rs,
        const sp_point_384* p, const sp_point_384* q, sp_digit* t)
{
    sp_digit* t1 = t;
    sp_digit* t2 = t + 2*7;
    sp_digit* t3 = t + 4*7;
    sp_digit* t4 = t + 6*7;
    sp_digit* t5 = t + 8*7;
    sp_digit* t6 = t + 10*7;
    sp_digit* x = ra->x;
    sp_digit* y = ra->y;
    sp_digit* z = ra->z;
    sp_digit* xs = rs->x;
    sp_digit* ys = rs->y;
    sp_digit* zs = rs->z;


    XMEMCPY(x, p->x, sizeof(p->x) / 2);
    XMEMCPY(y, p->y, sizeof(p->y) / 2);
    XMEMCPY(z, p->z, sizeof(p->z) / 2);
    ra->infinity = 0;
    rs->infinity = 0;

    /* U1 = X1*Z2^2 */
    sp_384_mont_sqr_7(t1, q->z, p384_mod, p384_mp_mod);
    sp_384_mont_mul_7(t3, t1, q->z, p384_mod, p384_mp_mod);
    sp_384_mont_mul_7(t1, t1, x, p384_mod, p384_mp_mod);
    /* U2 = X2*Z1^2 */
    sp_384_mont_sqr_7(t2, z, p384_mod, p384_mp_mod);
    sp_384_mont_mul_7(t4, t2, z, p384_mod, p384_mp_mod);
    sp_384_mont_mul_7(t2, t2, q->x, p384_mod, p384_mp_mod);
    /* S1 = Y1*Z2^3 */
    sp_384_mont_mul_7(t3, t3, y, p384_mod, p384_mp_mod);
    /* S2 = Y2*Z1^3 */
    sp_384_mont_mul_7(t4, t4, q->y, p384_mod, p384_mp_mod);
    /* H = U2 - U1 */
    sp_384_mont_sub_7(t2, t2, t1, p384_mod);
    /* RS = S2 + S1 */
    sp_384_mont_add_7(t6, t4, t3, p384_mod);
    /* R = S2 - S1 */
    sp_384_mont_sub_7(t4, t4, t3, p384_mod);
    /* Z3 = H*Z1*Z2 */
    /* ZS = H*Z1*Z2 */
    sp_384_mont_mul_7(z, z, q->z, p384_mod, p384_mp_mod);
    sp_384_mont_mul_7(z, z, t2, p384_mod, p384_mp_mod);
    XMEMCPY(zs, z, sizeof(p->z)/2);
    /* X3 = R^2 - H^3 - 2*U1*H^2 */
    /* XS = RS^2 - H^3 - 2*U1*H^2 */
    sp_384_mont_sqr_7(x, t4, p384_mod, p384_mp_mod);
    sp_384_mont_sqr_7(xs, t6, p384_mod, p384_mp_mod);
    sp_384_mont_sqr_7(t5, t2, p384_mod, p384_mp_mod);
    sp_384_mont_mul_7(y, t1, t5, p384_mod, p384_mp_mod);
    sp_384_mont_mul_7(t5, t5, t2, p384_mod, p384_mp_mod);
    sp_384_mont_sub_7(x, x, t5, p384_mod);
    sp_384_mont_sub_7(xs, xs, t5, p384_mod);
    sp_384_mont_dbl_7(t1, y, p384_mod);
    sp_384_mont_sub_7(x, x, t1, p384_mod);
    sp_384_mont_sub_7(xs, xs, t1, p384_mod);
    /* Y3 = R*(U1*H^2 - X3) - S1*H^3 */
    /* YS = -RS*(U1*H^2 - XS) - S1*H^3 */
    sp_384_mont_sub_7(ys, y, xs, p384_mod);
    sp_384_mont_sub_7(y, y, x, p384_mod);
    sp_384_mont_mul_7(y, y, t4, p384_mod, p384_mp_mod);
    sp_384_sub_7(t6, p384_mod, t6);
    sp_384_mont_mul_7(ys, ys, t6, p384_mod, p384_mp_mod);
    sp_384_mont_mul_7(t5, t5, t3, p384_mod, p384_mp_mod);
    sp_384_mont_sub_7(y, y, t5, p384_mod);
    sp_384_mont_sub_7(ys, ys, t5, p384_mod);
}

/* Structure used to describe recoding of scalar multiplication. */
typedef struct ecc_recode_384 {
    /* Index into pre-computation table. */
    uint8_t i;
    /* Use the negative of the point. */
    uint8_t neg;
} ecc_recode_384;

/* The index into pre-computation table to use. */
static const uint8_t recode_index_7_6[66] = {
     0,  1,  2,  3,  4,  5,  6,  7,  8,  9, 10, 11, 12, 13, 14, 15,
    16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31,
    32, 31, 30, 29, 28, 27, 26, 25, 24, 23, 22, 21, 20, 19, 18, 17,
    16, 15, 14, 13, 12, 11, 10,  9,  8,  7,  6,  5,  4,  3,  2,  1,
     0,  1,
};

/* Whether to negate y-ordinate. */
static const uint8_t recode_neg_7_6[66] = {
     0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,
     0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,
     1,  1,  1,  1,  1,  1,  1,  1,  1,  1,  1,  1,  1,  1,  1,  1,
     1,  1,  1,  1,  1,  1,  1,  1,  1,  1,  1,  1,  1,  1,  1,  1,
     0,  0,
};

/* Recode the scalar for multiplication using pre-computed values and
 * subtraction.
 *
 * k  Scalar to multiply by.
 * v  Vector of operations to perform.
 */
static void sp_384_ecc_recode_6_7(const sp_digit* k, ecc_recode_384* v)
{
    int i, j;
    uint8_t y;
    int carry = 0;
    int o;
    sp_digit n;

    j = 0;
    n = k[j];
    o = 0;
    for (i=0; i<65; i++) {
        y = n;
        if (o + 6 < 55) {
            y &= 0x3f;
            n >>= 6;
            o += 6;
        }
        else if (o + 6 == 55) {
            n >>= 6;
            if (++j < 7)
                n = k[j];
            o = 0;
        }
        else if (++j < 7) {
            n = k[j];
            y |= (n << (55 - o)) & 0x3f;
            o -= 49;
            n >>= o;
        }

        y += carry;
        v[i].i = recode_index_7_6[y];
        v[i].neg = recode_neg_7_6[y];
        carry = (y >> 6) + v[i].neg;
    }
}

#ifndef WC_NO_CACHE_RESISTANT
/* Touch each possible point that could be being copied.
 *
 * r      Point to copy into.
 * table  Table - start of the entires to access
 * idx    Index of entry to retrieve.
 */
static void sp_384_get_point_33_7(sp_point_384* r, const sp_point_384* table,
    int idx)
{
    int i;
    sp_digit mask;

    r->x[0] = 0;
    r->x[1] = 0;
    r->x[2] = 0;
    r->x[3] = 0;
    r->x[4] = 0;
    r->x[5] = 0;
    r->x[6] = 0;
    r->y[0] = 0;
    r->y[1] = 0;
    r->y[2] = 0;
    r->y[3] = 0;
    r->y[4] = 0;
    r->y[5] = 0;
    r->y[6] = 0;
    r->z[0] = 0;
    r->z[1] = 0;
    r->z[2] = 0;
    r->z[3] = 0;
    r->z[4] = 0;
    r->z[5] = 0;
    r->z[6] = 0;
    for (i = 1; i < 33; i++) {
        mask = 0 - (i == idx);
        r->x[0] |= mask & table[i].x[0];
        r->x[1] |= mask & table[i].x[1];
        r->x[2] |= mask & table[i].x[2];
        r->x[3] |= mask & table[i].x[3];
        r->x[4] |= mask & table[i].x[4];
        r->x[5] |= mask & table[i].x[5];
        r->x[6] |= mask & table[i].x[6];
        r->y[0] |= mask & table[i].y[0];
        r->y[1] |= mask & table[i].y[1];
        r->y[2] |= mask & table[i].y[2];
        r->y[3] |= mask & table[i].y[3];
        r->y[4] |= mask & table[i].y[4];
        r->y[5] |= mask & table[i].y[5];
        r->y[6] |= mask & table[i].y[6];
        r->z[0] |= mask & table[i].z[0];
        r->z[1] |= mask & table[i].z[1];
        r->z[2] |= mask & table[i].z[2];
        r->z[3] |= mask & table[i].z[3];
        r->z[4] |= mask & table[i].z[4];
        r->z[5] |= mask & table[i].z[5];
        r->z[6] |= mask & table[i].z[6];
    }
}
#endif /* !WC_NO_CACHE_RESISTANT */
/* Multiply the point by the scalar and return the result.
 * If map is true then convert result to affine coordinates.
 *
 * Window technique of 6 bits. (Add-Sub variation.)
 * Calculate 0..32 times the point. Use function that adds and
 * subtracts the same two points.
 * Recode to add or subtract one of the computed points.
 * Double to push up.
 * NOT a sliding window.
 *
 * r     Resulting point.
 * g     Point to multiply.
 * k     Scalar to multiply by.
 * map   Indicates whether to convert result to affine.
 * ct    Constant time required.
 * heap  Heap to use for allocation.
 * returns MEMORY_E when memory allocation fails and MP_OKAY on success.
 */
static int sp_384_ecc_mulmod_win_add_sub_7(sp_point_384* r, const sp_point_384* g,
        const sp_digit* k, int map, int ct, void* heap)
{
#if (!defined(WOLFSSL_SP_SMALL) && !defined(WOLFSSL_SMALL_STACK)) || defined(WOLFSSL_SP_NO_MALLOC)
    sp_point_384 td[33];
    sp_point_384 rtd, pd;
    sp_digit tmpd[2 * 7 * 6];
#endif
    sp_point_384* t;
    sp_point_384* rt;
    sp_point_384* p = NULL;
    sp_digit* tmp;
    sp_digit* negy;
    int i;
    ecc_recode_384 v[65];
    int err;

    /* Constant time used for cache attack resistance implementation. */
    (void)ct;
    (void)heap;

    err = sp_384_point_new_7(heap, rtd, rt);
    if (err == MP_OKAY)
        err = sp_384_point_new_7(heap, pd, p);
#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    t = (sp_point_384*)XMALLOC(sizeof(sp_point_384) * 33, heap, DYNAMIC_TYPE_ECC);
    if (t == NULL)
        err = MEMORY_E;
    tmp = (sp_digit*)XMALLOC(sizeof(sp_digit) * 2 * 7 * 6, heap,
                             DYNAMIC_TYPE_ECC);
    if (tmp == NULL)
        err = MEMORY_E;
#else
    t = td;
    tmp = tmpd;
#endif


    if (err == MP_OKAY) {
        /* t[0] = {0, 0, 1} * norm */
        XMEMSET(&t[0], 0, sizeof(t[0]));
        t[0].infinity = 1;
        /* t[1] = {g->x, g->y, g->z} * norm */
        err = sp_384_mod_mul_norm_7(t[1].x, g->x, p384_mod);
    }
    if (err == MP_OKAY) {
        err = sp_384_mod_mul_norm_7(t[1].y, g->y, p384_mod);
    }
    if (err == MP_OKAY) {
        err = sp_384_mod_mul_norm_7(t[1].z, g->z, p384_mod);
    }

    if (err == MP_OKAY) {
        t[1].infinity = 0;
        /* t[2] ... t[32]  */
        sp_384_proj_point_dbl_n_store_7(t, &t[ 1], 5, 1, tmp);
        sp_384_proj_point_add_7(&t[ 3], &t[ 2], &t[ 1], tmp);
        sp_384_proj_point_dbl_7(&t[ 6], &t[ 3], tmp);
        sp_384_proj_point_add_sub_7(&t[ 7], &t[ 5], &t[ 6], &t[ 1], tmp);
        sp_384_proj_point_dbl_7(&t[10], &t[ 5], tmp);
        sp_384_proj_point_add_sub_7(&t[11], &t[ 9], &t[10], &t[ 1], tmp);
        sp_384_proj_point_dbl_7(&t[12], &t[ 6], tmp);
        sp_384_proj_point_dbl_7(&t[14], &t[ 7], tmp);
        sp_384_proj_point_add_sub_7(&t[15], &t[13], &t[14], &t[ 1], tmp);
        sp_384_proj_point_dbl_7(&t[18], &t[ 9], tmp);
        sp_384_proj_point_add_sub_7(&t[19], &t[17], &t[18], &t[ 1], tmp);
        sp_384_proj_point_dbl_7(&t[20], &t[10], tmp);
        sp_384_proj_point_dbl_7(&t[22], &t[11], tmp);
        sp_384_proj_point_add_sub_7(&t[23], &t[21], &t[22], &t[ 1], tmp);
        sp_384_proj_point_dbl_7(&t[24], &t[12], tmp);
        sp_384_proj_point_dbl_7(&t[26], &t[13], tmp);
        sp_384_proj_point_add_sub_7(&t[27], &t[25], &t[26], &t[ 1], tmp);
        sp_384_proj_point_dbl_7(&t[28], &t[14], tmp);
        sp_384_proj_point_dbl_7(&t[30], &t[15], tmp);
        sp_384_proj_point_add_sub_7(&t[31], &t[29], &t[30], &t[ 1], tmp);

        negy = t[0].y;

        sp_384_ecc_recode_6_7(k, v);

        i = 64;
    #ifndef WC_NO_CACHE_RESISTANT
        if (ct) {
            sp_384_get_point_33_7(rt, t, v[i].i);
            rt->infinity = !v[i].i;
        }
        else
    #endif
        {
            XMEMCPY(rt, &t[v[i].i], sizeof(sp_point_384));
        }
        for (--i; i>=0; i--) {
            sp_384_proj_point_dbl_n_7(rt, 6, tmp);

        #ifndef WC_NO_CACHE_RESISTANT
            if (ct) {
                sp_384_get_point_33_7(p, t, v[i].i);
                p->infinity = !v[i].i;
            }
            else
        #endif
            {
                XMEMCPY(p, &t[v[i].i], sizeof(sp_point_384));
            }
            sp_384_sub_7(negy, p384_mod, p->y);
            sp_384_cond_copy_7(p->y, negy, (sp_digit)0 - v[i].neg);
            sp_384_proj_point_add_7(rt, rt, p, tmp);
        }

        if (map != 0) {
            sp_384_map_7(r, rt, tmp);
        }
        else {
            XMEMCPY(r, rt, sizeof(sp_point_384));
        }
    }

#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (t != NULL)
        XFREE(t, heap, DYNAMIC_TYPE_ECC);
    if (tmp != NULL)
        XFREE(tmp, heap, DYNAMIC_TYPE_ECC);
#endif
    sp_384_point_free_7(p, 0, heap);
    sp_384_point_free_7(rt, 0, heap);

    return err;
}

#ifdef FP_ECC
#endif /* FP_ECC */
/* Add two Montgomery form projective points. The second point has a q value of
 * one.
 * Only the first point can be the same pointer as the result point.
 *
 * r  Result of addition.
 * p  First point to add.
 * q  Second point to add.
 * t  Temporary ordinate data.
 */
static void sp_384_proj_point_add_qz1_7(sp_point_384* r, const sp_point_384* p,
        const sp_point_384* q, sp_digit* t)
{
    const sp_point_384* ap[2];
    sp_point_384* rp[2];
    sp_digit* t1 = t;
    sp_digit* t2 = t + 2*7;
    sp_digit* t3 = t + 4*7;
    sp_digit* t4 = t + 6*7;
    sp_digit* t5 = t + 8*7;
    sp_digit* x;
    sp_digit* y;
    sp_digit* z;
    int i;

    /* Check double */
    (void)sp_384_sub_7(t1, p384_mod, q->y);
    sp_384_norm_7(t1);
    if ((sp_384_cmp_equal_7(p->x, q->x) & sp_384_cmp_equal_7(p->z, q->z) &
        (sp_384_cmp_equal_7(p->y, q->y) | sp_384_cmp_equal_7(p->y, t1))) != 0) {
        sp_384_proj_point_dbl_7(r, p, t);
    }
    else {
        rp[0] = r;

        /*lint allow cast to different type of pointer*/
        rp[1] = (sp_point_384*)t; /*lint !e9087 !e740*/
        XMEMSET(rp[1], 0, sizeof(sp_point_384));
        x = rp[p->infinity | q->infinity]->x;
        y = rp[p->infinity | q->infinity]->y;
        z = rp[p->infinity | q->infinity]->z;

        ap[0] = p;
        ap[1] = q;
        for (i=0; i<7; i++) {
            r->x[i] = ap[p->infinity]->x[i];
        }
        for (i=0; i<7; i++) {
            r->y[i] = ap[p->infinity]->y[i];
        }
        for (i=0; i<7; i++) {
            r->z[i] = ap[p->infinity]->z[i];
        }
        r->infinity = ap[p->infinity]->infinity;

        /* U2 = X2*Z1^2 */
        sp_384_mont_sqr_7(t2, z, p384_mod, p384_mp_mod);
        sp_384_mont_mul_7(t4, t2, z, p384_mod, p384_mp_mod);
        sp_384_mont_mul_7(t2, t2, q->x, p384_mod, p384_mp_mod);
        /* S2 = Y2*Z1^3 */
        sp_384_mont_mul_7(t4, t4, q->y, p384_mod, p384_mp_mod);
        /* H = U2 - X1 */
        sp_384_mont_sub_7(t2, t2, x, p384_mod);
        /* R = S2 - Y1 */
        sp_384_mont_sub_7(t4, t4, y, p384_mod);
        /* Z3 = H*Z1 */
        sp_384_mont_mul_7(z, z, t2, p384_mod, p384_mp_mod);
        /* X3 = R^2 - H^3 - 2*X1*H^2 */
        sp_384_mont_sqr_7(t1, t4, p384_mod, p384_mp_mod);
        sp_384_mont_sqr_7(t5, t2, p384_mod, p384_mp_mod);
        sp_384_mont_mul_7(t3, x, t5, p384_mod, p384_mp_mod);
        sp_384_mont_mul_7(t5, t5, t2, p384_mod, p384_mp_mod);
        sp_384_mont_sub_7(x, t1, t5, p384_mod);
        sp_384_mont_dbl_7(t1, t3, p384_mod);
        sp_384_mont_sub_7(x, x, t1, p384_mod);
        /* Y3 = R*(X1*H^2 - X3) - Y1*H^3 */
        sp_384_mont_sub_7(t3, t3, x, p384_mod);
        sp_384_mont_mul_7(t3, t3, t4, p384_mod, p384_mp_mod);
        sp_384_mont_mul_7(t5, t5, y, p384_mod, p384_mp_mod);
        sp_384_mont_sub_7(y, t3, t5, p384_mod);
    }
}

#ifdef FP_ECC
/* Convert the projective point to affine.
 * Ordinates are in Montgomery form.
 *
 * a  Point to convert.
 * t  Temporary data.
 */
static void sp_384_proj_to_affine_7(sp_point_384* a, sp_digit* t)
{
    sp_digit* t1 = t;
    sp_digit* t2 = t + 2 * 7;
    sp_digit* tmp = t + 4 * 7;

    sp_384_mont_inv_7(t1, a->z, tmp);

    sp_384_mont_sqr_7(t2, t1, p384_mod, p384_mp_mod);
    sp_384_mont_mul_7(t1, t2, t1, p384_mod, p384_mp_mod);

    sp_384_mont_mul_7(a->x, a->x, t2, p384_mod, p384_mp_mod);
    sp_384_mont_mul_7(a->y, a->y, t1, p384_mod, p384_mp_mod);
    XMEMCPY(a->z, p384_norm_mod, sizeof(p384_norm_mod));
}

/* Generate the pre-computed table of points for the base point.
 *
 * a      The base point.
 * table  Place to store generated point data.
 * tmp    Temporary data.
 * heap  Heap to use for allocation.
 */
static int sp_384_gen_stripe_table_7(const sp_point_384* a,
        sp_table_entry_384* table, sp_digit* tmp, void* heap)
{
#if (!defined(WOLFSSL_SP_SMALL) && !defined(WOLFSSL_SMALL_STACK)) || defined(WOLFSSL_SP_NO_MALLOC)
    sp_point_384 td, s1d, s2d;
#endif
    sp_point_384* t;
    sp_point_384* s1 = NULL;
    sp_point_384* s2 = NULL;
    int i, j;
    int err;

    (void)heap;

    err = sp_384_point_new_7(heap, td, t);
    if (err == MP_OKAY) {
        err = sp_384_point_new_7(heap, s1d, s1);
    }
    if (err == MP_OKAY) {
        err = sp_384_point_new_7(heap, s2d, s2);
    }

    if (err == MP_OKAY) {
        err = sp_384_mod_mul_norm_7(t->x, a->x, p384_mod);
    }
    if (err == MP_OKAY) {
        err = sp_384_mod_mul_norm_7(t->y, a->y, p384_mod);
    }
    if (err == MP_OKAY) {
        err = sp_384_mod_mul_norm_7(t->z, a->z, p384_mod);
    }
    if (err == MP_OKAY) {
        t->infinity = 0;
        sp_384_proj_to_affine_7(t, tmp);

        XMEMCPY(s1->z, p384_norm_mod, sizeof(p384_norm_mod));
        s1->infinity = 0;
        XMEMCPY(s2->z, p384_norm_mod, sizeof(p384_norm_mod));
        s2->infinity = 0;

        /* table[0] = {0, 0, infinity} */
        XMEMSET(&table[0], 0, sizeof(sp_table_entry_384));
        /* table[1] = Affine version of 'a' in Montgomery form */
        XMEMCPY(table[1].x, t->x, sizeof(table->x));
        XMEMCPY(table[1].y, t->y, sizeof(table->y));

        for (i=1; i<8; i++) {
            sp_384_proj_point_dbl_n_7(t, 48, tmp);
            sp_384_proj_to_affine_7(t, tmp);
            XMEMCPY(table[1<<i].x, t->x, sizeof(table->x));
            XMEMCPY(table[1<<i].y, t->y, sizeof(table->y));
        }

        for (i=1; i<8; i++) {
            XMEMCPY(s1->x, table[1<<i].x, sizeof(table->x));
            XMEMCPY(s1->y, table[1<<i].y, sizeof(table->y));
            for (j=(1<<i)+1; j<(1<<(i+1)); j++) {
                XMEMCPY(s2->x, table[j-(1<<i)].x, sizeof(table->x));
                XMEMCPY(s2->y, table[j-(1<<i)].y, sizeof(table->y));
                sp_384_proj_point_add_qz1_7(t, s1, s2, tmp);
                sp_384_proj_to_affine_7(t, tmp);
                XMEMCPY(table[j].x, t->x, sizeof(table->x));
                XMEMCPY(table[j].y, t->y, sizeof(table->y));
            }
        }
    }

    sp_384_point_free_7(s2, 0, heap);
    sp_384_point_free_7(s1, 0, heap);
    sp_384_point_free_7( t, 0, heap);

    return err;
}

#endif /* FP_ECC */
#ifndef WC_NO_CACHE_RESISTANT
/* Touch each possible entry that could be being copied.
 *
 * r      Point to copy into.
 * table  Table - start of the entires to access
 * idx    Index of entry to retrieve.
 */
static void sp_384_get_entry_256_7(sp_point_384* r,
    const sp_table_entry_384* table, int idx)
{
    int i;
    sp_digit mask;

    r->x[0] = 0;
    r->x[1] = 0;
    r->x[2] = 0;
    r->x[3] = 0;
    r->x[4] = 0;
    r->x[5] = 0;
    r->x[6] = 0;
    r->y[0] = 0;
    r->y[1] = 0;
    r->y[2] = 0;
    r->y[3] = 0;
    r->y[4] = 0;
    r->y[5] = 0;
    r->y[6] = 0;
    for (i = 1; i < 256; i++) {
        mask = 0 - (i == idx);
        r->x[0] |= mask & table[i].x[0];
        r->x[1] |= mask & table[i].x[1];
        r->x[2] |= mask & table[i].x[2];
        r->x[3] |= mask & table[i].x[3];
        r->x[4] |= mask & table[i].x[4];
        r->x[5] |= mask & table[i].x[5];
        r->x[6] |= mask & table[i].x[6];
        r->y[0] |= mask & table[i].y[0];
        r->y[1] |= mask & table[i].y[1];
        r->y[2] |= mask & table[i].y[2];
        r->y[3] |= mask & table[i].y[3];
        r->y[4] |= mask & table[i].y[4];
        r->y[5] |= mask & table[i].y[5];
        r->y[6] |= mask & table[i].y[6];
    }
}
#endif /* !WC_NO_CACHE_RESISTANT */
/* Multiply the point by the scalar and return the result.
 * If map is true then convert result to affine coordinates.
 *
 * Implementation uses striping of bits.
 * Choose bits 8 bits apart.
 *
 * r      Resulting point.
 * k      Scalar to multiply by.
 * table  Pre-computed table.
 * map    Indicates whether to convert result to affine.
 * ct     Constant time required.
 * heap   Heap to use for allocation.
 * returns MEMORY_E when memory allocation fails and MP_OKAY on success.
 */
static int sp_384_ecc_mulmod_stripe_7(sp_point_384* r, const sp_point_384* g,
        const sp_table_entry_384* table, const sp_digit* k, int map,
        int ct, void* heap)
{
#if (!defined(WOLFSSL_SP_SMALL) && !defined(WOLFSSL_SMALL_STACK)) || defined(WOLFSSL_SP_NO_MALLOC)
    sp_point_384 rtd;
    sp_point_384 pd;
    sp_digit td[2 * 7 * 6];
#endif
    sp_point_384* rt;
    sp_point_384* p = NULL;
    sp_digit* t;
    int i, j;
    int y, x;
    int err;

    (void)g;
    /* Constant time used for cache attack resistance implementation. */
    (void)ct;
    (void)heap;


    err = sp_384_point_new_7(heap, rtd, rt);
    if (err == MP_OKAY) {
        err = sp_384_point_new_7(heap, pd, p);
    }
#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    t = (sp_digit*)XMALLOC(sizeof(sp_digit) * 2 * 7 * 6, heap,
                           DYNAMIC_TYPE_ECC);
    if (t == NULL) {
        err = MEMORY_E;
    }
#else
    t = td;
#endif

    if (err == MP_OKAY) {
        XMEMCPY(p->z, p384_norm_mod, sizeof(p384_norm_mod));
        XMEMCPY(rt->z, p384_norm_mod, sizeof(p384_norm_mod));

        y = 0;
        for (j=0,x=47; j<8; j++,x+=48) {
            y |= ((k[x / 55] >> (x % 55)) & 1) << j;
        }
    #ifndef WC_NO_CACHE_RESISTANT
        if (ct) {
            sp_384_get_entry_256_7(rt, table, y);
        } else
    #endif
        {
            XMEMCPY(rt->x, table[y].x, sizeof(table[y].x));
            XMEMCPY(rt->y, table[y].y, sizeof(table[y].y));
        }
        rt->infinity = !y;
        for (i=46; i>=0; i--) {
            y = 0;
            for (j=0,x=i; j<8; j++,x+=48) {
                y |= ((k[x / 55] >> (x % 55)) & 1) << j;
            }

            sp_384_proj_point_dbl_7(rt, rt, t);
        #ifndef WC_NO_CACHE_RESISTANT
            if (ct) {
                sp_384_get_entry_256_7(p, table, y);
            }
            else
        #endif
            {
                XMEMCPY(p->x, table[y].x, sizeof(table[y].x));
                XMEMCPY(p->y, table[y].y, sizeof(table[y].y));
            }
            p->infinity = !y;
            sp_384_proj_point_add_qz1_7(rt, rt, p, t);
        }

        if (map != 0) {
            sp_384_map_7(r, rt, t);
        }
        else {
            XMEMCPY(r, rt, sizeof(sp_point_384));
        }
    }

#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (t != NULL) {
        XFREE(t, heap, DYNAMIC_TYPE_ECC);
    }
#endif
    sp_384_point_free_7(p, 0, heap);
    sp_384_point_free_7(rt, 0, heap);

    return err;
}

#ifdef FP_ECC
#ifndef FP_ENTRIES
    #define FP_ENTRIES 16
#endif

typedef struct sp_cache_384_t {
    sp_digit x[7];
    sp_digit y[7];
    sp_table_entry_384 table[256];
    uint32_t cnt;
    int set;
} sp_cache_384_t;

static THREAD_LS_T sp_cache_384_t sp_cache_384[FP_ENTRIES];
static THREAD_LS_T int sp_cache_384_last = -1;
static THREAD_LS_T int sp_cache_384_inited = 0;

#ifndef HAVE_THREAD_LS
    static volatile int initCacheMutex_384 = 0;
    static wolfSSL_Mutex sp_cache_384_lock;
#endif

static void sp_ecc_get_cache_384(const sp_point_384* g, sp_cache_384_t** cache)
{
    int i, j;
    uint32_t least;

    if (sp_cache_384_inited == 0) {
        for (i=0; i<FP_ENTRIES; i++) {
            sp_cache_384[i].set = 0;
        }
        sp_cache_384_inited = 1;
    }

    /* Compare point with those in cache. */
    for (i=0; i<FP_ENTRIES; i++) {
        if (!sp_cache_384[i].set)
            continue;

        if (sp_384_cmp_equal_7(g->x, sp_cache_384[i].x) &
                           sp_384_cmp_equal_7(g->y, sp_cache_384[i].y)) {
            sp_cache_384[i].cnt++;
            break;
        }
    }

    /* No match. */
    if (i == FP_ENTRIES) {
        /* Find empty entry. */
        i = (sp_cache_384_last + 1) % FP_ENTRIES;
        for (; i != sp_cache_384_last; i=(i+1)%FP_ENTRIES) {
            if (!sp_cache_384[i].set) {
                break;
            }
        }

        /* Evict least used. */
        if (i == sp_cache_384_last) {
            least = sp_cache_384[0].cnt;
            for (j=1; j<FP_ENTRIES; j++) {
                if (sp_cache_384[j].cnt < least) {
                    i = j;
                    least = sp_cache_384[i].cnt;
                }
            }
        }

        XMEMCPY(sp_cache_384[i].x, g->x, sizeof(sp_cache_384[i].x));
        XMEMCPY(sp_cache_384[i].y, g->y, sizeof(sp_cache_384[i].y));
        sp_cache_384[i].set = 1;
        sp_cache_384[i].cnt = 1;
    }

    *cache = &sp_cache_384[i];
    sp_cache_384_last = i;
}
#endif /* FP_ECC */

/* Multiply the base point of P384 by the scalar and return the result.
 * If map is true then convert result to affine coordinates.
 *
 * r     Resulting point.
 * g     Point to multiply.
 * k     Scalar to multiply by.
 * map   Indicates whether to convert result to affine.
 * ct    Constant time required.
 * heap  Heap to use for allocation.
 * returns MEMORY_E when memory allocation fails and MP_OKAY on success.
 */
static int sp_384_ecc_mulmod_7(sp_point_384* r, const sp_point_384* g, const sp_digit* k,
        int map, int ct, void* heap)
{
#ifndef FP_ECC
    return sp_384_ecc_mulmod_win_add_sub_7(r, g, k, map, ct, heap);
#else
    sp_digit tmp[2 * 7 * 7];
    sp_cache_384_t* cache;
    int err = MP_OKAY;

#ifndef HAVE_THREAD_LS
    if (initCacheMutex_384 == 0) {
         wc_InitMutex(&sp_cache_384_lock);
         initCacheMutex_384 = 1;
    }
    if (wc_LockMutex(&sp_cache_384_lock) != 0)
       err = BAD_MUTEX_E;
#endif /* HAVE_THREAD_LS */

    if (err == MP_OKAY) {
        sp_ecc_get_cache_384(g, &cache);
        if (cache->cnt == 2)
            sp_384_gen_stripe_table_7(g, cache->table, tmp, heap);

#ifndef HAVE_THREAD_LS
        wc_UnLockMutex(&sp_cache_384_lock);
#endif /* HAVE_THREAD_LS */

        if (cache->cnt < 2) {
            err = sp_384_ecc_mulmod_win_add_sub_7(r, g, k, map, ct, heap);
        }
        else {
            err = sp_384_ecc_mulmod_stripe_7(r, g, cache->table, k,
                    map, ct, heap);
        }
    }

    return err;
#endif
}

#endif
/* Multiply the point by the scalar and return the result.
 * If map is true then convert result to affine coordinates.
 *
 * km    Scalar to multiply by.
 * p     Point to multiply.
 * r     Resulting point.
 * map   Indicates whether to convert result to affine.
 * heap  Heap to use for allocation.
 * returns MEMORY_E when memory allocation fails and MP_OKAY on success.
 */
int sp_ecc_mulmod_384(mp_int* km, ecc_point* gm, ecc_point* r, int map,
        void* heap)
{
#if (!defined(WOLFSSL_SP_SMALL) && !defined(WOLFSSL_SMALL_STACK)) || defined(WOLFSSL_SP_NO_MALLOC)
    sp_point_384 p;
    sp_digit kd[7];
#endif
    sp_point_384* point;
    sp_digit* k = NULL;
    int err = MP_OKAY;

    err = sp_384_point_new_7(heap, p, point);
#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (err == MP_OKAY) {
        k = (sp_digit*)XMALLOC(sizeof(sp_digit) * 7, heap,
                                                              DYNAMIC_TYPE_ECC);
        if (k == NULL)
            err = MEMORY_E;
    }
#else
    k = kd;
#endif
    if (err == MP_OKAY) {
        sp_384_from_mp(k, 7, km);
        sp_384_point_from_ecc_point_7(point, gm);

            err = sp_384_ecc_mulmod_7(point, point, k, map, 1, heap);
    }
    if (err == MP_OKAY) {
        err = sp_384_point_to_ecc_point_7(point, r);
    }

#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (k != NULL) {
        XFREE(k, heap, DYNAMIC_TYPE_ECC);
    }
#endif
    sp_384_point_free_7(point, 0, heap);

    return err;
}

#ifdef WOLFSSL_SP_SMALL
/* Multiply the base point of P384 by the scalar and return the result.
 * If map is true then convert result to affine coordinates.
 *
 * r     Resulting point.
 * k     Scalar to multiply by.
 * map   Indicates whether to convert result to affine.
 * heap  Heap to use for allocation.
 * returns MEMORY_E when memory allocation fails and MP_OKAY on success.
 */
static int sp_384_ecc_mulmod_base_7(sp_point_384* r, const sp_digit* k,
        int map, int ct, void* heap)
{
    /* No pre-computed values. */
    return sp_384_ecc_mulmod_7(r, &p384_base, k, map, ct, heap);
}

#else
static const sp_table_entry_384 p384_table[256] = {
    /* 0 */
    { { 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00 },
      { 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00 } },
    /* 1 */
    { { 0x50756649c0b528L,0x71c541ad9c707bL,0x71506d35b8838dL,
        0x4d1877fc3ce1d7L,0x6de2b645486845L,0x227025fee46c29L,
        0x134eab708a6785L },
      { 0x043dad4b03a4feL,0x517ef769535846L,0x58ba0ec14286feL,
        0x47a7fecc5d6f3aL,0x1a840c6c352196L,0x3d3bb00044c72dL,
        0x0ade2af0968571L } },
    /* 2 */
    { { 0x0647532b0c535bL,0x52a6e0a0c52c53L,0x5085aae6b24375L,
        0x7096bb501c66b5L,0x47bdb3df9b7b7bL,0x11227e9b2f0be6L,
        0x088b172704fa51L },
      { 0x0e796f2680dc64L,0x796eb06a482ebfL,0x2b441d02e04839L,
        0x19bef7312a5aecL,0x02247c38b8efb5L,0x099ed1185c329eL,
        0x1ed71d7cdb096fL } },
    /* 3 */
    { { 0x6a3cc39edffea5L,0x7a386fafd3f9c4L,0x366f78fbd8d6efL,
        0x529c7ad7873b80L,0x79eb30380eb471L,0x07c5d3b51760b7L,
        0x36ee4f1cc69183L },
      { 0x5ba260f526b605L,0x2f1dfaf0aa6e6fL,0x6bb5ca812a5752L,
        0x3002d8d1276bc9L,0x01f82269483777L,0x1df33eaaf733cdL,
        0x2b97e555f59255L } },
    /* 4 */
    { { 0x480c57f26feef9L,0x4d28741c248048L,0x0c9cf8af1f0c68L,
        0x778f6a639a8016L,0x148e88c42e9c53L,0x464051757ecfe9L,
        0x1a940bd0e2a5e1L },
      { 0x713a46b74536feL,0x1757b153e1d7ebL,0x30dc8c9da07486L,
        0x3b7460c1879b5eL,0x4b766c5317b315L,0x1b9de3aaf4d377L,
        0x245f124c2cf8f5L } },
    /* 5 */
    { { 0x426e2ee349ddd0L,0x7df3365f84a022L,0x03b005d29a7c45L,
        0x422c2337f9b5a4L,0x060494f4bde761L,0x5245e5db6da0b0L,
        0x22b71d744677f2L },
      { 0x19d097b7d5a7ceL,0x6bcb468823d34cL,0x1c3692d3be1d09L,
        0x3c80ec7aa01f02L,0x7170f2ebaafd97L,0x06cbcc7d79d4e8L,
        0x04a8da511fe760L } },
    /* 6 */
    { { 0x79c07a4fc52870L,0x6e9034a752c251L,0x603860a367382cL,
        0x56d912d6aa87d0L,0x0a348a24abaf76L,0x6c5a23da14adcbL,
        0x3cf60479a522b2L },
      { 0x18dd774c61ed22L,0x0ff30168f93b0cL,0x3f79ae15642eddL,
        0x40510f4915fbcbL,0x2c9ddfdfd1c6d6L,0x67b81b62aee55eL,
        0x2824de79b07a43L } },
    /* 7 */
    { { 0x6c66efe085c629L,0x48c212b7913470L,0x4480fd2d057f0aL,
        0x725ec7a89a9eb1L,0x78ce97ca1972b7L,0x54760ee70154fbL,
        0x362a40e27b9f93L },
      { 0x474dc7e7b14461L,0x602819389ef037L,0x1a13bc284370b2L,
        0x0193ff1295a59dL,0x79615bde6ea5d2L,0x2e76e3d886acc1L,
        0x3bb796812e2b60L } },
    /* 8 */
    { { 0x04cbb3893b9a2dL,0x4c16010a18baabL,0x19f7cb50f60831L,
        0x084f400a0936c1L,0x72f1cdd5bbbf00L,0x1b30b725dc6702L,
        0x182753e4fcc50cL },
      { 0x059a07eadaf9d6L,0x26d81e24bf603cL,0x45583c839dc399L,
        0x5579d4d6b1103aL,0x2e14ea59489ae7L,0x492f6e1c5ecc97L,
        0x03740dc05db420L } },
    /* 9 */
    { { 0x413be88510521fL,0x3753ee49982e99L,0x6cd4f7098e1cc5L,
        0x613c92bda4ec1dL,0x495378b677efe0L,0x132a2143839927L,
        0x0cf8c336291c0bL },
      { 0x7fc89d2208353fL,0x751b9da85657e1L,0x349b8a97d405c3L,
        0x65a964b048428fL,0x1adf481276455eL,0x5560c8d89c2ffcL,
        0x144fc11fac21a3L } },
    /* 10 */
    { { 0x7611f4df5bdf53L,0x634eb16234db80L,0x3c713b8e51174cL,
        0x52c3c68ac4b2edL,0x53025ba8bebe75L,0x7175d98143105bL,
        0x33ca8e266a48faL },
      { 0x0c9281d24fd048L,0x76b3177604bbf3L,0x3b26ae754e106fL,
        0x7f782275c6efc6L,0x36662538a4cb67L,0x0ca1255843e464L,
        0x2a4674e142d9bcL } },
    /* 11 */
    { { 0x303b4085d480d8L,0x68f23650f4fa7bL,0x552a3ceeba3367L,
        0x6da0c4947926e3L,0x6e0f5482eb8003L,0x0de717f3d6738aL,
        0x22e5dcc826a477L },
      { 0x1b05b27209cfc2L,0x7f0a0b65b6e146L,0x63586549ed3126L,
        0x7d628dd2b23124L,0x383423fe510391L,0x57ff609eabd569L,
        0x301f04370131baL } },
    /* 12 */
    { { 0x22fe4cdb32f048L,0x7f228ebdadbf5aL,0x02a99adb2d7c8eL,
        0x01a02e05286706L,0x62d6adf627a89fL,0x49c6ce906fbf2bL,
        0x0207256dae90b9L },
      { 0x23e036e71d6cebL,0x199ed8d604e3d7L,0x0c1a11c076d16fL,
        0x389291fb3da3f3L,0x47adc60f8f942eL,0x177048468e4b9aL,
        0x20c09f5e61d927L } },
    /* 13 */
    { { 0x129ea63615b0b8L,0x03fb4a9b588367L,0x5ad6da8da2d051L,
        0x33f782f44caeaaL,0x5a27fa80d45291L,0x6d1ed796942da4L,
        0x08435a931ef556L },
      { 0x004abb25351130L,0x6d33207c6fd7e7L,0x702130972074b7L,
        0x0e34748af900f7L,0x762a531a28c87aL,0x3a903b5a4a6ac7L,
        0x1775b79c35b105L } },
    /* 14 */
    { { 0x7470fd846612ceL,0x7dd9b431b32e53L,0x04bcd2be1a61bcL,
        0x36ed7c5b5c260bL,0x6795f5ef0a4084L,0x46e2880b401c93L,
        0x17d246c5aa8bdeL },
      { 0x707ae4db41b38dL,0x233c31f7f9558fL,0x585110ec67bdf4L,
        0x4d0cc931d0c703L,0x26fbe4356841a7L,0x64323e95239c44L,
        0x371dc9230f3221L } },
    /* 15 */
    { { 0x70ff1ae4b1ec9dL,0x7c1dcfddee0daaL,0x53286782188748L,
        0x6a5d9381e6f207L,0x3aa6c7d6523c4cL,0x6c02d83e0d97e2L,
        0x16a9c916b45312L },
      { 0x78146744b74de8L,0x742ec415269c6fL,0x237a2c6a860e79L,
        0x186baf17ba68a7L,0x4261e8789fa51fL,0x3dc136480a5903L,
        0x1953899e0cf159L } },
    /* 16 */
    { { 0x0205de2f9fbe67L,0x1706fee51c886fL,0x31a0b803c712bfL,
        0x0a6aa11ede7603L,0x2463ef2a145c31L,0x615403b30e8f4aL,
        0x3f024d6c5f5c5eL },
      { 0x53bc4fd4d01f95L,0x7d512ac15a692cL,0x72be38fcfe6aa0L,
        0x437f0b77bbca1eL,0x7fdcf70774a10eL,0x392d6c5cde37f3L,
        0x229cbce79621d1L } },
    /* 17 */
    { { 0x2de4da2341c342L,0x5ca9d4e08844e7L,0x60dd073bcf74c9L,
        0x4f30aa499b63ecL,0x23efd1eafa00d5L,0x7c99a7db1257b3L,
        0x00febc9b3171b1L },
      { 0x7e2fcf3045f8acL,0x2a642e9e3ce610L,0x23f82be69c5299L,
        0x66e49ad967c279L,0x1c895ddfd7a842L,0x798981e22f6d25L,
        0x0d595cb59322f3L } },
    /* 18 */
    { { 0x4bac017d8c1bbaL,0x73872161e7aafdL,0x0fd865f43d8163L,
        0x019d89457708b7L,0x1b983c4dd70684L,0x095e109b74d841L,
        0x25f1f0b3e0c76fL },
      { 0x4e61ddf96010e8L,0x1c40a53f542e5eL,0x01a74dfc8365f9L,
        0x69b36b92773333L,0x08e0fccc139ed3L,0x266d216ddc4269L,
        0x1f2b47717ce9b5L } },
    /* 19 */
    { { 0x0a9a81da57a41fL,0x0825d800736cccL,0x2d7876b4579d28L,
        0x3340ea6211a1e3L,0x49e89284f3ff54L,0x6276a210fe2c6eL,
        0x01c3c8f31be7cbL },
      { 0x2211da5d186e14L,0x1e6ffbb61bfea8L,0x536c7d060211d2L,
        0x320168720d1d55L,0x5835525ed667baL,0x5125e52495205eL,
        0x16113b9f3e9129L } },
    /* 20 */
    { { 0x3086073f3b236fL,0x283b03c443b5f5L,0x78e49ed0a067a7L,
        0x2a878fb79fb2b8L,0x662f04348a9337L,0x57ee2cf732d50bL,
        0x18b50dd65fd514L },
      { 0x5feb9ef2955926L,0x2c3edbef06a7b0L,0x32728dad651029L,
        0x116d00b1c4b347L,0x13254052bf1a1aL,0x3e77bf7fee5ec1L,
        0x253943ca388882L } },
    /* 21 */
    { { 0x32e5b33062e8afL,0x46ebd147a6d321L,0x2c8076dec6a15cL,
        0x7328d511ff0d80L,0x10ad7e926def0eL,0x4e8ca85937d736L,
        0x02638c26e8bf2fL },
      { 0x1deeb3fff1d63fL,0x5014417fa6e8efL,0x6e1da3de5c8f43L,
        0x7ca942b42295d9L,0x23faacf75bb4d1L,0x4a71fcd680053dL,
        0x04af4f90204dceL } },
    /* 22 */
    { { 0x23780d104cbba5L,0x4e8ff46bba9980L,0x2072a6da8d881fL,
        0x3cc3d881ae11c9L,0x2eee84ff19be89L,0x69b708ed77f004L,
        0x2a82928534eef9L },
      { 0x794331187d4543L,0x70e0f3edc0cc41L,0x3ab1fa0b84c854L,
        0x1478355c1d87baL,0x6f35fa7748ba28L,0x37b8be0531584dL,
        0x03c3141c23a69fL } },
    /* 23 */
    { { 0x5c244cdef029ddL,0x0d0f0a0cc37018L,0x17f8476604f6afL,
        0x13a6dd6ccc95c3L,0x5a242e9801b8f6L,0x211ca9cc632131L,
        0x264a6a46a4694fL },
      { 0x3ffd7235285887L,0x284be28302046fL,0x57f4b9b882f1d6L,
        0x5e21772c940661L,0x7619a735c600cfL,0x2f76f5a50c9106L,
        0x28d89c8c69de31L } },
    /* 24 */
    { { 0x799b5c91361ed8L,0x36ead8c66cd95cL,0x046c9969a91f5cL,
        0x46bbdba2a66ea9L,0x29db0e0215a599L,0x26c8849b36f756L,
        0x22c3feb31ff679L },
      { 0x585d1237b5d9efL,0x5ac57f522e8e8dL,0x617e66e8b56c41L,
        0x68826f276823cfL,0x0983f0e6f39231L,0x4e1075099084bdL,
        0x2a541f82be0416L } },
    /* 25 */
    { { 0x468a6e14cf381cL,0x4f7b845c6399edL,0x36aa29732ebe74L,
        0x19c726911ab46aL,0x2ad1fe431eec0eL,0x301e35051fd1eaL,
        0x36da815e7a1ab3L },
      { 0x05672e4507832aL,0x4ebf10fca51251L,0x6015843421cff0L,
        0x3affad832fc013L,0x712b58d9b45540L,0x1e4751d1f6213eL,
        0x0e7c2b218bafa7L } },
    /* 26 */
    { { 0x7abf784c52edf5L,0x6fcb4b135ca7b1L,0x435e46ac5f735cL,
        0x67f8364ca48c5fL,0x46d45b5fbd956bL,0x10deda6065db94L,
        0x0b37fdf85068f9L },
      { 0x74b3ba61f47ec8L,0x42c7ddf08c10ccL,0x1531a1fe422a20L,
        0x366f913d12be38L,0x6a846e30cb2edfL,0x2785898c994fedL,
        0x061be85f331af3L } },
    /* 27 */
    { { 0x23f5361dfcb91eL,0x3c26c8da6b1491L,0x6e444a1e620d65L,
        0x0c3babd5e8ac13L,0x573723ce612b82L,0x2d10e62a142c37L,
        0x3d1a114c2d98bdL },
      { 0x33950b401896f6L,0x7134efe7c12110L,0x31239fd2978472L,
        0x30333bf5978965L,0x79f93313dd769fL,0x457fb9e11662caL,
        0x190a73b251ae3cL } },
    /* 28 */
    { { 0x04dd54bb75f9a4L,0x0d7253a76ae093L,0x08f5b930792bbcL,
        0x041f79adafc265L,0x4a9ff24c61c11bL,0x0019c94e724725L,
        0x21975945d9cc2aL },
      { 0x3dfe76722b4a2bL,0x17f2f6107c1d94L,0x546e1ae2944b01L,
        0x53f1f06401e72dL,0x2dbe43fc7632d6L,0x5639132e185903L,
        0x0f2f34eb448385L } },
    /* 29 */
    { { 0x7b4cc7ec30ce93L,0x58fb6e4e4145f7L,0x5d1ed5540043b5L,
        0x19ffbe1f633adfL,0x5bfc0907259033L,0x6378f872e7ca0eL,
        0x2c127b2c01eb3cL },
      { 0x076eaf4f58839cL,0x2db54560bc9f68L,0x42ad0319b84062L,
        0x46c325d1fb019dL,0x76d2a19ee9eebcL,0x6fbd6d9e2aa8f7L,
        0x2396a598fe0991L } },
    /* 30 */
    { { 0x662fddf7fbd5e1L,0x7ca8ed22563ad3L,0x5b4768efece3b3L,
        0x643786a422d1eaL,0x36ce80494950e1L,0x1a30795b7f2778L,
        0x107f395c93f332L },
      { 0x7939c28332c144L,0x491610e3c8dc0bL,0x099ba2bfdac5fcL,
        0x5c2e3149ec29a7L,0x31b731d06f1dc3L,0x1cbb60d465d462L,
        0x3ca5461362cfd9L } },
    /* 31 */
    { { 0x653ff736ddc103L,0x7c6f2bdec0dfb2L,0x73f81b73a097d0L,
        0x05b775f84f180fL,0x56b2085af23413L,0x0d6f36256a61feL,
        0x26d3ed267fa68fL },
      { 0x54f89251d27ac2L,0x4fc6ad94a71202L,0x7ebf01969b4cc5L,
        0x7ba364dbc14760L,0x4f8370959a2587L,0x7b7631e37c6188L,
        0x29e51845f104cbL } },
    /* 32 */
    { { 0x426b775e3c647bL,0x327319e0a69180L,0x0c5cb034f6ff2fL,
        0x73aa39b98e9897L,0x7ee615f49fde6eL,0x3f712aa61e0db4L,
        0x33ca06c2ba2ce9L },
      { 0x14973541b8a543L,0x4b4e6101ba61faL,0x1d94e4233d0698L,
        0x501513c715d570L,0x1b8f8c3d01436bL,0x52f41a0445cf64L,
        0x3f709c3a75fb04L } },
    /* 33 */
    { { 0x073c0cbc7f41d6L,0x227c36f5ac8201L,0x508e110fef65d8L,
        0x0f317229529b7fL,0x45fc6030d00e24L,0x118a65d30cebeaL,
        0x3340cc4223a448L },
      { 0x204c999797612cL,0x7c05dd4ce9c5a3L,0x7b865d0a8750e4L,
        0x2f82c876ab7d34L,0x2243ddd2ab4808L,0x6834b9df8a4914L,
        0x123319ed950e0fL } },
    /* 34 */
    { { 0x50430efc14ab48L,0x7e9e4ce0d4e89cL,0x2332207fd8656dL,
        0x4a2809e97f4511L,0x2162bb1b968e2dL,0x29526d54af2972L,
        0x13edd9adcd939dL },
      { 0x793bca31e1ff7fL,0x6b959c9e4d2227L,0x628ac27809a5baL,
        0x2c71ffc7fbaa5fL,0x0c0b058f13c9ceL,0x5676eae68de2cfL,
        0x35508036ea19a4L } },
    /* 35 */
    { { 0x030bbd6dda1265L,0x67f9d12e31bb34L,0x7e4d8196e3ded3L,
        0x7b9120e5352498L,0x75857bce72d875L,0x4ead976a396caeL,
        0x31c5860553a64dL },
      { 0x1a0f792ee32189L,0x564c4efb8165d0L,0x7adc7d1a7fbcbeL,
        0x7ed7c2ccf327b7L,0x35df1b448ce33dL,0x6f67eb838997cdL,
        0x3ee37ec0077917L } },
    /* 36 */
    { { 0x345fa74d5bb921L,0x097c9a56ccfd8eL,0x00a0b5e8f971f8L,
        0x723d95223f69d4L,0x08e2e5c2777f87L,0x68b13676200109L,
        0x26ab5df0acbad6L },
      { 0x01bca7daac34aeL,0x49ca4d5f664dadL,0x110687b850914bL,
        0x1203d6f06443c9L,0x7a2ac743b04d4cL,0x40d96bd3337f82L,
        0x13728be0929c06L } },
    /* 37 */
    { { 0x631ca61127bc1aL,0x2b362fd5a77cd1L,0x17897d68568fb7L,
        0x21070af33db5b2L,0x6872e76221794aL,0x436f29fb076963L,
        0x1f2acfc0ecb7b3L },
      { 0x19bf15ca9b3586L,0x32489a4a17aee2L,0x2b31af3c929551L,
        0x0db7c420b9b19fL,0x538c39bd308c2bL,0x438775c0dea88fL,
        0x1537304d7cd07fL } },
    /* 38 */
    { { 0x53598d943caf0dL,0x1d5244bfe266adL,0x7158feb7ab3811L,
        0x1f46e13cf6fb53L,0x0dcab632eb9447L,0x46302968cfc632L,
        0x0b53d3cc5b6ec7L },
      { 0x69811ca143b7caL,0x5865bcf9f2a11aL,0x74ded7fa093b06L,
        0x1c878ec911d5afL,0x04610e82616e49L,0x1e157fe9640eb0L,
        0x046e6f8561d6c2L } },
    /* 39 */
    { { 0x631a3d3bbe682cL,0x3a4ce9dde5ba95L,0x28f11f7502f1f1L,
        0x0a55cf0c957e88L,0x495e4ec7e0a3bcL,0x30ad4d87ba365cL,
        0x0217b97a4c26f3L },
      { 0x01a9088c2e67fdL,0x7501c4c3d5e5e7L,0x265b7bb854c820L,
        0x729263c87e6b52L,0x308b9e3b8fb035L,0x33f1b86c1b23abL,
        0x0e81b8b21fc99cL } },
    /* 40 */
    { { 0x59f5a87237cac0L,0x6b3a86b0cf28b9L,0x13a53db13a4fc2L,
        0x313c169a1c253bL,0x060158304ed2bbL,0x21e171b71679bcL,
        0x10cdb754d76f86L },
      { 0x44355392ab473aL,0x64eb7cbda08caeL,0x3086426a900c71L,
        0x49016ed9f3c33cL,0x7e6354ab7e04f9L,0x17c4c91a40cd2eL,
        0x3509f461024c66L } },
    /* 41 */
    { { 0x2848f50f9b5a31L,0x68d1755b6c5504L,0x48cd5d5672ec00L,
        0x4d77421919d023L,0x1e1e349ef68807L,0x4ab5130cf415d7L,
        0x305464c6c7dbe6L },
      { 0x64eb0bad74251eL,0x64c6957e52bda4L,0x6c12583440dee6L,
        0x6d3bee05b00490L,0x186970de53dbc4L,0x3be03b37567a56L,
        0x2b553b1ebdc55bL } },
    /* 42 */
    { { 0x74dc3579efdc58L,0x26d29fed1bb71cL,0x334c825a9515afL,
        0x433c1e839273a6L,0x0d8a4e41cff423L,0x3454098fe42f8eL,
        0x1046674bf98686L },
      { 0x09a3e029c05dd2L,0x54d7cfc7fb53a7L,0x35f0ad37e14d7cL,
        0x73a294a13767b9L,0x3f519678275f4fL,0x788c63393993a4L,
        0x0781680b620123L } },
    /* 43 */
    { { 0x4c8e2ed4d5ffe8L,0x112db7d42fe4ebL,0x433b8f2d2be2edL,
        0x23e30b29a82cbcL,0x35d2f4c06ee85aL,0x78ff31ffe4b252L,
        0x0d31295c8cbff5L },
      { 0x314806ea0376a2L,0x4ea09e22bc0589L,0x0879575f00ba97L,
        0x188226d2996bb7L,0x7799368dc9411fL,0x7ab24e5c8cae36L,
        0x2b6a8e2ee4ea33L } },
    /* 44 */
    { { 0x70c7127d4ed72aL,0x24c9743ef34697L,0x2fd30e7a93683aL,
        0x538a89c246012cL,0x6c660a5394ed82L,0x79a95ea239d7e0L,
        0x3f3af3bbfb170dL },
      { 0x3b75aa779ae8c1L,0x33995a3cc0dde4L,0x7489d5720b7bfdL,
        0x599677ef9fa937L,0x3defd64c5ab44bL,0x27d52dc234522bL,
        0x2ac65d1a8450e0L } },
    /* 45 */
    { { 0x478585ec837d7dL,0x5f7971dc174887L,0x67576ed7bb296dL,
        0x5a78e529a74926L,0x640f73f4fa104bL,0x7d42a8b16e4730L,
        0x108c7eaa75fd01L },
      { 0x60661ef96e6896L,0x18d3a0761f3aa7L,0x6e71e163455539L,
        0x165827d6a7e583L,0x4e7f77e9527935L,0x790bebe2ae912eL,
        0x0b8fe9561adb55L } },
    /* 46 */
    { { 0x4d48036a9951a8L,0x371084f255a085L,0x66aeca69cea2c5L,
        0x04c99f40c745e7L,0x08dc4bfd9a0924L,0x0b0ec146b29df7L,
        0x05106218d01c91L },
      { 0x2a56ee99caedc7L,0x5d9b23a203922cL,0x1ce4c80b6a3ec4L,
        0x2666bcb75338cbL,0x185a81aac8c4aaL,0x2b4fb60a06c39eL,
        0x0327e1b3633f42L } },
    /* 47 */
    { { 0x72814710b2a556L,0x52c864f6e16534L,0x4978de66ddd9f2L,
        0x151f5950276cf0L,0x450ac6781d2dc2L,0x114b7a22dd61b2L,
        0x3b32b07f29faf8L },
      { 0x68444fdc2d6e94L,0x68526bd9e437bcL,0x0ca780e8b0d887L,
        0x69f3f850a716aaL,0x500b953e42cd57L,0x4e57744d812e7dL,
        0x000a5f0e715f48L } },
    /* 48 */
    { { 0x2aab10b8243a7dL,0x727d1f4b18b675L,0x0e6b9fdd91bbbbL,
        0x0d58269fc337e5L,0x45d6664105a266L,0x11946af1b14072L,
        0x2c2334f91e46e1L },
      { 0x6dc5f8756d2411L,0x21b34eaa25188bL,0x0d2797da83529eL,
        0x324df55616784bL,0x7039ec66d267dfL,0x2de79cdb2d108cL,
        0x14011b1ad0bde0L } },
    /* 49 */
    { { 0x2e160266425043L,0x55fbe11b712125L,0x7e3c58b3947fd9L,
        0x67aacc79c37ad3L,0x4a18e18d2dea0fL,0x5eef06e5674351L,
        0x37c3483ae33439L },
      { 0x5d5e1d75bb4045L,0x0f9d72db296efdL,0x60b1899dd894a9L,
        0x06e8818ded949aL,0x747fd853c39434L,0x0953b937d9efabL,
        0x09f08c0beeb901L } },
    /* 50 */
    { { 0x1d208a8f2d49ceL,0x54042c5be1445aL,0x1c2681fd943646L,
        0x219c8094e2e674L,0x442cddf07238b8L,0x574a051c590832L,
        0x0b72f4d61c818aL },
      { 0x7bc3cbe4680967L,0x0c8b3f25ae596bL,0x0445b0da74a9efL,
        0x0bbf46c40363b7L,0x1df575c50677a3L,0x016ea6e73d68adL,
        0x0b5207bd8db0fdL } },
    /* 51 */
    { { 0x2d39fdfea1103eL,0x2b252bf0362e34L,0x63d66c992baab9L,
        0x5ac97706de8550L,0x0cca390c39c1acL,0x0d9bec5f01b2eaL,
        0x369360a0f7e5f3L },
      { 0x6dd3461e201067L,0x70b2d3f63ed614L,0x487580487c54c7L,
        0x6020e48a44af2aL,0x1ccf80b21aab04L,0x3cf3b12d88d798L,
        0x349368eccc506fL } },
    /* 52 */
    { { 0x5a053753b0a354L,0x65e818dbb9b0aeL,0x7d5855ee50e4bfL,
        0x58dc06885c7467L,0x5ee15073e57bd3L,0x63254ebc1e07fdL,
        0x1d48e0392aa39bL },
      { 0x4e227c6558ffe9L,0x0c3033d8a82a3eL,0x7bde65c214e8d2L,
        0x6e23561559c16aL,0x5094c5e6deaffdL,0x78dca2880f1f91L,
        0x3d9d3f947d838dL } },
    /* 53 */
    { { 0x387ae5af63408fL,0x6d539aeb4e6edfL,0x7f3d3186368e70L,
        0x01a6446bc19989L,0x35288fbcd4482fL,0x39288d34ec2736L,
        0x1de9c47159ad76L },
      { 0x695dc7944f8d65L,0x3eca2c35575094L,0x0c918059a79b69L,
        0x4573a48c32a74eL,0x580d8bc8b93f52L,0x190be3a3d071eaL,
        0x2333e686b3a8cbL } },
    /* 54 */
    { { 0x2b110c7196fee2L,0x3ac70e99128a51L,0x20a6bb6b75d5e6L,
        0x5f447fa513149aL,0x560d69714cc7b2L,0x1d3ee25279fab1L,
        0x369adb2ccca959L },
      { 0x3fddb13dd821c2L,0x70bf21ba647be8L,0x64121227e3cbc9L,
        0x12633a4c892320L,0x3c15c61660f26dL,0x1932c3b3d19900L,
        0x18c718563eab71L } },
    /* 55 */
    { { 0x72ebe0fd752366L,0x681c2737d11759L,0x143c805e7ae4f0L,
        0x78ed3c2cc7b324L,0x5c16e14820254fL,0x226a4f1c4ec9f0L,
        0x2891bb915eaac6L },
      { 0x061eb453763b33L,0x07f88b81781a87L,0x72b5ac7a87127cL,
        0x7ea4e4cd7ff8b5L,0x5e8c3ce33908b6L,0x0bcb8a3d37feffL,
        0x01da9e8e7fc50bL } },
    /* 56 */
    { { 0x639dfe9e338d10L,0x32dfe856823608L,0x46a1d73bca3b9aL,
        0x2da685d4b0230eL,0x6e0bc1057b6d69L,0x7144ec724a5520L,
        0x0b067c26b87083L },
      { 0x0fc3f0eef4c43dL,0x63500f509552b7L,0x220d74af6f8b86L,
        0x038996eafa2aa9L,0x7f6750f4aee4d2L,0x3e1d3f06718720L,
        0x1ea1d37243814cL } },
    /* 57 */
    { { 0x322d4597c27050L,0x1beeb3ce17f109L,0x15e5ce2e6ef42eL,
        0x6c8be27da6b3a0L,0x66e3347f4d5f5cL,0x7172133899c279L,
        0x250aff4e548743L },
      { 0x28f0f6a43b566dL,0x0cd2437fefbca0L,0x5b1108cb36bdbaL,
        0x48a834d41fb7c2L,0x6cb8565680579fL,0x42da2412b45d9fL,
        0x33dfc1abb6c06eL } },
    /* 58 */
    { { 0x56e3c48ef96c80L,0x65667bb6c1381eL,0x09f70514375487L,
        0x1548ff115f4a08L,0x237de2d21a0710L,0x1425cdee9f43dfL,
        0x26a6a42e055b0aL },
      { 0x4ea9ea9dc7dfcbL,0x4df858583ac58aL,0x1d274f819f1d39L,
        0x26e9c56cf91fcbL,0x6cee31c7c3a465L,0x0bb8e00b108b28L,
        0x226158da117301L } },
    /* 59 */
    { { 0x5a7cd4fce73946L,0x7b6a462d0ac653L,0x732ea4bb1a3da5L,
        0x7c8e9f54711af4L,0x0a6cd55d4655f9L,0x341e6d13e4754aL,
        0x373c87098879a8L },
      { 0x7bc82e61b818bfL,0x5f2db48f44879fL,0x2a2f06833f1d28L,
        0x494e5b691a74c0L,0x17d6cf35fd6b57L,0x5f7028d1c25dfcL,
        0x377a9ab9562cb6L } },
    /* 60 */
    { { 0x4de8877e787b2eL,0x183e7352621a52L,0x2ab0509974962bL,
        0x045a450496cb8aL,0x3bf7118b5591c7L,0x7724f98d761c35L,
        0x301607e8d5a0c1L },
      { 0x0f58a3f24d4d58L,0x3771c19c464f3cL,0x06746f9c0bfafaL,
        0x56564c9c8feb52L,0x0d66d9a7d8a45fL,0x403578141193caL,
        0x00b0d0bdc19260L } },
    /* 61 */
    { { 0x571407157bdbc2L,0x138d5a1c2c0b99L,0x2ee4a8057dcbeaL,
        0x051ff2b58e9ed1L,0x067378ad9e7cdaL,0x7cc2c1db97a49eL,
        0x1e7536ccd849d6L },
      { 0x531fd95f3497c4L,0x55dc08325f61a7L,0x144e942bce32bfL,
        0x642d572f09e53aL,0x556ff188261678L,0x3e79c0d9d513d6L,
        0x0bbbc6656f6d52L } },
    /* 62 */
    { { 0x57d3eb50596edcL,0x26c520a487451dL,0x0a92db40aea8d6L,
        0x27df6345109616L,0x7733d611fd727cL,0x61d14171fef709L,
        0x36169ae417c36bL },
      { 0x6899f5d4091cf7L,0x56ce5dfe4ed0c1L,0x2c430ce5913fbcL,
        0x1b13547e0f8caeL,0x4840a8275d3699L,0x59b8ef209e81adL,
        0x22362dff5ea1a2L } },
    /* 63 */
    { { 0x7237237bd98425L,0x73258e162a9d0bL,0x0a59a1e8bb5118L,
        0x4190a7ee5d8077L,0x13684905fdbf7cL,0x31c4033a52626bL,
        0x010a30e4fbd448L },
      { 0x47623f981e909aL,0x670af7c325b481L,0x3d004241fa4944L,
        0x0905a2ca47f240L,0x58f3cdd7a187c3L,0x78b93aee05b43fL,
        0x19b91d4ef8d63bL } },
    /* 64 */
    { { 0x0d34e116973cf4L,0x4116fc9e69ee0eL,0x657ae2b4a482bbL,
        0x3522eed134d7cdL,0x741e0dde0a036aL,0x6554316a51cc7bL,
        0x00f31c6ca89837L },
      { 0x26770aa06b1dd7L,0x38233a4ceba649L,0x065a1110c96feaL,
        0x18d367839e0f15L,0x794543660558d1L,0x39b605139065dcL,
        0x29abbec071b637L } },
    /* 65 */
    { { 0x1464b401ab5245L,0x16db891b27ff74L,0x724eb49cb26e34L,
        0x74fee3bc9cc33eL,0x6a8bdbebe085eaL,0x5c2e75ca207129L,
        0x1d03f2268e6b08L },
      { 0x28b0a328e23b23L,0x645dc26209a0bcL,0x62c28990348d49L,
        0x4dd9be1fa333d0L,0x6183aac74a72e4L,0x1d6f3ee69e1d03L,
        0x2fff96db0ff670L } },
    /* 66 */
    { { 0x2358f5c6a2123fL,0x5b2bfc51bedb63L,0x4fc6674be649ecL,
        0x51fc16e44b813aL,0x2ffe10a73754c1L,0x69a0c7a053aeefL,
        0x150e605fb6b9b4L },
      { 0x179eef6b8b83c4L,0x64293b28ad05efL,0x331795fab98572L,
        0x09823eec78727dL,0x36508042b89b81L,0x65f1106adb927eL,
        0x2fc0234617f47cL } },
    /* 67 */
    { { 0x12aa244e8068dbL,0x0c834ae5348f00L,0x310fc1a4771cb3L,
        0x6c90a2f9e19ef9L,0x77946fa0573471L,0x37f5df81e5f72fL,
        0x204f5d72cbe048L },
      { 0x613c724383bba6L,0x1ce14844967e0aL,0x797c85e69aa493L,
        0x4fb15b0f2ce765L,0x5807978e2e8aa7L,0x52c75859876a75L,
        0x1554635c763d3eL } },
    /* 68 */
    { { 0x4f292200623f3bL,0x6222be53d7fe07L,0x1e02a9a08c2571L,
        0x22c6058216b912L,0x1ec20044c7ba17L,0x53f94c5efde12bL,
        0x102b8aadfe32a4L },
      { 0x45377aa927b102L,0x0d41b8062ee371L,0x77085a9018e62aL,
        0x0c69980024847cL,0x14739b423a73a9L,0x52ec6961fe3c17L,
        0x38a779c94b5a7dL } },
    /* 69 */
    { { 0x4d14008435af04L,0x363bfd8325b4e8L,0x48cdb715097c95L,
        0x1b534540f8bee0L,0x4ca1e5c90c2a76L,0x4b52c193d6eee0L,
        0x277a33c79becf5L },
      { 0x0fee0d511d3d06L,0x4627f3d6a58f8cL,0x7c81ac245119b8L,
        0x0c8d526ba1e07aL,0x3dbc242f55bac2L,0x2399df8f91fffdL,
        0x353e982079ba3bL } },
    /* 70 */
    { { 0x6405d3b0ab9645L,0x7f31abe3ee236bL,0x456170a9babbb1L,
        0x09634a2456a118L,0x5b1c6045acb9e5L,0x2c75c20d89d521L,
        0x2e27ccf5626399L },
      { 0x307cd97fed2ce4L,0x1c2fbb02b64087L,0x542a068d27e64dL,
        0x148c030b3bc6a6L,0x671129e616ade5L,0x123f40db60dafcL,
        0x07688f3c621220L } },
    /* 71 */
    { { 0x1c46b342f2c4b5L,0x27decc0b3c8f04L,0x0d9bd433464c54L,
        0x1f3d893b818572L,0x2536043b536c94L,0x57e00c4b19ebf9L,
        0x3938fb9e5ad55eL },
      { 0x6b390024c8b22fL,0x4583f97e20a976L,0x2559d24abcbad7L,
        0x67a9cabc9bd8c6L,0x73a56f09432e4aL,0x79eb0beb53a3b7L,
        0x3e19d47f6f8221L } },
    /* 72 */
    { { 0x7399cb9d10e0b2L,0x32acc1b8a36e2aL,0x287d60c2407035L,
        0x42c82420ea4b5cL,0x13f286658bc268L,0x3c91181156e064L,
        0x234b83dcdeb963L },
      { 0x79bc95486cfee6L,0x4d8fd3cb78af36L,0x07362ba5e80da8L,
        0x79d024a0d681b0L,0x6b58406907f87fL,0x4b40f1e977e58fL,
        0x38dcc6fd5fa342L } },
    /* 73 */
    { { 0x72282be1cd0abeL,0x02bd0fdfdf44e5L,0x19b0e0d2f753e4L,
        0x4514e76ce8c4c0L,0x02ebc9c8cdcc1bL,0x6ac0c0373e9fddL,
        0x0dc414af1c81a9L },
      { 0x7a109246f32562L,0x26982e6a3768edL,0x5ecd8daed76ab5L,
        0x2eaa70061eb261L,0x09e7c038a8c514L,0x2a2603cc300658L,
        0x25d93ab9e55cd4L } },
    /* 74 */
    { { 0x11b19fcbd5256aL,0x41e4d94274770fL,0x0133c1a411001fL,
        0x360bac481dbca3L,0x45908b18a9c22bL,0x1e34396fafb03aL,
        0x1b84fea7486edaL },
      { 0x183c62a71e6e16L,0x5f1dc30e93da8eL,0x6cb97b502573c3L,
        0x3708bf0964e3fcL,0x35a7f042eeacceL,0x56370da902c27fL,
        0x3a873c3b72797fL } },
    /* 75 */
    { { 0x6573c9cea4cc9bL,0x2c3b5f9d91e6dcL,0x2a90e2dbd9505eL,
        0x66a75444025f81L,0x1571fb894b03cdL,0x5d1a1f00fd26f3L,
        0x0d19a9fd618855L },
      { 0x659acd56515664L,0x7279478bd616a3L,0x09a909e76d56c3L,
        0x2fd70474250358L,0x3a1a25c850579cL,0x11b9e0f71b74ccL,
        0x1268daef3d1bffL } },
    /* 76 */
    { { 0x7f5acc46d93106L,0x5bc15512f939c8L,0x504b5f92f996deL,
        0x25965549be7a64L,0x357a3a2ae9b80dL,0x3f2bcf9c139cc0L,
        0x0a7ddd99f23b35L },
      { 0x6868f5a8a0b1c5L,0x319ec52f15b1beL,0x0770000a849021L,
        0x7f4d50287bd608L,0x62c971d28a9d7fL,0x164e89309acb72L,
        0x2a29f002cf4a32L } },
    /* 77 */
    { { 0x58a852ae11a338L,0x27e3a35f2dcef8L,0x494d5731ce9e18L,
        0x49516f33f4bb3eL,0x386b26ba370097L,0x4e8fac1ec30248L,
        0x2ac26d4c44455dL },
      { 0x20484198eb9dd0L,0x75982a0e06512bL,0x152271b9279b05L,
        0x5908a9857e36d2L,0x6a933ab45a60abL,0x58d8b1acb24fafL,
        0x28fbcf19425590L } },
    /* 78 */
    { { 0x5420e9df010879L,0x4aba72aec2f313L,0x438e544eda7494L,
        0x2e8e189ce6f7eaL,0x2f771e4efe45bdL,0x0d780293bce7efL,
        0x1569ad3d0d02acL },
      { 0x325251ebeaf771L,0x02510f1a8511e2L,0x3863816bf8aad1L,
        0x60fdb15fe6ac19L,0x4792aef52a348cL,0x38e57a104e9838L,
        0x0d171611a1df1bL } },
    /* 79 */
    { { 0x15ceb0bea65e90L,0x6e56482db339bcL,0x37f618f7b0261fL,
        0x6351abc226dabcL,0x0e999f617b74baL,0x37d3cc57af5b69L,
        0x21df2b987aac68L },
      { 0x2dddaa3a358610L,0x2da264bc560e47L,0x545615d538bf13L,
        0x1c95ac244b8cc7L,0x77de1f741852cbL,0x75d324f00996abL,
        0x3a79b13b46aa3bL } },
    /* 80 */
    { { 0x7db63998683186L,0x6849bb989d530cL,0x7b53c39ef7ed73L,
        0x53bcfbf664d3ffL,0x25ef27c57f71c7L,0x50120ee80f3ad6L,
        0x243aba40ed0205L },
      { 0x2aae5e0ee1fcebL,0x3449d0d8343fbeL,0x5b2864fb7cffc7L,
        0x64dceb5407ac3eL,0x20303a5695523dL,0x3def70812010b2L,
        0x07be937f2e9b6fL } },
    /* 81 */
    { { 0x5838f9e0540015L,0x728d8720efb9f7L,0x1ab5864490b0c8L,
        0x6531754458fdcfL,0x600ff9612440c0L,0x48735b36a585b7L,
        0x3d4aaea86b865dL },
      { 0x6898942cac32adL,0x3c84c5531f23a1L,0x3c9dbd572f7edeL,
        0x5691f0932a2976L,0x186f0db1ac0d27L,0x4fbed18bed5bc9L,
        0x0e26b0dee0b38cL } },
    /* 82 */
    { { 0x1188b4f8e60f5bL,0x602a915455b4a2L,0x60e06af289ff99L,
        0x579fe4bed999e5L,0x2bc03b15e6d9ddL,0x1689649edd66d5L,
        0x3165e277dca9d2L },
      { 0x7cb8a529cf5279L,0x57f8035b34d84dL,0x352e2eb26de8f1L,
        0x6406820c3367c4L,0x5d148f4c899899L,0x483e1408482e15L,
        0x1680bd1e517606L } },
    /* 83 */
    { { 0x5c877cc1c90202L,0x2881f158eae1f4L,0x6f45e207df4267L,
        0x59280eba1452d8L,0x4465b61e267db5L,0x171f1137e09e5cL,
        0x1368eb821daa93L },
      { 0x70fe26e3e66861L,0x52a6663170da7dL,0x71d1ce5b7d79dcL,
        0x1cffe9be1e1afdL,0x703745115a29c4L,0x73b7f897b2f65aL,
        0x02218c3a95891aL } },
    /* 84 */
    { { 0x16866db8a9e8c9L,0x4770b770123d9bL,0x4c116cf34a8465L,
        0x079b28263fc86aL,0x3751c755a72b58L,0x7bc8df1673243aL,
        0x12fff72454f064L },
      { 0x15c049b89554e7L,0x4ea9ef44d7cd9aL,0x42f50765c0d4f1L,
        0x158bb603cb011bL,0x0809dde16470b1L,0x63cad7422ea819L,
        0x38b6cd70f90d7eL } },
    /* 85 */
    { { 0x1e4aab6328e33fL,0x70575f026da3aeL,0x7e1b55c8c55219L,
        0x328d4b403d24caL,0x03b6df1f0a5bd1L,0x26b4bb8b648ed0L,
        0x17161f2f10b76aL },
      { 0x6cdb32bae8b4c0L,0x33176266227056L,0x4975fa58519b45L,
        0x254602ea511d96L,0x4e82e93e402a67L,0x0ca8b5929cdb4fL,
        0x3ae7e0a07918f5L } },
    /* 86 */
    { { 0x60f9d1fecf5b9bL,0x6257e40d2cd469L,0x6c7aa814d28456L,
        0x58aac7caac8e79L,0x703a55f0293cbfL,0x702390a0f48378L,
        0x24b9ae07218b07L },
      { 0x1ebc66cdaf24e3L,0x7d9ae5f9f8e199L,0x42055ee921a245L,
        0x035595936e4d49L,0x129c45d425c08bL,0x6486c5f19ce6ddL,
        0x027dbd5f18ba24L } },
    /* 87 */
    { { 0x7d6b78d29375fbL,0x0a3dc6ba22ae38L,0x35090fa91feaf6L,
        0x7f18587fb7b16eL,0x6e7091dd924608L,0x54e102cdbf5ff8L,
        0x31b131a4c22079L },
      { 0x368f87d6a53fb0L,0x1d3f3d69a3f240L,0x36bf5f9e40e1c6L,
        0x17f150e01f8456L,0x76e5d0835eb447L,0x662fc0a1207100L,
        0x14e3dd97a98e39L } },
    /* 88 */
    { { 0x0249d9c2663b4bL,0x56b68f9a71ba1cL,0x74b119567f9c02L,
        0x5e6f336d8c92acL,0x2ced58f9f74a84L,0x4b75a2c2a467c5L,
        0x30557011cf740eL },
      { 0x6a87993be454ebL,0x29b7076fb99a68L,0x62ae74aaf99bbaL,
        0x399f9aa8fb6c1bL,0x553c24a396dd27L,0x2868337a815ea6L,
        0x343ab6635cc776L } },
    /* 89 */
    { { 0x0e0b0eec142408L,0x79728229662121L,0x605d0ac75e6250L,
        0x49a097a01edfbeL,0x1e20cd270df6b6L,0x7438a0ca9291edL,
        0x29daa430da5f90L },
      { 0x7a33844624825aL,0x181715986985c1L,0x53a6853cae0b92L,
        0x6d98401bd925e8L,0x5a0a34f5dd5e24L,0x7b818ef53cf265L,
        0x0836e43c9d3194L } },
    /* 90 */
    { { 0x1179b70e6c5fd9L,0x0246d9305dd44cL,0x635255edfbe2fbL,
        0x5397b3523b4199L,0x59350cc47e6640L,0x2b57aa97ed4375L,
        0x37efd31abd153aL },
      { 0x7a7afa6907f4faL,0x75c10cb94e6a7eL,0x60a925ab69cc47L,
        0x2ff5bcd9239bd5L,0x13c2113e425f11L,0x56bd3d2f8a1437L,
        0x2c9adbab13774fL } },
    /* 91 */
    { { 0x4ab9f52a2e5f2bL,0x5e537e70b58903L,0x0f242658ebe4f2L,
        0x2648a1e7a5f9aeL,0x1b4c5081e73007L,0x6827d4aff51850L,
        0x3925e41726cd01L },
      { 0x56dd8a55ab3cfbL,0x72d6a31b6d5beaL,0x697bd2e5575112L,
        0x66935519a7aa12L,0x55e97dda7a3aceL,0x0e16afb4237b4cL,
        0x00b68fbff08093L } },
    /* 92 */
    { { 0x4b00366481d0d9L,0x37cb031fbfc5c4L,0x14643f6800dd03L,
        0x6793fef60fe0faL,0x4f43e329c92803L,0x1fce86b96a6d26L,
        0x0ad416975e213aL },
      { 0x7cc6a6711adcc9L,0x64b8a63c43c2d9L,0x1e6caa2a67c0d0L,
        0x610deffd17a54bL,0x57d669d5f38423L,0x77364b8f022636L,
        0x36d4d13602e024L } },
    /* 93 */
    { { 0x72e667ae50a2f5L,0x1b15c950c3a21aL,0x3ccc37c72e6dfeL,
        0x027f7e1d094fb8L,0x43ae1e90aa5d7eL,0x3f5feac3d97ce5L,
        0x0363ed0a336e55L },
      { 0x235f73d7663784L,0x5d8cfc588ad5a4L,0x10ab6ff333016eL,
        0x7d8886af2e1497L,0x549f34fd17988eL,0x3fc4fcaee69a33L,
        0x0622b133a13d9eL } },
    /* 94 */
    { { 0x6344cfa796c53eL,0x0e9a10d00136fdL,0x5d1d284a56efd8L,
        0x608b1968f8aca7L,0x2fa5a66776edcaL,0x13430c44f1609cL,
        0x1499973cb2152aL },
      { 0x3764648104ab58L,0x3226e409fadafcL,0x1513a8466459ddL,
        0x649206ec365035L,0x46149aa3f765b1L,0x3aebf0a035248eL,
        0x1ee60b8c373494L } },
    /* 95 */
    { { 0x4e9efcc15f3060L,0x5e5d50fd77cdc8L,0x071e5403516b58L,
        0x1b7d4e89b24ceaL,0x53b1fa66d6dc03L,0x457f15f892ab5fL,
        0x076332c9397260L },
      { 0x31422b79d7584bL,0x0b01d47e41ba80L,0x3e5611a3171528L,
        0x5f53b9a9fc1be4L,0x7e2fc3d82f110fL,0x006cf350ef0fbfL,
        0x123ae98ec81c12L } },
    /* 96 */
    { { 0x310d41df46e2f6L,0x2ff032a286cf13L,0x64751a721c4eadL,
        0x7b62bcc0339b95L,0x49acf0c195afa4L,0x359d48742544e5L,
        0x276b7632d9e2afL },
      { 0x656c6be182579aL,0x75b65a4d85b199L,0x04a911d1721bfaL,
        0x46e023d0e33477L,0x1ec2d580acd869L,0x540b456f398a37L,
        0x001f698210153dL } },
    /* 97 */
    { { 0x3ca35217b00dd0L,0x73961d034f4d3cL,0x4f520b61c4119dL,
        0x4919fde5cccff7L,0x4d0e0e6f38134dL,0x55c22586003e91L,
        0x24d39d5d8f1b19L },
      { 0x4d4fc3d73234dcL,0x40c50c9d5f8368L,0x149afbc86bf2b8L,
        0x1dbafefc21d7f1L,0x42e6b61355107fL,0x6e506cf4b54f29L,
        0x0f498a6c615228L } },
    /* 98 */
    { { 0x30618f437cfaf8L,0x059640658532c4L,0x1c8a4d90e96e1dL,
        0x4a327bcca4fb92L,0x54143b8040f1a0L,0x4ec0928c5a49e4L,
        0x2af5ad488d9b1fL },
      { 0x1b392bd5338f55L,0x539c0292b41823L,0x1fe35d4df86a02L,
        0x5fa5bb17988c65L,0x02b6cb715adc26L,0x09a48a0c2cb509L,
        0x365635f1a5a9f2L } },
    /* 99 */
    { { 0x58aa87bdc21f31L,0x156900c7cb1935L,0x0ec1f75ee2b6cfL,
        0x5f3e35a77ec314L,0x582dec7b9b7621L,0x3e65deb0e8202aL,
        0x325c314b8a66b7L },
      { 0x702e2a22f24d66L,0x3a20e9982014f1L,0x6424c5b86bbfb0L,
        0x424eea4d795351L,0x7fc4cce7c22055L,0x581383fceb92d7L,
        0x32b663f49ee81bL } },
    /* 100 */
    { { 0x76e2d0b648b73eL,0x59ca39fa50bddaL,0x18bb44f786a7e4L,
        0x28c8d49d464360L,0x1b8bf1d3a574eaL,0x7c670b9bf1635aL,
        0x2efb30a291f4b3L },
      { 0x5326c069cec548L,0x03bbe481416531L,0x08a415c8d93d6fL,
        0x3414a52120d383L,0x1f17a0fc6e9c5cL,0x0de9a090717463L,
        0x22d84b3c67ff07L } },
    /* 101 */
    { { 0x30b5014c3830ebL,0x70791dc1a18b37L,0x09e6ea4e24f423L,
        0x65e148a5253132L,0x446f05d5d40449L,0x7ad5d3d707c0e9L,
        0x18eedd63dd3ab5L },
      { 0x40d2eac6bb29e0L,0x5b0e9605e83c38L,0x554f2c666a56a8L,
        0x0ac27b6c94c48bL,0x1aaecdd91bafe5L,0x73c6e2bdf72634L,
        0x306dab96d19e03L } },
    /* 102 */
    { { 0x6d3e4b42772f41L,0x1aba7796f3a39bL,0x3a03fbb980e9c0L,
        0x2f2ea5da2186a8L,0x358ff444ef1fcfL,0x0798cc0329fcdcL,
        0x39a28bcc9aa46dL },
      { 0x42775c977fe4d2L,0x5eb8fc5483d6b0L,0x0bfe37c039e3f7L,
        0x429292eaf9df60L,0x188bdf4b840cd5L,0x06e10e090749cdL,
        0x0e52678e73192eL } },
    /* 103 */
    { { 0x05de80b08df5feL,0x2af8c77406c5f8L,0x53573c50a0304aL,
        0x277b10b751bca0L,0x65cf8c559132a5L,0x4c667abe25f73cL,
        0x0271809e05a575L },
      { 0x41ced461f7a2fbL,0x0889a9ebdd7075L,0x320c63f2b7760eL,
        0x4f8d4324151c63L,0x5af47315be2e5eL,0x73c62f6aee2885L,
        0x206d6412a56a97L } },
    /* 104 */
    { { 0x6b1c508b21d232L,0x3781185974ead6L,0x1aba7c3ebe1fcfL,
        0x5bdc03cd3f3a5aL,0x74a25036a0985bL,0x5929e30b7211b2L,
        0x16a9f3bc366bd7L },
      { 0x566a7057dcfffcL,0x23b5708a644bc0L,0x348cda2aa5ba8cL,
        0x466aa96b9750d4L,0x6a435ed9b20834L,0x2e7730f2cf9901L,
        0x2b5cd71d5b0410L } },
    /* 105 */
    { { 0x285ab3cee76ef4L,0x68895e3a57275dL,0x6fab2e48fd1265L,
        0x0f1de060428c94L,0x668a2b080b5905L,0x1b589dc3b0cb37L,
        0x3c037886592c9bL },
      { 0x7fb5c0f2e90d4dL,0x334eefb3d8c91aL,0x75747124700388L,
        0x547a2c2e2737f5L,0x2af9c080e37541L,0x0a295370d9091aL,
        0x0bb5c36dad99e6L } },
    /* 106 */
    { { 0x644116586f25cbL,0x0c3f41f9ee1f5dL,0x00628d43a3dedaL,
        0x16e1437aae9669L,0x6aba7861bf3e59L,0x60735631ff4c44L,
        0x345609efaa615eL },
      { 0x41f54792e6acefL,0x4791583f75864dL,0x37f2ff5c7508b1L,
        0x1288912516c3b0L,0x51a2135f6a539bL,0x3b775511f42091L,
        0x127c6afa7afe66L } },
    /* 107 */
    { { 0x79f4f4f7492b73L,0x583d967256342dL,0x51a729bff33ca3L,
        0x3977d2c22d8986L,0x066f528ba8d40bL,0x5d759d30f8eb94L,
        0x0f8e649192b408L },
      { 0x22d84e752555bbL,0x76953855c728c7L,0x3b2254e72aaaa4L,
        0x508cd4ce6c0212L,0x726296d6b5a6daL,0x7a77aa066986f3L,
        0x2267a497bbcf31L } },
    /* 108 */
    { { 0x7f3651bf825dc4L,0x3988817388c56fL,0x257313ed6c3dd0L,
        0x3feab7f3b8ffadL,0x6c0d3cb9e9c9b4L,0x1317be0a7b6ac4L,
        0x2a5f399d7df850L },
      { 0x2fe5a36c934f5eL,0x429199df88ded1L,0x435ea21619b357L,
        0x6aac6a063bac2bL,0x600c149978f5edL,0x76543aa1114c95L,
        0x163ca9c83c7596L } },
    /* 109 */
    { { 0x7dda4a3e4daedbL,0x1824cba360a4cdL,0x09312efd70e0c6L,
        0x454e68a146c885L,0x40aee762fe5c47L,0x29811cbd755a59L,
        0x34b37c95f28319L },
      { 0x77c58b08b717d2L,0x309470d9a0f491L,0x1ab9f40448e01cL,
        0x21c8bd819207b1L,0x6a01803e9361bcL,0x6e5e4c350ec415L,
        0x14fd55a91f8798L } },
    /* 110 */
    { { 0x4cee562f512a90L,0x0008361d53e390L,0x3789b307a892cfL,
        0x064f7be8770ae9L,0x41435d848762cfL,0x662204dd38baa6L,
        0x23d6dcf73f6c5aL },
      { 0x69bef2d2c75d95L,0x2b037c0c9bb43eL,0x495fb4d79a34cfL,
        0x184e140c601260L,0x60193f8d435f9cL,0x283fa52a0c3ad2L,
        0x1998635e3a7925L } },
    /* 111 */
    { { 0x1cfd458ce382deL,0x0dddbd201bbcaeL,0x14d2ae8ed45d60L,
        0x73d764ab0c24cbL,0x2a97fe899778adL,0x0dbd1e01eddfe9L,
        0x2ba5c72d4042c3L },
      { 0x27eebc3af788f1L,0x53ffc827fc5a30L,0x6d1d0726d35188L,
        0x4721275c50aa2aL,0x077125f02e690fL,0x6da8142405db5dL,
        0x126cef68992513L } },
    /* 112 */
    { { 0x3c6067035b2d69L,0x2a1ad7db2361acL,0x3debece6cad41cL,
        0x30095b30f9afc1L,0x25f50b9bd9c011L,0x79201b2f2c1da1L,
        0x3b5c151449c5bdL },
      { 0x76eff4127abdb4L,0x2d31e03ce0382aL,0x24ff21f8bda143L,
        0x0671f244fd3ebaL,0x0c1c00b6bcc6fbL,0x18de9f7c3ebefbL,
        0x33dd48c3809c67L } },
    /* 113 */
    { { 0x61d6c2722d94edL,0x7e426e31041cceL,0x4097439f1b47b0L,
        0x579e798b2d205bL,0x6a430d67f830ebL,0x0d2c676700f727L,
        0x05fea83a82f25bL },
      { 0x3f3482df866b98L,0x3dd353b6a5a9cdL,0x77fe6ae1a48170L,
        0x2f75cc2a8f7cddL,0x7442a3863dad17L,0x643de42d877a79L,
        0x0fec8a38fe7238L } },
    /* 114 */
    { { 0x79b70c0760ac07L,0x195d3af37e9b29L,0x1317ff20f7cf27L,
        0x624e1c739e7504L,0x67330ef50f943dL,0x775e8cf455d793L,
        0x17b94d2d913a9fL },
      { 0x4b627203609e7fL,0x06aac5fb93e041L,0x603c515fdc2611L,
        0x2592ca0d7ae472L,0x02395d1f50a6cbL,0x466ef9648f85d9L,
        0x297cf879768f72L } },
    /* 115 */
    { { 0x3489d67d85fa94L,0x0a6e5b739c8e04L,0x7ebb5eab442e90L,
        0x52665a007efbd0L,0x0967ca57b0d739L,0x24891f9d932b63L,
        0x3cc2d6dbadc9d3L },
      { 0x4b4773c81c5338L,0x73cd47dad7a0f9L,0x7c755bab6ae158L,
        0x50b03d6becefcaL,0x574d6e256d57f0L,0x188db4fffb92aeL,
        0x197e10118071eaL } },
    /* 116 */
    { { 0x45d0cbcba1e7f1L,0x1180056abec91aL,0x6c5f86624bbc28L,
        0x442c83f3b8e518L,0x4e16ae1843ecb4L,0x670cef2fd786c9L,
        0x205b4acb637d2cL },
      { 0x70b0e539aa8671L,0x67c982056bebd0L,0x645c831a5e7c36L,
        0x09e06951a14b32L,0x5dd610ad4c89e6L,0x41c35f20164831L,
        0x3821f29cb4cdb8L } },
    /* 117 */
    { { 0x2831ffaba10079L,0x70f6dac9ffe444L,0x1cfa32ccc03717L,
        0x01519fda22a3c8L,0x23215e815aaa27L,0x390671ad65cbf7L,
        0x03dd4d72de7d52L },
      { 0x1ecd972ee95923L,0x166f8da3813e8eL,0x33199bbd387a1aL,
        0x04525fe15e3dc7L,0x44d2ef54165898L,0x4b7e47d3dc47f7L,
        0x10d5c8db0b5d44L } },
    /* 118 */
    { { 0x176d95ba9cdb1bL,0x14025f04f23dfcL,0x49379332891687L,
        0x6625e5ccbb2a57L,0x7ac0abdbf9d0e5L,0x7aded4fbea15b2L,
        0x314844ac184d67L },
      { 0x6d9ce34f05eae3L,0x3805d2875856d2L,0x1c2122f85e40ebL,
        0x51cb9f2d483a9aL,0x367e91e20f1702L,0x573c3559838dfdL,
        0x0b282b0cb85af1L } },
    /* 119 */
    { { 0x6a12e4ef871eb5L,0x64bb517e14f5ffL,0x29e04d3aaa530bL,
        0x1b07d88268f261L,0x411be11ed16fb0L,0x1f480536db70bfL,
        0x17a7deadfd34e4L },
      { 0x76d72f30646612L,0x5a3bbb43a1b0a0L,0x5e1687440e82bfL,
        0x713b5e69481112L,0x46c3dcb499e174L,0x0862da3b4e2a24L,
        0x31cb55b4d62681L } },
    /* 120 */
    { { 0x5ffc74dae5bb45L,0x18944c37adb9beL,0x6aaa63b1ee641aL,
        0x090f4b6ee057d3L,0x4045cedd2ee00fL,0x21c2c798f7c282L,
        0x2c2c6ef38cd6bdL },
      { 0x40d78501a06293L,0x56f8caa5cc89a8L,0x7231d5f91b37aeL,
        0x655f1e5a465c6dL,0x3f59a81f9cf783L,0x09bbba04c23624L,
        0x0f71ee23bbacdeL } },
    /* 121 */
    { { 0x38d398c4741456L,0x5204c0654243c3L,0x34498c916ea77eL,
        0x12238c60e5fe43L,0x0fc54f411c7625L,0x30b2ca43aa80b6L,
        0x06bead1bb6ea92L },
      { 0x5902ba8674b4adL,0x075ab5b0fa254eL,0x58db83426521adL,
        0x5b66b6b3958e39L,0x2ce4e39890e07bL,0x46702513338b37L,
        0x363690c2ded4d7L } },
    /* 122 */
    { { 0x765642c6b75791L,0x0f4c4300d7f673L,0x404d8bbe101425L,
        0x61e91c88651f1bL,0x61ddc9bc60aed8L,0x0ef36910ce2e65L,
        0x04b44367aa63b8L },
      { 0x72822d3651b7dcL,0x4b750157a2716dL,0x091cb4f2118d16L,
        0x662ba93b101993L,0x447cbd54a1d40aL,0x12cdd48d674848L,
        0x16f10415cbec69L } },
    /* 123 */
    { { 0x0c57a3a751cd0eL,0x0833d7478fadceL,0x1e751f55686436L,
        0x489636c58e1df7L,0x26ad6da941266fL,0x22225d3559880fL,
        0x35b397c45ba0e2L },
      { 0x3ca97b70e1f2ceL,0x78e50427a8680cL,0x06137e042a8f91L,
        0x7ec40d2500b712L,0x3f0ad688ad7b0dL,0x24746fb33f9513L,
        0x3638fcce688f0bL } },
    /* 124 */
    { { 0x753163750bed6fL,0x786507cd16157bL,0x1d6ec228ce022aL,
        0x587255f42d1b31L,0x0c6adf72a3a0f6L,0x4bfeee2da33f5eL,
        0x08b7300814de6cL },
      { 0x00bf8df9a56e11L,0x75aead48fe42e8L,0x3de9bad911b2e2L,
        0x0fadb233e4b8bbL,0x5b054e8fd84f7dL,0x5eb3064152889bL,
        0x01c1c6e8c777a1L } },
    /* 125 */
    { { 0x5fa0e598f8fcb9L,0x11c129a1ae18dfL,0x5c41b482a2273bL,
        0x545664e5044c9cL,0x7e01c915bfb9abL,0x7f626e19296aa0L,
        0x20c91a9822a087L },
      { 0x273a9fbe3c378fL,0x0f126b44b7d350L,0x493764a75df951L,
        0x32dec3c367d24bL,0x1a7ae987fed9d3L,0x58a93055928b85L,
        0x11626975d7775fL } },
    /* 126 */
    { { 0x2bb174a95540a9L,0x10de02c58b613fL,0x2fa8f7b861f3eeL,
        0x44731260bdf3b3L,0x19c38ff7da41feL,0x3535a16e3d7172L,
        0x21a948b83cc7feL },
      { 0x0e6f72868bc259L,0x0c70799df3c979L,0x526919955584c3L,
        0x4d95fda04f8fa2L,0x7bb228e6c0f091L,0x4f728b88d92194L,
        0x2b361c5a136bedL } },
    /* 127 */
    { { 0x0c72ca10c53841L,0x4036ab49f9da12L,0x578408d2b7082bL,
        0x2c4903201fbf5eL,0x14722b3f42a6a8L,0x1997b786181694L,
        0x25c6f10de32849L },
      { 0x79f46d517ff2ffL,0x2dc5d97528f6deL,0x518a494489aa72L,
        0x52748f8af3cf97L,0x472da30a96bb16L,0x1be228f92465a9L,
        0x196f0c47d60479L } },
    /* 128 */
    { { 0x47dd7d139b3239L,0x049c9b06775d0fL,0x627ffc00562d5eL,
        0x04f578d5e5e243L,0x43a788ffcef8b9L,0x7db320be9dde28L,
        0x00837528b8572fL },
      { 0x2969eca306d695L,0x195b72795ec194L,0x5e1fa9b8e77e50L,
        0x4c627f2b3fbfd5L,0x4b91e0d0ee10ffL,0x5698c8d0f35833L,
        0x12d3a9431f475eL } },
    /* 129 */
    { { 0x6409457a0db57eL,0x795b35192e0433L,0x146f973fe79805L,
        0x3d49c516dfb9cfL,0x50dfc3646b3cdaL,0x16a08a2210ad06L,
        0x2b4ef5bcd5b826L },
      { 0x5ebabfee2e3e3eL,0x2e048e724d9726L,0x0a7a7ed6abef40L,
        0x71ff7f83e39ad8L,0x3405ac52a1b852L,0x2e3233357a608dL,
        0x38c1bf3b0e40e6L } },
    /* 130 */
    { { 0x59aec823e4712cL,0x6ed9878331ddadL,0x1cc6faf629f2a0L,
        0x445ff79f36c18cL,0x4edc7ed57aff3dL,0x22ee54c8bdd9e8L,
        0x35398f42d72ec5L },
      { 0x4e7a1cceee0ecfL,0x4c66a707dd1d31L,0x629ad157a23c04L,
        0x3b2c6031dc3c83L,0x3336acbcd3d96cL,0x26ce43adfce0f0L,
        0x3c869c98d699dcL } },
    /* 131 */
    { { 0x58b3cd9586ba11L,0x5d6514b8090033L,0x7c88c3bd736782L,
        0x1735f84f2130edL,0x47784095a9dee0L,0x76312c6e47901bL,
        0x1725f6ebc51455L },
      { 0x6744344bc4503eL,0x16630b4d66e12fL,0x7b3481752c3ec7L,
        0x47bb2ed1f46f95L,0x08a1a497dd1bcfL,0x1f525df2b8ed93L,
        0x0fe492ea993713L } },
    /* 132 */
    { { 0x71b8dd7268b448L,0x1743dfaf3728d7L,0x23938d547f530aL,
        0x648c3d497d0fc6L,0x26c0d769e3ad45L,0x4d25108769a806L,
        0x3fbf2025143575L },
      { 0x485bfd90339366L,0x2de2b99ed87461L,0x24a33347713badL,
        0x1674bc7073958aL,0x5bb2373ee85b5fL,0x57f9bd657e662cL,
        0x2041b248d39042L } },
    /* 133 */
    { { 0x5f01617d02f4eeL,0x2a8e31c4244b91L,0x2dab3e790229e0L,
        0x72d319ea7544afL,0x01ffb8b000cb56L,0x065e63b0daafd3L,
        0x3d7200a7111d6fL },
      { 0x4561ce1b568973L,0x37034c532dd8ecL,0x1368215020be02L,
        0x30e7184cf289ebL,0x199e0c27d815deL,0x7ee1b4dff324e5L,
        0x2f4a11de7fab5cL } },
    /* 134 */
    { { 0x33c2f99b1cdf2bL,0x1e0d78bf42a2c0L,0x64485dececaa67L,
        0x2242a41be93e92L,0x62297b1f15273cL,0x16ebfaafb02205L,
        0x0f50f805f1fdabL },
      { 0x28bb0b3a70eb28L,0x5b1c7d0160d683L,0x05c30a37959f78L,
        0x3d9301184922d2L,0x46c1ead7dbcb1aL,0x03ee161146a597L,
        0x2d413ed9a6ccc1L } },
    /* 135 */
    { { 0x685ab5f97a27c2L,0x59178214023751L,0x4ffef3c585ab17L,
        0x2bc85302aba2a9L,0x675b001780e856L,0x103c8a37f0b33dL,
        0x2241e98ece70a6L },
      { 0x546738260189edL,0x086c8f7a6b96edL,0x00832ad878a129L,
        0x0b679056ba7462L,0x020ce6264bf8c4L,0x3f9f4b4d92abfbL,
        0x3e9c55343c92edL } },
    /* 136 */
    { { 0x482cec9b3f5034L,0x08b59b3cd1fa30L,0x5a55d1bc8e58b5L,
        0x464a5259337d8eL,0x0a5b6c66ade5a5L,0x55db77b504ddadL,
        0x015992935eac35L },
      { 0x54fe51025e32fcL,0x5d7f52dbe4a579L,0x08c564a8c58696L,
        0x4482a8bec4503fL,0x440e75d9d94de9L,0x6992d768020bfaL,
        0x06c311e8ba01f6L } },
    /* 137 */
    { { 0x2a6ac808223878L,0x04d3ccb4aab0b8L,0x6e6ef09ff6e823L,
        0x15cb03ee9158dcL,0x0dc58919171bf7L,0x3273568abf3cb1L,
        0x1b55245b88d98bL },
      { 0x28e9383b1de0c1L,0x30d5009e4f1f1bL,0x334d185a56a134L,
        0x0875865dfa4c46L,0x266edf5eae3beeL,0x2e03ff16d1f7e5L,
        0x29a36bd9f0c16dL } },
    /* 138 */
    { { 0x004cff44b2e045L,0x426c96380ba982L,0x422292281e46d7L,
        0x508dd8d29d7204L,0x3a4ea73fb2995eL,0x4be64090ae07b2L,
        0x3339177a0eff22L },
      { 0x74a97ec2b3106eL,0x0c616d09169f5fL,0x1bb5d8907241a7L,
        0x661fb67f6d41bdL,0x018a88a0daf136L,0x746333a093a7b4L,
        0x3e19f1ac76424eL } },
    /* 139 */
    { { 0x542a5656527296L,0x0e7b9ce22f1bc9L,0x31b0945992b89bL,
        0x6e0570eb85056dL,0x32daf813483ae5L,0x69eeae9d59bb55L,
        0x315ad4b730b557L },
      { 0x2bc16795f32923L,0x6b02b7ba55130eL,0x1e9da67c012f85L,
        0x5616f014dabf8fL,0x777395fcd9c723L,0x2ff075e7743246L,
        0x2993538aff142eL } },
    /* 140 */
    { { 0x72dae20e552b40L,0x2e4ba69aa5d042L,0x001e563e618bd2L,
        0x28feeba3c98772L,0x648c356da2a907L,0x687e2325069ea7L,
        0x0d34ab09a394f0L },
      { 0x73c21813111286L,0x5829b53b304e20L,0x6fba574de08076L,
        0x79f7058f61614eL,0x4e71c9316f1191L,0x24ef12193e0a89L,
        0x35dc4e2bc9d848L } },
    /* 141 */
    { { 0x045e6d3b4ad1cdL,0x729c95493782f0L,0x77f59de85b361aL,
        0x5309b4babf28f8L,0x4d893d9290935fL,0x736f47f2b2669eL,
        0x23270922d757f3L },
      { 0x23a4826f70d4e9L,0x68a8c63215d33eL,0x4d6c2069205c9cL,
        0x46b2938a5eebe0L,0x41d1f1e2de3892L,0x5ca1775544bcb0L,
        0x3130629e5d19dcL } },
    /* 142 */
    { { 0x6e2681593375acL,0x117cfbabc22621L,0x6c903cd4e13ccaL,
        0x6f358f14d4bd97L,0x1bc58fa11089f1L,0x36aa2db4ac426aL,
        0x15ced8464b7ea1L },
      { 0x6966836cba7df5L,0x7c2b1851568113L,0x22b50ff2ffca66L,
        0x50e77d9f48e49aL,0x32775e9bbc7cc9L,0x403915bb0ece71L,
        0x1b8ec7cb9dd7aaL } },
    /* 143 */
    { { 0x65a888b677788bL,0x51887fac2e7806L,0x06792636f98d2bL,
        0x47bbcd59824c3bL,0x1aca908c43e6dcL,0x2e00d15c708981L,
        0x08e031c2c80634L },
      { 0x77fbc3a297c5ecL,0x10a7948af2919eL,0x10cdafb1fb6b2fL,
        0x27762309b486f0L,0x13abf26bbac641L,0x53da38478fc3eeL,
        0x3c22eff379bf55L } },
    /* 144 */
    { { 0x0163f484770ee3L,0x7f28e8942e0cbfL,0x5f86cb51b43831L,
        0x00feccd4e4782fL,0x40e5b417eafe7dL,0x79e5742bbea228L,
        0x3717154aa469beL },
      { 0x271d74a270f721L,0x40eb400890b70cL,0x0e37be81d4cb02L,
        0x786907f4e8d43fL,0x5a1f5b590a7acbL,0x048861883851fdL,
        0x11534a1e563dbbL } },
    /* 145 */
    { { 0x37a6357c525435L,0x6afe6f897b78a5L,0x7b7ff311d4f67bL,
        0x38879df15dc9f4L,0x727def7b8ba987L,0x20285dd0db4436L,
        0x156b0fc64b9243L },
      { 0x7e3a6ec0c1c390L,0x668a88d9bcf690L,0x5925aba5440dbeL,
        0x0f6891a044f593L,0x70b46edfed4d97L,0x1a6cc361bab201L,
        0x046f5bc6e160bcL } },
    /* 146 */
    { { 0x79350f076bc9d1L,0x077d9e79a586b9L,0x0896bc0c705764L,
        0x58e632b90e7e46L,0x14e87e0ad32488L,0x4b1bb3f72c6e00L,
        0x3c3ce9684a5fc5L },
      { 0x108fbaf1f703aaL,0x08405ecec17577L,0x199a8e2d44be73L,
        0x2eb22ed0067763L,0x633944deda3300L,0x20d739eb8e5efbL,
        0x2bbbd94086b532L } },
    /* 147 */
    { { 0x03c8b17a19045dL,0x6205a0a504980bL,0x67fdb3e962b9f0L,
        0x16399e01511a4bL,0x44b09fe9dffc96L,0x00a74ff44a1381L,
        0x14590deed3f886L },
      { 0x54e3d5c2a23ddbL,0x310e5138209d28L,0x613f45490c1c9bL,
        0x6bbc85d44bbec8L,0x2f85fc559e73f6L,0x0d71fa7d0fa8cbL,
        0x2898571d17fbb9L } },
    /* 148 */
    { { 0x5607a84335167dL,0x3009c1eb910f91L,0x7ce63447e62d0bL,
        0x03a0633afcf89eL,0x1234b5aaa50872L,0x5a307b534d547bL,
        0x2f4e97138a952eL },
      { 0x13914c2db0f658L,0x6cdcb47e6e75baL,0x5549169caca772L,
        0x0f20423dfeb16fL,0x6b1ae19d180239L,0x0b7b3bee9b7626L,
        0x1ca81adacfe4efL } },
    /* 149 */
    { { 0x219ec3ad19d96fL,0x3549f6548132dbL,0x699889c7aacd0bL,
        0x74602a58730b19L,0x62dc63bcece81cL,0x316f991c0c317aL,
        0x2b8627867b95e3L },
      { 0x67a25ddced1eedL,0x7e14f0eba756e7L,0x0873fbc09b0495L,
        0x0fefb0e16596adL,0x03e6cd98ef39bbL,0x1179b1cded249dL,
        0x35c79c1db1edc2L } },
    /* 150 */
    { { 0x1368309d4245bfL,0x442e55852a7667L,0x095b0f0f348b65L,
        0x6834cf459dfad4L,0x6645950c9be910L,0x06bd81288c71e6L,
        0x1b015b6e944edfL },
      { 0x7a6a83045ab0e3L,0x6afe88b9252ad0L,0x2285bd65523502L,
        0x6c78543879a282L,0x1c5e264b5c6393L,0x3a820c6a7453eeL,
        0x37562d1d61d3c3L } },
    /* 151 */
    { { 0x6c084f62230c72L,0x599490270bc6cfL,0x1d3369ddd3c53dL,
        0x516ddb5fac5da0L,0x35ab1e15011b1aL,0x5fba9106d3a180L,
        0x3be0f092a0917cL },
      { 0x57328f9fdc2538L,0x0526323fc8d5f6L,0x10cbb79521e602L,
        0x50d01167147ae2L,0x2ec7f1b3cda99eL,0x43073cc736e7beL,
        0x1ded89cadd83a6L } },
    /* 152 */
    { { 0x1d51bda65d56d5L,0x63f2fd4d2dc056L,0x326413d310ea6dL,
        0x3abba5bca92876L,0x6b9aa8bc4d6ebeL,0x1961c687f15d5dL,
        0x311cf07464c381L },
      { 0x2321b1064cd8aeL,0x6e3caac4443850L,0x3346fc4887d2d0L,
        0x1640417e0e640fL,0x4a958a52a07a9eL,0x1346a1b1cb374cL,
        0x0a793cf79beccbL } },
    /* 153 */
    { { 0x29d56cba89aaa5L,0x1581898c0b3c15L,0x1af5b77293c082L,
        0x1617ba53a006ceL,0x62dd3b384e475fL,0x71a9820c3f962aL,
        0x0e4938920b854eL },
      { 0x0b8d98849808abL,0x64c14923546de7L,0x6a20883b78a6fcL,
        0x72de211428acd6L,0x009678b47915bbL,0x21b5269ae5dae6L,
        0x313cc0e60b9457L } },
    /* 154 */
    { { 0x69ee421b1de38bL,0x44b484c6cec1c7L,0x0240596c6a8493L,
        0x2321a62c85fb9eL,0x7a10921802a341L,0x3d2a95507e45c3L,
        0x0752f40f3b6714L },
      { 0x596a38798751e6L,0x46bf186a0feb85L,0x0b23093e23b49cL,
        0x1bfa7bc5afdc07L,0x4ba96f873eefadL,0x292e453fae9e44L,
        0x2773646667b75cL } },
    /* 155 */
    { { 0x1f81a64e94f22aL,0x3125ee3d8683ddL,0x76a660a13b9582L,
        0x5aa584c3640c6eL,0x27cc99fd472953L,0x7048f4d58061d1L,
        0x379a1397ac81e8L },
      { 0x5d1ecd2b6b956bL,0x0829e0366b0697L,0x49548cec502421L,
        0x7af5e2f717c059L,0x329a25a0fec54eL,0x028e99e4bcd7f1L,
        0x071d5fe81fca78L } },
    /* 156 */
    { { 0x4b5c4aeb0fdfe4L,0x1367e11326ce37L,0x7c16f020ef5f19L,
        0x3c55303d77b471L,0x23a4457a06e46aL,0x2174426dd98424L,
        0x226f592114bd69L },
      { 0x4411b94455f15aL,0x52e0115381fae4L,0x45b6d8efbc8f7eL,
        0x58b1221bd86d26L,0x284fb6f8a7ec1fL,0x045835939ddd30L,
        0x0216960accd598L } },
    /* 157 */
    { { 0x4b61f9ec1f138aL,0x4460cd1e18502bL,0x277e4fce3c4726L,
        0x0244246d6414b9L,0x28fbfcef256984L,0x3347ed0db40577L,
        0x3b57fa9e044718L },
      { 0x4f73bcd6d1c833L,0x2c0d0dcf7f0136L,0x2010ac75454254L,
        0x7dc4f6151539a8L,0x0b8929ef6ea495L,0x517e20119d2bdfL,
        0x1e29f9a126ba15L } },
    /* 158 */
    { { 0x683a7c10470cd8L,0x0d05f0dbe0007fL,0x2f6a5026d649cdL,
        0x249ce2fdaed603L,0x116dc1e7a96609L,0x199bd8d82a0b98L,
        0x0694ad0219aeb2L },
      { 0x03a3656e864045L,0x4e552273df82a6L,0x19bcc7553d17abL,
        0x74ac536c1df632L,0x440302fb4a86f6L,0x1becec0e31c9feL,
        0x002045f8fa46b8L } },
    /* 159 */
    { { 0x5833ba384310a2L,0x1db83fad93f8baL,0x0a12713ee2f7edL,
        0x40e0f0fdcd2788L,0x1746de5fb239a5L,0x573748965cfa15L,
        0x1e3dedda0ef650L },
      { 0x6c8ca1c87607aeL,0x785dab9554fc0eL,0x649d8f91860ac8L,
        0x4436f88b52c0f9L,0x67f22ca8a5e4a3L,0x1f990fd219e4c9L,
        0x013dd21c08573fL } },
    /* 160 */
    { { 0x05d116141d161cL,0x5c1d2789da2ea5L,0x11f0d861f99f34L,
        0x692c2650963153L,0x3bd69f5329539eL,0x215898eef8885fL,
        0x041f79dd86f7f1L },
      { 0x76dcc5e96beebdL,0x7f2b50cb42a332L,0x067621cabef8abL,
        0x31e0be607054edL,0x4c67c5e357a3daL,0x5b1a63fbfb1c2bL,
        0x3112efbf5e5c31L } },
    /* 161 */
    { { 0x3f83e24c0c62f1L,0x51dc9c32aae4e0L,0x2ff89b33b66c78L,
        0x21b1c7d354142cL,0x243d8d381c84bcL,0x68729ee50cf4b7L,
        0x0ed29e0f442e09L },
      { 0x1ad7b57576451eL,0x6b2e296d6b91dcL,0x53f2b306e30f42L,
        0x3964ebd9ee184aL,0x0a32855df110e4L,0x31f2f90ddae05fL,
        0x3410cd04e23702L } },
    /* 162 */
    { { 0x60d1522ca8f2feL,0x12909237a83e34L,0x15637f80d58590L,
        0x3c72431b6d714dL,0x7c8e59a615bea2L,0x5f977b688ef35aL,
        0x071c198c0b3ab0L },
      { 0x2b54c699699b4bL,0x14da473c2fd0bcL,0x7ba818ea0ad427L,
        0x35117013940b2fL,0x6e1df6b5e609dbL,0x3f42502720b64dL,
        0x01ee7dc890e524L } },
    /* 163 */
    { { 0x12ec1448ff4e49L,0x3e2edac882522bL,0x20455ab300f93aL,
        0x5849585bd67c14L,0x0393d5aa34ba8bL,0x30f9a1f2044fa7L,
        0x1059c9377a93e0L },
      { 0x4e641cc0139e73L,0x0d9f23c9b0fa78L,0x4b2ad87e2b83f9L,
        0x1c343a9f6d9e3cL,0x1098a4cb46de4dL,0x4ddc893843a41eL,
        0x1797f4167d6e3aL } },
    /* 164 */
    { { 0x4add4675856031L,0x499bd5e5f7a0ffL,0x39ea1f1202271eL,
        0x0ecd7480d7a91eL,0x395f5e5fc10956L,0x0fa7f6b0c9f79bL,
        0x2fad4623aed6cbL },
      { 0x1563c33ae65825L,0x29881cafac827aL,0x50650baf4c45a1L,
        0x034aad988fb9e9L,0x20a6224dc5904cL,0x6fb141a990732bL,
        0x3ec9ae1b5755deL } },
    /* 165 */
    { { 0x3108e7c686ae17L,0x2e73a383b4ad8aL,0x4e6bb142ba4243L,
        0x24d355922c1d80L,0x2f850dd9a088baL,0x21c50325dd5e70L,
        0x33237dd5bd7fa4L },
      { 0x7823a39cab7630L,0x1535f71cff830eL,0x70d92ff0599261L,
        0x227154d2a2477cL,0x495e9bbb4f871cL,0x40d2034835686bL,
        0x31b08f97eaa942L } },
    /* 166 */
    { { 0x0016c19034d8ddL,0x68961627cf376fL,0x6acc90681615aeL,
        0x6bc7690c2e3204L,0x6ddf28d2fe19a2L,0x609b98f84dae4dL,
        0x0f32bfd7c94413L },
      { 0x7d7edc6b21f843L,0x49bbd2ebbc9872L,0x593d6ada7b6a23L,
        0x55736602939e9cL,0x79461537680e39L,0x7a7ee9399ca7cdL,
        0x008776f6655effL } },
    /* 167 */
    { { 0x64585f777233cfL,0x63ec12854de0f6L,0x6b7f9bbbc3f99dL,
        0x301c014b1b55d3L,0x7cf3663bbeb568L,0x24959dcb085bd1L,
        0x12366aa6752881L },
      { 0x77a74c0da5e57aL,0x3279ca93ad939fL,0x33c3c8a1ef08c9L,
        0x641b05ab42825eL,0x02f416d7d098dbL,0x7e3d58be292b68L,
        0x1864dbc46e1f46L } },
    /* 168 */
    { { 0x1da167b8153a9dL,0x47593d07d9e155L,0x386d984e12927fL,
        0x421a6f08a60c7cL,0x5ae9661c24dab3L,0x7927b2e7874507L,
        0x3266ea80609d53L },
      { 0x7d198f4c26b1e3L,0x430d4ea2c4048eL,0x58d8ab77e84ba3L,
        0x1cb14299c37297L,0x6db6031e8f695cL,0x159bd855e26d55L,
        0x3f3f6d318a73ddL } },
    /* 169 */
    { { 0x3ee958cca40298L,0x02a7e5eba32ad6L,0x43b4bab96f0e1eL,
        0x534be79062b2b1L,0x029ead089b37e3L,0x4d585da558f5aaL,
        0x1f9737eb43c376L },
      { 0x0426dfd9b86202L,0x4162866bc0a9f3L,0x18fc518e7bb465L,
        0x6db63380fed812L,0x421e117f709c30L,0x1597f8d0f5cee6L,
        0x04ffbf1289b06aL } },
    /* 170 */
    { { 0x61a1987ffa0a5fL,0x42058c7fc213c6L,0x15b1d38447d2c9L,
        0x3d5f5d7932565eL,0x5db754af445fa7L,0x5d489189fba499L,
        0x02c4c55f51141bL },
      { 0x26b15972e9993dL,0x2fc90bcbd97c45L,0x2ff60f8684b0f1L,
        0x1dc641dd339ab0L,0x3e38e6be23f82cL,0x3368162752c817L,
        0x19bba80ceb45ceL } },
    /* 171 */
    { { 0x7c6e95b4c6c693L,0x6bbc6d5efa7093L,0x74d7f90bf3bf1cL,
        0x54d5be1f0299a1L,0x7cb24f0aa427c6L,0x0a18f3e086c941L,
        0x058a1c90e4faefL },
      { 0x3d6bd016927e1eL,0x1da4ce773098b8L,0x2133522e690056L,
        0x0751416d3fc37eL,0x1beed1643eda66L,0x5288b6727d5c54L,
        0x199320e78655c6L } },
    /* 172 */
    { { 0x74575027eeaf94L,0x124bd533c3ceaeL,0x69421ab7a8a1d7L,
        0x37f2127e093f3dL,0x40281765252a08L,0x25a228798d856dL,
        0x326eca62759c4cL },
      { 0x0c337c51acb0a5L,0x122ba78c1ef110L,0x02498adbb68dc4L,
        0x67240c124b089eL,0x135865d25d9f89L,0x338a76d5ae5670L,
        0x03a8efaf130385L } },
    /* 173 */
    { { 0x3a450ac5e49beaL,0x282af80bb4b395L,0x6779eb0db1a139L,
        0x737cabdd174e55L,0x017b14ca79b5f2L,0x61fdef6048e137L,
        0x3acc12641f6277L },
      { 0x0f730746fe5096L,0x21d05c09d55ea1L,0x64d44bddb1a560L,
        0x75e5035c4778deL,0x158b7776613513L,0x7b5efa90c7599eL,
        0x2caa0791253b95L } },
    /* 174 */
    { { 0x288e5b6d53e6baL,0x435228909d45feL,0x33b4cf23b2a437L,
        0x45b352017d6db0L,0x4372d579d6ef32L,0x0fa9e5badbbd84L,
        0x3a78cff24759bbL },
      { 0x0899d2039eab6eL,0x4cf47d2f76bc22L,0x373f739a3a8c69L,
        0x09beaa5b1000b3L,0x0acdfbe83ebae5L,0x10c10befb0e900L,
        0x33d2ac4cc31be3L } },
    /* 175 */
    { { 0x765845931e08fbL,0x2a3c2a0dc58007L,0x7270da587d90e1L,
        0x1ee648b2bc8f86L,0x5d2ca68107b29eL,0x2b7064846e9e92L,
        0x3633ed98dbb962L },
      { 0x5e0f16a0349b1bL,0x58d8941f570ca4L,0x20abe376a4cf34L,
        0x0f4bd69a360977L,0x21eb07cc424ba7L,0x720d2ecdbbe6ecL,
        0x255597d5a97c34L } },
    /* 176 */
    { { 0x67bbf21a0f5e94L,0x422a3b05a64fc1L,0x773ac447ebddc7L,
        0x1a1331c08019f1L,0x01ef6d269744ddL,0x55f7be5b3b401aL,
        0x072e031c681273L },
      { 0x7183289e21c677L,0x5e0a3391f3162fL,0x5e02d9e65d914aL,
        0x07c79ea1adce2fL,0x667ca5c2e1cbe4L,0x4f287f22caccdaL,
        0x27eaa81673e75bL } },
    /* 177 */
    { { 0x5246180a078fe6L,0x67cc8c9fa3bb15L,0x370f8dd123db31L,
        0x1938dafa69671aL,0x5af72624950c5eL,0x78cc5221ebddf8L,
        0x22d616fe2a84caL },
      { 0x723985a839327fL,0x24fa95584a5e22L,0x3d8a5b3138d38bL,
        0x3829ef4a017acfL,0x4f09b00ae055c4L,0x01df84552e4516L,
        0x2a7a18993e8306L } },
    /* 178 */
    { { 0x7b6224bc310eccL,0x69e2cff429da16L,0x01c850e5722869L,
        0x2e4889443ee84bL,0x264a8df1b3d09fL,0x18a73fe478d0d6L,
        0x370b52740f9635L },
      { 0x52b7d3a9d6f501L,0x5c49808129ee42L,0x5b64e2643fd30cL,
        0x27d903fe31b32cL,0x594cb084d078f9L,0x567fb33e3ae650L,
        0x0db7be9932cb65L } },
    /* 179 */
    { { 0x19b78113ed7cbeL,0x002b2f097a1c8cL,0x70b1dc17fa5794L,
        0x786e8419519128L,0x1a45ba376af995L,0x4f6aa84b8d806cL,
        0x204b4b3bc7ca47L },
      { 0x7581a05fd94972L,0x1c73cadb870799L,0x758f6fefc09b88L,
        0x35c62ba8049b42L,0x6f5e71fc164cc3L,0x0cd738b5702721L,
        0x10021afac9a423L } },
    /* 180 */
    { { 0x654f7937e3c115L,0x5d198288b515cbL,0x4add965c25a6e3L,
        0x5a37df33cd76ffL,0x57bb7e288e1631L,0x049b69089e1a31L,
        0x383a88f4122a99L },
      { 0x4c0e4ef3d80a73L,0x553c77ac9f30e2L,0x20bb18c2021e82L,
        0x2aec0d1c4225c5L,0x397fce0ac9c302L,0x2ab0c2a246e8aaL,
        0x02e5e5190be080L } },
    /* 181 */
    { { 0x7a255a4ae03080L,0x0d68b01513f624L,0x29905bd4e48c8cL,
        0x1d81507027466bL,0x1684aaeb70dee1L,0x7dd460719f0981L,
        0x29c43b0f0a390cL },
      { 0x272567681b1f7dL,0x1d2a5f8502e0efL,0x0fd5cd6b221befL,
        0x5eb4749e9a0434L,0x7d1553a324e2a6L,0x2eefd8e86a7804L,
        0x2ad80d5335109cL } },
    /* 182 */
    { { 0x25342aef4c209dL,0x24e811ac4e0865L,0x3f209757f8ae9dL,
        0x1473ff8a5da57bL,0x340f61c3919cedL,0x7523bf85fb9bc0L,
        0x319602ebca7cceL },
      { 0x121e7541d442cbL,0x4ffa748e49c95cL,0x11493cd1d131dcL,
        0x42b215172ab6b5L,0x045fd87e13cc77L,0x0ae305df76342fL,
        0x373b033c538512L } },
    /* 183 */
    { { 0x389541e9539819L,0x769f3b29b7e239L,0x0d05f695e3232cL,
        0x029d04f0e9a9fbL,0x58b78b7a697fb8L,0x7531b082e6386bL,
        0x215d235bed95a9L },
      { 0x503947c1859c5dL,0x4b82a6ba45443fL,0x78328eab71b3a5L,
        0x7d8a77f8cb3509L,0x53fcd9802e41d4L,0x77552091976edbL,
        0x226c60ad7a5156L } },
    /* 184 */
    { { 0x77ad6a43360710L,0x0fdeabd326d7aeL,0x4012886c92104aL,
        0x2d6c378dd7ae33L,0x7e72ef2c0725f3L,0x4a4671f4ca18e0L,
        0x0afe3b4bb6220fL },
      { 0x212cf4b56e0d6aL,0x7c24d086521960L,0x0662cf71bd414dL,
        0x1085b916c58c25L,0x781eed2be9a350L,0x26880e80db6ab2L,
        0x169e356442f061L } },
    /* 185 */
    { { 0x57aa2ad748b02cL,0x68a34256772a9aL,0x1591c44962f96cL,
        0x110a9edd6e53d2L,0x31eab597e091a3L,0x603e64e200c65dL,
        0x2f66b72e8a1cfcL },
      { 0x5c79d138543f7fL,0x412524363fdfa3L,0x547977e3b40008L,
        0x735ca25436d9f7L,0x232b4888cae049L,0x27ce37a53d8f23L,
        0x34d45881a9b470L } },
    /* 186 */
    { { 0x76b95255924f43L,0x035c9f3bd1aa5dL,0x5eb71a010b4bd0L,
        0x6ce8dda7e39f46L,0x35679627ea70c0L,0x5c987767c7d77eL,
        0x1fa28952b620b7L },
      { 0x106f50b5924407L,0x1cc3435a889411L,0x0597cdce3bc528L,
        0x738f8b0d5077d1L,0x5894dd60c7dd6aL,0x0013d0721f5e2eL,
        0x344573480527d3L } },
    /* 187 */
    { { 0x2e2c1da52abf77L,0x394aa8464ad05eL,0x095259b7330a83L,
        0x686e81cf6a11f5L,0x405c7e48c93c7cL,0x65c3ca9444a2ecL,
        0x07bed6c59c3563L },
      { 0x51f9d994fb1471L,0x3c3ecfa5283b4eL,0x494dccda63f6ccL,
        0x4d07b255363a75L,0x0d2b6d3155d118L,0x3c688299fc9497L,
        0x235692fa3dea3aL } },
    /* 188 */
    { { 0x16b4d452669e98L,0x72451fa85406b9L,0x674a145d39151fL,
        0x325ffd067ae098L,0x527e7805cd1ae0L,0x422a1d1789e48dL,
        0x3e27be63f55e07L },
      { 0x7f95f6dee0b63fL,0x008e444cc74969L,0x01348f3a72b614L,
        0x000cfac81348c3L,0x508ae3e5309ce5L,0x2584fcdee44d34L,
        0x3a4dd994899ee9L } },
    /* 189 */
    { { 0x4d289cc0368708L,0x0e5ebc60dc3b40L,0x78cc44bfab1162L,
        0x77ef2173b7d11eL,0x06091718e39746L,0x30fe19319b83a4L,
        0x17e8f2988529c6L },
      { 0x68188bdcaa9f2aL,0x0e64b1350c1bddL,0x5b18ebac7cc4b3L,
        0x75315a9fcc046eL,0x36e9770fd43db4L,0x54c5857fc69121L,
        0x0417e18f3e909aL } },
    /* 190 */
    { { 0x29795db38059adL,0x6efd20c8fd4016L,0x3b6d1ce8f95a1aL,
        0x4db68f177f8238L,0x14ec7278d2340fL,0x47bd77ff2b77abL,
        0x3d2dc8cd34e9fcL },
      { 0x285980a5a83f0bL,0x08352e2d516654L,0x74894460481e1bL,
        0x17f6f3709c480dL,0x6b590d1b55221eL,0x45c100dc4c9be9L,
        0x1b13225f9d8b91L } },
    /* 191 */
    { { 0x0b905fb4b41d9dL,0x48cc8a474cb7a2L,0x4eda67e8de09b2L,
        0x1de47c829adde8L,0x118ad5b9933d77L,0x7a12665ac3f9a4L,
        0x05631a4fb52997L },
      { 0x5fb2a8e6806e63L,0x27d96bbcca369bL,0x46066f1a6b8c7bL,
        0x63b58fc7ca3072L,0x170a36229c0d62L,0x57176f1e463203L,
        0x0c7ce083e73b9cL } },
    /* 192 */
    { { 0x31caf2c09e1c72L,0x6530253219e9d2L,0x7650c98b601c57L,
        0x182469f99d56c0L,0x415f65d292b7a7L,0x30f62a55549b8eL,
        0x30f443f643f465L },
      { 0x6b35c575ddadd0L,0x14a23cf6d299eeL,0x2f0198c0967d7dL,
        0x1013058178d5bfL,0x39da601c9cc879L,0x09d8963ec340baL,
        0x1b735db13ad2a7L } },
    /* 193 */
    { { 0x20916ffdc83f01L,0x16892aa7c9f217L,0x6bff179888d532L,
        0x4adf3c3d366288L,0x41a62b954726aeL,0x3139609022aeb6L,
        0x3e8ab9b37aff7aL },
      { 0x76bbc70f24659aL,0x33fa98513886c6L,0x13b26af62c4ea6L,
        0x3c4d5826389a0cL,0x526ec28c02bf6aL,0x751ff083d79a7cL,
        0x110ac647990224L } },
    /* 194 */
    { { 0x2c6c62fa2b6e20L,0x3d37edad30c299L,0x6ef25b44b65fcaL,
        0x7470846914558eL,0x712456eb913275L,0x075a967a9a280eL,
        0x186c8188f2a2a0L },
      { 0x2f3b41a6a560b1L,0x3a8070b3f9e858L,0x140936ff0e1e78L,
        0x5fd298abe6da8aL,0x3823a55d08f153L,0x3445eafaee7552L,
        0x2a5fc96731a8b2L } },
    /* 195 */
    { { 0x06317be58edbbbL,0x4a38f3bfbe2786L,0x445b60f75896b7L,
        0x6ec7c92b5adf57L,0x07b6be8038a441L,0x1bcfe002879655L,
        0x2a2174037d6d0eL },
      { 0x776790cf9e48bdL,0x73e14a2c4ed1d3L,0x7eb5ed5f2fc2f7L,
        0x3e0aedb821b384L,0x0ee3b7e151c12fL,0x51a6a29e044bb2L,
        0x0ba13a00cb0d86L } },
    /* 196 */
    { { 0x77607d563ec8d8L,0x023fc726996e44L,0x6bd63f577a9986L,
        0x114a6351e53973L,0x3efe97989da046L,0x1051166e117ed7L,
        0x0354933dd4fb5fL },
      { 0x7699ca2f30c073L,0x4c973b83b9e6d3L,0x2017c2abdbc3e8L,
        0x0cdcdd7a26522bL,0x511070f5b23c7dL,0x70672327e83d57L,
        0x278f842b4a9f26L } },
    /* 197 */
    { { 0x0824f0d4ae972fL,0x60578dd08dcf52L,0x48a74858290fbbL,
        0x7302748bf23030L,0x184b229a178acfL,0x3e8460ade089d6L,
        0x13f2b557fad533L },
      { 0x7f96f3ae728d15L,0x018d8d40066341L,0x01fb94955a289aL,
        0x2d32ed6afc2657L,0x23f4f5e462c3acL,0x60eba5703bfc5aL,
        0x1b91cc06f16c7aL } },
    /* 198 */
    { { 0x411d68af8219b9L,0x79cca36320f4eeL,0x5c404e0ed72e20L,
        0x417cb8692e43f2L,0x305d29c7d98599L,0x3b754d5794a230L,
        0x1c97fb4be404e9L },
      { 0x7cdbafababd109L,0x1ead0eb0ca5090L,0x1a2b56095303e3L,
        0x75dea935012c8fL,0x67e31c071b1d1dL,0x7c324fbfd172c3L,
        0x157e257e6498f7L } },
    /* 199 */
    { { 0x19b00db175645bL,0x4c4f6cb69725f1L,0x36d9ce67bd47ceL,
        0x2005e105179d64L,0x7b952e717867feL,0x3c28599204032cL,
        0x0f5659d44fb347L },
      { 0x1ebcdedb979775L,0x4378d45cfd11a8L,0x14c85413ca66e9L,
        0x3dd17d681c8a4dL,0x58368e7dc23142L,0x14f3eaac6116afL,
        0x0adb45b255f6a0L } },
    /* 200 */
    { { 0x2f5e76279ad982L,0x125b3917034d09L,0x3839a6399e6ed3L,
        0x32fe0b3ebcd6a2L,0x24ccce8be90482L,0x467e26befcc187L,
        0x2828434e2e218eL },
      { 0x17247cd386efd9L,0x27f36a468d85c3L,0x65e181ef203bbfL,
        0x0433a6761120afL,0x1d607a2a8f8625L,0x49f4e55a13d919L,
        0x3367c3b7943e9dL } },
    /* 201 */
    { { 0x3391c7d1a46d4dL,0x38233d602d260cL,0x02127a0f78b7d4L,
        0x56841c162c24c0L,0x4273648fd09aa8L,0x019480bb0e754eL,
        0x3b927987b87e58L },
      { 0x6676be48c76f73L,0x01ec024e9655aeL,0x720fe1c6376704L,
        0x17e06b98885db3L,0x656adec85a4200L,0x73780893c3ce88L,
        0x0a339cdd8df664L } },
    /* 202 */
    { { 0x69af7244544ac7L,0x31ab7402084d2fL,0x67eceb7ef7cb19L,
        0x16f8583b996f61L,0x1e208d12faf91aL,0x4a91584ce4a42eL,
        0x3e08337216c93eL },
      { 0x7a6eea94f4cf77L,0x07a52894678c60L,0x302dd06b14631eL,
        0x7fddb7225c9ceaL,0x55e441d7acd153L,0x2a00d4490b0f44L,
        0x053ef125338cdbL } },
    /* 203 */
    { { 0x120c0c51584e3cL,0x78b3efca804f37L,0x662108aefb1dccL,
        0x11deb55f126709L,0x66def11ada8125L,0x05bbc0d1001711L,
        0x1ee1c99c7fa316L },
      { 0x746f287de53510L,0x1733ef2e32d09cL,0x1df64a2b0924beL,
        0x19758da8f6405eL,0x28f6eb3913e484L,0x7175a1090cc640L,
        0x048aee0d63f0bcL } },
    /* 204 */
    { { 0x1f3b1e3b0b29c3L,0x48649f4882a215L,0x485eca3a9e0dedL,
        0x4228ba85cc82e4L,0x36da1f39bc9379L,0x1659a7078499d1L,
        0x0a67d5f6c04188L },
      { 0x6ac39658afdce3L,0x0d667a0bde8ef6L,0x0ae6ec0bfe8548L,
        0x6d9cb2650571bfL,0x54bea107760ab9L,0x705c53bd340cf2L,
        0x111a86b610c70fL } },
    /* 205 */
    { { 0x7ecea05c6b8195L,0x4f8be93ce3738dL,0x305de9eb9f5d12L,
        0x2c3b9d3d474b56L,0x673691a05746c3L,0x2e3482c428c6eaL,
        0x2a8085fde1f472L },
      { 0x69d15877fd3226L,0x4609c9ec017cc3L,0x71e9b7fc1c3dbcL,
        0x4f8951254e2675L,0x63ee9d15afa010L,0x0f05775b645190L,
        0x28a0a439397ae3L } },
    /* 206 */
    { { 0x387fa03e9de330L,0x40cc32b828b6abL,0x02a482fbc04ac9L,
        0x68cad6e70429b7L,0x741877bff6f2c4L,0x48efe633d3b28bL,
        0x3e612218fe24b3L },
      { 0x6fc1d34fe37657L,0x3d04b9e1c8b5a1L,0x6a2c332ef8f163L,
        0x7ca97e2b135690L,0x37357d2a31208aL,0x29f02f2332bd68L,
        0x17c674c3e63a57L } },
    /* 207 */
    { { 0x683d9a0e6865bbL,0x5e77ec68ad4ce5L,0x4d18f236788bd6L,
        0x7f34b87204f4e3L,0x391ca40e9e578dL,0x3470ed6ddf4e23L,
        0x225544b3e50989L },
      { 0x48eda8cb4e462bL,0x2a948825cf9109L,0x473adedc7e1300L,
        0x37b843b82192edL,0x2b9ac1537dde36L,0x4efe7412732332L,
        0x29cc5981b5262bL } },
    /* 208 */
    { { 0x190d2fcad260f5L,0x7c53dd81d18027L,0x003def5f55db0eL,
        0x7f5ed25bee2df7L,0x2b87e9be167d2eL,0x2b999c7bbcd224L,
        0x1d68a2c260ad50L },
      { 0x010bcde84607a6L,0x0250de9b7e1bedL,0x746d36bfaf1b56L,
        0x3359475ff56abbL,0x7e84b9bc440b20L,0x2eaa7e3b52f162L,
        0x01165412f36a69L } },
    /* 209 */
    { { 0x639a02329e5836L,0x7aa3ee2e4d3a27L,0x5bc9b258ecb279L,
        0x4cb3dfae2d62c6L,0x08d9d3b0c6c437L,0x5a2c177d47eab2L,
        0x36120479fc1f26L },
      { 0x7609a75bd20e4aL,0x3ba414e17551fcL,0x42cd800e1b90c9L,
        0x04921811b88f9bL,0x4443697f9562fdL,0x3a8081b8186959L,
        0x3f5b5c97379e73L } },
    /* 210 */
    { { 0x6fd0e3cf13eafbL,0x3976b5415cbf67L,0x4de40889e48402L,
        0x17e4d36f24062aL,0x16ae7755cf334bL,0x2730ac94b7e0e1L,
        0x377592742f48e0L },
      { 0x5e10b18a045041L,0x682792afaae5a1L,0x19383ec971b816L,
        0x208b17dae2ffc0L,0x439f9d933179b6L,0x55485a9090bcaeL,
        0x1c316f42a2a35cL } },
    /* 211 */
    { { 0x67173897bdf646L,0x0b6956653ef94eL,0x5be3c97f7ea852L,
        0x3110c12671f08eL,0x2474076a3fc7ecL,0x53408be503fe72L,
        0x09155f53a5b44eL },
      { 0x5c804bdd4c27cdL,0x61e81eb8ffd50eL,0x2f7157fdf84717L,
        0x081f880d646440L,0x7aa892acddec51L,0x6ae70683443f33L,
        0x31ed9e8b33a75aL } },
    /* 212 */
    { { 0x0d724f8e357586L,0x1febbec91b4134L,0x6ff7b98a9475fdL,
        0x1c4d9b94e1f364L,0x2b8790499cef00L,0x42fd2080a1b31dL,
        0x3a3bbc6d9b0145L },
      { 0x75bfebc37e3ca9L,0x28db49c1723bd7L,0x50b12fa8a1f17aL,
        0x733d95bbc84b98L,0x45ede81f6c109eL,0x18f5e46fb37b5fL,
        0x34b980804aaec1L } },
    /* 213 */
    { { 0x56060c8a4f57bfL,0x0d2dfe223054c2L,0x718a5bbc03e5d6L,
        0x7b3344cc19b3b9L,0x4d11c9c054bcefL,0x1f5ad422c22e33L,
        0x2609299076f86bL },
      { 0x7b7a5fba89fd01L,0x7013113ef3b016L,0x23d5e0a173e34eL,
        0x736c14462f0f50L,0x1ef5f7ac74536aL,0x4baba6f4400ea4L,
        0x17b310612c9828L } },
    /* 214 */
    { { 0x4ebb19a708c8d3L,0x209f8c7f03d9bbL,0x00461cfe5798fbL,
        0x4f93b6ae822fadL,0x2e5b33b5ad5447L,0x40b024e547a84bL,
        0x22ffad40443385L },
      { 0x33809c888228bfL,0x559f655fefbe84L,0x0032f529fd2f60L,
        0x5a2191ece3478cL,0x5b957fcd771246L,0x6fec181f9ed123L,
        0x33eed3624136a3L } },
    /* 215 */
    { { 0x6a5df93b26139aL,0x55076598fd7134L,0x356a592f34f81dL,
        0x493c6b5a3d4741L,0x435498a4e2a39bL,0x2cd26a0d931c88L,
        0x01925ea3fc7835L },
      { 0x6e8d992b1efa05L,0x79508a727c667bL,0x5f3c15e6b4b698L,
        0x11b6c755257b93L,0x617f5af4b46393L,0x248d995b2b6656L,
        0x339db62e2e22ecL } },
    /* 216 */
    { { 0x52537a083843dcL,0x6a283c82a768c7L,0x13aa6bf25227acL,
        0x768d76ba8baf5eL,0x682977a6525808L,0x67ace52ac23b0bL,
        0x2374b5a2ed612dL },
      { 0x7139e60133c3a4L,0x715697a4f1d446L,0x4b018bf36677a0L,
        0x1dd43837414d83L,0x505ec70730d4f6L,0x09ac100907fa79L,
        0x21caad6e03217eL } },
    /* 217 */
    { { 0x0776d3999d4d49L,0x33bdd87e8bcff8L,0x1036b87f068fadL,
        0x0a9b8ffde4c872L,0x7ab2533596b1eaL,0x305a88fb965378L,
        0x3356d8fa4d65e5L },
      { 0x3366fa77d1ff11L,0x1e0bdbdcd2075cL,0x46910cefc967caL,
        0x7ce700737a1ff6L,0x1c5dc15409c9bdL,0x368436b9bdb595L,
        0x3e7ccd6560b5efL } },
    /* 218 */
    { { 0x1443789422c792L,0x524792b1717f2bL,0x1f7c1d95048e7aL,
        0x5cfe2a225b0d12L,0x245594d29ce85bL,0x20134d254ce168L,
        0x1b83296803921aL },
      { 0x79a78285b3beceL,0x3c738c3f3124d6L,0x6ab9d1fe0907cdL,
        0x0652ceb7fc104cL,0x06b5f58c8ae3fdL,0x486959261c5328L,
        0x0b3813ae677c90L } },
    /* 219 */
    { { 0x66b9941ac37b82L,0x651a4b609b0686L,0x046711edf3fc31L,
        0x77f89f38faa89bL,0x2683ddbf2d5edbL,0x389ef1dfaa3c25L,
        0x20b3616e66273eL },
      { 0x3c6db6e0cb5d37L,0x5d7ae5dc342bc4L,0x74a1dc6c52062bL,
        0x6f7c0bec109557L,0x5c51f7bc221d91L,0x0d7b5880745288L,
        0x1c46c145c4b0ddL } },
    /* 220 */
    { { 0x59ed485ea99eccL,0x201b71956bc21dL,0x72d5c32f73de65L,
        0x1aefd76547643eL,0x580a452cfb2c2dL,0x7cb1a63f5c4dc9L,
        0x39a8df727737aaL },
      { 0x365a341deca452L,0x714a1ad1689cbaL,0x16981d12c42697L,
        0x5a124f4ac91c75L,0x1b2e3f2fedc0dbL,0x4a1c72b8e9d521L,
        0x3855b4694e4e20L } },
    /* 221 */
    { { 0x16b3d047181ae9L,0x17508832f011afL,0x50d33cfeb2ebd1L,
        0x1deae237349984L,0x147c641aa6adecL,0x24a9fb4ebb1ddbL,
        0x2b367504a7a969L },
      { 0x4c55a3d430301bL,0x379ef6a5d492cbL,0x3c56541fc0f269L,
        0x73a546e91698ceL,0x2c2b62ee0b9b5dL,0x6284184d43d0efL,
        0x0e1f5cf6a4b9f0L } },
    /* 222 */
    { { 0x44833e8cd3fdacL,0x28e6665cb71c27L,0x2f8bf87f4ddbf3L,
        0x6cc6c767fb38daL,0x3bc114d734e8b5L,0x12963d5a78ca29L,
        0x34532a161ece41L },
      { 0x2443af5d2d37e9L,0x54e6008c8c452bL,0x2c55d54111cf1bL,
        0x55ac7f7522575aL,0x00a6fba3f8575fL,0x3f92ef3b793b8dL,
        0x387b97d69ecdf7L } },
    /* 223 */
    { { 0x0b464812d29f46L,0x36161daa626f9aL,0x5202fbdb264ca5L,
        0x21245805ff1304L,0x7f9c4a65657885L,0x542d3887f9501cL,
        0x086420deef8507L },
      { 0x5e159aa1b26cfbL,0x3f0ef5ffd0a50eL,0x364b29663a432aL,
        0x49c56888af32a8L,0x6f937e3e0945d1L,0x3cbdeec6d766cdL,
        0x2d80d342ece61aL } },
    /* 224 */
    { { 0x255e3026d8356eL,0x4ddba628c4de9aL,0x074323b593e0d9L,
        0x333bdb0a10eefbL,0x318b396e473c52L,0x6ebb5a95efd3d3L,
        0x3f3bff52aa4e4fL },
      { 0x3138a111c731d5L,0x674365e283b308L,0x5585edd9c416f2L,
        0x466763d9070fd4L,0x1b568befce8128L,0x16eb040e7b921eL,
        0x3d5c898687c157L } },
    /* 225 */
    { { 0x14827736973088L,0x4e110d53f301e6L,0x1f811b09870023L,
        0x53b5e500dbcacaL,0x4ddf0df1e6a7dcL,0x1e9575fb10ce35L,
        0x3fdc153644d936L },
      { 0x763547e2260594L,0x26e5ae764efc59L,0x13be6f4d791a29L,
        0x2021e61e3a0cf1L,0x339cd2b4a1c202L,0x5c7451e08f5121L,
        0x3728b3a851be68L } },
    /* 226 */
    { { 0x78873653277538L,0x444b9ed2ee7156L,0x79ac8b8b069cd3L,
        0x5f0e90933770e8L,0x307662c615389eL,0x40fe6d95a80057L,
        0x04822170cf993cL },
      { 0x677d5690fbfec2L,0x0355af4ae95cb3L,0x417411794fe79eL,
        0x48daf87400a085L,0x33521d3b5f0aaaL,0x53567a3be00ff7L,
        0x04712ccfb1cafbL } },
    /* 227 */
    { { 0x2b983283c3a7f3L,0x579f11b146a9a6L,0x1143d3b16a020eL,
        0x20f1483ef58b20L,0x3f03e18d747f06L,0x3129d12f15de37L,
        0x24c911f7222833L },
      { 0x1e0febcf3d5897L,0x505e26c01cdaacL,0x4f45a9adcff0e9L,
        0x14dfac063c5cebL,0x69e5ce713fededL,0x3481444a44611aL,
        0x0ea49295c7fdffL } },
    /* 228 */
    { { 0x64554cb4093beeL,0x344b4b18dd81f6L,0x350f43b4de9b59L,
        0x28a96a220934caL,0x4aa8da5689a515L,0x27171cbd518509L,
        0x0cfc1753f47c95L },
      { 0x7dfe091b615d6eL,0x7d1ee0aa0fb5c1L,0x145eef3200b7b5L,
        0x33fe88feeab18fL,0x1d62d4f87453e2L,0x43b8db4e47fff1L,
        0x1572f2b8b8f368L } },
    /* 229 */
    { { 0x6bc94e6b4e84f3L,0x60629dee586a66L,0x3bbad5fe65ca18L,
        0x217670db6c2fefL,0x0320a7f4e3272aL,0x3ccff0d976a6deL,
        0x3c26da8ae48cccL },
      { 0x53ecf156778435L,0x7533064765a443L,0x6c5c12f03ca5deL,
        0x44f8245350dabfL,0x342cdd777cf8b3L,0x2b539c42e9f58dL,
        0x10138affc279b1L } },
    /* 230 */
    { { 0x1b135e204c5ddbL,0x40887dfeaa1d37L,0x7fb0ef83da76ffL,
        0x521f2b79af55a5L,0x3f9b38b4c3f0d0L,0x20a9838cce61ceL,
        0x24bb4e2f4b1e32L },
      { 0x003f6aa386e27cL,0x68df59db0a0f8eL,0x21677d5192e713L,
        0x14ab9757501276L,0x411944af961524L,0x3184f39abc5c3fL,
        0x2a8dda80ca078dL } },
    /* 231 */
    { { 0x0592233cdbc95cL,0x54d5de5c66f40fL,0x351caa1512ab86L,
        0x681bdbee020084L,0x6ee2480c853e68L,0x6a5a44262b918fL,
        0x06574e15a3b91dL },
      { 0x31ba03dacd7fbeL,0x0c3da7c18a57a9L,0x49aaaded492d6bL,
        0x3071ff53469e02L,0x5efb4f0d7248c6L,0x6db5fb67f12628L,
        0x29cff668e3d024L } },
    /* 232 */
    { { 0x1b9ef3bb1b17ceL,0x6ccf8c24fe6312L,0x34c15487f45008L,
        0x1a84044095972cL,0x515073a47e449eL,0x2ddc93f9097feeL,
        0x1008fdc894c434L },
      { 0x08e5edb73399faL,0x65b1aa65547d4cL,0x3a117a1057c498L,
        0x7e16c3089d13acL,0x502f2ae4b6f851L,0x57a70f3eb62673L,
        0x111b48a9a03667L } },
    /* 233 */
    { { 0x5023024be164f1L,0x25ad117032401eL,0x46612b3bfe3427L,
        0x2f4f406a8a02b7L,0x16a93a5c4ddf07L,0x7ee71968fcdbe9L,
        0x2267875ace37daL },
      { 0x687e88b59eb2a6L,0x3ac7368fe716d3L,0x28d953a554a036L,
        0x34d52c0acca08fL,0x742a7cf8dd4fd9L,0x10bfeb8575ea60L,
        0x290e454d868dccL } },
    /* 234 */
    { { 0x4e72a3a8a4bdd2L,0x1ba36d1dee04d5L,0x7a43136b63195bL,
        0x6ca8e286a519f3L,0x568e64aece08a9L,0x571d5000b5c10bL,
        0x3f75e9f5dbdd40L },
      { 0x6fb0a698d6fa45L,0x0ce42209d7199cL,0x1f68275f708a3eL,
        0x5749832e91ec3cL,0x6c3665521428b2L,0x14b2bf5747bd4aL,
        0x3b6f940e42a22bL } },
    /* 235 */
    { { 0x4da0adbfb26c82L,0x16792a585f39acL,0x17df9dfda3975cL,
        0x4796b4afaf479bL,0x67be67234e0020L,0x69df5f201dda25L,
        0x09f71a4d12b3dcL },
      { 0x64ff5ec260a46aL,0x579c5b86385101L,0x4f29a7d549f697L,
        0x4e64261242e2ebL,0x54ecacdfb6b296L,0x46e0638b5fddadL,
        0x31eefd3208891dL } },
    /* 236 */
    { { 0x5b72c749fe01b2L,0x230cf27523713aL,0x533d1810e0d1e1L,
        0x5590db7d1dd1e2L,0x7b8ab73e8e43d3L,0x4c8a19bd1c17caL,
        0x19222ce9f74810L },
      { 0x6398b3dddc4582L,0x0352b7d88dfd53L,0x3c55b4e10c5a63L,
        0x38194d13f8a237L,0x106683fd25dd87L,0x59e0b62443458eL,
        0x196cb70aa9cbb9L } },
    /* 237 */
    { { 0x2885f7cd021d63L,0x162bfd4c3e1043L,0x77173dcf98fcd1L,
        0x13d4591d6add36L,0x59311154d0d8f2L,0x74336e86e79b8aL,
        0x13faadc5661883L },
      { 0x18938e7d9ec924L,0x14bcda8fcaa0a1L,0x706d85d41a1355L,
        0x0ac34520d168deL,0x5a92499fe17826L,0x36c2e3b4f00600L,
        0x29c2fd7b5f63deL } },
    /* 238 */
    { { 0x41250dfe2216c5L,0x44a0ec0366a217L,0x575bc1adf8b0dfL,
        0x5ff5cdbdb1800bL,0x7843d4dde8ca18L,0x5fa9e420865705L,
        0x235c38be6c6b02L },
      { 0x473b78aae91abbL,0x39470c6051e44bL,0x3f973cc2dc08c3L,
        0x2837932c5c91f6L,0x25e39ed754ec25L,0x1371c837118e53L,
        0x3b99f3b0aeafe2L } },
    /* 239 */
    { { 0x03acf51be46c65L,0x271fceacbaf5c3L,0x476589ed3a5e25L,
        0x78ec8c3c3c399cL,0x1f5c8bf4ac4c19L,0x730bb733ec68d2L,
        0x29a37e00dd287eL },
      { 0x448ed1bf92b5faL,0x10827c17b86478L,0x55e6fc05b28263L,
        0x0af1226c73a66aL,0x0b66e5df0d09c1L,0x26128315a02682L,
        0x22d84932c5e808L } },
    /* 240 */
    { { 0x5ec3afc26e3392L,0x08e142e45c0084L,0x4388d5ad0f01feL,
        0x0f7acd36e6140cL,0x028c14ed97dffbL,0x311845675a38c6L,
        0x01c1c8f09a3062L },
      { 0x5a302f4cf49e7dL,0x79267e254a44e1L,0x746165052317a1L,
        0x53a09263a566e8L,0x7d478ad5f73abcL,0x187ce5c947dad3L,
        0x18564e1a1ec45fL } },
    /* 241 */
    { { 0x7b9577a9aa0486L,0x766b40c7aaaef6L,0x1f6a411f5db907L,
        0x4543dd4d80beaeL,0x0ad938c7482806L,0x451568bf4b9be1L,
        0x3367ec85d30a22L },
      { 0x5446425747843dL,0x18d94ac223c6b2L,0x052ff3a354d359L,
        0x0b4933f89723f5L,0x03fb517740e056L,0x226b892871dddaL,
        0x2768c2b753f0fdL } },
    /* 242 */
    { { 0x685282ccfa5200L,0x411ed433627b89L,0x77d5c9b8bc9c1dL,
        0x4a13ef2ee5cd29L,0x5582a612407c9eL,0x2307cb42fc3aa9L,
        0x2e661df79956b8L },
      { 0x0e972b015254deL,0x5b63e14def8adeL,0x06995be2ca4a95L,
        0x6cc0cc1e94bf27L,0x7ed8499fe0052aL,0x671a6ca5a5e0f9L,
        0x31e10d4ba10f05L } },
    /* 243 */
    { { 0x690af07e9b2d8aL,0x6030af9e32c8ddL,0x45c7ca3bf2b235L,
        0x40959077b76c81L,0x61eee7f70d5a96L,0x6b04f6aafe9e38L,
        0x3c726f55f1898dL },
      { 0x77d0142a1a6194L,0x1c1631215708b9L,0x403a4f0a9b7585L,
        0x066c8e29f7cef0L,0x6fc32f98cf575eL,0x518a09d818c297L,
        0x34144e99989e75L } },
    /* 244 */
    { { 0x6adbada859fb6aL,0x0dcfb6506ccd51L,0x68f88b8d573e0dL,
        0x4b1ce35bd9af30L,0x241c8293ece2c9L,0x3b5f402c5c4adeL,
        0x34b9b1ee6fde87L },
      { 0x5e625340075e63L,0x54c3f3d9050da1L,0x2a3f9152509016L,
        0x3274e46111bc18L,0x3a7504fd01ac73L,0x4169b387a43209L,
        0x35626f852bc6d4L } },
    /* 245 */
    { { 0x576a4f4662e53bL,0x5ea3f20eecec26L,0x4e5f02be5cd7b0L,
        0x72cc5ac3314be8L,0x0f604ed3201fe9L,0x2a29378ea54bceL,
        0x2d52bd4d6ec4b6L },
      { 0x6a4c2b212c1c76L,0x778fd64a1bfa6dL,0x326828691863d6L,
        0x5616c8bd06a336L,0x5fab552564da4dL,0x46640cab3e91d2L,
        0x1d21f06427299eL } },
    /* 246 */
    { { 0x2bfe37dde98e9cL,0x164c54822332ebL,0x5b736c7df266e4L,
        0x59dab3a8da084cL,0x0ae1eab346f118L,0x182090a4327e3fL,
        0x07b13489dae2e6L },
      { 0x3bc92645452baaL,0x30b159894ae574L,0x5b947c5c78e1f4L,
        0x18f0e004a3c77fL,0x48ca8f357077d9L,0x349ffdcef9bca9L,
        0x3ed224bfd54772L } },
    /* 247 */
    { { 0x1bdad02db8dff8L,0x69fab4450b44b6L,0x3b6802d187518bL,
        0x098368d8eb556cL,0x3fe1943fbefcf4L,0x008851d0de6d42L,
        0x322cbc4605fe25L },
      { 0x2528aaf0d51afbL,0x7d48a9363a0cecL,0x4ba8f77d9a8f8bL,
        0x7dee903437d6c7L,0x1ff5a0d9ccc4b4L,0x34d9bd2fa99831L,
        0x30d9e4f58667c6L } },
    /* 248 */
    { { 0x38909b51b85197L,0x7ba16992512bd4L,0x2c776cfcfffec5L,
        0x2be7879075843cL,0x557e2b05d28ffcL,0x641b17bc5ce357L,
        0x1fcaf8a3710306L },
      { 0x54dca2299a2d48L,0x745d06ef305acaL,0x7c41c65c6944c2L,
        0x679412ec431902L,0x48f2b15ee62827L,0x341a96d8afe06eL,
        0x2a78fd3690c0e1L } },
    /* 249 */
    { { 0x6b7cec83fbc9c6L,0x238e8a82eefc67L,0x5d3c1d9ff0928cL,
        0x55b816d6409bbfL,0x7969612adae364L,0x55b6ff96db654eL,
        0x129beca10073a9L },
      { 0x0b1d2acdfc73deL,0x5d1a3605fa64bdL,0x436076146743beL,
        0x64044b89fcce0cL,0x7ae7b3c18f7fafL,0x7f083ee27cea36L,
        0x0292cd0d7c1ff0L } },
    /* 250 */
    { { 0x5a3c4c019b7d2eL,0x1a35a9b89712fbL,0x38736cc4f18c72L,
        0x603dd832a44e6bL,0x000d1d44aed104L,0x69b1f2fc274ebeL,
        0x03a7b993f76977L },
      { 0x299f3b3e346910L,0x5243f45295afd5L,0x34342cbfa588bdL,
        0x72c40dd1155510L,0x718024fed2f991L,0x2f935e765ad82aL,
        0x246799ea371fb8L } },
    /* 251 */
    { { 0x24fe4c76250533L,0x01cafb02fdf18eL,0x505cb25d462882L,
        0x3e038175157d87L,0x7e3e99b10cdeb1L,0x38b7e72ebc7936L,
        0x081845f7c73433L },
      { 0x049e61be05ebd5L,0x6ab82d8f0581f6L,0x62adffb427ac2eL,
        0x19431f809d198dL,0x36195f6c58b1d6L,0x22cc4c9dedc9a7L,
        0x24b146d8e694fcL } },
    /* 252 */
    { { 0x7c7bc8288b364dL,0x5c10f683cb894aL,0x19a62a68452958L,
        0x1fc24dcb4ce90eL,0x726baa4ed9581fL,0x1f34447dde73d6L,
        0x04c56708f30a21L },
      { 0x131e583a3f4963L,0x071215b4d502e7L,0x196aca542e5940L,
        0x3afd5a91f7450eL,0x671b6eedf49497L,0x6aac7aca5c29e4L,
        0x3fb512470f138bL } },
    /* 253 */
    { { 0x5eadc3f4eb453eL,0x16c795ba34b666L,0x5d7612a4697fddL,
        0x24dd19bb499e86L,0x415b89ca3eeb9bL,0x7c83edf599d809L,
        0x13bc64c9b70269L },
      { 0x52d3243dca3233L,0x0b21444b3a96a7L,0x6d551bc0083b90L,
        0x4f535b88c61176L,0x11e61924298010L,0x0a155b415bb61dL,
        0x17f94fbd26658fL } },
    /* 254 */
    { { 0x2dd06b90c28c65L,0x48582339c8fa6eL,0x01ac8bf2085d94L,
        0x053e660e020fdcL,0x1bece667edf07bL,0x4558f2b33ce24cL,
        0x2f1a766e8673fcL },
      { 0x1d77cd13c06819L,0x4d5dc5056f3a01L,0x18896c6fa18d69L,
        0x120047ca76d625L,0x6af8457d4f4e45L,0x70ddc53358b60aL,
        0x330e11130e82f0L } },
    /* 255 */
    { { 0x0643b1cd4c2356L,0x10a2ea0a8f7c92L,0x2752513011d029L,
        0x4cd4c50321f579L,0x5fdf9ba5724792L,0x2f691653e2ddc0L,
        0x0cfed3d84226cbL },
      { 0x704902a950f955L,0x069bfdb87bbf0cL,0x5817eeda8a5f84L,
        0x1914cdd9089905L,0x0e4a323d7b93f4L,0x1cc3fc340af0b2L,
        0x23874161bd6303L } },
};

/* Multiply the base point of P384 by the scalar and return the result.
 * If map is true then convert result to affine coordinates.
 *
 * r     Resulting point.
 * k     Scalar to multiply by.
 * map   Indicates whether to convert result to affine.
 * ct    Constant time required.
 * heap  Heap to use for allocation.
 * returns MEMORY_E when memory allocation fails and MP_OKAY on success.
 */
static int sp_384_ecc_mulmod_base_7(sp_point_384* r, const sp_digit* k,
        int map, int ct, void* heap)
{
    return sp_384_ecc_mulmod_stripe_7(r, &p384_base, p384_table,
                                      k, map, ct, heap);
}

#endif

/* Multiply the base point of P384 by the scalar and return the result.
 * If map is true then convert result to affine coordinates.
 *
 * km    Scalar to multiply by.
 * r     Resulting point.
 * map   Indicates whether to convert result to affine.
 * heap  Heap to use for allocation.
 * returns MEMORY_E when memory allocation fails and MP_OKAY on success.
 */
int sp_ecc_mulmod_base_384(mp_int* km, ecc_point* r, int map, void* heap)
{
#if (!defined(WOLFSSL_SP_SMALL) && !defined(WOLFSSL_SMALL_STACK)) || defined(WOLFSSL_SP_NO_MALLOC)
    sp_point_384 p;
    sp_digit kd[7];
#endif
    sp_point_384* point;
    sp_digit* k = NULL;
    int err = MP_OKAY;

    err = sp_384_point_new_7(heap, p, point);
#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (err == MP_OKAY) {
        k = (sp_digit*)XMALLOC(sizeof(sp_digit) * 7, heap,
                                                              DYNAMIC_TYPE_ECC);
        if (k == NULL) {
            err = MEMORY_E;
        }
    }
#else
    k = kd;
#endif
    if (err == MP_OKAY) {
        sp_384_from_mp(k, 7, km);

            err = sp_384_ecc_mulmod_base_7(point, k, map, 1, heap);
    }
    if (err == MP_OKAY) {
        err = sp_384_point_to_ecc_point_7(point, r);
    }

#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (k != NULL) {
        XFREE(k, heap, DYNAMIC_TYPE_ECC);
    }
#endif
    sp_384_point_free_7(point, 0, heap);

    return err;
}

#if defined(WOLFSSL_VALIDATE_ECC_KEYGEN) || defined(HAVE_ECC_SIGN) || \
                                                        defined(HAVE_ECC_VERIFY)
/* Returns 1 if the number of zero.
 * Implementation is constant time.
 *
 * a  Number to check.
 * returns 1 if the number is zero and 0 otherwise.
 */
static int sp_384_iszero_7(const sp_digit* a)
{
    return (a[0] | a[1] | a[2] | a[3] | a[4] | a[5] | a[6]) == 0;
}

#endif /* WOLFSSL_VALIDATE_ECC_KEYGEN || HAVE_ECC_SIGN || HAVE_ECC_VERIFY */
/* Add 1 to a. (a = a + 1)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 */
SP_NOINLINE static void sp_384_add_one_7(sp_digit* a)
{
    a[0]++;
    sp_384_norm_7(a);
}

/* Read big endian unsigned byte array into r.
 *
 * r  A single precision integer.
 * size  Maximum number of bytes to convert
 * a  Byte array.
 * n  Number of bytes in array to read.
 */
static void sp_384_from_bin(sp_digit* r, int size, const byte* a, int n)
{
    int i, j = 0;
    word32 s = 0;

    r[0] = 0;
    for (i = n-1; i >= 0; i--) {
        r[j] |= (((sp_digit)a[i]) << s);
        if (s >= 47U) {
            r[j] &= 0x7fffffffffffffL;
            s = 55U - s;
            if (j + 1 >= size) {
                break;
            }
            r[++j] = (sp_digit)a[i] >> s;
            s = 8U - s;
        }
        else {
            s += 8U;
        }
    }

    for (j++; j < size; j++) {
        r[j] = 0;
    }
}

/* Generates a scalar that is in the range 1..order-1.
 *
 * rng  Random number generator.
 * k    Scalar value.
 * returns RNG failures, MEMORY_E when memory allocation fails and
 * MP_OKAY on success.
 */
static int sp_384_ecc_gen_k_7(WC_RNG* rng, sp_digit* k)
{
    int err;
    byte buf[48];

    do {
        err = wc_RNG_GenerateBlock(rng, buf, sizeof(buf));
        if (err == 0) {
            sp_384_from_bin(k, 7, buf, (int)sizeof(buf));
            if (sp_384_cmp_7(k, p384_order2) < 0) {
                sp_384_add_one_7(k);
                break;
            }
        }
    }
    while (err == 0);

    return err;
}

/* Makes a random EC key pair.
 *
 * rng   Random number generator.
 * priv  Generated private value.
 * pub   Generated public point.
 * heap  Heap to use for allocation.
 * returns ECC_INF_E when the point does not have the correct order, RNG
 * failures, MEMORY_E when memory allocation fails and MP_OKAY on success.
 */
int sp_ecc_make_key_384(WC_RNG* rng, mp_int* priv, ecc_point* pub, void* heap)
{
#if (!defined(WOLFSSL_SP_SMALL) && !defined(WOLFSSL_SMALL_STACK)) || defined(WOLFSSL_SP_NO_MALLOC)
    sp_point_384 p;
    sp_digit kd[7];
#ifdef WOLFSSL_VALIDATE_ECC_KEYGEN
    sp_point_384 inf;
#endif
#endif
    sp_point_384* point;
    sp_digit* k = NULL;
#ifdef WOLFSSL_VALIDATE_ECC_KEYGEN
    sp_point_384* infinity = NULL;
#endif
    int err;

    (void)heap;

    err = sp_384_point_new_7(heap, p, point);
#ifdef WOLFSSL_VALIDATE_ECC_KEYGEN
    if (err == MP_OKAY) {
        err = sp_384_point_new_7(heap, inf, infinity);
    }
#endif
#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (err == MP_OKAY) {
        k = (sp_digit*)XMALLOC(sizeof(sp_digit) * 7, heap,
                                                              DYNAMIC_TYPE_ECC);
        if (k == NULL) {
            err = MEMORY_E;
        }
    }
#else
    k = kd;
#endif

    if (err == MP_OKAY) {
        err = sp_384_ecc_gen_k_7(rng, k);
    }
    if (err == MP_OKAY) {
            err = sp_384_ecc_mulmod_base_7(point, k, 1, 1, NULL);
    }

#ifdef WOLFSSL_VALIDATE_ECC_KEYGEN
    if (err == MP_OKAY) {
            err = sp_384_ecc_mulmod_7(infinity, point, p384_order, 1, 1, NULL);
    }
    if (err == MP_OKAY) {
        if (sp_384_iszero_7(point->x) || sp_384_iszero_7(point->y)) {
            err = ECC_INF_E;
        }
    }
#endif

    if (err == MP_OKAY) {
        err = sp_384_to_mp(k, priv);
    }
    if (err == MP_OKAY) {
        err = sp_384_point_to_ecc_point_7(point, pub);
    }

#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (k != NULL) {
        XFREE(k, heap, DYNAMIC_TYPE_ECC);
    }
#endif
#ifdef WOLFSSL_VALIDATE_ECC_KEYGEN
    sp_384_point_free_7(infinity, 1, heap);
#endif
    sp_384_point_free_7(point, 1, heap);

    return err;
}

#ifdef HAVE_ECC_DHE
/* Write r as big endian to byte array.
 * Fixed length number of bytes written: 48
 *
 * r  A single precision integer.
 * a  Byte array.
 */
static void sp_384_to_bin(sp_digit* r, byte* a)
{
    int i, j, s = 0, b;

    for (i=0; i<6; i++) {
        r[i+1] += r[i] >> 55;
        r[i] &= 0x7fffffffffffffL;
    }
    j = 384 / 8 - 1;
    a[j] = 0;
    for (i=0; i<7 && j>=0; i++) {
        b = 0;
        /* lint allow cast of mismatch sp_digit and int */
        a[j--] |= (byte)(r[i] << s); /*lint !e9033*/
        b += 8 - s;
        if (j < 0) {
            break;
        }
        while (b < 55) {
            a[j--] = (byte)(r[i] >> b);
            b += 8;
            if (j < 0) {
                break;
            }
        }
        s = 8 - (b - 55);
        if (j >= 0) {
            a[j] = 0;
        }
        if (s != 0) {
            j++;
        }
    }
}

/* Multiply the point by the scalar and serialize the X ordinate.
 * The number is 0 padded to maximum size on output.
 *
 * priv    Scalar to multiply the point by.
 * pub     Point to multiply.
 * out     Buffer to hold X ordinate.
 * outLen  On entry, size of the buffer in bytes.
 *         On exit, length of data in buffer in bytes.
 * heap    Heap to use for allocation.
 * returns BUFFER_E if the buffer is to small for output size,
 * MEMORY_E when memory allocation fails and MP_OKAY on success.
 */
int sp_ecc_secret_gen_384(mp_int* priv, ecc_point* pub, byte* out,
                          word32* outLen, void* heap)
{
#if (!defined(WOLFSSL_SP_SMALL) && !defined(WOLFSSL_SMALL_STACK)) || defined(WOLFSSL_SP_NO_MALLOC)
    sp_point_384 p;
    sp_digit kd[7];
#endif
    sp_point_384* point = NULL;
    sp_digit* k = NULL;
    int err = MP_OKAY;

    if (*outLen < 48U) {
        err = BUFFER_E;
    }

    if (err == MP_OKAY) {
        err = sp_384_point_new_7(heap, p, point);
    }
#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (err == MP_OKAY) {
        k = (sp_digit*)XMALLOC(sizeof(sp_digit) * 7, heap,
                                                              DYNAMIC_TYPE_ECC);
        if (k == NULL)
            err = MEMORY_E;
    }
#else
    k = kd;
#endif

    if (err == MP_OKAY) {
        sp_384_from_mp(k, 7, priv);
        sp_384_point_from_ecc_point_7(point, pub);
            err = sp_384_ecc_mulmod_7(point, point, k, 1, 1, heap);
    }
    if (err == MP_OKAY) {
        sp_384_to_bin(point->x, out);
        *outLen = 48;
    }

#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (k != NULL) {
        XFREE(k, heap, DYNAMIC_TYPE_ECC);
    }
#endif
    sp_384_point_free_7(point, 0, heap);

    return err;
}
#endif /* HAVE_ECC_DHE */

#if defined(HAVE_ECC_SIGN) || defined(HAVE_ECC_VERIFY)
#endif
#if defined(HAVE_ECC_SIGN) || defined(HAVE_ECC_VERIFY)
/* Multiply a by scalar b into r. (r = a * b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A scalar.
 */
SP_NOINLINE static void sp_384_mul_d_7(sp_digit* r, const sp_digit* a,
    sp_digit b)
{
#ifdef WOLFSSL_SP_SMALL
    int128_t tb = b;
    int128_t t = 0;
    int i;

    for (i = 0; i < 7; i++) {
        t += tb * a[i];
        r[i] = t & 0x7fffffffffffffL;
        t >>= 55;
    }
    r[7] = (sp_digit)t;
#else
    int128_t tb = b;
    int128_t t[7];

    t[ 0] = tb * a[ 0];
    t[ 1] = tb * a[ 1];
    t[ 2] = tb * a[ 2];
    t[ 3] = tb * a[ 3];
    t[ 4] = tb * a[ 4];
    t[ 5] = tb * a[ 5];
    t[ 6] = tb * a[ 6];
    r[ 0] =                           (t[ 0] & 0x7fffffffffffffL);
    r[ 1] = (sp_digit)(t[ 0] >> 55) + (t[ 1] & 0x7fffffffffffffL);
    r[ 2] = (sp_digit)(t[ 1] >> 55) + (t[ 2] & 0x7fffffffffffffL);
    r[ 3] = (sp_digit)(t[ 2] >> 55) + (t[ 3] & 0x7fffffffffffffL);
    r[ 4] = (sp_digit)(t[ 3] >> 55) + (t[ 4] & 0x7fffffffffffffL);
    r[ 5] = (sp_digit)(t[ 4] >> 55) + (t[ 5] & 0x7fffffffffffffL);
    r[ 6] = (sp_digit)(t[ 5] >> 55) + (t[ 6] & 0x7fffffffffffffL);
    r[ 7] = (sp_digit)(t[ 6] >> 55);
#endif /* WOLFSSL_SP_SMALL */
}

#ifdef WOLFSSL_SP_DIV_64
static WC_INLINE sp_digit sp_384_div_word_7(sp_digit d1, sp_digit d0,
    sp_digit dv)
{
    sp_digit d, r, t;

    /* All 55 bits from d1 and top 8 bits from d0. */
    d = (d1 << 8) | (d0 >> 47);
    r = d / dv;
    d -= r * dv;
    /* Up to 9 bits in r */
    /* Next 8 bits from d0. */
    r <<= 8;
    d <<= 8;
    d |= (d0 >> 39) & ((1 << 8) - 1);
    t = d / dv;
    d -= t * dv;
    r += t;
    /* Up to 17 bits in r */
    /* Next 8 bits from d0. */
    r <<= 8;
    d <<= 8;
    d |= (d0 >> 31) & ((1 << 8) - 1);
    t = d / dv;
    d -= t * dv;
    r += t;
    /* Up to 25 bits in r */
    /* Next 8 bits from d0. */
    r <<= 8;
    d <<= 8;
    d |= (d0 >> 23) & ((1 << 8) - 1);
    t = d / dv;
    d -= t * dv;
    r += t;
    /* Up to 33 bits in r */
    /* Next 8 bits from d0. */
    r <<= 8;
    d <<= 8;
    d |= (d0 >> 15) & ((1 << 8) - 1);
    t = d / dv;
    d -= t * dv;
    r += t;
    /* Up to 41 bits in r */
    /* Next 8 bits from d0. */
    r <<= 8;
    d <<= 8;
    d |= (d0 >> 7) & ((1 << 8) - 1);
    t = d / dv;
    d -= t * dv;
    r += t;
    /* Up to 49 bits in r */
    /* Remaining 7 bits from d0. */
    r <<= 7;
    d <<= 7;
    d |= d0 & ((1 << 7) - 1);
    t = d / dv;
    r += t;

    return r;
}
#endif /* WOLFSSL_SP_DIV_64 */

/* Divide d in a and put remainder into r (m*d + r = a)
 * m is not calculated as it is not needed at this time.
 *
 * a  Number to be divided.
 * d  Number to divide with.
 * m  Multiplier result.
 * r  Remainder from the division.
 * returns MEMORY_E when unable to allocate memory and MP_OKAY otherwise.
 */
static int sp_384_div_7(const sp_digit* a, const sp_digit* d, sp_digit* m,
        sp_digit* r)
{
    int i;
#ifndef WOLFSSL_SP_DIV_64
    int128_t d1;
#endif
    sp_digit dv, r1;
#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    sp_digit* td;
#else
    sp_digit t1d[14], t2d[7 + 1];
#endif
    sp_digit* t1;
    sp_digit* t2;
    int err = MP_OKAY;

    (void)m;

#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    td = (sp_digit*)XMALLOC(sizeof(sp_digit) * (3 * 7 + 1), NULL,
                                                       DYNAMIC_TYPE_TMP_BUFFER);
    if (td == NULL) {
        err = MEMORY_E;
    }
#endif

    if (err == MP_OKAY) {
#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
        t1 = td;
        t2 = td + 2 * 7;
#else
        t1 = t1d;
        t2 = t2d;
#endif

        dv = d[6];
        XMEMCPY(t1, a, sizeof(*t1) * 2U * 7U);
        for (i=6; i>=0; i--) {
            t1[7 + i] += t1[7 + i - 1] >> 55;
            t1[7 + i - 1] &= 0x7fffffffffffffL;
#ifndef WOLFSSL_SP_DIV_64
            d1 = t1[7 + i];
            d1 <<= 55;
            d1 += t1[7 + i - 1];
            r1 = (sp_digit)(d1 / dv);
#else
            r1 = sp_384_div_word_7(t1[7 + i], t1[7 + i - 1], dv);
#endif

            sp_384_mul_d_7(t2, d, r1);
            (void)sp_384_sub_7(&t1[i], &t1[i], t2);
            t1[7 + i] -= t2[7];
            t1[7 + i] += t1[7 + i - 1] >> 55;
            t1[7 + i - 1] &= 0x7fffffffffffffL;
            r1 = (((-t1[7 + i]) << 55) - t1[7 + i - 1]) / dv;
            r1++;
            sp_384_mul_d_7(t2, d, r1);
            (void)sp_384_add_7(&t1[i], &t1[i], t2);
            t1[7 + i] += t1[7 + i - 1] >> 55;
            t1[7 + i - 1] &= 0x7fffffffffffffL;
        }
        t1[7 - 1] += t1[7 - 2] >> 55;
        t1[7 - 2] &= 0x7fffffffffffffL;
        r1 = t1[7 - 1] / dv;

        sp_384_mul_d_7(t2, d, r1);
        (void)sp_384_sub_7(t1, t1, t2);
        XMEMCPY(r, t1, sizeof(*r) * 2U * 7U);
        for (i=0; i<6; i++) {
            r[i+1] += r[i] >> 55;
            r[i] &= 0x7fffffffffffffL;
        }
        sp_384_cond_add_7(r, r, d, 0 - ((r[6] < 0) ?
                    (sp_digit)1 : (sp_digit)0));
    }

#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (td != NULL) {
        XFREE(td, NULL, DYNAMIC_TYPE_TMP_BUFFER);
    }
#endif

    return err;
}

/* Reduce a modulo m into r. (r = a mod m)
 *
 * r  A single precision number that is the reduced result.
 * a  A single precision number that is to be reduced.
 * m  A single precision number that is the modulus to reduce with.
 * returns MEMORY_E when unable to allocate memory and MP_OKAY otherwise.
 */
static int sp_384_mod_7(sp_digit* r, const sp_digit* a, const sp_digit* m)
{
    return sp_384_div_7(a, m, NULL, r);
}

#endif
#if defined(HAVE_ECC_SIGN) || defined(HAVE_ECC_VERIFY)
#ifdef WOLFSSL_SP_SMALL
/* Order-2 for the P384 curve. */
static const uint64_t p384_order_minus_2[6] = {
    0xecec196accc52971U,0x581a0db248b0a77aU,0xc7634d81f4372ddfU,
    0xffffffffffffffffU,0xffffffffffffffffU,0xffffffffffffffffU
};
#else
/* The low half of the order-2 of the P384 curve. */
static const uint64_t p384_order_low[3] = {
    0xecec196accc52971U,0x581a0db248b0a77aU,0xc7634d81f4372ddfU
    
};
#endif /* WOLFSSL_SP_SMALL */

/* Multiply two number mod the order of P384 curve. (r = a * b mod order)
 *
 * r  Result of the multiplication.
 * a  First operand of the multiplication.
 * b  Second operand of the multiplication.
 */
static void sp_384_mont_mul_order_7(sp_digit* r, const sp_digit* a, const sp_digit* b)
{
    sp_384_mul_7(r, a, b);
    sp_384_mont_reduce_order_7(r, p384_order, p384_mp_order);
}

/* Square number mod the order of P384 curve. (r = a * a mod order)
 *
 * r  Result of the squaring.
 * a  Number to square.
 */
static void sp_384_mont_sqr_order_7(sp_digit* r, const sp_digit* a)
{
    sp_384_sqr_7(r, a);
    sp_384_mont_reduce_order_7(r, p384_order, p384_mp_order);
}

#ifndef WOLFSSL_SP_SMALL
/* Square number mod the order of P384 curve a number of times.
 * (r = a ^ n mod order)
 *
 * r  Result of the squaring.
 * a  Number to square.
 */
static void sp_384_mont_sqr_n_order_7(sp_digit* r, const sp_digit* a, int n)
{
    int i;

    sp_384_mont_sqr_order_7(r, a);
    for (i=1; i<n; i++) {
        sp_384_mont_sqr_order_7(r, r);
    }
}
#endif /* !WOLFSSL_SP_SMALL */

/* Invert the number, in Montgomery form, modulo the order of the P384 curve.
 * (r = 1 / a mod order)
 *
 * r   Inverse result.
 * a   Number to invert.
 * td  Temporary data.
 */

#ifdef WOLFSSL_SP_NONBLOCK
typedef struct sp_384_mont_inv_order_7_ctx {
    int state;
    int i;
} sp_384_mont_inv_order_7_ctx;
static int sp_384_mont_inv_order_7_nb(sp_ecc_ctx_t* sp_ctx, sp_digit* r, const sp_digit* a,
        sp_digit* t)
{
    int err = FP_WOULDBLOCK;
    sp_384_mont_inv_order_7_ctx* ctx = (sp_384_mont_inv_order_7_ctx*)sp_ctx;
    
    typedef char ctx_size_test[sizeof(sp_384_mont_inv_order_7_ctx) >= sizeof(*sp_ctx) ? -1 : 1];
    (void)sizeof(ctx_size_test);

    switch (ctx->state) {
    case 0:
        XMEMCPY(t, a, sizeof(sp_digit) * 7);
        ctx->i = 382;
        ctx->state = 1;
        break;
    case 1:
        sp_384_mont_sqr_order_7(t, t);
        ctx->state = 2;
        break;
    case 2:
        if ((p384_order_minus_2[ctx->i / 64] & ((sp_int_digit)1 << (ctx->i % 64))) != 0) {
            sp_384_mont_mul_order_7(t, t, a);
        }
        ctx->i--;
        ctx->state = (ctx->i == 0) ? 3 : 1;
        break;
    case 3:
        XMEMCPY(r, t, sizeof(sp_digit) * 7U);
        err = MP_OKAY;
        break;
    }
    return err;
}
#endif /* WOLFSSL_SP_NONBLOCK */

static void sp_384_mont_inv_order_7(sp_digit* r, const sp_digit* a,
        sp_digit* td)
{
#ifdef WOLFSSL_SP_SMALL
    sp_digit* t = td;
    int i;

    XMEMCPY(t, a, sizeof(sp_digit) * 7);
    for (i=382; i>=0; i--) {
        sp_384_mont_sqr_order_7(t, t);
        if ((p384_order_minus_2[i / 64] & ((sp_int_digit)1 << (i % 64))) != 0) {
            sp_384_mont_mul_order_7(t, t, a);
        }
    }
    XMEMCPY(r, t, sizeof(sp_digit) * 7U);
#else
    sp_digit* t = td;
    sp_digit* t2 = td + 2 * 7;
    sp_digit* t3 = td + 4 * 7;
    int i;

    /* t = a^2 */
    sp_384_mont_sqr_order_7(t, a);
    /* t = a^3 = t * a */
    sp_384_mont_mul_order_7(t, t, a);
    /* t2= a^c = t ^ 2 ^ 2 */
    sp_384_mont_sqr_n_order_7(t2, t, 2);
    /* t = a^f = t2 * t */
    sp_384_mont_mul_order_7(t, t2, t);
    /* t2= a^f0 = t ^ 2 ^ 4 */
    sp_384_mont_sqr_n_order_7(t2, t, 4);
    /* t = a^ff = t2 * t */
    sp_384_mont_mul_order_7(t, t2, t);
    /* t2= a^ff00 = t ^ 2 ^ 8 */
    sp_384_mont_sqr_n_order_7(t2, t, 8);
    /* t3= a^ffff = t2 * t */
    sp_384_mont_mul_order_7(t3, t2, t);
    /* t2= a^ffff0000 = t3 ^ 2 ^ 16 */
    sp_384_mont_sqr_n_order_7(t2, t3, 16);
    /* t = a^ffffffff = t2 * t3 */
    sp_384_mont_mul_order_7(t, t2, t3);
    /* t2= a^ffffffff0000 = t ^ 2 ^ 16  */
    sp_384_mont_sqr_n_order_7(t2, t, 16);
    /* t = a^ffffffffffff = t2 * t3 */
    sp_384_mont_mul_order_7(t, t2, t3);
    /* t2= a^ffffffffffff000000000000 = t ^ 2 ^ 48  */
    sp_384_mont_sqr_n_order_7(t2, t, 48);
    /* t= a^fffffffffffffffffffffffff = t2 * t */
    sp_384_mont_mul_order_7(t, t2, t);
    /* t2= a^ffffffffffffffffffffffff000000000000000000000000 */
    sp_384_mont_sqr_n_order_7(t2, t, 96);
    /* t2= a^ffffffffffffffffffffffffffffffffffffffffffffffff = t2 * t */
    sp_384_mont_mul_order_7(t2, t2, t);
    for (i=191; i>=1; i--) {
        sp_384_mont_sqr_order_7(t2, t2);
        if (((sp_digit)p384_order_low[i / 64] & ((sp_int_digit)1 << (i % 64))) != 0) {
            sp_384_mont_mul_order_7(t2, t2, a);
        }
    }
    sp_384_mont_sqr_order_7(t2, t2);
    sp_384_mont_mul_order_7(r, t2, a);
#endif /* WOLFSSL_SP_SMALL */
}

#endif /* HAVE_ECC_SIGN || HAVE_ECC_VERIFY */
#ifdef HAVE_ECC_SIGN
#ifndef SP_ECC_MAX_SIG_GEN
#define SP_ECC_MAX_SIG_GEN  64
#endif

/* Sign the hash using the private key.
 *   e = [hash, 384 bits] from binary
 *   r = (k.G)->x mod order
 *   s = (r * x + e) / k mod order
 * The hash is truncated to the first 384 bits.
 *
 * hash     Hash to sign.
 * hashLen  Length of the hash data.
 * rng      Random number generator.
 * priv     Private part of key - scalar.
 * rm       First part of result as an mp_int.
 * sm       Sirst part of result as an mp_int.
 * heap     Heap to use for allocation.
 * returns RNG failures, MEMORY_E when memory allocation fails and
 * MP_OKAY on success.
 */
#ifdef WOLFSSL_SP_NONBLOCK
typedef struct sp_ecc_sign_384_ctx {
    int state;
    union {
        sp_384_ecc_mulmod_7_ctx mulmod_ctx;
        sp_384_mont_inv_order_7_ctx mont_inv_order_ctx;
    };
    sp_digit e[2*7];
    sp_digit x[2*7];
    sp_digit k[2*7];
    sp_digit r[2*7];
    sp_digit tmp[3 * 2*7];
    sp_point_384 point;
    sp_digit* s;
    sp_digit* kInv;
    int i;
} sp_ecc_sign_384_ctx;

int sp_ecc_sign_384_nb(sp_ecc_ctx_t* sp_ctx, const byte* hash, word32 hashLen, WC_RNG* rng, mp_int* priv,
                    mp_int* rm, mp_int* sm, mp_int* km, void* heap)
{
    int err = FP_WOULDBLOCK;
    sp_ecc_sign_384_ctx* ctx = (sp_ecc_sign_384_ctx*)sp_ctx->data;

    typedef char ctx_size_test[sizeof(sp_ecc_sign_384_ctx) >= sizeof(*sp_ctx) ? -1 : 1];
    (void)sizeof(ctx_size_test);

    (void)heap;

    switch (ctx->state) {
    case 0: /* INIT */
        ctx->s = ctx->e;
        ctx->kInv = ctx->k;
        if (hashLen > 48U) {
            hashLen = 48U;
        }

        sp_384_from_bin(ctx->e, 7, hash, (int)hashLen);

        ctx->i = SP_ECC_MAX_SIG_GEN;
        ctx->state = 1;
        break;
    case 1: /* GEN */
        sp_384_from_mp(ctx->x, 7, priv);
        /* New random point. */
        if (km == NULL || mp_iszero(km)) {
            err = sp_384_ecc_gen_k_7(rng, ctx->k);
        }
        else {
            sp_384_from_mp(ctx->k, 7, km);
            mp_zero(km);
        }
        XMEMSET(&ctx->mulmod_ctx, 0, sizeof(ctx->mulmod_ctx));
        ctx->state = 2;
        break; 
    case 2: /* MULMOD */
        err = sp_384_ecc_mulmod_7_nb((sp_ecc_ctx_t*)&ctx->mulmod_ctx, 
            &ctx->point, &p384_base, ctx->k, 1, 1, heap);
        if (err == MP_OKAY) {
            ctx->state = 3;
        }
        break;
    case 3: /* MODORDER */
    {
        int64_t c;
        /* r = point->x mod order */
        XMEMCPY(ctx->r, ctx->point.x, sizeof(sp_digit) * 7U);
        sp_384_norm_7(ctx->r);
        c = sp_384_cmp_7(ctx->r, p384_order);
        sp_384_cond_sub_7(ctx->r, ctx->r, p384_order, 0L - (sp_digit)(c >= 0));
        sp_384_norm_7(ctx->r);
        ctx->state = 4;
        break;
    }
    case 4: /* KMODORDER */
        /* Conv k to Montgomery form (mod order) */
        sp_384_mul_7(ctx->k, ctx->k, p384_norm_order);
        err = sp_384_mod_7(ctx->k, ctx->k, p384_order);
        if (err == MP_OKAY) {
            sp_384_norm_7(ctx->k);
            XMEMSET(&ctx->mont_inv_order_ctx, 0, sizeof(ctx->mont_inv_order_ctx));
            ctx->state = 5;
        }
        break;
    case 5: /* KINV */
        /* kInv = 1/k mod order */
        err = sp_384_mont_inv_order_7_nb((sp_ecc_ctx_t*)&ctx->mont_inv_order_ctx, ctx->kInv, ctx->k, ctx->tmp);
        if (err == MP_OKAY) {
            XMEMSET(&ctx->mont_inv_order_ctx, 0, sizeof(ctx->mont_inv_order_ctx));
            ctx->state = 6;
        }
        break;
    case 6: /* KINVNORM */
        sp_384_norm_7(ctx->kInv);
        ctx->state = 7;
        break;
    case 7: /* R */
        /* s = r * x + e */
        sp_384_mul_7(ctx->x, ctx->x, ctx->r);
        ctx->state = 8;
        break;
    case 8: /* S1 */
        err = sp_384_mod_7(ctx->x, ctx->x, p384_order);
        if (err == MP_OKAY)
            ctx->state = 9;
        break;
    case 9: /* S2 */
    {
        sp_digit carry;
        int64_t c;
        sp_384_norm_7(ctx->x);
        carry = sp_384_add_7(ctx->s, ctx->e, ctx->x);
        sp_384_cond_sub_7(ctx->s, ctx->s, p384_order, 0 - carry);
        sp_384_norm_7(ctx->s);
        c = sp_384_cmp_7(ctx->s, p384_order);
        sp_384_cond_sub_7(ctx->s, ctx->s, p384_order, 0L - (sp_digit)(c >= 0));
        sp_384_norm_7(ctx->s);

        /* s = s * k^-1 mod order */
        sp_384_mont_mul_order_7(ctx->s, ctx->s, ctx->kInv);
        sp_384_norm_7(ctx->s);

        /* Check that signature is usable. */
        if (sp_384_iszero_7(ctx->s) == 0) {
            ctx->state = 10;
            break;
        }

        /* not usable gen, try again */
        ctx->i--;
        if (ctx->i == 0) {
            err = RNG_FAILURE_E;
        }
        ctx->state = 1;
        break;
    }
    case 10: /* RES */
        err = sp_384_to_mp(ctx->r, rm);
        if (err == MP_OKAY) {
            err = sp_384_to_mp(ctx->s, sm);
        }
        break;
    }

    if (err == MP_OKAY && ctx->state != 10) {
        err = FP_WOULDBLOCK;
    }
    if (err != FP_WOULDBLOCK) {
        XMEMSET(ctx->e, 0, sizeof(sp_digit) * 2U * 7U);
        XMEMSET(ctx->x, 0, sizeof(sp_digit) * 2U * 7U);
        XMEMSET(ctx->k, 0, sizeof(sp_digit) * 2U * 7U);
        XMEMSET(ctx->r, 0, sizeof(sp_digit) * 2U * 7U);
        XMEMSET(ctx->tmp, 0, sizeof(sp_digit) * 3U * 2U * 7U);
    }

    return err;
}
#endif /* WOLFSSL_SP_NONBLOCK */

int sp_ecc_sign_384(const byte* hash, word32 hashLen, WC_RNG* rng, mp_int* priv,
                    mp_int* rm, mp_int* sm, mp_int* km, void* heap)
{
#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    sp_digit* d = NULL;
#else
    sp_digit ed[2*7];
    sp_digit xd[2*7];
    sp_digit kd[2*7];
    sp_digit rd[2*7];
    sp_digit td[3 * 2*7];
    sp_point_384 p;
#endif
    sp_digit* e = NULL;
    sp_digit* x = NULL;
    sp_digit* k = NULL;
    sp_digit* r = NULL;
    sp_digit* tmp = NULL;
    sp_point_384* point = NULL;
    sp_digit carry;
    sp_digit* s = NULL;
    sp_digit* kInv = NULL;
    int err = MP_OKAY;
    int64_t c;
    int i;

    (void)heap;

    err = sp_384_point_new_7(heap, p, point);
#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (err == MP_OKAY) {
        d = (sp_digit*)XMALLOC(sizeof(sp_digit) * 7 * 2 * 7, heap,
                                                              DYNAMIC_TYPE_ECC);
        if (d == NULL) {
            err = MEMORY_E;
        }
    }
#endif

    if (err == MP_OKAY) {
#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
        e = d + 0 * 7;
        x = d + 2 * 7;
        k = d + 4 * 7;
        r = d + 6 * 7;
        tmp = d + 8 * 7;
#else
        e = ed;
        x = xd;
        k = kd;
        r = rd;
        tmp = td;
#endif
        s = e;
        kInv = k;

        if (hashLen > 48U) {
            hashLen = 48U;
        }

        sp_384_from_bin(e, 7, hash, (int)hashLen);
    }

    for (i = SP_ECC_MAX_SIG_GEN; err == MP_OKAY && i > 0; i--) {
        sp_384_from_mp(x, 7, priv);

        /* New random point. */
        if (km == NULL || mp_iszero(km)) {
            err = sp_384_ecc_gen_k_7(rng, k);
        }
        else {
            sp_384_from_mp(k, 7, km);
            mp_zero(km);
        }
        if (err == MP_OKAY) {
                err = sp_384_ecc_mulmod_base_7(point, k, 1, 1, NULL);
        }

        if (err == MP_OKAY) {
            /* r = point->x mod order */
            XMEMCPY(r, point->x, sizeof(sp_digit) * 7U);
            sp_384_norm_7(r);
            c = sp_384_cmp_7(r, p384_order);
            sp_384_cond_sub_7(r, r, p384_order, 0L - (sp_digit)(c >= 0));
            sp_384_norm_7(r);

            /* Conv k to Montgomery form (mod order) */
                sp_384_mul_7(k, k, p384_norm_order);
            err = sp_384_mod_7(k, k, p384_order);
        }
        if (err == MP_OKAY) {
            sp_384_norm_7(k);
            /* kInv = 1/k mod order */
                sp_384_mont_inv_order_7(kInv, k, tmp);
            sp_384_norm_7(kInv);

            /* s = r * x + e */
                sp_384_mul_7(x, x, r);
            err = sp_384_mod_7(x, x, p384_order);
        }
        if (err == MP_OKAY) {
            sp_384_norm_7(x);
            carry = sp_384_add_7(s, e, x);
            sp_384_cond_sub_7(s, s, p384_order, 0 - carry);
            sp_384_norm_7(s);
            c = sp_384_cmp_7(s, p384_order);
            sp_384_cond_sub_7(s, s, p384_order, 0L - (sp_digit)(c >= 0));
            sp_384_norm_7(s);

            /* s = s * k^-1 mod order */
                sp_384_mont_mul_order_7(s, s, kInv);
            sp_384_norm_7(s);

            /* Check that signature is usable. */
            if (sp_384_iszero_7(s) == 0) {
                break;
            }
        }
    }

    if (i == 0) {
        err = RNG_FAILURE_E;
    }

    if (err == MP_OKAY) {
        err = sp_384_to_mp(r, rm);
    }
    if (err == MP_OKAY) {
        err = sp_384_to_mp(s, sm);
    }

#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (d != NULL) {
        XMEMSET(d, 0, sizeof(sp_digit) * 8 * 7);
        XFREE(d, heap, DYNAMIC_TYPE_ECC);
    }
#else
    XMEMSET(e, 0, sizeof(sp_digit) * 2U * 7U);
    XMEMSET(x, 0, sizeof(sp_digit) * 2U * 7U);
    XMEMSET(k, 0, sizeof(sp_digit) * 2U * 7U);
    XMEMSET(r, 0, sizeof(sp_digit) * 2U * 7U);
    XMEMSET(r, 0, sizeof(sp_digit) * 2U * 7U);
    XMEMSET(tmp, 0, sizeof(sp_digit) * 3U * 2U * 7U);
#endif
    sp_384_point_free_7(point, 1, heap);

    return err;
}
#endif /* HAVE_ECC_SIGN */

#ifdef HAVE_ECC_VERIFY
/* Verify the signature values with the hash and public key.
 *   e = Truncate(hash, 384)
 *   u1 = e/s mod order
 *   u2 = r/s mod order
 *   r == (u1.G + u2.Q)->x mod order
 * Optimization: Leave point in projective form.
 *   (x, y, 1) == (x' / z'*z', y' / z'*z'*z', z' / z')
 *   (r + n*order).z'.z' mod prime == (u1.G + u2.Q)->x'
 * The hash is truncated to the first 384 bits.
 *
 * hash     Hash to sign.
 * hashLen  Length of the hash data.
 * rng      Random number generator.
 * priv     Private part of key - scalar.
 * rm       First part of result as an mp_int.
 * sm       Sirst part of result as an mp_int.
 * heap     Heap to use for allocation.
 * returns RNG failures, MEMORY_E when memory allocation fails and
 * MP_OKAY on success.
 */
#ifdef WOLFSSL_SP_NONBLOCK
typedef struct sp_ecc_verify_384_ctx {
    int state;
    union {
        sp_384_ecc_mulmod_7_ctx mulmod_ctx;
        sp_384_mont_inv_order_7_ctx mont_inv_order_ctx;
        sp_384_proj_point_dbl_7_ctx dbl_ctx;
        sp_384_proj_point_add_7_ctx add_ctx;
    };
    sp_digit u1[2*7];
    sp_digit u2[2*7];
    sp_digit s[2*7];
    sp_digit tmp[2*7 * 5];
    sp_point_384 p1;
    sp_point_384 p2;
} sp_ecc_verify_384_ctx;

int sp_ecc_verify_384_nb(sp_ecc_ctx_t* sp_ctx, const byte* hash, word32 hashLen, mp_int* pX,
    mp_int* pY, mp_int* pZ, mp_int* r, mp_int* sm, int* res, void* heap)
{
    int err = FP_WOULDBLOCK;
    sp_ecc_verify_384_ctx* ctx = (sp_ecc_verify_384_ctx*)sp_ctx->data;

    typedef char ctx_size_test[sizeof(sp_ecc_verify_384_ctx) >= sizeof(*sp_ctx) ? -1 : 1];
    (void)sizeof(ctx_size_test);

    switch (ctx->state) {
    case 0: /* INIT */
        if (hashLen > 48U) {
            hashLen = 48U;
        }

        sp_384_from_bin(ctx->u1, 7, hash, (int)hashLen);
        sp_384_from_mp(ctx->u2, 7, r);
        sp_384_from_mp(ctx->s, 7, sm);
        sp_384_from_mp(ctx->p2.x, 7, pX);
        sp_384_from_mp(ctx->p2.y, 7, pY);
        sp_384_from_mp(ctx->p2.z, 7, pZ);
        ctx->state = 1;
        break;
    case 1: /* NORMS0 */
        sp_384_mul_7(ctx->s, ctx->s, p384_norm_order);
        err = sp_384_mod_7(ctx->s, ctx->s, p384_order);
        if (err == MP_OKAY)
            ctx->state = 2;
        break;
    case 2: /* NORMS1 */
        sp_384_norm_7(ctx->s);
        XMEMSET(&ctx->mont_inv_order_ctx, 0, sizeof(ctx->mont_inv_order_ctx));
        ctx->state = 3;
        break;
    case 3: /* NORMS2 */
        err = sp_384_mont_inv_order_7_nb((sp_ecc_ctx_t*)&ctx->mont_inv_order_ctx, ctx->s, ctx->s, ctx->tmp);
        if (err == MP_OKAY) {
            ctx->state = 4;
        }
        break;
    case 4: /* NORMS3 */
        sp_384_mont_mul_order_7(ctx->u1, ctx->u1, ctx->s);
        ctx->state = 5;
        break;
    case 5: /* NORMS4 */
        sp_384_mont_mul_order_7(ctx->u2, ctx->u2, ctx->s);
        XMEMSET(&ctx->mulmod_ctx, 0, sizeof(ctx->mulmod_ctx));
        ctx->state = 6;
        break;
    case 6: /* MULBASE */
        err = sp_384_ecc_mulmod_7_nb((sp_ecc_ctx_t*)&ctx->mulmod_ctx, &ctx->p1, &p384_base, ctx->u1, 0, 0, heap);
        if (err == MP_OKAY) {
            XMEMSET(&ctx->mulmod_ctx, 0, sizeof(ctx->mulmod_ctx));
            ctx->state = 7;
        }
        break;
    case 7: /* MULMOD */
        err = sp_384_ecc_mulmod_7_nb((sp_ecc_ctx_t*)&ctx->mulmod_ctx, &ctx->p2, &ctx->p2, ctx->u2, 0, 0, heap);
        if (err == MP_OKAY) {
            XMEMSET(&ctx->add_ctx, 0, sizeof(ctx->add_ctx));
            ctx->state = 8;
        }
        break;
    case 8: /* ADD */
        err = sp_384_proj_point_add_7_nb((sp_ecc_ctx_t*)&ctx->add_ctx, &ctx->p1, &ctx->p1, &ctx->p2, ctx->tmp);
        if (err == MP_OKAY)
            ctx->state = 9;
        break;
    case 9: /* DBLPREP */
        if (sp_384_iszero_7(ctx->p1.z)) {
            if (sp_384_iszero_7(ctx->p1.x) && sp_384_iszero_7(ctx->p1.y)) {
                XMEMSET(&ctx->dbl_ctx, 0, sizeof(ctx->dbl_ctx));
                ctx->state = 10;
                break;
            }
            else {
                /* Y ordinate is not used from here - don't set. */
                int i;
                for (i=0; i<7; i++) {
                    ctx->p1.x[i] = 0;
                }
                XMEMCPY(ctx->p1.z, p384_norm_mod, sizeof(p384_norm_mod));
            }
        }
        ctx->state = 11;
        break;
    case 10: /* DBL */
        err = sp_384_proj_point_dbl_7_nb((sp_ecc_ctx_t*)&ctx->dbl_ctx, &ctx->p1, 
            &ctx->p2, ctx->tmp);
        if (err == MP_OKAY) {
            ctx->state = 11;
        }
        break;
    case 11: /* MONT */
        /* (r + n*order).z'.z' mod prime == (u1.G + u2.Q)->x' */
        /* Reload r and convert to Montgomery form. */
        sp_384_from_mp(ctx->u2, 7, r);
        err = sp_384_mod_mul_norm_7(ctx->u2, ctx->u2, p384_mod);
        if (err == MP_OKAY)
            ctx->state = 12;
        break;
    case 12: /* SQR */
        /* u1 = r.z'.z' mod prime */
        sp_384_mont_sqr_7(ctx->p1.z, ctx->p1.z, p384_mod, p384_mp_mod);
        ctx->state = 13;
        break;
    case 13: /* MUL */
        sp_384_mont_mul_7(ctx->u1, ctx->u2, ctx->p1.z, p384_mod, p384_mp_mod);
        ctx->state = 14;
        break;
    case 14: /* RES */
        err = MP_OKAY; /* math okay, now check result */
        *res = (int)(sp_384_cmp_7(ctx->p1.x, ctx->u1) == 0);
        if (*res == 0) {
            sp_digit carry;
            int64_t c;

            /* Reload r and add order. */
            sp_384_from_mp(ctx->u2, 7, r);
            carry = sp_384_add_7(ctx->u2, ctx->u2, p384_order);
            /* Carry means result is greater than mod and is not valid. */
            if (carry == 0) {
                sp_384_norm_7(ctx->u2);

                /* Compare with mod and if greater or equal then not valid. */
                c = sp_384_cmp_7(ctx->u2, p384_mod);
                if (c < 0) {
                    /* Convert to Montogomery form */
                    err = sp_384_mod_mul_norm_7(ctx->u2, ctx->u2, p384_mod);
                    if (err == MP_OKAY) {
                        /* u1 = (r + 1*order).z'.z' mod prime */
                        sp_384_mont_mul_7(ctx->u1, ctx->u2, ctx->p1.z, p384_mod,
                                                                  p384_mp_mod);
                        *res = (int)(sp_384_cmp_7(ctx->p1.x, ctx->u1) == 0);
                    }
                }
            }
        }
        break;
    }

    if (err == MP_OKAY && ctx->state != 14) {
        err = FP_WOULDBLOCK;
    }

    return err;
}
#endif /* WOLFSSL_SP_NONBLOCK */

int sp_ecc_verify_384(const byte* hash, word32 hashLen, mp_int* pX,
    mp_int* pY, mp_int* pZ, mp_int* r, mp_int* sm, int* res, void* heap)
{
#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    sp_digit* d = NULL;
#else
    sp_digit u1d[2*7];
    sp_digit u2d[2*7];
    sp_digit sd[2*7];
    sp_digit tmpd[2*7 * 5];
    sp_point_384 p1d;
    sp_point_384 p2d;
#endif
    sp_digit* u1 = NULL;
    sp_digit* u2 = NULL;
    sp_digit* s = NULL;
    sp_digit* tmp = NULL;
    sp_point_384* p1;
    sp_point_384* p2 = NULL;
    sp_digit carry;
    int64_t c;
    int err;

    err = sp_384_point_new_7(heap, p1d, p1);
    if (err == MP_OKAY) {
        err = sp_384_point_new_7(heap, p2d, p2);
    }
#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (err == MP_OKAY) {
        d = (sp_digit*)XMALLOC(sizeof(sp_digit) * 16 * 7, heap,
                                                              DYNAMIC_TYPE_ECC);
        if (d == NULL) {
            err = MEMORY_E;
        }
    }
#endif

    if (err == MP_OKAY) {
#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
        u1  = d + 0 * 7;
        u2  = d + 2 * 7;
        s   = d + 4 * 7;
        tmp = d + 6 * 7;
#else
        u1 = u1d;
        u2 = u2d;
        s  = sd;
        tmp = tmpd;
#endif

        if (hashLen > 48U) {
            hashLen = 48U;
        }

        sp_384_from_bin(u1, 7, hash, (int)hashLen);
        sp_384_from_mp(u2, 7, r);
        sp_384_from_mp(s, 7, sm);
        sp_384_from_mp(p2->x, 7, pX);
        sp_384_from_mp(p2->y, 7, pY);
        sp_384_from_mp(p2->z, 7, pZ);

        {
            sp_384_mul_7(s, s, p384_norm_order);
        }
        err = sp_384_mod_7(s, s, p384_order);
    }
    if (err == MP_OKAY) {
        sp_384_norm_7(s);
        {
            sp_384_mont_inv_order_7(s, s, tmp);
            sp_384_mont_mul_order_7(u1, u1, s);
            sp_384_mont_mul_order_7(u2, u2, s);
        }

            err = sp_384_ecc_mulmod_base_7(p1, u1, 0, 0, heap);
    }
    if (err == MP_OKAY) {
            err = sp_384_ecc_mulmod_7(p2, p2, u2, 0, 0, heap);
    }

    if (err == MP_OKAY) {
        {
            sp_384_proj_point_add_7(p1, p1, p2, tmp);
            if (sp_384_iszero_7(p1->z)) {
                if (sp_384_iszero_7(p1->x) && sp_384_iszero_7(p1->y)) {
                    sp_384_proj_point_dbl_7(p1, p2, tmp);
                }
                else {
                    /* Y ordinate is not used from here - don't set. */
                    p1->x[0] = 0;
                    p1->x[1] = 0;
                    p1->x[2] = 0;
                    p1->x[3] = 0;
                    p1->x[4] = 0;
                    p1->x[5] = 0;
                    p1->x[6] = 0;
                    XMEMCPY(p1->z, p384_norm_mod, sizeof(p384_norm_mod));
                }
            }
        }

        /* (r + n*order).z'.z' mod prime == (u1.G + u2.Q)->x' */
        /* Reload r and convert to Montgomery form. */
        sp_384_from_mp(u2, 7, r);
        err = sp_384_mod_mul_norm_7(u2, u2, p384_mod);
    }

    if (err == MP_OKAY) {
        /* u1 = r.z'.z' mod prime */
        sp_384_mont_sqr_7(p1->z, p1->z, p384_mod, p384_mp_mod);
        sp_384_mont_mul_7(u1, u2, p1->z, p384_mod, p384_mp_mod);
        *res = (int)(sp_384_cmp_7(p1->x, u1) == 0);
        if (*res == 0) {
            /* Reload r and add order. */
            sp_384_from_mp(u2, 7, r);
            carry = sp_384_add_7(u2, u2, p384_order);
            /* Carry means result is greater than mod and is not valid. */
            if (carry == 0) {
                sp_384_norm_7(u2);

                /* Compare with mod and if greater or equal then not valid. */
                c = sp_384_cmp_7(u2, p384_mod);
                if (c < 0) {
                    /* Convert to Montogomery form */
                    err = sp_384_mod_mul_norm_7(u2, u2, p384_mod);
                    if (err == MP_OKAY) {
                        /* u1 = (r + 1*order).z'.z' mod prime */
                        sp_384_mont_mul_7(u1, u2, p1->z, p384_mod,
                                                                  p384_mp_mod);
                        *res = (int)(sp_384_cmp_7(p1->x, u1) == 0);
                    }
                }
            }
        }
    }

#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (d != NULL)
        XFREE(d, heap, DYNAMIC_TYPE_ECC);
#endif
    sp_384_point_free_7(p1, 0, heap);
    sp_384_point_free_7(p2, 0, heap);

    return err;
}
#endif /* HAVE_ECC_VERIFY */

#ifdef HAVE_ECC_CHECK_KEY
/* Check that the x and y oridinates are a valid point on the curve.
 *
 * point  EC point.
 * heap   Heap to use if dynamically allocating.
 * returns MEMORY_E if dynamic memory allocation fails, MP_VAL if the point is
 * not on the curve and MP_OKAY otherwise.
 */
static int sp_384_ecc_is_point_7(sp_point_384* point, void* heap)
{
#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    sp_digit* d = NULL;
#else
    sp_digit t1d[2*7];
    sp_digit t2d[2*7];
#endif
    sp_digit* t1;
    sp_digit* t2;
    int err = MP_OKAY;

#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    d = (sp_digit*)XMALLOC(sizeof(sp_digit) * 7 * 4, heap, DYNAMIC_TYPE_ECC);
    if (d == NULL) {
        err = MEMORY_E;
    }
#endif
    (void)heap;

    if (err == MP_OKAY) {
#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
        t1 = d + 0 * 7;
        t2 = d + 2 * 7;
#else
        t1 = t1d;
        t2 = t2d;
#endif

        sp_384_sqr_7(t1, point->y);
        (void)sp_384_mod_7(t1, t1, p384_mod);
        sp_384_sqr_7(t2, point->x);
        (void)sp_384_mod_7(t2, t2, p384_mod);
        sp_384_mul_7(t2, t2, point->x);
        (void)sp_384_mod_7(t2, t2, p384_mod);
        (void)sp_384_sub_7(t2, p384_mod, t2);
        sp_384_mont_add_7(t1, t1, t2, p384_mod);

        sp_384_mont_add_7(t1, t1, point->x, p384_mod);
        sp_384_mont_add_7(t1, t1, point->x, p384_mod);
        sp_384_mont_add_7(t1, t1, point->x, p384_mod);

        if (sp_384_cmp_7(t1, p384_b) != 0) {
            err = MP_VAL;
        }
    }

#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (d != NULL) {
        XFREE(d, heap, DYNAMIC_TYPE_ECC);
    }
#endif

    return err;
}

/* Check that the x and y oridinates are a valid point on the curve.
 *
 * pX  X ordinate of EC point.
 * pY  Y ordinate of EC point.
 * returns MEMORY_E if dynamic memory allocation fails, MP_VAL if the point is
 * not on the curve and MP_OKAY otherwise.
 */
int sp_ecc_is_point_384(mp_int* pX, mp_int* pY)
{
#if (!defined(WOLFSSL_SP_SMALL) && !defined(WOLFSSL_SMALL_STACK)) || defined(WOLFSSL_SP_NO_MALLOC)
    sp_point_384 pubd;
#endif
    sp_point_384* pub;
    byte one[1] = { 1 };
    int err;

    err = sp_384_point_new_7(NULL, pubd, pub);
    if (err == MP_OKAY) {
        sp_384_from_mp(pub->x, 7, pX);
        sp_384_from_mp(pub->y, 7, pY);
        sp_384_from_bin(pub->z, 7, one, (int)sizeof(one));

        err = sp_384_ecc_is_point_7(pub, NULL);
    }

    sp_384_point_free_7(pub, 0, NULL);

    return err;
}

/* Check that the private scalar generates the EC point (px, py), the point is
 * on the curve and the point has the correct order.
 *
 * pX     X ordinate of EC point.
 * pY     Y ordinate of EC point.
 * privm  Private scalar that generates EC point.
 * returns MEMORY_E if dynamic memory allocation fails, MP_VAL if the point is
 * not on the curve, ECC_INF_E if the point does not have the correct order,
 * ECC_PRIV_KEY_E when the private scalar doesn't generate the EC point and
 * MP_OKAY otherwise.
 */
int sp_ecc_check_key_384(mp_int* pX, mp_int* pY, mp_int* privm, void* heap)
{
#if (!defined(WOLFSSL_SP_SMALL) && !defined(WOLFSSL_SMALL_STACK)) || defined(WOLFSSL_SP_NO_MALLOC)
    sp_digit privd[7];
    sp_point_384 pubd;
    sp_point_384 pd;
#endif
    sp_digit* priv = NULL;
    sp_point_384* pub;
    sp_point_384* p = NULL;
    byte one[1] = { 1 };
    int err;

    err = sp_384_point_new_7(heap, pubd, pub);
    if (err == MP_OKAY) {
        err = sp_384_point_new_7(heap, pd, p);
    }
#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (err == MP_OKAY) {
        priv = (sp_digit*)XMALLOC(sizeof(sp_digit) * 7, heap,
                                                              DYNAMIC_TYPE_ECC);
        if (priv == NULL) {
            err = MEMORY_E;
        }
    }
#endif

    if (err == MP_OKAY) {
#if (!defined(WOLFSSL_SP_SMALL) && !defined(WOLFSSL_SMALL_STACK)) || defined(WOLFSSL_SP_NO_MALLOC)
        priv = privd;
#endif

        sp_384_from_mp(pub->x, 7, pX);
        sp_384_from_mp(pub->y, 7, pY);
        sp_384_from_bin(pub->z, 7, one, (int)sizeof(one));
        sp_384_from_mp(priv, 7, privm);

        /* Check point at infinitiy. */
        if ((sp_384_iszero_7(pub->x) != 0) &&
            (sp_384_iszero_7(pub->y) != 0)) {
            err = ECC_INF_E;
        }
    }

    if (err == MP_OKAY) {
        /* Check range of X and Y */
        if (sp_384_cmp_7(pub->x, p384_mod) >= 0 ||
            sp_384_cmp_7(pub->y, p384_mod) >= 0) {
            err = ECC_OUT_OF_RANGE_E;
        }
    }

    if (err == MP_OKAY) {
        /* Check point is on curve */
        err = sp_384_ecc_is_point_7(pub, heap);
    }

    if (err == MP_OKAY) {
        /* Point * order = infinity */
            err = sp_384_ecc_mulmod_7(p, pub, p384_order, 1, 1, heap);
    }
    if (err == MP_OKAY) {
        /* Check result is infinity */
        if ((sp_384_iszero_7(p->x) == 0) ||
            (sp_384_iszero_7(p->y) == 0)) {
            err = ECC_INF_E;
        }
    }

    if (err == MP_OKAY) {
        /* Base * private = point */
            err = sp_384_ecc_mulmod_base_7(p, priv, 1, 1, heap);
    }
    if (err == MP_OKAY) {
        /* Check result is public key */
        if (sp_384_cmp_7(p->x, pub->x) != 0 ||
            sp_384_cmp_7(p->y, pub->y) != 0) {
            err = ECC_PRIV_KEY_E;
        }
    }

#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (priv != NULL) {
        XFREE(priv, heap, DYNAMIC_TYPE_ECC);
    }
#endif
    sp_384_point_free_7(p, 0, heap);
    sp_384_point_free_7(pub, 0, heap);

    return err;
}
#endif
#ifdef WOLFSSL_PUBLIC_ECC_ADD_DBL
/* Add two projective EC points together.
 * (pX, pY, pZ) + (qX, qY, qZ) = (rX, rY, rZ)
 *
 * pX   First EC point's X ordinate.
 * pY   First EC point's Y ordinate.
 * pZ   First EC point's Z ordinate.
 * qX   Second EC point's X ordinate.
 * qY   Second EC point's Y ordinate.
 * qZ   Second EC point's Z ordinate.
 * rX   Resultant EC point's X ordinate.
 * rY   Resultant EC point's Y ordinate.
 * rZ   Resultant EC point's Z ordinate.
 * returns MEMORY_E if dynamic memory allocation fails and MP_OKAY otherwise.
 */
int sp_ecc_proj_add_point_384(mp_int* pX, mp_int* pY, mp_int* pZ,
                              mp_int* qX, mp_int* qY, mp_int* qZ,
                              mp_int* rX, mp_int* rY, mp_int* rZ)
{
#if (!defined(WOLFSSL_SP_SMALL) && !defined(WOLFSSL_SMALL_STACK)) || defined(WOLFSSL_SP_NO_MALLOC)
    sp_digit tmpd[2 * 7 * 5];
    sp_point_384 pd;
    sp_point_384 qd;
#endif
    sp_digit* tmp;
    sp_point_384* p;
    sp_point_384* q = NULL;
    int err;

    err = sp_384_point_new_7(NULL, pd, p);
    if (err == MP_OKAY) {
        err = sp_384_point_new_7(NULL, qd, q);
    }
#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (err == MP_OKAY) {
        tmp = (sp_digit*)XMALLOC(sizeof(sp_digit) * 2 * 7 * 5, NULL,
                                                              DYNAMIC_TYPE_ECC);
        if (tmp == NULL) {
            err = MEMORY_E;
        }
    }
#else
    tmp = tmpd;
#endif

    if (err == MP_OKAY) {
        sp_384_from_mp(p->x, 7, pX);
        sp_384_from_mp(p->y, 7, pY);
        sp_384_from_mp(p->z, 7, pZ);
        sp_384_from_mp(q->x, 7, qX);
        sp_384_from_mp(q->y, 7, qY);
        sp_384_from_mp(q->z, 7, qZ);

            sp_384_proj_point_add_7(p, p, q, tmp);
    }

    if (err == MP_OKAY) {
        err = sp_384_to_mp(p->x, rX);
    }
    if (err == MP_OKAY) {
        err = sp_384_to_mp(p->y, rY);
    }
    if (err == MP_OKAY) {
        err = sp_384_to_mp(p->z, rZ);
    }

#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (tmp != NULL) {
        XFREE(tmp, NULL, DYNAMIC_TYPE_ECC);
    }
#endif
    sp_384_point_free_7(q, 0, NULL);
    sp_384_point_free_7(p, 0, NULL);

    return err;
}

/* Double a projective EC point.
 * (pX, pY, pZ) + (pX, pY, pZ) = (rX, rY, rZ)
 *
 * pX   EC point's X ordinate.
 * pY   EC point's Y ordinate.
 * pZ   EC point's Z ordinate.
 * rX   Resultant EC point's X ordinate.
 * rY   Resultant EC point's Y ordinate.
 * rZ   Resultant EC point's Z ordinate.
 * returns MEMORY_E if dynamic memory allocation fails and MP_OKAY otherwise.
 */
int sp_ecc_proj_dbl_point_384(mp_int* pX, mp_int* pY, mp_int* pZ,
                              mp_int* rX, mp_int* rY, mp_int* rZ)
{
#if (!defined(WOLFSSL_SP_SMALL) && !defined(WOLFSSL_SMALL_STACK)) || defined(WOLFSSL_SP_NO_MALLOC)
    sp_digit tmpd[2 * 7 * 2];
    sp_point_384 pd;
#endif
    sp_digit* tmp;
    sp_point_384* p;
    int err;

    err = sp_384_point_new_7(NULL, pd, p);
#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (err == MP_OKAY) {
        tmp = (sp_digit*)XMALLOC(sizeof(sp_digit) * 2 * 7 * 2, NULL,
                                                              DYNAMIC_TYPE_ECC);
        if (tmp == NULL) {
            err = MEMORY_E;
        }
    }
#else
    tmp = tmpd;
#endif

    if (err == MP_OKAY) {
        sp_384_from_mp(p->x, 7, pX);
        sp_384_from_mp(p->y, 7, pY);
        sp_384_from_mp(p->z, 7, pZ);

            sp_384_proj_point_dbl_7(p, p, tmp);
    }

    if (err == MP_OKAY) {
        err = sp_384_to_mp(p->x, rX);
    }
    if (err == MP_OKAY) {
        err = sp_384_to_mp(p->y, rY);
    }
    if (err == MP_OKAY) {
        err = sp_384_to_mp(p->z, rZ);
    }

#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (tmp != NULL) {
        XFREE(tmp, NULL, DYNAMIC_TYPE_ECC);
    }
#endif
    sp_384_point_free_7(p, 0, NULL);

    return err;
}

/* Map a projective EC point to affine in place.
 * pZ will be one.
 *
 * pX   EC point's X ordinate.
 * pY   EC point's Y ordinate.
 * pZ   EC point's Z ordinate.
 * returns MEMORY_E if dynamic memory allocation fails and MP_OKAY otherwise.
 */
int sp_ecc_map_384(mp_int* pX, mp_int* pY, mp_int* pZ)
{
#if (!defined(WOLFSSL_SP_SMALL) && !defined(WOLFSSL_SMALL_STACK)) || defined(WOLFSSL_SP_NO_MALLOC)
    sp_digit tmpd[2 * 7 * 6];
    sp_point_384 pd;
#endif
    sp_digit* tmp;
    sp_point_384* p;
    int err;

    err = sp_384_point_new_7(NULL, pd, p);
#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (err == MP_OKAY) {
        tmp = (sp_digit*)XMALLOC(sizeof(sp_digit) * 2 * 7 * 6, NULL,
                                                              DYNAMIC_TYPE_ECC);
        if (tmp == NULL) {
            err = MEMORY_E;
        }
    }
#else
    tmp = tmpd;
#endif
    if (err == MP_OKAY) {
        sp_384_from_mp(p->x, 7, pX);
        sp_384_from_mp(p->y, 7, pY);
        sp_384_from_mp(p->z, 7, pZ);

        sp_384_map_7(p, p, tmp);
    }

    if (err == MP_OKAY) {
        err = sp_384_to_mp(p->x, pX);
    }
    if (err == MP_OKAY) {
        err = sp_384_to_mp(p->y, pY);
    }
    if (err == MP_OKAY) {
        err = sp_384_to_mp(p->z, pZ);
    }

#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (tmp != NULL) {
        XFREE(tmp, NULL, DYNAMIC_TYPE_ECC);
    }
#endif
    sp_384_point_free_7(p, 0, NULL);

    return err;
}
#endif /* WOLFSSL_PUBLIC_ECC_ADD_DBL */
#ifdef HAVE_COMP_KEY
/* Find the square root of a number mod the prime of the curve.
 *
 * y  The number to operate on and the result.
 * returns MEMORY_E if dynamic memory allocation fails and MP_OKAY otherwise.
 */
static int sp_384_mont_sqrt_7(sp_digit* y)
{
#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    sp_digit* d;
#else
    sp_digit t1d[2 * 7];
    sp_digit t2d[2 * 7];
    sp_digit t3d[2 * 7];
    sp_digit t4d[2 * 7];
    sp_digit t5d[2 * 7];
#endif
    sp_digit* t1;
    sp_digit* t2;
    sp_digit* t3;
    sp_digit* t4;
    sp_digit* t5;
    int err = MP_OKAY;

#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    d = (sp_digit*)XMALLOC(sizeof(sp_digit) * 5 * 2 * 7, NULL, DYNAMIC_TYPE_ECC);
    if (d == NULL) {
        err = MEMORY_E;
    }
#endif

    if (err == MP_OKAY) {
#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
        t1 = d + 0 * 7;
        t2 = d + 2 * 7;
        t3 = d + 4 * 7;
        t4 = d + 6 * 7;
        t5 = d + 8 * 7;
#else
        t1 = t1d;
        t2 = t2d;
        t3 = t3d;
        t4 = t4d;
        t5 = t5d;
#endif

        {
            /* t2 = y ^ 0x2 */
            sp_384_mont_sqr_7(t2, y, p384_mod, p384_mp_mod);
            /* t1 = y ^ 0x3 */
            sp_384_mont_mul_7(t1, t2, y, p384_mod, p384_mp_mod);
            /* t5 = y ^ 0xc */
            sp_384_mont_sqr_n_7(t5, t1, 2, p384_mod, p384_mp_mod);
            /* t1 = y ^ 0xf */
            sp_384_mont_mul_7(t1, t1, t5, p384_mod, p384_mp_mod);
            /* t2 = y ^ 0x1e */
            sp_384_mont_sqr_7(t2, t1, p384_mod, p384_mp_mod);
            /* t3 = y ^ 0x1f */
            sp_384_mont_mul_7(t3, t2, y, p384_mod, p384_mp_mod);
            /* t2 = y ^ 0x3e0 */
            sp_384_mont_sqr_n_7(t2, t3, 5, p384_mod, p384_mp_mod);
            /* t1 = y ^ 0x3ff */
            sp_384_mont_mul_7(t1, t3, t2, p384_mod, p384_mp_mod);
            /* t2 = y ^ 0x7fe0 */
            sp_384_mont_sqr_n_7(t2, t1, 5, p384_mod, p384_mp_mod);
            /* t3 = y ^ 0x7fff */
            sp_384_mont_mul_7(t3, t3, t2, p384_mod, p384_mp_mod);
            /* t2 = y ^ 0x3fff800 */
            sp_384_mont_sqr_n_7(t2, t3, 15, p384_mod, p384_mp_mod);
            /* t4 = y ^ 0x3ffffff */
            sp_384_mont_mul_7(t4, t3, t2, p384_mod, p384_mp_mod);
            /* t2 = y ^ 0xffffffc000000 */
            sp_384_mont_sqr_n_7(t2, t4, 30, p384_mod, p384_mp_mod);
            /* t1 = y ^ 0xfffffffffffff */
            sp_384_mont_mul_7(t1, t4, t2, p384_mod, p384_mp_mod);
            /* t2 = y ^ 0xfffffffffffffff000000000000000 */
            sp_384_mont_sqr_n_7(t2, t1, 60, p384_mod, p384_mp_mod);
            /* t1 = y ^ 0xffffffffffffffffffffffffffffff */
            sp_384_mont_mul_7(t1, t1, t2, p384_mod, p384_mp_mod);
            /* t2 = y ^ 0xffffffffffffffffffffffffffffff000000000000000000000000000000 */
            sp_384_mont_sqr_n_7(t2, t1, 120, p384_mod, p384_mp_mod);
            /* t1 = y ^ 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff */
            sp_384_mont_mul_7(t1, t1, t2, p384_mod, p384_mp_mod);
            /* t2 = y ^ 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8000 */
            sp_384_mont_sqr_n_7(t2, t1, 15, p384_mod, p384_mp_mod);
            /* t1 = y ^ 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff */
            sp_384_mont_mul_7(t1, t3, t2, p384_mod, p384_mp_mod);
            /* t2 = y ^ 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff80000000 */
            sp_384_mont_sqr_n_7(t2, t1, 31, p384_mod, p384_mp_mod);
            /* t1 = y ^ 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbfffffff */
            sp_384_mont_mul_7(t1, t4, t2, p384_mod, p384_mp_mod);
            /* t2 = y ^ 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbfffffff0 */
            sp_384_mont_sqr_n_7(t2, t1, 4, p384_mod, p384_mp_mod);
            /* t1 = y ^ 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbfffffffc */
            sp_384_mont_mul_7(t1, t5, t2, p384_mod, p384_mp_mod);
            /* t2 = y ^ 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff0000000000000000 */
            sp_384_mont_sqr_n_7(t2, t1, 62, p384_mod, p384_mp_mod);
            /* t1 = y ^ 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff0000000000000001 */
            sp_384_mont_mul_7(t1, y, t2, p384_mod, p384_mp_mod);
            /* t2 = y ^ 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbfffffffc00000000000000040000000 */
            sp_384_mont_sqr_n_7(y, t1, 30, p384_mod, p384_mp_mod);
        }
    }

#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (d != NULL) {
        XFREE(d, NULL, DYNAMIC_TYPE_ECC);
    }
#endif

    return err;
}


/* Uncompress the point given the X ordinate.
 *
 * xm    X ordinate.
 * odd   Whether the Y ordinate is odd.
 * ym    Calculated Y ordinate.
 * returns MEMORY_E if dynamic memory allocation fails and MP_OKAY otherwise.
 */
int sp_ecc_uncompress_384(mp_int* xm, int odd, mp_int* ym)
{
#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    sp_digit* d;
#else
    sp_digit xd[2 * 7];
    sp_digit yd[2 * 7];
#endif
    sp_digit* x = NULL;
    sp_digit* y = NULL;
    int err = MP_OKAY;

#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    d = (sp_digit*)XMALLOC(sizeof(sp_digit) * 4 * 7, NULL, DYNAMIC_TYPE_ECC);
    if (d == NULL) {
        err = MEMORY_E;
    }
#endif

    if (err == MP_OKAY) {
#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
        x = d + 0 * 7;
        y = d + 2 * 7;
#else
        x = xd;
        y = yd;
#endif

        sp_384_from_mp(x, 7, xm);
        err = sp_384_mod_mul_norm_7(x, x, p384_mod);
    }
    if (err == MP_OKAY) {
        /* y = x^3 */
        {
            sp_384_mont_sqr_7(y, x, p384_mod, p384_mp_mod);
            sp_384_mont_mul_7(y, y, x, p384_mod, p384_mp_mod);
        }
        /* y = x^3 - 3x */
        sp_384_mont_sub_7(y, y, x, p384_mod);
        sp_384_mont_sub_7(y, y, x, p384_mod);
        sp_384_mont_sub_7(y, y, x, p384_mod);
        /* y = x^3 - 3x + b */
        err = sp_384_mod_mul_norm_7(x, p384_b, p384_mod);
    }
    if (err == MP_OKAY) {
        sp_384_mont_add_7(y, y, x, p384_mod);
        /* y = sqrt(x^3 - 3x + b) */
        err = sp_384_mont_sqrt_7(y);
    }
    if (err == MP_OKAY) {
        XMEMSET(y + 7, 0, 7U * sizeof(sp_digit));
        sp_384_mont_reduce_7(y, p384_mod, p384_mp_mod);
        if ((((word32)y[0] ^ (word32)odd) & 1U) != 0U) {
            sp_384_mont_sub_7(y, p384_mod, y, p384_mod);
        }

        err = sp_384_to_mp(y, ym);
    }

#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (d != NULL) {
        XFREE(d, NULL, DYNAMIC_TYPE_ECC);
    }
#endif

    return err;
}
#endif
#endif /* WOLFSSL_SP_384 */
#endif /* WOLFSSL_HAVE_SP_ECC */
#endif /* SP_WORD_SIZE == 64 */
#endif /* !WOLFSSL_SP_ASM */
#endif /* WOLFSSL_HAVE_SP_RSA || WOLFSSL_HAVE_SP_DH || WOLFSSL_HAVE_SP_ECC */
