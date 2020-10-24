/* sp.c
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
#ifndef WOLFSSL_SP_SMALL
#define WOLFSSL_SP_SMALL
#endif
#endif

#include <wolfssl/wolfcrypt/sp.h>

#ifdef __IAR_SYSTEMS_ICC__
#define __asm__        asm
#define __volatile__   volatile
#endif /* __IAR_SYSTEMS_ICC__ */
#ifdef __KEIL__
#define __asm__        __asm
#define __volatile__   volatile
#endif

#ifdef WOLFSSL_SP_ARM_CORTEX_M_ASM
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
        if (s >= 24U) {
            r[j] &= 0xffffffff;
            s = 32U - s;
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
#if DIGIT_BIT == 32
    int j;

    XMEMCPY(r, a->dp, sizeof(sp_digit) * a->used);

    for (j = a->used; j < size; j++) {
        r[j] = 0;
    }
#elif DIGIT_BIT > 32
    int i, j = 0;
    word32 s = 0;

    r[0] = 0;
    for (i = 0; i < a->used && j < size; i++) {
        r[j] |= ((sp_digit)a->dp[i] << s);
        r[j] &= 0xffffffff;
        s = 32U - s;
        if (j + 1 >= size) {
            break;
        }
        /* lint allow cast of mismatch word32 and mp_digit */
        r[++j] = (sp_digit)(a->dp[i] >> s); /*lint !e9033*/
        while ((s + 32U) <= (word32)DIGIT_BIT) {
            s += 32U;
            r[j] &= 0xffffffff;
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
        if (s + DIGIT_BIT >= 32) {
            r[j] &= 0xffffffff;
            if (j + 1 >= size) {
                break;
            }
            s = 32 - s;
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

    j = 2048 / 8 - 1;
    a[j] = 0;
    for (i=0; i<64 && j>=0; i++) {
        b = 0;
        /* lint allow cast of mismatch sp_digit and int */
        a[j--] |= (byte)(r[i] << s); /*lint !e9033*/
        b += 8 - s;
        if (j < 0) {
            break;
        }
        while (b < 32) {
            a[j--] = (byte)(r[i] >> b);
            b += 8;
            if (j < 0) {
                break;
            }
        }
        s = 8 - (b - 32);
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
SP_NOINLINE static void sp_2048_mul_8(sp_digit* r, const sp_digit* a,
        const sp_digit* b)
{
    sp_digit tmp[8];

    __asm__ __volatile__ (
        /* A[0] * B[0] */
        "ldr	r6, [%[a], #0]\n\t"
        "ldr	r8, [%[b], #0]\n\t"
        "umull	r3, r4, r6, r8\n\t"
        "mov	r5, #0\n\t"
        "str	r3, [%[tmp], #0]\n\t"
        "mov	r3, #0\n\t"
        /* A[0] * B[1] */
        "ldr	r8, [%[b], #4]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r4, r4, r6\n\t"
        "adc	r5, r5, r8\n\t"
        /* A[1] * B[0] */
        "ldr	r6, [%[a], #4]\n\t"
        "ldr	r8, [%[b], #0]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r4, r4, r6\n\t"
        "adcs 	r5, r5, r8\n\t"
        "adc	r3, r3, #0\n\t"
        "str	r4, [%[tmp], #4]\n\t"
        "mov	r4, #0\n\t"
        /* A[0] * B[2] */
        "ldr	r6, [%[a], #0]\n\t"
        "ldr	r8, [%[b], #8]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r5, r5, r6\n\t"
        "adcs 	r3, r3, r8\n\t"
        "adc	r4, r4, #0\n\t"
        /* A[1] * B[1] */
        "ldr	r6, [%[a], #4]\n\t"
        "ldr	r8, [%[b], #4]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r5, r5, r6\n\t"
        "adcs 	r3, r3, r8\n\t"
        "adc	r4, r4, #0\n\t"
        /* A[2] * B[0] */
        "ldr	r6, [%[a], #8]\n\t"
        "ldr	r8, [%[b], #0]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r5, r5, r6\n\t"
        "adcs 	r3, r3, r8\n\t"
        "adc	r4, r4, #0\n\t"
        "str	r5, [%[tmp], #8]\n\t"
        "mov	r5, #0\n\t"
        /* A[0] * B[3] */
        "ldr	r6, [%[a], #0]\n\t"
        "ldr	r8, [%[b], #12]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r3, r3, r6\n\t"
        "adcs 	r4, r4, r8\n\t"
        "adc	r5, r5, #0\n\t"
        /* A[1] * B[2] */
        "ldr	r6, [%[a], #4]\n\t"
        "ldr	r8, [%[b], #8]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r3, r3, r6\n\t"
        "adcs 	r4, r4, r8\n\t"
        "adc	r5, r5, #0\n\t"
        /* A[2] * B[1] */
        "ldr	r6, [%[a], #8]\n\t"
        "ldr	r8, [%[b], #4]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r3, r3, r6\n\t"
        "adcs 	r4, r4, r8\n\t"
        "adc	r5, r5, #0\n\t"
        /* A[3] * B[0] */
        "ldr	r6, [%[a], #12]\n\t"
        "ldr	r8, [%[b], #0]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r3, r3, r6\n\t"
        "adcs 	r4, r4, r8\n\t"
        "adc	r5, r5, #0\n\t"
        "str	r3, [%[tmp], #12]\n\t"
        "mov	r3, #0\n\t"
        /* A[0] * B[4] */
        "ldr	r6, [%[a], #0]\n\t"
        "ldr	r8, [%[b], #16]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r4, r4, r6\n\t"
        "adcs 	r5, r5, r8\n\t"
        "adc	r3, r3, #0\n\t"
        /* A[1] * B[3] */
        "ldr	r6, [%[a], #4]\n\t"
        "ldr	r8, [%[b], #12]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r4, r4, r6\n\t"
        "adcs 	r5, r5, r8\n\t"
        "adc	r3, r3, #0\n\t"
        /* A[2] * B[2] */
        "ldr	r6, [%[a], #8]\n\t"
        "ldr	r8, [%[b], #8]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r4, r4, r6\n\t"
        "adcs 	r5, r5, r8\n\t"
        "adc	r3, r3, #0\n\t"
        /* A[3] * B[1] */
        "ldr	r6, [%[a], #12]\n\t"
        "ldr	r8, [%[b], #4]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r4, r4, r6\n\t"
        "adcs 	r5, r5, r8\n\t"
        "adc	r3, r3, #0\n\t"
        /* A[4] * B[0] */
        "ldr	r6, [%[a], #16]\n\t"
        "ldr	r8, [%[b], #0]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r4, r4, r6\n\t"
        "adcs 	r5, r5, r8\n\t"
        "adc	r3, r3, #0\n\t"
        "str	r4, [%[tmp], #16]\n\t"
        "mov	r4, #0\n\t"
        /* A[0] * B[5] */
        "ldr	r6, [%[a], #0]\n\t"
        "ldr	r8, [%[b], #20]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r5, r5, r6\n\t"
        "adcs 	r3, r3, r8\n\t"
        "adc	r4, r4, #0\n\t"
        /* A[1] * B[4] */
        "ldr	r6, [%[a], #4]\n\t"
        "ldr	r8, [%[b], #16]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r5, r5, r6\n\t"
        "adcs 	r3, r3, r8\n\t"
        "adc	r4, r4, #0\n\t"
        /* A[2] * B[3] */
        "ldr	r6, [%[a], #8]\n\t"
        "ldr	r8, [%[b], #12]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r5, r5, r6\n\t"
        "adcs 	r3, r3, r8\n\t"
        "adc	r4, r4, #0\n\t"
        /* A[3] * B[2] */
        "ldr	r6, [%[a], #12]\n\t"
        "ldr	r8, [%[b], #8]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r5, r5, r6\n\t"
        "adcs 	r3, r3, r8\n\t"
        "adc	r4, r4, #0\n\t"
        /* A[4] * B[1] */
        "ldr	r6, [%[a], #16]\n\t"
        "ldr	r8, [%[b], #4]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r5, r5, r6\n\t"
        "adcs 	r3, r3, r8\n\t"
        "adc	r4, r4, #0\n\t"
        /* A[5] * B[0] */
        "ldr	r6, [%[a], #20]\n\t"
        "ldr	r8, [%[b], #0]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r5, r5, r6\n\t"
        "adcs 	r3, r3, r8\n\t"
        "adc	r4, r4, #0\n\t"
        "str	r5, [%[tmp], #20]\n\t"
        "mov	r5, #0\n\t"
        /* A[0] * B[6] */
        "ldr	r6, [%[a], #0]\n\t"
        "ldr	r8, [%[b], #24]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r3, r3, r6\n\t"
        "adcs 	r4, r4, r8\n\t"
        "adc	r5, r5, #0\n\t"
        /* A[1] * B[5] */
        "ldr	r6, [%[a], #4]\n\t"
        "ldr	r8, [%[b], #20]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r3, r3, r6\n\t"
        "adcs 	r4, r4, r8\n\t"
        "adc	r5, r5, #0\n\t"
        /* A[2] * B[4] */
        "ldr	r6, [%[a], #8]\n\t"
        "ldr	r8, [%[b], #16]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r3, r3, r6\n\t"
        "adcs 	r4, r4, r8\n\t"
        "adc	r5, r5, #0\n\t"
        /* A[3] * B[3] */
        "ldr	r6, [%[a], #12]\n\t"
        "ldr	r8, [%[b], #12]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r3, r3, r6\n\t"
        "adcs 	r4, r4, r8\n\t"
        "adc	r5, r5, #0\n\t"
        /* A[4] * B[2] */
        "ldr	r6, [%[a], #16]\n\t"
        "ldr	r8, [%[b], #8]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r3, r3, r6\n\t"
        "adcs 	r4, r4, r8\n\t"
        "adc	r5, r5, #0\n\t"
        /* A[5] * B[1] */
        "ldr	r6, [%[a], #20]\n\t"
        "ldr	r8, [%[b], #4]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r3, r3, r6\n\t"
        "adcs 	r4, r4, r8\n\t"
        "adc	r5, r5, #0\n\t"
        /* A[6] * B[0] */
        "ldr	r6, [%[a], #24]\n\t"
        "ldr	r8, [%[b], #0]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r3, r3, r6\n\t"
        "adcs 	r4, r4, r8\n\t"
        "adc	r5, r5, #0\n\t"
        "str	r3, [%[tmp], #24]\n\t"
        "mov	r3, #0\n\t"
        /* A[0] * B[7] */
        "ldr	r6, [%[a], #0]\n\t"
        "ldr	r8, [%[b], #28]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r4, r4, r6\n\t"
        "adcs 	r5, r5, r8\n\t"
        "adc	r3, r3, #0\n\t"
        /* A[1] * B[6] */
        "ldr	r6, [%[a], #4]\n\t"
        "ldr	r8, [%[b], #24]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r4, r4, r6\n\t"
        "adcs 	r5, r5, r8\n\t"
        "adc	r3, r3, #0\n\t"
        /* A[2] * B[5] */
        "ldr	r6, [%[a], #8]\n\t"
        "ldr	r8, [%[b], #20]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r4, r4, r6\n\t"
        "adcs 	r5, r5, r8\n\t"
        "adc	r3, r3, #0\n\t"
        /* A[3] * B[4] */
        "ldr	r6, [%[a], #12]\n\t"
        "ldr	r8, [%[b], #16]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r4, r4, r6\n\t"
        "adcs 	r5, r5, r8\n\t"
        "adc	r3, r3, #0\n\t"
        /* A[4] * B[3] */
        "ldr	r6, [%[a], #16]\n\t"
        "ldr	r8, [%[b], #12]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r4, r4, r6\n\t"
        "adcs 	r5, r5, r8\n\t"
        "adc	r3, r3, #0\n\t"
        /* A[5] * B[2] */
        "ldr	r6, [%[a], #20]\n\t"
        "ldr	r8, [%[b], #8]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r4, r4, r6\n\t"
        "adcs 	r5, r5, r8\n\t"
        "adc	r3, r3, #0\n\t"
        /* A[6] * B[1] */
        "ldr	r6, [%[a], #24]\n\t"
        "ldr	r8, [%[b], #4]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r4, r4, r6\n\t"
        "adcs 	r5, r5, r8\n\t"
        "adc	r3, r3, #0\n\t"
        /* A[7] * B[0] */
        "ldr	r6, [%[a], #28]\n\t"
        "ldr	r8, [%[b], #0]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r4, r4, r6\n\t"
        "adcs 	r5, r5, r8\n\t"
        "adc	r3, r3, #0\n\t"
        "str	r4, [%[tmp], #28]\n\t"
        "mov	r4, #0\n\t"
        /* A[1] * B[7] */
        "ldr	r6, [%[a], #4]\n\t"
        "ldr	r8, [%[b], #28]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r5, r5, r6\n\t"
        "adcs 	r3, r3, r8\n\t"
        "adc	r4, r4, #0\n\t"
        /* A[2] * B[6] */
        "ldr	r6, [%[a], #8]\n\t"
        "ldr	r8, [%[b], #24]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r5, r5, r6\n\t"
        "adcs 	r3, r3, r8\n\t"
        "adc	r4, r4, #0\n\t"
        /* A[3] * B[5] */
        "ldr	r6, [%[a], #12]\n\t"
        "ldr	r8, [%[b], #20]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r5, r5, r6\n\t"
        "adcs 	r3, r3, r8\n\t"
        "adc	r4, r4, #0\n\t"
        /* A[4] * B[4] */
        "ldr	r6, [%[a], #16]\n\t"
        "ldr	r8, [%[b], #16]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r5, r5, r6\n\t"
        "adcs 	r3, r3, r8\n\t"
        "adc	r4, r4, #0\n\t"
        /* A[5] * B[3] */
        "ldr	r6, [%[a], #20]\n\t"
        "ldr	r8, [%[b], #12]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r5, r5, r6\n\t"
        "adcs 	r3, r3, r8\n\t"
        "adc	r4, r4, #0\n\t"
        /* A[6] * B[2] */
        "ldr	r6, [%[a], #24]\n\t"
        "ldr	r8, [%[b], #8]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r5, r5, r6\n\t"
        "adcs 	r3, r3, r8\n\t"
        "adc	r4, r4, #0\n\t"
        /* A[7] * B[1] */
        "ldr	r6, [%[a], #28]\n\t"
        "ldr	r8, [%[b], #4]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r5, r5, r6\n\t"
        "adcs 	r3, r3, r8\n\t"
        "adc	r4, r4, #0\n\t"
        "str	r5, [%[r], #32]\n\t"
        "mov	r5, #0\n\t"
        /* A[2] * B[7] */
        "ldr	r6, [%[a], #8]\n\t"
        "ldr	r8, [%[b], #28]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r3, r3, r6\n\t"
        "adcs 	r4, r4, r8\n\t"
        "adc	r5, r5, #0\n\t"
        /* A[3] * B[6] */
        "ldr	r6, [%[a], #12]\n\t"
        "ldr	r8, [%[b], #24]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r3, r3, r6\n\t"
        "adcs 	r4, r4, r8\n\t"
        "adc	r5, r5, #0\n\t"
        /* A[4] * B[5] */
        "ldr	r6, [%[a], #16]\n\t"
        "ldr	r8, [%[b], #20]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r3, r3, r6\n\t"
        "adcs 	r4, r4, r8\n\t"
        "adc	r5, r5, #0\n\t"
        /* A[5] * B[4] */
        "ldr	r6, [%[a], #20]\n\t"
        "ldr	r8, [%[b], #16]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r3, r3, r6\n\t"
        "adcs 	r4, r4, r8\n\t"
        "adc	r5, r5, #0\n\t"
        /* A[6] * B[3] */
        "ldr	r6, [%[a], #24]\n\t"
        "ldr	r8, [%[b], #12]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r3, r3, r6\n\t"
        "adcs 	r4, r4, r8\n\t"
        "adc	r5, r5, #0\n\t"
        /* A[7] * B[2] */
        "ldr	r6, [%[a], #28]\n\t"
        "ldr	r8, [%[b], #8]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r3, r3, r6\n\t"
        "adcs 	r4, r4, r8\n\t"
        "adc	r5, r5, #0\n\t"
        "str	r3, [%[r], #36]\n\t"
        "mov	r3, #0\n\t"
        /* A[3] * B[7] */
        "ldr	r6, [%[a], #12]\n\t"
        "ldr	r8, [%[b], #28]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r4, r4, r6\n\t"
        "adcs 	r5, r5, r8\n\t"
        "adc	r3, r3, #0\n\t"
        /* A[4] * B[6] */
        "ldr	r6, [%[a], #16]\n\t"
        "ldr	r8, [%[b], #24]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r4, r4, r6\n\t"
        "adcs 	r5, r5, r8\n\t"
        "adc	r3, r3, #0\n\t"
        /* A[5] * B[5] */
        "ldr	r6, [%[a], #20]\n\t"
        "ldr	r8, [%[b], #20]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r4, r4, r6\n\t"
        "adcs 	r5, r5, r8\n\t"
        "adc	r3, r3, #0\n\t"
        /* A[6] * B[4] */
        "ldr	r6, [%[a], #24]\n\t"
        "ldr	r8, [%[b], #16]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r4, r4, r6\n\t"
        "adcs 	r5, r5, r8\n\t"
        "adc	r3, r3, #0\n\t"
        /* A[7] * B[3] */
        "ldr	r6, [%[a], #28]\n\t"
        "ldr	r8, [%[b], #12]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r4, r4, r6\n\t"
        "adcs 	r5, r5, r8\n\t"
        "adc	r3, r3, #0\n\t"
        "str	r4, [%[r], #40]\n\t"
        "mov	r4, #0\n\t"
        /* A[4] * B[7] */
        "ldr	r6, [%[a], #16]\n\t"
        "ldr	r8, [%[b], #28]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r5, r5, r6\n\t"
        "adcs 	r3, r3, r8\n\t"
        "adc	r4, r4, #0\n\t"
        /* A[5] * B[6] */
        "ldr	r6, [%[a], #20]\n\t"
        "ldr	r8, [%[b], #24]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r5, r5, r6\n\t"
        "adcs 	r3, r3, r8\n\t"
        "adc	r4, r4, #0\n\t"
        /* A[6] * B[5] */
        "ldr	r6, [%[a], #24]\n\t"
        "ldr	r8, [%[b], #20]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r5, r5, r6\n\t"
        "adcs 	r3, r3, r8\n\t"
        "adc	r4, r4, #0\n\t"
        /* A[7] * B[4] */
        "ldr	r6, [%[a], #28]\n\t"
        "ldr	r8, [%[b], #16]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r5, r5, r6\n\t"
        "adcs 	r3, r3, r8\n\t"
        "adc	r4, r4, #0\n\t"
        "str	r5, [%[r], #44]\n\t"
        "mov	r5, #0\n\t"
        /* A[5] * B[7] */
        "ldr	r6, [%[a], #20]\n\t"
        "ldr	r8, [%[b], #28]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r3, r3, r6\n\t"
        "adcs 	r4, r4, r8\n\t"
        "adc	r5, r5, #0\n\t"
        /* A[6] * B[6] */
        "ldr	r6, [%[a], #24]\n\t"
        "ldr	r8, [%[b], #24]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r3, r3, r6\n\t"
        "adcs 	r4, r4, r8\n\t"
        "adc	r5, r5, #0\n\t"
        /* A[7] * B[5] */
        "ldr	r6, [%[a], #28]\n\t"
        "ldr	r8, [%[b], #20]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r3, r3, r6\n\t"
        "adcs 	r4, r4, r8\n\t"
        "adc	r5, r5, #0\n\t"
        "str	r3, [%[r], #48]\n\t"
        "mov	r3, #0\n\t"
        /* A[6] * B[7] */
        "ldr	r6, [%[a], #24]\n\t"
        "ldr	r8, [%[b], #28]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r4, r4, r6\n\t"
        "adcs 	r5, r5, r8\n\t"
        "adc	r3, r3, #0\n\t"
        /* A[7] * B[6] */
        "ldr	r6, [%[a], #28]\n\t"
        "ldr	r8, [%[b], #24]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r4, r4, r6\n\t"
        "adcs 	r5, r5, r8\n\t"
        "adc	r3, r3, #0\n\t"
        "str	r4, [%[r], #52]\n\t"
        "mov	r4, #0\n\t"
        /* A[7] * B[7] */
        "ldr	r6, [%[a], #28]\n\t"
        "ldr	r8, [%[b], #28]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r5, r5, r6\n\t"
        "adc	r3, r3, r8\n\t"
        "str	r5, [%[r], #56]\n\t"
        "str	r3, [%[r], #60]\n\t"
        /* Transfer tmp to r */
        "ldr	r3, [%[tmp], #0]\n\t"
        "ldr	r4, [%[tmp], #4]\n\t"
        "ldr	r5, [%[tmp], #8]\n\t"
        "ldr	r6, [%[tmp], #12]\n\t"
        "str	r3, [%[r], #0]\n\t"
        "str	r4, [%[r], #4]\n\t"
        "str	r5, [%[r], #8]\n\t"
        "str	r6, [%[r], #12]\n\t"
        "ldr	r3, [%[tmp], #16]\n\t"
        "ldr	r4, [%[tmp], #20]\n\t"
        "ldr	r5, [%[tmp], #24]\n\t"
        "ldr	r6, [%[tmp], #28]\n\t"
        "str	r3, [%[r], #16]\n\t"
        "str	r4, [%[r], #20]\n\t"
        "str	r5, [%[r], #24]\n\t"
        "str	r6, [%[r], #28]\n\t"
        :
        : [r] "r" (r), [a] "r" (a), [b] "r" (b), [tmp] "r" (tmp)
        : "memory", "r3", "r4", "r5", "r6", "r8"
    );
}

/* Square a and put result in r. (r = a * a)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 */
SP_NOINLINE static void sp_2048_sqr_8(sp_digit* r, const sp_digit* a)
{
    sp_digit tmp[8];
    __asm__ __volatile__ (
        /* A[0] * A[0] */
        "ldr	r6, [%[a], #0]\n\t"
        "umull	r3, r4, r6, r6\n\t"
        "mov	r5, #0\n\t"
        "str	r3, [%[tmp], #0]\n\t"
        "mov	r3, #0\n\t"
        /* A[0] * A[1] */
        "ldr	r8, [%[a], #4]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r4, r4, r6\n\t"
        "adc	r5, r5, r8\n\t"
        "adds	r4, r4, r6\n\t"
        "adcs 	r5, r5, r8\n\t"
        "adc	r3, r3, #0\n\t"
        "str	r4, [%[tmp], #4]\n\t"
        "mov	r4, #0\n\t"
        /* A[0] * A[2] */
        "ldr	r6, [%[a], #0]\n\t"
        "ldr	r8, [%[a], #8]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r5, r5, r6\n\t"
        "adc	r3, r3, r8\n\t"
        "adds	r5, r5, r6\n\t"
        "adcs 	r3, r3, r8\n\t"
        "adc	r4, r4, #0\n\t"
        /* A[1] * A[1] */
        "ldr	r6, [%[a], #4]\n\t"
        "umull	r6, r8, r6, r6\n\t"
        "adds	r5, r5, r6\n\t"
        "adcs	r3, r3, r8\n\t"
        "adc	r4, r4, #0\n\t"
        "str	r5, [%[tmp], #8]\n\t"
        "mov	r5, #0\n\t"
        /* A[0] * A[3] */
        "ldr	r6, [%[a], #0]\n\t"
        "ldr	r8, [%[a], #12]\n\t"
        "umull	r9, r10, r6, r8\n\t"
        "mov	r11, #0\n\t"
        /* A[1] * A[2] */
        "ldr	r6, [%[a], #4]\n\t"
        "ldr	r8, [%[a], #8]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r9, r9, r6\n\t"
        "adcs 	r10, r10, r8\n\t"
        "adc	r11, r11, #0\n\t"
        "adds	r9, r9, r9\n\t"
        "adcs	r10, r10, r10\n\t"
        "adc	r11, r11, r11\n\t"
        "adds	r3, r3, r9\n\t"
        "adcs	r4, r4, r10\n\t"
        "adc	r5, r5, r11\n\t"
        "str	r3, [%[tmp], #12]\n\t"
        "mov	r3, #0\n\t"
        /* A[0] * A[4] */
        "ldr	r6, [%[a], #0]\n\t"
        "ldr	r8, [%[a], #16]\n\t"
        "umull	r9, r10, r6, r8\n\t"
        "mov	r11, #0\n\t"
        /* A[1] * A[3] */
        "ldr	r6, [%[a], #4]\n\t"
        "ldr	r8, [%[a], #12]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r9, r9, r6\n\t"
        "adcs 	r10, r10, r8\n\t"
        "adc	r11, r11, #0\n\t"
        /* A[2] * A[2] */
        "ldr	r6, [%[a], #8]\n\t"
        "umull	r6, r8, r6, r6\n\t"
        "adds	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "adc	r3, r3, #0\n\t"
        "adds	r9, r9, r9\n\t"
        "adcs	r10, r10, r10\n\t"
        "adc	r11, r11, r11\n\t"
        "adds	r4, r4, r9\n\t"
        "adcs	r5, r5, r10\n\t"
        "adc	r3, r3, r11\n\t"
        "str	r4, [%[tmp], #16]\n\t"
        "mov	r4, #0\n\t"
        /* A[0] * A[5] */
        "ldr	r6, [%[a], #0]\n\t"
        "ldr	r8, [%[a], #20]\n\t"
        "umull	r9, r10, r6, r8\n\t"
        "mov	r11, #0\n\t"
        /* A[1] * A[4] */
        "ldr	r6, [%[a], #4]\n\t"
        "ldr	r8, [%[a], #16]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r9, r9, r6\n\t"
        "adcs 	r10, r10, r8\n\t"
        "adc	r11, r11, #0\n\t"
        /* A[2] * A[3] */
        "ldr	r6, [%[a], #8]\n\t"
        "ldr	r8, [%[a], #12]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r9, r9, r6\n\t"
        "adcs 	r10, r10, r8\n\t"
        "adc	r11, r11, #0\n\t"
        "adds	r9, r9, r9\n\t"
        "adcs	r10, r10, r10\n\t"
        "adc	r11, r11, r11\n\t"
        "adds	r5, r5, r9\n\t"
        "adcs	r3, r3, r10\n\t"
        "adc	r4, r4, r11\n\t"
        "str	r5, [%[tmp], #20]\n\t"
        "mov	r5, #0\n\t"
        /* A[0] * A[6] */
        "ldr	r6, [%[a], #0]\n\t"
        "ldr	r8, [%[a], #24]\n\t"
        "umull	r9, r10, r6, r8\n\t"
        "mov	r11, #0\n\t"
        /* A[1] * A[5] */
        "ldr	r6, [%[a], #4]\n\t"
        "ldr	r8, [%[a], #20]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r9, r9, r6\n\t"
        "adcs 	r10, r10, r8\n\t"
        "adc	r11, r11, #0\n\t"
        /* A[2] * A[4] */
        "ldr	r6, [%[a], #8]\n\t"
        "ldr	r8, [%[a], #16]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r9, r9, r6\n\t"
        "adcs 	r10, r10, r8\n\t"
        "adc	r11, r11, #0\n\t"
        /* A[3] * A[3] */
        "ldr	r6, [%[a], #12]\n\t"
        "umull	r6, r8, r6, r6\n\t"
        "adds	r3, r3, r6\n\t"
        "adcs	r4, r4, r8\n\t"
        "adc	r5, r5, #0\n\t"
        "adds	r9, r9, r9\n\t"
        "adcs	r10, r10, r10\n\t"
        "adc	r11, r11, r11\n\t"
        "adds	r3, r3, r9\n\t"
        "adcs	r4, r4, r10\n\t"
        "adc	r5, r5, r11\n\t"
        "str	r3, [%[tmp], #24]\n\t"
        "mov	r3, #0\n\t"
        /* A[0] * A[7] */
        "ldr	r6, [%[a], #0]\n\t"
        "ldr	r8, [%[a], #28]\n\t"
        "umull	r9, r10, r6, r8\n\t"
        "mov	r11, #0\n\t"
        /* A[1] * A[6] */
        "ldr	r6, [%[a], #4]\n\t"
        "ldr	r8, [%[a], #24]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r9, r9, r6\n\t"
        "adcs 	r10, r10, r8\n\t"
        "adc	r11, r11, #0\n\t"
        /* A[2] * A[5] */
        "ldr	r6, [%[a], #8]\n\t"
        "ldr	r8, [%[a], #20]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r9, r9, r6\n\t"
        "adcs 	r10, r10, r8\n\t"
        "adc	r11, r11, #0\n\t"
        /* A[3] * A[4] */
        "ldr	r6, [%[a], #12]\n\t"
        "ldr	r8, [%[a], #16]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r9, r9, r6\n\t"
        "adcs 	r10, r10, r8\n\t"
        "adc	r11, r11, #0\n\t"
        "adds	r9, r9, r9\n\t"
        "adcs	r10, r10, r10\n\t"
        "adc	r11, r11, r11\n\t"
        "adds	r4, r4, r9\n\t"
        "adcs	r5, r5, r10\n\t"
        "adc	r3, r3, r11\n\t"
        "str	r4, [%[tmp], #28]\n\t"
        "mov	r4, #0\n\t"
        /* A[1] * A[7] */
        "ldr	r6, [%[a], #4]\n\t"
        "ldr	r8, [%[a], #28]\n\t"
        "umull	r9, r10, r6, r8\n\t"
        "mov	r11, #0\n\t"
        /* A[2] * A[6] */
        "ldr	r6, [%[a], #8]\n\t"
        "ldr	r8, [%[a], #24]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r9, r9, r6\n\t"
        "adcs 	r10, r10, r8\n\t"
        "adc	r11, r11, #0\n\t"
        /* A[3] * A[5] */
        "ldr	r6, [%[a], #12]\n\t"
        "ldr	r8, [%[a], #20]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r9, r9, r6\n\t"
        "adcs 	r10, r10, r8\n\t"
        "adc	r11, r11, #0\n\t"
        /* A[4] * A[4] */
        "ldr	r6, [%[a], #16]\n\t"
        "umull	r6, r8, r6, r6\n\t"
        "adds	r5, r5, r6\n\t"
        "adcs	r3, r3, r8\n\t"
        "adc	r4, r4, #0\n\t"
        "adds	r9, r9, r9\n\t"
        "adcs	r10, r10, r10\n\t"
        "adc	r11, r11, r11\n\t"
        "adds	r5, r5, r9\n\t"
        "adcs	r3, r3, r10\n\t"
        "adc	r4, r4, r11\n\t"
        "str	r5, [%[r], #32]\n\t"
        "mov	r5, #0\n\t"
        /* A[2] * A[7] */
        "ldr	r6, [%[a], #8]\n\t"
        "ldr	r8, [%[a], #28]\n\t"
        "umull	r9, r10, r6, r8\n\t"
        "mov	r11, #0\n\t"
        /* A[3] * A[6] */
        "ldr	r6, [%[a], #12]\n\t"
        "ldr	r8, [%[a], #24]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r9, r9, r6\n\t"
        "adcs 	r10, r10, r8\n\t"
        "adc	r11, r11, #0\n\t"
        /* A[4] * A[5] */
        "ldr	r6, [%[a], #16]\n\t"
        "ldr	r8, [%[a], #20]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r9, r9, r6\n\t"
        "adcs 	r10, r10, r8\n\t"
        "adc	r11, r11, #0\n\t"
        "adds	r9, r9, r9\n\t"
        "adcs	r10, r10, r10\n\t"
        "adc	r11, r11, r11\n\t"
        "adds	r3, r3, r9\n\t"
        "adcs	r4, r4, r10\n\t"
        "adc	r5, r5, r11\n\t"
        "str	r3, [%[r], #36]\n\t"
        "mov	r3, #0\n\t"
        /* A[3] * A[7] */
        "ldr	r6, [%[a], #12]\n\t"
        "ldr	r8, [%[a], #28]\n\t"
        "umull	r9, r10, r6, r8\n\t"
        "mov	r11, #0\n\t"
        /* A[4] * A[6] */
        "ldr	r6, [%[a], #16]\n\t"
        "ldr	r8, [%[a], #24]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r9, r9, r6\n\t"
        "adcs 	r10, r10, r8\n\t"
        "adc	r11, r11, #0\n\t"
        /* A[5] * A[5] */
        "ldr	r6, [%[a], #20]\n\t"
        "umull	r6, r8, r6, r6\n\t"
        "adds	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "adc	r3, r3, #0\n\t"
        "adds	r9, r9, r9\n\t"
        "adcs	r10, r10, r10\n\t"
        "adc	r11, r11, r11\n\t"
        "adds	r4, r4, r9\n\t"
        "adcs	r5, r5, r10\n\t"
        "adc	r3, r3, r11\n\t"
        "str	r4, [%[r], #40]\n\t"
        "mov	r4, #0\n\t"
        /* A[4] * A[7] */
        "ldr	r6, [%[a], #16]\n\t"
        "ldr	r8, [%[a], #28]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r5, r5, r6\n\t"
        "adcs 	r3, r3, r8\n\t"
        "adc	r4, r4, #0\n\t"
        "adds	r5, r5, r6\n\t"
        "adcs 	r3, r3, r8\n\t"
        "adc	r4, r4, #0\n\t"
        /* A[5] * A[6] */
        "ldr	r6, [%[a], #20]\n\t"
        "ldr	r8, [%[a], #24]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r5, r5, r6\n\t"
        "adcs 	r3, r3, r8\n\t"
        "adc	r4, r4, #0\n\t"
        "adds	r5, r5, r6\n\t"
        "adcs 	r3, r3, r8\n\t"
        "adc	r4, r4, #0\n\t"
        "str	r5, [%[r], #44]\n\t"
        "mov	r5, #0\n\t"
        /* A[5] * A[7] */
        "ldr	r6, [%[a], #20]\n\t"
        "ldr	r8, [%[a], #28]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r3, r3, r6\n\t"
        "adcs 	r4, r4, r8\n\t"
        "adc	r5, r5, #0\n\t"
        "adds	r3, r3, r6\n\t"
        "adcs 	r4, r4, r8\n\t"
        "adc	r5, r5, #0\n\t"
        /* A[6] * A[6] */
        "ldr	r6, [%[a], #24]\n\t"
        "umull	r6, r8, r6, r6\n\t"
        "adds	r3, r3, r6\n\t"
        "adcs	r4, r4, r8\n\t"
        "adc	r5, r5, #0\n\t"
        "str	r3, [%[r], #48]\n\t"
        "mov	r3, #0\n\t"
        /* A[6] * A[7] */
        "ldr	r6, [%[a], #24]\n\t"
        "ldr	r8, [%[a], #28]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r4, r4, r6\n\t"
        "adcs 	r5, r5, r8\n\t"
        "adc	r3, r3, #0\n\t"
        "adds	r4, r4, r6\n\t"
        "adcs 	r5, r5, r8\n\t"
        "adc	r3, r3, #0\n\t"
        "str	r4, [%[r], #52]\n\t"
        "mov	r4, #0\n\t"
        /* A[7] * A[7] */
        "ldr	r6, [%[a], #28]\n\t"
        "umull	r6, r8, r6, r6\n\t"
        "adds	r5, r5, r6\n\t"
        "adc	r3, r3, r8\n\t"
        "str	r5, [%[r], #56]\n\t"
        "str	r3, [%[r], #60]\n\t"
        /* Transfer tmp to r */
        "ldr	r3, [%[tmp], #0]\n\t"
        "ldr	r4, [%[tmp], #4]\n\t"
        "ldr	r5, [%[tmp], #8]\n\t"
        "ldr	r6, [%[tmp], #12]\n\t"
        "str	r3, [%[r], #0]\n\t"
        "str	r4, [%[r], #4]\n\t"
        "str	r5, [%[r], #8]\n\t"
        "str	r6, [%[r], #12]\n\t"
        "ldr	r3, [%[tmp], #16]\n\t"
        "ldr	r4, [%[tmp], #20]\n\t"
        "ldr	r5, [%[tmp], #24]\n\t"
        "ldr	r6, [%[tmp], #28]\n\t"
        "str	r3, [%[r], #16]\n\t"
        "str	r4, [%[r], #20]\n\t"
        "str	r5, [%[r], #24]\n\t"
        "str	r6, [%[r], #28]\n\t"
        :
        : [r] "r" (r), [a] "r" (a), [tmp] "r" (tmp)
        : "memory", "r3", "r4", "r5", "r6", "r8", "r9", "r10", "r11"
    );
}

/* Add b to a into r. (r = a + b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A single precision integer.
 */
SP_NOINLINE static sp_digit sp_2048_add_8(sp_digit* r, const sp_digit* a,
        const sp_digit* b)
{
    sp_digit c = 0;

    __asm__ __volatile__ (
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adds	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "mov	%[c], #0\n\t"
        "adc	%[c], %[c], %[c]\n\t"
        : [c] "+r" (c), [r] "+r" (r), [a] "+r" (a), [b] "+r" (b)
        :
        : "memory", "r4", "r5", "r6", "r8"
    );

    return c;
}

/* Sub b from a into r. (r = a - b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A single precision integer.
 */
SP_NOINLINE static sp_digit sp_2048_sub_in_place_16(sp_digit* a,
        const sp_digit* b)
{
    sp_digit c = 0;

    __asm__ __volatile__ (
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "subs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "sbc	%[c], %[c], %[c]\n\t"
        : [c] "+r" (c), [a] "+r" (a), [b] "+r" (b)
        :
        : "memory", "r3", "r4", "r5", "r6"
    );

    return c;
}

/* Add b to a into r. (r = a + b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A single precision integer.
 */
SP_NOINLINE static sp_digit sp_2048_add_16(sp_digit* r, const sp_digit* a,
        const sp_digit* b)
{
    sp_digit c = 0;

    __asm__ __volatile__ (
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adds	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "mov	%[c], #0\n\t"
        "adc	%[c], %[c], %[c]\n\t"
        : [c] "+r" (c), [r] "+r" (r), [a] "+r" (a), [b] "+r" (b)
        :
        : "memory", "r4", "r5", "r6", "r8"
    );

    return c;
}

/* AND m into each word of a and store in r.
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * m  Mask to AND against each digit.
 */
static void sp_2048_mask_8(sp_digit* r, const sp_digit* a, sp_digit m)
{
#ifdef WOLFSSL_SP_SMALL
    int i;

    for (i=0; i<8; i++) {
        r[i] = a[i] & m;
    }
#else
    r[0] = a[0] & m;
    r[1] = a[1] & m;
    r[2] = a[2] & m;
    r[3] = a[3] & m;
    r[4] = a[4] & m;
    r[5] = a[5] & m;
    r[6] = a[6] & m;
    r[7] = a[7] & m;
#endif
}

/* Multiply a and b into r. (r = a * b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A single precision integer.
 */
SP_NOINLINE static void sp_2048_mul_16(sp_digit* r, const sp_digit* a,
        const sp_digit* b)
{
    sp_digit* z0 = r;
    sp_digit z1[16];
    sp_digit a1[8];
    sp_digit b1[8];
    sp_digit z2[16];
    sp_digit u, ca, cb;

    ca = sp_2048_add_8(a1, a, &a[8]);
    cb = sp_2048_add_8(b1, b, &b[8]);
    u  = ca & cb;
    sp_2048_mul_8(z1, a1, b1);
    sp_2048_mul_8(z2, &a[8], &b[8]);
    sp_2048_mul_8(z0, a, b);
    sp_2048_mask_8(r + 16, a1, 0 - cb);
    sp_2048_mask_8(b1, b1, 0 - ca);
    u += sp_2048_add_8(r + 16, r + 16, b1);
    u += sp_2048_sub_in_place_16(z1, z2);
    u += sp_2048_sub_in_place_16(z1, z0);
    u += sp_2048_add_16(r + 8, r + 8, z1);
    r[24] = u;
    XMEMSET(r + 24 + 1, 0, sizeof(sp_digit) * (8 - 1));
    (void)sp_2048_add_16(r + 16, r + 16, z2);
}

/* Square a and put result in r. (r = a * a)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 */
SP_NOINLINE static void sp_2048_sqr_16(sp_digit* r, const sp_digit* a)
{
    sp_digit* z0 = r;
    sp_digit z2[16];
    sp_digit z1[16];
    sp_digit a1[8];
    sp_digit u;

    u = sp_2048_add_8(a1, a, &a[8]);
    sp_2048_sqr_8(z1, a1);
    sp_2048_sqr_8(z2, &a[8]);
    sp_2048_sqr_8(z0, a);
    sp_2048_mask_8(r + 16, a1, 0 - u);
    u += sp_2048_add_8(r + 16, r + 16, r + 16);
    u += sp_2048_sub_in_place_16(z1, z2);
    u += sp_2048_sub_in_place_16(z1, z0);
    u += sp_2048_add_16(r + 8, r + 8, z1);
    r[24] = u;
    XMEMSET(r + 24 + 1, 0, sizeof(sp_digit) * (8 - 1));
    (void)sp_2048_add_16(r + 16, r + 16, z2);
}

/* Sub b from a into r. (r = a - b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A single precision integer.
 */
SP_NOINLINE static sp_digit sp_2048_sub_in_place_32(sp_digit* a,
        const sp_digit* b)
{
    sp_digit c = 0;

    __asm__ __volatile__ (
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "subs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "sbc	%[c], %[c], %[c]\n\t"
        : [c] "+r" (c), [a] "+r" (a), [b] "+r" (b)
        :
        : "memory", "r3", "r4", "r5", "r6"
    );

    return c;
}

/* Add b to a into r. (r = a + b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A single precision integer.
 */
SP_NOINLINE static sp_digit sp_2048_add_32(sp_digit* r, const sp_digit* a,
        const sp_digit* b)
{
    sp_digit c = 0;

    __asm__ __volatile__ (
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adds	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "mov	%[c], #0\n\t"
        "adc	%[c], %[c], %[c]\n\t"
        : [c] "+r" (c), [r] "+r" (r), [a] "+r" (a), [b] "+r" (b)
        :
        : "memory", "r4", "r5", "r6", "r8"
    );

    return c;
}

/* AND m into each word of a and store in r.
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * m  Mask to AND against each digit.
 */
static void sp_2048_mask_16(sp_digit* r, const sp_digit* a, sp_digit m)
{
#ifdef WOLFSSL_SP_SMALL
    int i;

    for (i=0; i<16; i++) {
        r[i] = a[i] & m;
    }
#else
    int i;

    for (i = 0; i < 16; i += 8) {
        r[i+0] = a[i+0] & m;
        r[i+1] = a[i+1] & m;
        r[i+2] = a[i+2] & m;
        r[i+3] = a[i+3] & m;
        r[i+4] = a[i+4] & m;
        r[i+5] = a[i+5] & m;
        r[i+6] = a[i+6] & m;
        r[i+7] = a[i+7] & m;
    }
#endif
}

/* Multiply a and b into r. (r = a * b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A single precision integer.
 */
SP_NOINLINE static void sp_2048_mul_32(sp_digit* r, const sp_digit* a,
        const sp_digit* b)
{
    sp_digit* z0 = r;
    sp_digit z1[32];
    sp_digit a1[16];
    sp_digit b1[16];
    sp_digit z2[32];
    sp_digit u, ca, cb;

    ca = sp_2048_add_16(a1, a, &a[16]);
    cb = sp_2048_add_16(b1, b, &b[16]);
    u  = ca & cb;
    sp_2048_mul_16(z1, a1, b1);
    sp_2048_mul_16(z2, &a[16], &b[16]);
    sp_2048_mul_16(z0, a, b);
    sp_2048_mask_16(r + 32, a1, 0 - cb);
    sp_2048_mask_16(b1, b1, 0 - ca);
    u += sp_2048_add_16(r + 32, r + 32, b1);
    u += sp_2048_sub_in_place_32(z1, z2);
    u += sp_2048_sub_in_place_32(z1, z0);
    u += sp_2048_add_32(r + 16, r + 16, z1);
    r[48] = u;
    XMEMSET(r + 48 + 1, 0, sizeof(sp_digit) * (16 - 1));
    (void)sp_2048_add_32(r + 32, r + 32, z2);
}

/* Square a and put result in r. (r = a * a)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 */
SP_NOINLINE static void sp_2048_sqr_32(sp_digit* r, const sp_digit* a)
{
    sp_digit* z0 = r;
    sp_digit z2[32];
    sp_digit z1[32];
    sp_digit a1[16];
    sp_digit u;

    u = sp_2048_add_16(a1, a, &a[16]);
    sp_2048_sqr_16(z1, a1);
    sp_2048_sqr_16(z2, &a[16]);
    sp_2048_sqr_16(z0, a);
    sp_2048_mask_16(r + 32, a1, 0 - u);
    u += sp_2048_add_16(r + 32, r + 32, r + 32);
    u += sp_2048_sub_in_place_32(z1, z2);
    u += sp_2048_sub_in_place_32(z1, z0);
    u += sp_2048_add_32(r + 16, r + 16, z1);
    r[48] = u;
    XMEMSET(r + 48 + 1, 0, sizeof(sp_digit) * (16 - 1));
    (void)sp_2048_add_32(r + 32, r + 32, z2);
}

/* Sub b from a into r. (r = a - b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A single precision integer.
 */
SP_NOINLINE static sp_digit sp_2048_sub_in_place_64(sp_digit* a,
        const sp_digit* b)
{
    sp_digit c = 0;

    __asm__ __volatile__ (
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "subs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "sbc	%[c], %[c], %[c]\n\t"
        : [c] "+r" (c), [a] "+r" (a), [b] "+r" (b)
        :
        : "memory", "r3", "r4", "r5", "r6"
    );

    return c;
}

/* Add b to a into r. (r = a + b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A single precision integer.
 */
SP_NOINLINE static sp_digit sp_2048_add_64(sp_digit* r, const sp_digit* a,
        const sp_digit* b)
{
    sp_digit c = 0;

    __asm__ __volatile__ (
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adds	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "mov	%[c], #0\n\t"
        "adc	%[c], %[c], %[c]\n\t"
        : [c] "+r" (c), [r] "+r" (r), [a] "+r" (a), [b] "+r" (b)
        :
        : "memory", "r4", "r5", "r6", "r8"
    );

    return c;
}

/* AND m into each word of a and store in r.
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * m  Mask to AND against each digit.
 */
static void sp_2048_mask_32(sp_digit* r, const sp_digit* a, sp_digit m)
{
#ifdef WOLFSSL_SP_SMALL
    int i;

    for (i=0; i<32; i++) {
        r[i] = a[i] & m;
    }
#else
    int i;

    for (i = 0; i < 32; i += 8) {
        r[i+0] = a[i+0] & m;
        r[i+1] = a[i+1] & m;
        r[i+2] = a[i+2] & m;
        r[i+3] = a[i+3] & m;
        r[i+4] = a[i+4] & m;
        r[i+5] = a[i+5] & m;
        r[i+6] = a[i+6] & m;
        r[i+7] = a[i+7] & m;
    }
#endif
}

/* Multiply a and b into r. (r = a * b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A single precision integer.
 */
SP_NOINLINE static void sp_2048_mul_64(sp_digit* r, const sp_digit* a,
        const sp_digit* b)
{
    sp_digit* z0 = r;
    sp_digit z1[64];
    sp_digit a1[32];
    sp_digit b1[32];
    sp_digit z2[64];
    sp_digit u, ca, cb;

    ca = sp_2048_add_32(a1, a, &a[32]);
    cb = sp_2048_add_32(b1, b, &b[32]);
    u  = ca & cb;
    sp_2048_mul_32(z1, a1, b1);
    sp_2048_mul_32(z2, &a[32], &b[32]);
    sp_2048_mul_32(z0, a, b);
    sp_2048_mask_32(r + 64, a1, 0 - cb);
    sp_2048_mask_32(b1, b1, 0 - ca);
    u += sp_2048_add_32(r + 64, r + 64, b1);
    u += sp_2048_sub_in_place_64(z1, z2);
    u += sp_2048_sub_in_place_64(z1, z0);
    u += sp_2048_add_64(r + 32, r + 32, z1);
    r[96] = u;
    XMEMSET(r + 96 + 1, 0, sizeof(sp_digit) * (32 - 1));
    (void)sp_2048_add_64(r + 64, r + 64, z2);
}

/* Square a and put result in r. (r = a * a)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 */
SP_NOINLINE static void sp_2048_sqr_64(sp_digit* r, const sp_digit* a)
{
    sp_digit* z0 = r;
    sp_digit z2[64];
    sp_digit z1[64];
    sp_digit a1[32];
    sp_digit u;

    u = sp_2048_add_32(a1, a, &a[32]);
    sp_2048_sqr_32(z1, a1);
    sp_2048_sqr_32(z2, &a[32]);
    sp_2048_sqr_32(z0, a);
    sp_2048_mask_32(r + 64, a1, 0 - u);
    u += sp_2048_add_32(r + 64, r + 64, r + 64);
    u += sp_2048_sub_in_place_64(z1, z2);
    u += sp_2048_sub_in_place_64(z1, z0);
    u += sp_2048_add_64(r + 32, r + 32, z1);
    r[96] = u;
    XMEMSET(r + 96 + 1, 0, sizeof(sp_digit) * (32 - 1));
    (void)sp_2048_add_64(r + 64, r + 64, z2);
}

#endif /* !WOLFSSL_SP_SMALL */
#ifdef WOLFSSL_SP_SMALL
/* Add b to a into r. (r = a + b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A single precision integer.
 */
SP_NOINLINE static sp_digit sp_2048_add_64(sp_digit* r, const sp_digit* a,
        const sp_digit* b)
{
    sp_digit c = 0;

    __asm__ __volatile__ (
        "mov	r6, %[a]\n\t"
        "mov	r8, #0\n\t"
        "add	r6, r6, #256\n\t"
        "sub	r8, r8, #1\n\t"
        "\n1:\n\t"
        "adds	%[c], %[c], r8\n\t"
        "ldr	r4, [%[a]]\n\t"
        "ldr	r5, [%[b]]\n\t"
        "adcs	r4, r4, r5\n\t"
        "str	r4, [%[r]]\n\t"
        "mov	%[c], #0\n\t"
        "adc	%[c], %[c], %[c]\n\t"
        "add	%[a], %[a], #4\n\t"
        "add	%[b], %[b], #4\n\t"
        "add	%[r], %[r], #4\n\t"
        "cmp	%[a], r6\n\t"
        "bne	1b\n\t"
        : [c] "+r" (c), [r] "+r" (r), [a] "+r" (a), [b] "+r" (b)
        :
        : "memory", "r4", "r5", "r6", "r8"
    );

    return c;
}

#endif /* WOLFSSL_SP_SMALL */
#ifdef WOLFSSL_SP_SMALL
/* Sub b from a into a. (a -= b)
 *
 * a  A single precision integer.
 * b  A single precision integer.
 */
SP_NOINLINE static sp_digit sp_2048_sub_in_place_64(sp_digit* a,
        const sp_digit* b)
{
    sp_digit c = 0;
    __asm__ __volatile__ (
        "mov	r8, %[a]\n\t"
        "add	r8, r8, #256\n\t"
        "\n1:\n\t"
        "mov	r5, #0\n\t"
        "subs	r5, r5, %[c]\n\t"
        "ldr	r3, [%[a]]\n\t"
        "ldr	r4, [%[a], #4]\n\t"
        "ldr	r5, [%[b]]\n\t"
        "ldr	r6, [%[b], #4]\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "str	r3, [%[a]]\n\t"
        "str	r4, [%[a], #4]\n\t"
        "sbc	%[c], %[c], %[c]\n\t"
        "add	%[a], %[a], #8\n\t"
        "add	%[b], %[b], #8\n\t"
        "cmp	%[a], r8\n\t"
        "bne	1b\n\t"
        : [c] "+r" (c), [a] "+r" (a), [b] "+r" (b)
        :
        : "memory", "r3", "r4", "r5", "r6", "r8"
    );

    return c;
}

#endif /* WOLFSSL_SP_SMALL */
#ifdef WOLFSSL_SP_SMALL
/* Multiply a and b into r. (r = a * b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A single precision integer.
 */
SP_NOINLINE static void sp_2048_mul_64(sp_digit* r, const sp_digit* a,
        const sp_digit* b)
{
    sp_digit tmp[64 * 2];
    __asm__ __volatile__ (
        "mov	r3, #0\n\t"
        "mov	r4, #0\n\t"
        "mov	r9, r3\n\t"
        "mov	r12, %[r]\n\t"
        "mov	r10, %[a]\n\t"
        "mov	r11, %[b]\n\t"
        "mov	r6, #1\n\t"
        "lsl	r6, r6, #8\n\t"
        "add	r6, r6, r10\n\t"
        "mov	r14, r6\n\t"
        "\n1:\n\t"
        "mov	%[r], #0\n\t"
        "mov	r5, #0\n\t"
        "mov	r6, #252\n\t"
        "mov	%[a], r9\n\t"
        "subs	%[a], %[a], r6\n\t"
        "sbc	r6, r6, r6\n\t"
        "mvn	r6, r6\n\t"
        "and	%[a], %[a], r6\n\t"
        "mov	%[b], r9\n\t"
        "sub	%[b], %[b], %[a]\n\t"
        "add	%[a], %[a], r10\n\t"
        "add	%[b], %[b], r11\n\t"
        "\n2:\n\t"
        /* Multiply Start */
        "ldr	r6, [%[a]]\n\t"
        "ldr	r8, [%[b]]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r3, r3, r6\n\t"
        "adcs 	r4, r4, r8\n\t"
        "adc	r5, r5, %[r]\n\t"
        /* Multiply Done */
        "add	%[a], %[a], #4\n\t"
        "sub	%[b], %[b], #4\n\t"
        "cmp	%[a], r14\n\t"
        "beq	3f\n\t"
        "mov	r6, r9\n\t"
        "add	r6, r6, r10\n\t"
        "cmp	%[a], r6\n\t"
        "ble	2b\n\t"
        "\n3:\n\t"
        "mov	%[r], r12\n\t"
        "mov	r8, r9\n\t"
        "str	r3, [%[r], r8]\n\t"
        "mov	r3, r4\n\t"
        "mov	r4, r5\n\t"
        "add	r8, r8, #4\n\t"
        "mov	r9, r8\n\t"
        "mov	r6, #1\n\t"
        "lsl	r6, r6, #8\n\t"
        "add	r6, r6, #248\n\t"
        "cmp	r8, r6\n\t"
        "ble	1b\n\t"
        "str	r3, [%[r], r8]\n\t"
        "mov	%[a], r10\n\t"
        "mov	%[b], r11\n\t"
        :
        : [r] "r" (tmp), [a] "r" (a), [b] "r" (b)
        : "memory", "r3", "r4", "r5", "r6", "r8", "r9", "r10", "r11", "r12", "r14"
    );

    XMEMCPY(r, tmp, sizeof(tmp));
}

/* Square a and put result in r. (r = a * a)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 */
SP_NOINLINE static void sp_2048_sqr_64(sp_digit* r, const sp_digit* a)
{
    __asm__ __volatile__ (
        "mov	r3, #0\n\t"
        "mov	r4, #0\n\t"
        "mov	r5, #0\n\t"
        "mov	r9, r3\n\t"
        "mov	r12, %[r]\n\t"
        "mov	r6, #2\n\t"
        "lsl	r6, r6, #8\n\t"
        "neg	r6, r6\n\t"
        "add	sp, sp, r6\n\t"
        "mov	r11, sp\n\t"
        "mov	r10, %[a]\n\t"
        "\n1:\n\t"
        "mov	%[r], #0\n\t"
        "mov	r6, #252\n\t"
        "mov	%[a], r9\n\t"
        "subs	%[a], %[a], r6\n\t"
        "sbc	r6, r6, r6\n\t"
        "mvn	r6, r6\n\t"
        "and	%[a], %[a], r6\n\t"
        "mov	r2, r9\n\t"
        "sub	r2, r2, %[a]\n\t"
        "add	%[a], %[a], r10\n\t"
        "add	r2, r2, r10\n\t"
        "\n2:\n\t"
        "cmp	r2, %[a]\n\t"
        "beq	4f\n\t"
        /* Multiply * 2: Start */
        "ldr	r6, [%[a]]\n\t"
        "ldr	r8, [r2]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r3, r3, r6\n\t"
        "adcs 	r4, r4, r8\n\t"
        "adc	r5, r5, %[r]\n\t"
        "adds	r3, r3, r6\n\t"
        "adcs 	r4, r4, r8\n\t"
        "adc	r5, r5, %[r]\n\t"
        /* Multiply * 2: Done */
        "bal	5f\n\t"
        "\n4:\n\t"
        /* Square: Start */
        "ldr	r6, [%[a]]\n\t"
        "umull	r6, r8, r6, r6\n\t"
        "adds	r3, r3, r6\n\t"
        "adcs	r4, r4, r8\n\t"
        "adc	r5, r5, %[r]\n\t"
        /* Square: Done */
        "\n5:\n\t"
        "add	%[a], %[a], #4\n\t"
        "sub	r2, r2, #4\n\t"
        "mov	r6, #1\n\t"
        "lsl	r6, r6, #8\n\t"
        "add	r6, r6, r10\n\t"
        "cmp	%[a], r6\n\t"
        "beq	3f\n\t"
        "cmp	%[a], r2\n\t"
        "bgt	3f\n\t"
        "mov	r8, r9\n\t"
        "add	r8, r8, r10\n\t"
        "cmp	%[a], r8\n\t"
        "ble	2b\n\t"
        "\n3:\n\t"
        "mov	%[r], r11\n\t"
        "mov	r8, r9\n\t"
        "str	r3, [%[r], r8]\n\t"
        "mov	r3, r4\n\t"
        "mov	r4, r5\n\t"
        "mov	r5, #0\n\t"
        "add	r8, r8, #4\n\t"
        "mov	r9, r8\n\t"
        "mov	r6, #1\n\t"
        "lsl	r6, r6, #8\n\t"
        "add	r6, r6, #248\n\t"
        "cmp	r8, r6\n\t"
        "ble	1b\n\t"
        "mov	%[a], r10\n\t"
        "str	r3, [%[r], r8]\n\t"
        "mov	%[r], r12\n\t"
        "mov	%[a], r11\n\t"
        "mov	r3, #1\n\t"
        "lsl	r3, r3, #8\n\t"
        "add	r3, r3, #252\n\t"
        "\n4:\n\t"
        "ldr	r6, [%[a], r3]\n\t"
        "str	r6, [%[r], r3]\n\t"
        "subs	r3, r3, #4\n\t"
        "bge	4b\n\t"
        "mov	r6, #2\n\t"
        "lsl	r6, r6, #8\n\t"
        "add	sp, sp, r6\n\t"
        :
        : [r] "r" (r), [a] "r" (a)
        : "memory", "r2", "r3", "r4", "r5", "r6", "r8", "r9", "r10", "r11", "r12"
    );
}

#endif /* WOLFSSL_SP_SMALL */
#if (defined(WOLFSSL_HAVE_SP_RSA) || defined(WOLFSSL_HAVE_SP_DH)) && !defined(WOLFSSL_RSA_PUBLIC_ONLY)
#ifdef WOLFSSL_SP_SMALL
/* AND m into each word of a and store in r.
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * m  Mask to AND against each digit.
 */
static void sp_2048_mask_32(sp_digit* r, const sp_digit* a, sp_digit m)
{
    int i;

    for (i=0; i<32; i++) {
        r[i] = a[i] & m;
    }
}

#endif /* WOLFSSL_SP_SMALL */
#ifdef WOLFSSL_SP_SMALL
/* Add b to a into r. (r = a + b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A single precision integer.
 */
SP_NOINLINE static sp_digit sp_2048_add_32(sp_digit* r, const sp_digit* a,
        const sp_digit* b)
{
    sp_digit c = 0;

    __asm__ __volatile__ (
        "mov	r6, %[a]\n\t"
        "mov	r8, #0\n\t"
        "add	r6, r6, #128\n\t"
        "sub	r8, r8, #1\n\t"
        "\n1:\n\t"
        "adds	%[c], %[c], r8\n\t"
        "ldr	r4, [%[a]]\n\t"
        "ldr	r5, [%[b]]\n\t"
        "adcs	r4, r4, r5\n\t"
        "str	r4, [%[r]]\n\t"
        "mov	%[c], #0\n\t"
        "adc	%[c], %[c], %[c]\n\t"
        "add	%[a], %[a], #4\n\t"
        "add	%[b], %[b], #4\n\t"
        "add	%[r], %[r], #4\n\t"
        "cmp	%[a], r6\n\t"
        "bne	1b\n\t"
        : [c] "+r" (c), [r] "+r" (r), [a] "+r" (a), [b] "+r" (b)
        :
        : "memory", "r4", "r5", "r6", "r8"
    );

    return c;
}

#endif /* WOLFSSL_SP_SMALL */
#ifdef WOLFSSL_SP_SMALL
/* Sub b from a into a. (a -= b)
 *
 * a  A single precision integer.
 * b  A single precision integer.
 */
SP_NOINLINE static sp_digit sp_2048_sub_in_place_32(sp_digit* a,
        const sp_digit* b)
{
    sp_digit c = 0;
    __asm__ __volatile__ (
        "mov	r8, %[a]\n\t"
        "add	r8, r8, #128\n\t"
        "\n1:\n\t"
        "mov	r5, #0\n\t"
        "subs	r5, r5, %[c]\n\t"
        "ldr	r3, [%[a]]\n\t"
        "ldr	r4, [%[a], #4]\n\t"
        "ldr	r5, [%[b]]\n\t"
        "ldr	r6, [%[b], #4]\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "str	r3, [%[a]]\n\t"
        "str	r4, [%[a], #4]\n\t"
        "sbc	%[c], %[c], %[c]\n\t"
        "add	%[a], %[a], #8\n\t"
        "add	%[b], %[b], #8\n\t"
        "cmp	%[a], r8\n\t"
        "bne	1b\n\t"
        : [c] "+r" (c), [a] "+r" (a), [b] "+r" (b)
        :
        : "memory", "r3", "r4", "r5", "r6", "r8"
    );

    return c;
}

#endif /* WOLFSSL_SP_SMALL */
#ifdef WOLFSSL_SP_SMALL
/* Multiply a and b into r. (r = a * b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A single precision integer.
 */
SP_NOINLINE static void sp_2048_mul_32(sp_digit* r, const sp_digit* a,
        const sp_digit* b)
{
    sp_digit tmp[32 * 2];
    __asm__ __volatile__ (
        "mov	r3, #0\n\t"
        "mov	r4, #0\n\t"
        "mov	r9, r3\n\t"
        "mov	r12, %[r]\n\t"
        "mov	r10, %[a]\n\t"
        "mov	r11, %[b]\n\t"
        "mov	r6, #128\n\t"
        "add	r6, r6, r10\n\t"
        "mov	r14, r6\n\t"
        "\n1:\n\t"
        "mov	%[r], #0\n\t"
        "mov	r5, #0\n\t"
        "mov	r6, #124\n\t"
        "mov	%[a], r9\n\t"
        "subs	%[a], %[a], r6\n\t"
        "sbc	r6, r6, r6\n\t"
        "mvn	r6, r6\n\t"
        "and	%[a], %[a], r6\n\t"
        "mov	%[b], r9\n\t"
        "sub	%[b], %[b], %[a]\n\t"
        "add	%[a], %[a], r10\n\t"
        "add	%[b], %[b], r11\n\t"
        "\n2:\n\t"
        /* Multiply Start */
        "ldr	r6, [%[a]]\n\t"
        "ldr	r8, [%[b]]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r3, r3, r6\n\t"
        "adcs 	r4, r4, r8\n\t"
        "adc	r5, r5, %[r]\n\t"
        /* Multiply Done */
        "add	%[a], %[a], #4\n\t"
        "sub	%[b], %[b], #4\n\t"
        "cmp	%[a], r14\n\t"
        "beq	3f\n\t"
        "mov	r6, r9\n\t"
        "add	r6, r6, r10\n\t"
        "cmp	%[a], r6\n\t"
        "ble	2b\n\t"
        "\n3:\n\t"
        "mov	%[r], r12\n\t"
        "mov	r8, r9\n\t"
        "str	r3, [%[r], r8]\n\t"
        "mov	r3, r4\n\t"
        "mov	r4, r5\n\t"
        "add	r8, r8, #4\n\t"
        "mov	r9, r8\n\t"
        "mov	r6, #248\n\t"
        "cmp	r8, r6\n\t"
        "ble	1b\n\t"
        "str	r3, [%[r], r8]\n\t"
        "mov	%[a], r10\n\t"
        "mov	%[b], r11\n\t"
        :
        : [r] "r" (tmp), [a] "r" (a), [b] "r" (b)
        : "memory", "r3", "r4", "r5", "r6", "r8", "r9", "r10", "r11", "r12", "r14"
    );

    XMEMCPY(r, tmp, sizeof(tmp));
}

/* Square a and put result in r. (r = a * a)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 */
SP_NOINLINE static void sp_2048_sqr_32(sp_digit* r, const sp_digit* a)
{
    __asm__ __volatile__ (
        "mov	r3, #0\n\t"
        "mov	r4, #0\n\t"
        "mov	r5, #0\n\t"
        "mov	r9, r3\n\t"
        "mov	r12, %[r]\n\t"
        "mov	r6, #1\n\t"
        "lsl	r6, r6, #8\n\t"
        "neg	r6, r6\n\t"
        "add	sp, sp, r6\n\t"
        "mov	r11, sp\n\t"
        "mov	r10, %[a]\n\t"
        "\n1:\n\t"
        "mov	%[r], #0\n\t"
        "mov	r6, #124\n\t"
        "mov	%[a], r9\n\t"
        "subs	%[a], %[a], r6\n\t"
        "sbc	r6, r6, r6\n\t"
        "mvn	r6, r6\n\t"
        "and	%[a], %[a], r6\n\t"
        "mov	r2, r9\n\t"
        "sub	r2, r2, %[a]\n\t"
        "add	%[a], %[a], r10\n\t"
        "add	r2, r2, r10\n\t"
        "\n2:\n\t"
        "cmp	r2, %[a]\n\t"
        "beq	4f\n\t"
        /* Multiply * 2: Start */
        "ldr	r6, [%[a]]\n\t"
        "ldr	r8, [r2]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r3, r3, r6\n\t"
        "adcs 	r4, r4, r8\n\t"
        "adc	r5, r5, %[r]\n\t"
        "adds	r3, r3, r6\n\t"
        "adcs 	r4, r4, r8\n\t"
        "adc	r5, r5, %[r]\n\t"
        /* Multiply * 2: Done */
        "bal	5f\n\t"
        "\n4:\n\t"
        /* Square: Start */
        "ldr	r6, [%[a]]\n\t"
        "umull	r6, r8, r6, r6\n\t"
        "adds	r3, r3, r6\n\t"
        "adcs	r4, r4, r8\n\t"
        "adc	r5, r5, %[r]\n\t"
        /* Square: Done */
        "\n5:\n\t"
        "add	%[a], %[a], #4\n\t"
        "sub	r2, r2, #4\n\t"
        "mov	r6, #128\n\t"
        "add	r6, r6, r10\n\t"
        "cmp	%[a], r6\n\t"
        "beq	3f\n\t"
        "cmp	%[a], r2\n\t"
        "bgt	3f\n\t"
        "mov	r8, r9\n\t"
        "add	r8, r8, r10\n\t"
        "cmp	%[a], r8\n\t"
        "ble	2b\n\t"
        "\n3:\n\t"
        "mov	%[r], r11\n\t"
        "mov	r8, r9\n\t"
        "str	r3, [%[r], r8]\n\t"
        "mov	r3, r4\n\t"
        "mov	r4, r5\n\t"
        "mov	r5, #0\n\t"
        "add	r8, r8, #4\n\t"
        "mov	r9, r8\n\t"
        "mov	r6, #248\n\t"
        "cmp	r8, r6\n\t"
        "ble	1b\n\t"
        "mov	%[a], r10\n\t"
        "str	r3, [%[r], r8]\n\t"
        "mov	%[r], r12\n\t"
        "mov	%[a], r11\n\t"
        "mov	r3, #252\n\t"
        "\n4:\n\t"
        "ldr	r6, [%[a], r3]\n\t"
        "str	r6, [%[r], r3]\n\t"
        "subs	r3, r3, #4\n\t"
        "bge	4b\n\t"
        "mov	r6, #1\n\t"
        "lsl	r6, r6, #8\n\t"
        "add	sp, sp, r6\n\t"
        :
        : [r] "r" (r), [a] "r" (a)
        : "memory", "r2", "r3", "r4", "r5", "r6", "r8", "r9", "r10", "r11", "r12"
    );
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

    /* rho = -1/m mod b */
    *rho = -x;
}

/* Mul a by digit b into r. (r = a * b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A single precision digit.
 */
SP_NOINLINE static void sp_2048_mul_d_64(sp_digit* r, const sp_digit* a,
        sp_digit b)
{
    __asm__ __volatile__ (
        "add	r9, %[a], #256\n\t"
        /* A[0] * B */
        "ldr	r6, [%[a]], #4\n\t"
        "umull	r5, r3, r6, %[b]\n\t"
        "mov	r4, #0\n\t"
        "str	r5, [%[r]], #4\n\t"
        /* A[0] * B - Done */
        "\n1:\n\t"
        "mov	r5, #0\n\t"
        /* A[] * B */
        "ldr	r6, [%[a]], #4\n\t"
        "umull	r6, r8, r6, %[b]\n\t"
        "adds	r3, r3, r6\n\t"
        "adcs 	r4, r4, r8\n\t"
        "adc	r5, r5, #0\n\t"
        /* A[] * B - Done */
        "str	r3, [%[r]], #4\n\t"
        "mov	r3, r4\n\t"
        "mov	r4, r5\n\t"
        "cmp	%[a], r9\n\t"
        "blt	1b\n\t"
        "str	r3, [%[r]]\n\t"
        : [r] "+r" (r), [a] "+r" (a)
        : [b] "r" (b)
        : "memory", "r3", "r4", "r5", "r6", "r8", "r9"
    );
}

#if (defined(WOLFSSL_HAVE_SP_RSA) || defined(WOLFSSL_HAVE_SP_DH)) && !defined(WOLFSSL_RSA_PUBLIC_ONLY)
/* r = 2^n mod m where n is the number of bits to reduce by.
 * Given m must be 2048 bits, just need to subtract.
 *
 * r  A single precision number.
 * m  A single precision number.
 */
static void sp_2048_mont_norm_32(sp_digit* r, const sp_digit* m)
{
    XMEMSET(r, 0, sizeof(sp_digit) * 32);

    /* r = 2^n mod m */
    sp_2048_sub_in_place_32(r, m);
}

/* Conditionally subtract b from a using the mask m.
 * m is -1 to subtract and 0 when not copying.
 *
 * r  A single precision number representing condition subtract result.
 * a  A single precision number to subtract from.
 * b  A single precision number to subtract.
 * m  Mask value to apply.
 */
SP_NOINLINE static sp_digit sp_2048_cond_sub_32(sp_digit* r, const sp_digit* a,
        const sp_digit* b, sp_digit m)
{
    sp_digit c = 0;

    __asm__ __volatile__ (
        "mov	r5, #128\n\t"
        "mov	r9, r5\n\t"
        "mov	r8, #0\n\t"
        "\n1:\n\t"
        "ldr	r6, [%[b], r8]\n\t"
        "and	r6, r6, %[m]\n\t"
        "mov	r5, #0\n\t"
        "subs	r5, r5, %[c]\n\t"
        "ldr	r5, [%[a], r8]\n\t"
        "sbcs	r5, r5, r6\n\t"
        "sbcs	%[c], %[c], %[c]\n\t"
        "str	r5, [%[r], r8]\n\t"
        "add	r8, r8, #4\n\t"
        "cmp	r8, r9\n\t"
        "blt	1b\n\t"
        : [c] "+r" (c)
        : [r] "r" (r), [a] "r" (a), [b] "r" (b), [m] "r" (m)
        : "memory", "r5", "r6", "r8", "r9"
    );

    return c;
}

/* Reduce the number back to 2048 bits using Montgomery reduction.
 *
 * a   A single precision number to reduce in place.
 * m   The single precision number representing the modulus.
 * mp  The digit representing the negative inverse of m mod 2^n.
 */
SP_NOINLINE static void sp_2048_mont_reduce_32(sp_digit* a, const sp_digit* m,
        sp_digit mp)
{
    sp_digit ca = 0;

    __asm__ __volatile__ (
        "mov	r9, %[mp]\n\t"
        "mov	r12, %[m]\n\t"
        "mov	r10, %[a]\n\t"
        "mov	r4, #0\n\t"
        "add	r11, r10, #128\n\t"
        "\n1:\n\t"
        /* mu = a[i] * mp */
        "mov	%[mp], r9\n\t"
        "ldr	%[a], [r10]\n\t"
        "mul	%[mp], %[mp], %[a]\n\t"
        "mov	%[m], r12\n\t"
        "add	r14, r10, #120\n\t"
        "\n2:\n\t"
        /* a[i+j] += m[j] * mu */
        "ldr	%[a], [r10]\n\t"
        "mov	r5, #0\n\t"
        /* Multiply m[j] and mu - Start */
        "ldr	r8, [%[m]], #4\n\t"
        "umull	r6, r8, %[mp], r8\n\t"
        "adds	%[a], %[a], r6\n\t"
        "adc	r5, r5, r8\n\t"
        /* Multiply m[j] and mu - Done */
        "adds	r4, r4, %[a]\n\t"
        "adc	r5, r5, #0\n\t"
        "str	r4, [r10], #4\n\t"
        /* a[i+j+1] += m[j+1] * mu */
        "ldr	%[a], [r10]\n\t"
        "mov	r4, #0\n\t"
        /* Multiply m[j] and mu - Start */
        "ldr	r8, [%[m]], #4\n\t"
        "umull	r6, r8, %[mp], r8\n\t"
        "adds	%[a], %[a], r6\n\t"
        "adc	r4, r4, r8\n\t"
        /* Multiply m[j] and mu - Done */
        "adds	r5, r5, %[a]\n\t"
        "adc	r4, r4, #0\n\t"
        "str	r5, [r10], #4\n\t"
        "cmp	r10, r14\n\t"
        "blt	2b\n\t"
        /* a[i+30] += m[30] * mu */
        "ldr	%[a], [r10]\n\t"
        "mov	r5, #0\n\t"
        /* Multiply m[j] and mu - Start */
        "ldr	r8, [%[m]], #4\n\t"
        "umull	r6, r8, %[mp], r8\n\t"
        "adds	%[a], %[a], r6\n\t"
        "adc	r5, r5, r8\n\t"
        /* Multiply m[j] and mu - Done */
        "adds	r4, r4, %[a]\n\t"
        "adc	r5, r5, #0\n\t"
        "str	r4, [r10], #4\n\t"
        /* a[i+31] += m[31] * mu */
        "mov	r4, %[ca]\n\t"
        "mov	%[ca], #0\n\t"
        /* Multiply m[31] and mu - Start */
        "ldr	r8, [%[m]]\n\t"
        "umull	r6, r8, %[mp], r8\n\t"
        "adds	r5, r5, r6\n\t"
        "adcs 	r4, r4, r8\n\t"
        "adc	%[ca], %[ca], #0\n\t"
        /* Multiply m[31] and mu - Done */
        "ldr	r6, [r10]\n\t"
        "ldr	r8, [r10, #4]\n\t"
        "adds	r6, r6, r5\n\t"
        "adcs	r8, r8, r4\n\t"
        "adc	%[ca], %[ca], #0\n\t"
        "str	r6, [r10]\n\t"
        "str	r8, [r10, #4]\n\t"
        /* Next word in a */
        "sub	r10, r10, #120\n\t"
        "cmp	r10, r11\n\t"
        "blt	1b\n\t"
        "mov	%[a], r10\n\t"
        "mov	%[m], r12\n\t"
        : [ca] "+r" (ca), [a] "+r" (a)
        : [m] "r" (m), [mp] "r" (mp)
        : "memory", "r4", "r5", "r6", "r8", "r9", "r10", "r11", "r12", "r14"
    );

    sp_2048_cond_sub_32(a - 32, a, m, (sp_digit)0 - ca);
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
static void sp_2048_mont_mul_32(sp_digit* r, const sp_digit* a, const sp_digit* b,
        const sp_digit* m, sp_digit mp)
{
    sp_2048_mul_32(r, a, b);
    sp_2048_mont_reduce_32(r, m, mp);
}

/* Square the Montgomery form number. (r = a * a mod m)
 *
 * r   Result of squaring.
 * a   Number to square in Montogmery form.
 * m   Modulus (prime).
 * mp  Montogmery mulitplier.
 */
static void sp_2048_mont_sqr_32(sp_digit* r, const sp_digit* a, const sp_digit* m,
        sp_digit mp)
{
    sp_2048_sqr_32(r, a);
    sp_2048_mont_reduce_32(r, m, mp);
}

/* Mul a by digit b into r. (r = a * b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A single precision digit.
 */
SP_NOINLINE static void sp_2048_mul_d_32(sp_digit* r, const sp_digit* a,
        sp_digit b)
{
    __asm__ __volatile__ (
        "add	r9, %[a], #128\n\t"
        /* A[0] * B */
        "ldr	r6, [%[a]], #4\n\t"
        "umull	r5, r3, r6, %[b]\n\t"
        "mov	r4, #0\n\t"
        "str	r5, [%[r]], #4\n\t"
        /* A[0] * B - Done */
        "\n1:\n\t"
        "mov	r5, #0\n\t"
        /* A[] * B */
        "ldr	r6, [%[a]], #4\n\t"
        "umull	r6, r8, r6, %[b]\n\t"
        "adds	r3, r3, r6\n\t"
        "adcs 	r4, r4, r8\n\t"
        "adc	r5, r5, #0\n\t"
        /* A[] * B - Done */
        "str	r3, [%[r]], #4\n\t"
        "mov	r3, r4\n\t"
        "mov	r4, r5\n\t"
        "cmp	%[a], r9\n\t"
        "blt	1b\n\t"
        "str	r3, [%[r]]\n\t"
        : [r] "+r" (r), [a] "+r" (a)
        : [b] "r" (b)
        : "memory", "r3", "r4", "r5", "r6", "r8", "r9"
    );
}

/* Divide the double width number (d1|d0) by the dividend. (d1|d0 / div)
 *
 * d1   The high order half of the number to divide.
 * d0   The low order half of the number to divide.
 * div  The dividend.
 * returns the result of the division.
 *
 * Note that this is an approximate div. It may give an answer 1 larger.
 */
SP_NOINLINE static sp_digit div_2048_word_32(sp_digit d1, sp_digit d0,
        sp_digit div)
{
    sp_digit r = 0;

    __asm__ __volatile__ (
        "lsr	r6, %[div], #16\n\t"
        "add	r6, r6, #1\n\t"
        "udiv	r4, %[d1], r6\n\t"
        "lsl	r8, r4, #16\n\t"
        "umull	r4, r5, %[div], r8\n\t"
        "subs	%[d0], %[d0], r4\n\t"
        "sbc	%[d1], %[d1], r5\n\t"
        "udiv	r5, %[d1], r6\n\t"
        "lsl	r4, r5, #16\n\t"
        "add	r8, r8, r4\n\t"
        "umull	r4, r5, %[div], r4\n\t"
        "subs	%[d0], %[d0], r4\n\t"
        "sbc	%[d1], %[d1], r5\n\t"
        "lsl	r4, %[d1], #16\n\t"
        "orr	r4, r4, %[d0], lsr #16\n\t"
        "udiv	r4, r4, r6\n\t"
        "add	r8, r8, r4\n\t"
        "umull	r4, r5, %[div], r4\n\t"
        "subs	%[d0], %[d0], r4\n\t"
        "sbc	%[d1], %[d1], r5\n\t"
        "lsl	r4, %[d1], #16\n\t"
        "orr	r4, r4, %[d0], lsr #16\n\t"
        "udiv	r4, r4, r6\n\t"
        "add	r8, r8, r4\n\t"
        "umull	r4, r5, %[div], r4\n\t"
        "subs	%[d0], %[d0], r4\n\t"
        "sbc	%[d1], %[d1], r5\n\t"
        "udiv	r4, %[d0], %[div]\n\t"
        "add	r8, r8, r4\n\t"
        "mov	%[r], r8\n\t"
        : [r] "+r" (r)
        : [d1] "r" (d1), [d0] "r" (d0), [div] "r" (div)
        : "r4", "r5", "r6", "r8"
    );
    return r;
}

/* Compare a with b in constant time.
 *
 * a  A single precision integer.
 * b  A single precision integer.
 * return -ve, 0 or +ve if a is less than, equal to or greater than b
 * respectively.
 */
SP_NOINLINE static int32_t sp_2048_cmp_32(const sp_digit* a, const sp_digit* b)
{
    sp_digit r = 0;


    __asm__ __volatile__ (
        "mov	r3, #0\n\t"
        "mvn	r3, r3\n\t"
        "mov	r6, #124\n\t"
        "\n1:\n\t"
        "ldr	r8, [%[a], r6]\n\t"
        "ldr	r5, [%[b], r6]\n\t"
        "and	r8, r8, r3\n\t"
        "and	r5, r5, r3\n\t"
        "mov	r4, r8\n\t"
        "subs	r8, r8, r5\n\t"
        "sbc	r8, r8, r8\n\t"
        "add	%[r], %[r], r8\n\t"
        "mvn	r8, r8\n\t"
        "and	r3, r3, r8\n\t"
        "subs	r5, r5, r4\n\t"
        "sbc	r8, r8, r8\n\t"
        "sub	%[r], %[r], r8\n\t"
        "mvn	r8, r8\n\t"
        "and	r3, r3, r8\n\t"
        "sub	r6, r6, #4\n\t"
        "cmp	r6, #0\n\t"
        "bge	1b\n\t"
        : [r] "+r" (r)
        : [a] "r" (a), [b] "r" (b)
        : "r3", "r4", "r5", "r6", "r8"
    );

    return r;
}

/* Divide d in a and put remainder into r (m*d + r = a)
 * m is not calculated as it is not needed at this time.
 *
 * a  Nmber to be divided.
 * d  Number to divide with.
 * m  Multiplier result.
 * r  Remainder from the division.
 * returns MP_OKAY indicating success.
 */
static WC_INLINE int sp_2048_div_32(const sp_digit* a, const sp_digit* d, sp_digit* m,
        sp_digit* r)
{
    sp_digit t1[64], t2[33];
    sp_digit div, r1;
    int i;

    (void)m;

    div = d[31];
    XMEMCPY(t1, a, sizeof(*t1) * 2 * 32);
    for (i=31; i>=0; i--) {
        r1 = div_2048_word_32(t1[32 + i], t1[32 + i - 1], div);

        sp_2048_mul_d_32(t2, d, r1);
        t1[32 + i] += sp_2048_sub_in_place_32(&t1[i], t2);
        t1[32 + i] -= t2[32];
        sp_2048_mask_32(t2, d, t1[32 + i]);
        t1[32 + i] += sp_2048_add_32(&t1[i], &t1[i], t2);
        sp_2048_mask_32(t2, d, t1[32 + i]);
        t1[32 + i] += sp_2048_add_32(&t1[i], &t1[i], t2);
    }

    r1 = sp_2048_cmp_32(t1, d) >= 0;
    sp_2048_cond_sub_32(r, t1, d, (sp_digit)0 - r1);

    return MP_OKAY;
}

/* Reduce a modulo m into r. (r = a mod m)
 *
 * r  A single precision number that is the reduced result.
 * a  A single precision number that is to be reduced.
 * m  A single precision number that is the modulus to reduce with.
 * returns MP_OKAY indicating success.
 */
static WC_INLINE int sp_2048_mod_32(sp_digit* r, const sp_digit* a, const sp_digit* m)
{
    return sp_2048_div_32(a, m, NULL, r);
}

#ifdef WOLFSSL_SP_SMALL
/* Modular exponentiate a to the e mod m. (r = a^e mod m)
 *
 * r     A single precision number that is the result of the operation.
 * a     A single precision number being exponentiated.
 * e     A single precision number that is the exponent.
 * bits  The number of bits in the exponent.
 * m     A single precision number that is the modulus.
 * returns 0 on success and MEMORY_E on dynamic memory allocation failure.
 */
static int sp_2048_mod_exp_32(sp_digit* r, const sp_digit* a, const sp_digit* e,
        int bits, const sp_digit* m, int reduceA)
{
#if defined(WOLFSSL_SMALL_STACK) && !defined(WOLFSSL_SP_NO_MALLOC)
    sp_digit* td;
#else
    sp_digit td[16 * 64];
#endif
    sp_digit* t[16];
    sp_digit* norm;
    sp_digit mp = 1;
    sp_digit n;
    sp_digit mask;
    int i;
    int c, y;
    int err = MP_OKAY;

#if defined(WOLFSSL_SMALL_STACK) && !defined(WOLFSSL_SP_NO_MALLOC)
    td = (sp_digit*)XMALLOC(sizeof(sp_digit) * (16 * 64), NULL,
                            DYNAMIC_TYPE_TMP_BUFFER);
    if (td == NULL) {
        err = MEMORY_E;
    }
#endif

    if (err == MP_OKAY) {
        norm = td;
        for (i=0; i<16; i++) {
#if defined(WOLFSSL_SMALL_STACK) && !defined(WOLFSSL_SP_NO_MALLOC)
            t[i] = td + i * 64;
#else
            t[i] = &td[i * 64];
#endif
        }

        sp_2048_mont_setup(m, &mp);
        sp_2048_mont_norm_32(norm, m);

        XMEMSET(t[1], 0, sizeof(sp_digit) * 32U);
        if (reduceA != 0) {
            err = sp_2048_mod_32(t[1] + 32, a, m);
            if (err == MP_OKAY) {
                err = sp_2048_mod_32(t[1], t[1], m);
            }
        }
        else {
            XMEMCPY(t[1] + 32, a, sizeof(sp_digit) * 32);
            err = sp_2048_mod_32(t[1], t[1], m);
        }
    }

    if (err == MP_OKAY) {
        sp_2048_mont_sqr_32(t[ 2], t[ 1], m, mp);
        sp_2048_mont_mul_32(t[ 3], t[ 2], t[ 1], m, mp);
        sp_2048_mont_sqr_32(t[ 4], t[ 2], m, mp);
        sp_2048_mont_mul_32(t[ 5], t[ 3], t[ 2], m, mp);
        sp_2048_mont_sqr_32(t[ 6], t[ 3], m, mp);
        sp_2048_mont_mul_32(t[ 7], t[ 4], t[ 3], m, mp);
        sp_2048_mont_sqr_32(t[ 8], t[ 4], m, mp);
        sp_2048_mont_mul_32(t[ 9], t[ 5], t[ 4], m, mp);
        sp_2048_mont_sqr_32(t[10], t[ 5], m, mp);
        sp_2048_mont_mul_32(t[11], t[ 6], t[ 5], m, mp);
        sp_2048_mont_sqr_32(t[12], t[ 6], m, mp);
        sp_2048_mont_mul_32(t[13], t[ 7], t[ 6], m, mp);
        sp_2048_mont_sqr_32(t[14], t[ 7], m, mp);
        sp_2048_mont_mul_32(t[15], t[ 8], t[ 7], m, mp);

        i = (bits - 1) / 32;
        n = e[i--];
        c = bits & 31;
        if (c == 0) {
            c = 32;
        }
        c -= bits % 4;
        if (c == 32) {
            c = 28;
        }
        y = (int)(n >> c);
        n <<= 32 - c;
        XMEMCPY(r, t[y], sizeof(sp_digit) * 32);
        for (; i>=0 || c>=4; ) {
            if (c == 0) {
                n = e[i--];
                y = n >> 28;
                n <<= 4;
                c = 28;
            }
            else if (c < 4) {
                y = n >> 28;
                n = e[i--];
                c = 4 - c;
                y |= n >> (32 - c);
                n <<= c;
                c = 32 - c;
            }
            else {
                y = (n >> 28) & 0xf;
                n <<= 4;
                c -= 4;
            }

            sp_2048_mont_sqr_32(r, r, m, mp);
            sp_2048_mont_sqr_32(r, r, m, mp);
            sp_2048_mont_sqr_32(r, r, m, mp);
            sp_2048_mont_sqr_32(r, r, m, mp);

            sp_2048_mont_mul_32(r, r, t[y], m, mp);
        }

        XMEMSET(&r[32], 0, sizeof(sp_digit) * 32U);
        sp_2048_mont_reduce_32(r, m, mp);

        mask = 0 - (sp_2048_cmp_32(r, m) >= 0);
        sp_2048_cond_sub_32(r, r, m, mask);
    }

#if defined(WOLFSSL_SMALL_STACK) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (td != NULL) {
        XFREE(td, NULL, DYNAMIC_TYPE_TMP_BUFFER);
    }
#endif

    return err;
}
#else
/* Modular exponentiate a to the e mod m. (r = a^e mod m)
 *
 * r     A single precision number that is the result of the operation.
 * a     A single precision number being exponentiated.
 * e     A single precision number that is the exponent.
 * bits  The number of bits in the exponent.
 * m     A single precision number that is the modulus.
 * returns 0 on success and MEMORY_E on dynamic memory allocation failure.
 */
static int sp_2048_mod_exp_32(sp_digit* r, const sp_digit* a, const sp_digit* e,
        int bits, const sp_digit* m, int reduceA)
{
#if defined(WOLFSSL_SMALL_STACK) && !defined(WOLFSSL_SP_NO_MALLOC)
    sp_digit* td;
#else
    sp_digit td[32 * 64];
#endif
    sp_digit* t[32];
    sp_digit* norm;
    sp_digit mp = 1;
    sp_digit n;
    sp_digit mask;
    int i;
    int c, y;
    int err = MP_OKAY;

#if defined(WOLFSSL_SMALL_STACK) && !defined(WOLFSSL_SP_NO_MALLOC)
    td = (sp_digit*)XMALLOC(sizeof(sp_digit) * (32 * 64), NULL,
                            DYNAMIC_TYPE_TMP_BUFFER);
    if (td == NULL) {
        err = MEMORY_E;
    }
#endif

    if (err == MP_OKAY) {
        norm = td;
        for (i=0; i<32; i++) {
#if defined(WOLFSSL_SMALL_STACK) && !defined(WOLFSSL_SP_NO_MALLOC)
            t[i] = td + i * 64;
#else
            t[i] = &td[i * 64];
#endif
        }

        sp_2048_mont_setup(m, &mp);
        sp_2048_mont_norm_32(norm, m);

        XMEMSET(t[1], 0, sizeof(sp_digit) * 32U);
        if (reduceA != 0) {
            err = sp_2048_mod_32(t[1] + 32, a, m);
            if (err == MP_OKAY) {
                err = sp_2048_mod_32(t[1], t[1], m);
            }
        }
        else {
            XMEMCPY(t[1] + 32, a, sizeof(sp_digit) * 32);
            err = sp_2048_mod_32(t[1], t[1], m);
        }
    }

    if (err == MP_OKAY) {
        sp_2048_mont_sqr_32(t[ 2], t[ 1], m, mp);
        sp_2048_mont_mul_32(t[ 3], t[ 2], t[ 1], m, mp);
        sp_2048_mont_sqr_32(t[ 4], t[ 2], m, mp);
        sp_2048_mont_mul_32(t[ 5], t[ 3], t[ 2], m, mp);
        sp_2048_mont_sqr_32(t[ 6], t[ 3], m, mp);
        sp_2048_mont_mul_32(t[ 7], t[ 4], t[ 3], m, mp);
        sp_2048_mont_sqr_32(t[ 8], t[ 4], m, mp);
        sp_2048_mont_mul_32(t[ 9], t[ 5], t[ 4], m, mp);
        sp_2048_mont_sqr_32(t[10], t[ 5], m, mp);
        sp_2048_mont_mul_32(t[11], t[ 6], t[ 5], m, mp);
        sp_2048_mont_sqr_32(t[12], t[ 6], m, mp);
        sp_2048_mont_mul_32(t[13], t[ 7], t[ 6], m, mp);
        sp_2048_mont_sqr_32(t[14], t[ 7], m, mp);
        sp_2048_mont_mul_32(t[15], t[ 8], t[ 7], m, mp);
        sp_2048_mont_sqr_32(t[16], t[ 8], m, mp);
        sp_2048_mont_mul_32(t[17], t[ 9], t[ 8], m, mp);
        sp_2048_mont_sqr_32(t[18], t[ 9], m, mp);
        sp_2048_mont_mul_32(t[19], t[10], t[ 9], m, mp);
        sp_2048_mont_sqr_32(t[20], t[10], m, mp);
        sp_2048_mont_mul_32(t[21], t[11], t[10], m, mp);
        sp_2048_mont_sqr_32(t[22], t[11], m, mp);
        sp_2048_mont_mul_32(t[23], t[12], t[11], m, mp);
        sp_2048_mont_sqr_32(t[24], t[12], m, mp);
        sp_2048_mont_mul_32(t[25], t[13], t[12], m, mp);
        sp_2048_mont_sqr_32(t[26], t[13], m, mp);
        sp_2048_mont_mul_32(t[27], t[14], t[13], m, mp);
        sp_2048_mont_sqr_32(t[28], t[14], m, mp);
        sp_2048_mont_mul_32(t[29], t[15], t[14], m, mp);
        sp_2048_mont_sqr_32(t[30], t[15], m, mp);
        sp_2048_mont_mul_32(t[31], t[16], t[15], m, mp);

        i = (bits - 1) / 32;
        n = e[i--];
        c = bits & 31;
        if (c == 0) {
            c = 32;
        }
        c -= bits % 5;
        if (c == 32) {
            c = 27;
        }
        y = (int)(n >> c);
        n <<= 32 - c;
        XMEMCPY(r, t[y], sizeof(sp_digit) * 32);
        for (; i>=0 || c>=5; ) {
            if (c == 0) {
                n = e[i--];
                y = n >> 27;
                n <<= 5;
                c = 27;
            }
            else if (c < 5) {
                y = n >> 27;
                n = e[i--];
                c = 5 - c;
                y |= n >> (32 - c);
                n <<= c;
                c = 32 - c;
            }
            else {
                y = (n >> 27) & 0x1f;
                n <<= 5;
                c -= 5;
            }

            sp_2048_mont_sqr_32(r, r, m, mp);
            sp_2048_mont_sqr_32(r, r, m, mp);
            sp_2048_mont_sqr_32(r, r, m, mp);
            sp_2048_mont_sqr_32(r, r, m, mp);
            sp_2048_mont_sqr_32(r, r, m, mp);

            sp_2048_mont_mul_32(r, r, t[y], m, mp);
        }

        XMEMSET(&r[32], 0, sizeof(sp_digit) * 32U);
        sp_2048_mont_reduce_32(r, m, mp);

        mask = 0 - (sp_2048_cmp_32(r, m) >= 0);
        sp_2048_cond_sub_32(r, r, m, mask);
    }

#if defined(WOLFSSL_SMALL_STACK) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (td != NULL) {
        XFREE(td, NULL, DYNAMIC_TYPE_TMP_BUFFER);
    }
#endif

    return err;
}
#endif /* WOLFSSL_SP_SMALL */

#endif /* (WOLFSSL_HAVE_SP_RSA || WOLFSSL_HAVE_SP_DH) && !WOLFSSL_RSA_PUBLIC_ONLY */

#if defined(WOLFSSL_HAVE_SP_RSA) || defined(WOLFSSL_HAVE_SP_DH)
/* r = 2^n mod m where n is the number of bits to reduce by.
 * Given m must be 2048 bits, just need to subtract.
 *
 * r  A single precision number.
 * m  A single precision number.
 */
static void sp_2048_mont_norm_64(sp_digit* r, const sp_digit* m)
{
    XMEMSET(r, 0, sizeof(sp_digit) * 64);

    /* r = 2^n mod m */
    sp_2048_sub_in_place_64(r, m);
}

#endif /* WOLFSSL_HAVE_SP_RSA || WOLFSSL_HAVE_SP_DH */
/* Conditionally subtract b from a using the mask m.
 * m is -1 to subtract and 0 when not copying.
 *
 * r  A single precision number representing condition subtract result.
 * a  A single precision number to subtract from.
 * b  A single precision number to subtract.
 * m  Mask value to apply.
 */
SP_NOINLINE static sp_digit sp_2048_cond_sub_64(sp_digit* r, const sp_digit* a,
        const sp_digit* b, sp_digit m)
{
    sp_digit c = 0;

    __asm__ __volatile__ (
        "mov	r5, #1\n\t"
        "lsl	r5, r5, #8\n\t"
        "mov	r9, r5\n\t"
        "mov	r8, #0\n\t"
        "\n1:\n\t"
        "ldr	r6, [%[b], r8]\n\t"
        "and	r6, r6, %[m]\n\t"
        "mov	r5, #0\n\t"
        "subs	r5, r5, %[c]\n\t"
        "ldr	r5, [%[a], r8]\n\t"
        "sbcs	r5, r5, r6\n\t"
        "sbcs	%[c], %[c], %[c]\n\t"
        "str	r5, [%[r], r8]\n\t"
        "add	r8, r8, #4\n\t"
        "cmp	r8, r9\n\t"
        "blt	1b\n\t"
        : [c] "+r" (c)
        : [r] "r" (r), [a] "r" (a), [b] "r" (b), [m] "r" (m)
        : "memory", "r5", "r6", "r8", "r9"
    );

    return c;
}

/* Reduce the number back to 2048 bits using Montgomery reduction.
 *
 * a   A single precision number to reduce in place.
 * m   The single precision number representing the modulus.
 * mp  The digit representing the negative inverse of m mod 2^n.
 */
SP_NOINLINE static void sp_2048_mont_reduce_64(sp_digit* a, const sp_digit* m,
        sp_digit mp)
{
    sp_digit ca = 0;

    __asm__ __volatile__ (
        "mov	r9, %[mp]\n\t"
        "mov	r12, %[m]\n\t"
        "mov	r10, %[a]\n\t"
        "mov	r4, #0\n\t"
        "add	r11, r10, #256\n\t"
        "\n1:\n\t"
        /* mu = a[i] * mp */
        "mov	%[mp], r9\n\t"
        "ldr	%[a], [r10]\n\t"
        "mul	%[mp], %[mp], %[a]\n\t"
        "mov	%[m], r12\n\t"
        "add	r14, r10, #248\n\t"
        "\n2:\n\t"
        /* a[i+j] += m[j] * mu */
        "ldr	%[a], [r10]\n\t"
        "mov	r5, #0\n\t"
        /* Multiply m[j] and mu - Start */
        "ldr	r8, [%[m]], #4\n\t"
        "umull	r6, r8, %[mp], r8\n\t"
        "adds	%[a], %[a], r6\n\t"
        "adc	r5, r5, r8\n\t"
        /* Multiply m[j] and mu - Done */
        "adds	r4, r4, %[a]\n\t"
        "adc	r5, r5, #0\n\t"
        "str	r4, [r10], #4\n\t"
        /* a[i+j+1] += m[j+1] * mu */
        "ldr	%[a], [r10]\n\t"
        "mov	r4, #0\n\t"
        /* Multiply m[j] and mu - Start */
        "ldr	r8, [%[m]], #4\n\t"
        "umull	r6, r8, %[mp], r8\n\t"
        "adds	%[a], %[a], r6\n\t"
        "adc	r4, r4, r8\n\t"
        /* Multiply m[j] and mu - Done */
        "adds	r5, r5, %[a]\n\t"
        "adc	r4, r4, #0\n\t"
        "str	r5, [r10], #4\n\t"
        "cmp	r10, r14\n\t"
        "blt	2b\n\t"
        /* a[i+62] += m[62] * mu */
        "ldr	%[a], [r10]\n\t"
        "mov	r5, #0\n\t"
        /* Multiply m[j] and mu - Start */
        "ldr	r8, [%[m]], #4\n\t"
        "umull	r6, r8, %[mp], r8\n\t"
        "adds	%[a], %[a], r6\n\t"
        "adc	r5, r5, r8\n\t"
        /* Multiply m[j] and mu - Done */
        "adds	r4, r4, %[a]\n\t"
        "adc	r5, r5, #0\n\t"
        "str	r4, [r10], #4\n\t"
        /* a[i+63] += m[63] * mu */
        "mov	r4, %[ca]\n\t"
        "mov	%[ca], #0\n\t"
        /* Multiply m[63] and mu - Start */
        "ldr	r8, [%[m]]\n\t"
        "umull	r6, r8, %[mp], r8\n\t"
        "adds	r5, r5, r6\n\t"
        "adcs 	r4, r4, r8\n\t"
        "adc	%[ca], %[ca], #0\n\t"
        /* Multiply m[63] and mu - Done */
        "ldr	r6, [r10]\n\t"
        "ldr	r8, [r10, #4]\n\t"
        "adds	r6, r6, r5\n\t"
        "adcs	r8, r8, r4\n\t"
        "adc	%[ca], %[ca], #0\n\t"
        "str	r6, [r10]\n\t"
        "str	r8, [r10, #4]\n\t"
        /* Next word in a */
        "sub	r10, r10, #248\n\t"
        "cmp	r10, r11\n\t"
        "blt	1b\n\t"
        "mov	%[a], r10\n\t"
        "mov	%[m], r12\n\t"
        : [ca] "+r" (ca), [a] "+r" (a)
        : [m] "r" (m), [mp] "r" (mp)
        : "memory", "r4", "r5", "r6", "r8", "r9", "r10", "r11", "r12", "r14"
    );

    sp_2048_cond_sub_64(a - 64, a, m, (sp_digit)0 - ca);
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
static void sp_2048_mont_mul_64(sp_digit* r, const sp_digit* a, const sp_digit* b,
        const sp_digit* m, sp_digit mp)
{
    sp_2048_mul_64(r, a, b);
    sp_2048_mont_reduce_64(r, m, mp);
}

/* Square the Montgomery form number. (r = a * a mod m)
 *
 * r   Result of squaring.
 * a   Number to square in Montogmery form.
 * m   Modulus (prime).
 * mp  Montogmery mulitplier.
 */
static void sp_2048_mont_sqr_64(sp_digit* r, const sp_digit* a, const sp_digit* m,
        sp_digit mp)
{
    sp_2048_sqr_64(r, a);
    sp_2048_mont_reduce_64(r, m, mp);
}

/* Divide the double width number (d1|d0) by the dividend. (d1|d0 / div)
 *
 * d1   The high order half of the number to divide.
 * d0   The low order half of the number to divide.
 * div  The dividend.
 * returns the result of the division.
 *
 * Note that this is an approximate div. It may give an answer 1 larger.
 */
SP_NOINLINE static sp_digit div_2048_word_64(sp_digit d1, sp_digit d0,
        sp_digit div)
{
    sp_digit r = 0;

    __asm__ __volatile__ (
        "lsr	r6, %[div], #16\n\t"
        "add	r6, r6, #1\n\t"
        "udiv	r4, %[d1], r6\n\t"
        "lsl	r8, r4, #16\n\t"
        "umull	r4, r5, %[div], r8\n\t"
        "subs	%[d0], %[d0], r4\n\t"
        "sbc	%[d1], %[d1], r5\n\t"
        "udiv	r5, %[d1], r6\n\t"
        "lsl	r4, r5, #16\n\t"
        "add	r8, r8, r4\n\t"
        "umull	r4, r5, %[div], r4\n\t"
        "subs	%[d0], %[d0], r4\n\t"
        "sbc	%[d1], %[d1], r5\n\t"
        "lsl	r4, %[d1], #16\n\t"
        "orr	r4, r4, %[d0], lsr #16\n\t"
        "udiv	r4, r4, r6\n\t"
        "add	r8, r8, r4\n\t"
        "umull	r4, r5, %[div], r4\n\t"
        "subs	%[d0], %[d0], r4\n\t"
        "sbc	%[d1], %[d1], r5\n\t"
        "lsl	r4, %[d1], #16\n\t"
        "orr	r4, r4, %[d0], lsr #16\n\t"
        "udiv	r4, r4, r6\n\t"
        "add	r8, r8, r4\n\t"
        "umull	r4, r5, %[div], r4\n\t"
        "subs	%[d0], %[d0], r4\n\t"
        "sbc	%[d1], %[d1], r5\n\t"
        "udiv	r4, %[d0], %[div]\n\t"
        "add	r8, r8, r4\n\t"
        "mov	%[r], r8\n\t"
        : [r] "+r" (r)
        : [d1] "r" (d1), [d0] "r" (d0), [div] "r" (div)
        : "r4", "r5", "r6", "r8"
    );
    return r;
}

/* AND m into each word of a and store in r.
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * m  Mask to AND against each digit.
 */
static void sp_2048_mask_64(sp_digit* r, const sp_digit* a, sp_digit m)
{
#ifdef WOLFSSL_SP_SMALL
    int i;

    for (i=0; i<64; i++) {
        r[i] = a[i] & m;
    }
#else
    int i;

    for (i = 0; i < 64; i += 8) {
        r[i+0] = a[i+0] & m;
        r[i+1] = a[i+1] & m;
        r[i+2] = a[i+2] & m;
        r[i+3] = a[i+3] & m;
        r[i+4] = a[i+4] & m;
        r[i+5] = a[i+5] & m;
        r[i+6] = a[i+6] & m;
        r[i+7] = a[i+7] & m;
    }
#endif
}

/* Compare a with b in constant time.
 *
 * a  A single precision integer.
 * b  A single precision integer.
 * return -ve, 0 or +ve if a is less than, equal to or greater than b
 * respectively.
 */
SP_NOINLINE static int32_t sp_2048_cmp_64(const sp_digit* a, const sp_digit* b)
{
    sp_digit r = 0;


    __asm__ __volatile__ (
        "mov	r3, #0\n\t"
        "mvn	r3, r3\n\t"
        "mov	r6, #252\n\t"
        "\n1:\n\t"
        "ldr	r8, [%[a], r6]\n\t"
        "ldr	r5, [%[b], r6]\n\t"
        "and	r8, r8, r3\n\t"
        "and	r5, r5, r3\n\t"
        "mov	r4, r8\n\t"
        "subs	r8, r8, r5\n\t"
        "sbc	r8, r8, r8\n\t"
        "add	%[r], %[r], r8\n\t"
        "mvn	r8, r8\n\t"
        "and	r3, r3, r8\n\t"
        "subs	r5, r5, r4\n\t"
        "sbc	r8, r8, r8\n\t"
        "sub	%[r], %[r], r8\n\t"
        "mvn	r8, r8\n\t"
        "and	r3, r3, r8\n\t"
        "sub	r6, r6, #4\n\t"
        "cmp	r6, #0\n\t"
        "bge	1b\n\t"
        : [r] "+r" (r)
        : [a] "r" (a), [b] "r" (b)
        : "r3", "r4", "r5", "r6", "r8"
    );

    return r;
}

/* Divide d in a and put remainder into r (m*d + r = a)
 * m is not calculated as it is not needed at this time.
 *
 * a  Nmber to be divided.
 * d  Number to divide with.
 * m  Multiplier result.
 * r  Remainder from the division.
 * returns MP_OKAY indicating success.
 */
static WC_INLINE int sp_2048_div_64(const sp_digit* a, const sp_digit* d, sp_digit* m,
        sp_digit* r)
{
    sp_digit t1[128], t2[65];
    sp_digit div, r1;
    int i;

    (void)m;

    div = d[63];
    XMEMCPY(t1, a, sizeof(*t1) * 2 * 64);
    for (i=63; i>=0; i--) {
        r1 = div_2048_word_64(t1[64 + i], t1[64 + i - 1], div);

        sp_2048_mul_d_64(t2, d, r1);
        t1[64 + i] += sp_2048_sub_in_place_64(&t1[i], t2);
        t1[64 + i] -= t2[64];
        sp_2048_mask_64(t2, d, t1[64 + i]);
        t1[64 + i] += sp_2048_add_64(&t1[i], &t1[i], t2);
        sp_2048_mask_64(t2, d, t1[64 + i]);
        t1[64 + i] += sp_2048_add_64(&t1[i], &t1[i], t2);
    }

    r1 = sp_2048_cmp_64(t1, d) >= 0;
    sp_2048_cond_sub_64(r, t1, d, (sp_digit)0 - r1);

    return MP_OKAY;
}

/* Reduce a modulo m into r. (r = a mod m)
 *
 * r  A single precision number that is the reduced result.
 * a  A single precision number that is to be reduced.
 * m  A single precision number that is the modulus to reduce with.
 * returns MP_OKAY indicating success.
 */
static WC_INLINE int sp_2048_mod_64(sp_digit* r, const sp_digit* a, const sp_digit* m)
{
    return sp_2048_div_64(a, m, NULL, r);
}

/* Divide d in a and put remainder into r (m*d + r = a)
 * m is not calculated as it is not needed at this time.
 *
 * a  Nmber to be divided.
 * d  Number to divide with.
 * m  Multiplier result.
 * r  Remainder from the division.
 * returns MP_OKAY indicating success.
 */
static WC_INLINE int sp_2048_div_64_cond(const sp_digit* a, const sp_digit* d, sp_digit* m,
        sp_digit* r)
{
    sp_digit t1[128], t2[65];
    sp_digit div, r1;
    int i;

    (void)m;

    div = d[63];
    XMEMCPY(t1, a, sizeof(*t1) * 2 * 64);
    for (i=63; i>=0; i--) {
        r1 = div_2048_word_64(t1[64 + i], t1[64 + i - 1], div);

        sp_2048_mul_d_64(t2, d, r1);
        t1[64 + i] += sp_2048_sub_in_place_64(&t1[i], t2);
        t1[64 + i] -= t2[64];
        if (t1[64 + i] != 0) {
            t1[64 + i] += sp_2048_add_64(&t1[i], &t1[i], d);
            if (t1[64 + i] != 0)
                t1[64 + i] += sp_2048_add_64(&t1[i], &t1[i], d);
        }
    }

    r1 = sp_2048_cmp_64(t1, d) >= 0;
    sp_2048_cond_sub_64(r, t1, d, (sp_digit)0 - r1);

    return MP_OKAY;
}

/* Reduce a modulo m into r. (r = a mod m)
 *
 * r  A single precision number that is the reduced result.
 * a  A single precision number that is to be reduced.
 * m  A single precision number that is the modulus to reduce with.
 * returns MP_OKAY indicating success.
 */
static WC_INLINE int sp_2048_mod_64_cond(sp_digit* r, const sp_digit* a, const sp_digit* m)
{
    return sp_2048_div_64_cond(a, m, NULL, r);
}

#if (defined(WOLFSSL_HAVE_SP_RSA) && !defined(WOLFSSL_RSA_PUBLIC_ONLY)) || \
                                                     defined(WOLFSSL_HAVE_SP_DH)
#ifdef WOLFSSL_SP_SMALL
/* Modular exponentiate a to the e mod m. (r = a^e mod m)
 *
 * r     A single precision number that is the result of the operation.
 * a     A single precision number being exponentiated.
 * e     A single precision number that is the exponent.
 * bits  The number of bits in the exponent.
 * m     A single precision number that is the modulus.
 * returns 0 on success and MEMORY_E on dynamic memory allocation failure.
 */
static int sp_2048_mod_exp_64(sp_digit* r, const sp_digit* a, const sp_digit* e,
        int bits, const sp_digit* m, int reduceA)
{
#if defined(WOLFSSL_SMALL_STACK) && !defined(WOLFSSL_SP_NO_MALLOC)
    sp_digit* td;
#else
    sp_digit td[16 * 128];
#endif
    sp_digit* t[16];
    sp_digit* norm;
    sp_digit mp = 1;
    sp_digit n;
    sp_digit mask;
    int i;
    int c, y;
    int err = MP_OKAY;

#if defined(WOLFSSL_SMALL_STACK) && !defined(WOLFSSL_SP_NO_MALLOC)
    td = (sp_digit*)XMALLOC(sizeof(sp_digit) * (16 * 128), NULL,
                            DYNAMIC_TYPE_TMP_BUFFER);
    if (td == NULL) {
        err = MEMORY_E;
    }
#endif

    if (err == MP_OKAY) {
        norm = td;
        for (i=0; i<16; i++) {
#if defined(WOLFSSL_SMALL_STACK) && !defined(WOLFSSL_SP_NO_MALLOC)
            t[i] = td + i * 128;
#else
            t[i] = &td[i * 128];
#endif
        }

        sp_2048_mont_setup(m, &mp);
        sp_2048_mont_norm_64(norm, m);

        XMEMSET(t[1], 0, sizeof(sp_digit) * 64U);
        if (reduceA != 0) {
            err = sp_2048_mod_64(t[1] + 64, a, m);
            if (err == MP_OKAY) {
                err = sp_2048_mod_64(t[1], t[1], m);
            }
        }
        else {
            XMEMCPY(t[1] + 64, a, sizeof(sp_digit) * 64);
            err = sp_2048_mod_64(t[1], t[1], m);
        }
    }

    if (err == MP_OKAY) {
        sp_2048_mont_sqr_64(t[ 2], t[ 1], m, mp);
        sp_2048_mont_mul_64(t[ 3], t[ 2], t[ 1], m, mp);
        sp_2048_mont_sqr_64(t[ 4], t[ 2], m, mp);
        sp_2048_mont_mul_64(t[ 5], t[ 3], t[ 2], m, mp);
        sp_2048_mont_sqr_64(t[ 6], t[ 3], m, mp);
        sp_2048_mont_mul_64(t[ 7], t[ 4], t[ 3], m, mp);
        sp_2048_mont_sqr_64(t[ 8], t[ 4], m, mp);
        sp_2048_mont_mul_64(t[ 9], t[ 5], t[ 4], m, mp);
        sp_2048_mont_sqr_64(t[10], t[ 5], m, mp);
        sp_2048_mont_mul_64(t[11], t[ 6], t[ 5], m, mp);
        sp_2048_mont_sqr_64(t[12], t[ 6], m, mp);
        sp_2048_mont_mul_64(t[13], t[ 7], t[ 6], m, mp);
        sp_2048_mont_sqr_64(t[14], t[ 7], m, mp);
        sp_2048_mont_mul_64(t[15], t[ 8], t[ 7], m, mp);

        i = (bits - 1) / 32;
        n = e[i--];
        c = bits & 31;
        if (c == 0) {
            c = 32;
        }
        c -= bits % 4;
        if (c == 32) {
            c = 28;
        }
        y = (int)(n >> c);
        n <<= 32 - c;
        XMEMCPY(r, t[y], sizeof(sp_digit) * 64);
        for (; i>=0 || c>=4; ) {
            if (c == 0) {
                n = e[i--];
                y = n >> 28;
                n <<= 4;
                c = 28;
            }
            else if (c < 4) {
                y = n >> 28;
                n = e[i--];
                c = 4 - c;
                y |= n >> (32 - c);
                n <<= c;
                c = 32 - c;
            }
            else {
                y = (n >> 28) & 0xf;
                n <<= 4;
                c -= 4;
            }

            sp_2048_mont_sqr_64(r, r, m, mp);
            sp_2048_mont_sqr_64(r, r, m, mp);
            sp_2048_mont_sqr_64(r, r, m, mp);
            sp_2048_mont_sqr_64(r, r, m, mp);

            sp_2048_mont_mul_64(r, r, t[y], m, mp);
        }

        XMEMSET(&r[64], 0, sizeof(sp_digit) * 64U);
        sp_2048_mont_reduce_64(r, m, mp);

        mask = 0 - (sp_2048_cmp_64(r, m) >= 0);
        sp_2048_cond_sub_64(r, r, m, mask);
    }

#if defined(WOLFSSL_SMALL_STACK) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (td != NULL) {
        XFREE(td, NULL, DYNAMIC_TYPE_TMP_BUFFER);
    }
#endif

    return err;
}
#else
/* Modular exponentiate a to the e mod m. (r = a^e mod m)
 *
 * r     A single precision number that is the result of the operation.
 * a     A single precision number being exponentiated.
 * e     A single precision number that is the exponent.
 * bits  The number of bits in the exponent.
 * m     A single precision number that is the modulus.
 * returns 0 on success and MEMORY_E on dynamic memory allocation failure.
 */
static int sp_2048_mod_exp_64(sp_digit* r, const sp_digit* a, const sp_digit* e,
        int bits, const sp_digit* m, int reduceA)
{
#if defined(WOLFSSL_SMALL_STACK) && !defined(WOLFSSL_SP_NO_MALLOC)
    sp_digit* td;
#else
    sp_digit td[32 * 128];
#endif
    sp_digit* t[32];
    sp_digit* norm;
    sp_digit mp = 1;
    sp_digit n;
    sp_digit mask;
    int i;
    int c, y;
    int err = MP_OKAY;

#if defined(WOLFSSL_SMALL_STACK) && !defined(WOLFSSL_SP_NO_MALLOC)
    td = (sp_digit*)XMALLOC(sizeof(sp_digit) * (32 * 128), NULL,
                            DYNAMIC_TYPE_TMP_BUFFER);
    if (td == NULL) {
        err = MEMORY_E;
    }
#endif

    if (err == MP_OKAY) {
        norm = td;
        for (i=0; i<32; i++) {
#if defined(WOLFSSL_SMALL_STACK) && !defined(WOLFSSL_SP_NO_MALLOC)
            t[i] = td + i * 128;
#else
            t[i] = &td[i * 128];
#endif
        }

        sp_2048_mont_setup(m, &mp);
        sp_2048_mont_norm_64(norm, m);

        XMEMSET(t[1], 0, sizeof(sp_digit) * 64U);
        if (reduceA != 0) {
            err = sp_2048_mod_64(t[1] + 64, a, m);
            if (err == MP_OKAY) {
                err = sp_2048_mod_64(t[1], t[1], m);
            }
        }
        else {
            XMEMCPY(t[1] + 64, a, sizeof(sp_digit) * 64);
            err = sp_2048_mod_64(t[1], t[1], m);
        }
    }

    if (err == MP_OKAY) {
        sp_2048_mont_sqr_64(t[ 2], t[ 1], m, mp);
        sp_2048_mont_mul_64(t[ 3], t[ 2], t[ 1], m, mp);
        sp_2048_mont_sqr_64(t[ 4], t[ 2], m, mp);
        sp_2048_mont_mul_64(t[ 5], t[ 3], t[ 2], m, mp);
        sp_2048_mont_sqr_64(t[ 6], t[ 3], m, mp);
        sp_2048_mont_mul_64(t[ 7], t[ 4], t[ 3], m, mp);
        sp_2048_mont_sqr_64(t[ 8], t[ 4], m, mp);
        sp_2048_mont_mul_64(t[ 9], t[ 5], t[ 4], m, mp);
        sp_2048_mont_sqr_64(t[10], t[ 5], m, mp);
        sp_2048_mont_mul_64(t[11], t[ 6], t[ 5], m, mp);
        sp_2048_mont_sqr_64(t[12], t[ 6], m, mp);
        sp_2048_mont_mul_64(t[13], t[ 7], t[ 6], m, mp);
        sp_2048_mont_sqr_64(t[14], t[ 7], m, mp);
        sp_2048_mont_mul_64(t[15], t[ 8], t[ 7], m, mp);
        sp_2048_mont_sqr_64(t[16], t[ 8], m, mp);
        sp_2048_mont_mul_64(t[17], t[ 9], t[ 8], m, mp);
        sp_2048_mont_sqr_64(t[18], t[ 9], m, mp);
        sp_2048_mont_mul_64(t[19], t[10], t[ 9], m, mp);
        sp_2048_mont_sqr_64(t[20], t[10], m, mp);
        sp_2048_mont_mul_64(t[21], t[11], t[10], m, mp);
        sp_2048_mont_sqr_64(t[22], t[11], m, mp);
        sp_2048_mont_mul_64(t[23], t[12], t[11], m, mp);
        sp_2048_mont_sqr_64(t[24], t[12], m, mp);
        sp_2048_mont_mul_64(t[25], t[13], t[12], m, mp);
        sp_2048_mont_sqr_64(t[26], t[13], m, mp);
        sp_2048_mont_mul_64(t[27], t[14], t[13], m, mp);
        sp_2048_mont_sqr_64(t[28], t[14], m, mp);
        sp_2048_mont_mul_64(t[29], t[15], t[14], m, mp);
        sp_2048_mont_sqr_64(t[30], t[15], m, mp);
        sp_2048_mont_mul_64(t[31], t[16], t[15], m, mp);

        i = (bits - 1) / 32;
        n = e[i--];
        c = bits & 31;
        if (c == 0) {
            c = 32;
        }
        c -= bits % 5;
        if (c == 32) {
            c = 27;
        }
        y = (int)(n >> c);
        n <<= 32 - c;
        XMEMCPY(r, t[y], sizeof(sp_digit) * 64);
        for (; i>=0 || c>=5; ) {
            if (c == 0) {
                n = e[i--];
                y = n >> 27;
                n <<= 5;
                c = 27;
            }
            else if (c < 5) {
                y = n >> 27;
                n = e[i--];
                c = 5 - c;
                y |= n >> (32 - c);
                n <<= c;
                c = 32 - c;
            }
            else {
                y = (n >> 27) & 0x1f;
                n <<= 5;
                c -= 5;
            }

            sp_2048_mont_sqr_64(r, r, m, mp);
            sp_2048_mont_sqr_64(r, r, m, mp);
            sp_2048_mont_sqr_64(r, r, m, mp);
            sp_2048_mont_sqr_64(r, r, m, mp);
            sp_2048_mont_sqr_64(r, r, m, mp);

            sp_2048_mont_mul_64(r, r, t[y], m, mp);
        }

        XMEMSET(&r[64], 0, sizeof(sp_digit) * 64U);
        sp_2048_mont_reduce_64(r, m, mp);

        mask = 0 - (sp_2048_cmp_64(r, m) >= 0);
        sp_2048_cond_sub_64(r, r, m, mask);
    }

#if defined(WOLFSSL_SMALL_STACK) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (td != NULL) {
        XFREE(td, NULL, DYNAMIC_TYPE_TMP_BUFFER);
    }
#endif

    return err;
}
#endif /* WOLFSSL_SP_SMALL */
#endif /* (WOLFSSL_HAVE_SP_RSA && !WOLFSSL_RSA_PUBLIC_ONLY) || WOLFSSL_HAVE_SP_DH */

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
#if (!defined(WOLFSSL_SP_SMALL) && !defined(WOLFSSL_SMALL_STACK)) || defined(WOLFSSL_SP_NO_MALLOC)
    sp_digit a[128], m[64], r[128];
#else
    sp_digit* d = NULL;
    sp_digit* a = NULL;
    sp_digit* m = NULL;
    sp_digit* r = NULL;
#endif
    sp_digit *ah = NULL;
    sp_digit e[1];
    int err = MP_OKAY;

    if (*outLen < 256)
        err = MP_TO_E;
    if (err == MP_OKAY && (mp_count_bits(em) > 32 || inLen > 256 ||
                                                     mp_count_bits(mm) != 2048))
        err = MP_READ_E;

#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (err == MP_OKAY) {
        d = (sp_digit*)XMALLOC(sizeof(sp_digit) * 64 * 5, NULL,
                                                              DYNAMIC_TYPE_RSA);
        if (d == NULL)
            err = MEMORY_E;
    }

    if (err == MP_OKAY) {
        a = d;
        r = a + 64 * 2;
        m = r + 64 * 2;
    }
#endif

    if (err == MP_OKAY) {
        ah = a + 64;

        sp_2048_from_bin(ah, 64, in, inLen);
#if DIGIT_BIT >= 32
        e[0] = em->dp[0];
#else
        e[0] = em->dp[0];
        if (em->used > 1) {
            e[0] |= ((sp_digit)em->dp[1]) << DIGIT_BIT;
        }
#endif
        if (e[0] == 0) {
            err = MP_EXPTMOD_E;
        }
    }
    if (err == MP_OKAY) {
        sp_2048_from_mp(m, 64, mm);

        if (e[0] == 0x3) {
            if (err == MP_OKAY) {
                sp_2048_sqr_64(r, ah);
                err = sp_2048_mod_64_cond(r, r, m);
            }
            if (err == MP_OKAY) {
                sp_2048_mul_64(r, ah, r);
                err = sp_2048_mod_64_cond(r, r, m);
            }
        }
        else {
            int i;
            sp_digit mp;

            sp_2048_mont_setup(m, &mp);

            /* Convert to Montgomery form. */
            XMEMSET(a, 0, sizeof(sp_digit) * 64);
            err = sp_2048_mod_64_cond(a, a, m);

            if (err == MP_OKAY) {
                for (i = 31; i >= 0; i--) {
                    if (e[0] >> i) {
                        break;
                    }
                }

                XMEMCPY(r, a, sizeof(sp_digit) * 64);
                for (i--; i>=0; i--) {
                    sp_2048_mont_sqr_64(r, r, m, mp);
                    if (((e[0] >> i) & 1) == 1) {
                        sp_2048_mont_mul_64(r, r, a, m, mp);
                    }
                }
                XMEMSET(&r[64], 0, sizeof(sp_digit) * 64);
                sp_2048_mont_reduce_64(r, m, mp);

                for (i = 63; i > 0; i--) {
                    if (r[i] != m[i]) {
                        break;
                    }
                }
                if (r[i] >= m[i]) {
                    sp_2048_sub_in_place_64(r, m);
                }
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
}

#ifndef WOLFSSL_RSA_PUBLIC_ONLY
/* Conditionally add a and b using the mask m.
 * m is -1 to add and 0 when not.
 *
 * r  A single precision number representing conditional add result.
 * a  A single precision number to add with.
 * b  A single precision number to add.
 * m  Mask value to apply.
 */
SP_NOINLINE static sp_digit sp_2048_cond_add_32(sp_digit* r, const sp_digit* a, const sp_digit* b,
        sp_digit m)
{
    sp_digit c = 0;

    __asm__ __volatile__ (
        "mov	r5, #128\n\t"
        "mov	r9, r5\n\t"
        "mov	r8, #0\n\t"
        "\n1:\n\t"
        "ldr	r6, [%[b], r8]\n\t"
        "and	r6, r6, %[m]\n\t"
        "adds	r5, %[c], #-1\n\t"
        "ldr	r5, [%[a], r8]\n\t"
        "adcs	r5, r5, r6\n\t"
        "mov	%[c], #0\n\t"
        "adcs	%[c], %[c], %[c]\n\t"
        "str	r5, [%[r], r8]\n\t"
        "add	r8, r8, #4\n\t"
        "cmp	r8, r9\n\t"
        "blt	1b\n\t"
        : [c] "+r" (c)
        : [r] "r" (r), [a] "r" (a), [b] "r" (b), [m] "r" (m)
        : "memory", "r5", "r6", "r8", "r9"
    );

    return c;
}

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
        d = (sp_digit*)XMALLOC(sizeof(sp_digit) * 64 * 4, NULL,
                                                              DYNAMIC_TYPE_RSA);
        if (d == NULL) {
            err = MEMORY_E;
        }
    }
    if (err == MP_OKAY) {
        a = d + 64;
        m = a + 128;
        r = a;

        sp_2048_from_bin(a, 64, in, inLen);
        sp_2048_from_mp(d, 64, dm);
        sp_2048_from_mp(m, 64, mm);
        err = sp_2048_mod_exp_64(r, a, d, 2048, m, 0);
    }
    if (err == MP_OKAY) {
        sp_2048_to_bin(r, out);
        *outLen = 256;
    }

    if (d != NULL) {
        XMEMSET(d, 0, sizeof(sp_digit) * 64);
        XFREE(d, NULL, DYNAMIC_TYPE_RSA);
    }

    return err;
#else
#if (!defined(WOLFSSL_SP_SMALL) && !defined(WOLFSSL_SMALL_STACK)) || defined(WOLFSSL_SP_NO_MALLOC)
    sp_digit a[64 * 2];
    sp_digit p[32], q[32], dp[32];
    sp_digit tmpa[64], tmpb[64];
#else
    sp_digit* t = NULL;
    sp_digit* a = NULL;
    sp_digit* p = NULL;
    sp_digit* q = NULL;
    sp_digit* dp = NULL;
    sp_digit* tmpa = NULL;
    sp_digit* tmpb = NULL;
#endif
    sp_digit* r = NULL;
    sp_digit* qi = NULL;
    sp_digit* dq = NULL;
    sp_digit c;
    int err = MP_OKAY;

    (void)dm;
    (void)mm;

    if (*outLen < 256)
        err = MP_TO_E;
    if (err == MP_OKAY && (inLen > 256 || mp_count_bits(mm) != 2048))
        err = MP_READ_E;

#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (err == MP_OKAY) {
        t = (sp_digit*)XMALLOC(sizeof(sp_digit) * 32 * 11, NULL,
                                                              DYNAMIC_TYPE_RSA);
        if (t == NULL)
            err = MEMORY_E;
    }
    if (err == MP_OKAY) {
        a = t;
        p = a + 64 * 2;
        q = p + 32;
        qi = dq = dp = q + 32;
        tmpa = qi + 32;
        tmpb = tmpa + 64;

        r = t + 64;
    }
#else
#endif

    if (err == MP_OKAY) {
#if (!defined(WOLFSSL_SP_SMALL) && !defined(WOLFSSL_SMALL_STACK)) || defined(WOLFSSL_SP_NO_MALLOC)
        r = a;
        qi = dq = dp;
#endif
        sp_2048_from_bin(a, 64, in, inLen);
        sp_2048_from_mp(p, 32, pm);
        sp_2048_from_mp(q, 32, qm);
        sp_2048_from_mp(dp, 32, dpm);

        err = sp_2048_mod_exp_32(tmpa, a, dp, 1024, p, 1);
    }
    if (err == MP_OKAY) {
        sp_2048_from_mp(dq, 32, dqm);
        err = sp_2048_mod_exp_32(tmpb, a, dq, 1024, q, 1);
    }

    if (err == MP_OKAY) {
        c = sp_2048_sub_in_place_32(tmpa, tmpb);
        c += sp_2048_cond_add_32(tmpa, tmpa, p, c);
        sp_2048_cond_add_32(tmpa, tmpa, p, c);

        sp_2048_from_mp(qi, 32, qim);
        sp_2048_mul_32(tmpa, tmpa, qi);
        err = sp_2048_mod_32(tmpa, tmpa, p);
    }

    if (err == MP_OKAY) {
        sp_2048_mul_32(tmpa, q, tmpa);
        XMEMSET(&tmpb[32], 0, sizeof(sp_digit) * 32);
        sp_2048_add_64(r, tmpb, tmpa);

        sp_2048_to_bin(r, out);
        *outLen = 256;
    }

#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (t != NULL) {
        XMEMSET(t, 0, sizeof(sp_digit) * 32 * 11);
        XFREE(t, NULL, DYNAMIC_TYPE_RSA);
    }
#else
    XMEMSET(tmpa, 0, sizeof(tmpa));
    XMEMSET(tmpb, 0, sizeof(tmpb));
    XMEMSET(p,    0, sizeof(p));
    XMEMSET(q,    0, sizeof(q));
    XMEMSET(dp,   0, sizeof(dp));
#endif
#endif /* SP_RSA_PRIVATE_EXP_D || RSA_LOW_MEM */
    return err;
}
#endif /* WOLFSSL_RSA_PUBLIC_ONLY */
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
#if DIGIT_BIT == 32
        XMEMCPY(r->dp, a, sizeof(sp_digit) * 64);
        r->used = 64;
        mp_clamp(r);
#elif DIGIT_BIT < 32
        int i, j = 0, s = 0;

        r->dp[0] = 0;
        for (i = 0; i < 64; i++) {
            r->dp[j] |= (mp_digit)(a[i] << s);
            r->dp[j] &= (1L << DIGIT_BIT) - 1;
            s = DIGIT_BIT - s;
            r->dp[++j] = (mp_digit)(a[i] >> s);
            while (s + DIGIT_BIT <= 32) {
                s += DIGIT_BIT;
                r->dp[j++] &= (1L << DIGIT_BIT) - 1;
                if (s == SP_WORD_SIZE) {
                    r->dp[j] = 0;
                }
                else {
                    r->dp[j] = (mp_digit)(a[i] >> s);
                }
            }
            s = 32 - s;
        }
        r->used = (2048 + DIGIT_BIT - 1) / DIGIT_BIT;
        mp_clamp(r);
#else
        int i, j = 0, s = 0;

        r->dp[0] = 0;
        for (i = 0; i < 64; i++) {
            r->dp[j] |= ((mp_digit)a[i]) << s;
            if (s + 32 >= DIGIT_BIT) {
    #if DIGIT_BIT != 32 && DIGIT_BIT != 64
                r->dp[j] &= (1L << DIGIT_BIT) - 1;
    #endif
                s = DIGIT_BIT - s;
                r->dp[++j] = a[i] >> s;
                s = 32 - s;
            }
            else {
                s += 32;
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
    int err = MP_OKAY;
    sp_digit b[128], e[64], m[64];
    sp_digit* r = b;
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
        sp_2048_from_mp(b, 64, base);
        sp_2048_from_mp(e, 64, exp);
        sp_2048_from_mp(m, 64, mod);

        err = sp_2048_mod_exp_64(r, b, e, expBits, m, 0);
    }

    if (err == MP_OKAY) {
        err = sp_2048_to_mp(r, res);
    }

    XMEMSET(e, 0, sizeof(e));

    return err;
}

#ifdef WOLFSSL_HAVE_SP_DH

#ifdef HAVE_FFDHE_2048
static void sp_2048_lshift_64(sp_digit* r, sp_digit* a, byte n)
{
    __asm__ __volatile__ (
        "mov r6, #31\n\t"
        "sub r6, r6, %[n]\n\t"
        "add       %[a], %[a], #192\n\t"
        "add       %[r], %[r], #192\n\t"
        "ldr r3, [%[a], #60]\n\t"
        "lsr r4, r3, #1\n\t"
        "lsl r3, r3, %[n]\n\t"
        "lsr r4, r4, r6\n\t"
        "ldr       r2, [%[a], #56]\n\t"
        "str       r4, [%[r], #64]\n\t"
        "lsr       r5, r2, #1\n\t"
        "lsl       r2, r2, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r3, r3, r5\n\t"
        "ldr       r4, [%[a], #52]\n\t"
        "str       r3, [%[r], #60]\n\t"
        "lsr       r5, r4, #1\n\t"
        "lsl       r4, r4, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r2, r2, r5\n\t"
        "ldr       r3, [%[a], #48]\n\t"
        "str       r2, [%[r], #56]\n\t"
        "lsr       r5, r3, #1\n\t"
        "lsl       r3, r3, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r4, r4, r5\n\t"
        "ldr       r2, [%[a], #44]\n\t"
        "str       r4, [%[r], #52]\n\t"
        "lsr       r5, r2, #1\n\t"
        "lsl       r2, r2, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r3, r3, r5\n\t"
        "ldr       r4, [%[a], #40]\n\t"
        "str       r3, [%[r], #48]\n\t"
        "lsr       r5, r4, #1\n\t"
        "lsl       r4, r4, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r2, r2, r5\n\t"
        "ldr       r3, [%[a], #36]\n\t"
        "str       r2, [%[r], #44]\n\t"
        "lsr       r5, r3, #1\n\t"
        "lsl       r3, r3, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r4, r4, r5\n\t"
        "ldr       r2, [%[a], #32]\n\t"
        "str       r4, [%[r], #40]\n\t"
        "lsr       r5, r2, #1\n\t"
        "lsl       r2, r2, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r3, r3, r5\n\t"
        "ldr       r4, [%[a], #28]\n\t"
        "str       r3, [%[r], #36]\n\t"
        "lsr       r5, r4, #1\n\t"
        "lsl       r4, r4, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r2, r2, r5\n\t"
        "ldr       r3, [%[a], #24]\n\t"
        "str       r2, [%[r], #32]\n\t"
        "lsr       r5, r3, #1\n\t"
        "lsl       r3, r3, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r4, r4, r5\n\t"
        "ldr       r2, [%[a], #20]\n\t"
        "str       r4, [%[r], #28]\n\t"
        "lsr       r5, r2, #1\n\t"
        "lsl       r2, r2, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r3, r3, r5\n\t"
        "ldr       r4, [%[a], #16]\n\t"
        "str       r3, [%[r], #24]\n\t"
        "lsr       r5, r4, #1\n\t"
        "lsl       r4, r4, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r2, r2, r5\n\t"
        "ldr       r3, [%[a], #12]\n\t"
        "str       r2, [%[r], #20]\n\t"
        "lsr       r5, r3, #1\n\t"
        "lsl       r3, r3, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r4, r4, r5\n\t"
        "ldr       r2, [%[a], #8]\n\t"
        "str       r4, [%[r], #16]\n\t"
        "lsr       r5, r2, #1\n\t"
        "lsl       r2, r2, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r3, r3, r5\n\t"
        "ldr       r4, [%[a], #4]\n\t"
        "str       r3, [%[r], #12]\n\t"
        "lsr       r5, r4, #1\n\t"
        "lsl       r4, r4, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r2, r2, r5\n\t"
        "ldr       r3, [%[a], #0]\n\t"
        "str       r2, [%[r], #8]\n\t"
        "lsr       r5, r3, #1\n\t"
        "lsl       r3, r3, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r4, r4, r5\n\t"
        "sub     %[a], %[a], #64\n\t"
        "sub     %[r], %[r], #64\n\t"
        "ldr       r2, [%[a], #60]\n\t"
        "str       r4, [%[r], #68]\n\t"
        "lsr       r5, r2, #1\n\t"
        "lsl       r2, r2, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r3, r3, r5\n\t"
        "ldr       r4, [%[a], #56]\n\t"
        "str       r3, [%[r], #64]\n\t"
        "lsr       r5, r4, #1\n\t"
        "lsl       r4, r4, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r2, r2, r5\n\t"
        "ldr       r3, [%[a], #52]\n\t"
        "str       r2, [%[r], #60]\n\t"
        "lsr       r5, r3, #1\n\t"
        "lsl       r3, r3, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r4, r4, r5\n\t"
        "ldr       r2, [%[a], #48]\n\t"
        "str       r4, [%[r], #56]\n\t"
        "lsr       r5, r2, #1\n\t"
        "lsl       r2, r2, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r3, r3, r5\n\t"
        "ldr       r4, [%[a], #44]\n\t"
        "str       r3, [%[r], #52]\n\t"
        "lsr       r5, r4, #1\n\t"
        "lsl       r4, r4, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r2, r2, r5\n\t"
        "ldr       r3, [%[a], #40]\n\t"
        "str       r2, [%[r], #48]\n\t"
        "lsr       r5, r3, #1\n\t"
        "lsl       r3, r3, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r4, r4, r5\n\t"
        "ldr       r2, [%[a], #36]\n\t"
        "str       r4, [%[r], #44]\n\t"
        "lsr       r5, r2, #1\n\t"
        "lsl       r2, r2, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r3, r3, r5\n\t"
        "ldr       r4, [%[a], #32]\n\t"
        "str       r3, [%[r], #40]\n\t"
        "lsr       r5, r4, #1\n\t"
        "lsl       r4, r4, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r2, r2, r5\n\t"
        "ldr       r3, [%[a], #28]\n\t"
        "str       r2, [%[r], #36]\n\t"
        "lsr       r5, r3, #1\n\t"
        "lsl       r3, r3, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r4, r4, r5\n\t"
        "ldr       r2, [%[a], #24]\n\t"
        "str       r4, [%[r], #32]\n\t"
        "lsr       r5, r2, #1\n\t"
        "lsl       r2, r2, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r3, r3, r5\n\t"
        "ldr       r4, [%[a], #20]\n\t"
        "str       r3, [%[r], #28]\n\t"
        "lsr       r5, r4, #1\n\t"
        "lsl       r4, r4, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r2, r2, r5\n\t"
        "ldr       r3, [%[a], #16]\n\t"
        "str       r2, [%[r], #24]\n\t"
        "lsr       r5, r3, #1\n\t"
        "lsl       r3, r3, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r4, r4, r5\n\t"
        "ldr       r2, [%[a], #12]\n\t"
        "str       r4, [%[r], #20]\n\t"
        "lsr       r5, r2, #1\n\t"
        "lsl       r2, r2, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r3, r3, r5\n\t"
        "ldr       r4, [%[a], #8]\n\t"
        "str       r3, [%[r], #16]\n\t"
        "lsr       r5, r4, #1\n\t"
        "lsl       r4, r4, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r2, r2, r5\n\t"
        "ldr       r3, [%[a], #4]\n\t"
        "str       r2, [%[r], #12]\n\t"
        "lsr       r5, r3, #1\n\t"
        "lsl       r3, r3, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r4, r4, r5\n\t"
        "ldr       r2, [%[a], #0]\n\t"
        "str       r4, [%[r], #8]\n\t"
        "lsr       r5, r2, #1\n\t"
        "lsl       r2, r2, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r3, r3, r5\n\t"
        "sub     %[a], %[a], #64\n\t"
        "sub     %[r], %[r], #64\n\t"
        "ldr       r4, [%[a], #60]\n\t"
        "str       r3, [%[r], #68]\n\t"
        "lsr       r5, r4, #1\n\t"
        "lsl       r4, r4, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r2, r2, r5\n\t"
        "ldr       r3, [%[a], #56]\n\t"
        "str       r2, [%[r], #64]\n\t"
        "lsr       r5, r3, #1\n\t"
        "lsl       r3, r3, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r4, r4, r5\n\t"
        "ldr       r2, [%[a], #52]\n\t"
        "str       r4, [%[r], #60]\n\t"
        "lsr       r5, r2, #1\n\t"
        "lsl       r2, r2, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r3, r3, r5\n\t"
        "ldr       r4, [%[a], #48]\n\t"
        "str       r3, [%[r], #56]\n\t"
        "lsr       r5, r4, #1\n\t"
        "lsl       r4, r4, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r2, r2, r5\n\t"
        "ldr       r3, [%[a], #44]\n\t"
        "str       r2, [%[r], #52]\n\t"
        "lsr       r5, r3, #1\n\t"
        "lsl       r3, r3, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r4, r4, r5\n\t"
        "ldr       r2, [%[a], #40]\n\t"
        "str       r4, [%[r], #48]\n\t"
        "lsr       r5, r2, #1\n\t"
        "lsl       r2, r2, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r3, r3, r5\n\t"
        "ldr       r4, [%[a], #36]\n\t"
        "str       r3, [%[r], #44]\n\t"
        "lsr       r5, r4, #1\n\t"
        "lsl       r4, r4, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r2, r2, r5\n\t"
        "ldr       r3, [%[a], #32]\n\t"
        "str       r2, [%[r], #40]\n\t"
        "lsr       r5, r3, #1\n\t"
        "lsl       r3, r3, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r4, r4, r5\n\t"
        "ldr       r2, [%[a], #28]\n\t"
        "str       r4, [%[r], #36]\n\t"
        "lsr       r5, r2, #1\n\t"
        "lsl       r2, r2, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r3, r3, r5\n\t"
        "ldr       r4, [%[a], #24]\n\t"
        "str       r3, [%[r], #32]\n\t"
        "lsr       r5, r4, #1\n\t"
        "lsl       r4, r4, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r2, r2, r5\n\t"
        "ldr       r3, [%[a], #20]\n\t"
        "str       r2, [%[r], #28]\n\t"
        "lsr       r5, r3, #1\n\t"
        "lsl       r3, r3, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r4, r4, r5\n\t"
        "ldr       r2, [%[a], #16]\n\t"
        "str       r4, [%[r], #24]\n\t"
        "lsr       r5, r2, #1\n\t"
        "lsl       r2, r2, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r3, r3, r5\n\t"
        "ldr       r4, [%[a], #12]\n\t"
        "str       r3, [%[r], #20]\n\t"
        "lsr       r5, r4, #1\n\t"
        "lsl       r4, r4, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r2, r2, r5\n\t"
        "ldr       r3, [%[a], #8]\n\t"
        "str       r2, [%[r], #16]\n\t"
        "lsr       r5, r3, #1\n\t"
        "lsl       r3, r3, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r4, r4, r5\n\t"
        "ldr       r2, [%[a], #4]\n\t"
        "str       r4, [%[r], #12]\n\t"
        "lsr       r5, r2, #1\n\t"
        "lsl       r2, r2, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r3, r3, r5\n\t"
        "ldr       r4, [%[a], #0]\n\t"
        "str       r3, [%[r], #8]\n\t"
        "lsr       r5, r4, #1\n\t"
        "lsl       r4, r4, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r2, r2, r5\n\t"
        "sub     %[a], %[a], #64\n\t"
        "sub     %[r], %[r], #64\n\t"
        "ldr       r3, [%[a], #60]\n\t"
        "str       r2, [%[r], #68]\n\t"
        "lsr       r5, r3, #1\n\t"
        "lsl       r3, r3, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r4, r4, r5\n\t"
        "ldr       r2, [%[a], #56]\n\t"
        "str       r4, [%[r], #64]\n\t"
        "lsr       r5, r2, #1\n\t"
        "lsl       r2, r2, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r3, r3, r5\n\t"
        "ldr       r4, [%[a], #52]\n\t"
        "str       r3, [%[r], #60]\n\t"
        "lsr       r5, r4, #1\n\t"
        "lsl       r4, r4, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r2, r2, r5\n\t"
        "ldr       r3, [%[a], #48]\n\t"
        "str       r2, [%[r], #56]\n\t"
        "lsr       r5, r3, #1\n\t"
        "lsl       r3, r3, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r4, r4, r5\n\t"
        "ldr       r2, [%[a], #44]\n\t"
        "str       r4, [%[r], #52]\n\t"
        "lsr       r5, r2, #1\n\t"
        "lsl       r2, r2, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r3, r3, r5\n\t"
        "ldr       r4, [%[a], #40]\n\t"
        "str       r3, [%[r], #48]\n\t"
        "lsr       r5, r4, #1\n\t"
        "lsl       r4, r4, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r2, r2, r5\n\t"
        "ldr       r3, [%[a], #36]\n\t"
        "str       r2, [%[r], #44]\n\t"
        "lsr       r5, r3, #1\n\t"
        "lsl       r3, r3, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r4, r4, r5\n\t"
        "ldr       r2, [%[a], #32]\n\t"
        "str       r4, [%[r], #40]\n\t"
        "lsr       r5, r2, #1\n\t"
        "lsl       r2, r2, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r3, r3, r5\n\t"
        "ldr       r4, [%[a], #28]\n\t"
        "str       r3, [%[r], #36]\n\t"
        "lsr       r5, r4, #1\n\t"
        "lsl       r4, r4, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r2, r2, r5\n\t"
        "ldr       r3, [%[a], #24]\n\t"
        "str       r2, [%[r], #32]\n\t"
        "lsr       r5, r3, #1\n\t"
        "lsl       r3, r3, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r4, r4, r5\n\t"
        "ldr       r2, [%[a], #20]\n\t"
        "str       r4, [%[r], #28]\n\t"
        "lsr       r5, r2, #1\n\t"
        "lsl       r2, r2, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r3, r3, r5\n\t"
        "ldr       r4, [%[a], #16]\n\t"
        "str       r3, [%[r], #24]\n\t"
        "lsr       r5, r4, #1\n\t"
        "lsl       r4, r4, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r2, r2, r5\n\t"
        "ldr       r3, [%[a], #12]\n\t"
        "str       r2, [%[r], #20]\n\t"
        "lsr       r5, r3, #1\n\t"
        "lsl       r3, r3, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r4, r4, r5\n\t"
        "ldr       r2, [%[a], #8]\n\t"
        "str       r4, [%[r], #16]\n\t"
        "lsr       r5, r2, #1\n\t"
        "lsl       r2, r2, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r3, r3, r5\n\t"
        "ldr       r4, [%[a], #4]\n\t"
        "str       r3, [%[r], #12]\n\t"
        "lsr       r5, r4, #1\n\t"
        "lsl       r4, r4, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r2, r2, r5\n\t"
        "ldr       r3, [%[a], #0]\n\t"
        "str       r2, [%[r], #8]\n\t"
        "lsr       r5, r3, #1\n\t"
        "lsl       r3, r3, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r4, r4, r5\n\t"
        "str r3, [%[r]]\n\t"
        "str r4, [%[r], #4]\n\t"
        :
        : [r] "r" (r), [a] "r" (a), [n] "r" (n)
        : "memory", "r2", "r3", "r4", "r5", "r6"
    );
}

/* Modular exponentiate 2 to the e mod m. (r = 2^e mod m)
 *
 * r     A single precision number that is the result of the operation.
 * e     A single precision number that is the exponent.
 * bits  The number of bits in the exponent.
 * m     A single precision number that is the modulus.
 * returns 0 on success and MEMORY_E on dynamic memory allocation failure.
 */
static int sp_2048_mod_exp_2_64(sp_digit* r, const sp_digit* e, int bits,
        const sp_digit* m)
{
#if defined(WOLFSSL_SMALL_STACK) && !defined(WOLFSSL_SP_NO_MALLOC)
    sp_digit* td;
#else
    sp_digit td[193];
#endif
    sp_digit* norm;
    sp_digit* tmp;
    sp_digit mp = 1;
    sp_digit n, o;
    sp_digit mask;
    int i;
    int c, y;
    int err = MP_OKAY;

#if defined(WOLFSSL_SMALL_STACK) && !defined(WOLFSSL_SP_NO_MALLOC)
    td = (sp_digit*)XMALLOC(sizeof(sp_digit) * 193, NULL,
                            DYNAMIC_TYPE_TMP_BUFFER);
    if (td == NULL) {
        err = MEMORY_E;
    }
#endif

    if (err == MP_OKAY) {
        norm = td;
#if defined(WOLFSSL_SMALL_STACK) && !defined(WOLFSSL_SP_NO_MALLOC)
        tmp = td + 128;
#else
        tmp = &td[128];
#endif

        sp_2048_mont_setup(m, &mp);
        sp_2048_mont_norm_64(norm, m);

        i = (bits - 1) / 32;
        n = e[i--];
        c = bits & 31;
        if (c == 0) {
            c = 32;
        }
        c -= bits % 5;
        if (c == 32) {
            c = 27;
        }
        y = (int)(n >> c);
        n <<= 32 - c;
        sp_2048_lshift_64(r, norm, y);
        for (; i>=0 || c>=5; ) {
            if (c == 0) {
                n = e[i--];
                y = n >> 27;
                n <<= 5;
                c = 27;
            }
            else if (c < 5) {
                y = n >> 27;
                n = e[i--];
                c = 5 - c;
                y |= n >> (32 - c);
                n <<= c;
                c = 32 - c;
            }
            else {
                y = (n >> 27) & 0x1f;
                n <<= 5;
                c -= 5;
            }

            sp_2048_mont_sqr_64(r, r, m, mp);
            sp_2048_mont_sqr_64(r, r, m, mp);
            sp_2048_mont_sqr_64(r, r, m, mp);
            sp_2048_mont_sqr_64(r, r, m, mp);
            sp_2048_mont_sqr_64(r, r, m, mp);

            sp_2048_lshift_64(r, r, y);
            sp_2048_mul_d_64(tmp, norm, r[64]);
            r[64] = 0;
            o = sp_2048_add_64(r, r, tmp);
            sp_2048_cond_sub_64(r, r, m, (sp_digit)0 - o);
        }

        XMEMSET(&r[64], 0, sizeof(sp_digit) * 64U);
        sp_2048_mont_reduce_64(r, m, mp);

        mask = 0 - (sp_2048_cmp_64(r, m) >= 0);
        sp_2048_cond_sub_64(r, r, m, mask);
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
    int err = MP_OKAY;
    sp_digit b[128], e[64], m[64];
    sp_digit* r = b;
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
        sp_2048_from_mp(b, 64, base);
        sp_2048_from_bin(e, 64, exp, expLen);
        sp_2048_from_mp(m, 64, mod);

    #ifdef HAVE_FFDHE_2048
        if (base->used == 1 && base->dp[0] == 2 && m[63] == (sp_digit)-1)
            err = sp_2048_mod_exp_2_64(r, e, expLen * 8, m);
        else
    #endif
            err = sp_2048_mod_exp_64(r, b, e, expLen * 8, m, 0);

    }

    if (err == MP_OKAY) {
        sp_2048_to_bin(r, out);
        *outLen = 256;
        for (i=0; i<256 && out[i] == 0; i++) {
        }
        *outLen -= i;
        XMEMMOVE(out, out + i, *outLen);

    }

    XMEMSET(e, 0, sizeof(e));

    return err;
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
    int err = MP_OKAY;
    sp_digit b[64], e[32], m[32];
    sp_digit* r = b;
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
        sp_2048_from_mp(b, 32, base);
        sp_2048_from_mp(e, 32, exp);
        sp_2048_from_mp(m, 32, mod);

        err = sp_2048_mod_exp_32(r, b, e, expBits, m, 0);
    }

    if (err == MP_OKAY) {
        XMEMSET(r + 32, 0, sizeof(*r) * 32U);
        err = sp_2048_to_mp(r, res);
        res->used = mod->used;
        mp_clamp(res);
    }

    XMEMSET(e, 0, sizeof(e));

    return err;
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
        if (s >= 24U) {
            r[j] &= 0xffffffff;
            s = 32U - s;
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
#if DIGIT_BIT == 32
    int j;

    XMEMCPY(r, a->dp, sizeof(sp_digit) * a->used);

    for (j = a->used; j < size; j++) {
        r[j] = 0;
    }
#elif DIGIT_BIT > 32
    int i, j = 0;
    word32 s = 0;

    r[0] = 0;
    for (i = 0; i < a->used && j < size; i++) {
        r[j] |= ((sp_digit)a->dp[i] << s);
        r[j] &= 0xffffffff;
        s = 32U - s;
        if (j + 1 >= size) {
            break;
        }
        /* lint allow cast of mismatch word32 and mp_digit */
        r[++j] = (sp_digit)(a->dp[i] >> s); /*lint !e9033*/
        while ((s + 32U) <= (word32)DIGIT_BIT) {
            s += 32U;
            r[j] &= 0xffffffff;
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
        if (s + DIGIT_BIT >= 32) {
            r[j] &= 0xffffffff;
            if (j + 1 >= size) {
                break;
            }
            s = 32 - s;
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

    j = 3072 / 8 - 1;
    a[j] = 0;
    for (i=0; i<96 && j>=0; i++) {
        b = 0;
        /* lint allow cast of mismatch sp_digit and int */
        a[j--] |= (byte)(r[i] << s); /*lint !e9033*/
        b += 8 - s;
        if (j < 0) {
            break;
        }
        while (b < 32) {
            a[j--] = (byte)(r[i] >> b);
            b += 8;
            if (j < 0) {
                break;
            }
        }
        s = 8 - (b - 32);
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
SP_NOINLINE static void sp_3072_mul_12(sp_digit* r, const sp_digit* a,
        const sp_digit* b)
{
    sp_digit tmp[12 * 2];
    __asm__ __volatile__ (
        "mov	r3, #0\n\t"
        "mov	r4, #0\n\t"
        "mov	r9, r3\n\t"
        "mov	r12, %[r]\n\t"
        "mov	r10, %[a]\n\t"
        "mov	r11, %[b]\n\t"
        "mov	r6, #48\n\t"
        "add	r6, r6, r10\n\t"
        "mov	r14, r6\n\t"
        "\n1:\n\t"
        "mov	%[r], #0\n\t"
        "mov	r5, #0\n\t"
        "mov	r6, #44\n\t"
        "mov	%[a], r9\n\t"
        "subs	%[a], %[a], r6\n\t"
        "sbc	r6, r6, r6\n\t"
        "mvn	r6, r6\n\t"
        "and	%[a], %[a], r6\n\t"
        "mov	%[b], r9\n\t"
        "sub	%[b], %[b], %[a]\n\t"
        "add	%[a], %[a], r10\n\t"
        "add	%[b], %[b], r11\n\t"
        "\n2:\n\t"
        /* Multiply Start */
        "ldr	r6, [%[a]]\n\t"
        "ldr	r8, [%[b]]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r3, r3, r6\n\t"
        "adcs 	r4, r4, r8\n\t"
        "adc	r5, r5, %[r]\n\t"
        /* Multiply Done */
        "add	%[a], %[a], #4\n\t"
        "sub	%[b], %[b], #4\n\t"
        "cmp	%[a], r14\n\t"
        "beq	3f\n\t"
        "mov	r6, r9\n\t"
        "add	r6, r6, r10\n\t"
        "cmp	%[a], r6\n\t"
        "ble	2b\n\t"
        "\n3:\n\t"
        "mov	%[r], r12\n\t"
        "mov	r8, r9\n\t"
        "str	r3, [%[r], r8]\n\t"
        "mov	r3, r4\n\t"
        "mov	r4, r5\n\t"
        "add	r8, r8, #4\n\t"
        "mov	r9, r8\n\t"
        "mov	r6, #88\n\t"
        "cmp	r8, r6\n\t"
        "ble	1b\n\t"
        "str	r3, [%[r], r8]\n\t"
        "mov	%[a], r10\n\t"
        "mov	%[b], r11\n\t"
        :
        : [r] "r" (tmp), [a] "r" (a), [b] "r" (b)
        : "memory", "r3", "r4", "r5", "r6", "r8", "r9", "r10", "r11", "r12", "r14"
    );

    XMEMCPY(r, tmp, sizeof(tmp));
}

/* Square a and put result in r. (r = a * a)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 */
SP_NOINLINE static void sp_3072_sqr_12(sp_digit* r, const sp_digit* a)
{
    __asm__ __volatile__ (
        "mov	r3, #0\n\t"
        "mov	r4, #0\n\t"
        "mov	r5, #0\n\t"
        "mov	r9, r3\n\t"
        "mov	r12, %[r]\n\t"
        "mov	r6, #96\n\t"
        "neg	r6, r6\n\t"
        "add	sp, sp, r6\n\t"
        "mov	r11, sp\n\t"
        "mov	r10, %[a]\n\t"
        "\n1:\n\t"
        "mov	%[r], #0\n\t"
        "mov	r6, #44\n\t"
        "mov	%[a], r9\n\t"
        "subs	%[a], %[a], r6\n\t"
        "sbc	r6, r6, r6\n\t"
        "mvn	r6, r6\n\t"
        "and	%[a], %[a], r6\n\t"
        "mov	r2, r9\n\t"
        "sub	r2, r2, %[a]\n\t"
        "add	%[a], %[a], r10\n\t"
        "add	r2, r2, r10\n\t"
        "\n2:\n\t"
        "cmp	r2, %[a]\n\t"
        "beq	4f\n\t"
        /* Multiply * 2: Start */
        "ldr	r6, [%[a]]\n\t"
        "ldr	r8, [r2]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r3, r3, r6\n\t"
        "adcs 	r4, r4, r8\n\t"
        "adc	r5, r5, %[r]\n\t"
        "adds	r3, r3, r6\n\t"
        "adcs 	r4, r4, r8\n\t"
        "adc	r5, r5, %[r]\n\t"
        /* Multiply * 2: Done */
        "bal	5f\n\t"
        "\n4:\n\t"
        /* Square: Start */
        "ldr	r6, [%[a]]\n\t"
        "umull	r6, r8, r6, r6\n\t"
        "adds	r3, r3, r6\n\t"
        "adcs	r4, r4, r8\n\t"
        "adc	r5, r5, %[r]\n\t"
        /* Square: Done */
        "\n5:\n\t"
        "add	%[a], %[a], #4\n\t"
        "sub	r2, r2, #4\n\t"
        "mov	r6, #48\n\t"
        "add	r6, r6, r10\n\t"
        "cmp	%[a], r6\n\t"
        "beq	3f\n\t"
        "cmp	%[a], r2\n\t"
        "bgt	3f\n\t"
        "mov	r8, r9\n\t"
        "add	r8, r8, r10\n\t"
        "cmp	%[a], r8\n\t"
        "ble	2b\n\t"
        "\n3:\n\t"
        "mov	%[r], r11\n\t"
        "mov	r8, r9\n\t"
        "str	r3, [%[r], r8]\n\t"
        "mov	r3, r4\n\t"
        "mov	r4, r5\n\t"
        "mov	r5, #0\n\t"
        "add	r8, r8, #4\n\t"
        "mov	r9, r8\n\t"
        "mov	r6, #88\n\t"
        "cmp	r8, r6\n\t"
        "ble	1b\n\t"
        "mov	%[a], r10\n\t"
        "str	r3, [%[r], r8]\n\t"
        "mov	%[r], r12\n\t"
        "mov	%[a], r11\n\t"
        "mov	r3, #92\n\t"
        "\n4:\n\t"
        "ldr	r6, [%[a], r3]\n\t"
        "str	r6, [%[r], r3]\n\t"
        "subs	r3, r3, #4\n\t"
        "bge	4b\n\t"
        "mov	r6, #96\n\t"
        "add	sp, sp, r6\n\t"
        :
        : [r] "r" (r), [a] "r" (a)
        : "memory", "r2", "r3", "r4", "r5", "r6", "r8", "r9", "r10", "r11", "r12"
    );
}

/* Add b to a into r. (r = a + b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A single precision integer.
 */
SP_NOINLINE static sp_digit sp_3072_add_12(sp_digit* r, const sp_digit* a,
        const sp_digit* b)
{
    sp_digit c = 0;

    __asm__ __volatile__ (
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adds	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "mov	%[c], #0\n\t"
        "adc	%[c], %[c], %[c]\n\t"
        : [c] "+r" (c), [r] "+r" (r), [a] "+r" (a), [b] "+r" (b)
        :
        : "memory", "r4", "r5", "r6", "r8"
    );

    return c;
}

/* Sub b from a into r. (r = a - b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A single precision integer.
 */
SP_NOINLINE static sp_digit sp_3072_sub_in_place_24(sp_digit* a,
        const sp_digit* b)
{
    sp_digit c = 0;

    __asm__ __volatile__ (
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "subs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "sbc	%[c], %[c], %[c]\n\t"
        : [c] "+r" (c), [a] "+r" (a), [b] "+r" (b)
        :
        : "memory", "r3", "r4", "r5", "r6"
    );

    return c;
}

/* Add b to a into r. (r = a + b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A single precision integer.
 */
SP_NOINLINE static sp_digit sp_3072_add_24(sp_digit* r, const sp_digit* a,
        const sp_digit* b)
{
    sp_digit c = 0;

    __asm__ __volatile__ (
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adds	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "mov	%[c], #0\n\t"
        "adc	%[c], %[c], %[c]\n\t"
        : [c] "+r" (c), [r] "+r" (r), [a] "+r" (a), [b] "+r" (b)
        :
        : "memory", "r4", "r5", "r6", "r8"
    );

    return c;
}

/* AND m into each word of a and store in r.
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * m  Mask to AND against each digit.
 */
static void sp_3072_mask_12(sp_digit* r, const sp_digit* a, sp_digit m)
{
#ifdef WOLFSSL_SP_SMALL
    int i;

    for (i=0; i<12; i++) {
        r[i] = a[i] & m;
    }
#else
    r[0] = a[0] & m;
    r[1] = a[1] & m;
    r[2] = a[2] & m;
    r[3] = a[3] & m;
    r[4] = a[4] & m;
    r[5] = a[5] & m;
    r[6] = a[6] & m;
    r[7] = a[7] & m;
    r[8] = a[8] & m;
    r[9] = a[9] & m;
    r[10] = a[10] & m;
    r[11] = a[11] & m;
#endif
}

/* Multiply a and b into r. (r = a * b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A single precision integer.
 */
SP_NOINLINE static void sp_3072_mul_24(sp_digit* r, const sp_digit* a,
        const sp_digit* b)
{
    sp_digit* z0 = r;
    sp_digit z1[24];
    sp_digit a1[12];
    sp_digit b1[12];
    sp_digit z2[24];
    sp_digit u, ca, cb;

    ca = sp_3072_add_12(a1, a, &a[12]);
    cb = sp_3072_add_12(b1, b, &b[12]);
    u  = ca & cb;
    sp_3072_mul_12(z1, a1, b1);
    sp_3072_mul_12(z2, &a[12], &b[12]);
    sp_3072_mul_12(z0, a, b);
    sp_3072_mask_12(r + 24, a1, 0 - cb);
    sp_3072_mask_12(b1, b1, 0 - ca);
    u += sp_3072_add_12(r + 24, r + 24, b1);
    u += sp_3072_sub_in_place_24(z1, z2);
    u += sp_3072_sub_in_place_24(z1, z0);
    u += sp_3072_add_24(r + 12, r + 12, z1);
    r[36] = u;
    XMEMSET(r + 36 + 1, 0, sizeof(sp_digit) * (12 - 1));
    (void)sp_3072_add_24(r + 24, r + 24, z2);
}

/* Square a and put result in r. (r = a * a)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 */
SP_NOINLINE static void sp_3072_sqr_24(sp_digit* r, const sp_digit* a)
{
    sp_digit* z0 = r;
    sp_digit z2[24];
    sp_digit z1[24];
    sp_digit a1[12];
    sp_digit u;

    u = sp_3072_add_12(a1, a, &a[12]);
    sp_3072_sqr_12(z1, a1);
    sp_3072_sqr_12(z2, &a[12]);
    sp_3072_sqr_12(z0, a);
    sp_3072_mask_12(r + 24, a1, 0 - u);
    u += sp_3072_add_12(r + 24, r + 24, r + 24);
    u += sp_3072_sub_in_place_24(z1, z2);
    u += sp_3072_sub_in_place_24(z1, z0);
    u += sp_3072_add_24(r + 12, r + 12, z1);
    r[36] = u;
    XMEMSET(r + 36 + 1, 0, sizeof(sp_digit) * (12 - 1));
    (void)sp_3072_add_24(r + 24, r + 24, z2);
}

/* Sub b from a into r. (r = a - b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A single precision integer.
 */
SP_NOINLINE static sp_digit sp_3072_sub_in_place_48(sp_digit* a,
        const sp_digit* b)
{
    sp_digit c = 0;

    __asm__ __volatile__ (
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "subs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "sbc	%[c], %[c], %[c]\n\t"
        : [c] "+r" (c), [a] "+r" (a), [b] "+r" (b)
        :
        : "memory", "r3", "r4", "r5", "r6"
    );

    return c;
}

/* Add b to a into r. (r = a + b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A single precision integer.
 */
SP_NOINLINE static sp_digit sp_3072_add_48(sp_digit* r, const sp_digit* a,
        const sp_digit* b)
{
    sp_digit c = 0;

    __asm__ __volatile__ (
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adds	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "mov	%[c], #0\n\t"
        "adc	%[c], %[c], %[c]\n\t"
        : [c] "+r" (c), [r] "+r" (r), [a] "+r" (a), [b] "+r" (b)
        :
        : "memory", "r4", "r5", "r6", "r8"
    );

    return c;
}

/* AND m into each word of a and store in r.
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * m  Mask to AND against each digit.
 */
static void sp_3072_mask_24(sp_digit* r, const sp_digit* a, sp_digit m)
{
#ifdef WOLFSSL_SP_SMALL
    int i;

    for (i=0; i<24; i++) {
        r[i] = a[i] & m;
    }
#else
    int i;

    for (i = 0; i < 24; i += 8) {
        r[i+0] = a[i+0] & m;
        r[i+1] = a[i+1] & m;
        r[i+2] = a[i+2] & m;
        r[i+3] = a[i+3] & m;
        r[i+4] = a[i+4] & m;
        r[i+5] = a[i+5] & m;
        r[i+6] = a[i+6] & m;
        r[i+7] = a[i+7] & m;
    }
#endif
}

/* Multiply a and b into r. (r = a * b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A single precision integer.
 */
SP_NOINLINE static void sp_3072_mul_48(sp_digit* r, const sp_digit* a,
        const sp_digit* b)
{
    sp_digit* z0 = r;
    sp_digit z1[48];
    sp_digit a1[24];
    sp_digit b1[24];
    sp_digit z2[48];
    sp_digit u, ca, cb;

    ca = sp_3072_add_24(a1, a, &a[24]);
    cb = sp_3072_add_24(b1, b, &b[24]);
    u  = ca & cb;
    sp_3072_mul_24(z1, a1, b1);
    sp_3072_mul_24(z2, &a[24], &b[24]);
    sp_3072_mul_24(z0, a, b);
    sp_3072_mask_24(r + 48, a1, 0 - cb);
    sp_3072_mask_24(b1, b1, 0 - ca);
    u += sp_3072_add_24(r + 48, r + 48, b1);
    u += sp_3072_sub_in_place_48(z1, z2);
    u += sp_3072_sub_in_place_48(z1, z0);
    u += sp_3072_add_48(r + 24, r + 24, z1);
    r[72] = u;
    XMEMSET(r + 72 + 1, 0, sizeof(sp_digit) * (24 - 1));
    (void)sp_3072_add_48(r + 48, r + 48, z2);
}

/* Square a and put result in r. (r = a * a)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 */
SP_NOINLINE static void sp_3072_sqr_48(sp_digit* r, const sp_digit* a)
{
    sp_digit* z0 = r;
    sp_digit z2[48];
    sp_digit z1[48];
    sp_digit a1[24];
    sp_digit u;

    u = sp_3072_add_24(a1, a, &a[24]);
    sp_3072_sqr_24(z1, a1);
    sp_3072_sqr_24(z2, &a[24]);
    sp_3072_sqr_24(z0, a);
    sp_3072_mask_24(r + 48, a1, 0 - u);
    u += sp_3072_add_24(r + 48, r + 48, r + 48);
    u += sp_3072_sub_in_place_48(z1, z2);
    u += sp_3072_sub_in_place_48(z1, z0);
    u += sp_3072_add_48(r + 24, r + 24, z1);
    r[72] = u;
    XMEMSET(r + 72 + 1, 0, sizeof(sp_digit) * (24 - 1));
    (void)sp_3072_add_48(r + 48, r + 48, z2);
}

/* Sub b from a into r. (r = a - b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A single precision integer.
 */
SP_NOINLINE static sp_digit sp_3072_sub_in_place_96(sp_digit* a,
        const sp_digit* b)
{
    sp_digit c = 0;

    __asm__ __volatile__ (
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "subs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "sbc	%[c], %[c], %[c]\n\t"
        : [c] "+r" (c), [a] "+r" (a), [b] "+r" (b)
        :
        : "memory", "r3", "r4", "r5", "r6"
    );

    return c;
}

/* Add b to a into r. (r = a + b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A single precision integer.
 */
SP_NOINLINE static sp_digit sp_3072_add_96(sp_digit* r, const sp_digit* a,
        const sp_digit* b)
{
    sp_digit c = 0;

    __asm__ __volatile__ (
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adds	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "mov	%[c], #0\n\t"
        "adc	%[c], %[c], %[c]\n\t"
        : [c] "+r" (c), [r] "+r" (r), [a] "+r" (a), [b] "+r" (b)
        :
        : "memory", "r4", "r5", "r6", "r8"
    );

    return c;
}

/* AND m into each word of a and store in r.
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * m  Mask to AND against each digit.
 */
static void sp_3072_mask_48(sp_digit* r, const sp_digit* a, sp_digit m)
{
#ifdef WOLFSSL_SP_SMALL
    int i;

    for (i=0; i<48; i++) {
        r[i] = a[i] & m;
    }
#else
    int i;

    for (i = 0; i < 48; i += 8) {
        r[i+0] = a[i+0] & m;
        r[i+1] = a[i+1] & m;
        r[i+2] = a[i+2] & m;
        r[i+3] = a[i+3] & m;
        r[i+4] = a[i+4] & m;
        r[i+5] = a[i+5] & m;
        r[i+6] = a[i+6] & m;
        r[i+7] = a[i+7] & m;
    }
#endif
}

/* Multiply a and b into r. (r = a * b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A single precision integer.
 */
SP_NOINLINE static void sp_3072_mul_96(sp_digit* r, const sp_digit* a,
        const sp_digit* b)
{
    sp_digit* z0 = r;
    sp_digit z1[96];
    sp_digit a1[48];
    sp_digit b1[48];
    sp_digit z2[96];
    sp_digit u, ca, cb;

    ca = sp_3072_add_48(a1, a, &a[48]);
    cb = sp_3072_add_48(b1, b, &b[48]);
    u  = ca & cb;
    sp_3072_mul_48(z1, a1, b1);
    sp_3072_mul_48(z2, &a[48], &b[48]);
    sp_3072_mul_48(z0, a, b);
    sp_3072_mask_48(r + 96, a1, 0 - cb);
    sp_3072_mask_48(b1, b1, 0 - ca);
    u += sp_3072_add_48(r + 96, r + 96, b1);
    u += sp_3072_sub_in_place_96(z1, z2);
    u += sp_3072_sub_in_place_96(z1, z0);
    u += sp_3072_add_96(r + 48, r + 48, z1);
    r[144] = u;
    XMEMSET(r + 144 + 1, 0, sizeof(sp_digit) * (48 - 1));
    (void)sp_3072_add_96(r + 96, r + 96, z2);
}

/* Square a and put result in r. (r = a * a)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 */
SP_NOINLINE static void sp_3072_sqr_96(sp_digit* r, const sp_digit* a)
{
    sp_digit* z0 = r;
    sp_digit z2[96];
    sp_digit z1[96];
    sp_digit a1[48];
    sp_digit u;

    u = sp_3072_add_48(a1, a, &a[48]);
    sp_3072_sqr_48(z1, a1);
    sp_3072_sqr_48(z2, &a[48]);
    sp_3072_sqr_48(z0, a);
    sp_3072_mask_48(r + 96, a1, 0 - u);
    u += sp_3072_add_48(r + 96, r + 96, r + 96);
    u += sp_3072_sub_in_place_96(z1, z2);
    u += sp_3072_sub_in_place_96(z1, z0);
    u += sp_3072_add_96(r + 48, r + 48, z1);
    r[144] = u;
    XMEMSET(r + 144 + 1, 0, sizeof(sp_digit) * (48 - 1));
    (void)sp_3072_add_96(r + 96, r + 96, z2);
}

#endif /* !WOLFSSL_SP_SMALL */
#ifdef WOLFSSL_SP_SMALL
/* Add b to a into r. (r = a + b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A single precision integer.
 */
SP_NOINLINE static sp_digit sp_3072_add_96(sp_digit* r, const sp_digit* a,
        const sp_digit* b)
{
    sp_digit c = 0;

    __asm__ __volatile__ (
        "mov	r6, %[a]\n\t"
        "mov	r8, #0\n\t"
        "add	r6, r6, #384\n\t"
        "sub	r8, r8, #1\n\t"
        "\n1:\n\t"
        "adds	%[c], %[c], r8\n\t"
        "ldr	r4, [%[a]]\n\t"
        "ldr	r5, [%[b]]\n\t"
        "adcs	r4, r4, r5\n\t"
        "str	r4, [%[r]]\n\t"
        "mov	%[c], #0\n\t"
        "adc	%[c], %[c], %[c]\n\t"
        "add	%[a], %[a], #4\n\t"
        "add	%[b], %[b], #4\n\t"
        "add	%[r], %[r], #4\n\t"
        "cmp	%[a], r6\n\t"
        "bne	1b\n\t"
        : [c] "+r" (c), [r] "+r" (r), [a] "+r" (a), [b] "+r" (b)
        :
        : "memory", "r4", "r5", "r6", "r8"
    );

    return c;
}

#endif /* WOLFSSL_SP_SMALL */
#ifdef WOLFSSL_SP_SMALL
/* Sub b from a into a. (a -= b)
 *
 * a  A single precision integer.
 * b  A single precision integer.
 */
SP_NOINLINE static sp_digit sp_3072_sub_in_place_96(sp_digit* a,
        const sp_digit* b)
{
    sp_digit c = 0;
    __asm__ __volatile__ (
        "mov	r8, %[a]\n\t"
        "add	r8, r8, #384\n\t"
        "\n1:\n\t"
        "mov	r5, #0\n\t"
        "subs	r5, r5, %[c]\n\t"
        "ldr	r3, [%[a]]\n\t"
        "ldr	r4, [%[a], #4]\n\t"
        "ldr	r5, [%[b]]\n\t"
        "ldr	r6, [%[b], #4]\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "str	r3, [%[a]]\n\t"
        "str	r4, [%[a], #4]\n\t"
        "sbc	%[c], %[c], %[c]\n\t"
        "add	%[a], %[a], #8\n\t"
        "add	%[b], %[b], #8\n\t"
        "cmp	%[a], r8\n\t"
        "bne	1b\n\t"
        : [c] "+r" (c), [a] "+r" (a), [b] "+r" (b)
        :
        : "memory", "r3", "r4", "r5", "r6", "r8"
    );

    return c;
}

#endif /* WOLFSSL_SP_SMALL */
#ifdef WOLFSSL_SP_SMALL
/* Multiply a and b into r. (r = a * b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A single precision integer.
 */
SP_NOINLINE static void sp_3072_mul_96(sp_digit* r, const sp_digit* a,
        const sp_digit* b)
{
    sp_digit tmp[96 * 2];
    __asm__ __volatile__ (
        "mov	r3, #0\n\t"
        "mov	r4, #0\n\t"
        "mov	r9, r3\n\t"
        "mov	r12, %[r]\n\t"
        "mov	r10, %[a]\n\t"
        "mov	r11, %[b]\n\t"
        "mov	r6, #1\n\t"
        "lsl	r6, r6, #8\n\t"
        "add	r6, r6, #128\n\t"
        "add	r6, r6, r10\n\t"
        "mov	r14, r6\n\t"
        "\n1:\n\t"
        "mov	%[r], #0\n\t"
        "mov	r5, #0\n\t"
        "mov	r6, #1\n\t"
        "lsl	r6, r6, #8\n\t"
        "add	r6, r6, #124\n\t"
        "mov	%[a], r9\n\t"
        "subs	%[a], %[a], r6\n\t"
        "sbc	r6, r6, r6\n\t"
        "mvn	r6, r6\n\t"
        "and	%[a], %[a], r6\n\t"
        "mov	%[b], r9\n\t"
        "sub	%[b], %[b], %[a]\n\t"
        "add	%[a], %[a], r10\n\t"
        "add	%[b], %[b], r11\n\t"
        "\n2:\n\t"
        /* Multiply Start */
        "ldr	r6, [%[a]]\n\t"
        "ldr	r8, [%[b]]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r3, r3, r6\n\t"
        "adcs 	r4, r4, r8\n\t"
        "adc	r5, r5, %[r]\n\t"
        /* Multiply Done */
        "add	%[a], %[a], #4\n\t"
        "sub	%[b], %[b], #4\n\t"
        "cmp	%[a], r14\n\t"
        "beq	3f\n\t"
        "mov	r6, r9\n\t"
        "add	r6, r6, r10\n\t"
        "cmp	%[a], r6\n\t"
        "ble	2b\n\t"
        "\n3:\n\t"
        "mov	%[r], r12\n\t"
        "mov	r8, r9\n\t"
        "str	r3, [%[r], r8]\n\t"
        "mov	r3, r4\n\t"
        "mov	r4, r5\n\t"
        "add	r8, r8, #4\n\t"
        "mov	r9, r8\n\t"
        "mov	r6, #2\n\t"
        "lsl	r6, r6, #8\n\t"
        "add	r6, r6, #248\n\t"
        "cmp	r8, r6\n\t"
        "ble	1b\n\t"
        "str	r3, [%[r], r8]\n\t"
        "mov	%[a], r10\n\t"
        "mov	%[b], r11\n\t"
        :
        : [r] "r" (tmp), [a] "r" (a), [b] "r" (b)
        : "memory", "r3", "r4", "r5", "r6", "r8", "r9", "r10", "r11", "r12", "r14"
    );

    XMEMCPY(r, tmp, sizeof(tmp));
}

/* Square a and put result in r. (r = a * a)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 */
SP_NOINLINE static void sp_3072_sqr_96(sp_digit* r, const sp_digit* a)
{
    __asm__ __volatile__ (
        "mov	r3, #0\n\t"
        "mov	r4, #0\n\t"
        "mov	r5, #0\n\t"
        "mov	r9, r3\n\t"
        "mov	r12, %[r]\n\t"
        "mov	r6, #3\n\t"
        "lsl	r6, r6, #8\n\t"
        "neg	r6, r6\n\t"
        "add	sp, sp, r6\n\t"
        "mov	r11, sp\n\t"
        "mov	r10, %[a]\n\t"
        "\n1:\n\t"
        "mov	%[r], #0\n\t"
        "mov	r6, #1\n\t"
        "lsl	r6, r6, #8\n\t"
        "add	r6, r6, #124\n\t"
        "mov	%[a], r9\n\t"
        "subs	%[a], %[a], r6\n\t"
        "sbc	r6, r6, r6\n\t"
        "mvn	r6, r6\n\t"
        "and	%[a], %[a], r6\n\t"
        "mov	r2, r9\n\t"
        "sub	r2, r2, %[a]\n\t"
        "add	%[a], %[a], r10\n\t"
        "add	r2, r2, r10\n\t"
        "\n2:\n\t"
        "cmp	r2, %[a]\n\t"
        "beq	4f\n\t"
        /* Multiply * 2: Start */
        "ldr	r6, [%[a]]\n\t"
        "ldr	r8, [r2]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r3, r3, r6\n\t"
        "adcs 	r4, r4, r8\n\t"
        "adc	r5, r5, %[r]\n\t"
        "adds	r3, r3, r6\n\t"
        "adcs 	r4, r4, r8\n\t"
        "adc	r5, r5, %[r]\n\t"
        /* Multiply * 2: Done */
        "bal	5f\n\t"
        "\n4:\n\t"
        /* Square: Start */
        "ldr	r6, [%[a]]\n\t"
        "umull	r6, r8, r6, r6\n\t"
        "adds	r3, r3, r6\n\t"
        "adcs	r4, r4, r8\n\t"
        "adc	r5, r5, %[r]\n\t"
        /* Square: Done */
        "\n5:\n\t"
        "add	%[a], %[a], #4\n\t"
        "sub	r2, r2, #4\n\t"
        "mov	r6, #1\n\t"
        "lsl	r6, r6, #8\n\t"
        "add	r6, r6, #128\n\t"
        "add	r6, r6, r10\n\t"
        "cmp	%[a], r6\n\t"
        "beq	3f\n\t"
        "cmp	%[a], r2\n\t"
        "bgt	3f\n\t"
        "mov	r8, r9\n\t"
        "add	r8, r8, r10\n\t"
        "cmp	%[a], r8\n\t"
        "ble	2b\n\t"
        "\n3:\n\t"
        "mov	%[r], r11\n\t"
        "mov	r8, r9\n\t"
        "str	r3, [%[r], r8]\n\t"
        "mov	r3, r4\n\t"
        "mov	r4, r5\n\t"
        "mov	r5, #0\n\t"
        "add	r8, r8, #4\n\t"
        "mov	r9, r8\n\t"
        "mov	r6, #2\n\t"
        "lsl	r6, r6, #8\n\t"
        "add	r6, r6, #248\n\t"
        "cmp	r8, r6\n\t"
        "ble	1b\n\t"
        "mov	%[a], r10\n\t"
        "str	r3, [%[r], r8]\n\t"
        "mov	%[r], r12\n\t"
        "mov	%[a], r11\n\t"
        "mov	r3, #2\n\t"
        "lsl	r3, r3, #8\n\t"
        "add	r3, r3, #252\n\t"
        "\n4:\n\t"
        "ldr	r6, [%[a], r3]\n\t"
        "str	r6, [%[r], r3]\n\t"
        "subs	r3, r3, #4\n\t"
        "bge	4b\n\t"
        "mov	r6, #3\n\t"
        "lsl	r6, r6, #8\n\t"
        "add	sp, sp, r6\n\t"
        :
        : [r] "r" (r), [a] "r" (a)
        : "memory", "r2", "r3", "r4", "r5", "r6", "r8", "r9", "r10", "r11", "r12"
    );
}

#endif /* WOLFSSL_SP_SMALL */
#if (defined(WOLFSSL_HAVE_SP_RSA) || defined(WOLFSSL_HAVE_SP_DH)) && !defined(WOLFSSL_RSA_PUBLIC_ONLY)
#ifdef WOLFSSL_SP_SMALL
/* AND m into each word of a and store in r.
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * m  Mask to AND against each digit.
 */
static void sp_3072_mask_48(sp_digit* r, const sp_digit* a, sp_digit m)
{
    int i;

    for (i=0; i<48; i++) {
        r[i] = a[i] & m;
    }
}

#endif /* WOLFSSL_SP_SMALL */
#ifdef WOLFSSL_SP_SMALL
/* Add b to a into r. (r = a + b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A single precision integer.
 */
SP_NOINLINE static sp_digit sp_3072_add_48(sp_digit* r, const sp_digit* a,
        const sp_digit* b)
{
    sp_digit c = 0;

    __asm__ __volatile__ (
        "mov	r6, %[a]\n\t"
        "mov	r8, #0\n\t"
        "add	r6, r6, #192\n\t"
        "sub	r8, r8, #1\n\t"
        "\n1:\n\t"
        "adds	%[c], %[c], r8\n\t"
        "ldr	r4, [%[a]]\n\t"
        "ldr	r5, [%[b]]\n\t"
        "adcs	r4, r4, r5\n\t"
        "str	r4, [%[r]]\n\t"
        "mov	%[c], #0\n\t"
        "adc	%[c], %[c], %[c]\n\t"
        "add	%[a], %[a], #4\n\t"
        "add	%[b], %[b], #4\n\t"
        "add	%[r], %[r], #4\n\t"
        "cmp	%[a], r6\n\t"
        "bne	1b\n\t"
        : [c] "+r" (c), [r] "+r" (r), [a] "+r" (a), [b] "+r" (b)
        :
        : "memory", "r4", "r5", "r6", "r8"
    );

    return c;
}

#endif /* WOLFSSL_SP_SMALL */
#ifdef WOLFSSL_SP_SMALL
/* Sub b from a into a. (a -= b)
 *
 * a  A single precision integer.
 * b  A single precision integer.
 */
SP_NOINLINE static sp_digit sp_3072_sub_in_place_48(sp_digit* a,
        const sp_digit* b)
{
    sp_digit c = 0;
    __asm__ __volatile__ (
        "mov	r8, %[a]\n\t"
        "add	r8, r8, #192\n\t"
        "\n1:\n\t"
        "mov	r5, #0\n\t"
        "subs	r5, r5, %[c]\n\t"
        "ldr	r3, [%[a]]\n\t"
        "ldr	r4, [%[a], #4]\n\t"
        "ldr	r5, [%[b]]\n\t"
        "ldr	r6, [%[b], #4]\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "str	r3, [%[a]]\n\t"
        "str	r4, [%[a], #4]\n\t"
        "sbc	%[c], %[c], %[c]\n\t"
        "add	%[a], %[a], #8\n\t"
        "add	%[b], %[b], #8\n\t"
        "cmp	%[a], r8\n\t"
        "bne	1b\n\t"
        : [c] "+r" (c), [a] "+r" (a), [b] "+r" (b)
        :
        : "memory", "r3", "r4", "r5", "r6", "r8"
    );

    return c;
}

#endif /* WOLFSSL_SP_SMALL */
#ifdef WOLFSSL_SP_SMALL
/* Multiply a and b into r. (r = a * b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A single precision integer.
 */
SP_NOINLINE static void sp_3072_mul_48(sp_digit* r, const sp_digit* a,
        const sp_digit* b)
{
    sp_digit tmp[48 * 2];
    __asm__ __volatile__ (
        "mov	r3, #0\n\t"
        "mov	r4, #0\n\t"
        "mov	r9, r3\n\t"
        "mov	r12, %[r]\n\t"
        "mov	r10, %[a]\n\t"
        "mov	r11, %[b]\n\t"
        "mov	r6, #192\n\t"
        "add	r6, r6, r10\n\t"
        "mov	r14, r6\n\t"
        "\n1:\n\t"
        "mov	%[r], #0\n\t"
        "mov	r5, #0\n\t"
        "mov	r6, #188\n\t"
        "mov	%[a], r9\n\t"
        "subs	%[a], %[a], r6\n\t"
        "sbc	r6, r6, r6\n\t"
        "mvn	r6, r6\n\t"
        "and	%[a], %[a], r6\n\t"
        "mov	%[b], r9\n\t"
        "sub	%[b], %[b], %[a]\n\t"
        "add	%[a], %[a], r10\n\t"
        "add	%[b], %[b], r11\n\t"
        "\n2:\n\t"
        /* Multiply Start */
        "ldr	r6, [%[a]]\n\t"
        "ldr	r8, [%[b]]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r3, r3, r6\n\t"
        "adcs 	r4, r4, r8\n\t"
        "adc	r5, r5, %[r]\n\t"
        /* Multiply Done */
        "add	%[a], %[a], #4\n\t"
        "sub	%[b], %[b], #4\n\t"
        "cmp	%[a], r14\n\t"
        "beq	3f\n\t"
        "mov	r6, r9\n\t"
        "add	r6, r6, r10\n\t"
        "cmp	%[a], r6\n\t"
        "ble	2b\n\t"
        "\n3:\n\t"
        "mov	%[r], r12\n\t"
        "mov	r8, r9\n\t"
        "str	r3, [%[r], r8]\n\t"
        "mov	r3, r4\n\t"
        "mov	r4, r5\n\t"
        "add	r8, r8, #4\n\t"
        "mov	r9, r8\n\t"
        "mov	r6, #1\n\t"
        "lsl	r6, r6, #8\n\t"
        "add	r6, r6, #120\n\t"
        "cmp	r8, r6\n\t"
        "ble	1b\n\t"
        "str	r3, [%[r], r8]\n\t"
        "mov	%[a], r10\n\t"
        "mov	%[b], r11\n\t"
        :
        : [r] "r" (tmp), [a] "r" (a), [b] "r" (b)
        : "memory", "r3", "r4", "r5", "r6", "r8", "r9", "r10", "r11", "r12", "r14"
    );

    XMEMCPY(r, tmp, sizeof(tmp));
}

/* Square a and put result in r. (r = a * a)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 */
SP_NOINLINE static void sp_3072_sqr_48(sp_digit* r, const sp_digit* a)
{
    __asm__ __volatile__ (
        "mov	r3, #0\n\t"
        "mov	r4, #0\n\t"
        "mov	r5, #0\n\t"
        "mov	r9, r3\n\t"
        "mov	r12, %[r]\n\t"
        "mov	r6, #1\n\t"
        "lsl	r6, r6, #8\n\t"
        "add	r6, r6, #128\n\t"
        "neg	r6, r6\n\t"
        "add	sp, sp, r6\n\t"
        "mov	r11, sp\n\t"
        "mov	r10, %[a]\n\t"
        "\n1:\n\t"
        "mov	%[r], #0\n\t"
        "mov	r6, #188\n\t"
        "mov	%[a], r9\n\t"
        "subs	%[a], %[a], r6\n\t"
        "sbc	r6, r6, r6\n\t"
        "mvn	r6, r6\n\t"
        "and	%[a], %[a], r6\n\t"
        "mov	r2, r9\n\t"
        "sub	r2, r2, %[a]\n\t"
        "add	%[a], %[a], r10\n\t"
        "add	r2, r2, r10\n\t"
        "\n2:\n\t"
        "cmp	r2, %[a]\n\t"
        "beq	4f\n\t"
        /* Multiply * 2: Start */
        "ldr	r6, [%[a]]\n\t"
        "ldr	r8, [r2]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r3, r3, r6\n\t"
        "adcs 	r4, r4, r8\n\t"
        "adc	r5, r5, %[r]\n\t"
        "adds	r3, r3, r6\n\t"
        "adcs 	r4, r4, r8\n\t"
        "adc	r5, r5, %[r]\n\t"
        /* Multiply * 2: Done */
        "bal	5f\n\t"
        "\n4:\n\t"
        /* Square: Start */
        "ldr	r6, [%[a]]\n\t"
        "umull	r6, r8, r6, r6\n\t"
        "adds	r3, r3, r6\n\t"
        "adcs	r4, r4, r8\n\t"
        "adc	r5, r5, %[r]\n\t"
        /* Square: Done */
        "\n5:\n\t"
        "add	%[a], %[a], #4\n\t"
        "sub	r2, r2, #4\n\t"
        "mov	r6, #192\n\t"
        "add	r6, r6, r10\n\t"
        "cmp	%[a], r6\n\t"
        "beq	3f\n\t"
        "cmp	%[a], r2\n\t"
        "bgt	3f\n\t"
        "mov	r8, r9\n\t"
        "add	r8, r8, r10\n\t"
        "cmp	%[a], r8\n\t"
        "ble	2b\n\t"
        "\n3:\n\t"
        "mov	%[r], r11\n\t"
        "mov	r8, r9\n\t"
        "str	r3, [%[r], r8]\n\t"
        "mov	r3, r4\n\t"
        "mov	r4, r5\n\t"
        "mov	r5, #0\n\t"
        "add	r8, r8, #4\n\t"
        "mov	r9, r8\n\t"
        "mov	r6, #1\n\t"
        "lsl	r6, r6, #8\n\t"
        "add	r6, r6, #120\n\t"
        "cmp	r8, r6\n\t"
        "ble	1b\n\t"
        "mov	%[a], r10\n\t"
        "str	r3, [%[r], r8]\n\t"
        "mov	%[r], r12\n\t"
        "mov	%[a], r11\n\t"
        "mov	r3, #1\n\t"
        "lsl	r3, r3, #8\n\t"
        "add	r3, r3, #124\n\t"
        "\n4:\n\t"
        "ldr	r6, [%[a], r3]\n\t"
        "str	r6, [%[r], r3]\n\t"
        "subs	r3, r3, #4\n\t"
        "bge	4b\n\t"
        "mov	r6, #1\n\t"
        "lsl	r6, r6, #8\n\t"
        "add	r6, r6, #128\n\t"
        "add	sp, sp, r6\n\t"
        :
        : [r] "r" (r), [a] "r" (a)
        : "memory", "r2", "r3", "r4", "r5", "r6", "r8", "r9", "r10", "r11", "r12"
    );
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

    /* rho = -1/m mod b */
    *rho = -x;
}

/* Mul a by digit b into r. (r = a * b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A single precision digit.
 */
SP_NOINLINE static void sp_3072_mul_d_96(sp_digit* r, const sp_digit* a,
        sp_digit b)
{
    __asm__ __volatile__ (
        "add	r9, %[a], #384\n\t"
        /* A[0] * B */
        "ldr	r6, [%[a]], #4\n\t"
        "umull	r5, r3, r6, %[b]\n\t"
        "mov	r4, #0\n\t"
        "str	r5, [%[r]], #4\n\t"
        /* A[0] * B - Done */
        "\n1:\n\t"
        "mov	r5, #0\n\t"
        /* A[] * B */
        "ldr	r6, [%[a]], #4\n\t"
        "umull	r6, r8, r6, %[b]\n\t"
        "adds	r3, r3, r6\n\t"
        "adcs 	r4, r4, r8\n\t"
        "adc	r5, r5, #0\n\t"
        /* A[] * B - Done */
        "str	r3, [%[r]], #4\n\t"
        "mov	r3, r4\n\t"
        "mov	r4, r5\n\t"
        "cmp	%[a], r9\n\t"
        "blt	1b\n\t"
        "str	r3, [%[r]]\n\t"
        : [r] "+r" (r), [a] "+r" (a)
        : [b] "r" (b)
        : "memory", "r3", "r4", "r5", "r6", "r8", "r9"
    );
}

#if (defined(WOLFSSL_HAVE_SP_RSA) || defined(WOLFSSL_HAVE_SP_DH)) && !defined(WOLFSSL_RSA_PUBLIC_ONLY)
/* r = 2^n mod m where n is the number of bits to reduce by.
 * Given m must be 3072 bits, just need to subtract.
 *
 * r  A single precision number.
 * m  A single precision number.
 */
static void sp_3072_mont_norm_48(sp_digit* r, const sp_digit* m)
{
    XMEMSET(r, 0, sizeof(sp_digit) * 48);

    /* r = 2^n mod m */
    sp_3072_sub_in_place_48(r, m);
}

/* Conditionally subtract b from a using the mask m.
 * m is -1 to subtract and 0 when not copying.
 *
 * r  A single precision number representing condition subtract result.
 * a  A single precision number to subtract from.
 * b  A single precision number to subtract.
 * m  Mask value to apply.
 */
SP_NOINLINE static sp_digit sp_3072_cond_sub_48(sp_digit* r, const sp_digit* a,
        const sp_digit* b, sp_digit m)
{
    sp_digit c = 0;

    __asm__ __volatile__ (
        "mov	r5, #192\n\t"
        "mov	r9, r5\n\t"
        "mov	r8, #0\n\t"
        "\n1:\n\t"
        "ldr	r6, [%[b], r8]\n\t"
        "and	r6, r6, %[m]\n\t"
        "mov	r5, #0\n\t"
        "subs	r5, r5, %[c]\n\t"
        "ldr	r5, [%[a], r8]\n\t"
        "sbcs	r5, r5, r6\n\t"
        "sbcs	%[c], %[c], %[c]\n\t"
        "str	r5, [%[r], r8]\n\t"
        "add	r8, r8, #4\n\t"
        "cmp	r8, r9\n\t"
        "blt	1b\n\t"
        : [c] "+r" (c)
        : [r] "r" (r), [a] "r" (a), [b] "r" (b), [m] "r" (m)
        : "memory", "r5", "r6", "r8", "r9"
    );

    return c;
}

/* Reduce the number back to 3072 bits using Montgomery reduction.
 *
 * a   A single precision number to reduce in place.
 * m   The single precision number representing the modulus.
 * mp  The digit representing the negative inverse of m mod 2^n.
 */
SP_NOINLINE static void sp_3072_mont_reduce_48(sp_digit* a, const sp_digit* m,
        sp_digit mp)
{
    sp_digit ca = 0;

    __asm__ __volatile__ (
        "mov	r9, %[mp]\n\t"
        "mov	r12, %[m]\n\t"
        "mov	r10, %[a]\n\t"
        "mov	r4, #0\n\t"
        "add	r11, r10, #192\n\t"
        "\n1:\n\t"
        /* mu = a[i] * mp */
        "mov	%[mp], r9\n\t"
        "ldr	%[a], [r10]\n\t"
        "mul	%[mp], %[mp], %[a]\n\t"
        "mov	%[m], r12\n\t"
        "add	r14, r10, #184\n\t"
        "\n2:\n\t"
        /* a[i+j] += m[j] * mu */
        "ldr	%[a], [r10]\n\t"
        "mov	r5, #0\n\t"
        /* Multiply m[j] and mu - Start */
        "ldr	r8, [%[m]], #4\n\t"
        "umull	r6, r8, %[mp], r8\n\t"
        "adds	%[a], %[a], r6\n\t"
        "adc	r5, r5, r8\n\t"
        /* Multiply m[j] and mu - Done */
        "adds	r4, r4, %[a]\n\t"
        "adc	r5, r5, #0\n\t"
        "str	r4, [r10], #4\n\t"
        /* a[i+j+1] += m[j+1] * mu */
        "ldr	%[a], [r10]\n\t"
        "mov	r4, #0\n\t"
        /* Multiply m[j] and mu - Start */
        "ldr	r8, [%[m]], #4\n\t"
        "umull	r6, r8, %[mp], r8\n\t"
        "adds	%[a], %[a], r6\n\t"
        "adc	r4, r4, r8\n\t"
        /* Multiply m[j] and mu - Done */
        "adds	r5, r5, %[a]\n\t"
        "adc	r4, r4, #0\n\t"
        "str	r5, [r10], #4\n\t"
        "cmp	r10, r14\n\t"
        "blt	2b\n\t"
        /* a[i+46] += m[46] * mu */
        "ldr	%[a], [r10]\n\t"
        "mov	r5, #0\n\t"
        /* Multiply m[j] and mu - Start */
        "ldr	r8, [%[m]], #4\n\t"
        "umull	r6, r8, %[mp], r8\n\t"
        "adds	%[a], %[a], r6\n\t"
        "adc	r5, r5, r8\n\t"
        /* Multiply m[j] and mu - Done */
        "adds	r4, r4, %[a]\n\t"
        "adc	r5, r5, #0\n\t"
        "str	r4, [r10], #4\n\t"
        /* a[i+47] += m[47] * mu */
        "mov	r4, %[ca]\n\t"
        "mov	%[ca], #0\n\t"
        /* Multiply m[47] and mu - Start */
        "ldr	r8, [%[m]]\n\t"
        "umull	r6, r8, %[mp], r8\n\t"
        "adds	r5, r5, r6\n\t"
        "adcs 	r4, r4, r8\n\t"
        "adc	%[ca], %[ca], #0\n\t"
        /* Multiply m[47] and mu - Done */
        "ldr	r6, [r10]\n\t"
        "ldr	r8, [r10, #4]\n\t"
        "adds	r6, r6, r5\n\t"
        "adcs	r8, r8, r4\n\t"
        "adc	%[ca], %[ca], #0\n\t"
        "str	r6, [r10]\n\t"
        "str	r8, [r10, #4]\n\t"
        /* Next word in a */
        "sub	r10, r10, #184\n\t"
        "cmp	r10, r11\n\t"
        "blt	1b\n\t"
        "mov	%[a], r10\n\t"
        "mov	%[m], r12\n\t"
        : [ca] "+r" (ca), [a] "+r" (a)
        : [m] "r" (m), [mp] "r" (mp)
        : "memory", "r4", "r5", "r6", "r8", "r9", "r10", "r11", "r12", "r14"
    );

    sp_3072_cond_sub_48(a - 48, a, m, (sp_digit)0 - ca);
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
static void sp_3072_mont_mul_48(sp_digit* r, const sp_digit* a, const sp_digit* b,
        const sp_digit* m, sp_digit mp)
{
    sp_3072_mul_48(r, a, b);
    sp_3072_mont_reduce_48(r, m, mp);
}

/* Square the Montgomery form number. (r = a * a mod m)
 *
 * r   Result of squaring.
 * a   Number to square in Montogmery form.
 * m   Modulus (prime).
 * mp  Montogmery mulitplier.
 */
static void sp_3072_mont_sqr_48(sp_digit* r, const sp_digit* a, const sp_digit* m,
        sp_digit mp)
{
    sp_3072_sqr_48(r, a);
    sp_3072_mont_reduce_48(r, m, mp);
}

/* Mul a by digit b into r. (r = a * b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A single precision digit.
 */
SP_NOINLINE static void sp_3072_mul_d_48(sp_digit* r, const sp_digit* a,
        sp_digit b)
{
    __asm__ __volatile__ (
        "add	r9, %[a], #192\n\t"
        /* A[0] * B */
        "ldr	r6, [%[a]], #4\n\t"
        "umull	r5, r3, r6, %[b]\n\t"
        "mov	r4, #0\n\t"
        "str	r5, [%[r]], #4\n\t"
        /* A[0] * B - Done */
        "\n1:\n\t"
        "mov	r5, #0\n\t"
        /* A[] * B */
        "ldr	r6, [%[a]], #4\n\t"
        "umull	r6, r8, r6, %[b]\n\t"
        "adds	r3, r3, r6\n\t"
        "adcs 	r4, r4, r8\n\t"
        "adc	r5, r5, #0\n\t"
        /* A[] * B - Done */
        "str	r3, [%[r]], #4\n\t"
        "mov	r3, r4\n\t"
        "mov	r4, r5\n\t"
        "cmp	%[a], r9\n\t"
        "blt	1b\n\t"
        "str	r3, [%[r]]\n\t"
        : [r] "+r" (r), [a] "+r" (a)
        : [b] "r" (b)
        : "memory", "r3", "r4", "r5", "r6", "r8", "r9"
    );
}

/* Divide the double width number (d1|d0) by the dividend. (d1|d0 / div)
 *
 * d1   The high order half of the number to divide.
 * d0   The low order half of the number to divide.
 * div  The dividend.
 * returns the result of the division.
 *
 * Note that this is an approximate div. It may give an answer 1 larger.
 */
SP_NOINLINE static sp_digit div_3072_word_48(sp_digit d1, sp_digit d0,
        sp_digit div)
{
    sp_digit r = 0;

    __asm__ __volatile__ (
        "lsr	r6, %[div], #16\n\t"
        "add	r6, r6, #1\n\t"
        "udiv	r4, %[d1], r6\n\t"
        "lsl	r8, r4, #16\n\t"
        "umull	r4, r5, %[div], r8\n\t"
        "subs	%[d0], %[d0], r4\n\t"
        "sbc	%[d1], %[d1], r5\n\t"
        "udiv	r5, %[d1], r6\n\t"
        "lsl	r4, r5, #16\n\t"
        "add	r8, r8, r4\n\t"
        "umull	r4, r5, %[div], r4\n\t"
        "subs	%[d0], %[d0], r4\n\t"
        "sbc	%[d1], %[d1], r5\n\t"
        "lsl	r4, %[d1], #16\n\t"
        "orr	r4, r4, %[d0], lsr #16\n\t"
        "udiv	r4, r4, r6\n\t"
        "add	r8, r8, r4\n\t"
        "umull	r4, r5, %[div], r4\n\t"
        "subs	%[d0], %[d0], r4\n\t"
        "sbc	%[d1], %[d1], r5\n\t"
        "lsl	r4, %[d1], #16\n\t"
        "orr	r4, r4, %[d0], lsr #16\n\t"
        "udiv	r4, r4, r6\n\t"
        "add	r8, r8, r4\n\t"
        "umull	r4, r5, %[div], r4\n\t"
        "subs	%[d0], %[d0], r4\n\t"
        "sbc	%[d1], %[d1], r5\n\t"
        "udiv	r4, %[d0], %[div]\n\t"
        "add	r8, r8, r4\n\t"
        "mov	%[r], r8\n\t"
        : [r] "+r" (r)
        : [d1] "r" (d1), [d0] "r" (d0), [div] "r" (div)
        : "r4", "r5", "r6", "r8"
    );
    return r;
}

/* Compare a with b in constant time.
 *
 * a  A single precision integer.
 * b  A single precision integer.
 * return -ve, 0 or +ve if a is less than, equal to or greater than b
 * respectively.
 */
SP_NOINLINE static int32_t sp_3072_cmp_48(const sp_digit* a, const sp_digit* b)
{
    sp_digit r = 0;


    __asm__ __volatile__ (
        "mov	r3, #0\n\t"
        "mvn	r3, r3\n\t"
        "mov	r6, #188\n\t"
        "\n1:\n\t"
        "ldr	r8, [%[a], r6]\n\t"
        "ldr	r5, [%[b], r6]\n\t"
        "and	r8, r8, r3\n\t"
        "and	r5, r5, r3\n\t"
        "mov	r4, r8\n\t"
        "subs	r8, r8, r5\n\t"
        "sbc	r8, r8, r8\n\t"
        "add	%[r], %[r], r8\n\t"
        "mvn	r8, r8\n\t"
        "and	r3, r3, r8\n\t"
        "subs	r5, r5, r4\n\t"
        "sbc	r8, r8, r8\n\t"
        "sub	%[r], %[r], r8\n\t"
        "mvn	r8, r8\n\t"
        "and	r3, r3, r8\n\t"
        "sub	r6, r6, #4\n\t"
        "cmp	r6, #0\n\t"
        "bge	1b\n\t"
        : [r] "+r" (r)
        : [a] "r" (a), [b] "r" (b)
        : "r3", "r4", "r5", "r6", "r8"
    );

    return r;
}

/* Divide d in a and put remainder into r (m*d + r = a)
 * m is not calculated as it is not needed at this time.
 *
 * a  Nmber to be divided.
 * d  Number to divide with.
 * m  Multiplier result.
 * r  Remainder from the division.
 * returns MP_OKAY indicating success.
 */
static WC_INLINE int sp_3072_div_48(const sp_digit* a, const sp_digit* d, sp_digit* m,
        sp_digit* r)
{
    sp_digit t1[96], t2[49];
    sp_digit div, r1;
    int i;

    (void)m;

    div = d[47];
    XMEMCPY(t1, a, sizeof(*t1) * 2 * 48);
    for (i=47; i>=0; i--) {
        r1 = div_3072_word_48(t1[48 + i], t1[48 + i - 1], div);

        sp_3072_mul_d_48(t2, d, r1);
        t1[48 + i] += sp_3072_sub_in_place_48(&t1[i], t2);
        t1[48 + i] -= t2[48];
        sp_3072_mask_48(t2, d, t1[48 + i]);
        t1[48 + i] += sp_3072_add_48(&t1[i], &t1[i], t2);
        sp_3072_mask_48(t2, d, t1[48 + i]);
        t1[48 + i] += sp_3072_add_48(&t1[i], &t1[i], t2);
    }

    r1 = sp_3072_cmp_48(t1, d) >= 0;
    sp_3072_cond_sub_48(r, t1, d, (sp_digit)0 - r1);

    return MP_OKAY;
}

/* Reduce a modulo m into r. (r = a mod m)
 *
 * r  A single precision number that is the reduced result.
 * a  A single precision number that is to be reduced.
 * m  A single precision number that is the modulus to reduce with.
 * returns MP_OKAY indicating success.
 */
static WC_INLINE int sp_3072_mod_48(sp_digit* r, const sp_digit* a, const sp_digit* m)
{
    return sp_3072_div_48(a, m, NULL, r);
}

#ifdef WOLFSSL_SP_SMALL
/* Modular exponentiate a to the e mod m. (r = a^e mod m)
 *
 * r     A single precision number that is the result of the operation.
 * a     A single precision number being exponentiated.
 * e     A single precision number that is the exponent.
 * bits  The number of bits in the exponent.
 * m     A single precision number that is the modulus.
 * returns 0 on success and MEMORY_E on dynamic memory allocation failure.
 */
static int sp_3072_mod_exp_48(sp_digit* r, const sp_digit* a, const sp_digit* e,
        int bits, const sp_digit* m, int reduceA)
{
#if defined(WOLFSSL_SMALL_STACK) && !defined(WOLFSSL_SP_NO_MALLOC)
    sp_digit* td;
#else
    sp_digit td[16 * 96];
#endif
    sp_digit* t[16];
    sp_digit* norm;
    sp_digit mp = 1;
    sp_digit n;
    sp_digit mask;
    int i;
    int c, y;
    int err = MP_OKAY;

#if defined(WOLFSSL_SMALL_STACK) && !defined(WOLFSSL_SP_NO_MALLOC)
    td = (sp_digit*)XMALLOC(sizeof(sp_digit) * (16 * 96), NULL,
                            DYNAMIC_TYPE_TMP_BUFFER);
    if (td == NULL) {
        err = MEMORY_E;
    }
#endif

    if (err == MP_OKAY) {
        norm = td;
        for (i=0; i<16; i++) {
#if defined(WOLFSSL_SMALL_STACK) && !defined(WOLFSSL_SP_NO_MALLOC)
            t[i] = td + i * 96;
#else
            t[i] = &td[i * 96];
#endif
        }

        sp_3072_mont_setup(m, &mp);
        sp_3072_mont_norm_48(norm, m);

        XMEMSET(t[1], 0, sizeof(sp_digit) * 48U);
        if (reduceA != 0) {
            err = sp_3072_mod_48(t[1] + 48, a, m);
            if (err == MP_OKAY) {
                err = sp_3072_mod_48(t[1], t[1], m);
            }
        }
        else {
            XMEMCPY(t[1] + 48, a, sizeof(sp_digit) * 48);
            err = sp_3072_mod_48(t[1], t[1], m);
        }
    }

    if (err == MP_OKAY) {
        sp_3072_mont_sqr_48(t[ 2], t[ 1], m, mp);
        sp_3072_mont_mul_48(t[ 3], t[ 2], t[ 1], m, mp);
        sp_3072_mont_sqr_48(t[ 4], t[ 2], m, mp);
        sp_3072_mont_mul_48(t[ 5], t[ 3], t[ 2], m, mp);
        sp_3072_mont_sqr_48(t[ 6], t[ 3], m, mp);
        sp_3072_mont_mul_48(t[ 7], t[ 4], t[ 3], m, mp);
        sp_3072_mont_sqr_48(t[ 8], t[ 4], m, mp);
        sp_3072_mont_mul_48(t[ 9], t[ 5], t[ 4], m, mp);
        sp_3072_mont_sqr_48(t[10], t[ 5], m, mp);
        sp_3072_mont_mul_48(t[11], t[ 6], t[ 5], m, mp);
        sp_3072_mont_sqr_48(t[12], t[ 6], m, mp);
        sp_3072_mont_mul_48(t[13], t[ 7], t[ 6], m, mp);
        sp_3072_mont_sqr_48(t[14], t[ 7], m, mp);
        sp_3072_mont_mul_48(t[15], t[ 8], t[ 7], m, mp);

        i = (bits - 1) / 32;
        n = e[i--];
        c = bits & 31;
        if (c == 0) {
            c = 32;
        }
        c -= bits % 4;
        if (c == 32) {
            c = 28;
        }
        y = (int)(n >> c);
        n <<= 32 - c;
        XMEMCPY(r, t[y], sizeof(sp_digit) * 48);
        for (; i>=0 || c>=4; ) {
            if (c == 0) {
                n = e[i--];
                y = n >> 28;
                n <<= 4;
                c = 28;
            }
            else if (c < 4) {
                y = n >> 28;
                n = e[i--];
                c = 4 - c;
                y |= n >> (32 - c);
                n <<= c;
                c = 32 - c;
            }
            else {
                y = (n >> 28) & 0xf;
                n <<= 4;
                c -= 4;
            }

            sp_3072_mont_sqr_48(r, r, m, mp);
            sp_3072_mont_sqr_48(r, r, m, mp);
            sp_3072_mont_sqr_48(r, r, m, mp);
            sp_3072_mont_sqr_48(r, r, m, mp);

            sp_3072_mont_mul_48(r, r, t[y], m, mp);
        }

        XMEMSET(&r[48], 0, sizeof(sp_digit) * 48U);
        sp_3072_mont_reduce_48(r, m, mp);

        mask = 0 - (sp_3072_cmp_48(r, m) >= 0);
        sp_3072_cond_sub_48(r, r, m, mask);
    }

#if defined(WOLFSSL_SMALL_STACK) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (td != NULL) {
        XFREE(td, NULL, DYNAMIC_TYPE_TMP_BUFFER);
    }
#endif

    return err;
}
#else
/* Modular exponentiate a to the e mod m. (r = a^e mod m)
 *
 * r     A single precision number that is the result of the operation.
 * a     A single precision number being exponentiated.
 * e     A single precision number that is the exponent.
 * bits  The number of bits in the exponent.
 * m     A single precision number that is the modulus.
 * returns 0 on success and MEMORY_E on dynamic memory allocation failure.
 */
static int sp_3072_mod_exp_48(sp_digit* r, const sp_digit* a, const sp_digit* e,
        int bits, const sp_digit* m, int reduceA)
{
#if defined(WOLFSSL_SMALL_STACK) && !defined(WOLFSSL_SP_NO_MALLOC)
    sp_digit* td;
#else
    sp_digit td[32 * 96];
#endif
    sp_digit* t[32];
    sp_digit* norm;
    sp_digit mp = 1;
    sp_digit n;
    sp_digit mask;
    int i;
    int c, y;
    int err = MP_OKAY;

#if defined(WOLFSSL_SMALL_STACK) && !defined(WOLFSSL_SP_NO_MALLOC)
    td = (sp_digit*)XMALLOC(sizeof(sp_digit) * (32 * 96), NULL,
                            DYNAMIC_TYPE_TMP_BUFFER);
    if (td == NULL) {
        err = MEMORY_E;
    }
#endif

    if (err == MP_OKAY) {
        norm = td;
        for (i=0; i<32; i++) {
#if defined(WOLFSSL_SMALL_STACK) && !defined(WOLFSSL_SP_NO_MALLOC)
            t[i] = td + i * 96;
#else
            t[i] = &td[i * 96];
#endif
        }

        sp_3072_mont_setup(m, &mp);
        sp_3072_mont_norm_48(norm, m);

        XMEMSET(t[1], 0, sizeof(sp_digit) * 48U);
        if (reduceA != 0) {
            err = sp_3072_mod_48(t[1] + 48, a, m);
            if (err == MP_OKAY) {
                err = sp_3072_mod_48(t[1], t[1], m);
            }
        }
        else {
            XMEMCPY(t[1] + 48, a, sizeof(sp_digit) * 48);
            err = sp_3072_mod_48(t[1], t[1], m);
        }
    }

    if (err == MP_OKAY) {
        sp_3072_mont_sqr_48(t[ 2], t[ 1], m, mp);
        sp_3072_mont_mul_48(t[ 3], t[ 2], t[ 1], m, mp);
        sp_3072_mont_sqr_48(t[ 4], t[ 2], m, mp);
        sp_3072_mont_mul_48(t[ 5], t[ 3], t[ 2], m, mp);
        sp_3072_mont_sqr_48(t[ 6], t[ 3], m, mp);
        sp_3072_mont_mul_48(t[ 7], t[ 4], t[ 3], m, mp);
        sp_3072_mont_sqr_48(t[ 8], t[ 4], m, mp);
        sp_3072_mont_mul_48(t[ 9], t[ 5], t[ 4], m, mp);
        sp_3072_mont_sqr_48(t[10], t[ 5], m, mp);
        sp_3072_mont_mul_48(t[11], t[ 6], t[ 5], m, mp);
        sp_3072_mont_sqr_48(t[12], t[ 6], m, mp);
        sp_3072_mont_mul_48(t[13], t[ 7], t[ 6], m, mp);
        sp_3072_mont_sqr_48(t[14], t[ 7], m, mp);
        sp_3072_mont_mul_48(t[15], t[ 8], t[ 7], m, mp);
        sp_3072_mont_sqr_48(t[16], t[ 8], m, mp);
        sp_3072_mont_mul_48(t[17], t[ 9], t[ 8], m, mp);
        sp_3072_mont_sqr_48(t[18], t[ 9], m, mp);
        sp_3072_mont_mul_48(t[19], t[10], t[ 9], m, mp);
        sp_3072_mont_sqr_48(t[20], t[10], m, mp);
        sp_3072_mont_mul_48(t[21], t[11], t[10], m, mp);
        sp_3072_mont_sqr_48(t[22], t[11], m, mp);
        sp_3072_mont_mul_48(t[23], t[12], t[11], m, mp);
        sp_3072_mont_sqr_48(t[24], t[12], m, mp);
        sp_3072_mont_mul_48(t[25], t[13], t[12], m, mp);
        sp_3072_mont_sqr_48(t[26], t[13], m, mp);
        sp_3072_mont_mul_48(t[27], t[14], t[13], m, mp);
        sp_3072_mont_sqr_48(t[28], t[14], m, mp);
        sp_3072_mont_mul_48(t[29], t[15], t[14], m, mp);
        sp_3072_mont_sqr_48(t[30], t[15], m, mp);
        sp_3072_mont_mul_48(t[31], t[16], t[15], m, mp);

        i = (bits - 1) / 32;
        n = e[i--];
        c = bits & 31;
        if (c == 0) {
            c = 32;
        }
        c -= bits % 5;
        if (c == 32) {
            c = 27;
        }
        y = (int)(n >> c);
        n <<= 32 - c;
        XMEMCPY(r, t[y], sizeof(sp_digit) * 48);
        for (; i>=0 || c>=5; ) {
            if (c == 0) {
                n = e[i--];
                y = n >> 27;
                n <<= 5;
                c = 27;
            }
            else if (c < 5) {
                y = n >> 27;
                n = e[i--];
                c = 5 - c;
                y |= n >> (32 - c);
                n <<= c;
                c = 32 - c;
            }
            else {
                y = (n >> 27) & 0x1f;
                n <<= 5;
                c -= 5;
            }

            sp_3072_mont_sqr_48(r, r, m, mp);
            sp_3072_mont_sqr_48(r, r, m, mp);
            sp_3072_mont_sqr_48(r, r, m, mp);
            sp_3072_mont_sqr_48(r, r, m, mp);
            sp_3072_mont_sqr_48(r, r, m, mp);

            sp_3072_mont_mul_48(r, r, t[y], m, mp);
        }

        XMEMSET(&r[48], 0, sizeof(sp_digit) * 48U);
        sp_3072_mont_reduce_48(r, m, mp);

        mask = 0 - (sp_3072_cmp_48(r, m) >= 0);
        sp_3072_cond_sub_48(r, r, m, mask);
    }

#if defined(WOLFSSL_SMALL_STACK) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (td != NULL) {
        XFREE(td, NULL, DYNAMIC_TYPE_TMP_BUFFER);
    }
#endif

    return err;
}
#endif /* WOLFSSL_SP_SMALL */

#endif /* (WOLFSSL_HAVE_SP_RSA || WOLFSSL_HAVE_SP_DH) && !WOLFSSL_RSA_PUBLIC_ONLY */

#if defined(WOLFSSL_HAVE_SP_RSA) || defined(WOLFSSL_HAVE_SP_DH)
/* r = 2^n mod m where n is the number of bits to reduce by.
 * Given m must be 3072 bits, just need to subtract.
 *
 * r  A single precision number.
 * m  A single precision number.
 */
static void sp_3072_mont_norm_96(sp_digit* r, const sp_digit* m)
{
    XMEMSET(r, 0, sizeof(sp_digit) * 96);

    /* r = 2^n mod m */
    sp_3072_sub_in_place_96(r, m);
}

#endif /* WOLFSSL_HAVE_SP_RSA || WOLFSSL_HAVE_SP_DH */
/* Conditionally subtract b from a using the mask m.
 * m is -1 to subtract and 0 when not copying.
 *
 * r  A single precision number representing condition subtract result.
 * a  A single precision number to subtract from.
 * b  A single precision number to subtract.
 * m  Mask value to apply.
 */
SP_NOINLINE static sp_digit sp_3072_cond_sub_96(sp_digit* r, const sp_digit* a,
        const sp_digit* b, sp_digit m)
{
    sp_digit c = 0;

    __asm__ __volatile__ (
        "mov	r5, #1\n\t"
        "lsl	r5, r5, #8\n\t"
        "add	r5, r5, #128\n\t"
        "mov	r9, r5\n\t"
        "mov	r8, #0\n\t"
        "\n1:\n\t"
        "ldr	r6, [%[b], r8]\n\t"
        "and	r6, r6, %[m]\n\t"
        "mov	r5, #0\n\t"
        "subs	r5, r5, %[c]\n\t"
        "ldr	r5, [%[a], r8]\n\t"
        "sbcs	r5, r5, r6\n\t"
        "sbcs	%[c], %[c], %[c]\n\t"
        "str	r5, [%[r], r8]\n\t"
        "add	r8, r8, #4\n\t"
        "cmp	r8, r9\n\t"
        "blt	1b\n\t"
        : [c] "+r" (c)
        : [r] "r" (r), [a] "r" (a), [b] "r" (b), [m] "r" (m)
        : "memory", "r5", "r6", "r8", "r9"
    );

    return c;
}

/* Reduce the number back to 3072 bits using Montgomery reduction.
 *
 * a   A single precision number to reduce in place.
 * m   The single precision number representing the modulus.
 * mp  The digit representing the negative inverse of m mod 2^n.
 */
SP_NOINLINE static void sp_3072_mont_reduce_96(sp_digit* a, const sp_digit* m,
        sp_digit mp)
{
    sp_digit ca = 0;

    __asm__ __volatile__ (
        "mov	r9, %[mp]\n\t"
        "mov	r12, %[m]\n\t"
        "mov	r10, %[a]\n\t"
        "mov	r4, #0\n\t"
        "add	r11, r10, #384\n\t"
        "\n1:\n\t"
        /* mu = a[i] * mp */
        "mov	%[mp], r9\n\t"
        "ldr	%[a], [r10]\n\t"
        "mul	%[mp], %[mp], %[a]\n\t"
        "mov	%[m], r12\n\t"
        "add	r14, r10, #376\n\t"
        "\n2:\n\t"
        /* a[i+j] += m[j] * mu */
        "ldr	%[a], [r10]\n\t"
        "mov	r5, #0\n\t"
        /* Multiply m[j] and mu - Start */
        "ldr	r8, [%[m]], #4\n\t"
        "umull	r6, r8, %[mp], r8\n\t"
        "adds	%[a], %[a], r6\n\t"
        "adc	r5, r5, r8\n\t"
        /* Multiply m[j] and mu - Done */
        "adds	r4, r4, %[a]\n\t"
        "adc	r5, r5, #0\n\t"
        "str	r4, [r10], #4\n\t"
        /* a[i+j+1] += m[j+1] * mu */
        "ldr	%[a], [r10]\n\t"
        "mov	r4, #0\n\t"
        /* Multiply m[j] and mu - Start */
        "ldr	r8, [%[m]], #4\n\t"
        "umull	r6, r8, %[mp], r8\n\t"
        "adds	%[a], %[a], r6\n\t"
        "adc	r4, r4, r8\n\t"
        /* Multiply m[j] and mu - Done */
        "adds	r5, r5, %[a]\n\t"
        "adc	r4, r4, #0\n\t"
        "str	r5, [r10], #4\n\t"
        "cmp	r10, r14\n\t"
        "blt	2b\n\t"
        /* a[i+94] += m[94] * mu */
        "ldr	%[a], [r10]\n\t"
        "mov	r5, #0\n\t"
        /* Multiply m[j] and mu - Start */
        "ldr	r8, [%[m]], #4\n\t"
        "umull	r6, r8, %[mp], r8\n\t"
        "adds	%[a], %[a], r6\n\t"
        "adc	r5, r5, r8\n\t"
        /* Multiply m[j] and mu - Done */
        "adds	r4, r4, %[a]\n\t"
        "adc	r5, r5, #0\n\t"
        "str	r4, [r10], #4\n\t"
        /* a[i+95] += m[95] * mu */
        "mov	r4, %[ca]\n\t"
        "mov	%[ca], #0\n\t"
        /* Multiply m[95] and mu - Start */
        "ldr	r8, [%[m]]\n\t"
        "umull	r6, r8, %[mp], r8\n\t"
        "adds	r5, r5, r6\n\t"
        "adcs 	r4, r4, r8\n\t"
        "adc	%[ca], %[ca], #0\n\t"
        /* Multiply m[95] and mu - Done */
        "ldr	r6, [r10]\n\t"
        "ldr	r8, [r10, #4]\n\t"
        "adds	r6, r6, r5\n\t"
        "adcs	r8, r8, r4\n\t"
        "adc	%[ca], %[ca], #0\n\t"
        "str	r6, [r10]\n\t"
        "str	r8, [r10, #4]\n\t"
        /* Next word in a */
        "sub	r10, r10, #376\n\t"
        "cmp	r10, r11\n\t"
        "blt	1b\n\t"
        "mov	%[a], r10\n\t"
        "mov	%[m], r12\n\t"
        : [ca] "+r" (ca), [a] "+r" (a)
        : [m] "r" (m), [mp] "r" (mp)
        : "memory", "r4", "r5", "r6", "r8", "r9", "r10", "r11", "r12", "r14"
    );

    sp_3072_cond_sub_96(a - 96, a, m, (sp_digit)0 - ca);
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
static void sp_3072_mont_mul_96(sp_digit* r, const sp_digit* a, const sp_digit* b,
        const sp_digit* m, sp_digit mp)
{
    sp_3072_mul_96(r, a, b);
    sp_3072_mont_reduce_96(r, m, mp);
}

/* Square the Montgomery form number. (r = a * a mod m)
 *
 * r   Result of squaring.
 * a   Number to square in Montogmery form.
 * m   Modulus (prime).
 * mp  Montogmery mulitplier.
 */
static void sp_3072_mont_sqr_96(sp_digit* r, const sp_digit* a, const sp_digit* m,
        sp_digit mp)
{
    sp_3072_sqr_96(r, a);
    sp_3072_mont_reduce_96(r, m, mp);
}

/* Divide the double width number (d1|d0) by the dividend. (d1|d0 / div)
 *
 * d1   The high order half of the number to divide.
 * d0   The low order half of the number to divide.
 * div  The dividend.
 * returns the result of the division.
 *
 * Note that this is an approximate div. It may give an answer 1 larger.
 */
SP_NOINLINE static sp_digit div_3072_word_96(sp_digit d1, sp_digit d0,
        sp_digit div)
{
    sp_digit r = 0;

    __asm__ __volatile__ (
        "lsr	r6, %[div], #16\n\t"
        "add	r6, r6, #1\n\t"
        "udiv	r4, %[d1], r6\n\t"
        "lsl	r8, r4, #16\n\t"
        "umull	r4, r5, %[div], r8\n\t"
        "subs	%[d0], %[d0], r4\n\t"
        "sbc	%[d1], %[d1], r5\n\t"
        "udiv	r5, %[d1], r6\n\t"
        "lsl	r4, r5, #16\n\t"
        "add	r8, r8, r4\n\t"
        "umull	r4, r5, %[div], r4\n\t"
        "subs	%[d0], %[d0], r4\n\t"
        "sbc	%[d1], %[d1], r5\n\t"
        "lsl	r4, %[d1], #16\n\t"
        "orr	r4, r4, %[d0], lsr #16\n\t"
        "udiv	r4, r4, r6\n\t"
        "add	r8, r8, r4\n\t"
        "umull	r4, r5, %[div], r4\n\t"
        "subs	%[d0], %[d0], r4\n\t"
        "sbc	%[d1], %[d1], r5\n\t"
        "lsl	r4, %[d1], #16\n\t"
        "orr	r4, r4, %[d0], lsr #16\n\t"
        "udiv	r4, r4, r6\n\t"
        "add	r8, r8, r4\n\t"
        "umull	r4, r5, %[div], r4\n\t"
        "subs	%[d0], %[d0], r4\n\t"
        "sbc	%[d1], %[d1], r5\n\t"
        "udiv	r4, %[d0], %[div]\n\t"
        "add	r8, r8, r4\n\t"
        "mov	%[r], r8\n\t"
        : [r] "+r" (r)
        : [d1] "r" (d1), [d0] "r" (d0), [div] "r" (div)
        : "r4", "r5", "r6", "r8"
    );
    return r;
}

/* AND m into each word of a and store in r.
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * m  Mask to AND against each digit.
 */
static void sp_3072_mask_96(sp_digit* r, const sp_digit* a, sp_digit m)
{
#ifdef WOLFSSL_SP_SMALL
    int i;

    for (i=0; i<96; i++) {
        r[i] = a[i] & m;
    }
#else
    int i;

    for (i = 0; i < 96; i += 8) {
        r[i+0] = a[i+0] & m;
        r[i+1] = a[i+1] & m;
        r[i+2] = a[i+2] & m;
        r[i+3] = a[i+3] & m;
        r[i+4] = a[i+4] & m;
        r[i+5] = a[i+5] & m;
        r[i+6] = a[i+6] & m;
        r[i+7] = a[i+7] & m;
    }
#endif
}

/* Compare a with b in constant time.
 *
 * a  A single precision integer.
 * b  A single precision integer.
 * return -ve, 0 or +ve if a is less than, equal to or greater than b
 * respectively.
 */
SP_NOINLINE static int32_t sp_3072_cmp_96(const sp_digit* a, const sp_digit* b)
{
    sp_digit r = 0;


    __asm__ __volatile__ (
        "mov	r3, #0\n\t"
        "mvn	r3, r3\n\t"
        "mov	r6, #1\n\t"
        "lsl	r6, r6, #8\n\t"
        "add	r6, r6, #124\n\t"
        "\n1:\n\t"
        "ldr	r8, [%[a], r6]\n\t"
        "ldr	r5, [%[b], r6]\n\t"
        "and	r8, r8, r3\n\t"
        "and	r5, r5, r3\n\t"
        "mov	r4, r8\n\t"
        "subs	r8, r8, r5\n\t"
        "sbc	r8, r8, r8\n\t"
        "add	%[r], %[r], r8\n\t"
        "mvn	r8, r8\n\t"
        "and	r3, r3, r8\n\t"
        "subs	r5, r5, r4\n\t"
        "sbc	r8, r8, r8\n\t"
        "sub	%[r], %[r], r8\n\t"
        "mvn	r8, r8\n\t"
        "and	r3, r3, r8\n\t"
        "sub	r6, r6, #4\n\t"
        "cmp	r6, #0\n\t"
        "bge	1b\n\t"
        : [r] "+r" (r)
        : [a] "r" (a), [b] "r" (b)
        : "r3", "r4", "r5", "r6", "r8"
    );

    return r;
}

/* Divide d in a and put remainder into r (m*d + r = a)
 * m is not calculated as it is not needed at this time.
 *
 * a  Nmber to be divided.
 * d  Number to divide with.
 * m  Multiplier result.
 * r  Remainder from the division.
 * returns MP_OKAY indicating success.
 */
static WC_INLINE int sp_3072_div_96(const sp_digit* a, const sp_digit* d, sp_digit* m,
        sp_digit* r)
{
    sp_digit t1[192], t2[97];
    sp_digit div, r1;
    int i;

    (void)m;

    div = d[95];
    XMEMCPY(t1, a, sizeof(*t1) * 2 * 96);
    for (i=95; i>=0; i--) {
        r1 = div_3072_word_96(t1[96 + i], t1[96 + i - 1], div);

        sp_3072_mul_d_96(t2, d, r1);
        t1[96 + i] += sp_3072_sub_in_place_96(&t1[i], t2);
        t1[96 + i] -= t2[96];
        sp_3072_mask_96(t2, d, t1[96 + i]);
        t1[96 + i] += sp_3072_add_96(&t1[i], &t1[i], t2);
        sp_3072_mask_96(t2, d, t1[96 + i]);
        t1[96 + i] += sp_3072_add_96(&t1[i], &t1[i], t2);
    }

    r1 = sp_3072_cmp_96(t1, d) >= 0;
    sp_3072_cond_sub_96(r, t1, d, (sp_digit)0 - r1);

    return MP_OKAY;
}

/* Reduce a modulo m into r. (r = a mod m)
 *
 * r  A single precision number that is the reduced result.
 * a  A single precision number that is to be reduced.
 * m  A single precision number that is the modulus to reduce with.
 * returns MP_OKAY indicating success.
 */
static WC_INLINE int sp_3072_mod_96(sp_digit* r, const sp_digit* a, const sp_digit* m)
{
    return sp_3072_div_96(a, m, NULL, r);
}

/* Divide d in a and put remainder into r (m*d + r = a)
 * m is not calculated as it is not needed at this time.
 *
 * a  Nmber to be divided.
 * d  Number to divide with.
 * m  Multiplier result.
 * r  Remainder from the division.
 * returns MP_OKAY indicating success.
 */
static WC_INLINE int sp_3072_div_96_cond(const sp_digit* a, const sp_digit* d, sp_digit* m,
        sp_digit* r)
{
    sp_digit t1[192], t2[97];
    sp_digit div, r1;
    int i;

    (void)m;

    div = d[95];
    XMEMCPY(t1, a, sizeof(*t1) * 2 * 96);
    for (i=95; i>=0; i--) {
        r1 = div_3072_word_96(t1[96 + i], t1[96 + i - 1], div);

        sp_3072_mul_d_96(t2, d, r1);
        t1[96 + i] += sp_3072_sub_in_place_96(&t1[i], t2);
        t1[96 + i] -= t2[96];
        if (t1[96 + i] != 0) {
            t1[96 + i] += sp_3072_add_96(&t1[i], &t1[i], d);
            if (t1[96 + i] != 0)
                t1[96 + i] += sp_3072_add_96(&t1[i], &t1[i], d);
        }
    }

    r1 = sp_3072_cmp_96(t1, d) >= 0;
    sp_3072_cond_sub_96(r, t1, d, (sp_digit)0 - r1);

    return MP_OKAY;
}

/* Reduce a modulo m into r. (r = a mod m)
 *
 * r  A single precision number that is the reduced result.
 * a  A single precision number that is to be reduced.
 * m  A single precision number that is the modulus to reduce with.
 * returns MP_OKAY indicating success.
 */
static WC_INLINE int sp_3072_mod_96_cond(sp_digit* r, const sp_digit* a, const sp_digit* m)
{
    return sp_3072_div_96_cond(a, m, NULL, r);
}

#if (defined(WOLFSSL_HAVE_SP_RSA) && !defined(WOLFSSL_RSA_PUBLIC_ONLY)) || \
                                                     defined(WOLFSSL_HAVE_SP_DH)
#ifdef WOLFSSL_SP_SMALL
/* Modular exponentiate a to the e mod m. (r = a^e mod m)
 *
 * r     A single precision number that is the result of the operation.
 * a     A single precision number being exponentiated.
 * e     A single precision number that is the exponent.
 * bits  The number of bits in the exponent.
 * m     A single precision number that is the modulus.
 * returns 0 on success and MEMORY_E on dynamic memory allocation failure.
 */
static int sp_3072_mod_exp_96(sp_digit* r, const sp_digit* a, const sp_digit* e,
        int bits, const sp_digit* m, int reduceA)
{
#if defined(WOLFSSL_SMALL_STACK) && !defined(WOLFSSL_SP_NO_MALLOC)
    sp_digit* td;
#else
    sp_digit td[16 * 192];
#endif
    sp_digit* t[16];
    sp_digit* norm;
    sp_digit mp = 1;
    sp_digit n;
    sp_digit mask;
    int i;
    int c, y;
    int err = MP_OKAY;

#if defined(WOLFSSL_SMALL_STACK) && !defined(WOLFSSL_SP_NO_MALLOC)
    td = (sp_digit*)XMALLOC(sizeof(sp_digit) * (16 * 192), NULL,
                            DYNAMIC_TYPE_TMP_BUFFER);
    if (td == NULL) {
        err = MEMORY_E;
    }
#endif

    if (err == MP_OKAY) {
        norm = td;
        for (i=0; i<16; i++) {
#if defined(WOLFSSL_SMALL_STACK) && !defined(WOLFSSL_SP_NO_MALLOC)
            t[i] = td + i * 192;
#else
            t[i] = &td[i * 192];
#endif
        }

        sp_3072_mont_setup(m, &mp);
        sp_3072_mont_norm_96(norm, m);

        XMEMSET(t[1], 0, sizeof(sp_digit) * 96U);
        if (reduceA != 0) {
            err = sp_3072_mod_96(t[1] + 96, a, m);
            if (err == MP_OKAY) {
                err = sp_3072_mod_96(t[1], t[1], m);
            }
        }
        else {
            XMEMCPY(t[1] + 96, a, sizeof(sp_digit) * 96);
            err = sp_3072_mod_96(t[1], t[1], m);
        }
    }

    if (err == MP_OKAY) {
        sp_3072_mont_sqr_96(t[ 2], t[ 1], m, mp);
        sp_3072_mont_mul_96(t[ 3], t[ 2], t[ 1], m, mp);
        sp_3072_mont_sqr_96(t[ 4], t[ 2], m, mp);
        sp_3072_mont_mul_96(t[ 5], t[ 3], t[ 2], m, mp);
        sp_3072_mont_sqr_96(t[ 6], t[ 3], m, mp);
        sp_3072_mont_mul_96(t[ 7], t[ 4], t[ 3], m, mp);
        sp_3072_mont_sqr_96(t[ 8], t[ 4], m, mp);
        sp_3072_mont_mul_96(t[ 9], t[ 5], t[ 4], m, mp);
        sp_3072_mont_sqr_96(t[10], t[ 5], m, mp);
        sp_3072_mont_mul_96(t[11], t[ 6], t[ 5], m, mp);
        sp_3072_mont_sqr_96(t[12], t[ 6], m, mp);
        sp_3072_mont_mul_96(t[13], t[ 7], t[ 6], m, mp);
        sp_3072_mont_sqr_96(t[14], t[ 7], m, mp);
        sp_3072_mont_mul_96(t[15], t[ 8], t[ 7], m, mp);

        i = (bits - 1) / 32;
        n = e[i--];
        c = bits & 31;
        if (c == 0) {
            c = 32;
        }
        c -= bits % 4;
        if (c == 32) {
            c = 28;
        }
        y = (int)(n >> c);
        n <<= 32 - c;
        XMEMCPY(r, t[y], sizeof(sp_digit) * 96);
        for (; i>=0 || c>=4; ) {
            if (c == 0) {
                n = e[i--];
                y = n >> 28;
                n <<= 4;
                c = 28;
            }
            else if (c < 4) {
                y = n >> 28;
                n = e[i--];
                c = 4 - c;
                y |= n >> (32 - c);
                n <<= c;
                c = 32 - c;
            }
            else {
                y = (n >> 28) & 0xf;
                n <<= 4;
                c -= 4;
            }

            sp_3072_mont_sqr_96(r, r, m, mp);
            sp_3072_mont_sqr_96(r, r, m, mp);
            sp_3072_mont_sqr_96(r, r, m, mp);
            sp_3072_mont_sqr_96(r, r, m, mp);

            sp_3072_mont_mul_96(r, r, t[y], m, mp);
        }

        XMEMSET(&r[96], 0, sizeof(sp_digit) * 96U);
        sp_3072_mont_reduce_96(r, m, mp);

        mask = 0 - (sp_3072_cmp_96(r, m) >= 0);
        sp_3072_cond_sub_96(r, r, m, mask);
    }

#if defined(WOLFSSL_SMALL_STACK) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (td != NULL) {
        XFREE(td, NULL, DYNAMIC_TYPE_TMP_BUFFER);
    }
#endif

    return err;
}
#else
/* Modular exponentiate a to the e mod m. (r = a^e mod m)
 *
 * r     A single precision number that is the result of the operation.
 * a     A single precision number being exponentiated.
 * e     A single precision number that is the exponent.
 * bits  The number of bits in the exponent.
 * m     A single precision number that is the modulus.
 * returns 0 on success and MEMORY_E on dynamic memory allocation failure.
 */
static int sp_3072_mod_exp_96(sp_digit* r, const sp_digit* a, const sp_digit* e,
        int bits, const sp_digit* m, int reduceA)
{
#if defined(WOLFSSL_SMALL_STACK) && !defined(WOLFSSL_SP_NO_MALLOC)
    sp_digit* td;
#else
    sp_digit td[32 * 192];
#endif
    sp_digit* t[32];
    sp_digit* norm;
    sp_digit mp = 1;
    sp_digit n;
    sp_digit mask;
    int i;
    int c, y;
    int err = MP_OKAY;

#if defined(WOLFSSL_SMALL_STACK) && !defined(WOLFSSL_SP_NO_MALLOC)
    td = (sp_digit*)XMALLOC(sizeof(sp_digit) * (32 * 192), NULL,
                            DYNAMIC_TYPE_TMP_BUFFER);
    if (td == NULL) {
        err = MEMORY_E;
    }
#endif

    if (err == MP_OKAY) {
        norm = td;
        for (i=0; i<32; i++) {
#if defined(WOLFSSL_SMALL_STACK) && !defined(WOLFSSL_SP_NO_MALLOC)
            t[i] = td + i * 192;
#else
            t[i] = &td[i * 192];
#endif
        }

        sp_3072_mont_setup(m, &mp);
        sp_3072_mont_norm_96(norm, m);

        XMEMSET(t[1], 0, sizeof(sp_digit) * 96U);
        if (reduceA != 0) {
            err = sp_3072_mod_96(t[1] + 96, a, m);
            if (err == MP_OKAY) {
                err = sp_3072_mod_96(t[1], t[1], m);
            }
        }
        else {
            XMEMCPY(t[1] + 96, a, sizeof(sp_digit) * 96);
            err = sp_3072_mod_96(t[1], t[1], m);
        }
    }

    if (err == MP_OKAY) {
        sp_3072_mont_sqr_96(t[ 2], t[ 1], m, mp);
        sp_3072_mont_mul_96(t[ 3], t[ 2], t[ 1], m, mp);
        sp_3072_mont_sqr_96(t[ 4], t[ 2], m, mp);
        sp_3072_mont_mul_96(t[ 5], t[ 3], t[ 2], m, mp);
        sp_3072_mont_sqr_96(t[ 6], t[ 3], m, mp);
        sp_3072_mont_mul_96(t[ 7], t[ 4], t[ 3], m, mp);
        sp_3072_mont_sqr_96(t[ 8], t[ 4], m, mp);
        sp_3072_mont_mul_96(t[ 9], t[ 5], t[ 4], m, mp);
        sp_3072_mont_sqr_96(t[10], t[ 5], m, mp);
        sp_3072_mont_mul_96(t[11], t[ 6], t[ 5], m, mp);
        sp_3072_mont_sqr_96(t[12], t[ 6], m, mp);
        sp_3072_mont_mul_96(t[13], t[ 7], t[ 6], m, mp);
        sp_3072_mont_sqr_96(t[14], t[ 7], m, mp);
        sp_3072_mont_mul_96(t[15], t[ 8], t[ 7], m, mp);
        sp_3072_mont_sqr_96(t[16], t[ 8], m, mp);
        sp_3072_mont_mul_96(t[17], t[ 9], t[ 8], m, mp);
        sp_3072_mont_sqr_96(t[18], t[ 9], m, mp);
        sp_3072_mont_mul_96(t[19], t[10], t[ 9], m, mp);
        sp_3072_mont_sqr_96(t[20], t[10], m, mp);
        sp_3072_mont_mul_96(t[21], t[11], t[10], m, mp);
        sp_3072_mont_sqr_96(t[22], t[11], m, mp);
        sp_3072_mont_mul_96(t[23], t[12], t[11], m, mp);
        sp_3072_mont_sqr_96(t[24], t[12], m, mp);
        sp_3072_mont_mul_96(t[25], t[13], t[12], m, mp);
        sp_3072_mont_sqr_96(t[26], t[13], m, mp);
        sp_3072_mont_mul_96(t[27], t[14], t[13], m, mp);
        sp_3072_mont_sqr_96(t[28], t[14], m, mp);
        sp_3072_mont_mul_96(t[29], t[15], t[14], m, mp);
        sp_3072_mont_sqr_96(t[30], t[15], m, mp);
        sp_3072_mont_mul_96(t[31], t[16], t[15], m, mp);

        i = (bits - 1) / 32;
        n = e[i--];
        c = bits & 31;
        if (c == 0) {
            c = 32;
        }
        c -= bits % 5;
        if (c == 32) {
            c = 27;
        }
        y = (int)(n >> c);
        n <<= 32 - c;
        XMEMCPY(r, t[y], sizeof(sp_digit) * 96);
        for (; i>=0 || c>=5; ) {
            if (c == 0) {
                n = e[i--];
                y = n >> 27;
                n <<= 5;
                c = 27;
            }
            else if (c < 5) {
                y = n >> 27;
                n = e[i--];
                c = 5 - c;
                y |= n >> (32 - c);
                n <<= c;
                c = 32 - c;
            }
            else {
                y = (n >> 27) & 0x1f;
                n <<= 5;
                c -= 5;
            }

            sp_3072_mont_sqr_96(r, r, m, mp);
            sp_3072_mont_sqr_96(r, r, m, mp);
            sp_3072_mont_sqr_96(r, r, m, mp);
            sp_3072_mont_sqr_96(r, r, m, mp);
            sp_3072_mont_sqr_96(r, r, m, mp);

            sp_3072_mont_mul_96(r, r, t[y], m, mp);
        }

        XMEMSET(&r[96], 0, sizeof(sp_digit) * 96U);
        sp_3072_mont_reduce_96(r, m, mp);

        mask = 0 - (sp_3072_cmp_96(r, m) >= 0);
        sp_3072_cond_sub_96(r, r, m, mask);
    }

#if defined(WOLFSSL_SMALL_STACK) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (td != NULL) {
        XFREE(td, NULL, DYNAMIC_TYPE_TMP_BUFFER);
    }
#endif

    return err;
}
#endif /* WOLFSSL_SP_SMALL */
#endif /* (WOLFSSL_HAVE_SP_RSA && !WOLFSSL_RSA_PUBLIC_ONLY) || WOLFSSL_HAVE_SP_DH */

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
#if (!defined(WOLFSSL_SP_SMALL) && !defined(WOLFSSL_SMALL_STACK)) || defined(WOLFSSL_SP_NO_MALLOC)
    sp_digit a[192], m[96], r[192];
#else
    sp_digit* d = NULL;
    sp_digit* a = NULL;
    sp_digit* m = NULL;
    sp_digit* r = NULL;
#endif
    sp_digit *ah = NULL;
    sp_digit e[1];
    int err = MP_OKAY;

    if (*outLen < 384)
        err = MP_TO_E;
    if (err == MP_OKAY && (mp_count_bits(em) > 32 || inLen > 384 ||
                                                     mp_count_bits(mm) != 3072))
        err = MP_READ_E;

#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (err == MP_OKAY) {
        d = (sp_digit*)XMALLOC(sizeof(sp_digit) * 96 * 5, NULL,
                                                              DYNAMIC_TYPE_RSA);
        if (d == NULL)
            err = MEMORY_E;
    }

    if (err == MP_OKAY) {
        a = d;
        r = a + 96 * 2;
        m = r + 96 * 2;
    }
#endif

    if (err == MP_OKAY) {
        ah = a + 96;

        sp_3072_from_bin(ah, 96, in, inLen);
#if DIGIT_BIT >= 32
        e[0] = em->dp[0];
#else
        e[0] = em->dp[0];
        if (em->used > 1) {
            e[0] |= ((sp_digit)em->dp[1]) << DIGIT_BIT;
        }
#endif
        if (e[0] == 0) {
            err = MP_EXPTMOD_E;
        }
    }
    if (err == MP_OKAY) {
        sp_3072_from_mp(m, 96, mm);

        if (e[0] == 0x3) {
            if (err == MP_OKAY) {
                sp_3072_sqr_96(r, ah);
                err = sp_3072_mod_96_cond(r, r, m);
            }
            if (err == MP_OKAY) {
                sp_3072_mul_96(r, ah, r);
                err = sp_3072_mod_96_cond(r, r, m);
            }
        }
        else {
            int i;
            sp_digit mp;

            sp_3072_mont_setup(m, &mp);

            /* Convert to Montgomery form. */
            XMEMSET(a, 0, sizeof(sp_digit) * 96);
            err = sp_3072_mod_96_cond(a, a, m);

            if (err == MP_OKAY) {
                for (i = 31; i >= 0; i--) {
                    if (e[0] >> i) {
                        break;
                    }
                }

                XMEMCPY(r, a, sizeof(sp_digit) * 96);
                for (i--; i>=0; i--) {
                    sp_3072_mont_sqr_96(r, r, m, mp);
                    if (((e[0] >> i) & 1) == 1) {
                        sp_3072_mont_mul_96(r, r, a, m, mp);
                    }
                }
                XMEMSET(&r[96], 0, sizeof(sp_digit) * 96);
                sp_3072_mont_reduce_96(r, m, mp);

                for (i = 95; i > 0; i--) {
                    if (r[i] != m[i]) {
                        break;
                    }
                }
                if (r[i] >= m[i]) {
                    sp_3072_sub_in_place_96(r, m);
                }
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
}

#ifndef WOLFSSL_RSA_PUBLIC_ONLY
/* Conditionally add a and b using the mask m.
 * m is -1 to add and 0 when not.
 *
 * r  A single precision number representing conditional add result.
 * a  A single precision number to add with.
 * b  A single precision number to add.
 * m  Mask value to apply.
 */
SP_NOINLINE static sp_digit sp_3072_cond_add_48(sp_digit* r, const sp_digit* a, const sp_digit* b,
        sp_digit m)
{
    sp_digit c = 0;

    __asm__ __volatile__ (
        "mov	r5, #192\n\t"
        "mov	r9, r5\n\t"
        "mov	r8, #0\n\t"
        "\n1:\n\t"
        "ldr	r6, [%[b], r8]\n\t"
        "and	r6, r6, %[m]\n\t"
        "adds	r5, %[c], #-1\n\t"
        "ldr	r5, [%[a], r8]\n\t"
        "adcs	r5, r5, r6\n\t"
        "mov	%[c], #0\n\t"
        "adcs	%[c], %[c], %[c]\n\t"
        "str	r5, [%[r], r8]\n\t"
        "add	r8, r8, #4\n\t"
        "cmp	r8, r9\n\t"
        "blt	1b\n\t"
        : [c] "+r" (c)
        : [r] "r" (r), [a] "r" (a), [b] "r" (b), [m] "r" (m)
        : "memory", "r5", "r6", "r8", "r9"
    );

    return c;
}

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
        d = (sp_digit*)XMALLOC(sizeof(sp_digit) * 96 * 4, NULL,
                                                              DYNAMIC_TYPE_RSA);
        if (d == NULL) {
            err = MEMORY_E;
        }
    }
    if (err == MP_OKAY) {
        a = d + 96;
        m = a + 192;
        r = a;

        sp_3072_from_bin(a, 96, in, inLen);
        sp_3072_from_mp(d, 96, dm);
        sp_3072_from_mp(m, 96, mm);
        err = sp_3072_mod_exp_96(r, a, d, 3072, m, 0);
    }
    if (err == MP_OKAY) {
        sp_3072_to_bin(r, out);
        *outLen = 384;
    }

    if (d != NULL) {
        XMEMSET(d, 0, sizeof(sp_digit) * 96);
        XFREE(d, NULL, DYNAMIC_TYPE_RSA);
    }

    return err;
#else
#if (!defined(WOLFSSL_SP_SMALL) && !defined(WOLFSSL_SMALL_STACK)) || defined(WOLFSSL_SP_NO_MALLOC)
    sp_digit a[96 * 2];
    sp_digit p[48], q[48], dp[48];
    sp_digit tmpa[96], tmpb[96];
#else
    sp_digit* t = NULL;
    sp_digit* a = NULL;
    sp_digit* p = NULL;
    sp_digit* q = NULL;
    sp_digit* dp = NULL;
    sp_digit* tmpa = NULL;
    sp_digit* tmpb = NULL;
#endif
    sp_digit* r = NULL;
    sp_digit* qi = NULL;
    sp_digit* dq = NULL;
    sp_digit c;
    int err = MP_OKAY;

    (void)dm;
    (void)mm;

    if (*outLen < 384)
        err = MP_TO_E;
    if (err == MP_OKAY && (inLen > 384 || mp_count_bits(mm) != 3072))
        err = MP_READ_E;

#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (err == MP_OKAY) {
        t = (sp_digit*)XMALLOC(sizeof(sp_digit) * 48 * 11, NULL,
                                                              DYNAMIC_TYPE_RSA);
        if (t == NULL)
            err = MEMORY_E;
    }
    if (err == MP_OKAY) {
        a = t;
        p = a + 96 * 2;
        q = p + 48;
        qi = dq = dp = q + 48;
        tmpa = qi + 48;
        tmpb = tmpa + 96;

        r = t + 96;
    }
#else
#endif

    if (err == MP_OKAY) {
#if (!defined(WOLFSSL_SP_SMALL) && !defined(WOLFSSL_SMALL_STACK)) || defined(WOLFSSL_SP_NO_MALLOC)
        r = a;
        qi = dq = dp;
#endif
        sp_3072_from_bin(a, 96, in, inLen);
        sp_3072_from_mp(p, 48, pm);
        sp_3072_from_mp(q, 48, qm);
        sp_3072_from_mp(dp, 48, dpm);

        err = sp_3072_mod_exp_48(tmpa, a, dp, 1536, p, 1);
    }
    if (err == MP_OKAY) {
        sp_3072_from_mp(dq, 48, dqm);
        err = sp_3072_mod_exp_48(tmpb, a, dq, 1536, q, 1);
    }

    if (err == MP_OKAY) {
        c = sp_3072_sub_in_place_48(tmpa, tmpb);
        c += sp_3072_cond_add_48(tmpa, tmpa, p, c);
        sp_3072_cond_add_48(tmpa, tmpa, p, c);

        sp_3072_from_mp(qi, 48, qim);
        sp_3072_mul_48(tmpa, tmpa, qi);
        err = sp_3072_mod_48(tmpa, tmpa, p);
    }

    if (err == MP_OKAY) {
        sp_3072_mul_48(tmpa, q, tmpa);
        XMEMSET(&tmpb[48], 0, sizeof(sp_digit) * 48);
        sp_3072_add_96(r, tmpb, tmpa);

        sp_3072_to_bin(r, out);
        *outLen = 384;
    }

#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (t != NULL) {
        XMEMSET(t, 0, sizeof(sp_digit) * 48 * 11);
        XFREE(t, NULL, DYNAMIC_TYPE_RSA);
    }
#else
    XMEMSET(tmpa, 0, sizeof(tmpa));
    XMEMSET(tmpb, 0, sizeof(tmpb));
    XMEMSET(p,    0, sizeof(p));
    XMEMSET(q,    0, sizeof(q));
    XMEMSET(dp,   0, sizeof(dp));
#endif
#endif /* SP_RSA_PRIVATE_EXP_D || RSA_LOW_MEM */
    return err;
}
#endif /* WOLFSSL_RSA_PUBLIC_ONLY */
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
#if DIGIT_BIT == 32
        XMEMCPY(r->dp, a, sizeof(sp_digit) * 96);
        r->used = 96;
        mp_clamp(r);
#elif DIGIT_BIT < 32
        int i, j = 0, s = 0;

        r->dp[0] = 0;
        for (i = 0; i < 96; i++) {
            r->dp[j] |= (mp_digit)(a[i] << s);
            r->dp[j] &= (1L << DIGIT_BIT) - 1;
            s = DIGIT_BIT - s;
            r->dp[++j] = (mp_digit)(a[i] >> s);
            while (s + DIGIT_BIT <= 32) {
                s += DIGIT_BIT;
                r->dp[j++] &= (1L << DIGIT_BIT) - 1;
                if (s == SP_WORD_SIZE) {
                    r->dp[j] = 0;
                }
                else {
                    r->dp[j] = (mp_digit)(a[i] >> s);
                }
            }
            s = 32 - s;
        }
        r->used = (3072 + DIGIT_BIT - 1) / DIGIT_BIT;
        mp_clamp(r);
#else
        int i, j = 0, s = 0;

        r->dp[0] = 0;
        for (i = 0; i < 96; i++) {
            r->dp[j] |= ((mp_digit)a[i]) << s;
            if (s + 32 >= DIGIT_BIT) {
    #if DIGIT_BIT != 32 && DIGIT_BIT != 64
                r->dp[j] &= (1L << DIGIT_BIT) - 1;
    #endif
                s = DIGIT_BIT - s;
                r->dp[++j] = a[i] >> s;
                s = 32 - s;
            }
            else {
                s += 32;
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
    int err = MP_OKAY;
    sp_digit b[192], e[96], m[96];
    sp_digit* r = b;
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
        sp_3072_from_mp(b, 96, base);
        sp_3072_from_mp(e, 96, exp);
        sp_3072_from_mp(m, 96, mod);

        err = sp_3072_mod_exp_96(r, b, e, expBits, m, 0);
    }

    if (err == MP_OKAY) {
        err = sp_3072_to_mp(r, res);
    }

    XMEMSET(e, 0, sizeof(e));

    return err;
}

#ifdef WOLFSSL_HAVE_SP_DH

#ifdef HAVE_FFDHE_3072
static void sp_3072_lshift_96(sp_digit* r, sp_digit* a, byte n)
{
    __asm__ __volatile__ (
        "mov r6, #31\n\t"
        "sub r6, r6, %[n]\n\t"
        "add       %[a], %[a], #320\n\t"
        "add       %[r], %[r], #320\n\t"
        "ldr r3, [%[a], #60]\n\t"
        "lsr r4, r3, #1\n\t"
        "lsl r3, r3, %[n]\n\t"
        "lsr r4, r4, r6\n\t"
        "ldr       r2, [%[a], #56]\n\t"
        "str       r4, [%[r], #64]\n\t"
        "lsr       r5, r2, #1\n\t"
        "lsl       r2, r2, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r3, r3, r5\n\t"
        "ldr       r4, [%[a], #52]\n\t"
        "str       r3, [%[r], #60]\n\t"
        "lsr       r5, r4, #1\n\t"
        "lsl       r4, r4, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r2, r2, r5\n\t"
        "ldr       r3, [%[a], #48]\n\t"
        "str       r2, [%[r], #56]\n\t"
        "lsr       r5, r3, #1\n\t"
        "lsl       r3, r3, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r4, r4, r5\n\t"
        "ldr       r2, [%[a], #44]\n\t"
        "str       r4, [%[r], #52]\n\t"
        "lsr       r5, r2, #1\n\t"
        "lsl       r2, r2, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r3, r3, r5\n\t"
        "ldr       r4, [%[a], #40]\n\t"
        "str       r3, [%[r], #48]\n\t"
        "lsr       r5, r4, #1\n\t"
        "lsl       r4, r4, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r2, r2, r5\n\t"
        "ldr       r3, [%[a], #36]\n\t"
        "str       r2, [%[r], #44]\n\t"
        "lsr       r5, r3, #1\n\t"
        "lsl       r3, r3, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r4, r4, r5\n\t"
        "ldr       r2, [%[a], #32]\n\t"
        "str       r4, [%[r], #40]\n\t"
        "lsr       r5, r2, #1\n\t"
        "lsl       r2, r2, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r3, r3, r5\n\t"
        "ldr       r4, [%[a], #28]\n\t"
        "str       r3, [%[r], #36]\n\t"
        "lsr       r5, r4, #1\n\t"
        "lsl       r4, r4, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r2, r2, r5\n\t"
        "ldr       r3, [%[a], #24]\n\t"
        "str       r2, [%[r], #32]\n\t"
        "lsr       r5, r3, #1\n\t"
        "lsl       r3, r3, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r4, r4, r5\n\t"
        "ldr       r2, [%[a], #20]\n\t"
        "str       r4, [%[r], #28]\n\t"
        "lsr       r5, r2, #1\n\t"
        "lsl       r2, r2, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r3, r3, r5\n\t"
        "ldr       r4, [%[a], #16]\n\t"
        "str       r3, [%[r], #24]\n\t"
        "lsr       r5, r4, #1\n\t"
        "lsl       r4, r4, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r2, r2, r5\n\t"
        "ldr       r3, [%[a], #12]\n\t"
        "str       r2, [%[r], #20]\n\t"
        "lsr       r5, r3, #1\n\t"
        "lsl       r3, r3, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r4, r4, r5\n\t"
        "ldr       r2, [%[a], #8]\n\t"
        "str       r4, [%[r], #16]\n\t"
        "lsr       r5, r2, #1\n\t"
        "lsl       r2, r2, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r3, r3, r5\n\t"
        "ldr       r4, [%[a], #4]\n\t"
        "str       r3, [%[r], #12]\n\t"
        "lsr       r5, r4, #1\n\t"
        "lsl       r4, r4, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r2, r2, r5\n\t"
        "ldr       r3, [%[a], #0]\n\t"
        "str       r2, [%[r], #8]\n\t"
        "lsr       r5, r3, #1\n\t"
        "lsl       r3, r3, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r4, r4, r5\n\t"
        "sub     %[a], %[a], #64\n\t"
        "sub     %[r], %[r], #64\n\t"
        "ldr       r2, [%[a], #60]\n\t"
        "str       r4, [%[r], #68]\n\t"
        "lsr       r5, r2, #1\n\t"
        "lsl       r2, r2, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r3, r3, r5\n\t"
        "ldr       r4, [%[a], #56]\n\t"
        "str       r3, [%[r], #64]\n\t"
        "lsr       r5, r4, #1\n\t"
        "lsl       r4, r4, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r2, r2, r5\n\t"
        "ldr       r3, [%[a], #52]\n\t"
        "str       r2, [%[r], #60]\n\t"
        "lsr       r5, r3, #1\n\t"
        "lsl       r3, r3, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r4, r4, r5\n\t"
        "ldr       r2, [%[a], #48]\n\t"
        "str       r4, [%[r], #56]\n\t"
        "lsr       r5, r2, #1\n\t"
        "lsl       r2, r2, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r3, r3, r5\n\t"
        "ldr       r4, [%[a], #44]\n\t"
        "str       r3, [%[r], #52]\n\t"
        "lsr       r5, r4, #1\n\t"
        "lsl       r4, r4, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r2, r2, r5\n\t"
        "ldr       r3, [%[a], #40]\n\t"
        "str       r2, [%[r], #48]\n\t"
        "lsr       r5, r3, #1\n\t"
        "lsl       r3, r3, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r4, r4, r5\n\t"
        "ldr       r2, [%[a], #36]\n\t"
        "str       r4, [%[r], #44]\n\t"
        "lsr       r5, r2, #1\n\t"
        "lsl       r2, r2, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r3, r3, r5\n\t"
        "ldr       r4, [%[a], #32]\n\t"
        "str       r3, [%[r], #40]\n\t"
        "lsr       r5, r4, #1\n\t"
        "lsl       r4, r4, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r2, r2, r5\n\t"
        "ldr       r3, [%[a], #28]\n\t"
        "str       r2, [%[r], #36]\n\t"
        "lsr       r5, r3, #1\n\t"
        "lsl       r3, r3, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r4, r4, r5\n\t"
        "ldr       r2, [%[a], #24]\n\t"
        "str       r4, [%[r], #32]\n\t"
        "lsr       r5, r2, #1\n\t"
        "lsl       r2, r2, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r3, r3, r5\n\t"
        "ldr       r4, [%[a], #20]\n\t"
        "str       r3, [%[r], #28]\n\t"
        "lsr       r5, r4, #1\n\t"
        "lsl       r4, r4, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r2, r2, r5\n\t"
        "ldr       r3, [%[a], #16]\n\t"
        "str       r2, [%[r], #24]\n\t"
        "lsr       r5, r3, #1\n\t"
        "lsl       r3, r3, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r4, r4, r5\n\t"
        "ldr       r2, [%[a], #12]\n\t"
        "str       r4, [%[r], #20]\n\t"
        "lsr       r5, r2, #1\n\t"
        "lsl       r2, r2, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r3, r3, r5\n\t"
        "ldr       r4, [%[a], #8]\n\t"
        "str       r3, [%[r], #16]\n\t"
        "lsr       r5, r4, #1\n\t"
        "lsl       r4, r4, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r2, r2, r5\n\t"
        "ldr       r3, [%[a], #4]\n\t"
        "str       r2, [%[r], #12]\n\t"
        "lsr       r5, r3, #1\n\t"
        "lsl       r3, r3, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r4, r4, r5\n\t"
        "ldr       r2, [%[a], #0]\n\t"
        "str       r4, [%[r], #8]\n\t"
        "lsr       r5, r2, #1\n\t"
        "lsl       r2, r2, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r3, r3, r5\n\t"
        "sub     %[a], %[a], #64\n\t"
        "sub     %[r], %[r], #64\n\t"
        "ldr       r4, [%[a], #60]\n\t"
        "str       r3, [%[r], #68]\n\t"
        "lsr       r5, r4, #1\n\t"
        "lsl       r4, r4, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r2, r2, r5\n\t"
        "ldr       r3, [%[a], #56]\n\t"
        "str       r2, [%[r], #64]\n\t"
        "lsr       r5, r3, #1\n\t"
        "lsl       r3, r3, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r4, r4, r5\n\t"
        "ldr       r2, [%[a], #52]\n\t"
        "str       r4, [%[r], #60]\n\t"
        "lsr       r5, r2, #1\n\t"
        "lsl       r2, r2, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r3, r3, r5\n\t"
        "ldr       r4, [%[a], #48]\n\t"
        "str       r3, [%[r], #56]\n\t"
        "lsr       r5, r4, #1\n\t"
        "lsl       r4, r4, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r2, r2, r5\n\t"
        "ldr       r3, [%[a], #44]\n\t"
        "str       r2, [%[r], #52]\n\t"
        "lsr       r5, r3, #1\n\t"
        "lsl       r3, r3, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r4, r4, r5\n\t"
        "ldr       r2, [%[a], #40]\n\t"
        "str       r4, [%[r], #48]\n\t"
        "lsr       r5, r2, #1\n\t"
        "lsl       r2, r2, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r3, r3, r5\n\t"
        "ldr       r4, [%[a], #36]\n\t"
        "str       r3, [%[r], #44]\n\t"
        "lsr       r5, r4, #1\n\t"
        "lsl       r4, r4, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r2, r2, r5\n\t"
        "ldr       r3, [%[a], #32]\n\t"
        "str       r2, [%[r], #40]\n\t"
        "lsr       r5, r3, #1\n\t"
        "lsl       r3, r3, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r4, r4, r5\n\t"
        "ldr       r2, [%[a], #28]\n\t"
        "str       r4, [%[r], #36]\n\t"
        "lsr       r5, r2, #1\n\t"
        "lsl       r2, r2, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r3, r3, r5\n\t"
        "ldr       r4, [%[a], #24]\n\t"
        "str       r3, [%[r], #32]\n\t"
        "lsr       r5, r4, #1\n\t"
        "lsl       r4, r4, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r2, r2, r5\n\t"
        "ldr       r3, [%[a], #20]\n\t"
        "str       r2, [%[r], #28]\n\t"
        "lsr       r5, r3, #1\n\t"
        "lsl       r3, r3, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r4, r4, r5\n\t"
        "ldr       r2, [%[a], #16]\n\t"
        "str       r4, [%[r], #24]\n\t"
        "lsr       r5, r2, #1\n\t"
        "lsl       r2, r2, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r3, r3, r5\n\t"
        "ldr       r4, [%[a], #12]\n\t"
        "str       r3, [%[r], #20]\n\t"
        "lsr       r5, r4, #1\n\t"
        "lsl       r4, r4, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r2, r2, r5\n\t"
        "ldr       r3, [%[a], #8]\n\t"
        "str       r2, [%[r], #16]\n\t"
        "lsr       r5, r3, #1\n\t"
        "lsl       r3, r3, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r4, r4, r5\n\t"
        "ldr       r2, [%[a], #4]\n\t"
        "str       r4, [%[r], #12]\n\t"
        "lsr       r5, r2, #1\n\t"
        "lsl       r2, r2, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r3, r3, r5\n\t"
        "ldr       r4, [%[a], #0]\n\t"
        "str       r3, [%[r], #8]\n\t"
        "lsr       r5, r4, #1\n\t"
        "lsl       r4, r4, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r2, r2, r5\n\t"
        "sub     %[a], %[a], #64\n\t"
        "sub     %[r], %[r], #64\n\t"
        "ldr       r3, [%[a], #60]\n\t"
        "str       r2, [%[r], #68]\n\t"
        "lsr       r5, r3, #1\n\t"
        "lsl       r3, r3, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r4, r4, r5\n\t"
        "ldr       r2, [%[a], #56]\n\t"
        "str       r4, [%[r], #64]\n\t"
        "lsr       r5, r2, #1\n\t"
        "lsl       r2, r2, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r3, r3, r5\n\t"
        "ldr       r4, [%[a], #52]\n\t"
        "str       r3, [%[r], #60]\n\t"
        "lsr       r5, r4, #1\n\t"
        "lsl       r4, r4, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r2, r2, r5\n\t"
        "ldr       r3, [%[a], #48]\n\t"
        "str       r2, [%[r], #56]\n\t"
        "lsr       r5, r3, #1\n\t"
        "lsl       r3, r3, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r4, r4, r5\n\t"
        "ldr       r2, [%[a], #44]\n\t"
        "str       r4, [%[r], #52]\n\t"
        "lsr       r5, r2, #1\n\t"
        "lsl       r2, r2, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r3, r3, r5\n\t"
        "ldr       r4, [%[a], #40]\n\t"
        "str       r3, [%[r], #48]\n\t"
        "lsr       r5, r4, #1\n\t"
        "lsl       r4, r4, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r2, r2, r5\n\t"
        "ldr       r3, [%[a], #36]\n\t"
        "str       r2, [%[r], #44]\n\t"
        "lsr       r5, r3, #1\n\t"
        "lsl       r3, r3, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r4, r4, r5\n\t"
        "ldr       r2, [%[a], #32]\n\t"
        "str       r4, [%[r], #40]\n\t"
        "lsr       r5, r2, #1\n\t"
        "lsl       r2, r2, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r3, r3, r5\n\t"
        "ldr       r4, [%[a], #28]\n\t"
        "str       r3, [%[r], #36]\n\t"
        "lsr       r5, r4, #1\n\t"
        "lsl       r4, r4, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r2, r2, r5\n\t"
        "ldr       r3, [%[a], #24]\n\t"
        "str       r2, [%[r], #32]\n\t"
        "lsr       r5, r3, #1\n\t"
        "lsl       r3, r3, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r4, r4, r5\n\t"
        "ldr       r2, [%[a], #20]\n\t"
        "str       r4, [%[r], #28]\n\t"
        "lsr       r5, r2, #1\n\t"
        "lsl       r2, r2, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r3, r3, r5\n\t"
        "ldr       r4, [%[a], #16]\n\t"
        "str       r3, [%[r], #24]\n\t"
        "lsr       r5, r4, #1\n\t"
        "lsl       r4, r4, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r2, r2, r5\n\t"
        "ldr       r3, [%[a], #12]\n\t"
        "str       r2, [%[r], #20]\n\t"
        "lsr       r5, r3, #1\n\t"
        "lsl       r3, r3, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r4, r4, r5\n\t"
        "ldr       r2, [%[a], #8]\n\t"
        "str       r4, [%[r], #16]\n\t"
        "lsr       r5, r2, #1\n\t"
        "lsl       r2, r2, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r3, r3, r5\n\t"
        "ldr       r4, [%[a], #4]\n\t"
        "str       r3, [%[r], #12]\n\t"
        "lsr       r5, r4, #1\n\t"
        "lsl       r4, r4, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r2, r2, r5\n\t"
        "ldr       r3, [%[a], #0]\n\t"
        "str       r2, [%[r], #8]\n\t"
        "lsr       r5, r3, #1\n\t"
        "lsl       r3, r3, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r4, r4, r5\n\t"
        "sub     %[a], %[a], #64\n\t"
        "sub     %[r], %[r], #64\n\t"
        "ldr       r2, [%[a], #60]\n\t"
        "str       r4, [%[r], #68]\n\t"
        "lsr       r5, r2, #1\n\t"
        "lsl       r2, r2, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r3, r3, r5\n\t"
        "ldr       r4, [%[a], #56]\n\t"
        "str       r3, [%[r], #64]\n\t"
        "lsr       r5, r4, #1\n\t"
        "lsl       r4, r4, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r2, r2, r5\n\t"
        "ldr       r3, [%[a], #52]\n\t"
        "str       r2, [%[r], #60]\n\t"
        "lsr       r5, r3, #1\n\t"
        "lsl       r3, r3, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r4, r4, r5\n\t"
        "ldr       r2, [%[a], #48]\n\t"
        "str       r4, [%[r], #56]\n\t"
        "lsr       r5, r2, #1\n\t"
        "lsl       r2, r2, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r3, r3, r5\n\t"
        "ldr       r4, [%[a], #44]\n\t"
        "str       r3, [%[r], #52]\n\t"
        "lsr       r5, r4, #1\n\t"
        "lsl       r4, r4, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r2, r2, r5\n\t"
        "ldr       r3, [%[a], #40]\n\t"
        "str       r2, [%[r], #48]\n\t"
        "lsr       r5, r3, #1\n\t"
        "lsl       r3, r3, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r4, r4, r5\n\t"
        "ldr       r2, [%[a], #36]\n\t"
        "str       r4, [%[r], #44]\n\t"
        "lsr       r5, r2, #1\n\t"
        "lsl       r2, r2, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r3, r3, r5\n\t"
        "ldr       r4, [%[a], #32]\n\t"
        "str       r3, [%[r], #40]\n\t"
        "lsr       r5, r4, #1\n\t"
        "lsl       r4, r4, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r2, r2, r5\n\t"
        "ldr       r3, [%[a], #28]\n\t"
        "str       r2, [%[r], #36]\n\t"
        "lsr       r5, r3, #1\n\t"
        "lsl       r3, r3, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r4, r4, r5\n\t"
        "ldr       r2, [%[a], #24]\n\t"
        "str       r4, [%[r], #32]\n\t"
        "lsr       r5, r2, #1\n\t"
        "lsl       r2, r2, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r3, r3, r5\n\t"
        "ldr       r4, [%[a], #20]\n\t"
        "str       r3, [%[r], #28]\n\t"
        "lsr       r5, r4, #1\n\t"
        "lsl       r4, r4, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r2, r2, r5\n\t"
        "ldr       r3, [%[a], #16]\n\t"
        "str       r2, [%[r], #24]\n\t"
        "lsr       r5, r3, #1\n\t"
        "lsl       r3, r3, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r4, r4, r5\n\t"
        "ldr       r2, [%[a], #12]\n\t"
        "str       r4, [%[r], #20]\n\t"
        "lsr       r5, r2, #1\n\t"
        "lsl       r2, r2, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r3, r3, r5\n\t"
        "ldr       r4, [%[a], #8]\n\t"
        "str       r3, [%[r], #16]\n\t"
        "lsr       r5, r4, #1\n\t"
        "lsl       r4, r4, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r2, r2, r5\n\t"
        "ldr       r3, [%[a], #4]\n\t"
        "str       r2, [%[r], #12]\n\t"
        "lsr       r5, r3, #1\n\t"
        "lsl       r3, r3, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r4, r4, r5\n\t"
        "ldr       r2, [%[a], #0]\n\t"
        "str       r4, [%[r], #8]\n\t"
        "lsr       r5, r2, #1\n\t"
        "lsl       r2, r2, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r3, r3, r5\n\t"
        "sub     %[a], %[a], #64\n\t"
        "sub     %[r], %[r], #64\n\t"
        "ldr       r4, [%[a], #60]\n\t"
        "str       r3, [%[r], #68]\n\t"
        "lsr       r5, r4, #1\n\t"
        "lsl       r4, r4, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r2, r2, r5\n\t"
        "ldr       r3, [%[a], #56]\n\t"
        "str       r2, [%[r], #64]\n\t"
        "lsr       r5, r3, #1\n\t"
        "lsl       r3, r3, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r4, r4, r5\n\t"
        "ldr       r2, [%[a], #52]\n\t"
        "str       r4, [%[r], #60]\n\t"
        "lsr       r5, r2, #1\n\t"
        "lsl       r2, r2, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r3, r3, r5\n\t"
        "ldr       r4, [%[a], #48]\n\t"
        "str       r3, [%[r], #56]\n\t"
        "lsr       r5, r4, #1\n\t"
        "lsl       r4, r4, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r2, r2, r5\n\t"
        "ldr       r3, [%[a], #44]\n\t"
        "str       r2, [%[r], #52]\n\t"
        "lsr       r5, r3, #1\n\t"
        "lsl       r3, r3, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r4, r4, r5\n\t"
        "ldr       r2, [%[a], #40]\n\t"
        "str       r4, [%[r], #48]\n\t"
        "lsr       r5, r2, #1\n\t"
        "lsl       r2, r2, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r3, r3, r5\n\t"
        "ldr       r4, [%[a], #36]\n\t"
        "str       r3, [%[r], #44]\n\t"
        "lsr       r5, r4, #1\n\t"
        "lsl       r4, r4, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r2, r2, r5\n\t"
        "ldr       r3, [%[a], #32]\n\t"
        "str       r2, [%[r], #40]\n\t"
        "lsr       r5, r3, #1\n\t"
        "lsl       r3, r3, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r4, r4, r5\n\t"
        "ldr       r2, [%[a], #28]\n\t"
        "str       r4, [%[r], #36]\n\t"
        "lsr       r5, r2, #1\n\t"
        "lsl       r2, r2, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r3, r3, r5\n\t"
        "ldr       r4, [%[a], #24]\n\t"
        "str       r3, [%[r], #32]\n\t"
        "lsr       r5, r4, #1\n\t"
        "lsl       r4, r4, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r2, r2, r5\n\t"
        "ldr       r3, [%[a], #20]\n\t"
        "str       r2, [%[r], #28]\n\t"
        "lsr       r5, r3, #1\n\t"
        "lsl       r3, r3, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r4, r4, r5\n\t"
        "ldr       r2, [%[a], #16]\n\t"
        "str       r4, [%[r], #24]\n\t"
        "lsr       r5, r2, #1\n\t"
        "lsl       r2, r2, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r3, r3, r5\n\t"
        "ldr       r4, [%[a], #12]\n\t"
        "str       r3, [%[r], #20]\n\t"
        "lsr       r5, r4, #1\n\t"
        "lsl       r4, r4, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r2, r2, r5\n\t"
        "ldr       r3, [%[a], #8]\n\t"
        "str       r2, [%[r], #16]\n\t"
        "lsr       r5, r3, #1\n\t"
        "lsl       r3, r3, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r4, r4, r5\n\t"
        "ldr       r2, [%[a], #4]\n\t"
        "str       r4, [%[r], #12]\n\t"
        "lsr       r5, r2, #1\n\t"
        "lsl       r2, r2, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r3, r3, r5\n\t"
        "ldr       r4, [%[a], #0]\n\t"
        "str       r3, [%[r], #8]\n\t"
        "lsr       r5, r4, #1\n\t"
        "lsl       r4, r4, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r2, r2, r5\n\t"
        "str r4, [%[r]]\n\t"
        "str r2, [%[r], #4]\n\t"
        :
        : [r] "r" (r), [a] "r" (a), [n] "r" (n)
        : "memory", "r2", "r3", "r4", "r5", "r6"
    );
}

/* Modular exponentiate 2 to the e mod m. (r = 2^e mod m)
 *
 * r     A single precision number that is the result of the operation.
 * e     A single precision number that is the exponent.
 * bits  The number of bits in the exponent.
 * m     A single precision number that is the modulus.
 * returns 0 on success and MEMORY_E on dynamic memory allocation failure.
 */
static int sp_3072_mod_exp_2_96(sp_digit* r, const sp_digit* e, int bits,
        const sp_digit* m)
{
#if defined(WOLFSSL_SMALL_STACK) && !defined(WOLFSSL_SP_NO_MALLOC)
    sp_digit* td;
#else
    sp_digit td[289];
#endif
    sp_digit* norm;
    sp_digit* tmp;
    sp_digit mp = 1;
    sp_digit n, o;
    sp_digit mask;
    int i;
    int c, y;
    int err = MP_OKAY;

#if defined(WOLFSSL_SMALL_STACK) && !defined(WOLFSSL_SP_NO_MALLOC)
    td = (sp_digit*)XMALLOC(sizeof(sp_digit) * 289, NULL,
                            DYNAMIC_TYPE_TMP_BUFFER);
    if (td == NULL) {
        err = MEMORY_E;
    }
#endif

    if (err == MP_OKAY) {
        norm = td;
#if defined(WOLFSSL_SMALL_STACK) && !defined(WOLFSSL_SP_NO_MALLOC)
        tmp = td + 192;
#else
        tmp = &td[192];
#endif

        sp_3072_mont_setup(m, &mp);
        sp_3072_mont_norm_96(norm, m);

        i = (bits - 1) / 32;
        n = e[i--];
        c = bits & 31;
        if (c == 0) {
            c = 32;
        }
        c -= bits % 5;
        if (c == 32) {
            c = 27;
        }
        y = (int)(n >> c);
        n <<= 32 - c;
        sp_3072_lshift_96(r, norm, y);
        for (; i>=0 || c>=5; ) {
            if (c == 0) {
                n = e[i--];
                y = n >> 27;
                n <<= 5;
                c = 27;
            }
            else if (c < 5) {
                y = n >> 27;
                n = e[i--];
                c = 5 - c;
                y |= n >> (32 - c);
                n <<= c;
                c = 32 - c;
            }
            else {
                y = (n >> 27) & 0x1f;
                n <<= 5;
                c -= 5;
            }

            sp_3072_mont_sqr_96(r, r, m, mp);
            sp_3072_mont_sqr_96(r, r, m, mp);
            sp_3072_mont_sqr_96(r, r, m, mp);
            sp_3072_mont_sqr_96(r, r, m, mp);
            sp_3072_mont_sqr_96(r, r, m, mp);

            sp_3072_lshift_96(r, r, y);
            sp_3072_mul_d_96(tmp, norm, r[96]);
            r[96] = 0;
            o = sp_3072_add_96(r, r, tmp);
            sp_3072_cond_sub_96(r, r, m, (sp_digit)0 - o);
        }

        XMEMSET(&r[96], 0, sizeof(sp_digit) * 96U);
        sp_3072_mont_reduce_96(r, m, mp);

        mask = 0 - (sp_3072_cmp_96(r, m) >= 0);
        sp_3072_cond_sub_96(r, r, m, mask);
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
    int err = MP_OKAY;
    sp_digit b[192], e[96], m[96];
    sp_digit* r = b;
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
        sp_3072_from_mp(b, 96, base);
        sp_3072_from_bin(e, 96, exp, expLen);
        sp_3072_from_mp(m, 96, mod);

    #ifdef HAVE_FFDHE_3072
        if (base->used == 1 && base->dp[0] == 2 && m[95] == (sp_digit)-1)
            err = sp_3072_mod_exp_2_96(r, e, expLen * 8, m);
        else
    #endif
            err = sp_3072_mod_exp_96(r, b, e, expLen * 8, m, 0);

    }

    if (err == MP_OKAY) {
        sp_3072_to_bin(r, out);
        *outLen = 384;
        for (i=0; i<384 && out[i] == 0; i++) {
        }
        *outLen -= i;
        XMEMMOVE(out, out + i, *outLen);

    }

    XMEMSET(e, 0, sizeof(e));

    return err;
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
    int err = MP_OKAY;
    sp_digit b[96], e[48], m[48];
    sp_digit* r = b;
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
        sp_3072_from_mp(b, 48, base);
        sp_3072_from_mp(e, 48, exp);
        sp_3072_from_mp(m, 48, mod);

        err = sp_3072_mod_exp_48(r, b, e, expBits, m, 0);
    }

    if (err == MP_OKAY) {
        XMEMSET(r + 48, 0, sizeof(*r) * 48U);
        err = sp_3072_to_mp(r, res);
        res->used = mod->used;
        mp_clamp(res);
    }

    XMEMSET(e, 0, sizeof(e));

    return err;
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
        if (s >= 24U) {
            r[j] &= 0xffffffff;
            s = 32U - s;
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
#if DIGIT_BIT == 32
    int j;

    XMEMCPY(r, a->dp, sizeof(sp_digit) * a->used);

    for (j = a->used; j < size; j++) {
        r[j] = 0;
    }
#elif DIGIT_BIT > 32
    int i, j = 0;
    word32 s = 0;

    r[0] = 0;
    for (i = 0; i < a->used && j < size; i++) {
        r[j] |= ((sp_digit)a->dp[i] << s);
        r[j] &= 0xffffffff;
        s = 32U - s;
        if (j + 1 >= size) {
            break;
        }
        /* lint allow cast of mismatch word32 and mp_digit */
        r[++j] = (sp_digit)(a->dp[i] >> s); /*lint !e9033*/
        while ((s + 32U) <= (word32)DIGIT_BIT) {
            s += 32U;
            r[j] &= 0xffffffff;
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
        if (s + DIGIT_BIT >= 32) {
            r[j] &= 0xffffffff;
            if (j + 1 >= size) {
                break;
            }
            s = 32 - s;
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

    j = 4096 / 8 - 1;
    a[j] = 0;
    for (i=0; i<128 && j>=0; i++) {
        b = 0;
        /* lint allow cast of mismatch sp_digit and int */
        a[j--] |= (byte)(r[i] << s); /*lint !e9033*/
        b += 8 - s;
        if (j < 0) {
            break;
        }
        while (b < 32) {
            a[j--] = (byte)(r[i] >> b);
            b += 8;
            if (j < 0) {
                break;
            }
        }
        s = 8 - (b - 32);
        if (j >= 0) {
            a[j] = 0;
        }
        if (s != 0) {
            j++;
        }
    }
}

#ifndef WOLFSSL_SP_SMALL
/* Sub b from a into r. (r = a - b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A single precision integer.
 */
SP_NOINLINE static sp_digit sp_4096_sub_in_place_128(sp_digit* a,
        const sp_digit* b)
{
    sp_digit c = 0;

    __asm__ __volatile__ (
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "subs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "sbc	%[c], %[c], %[c]\n\t"
        : [c] "+r" (c), [a] "+r" (a), [b] "+r" (b)
        :
        : "memory", "r3", "r4", "r5", "r6"
    );

    return c;
}

/* Add b to a into r. (r = a + b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A single precision integer.
 */
SP_NOINLINE static sp_digit sp_4096_add_128(sp_digit* r, const sp_digit* a,
        const sp_digit* b)
{
    sp_digit c = 0;

    __asm__ __volatile__ (
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adds	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "mov	%[c], #0\n\t"
        "adc	%[c], %[c], %[c]\n\t"
        : [c] "+r" (c), [r] "+r" (r), [a] "+r" (a), [b] "+r" (b)
        :
        : "memory", "r4", "r5", "r6", "r8"
    );

    return c;
}

/* Multiply a and b into r. (r = a * b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A single precision integer.
 */
SP_NOINLINE static void sp_4096_mul_128(sp_digit* r, const sp_digit* a,
        const sp_digit* b)
{
    sp_digit* z0 = r;
    sp_digit z1[128];
    sp_digit a1[64];
    sp_digit b1[64];
    sp_digit z2[128];
    sp_digit u, ca, cb;

    ca = sp_2048_add_64(a1, a, &a[64]);
    cb = sp_2048_add_64(b1, b, &b[64]);
    u  = ca & cb;
    sp_2048_mul_64(z1, a1, b1);
    sp_2048_mul_64(z2, &a[64], &b[64]);
    sp_2048_mul_64(z0, a, b);
    sp_2048_mask_64(r + 128, a1, 0 - cb);
    sp_2048_mask_64(b1, b1, 0 - ca);
    u += sp_2048_add_64(r + 128, r + 128, b1);
    u += sp_4096_sub_in_place_128(z1, z2);
    u += sp_4096_sub_in_place_128(z1, z0);
    u += sp_4096_add_128(r + 64, r + 64, z1);
    r[192] = u;
    XMEMSET(r + 192 + 1, 0, sizeof(sp_digit) * (64 - 1));
    (void)sp_4096_add_128(r + 128, r + 128, z2);
}

/* Square a and put result in r. (r = a * a)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 */
SP_NOINLINE static void sp_4096_sqr_128(sp_digit* r, const sp_digit* a)
{
    sp_digit* z0 = r;
    sp_digit z2[128];
    sp_digit z1[128];
    sp_digit a1[64];
    sp_digit u;

    u = sp_2048_add_64(a1, a, &a[64]);
    sp_2048_sqr_64(z1, a1);
    sp_2048_sqr_64(z2, &a[64]);
    sp_2048_sqr_64(z0, a);
    sp_2048_mask_64(r + 128, a1, 0 - u);
    u += sp_2048_add_64(r + 128, r + 128, r + 128);
    u += sp_4096_sub_in_place_128(z1, z2);
    u += sp_4096_sub_in_place_128(z1, z0);
    u += sp_4096_add_128(r + 64, r + 64, z1);
    r[192] = u;
    XMEMSET(r + 192 + 1, 0, sizeof(sp_digit) * (64 - 1));
    (void)sp_4096_add_128(r + 128, r + 128, z2);
}

#endif /* !WOLFSSL_SP_SMALL */
#ifdef WOLFSSL_SP_SMALL
/* Add b to a into r. (r = a + b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A single precision integer.
 */
SP_NOINLINE static sp_digit sp_4096_add_128(sp_digit* r, const sp_digit* a,
        const sp_digit* b)
{
    sp_digit c = 0;

    __asm__ __volatile__ (
        "mov	r6, %[a]\n\t"
        "mov	r8, #0\n\t"
        "add	r6, r6, #512\n\t"
        "sub	r8, r8, #1\n\t"
        "\n1:\n\t"
        "adds	%[c], %[c], r8\n\t"
        "ldr	r4, [%[a]]\n\t"
        "ldr	r5, [%[b]]\n\t"
        "adcs	r4, r4, r5\n\t"
        "str	r4, [%[r]]\n\t"
        "mov	%[c], #0\n\t"
        "adc	%[c], %[c], %[c]\n\t"
        "add	%[a], %[a], #4\n\t"
        "add	%[b], %[b], #4\n\t"
        "add	%[r], %[r], #4\n\t"
        "cmp	%[a], r6\n\t"
        "bne	1b\n\t"
        : [c] "+r" (c), [r] "+r" (r), [a] "+r" (a), [b] "+r" (b)
        :
        : "memory", "r4", "r5", "r6", "r8"
    );

    return c;
}

#endif /* WOLFSSL_SP_SMALL */
#ifdef WOLFSSL_SP_SMALL
/* Sub b from a into a. (a -= b)
 *
 * a  A single precision integer.
 * b  A single precision integer.
 */
SP_NOINLINE static sp_digit sp_4096_sub_in_place_128(sp_digit* a,
        const sp_digit* b)
{
    sp_digit c = 0;
    __asm__ __volatile__ (
        "mov	r8, %[a]\n\t"
        "add	r8, r8, #512\n\t"
        "\n1:\n\t"
        "mov	r5, #0\n\t"
        "subs	r5, r5, %[c]\n\t"
        "ldr	r3, [%[a]]\n\t"
        "ldr	r4, [%[a], #4]\n\t"
        "ldr	r5, [%[b]]\n\t"
        "ldr	r6, [%[b], #4]\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "str	r3, [%[a]]\n\t"
        "str	r4, [%[a], #4]\n\t"
        "sbc	%[c], %[c], %[c]\n\t"
        "add	%[a], %[a], #8\n\t"
        "add	%[b], %[b], #8\n\t"
        "cmp	%[a], r8\n\t"
        "bne	1b\n\t"
        : [c] "+r" (c), [a] "+r" (a), [b] "+r" (b)
        :
        : "memory", "r3", "r4", "r5", "r6", "r8"
    );

    return c;
}

#endif /* WOLFSSL_SP_SMALL */
#ifdef WOLFSSL_SP_SMALL
/* Multiply a and b into r. (r = a * b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A single precision integer.
 */
SP_NOINLINE static void sp_4096_mul_128(sp_digit* r, const sp_digit* a,
        const sp_digit* b)
{
    sp_digit tmp[128 * 2];
    __asm__ __volatile__ (
        "mov	r3, #0\n\t"
        "mov	r4, #0\n\t"
        "mov	r9, r3\n\t"
        "mov	r12, %[r]\n\t"
        "mov	r10, %[a]\n\t"
        "mov	r11, %[b]\n\t"
        "mov	r6, #2\n\t"
        "lsl	r6, r6, #8\n\t"
        "add	r6, r6, r10\n\t"
        "mov	r14, r6\n\t"
        "\n1:\n\t"
        "mov	%[r], #0\n\t"
        "mov	r5, #0\n\t"
        "mov	r6, #1\n\t"
        "lsl	r6, r6, #8\n\t"
        "add	r6, r6, #252\n\t"
        "mov	%[a], r9\n\t"
        "subs	%[a], %[a], r6\n\t"
        "sbc	r6, r6, r6\n\t"
        "mvn	r6, r6\n\t"
        "and	%[a], %[a], r6\n\t"
        "mov	%[b], r9\n\t"
        "sub	%[b], %[b], %[a]\n\t"
        "add	%[a], %[a], r10\n\t"
        "add	%[b], %[b], r11\n\t"
        "\n2:\n\t"
        /* Multiply Start */
        "ldr	r6, [%[a]]\n\t"
        "ldr	r8, [%[b]]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r3, r3, r6\n\t"
        "adcs 	r4, r4, r8\n\t"
        "adc	r5, r5, %[r]\n\t"
        /* Multiply Done */
        "add	%[a], %[a], #4\n\t"
        "sub	%[b], %[b], #4\n\t"
        "cmp	%[a], r14\n\t"
        "beq	3f\n\t"
        "mov	r6, r9\n\t"
        "add	r6, r6, r10\n\t"
        "cmp	%[a], r6\n\t"
        "ble	2b\n\t"
        "\n3:\n\t"
        "mov	%[r], r12\n\t"
        "mov	r8, r9\n\t"
        "str	r3, [%[r], r8]\n\t"
        "mov	r3, r4\n\t"
        "mov	r4, r5\n\t"
        "add	r8, r8, #4\n\t"
        "mov	r9, r8\n\t"
        "mov	r6, #3\n\t"
        "lsl	r6, r6, #8\n\t"
        "add	r6, r6, #248\n\t"
        "cmp	r8, r6\n\t"
        "ble	1b\n\t"
        "str	r3, [%[r], r8]\n\t"
        "mov	%[a], r10\n\t"
        "mov	%[b], r11\n\t"
        :
        : [r] "r" (tmp), [a] "r" (a), [b] "r" (b)
        : "memory", "r3", "r4", "r5", "r6", "r8", "r9", "r10", "r11", "r12", "r14"
    );

    XMEMCPY(r, tmp, sizeof(tmp));
}

/* Square a and put result in r. (r = a * a)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 */
SP_NOINLINE static void sp_4096_sqr_128(sp_digit* r, const sp_digit* a)
{
    __asm__ __volatile__ (
        "mov	r3, #0\n\t"
        "mov	r4, #0\n\t"
        "mov	r5, #0\n\t"
        "mov	r9, r3\n\t"
        "mov	r12, %[r]\n\t"
        "mov	r6, #4\n\t"
        "lsl	r6, r6, #8\n\t"
        "neg	r6, r6\n\t"
        "add	sp, sp, r6\n\t"
        "mov	r11, sp\n\t"
        "mov	r10, %[a]\n\t"
        "\n1:\n\t"
        "mov	%[r], #0\n\t"
        "mov	r6, #1\n\t"
        "lsl	r6, r6, #8\n\t"
        "add	r6, r6, #252\n\t"
        "mov	%[a], r9\n\t"
        "subs	%[a], %[a], r6\n\t"
        "sbc	r6, r6, r6\n\t"
        "mvn	r6, r6\n\t"
        "and	%[a], %[a], r6\n\t"
        "mov	r2, r9\n\t"
        "sub	r2, r2, %[a]\n\t"
        "add	%[a], %[a], r10\n\t"
        "add	r2, r2, r10\n\t"
        "\n2:\n\t"
        "cmp	r2, %[a]\n\t"
        "beq	4f\n\t"
        /* Multiply * 2: Start */
        "ldr	r6, [%[a]]\n\t"
        "ldr	r8, [r2]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r3, r3, r6\n\t"
        "adcs 	r4, r4, r8\n\t"
        "adc	r5, r5, %[r]\n\t"
        "adds	r3, r3, r6\n\t"
        "adcs 	r4, r4, r8\n\t"
        "adc	r5, r5, %[r]\n\t"
        /* Multiply * 2: Done */
        "bal	5f\n\t"
        "\n4:\n\t"
        /* Square: Start */
        "ldr	r6, [%[a]]\n\t"
        "umull	r6, r8, r6, r6\n\t"
        "adds	r3, r3, r6\n\t"
        "adcs	r4, r4, r8\n\t"
        "adc	r5, r5, %[r]\n\t"
        /* Square: Done */
        "\n5:\n\t"
        "add	%[a], %[a], #4\n\t"
        "sub	r2, r2, #4\n\t"
        "mov	r6, #2\n\t"
        "lsl	r6, r6, #8\n\t"
        "add	r6, r6, r10\n\t"
        "cmp	%[a], r6\n\t"
        "beq	3f\n\t"
        "cmp	%[a], r2\n\t"
        "bgt	3f\n\t"
        "mov	r8, r9\n\t"
        "add	r8, r8, r10\n\t"
        "cmp	%[a], r8\n\t"
        "ble	2b\n\t"
        "\n3:\n\t"
        "mov	%[r], r11\n\t"
        "mov	r8, r9\n\t"
        "str	r3, [%[r], r8]\n\t"
        "mov	r3, r4\n\t"
        "mov	r4, r5\n\t"
        "mov	r5, #0\n\t"
        "add	r8, r8, #4\n\t"
        "mov	r9, r8\n\t"
        "mov	r6, #3\n\t"
        "lsl	r6, r6, #8\n\t"
        "add	r6, r6, #248\n\t"
        "cmp	r8, r6\n\t"
        "ble	1b\n\t"
        "mov	%[a], r10\n\t"
        "str	r3, [%[r], r8]\n\t"
        "mov	%[r], r12\n\t"
        "mov	%[a], r11\n\t"
        "mov	r3, #3\n\t"
        "lsl	r3, r3, #8\n\t"
        "add	r3, r3, #252\n\t"
        "\n4:\n\t"
        "ldr	r6, [%[a], r3]\n\t"
        "str	r6, [%[r], r3]\n\t"
        "subs	r3, r3, #4\n\t"
        "bge	4b\n\t"
        "mov	r6, #4\n\t"
        "lsl	r6, r6, #8\n\t"
        "add	sp, sp, r6\n\t"
        :
        : [r] "r" (r), [a] "r" (a)
        : "memory", "r2", "r3", "r4", "r5", "r6", "r8", "r9", "r10", "r11", "r12"
    );
}

#endif /* WOLFSSL_SP_SMALL */
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

    /* rho = -1/m mod b */
    *rho = -x;
}

/* Mul a by digit b into r. (r = a * b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A single precision digit.
 */
SP_NOINLINE static void sp_4096_mul_d_128(sp_digit* r, const sp_digit* a,
        sp_digit b)
{
    __asm__ __volatile__ (
        "add	r9, %[a], #512\n\t"
        /* A[0] * B */
        "ldr	r6, [%[a]], #4\n\t"
        "umull	r5, r3, r6, %[b]\n\t"
        "mov	r4, #0\n\t"
        "str	r5, [%[r]], #4\n\t"
        /* A[0] * B - Done */
        "\n1:\n\t"
        "mov	r5, #0\n\t"
        /* A[] * B */
        "ldr	r6, [%[a]], #4\n\t"
        "umull	r6, r8, r6, %[b]\n\t"
        "adds	r3, r3, r6\n\t"
        "adcs 	r4, r4, r8\n\t"
        "adc	r5, r5, #0\n\t"
        /* A[] * B - Done */
        "str	r3, [%[r]], #4\n\t"
        "mov	r3, r4\n\t"
        "mov	r4, r5\n\t"
        "cmp	%[a], r9\n\t"
        "blt	1b\n\t"
        "str	r3, [%[r]]\n\t"
        : [r] "+r" (r), [a] "+r" (a)
        : [b] "r" (b)
        : "memory", "r3", "r4", "r5", "r6", "r8", "r9"
    );
}

#if defined(WOLFSSL_HAVE_SP_RSA) || defined(WOLFSSL_HAVE_SP_DH)
/* r = 2^n mod m where n is the number of bits to reduce by.
 * Given m must be 4096 bits, just need to subtract.
 *
 * r  A single precision number.
 * m  A single precision number.
 */
static void sp_4096_mont_norm_128(sp_digit* r, const sp_digit* m)
{
    XMEMSET(r, 0, sizeof(sp_digit) * 128);

    /* r = 2^n mod m */
    sp_4096_sub_in_place_128(r, m);
}

#endif /* WOLFSSL_HAVE_SP_RSA || WOLFSSL_HAVE_SP_DH */
/* Conditionally subtract b from a using the mask m.
 * m is -1 to subtract and 0 when not copying.
 *
 * r  A single precision number representing condition subtract result.
 * a  A single precision number to subtract from.
 * b  A single precision number to subtract.
 * m  Mask value to apply.
 */
SP_NOINLINE static sp_digit sp_4096_cond_sub_128(sp_digit* r, const sp_digit* a,
        const sp_digit* b, sp_digit m)
{
    sp_digit c = 0;

    __asm__ __volatile__ (
        "mov	r5, #2\n\t"
        "lsl	r5, r5, #8\n\t"
        "mov	r9, r5\n\t"
        "mov	r8, #0\n\t"
        "\n1:\n\t"
        "ldr	r6, [%[b], r8]\n\t"
        "and	r6, r6, %[m]\n\t"
        "mov	r5, #0\n\t"
        "subs	r5, r5, %[c]\n\t"
        "ldr	r5, [%[a], r8]\n\t"
        "sbcs	r5, r5, r6\n\t"
        "sbcs	%[c], %[c], %[c]\n\t"
        "str	r5, [%[r], r8]\n\t"
        "add	r8, r8, #4\n\t"
        "cmp	r8, r9\n\t"
        "blt	1b\n\t"
        : [c] "+r" (c)
        : [r] "r" (r), [a] "r" (a), [b] "r" (b), [m] "r" (m)
        : "memory", "r5", "r6", "r8", "r9"
    );

    return c;
}

/* Reduce the number back to 4096 bits using Montgomery reduction.
 *
 * a   A single precision number to reduce in place.
 * m   The single precision number representing the modulus.
 * mp  The digit representing the negative inverse of m mod 2^n.
 */
SP_NOINLINE static void sp_4096_mont_reduce_128(sp_digit* a, const sp_digit* m,
        sp_digit mp)
{
    sp_digit ca = 0;

    __asm__ __volatile__ (
        "mov	r9, %[mp]\n\t"
        "mov	r12, %[m]\n\t"
        "mov	r10, %[a]\n\t"
        "mov	r4, #0\n\t"
        "add	r11, r10, #512\n\t"
        "\n1:\n\t"
        /* mu = a[i] * mp */
        "mov	%[mp], r9\n\t"
        "ldr	%[a], [r10]\n\t"
        "mul	%[mp], %[mp], %[a]\n\t"
        "mov	%[m], r12\n\t"
        "add	r14, r10, #504\n\t"
        "\n2:\n\t"
        /* a[i+j] += m[j] * mu */
        "ldr	%[a], [r10]\n\t"
        "mov	r5, #0\n\t"
        /* Multiply m[j] and mu - Start */
        "ldr	r8, [%[m]], #4\n\t"
        "umull	r6, r8, %[mp], r8\n\t"
        "adds	%[a], %[a], r6\n\t"
        "adc	r5, r5, r8\n\t"
        /* Multiply m[j] and mu - Done */
        "adds	r4, r4, %[a]\n\t"
        "adc	r5, r5, #0\n\t"
        "str	r4, [r10], #4\n\t"
        /* a[i+j+1] += m[j+1] * mu */
        "ldr	%[a], [r10]\n\t"
        "mov	r4, #0\n\t"
        /* Multiply m[j] and mu - Start */
        "ldr	r8, [%[m]], #4\n\t"
        "umull	r6, r8, %[mp], r8\n\t"
        "adds	%[a], %[a], r6\n\t"
        "adc	r4, r4, r8\n\t"
        /* Multiply m[j] and mu - Done */
        "adds	r5, r5, %[a]\n\t"
        "adc	r4, r4, #0\n\t"
        "str	r5, [r10], #4\n\t"
        "cmp	r10, r14\n\t"
        "blt	2b\n\t"
        /* a[i+126] += m[126] * mu */
        "ldr	%[a], [r10]\n\t"
        "mov	r5, #0\n\t"
        /* Multiply m[j] and mu - Start */
        "ldr	r8, [%[m]], #4\n\t"
        "umull	r6, r8, %[mp], r8\n\t"
        "adds	%[a], %[a], r6\n\t"
        "adc	r5, r5, r8\n\t"
        /* Multiply m[j] and mu - Done */
        "adds	r4, r4, %[a]\n\t"
        "adc	r5, r5, #0\n\t"
        "str	r4, [r10], #4\n\t"
        /* a[i+127] += m[127] * mu */
        "mov	r4, %[ca]\n\t"
        "mov	%[ca], #0\n\t"
        /* Multiply m[127] and mu - Start */
        "ldr	r8, [%[m]]\n\t"
        "umull	r6, r8, %[mp], r8\n\t"
        "adds	r5, r5, r6\n\t"
        "adcs 	r4, r4, r8\n\t"
        "adc	%[ca], %[ca], #0\n\t"
        /* Multiply m[127] and mu - Done */
        "ldr	r6, [r10]\n\t"
        "ldr	r8, [r10, #4]\n\t"
        "adds	r6, r6, r5\n\t"
        "adcs	r8, r8, r4\n\t"
        "adc	%[ca], %[ca], #0\n\t"
        "str	r6, [r10]\n\t"
        "str	r8, [r10, #4]\n\t"
        /* Next word in a */
        "sub	r10, r10, #504\n\t"
        "cmp	r10, r11\n\t"
        "blt	1b\n\t"
        "mov	%[a], r10\n\t"
        "mov	%[m], r12\n\t"
        : [ca] "+r" (ca), [a] "+r" (a)
        : [m] "r" (m), [mp] "r" (mp)
        : "memory", "r4", "r5", "r6", "r8", "r9", "r10", "r11", "r12", "r14"
    );

    sp_4096_cond_sub_128(a - 128, a, m, (sp_digit)0 - ca);
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
static void sp_4096_mont_mul_128(sp_digit* r, const sp_digit* a, const sp_digit* b,
        const sp_digit* m, sp_digit mp)
{
    sp_4096_mul_128(r, a, b);
    sp_4096_mont_reduce_128(r, m, mp);
}

/* Square the Montgomery form number. (r = a * a mod m)
 *
 * r   Result of squaring.
 * a   Number to square in Montogmery form.
 * m   Modulus (prime).
 * mp  Montogmery mulitplier.
 */
static void sp_4096_mont_sqr_128(sp_digit* r, const sp_digit* a, const sp_digit* m,
        sp_digit mp)
{
    sp_4096_sqr_128(r, a);
    sp_4096_mont_reduce_128(r, m, mp);
}

/* Divide the double width number (d1|d0) by the dividend. (d1|d0 / div)
 *
 * d1   The high order half of the number to divide.
 * d0   The low order half of the number to divide.
 * div  The dividend.
 * returns the result of the division.
 *
 * Note that this is an approximate div. It may give an answer 1 larger.
 */
SP_NOINLINE static sp_digit div_4096_word_128(sp_digit d1, sp_digit d0,
        sp_digit div)
{
    sp_digit r = 0;

    __asm__ __volatile__ (
        "lsr	r6, %[div], #16\n\t"
        "add	r6, r6, #1\n\t"
        "udiv	r4, %[d1], r6\n\t"
        "lsl	r8, r4, #16\n\t"
        "umull	r4, r5, %[div], r8\n\t"
        "subs	%[d0], %[d0], r4\n\t"
        "sbc	%[d1], %[d1], r5\n\t"
        "udiv	r5, %[d1], r6\n\t"
        "lsl	r4, r5, #16\n\t"
        "add	r8, r8, r4\n\t"
        "umull	r4, r5, %[div], r4\n\t"
        "subs	%[d0], %[d0], r4\n\t"
        "sbc	%[d1], %[d1], r5\n\t"
        "lsl	r4, %[d1], #16\n\t"
        "orr	r4, r4, %[d0], lsr #16\n\t"
        "udiv	r4, r4, r6\n\t"
        "add	r8, r8, r4\n\t"
        "umull	r4, r5, %[div], r4\n\t"
        "subs	%[d0], %[d0], r4\n\t"
        "sbc	%[d1], %[d1], r5\n\t"
        "lsl	r4, %[d1], #16\n\t"
        "orr	r4, r4, %[d0], lsr #16\n\t"
        "udiv	r4, r4, r6\n\t"
        "add	r8, r8, r4\n\t"
        "umull	r4, r5, %[div], r4\n\t"
        "subs	%[d0], %[d0], r4\n\t"
        "sbc	%[d1], %[d1], r5\n\t"
        "udiv	r4, %[d0], %[div]\n\t"
        "add	r8, r8, r4\n\t"
        "mov	%[r], r8\n\t"
        : [r] "+r" (r)
        : [d1] "r" (d1), [d0] "r" (d0), [div] "r" (div)
        : "r4", "r5", "r6", "r8"
    );
    return r;
}

/* AND m into each word of a and store in r.
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * m  Mask to AND against each digit.
 */
static void sp_4096_mask_128(sp_digit* r, const sp_digit* a, sp_digit m)
{
#ifdef WOLFSSL_SP_SMALL
    int i;

    for (i=0; i<128; i++) {
        r[i] = a[i] & m;
    }
#else
    int i;

    for (i = 0; i < 128; i += 8) {
        r[i+0] = a[i+0] & m;
        r[i+1] = a[i+1] & m;
        r[i+2] = a[i+2] & m;
        r[i+3] = a[i+3] & m;
        r[i+4] = a[i+4] & m;
        r[i+5] = a[i+5] & m;
        r[i+6] = a[i+6] & m;
        r[i+7] = a[i+7] & m;
    }
#endif
}

/* Compare a with b in constant time.
 *
 * a  A single precision integer.
 * b  A single precision integer.
 * return -ve, 0 or +ve if a is less than, equal to or greater than b
 * respectively.
 */
SP_NOINLINE static int32_t sp_4096_cmp_128(const sp_digit* a, const sp_digit* b)
{
    sp_digit r = 0;


    __asm__ __volatile__ (
        "mov	r3, #0\n\t"
        "mvn	r3, r3\n\t"
        "mov	r6, #1\n\t"
        "lsl	r6, r6, #8\n\t"
        "add	r6, r6, #252\n\t"
        "\n1:\n\t"
        "ldr	r8, [%[a], r6]\n\t"
        "ldr	r5, [%[b], r6]\n\t"
        "and	r8, r8, r3\n\t"
        "and	r5, r5, r3\n\t"
        "mov	r4, r8\n\t"
        "subs	r8, r8, r5\n\t"
        "sbc	r8, r8, r8\n\t"
        "add	%[r], %[r], r8\n\t"
        "mvn	r8, r8\n\t"
        "and	r3, r3, r8\n\t"
        "subs	r5, r5, r4\n\t"
        "sbc	r8, r8, r8\n\t"
        "sub	%[r], %[r], r8\n\t"
        "mvn	r8, r8\n\t"
        "and	r3, r3, r8\n\t"
        "sub	r6, r6, #4\n\t"
        "cmp	r6, #0\n\t"
        "bge	1b\n\t"
        : [r] "+r" (r)
        : [a] "r" (a), [b] "r" (b)
        : "r3", "r4", "r5", "r6", "r8"
    );

    return r;
}

/* Divide d in a and put remainder into r (m*d + r = a)
 * m is not calculated as it is not needed at this time.
 *
 * a  Nmber to be divided.
 * d  Number to divide with.
 * m  Multiplier result.
 * r  Remainder from the division.
 * returns MP_OKAY indicating success.
 */
static WC_INLINE int sp_4096_div_128(const sp_digit* a, const sp_digit* d, sp_digit* m,
        sp_digit* r)
{
    sp_digit t1[256], t2[129];
    sp_digit div, r1;
    int i;

    (void)m;

    div = d[127];
    XMEMCPY(t1, a, sizeof(*t1) * 2 * 128);
    for (i=127; i>=0; i--) {
        r1 = div_4096_word_128(t1[128 + i], t1[128 + i - 1], div);

        sp_4096_mul_d_128(t2, d, r1);
        t1[128 + i] += sp_4096_sub_in_place_128(&t1[i], t2);
        t1[128 + i] -= t2[128];
        sp_4096_mask_128(t2, d, t1[128 + i]);
        t1[128 + i] += sp_4096_add_128(&t1[i], &t1[i], t2);
        sp_4096_mask_128(t2, d, t1[128 + i]);
        t1[128 + i] += sp_4096_add_128(&t1[i], &t1[i], t2);
    }

    r1 = sp_4096_cmp_128(t1, d) >= 0;
    sp_4096_cond_sub_128(r, t1, d, (sp_digit)0 - r1);

    return MP_OKAY;
}

/* Reduce a modulo m into r. (r = a mod m)
 *
 * r  A single precision number that is the reduced result.
 * a  A single precision number that is to be reduced.
 * m  A single precision number that is the modulus to reduce with.
 * returns MP_OKAY indicating success.
 */
static WC_INLINE int sp_4096_mod_128(sp_digit* r, const sp_digit* a, const sp_digit* m)
{
    return sp_4096_div_128(a, m, NULL, r);
}

/* Divide d in a and put remainder into r (m*d + r = a)
 * m is not calculated as it is not needed at this time.
 *
 * a  Nmber to be divided.
 * d  Number to divide with.
 * m  Multiplier result.
 * r  Remainder from the division.
 * returns MP_OKAY indicating success.
 */
static WC_INLINE int sp_4096_div_128_cond(const sp_digit* a, const sp_digit* d, sp_digit* m,
        sp_digit* r)
{
    sp_digit t1[256], t2[129];
    sp_digit div, r1;
    int i;

    (void)m;

    div = d[127];
    XMEMCPY(t1, a, sizeof(*t1) * 2 * 128);
    for (i=127; i>=0; i--) {
        r1 = div_4096_word_128(t1[128 + i], t1[128 + i - 1], div);

        sp_4096_mul_d_128(t2, d, r1);
        t1[128 + i] += sp_4096_sub_in_place_128(&t1[i], t2);
        t1[128 + i] -= t2[128];
        if (t1[128 + i] != 0) {
            t1[128 + i] += sp_4096_add_128(&t1[i], &t1[i], d);
            if (t1[128 + i] != 0)
                t1[128 + i] += sp_4096_add_128(&t1[i], &t1[i], d);
        }
    }

    r1 = sp_4096_cmp_128(t1, d) >= 0;
    sp_4096_cond_sub_128(r, t1, d, (sp_digit)0 - r1);

    return MP_OKAY;
}

/* Reduce a modulo m into r. (r = a mod m)
 *
 * r  A single precision number that is the reduced result.
 * a  A single precision number that is to be reduced.
 * m  A single precision number that is the modulus to reduce with.
 * returns MP_OKAY indicating success.
 */
static WC_INLINE int sp_4096_mod_128_cond(sp_digit* r, const sp_digit* a, const sp_digit* m)
{
    return sp_4096_div_128_cond(a, m, NULL, r);
}

#if (defined(WOLFSSL_HAVE_SP_RSA) && !defined(WOLFSSL_RSA_PUBLIC_ONLY)) || \
                                                     defined(WOLFSSL_HAVE_SP_DH)
#ifdef WOLFSSL_SP_SMALL
/* Modular exponentiate a to the e mod m. (r = a^e mod m)
 *
 * r     A single precision number that is the result of the operation.
 * a     A single precision number being exponentiated.
 * e     A single precision number that is the exponent.
 * bits  The number of bits in the exponent.
 * m     A single precision number that is the modulus.
 * returns 0 on success and MEMORY_E on dynamic memory allocation failure.
 */
static int sp_4096_mod_exp_128(sp_digit* r, const sp_digit* a, const sp_digit* e,
        int bits, const sp_digit* m, int reduceA)
{
#if defined(WOLFSSL_SMALL_STACK) && !defined(WOLFSSL_SP_NO_MALLOC)
    sp_digit* td;
#else
    sp_digit td[16 * 256];
#endif
    sp_digit* t[16];
    sp_digit* norm;
    sp_digit mp = 1;
    sp_digit n;
    sp_digit mask;
    int i;
    int c, y;
    int err = MP_OKAY;

#if defined(WOLFSSL_SMALL_STACK) && !defined(WOLFSSL_SP_NO_MALLOC)
    td = (sp_digit*)XMALLOC(sizeof(sp_digit) * (16 * 256), NULL,
                            DYNAMIC_TYPE_TMP_BUFFER);
    if (td == NULL) {
        err = MEMORY_E;
    }
#endif

    if (err == MP_OKAY) {
        norm = td;
        for (i=0; i<16; i++) {
#if defined(WOLFSSL_SMALL_STACK) && !defined(WOLFSSL_SP_NO_MALLOC)
            t[i] = td + i * 256;
#else
            t[i] = &td[i * 256];
#endif
        }

        sp_4096_mont_setup(m, &mp);
        sp_4096_mont_norm_128(norm, m);

        XMEMSET(t[1], 0, sizeof(sp_digit) * 128U);
        if (reduceA != 0) {
            err = sp_4096_mod_128(t[1] + 128, a, m);
            if (err == MP_OKAY) {
                err = sp_4096_mod_128(t[1], t[1], m);
            }
        }
        else {
            XMEMCPY(t[1] + 128, a, sizeof(sp_digit) * 128);
            err = sp_4096_mod_128(t[1], t[1], m);
        }
    }

    if (err == MP_OKAY) {
        sp_4096_mont_sqr_128(t[ 2], t[ 1], m, mp);
        sp_4096_mont_mul_128(t[ 3], t[ 2], t[ 1], m, mp);
        sp_4096_mont_sqr_128(t[ 4], t[ 2], m, mp);
        sp_4096_mont_mul_128(t[ 5], t[ 3], t[ 2], m, mp);
        sp_4096_mont_sqr_128(t[ 6], t[ 3], m, mp);
        sp_4096_mont_mul_128(t[ 7], t[ 4], t[ 3], m, mp);
        sp_4096_mont_sqr_128(t[ 8], t[ 4], m, mp);
        sp_4096_mont_mul_128(t[ 9], t[ 5], t[ 4], m, mp);
        sp_4096_mont_sqr_128(t[10], t[ 5], m, mp);
        sp_4096_mont_mul_128(t[11], t[ 6], t[ 5], m, mp);
        sp_4096_mont_sqr_128(t[12], t[ 6], m, mp);
        sp_4096_mont_mul_128(t[13], t[ 7], t[ 6], m, mp);
        sp_4096_mont_sqr_128(t[14], t[ 7], m, mp);
        sp_4096_mont_mul_128(t[15], t[ 8], t[ 7], m, mp);

        i = (bits - 1) / 32;
        n = e[i--];
        c = bits & 31;
        if (c == 0) {
            c = 32;
        }
        c -= bits % 4;
        if (c == 32) {
            c = 28;
        }
        y = (int)(n >> c);
        n <<= 32 - c;
        XMEMCPY(r, t[y], sizeof(sp_digit) * 128);
        for (; i>=0 || c>=4; ) {
            if (c == 0) {
                n = e[i--];
                y = n >> 28;
                n <<= 4;
                c = 28;
            }
            else if (c < 4) {
                y = n >> 28;
                n = e[i--];
                c = 4 - c;
                y |= n >> (32 - c);
                n <<= c;
                c = 32 - c;
            }
            else {
                y = (n >> 28) & 0xf;
                n <<= 4;
                c -= 4;
            }

            sp_4096_mont_sqr_128(r, r, m, mp);
            sp_4096_mont_sqr_128(r, r, m, mp);
            sp_4096_mont_sqr_128(r, r, m, mp);
            sp_4096_mont_sqr_128(r, r, m, mp);

            sp_4096_mont_mul_128(r, r, t[y], m, mp);
        }

        XMEMSET(&r[128], 0, sizeof(sp_digit) * 128U);
        sp_4096_mont_reduce_128(r, m, mp);

        mask = 0 - (sp_4096_cmp_128(r, m) >= 0);
        sp_4096_cond_sub_128(r, r, m, mask);
    }

#if defined(WOLFSSL_SMALL_STACK) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (td != NULL) {
        XFREE(td, NULL, DYNAMIC_TYPE_TMP_BUFFER);
    }
#endif

    return err;
}
#else
/* Modular exponentiate a to the e mod m. (r = a^e mod m)
 *
 * r     A single precision number that is the result of the operation.
 * a     A single precision number being exponentiated.
 * e     A single precision number that is the exponent.
 * bits  The number of bits in the exponent.
 * m     A single precision number that is the modulus.
 * returns 0 on success and MEMORY_E on dynamic memory allocation failure.
 */
static int sp_4096_mod_exp_128(sp_digit* r, const sp_digit* a, const sp_digit* e,
        int bits, const sp_digit* m, int reduceA)
{
#if defined(WOLFSSL_SMALL_STACK) && !defined(WOLFSSL_SP_NO_MALLOC)
    sp_digit* td;
#else
    sp_digit td[32 * 256];
#endif
    sp_digit* t[32];
    sp_digit* norm;
    sp_digit mp = 1;
    sp_digit n;
    sp_digit mask;
    int i;
    int c, y;
    int err = MP_OKAY;

#if defined(WOLFSSL_SMALL_STACK) && !defined(WOLFSSL_SP_NO_MALLOC)
    td = (sp_digit*)XMALLOC(sizeof(sp_digit) * (32 * 256), NULL,
                            DYNAMIC_TYPE_TMP_BUFFER);
    if (td == NULL) {
        err = MEMORY_E;
    }
#endif

    if (err == MP_OKAY) {
        norm = td;
        for (i=0; i<32; i++) {
#if defined(WOLFSSL_SMALL_STACK) && !defined(WOLFSSL_SP_NO_MALLOC)
            t[i] = td + i * 256;
#else
            t[i] = &td[i * 256];
#endif
        }

        sp_4096_mont_setup(m, &mp);
        sp_4096_mont_norm_128(norm, m);

        XMEMSET(t[1], 0, sizeof(sp_digit) * 128U);
        if (reduceA != 0) {
            err = sp_4096_mod_128(t[1] + 128, a, m);
            if (err == MP_OKAY) {
                err = sp_4096_mod_128(t[1], t[1], m);
            }
        }
        else {
            XMEMCPY(t[1] + 128, a, sizeof(sp_digit) * 128);
            err = sp_4096_mod_128(t[1], t[1], m);
        }
    }

    if (err == MP_OKAY) {
        sp_4096_mont_sqr_128(t[ 2], t[ 1], m, mp);
        sp_4096_mont_mul_128(t[ 3], t[ 2], t[ 1], m, mp);
        sp_4096_mont_sqr_128(t[ 4], t[ 2], m, mp);
        sp_4096_mont_mul_128(t[ 5], t[ 3], t[ 2], m, mp);
        sp_4096_mont_sqr_128(t[ 6], t[ 3], m, mp);
        sp_4096_mont_mul_128(t[ 7], t[ 4], t[ 3], m, mp);
        sp_4096_mont_sqr_128(t[ 8], t[ 4], m, mp);
        sp_4096_mont_mul_128(t[ 9], t[ 5], t[ 4], m, mp);
        sp_4096_mont_sqr_128(t[10], t[ 5], m, mp);
        sp_4096_mont_mul_128(t[11], t[ 6], t[ 5], m, mp);
        sp_4096_mont_sqr_128(t[12], t[ 6], m, mp);
        sp_4096_mont_mul_128(t[13], t[ 7], t[ 6], m, mp);
        sp_4096_mont_sqr_128(t[14], t[ 7], m, mp);
        sp_4096_mont_mul_128(t[15], t[ 8], t[ 7], m, mp);
        sp_4096_mont_sqr_128(t[16], t[ 8], m, mp);
        sp_4096_mont_mul_128(t[17], t[ 9], t[ 8], m, mp);
        sp_4096_mont_sqr_128(t[18], t[ 9], m, mp);
        sp_4096_mont_mul_128(t[19], t[10], t[ 9], m, mp);
        sp_4096_mont_sqr_128(t[20], t[10], m, mp);
        sp_4096_mont_mul_128(t[21], t[11], t[10], m, mp);
        sp_4096_mont_sqr_128(t[22], t[11], m, mp);
        sp_4096_mont_mul_128(t[23], t[12], t[11], m, mp);
        sp_4096_mont_sqr_128(t[24], t[12], m, mp);
        sp_4096_mont_mul_128(t[25], t[13], t[12], m, mp);
        sp_4096_mont_sqr_128(t[26], t[13], m, mp);
        sp_4096_mont_mul_128(t[27], t[14], t[13], m, mp);
        sp_4096_mont_sqr_128(t[28], t[14], m, mp);
        sp_4096_mont_mul_128(t[29], t[15], t[14], m, mp);
        sp_4096_mont_sqr_128(t[30], t[15], m, mp);
        sp_4096_mont_mul_128(t[31], t[16], t[15], m, mp);

        i = (bits - 1) / 32;
        n = e[i--];
        c = bits & 31;
        if (c == 0) {
            c = 32;
        }
        c -= bits % 5;
        if (c == 32) {
            c = 27;
        }
        y = (int)(n >> c);
        n <<= 32 - c;
        XMEMCPY(r, t[y], sizeof(sp_digit) * 128);
        for (; i>=0 || c>=5; ) {
            if (c == 0) {
                n = e[i--];
                y = n >> 27;
                n <<= 5;
                c = 27;
            }
            else if (c < 5) {
                y = n >> 27;
                n = e[i--];
                c = 5 - c;
                y |= n >> (32 - c);
                n <<= c;
                c = 32 - c;
            }
            else {
                y = (n >> 27) & 0x1f;
                n <<= 5;
                c -= 5;
            }

            sp_4096_mont_sqr_128(r, r, m, mp);
            sp_4096_mont_sqr_128(r, r, m, mp);
            sp_4096_mont_sqr_128(r, r, m, mp);
            sp_4096_mont_sqr_128(r, r, m, mp);
            sp_4096_mont_sqr_128(r, r, m, mp);

            sp_4096_mont_mul_128(r, r, t[y], m, mp);
        }

        XMEMSET(&r[128], 0, sizeof(sp_digit) * 128U);
        sp_4096_mont_reduce_128(r, m, mp);

        mask = 0 - (sp_4096_cmp_128(r, m) >= 0);
        sp_4096_cond_sub_128(r, r, m, mask);
    }

#if defined(WOLFSSL_SMALL_STACK) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (td != NULL) {
        XFREE(td, NULL, DYNAMIC_TYPE_TMP_BUFFER);
    }
#endif

    return err;
}
#endif /* WOLFSSL_SP_SMALL */
#endif /* (WOLFSSL_HAVE_SP_RSA && !WOLFSSL_RSA_PUBLIC_ONLY) || WOLFSSL_HAVE_SP_DH */

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
#if (!defined(WOLFSSL_SP_SMALL) && !defined(WOLFSSL_SMALL_STACK)) || defined(WOLFSSL_SP_NO_MALLOC)
    sp_digit a[256], m[128], r[256];
#else
    sp_digit* d = NULL;
    sp_digit* a = NULL;
    sp_digit* m = NULL;
    sp_digit* r = NULL;
#endif
    sp_digit *ah = NULL;
    sp_digit e[1];
    int err = MP_OKAY;

    if (*outLen < 512)
        err = MP_TO_E;
    if (err == MP_OKAY && (mp_count_bits(em) > 32 || inLen > 512 ||
                                                     mp_count_bits(mm) != 4096))
        err = MP_READ_E;

#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (err == MP_OKAY) {
        d = (sp_digit*)XMALLOC(sizeof(sp_digit) * 128 * 5, NULL,
                                                              DYNAMIC_TYPE_RSA);
        if (d == NULL)
            err = MEMORY_E;
    }

    if (err == MP_OKAY) {
        a = d;
        r = a + 128 * 2;
        m = r + 128 * 2;
    }
#endif

    if (err == MP_OKAY) {
        ah = a + 128;

        sp_4096_from_bin(ah, 128, in, inLen);
#if DIGIT_BIT >= 32
        e[0] = em->dp[0];
#else
        e[0] = em->dp[0];
        if (em->used > 1) {
            e[0] |= ((sp_digit)em->dp[1]) << DIGIT_BIT;
        }
#endif
        if (e[0] == 0) {
            err = MP_EXPTMOD_E;
        }
    }
    if (err == MP_OKAY) {
        sp_4096_from_mp(m, 128, mm);

        if (e[0] == 0x3) {
            if (err == MP_OKAY) {
                sp_4096_sqr_128(r, ah);
                err = sp_4096_mod_128_cond(r, r, m);
            }
            if (err == MP_OKAY) {
                sp_4096_mul_128(r, ah, r);
                err = sp_4096_mod_128_cond(r, r, m);
            }
        }
        else {
            int i;
            sp_digit mp;

            sp_4096_mont_setup(m, &mp);

            /* Convert to Montgomery form. */
            XMEMSET(a, 0, sizeof(sp_digit) * 128);
            err = sp_4096_mod_128_cond(a, a, m);

            if (err == MP_OKAY) {
                for (i = 31; i >= 0; i--) {
                    if (e[0] >> i) {
                        break;
                    }
                }

                XMEMCPY(r, a, sizeof(sp_digit) * 128);
                for (i--; i>=0; i--) {
                    sp_4096_mont_sqr_128(r, r, m, mp);
                    if (((e[0] >> i) & 1) == 1) {
                        sp_4096_mont_mul_128(r, r, a, m, mp);
                    }
                }
                XMEMSET(&r[128], 0, sizeof(sp_digit) * 128);
                sp_4096_mont_reduce_128(r, m, mp);

                for (i = 127; i > 0; i--) {
                    if (r[i] != m[i]) {
                        break;
                    }
                }
                if (r[i] >= m[i]) {
                    sp_4096_sub_in_place_128(r, m);
                }
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
}

#ifndef WOLFSSL_RSA_PUBLIC_ONLY
/* Conditionally add a and b using the mask m.
 * m is -1 to add and 0 when not.
 *
 * r  A single precision number representing conditional add result.
 * a  A single precision number to add with.
 * b  A single precision number to add.
 * m  Mask value to apply.
 */
SP_NOINLINE static sp_digit sp_4096_cond_add_64(sp_digit* r, const sp_digit* a, const sp_digit* b,
        sp_digit m)
{
    sp_digit c = 0;

    __asm__ __volatile__ (
        "mov	r5, #1\n\t"
        "lsl	r5, r5, #8\n\t"
        "mov	r9, r5\n\t"
        "mov	r8, #0\n\t"
        "\n1:\n\t"
        "ldr	r6, [%[b], r8]\n\t"
        "and	r6, r6, %[m]\n\t"
        "adds	r5, %[c], #-1\n\t"
        "ldr	r5, [%[a], r8]\n\t"
        "adcs	r5, r5, r6\n\t"
        "mov	%[c], #0\n\t"
        "adcs	%[c], %[c], %[c]\n\t"
        "str	r5, [%[r], r8]\n\t"
        "add	r8, r8, #4\n\t"
        "cmp	r8, r9\n\t"
        "blt	1b\n\t"
        : [c] "+r" (c)
        : [r] "r" (r), [a] "r" (a), [b] "r" (b), [m] "r" (m)
        : "memory", "r5", "r6", "r8", "r9"
    );

    return c;
}

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
        d = (sp_digit*)XMALLOC(sizeof(sp_digit) * 128 * 4, NULL,
                                                              DYNAMIC_TYPE_RSA);
        if (d == NULL) {
            err = MEMORY_E;
        }
    }
    if (err == MP_OKAY) {
        a = d + 128;
        m = a + 256;
        r = a;

        sp_4096_from_bin(a, 128, in, inLen);
        sp_4096_from_mp(d, 128, dm);
        sp_4096_from_mp(m, 128, mm);
        err = sp_4096_mod_exp_128(r, a, d, 4096, m, 0);
    }
    if (err == MP_OKAY) {
        sp_4096_to_bin(r, out);
        *outLen = 512;
    }

    if (d != NULL) {
        XMEMSET(d, 0, sizeof(sp_digit) * 128);
        XFREE(d, NULL, DYNAMIC_TYPE_RSA);
    }

    return err;
#else
#if (!defined(WOLFSSL_SP_SMALL) && !defined(WOLFSSL_SMALL_STACK)) || defined(WOLFSSL_SP_NO_MALLOC)
    sp_digit a[128 * 2];
    sp_digit p[64], q[64], dp[64];
    sp_digit tmpa[128], tmpb[128];
#else
    sp_digit* t = NULL;
    sp_digit* a = NULL;
    sp_digit* p = NULL;
    sp_digit* q = NULL;
    sp_digit* dp = NULL;
    sp_digit* tmpa = NULL;
    sp_digit* tmpb = NULL;
#endif
    sp_digit* r = NULL;
    sp_digit* qi = NULL;
    sp_digit* dq = NULL;
    sp_digit c;
    int err = MP_OKAY;

    (void)dm;
    (void)mm;

    if (*outLen < 512)
        err = MP_TO_E;
    if (err == MP_OKAY && (inLen > 512 || mp_count_bits(mm) != 4096))
        err = MP_READ_E;

#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (err == MP_OKAY) {
        t = (sp_digit*)XMALLOC(sizeof(sp_digit) * 64 * 11, NULL,
                                                              DYNAMIC_TYPE_RSA);
        if (t == NULL)
            err = MEMORY_E;
    }
    if (err == MP_OKAY) {
        a = t;
        p = a + 128 * 2;
        q = p + 64;
        qi = dq = dp = q + 64;
        tmpa = qi + 64;
        tmpb = tmpa + 128;

        r = t + 128;
    }
#else
#endif

    if (err == MP_OKAY) {
#if (!defined(WOLFSSL_SP_SMALL) && !defined(WOLFSSL_SMALL_STACK)) || defined(WOLFSSL_SP_NO_MALLOC)
        r = a;
        qi = dq = dp;
#endif
        sp_4096_from_bin(a, 128, in, inLen);
        sp_4096_from_mp(p, 64, pm);
        sp_4096_from_mp(q, 64, qm);
        sp_4096_from_mp(dp, 64, dpm);

        err = sp_2048_mod_exp_64(tmpa, a, dp, 2048, p, 1);
    }
    if (err == MP_OKAY) {
        sp_4096_from_mp(dq, 64, dqm);
        err = sp_2048_mod_exp_64(tmpb, a, dq, 2048, q, 1);
    }

    if (err == MP_OKAY) {
        c = sp_2048_sub_in_place_64(tmpa, tmpb);
        c += sp_4096_cond_add_64(tmpa, tmpa, p, c);
        sp_4096_cond_add_64(tmpa, tmpa, p, c);

        sp_2048_from_mp(qi, 64, qim);
        sp_2048_mul_64(tmpa, tmpa, qi);
        err = sp_2048_mod_64(tmpa, tmpa, p);
    }

    if (err == MP_OKAY) {
        sp_2048_mul_64(tmpa, q, tmpa);
        XMEMSET(&tmpb[64], 0, sizeof(sp_digit) * 64);
        sp_4096_add_128(r, tmpb, tmpa);

        sp_4096_to_bin(r, out);
        *outLen = 512;
    }

#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (t != NULL) {
        XMEMSET(t, 0, sizeof(sp_digit) * 64 * 11);
        XFREE(t, NULL, DYNAMIC_TYPE_RSA);
    }
#else
    XMEMSET(tmpa, 0, sizeof(tmpa));
    XMEMSET(tmpb, 0, sizeof(tmpb));
    XMEMSET(p,    0, sizeof(p));
    XMEMSET(q,    0, sizeof(q));
    XMEMSET(dp,   0, sizeof(dp));
#endif
#endif /* SP_RSA_PRIVATE_EXP_D || RSA_LOW_MEM */
    return err;
}
#endif /* WOLFSSL_RSA_PUBLIC_ONLY */
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
#if DIGIT_BIT == 32
        XMEMCPY(r->dp, a, sizeof(sp_digit) * 128);
        r->used = 128;
        mp_clamp(r);
#elif DIGIT_BIT < 32
        int i, j = 0, s = 0;

        r->dp[0] = 0;
        for (i = 0; i < 128; i++) {
            r->dp[j] |= (mp_digit)(a[i] << s);
            r->dp[j] &= (1L << DIGIT_BIT) - 1;
            s = DIGIT_BIT - s;
            r->dp[++j] = (mp_digit)(a[i] >> s);
            while (s + DIGIT_BIT <= 32) {
                s += DIGIT_BIT;
                r->dp[j++] &= (1L << DIGIT_BIT) - 1;
                if (s == SP_WORD_SIZE) {
                    r->dp[j] = 0;
                }
                else {
                    r->dp[j] = (mp_digit)(a[i] >> s);
                }
            }
            s = 32 - s;
        }
        r->used = (4096 + DIGIT_BIT - 1) / DIGIT_BIT;
        mp_clamp(r);
#else
        int i, j = 0, s = 0;

        r->dp[0] = 0;
        for (i = 0; i < 128; i++) {
            r->dp[j] |= ((mp_digit)a[i]) << s;
            if (s + 32 >= DIGIT_BIT) {
    #if DIGIT_BIT != 32 && DIGIT_BIT != 64
                r->dp[j] &= (1L << DIGIT_BIT) - 1;
    #endif
                s = DIGIT_BIT - s;
                r->dp[++j] = a[i] >> s;
                s = 32 - s;
            }
            else {
                s += 32;
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
    int err = MP_OKAY;
    sp_digit b[256], e[128], m[128];
    sp_digit* r = b;
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
        sp_4096_from_mp(b, 128, base);
        sp_4096_from_mp(e, 128, exp);
        sp_4096_from_mp(m, 128, mod);

        err = sp_4096_mod_exp_128(r, b, e, expBits, m, 0);
    }

    if (err == MP_OKAY) {
        err = sp_4096_to_mp(r, res);
    }

    XMEMSET(e, 0, sizeof(e));

    return err;
}

#ifdef WOLFSSL_HAVE_SP_DH

#ifdef HAVE_FFDHE_4096
static void sp_4096_lshift_128(sp_digit* r, sp_digit* a, byte n)
{
    __asm__ __volatile__ (
        "mov r6, #31\n\t"
        "sub r6, r6, %[n]\n\t"
        "add       %[a], %[a], #448\n\t"
        "add       %[r], %[r], #448\n\t"
        "ldr r3, [%[a], #60]\n\t"
        "lsr r4, r3, #1\n\t"
        "lsl r3, r3, %[n]\n\t"
        "lsr r4, r4, r6\n\t"
        "ldr       r2, [%[a], #56]\n\t"
        "str       r4, [%[r], #64]\n\t"
        "lsr       r5, r2, #1\n\t"
        "lsl       r2, r2, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r3, r3, r5\n\t"
        "ldr       r4, [%[a], #52]\n\t"
        "str       r3, [%[r], #60]\n\t"
        "lsr       r5, r4, #1\n\t"
        "lsl       r4, r4, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r2, r2, r5\n\t"
        "ldr       r3, [%[a], #48]\n\t"
        "str       r2, [%[r], #56]\n\t"
        "lsr       r5, r3, #1\n\t"
        "lsl       r3, r3, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r4, r4, r5\n\t"
        "ldr       r2, [%[a], #44]\n\t"
        "str       r4, [%[r], #52]\n\t"
        "lsr       r5, r2, #1\n\t"
        "lsl       r2, r2, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r3, r3, r5\n\t"
        "ldr       r4, [%[a], #40]\n\t"
        "str       r3, [%[r], #48]\n\t"
        "lsr       r5, r4, #1\n\t"
        "lsl       r4, r4, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r2, r2, r5\n\t"
        "ldr       r3, [%[a], #36]\n\t"
        "str       r2, [%[r], #44]\n\t"
        "lsr       r5, r3, #1\n\t"
        "lsl       r3, r3, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r4, r4, r5\n\t"
        "ldr       r2, [%[a], #32]\n\t"
        "str       r4, [%[r], #40]\n\t"
        "lsr       r5, r2, #1\n\t"
        "lsl       r2, r2, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r3, r3, r5\n\t"
        "ldr       r4, [%[a], #28]\n\t"
        "str       r3, [%[r], #36]\n\t"
        "lsr       r5, r4, #1\n\t"
        "lsl       r4, r4, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r2, r2, r5\n\t"
        "ldr       r3, [%[a], #24]\n\t"
        "str       r2, [%[r], #32]\n\t"
        "lsr       r5, r3, #1\n\t"
        "lsl       r3, r3, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r4, r4, r5\n\t"
        "ldr       r2, [%[a], #20]\n\t"
        "str       r4, [%[r], #28]\n\t"
        "lsr       r5, r2, #1\n\t"
        "lsl       r2, r2, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r3, r3, r5\n\t"
        "ldr       r4, [%[a], #16]\n\t"
        "str       r3, [%[r], #24]\n\t"
        "lsr       r5, r4, #1\n\t"
        "lsl       r4, r4, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r2, r2, r5\n\t"
        "ldr       r3, [%[a], #12]\n\t"
        "str       r2, [%[r], #20]\n\t"
        "lsr       r5, r3, #1\n\t"
        "lsl       r3, r3, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r4, r4, r5\n\t"
        "ldr       r2, [%[a], #8]\n\t"
        "str       r4, [%[r], #16]\n\t"
        "lsr       r5, r2, #1\n\t"
        "lsl       r2, r2, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r3, r3, r5\n\t"
        "ldr       r4, [%[a], #4]\n\t"
        "str       r3, [%[r], #12]\n\t"
        "lsr       r5, r4, #1\n\t"
        "lsl       r4, r4, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r2, r2, r5\n\t"
        "ldr       r3, [%[a], #0]\n\t"
        "str       r2, [%[r], #8]\n\t"
        "lsr       r5, r3, #1\n\t"
        "lsl       r3, r3, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r4, r4, r5\n\t"
        "sub     %[a], %[a], #64\n\t"
        "sub     %[r], %[r], #64\n\t"
        "ldr       r2, [%[a], #60]\n\t"
        "str       r4, [%[r], #68]\n\t"
        "lsr       r5, r2, #1\n\t"
        "lsl       r2, r2, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r3, r3, r5\n\t"
        "ldr       r4, [%[a], #56]\n\t"
        "str       r3, [%[r], #64]\n\t"
        "lsr       r5, r4, #1\n\t"
        "lsl       r4, r4, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r2, r2, r5\n\t"
        "ldr       r3, [%[a], #52]\n\t"
        "str       r2, [%[r], #60]\n\t"
        "lsr       r5, r3, #1\n\t"
        "lsl       r3, r3, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r4, r4, r5\n\t"
        "ldr       r2, [%[a], #48]\n\t"
        "str       r4, [%[r], #56]\n\t"
        "lsr       r5, r2, #1\n\t"
        "lsl       r2, r2, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r3, r3, r5\n\t"
        "ldr       r4, [%[a], #44]\n\t"
        "str       r3, [%[r], #52]\n\t"
        "lsr       r5, r4, #1\n\t"
        "lsl       r4, r4, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r2, r2, r5\n\t"
        "ldr       r3, [%[a], #40]\n\t"
        "str       r2, [%[r], #48]\n\t"
        "lsr       r5, r3, #1\n\t"
        "lsl       r3, r3, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r4, r4, r5\n\t"
        "ldr       r2, [%[a], #36]\n\t"
        "str       r4, [%[r], #44]\n\t"
        "lsr       r5, r2, #1\n\t"
        "lsl       r2, r2, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r3, r3, r5\n\t"
        "ldr       r4, [%[a], #32]\n\t"
        "str       r3, [%[r], #40]\n\t"
        "lsr       r5, r4, #1\n\t"
        "lsl       r4, r4, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r2, r2, r5\n\t"
        "ldr       r3, [%[a], #28]\n\t"
        "str       r2, [%[r], #36]\n\t"
        "lsr       r5, r3, #1\n\t"
        "lsl       r3, r3, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r4, r4, r5\n\t"
        "ldr       r2, [%[a], #24]\n\t"
        "str       r4, [%[r], #32]\n\t"
        "lsr       r5, r2, #1\n\t"
        "lsl       r2, r2, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r3, r3, r5\n\t"
        "ldr       r4, [%[a], #20]\n\t"
        "str       r3, [%[r], #28]\n\t"
        "lsr       r5, r4, #1\n\t"
        "lsl       r4, r4, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r2, r2, r5\n\t"
        "ldr       r3, [%[a], #16]\n\t"
        "str       r2, [%[r], #24]\n\t"
        "lsr       r5, r3, #1\n\t"
        "lsl       r3, r3, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r4, r4, r5\n\t"
        "ldr       r2, [%[a], #12]\n\t"
        "str       r4, [%[r], #20]\n\t"
        "lsr       r5, r2, #1\n\t"
        "lsl       r2, r2, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r3, r3, r5\n\t"
        "ldr       r4, [%[a], #8]\n\t"
        "str       r3, [%[r], #16]\n\t"
        "lsr       r5, r4, #1\n\t"
        "lsl       r4, r4, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r2, r2, r5\n\t"
        "ldr       r3, [%[a], #4]\n\t"
        "str       r2, [%[r], #12]\n\t"
        "lsr       r5, r3, #1\n\t"
        "lsl       r3, r3, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r4, r4, r5\n\t"
        "ldr       r2, [%[a], #0]\n\t"
        "str       r4, [%[r], #8]\n\t"
        "lsr       r5, r2, #1\n\t"
        "lsl       r2, r2, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r3, r3, r5\n\t"
        "sub     %[a], %[a], #64\n\t"
        "sub     %[r], %[r], #64\n\t"
        "ldr       r4, [%[a], #60]\n\t"
        "str       r3, [%[r], #68]\n\t"
        "lsr       r5, r4, #1\n\t"
        "lsl       r4, r4, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r2, r2, r5\n\t"
        "ldr       r3, [%[a], #56]\n\t"
        "str       r2, [%[r], #64]\n\t"
        "lsr       r5, r3, #1\n\t"
        "lsl       r3, r3, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r4, r4, r5\n\t"
        "ldr       r2, [%[a], #52]\n\t"
        "str       r4, [%[r], #60]\n\t"
        "lsr       r5, r2, #1\n\t"
        "lsl       r2, r2, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r3, r3, r5\n\t"
        "ldr       r4, [%[a], #48]\n\t"
        "str       r3, [%[r], #56]\n\t"
        "lsr       r5, r4, #1\n\t"
        "lsl       r4, r4, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r2, r2, r5\n\t"
        "ldr       r3, [%[a], #44]\n\t"
        "str       r2, [%[r], #52]\n\t"
        "lsr       r5, r3, #1\n\t"
        "lsl       r3, r3, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r4, r4, r5\n\t"
        "ldr       r2, [%[a], #40]\n\t"
        "str       r4, [%[r], #48]\n\t"
        "lsr       r5, r2, #1\n\t"
        "lsl       r2, r2, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r3, r3, r5\n\t"
        "ldr       r4, [%[a], #36]\n\t"
        "str       r3, [%[r], #44]\n\t"
        "lsr       r5, r4, #1\n\t"
        "lsl       r4, r4, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r2, r2, r5\n\t"
        "ldr       r3, [%[a], #32]\n\t"
        "str       r2, [%[r], #40]\n\t"
        "lsr       r5, r3, #1\n\t"
        "lsl       r3, r3, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r4, r4, r5\n\t"
        "ldr       r2, [%[a], #28]\n\t"
        "str       r4, [%[r], #36]\n\t"
        "lsr       r5, r2, #1\n\t"
        "lsl       r2, r2, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r3, r3, r5\n\t"
        "ldr       r4, [%[a], #24]\n\t"
        "str       r3, [%[r], #32]\n\t"
        "lsr       r5, r4, #1\n\t"
        "lsl       r4, r4, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r2, r2, r5\n\t"
        "ldr       r3, [%[a], #20]\n\t"
        "str       r2, [%[r], #28]\n\t"
        "lsr       r5, r3, #1\n\t"
        "lsl       r3, r3, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r4, r4, r5\n\t"
        "ldr       r2, [%[a], #16]\n\t"
        "str       r4, [%[r], #24]\n\t"
        "lsr       r5, r2, #1\n\t"
        "lsl       r2, r2, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r3, r3, r5\n\t"
        "ldr       r4, [%[a], #12]\n\t"
        "str       r3, [%[r], #20]\n\t"
        "lsr       r5, r4, #1\n\t"
        "lsl       r4, r4, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r2, r2, r5\n\t"
        "ldr       r3, [%[a], #8]\n\t"
        "str       r2, [%[r], #16]\n\t"
        "lsr       r5, r3, #1\n\t"
        "lsl       r3, r3, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r4, r4, r5\n\t"
        "ldr       r2, [%[a], #4]\n\t"
        "str       r4, [%[r], #12]\n\t"
        "lsr       r5, r2, #1\n\t"
        "lsl       r2, r2, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r3, r3, r5\n\t"
        "ldr       r4, [%[a], #0]\n\t"
        "str       r3, [%[r], #8]\n\t"
        "lsr       r5, r4, #1\n\t"
        "lsl       r4, r4, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r2, r2, r5\n\t"
        "sub     %[a], %[a], #64\n\t"
        "sub     %[r], %[r], #64\n\t"
        "ldr       r3, [%[a], #60]\n\t"
        "str       r2, [%[r], #68]\n\t"
        "lsr       r5, r3, #1\n\t"
        "lsl       r3, r3, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r4, r4, r5\n\t"
        "ldr       r2, [%[a], #56]\n\t"
        "str       r4, [%[r], #64]\n\t"
        "lsr       r5, r2, #1\n\t"
        "lsl       r2, r2, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r3, r3, r5\n\t"
        "ldr       r4, [%[a], #52]\n\t"
        "str       r3, [%[r], #60]\n\t"
        "lsr       r5, r4, #1\n\t"
        "lsl       r4, r4, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r2, r2, r5\n\t"
        "ldr       r3, [%[a], #48]\n\t"
        "str       r2, [%[r], #56]\n\t"
        "lsr       r5, r3, #1\n\t"
        "lsl       r3, r3, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r4, r4, r5\n\t"
        "ldr       r2, [%[a], #44]\n\t"
        "str       r4, [%[r], #52]\n\t"
        "lsr       r5, r2, #1\n\t"
        "lsl       r2, r2, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r3, r3, r5\n\t"
        "ldr       r4, [%[a], #40]\n\t"
        "str       r3, [%[r], #48]\n\t"
        "lsr       r5, r4, #1\n\t"
        "lsl       r4, r4, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r2, r2, r5\n\t"
        "ldr       r3, [%[a], #36]\n\t"
        "str       r2, [%[r], #44]\n\t"
        "lsr       r5, r3, #1\n\t"
        "lsl       r3, r3, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r4, r4, r5\n\t"
        "ldr       r2, [%[a], #32]\n\t"
        "str       r4, [%[r], #40]\n\t"
        "lsr       r5, r2, #1\n\t"
        "lsl       r2, r2, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r3, r3, r5\n\t"
        "ldr       r4, [%[a], #28]\n\t"
        "str       r3, [%[r], #36]\n\t"
        "lsr       r5, r4, #1\n\t"
        "lsl       r4, r4, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r2, r2, r5\n\t"
        "ldr       r3, [%[a], #24]\n\t"
        "str       r2, [%[r], #32]\n\t"
        "lsr       r5, r3, #1\n\t"
        "lsl       r3, r3, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r4, r4, r5\n\t"
        "ldr       r2, [%[a], #20]\n\t"
        "str       r4, [%[r], #28]\n\t"
        "lsr       r5, r2, #1\n\t"
        "lsl       r2, r2, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r3, r3, r5\n\t"
        "ldr       r4, [%[a], #16]\n\t"
        "str       r3, [%[r], #24]\n\t"
        "lsr       r5, r4, #1\n\t"
        "lsl       r4, r4, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r2, r2, r5\n\t"
        "ldr       r3, [%[a], #12]\n\t"
        "str       r2, [%[r], #20]\n\t"
        "lsr       r5, r3, #1\n\t"
        "lsl       r3, r3, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r4, r4, r5\n\t"
        "ldr       r2, [%[a], #8]\n\t"
        "str       r4, [%[r], #16]\n\t"
        "lsr       r5, r2, #1\n\t"
        "lsl       r2, r2, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r3, r3, r5\n\t"
        "ldr       r4, [%[a], #4]\n\t"
        "str       r3, [%[r], #12]\n\t"
        "lsr       r5, r4, #1\n\t"
        "lsl       r4, r4, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r2, r2, r5\n\t"
        "ldr       r3, [%[a], #0]\n\t"
        "str       r2, [%[r], #8]\n\t"
        "lsr       r5, r3, #1\n\t"
        "lsl       r3, r3, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r4, r4, r5\n\t"
        "sub     %[a], %[a], #64\n\t"
        "sub     %[r], %[r], #64\n\t"
        "ldr       r2, [%[a], #60]\n\t"
        "str       r4, [%[r], #68]\n\t"
        "lsr       r5, r2, #1\n\t"
        "lsl       r2, r2, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r3, r3, r5\n\t"
        "ldr       r4, [%[a], #56]\n\t"
        "str       r3, [%[r], #64]\n\t"
        "lsr       r5, r4, #1\n\t"
        "lsl       r4, r4, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r2, r2, r5\n\t"
        "ldr       r3, [%[a], #52]\n\t"
        "str       r2, [%[r], #60]\n\t"
        "lsr       r5, r3, #1\n\t"
        "lsl       r3, r3, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r4, r4, r5\n\t"
        "ldr       r2, [%[a], #48]\n\t"
        "str       r4, [%[r], #56]\n\t"
        "lsr       r5, r2, #1\n\t"
        "lsl       r2, r2, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r3, r3, r5\n\t"
        "ldr       r4, [%[a], #44]\n\t"
        "str       r3, [%[r], #52]\n\t"
        "lsr       r5, r4, #1\n\t"
        "lsl       r4, r4, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r2, r2, r5\n\t"
        "ldr       r3, [%[a], #40]\n\t"
        "str       r2, [%[r], #48]\n\t"
        "lsr       r5, r3, #1\n\t"
        "lsl       r3, r3, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r4, r4, r5\n\t"
        "ldr       r2, [%[a], #36]\n\t"
        "str       r4, [%[r], #44]\n\t"
        "lsr       r5, r2, #1\n\t"
        "lsl       r2, r2, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r3, r3, r5\n\t"
        "ldr       r4, [%[a], #32]\n\t"
        "str       r3, [%[r], #40]\n\t"
        "lsr       r5, r4, #1\n\t"
        "lsl       r4, r4, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r2, r2, r5\n\t"
        "ldr       r3, [%[a], #28]\n\t"
        "str       r2, [%[r], #36]\n\t"
        "lsr       r5, r3, #1\n\t"
        "lsl       r3, r3, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r4, r4, r5\n\t"
        "ldr       r2, [%[a], #24]\n\t"
        "str       r4, [%[r], #32]\n\t"
        "lsr       r5, r2, #1\n\t"
        "lsl       r2, r2, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r3, r3, r5\n\t"
        "ldr       r4, [%[a], #20]\n\t"
        "str       r3, [%[r], #28]\n\t"
        "lsr       r5, r4, #1\n\t"
        "lsl       r4, r4, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r2, r2, r5\n\t"
        "ldr       r3, [%[a], #16]\n\t"
        "str       r2, [%[r], #24]\n\t"
        "lsr       r5, r3, #1\n\t"
        "lsl       r3, r3, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r4, r4, r5\n\t"
        "ldr       r2, [%[a], #12]\n\t"
        "str       r4, [%[r], #20]\n\t"
        "lsr       r5, r2, #1\n\t"
        "lsl       r2, r2, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r3, r3, r5\n\t"
        "ldr       r4, [%[a], #8]\n\t"
        "str       r3, [%[r], #16]\n\t"
        "lsr       r5, r4, #1\n\t"
        "lsl       r4, r4, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r2, r2, r5\n\t"
        "ldr       r3, [%[a], #4]\n\t"
        "str       r2, [%[r], #12]\n\t"
        "lsr       r5, r3, #1\n\t"
        "lsl       r3, r3, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r4, r4, r5\n\t"
        "ldr       r2, [%[a], #0]\n\t"
        "str       r4, [%[r], #8]\n\t"
        "lsr       r5, r2, #1\n\t"
        "lsl       r2, r2, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r3, r3, r5\n\t"
        "sub     %[a], %[a], #64\n\t"
        "sub     %[r], %[r], #64\n\t"
        "ldr       r4, [%[a], #60]\n\t"
        "str       r3, [%[r], #68]\n\t"
        "lsr       r5, r4, #1\n\t"
        "lsl       r4, r4, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r2, r2, r5\n\t"
        "ldr       r3, [%[a], #56]\n\t"
        "str       r2, [%[r], #64]\n\t"
        "lsr       r5, r3, #1\n\t"
        "lsl       r3, r3, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r4, r4, r5\n\t"
        "ldr       r2, [%[a], #52]\n\t"
        "str       r4, [%[r], #60]\n\t"
        "lsr       r5, r2, #1\n\t"
        "lsl       r2, r2, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r3, r3, r5\n\t"
        "ldr       r4, [%[a], #48]\n\t"
        "str       r3, [%[r], #56]\n\t"
        "lsr       r5, r4, #1\n\t"
        "lsl       r4, r4, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r2, r2, r5\n\t"
        "ldr       r3, [%[a], #44]\n\t"
        "str       r2, [%[r], #52]\n\t"
        "lsr       r5, r3, #1\n\t"
        "lsl       r3, r3, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r4, r4, r5\n\t"
        "ldr       r2, [%[a], #40]\n\t"
        "str       r4, [%[r], #48]\n\t"
        "lsr       r5, r2, #1\n\t"
        "lsl       r2, r2, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r3, r3, r5\n\t"
        "ldr       r4, [%[a], #36]\n\t"
        "str       r3, [%[r], #44]\n\t"
        "lsr       r5, r4, #1\n\t"
        "lsl       r4, r4, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r2, r2, r5\n\t"
        "ldr       r3, [%[a], #32]\n\t"
        "str       r2, [%[r], #40]\n\t"
        "lsr       r5, r3, #1\n\t"
        "lsl       r3, r3, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r4, r4, r5\n\t"
        "ldr       r2, [%[a], #28]\n\t"
        "str       r4, [%[r], #36]\n\t"
        "lsr       r5, r2, #1\n\t"
        "lsl       r2, r2, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r3, r3, r5\n\t"
        "ldr       r4, [%[a], #24]\n\t"
        "str       r3, [%[r], #32]\n\t"
        "lsr       r5, r4, #1\n\t"
        "lsl       r4, r4, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r2, r2, r5\n\t"
        "ldr       r3, [%[a], #20]\n\t"
        "str       r2, [%[r], #28]\n\t"
        "lsr       r5, r3, #1\n\t"
        "lsl       r3, r3, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r4, r4, r5\n\t"
        "ldr       r2, [%[a], #16]\n\t"
        "str       r4, [%[r], #24]\n\t"
        "lsr       r5, r2, #1\n\t"
        "lsl       r2, r2, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r3, r3, r5\n\t"
        "ldr       r4, [%[a], #12]\n\t"
        "str       r3, [%[r], #20]\n\t"
        "lsr       r5, r4, #1\n\t"
        "lsl       r4, r4, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r2, r2, r5\n\t"
        "ldr       r3, [%[a], #8]\n\t"
        "str       r2, [%[r], #16]\n\t"
        "lsr       r5, r3, #1\n\t"
        "lsl       r3, r3, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r4, r4, r5\n\t"
        "ldr       r2, [%[a], #4]\n\t"
        "str       r4, [%[r], #12]\n\t"
        "lsr       r5, r2, #1\n\t"
        "lsl       r2, r2, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r3, r3, r5\n\t"
        "ldr       r4, [%[a], #0]\n\t"
        "str       r3, [%[r], #8]\n\t"
        "lsr       r5, r4, #1\n\t"
        "lsl       r4, r4, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r2, r2, r5\n\t"
        "sub     %[a], %[a], #64\n\t"
        "sub     %[r], %[r], #64\n\t"
        "ldr       r3, [%[a], #60]\n\t"
        "str       r2, [%[r], #68]\n\t"
        "lsr       r5, r3, #1\n\t"
        "lsl       r3, r3, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r4, r4, r5\n\t"
        "ldr       r2, [%[a], #56]\n\t"
        "str       r4, [%[r], #64]\n\t"
        "lsr       r5, r2, #1\n\t"
        "lsl       r2, r2, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r3, r3, r5\n\t"
        "ldr       r4, [%[a], #52]\n\t"
        "str       r3, [%[r], #60]\n\t"
        "lsr       r5, r4, #1\n\t"
        "lsl       r4, r4, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r2, r2, r5\n\t"
        "ldr       r3, [%[a], #48]\n\t"
        "str       r2, [%[r], #56]\n\t"
        "lsr       r5, r3, #1\n\t"
        "lsl       r3, r3, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r4, r4, r5\n\t"
        "ldr       r2, [%[a], #44]\n\t"
        "str       r4, [%[r], #52]\n\t"
        "lsr       r5, r2, #1\n\t"
        "lsl       r2, r2, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r3, r3, r5\n\t"
        "ldr       r4, [%[a], #40]\n\t"
        "str       r3, [%[r], #48]\n\t"
        "lsr       r5, r4, #1\n\t"
        "lsl       r4, r4, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r2, r2, r5\n\t"
        "ldr       r3, [%[a], #36]\n\t"
        "str       r2, [%[r], #44]\n\t"
        "lsr       r5, r3, #1\n\t"
        "lsl       r3, r3, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r4, r4, r5\n\t"
        "ldr       r2, [%[a], #32]\n\t"
        "str       r4, [%[r], #40]\n\t"
        "lsr       r5, r2, #1\n\t"
        "lsl       r2, r2, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r3, r3, r5\n\t"
        "ldr       r4, [%[a], #28]\n\t"
        "str       r3, [%[r], #36]\n\t"
        "lsr       r5, r4, #1\n\t"
        "lsl       r4, r4, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r2, r2, r5\n\t"
        "ldr       r3, [%[a], #24]\n\t"
        "str       r2, [%[r], #32]\n\t"
        "lsr       r5, r3, #1\n\t"
        "lsl       r3, r3, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r4, r4, r5\n\t"
        "ldr       r2, [%[a], #20]\n\t"
        "str       r4, [%[r], #28]\n\t"
        "lsr       r5, r2, #1\n\t"
        "lsl       r2, r2, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r3, r3, r5\n\t"
        "ldr       r4, [%[a], #16]\n\t"
        "str       r3, [%[r], #24]\n\t"
        "lsr       r5, r4, #1\n\t"
        "lsl       r4, r4, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r2, r2, r5\n\t"
        "ldr       r3, [%[a], #12]\n\t"
        "str       r2, [%[r], #20]\n\t"
        "lsr       r5, r3, #1\n\t"
        "lsl       r3, r3, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r4, r4, r5\n\t"
        "ldr       r2, [%[a], #8]\n\t"
        "str       r4, [%[r], #16]\n\t"
        "lsr       r5, r2, #1\n\t"
        "lsl       r2, r2, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r3, r3, r5\n\t"
        "ldr       r4, [%[a], #4]\n\t"
        "str       r3, [%[r], #12]\n\t"
        "lsr       r5, r4, #1\n\t"
        "lsl       r4, r4, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r2, r2, r5\n\t"
        "ldr       r3, [%[a], #0]\n\t"
        "str       r2, [%[r], #8]\n\t"
        "lsr       r5, r3, #1\n\t"
        "lsl       r3, r3, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r4, r4, r5\n\t"
        "sub     %[a], %[a], #64\n\t"
        "sub     %[r], %[r], #64\n\t"
        "ldr       r2, [%[a], #60]\n\t"
        "str       r4, [%[r], #68]\n\t"
        "lsr       r5, r2, #1\n\t"
        "lsl       r2, r2, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r3, r3, r5\n\t"
        "ldr       r4, [%[a], #56]\n\t"
        "str       r3, [%[r], #64]\n\t"
        "lsr       r5, r4, #1\n\t"
        "lsl       r4, r4, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r2, r2, r5\n\t"
        "ldr       r3, [%[a], #52]\n\t"
        "str       r2, [%[r], #60]\n\t"
        "lsr       r5, r3, #1\n\t"
        "lsl       r3, r3, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r4, r4, r5\n\t"
        "ldr       r2, [%[a], #48]\n\t"
        "str       r4, [%[r], #56]\n\t"
        "lsr       r5, r2, #1\n\t"
        "lsl       r2, r2, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r3, r3, r5\n\t"
        "ldr       r4, [%[a], #44]\n\t"
        "str       r3, [%[r], #52]\n\t"
        "lsr       r5, r4, #1\n\t"
        "lsl       r4, r4, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r2, r2, r5\n\t"
        "ldr       r3, [%[a], #40]\n\t"
        "str       r2, [%[r], #48]\n\t"
        "lsr       r5, r3, #1\n\t"
        "lsl       r3, r3, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r4, r4, r5\n\t"
        "ldr       r2, [%[a], #36]\n\t"
        "str       r4, [%[r], #44]\n\t"
        "lsr       r5, r2, #1\n\t"
        "lsl       r2, r2, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r3, r3, r5\n\t"
        "ldr       r4, [%[a], #32]\n\t"
        "str       r3, [%[r], #40]\n\t"
        "lsr       r5, r4, #1\n\t"
        "lsl       r4, r4, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r2, r2, r5\n\t"
        "ldr       r3, [%[a], #28]\n\t"
        "str       r2, [%[r], #36]\n\t"
        "lsr       r5, r3, #1\n\t"
        "lsl       r3, r3, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r4, r4, r5\n\t"
        "ldr       r2, [%[a], #24]\n\t"
        "str       r4, [%[r], #32]\n\t"
        "lsr       r5, r2, #1\n\t"
        "lsl       r2, r2, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r3, r3, r5\n\t"
        "ldr       r4, [%[a], #20]\n\t"
        "str       r3, [%[r], #28]\n\t"
        "lsr       r5, r4, #1\n\t"
        "lsl       r4, r4, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r2, r2, r5\n\t"
        "ldr       r3, [%[a], #16]\n\t"
        "str       r2, [%[r], #24]\n\t"
        "lsr       r5, r3, #1\n\t"
        "lsl       r3, r3, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r4, r4, r5\n\t"
        "ldr       r2, [%[a], #12]\n\t"
        "str       r4, [%[r], #20]\n\t"
        "lsr       r5, r2, #1\n\t"
        "lsl       r2, r2, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r3, r3, r5\n\t"
        "ldr       r4, [%[a], #8]\n\t"
        "str       r3, [%[r], #16]\n\t"
        "lsr       r5, r4, #1\n\t"
        "lsl       r4, r4, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r2, r2, r5\n\t"
        "ldr       r3, [%[a], #4]\n\t"
        "str       r2, [%[r], #12]\n\t"
        "lsr       r5, r3, #1\n\t"
        "lsl       r3, r3, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r4, r4, r5\n\t"
        "ldr       r2, [%[a], #0]\n\t"
        "str       r4, [%[r], #8]\n\t"
        "lsr       r5, r2, #1\n\t"
        "lsl       r2, r2, %[n]\n\t"
        "lsr       r5, r5, r6\n\t"
        "orr       r3, r3, r5\n\t"
        "str r2, [%[r]]\n\t"
        "str r3, [%[r], #4]\n\t"
        :
        : [r] "r" (r), [a] "r" (a), [n] "r" (n)
        : "memory", "r2", "r3", "r4", "r5", "r6"
    );
}

/* Modular exponentiate 2 to the e mod m. (r = 2^e mod m)
 *
 * r     A single precision number that is the result of the operation.
 * e     A single precision number that is the exponent.
 * bits  The number of bits in the exponent.
 * m     A single precision number that is the modulus.
 * returns 0 on success and MEMORY_E on dynamic memory allocation failure.
 */
static int sp_4096_mod_exp_2_128(sp_digit* r, const sp_digit* e, int bits,
        const sp_digit* m)
{
#if defined(WOLFSSL_SMALL_STACK) && !defined(WOLFSSL_SP_NO_MALLOC)
    sp_digit* td;
#else
    sp_digit td[385];
#endif
    sp_digit* norm;
    sp_digit* tmp;
    sp_digit mp = 1;
    sp_digit n, o;
    sp_digit mask;
    int i;
    int c, y;
    int err = MP_OKAY;

#if defined(WOLFSSL_SMALL_STACK) && !defined(WOLFSSL_SP_NO_MALLOC)
    td = (sp_digit*)XMALLOC(sizeof(sp_digit) * 385, NULL,
                            DYNAMIC_TYPE_TMP_BUFFER);
    if (td == NULL) {
        err = MEMORY_E;
    }
#endif

    if (err == MP_OKAY) {
        norm = td;
#if defined(WOLFSSL_SMALL_STACK) && !defined(WOLFSSL_SP_NO_MALLOC)
        tmp = td + 256;
#else
        tmp = &td[256];
#endif

        sp_4096_mont_setup(m, &mp);
        sp_4096_mont_norm_128(norm, m);

        i = (bits - 1) / 32;
        n = e[i--];
        c = bits & 31;
        if (c == 0) {
            c = 32;
        }
        c -= bits % 5;
        if (c == 32) {
            c = 27;
        }
        y = (int)(n >> c);
        n <<= 32 - c;
        sp_4096_lshift_128(r, norm, y);
        for (; i>=0 || c>=5; ) {
            if (c == 0) {
                n = e[i--];
                y = n >> 27;
                n <<= 5;
                c = 27;
            }
            else if (c < 5) {
                y = n >> 27;
                n = e[i--];
                c = 5 - c;
                y |= n >> (32 - c);
                n <<= c;
                c = 32 - c;
            }
            else {
                y = (n >> 27) & 0x1f;
                n <<= 5;
                c -= 5;
            }

            sp_4096_mont_sqr_128(r, r, m, mp);
            sp_4096_mont_sqr_128(r, r, m, mp);
            sp_4096_mont_sqr_128(r, r, m, mp);
            sp_4096_mont_sqr_128(r, r, m, mp);
            sp_4096_mont_sqr_128(r, r, m, mp);

            sp_4096_lshift_128(r, r, y);
            sp_4096_mul_d_128(tmp, norm, r[128]);
            r[128] = 0;
            o = sp_4096_add_128(r, r, tmp);
            sp_4096_cond_sub_128(r, r, m, (sp_digit)0 - o);
        }

        XMEMSET(&r[128], 0, sizeof(sp_digit) * 128U);
        sp_4096_mont_reduce_128(r, m, mp);

        mask = 0 - (sp_4096_cmp_128(r, m) >= 0);
        sp_4096_cond_sub_128(r, r, m, mask);
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
    int err = MP_OKAY;
    sp_digit b[256], e[128], m[128];
    sp_digit* r = b;
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
        sp_4096_from_mp(b, 128, base);
        sp_4096_from_bin(e, 128, exp, expLen);
        sp_4096_from_mp(m, 128, mod);

    #ifdef HAVE_FFDHE_4096
        if (base->used == 1 && base->dp[0] == 2 && m[127] == (sp_digit)-1)
            err = sp_4096_mod_exp_2_128(r, e, expLen * 8, m);
        else
    #endif
            err = sp_4096_mod_exp_128(r, b, e, expLen * 8, m, 0);

    }

    if (err == MP_OKAY) {
        sp_4096_to_bin(r, out);
        *outLen = 512;
        for (i=0; i<512 && out[i] == 0; i++) {
        }
        *outLen -= i;
        XMEMMOVE(out, out + i, *outLen);

    }

    XMEMSET(e, 0, sizeof(e));

    return err;
}
#endif /* WOLFSSL_HAVE_SP_DH */

#endif /* WOLFSSL_HAVE_SP_DH || (WOLFSSL_HAVE_SP_RSA && !WOLFSSL_RSA_PUBLIC_ONLY) */

#endif /* WOLFSSL_SP_4096 */

#endif /* WOLFSSL_HAVE_SP_RSA || WOLFSSL_HAVE_SP_DH */
#ifdef WOLFSSL_HAVE_SP_ECC
#ifndef WOLFSSL_SP_NO_256

/* Point structure to use. */
typedef struct sp_point_256 {
    sp_digit x[2 * 8];
    sp_digit y[2 * 8];
    sp_digit z[2 * 8];
    int infinity;
} sp_point_256;

/* The modulus (prime) of the curve P256. */
static const sp_digit p256_mod[8] = {
    0xffffffff,0xffffffff,0xffffffff,0x00000000,0x00000000,0x00000000,
    0x00000001,0xffffffff
};
/* The Montogmery normalizer for modulus of the curve P256. */
static const sp_digit p256_norm_mod[8] = {
    0x00000001,0x00000000,0x00000000,0xffffffff,0xffffffff,0xffffffff,
    0xfffffffe,0x00000000
};
/* The Montogmery multiplier for modulus of the curve P256. */
static const sp_digit p256_mp_mod = 0x00000001;
#if defined(WOLFSSL_VALIDATE_ECC_KEYGEN) || defined(HAVE_ECC_SIGN) || \
                                            defined(HAVE_ECC_VERIFY)
/* The order of the curve P256. */
static const sp_digit p256_order[8] = {
    0xfc632551,0xf3b9cac2,0xa7179e84,0xbce6faad,0xffffffff,0xffffffff,
    0x00000000,0xffffffff
};
#endif
/* The order of the curve P256 minus 2. */
static const sp_digit p256_order2[8] = {
    0xfc63254f,0xf3b9cac2,0xa7179e84,0xbce6faad,0xffffffff,0xffffffff,
    0x00000000,0xffffffff
};
#if defined(HAVE_ECC_SIGN) || defined(HAVE_ECC_VERIFY)
/* The Montogmery normalizer for order of the curve P256. */
static const sp_digit p256_norm_order[8] = {
    0x039cdaaf,0x0c46353d,0x58e8617b,0x43190552,0x00000000,0x00000000,
    0xffffffff,0x00000000
};
#endif
#if defined(HAVE_ECC_SIGN) || defined(HAVE_ECC_VERIFY)
/* The Montogmery multiplier for order of the curve P256. */
static const sp_digit p256_mp_order = 0xee00bc4f;
#endif
/* The base point of curve P256. */
static const sp_point_256 p256_base = {
    /* X ordinate */
    {
        0xd898c296,0xf4a13945,0x2deb33a0,0x77037d81,0x63a440f2,0xf8bce6e5,
        0xe12c4247,0x6b17d1f2,
        0L, 0L, 0L, 0L, 0L, 0L, 0L, 0L
    },
    /* Y ordinate */
    {
        0x37bf51f5,0xcbb64068,0x6b315ece,0x2bce3357,0x7c0f9e16,0x8ee7eb4a,
        0xfe1a7f9b,0x4fe342e2,
        0L, 0L, 0L, 0L, 0L, 0L, 0L, 0L
    },
    /* Z ordinate */
    {
        0x00000001,0x00000000,0x00000000,0x00000000,0x00000000,0x00000000,
        0x00000000,0x00000000,
        0L, 0L, 0L, 0L, 0L, 0L, 0L, 0L
    },
    /* infinity */
    0
};
#if defined(HAVE_ECC_CHECK_KEY) || defined(HAVE_COMP_KEY)
static const sp_digit p256_b[8] = {
    0x27d2604b,0x3bce3c3e,0xcc53b0f6,0x651d06b0,0x769886bc,0xb3ebbd55,
    0xaa3a93e7,0x5ac635d8
};
#endif

static int sp_256_point_new_ex_8(void* heap, sp_point_256* sp, sp_point_256** p)
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
#define sp_256_point_new_8(heap, sp, p) sp_256_point_new_ex_8((heap), NULL, &(p))
#else
/* Set pointer to data and return no error. */
#define sp_256_point_new_8(heap, sp, p) sp_256_point_new_ex_8((heap), &(sp), &(p))
#endif


static void sp_256_point_free_8(sp_point_256* p, int clear, void* heap)
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
 */
static int sp_256_mod_mul_norm_8(sp_digit* r, const sp_digit* a, const sp_digit* m)
{
   (void)m;

    __asm__ __volatile__ (
        "sub   sp, sp, #24\n\t"
        "ldr r2, [%[a], #0]\n\t"
        "ldr r3, [%[a], #4]\n\t"
        "ldr r4, [%[a], #8]\n\t"
        "ldr r5, [%[a], #12]\n\t"
        "ldr r6, [%[a], #16]\n\t"
        "ldr r8, [%[a], #20]\n\t"
        "ldr r9, [%[a], #24]\n\t"
        "ldr r10, [%[a], #28]\n\t"
        /* Clear overflow and underflow */
        "mov   r14, #0\n\t"
        "mov   r12, #0\n\t"
        /* t[0] =  1  1  0 -1 -1 -1 -1  0 */
        "adds  r11, r2, r3\n\t"
        "adc   r14, r14, #0\n\t"
        "subs    r11, r11, r5\n\t"
        "sbc     r12, r12, #0\n\t"
        "subs    r11, r11, r6\n\t"
        "sbc     r12, r12, #0\n\t"
        "subs    r11, r11, r8\n\t"
        "sbc     r12, r12, #0\n\t"
        "subs    r11, r11, r9\n\t"
        "sbc     r12, r12, #0\n\t"
        /* Store t[0] */
        "str       r11, [sp, #0]\n\t"
        "neg       r12, r12\n\t"
        "mov       r11, #0\n\t"
        /* t[1] =  0  1  1  0 -1 -1 -1 -1 */
        "adds  r14, r14, r3\n\t"
        "adc   r11, r11, #0\n\t"
        "adds  r14, r14, r4\n\t"
        "adc   r11, r11, #0\n\t"
        "subs      r14, r14, r12\n\t"
        "mov       r12, #0\n\t"
        "sbc       r12, r12, #0\n\t"
        "subs    r14, r14, r6\n\t"
        "sbc     r12, r12, #0\n\t"
        "subs    r14, r14, r8\n\t"
        "sbc     r12, r12, #0\n\t"
        "subs    r14, r14, r9\n\t"
        "sbc     r12, r12, #0\n\t"
        "subs    r14, r14, r10\n\t"
        "sbc     r12, r12, #0\n\t"
        /* Store t[1] */
        "str       r14, [sp, #4]\n\t"
        "neg       r12, r12\n\t"
        "mov       r14, #0\n\t"
        /* t[2] =  0  0  1  1  0 -1 -1 -1 */
        "adds  r11, r11, r4\n\t"
        "adc   r14, r14, #0\n\t"
        "adds  r11, r11, r5\n\t"
        "adc   r14, r14, #0\n\t"
        "subs      r11, r11, r12\n\t"
        "mov       r12, #0\n\t"
        "sbc       r12, r12, #0\n\t"
        "subs    r11, r11, r8\n\t"
        "sbc     r12, r12, #0\n\t"
        "subs    r11, r11, r9\n\t"
        "sbc     r12, r12, #0\n\t"
        "subs    r11, r11, r10\n\t"
        "sbc     r12, r12, #0\n\t"
        /* Store t[2] */
        "str       r11, [sp, #8]\n\t"
        "neg       r12, r12\n\t"
        "mov       r11, #0\n\t"
        /* t[3] = -1 -1  0  2  2  1  0 -1 */
        "adds  r14, r14, r5\n\t"
        "adc   r11, r11, #0\n\t"
        "adds  r14, r14, r5\n\t"
        "adc   r11, r11, #0\n\t"
        "adds  r14, r14, r6\n\t"
        "adc   r11, r11, #0\n\t"
        "adds  r14, r14, r6\n\t"
        "adc   r11, r11, #0\n\t"
        "adds  r14, r14, r8\n\t"
        "adc   r11, r11, #0\n\t"
        "subs      r14, r14, r12\n\t"
        "mov       r12, #0\n\t"
        "sbc       r12, r12, #0\n\t"
        "subs    r14, r14, r2\n\t"
        "sbc     r12, r12, #0\n\t"
        "subs    r14, r14, r3\n\t"
        "sbc     r12, r12, #0\n\t"
        "subs    r14, r14, r10\n\t"
        "sbc     r12, r12, #0\n\t"
        /* Store t[3] */
        "str       r14, [sp, #12]\n\t"
        "neg       r12, r12\n\t"
        "mov       r14, #0\n\t"
        /* t[4] =  0 -1 -1  0  2  2  1  0 */
        "adds  r11, r11, r6\n\t"
        "adc   r14, r14, #0\n\t"
        "adds  r11, r11, r6\n\t"
        "adc   r14, r14, #0\n\t"
        "adds  r11, r11, r8\n\t"
        "adc   r14, r14, #0\n\t"
        "adds  r11, r11, r8\n\t"
        "adc   r14, r14, #0\n\t"
        "adds  r11, r11, r9\n\t"
        "adc   r14, r14, #0\n\t"
        "subs      r11, r11, r12\n\t"
        "mov       r12, #0\n\t"
        "sbc       r12, r12, #0\n\t"
        "subs    r11, r11, r3\n\t"
        "sbc     r12, r12, #0\n\t"
        "subs    r11, r11, r4\n\t"
        "sbc     r12, r12, #0\n\t"
        /* Store t[4] */
        "str       r11, [sp, #16]\n\t"
        "neg       r12, r12\n\t"
        "mov       r11, #0\n\t"
        /* t[5] =  0  0 -1 -1  0  2  2  1 */
        "adds  r14, r14, r8\n\t"
        "adc   r11, r11, #0\n\t"
        "adds  r14, r14, r8\n\t"
        "adc   r11, r11, #0\n\t"
        "adds  r14, r14, r9\n\t"
        "adc   r11, r11, #0\n\t"
        "adds  r14, r14, r9\n\t"
        "adc   r11, r11, #0\n\t"
        "adds  r14, r14, r10\n\t"
        "adc   r11, r11, #0\n\t"
        "subs      r14, r14, r12\n\t"
        "mov       r12, #0\n\t"
        "sbc       r12, r12, #0\n\t"
        "subs    r14, r14, r4\n\t"
        "sbc     r12, r12, #0\n\t"
        "subs    r14, r14, r5\n\t"
        "sbc     r12, r12, #0\n\t"
        /* Store t[5] */
        "str       r14, [sp, #20]\n\t"
        "neg       r12, r12\n\t"
        "mov       r14, #0\n\t"
        /* t[6] = -1 -1  0  0  0  1  3  2 */
        "adds  r11, r11, r8\n\t"
        "adc   r14, r14, #0\n\t"
        "adds  r11, r11, r9\n\t"
        "adc   r14, r14, #0\n\t"
        "adds  r11, r11, r9\n\t"
        "adc   r14, r14, #0\n\t"
        "adds  r11, r11, r9\n\t"
        "adc   r14, r14, #0\n\t"
        "adds  r11, r11, r10\n\t"
        "adc   r14, r14, #0\n\t"
        "adds  r11, r11, r10\n\t"
        "adc   r14, r14, #0\n\t"
        "subs      r11, r11, r12\n\t"
        "mov       r12, #0\n\t"
        "sbc       r12, r12, #0\n\t"
        "subs    r11, r11, r2\n\t"
        "sbc     r12, r12, #0\n\t"
        "subs    r11, r11, r3\n\t"
        "sbc     r12, r12, #0\n\t"
        /* Store t[6] */
        "mov       r9, r11\n\t"
        "neg       r12, r12\n\t"
        "mov       r11, #0\n\t"
        /* t[7] =  1  0 -1 -1 -1 -1  0  3 */
        "adds  r14, r14, r2\n\t"
        "adc   r11, r11, #0\n\t"
        "adds  r14, r14, r10\n\t"
        "adc   r11, r11, #0\n\t"
        "adds  r14, r14, r10\n\t"
        "adc   r11, r11, #0\n\t"
        "adds  r14, r14, r10\n\t"
        "adc   r11, r11, #0\n\t"
        "subs      r14, r14, r12\n\t"
        "mov       r12, #0\n\t"
        "sbc       r12, r12, #0\n\t"
        "subs    r14, r14, r4\n\t"
        "sbc     r12, r12, #0\n\t"
        "subs    r14, r14, r5\n\t"
        "sbc     r12, r12, #0\n\t"
        "subs    r14, r14, r6\n\t"
        "sbc     r12, r12, #0\n\t"
        "subs    r14, r14, r8\n\t"
        "sbc     r12, r12, #0\n\t"
        /* Store t[7] */
        /* Load intermediate */
        "ldr r2, [sp, #0]\n\t"
        "ldr r3, [sp, #4]\n\t"
        "ldr r4, [sp, #8]\n\t"
        "ldr r5, [sp, #12]\n\t"
        "ldr r6, [sp, #16]\n\t"
        "ldr r8, [sp, #20]\n\t"
        "neg   r12, r12\n\t"
        /* Add overflow */
        /* Subtract underflow - add neg underflow */
        "adds  r2, r2, r11\n\t"
        "adcs  r3, r3, #0\n\t"
        "adcs  r4, r4, #0\n\t"
        "adds  r5, r5, r12\n\t"
        "adcs  r6, r6, #0\n\t"
        "adcs  r8, r8, #0\n\t"
        "adcs  r9, r9, r12\n\t"
        "adc   r14, r14, r11\n\t"
        /* Subtract overflow */
        /* Add underflow - subtract neg underflow */
        "subs  r2, r2, r12\n\t"
        "sbcs  r3, r3, #0\n\t"
        "sbcs  r4, r4, #0\n\t"
        "subs  r5, r5, r11\n\t"
        "sbcs  r6, r6, #0\n\t"
        "sbcs  r8, r8, #0\n\t"
        "sbcs  r9, r9, r11\n\t"
        "sbc   r14, r14, r12\n\t"
        /* Store result */
        "str r2, [%[r], #0]\n\t"
        "str r3, [%[r], #4]\n\t"
        "str r4, [%[r], #8]\n\t"
        "str r5, [%[r], #12]\n\t"
        "str r6, [%[r], #16]\n\t"
        "str r8, [%[r], #20]\n\t"
        "str r9, [%[r], #24]\n\t"
        "str r14, [%[r], #28]\n\t"
        "add   sp, sp, #24\n\t"
        :
        : [r] "r" (r), [a] "r" (a)
        : "r2", "r3", "r4", "r5", "r6", "r8", "r9", "r10", "r11", "r14", "r12"
    );

    return MP_OKAY;
}

/* Convert an mp_int to an array of sp_digit.
 *
 * r  A single precision integer.
 * size  Maximum number of bytes to convert
 * a  A multi-precision integer.
 */
static void sp_256_from_mp(sp_digit* r, int size, const mp_int* a)
{
#if DIGIT_BIT == 32
    int j;

    XMEMCPY(r, a->dp, sizeof(sp_digit) * a->used);

    for (j = a->used; j < size; j++) {
        r[j] = 0;
    }
#elif DIGIT_BIT > 32
    int i, j = 0;
    word32 s = 0;

    r[0] = 0;
    for (i = 0; i < a->used && j < size; i++) {
        r[j] |= ((sp_digit)a->dp[i] << s);
        r[j] &= 0xffffffff;
        s = 32U - s;
        if (j + 1 >= size) {
            break;
        }
        /* lint allow cast of mismatch word32 and mp_digit */
        r[++j] = (sp_digit)(a->dp[i] >> s); /*lint !e9033*/
        while ((s + 32U) <= (word32)DIGIT_BIT) {
            s += 32U;
            r[j] &= 0xffffffff;
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
        if (s + DIGIT_BIT >= 32) {
            r[j] &= 0xffffffff;
            if (j + 1 >= size) {
                break;
            }
            s = 32 - s;
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
static void sp_256_point_from_ecc_point_8(sp_point_256* p, const ecc_point* pm)
{
    XMEMSET(p->x, 0, sizeof(p->x));
    XMEMSET(p->y, 0, sizeof(p->y));
    XMEMSET(p->z, 0, sizeof(p->z));
    sp_256_from_mp(p->x, 8, pm->x);
    sp_256_from_mp(p->y, 8, pm->y);
    sp_256_from_mp(p->z, 8, pm->z);
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
#if DIGIT_BIT == 32
        XMEMCPY(r->dp, a, sizeof(sp_digit) * 8);
        r->used = 8;
        mp_clamp(r);
#elif DIGIT_BIT < 32
        int i, j = 0, s = 0;

        r->dp[0] = 0;
        for (i = 0; i < 8; i++) {
            r->dp[j] |= (mp_digit)(a[i] << s);
            r->dp[j] &= (1L << DIGIT_BIT) - 1;
            s = DIGIT_BIT - s;
            r->dp[++j] = (mp_digit)(a[i] >> s);
            while (s + DIGIT_BIT <= 32) {
                s += DIGIT_BIT;
                r->dp[j++] &= (1L << DIGIT_BIT) - 1;
                if (s == SP_WORD_SIZE) {
                    r->dp[j] = 0;
                }
                else {
                    r->dp[j] = (mp_digit)(a[i] >> s);
                }
            }
            s = 32 - s;
        }
        r->used = (256 + DIGIT_BIT - 1) / DIGIT_BIT;
        mp_clamp(r);
#else
        int i, j = 0, s = 0;

        r->dp[0] = 0;
        for (i = 0; i < 8; i++) {
            r->dp[j] |= ((mp_digit)a[i]) << s;
            if (s + 32 >= DIGIT_BIT) {
    #if DIGIT_BIT != 32 && DIGIT_BIT != 64
                r->dp[j] &= (1L << DIGIT_BIT) - 1;
    #endif
                s = DIGIT_BIT - s;
                r->dp[++j] = a[i] >> s;
                s = 32 - s;
            }
            else {
                s += 32;
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
static int sp_256_point_to_ecc_point_8(const sp_point_256* p, ecc_point* pm)
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

/* Multiply two Montogmery form numbers mod the modulus (prime).
 * (r = a * b mod m)
 *
 * r   Result of multiplication.
 * a   First number to multiply in Montogmery form.
 * b   Second number to multiply in Montogmery form.
 * m   Modulus (prime).
 * mp  Montogmery mulitplier.
 */
SP_NOINLINE static void sp_256_mont_mul_8(sp_digit* r, const sp_digit* a, const sp_digit* b,
        const sp_digit* m, sp_digit mp)
{
    (void)mp;
    (void)m;

    __asm__ __volatile__ (
        "sub   sp, sp, #68\n\t"
        "mov   r5, #0\n\t"
        /*  A[0] * B[0] */
        "ldr	r6, [%[a], #0]\n\t"
        "ldr	r8, [%[b], #0]\n\t"
        "umull	r9, r10, r6, r8\n\t"
        "str r9, [sp, #0]\n\t"
        /*  A[0] * B[1] */
        "ldr	r6, [%[a], #0]\n\t"
        "ldr	r8, [%[b], #4]\n\t"
        "umull	r3, r4, r6, r8\n\t"
        "adds	r10, r3, r10\n\t"
        "adc	r11, r4, #0\n\t"
        /*  A[1] * B[0] */
        "ldr	r6, [%[a], #4]\n\t"
        "ldr	r8, [%[b], #0]\n\t"
        "umull	r3, r4, r6, r8\n\t"
        "adds	r10, r3, r10\n\t"
        "adcs	r11, r4, r11\n\t"
        "adc	r14, r5, #0\n\t"
        "str r10, [sp, #4]\n\t"
        /*  A[0] * B[2] */
        "ldr	r6, [%[a], #0]\n\t"
        "ldr	r8, [%[b], #8]\n\t"
        "umull	r3, r4, r6, r8\n\t"
        "adds	r11, r3, r11\n\t"
        "adc	r14, r4, r14\n\t"
        /*  A[1] * B[1] */
        "ldr	r6, [%[a], #4]\n\t"
        "ldr	r8, [%[b], #4]\n\t"
        "umull	r3, r4, r6, r8\n\t"
        "adds	r11, r3, r11\n\t"
        "adcs	r14, r4, r14\n\t"
        "adc	r9, r5, #0\n\t"
        /*  A[2] * B[0] */
        "ldr	r6, [%[a], #8]\n\t"
        "ldr	r8, [%[b], #0]\n\t"
        "umull	r3, r4, r6, r8\n\t"
        "adds	r11, r3, r11\n\t"
        "adcs	r14, r4, r14\n\t"
        "adc	r9, r5, r9\n\t"
        "str r11, [sp, #8]\n\t"
        /*  A[0] * B[3] */
        "ldr	r6, [%[a], #0]\n\t"
        "ldr	r8, [%[b], #12]\n\t"
        "umull	r3, r4, r6, r8\n\t"
        "adds	r14, r3, r14\n\t"
        "adcs	r9, r4, r9\n\t"
        "adc	r10, r5, #0\n\t"
        /*  A[1] * B[2] */
        "ldr	r6, [%[a], #4]\n\t"
        "ldr	r8, [%[b], #8]\n\t"
        "umull	r3, r4, r6, r8\n\t"
        "adds	r14, r3, r14\n\t"
        "adcs	r9, r4, r9\n\t"
        "adc	r10, r5, r10\n\t"
        /*  A[2] * B[1] */
        "ldr	r6, [%[a], #8]\n\t"
        "ldr	r8, [%[b], #4]\n\t"
        "umull	r3, r4, r6, r8\n\t"
        "adds	r14, r3, r14\n\t"
        "adcs	r9, r4, r9\n\t"
        "adc	r10, r5, r10\n\t"
        /*  A[3] * B[0] */
        "ldr	r6, [%[a], #12]\n\t"
        "ldr	r8, [%[b], #0]\n\t"
        "umull	r3, r4, r6, r8\n\t"
        "adds	r14, r3, r14\n\t"
        "adcs	r9, r4, r9\n\t"
        "adc	r10, r5, r10\n\t"
        "str r14, [sp, #12]\n\t"
        /*  A[0] * B[4] */
        "ldr	r6, [%[a], #0]\n\t"
        "ldr	r8, [%[b], #16]\n\t"
        "umull	r3, r4, r6, r8\n\t"
        "adds	r9, r3, r9\n\t"
        "adcs	r10, r4, r10\n\t"
        "adc	r11, r5, #0\n\t"
        /*  A[1] * B[3] */
        "ldr	r6, [%[a], #4]\n\t"
        "ldr	r8, [%[b], #12]\n\t"
        "umull	r3, r4, r6, r8\n\t"
        "adds	r9, r3, r9\n\t"
        "adcs	r10, r4, r10\n\t"
        "adc	r11, r5, r11\n\t"
        /*  A[2] * B[2] */
        "ldr	r6, [%[a], #8]\n\t"
        "ldr	r8, [%[b], #8]\n\t"
        "umull	r3, r4, r6, r8\n\t"
        "adds	r9, r3, r9\n\t"
        "adcs	r10, r4, r10\n\t"
        "adc	r11, r5, r11\n\t"
        /*  A[3] * B[1] */
        "ldr	r6, [%[a], #12]\n\t"
        "ldr	r8, [%[b], #4]\n\t"
        "umull	r3, r4, r6, r8\n\t"
        "adds	r9, r3, r9\n\t"
        "adcs	r10, r4, r10\n\t"
        "adc	r11, r5, r11\n\t"
        /*  A[4] * B[0] */
        "ldr	r6, [%[a], #16]\n\t"
        "ldr	r8, [%[b], #0]\n\t"
        "umull	r3, r4, r6, r8\n\t"
        "adds	r9, r3, r9\n\t"
        "adcs	r10, r4, r10\n\t"
        "adc	r11, r5, r11\n\t"
        "str r9, [sp, #16]\n\t"
        /*  A[0] * B[5] */
        "ldr	r6, [%[a], #0]\n\t"
        "ldr	r8, [%[b], #20]\n\t"
        "umull	r3, r4, r6, r8\n\t"
        "adds	r10, r3, r10\n\t"
        "adcs	r11, r4, r11\n\t"
        "adc	r14, r5, #0\n\t"
        /*  A[1] * B[4] */
        "ldr	r6, [%[a], #4]\n\t"
        "ldr	r8, [%[b], #16]\n\t"
        "umull	r3, r4, r6, r8\n\t"
        "adds	r10, r3, r10\n\t"
        "adcs	r11, r4, r11\n\t"
        "adc	r14, r5, r14\n\t"
        /*  A[2] * B[3] */
        "ldr	r6, [%[a], #8]\n\t"
        "ldr	r8, [%[b], #12]\n\t"
        "umull	r3, r4, r6, r8\n\t"
        "adds	r10, r3, r10\n\t"
        "adcs	r11, r4, r11\n\t"
        "adc	r14, r5, r14\n\t"
        /*  A[3] * B[2] */
        "ldr	r6, [%[a], #12]\n\t"
        "ldr	r8, [%[b], #8]\n\t"
        "umull	r3, r4, r6, r8\n\t"
        "adds	r10, r3, r10\n\t"
        "adcs	r11, r4, r11\n\t"
        "adc	r14, r5, r14\n\t"
        /*  A[4] * B[1] */
        "ldr	r6, [%[a], #16]\n\t"
        "ldr	r8, [%[b], #4]\n\t"
        "umull	r3, r4, r6, r8\n\t"
        "adds	r10, r3, r10\n\t"
        "adcs	r11, r4, r11\n\t"
        "adc	r14, r5, r14\n\t"
        /*  A[5] * B[0] */
        "ldr	r6, [%[a], #20]\n\t"
        "ldr	r8, [%[b], #0]\n\t"
        "umull	r3, r4, r6, r8\n\t"
        "adds	r10, r3, r10\n\t"
        "adcs	r11, r4, r11\n\t"
        "adc	r14, r5, r14\n\t"
        "str r10, [sp, #20]\n\t"
        /*  A[0] * B[6] */
        "ldr	r6, [%[a], #0]\n\t"
        "ldr	r8, [%[b], #24]\n\t"
        "umull	r3, r4, r6, r8\n\t"
        "adds	r11, r3, r11\n\t"
        "adcs	r14, r4, r14\n\t"
        "adc	r9, r5, #0\n\t"
        /*  A[1] * B[5] */
        "ldr	r6, [%[a], #4]\n\t"
        "ldr	r8, [%[b], #20]\n\t"
        "umull	r3, r4, r6, r8\n\t"
        "adds	r11, r3, r11\n\t"
        "adcs	r14, r4, r14\n\t"
        "adc	r9, r5, r9\n\t"
        /*  A[2] * B[4] */
        "ldr	r6, [%[a], #8]\n\t"
        "ldr	r8, [%[b], #16]\n\t"
        "umull	r3, r4, r6, r8\n\t"
        "adds	r11, r3, r11\n\t"
        "adcs	r14, r4, r14\n\t"
        "adc	r9, r5, r9\n\t"
        /*  A[3] * B[3] */
        "ldr	r6, [%[a], #12]\n\t"
        "ldr	r8, [%[b], #12]\n\t"
        "umull	r3, r4, r6, r8\n\t"
        "adds	r11, r3, r11\n\t"
        "adcs	r14, r4, r14\n\t"
        "adc	r9, r5, r9\n\t"
        /*  A[4] * B[2] */
        "ldr	r6, [%[a], #16]\n\t"
        "ldr	r8, [%[b], #8]\n\t"
        "umull	r3, r4, r6, r8\n\t"
        "adds	r11, r3, r11\n\t"
        "adcs	r14, r4, r14\n\t"
        "adc	r9, r5, r9\n\t"
        /*  A[5] * B[1] */
        "ldr	r6, [%[a], #20]\n\t"
        "ldr	r8, [%[b], #4]\n\t"
        "umull	r3, r4, r6, r8\n\t"
        "adds	r11, r3, r11\n\t"
        "adcs	r14, r4, r14\n\t"
        "adc	r9, r5, r9\n\t"
        /*  A[6] * B[0] */
        "ldr	r6, [%[a], #24]\n\t"
        "ldr	r8, [%[b], #0]\n\t"
        "umull	r3, r4, r6, r8\n\t"
        "adds	r11, r3, r11\n\t"
        "adcs	r14, r4, r14\n\t"
        "adc	r9, r5, r9\n\t"
        "str r11, [sp, #24]\n\t"
        /*  A[0] * B[7] */
        "ldr	r6, [%[a], #0]\n\t"
        "ldr	r8, [%[b], #28]\n\t"
        "umull	r3, r4, r6, r8\n\t"
        "adds	r14, r3, r14\n\t"
        "adcs	r9, r4, r9\n\t"
        "adc	r10, r5, #0\n\t"
        /*  A[1] * B[6] */
        "ldr	r6, [%[a], #4]\n\t"
        "ldr	r8, [%[b], #24]\n\t"
        "umull	r3, r4, r6, r8\n\t"
        "adds	r14, r3, r14\n\t"
        "adcs	r9, r4, r9\n\t"
        "adc	r10, r5, r10\n\t"
        /*  A[2] * B[5] */
        "ldr	r6, [%[a], #8]\n\t"
        "ldr	r8, [%[b], #20]\n\t"
        "umull	r3, r4, r6, r8\n\t"
        "adds	r14, r3, r14\n\t"
        "adcs	r9, r4, r9\n\t"
        "adc	r10, r5, r10\n\t"
        /*  A[3] * B[4] */
        "ldr	r6, [%[a], #12]\n\t"
        "ldr	r8, [%[b], #16]\n\t"
        "umull	r3, r4, r6, r8\n\t"
        "adds	r14, r3, r14\n\t"
        "adcs	r9, r4, r9\n\t"
        "adc	r10, r5, r10\n\t"
        /*  A[4] * B[3] */
        "ldr	r6, [%[a], #16]\n\t"
        "ldr	r8, [%[b], #12]\n\t"
        "umull	r3, r4, r6, r8\n\t"
        "adds	r14, r3, r14\n\t"
        "adcs	r9, r4, r9\n\t"
        "adc	r10, r5, r10\n\t"
        /*  A[5] * B[2] */
        "ldr	r6, [%[a], #20]\n\t"
        "ldr	r8, [%[b], #8]\n\t"
        "umull	r3, r4, r6, r8\n\t"
        "adds	r14, r3, r14\n\t"
        "adcs	r9, r4, r9\n\t"
        "adc	r10, r5, r10\n\t"
        /*  A[6] * B[1] */
        "ldr	r6, [%[a], #24]\n\t"
        "ldr	r8, [%[b], #4]\n\t"
        "umull	r3, r4, r6, r8\n\t"
        "adds	r14, r3, r14\n\t"
        "adcs	r9, r4, r9\n\t"
        "adc	r10, r5, r10\n\t"
        /*  A[7] * B[0] */
        "ldr	r6, [%[a], #28]\n\t"
        "ldr	r8, [%[b], #0]\n\t"
        "umull	r3, r4, r6, r8\n\t"
        "adds	r14, r3, r14\n\t"
        "adcs	r9, r4, r9\n\t"
        "adc	r10, r5, r10\n\t"
        "str r14, [sp, #28]\n\t"
        /*  A[1] * B[7] */
        "ldr	r6, [%[a], #4]\n\t"
        "ldr	r8, [%[b], #28]\n\t"
        "umull	r3, r4, r6, r8\n\t"
        "adds	r9, r3, r9\n\t"
        "adcs	r10, r4, r10\n\t"
        "adc	r11, r5, #0\n\t"
        /*  A[2] * B[6] */
        "ldr	r6, [%[a], #8]\n\t"
        "ldr	r8, [%[b], #24]\n\t"
        "umull	r3, r4, r6, r8\n\t"
        "adds	r9, r3, r9\n\t"
        "adcs	r10, r4, r10\n\t"
        "adc	r11, r5, r11\n\t"
        /*  A[3] * B[5] */
        "ldr	r6, [%[a], #12]\n\t"
        "ldr	r8, [%[b], #20]\n\t"
        "umull	r3, r4, r6, r8\n\t"
        "adds	r9, r3, r9\n\t"
        "adcs	r10, r4, r10\n\t"
        "adc	r11, r5, r11\n\t"
        /*  A[4] * B[4] */
        "ldr	r6, [%[a], #16]\n\t"
        "ldr	r8, [%[b], #16]\n\t"
        "umull	r3, r4, r6, r8\n\t"
        "adds	r9, r3, r9\n\t"
        "adcs	r10, r4, r10\n\t"
        "adc	r11, r5, r11\n\t"
        /*  A[5] * B[3] */
        "ldr	r6, [%[a], #20]\n\t"
        "ldr	r8, [%[b], #12]\n\t"
        "umull	r3, r4, r6, r8\n\t"
        "adds	r9, r3, r9\n\t"
        "adcs	r10, r4, r10\n\t"
        "adc	r11, r5, r11\n\t"
        /*  A[6] * B[2] */
        "ldr	r6, [%[a], #24]\n\t"
        "ldr	r8, [%[b], #8]\n\t"
        "umull	r3, r4, r6, r8\n\t"
        "adds	r9, r3, r9\n\t"
        "adcs	r10, r4, r10\n\t"
        "adc	r11, r5, r11\n\t"
        /*  A[7] * B[1] */
        "ldr	r6, [%[a], #28]\n\t"
        "ldr	r8, [%[b], #4]\n\t"
        "umull	r3, r4, r6, r8\n\t"
        "adds	r9, r3, r9\n\t"
        "adcs	r10, r4, r10\n\t"
        "adc	r11, r5, r11\n\t"
        "str r9, [sp, #32]\n\t"
        /*  A[2] * B[7] */
        "ldr	r6, [%[a], #8]\n\t"
        "ldr	r8, [%[b], #28]\n\t"
        "umull	r3, r4, r6, r8\n\t"
        "adds	r10, r3, r10\n\t"
        "adcs	r11, r4, r11\n\t"
        "adc	r14, r5, #0\n\t"
        /*  A[3] * B[6] */
        "ldr	r6, [%[a], #12]\n\t"
        "ldr	r8, [%[b], #24]\n\t"
        "umull	r3, r4, r6, r8\n\t"
        "adds	r10, r3, r10\n\t"
        "adcs	r11, r4, r11\n\t"
        "adc	r14, r5, r14\n\t"
        /*  A[4] * B[5] */
        "ldr	r6, [%[a], #16]\n\t"
        "ldr	r8, [%[b], #20]\n\t"
        "umull	r3, r4, r6, r8\n\t"
        "adds	r10, r3, r10\n\t"
        "adcs	r11, r4, r11\n\t"
        "adc	r14, r5, r14\n\t"
        /*  A[5] * B[4] */
        "ldr	r6, [%[a], #20]\n\t"
        "ldr	r8, [%[b], #16]\n\t"
        "umull	r3, r4, r6, r8\n\t"
        "adds	r10, r3, r10\n\t"
        "adcs	r11, r4, r11\n\t"
        "adc	r14, r5, r14\n\t"
        /*  A[6] * B[3] */
        "ldr	r6, [%[a], #24]\n\t"
        "ldr	r8, [%[b], #12]\n\t"
        "umull	r3, r4, r6, r8\n\t"
        "adds	r10, r3, r10\n\t"
        "adcs	r11, r4, r11\n\t"
        "adc	r14, r5, r14\n\t"
        /*  A[7] * B[2] */
        "ldr	r6, [%[a], #28]\n\t"
        "ldr	r8, [%[b], #8]\n\t"
        "umull	r3, r4, r6, r8\n\t"
        "adds	r10, r3, r10\n\t"
        "adcs	r11, r4, r11\n\t"
        "adc	r14, r5, r14\n\t"
        "str r10, [sp, #36]\n\t"
        /*  A[3] * B[7] */
        "ldr	r6, [%[a], #12]\n\t"
        "ldr	r8, [%[b], #28]\n\t"
        "umull	r3, r4, r6, r8\n\t"
        "adds	r11, r3, r11\n\t"
        "adcs	r14, r4, r14\n\t"
        "adc	r9, r5, #0\n\t"
        /*  A[4] * B[6] */
        "ldr	r6, [%[a], #16]\n\t"
        "ldr	r8, [%[b], #24]\n\t"
        "umull	r3, r4, r6, r8\n\t"
        "adds	r11, r3, r11\n\t"
        "adcs	r14, r4, r14\n\t"
        "adc	r9, r5, r9\n\t"
        /*  A[5] * B[5] */
        "ldr	r6, [%[a], #20]\n\t"
        "ldr	r8, [%[b], #20]\n\t"
        "umull	r3, r4, r6, r8\n\t"
        "adds	r11, r3, r11\n\t"
        "adcs	r14, r4, r14\n\t"
        "adc	r9, r5, r9\n\t"
        /*  A[6] * B[4] */
        "ldr	r6, [%[a], #24]\n\t"
        "ldr	r8, [%[b], #16]\n\t"
        "umull	r3, r4, r6, r8\n\t"
        "adds	r11, r3, r11\n\t"
        "adcs	r14, r4, r14\n\t"
        "adc	r9, r5, r9\n\t"
        /*  A[7] * B[3] */
        "ldr	r6, [%[a], #28]\n\t"
        "ldr	r8, [%[b], #12]\n\t"
        "umull	r3, r4, r6, r8\n\t"
        "adds	r11, r3, r11\n\t"
        "adcs	r14, r4, r14\n\t"
        "adc	r9, r5, r9\n\t"
        "str r11, [sp, #40]\n\t"
        /*  A[4] * B[7] */
        "ldr	r6, [%[a], #16]\n\t"
        "ldr	r8, [%[b], #28]\n\t"
        "umull	r3, r4, r6, r8\n\t"
        "adds	r14, r3, r14\n\t"
        "adcs	r9, r4, r9\n\t"
        "adc	r10, r5, #0\n\t"
        /*  A[5] * B[6] */
        "ldr	r6, [%[a], #20]\n\t"
        "ldr	r8, [%[b], #24]\n\t"
        "umull	r3, r4, r6, r8\n\t"
        "adds	r14, r3, r14\n\t"
        "adcs	r9, r4, r9\n\t"
        "adc	r10, r5, r10\n\t"
        /*  A[6] * B[5] */
        "ldr	r6, [%[a], #24]\n\t"
        "ldr	r8, [%[b], #20]\n\t"
        "umull	r3, r4, r6, r8\n\t"
        "adds	r14, r3, r14\n\t"
        "adcs	r9, r4, r9\n\t"
        "adc	r10, r5, r10\n\t"
        /*  A[7] * B[4] */
        "ldr	r6, [%[a], #28]\n\t"
        "ldr	r8, [%[b], #16]\n\t"
        "umull	r3, r4, r6, r8\n\t"
        "adds	r14, r3, r14\n\t"
        "adcs	r9, r4, r9\n\t"
        "adc	r10, r5, r10\n\t"
        "str r14, [sp, #44]\n\t"
        /*  A[5] * B[7] */
        "ldr	r6, [%[a], #20]\n\t"
        "ldr	r8, [%[b], #28]\n\t"
        "umull	r3, r4, r6, r8\n\t"
        "adds	r9, r3, r9\n\t"
        "adcs	r10, r4, r10\n\t"
        "adc	r11, r5, #0\n\t"
        /*  A[6] * B[6] */
        "ldr	r6, [%[a], #24]\n\t"
        "ldr	r8, [%[b], #24]\n\t"
        "umull	r3, r4, r6, r8\n\t"
        "adds	r9, r3, r9\n\t"
        "adcs	r10, r4, r10\n\t"
        "adc	r11, r5, r11\n\t"
        /*  A[7] * B[5] */
        "ldr	r6, [%[a], #28]\n\t"
        "ldr	r8, [%[b], #20]\n\t"
        "umull	r3, r4, r6, r8\n\t"
        "adds	r9, r3, r9\n\t"
        "adcs	r10, r4, r10\n\t"
        "adc	r11, r5, r11\n\t"
        /*  A[6] * B[7] */
        "ldr	r6, [%[a], #24]\n\t"
        "ldr	r8, [%[b], #28]\n\t"
        "umull	r3, r4, r6, r8\n\t"
        "adds	r10, r3, r10\n\t"
        "adcs	r11, r4, r11\n\t"
        "adc	r14, r5, #0\n\t"
        /*  A[7] * B[6] */
        "ldr	r6, [%[a], #28]\n\t"
        "ldr	r8, [%[b], #24]\n\t"
        "umull	r3, r4, r6, r8\n\t"
        "adds	r10, r3, r10\n\t"
        "adcs	r11, r4, r11\n\t"
        "adc	r14, r5, r14\n\t"
        /*  A[7] * B[7] */
        "ldr	r6, [%[a], #28]\n\t"
        "ldr	r8, [%[b], #28]\n\t"
        "umull	r3, r4, r6, r8\n\t"
        "adds	r11, r3, r11\n\t"
        "adc	r14, r4, r14\n\t"
        "str r9, [sp, #48]\n\t"
        "str r10, [sp, #52]\n\t"
        "str r11, [sp, #56]\n\t"
        "str r14, [sp, #60]\n\t"
        /* Start Reduction */
        "ldr r4, [sp, #0]\n\t"
        "ldr r5, [sp, #4]\n\t"
        "ldr r6, [sp, #8]\n\t"
        "ldr r8, [sp, #12]\n\t"
        "ldr r9, [sp, #16]\n\t"
        "ldr r10, [sp, #20]\n\t"
        "ldr r11, [sp, #24]\n\t"
        "ldr r14, [sp, #28]\n\t"
        /* mu = a[0]-a[7] + a[0]-a[4] << 96 + (a[0]-a[1] * 2) << 192 */
        /*    - a[0] << 224 */
        /*   + (a[0]-a[1] * 2) << (6 * 32) */
        "adds  r11, r11, r4\n\t"
        "adc   r14, r14, r5\n\t"
        "adds  r11, r11, r4\n\t"
        "adc   r14, r14, r5\n\t"
        /*   - a[0] << (7 * 32) */
        "sub   r14, r14, r4\n\t"
        /*   + a[0]-a[4] << (3 * 32) */
        "mov   %[a], r8\n\t"
        "mov   %[b], r9\n\t"
        "adds  r8, r8, r4\n\t"
        "adcs  r9, r9, r5\n\t"
        "adcs  r10, r10, r6\n\t"
        "adcs  r11, r11, %[a]\n\t"
        "adc   r14, r14, %[b]\n\t"
        "str r4, [sp, #0]\n\t"
        "str r5, [sp, #4]\n\t"
        "str r6, [sp, #8]\n\t"
        "str r8, [sp, #12]\n\t"
        "str r9, [sp, #16]\n\t"
        "str r10, [sp, #20]\n\t"
        /* a += mu * m */
        /*   += mu * ((1 << 256) - (1 << 224) + (1 << 192) + (1 << 96) - 1) */
        "mov   %[a], #0\n\t"
        /* a[6] +=        t[0] + t[3] */
        "ldr   r3, [sp, #24]\n\t"
        "adds  r3, r3, r4\n\t"
        "adc   %[b], %[a], #0\n\t"
        "adds  r3, r3, r8\n\t"
        "adc   %[b], %[b], #0\n\t"
        "str   r11, [sp, #24]\n\t"
        /* a[7] +=        t[1] + t[4] */
        "ldr   r3, [sp, #28]\n\t"
        "adds  r3, r3, %[b]\n\t"
        "adc   %[b], %[a], #0\n\t"
        "adds  r3, r3, r5\n\t"
        "adc   %[b], %[b], #0\n\t"
        "adds  r3, r3, r9\n\t"
        "adc   %[b], %[b], #0\n\t"
        "str   r14, [sp, #28]\n\t"
        "str   r3, [sp, #64]\n\t"
        /* a[8] += t[0] + t[2] + t[5] */
        "ldr   r3, [sp, #32]\n\t"
        "adds  r3, r3, %[b]\n\t"
        "adc   %[b], %[a], #0\n\t"
        "adds  r3, r3, r4\n\t"
        "adc   %[b], %[b], #0\n\t"
        "adds  r3, r3, r6\n\t"
        "adc   %[b], %[b], #0\n\t"
        "adds  r3, r3, r10\n\t"
        "adc   %[b], %[b], #0\n\t"
        "str   r3, [sp, #32]\n\t"
        /* a[9]  += t[1] + t[3] + t[6] */
        /* a[10] += t[2] + t[4] + t[7] */
        "ldr   r3, [sp, #36]\n\t"
        "ldr   r4, [sp, #40]\n\t"
        "adds  r3, r3, %[b]\n\t"
        "adcs  r4, r4, #0\n\t"
        "adc   %[b], %[a], #0\n\t"
        "adds  r3, r3, r5\n\t"
        "adcs  r4, r4, r6\n\t"
        "adc   %[b], %[b], #0\n\t"
        "adds  r3, r3, r8\n\t"
        "adcs  r4, r4, r9\n\t"
        "adc   %[b], %[b], #0\n\t"
        "adds  r3, r3, r11\n\t"
        "adcs  r4, r4, r14\n\t"
        "adc   %[b], %[b], #0\n\t"
        "str   r3, [sp, #36]\n\t"
        "str   r4, [sp, #40]\n\t"
        /* a[11] += t[3] + t[5] */
        /* a[12] += t[4] + t[6] */
        /* a[13] += t[5] + t[7] */
        /* a[14] += t[6] */
        "ldr   r3, [sp, #44]\n\t"
        "ldr   r4, [sp, #48]\n\t"
        "ldr   r5, [sp, #52]\n\t"
        "ldr   r6, [sp, #56]\n\t"
        "adds  r3, r3, %[b]\n\t"
        "adcs  r4, r4, #0\n\t"
        "adcs  r5, r5, #0\n\t"
        "adcs  r6, r6, #0\n\t"
        "adc   %[b], %[a], #0\n\t"
        "adds  r3, r3, r8\n\t"
        "adcs  r4, r4, r9\n\t"
        "adcs  r5, r5, r10\n\t"
        "adcs  r6, r6, r11\n\t"
        "adc   %[b], %[b], #0\n\t"
        "adds  r3, r3, r10\n\t"
        "adcs  r4, r4, r11\n\t"
        "adcs  r5, r5, r14\n\t"
        "adcs  r6, r6, #0\n\t"
        "adc   %[b], %[b], #0\n\t"
        "str   r3, [sp, #44]\n\t"
        "str   r4, [sp, #48]\n\t"
        "str   r5, [sp, #52]\n\t"
        "str   r6, [sp, #56]\n\t"
        /* a[15] += t[7] */
        "ldr   r3, [sp, #60]\n\t"
        "adds  r3, r3, %[b]\n\t"
        "adc   %[b], %[a], #0\n\t"
        "adds  r3, r3, r14\n\t"
        "adc   %[b], %[b], #0\n\t"
        "str   r3, [sp, #60]\n\t"
        "ldr   r3, [sp, #64]\n\t"
        "ldr   r4, [sp, #32]\n\t"
        "ldr   r5, [sp, #36]\n\t"
        "ldr   r6, [sp, #40]\n\t"
        "ldr   r9, [sp, #0]\n\t"
        "ldr   r10, [sp, #4]\n\t"
        "ldr   r11, [sp, #8]\n\t"
        "ldr   r14, [sp, #12]\n\t"
        "subs  r3, r3, r9\n\t"
        "sbcs  r4, r4, r10\n\t"
        "sbcs  r5, r5, r11\n\t"
        "sbcs  r6, r6, r14\n\t"
        "str   r4, [sp, #32]\n\t"
        "str   r5, [sp, #36]\n\t"
        "str   r6, [sp, #40]\n\t"
        "ldr   r3, [sp, #44]\n\t"
        "ldr   r4, [sp, #48]\n\t"
        "ldr   r5, [sp, #52]\n\t"
        "ldr   r6, [sp, #56]\n\t"
        "ldr   r8, [sp, #60]\n\t"
        "ldr   r9, [sp, #16]\n\t"
        "ldr   r10, [sp, #20]\n\t"
        "ldr   r11, [sp, #24]\n\t"
        "ldr   r14, [sp, #28]\n\t"
        "sbcs  r3, r3, r9\n\t"
        "sbcs  r4, r4, r10\n\t"
        "sbcs  r5, r5, r11\n\t"
        "sbcs  r6, r6, r14\n\t"
        "sbc   r8, r8, #0\n\t"
        "str   r3, [sp, #44]\n\t"
        "str   r4, [sp, #48]\n\t"
        "str   r5, [sp, #52]\n\t"
        "str   r6, [sp, #56]\n\t"
        "str   r8, [sp, #60]\n\t"
        /* mask m and sub from result if overflow */
        "sub   %[b], %[a], %[b]\n\t"
        "and   %[a], %[b], #1\n\t"
        "ldr       r3, [sp, #32]\n\t"
        "ldr       r4, [sp, #36]\n\t"
        "ldr       r5, [sp, #40]\n\t"
        "ldr       r6, [sp, #44]\n\t"
        "ldr       r8, [sp, #48]\n\t"
        "ldr       r9, [sp, #52]\n\t"
        "ldr       r10, [sp, #56]\n\t"
        "ldr       r11, [sp, #60]\n\t"
        "subs      r3, r3, %[b]\n\t"
        "sbcs      r4, r4, %[b]\n\t"
        "sbcs      r5, r5, %[b]\n\t"
        "sbcs      r6, r6, #0\n\t"
        "sbcs      r8, r8, #0\n\t"
        "sbcs      r9, r9, #0\n\t"
        "sbcs      r10, r10, %[a]\n\t"
        "sbc       r11, r11, %[b]\n\t"
        "str       r3, [%[r], #0]\n\t"
        "str       r4, [%[r], #4]\n\t"
        "str       r5, [%[r], #8]\n\t"
        "str       r6, [%[r], #12]\n\t"
        "str       r8, [%[r], #16]\n\t"
        "str       r9, [%[r], #20]\n\t"
        "str       r10, [%[r], #24]\n\t"
        "str       r11, [%[r], #28]\n\t"
        "add   sp, sp, #68\n\t"
        : [a] "+r" (a), [b] "+r" (b)
        : [r] "r" (r)
        : "memory", "r9", "r10", "r11", "r14", "r3", "r4", "r5", "r6", "r8"
    );
}

/* Square the Montgomery form number mod the modulus (prime). (r = a * a mod m)
 *
 * r   Result of squaring.
 * a   Number to square in Montogmery form.
 * m   Modulus (prime).
 * mp  Montogmery mulitplier.
 */
SP_NOINLINE static void sp_256_mont_sqr_8(sp_digit* r, const sp_digit* a, const sp_digit* m,
        sp_digit mp)
{
    (void)mp;
    (void)m;

    __asm__ __volatile__ (
        "sub   sp, sp, #68\n\t"
        "mov   r5, #0\n\t"
        /*  A[0] * A[1] */
        "ldr       r6, [%[a], #0]\n\t"
        "ldr       r8, [%[a], #4]\n\t"
        "umull     r10, r11, r6, r8\n\t"
        "str r10, [sp, #4]\n\t"
        /*  A[0] * A[2] */
        "ldr       r6, [%[a], #0]\n\t"
        "ldr       r8, [%[a], #8]\n\t"
        "umull     r3, r4, r6, r8\n\t"
        "adds  r11, r3, r11\n\t"
        "adc r14, r4, #0\n\t"
        "str r11, [sp, #8]\n\t"
        /*  A[0] * A[3] */
        "ldr       r6, [%[a], #0]\n\t"
        "ldr       r8, [%[a], #12]\n\t"
        "umull     r3, r4, r6, r8\n\t"
        "adds  r14, r3, r14\n\t"
        "adc r9, r4, #0\n\t"
        /*  A[1] * A[2] */
        "ldr       r6, [%[a], #4]\n\t"
        "ldr       r8, [%[a], #8]\n\t"
        "umull     r3, r4, r6, r8\n\t"
        "adds  r14, r3, r14\n\t"
        "adcs r9, r4, r9\n\t"
        "adc   r10, r5, #0\n\t"
        "str r14, [sp, #12]\n\t"
        /*  A[0] * A[4] */
        "ldr       r6, [%[a], #0]\n\t"
        "ldr       r8, [%[a], #16]\n\t"
        "umull     r3, r4, r6, r8\n\t"
        "adds  r9, r3, r9\n\t"
        "adc r10, r4, r10\n\t"
        /*  A[1] * A[3] */
        "ldr       r6, [%[a], #4]\n\t"
        "ldr       r8, [%[a], #12]\n\t"
        "umull     r3, r4, r6, r8\n\t"
        "adds  r9, r3, r9\n\t"
        "adcs r10, r4, r10\n\t"
        "adc   r11, r5, #0\n\t"
        "str r9, [sp, #16]\n\t"
        /*  A[0] * A[5] */
        "ldr       r6, [%[a], #0]\n\t"
        "ldr       r8, [%[a], #20]\n\t"
        "umull     r3, r4, r6, r8\n\t"
        "adds  r10, r3, r10\n\t"
        "adc r11, r4, r11\n\t"
        /*  A[1] * A[4] */
        "ldr       r6, [%[a], #4]\n\t"
        "ldr       r8, [%[a], #16]\n\t"
        "umull     r3, r4, r6, r8\n\t"
        "adds  r10, r3, r10\n\t"
        "adcs r11, r4, r11\n\t"
        "adc   r14, r5, #0\n\t"
        /*  A[2] * A[3] */
        "ldr       r6, [%[a], #8]\n\t"
        "ldr       r8, [%[a], #12]\n\t"
        "umull     r3, r4, r6, r8\n\t"
        "adds  r10, r3, r10\n\t"
        "adcs r11, r4, r11\n\t"
        "adc   r14, r5, r14\n\t"
        "str r10, [sp, #20]\n\t"
        /*  A[0] * A[6] */
        "ldr       r6, [%[a], #0]\n\t"
        "ldr       r8, [%[a], #24]\n\t"
        "umull     r3, r4, r6, r8\n\t"
        "adds  r11, r3, r11\n\t"
        "adcs r14, r4, r14\n\t"
        "adc   r9, r5, #0\n\t"
        /*  A[1] * A[5] */
        "ldr       r6, [%[a], #4]\n\t"
        "ldr       r8, [%[a], #20]\n\t"
        "umull     r3, r4, r6, r8\n\t"
        "adds  r11, r3, r11\n\t"
        "adcs r14, r4, r14\n\t"
        "adc   r9, r5, r9\n\t"
        /*  A[2] * A[4] */
        "ldr       r6, [%[a], #8]\n\t"
        "ldr       r8, [%[a], #16]\n\t"
        "umull     r3, r4, r6, r8\n\t"
        "adds  r11, r3, r11\n\t"
        "adcs r14, r4, r14\n\t"
        "adc   r9, r5, r9\n\t"
        "str r11, [sp, #24]\n\t"
        /*  A[0] * A[7] */
        "ldr       r6, [%[a], #0]\n\t"
        "ldr       r8, [%[a], #28]\n\t"
        "umull     r3, r4, r6, r8\n\t"
        "adds  r14, r3, r14\n\t"
        "adcs r9, r4, r9\n\t"
        "adc   r10, r5, #0\n\t"
        /*  A[1] * A[6] */
        "ldr       r6, [%[a], #4]\n\t"
        "ldr       r8, [%[a], #24]\n\t"
        "umull     r3, r4, r6, r8\n\t"
        "adds  r14, r3, r14\n\t"
        "adcs r9, r4, r9\n\t"
        "adc   r10, r5, r10\n\t"
        /*  A[2] * A[5] */
        "ldr       r6, [%[a], #8]\n\t"
        "ldr       r8, [%[a], #20]\n\t"
        "umull     r3, r4, r6, r8\n\t"
        "adds  r14, r3, r14\n\t"
        "adcs r9, r4, r9\n\t"
        "adc   r10, r5, r10\n\t"
        /*  A[3] * A[4] */
        "ldr       r6, [%[a], #12]\n\t"
        "ldr       r8, [%[a], #16]\n\t"
        "umull     r3, r4, r6, r8\n\t"
        "adds  r14, r3, r14\n\t"
        "adcs r9, r4, r9\n\t"
        "adc   r10, r5, r10\n\t"
        "str r14, [sp, #28]\n\t"
        /*  A[1] * A[7] */
        "ldr       r6, [%[a], #4]\n\t"
        "ldr       r8, [%[a], #28]\n\t"
        "umull     r3, r4, r6, r8\n\t"
        "adds  r9, r3, r9\n\t"
        "adcs r10, r4, r10\n\t"
        "adc   r11, r5, #0\n\t"
        /*  A[2] * A[6] */
        "ldr       r6, [%[a], #8]\n\t"
        "ldr       r8, [%[a], #24]\n\t"
        "umull     r3, r4, r6, r8\n\t"
        "adds  r9, r3, r9\n\t"
        "adcs r10, r4, r10\n\t"
        "adc   r11, r5, r11\n\t"
        /*  A[3] * A[5] */
        "ldr       r6, [%[a], #12]\n\t"
        "ldr       r8, [%[a], #20]\n\t"
        "umull     r3, r4, r6, r8\n\t"
        "adds  r9, r3, r9\n\t"
        "adcs r10, r4, r10\n\t"
        "adc   r11, r5, r11\n\t"
        "str r9, [sp, #32]\n\t"
        /*  A[2] * A[7] */
        "ldr       r6, [%[a], #8]\n\t"
        "ldr       r8, [%[a], #28]\n\t"
        "umull     r3, r4, r6, r8\n\t"
        "adds  r10, r3, r10\n\t"
        "adcs r11, r4, r11\n\t"
        "adc   r14, r5, #0\n\t"
        /*  A[3] * A[6] */
        "ldr       r6, [%[a], #12]\n\t"
        "ldr       r8, [%[a], #24]\n\t"
        "umull     r3, r4, r6, r8\n\t"
        "adds  r10, r3, r10\n\t"
        "adcs r11, r4, r11\n\t"
        "adc   r14, r5, r14\n\t"
        /*  A[4] * A[5] */
        "ldr       r6, [%[a], #16]\n\t"
        "ldr       r8, [%[a], #20]\n\t"
        "umull     r3, r4, r6, r8\n\t"
        "adds  r10, r3, r10\n\t"
        "adcs r11, r4, r11\n\t"
        "adc   r14, r5, r14\n\t"
        "str r10, [sp, #36]\n\t"
        /*  A[3] * A[7] */
        "ldr       r6, [%[a], #12]\n\t"
        "ldr       r8, [%[a], #28]\n\t"
        "umull     r3, r4, r6, r8\n\t"
        "adds  r11, r3, r11\n\t"
        "adcs r14, r4, r14\n\t"
        "adc   r9, r5, #0\n\t"
        /*  A[4] * A[6] */
        "ldr       r6, [%[a], #16]\n\t"
        "ldr       r8, [%[a], #24]\n\t"
        "umull     r3, r4, r6, r8\n\t"
        "adds  r11, r3, r11\n\t"
        "adcs r14, r4, r14\n\t"
        "adc   r9, r5, r9\n\t"
        "str r11, [sp, #40]\n\t"
        /*  A[4] * A[7] */
        "ldr       r6, [%[a], #16]\n\t"
        "ldr       r8, [%[a], #28]\n\t"
        "umull     r3, r4, r6, r8\n\t"
        "adds  r14, r3, r14\n\t"
        "adcs r9, r4, r9\n\t"
        "adc   r10, r5, #0\n\t"
        /*  A[5] * A[6] */
        "ldr       r6, [%[a], #20]\n\t"
        "ldr       r8, [%[a], #24]\n\t"
        "umull     r3, r4, r6, r8\n\t"
        "adds  r14, r3, r14\n\t"
        "adcs r9, r4, r9\n\t"
        "adc   r10, r5, r10\n\t"
        "str r14, [sp, #44]\n\t"
        /*  A[5] * A[7] */
        "ldr       r6, [%[a], #20]\n\t"
        "ldr       r8, [%[a], #28]\n\t"
        "umull     r3, r4, r6, r8\n\t"
        "adds  r9, r3, r9\n\t"
        "adcs r10, r4, r10\n\t"
        "adc   r11, r5, #0\n\t"
        "str r9, [sp, #48]\n\t"
        /*  A[6] * A[7] */
        "ldr       r6, [%[a], #24]\n\t"
        "ldr       r8, [%[a], #28]\n\t"
        "umull     r3, r4, r6, r8\n\t"
        "adds  r10, r3, r10\n\t"
        "adc r11, r4, r11\n\t"
        "str r10, [sp, #52]\n\t"
        "str   r11, [sp, #56]\n\t"
        /*  Double */
        "ldr       r4, [sp, #4]\n\t"
        "ldr       r6, [sp, #8]\n\t"
        "ldr       r8, [sp, #12]\n\t"
        "ldr       r9, [sp, #16]\n\t"
        "ldr       r10, [sp, #20]\n\t"
        "ldr       r11, [sp, #24]\n\t"
        "ldr       r14, [sp, #28]\n\t"
        "ldr       r12, [sp, #32]\n\t"
        "ldr       r3, [sp, #36]\n\t"
        "adds        r4, r4, r4\n\t"
        "adcs      r6, r6, r6\n\t"
        "adcs      r8, r8, r8\n\t"
        "adcs      r9, r9, r9\n\t"
        "adcs      r10, r10, r10\n\t"
        "adcs      r11, r11, r11\n\t"
        "adcs      r14, r14, r14\n\t"
        "adcs      r12, r12, r12\n\t"
        "adcs      r3, r3, r3\n\t"
        "str       r4, [sp, #4]\n\t"
        "str       r6, [sp, #8]\n\t"
        "str       r8, [sp, #12]\n\t"
        "str       r9, [sp, #16]\n\t"
        "str       r10, [sp, #20]\n\t"
        "str       r11, [sp, #24]\n\t"
        "str       r14, [sp, #28]\n\t"
        "str       r12, [sp, #32]\n\t"
        "str       r3, [sp, #36]\n\t"
        "ldr       r4, [sp, #40]\n\t"
        "ldr       r6, [sp, #44]\n\t"
        "ldr       r8, [sp, #48]\n\t"
        "ldr       r9, [sp, #52]\n\t"
        "ldr       r10, [sp, #56]\n\t"
        "adcs        r4, r4, r4\n\t"
        "adcs      r6, r6, r6\n\t"
        "adcs      r8, r8, r8\n\t"
        "adcs      r9, r9, r9\n\t"
        "adcs      r10, r10, r10\n\t"
        "str       r4, [sp, #40]\n\t"
        "str       r6, [sp, #44]\n\t"
        "str       r8, [sp, #48]\n\t"
        "str       r9, [sp, #52]\n\t"
        "str       r10, [sp, #56]\n\t"
        "adc   r11, r5, #0\n\t"
        "str   r11, [sp, #60]\n\t"
        "ldr       r4, [sp, #4]\n\t"
        "ldr       r5, [sp, #8]\n\t"
        "ldr       r12, [sp, #12]\n\t"
        /*  A[0] * A[0] */
        "ldr       r6, [%[a], #0]\n\t"
        "umull     r9, r10, r6, r6\n\t"
        /*  A[1] * A[1] */
        "ldr       r6, [%[a], #4]\n\t"
        "umull     r11, r14, r6, r6\n\t"
        "adds      r10, r10, r4\n\t"
        "adcs      r11, r11, r5\n\t"
        "adcs      r14, r14, r12\n\t"
        "str       r9, [sp, #0]\n\t"
        "str       r10, [sp, #4]\n\t"
        "str       r11, [sp, #8]\n\t"
        "str       r14, [sp, #12]\n\t"
        "ldr       r3, [sp, #16]\n\t"
        "ldr       r4, [sp, #20]\n\t"
        "ldr       r5, [sp, #24]\n\t"
        "ldr       r12, [sp, #28]\n\t"
        /*  A[2] * A[2] */
        "ldr       r6, [%[a], #8]\n\t"
        "umull     r9, r10, r6, r6\n\t"
        /*  A[3] * A[3] */
        "ldr       r6, [%[a], #12]\n\t"
        "umull     r11, r14, r6, r6\n\t"
        "adcs      r9, r9, r3\n\t"
        "adcs      r10, r10, r4\n\t"
        "adcs      r11, r11, r5\n\t"
        "adcs      r14, r14, r12\n\t"
        "str       r9, [sp, #16]\n\t"
        "str       r10, [sp, #20]\n\t"
        "str       r11, [sp, #24]\n\t"
        "str       r14, [sp, #28]\n\t"
        "ldr       r3, [sp, #32]\n\t"
        "ldr       r4, [sp, #36]\n\t"
        "ldr       r5, [sp, #40]\n\t"
        "ldr       r12, [sp, #44]\n\t"
        /*  A[4] * A[4] */
        "ldr       r6, [%[a], #16]\n\t"
        "umull     r9, r10, r6, r6\n\t"
        /*  A[5] * A[5] */
        "ldr       r6, [%[a], #20]\n\t"
        "umull     r11, r14, r6, r6\n\t"
        "adcs      r9, r9, r3\n\t"
        "adcs      r10, r10, r4\n\t"
        "adcs      r11, r11, r5\n\t"
        "adcs      r14, r14, r12\n\t"
        "str       r9, [sp, #32]\n\t"
        "str       r10, [sp, #36]\n\t"
        "str       r11, [sp, #40]\n\t"
        "str       r14, [sp, #44]\n\t"
        "ldr       r3, [sp, #48]\n\t"
        "ldr       r4, [sp, #52]\n\t"
        "ldr       r5, [sp, #56]\n\t"
        "ldr       r12, [sp, #60]\n\t"
        /*  A[6] * A[6] */
        "ldr       r6, [%[a], #24]\n\t"
        "umull     r9, r10, r6, r6\n\t"
        /*  A[7] * A[7] */
        "ldr       r6, [%[a], #28]\n\t"
        "umull     r11, r14, r6, r6\n\t"
        "adcs      r9, r9, r3\n\t"
        "adcs      r10, r10, r4\n\t"
        "adcs      r11, r11, r5\n\t"
        "adc       r14, r14, r12\n\t"
        "str       r9, [sp, #48]\n\t"
        "str       r10, [sp, #52]\n\t"
        "str       r11, [sp, #56]\n\t"
        "str       r14, [sp, #60]\n\t"
        /* Start Reduction */
        "ldr r4, [sp, #0]\n\t"
        "ldr r5, [sp, #4]\n\t"
        "ldr r6, [sp, #8]\n\t"
        "ldr r8, [sp, #12]\n\t"
        "ldr r9, [sp, #16]\n\t"
        "ldr r10, [sp, #20]\n\t"
        "ldr r11, [sp, #24]\n\t"
        "ldr r14, [sp, #28]\n\t"
        /* mu = a[0]-a[7] + a[0]-a[4] << 96 + (a[0]-a[1] * 2) << 192 */
        /*    - a[0] << 224 */
        /*   + (a[0]-a[1] * 2) << (6 * 32) */
        "adds  r11, r11, r4\n\t"
        "adc   r14, r14, r5\n\t"
        "adds  r11, r11, r4\n\t"
        "adc   r14, r14, r5\n\t"
        /*   - a[0] << (7 * 32) */
        "sub   r14, r14, r4\n\t"
        /*   + a[0]-a[4] << (3 * 32) */
        "mov   %[a], r8\n\t"
        "mov   r12, r9\n\t"
        "adds  r8, r8, r4\n\t"
        "adcs  r9, r9, r5\n\t"
        "adcs  r10, r10, r6\n\t"
        "adcs  r11, r11, %[a]\n\t"
        "adc   r14, r14, r12\n\t"
        "str r4, [sp, #0]\n\t"
        "str r5, [sp, #4]\n\t"
        "str r6, [sp, #8]\n\t"
        "str r8, [sp, #12]\n\t"
        "str r9, [sp, #16]\n\t"
        "str r10, [sp, #20]\n\t"
        /* a += mu * m */
        /*   += mu * ((1 << 256) - (1 << 224) + (1 << 192) + (1 << 96) - 1) */
        "mov   %[a], #0\n\t"
        /* a[6] +=        t[0] + t[3] */
        "ldr   r3, [sp, #24]\n\t"
        "adds  r3, r3, r4\n\t"
        "adc   r12, %[a], #0\n\t"
        "adds  r3, r3, r8\n\t"
        "adc   r12, r12, #0\n\t"
        "str   r11, [sp, #24]\n\t"
        /* a[7] +=        t[1] + t[4] */
        "ldr   r3, [sp, #28]\n\t"
        "adds  r3, r3, r12\n\t"
        "adc   r12, %[a], #0\n\t"
        "adds  r3, r3, r5\n\t"
        "adc   r12, r12, #0\n\t"
        "adds  r3, r3, r9\n\t"
        "adc   r12, r12, #0\n\t"
        "str   r14, [sp, #28]\n\t"
        "str   r3, [sp, #64]\n\t"
        /* a[8] += t[0] + t[2] + t[5] */
        "ldr   r3, [sp, #32]\n\t"
        "adds  r3, r3, r12\n\t"
        "adc   r12, %[a], #0\n\t"
        "adds  r3, r3, r4\n\t"
        "adc   r12, r12, #0\n\t"
        "adds  r3, r3, r6\n\t"
        "adc   r12, r12, #0\n\t"
        "adds  r3, r3, r10\n\t"
        "adc   r12, r12, #0\n\t"
        "str   r3, [sp, #32]\n\t"
        /* a[9]  += t[1] + t[3] + t[6] */
        /* a[10] += t[2] + t[4] + t[7] */
        "ldr   r3, [sp, #36]\n\t"
        "ldr   r4, [sp, #40]\n\t"
        "adds  r3, r3, r12\n\t"
        "adcs  r4, r4, #0\n\t"
        "adc   r12, %[a], #0\n\t"
        "adds  r3, r3, r5\n\t"
        "adcs  r4, r4, r6\n\t"
        "adc   r12, r12, #0\n\t"
        "adds  r3, r3, r8\n\t"
        "adcs  r4, r4, r9\n\t"
        "adc   r12, r12, #0\n\t"
        "adds  r3, r3, r11\n\t"
        "adcs  r4, r4, r14\n\t"
        "adc   r12, r12, #0\n\t"
        "str   r3, [sp, #36]\n\t"
        "str   r4, [sp, #40]\n\t"
        /* a[11] += t[3] + t[5] */
        /* a[12] += t[4] + t[6] */
        /* a[13] += t[5] + t[7] */
        /* a[14] += t[6] */
        "ldr   r3, [sp, #44]\n\t"
        "ldr   r4, [sp, #48]\n\t"
        "ldr   r5, [sp, #52]\n\t"
        "ldr   r6, [sp, #56]\n\t"
        "adds  r3, r3, r12\n\t"
        "adcs  r4, r4, #0\n\t"
        "adcs  r5, r5, #0\n\t"
        "adcs  r6, r6, #0\n\t"
        "adc   r12, %[a], #0\n\t"
        "adds  r3, r3, r8\n\t"
        "adcs  r4, r4, r9\n\t"
        "adcs  r5, r5, r10\n\t"
        "adcs  r6, r6, r11\n\t"
        "adc   r12, r12, #0\n\t"
        "adds  r3, r3, r10\n\t"
        "adcs  r4, r4, r11\n\t"
        "adcs  r5, r5, r14\n\t"
        "adcs  r6, r6, #0\n\t"
        "adc   r12, r12, #0\n\t"
        "str   r3, [sp, #44]\n\t"
        "str   r4, [sp, #48]\n\t"
        "str   r5, [sp, #52]\n\t"
        "str   r6, [sp, #56]\n\t"
        /* a[15] += t[7] */
        "ldr   r3, [sp, #60]\n\t"
        "adds  r3, r3, r12\n\t"
        "adc   r12, %[a], #0\n\t"
        "adds  r3, r3, r14\n\t"
        "adc   r12, r12, #0\n\t"
        "str   r3, [sp, #60]\n\t"
        "ldr   r3, [sp, #64]\n\t"
        "ldr   r4, [sp, #32]\n\t"
        "ldr   r5, [sp, #36]\n\t"
        "ldr   r6, [sp, #40]\n\t"
        "ldr   r9, [sp, #0]\n\t"
        "ldr   r10, [sp, #4]\n\t"
        "ldr   r11, [sp, #8]\n\t"
        "ldr   r14, [sp, #12]\n\t"
        "subs  r3, r3, r9\n\t"
        "sbcs  r4, r4, r10\n\t"
        "sbcs  r5, r5, r11\n\t"
        "sbcs  r6, r6, r14\n\t"
        "str   r4, [sp, #32]\n\t"
        "str   r5, [sp, #36]\n\t"
        "str   r6, [sp, #40]\n\t"
        "ldr   r3, [sp, #44]\n\t"
        "ldr   r4, [sp, #48]\n\t"
        "ldr   r5, [sp, #52]\n\t"
        "ldr   r6, [sp, #56]\n\t"
        "ldr   r8, [sp, #60]\n\t"
        "ldr   r9, [sp, #16]\n\t"
        "ldr   r10, [sp, #20]\n\t"
        "ldr   r11, [sp, #24]\n\t"
        "ldr   r14, [sp, #28]\n\t"
        "sbcs  r3, r3, r9\n\t"
        "sbcs  r4, r4, r10\n\t"
        "sbcs  r5, r5, r11\n\t"
        "sbcs  r6, r6, r14\n\t"
        "sbc   r8, r8, #0\n\t"
        "str   r3, [sp, #44]\n\t"
        "str   r4, [sp, #48]\n\t"
        "str   r5, [sp, #52]\n\t"
        "str   r6, [sp, #56]\n\t"
        "str   r8, [sp, #60]\n\t"
        /* mask m and sub from result if overflow */
        "sub   r12, %[a], r12\n\t"
        "and   %[a], r12, #1\n\t"
        "ldr       r3, [sp, #32]\n\t"
        "ldr       r4, [sp, #36]\n\t"
        "ldr       r5, [sp, #40]\n\t"
        "ldr       r6, [sp, #44]\n\t"
        "ldr       r8, [sp, #48]\n\t"
        "ldr       r9, [sp, #52]\n\t"
        "ldr       r10, [sp, #56]\n\t"
        "ldr       r11, [sp, #60]\n\t"
        "subs      r3, r3, r12\n\t"
        "sbcs      r4, r4, r12\n\t"
        "sbcs      r5, r5, r12\n\t"
        "sbcs      r6, r6, #0\n\t"
        "sbcs      r8, r8, #0\n\t"
        "sbcs      r9, r9, #0\n\t"
        "sbcs      r10, r10, %[a]\n\t"
        "sbc       r11, r11, r12\n\t"
        "str       r3, [%[r], #0]\n\t"
        "str       r4, [%[r], #4]\n\t"
        "str       r5, [%[r], #8]\n\t"
        "str       r6, [%[r], #12]\n\t"
        "str       r8, [%[r], #16]\n\t"
        "str       r9, [%[r], #20]\n\t"
        "str       r10, [%[r], #24]\n\t"
        "str       r11, [%[r], #28]\n\t"
        "add   sp, sp, #68\n\t"
        : [a] "+r" (a)
        : [r] "r" (r)
        : "memory", "r9", "r10", "r11", "r14", "r3", "r4", "r5", "r6", "r8", "r12"
    );
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
static void sp_256_mont_sqr_n_8(sp_digit* r, const sp_digit* a, int n,
        const sp_digit* m, sp_digit mp)
{
    sp_256_mont_sqr_8(r, a, m, mp);
    for (; n > 1; n--) {
        sp_256_mont_sqr_8(r, r, m, mp);
    }
}

#endif /* !WOLFSSL_SP_SMALL || HAVE_COMP_KEY */
#ifdef WOLFSSL_SP_SMALL
/* Mod-2 for the P256 curve. */
static const uint32_t p256_mod_minus_2[8] = {
    0xfffffffdU,0xffffffffU,0xffffffffU,0x00000000U,0x00000000U,0x00000000U,
    0x00000001U,0xffffffffU
};
#endif /* !WOLFSSL_SP_SMALL */

/* Invert the number, in Montgomery form, modulo the modulus (prime) of the
 * P256 curve. (r = 1 / a mod m)
 *
 * r   Inverse result.
 * a   Number to invert.
 * td  Temporary data.
 */
static void sp_256_mont_inv_8(sp_digit* r, const sp_digit* a, sp_digit* td)
{
#ifdef WOLFSSL_SP_SMALL
    sp_digit* t = td;
    int i;

    XMEMCPY(t, a, sizeof(sp_digit) * 8);
    for (i=254; i>=0; i--) {
        sp_256_mont_sqr_8(t, t, p256_mod, p256_mp_mod);
        if (p256_mod_minus_2[i / 32] & ((sp_digit)1 << (i % 32)))
            sp_256_mont_mul_8(t, t, a, p256_mod, p256_mp_mod);
    }
    XMEMCPY(r, t, sizeof(sp_digit) * 8);
#else
    sp_digit* t1 = td;
    sp_digit* t2 = td + 2 * 8;
    sp_digit* t3 = td + 4 * 8;
    /* 0x2 */
    sp_256_mont_sqr_8(t1, a, p256_mod, p256_mp_mod);
    /* 0x3 */
    sp_256_mont_mul_8(t2, t1, a, p256_mod, p256_mp_mod);
    /* 0xc */
    sp_256_mont_sqr_n_8(t1, t2, 2, p256_mod, p256_mp_mod);
    /* 0xd */
    sp_256_mont_mul_8(t3, t1, a, p256_mod, p256_mp_mod);
    /* 0xf */
    sp_256_mont_mul_8(t2, t2, t1, p256_mod, p256_mp_mod);
    /* 0xf0 */
    sp_256_mont_sqr_n_8(t1, t2, 4, p256_mod, p256_mp_mod);
    /* 0xfd */
    sp_256_mont_mul_8(t3, t3, t1, p256_mod, p256_mp_mod);
    /* 0xff */
    sp_256_mont_mul_8(t2, t2, t1, p256_mod, p256_mp_mod);
    /* 0xff00 */
    sp_256_mont_sqr_n_8(t1, t2, 8, p256_mod, p256_mp_mod);
    /* 0xfffd */
    sp_256_mont_mul_8(t3, t3, t1, p256_mod, p256_mp_mod);
    /* 0xffff */
    sp_256_mont_mul_8(t2, t2, t1, p256_mod, p256_mp_mod);
    /* 0xffff0000 */
    sp_256_mont_sqr_n_8(t1, t2, 16, p256_mod, p256_mp_mod);
    /* 0xfffffffd */
    sp_256_mont_mul_8(t3, t3, t1, p256_mod, p256_mp_mod);
    /* 0xffffffff */
    sp_256_mont_mul_8(t2, t2, t1, p256_mod, p256_mp_mod);
    /* 0xffffffff00000000 */
    sp_256_mont_sqr_n_8(t1, t2, 32, p256_mod, p256_mp_mod);
    /* 0xffffffffffffffff */
    sp_256_mont_mul_8(t2, t2, t1, p256_mod, p256_mp_mod);
    /* 0xffffffff00000001 */
    sp_256_mont_mul_8(r, t1, a, p256_mod, p256_mp_mod);
    /* 0xffffffff000000010000000000000000000000000000000000000000 */
    sp_256_mont_sqr_n_8(r, r, 160, p256_mod, p256_mp_mod);
    /* 0xffffffff00000001000000000000000000000000ffffffffffffffff */
    sp_256_mont_mul_8(r, r, t2, p256_mod, p256_mp_mod);
    /* 0xffffffff00000001000000000000000000000000ffffffffffffffff00000000 */
    sp_256_mont_sqr_n_8(r, r, 32, p256_mod, p256_mp_mod);
    /* 0xffffffff00000001000000000000000000000000fffffffffffffffffffffffd */
    sp_256_mont_mul_8(r, r, t3, p256_mod, p256_mp_mod);
#endif /* WOLFSSL_SP_SMALL */
}

/* Compare a with b in constant time.
 *
 * a  A single precision integer.
 * b  A single precision integer.
 * return -ve, 0 or +ve if a is less than, equal to or greater than b
 * respectively.
 */
SP_NOINLINE static int32_t sp_256_cmp_8(const sp_digit* a, const sp_digit* b)
{
    sp_digit r = 0;


    __asm__ __volatile__ (
        "mov	r3, #0\n\t"
        "mvn	r3, r3\n\t"
        "mov	r6, #28\n\t"
        "\n1:\n\t"
        "ldr	r8, [%[a], r6]\n\t"
        "ldr	r5, [%[b], r6]\n\t"
        "and	r8, r8, r3\n\t"
        "and	r5, r5, r3\n\t"
        "mov	r4, r8\n\t"
        "subs	r8, r8, r5\n\t"
        "sbc	r8, r8, r8\n\t"
        "add	%[r], %[r], r8\n\t"
        "mvn	r8, r8\n\t"
        "and	r3, r3, r8\n\t"
        "subs	r5, r5, r4\n\t"
        "sbc	r8, r8, r8\n\t"
        "sub	%[r], %[r], r8\n\t"
        "mvn	r8, r8\n\t"
        "and	r3, r3, r8\n\t"
        "sub	r6, r6, #4\n\t"
        "cmp	r6, #0\n\t"
        "bge	1b\n\t"
        : [r] "+r" (r)
        : [a] "r" (a), [b] "r" (b)
        : "r3", "r4", "r5", "r6", "r8"
    );

    return r;
}

/* Normalize the values in each word to 32.
 *
 * a  Array of sp_digit to normalize.
 */
#define sp_256_norm_8(a)

/* Conditionally subtract b from a using the mask m.
 * m is -1 to subtract and 0 when not copying.
 *
 * r  A single precision number representing condition subtract result.
 * a  A single precision number to subtract from.
 * b  A single precision number to subtract.
 * m  Mask value to apply.
 */
SP_NOINLINE static sp_digit sp_256_cond_sub_8(sp_digit* r, const sp_digit* a,
        const sp_digit* b, sp_digit m)
{
    sp_digit c = 0;

    __asm__ __volatile__ (
        "mov	r5, #32\n\t"
        "mov	r9, r5\n\t"
        "mov	r8, #0\n\t"
        "\n1:\n\t"
        "ldr	r6, [%[b], r8]\n\t"
        "and	r6, r6, %[m]\n\t"
        "mov	r5, #0\n\t"
        "subs	r5, r5, %[c]\n\t"
        "ldr	r5, [%[a], r8]\n\t"
        "sbcs	r5, r5, r6\n\t"
        "sbcs	%[c], %[c], %[c]\n\t"
        "str	r5, [%[r], r8]\n\t"
        "add	r8, r8, #4\n\t"
        "cmp	r8, r9\n\t"
        "blt	1b\n\t"
        : [c] "+r" (c)
        : [r] "r" (r), [a] "r" (a), [b] "r" (b), [m] "r" (m)
        : "memory", "r5", "r6", "r8", "r9"
    );

    return c;
}

/* Reduce the number back to 256 bits using Montgomery reduction.
 *
 * a   A single precision number to reduce in place.
 * m   The single precision number representing the modulus.
 * mp  The digit representing the negative inverse of m mod 2^n.
 */
SP_NOINLINE static void sp_256_mont_reduce_8(sp_digit* a, const sp_digit* m,
        sp_digit mp)
{
    (void)mp;
    (void)m;

    __asm__ __volatile__ (
        "mov	r2, #0\n\t"
        "mov	r1, #0\n\t"
        /* i = 0 */
        "mov	r9, r2\n\t"
        "\n1:\n\t"
        "mov	r4, #0\n\t"
        /* mu = a[i] * 1 (mp) = a[i] */
        "ldr	r3, [%[a]]\n\t"
        /* a[i] += -1 * mu = -1 * a[i] => a[i] = 0 no carry */
        /* a[i+1] += -1 * mu */
        "ldr	r6, [%[a], #4]\n\t"
        "mov	r5, #0\n\t"
        "adds	r4, r4, r6\n\t"
        "adc	r5, r5, r2\n\t"
        "str	r4, [%[a], #4]\n\t"
        /* a[i+2] += -1 * mu */
        "ldr	r6, [%[a], #8]\n\t"
        "mov	r4, #0\n\t"
        "adds	r5, r5, r6\n\t"
        "adc	r4, r4, r2\n\t"
        "str	r5, [%[a], #8]\n\t"
        /* a[i+3] += 0 * mu */
        "ldr	r6, [%[a], #12]\n\t"
        "mov	r5, #0\n\t"
        "adds	r4, r4, r3\n\t"
        "adc	r5, r5, r2\n\t"
        "adds	r4, r4, r6\n\t"
        "adc	r5, r5, r2\n\t"
        "str	r4, [%[a], #12]\n\t"
        /* a[i+4] += 0 * mu */
        "ldr	r6, [%[a], #16]\n\t"
        "mov	r4, #0\n\t"
        "adds	r5, r5, r6\n\t"
        "adc	r4, r4, r2\n\t"
        "str	r5, [%[a], #16]\n\t"
        /* a[i+5] += 0 * mu */
        "ldr	r6, [%[a], #20]\n\t"
        "mov	r5, #0\n\t"
        "adds	r4, r4, r6\n\t"
        "adc	r5, r5, r2\n\t"
        "str	r4, [%[a], #20]\n\t"
        /* a[i+6] += 1 * mu */
        "ldr	r6, [%[a], #24]\n\t"
        "mov	r4, #0\n\t"
        "adds	r5, r5, r3\n\t"
        "adc	r4, r4, r2\n\t"
        "adds	r5, r5, r6\n\t"
        "adc	r4, r4, r2\n\t"
        "str	r5, [%[a], #24]\n\t"
        /* a[i+7] += -1 * mu */
        "ldr	r6, [%[a], #28]\n\t"
        "ldr	r8, [%[a], #32]\n\t"
        "adds	r5, r1, r3\n\t"
        "mov	r1, #0\n\t"
        "adc	r1, r1, r2\n\t"
        "subs	r4, r4, r3\n\t"
        "sbcs	r5, r5, r2\n\t"
        "sbc	r1, r1, r2\n\t"
        "adds	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "adc	r1, r1, r2\n\t"
        "str	r4, [%[a],  #28]\n\t"
        "str	r5, [%[a], #32]\n\t"
        /* i += 1 */
        "add	r9, r9, #1\n\t"
        "add	%[a], %[a], #4\n\t"
        "mov	r6, #8\n\t"
        "cmp	r9, r6\n\t"
        "blt	1b\n\t"
        "sub	%[a], %[a], #32\n\t"
        "mov	r3, r1\n\t"
        "sub	r1, r1, #1\n\t"
        "mvn	r1, r1\n\t"
        "ldr	r4, [%[a],#32]\n\t"
        "ldr	r5, [%[a],#36]\n\t"
        "ldr	r6, [%[a],#40]\n\t"
        "ldr	r8, [%[a],#44]\n\t"
        "ldr	r9, [%[a],#48]\n\t"
        "ldr	r10, [%[a],#52]\n\t"
        "ldr	r11, [%[a],#56]\n\t"
        "ldr	r14, [%[a],#60]\n\t"
        "subs	r4, r4, r1\n\t"
        "sbcs	r5, r5, r1\n\t"
        "sbcs	r6, r6, r1\n\t"
        "sbcs	r8, r8, r2\n\t"
        "sbcs	r9, r9, r2\n\t"
        "sbcs	r10, r10, r2\n\t"
        "sbcs	r11, r11, r3\n\t"
        "sbc	r14, r14, r1\n\t"
        "str	r4, [%[a],#0]\n\t"
        "str	r5, [%[a],#4]\n\t"
        "str	r6, [%[a],#8]\n\t"
        "str	r8, [%[a],#12]\n\t"
        "str	r9, [%[a],#16]\n\t"
        "str	r10, [%[a],#20]\n\t"
        "str	r11, [%[a],#24]\n\t"
        "str	r14, [%[a],#28]\n\t"
        : [a] "+r" (a)
        :
        : "memory", "r1", "r2", "r3", "r4", "r5", "r6", "r8", "r9", "r10", "r11", "r14"
    );


    (void)m;
    (void)mp;
}

/* Reduce the number back to 256 bits using Montgomery reduction.
 *
 * a   A single precision number to reduce in place.
 * m   The single precision number representing the modulus.
 * mp  The digit representing the negative inverse of m mod 2^n.
 */
SP_NOINLINE static void sp_256_mont_reduce_order_8(sp_digit* a, const sp_digit* m,
        sp_digit mp)
{
    sp_digit ca = 0;

    __asm__ __volatile__ (
        "mov	r9, %[mp]\n\t"
        "mov	r12, %[m]\n\t"
        "mov	r10, %[a]\n\t"
        "mov	r4, #0\n\t"
        "add	r11, r10, #32\n\t"
        "\n1:\n\t"
        /* mu = a[i] * mp */
        "mov	%[mp], r9\n\t"
        "ldr	%[a], [r10]\n\t"
        "mul	%[mp], %[mp], %[a]\n\t"
        "mov	%[m], r12\n\t"
        "add	r14, r10, #24\n\t"
        "\n2:\n\t"
        /* a[i+j] += m[j] * mu */
        "ldr	%[a], [r10]\n\t"
        "mov	r5, #0\n\t"
        /* Multiply m[j] and mu - Start */
        "ldr	r8, [%[m]], #4\n\t"
        "umull	r6, r8, %[mp], r8\n\t"
        "adds	%[a], %[a], r6\n\t"
        "adc	r5, r5, r8\n\t"
        /* Multiply m[j] and mu - Done */
        "adds	r4, r4, %[a]\n\t"
        "adc	r5, r5, #0\n\t"
        "str	r4, [r10], #4\n\t"
        /* a[i+j+1] += m[j+1] * mu */
        "ldr	%[a], [r10]\n\t"
        "mov	r4, #0\n\t"
        /* Multiply m[j] and mu - Start */
        "ldr	r8, [%[m]], #4\n\t"
        "umull	r6, r8, %[mp], r8\n\t"
        "adds	%[a], %[a], r6\n\t"
        "adc	r4, r4, r8\n\t"
        /* Multiply m[j] and mu - Done */
        "adds	r5, r5, %[a]\n\t"
        "adc	r4, r4, #0\n\t"
        "str	r5, [r10], #4\n\t"
        "cmp	r10, r14\n\t"
        "blt	2b\n\t"
        /* a[i+6] += m[6] * mu */
        "ldr	%[a], [r10]\n\t"
        "mov	r5, #0\n\t"
        /* Multiply m[j] and mu - Start */
        "ldr	r8, [%[m]], #4\n\t"
        "umull	r6, r8, %[mp], r8\n\t"
        "adds	%[a], %[a], r6\n\t"
        "adc	r5, r5, r8\n\t"
        /* Multiply m[j] and mu - Done */
        "adds	r4, r4, %[a]\n\t"
        "adc	r5, r5, #0\n\t"
        "str	r4, [r10], #4\n\t"
        /* a[i+7] += m[7] * mu */
        "mov	r4, %[ca]\n\t"
        "mov	%[ca], #0\n\t"
        /* Multiply m[7] and mu - Start */
        "ldr	r8, [%[m]]\n\t"
        "umull	r6, r8, %[mp], r8\n\t"
        "adds	r5, r5, r6\n\t"
        "adcs 	r4, r4, r8\n\t"
        "adc	%[ca], %[ca], #0\n\t"
        /* Multiply m[7] and mu - Done */
        "ldr	r6, [r10]\n\t"
        "ldr	r8, [r10, #4]\n\t"
        "adds	r6, r6, r5\n\t"
        "adcs	r8, r8, r4\n\t"
        "adc	%[ca], %[ca], #0\n\t"
        "str	r6, [r10]\n\t"
        "str	r8, [r10, #4]\n\t"
        /* Next word in a */
        "sub	r10, r10, #24\n\t"
        "cmp	r10, r11\n\t"
        "blt	1b\n\t"
        "mov	%[a], r10\n\t"
        "mov	%[m], r12\n\t"
        : [ca] "+r" (ca), [a] "+r" (a)
        : [m] "r" (m), [mp] "r" (mp)
        : "memory", "r4", "r5", "r6", "r8", "r9", "r10", "r11", "r12", "r14"
    );

    sp_256_cond_sub_8(a - 8, a, m, (sp_digit)0 - ca);
}

/* Map the Montgomery form projective coordinate point to an affine point.
 *
 * r  Resulting affine coordinate point.
 * p  Montgomery form projective coordinate point.
 * t  Temporary ordinate data.
 */
static void sp_256_map_8(sp_point_256* r, const sp_point_256* p, sp_digit* t)
{
    sp_digit* t1 = t;
    sp_digit* t2 = t + 2*8;
    int32_t n;

    sp_256_mont_inv_8(t1, p->z, t + 2*8);

    sp_256_mont_sqr_8(t2, t1, p256_mod, p256_mp_mod);
    sp_256_mont_mul_8(t1, t2, t1, p256_mod, p256_mp_mod);

    /* x /= z^2 */
    sp_256_mont_mul_8(r->x, p->x, t2, p256_mod, p256_mp_mod);
    XMEMSET(r->x + 8, 0, sizeof(r->x) / 2U);
    sp_256_mont_reduce_8(r->x, p256_mod, p256_mp_mod);
    /* Reduce x to less than modulus */
    n = sp_256_cmp_8(r->x, p256_mod);
    sp_256_cond_sub_8(r->x, r->x, p256_mod, 0 - ((n >= 0) ?
                (sp_digit)1 : (sp_digit)0));
    sp_256_norm_8(r->x);

    /* y /= z^3 */
    sp_256_mont_mul_8(r->y, p->y, t1, p256_mod, p256_mp_mod);
    XMEMSET(r->y + 8, 0, sizeof(r->y) / 2U);
    sp_256_mont_reduce_8(r->y, p256_mod, p256_mp_mod);
    /* Reduce y to less than modulus */
    n = sp_256_cmp_8(r->y, p256_mod);
    sp_256_cond_sub_8(r->y, r->y, p256_mod, 0 - ((n >= 0) ?
                (sp_digit)1 : (sp_digit)0));
    sp_256_norm_8(r->y);

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
SP_NOINLINE static sp_digit sp_256_add_8(sp_digit* r, const sp_digit* a,
        const sp_digit* b)
{
    sp_digit c = 0;

    __asm__ __volatile__ (
        "mov	r6, %[a]\n\t"
        "mov	r8, #0\n\t"
        "add	r6, r6, #32\n\t"
        "sub	r8, r8, #1\n\t"
        "\n1:\n\t"
        "adds	%[c], %[c], r8\n\t"
        "ldr	r4, [%[a]]\n\t"
        "ldr	r5, [%[b]]\n\t"
        "adcs	r4, r4, r5\n\t"
        "str	r4, [%[r]]\n\t"
        "mov	%[c], #0\n\t"
        "adc	%[c], %[c], %[c]\n\t"
        "add	%[a], %[a], #4\n\t"
        "add	%[b], %[b], #4\n\t"
        "add	%[r], %[r], #4\n\t"
        "cmp	%[a], r6\n\t"
        "bne	1b\n\t"
        : [c] "+r" (c), [r] "+r" (r), [a] "+r" (a), [b] "+r" (b)
        :
        : "memory", "r4", "r5", "r6", "r8"
    );

    return c;
}

#else
/* Add b to a into r. (r = a + b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A single precision integer.
 */
SP_NOINLINE static sp_digit sp_256_add_8(sp_digit* r, const sp_digit* a,
        const sp_digit* b)
{
    sp_digit c = 0;

    __asm__ __volatile__ (
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adds	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "mov	%[c], #0\n\t"
        "adc	%[c], %[c], %[c]\n\t"
        : [c] "+r" (c), [r] "+r" (r), [a] "+r" (a), [b] "+r" (b)
        :
        : "memory", "r4", "r5", "r6", "r8"
    );

    return c;
}

#endif /* WOLFSSL_SP_SMALL */
/* Add two Montgomery form numbers (r = a + b % m).
 *
 * r   Result of addition.
 * a   First number to add in Montogmery form.
 * b   Second number to add in Montogmery form.
 * m   Modulus (prime).
 */
SP_NOINLINE static void sp_256_mont_add_8(sp_digit* r, const sp_digit* a, const sp_digit* b,
        const sp_digit* m)
{
    (void)m;

    __asm__ __volatile__ (
        "mov   r12, #0\n\t"
        "ldr       r4, [%[a],#0]\n\t"
        "ldr       r5, [%[a],#4]\n\t"
        "ldr       r6, [%[a],#8]\n\t"
        "ldr       r8, [%[a],#12]\n\t"
        "ldr       r9, [%[b],#0]\n\t"
        "ldr       r10, [%[b],#4]\n\t"
        "ldr       r11, [%[b],#8]\n\t"
        "ldr       r14, [%[b],#12]\n\t"
        "adds    r4, r4, r9\n\t"
        "adcs    r5, r5, r10\n\t"
        "adcs    r6, r6, r11\n\t"
        "adcs    r8, r8, r14\n\t"
        "str       r4, [%[r],#0]\n\t"
        "str       r5, [%[r],#4]\n\t"
        "str       r6, [%[r],#8]\n\t"
        "str       r8, [%[r],#12]\n\t"
        "ldr       r4, [%[a],#16]\n\t"
        "ldr       r5, [%[a],#20]\n\t"
        "ldr       r6, [%[a],#24]\n\t"
        "ldr       r8, [%[a],#28]\n\t"
        "ldr       r9, [%[b],#16]\n\t"
        "ldr       r10, [%[b],#20]\n\t"
        "ldr       r11, [%[b],#24]\n\t"
        "ldr       r14, [%[b],#28]\n\t"
        "adcs    r4, r4, r9\n\t"
        "adcs    r5, r5, r10\n\t"
        "adcs    r6, r6, r11\n\t"
        "adcs    r8, r8, r14\n\t"
        "adc   r3, r12, #0\n\t"
        "sub   r3, r12, r3\n\t"
        "and   r12, r3, #1\n\t"
        "ldr   r9, [%[r],#0]\n\t"
        "ldr   r10, [%[r],#4]\n\t"
        "ldr   r11, [%[r],#8]\n\t"
        "ldr   r14, [%[r],#12]\n\t"
        "subs  r9, r9, r3\n\t"
        "sbcs  r10, r10, r3\n\t"
        "sbcs  r11, r11, r3\n\t"
        "sbcs  r14, r14, #0\n\t"
        "sbcs  r4, r4, #0\n\t"
        "sbcs  r5, r5, #0\n\t"
        "sbcs  r6, r6, r12\n\t"
        "sbc   r8, r8, r3\n\t"
        "str   r9, [%[r],#0]\n\t"
        "str   r10, [%[r],#4]\n\t"
        "str   r11, [%[r],#8]\n\t"
        "str   r14, [%[r],#12]\n\t"
        "str   r4, [%[r],#16]\n\t"
        "str   r5, [%[r],#20]\n\t"
        "str   r6, [%[r],#24]\n\t"
        "str   r8, [%[r],#28]\n\t"
        :
        : [r] "r" (r), [a] "r" (a), [b] "r" (b)
        : "memory", "r4", "r5", "r6", "r8", "r9", "r10", "r11", "r14", "r3", "r12"
    );
}

/* Double a Montgomery form number (r = a + a % m).
 *
 * r   Result of doubling.
 * a   Number to double in Montogmery form.
 * m   Modulus (prime).
 */
SP_NOINLINE static void sp_256_mont_dbl_8(sp_digit* r, const sp_digit* a, const sp_digit* m)
{
    (void)m;

    __asm__ __volatile__ (
        "mov   r12, #0\n\t"
        "ldr        r4, [%[a],#0]\n\t"
        "ldr        r5, [%[a],#4]\n\t"
        "ldr        r6, [%[a],#8]\n\t"
        "ldr        r8, [%[a],#12]\n\t"
        "ldr        r9, [%[a],#16]\n\t"
        "ldr        r10, [%[a],#20]\n\t"
        "ldr        r11, [%[a],#24]\n\t"
        "ldr        r14, [%[a],#28]\n\t"
        "adds      r4, r4, r4\n\t"
        "adcs      r5, r5, r5\n\t"
        "adcs      r6, r6, r6\n\t"
        "adcs      r8, r8, r8\n\t"
        "adcs      r9, r9, r9\n\t"
        "adcs      r10, r10, r10\n\t"
        "adcs      r11, r11, r11\n\t"
        "adcs      r14, r14, r14\n\t"
        "adc   r3, r12, #0\n\t"
        "sub   r3, r12, r3\n\t"
        "and   r12, r3, #1\n\t"
        "subs  r4, r4, r3\n\t"
        "sbcs  r5, r5, r3\n\t"
        "sbcs  r6, r6, r3\n\t"
        "sbcs  r8, r8, #0\n\t"
        "sbcs  r9, r9, #0\n\t"
        "sbcs  r10, r10, #0\n\t"
        "sbcs  r11, r11, r12\n\t"
        "sbc   r14, r14, r3\n\t"
        "str   r4, [%[r],#0]\n\t"
        "str   r5, [%[r],#4]\n\t"
        "str   r6, [%[r],#8]\n\t"
        "str   r8, [%[r],#12]\n\t"
        "str   r9, [%[r],#16]\n\t"
        "str   r10, [%[r],#20]\n\t"
        "str   r11, [%[r],#24]\n\t"
        "str   r14, [%[r],#28]\n\t"
        :
        : [r] "r" (r), [a] "r" (a)
        : "memory", "r4", "r5", "r6", "r8", "r9", "r10", "r11", "r14", "r3", "r12"
    );
}

/* Triple a Montgomery form number (r = a + a + a % m).
 *
 * r   Result of Tripling.
 * a   Number to triple in Montogmery form.
 * m   Modulus (prime).
 */
SP_NOINLINE static void sp_256_mont_tpl_8(sp_digit* r, const sp_digit* a, const sp_digit* m)
{
    (void)m;

    __asm__ __volatile__ (
        "ldr	r2, [%[a],#0]\n\t"
        "ldr	r3, [%[a],#4]\n\t"
        "ldr	r4, [%[a],#8]\n\t"
        "ldr	r5, [%[a],#12]\n\t"
        "ldr	r6, [%[a],#16]\n\t"
        "ldr	r8, [%[a],#20]\n\t"
        "ldr	r9, [%[a],#24]\n\t"
        "ldr	r10, [%[a],#28]\n\t"
        "adds	r2, r2, r2\n\t"
        "adcs	r3, r3, r3\n\t"
        "adcs	r4, r4, r4\n\t"
        "adcs	r5, r5, r5\n\t"
        "adcs	r6, r6, r6\n\t"
        "adcs	r8, r8, r8\n\t"
        "adcs	r9, r9, r9\n\t"
        "adcs	r10, r10, r10\n\t"
        "mov	r11, #0\n\t"
        "mov	r14, #0\n\t"
        "adc	r11, r11, r11\n\t"
        "mov	r12, r11\n\t"
        "sub	r11, r11, #1\n\t"
        "mvn	r11, r11\n\t"
        "subs	r2, r2, r11\n\t"
        "sbcs	r3, r3, r11\n\t"
        "sbcs	r4, r4, r11\n\t"
        "sbcs	r5, r5, r14\n\t"
        "sbcs	r6, r6, r14\n\t"
        "sbcs	r8, r8, r14\n\t"
        "sbcs	r9, r9, r12\n\t"
        "sbc	r10, r10, r11\n\t"
        "ldr	r12, [%[a],#0]\n\t"
        "ldr	r14, [%[a],#4]\n\t"
        "adds	r2, r2, r12\n\t"
        "adcs	r3, r3, r14\n\t"
        "ldr	r12, [%[a],#8]\n\t"
        "ldr	r14, [%[a],#12]\n\t"
        "adcs	r4, r4, r12\n\t"
        "adcs	r5, r5, r14\n\t"
        "ldr	r12, [%[a],#16]\n\t"
        "ldr	r14, [%[a],#20]\n\t"
        "adcs	r6, r6, r12\n\t"
        "adcs	r8, r8, r14\n\t"
        "ldr	r12, [%[a],#24]\n\t"
        "ldr	r14, [%[a],#28]\n\t"
        "adcs	r9, r9, r12\n\t"
        "adcs	r10, r10, r14\n\t"
        "mov	r11, #0\n\t"
        "mov	r14, #0\n\t"
        "adc	r11, r11, r11\n\t"
        "mov	r12, r11\n\t"
        "sub	r11, r11, #1\n\t"
        "mvn	r11, r11\n\t"
        "subs	r2, r2, r11\n\t"
        "str	r2, [%[r],#0]\n\t"
        "sbcs	r3, r3, r11\n\t"
        "str	r3, [%[r],#4]\n\t"
        "sbcs	r4, r4, r11\n\t"
        "str	r4, [%[r],#8]\n\t"
        "sbcs	r5, r5, r14\n\t"
        "str	r5, [%[r],#12]\n\t"
        "sbcs	r6, r6, r14\n\t"
        "str	r6, [%[r],#16]\n\t"
        "sbcs	r8, r8, r14\n\t"
        "str	r8, [%[r],#20]\n\t"
        "sbcs	r9, r9, r12\n\t"
        "str	r9, [%[r],#24]\n\t"
        "sbc	r10, r10, r11\n\t"
        "str	r10, [%[r],#28]\n\t"
        :
        : [r] "r" (r), [a] "r" (a)
        : "memory", "r11", "r12", "r14", "r2", "r3", "r4", "r5", "r6", "r8", "r9", "r10"
    );
}

/* Subtract two Montgomery form numbers (r = a - b % m).
 *
 * r   Result of subtration.
 * a   Number to subtract from in Montogmery form.
 * b   Number to subtract with in Montogmery form.
 * m   Modulus (prime).
 */
SP_NOINLINE static void sp_256_mont_sub_8(sp_digit* r, const sp_digit* a, const sp_digit* b,
        const sp_digit* m)
{
    (void)m;

    __asm__ __volatile__ (
        "mov   r12, #0\n\t"
        "ldr       r4, [%[a],#0]\n\t"
        "ldr       r5, [%[a],#4]\n\t"
        "ldr       r6, [%[a],#8]\n\t"
        "ldr       r8, [%[a],#12]\n\t"
        "ldr       r9, [%[b],#0]\n\t"
        "ldr       r10, [%[b],#4]\n\t"
        "ldr       r11, [%[b],#8]\n\t"
        "ldr       r14, [%[b],#12]\n\t"
        "subs    r4, r4, r9\n\t"
        "sbcs    r5, r5, r10\n\t"
        "sbcs    r6, r6, r11\n\t"
        "sbcs    r8, r8, r14\n\t"
        "str       r4, [%[r],#0]\n\t"
        "str       r5, [%[r],#4]\n\t"
        "str       r6, [%[r],#8]\n\t"
        "str       r8, [%[r],#12]\n\t"
        "ldr       r4, [%[a],#16]\n\t"
        "ldr       r5, [%[a],#20]\n\t"
        "ldr       r6, [%[a],#24]\n\t"
        "ldr       r8, [%[a],#28]\n\t"
        "ldr       r9, [%[b],#16]\n\t"
        "ldr       r10, [%[b],#20]\n\t"
        "ldr       r11, [%[b],#24]\n\t"
        "ldr       r14, [%[b],#28]\n\t"
        "sbcs    r4, r4, r9\n\t"
        "sbcs    r5, r5, r10\n\t"
        "sbcs    r6, r6, r11\n\t"
        "sbcs    r8, r8, r14\n\t"
        "sbc   r3, r12, #0\n\t"
        "and   r12, r3, #1\n\t"
        "ldr   r9, [%[r],#0]\n\t"
        "ldr   r10, [%[r],#4]\n\t"
        "ldr   r11, [%[r],#8]\n\t"
        "ldr   r14, [%[r],#12]\n\t"
        "adds  r9, r9, r3\n\t"
        "adcs  r10, r10, r3\n\t"
        "adcs  r11, r11, r3\n\t"
        "adcs  r14, r14, #0\n\t"
        "adcs  r4, r4, #0\n\t"
        "adcs  r5, r5, #0\n\t"
        "adcs  r6, r6, r12\n\t"
        "adc   r8, r8, r3\n\t"
        "str   r9, [%[r],#0]\n\t"
        "str   r10, [%[r],#4]\n\t"
        "str   r11, [%[r],#8]\n\t"
        "str   r14, [%[r],#12]\n\t"
        "str   r4, [%[r],#16]\n\t"
        "str   r5, [%[r],#20]\n\t"
        "str   r6, [%[r],#24]\n\t"
        "str   r8, [%[r],#28]\n\t"
        :
        : [r] "r" (r), [a] "r" (a), [b] "r" (b)
        : "memory", "r4", "r5", "r6", "r8", "r9", "r10", "r11", "r14", "r3", "r12"
    );
}

/* Divide the number by 2 mod the modulus (prime). (r = a / 2 % m)
 *
 * r  Result of division by 2.
 * a  Number to divide.
 * m  Modulus (prime).
 */
SP_NOINLINE static void sp_256_div2_8(sp_digit* r, const sp_digit* a, const sp_digit* m)
{
    __asm__ __volatile__ (
        "ldr	r8, [%[a], #0]\n\t"
        "lsl	r8, r8, #31\n\t"
        "lsr	r8, r8, #31\n\t"
        "mov	r5, #0\n\t"
        "sub	r5, r5, r8\n\t"
        "mov	r8, #0\n\t"
        "lsl	r6, r5, #31\n\t"
        "lsr	r6, r6, #31\n\t"
        "ldr	r3, [%[a], #0]\n\t"
        "ldr	r4, [%[a], #4]\n\t"
        "adds	r3, r3, r5\n\t"
        "adcs	r4, r4, r5\n\t"
        "str	r3, [%[r], #0]\n\t"
        "str	r4, [%[r], #4]\n\t"
        "ldr	r3, [%[a], #8]\n\t"
        "ldr	r4, [%[a], #12]\n\t"
        "adcs	r3, r3, r5\n\t"
        "adcs	r4, r4, r8\n\t"
        "str	r3, [%[r], #8]\n\t"
        "str	r4, [%[r], #12]\n\t"
        "ldr	r3, [%[a], #16]\n\t"
        "ldr	r4, [%[a], #20]\n\t"
        "adcs	r3, r3, r8\n\t"
        "adcs	r4, r4, r8\n\t"
        "str	r3, [%[r], #16]\n\t"
        "str	r4, [%[r], #20]\n\t"
        "ldr	r3, [%[a], #24]\n\t"
        "ldr	r4, [%[a], #28]\n\t"
        "adcs	r3, r3, r6\n\t"
        "adcs	r4, r4, r5\n\t"
        "adc	r8, r8, r8\n\t"
        "lsl	r8, r8, #31\n\t"
        "lsr	r5, r3, #1\n\t"
        "lsl	r3, r3, #31\n\t"
        "lsr	r6, r4, #1\n\t"
        "lsl	r4, r4, #31\n\t"
        "orr	r5, r5, r4\n\t"
        "orr	r6, r6, r8\n\t"
        "mov	r8, r3\n\t"
        "str	r5, [%[r], #24]\n\t"
        "str	r6, [%[r], #28]\n\t"
        "ldr	r3, [%[a], #16]\n\t"
        "ldr	r4, [%[a], #20]\n\t"
        "lsr	r5, r3, #1\n\t"
        "lsl	r3, r3, #31\n\t"
        "lsr	r6, r4, #1\n\t"
        "lsl	r4, r4, #31\n\t"
        "orr	r5, r5, r4\n\t"
        "orr	r6, r6, r8\n\t"
        "mov	r8, r3\n\t"
        "str	r5, [%[r], #16]\n\t"
        "str	r6, [%[r], #20]\n\t"
        "ldr	r3, [%[a], #8]\n\t"
        "ldr	r4, [%[a], #12]\n\t"
        "lsr	r5, r3, #1\n\t"
        "lsl	r3, r3, #31\n\t"
        "lsr	r6, r4, #1\n\t"
        "lsl	r4, r4, #31\n\t"
        "orr	r5, r5, r4\n\t"
        "orr	r6, r6, r8\n\t"
        "mov	r8, r3\n\t"
        "str	r5, [%[r], #8]\n\t"
        "str	r6, [%[r], #12]\n\t"
        "ldr	r3, [%[r], #0]\n\t"
        "ldr	r4, [%[r], #4]\n\t"
        "lsr	r5, r3, #1\n\t"
        "lsr	r6, r4, #1\n\t"
        "lsl	r4, r4, #31\n\t"
        "orr	r5, r5, r4\n\t"
        "orr	r6, r6, r8\n\t"
        "str	r5, [%[r], #0]\n\t"
        "str	r6, [%[r], #4]\n\t"
        :
        : [r] "r" (r), [a] "r" (a), [m] "r" (m)
        : "memory", "r3", "r4", "r5", "r6", "r8"
    );
}

/* Double the Montgomery form projective point p.
 *
 * r  Result of doubling point.
 * p  Point to double.
 * t  Temporary ordinate data.
 */
#ifdef WOLFSSL_SP_NONBLOCK
typedef struct sp_256_proj_point_dbl_8_ctx {
    int state;
    sp_digit* t1;
    sp_digit* t2;
    sp_digit* x;
    sp_digit* y;
    sp_digit* z;
} sp_256_proj_point_dbl_8_ctx;

static int sp_256_proj_point_dbl_8_nb(sp_ecc_ctx_t* sp_ctx, sp_point_256* r, const sp_point_256* p, sp_digit* t)
{
    int err = FP_WOULDBLOCK;
    sp_256_proj_point_dbl_8_ctx* ctx = (sp_256_proj_point_dbl_8_ctx*)sp_ctx->data;

    typedef char ctx_size_test[sizeof(sp_256_proj_point_dbl_8_ctx) >= sizeof(*sp_ctx) ? -1 : 1];
    (void)sizeof(ctx_size_test);

    switch (ctx->state) {
    case 0:
        ctx->t1 = t;
        ctx->t2 = t + 2*8;
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
        sp_256_mont_sqr_8(ctx->t1, p->z, p256_mod, p256_mp_mod);
        ctx->state = 2;
        break;
    case 2:
        /* Z = Y * Z */
        sp_256_mont_mul_8(ctx->z, p->y, p->z, p256_mod, p256_mp_mod);
        ctx->state = 3;
        break;
    case 3:
        /* Z = 2Z */
        sp_256_mont_dbl_8(ctx->z, ctx->z, p256_mod);
        ctx->state = 4;
        break;
    case 4:
        /* T2 = X - T1 */
        sp_256_mont_sub_8(ctx->t2, p->x, ctx->t1, p256_mod);
        ctx->state = 5;
        break;
    case 5:
        /* T1 = X + T1 */
        sp_256_mont_add_8(ctx->t1, p->x, ctx->t1, p256_mod);
        ctx->state = 6;
        break;
    case 6:
        /* T2 = T1 * T2 */
        sp_256_mont_mul_8(ctx->t2, ctx->t1, ctx->t2, p256_mod, p256_mp_mod);
        ctx->state = 7;
        break;
    case 7:
        /* T1 = 3T2 */
        sp_256_mont_tpl_8(ctx->t1, ctx->t2, p256_mod);
        ctx->state = 8;
        break;
    case 8:
        /* Y = 2Y */
        sp_256_mont_dbl_8(ctx->y, p->y, p256_mod);
        ctx->state = 9;
        break;
    case 9:
        /* Y = Y * Y */
        sp_256_mont_sqr_8(ctx->y, ctx->y, p256_mod, p256_mp_mod);
        ctx->state = 10;
        break;
    case 10:
        /* T2 = Y * Y */
        sp_256_mont_sqr_8(ctx->t2, ctx->y, p256_mod, p256_mp_mod);
        ctx->state = 11;
        break;
    case 11:
        /* T2 = T2/2 */
        sp_256_div2_8(ctx->t2, ctx->t2, p256_mod);
        ctx->state = 12;
        break;
    case 12:
        /* Y = Y * X */
        sp_256_mont_mul_8(ctx->y, ctx->y, p->x, p256_mod, p256_mp_mod);
        ctx->state = 13;
        break;
    case 13:
        /* X = T1 * T1 */
        sp_256_mont_sqr_8(ctx->x, ctx->t1, p256_mod, p256_mp_mod);
        ctx->state = 14;
        break;
    case 14:
        /* X = X - Y */
        sp_256_mont_sub_8(ctx->x, ctx->x, ctx->y, p256_mod);
        ctx->state = 15;
        break;
    case 15:
        /* X = X - Y */
        sp_256_mont_sub_8(ctx->x, ctx->x, ctx->y, p256_mod);
        ctx->state = 16;
        break;
    case 16:
        /* Y = Y - X */
        sp_256_mont_sub_8(ctx->y, ctx->y, ctx->x, p256_mod);
        ctx->state = 17;
        break;
    case 17:
        /* Y = Y * T1 */
        sp_256_mont_mul_8(ctx->y, ctx->y, ctx->t1, p256_mod, p256_mp_mod);
        ctx->state = 18;
        break;
    case 18:
        /* Y = Y - T2 */
        sp_256_mont_sub_8(ctx->y, ctx->y, ctx->t2, p256_mod);
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

static void sp_256_proj_point_dbl_8(sp_point_256* r, const sp_point_256* p, sp_digit* t)
{
    sp_digit* t1 = t;
    sp_digit* t2 = t + 2*8;
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
    sp_256_mont_sqr_8(t1, p->z, p256_mod, p256_mp_mod);
    /* Z = Y * Z */
    sp_256_mont_mul_8(z, p->y, p->z, p256_mod, p256_mp_mod);
    /* Z = 2Z */
    sp_256_mont_dbl_8(z, z, p256_mod);
    /* T2 = X - T1 */
    sp_256_mont_sub_8(t2, p->x, t1, p256_mod);
    /* T1 = X + T1 */
    sp_256_mont_add_8(t1, p->x, t1, p256_mod);
    /* T2 = T1 * T2 */
    sp_256_mont_mul_8(t2, t1, t2, p256_mod, p256_mp_mod);
    /* T1 = 3T2 */
    sp_256_mont_tpl_8(t1, t2, p256_mod);
    /* Y = 2Y */
    sp_256_mont_dbl_8(y, p->y, p256_mod);
    /* Y = Y * Y */
    sp_256_mont_sqr_8(y, y, p256_mod, p256_mp_mod);
    /* T2 = Y * Y */
    sp_256_mont_sqr_8(t2, y, p256_mod, p256_mp_mod);
    /* T2 = T2/2 */
    sp_256_div2_8(t2, t2, p256_mod);
    /* Y = Y * X */
    sp_256_mont_mul_8(y, y, p->x, p256_mod, p256_mp_mod);
    /* X = T1 * T1 */
    sp_256_mont_sqr_8(x, t1, p256_mod, p256_mp_mod);
    /* X = X - Y */
    sp_256_mont_sub_8(x, x, y, p256_mod);
    /* X = X - Y */
    sp_256_mont_sub_8(x, x, y, p256_mod);
    /* Y = Y - X */
    sp_256_mont_sub_8(y, y, x, p256_mod);
    /* Y = Y * T1 */
    sp_256_mont_mul_8(y, y, t1, p256_mod, p256_mp_mod);
    /* Y = Y - T2 */
    sp_256_mont_sub_8(y, y, t2, p256_mod);
}

#ifdef WOLFSSL_SP_SMALL
/* Sub b from a into r. (r = a - b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A single precision integer.
 */
SP_NOINLINE static sp_digit sp_256_sub_8(sp_digit* r, const sp_digit* a,
        const sp_digit* b)
{
    sp_digit c = 0;

    __asm__ __volatile__ (
        "mov	r6, %[a]\n\t"
        "add	r6, r6, #32\n\t"
        "\n1:\n\t"
        "mov	r5, #0\n\t"
        "subs	r5, r5, %[c]\n\t"
        "ldr	r4, [%[a]]\n\t"
        "ldr	r5, [%[b]]\n\t"
        "sbcs	r4, r4, r5\n\t"
        "str	r4, [%[r]]\n\t"
        "sbc	%[c], %[c], %[c]\n\t"
        "add	%[a], %[a], #4\n\t"
        "add	%[b], %[b], #4\n\t"
        "add	%[r], %[r], #4\n\t"
        "cmp	%[a], r6\n\t"
        "bne	1b\n\t"
        : [c] "+r" (c), [r] "+r" (r), [a] "+r" (a), [b] "+r" (b)
        :
        : "memory", "r4", "r5", "r6"
    );

    return c;
}

#else
/* Sub b from a into r. (r = a - b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A single precision integer.
 */
SP_NOINLINE static sp_digit sp_256_sub_8(sp_digit* r, const sp_digit* a,
        const sp_digit* b)
{
    sp_digit c = 0;

    __asm__ __volatile__ (
        "ldr	r4, [%[a], #0]\n\t"
        "ldr	r5, [%[a], #4]\n\t"
        "ldr	r6, [%[b], #0]\n\t"
        "ldr	r8, [%[b], #4]\n\t"
        "subs	r4, r4, r6\n\t"
        "sbcs	r5, r5, r8\n\t"
        "str	r4, [%[r], #0]\n\t"
        "str	r5, [%[r], #4]\n\t"
        "ldr	r4, [%[a], #8]\n\t"
        "ldr	r5, [%[a], #12]\n\t"
        "ldr	r6, [%[b], #8]\n\t"
        "ldr	r8, [%[b], #12]\n\t"
        "sbcs	r4, r4, r6\n\t"
        "sbcs	r5, r5, r8\n\t"
        "str	r4, [%[r], #8]\n\t"
        "str	r5, [%[r], #12]\n\t"
        "ldr	r4, [%[a], #16]\n\t"
        "ldr	r5, [%[a], #20]\n\t"
        "ldr	r6, [%[b], #16]\n\t"
        "ldr	r8, [%[b], #20]\n\t"
        "sbcs	r4, r4, r6\n\t"
        "sbcs	r5, r5, r8\n\t"
        "str	r4, [%[r], #16]\n\t"
        "str	r5, [%[r], #20]\n\t"
        "ldr	r4, [%[a], #24]\n\t"
        "ldr	r5, [%[a], #28]\n\t"
        "ldr	r6, [%[b], #24]\n\t"
        "ldr	r8, [%[b], #28]\n\t"
        "sbcs	r4, r4, r6\n\t"
        "sbcs	r5, r5, r8\n\t"
        "str	r4, [%[r], #24]\n\t"
        "str	r5, [%[r], #28]\n\t"
        "sbc	%[c], %[c], %[c]\n\t"
        : [c] "+r" (c), [r] "+r" (r), [a] "+r" (a), [b] "+r" (b)
        :
        : "memory", "r4", "r5", "r6", "r8"
    );

    return c;
}

#endif /* WOLFSSL_SP_SMALL */
/* Compare two numbers to determine if they are equal.
 * Constant time implementation.
 *
 * a  First number to compare.
 * b  Second number to compare.
 * returns 1 when equal and 0 otherwise.
 */
static int sp_256_cmp_equal_8(const sp_digit* a, const sp_digit* b)
{
    return ((a[0] ^ b[0]) | (a[1] ^ b[1]) | (a[2] ^ b[2]) | (a[3] ^ b[3]) |
            (a[4] ^ b[4]) | (a[5] ^ b[5]) | (a[6] ^ b[6]) | (a[7] ^ b[7])) == 0;
}

/* Add two Montgomery form projective points.
 *
 * r  Result of addition.
 * p  First point to add.
 * q  Second point to add.
 * t  Temporary ordinate data.
 */

#ifdef WOLFSSL_SP_NONBLOCK
typedef struct sp_256_proj_point_add_8_ctx {
    int state;
    sp_256_proj_point_dbl_8_ctx dbl_ctx;
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
} sp_256_proj_point_add_8_ctx;

static int sp_256_proj_point_add_8_nb(sp_ecc_ctx_t* sp_ctx, sp_point_256* r, 
    const sp_point_256* p, const sp_point_256* q, sp_digit* t)
{
    int err = FP_WOULDBLOCK;
    sp_256_proj_point_add_8_ctx* ctx = (sp_256_proj_point_add_8_ctx*)sp_ctx->data;

    /* Ensure only the first point is the same as the result. */
    if (q == r) {
        const sp_point_256* a = p;
        p = q;
        q = a;
    }

    typedef char ctx_size_test[sizeof(sp_256_proj_point_add_8_ctx) >= sizeof(*sp_ctx) ? -1 : 1];
    (void)sizeof(ctx_size_test);

    switch (ctx->state) {
    case 0: /* INIT */
        ctx->t1 = t;
        ctx->t2 = t + 2*8;
        ctx->t3 = t + 4*8;
        ctx->t4 = t + 6*8;
        ctx->t5 = t + 8*8;

        ctx->state = 1;
        break;
    case 1:
        /* Check double */
        (void)sp_256_sub_8(ctx->t1, p256_mod, q->y);
        sp_256_norm_8(ctx->t1);
        if ((sp_256_cmp_equal_8(p->x, q->x) & sp_256_cmp_equal_8(p->z, q->z) &
            (sp_256_cmp_equal_8(p->y, q->y) | sp_256_cmp_equal_8(p->y, ctx->t1))) != 0)
        {
            XMEMSET(&ctx->dbl_ctx, 0, sizeof(ctx->dbl_ctx));
            ctx->state = 2;
        }
        else {
            ctx->state = 3;
        }
        break;
    case 2:
        err = sp_256_proj_point_dbl_8_nb((sp_ecc_ctx_t*)&ctx->dbl_ctx, r, p, t);
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
        for (i=0; i<8; i++) {
            r->x[i] = ctx->ap[p->infinity]->x[i];
        }
        for (i=0; i<8; i++) {
            r->y[i] = ctx->ap[p->infinity]->y[i];
        }
        for (i=0; i<8; i++) {
            r->z[i] = ctx->ap[p->infinity]->z[i];
        }
        r->infinity = ctx->ap[p->infinity]->infinity;

        ctx->state = 4;
        break;
    }
    case 4:
        /* U1 = X1*Z2^2 */
        sp_256_mont_sqr_8(ctx->t1, q->z, p256_mod, p256_mp_mod);
        ctx->state = 5;
        break;
    case 5:
        sp_256_mont_mul_8(ctx->t3, ctx->t1, q->z, p256_mod, p256_mp_mod);
        ctx->state = 6;
        break;
    case 6:
        sp_256_mont_mul_8(ctx->t1, ctx->t1, ctx->x, p256_mod, p256_mp_mod);
        ctx->state = 7;
        break;
    case 7:
        /* U2 = X2*Z1^2 */
        sp_256_mont_sqr_8(ctx->t2, ctx->z, p256_mod, p256_mp_mod);
        ctx->state = 8;
        break;
    case 8:
        sp_256_mont_mul_8(ctx->t4, ctx->t2, ctx->z, p256_mod, p256_mp_mod);
        ctx->state = 9;
        break;
    case 9:
        sp_256_mont_mul_8(ctx->t2, ctx->t2, q->x, p256_mod, p256_mp_mod);
        ctx->state = 10;
        break;
    case 10:
        /* S1 = Y1*Z2^3 */
        sp_256_mont_mul_8(ctx->t3, ctx->t3, ctx->y, p256_mod, p256_mp_mod);
        ctx->state = 11;
        break;
    case 11:
        /* S2 = Y2*Z1^3 */
        sp_256_mont_mul_8(ctx->t4, ctx->t4, q->y, p256_mod, p256_mp_mod);
        ctx->state = 12;
        break;
    case 12:
        /* H = U2 - U1 */
        sp_256_mont_sub_8(ctx->t2, ctx->t2, ctx->t1, p256_mod);
        ctx->state = 13;
        break;
    case 13:
        /* R = S2 - S1 */
        sp_256_mont_sub_8(ctx->t4, ctx->t4, ctx->t3, p256_mod);
        ctx->state = 14;
        break;
    case 14:
        /* Z3 = H*Z1*Z2 */
        sp_256_mont_mul_8(ctx->z, ctx->z, q->z, p256_mod, p256_mp_mod);
        ctx->state = 15;
        break;
    case 15:
        sp_256_mont_mul_8(ctx->z, ctx->z, ctx->t2, p256_mod, p256_mp_mod);
        ctx->state = 16;
        break;
    case 16:
        /* X3 = R^2 - H^3 - 2*U1*H^2 */
        sp_256_mont_sqr_8(ctx->x, ctx->t4, p256_mod, p256_mp_mod);
        ctx->state = 17;
        break;
    case 17:
        sp_256_mont_sqr_8(ctx->t5, ctx->t2, p256_mod, p256_mp_mod);
        ctx->state = 18;
        break;
    case 18:
        sp_256_mont_mul_8(ctx->y, ctx->t1, ctx->t5, p256_mod, p256_mp_mod);
        ctx->state = 19;
        break;
    case 19:
        sp_256_mont_mul_8(ctx->t5, ctx->t5, ctx->t2, p256_mod, p256_mp_mod);
        ctx->state = 20;
        break;
    case 20:
        sp_256_mont_sub_8(ctx->x, ctx->x, ctx->t5, p256_mod);
        ctx->state = 21;
        break;
    case 21:
        sp_256_mont_dbl_8(ctx->t1, ctx->y, p256_mod);
        ctx->state = 22;
        break;
    case 22:
        sp_256_mont_sub_8(ctx->x, ctx->x, ctx->t1, p256_mod);
        ctx->state = 23;
        break;
    case 23:
        /* Y3 = R*(U1*H^2 - X3) - S1*H^3 */
        sp_256_mont_sub_8(ctx->y, ctx->y, ctx->x, p256_mod);
        ctx->state = 24;
        break;
    case 24:
        sp_256_mont_mul_8(ctx->y, ctx->y, ctx->t4, p256_mod, p256_mp_mod);
        ctx->state = 25;
        break;
    case 25:
        sp_256_mont_mul_8(ctx->t5, ctx->t5, ctx->t3, p256_mod, p256_mp_mod);
        ctx->state = 26;
        break;
    case 26:
        sp_256_mont_sub_8(ctx->y, ctx->y, ctx->t5, p256_mod);
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

static void sp_256_proj_point_add_8(sp_point_256* r, const sp_point_256* p, const sp_point_256* q,
        sp_digit* t)
{
    const sp_point_256* ap[2];
    sp_point_256* rp[2];
    sp_digit* t1 = t;
    sp_digit* t2 = t + 2*8;
    sp_digit* t3 = t + 4*8;
    sp_digit* t4 = t + 6*8;
    sp_digit* t5 = t + 8*8;
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
    (void)sp_256_sub_8(t1, p256_mod, q->y);
    sp_256_norm_8(t1);
    if ((sp_256_cmp_equal_8(p->x, q->x) & sp_256_cmp_equal_8(p->z, q->z) &
        (sp_256_cmp_equal_8(p->y, q->y) | sp_256_cmp_equal_8(p->y, t1))) != 0) {
        sp_256_proj_point_dbl_8(r, p, t);
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
        for (i=0; i<8; i++) {
            r->x[i] = ap[p->infinity]->x[i];
        }
        for (i=0; i<8; i++) {
            r->y[i] = ap[p->infinity]->y[i];
        }
        for (i=0; i<8; i++) {
            r->z[i] = ap[p->infinity]->z[i];
        }
        r->infinity = ap[p->infinity]->infinity;

        /* U1 = X1*Z2^2 */
        sp_256_mont_sqr_8(t1, q->z, p256_mod, p256_mp_mod);
        sp_256_mont_mul_8(t3, t1, q->z, p256_mod, p256_mp_mod);
        sp_256_mont_mul_8(t1, t1, x, p256_mod, p256_mp_mod);
        /* U2 = X2*Z1^2 */
        sp_256_mont_sqr_8(t2, z, p256_mod, p256_mp_mod);
        sp_256_mont_mul_8(t4, t2, z, p256_mod, p256_mp_mod);
        sp_256_mont_mul_8(t2, t2, q->x, p256_mod, p256_mp_mod);
        /* S1 = Y1*Z2^3 */
        sp_256_mont_mul_8(t3, t3, y, p256_mod, p256_mp_mod);
        /* S2 = Y2*Z1^3 */
        sp_256_mont_mul_8(t4, t4, q->y, p256_mod, p256_mp_mod);
        /* H = U2 - U1 */
        sp_256_mont_sub_8(t2, t2, t1, p256_mod);
        /* R = S2 - S1 */
        sp_256_mont_sub_8(t4, t4, t3, p256_mod);
        /* Z3 = H*Z1*Z2 */
        sp_256_mont_mul_8(z, z, q->z, p256_mod, p256_mp_mod);
        sp_256_mont_mul_8(z, z, t2, p256_mod, p256_mp_mod);
        /* X3 = R^2 - H^3 - 2*U1*H^2 */
        sp_256_mont_sqr_8(x, t4, p256_mod, p256_mp_mod);
        sp_256_mont_sqr_8(t5, t2, p256_mod, p256_mp_mod);
        sp_256_mont_mul_8(y, t1, t5, p256_mod, p256_mp_mod);
        sp_256_mont_mul_8(t5, t5, t2, p256_mod, p256_mp_mod);
        sp_256_mont_sub_8(x, x, t5, p256_mod);
        sp_256_mont_dbl_8(t1, y, p256_mod);
        sp_256_mont_sub_8(x, x, t1, p256_mod);
        /* Y3 = R*(U1*H^2 - X3) - S1*H^3 */
        sp_256_mont_sub_8(y, y, x, p256_mod);
        sp_256_mont_mul_8(y, y, t4, p256_mod, p256_mp_mod);
        sp_256_mont_mul_8(t5, t5, t3, p256_mod, p256_mp_mod);
        sp_256_mont_sub_8(y, y, t5, p256_mod);
    }
}

#ifndef WC_NO_CACHE_RESISTANT
/* Touch each possible point that could be being copied.
 *
 * r      Point to copy into.
 * table  Table - start of the entires to access
 * idx    Index of entry to retrieve.
 */
static void sp_256_get_point_16_8(sp_point_256* r, const sp_point_256* table,
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
    r->x[7] = 0;
    r->y[0] = 0;
    r->y[1] = 0;
    r->y[2] = 0;
    r->y[3] = 0;
    r->y[4] = 0;
    r->y[5] = 0;
    r->y[6] = 0;
    r->y[7] = 0;
    r->z[0] = 0;
    r->z[1] = 0;
    r->z[2] = 0;
    r->z[3] = 0;
    r->z[4] = 0;
    r->z[5] = 0;
    r->z[6] = 0;
    r->z[7] = 0;
    for (i = 1; i < 16; i++) {
        mask = 0 - (i == idx);
        r->x[0] |= mask & table[i].x[0];
        r->x[1] |= mask & table[i].x[1];
        r->x[2] |= mask & table[i].x[2];
        r->x[3] |= mask & table[i].x[3];
        r->x[4] |= mask & table[i].x[4];
        r->x[5] |= mask & table[i].x[5];
        r->x[6] |= mask & table[i].x[6];
        r->x[7] |= mask & table[i].x[7];
        r->y[0] |= mask & table[i].y[0];
        r->y[1] |= mask & table[i].y[1];
        r->y[2] |= mask & table[i].y[2];
        r->y[3] |= mask & table[i].y[3];
        r->y[4] |= mask & table[i].y[4];
        r->y[5] |= mask & table[i].y[5];
        r->y[6] |= mask & table[i].y[6];
        r->y[7] |= mask & table[i].y[7];
        r->z[0] |= mask & table[i].z[0];
        r->z[1] |= mask & table[i].z[1];
        r->z[2] |= mask & table[i].z[2];
        r->z[3] |= mask & table[i].z[3];
        r->z[4] |= mask & table[i].z[4];
        r->z[5] |= mask & table[i].z[5];
        r->z[6] |= mask & table[i].z[6];
        r->z[7] |= mask & table[i].z[7];
    }
}
#endif /* !WC_NO_CACHE_RESISTANT */
/* Multiply the point by the scalar and return the result.
 * If map is true then convert result to affine coordinates.
 *
 * Simple, smaller code size and memory size, of windowing.
 * Calculate uindow of 4 bits.
 * Only add points from table.
 *
 * r     Resulting point.
 * g     Point to multiply.
 * k     Scalar to multiply by.
 * map   Indicates whether to convert result to affine.
 * ct    Constant time required.
 * heap  Heap to use for allocation.
 * returns MEMORY_E when memory allocation fails and MP_OKAY on success.
 */
static int sp_256_ecc_mulmod_fast_8(sp_point_256* r, const sp_point_256* g, const sp_digit* k,
        int map, int ct, void* heap)
{
#if (!defined(WOLFSSL_SP_SMALL) && !defined(WOLFSSL_SMALL_STACK)) || defined(WOLFSSL_SP_NO_MALLOC)
    sp_point_256 td[16];
    sp_point_256 rtd;
    sp_digit tmpd[2 * 8 * 5];
#ifndef WC_NO_CACHE_RESISTANT
    sp_point_256 pd;
#endif
#endif
    sp_point_256* t;
    sp_point_256* rt;
#ifndef WC_NO_CACHE_RESISTANT
    sp_point_256* p;
#endif
    sp_digit* tmp;
    sp_digit n;
    int i;
    int c, y;
    int err;

    /* Constant time used for cache attack resistance implementation. */
    (void)ct;
    (void)heap;

    err = sp_256_point_new_8(heap, rtd, rt);
#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
#ifndef WC_NO_CACHE_RESISTANT
    t = (sp_point_256*)XMALLOC(sizeof(sp_point_256) * 17, heap, DYNAMIC_TYPE_ECC);
#else
    t = (sp_point_256*)XMALLOC(sizeof(sp_point_256) * 16, heap, DYNAMIC_TYPE_ECC);
#endif
    if (t == NULL)
        err = MEMORY_E;
    tmp = (sp_digit*)XMALLOC(sizeof(sp_digit) * 2 * 8 * 5, heap,
                             DYNAMIC_TYPE_ECC);
    if (tmp == NULL)
        err = MEMORY_E;
#else
    t = td;
    tmp = tmpd;
#endif

    if (err == MP_OKAY) {
#ifndef WC_NO_CACHE_RESISTANT
    #if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
        p = t + 16;
    #else
        p = &pd;
    #endif
#endif
        /* t[0] = {0, 0, 1} * norm */
        XMEMSET(&t[0], 0, sizeof(t[0]));
        t[0].infinity = 1;
        /* t[1] = {g->x, g->y, g->z} * norm */
        (void)sp_256_mod_mul_norm_8(t[1].x, g->x, p256_mod);
        (void)sp_256_mod_mul_norm_8(t[1].y, g->y, p256_mod);
        (void)sp_256_mod_mul_norm_8(t[1].z, g->z, p256_mod);
        t[1].infinity = 0;
        sp_256_proj_point_dbl_8(&t[ 2], &t[ 1], tmp);
        t[ 2].infinity = 0;
        sp_256_proj_point_add_8(&t[ 3], &t[ 2], &t[ 1], tmp);
        t[ 3].infinity = 0;
        sp_256_proj_point_dbl_8(&t[ 4], &t[ 2], tmp);
        t[ 4].infinity = 0;
        sp_256_proj_point_add_8(&t[ 5], &t[ 3], &t[ 2], tmp);
        t[ 5].infinity = 0;
        sp_256_proj_point_dbl_8(&t[ 6], &t[ 3], tmp);
        t[ 6].infinity = 0;
        sp_256_proj_point_add_8(&t[ 7], &t[ 4], &t[ 3], tmp);
        t[ 7].infinity = 0;
        sp_256_proj_point_dbl_8(&t[ 8], &t[ 4], tmp);
        t[ 8].infinity = 0;
        sp_256_proj_point_add_8(&t[ 9], &t[ 5], &t[ 4], tmp);
        t[ 9].infinity = 0;
        sp_256_proj_point_dbl_8(&t[10], &t[ 5], tmp);
        t[10].infinity = 0;
        sp_256_proj_point_add_8(&t[11], &t[ 6], &t[ 5], tmp);
        t[11].infinity = 0;
        sp_256_proj_point_dbl_8(&t[12], &t[ 6], tmp);
        t[12].infinity = 0;
        sp_256_proj_point_add_8(&t[13], &t[ 7], &t[ 6], tmp);
        t[13].infinity = 0;
        sp_256_proj_point_dbl_8(&t[14], &t[ 7], tmp);
        t[14].infinity = 0;
        sp_256_proj_point_add_8(&t[15], &t[ 8], &t[ 7], tmp);
        t[15].infinity = 0;

        i = 6;
        n = k[i+1] << 0;
        c = 28;
        y = n >> 28;
    #ifndef WC_NO_CACHE_RESISTANT
        if (ct) {
            sp_256_get_point_16_8(rt, t, y);
            rt->infinity = !y;
        }
        else
    #endif
        {
            XMEMCPY(rt, &t[y], sizeof(sp_point_256));
        }
        n <<= 4;
        for (; i>=0 || c>=4; ) {
            if (c < 4) {
                n |= k[i--];
                c += 32;
            }
            y = (n >> 28) & 0xf;
            n <<= 4;
            c -= 4;

            sp_256_proj_point_dbl_8(rt, rt, tmp);
            sp_256_proj_point_dbl_8(rt, rt, tmp);
            sp_256_proj_point_dbl_8(rt, rt, tmp);
            sp_256_proj_point_dbl_8(rt, rt, tmp);

    #ifndef WC_NO_CACHE_RESISTANT
            if (ct) {
                sp_256_get_point_16_8(p, t, y);
                p->infinity = !y;
                sp_256_proj_point_add_8(rt, rt, p, tmp);
            }
            else
    #endif
            {
                sp_256_proj_point_add_8(rt, rt, &t[y], tmp);
            }
        }

        if (map != 0) {
            sp_256_map_8(r, rt, tmp);
        }
        else {
            XMEMCPY(r, rt, sizeof(sp_point_256));
        }
    }

#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (tmp != NULL) {
        XMEMSET(tmp, 0, sizeof(sp_digit) * 2 * 8 * 5);
        XFREE(tmp, heap, DYNAMIC_TYPE_ECC);
    }
    if (t != NULL) {
        XMEMSET(t, 0, sizeof(sp_point_256) * 16);
        XFREE(t, heap, DYNAMIC_TYPE_ECC);
    }
#else
    ForceZero(tmpd, sizeof(tmpd));
    ForceZero(td, sizeof(td));
#endif
    sp_256_point_free_8(rt, 1, heap);

    return err;
}

/* A table entry for pre-computed points. */
typedef struct sp_table_entry_256 {
    sp_digit x[8];
    sp_digit y[8];
} sp_table_entry_256;

#ifdef FP_ECC
/* Double the Montgomery form projective point p a number of times.
 *
 * r  Result of repeated doubling of point.
 * p  Point to double.
 * n  Number of times to double
 * t  Temporary ordinate data.
 */
static void sp_256_proj_point_dbl_n_8(sp_point_256* p, int n, sp_digit* t)
{
    sp_digit* w = t;
    sp_digit* a = t + 2*8;
    sp_digit* b = t + 4*8;
    sp_digit* t1 = t + 6*8;
    sp_digit* t2 = t + 8*8;
    sp_digit* x;
    sp_digit* y;
    sp_digit* z;

    x = p->x;
    y = p->y;
    z = p->z;

    /* Y = 2*Y */
    sp_256_mont_dbl_8(y, y, p256_mod);
    /* W = Z^4 */
    sp_256_mont_sqr_8(w, z, p256_mod, p256_mp_mod);
    sp_256_mont_sqr_8(w, w, p256_mod, p256_mp_mod);

#ifndef WOLFSSL_SP_SMALL
    while (--n > 0)
#else
    while (--n >= 0)
#endif
    {
        /* A = 3*(X^2 - W) */
        sp_256_mont_sqr_8(t1, x, p256_mod, p256_mp_mod);
        sp_256_mont_sub_8(t1, t1, w, p256_mod);
        sp_256_mont_tpl_8(a, t1, p256_mod);
        /* B = X*Y^2 */
        sp_256_mont_sqr_8(t1, y, p256_mod, p256_mp_mod);
        sp_256_mont_mul_8(b, t1, x, p256_mod, p256_mp_mod);
        /* X = A^2 - 2B */
        sp_256_mont_sqr_8(x, a, p256_mod, p256_mp_mod);
        sp_256_mont_dbl_8(t2, b, p256_mod);
        sp_256_mont_sub_8(x, x, t2, p256_mod);
        /* Z = Z*Y */
        sp_256_mont_mul_8(z, z, y, p256_mod, p256_mp_mod);
        /* t2 = Y^4 */
        sp_256_mont_sqr_8(t1, t1, p256_mod, p256_mp_mod);
#ifdef WOLFSSL_SP_SMALL
        if (n != 0)
#endif
        {
            /* W = W*Y^4 */
            sp_256_mont_mul_8(w, w, t1, p256_mod, p256_mp_mod);
        }
        /* y = 2*A*(B - X) - Y^4 */
        sp_256_mont_sub_8(y, b, x, p256_mod);
        sp_256_mont_mul_8(y, y, a, p256_mod, p256_mp_mod);
        sp_256_mont_dbl_8(y, y, p256_mod);
        sp_256_mont_sub_8(y, y, t1, p256_mod);
    }
#ifndef WOLFSSL_SP_SMALL
    /* A = 3*(X^2 - W) */
    sp_256_mont_sqr_8(t1, x, p256_mod, p256_mp_mod);
    sp_256_mont_sub_8(t1, t1, w, p256_mod);
    sp_256_mont_tpl_8(a, t1, p256_mod);
    /* B = X*Y^2 */
    sp_256_mont_sqr_8(t1, y, p256_mod, p256_mp_mod);
    sp_256_mont_mul_8(b, t1, x, p256_mod, p256_mp_mod);
    /* X = A^2 - 2B */
    sp_256_mont_sqr_8(x, a, p256_mod, p256_mp_mod);
    sp_256_mont_dbl_8(t2, b, p256_mod);
    sp_256_mont_sub_8(x, x, t2, p256_mod);
    /* Z = Z*Y */
    sp_256_mont_mul_8(z, z, y, p256_mod, p256_mp_mod);
    /* t2 = Y^4 */
    sp_256_mont_sqr_8(t1, t1, p256_mod, p256_mp_mod);
    /* y = 2*A*(B - X) - Y^4 */
    sp_256_mont_sub_8(y, b, x, p256_mod);
    sp_256_mont_mul_8(y, y, a, p256_mod, p256_mp_mod);
    sp_256_mont_dbl_8(y, y, p256_mod);
    sp_256_mont_sub_8(y, y, t1, p256_mod);
#endif
    /* Y = Y/2 */
    sp_256_div2_8(y, y, p256_mod);
}

/* Convert the projective point to affine.
 * Ordinates are in Montgomery form.
 *
 * a  Point to convert.
 * t  Temporary data.
 */
static void sp_256_proj_to_affine_8(sp_point_256* a, sp_digit* t)
{
    sp_digit* t1 = t;
    sp_digit* t2 = t + 2 * 8;
    sp_digit* tmp = t + 4 * 8;

    sp_256_mont_inv_8(t1, a->z, tmp);

    sp_256_mont_sqr_8(t2, t1, p256_mod, p256_mp_mod);
    sp_256_mont_mul_8(t1, t2, t1, p256_mod, p256_mp_mod);

    sp_256_mont_mul_8(a->x, a->x, t2, p256_mod, p256_mp_mod);
    sp_256_mont_mul_8(a->y, a->y, t1, p256_mod, p256_mp_mod);
    XMEMCPY(a->z, p256_norm_mod, sizeof(p256_norm_mod));
}

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
static void sp_256_proj_point_add_qz1_8(sp_point_256* r, const sp_point_256* p,
        const sp_point_256* q, sp_digit* t)
{
    const sp_point_256* ap[2];
    sp_point_256* rp[2];
    sp_digit* t1 = t;
    sp_digit* t2 = t + 2*8;
    sp_digit* t3 = t + 4*8;
    sp_digit* t4 = t + 6*8;
    sp_digit* t5 = t + 8*8;
    sp_digit* x;
    sp_digit* y;
    sp_digit* z;
    int i;

    /* Check double */
    (void)sp_256_sub_8(t1, p256_mod, q->y);
    sp_256_norm_8(t1);
    if ((sp_256_cmp_equal_8(p->x, q->x) & sp_256_cmp_equal_8(p->z, q->z) &
        (sp_256_cmp_equal_8(p->y, q->y) | sp_256_cmp_equal_8(p->y, t1))) != 0) {
        sp_256_proj_point_dbl_8(r, p, t);
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
        for (i=0; i<8; i++) {
            r->x[i] = ap[p->infinity]->x[i];
        }
        for (i=0; i<8; i++) {
            r->y[i] = ap[p->infinity]->y[i];
        }
        for (i=0; i<8; i++) {
            r->z[i] = ap[p->infinity]->z[i];
        }
        r->infinity = ap[p->infinity]->infinity;

        /* U2 = X2*Z1^2 */
        sp_256_mont_sqr_8(t2, z, p256_mod, p256_mp_mod);
        sp_256_mont_mul_8(t4, t2, z, p256_mod, p256_mp_mod);
        sp_256_mont_mul_8(t2, t2, q->x, p256_mod, p256_mp_mod);
        /* S2 = Y2*Z1^3 */
        sp_256_mont_mul_8(t4, t4, q->y, p256_mod, p256_mp_mod);
        /* H = U2 - X1 */
        sp_256_mont_sub_8(t2, t2, x, p256_mod);
        /* R = S2 - Y1 */
        sp_256_mont_sub_8(t4, t4, y, p256_mod);
        /* Z3 = H*Z1 */
        sp_256_mont_mul_8(z, z, t2, p256_mod, p256_mp_mod);
        /* X3 = R^2 - H^3 - 2*X1*H^2 */
        sp_256_mont_sqr_8(t1, t4, p256_mod, p256_mp_mod);
        sp_256_mont_sqr_8(t5, t2, p256_mod, p256_mp_mod);
        sp_256_mont_mul_8(t3, x, t5, p256_mod, p256_mp_mod);
        sp_256_mont_mul_8(t5, t5, t2, p256_mod, p256_mp_mod);
        sp_256_mont_sub_8(x, t1, t5, p256_mod);
        sp_256_mont_dbl_8(t1, t3, p256_mod);
        sp_256_mont_sub_8(x, x, t1, p256_mod);
        /* Y3 = R*(X1*H^2 - X3) - Y1*H^3 */
        sp_256_mont_sub_8(t3, t3, x, p256_mod);
        sp_256_mont_mul_8(t3, t3, t4, p256_mod, p256_mp_mod);
        sp_256_mont_mul_8(t5, t5, y, p256_mod, p256_mp_mod);
        sp_256_mont_sub_8(y, t3, t5, p256_mod);
    }
}

#ifdef WOLFSSL_SP_SMALL
#ifdef FP_ECC
/* Generate the pre-computed table of points for the base point.
 *
 * a      The base point.
 * table  Place to store generated point data.
 * tmp    Temporary data.
 * heap  Heap to use for allocation.
 */
static int sp_256_gen_stripe_table_8(const sp_point_256* a,
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

    err = sp_256_point_new_8(heap, td, t);
    if (err == MP_OKAY) {
        err = sp_256_point_new_8(heap, s1d, s1);
    }
    if (err == MP_OKAY) {
        err = sp_256_point_new_8(heap, s2d, s2);
    }

    if (err == MP_OKAY) {
        err = sp_256_mod_mul_norm_8(t->x, a->x, p256_mod);
    }
    if (err == MP_OKAY) {
        err = sp_256_mod_mul_norm_8(t->y, a->y, p256_mod);
    }
    if (err == MP_OKAY) {
        err = sp_256_mod_mul_norm_8(t->z, a->z, p256_mod);
    }
    if (err == MP_OKAY) {
        t->infinity = 0;
        sp_256_proj_to_affine_8(t, tmp);

        XMEMCPY(s1->z, p256_norm_mod, sizeof(p256_norm_mod));
        s1->infinity = 0;
        XMEMCPY(s2->z, p256_norm_mod, sizeof(p256_norm_mod));
        s2->infinity = 0;

        /* table[0] = {0, 0, infinity} */
        XMEMSET(&table[0], 0, sizeof(sp_table_entry_256));
        /* table[1] = Affine version of 'a' in Montgomery form */
        XMEMCPY(table[1].x, t->x, sizeof(table->x));
        XMEMCPY(table[1].y, t->y, sizeof(table->y));

        for (i=1; i<4; i++) {
            sp_256_proj_point_dbl_n_8(t, 64, tmp);
            sp_256_proj_to_affine_8(t, tmp);
            XMEMCPY(table[1<<i].x, t->x, sizeof(table->x));
            XMEMCPY(table[1<<i].y, t->y, sizeof(table->y));
        }

        for (i=1; i<4; i++) {
            XMEMCPY(s1->x, table[1<<i].x, sizeof(table->x));
            XMEMCPY(s1->y, table[1<<i].y, sizeof(table->y));
            for (j=(1<<i)+1; j<(1<<(i+1)); j++) {
                XMEMCPY(s2->x, table[j-(1<<i)].x, sizeof(table->x));
                XMEMCPY(s2->y, table[j-(1<<i)].y, sizeof(table->y));
                sp_256_proj_point_add_qz1_8(t, s1, s2, tmp);
                sp_256_proj_to_affine_8(t, tmp);
                XMEMCPY(table[j].x, t->x, sizeof(table->x));
                XMEMCPY(table[j].y, t->y, sizeof(table->y));
            }
        }
    }

    sp_256_point_free_8(s2, 0, heap);
    sp_256_point_free_8(s1, 0, heap);
    sp_256_point_free_8( t, 0, heap);

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
static void sp_256_get_entry_16_8(sp_point_256* r,
    const sp_table_entry_256* table, int idx)
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
    r->x[7] = 0;
    r->y[0] = 0;
    r->y[1] = 0;
    r->y[2] = 0;
    r->y[3] = 0;
    r->y[4] = 0;
    r->y[5] = 0;
    r->y[6] = 0;
    r->y[7] = 0;
    for (i = 1; i < 16; i++) {
        mask = 0 - (i == idx);
        r->x[0] |= mask & table[i].x[0];
        r->x[1] |= mask & table[i].x[1];
        r->x[2] |= mask & table[i].x[2];
        r->x[3] |= mask & table[i].x[3];
        r->x[4] |= mask & table[i].x[4];
        r->x[5] |= mask & table[i].x[5];
        r->x[6] |= mask & table[i].x[6];
        r->x[7] |= mask & table[i].x[7];
        r->y[0] |= mask & table[i].y[0];
        r->y[1] |= mask & table[i].y[1];
        r->y[2] |= mask & table[i].y[2];
        r->y[3] |= mask & table[i].y[3];
        r->y[4] |= mask & table[i].y[4];
        r->y[5] |= mask & table[i].y[5];
        r->y[6] |= mask & table[i].y[6];
        r->y[7] |= mask & table[i].y[7];
    }
}
#endif /* !WC_NO_CACHE_RESISTANT */
/* Multiply the point by the scalar and return the result.
 * If map is true then convert result to affine coordinates.
 *
 * Implementation uses striping of bits.
 * Choose bits 4 bits apart.
 *
 * r      Resulting point.
 * k      Scalar to multiply by.
 * table  Pre-computed table.
 * map    Indicates whether to convert result to affine.
 * ct     Constant time required.
 * heap   Heap to use for allocation.
 * returns MEMORY_E when memory allocation fails and MP_OKAY on success.
 */
static int sp_256_ecc_mulmod_stripe_8(sp_point_256* r, const sp_point_256* g,
        const sp_table_entry_256* table, const sp_digit* k, int map,
        int ct, void* heap)
{
#if (!defined(WOLFSSL_SP_SMALL) && !defined(WOLFSSL_SMALL_STACK)) || defined(WOLFSSL_SP_NO_MALLOC)
    sp_point_256 rtd;
    sp_point_256 pd;
    sp_digit td[2 * 8 * 5];
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


    err = sp_256_point_new_8(heap, rtd, rt);
    if (err == MP_OKAY) {
        err = sp_256_point_new_8(heap, pd, p);
    }
#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    t = (sp_digit*)XMALLOC(sizeof(sp_digit) * 2 * 8 * 5, heap,
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
        for (j=0,x=63; j<4; j++,x+=64) {
            y |= ((k[x / 32] >> (x % 32)) & 1) << j;
        }
    #ifndef WC_NO_CACHE_RESISTANT
        if (ct) {
            sp_256_get_entry_16_8(rt, table, y);
        } else
    #endif
        {
            XMEMCPY(rt->x, table[y].x, sizeof(table[y].x));
            XMEMCPY(rt->y, table[y].y, sizeof(table[y].y));
        }
        rt->infinity = !y;
        for (i=62; i>=0; i--) {
            y = 0;
            for (j=0,x=i; j<4; j++,x+=64) {
                y |= ((k[x / 32] >> (x % 32)) & 1) << j;
            }

            sp_256_proj_point_dbl_8(rt, rt, t);
        #ifndef WC_NO_CACHE_RESISTANT
            if (ct) {
                sp_256_get_entry_16_8(p, table, y);
            }
            else
        #endif
            {
                XMEMCPY(p->x, table[y].x, sizeof(table[y].x));
                XMEMCPY(p->y, table[y].y, sizeof(table[y].y));
            }
            p->infinity = !y;
            sp_256_proj_point_add_qz1_8(rt, rt, p, t);
        }

        if (map != 0) {
            sp_256_map_8(r, rt, t);
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
    sp_256_point_free_8(p, 0, heap);
    sp_256_point_free_8(rt, 0, heap);

    return err;
}

#ifdef FP_ECC
#ifndef FP_ENTRIES
    #define FP_ENTRIES 16
#endif

typedef struct sp_cache_256_t {
    sp_digit x[8];
    sp_digit y[8];
    sp_table_entry_256 table[16];
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

        if (sp_256_cmp_equal_8(g->x, sp_cache_256[i].x) &
                           sp_256_cmp_equal_8(g->y, sp_cache_256[i].y)) {
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
static int sp_256_ecc_mulmod_8(sp_point_256* r, const sp_point_256* g, const sp_digit* k,
        int map, int ct, void* heap)
{
#ifndef FP_ECC
    return sp_256_ecc_mulmod_fast_8(r, g, k, map, ct, heap);
#else
    sp_digit tmp[2 * 8 * 5];
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
            sp_256_gen_stripe_table_8(g, cache->table, tmp, heap);

#ifndef HAVE_THREAD_LS
        wc_UnLockMutex(&sp_cache_256_lock);
#endif /* HAVE_THREAD_LS */

        if (cache->cnt < 2) {
            err = sp_256_ecc_mulmod_fast_8(r, g, k, map, ct, heap);
        }
        else {
            err = sp_256_ecc_mulmod_stripe_8(r, g, cache->table, k,
                    map, ct, heap);
        }
    }

    return err;
#endif
}

#else
#ifdef FP_ECC
/* Generate the pre-computed table of points for the base point.
 *
 * a      The base point.
 * table  Place to store generated point data.
 * tmp    Temporary data.
 * heap  Heap to use for allocation.
 */
static int sp_256_gen_stripe_table_8(const sp_point_256* a,
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

    err = sp_256_point_new_8(heap, td, t);
    if (err == MP_OKAY) {
        err = sp_256_point_new_8(heap, s1d, s1);
    }
    if (err == MP_OKAY) {
        err = sp_256_point_new_8(heap, s2d, s2);
    }

    if (err == MP_OKAY) {
        err = sp_256_mod_mul_norm_8(t->x, a->x, p256_mod);
    }
    if (err == MP_OKAY) {
        err = sp_256_mod_mul_norm_8(t->y, a->y, p256_mod);
    }
    if (err == MP_OKAY) {
        err = sp_256_mod_mul_norm_8(t->z, a->z, p256_mod);
    }
    if (err == MP_OKAY) {
        t->infinity = 0;
        sp_256_proj_to_affine_8(t, tmp);

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
            sp_256_proj_point_dbl_n_8(t, 32, tmp);
            sp_256_proj_to_affine_8(t, tmp);
            XMEMCPY(table[1<<i].x, t->x, sizeof(table->x));
            XMEMCPY(table[1<<i].y, t->y, sizeof(table->y));
        }

        for (i=1; i<8; i++) {
            XMEMCPY(s1->x, table[1<<i].x, sizeof(table->x));
            XMEMCPY(s1->y, table[1<<i].y, sizeof(table->y));
            for (j=(1<<i)+1; j<(1<<(i+1)); j++) {
                XMEMCPY(s2->x, table[j-(1<<i)].x, sizeof(table->x));
                XMEMCPY(s2->y, table[j-(1<<i)].y, sizeof(table->y));
                sp_256_proj_point_add_qz1_8(t, s1, s2, tmp);
                sp_256_proj_to_affine_8(t, tmp);
                XMEMCPY(table[j].x, t->x, sizeof(table->x));
                XMEMCPY(table[j].y, t->y, sizeof(table->y));
            }
        }
    }

    sp_256_point_free_8(s2, 0, heap);
    sp_256_point_free_8(s1, 0, heap);
    sp_256_point_free_8( t, 0, heap);

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
static void sp_256_get_entry_256_8(sp_point_256* r,
    const sp_table_entry_256* table, int idx)
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
    r->x[7] = 0;
    r->y[0] = 0;
    r->y[1] = 0;
    r->y[2] = 0;
    r->y[3] = 0;
    r->y[4] = 0;
    r->y[5] = 0;
    r->y[6] = 0;
    r->y[7] = 0;
    for (i = 1; i < 256; i++) {
        mask = 0 - (i == idx);
        r->x[0] |= mask & table[i].x[0];
        r->x[1] |= mask & table[i].x[1];
        r->x[2] |= mask & table[i].x[2];
        r->x[3] |= mask & table[i].x[3];
        r->x[4] |= mask & table[i].x[4];
        r->x[5] |= mask & table[i].x[5];
        r->x[6] |= mask & table[i].x[6];
        r->x[7] |= mask & table[i].x[7];
        r->y[0] |= mask & table[i].y[0];
        r->y[1] |= mask & table[i].y[1];
        r->y[2] |= mask & table[i].y[2];
        r->y[3] |= mask & table[i].y[3];
        r->y[4] |= mask & table[i].y[4];
        r->y[5] |= mask & table[i].y[5];
        r->y[6] |= mask & table[i].y[6];
        r->y[7] |= mask & table[i].y[7];
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
static int sp_256_ecc_mulmod_stripe_8(sp_point_256* r, const sp_point_256* g,
        const sp_table_entry_256* table, const sp_digit* k, int map,
        int ct, void* heap)
{
#if (!defined(WOLFSSL_SP_SMALL) && !defined(WOLFSSL_SMALL_STACK)) || defined(WOLFSSL_SP_NO_MALLOC)
    sp_point_256 rtd;
    sp_point_256 pd;
    sp_digit td[2 * 8 * 5];
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


    err = sp_256_point_new_8(heap, rtd, rt);
    if (err == MP_OKAY) {
        err = sp_256_point_new_8(heap, pd, p);
    }
#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    t = (sp_digit*)XMALLOC(sizeof(sp_digit) * 2 * 8 * 5, heap,
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
            y |= ((k[x / 32] >> (x % 32)) & 1) << j;
        }
    #ifndef WC_NO_CACHE_RESISTANT
        if (ct) {
            sp_256_get_entry_256_8(rt, table, y);
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
                y |= ((k[x / 32] >> (x % 32)) & 1) << j;
            }

            sp_256_proj_point_dbl_8(rt, rt, t);
        #ifndef WC_NO_CACHE_RESISTANT
            if (ct) {
                sp_256_get_entry_256_8(p, table, y);
            }
            else
        #endif
            {
                XMEMCPY(p->x, table[y].x, sizeof(table[y].x));
                XMEMCPY(p->y, table[y].y, sizeof(table[y].y));
            }
            p->infinity = !y;
            sp_256_proj_point_add_qz1_8(rt, rt, p, t);
        }

        if (map != 0) {
            sp_256_map_8(r, rt, t);
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
    sp_256_point_free_8(p, 0, heap);
    sp_256_point_free_8(rt, 0, heap);

    return err;
}

#ifdef FP_ECC
#ifndef FP_ENTRIES
    #define FP_ENTRIES 16
#endif

typedef struct sp_cache_256_t {
    sp_digit x[8];
    sp_digit y[8];
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

        if (sp_256_cmp_equal_8(g->x, sp_cache_256[i].x) &
                           sp_256_cmp_equal_8(g->y, sp_cache_256[i].y)) {
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
static int sp_256_ecc_mulmod_8(sp_point_256* r, const sp_point_256* g, const sp_digit* k,
        int map, int ct, void* heap)
{
#ifndef FP_ECC
    return sp_256_ecc_mulmod_fast_8(r, g, k, map, ct, heap);
#else
    sp_digit tmp[2 * 8 * 5];
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
            sp_256_gen_stripe_table_8(g, cache->table, tmp, heap);

#ifndef HAVE_THREAD_LS
        wc_UnLockMutex(&sp_cache_256_lock);
#endif /* HAVE_THREAD_LS */

        if (cache->cnt < 2) {
            err = sp_256_ecc_mulmod_fast_8(r, g, k, map, ct, heap);
        }
        else {
            err = sp_256_ecc_mulmod_stripe_8(r, g, cache->table, k,
                    map, ct, heap);
        }
    }

    return err;
#endif
}

#endif /* WOLFSSL_SP_SMALL */
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
    sp_digit kd[8];
#endif
    sp_point_256* point;
    sp_digit* k = NULL;
    int err = MP_OKAY;

    err = sp_256_point_new_8(heap, p, point);
#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (err == MP_OKAY) {
        k = (sp_digit*)XMALLOC(sizeof(sp_digit) * 8, heap,
                                                              DYNAMIC_TYPE_ECC);
        if (k == NULL)
            err = MEMORY_E;
    }
#else
    k = kd;
#endif
    if (err == MP_OKAY) {
        sp_256_from_mp(k, 8, km);
        sp_256_point_from_ecc_point_8(point, gm);

            err = sp_256_ecc_mulmod_8(point, point, k, map, 1, heap);
    }
    if (err == MP_OKAY) {
        err = sp_256_point_to_ecc_point_8(point, r);
    }

#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (k != NULL) {
        XFREE(k, heap, DYNAMIC_TYPE_ECC);
    }
#endif
    sp_256_point_free_8(point, 0, heap);

    return err;
}

#ifdef WOLFSSL_SP_SMALL
static const sp_table_entry_256 p256_table[16] = {
    /* 0 */
    { { 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00 },
      { 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00 } },
    /* 1 */
    { { 0x18a9143c,0x79e730d4,0x5fedb601,0x75ba95fc,0x77622510,0x79fb732b,
        0xa53755c6,0x18905f76 },
      { 0xce95560a,0xddf25357,0xba19e45c,0x8b4ab8e4,0xdd21f325,0xd2e88688,
        0x25885d85,0x8571ff18 } },
    /* 2 */
    { { 0x16a0d2bb,0x4f922fc5,0x1a623499,0x0d5cc16c,0x57c62c8b,0x9241cf3a,
        0xfd1b667f,0x2f5e6961 },
      { 0xf5a01797,0x5c15c70b,0x60956192,0x3d20b44d,0x071fdb52,0x04911b37,
        0x8d6f0f7b,0xf648f916 } },
    /* 3 */
    { { 0xe137bbbc,0x9e566847,0x8a6a0bec,0xe434469e,0x79d73463,0xb1c42761,
        0x133d0015,0x5abe0285 },
      { 0xc04c7dab,0x92aa837c,0x43260c07,0x573d9f4c,0x78e6cc37,0x0c931562,
        0x6b6f7383,0x94bb725b } },
    /* 4 */
    { { 0xbfe20925,0x62a8c244,0x8fdce867,0x91c19ac3,0xdd387063,0x5a96a5d5,
        0x21d324f6,0x61d587d4 },
      { 0xa37173ea,0xe87673a2,0x53778b65,0x23848008,0x05bab43e,0x10f8441e,
        0x4621efbe,0xfa11fe12 } },
    /* 5 */
    { { 0x2cb19ffd,0x1c891f2b,0xb1923c23,0x01ba8d5b,0x8ac5ca8e,0xb6d03d67,
        0x1f13bedc,0x586eb04c },
      { 0x27e8ed09,0x0c35c6e5,0x1819ede2,0x1e81a33c,0x56c652fa,0x278fd6c0,
        0x70864f11,0x19d5ac08 } },
    /* 6 */
    { { 0xd2b533d5,0x62577734,0xa1bdddc0,0x673b8af6,0xa79ec293,0x577e7c9a,
        0xc3b266b1,0xbb6de651 },
      { 0xb65259b3,0xe7e9303a,0xd03a7480,0xd6a0afd3,0x9b3cfc27,0xc5ac83d1,
        0x5d18b99b,0x60b4619a } },
    /* 7 */
    { { 0x1ae5aa1c,0xbd6a38e1,0x49e73658,0xb8b7652b,0xee5f87ed,0x0b130014,
        0xaeebffcd,0x9d0f27b2 },
      { 0x7a730a55,0xca924631,0xddbbc83a,0x9c955b2f,0xac019a71,0x07c1dfe0,
        0x356ec48d,0x244a566d } },
    /* 8 */
    { { 0xf4f8b16a,0x56f8410e,0xc47b266a,0x97241afe,0x6d9c87c1,0x0a406b8e,
        0xcd42ab1b,0x803f3e02 },
      { 0x04dbec69,0x7f0309a8,0x3bbad05f,0xa83b85f7,0xad8e197f,0xc6097273,
        0x5067adc1,0xc097440e } },
    /* 9 */
    { { 0xc379ab34,0x846a56f2,0x841df8d1,0xa8ee068b,0x176c68ef,0x20314459,
        0x915f1f30,0xf1af32d5 },
      { 0x5d75bd50,0x99c37531,0xf72f67bc,0x837cffba,0x48d7723f,0x0613a418,
        0xe2d41c8b,0x23d0f130 } },
    /* 10 */
    { { 0xd5be5a2b,0xed93e225,0x5934f3c6,0x6fe79983,0x22626ffc,0x43140926,
        0x7990216a,0x50bbb4d9 },
      { 0xe57ec63e,0x378191c6,0x181dcdb2,0x65422c40,0x0236e0f6,0x41a8099b,
        0x01fe49c3,0x2b100118 } },
    /* 11 */
    { { 0x9b391593,0xfc68b5c5,0x598270fc,0xc385f5a2,0xd19adcbb,0x7144f3aa,
        0x83fbae0c,0xdd558999 },
      { 0x74b82ff4,0x93b88b8e,0x71e734c9,0xd2e03c40,0x43c0322a,0x9a7a9eaf,
        0x149d6041,0xe6e4c551 } },
    /* 12 */
    { { 0x80ec21fe,0x5fe14bfe,0xc255be82,0xf6ce116a,0x2f4a5d67,0x98bc5a07,
        0xdb7e63af,0xfad27148 },
      { 0x29ab05b3,0x90c0b6ac,0x4e251ae6,0x37a9a83c,0xc2aade7d,0x0a7dc875,
        0x9f0e1a84,0x77387de3 } },
    /* 13 */
    { { 0xa56c0dd7,0x1e9ecc49,0x46086c74,0xa5cffcd8,0xf505aece,0x8f7a1408,
        0xbef0c47e,0xb37b85c0 },
      { 0xcc0e6a8f,0x3596b6e4,0x6b388f23,0xfd6d4bbf,0xc39cef4e,0xaba453fa,
        0xf9f628d5,0x9c135ac8 } },
    /* 14 */
    { { 0x95c8f8be,0x0a1c7294,0x3bf362bf,0x2961c480,0xdf63d4ac,0x9e418403,
        0x91ece900,0xc109f9cb },
      { 0x58945705,0xc2d095d0,0xddeb85c0,0xb9083d96,0x7a40449b,0x84692b8d,
        0x2eee1ee1,0x9bc3344f } },
    /* 15 */
    { { 0x42913074,0x0d5ae356,0x48a542b1,0x55491b27,0xb310732a,0x469ca665,
        0x5f1a4cc1,0x29591d52 },
      { 0xb84f983f,0xe76f5b6b,0x9f5f84e1,0xbe7eef41,0x80baa189,0x1200d496,
        0x18ef332c,0x6376551f } },
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
static int sp_256_ecc_mulmod_base_8(sp_point_256* r, const sp_digit* k,
        int map, int ct, void* heap)
{
    return sp_256_ecc_mulmod_stripe_8(r, &p256_base, p256_table,
                                      k, map, ct, heap);
}

#else
static const sp_table_entry_256 p256_table[256] = {
    /* 0 */
    { { 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00 },
      { 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00 } },
    /* 1 */
    { { 0x18a9143c,0x79e730d4,0x5fedb601,0x75ba95fc,0x77622510,0x79fb732b,
        0xa53755c6,0x18905f76 },
      { 0xce95560a,0xddf25357,0xba19e45c,0x8b4ab8e4,0xdd21f325,0xd2e88688,
        0x25885d85,0x8571ff18 } },
    /* 2 */
    { { 0x4147519a,0x20288602,0x26b372f0,0xd0981eac,0xa785ebc8,0xa9d4a7ca,
        0xdbdf58e9,0xd953c50d },
      { 0xfd590f8f,0x9d6361cc,0x44e6c917,0x72e9626b,0x22eb64cf,0x7fd96110,
        0x9eb288f3,0x863ebb7e } },
    /* 3 */
    { { 0x5cdb6485,0x7856b623,0x2f0a2f97,0x808f0ea2,0x4f7e300b,0x3e68d954,
        0xb5ff80a0,0x00076055 },
      { 0x838d2010,0x7634eb9b,0x3243708a,0x54014fbb,0x842a6606,0xe0e47d39,
        0x34373ee0,0x83087761 } },
    /* 4 */
    { { 0x16a0d2bb,0x4f922fc5,0x1a623499,0x0d5cc16c,0x57c62c8b,0x9241cf3a,
        0xfd1b667f,0x2f5e6961 },
      { 0xf5a01797,0x5c15c70b,0x60956192,0x3d20b44d,0x071fdb52,0x04911b37,
        0x8d6f0f7b,0xf648f916 } },
    /* 5 */
    { { 0xe137bbbc,0x9e566847,0x8a6a0bec,0xe434469e,0x79d73463,0xb1c42761,
        0x133d0015,0x5abe0285 },
      { 0xc04c7dab,0x92aa837c,0x43260c07,0x573d9f4c,0x78e6cc37,0x0c931562,
        0x6b6f7383,0x94bb725b } },
    /* 6 */
    { { 0x720f141c,0xbbf9b48f,0x2df5bc74,0x6199b3cd,0x411045c4,0xdc3f6129,
        0x2f7dc4ef,0xcdd6bbcb },
      { 0xeaf436fd,0xcca6700b,0xb99326be,0x6f647f6d,0x014f2522,0x0c0fa792,
        0x4bdae5f6,0xa361bebd } },
    /* 7 */
    { { 0x597c13c7,0x28aa2558,0x50b7c3e1,0xc38d635f,0xf3c09d1d,0x07039aec,
        0xc4b5292c,0xba12ca09 },
      { 0x59f91dfd,0x9e408fa4,0xceea07fb,0x3af43b66,0x9d780b29,0x1eceb089,
        0x701fef4b,0x53ebb99d } },
    /* 8 */
    { { 0xb0e63d34,0x4fe7ee31,0xa9e54fab,0xf4600572,0xd5e7b5a4,0xc0493334,
        0x06d54831,0x8589fb92 },
      { 0x6583553a,0xaa70f5cc,0xe25649e5,0x0879094a,0x10044652,0xcc904507,
        0x02541c4f,0xebb0696d } },
    /* 9 */
    { { 0xac1647c5,0x4616ca15,0xc4cf5799,0xb8127d47,0x764dfbac,0xdc666aa3,
        0xd1b27da3,0xeb2820cb },
      { 0x6a87e008,0x9406f8d8,0x922378f3,0xd87dfa9d,0x80ccecb2,0x56ed2e42,
        0x55a7da1d,0x1f28289b } },
    /* 10 */
    { { 0x3b89da99,0xabbaa0c0,0xb8284022,0xa6f2d79e,0xb81c05e8,0x27847862,
        0x05e54d63,0x337a4b59 },
      { 0x21f7794a,0x3c67500d,0x7d6d7f61,0x207005b7,0x04cfd6e8,0x0a5a3781,
        0xf4c2fbd6,0x0d65e0d5 } },
    /* 11 */
    { { 0xb5275d38,0xd9d09bbe,0x0be0a358,0x4268a745,0x973eb265,0xf0762ff4,
        0x52f4a232,0xc23da242 },
      { 0x0b94520c,0x5da1b84f,0xb05bd78e,0x09666763,0x94d29ea1,0x3a4dcb86,
        0xc790cff1,0x19de3b8c } },
    /* 12 */
    { { 0x26c5fe04,0x183a716c,0x3bba1bdb,0x3b28de0b,0xa4cb712c,0x7432c586,
        0x91fccbfd,0xe34dcbd4 },
      { 0xaaa58403,0xb408d46b,0x82e97a53,0x9a697486,0x36aaa8af,0x9e390127,
        0x7b4e0f7f,0xe7641f44 } },
    /* 13 */
    { { 0xdf64ba59,0x7d753941,0x0b0242fc,0xd33f10ec,0xa1581859,0x4f06dfc6,
        0x052a57bf,0x4a12df57 },
      { 0x9439dbd0,0xbfa6338f,0xbde53e1f,0xd3c24bd4,0x21f1b314,0xfd5e4ffa,
        0xbb5bea46,0x6af5aa93 } },
    /* 14 */
    { { 0x10c91999,0xda10b699,0x2a580491,0x0a24b440,0xb8cc2090,0x3e0094b4,
        0x66a44013,0x5fe3475a },
      { 0xf93e7b4b,0xb0f8cabd,0x7c23f91a,0x292b501a,0xcd1e6263,0x42e889ae,
        0xecfea916,0xb544e308 } },
    /* 15 */
    { { 0x16ddfdce,0x6478c6e9,0xf89179e6,0x2c329166,0x4d4e67e1,0x4e8d6e76,
        0xa6b0c20b,0xe0b6b2bd },
      { 0xbb7efb57,0x0d312df2,0x790c4007,0x1aac0dde,0x679bc944,0xf90336ad,
        0x25a63774,0x71c023de } },
    /* 16 */
    { { 0xbfe20925,0x62a8c244,0x8fdce867,0x91c19ac3,0xdd387063,0x5a96a5d5,
        0x21d324f6,0x61d587d4 },
      { 0xa37173ea,0xe87673a2,0x53778b65,0x23848008,0x05bab43e,0x10f8441e,
        0x4621efbe,0xfa11fe12 } },
    /* 17 */
    { { 0x2cb19ffd,0x1c891f2b,0xb1923c23,0x01ba8d5b,0x8ac5ca8e,0xb6d03d67,
        0x1f13bedc,0x586eb04c },
      { 0x27e8ed09,0x0c35c6e5,0x1819ede2,0x1e81a33c,0x56c652fa,0x278fd6c0,
        0x70864f11,0x19d5ac08 } },
    /* 18 */
    { { 0x309a4e1f,0x1e99f581,0xe9270074,0xab7de71b,0xefd28d20,0x26a5ef0b,
        0x7f9c563f,0xe7c0073f },
      { 0x0ef59f76,0x1f6d663a,0x20fcb050,0x669b3b54,0x7a6602d4,0xc08c1f7a,
        0xc65b3c0a,0xe08504fe } },
    /* 19 */
    { { 0xa031b3ca,0xf098f68d,0xe6da6d66,0x6d1cab9e,0x94f246e8,0x5bfd81fa,
        0x5b0996b4,0x78f01882 },
      { 0x3a25787f,0xb7eefde4,0x1dccac9b,0x8016f80d,0xb35bfc36,0x0cea4877,
        0x7e94747a,0x43a773b8 } },
    /* 20 */
    { { 0xd2b533d5,0x62577734,0xa1bdddc0,0x673b8af6,0xa79ec293,0x577e7c9a,
        0xc3b266b1,0xbb6de651 },
      { 0xb65259b3,0xe7e9303a,0xd03a7480,0xd6a0afd3,0x9b3cfc27,0xc5ac83d1,
        0x5d18b99b,0x60b4619a } },
    /* 21 */
    { { 0x1ae5aa1c,0xbd6a38e1,0x49e73658,0xb8b7652b,0xee5f87ed,0x0b130014,
        0xaeebffcd,0x9d0f27b2 },
      { 0x7a730a55,0xca924631,0xddbbc83a,0x9c955b2f,0xac019a71,0x07c1dfe0,
        0x356ec48d,0x244a566d } },
    /* 22 */
    { { 0xeacf1f96,0x6db0394a,0x024c271c,0x9f2122a9,0x82cbd3b9,0x2626ac1b,
        0x3581ef69,0x45e58c87 },
      { 0xa38f9dbc,0xd3ff479d,0xe888a040,0xa8aaf146,0x46e0bed7,0x945adfb2,
        0xc1e4b7a4,0xc040e21c } },
    /* 23 */
    { { 0x6f8117b6,0x847af000,0x73a35433,0x651969ff,0x1d9475eb,0x482b3576,
        0x682c6ec7,0x1cdf5c97 },
      { 0x11f04839,0x7db775b4,0x48de1698,0x7dbeacf4,0xb70b3219,0xb2921dd1,
        0xa92dff3d,0x046755f8 } },
    /* 24 */
    { { 0xbce8ffcd,0xcc8ac5d2,0x2fe61a82,0x0d53c48b,0x7202d6c7,0xf6f16172,
        0x3b83a5f3,0x046e5e11 },
      { 0xd8007f01,0xe7b8ff64,0x5af43183,0x7fb1ef12,0x35e1a03c,0x045c5ea6,
        0x303d005b,0x6e0106c3 } },
    /* 25 */
    { { 0x88dd73b1,0x48c73584,0x995ed0d9,0x7670708f,0xc56a2ab7,0x38385ea8,
        0xe901cf1f,0x442594ed },
      { 0x12d4b65b,0xf8faa2c9,0x96c90c37,0x94c2343b,0x5e978d1f,0xd326e4a1,
        0x4c2ee68e,0xa796fa51 } },
    /* 26 */
    { { 0x823addd7,0x359fb604,0xe56693b3,0x9e2a6183,0x3cbf3c80,0xf885b78e,
        0xc69766e9,0xe4ad2da9 },
      { 0x8e048a61,0x357f7f42,0xc092d9a0,0x082d198c,0xc03ed8ef,0xfc3a1af4,
        0xc37b5143,0xc5e94046 } },
    /* 27 */
    { { 0x2be75f9e,0x476a538c,0xcb123a78,0x6fd1a9e8,0xb109c04b,0xd85e4df0,
        0xdb464747,0x63283daf },
      { 0xbaf2df15,0xce728cf7,0x0ad9a7f4,0xe592c455,0xe834bcc3,0xfab226ad,
        0x1981a938,0x68bd19ab } },
    /* 28 */
    { { 0x1887d659,0xc08ead51,0xb359305a,0x3374d5f4,0xcfe74fe3,0x96986981,
        0x3c6fdfd6,0x495292f5 },
      { 0x1acec896,0x4a878c9e,0xec5b4484,0xd964b210,0x664d60a7,0x6696f7e2,
        0x26036837,0x0ec7530d } },
    /* 29 */
    { { 0xad2687bb,0x2da13a05,0xf32e21fa,0xa1f83b6a,0x1dd4607b,0x390f5ef5,
        0x64863f0b,0x0f6207a6 },
      { 0x0f138233,0xbd67e3bb,0x272aa718,0xdd66b96c,0x26ec88ae,0x8ed00407,
        0x08ed6dcf,0xff0db072 } },
    /* 30 */
    { { 0x4c95d553,0x749fa101,0x5d680a8a,0xa44052fd,0xff3b566f,0x183b4317,
        0x88740ea3,0x313b513c },
      { 0x08d11549,0xb402e2ac,0xb4dee21c,0x071ee10b,0x47f2320e,0x26b987dd,
        0x86f19f81,0x2d3abcf9 } },
    /* 31 */
    { { 0x815581a2,0x4c288501,0x632211af,0x9a0a6d56,0x0cab2e99,0x19ba7a0f,
        0xded98cdf,0xc036fa10 },
      { 0xc1fbd009,0x29ae08ba,0x06d15816,0x0b68b190,0x9b9e0d8f,0xc2eb3277,
        0xb6d40194,0xa6b2a2c4 } },
    /* 32 */
    { { 0x6d3549cf,0xd433e50f,0xfacd665e,0x6f33696f,0xce11fcb4,0x695bfdac,
        0xaf7c9860,0x810ee252 },
      { 0x7159bb2c,0x65450fe1,0x758b357b,0xf7dfbebe,0xd69fea72,0x2b057e74,
        0x92731745,0xd485717a } },
    /* 33 */
    { { 0xf0cb5a98,0x11741a8a,0x1f3110bf,0xd3da8f93,0xab382adf,0x1994e2cb,
        0x2f9a604e,0x6a6045a7 },
      { 0xa2b2411d,0x170c0d3f,0x510e96e0,0xbe0eb83e,0x8865b3cc,0x3bcc9f73,
        0xf9e15790,0xd3e45cfa } },
    /* 34 */
    { { 0xe83f7669,0xce1f69bb,0x72877d6b,0x09f8ae82,0x3244278d,0x9548ae54,
        0xe3c2c19c,0x207755de },
      { 0x6fef1945,0x87bd61d9,0xb12d28c3,0x18813cef,0x72df64aa,0x9fbcd1d6,
        0x7154b00d,0x48dc5ee5 } },
    /* 35 */
    { { 0xf7e5a199,0x123790bf,0x989ccbb7,0xe0efb8cf,0x0a519c79,0xc27a2bfe,
        0xdff6f445,0xf2fb0aed },
      { 0xf0b5025f,0x41c09575,0x40fa9f22,0x550543d7,0x380bfbd0,0x8fa3c8ad,
        0xdb28d525,0xa13e9015 } },
    /* 36 */
    { { 0xa2b65cbc,0xf9f7a350,0x2a464226,0x0b04b972,0xe23f07a1,0x265ce241,
        0x1497526f,0x2bf0d6b0 },
      { 0x4b216fb7,0xd3d4dd3f,0xfbdda26a,0xf7d7b867,0x6708505c,0xaeb7b83f,
        0x162fe89f,0x42a94a5a } },
    /* 37 */
    { { 0xeaadf191,0x5846ad0b,0x25a268d7,0x0f8a4890,0x494dc1f6,0xe8603050,
        0xc65ede3d,0x2c2dd969 },
      { 0x93849c17,0x6d02171d,0x1da250dd,0x460488ba,0x3c3a5485,0x4810c706,
        0x42c56dbc,0xf437fa1f } },
    /* 38 */
    { { 0x4a0f7dab,0x6aa0d714,0x1776e9ac,0x0f049793,0xf5f39786,0x52c0a050,
        0x54707aa8,0xaaf45b33 },
      { 0xc18d364a,0x85e37c33,0x3e497165,0xd40b9b06,0x15ec5444,0xf4171681,
        0xf4f272bc,0xcdf6310d } },
    /* 39 */
    { { 0x8ea8b7ef,0x7473c623,0x85bc2287,0x08e93518,0x2bda8e34,0x41956772,
        0xda9e2ff2,0xf0d008ba },
      { 0x2414d3b1,0x2912671d,0xb019ea76,0xb3754985,0x453bcbdb,0x5c61b96d,
        0xca887b8b,0x5bd5c2f5 } },
    /* 40 */
    { { 0xf49a3154,0xef0f469e,0x6e2b2e9a,0x3e85a595,0xaa924a9c,0x45aaec1e,
        0xa09e4719,0xaa12dfc8 },
      { 0x4df69f1d,0x26f27227,0xa2ff5e73,0xe0e4c82c,0xb7a9dd44,0xb9d8ce73,
        0xe48ca901,0x6c036e73 } },
    /* 41 */
    { { 0x0f6e3138,0x5cfae12a,0x25ad345a,0x6966ef00,0x45672bc5,0x8993c64b,
        0x96afbe24,0x292ff658 },
      { 0x5e213402,0xd5250d44,0x4392c9fe,0xf6580e27,0xda1c72e8,0x097b397f,
        0x311b7276,0x644e0c90 } },
    /* 42 */
    { { 0xa47153f0,0xe1e421e1,0x920418c9,0xb86c3b79,0x705d7672,0x93bdce87,
        0xcab79a77,0xf25ae793 },
      { 0x6d869d0c,0x1f3194a3,0x4986c264,0x9d55c882,0x096e945e,0x49fb5ea3,
        0x13db0a3e,0x39b8e653 } },
    /* 43 */
    { { 0xb6fd2e59,0x37754200,0x9255c98f,0x35e2c066,0x0e2a5739,0xd9dab21a,
        0x0f19db06,0x39122f2f },
      { 0x03cad53c,0xcfbce1e0,0xe65c17e3,0x225b2c0f,0x9aa13877,0x72baf1d2,
        0xce80ff8d,0x8de80af8 } },
    /* 44 */
    { { 0x207bbb76,0xafbea8d9,0x21782758,0x921c7e7c,0x1c0436b1,0xdfa2b74b,
        0x2e368c04,0x87194906 },
      { 0xa3993df5,0xb5f928bb,0xf3b3d26a,0x639d75b5,0x85b55050,0x011aa78a,
        0x5b74fde1,0xfc315e6a } },
    /* 45 */
    { { 0xe8d6ecfa,0x561fd41a,0x1aec7f86,0x5f8c44f6,0x4924741d,0x98452a7b,
        0xee389088,0xe6d4a7ad },
      { 0x4593c75d,0x60552ed1,0xdd271162,0x70a70da4,0x7ba2c7db,0xd2aede93,
        0x9be2ae57,0x35dfaf9a } },
    /* 46 */
    { { 0xaa736636,0x6b956fcd,0xae2cab7e,0x09f51d97,0x0f349966,0xfb10bf41,
        0x1c830d2b,0x1da5c7d7 },
      { 0x3cce6825,0x5c41e483,0xf9573c3b,0x15ad118f,0xf23036b8,0xa28552c7,
        0xdbf4b9d6,0x7077c0fd } },
    /* 47 */
    { { 0x46b9661c,0xbf63ff8d,0x0d2cfd71,0xa1dfd36b,0xa847f8f7,0x0373e140,
        0xe50efe44,0x53a8632e },
      { 0x696d8051,0x0976ff68,0xc74f468a,0xdaec0c95,0x5e4e26bd,0x62994dc3,
        0x34e1fcc1,0x028ca76d } },
    /* 48 */
    { { 0xfc9877ee,0xd11d47dc,0x801d0002,0xc8b36210,0x54c260b6,0xd002c117,
        0x6962f046,0x04c17cd8 },
      { 0xb0daddf5,0x6d9bd094,0x24ce55c0,0xbea23575,0x72da03b5,0x663356e6,
        0xfed97474,0xf7ba4de9 } },
    /* 49 */
    { { 0xebe1263f,0xd0dbfa34,0x71ae7ce6,0x55763735,0x82a6f523,0xd2440553,
        0x52131c41,0xe31f9600 },
      { 0xea6b6ec6,0xd1bb9216,0x73c2fc44,0x37a1d12e,0x89d0a294,0xc10e7eac,
        0xce34d47b,0xaa3a6259 } },
    /* 50 */
    { { 0x36f3dcd3,0xfbcf9df5,0xd2bf7360,0x6ceded50,0xdf504f5b,0x491710fa,
        0x7e79daee,0x2398dd62 },
      { 0x6d09569e,0xcf4705a3,0x5149f769,0xea0619bb,0x35f6034c,0xff9c0377,
        0x1c046210,0x5717f5b2 } },
    /* 51 */
    { { 0x21dd895e,0x9fe229c9,0x40c28451,0x8e518500,0x1d637ecd,0xfa13d239,
        0x0e3c28de,0x660a2c56 },
      { 0xd67fcbd0,0x9cca88ae,0x0ea9f096,0xc8472478,0x72e92b4d,0x32b2f481,
        0x4f522453,0x624ee54c } },
    /* 52 */
    { { 0xd897eccc,0x09549ce4,0x3f9880aa,0x4d49d1d9,0x043a7c20,0x723c2423,
        0x92bdfbc0,0x4f392afb },
      { 0x7de44fd9,0x6969f8fa,0x57b32156,0xb66cfbe4,0x368ebc3c,0xdb2fa803,
        0xccdb399c,0x8a3e7977 } },
    /* 53 */
    { { 0x06c4b125,0xdde1881f,0xf6e3ca8c,0xae34e300,0x5c7a13e9,0xef6999de,
        0x70c24404,0x3888d023 },
      { 0x44f91081,0x76280356,0x5f015504,0x3d9fcf61,0x632cd36e,0x1827edc8,
        0x18102336,0xa5e62e47 } },
    /* 54 */
    { { 0x2facd6c8,0x1a825ee3,0x54bcbc66,0x699c6354,0x98df9931,0x0ce3edf7,
        0x466a5adc,0x2c4768e6 },
      { 0x90a64bc9,0xb346ff8c,0xe4779f5c,0x630a6020,0xbc05e884,0xd949d064,
        0xf9e652a0,0x7b5e6441 } },
    /* 55 */
    { { 0x1d28444a,0x2169422c,0xbe136a39,0xe996c5d8,0xfb0c7fce,0x2387afe5,
        0x0c8d744a,0xb8af73cb },
      { 0x338b86fd,0x5fde83aa,0xa58a5cff,0xfee3f158,0x20ac9433,0xc9ee8f6f,
        0x7f3f0895,0xa036395f } },
    /* 56 */
    { { 0xa10f7770,0x8c73c6bb,0xa12a0e24,0xa6f16d81,0x51bc2b9f,0x100df682,
        0x875fb533,0x4be36b01 },
      { 0x9fb56dbb,0x9226086e,0x07e7a4f8,0x306fef8b,0x66d52f20,0xeeaccc05,
        0x1bdc00c0,0x8cbc9a87 } },
    /* 57 */
    { { 0xc0dac4ab,0xe131895c,0x712ff112,0xa874a440,0x6a1cee57,0x6332ae7c,
        0x0c0835f8,0x44e7553e },
      { 0x7734002d,0x6d503fff,0x0b34425c,0x9d35cb8b,0x0e8738b5,0x95f70276,
        0x5eb8fc18,0x470a683a } },
    /* 58 */
    { { 0x90513482,0x81b761dc,0x01e9276a,0x0287202a,0x0ce73083,0xcda441ee,
        0xc63dc6ef,0x16410690 },
      { 0x6d06a2ed,0xf5034a06,0x189b100b,0xdd4d7745,0xab8218c9,0xd914ae72,
        0x7abcbb4f,0xd73479fd } },
    /* 59 */
    { { 0x5ad4c6e5,0x7edefb16,0x5b06d04d,0x262cf08f,0x8575cb14,0x12ed5bb1,
        0x0771666b,0x816469e3 },
      { 0x561e291e,0xd7ab9d79,0xc1de1661,0xeb9daf22,0x135e0513,0xf49827eb,
        0xf0dd3f9c,0x0a36dd23 } },
    /* 60 */
    { { 0x41d5533c,0x098d32c7,0x8684628f,0x7c5f5a9e,0xe349bd11,0x39a228ad,
        0xfdbab118,0xe331dfd6 },
      { 0x6bcc6ed8,0x5100ab68,0xef7a260e,0x7160c3bd,0xbce850d7,0x9063d9a7,
        0x492e3389,0xd3b4782a } },
    /* 61 */
    { { 0xf3821f90,0xa149b6e8,0x66eb7aad,0x92edd9ed,0x1a013116,0x0bb66953,
        0x4c86a5bd,0x7281275a },
      { 0xd3ff47e5,0x503858f7,0x61016441,0x5e1616bc,0x7dfd9bb1,0x62b0f11a,
        0xce145059,0x2c062e7e } },
    /* 62 */
    { { 0x0159ac2e,0xa76f996f,0xcbdb2713,0x281e7736,0x08e46047,0x2ad6d288,
        0x2c4e7ef1,0x282a35f9 },
      { 0xc0ce5cd2,0x9c354b1e,0x1379c229,0xcf99efc9,0x3e82c11e,0x992caf38,
        0x554d2abd,0xc71cd513 } },
    /* 63 */
    { { 0x09b578f4,0x4885de9c,0xe3affa7a,0x1884e258,0x59182f1f,0x8f76b1b7,
        0xcf47f3a3,0xc50f6740 },
      { 0x374b68ea,0xa9c4adf3,0x69965fe2,0xa406f323,0x85a53050,0x2f86a222,
        0x212958dc,0xb9ecb3a7 } },
    /* 64 */
    { { 0xf4f8b16a,0x56f8410e,0xc47b266a,0x97241afe,0x6d9c87c1,0x0a406b8e,
        0xcd42ab1b,0x803f3e02 },
      { 0x04dbec69,0x7f0309a8,0x3bbad05f,0xa83b85f7,0xad8e197f,0xc6097273,
        0x5067adc1,0xc097440e } },
    /* 65 */
    { { 0xc379ab34,0x846a56f2,0x841df8d1,0xa8ee068b,0x176c68ef,0x20314459,
        0x915f1f30,0xf1af32d5 },
      { 0x5d75bd50,0x99c37531,0xf72f67bc,0x837cffba,0x48d7723f,0x0613a418,
        0xe2d41c8b,0x23d0f130 } },
    /* 66 */
    { { 0xf41500d9,0x857ab6ed,0xfcbeada8,0x0d890ae5,0x89725951,0x52fe8648,
        0xc0a3fadd,0xb0288dd6 },
      { 0x650bcb08,0x85320f30,0x695d6e16,0x71af6313,0xb989aa76,0x31f520a7,
        0xf408c8d2,0xffd3724f } },
    /* 67 */
    { { 0xb458e6cb,0x53968e64,0x317a5d28,0x992dad20,0x7aa75f56,0x3814ae0b,
        0xd78c26df,0xf5590f4a },
      { 0xcf0ba55a,0x0fc24bd3,0x0c778bae,0x0fc4724a,0x683b674a,0x1ce9864f,
        0xf6f74a20,0x18d6da54 } },
    /* 68 */
    { { 0xd5be5a2b,0xed93e225,0x5934f3c6,0x6fe79983,0x22626ffc,0x43140926,
        0x7990216a,0x50bbb4d9 },
      { 0xe57ec63e,0x378191c6,0x181dcdb2,0x65422c40,0x0236e0f6,0x41a8099b,
        0x01fe49c3,0x2b100118 } },
    /* 69 */
    { { 0x9b391593,0xfc68b5c5,0x598270fc,0xc385f5a2,0xd19adcbb,0x7144f3aa,
        0x83fbae0c,0xdd558999 },
      { 0x74b82ff4,0x93b88b8e,0x71e734c9,0xd2e03c40,0x43c0322a,0x9a7a9eaf,
        0x149d6041,0xe6e4c551 } },
    /* 70 */
    { { 0x1e9af288,0x55f655bb,0xf7ada931,0x647e1a64,0xcb2820e5,0x43697e4b,
        0x07ed56ff,0x51e00db1 },
      { 0x771c327e,0x43d169b8,0x4a96c2ad,0x29cdb20b,0x3deb4779,0xc07d51f5,
        0x49829177,0xe22f4241 } },
    /* 71 */
    { { 0x635f1abb,0xcd45e8f4,0x68538874,0x7edc0cb5,0xb5a8034d,0xc9472c1f,
        0x52dc48c9,0xf709373d },
      { 0xa8af30d6,0x401966bb,0xf137b69c,0x95bf5f4a,0x9361c47e,0x3966162a,
        0xe7275b11,0xbd52d288 } },
    /* 72 */
    { { 0x9c5fa877,0xab155c7a,0x7d3a3d48,0x17dad672,0x73d189d8,0x43f43f9e,
        0xc8aa77a6,0xa0d0f8e4 },
      { 0xcc94f92d,0x0bbeafd8,0x0c4ddb3a,0xd818c8be,0xb82eba14,0x22cc65f8,
        0x946d6a00,0xa56c78c7 } },
    /* 73 */
    { { 0x0dd09529,0x2962391b,0x3daddfcf,0x803e0ea6,0x5b5bf481,0x2c77351f,
        0x731a367a,0xd8befdf8 },
      { 0xfc0157f4,0xab919d42,0xfec8e650,0xf51caed7,0x02d48b0a,0xcdf9cb40,
        0xce9f6478,0x854a68a5 } },
    /* 74 */
    { { 0x63506ea5,0xdc35f67b,0xa4fe0d66,0x9286c489,0xfe95cd4d,0x3f101d3b,
        0x98846a95,0x5cacea0b },
      { 0x9ceac44d,0xa90df60c,0x354d1c3a,0x3db29af4,0xad5dbabe,0x08dd3de8,
        0x35e4efa9,0xe4982d12 } },
    /* 75 */
    { { 0xc34cd55e,0x23104a22,0x2680d132,0x58695bb3,0x1fa1d943,0xfb345afa,
        0x16b20499,0x8046b7f6 },
      { 0x38e7d098,0xb533581e,0xf46f0b70,0xd7f61e8d,0x44cb78c4,0x30dea9ea,
        0x9082af55,0xeb17ca7b } },
    /* 76 */
    { { 0x76a145b9,0x1751b598,0xc1bc71ec,0xa5cf6b0f,0x392715bb,0xd3e03565,
        0xfab5e131,0x097b00ba },
      { 0x565f69e1,0xaa66c8e9,0xb5be5199,0x77e8f75a,0xda4fd984,0x6033ba11,
        0xafdbcc9e,0xf95c747b } },
    /* 77 */
    { { 0xbebae45e,0x558f01d3,0xc4bc6955,0xa8ebe9f0,0xdbc64fc6,0xaeb705b1,
        0x566ed837,0x3512601e },
      { 0xfa1161cd,0x9336f1e1,0x4c65ef87,0x328ab8d5,0x724f21e5,0x4757eee2,
        0x6068ab6b,0x0ef97123 } },
    /* 78 */
    { { 0x54ca4226,0x02598cf7,0xf8642c8e,0x5eede138,0x468e1790,0x48963f74,
        0x3b4fbc95,0xfc16d933 },
      { 0xe7c800ca,0xbe96fb31,0x2678adaa,0x13806331,0x6ff3e8b5,0x3d624497,
        0xb95d7a17,0x14ca4af1 } },
    /* 79 */
    { { 0xbd2f81d5,0x7a4771ba,0x01f7d196,0x1a5f9d69,0xcad9c907,0xd898bef7,
        0xf59c231d,0x4057b063 },
      { 0x89c05c0a,0xbffd82fe,0x1dc0df85,0xe4911c6f,0xa35a16db,0x3befccae,
        0xf1330b13,0x1c3b5d64 } },
    /* 80 */
    { { 0x80ec21fe,0x5fe14bfe,0xc255be82,0xf6ce116a,0x2f4a5d67,0x98bc5a07,
        0xdb7e63af,0xfad27148 },
      { 0x29ab05b3,0x90c0b6ac,0x4e251ae6,0x37a9a83c,0xc2aade7d,0x0a7dc875,
        0x9f0e1a84,0x77387de3 } },
    /* 81 */
    { { 0xa56c0dd7,0x1e9ecc49,0x46086c74,0xa5cffcd8,0xf505aece,0x8f7a1408,
        0xbef0c47e,0xb37b85c0 },
      { 0xcc0e6a8f,0x3596b6e4,0x6b388f23,0xfd6d4bbf,0xc39cef4e,0xaba453fa,
        0xf9f628d5,0x9c135ac8 } },
    /* 82 */
    { { 0x84e35743,0x32aa3202,0x85a3cdef,0x320d6ab1,0x1df19819,0xb821b176,
        0xc433851f,0x5721361f },
      { 0x71fc9168,0x1f0db36a,0x5e5c403c,0x5f98ba73,0x37bcd8f5,0xf64ca87e,
        0xe6bb11bd,0xdcbac3c9 } },
    /* 83 */
    { { 0x4518cbe2,0xf01d9968,0x9c9eb04e,0xd242fc18,0xe47feebf,0x727663c7,
        0x2d626862,0xb8c1c89e },
      { 0xc8e1d569,0x51a58bdd,0xb7d88cd0,0x563809c8,0xf11f31eb,0x26c27fd9,
        0x2f9422d4,0x5d23bbda } },
    /* 84 */
    { { 0x95c8f8be,0x0a1c7294,0x3bf362bf,0x2961c480,0xdf63d4ac,0x9e418403,
        0x91ece900,0xc109f9cb },
      { 0x58945705,0xc2d095d0,0xddeb85c0,0xb9083d96,0x7a40449b,0x84692b8d,
        0x2eee1ee1,0x9bc3344f } },
    /* 85 */
    { { 0x42913074,0x0d5ae356,0x48a542b1,0x55491b27,0xb310732a,0x469ca665,
        0x5f1a4cc1,0x29591d52 },
      { 0xb84f983f,0xe76f5b6b,0x9f5f84e1,0xbe7eef41,0x80baa189,0x1200d496,
        0x18ef332c,0x6376551f } },
    /* 86 */
    { { 0x562976cc,0xbda5f14e,0x0ef12c38,0x22bca3e6,0x6cca9852,0xbbfa3064,
        0x08e2987a,0xbdb79dc8 },
      { 0xcb06a772,0xfd2cb5c9,0xfe536dce,0x38f475aa,0x7c2b5db8,0xc2a3e022,
        0xadd3c14a,0x8ee86001 } },
    /* 87 */
    { { 0xa4ade873,0xcbe96981,0xc4fba48c,0x7ee9aa4d,0x5a054ba5,0x2cee2899,
        0x6f77aa4b,0x92e51d7a },
      { 0x7190a34d,0x948bafa8,0xf6bd1ed1,0xd698f75b,0x0caf1144,0xd00ee6e3,
        0x0a56aaaa,0x5182f86f } },
    /* 88 */
    { { 0x7a4cc99c,0xfba6212c,0x3e6d9ca1,0xff609b68,0x5ac98c5a,0x5dbb27cb,
        0x4073a6f2,0x91dcab5d },
      { 0x5f575a70,0x01b6cc3d,0x6f8d87fa,0x0cb36139,0x89981736,0x165d4e8c,
        0x97974f2b,0x17a0cedb } },
    /* 89 */
    { { 0x076c8d3a,0x38861e2a,0x210f924b,0x701aad39,0x13a835d9,0x94d0eae4,
        0x7f4cdf41,0x2e8ce36c },
      { 0x037a862b,0x91273dab,0x60e4c8fa,0x01ba9bb7,0x33baf2dd,0xf9645388,
        0x34f668f3,0xf4ccc6cb } },
    /* 90 */
    { { 0xf1f79687,0x44ef525c,0x92efa815,0x7c595495,0xa5c78d29,0xe1231741,
        0x9a0df3c9,0xac0db488 },
      { 0xdf01747f,0x86bfc711,0xef17df13,0x592b9358,0x5ccb6bb5,0xe5880e4f,
        0x94c974a2,0x95a64a61 } },
    /* 91 */
    { { 0xc15a4c93,0x72c1efda,0x82585141,0x40269b73,0x16cb0bad,0x6a8dfb1c,
        0x29210677,0x231e54ba },
      { 0x8ae6d2dc,0xa70df917,0x39112918,0x4d6aa63f,0x5e5b7223,0xf627726b,
        0xd8a731e1,0xab0be032 } },
    /* 92 */
    { { 0x8d131f2d,0x097ad0e9,0x3b04f101,0x637f09e3,0xd5e9a748,0x1ac86196,
        0x2cf6a679,0xf1bcc880 },
      { 0xe8daacb4,0x25c69140,0x60f65009,0x3c4e4055,0x477937a6,0x591cc8fc,
        0x5aebb271,0x85169469 } },
    /* 93 */
    { { 0xf1dcf593,0xde35c143,0xb018be3b,0x78202b29,0x9bdd9d3d,0xe9cdadc2,
        0xdaad55d8,0x8f67d9d2 },
      { 0x7481ea5f,0x84111656,0xe34c590c,0xe7d2dde9,0x05053fa8,0xffdd43f4,
        0xc0728b5d,0xf84572b9 } },
    /* 94 */
    { { 0x97af71c9,0x5e1a7a71,0x7a736565,0xa1449444,0x0e1d5063,0xa1b4ae07,
        0x616b2c19,0xedee2710 },
      { 0x11734121,0xb2f034f5,0x4a25e9f0,0x1cac6e55,0xa40c2ecf,0x8dc148f3,
        0x44ebd7f4,0x9fd27e9b } },
    /* 95 */
    { { 0xf6e2cb16,0x3cc7658a,0xfe5919b6,0xe3eb7d2c,0x168d5583,0x5a8c5816,
        0x958ff387,0xa40c2fb6 },
      { 0xfedcc158,0x8c9ec560,0x55f23056,0x7ad804c6,0x9a307e12,0xd9396704,
        0x7dc6decf,0x99bc9bb8 } },
    /* 96 */
    { { 0x927dafc6,0x84a9521d,0x5c09cd19,0x52c1fb69,0xf9366dde,0x9d9581a0,
        0xa16d7e64,0x9abe210b },
      { 0x48915220,0x480af84a,0x4dd816c6,0xfa73176a,0x1681ca5a,0xc7d53987,
        0x87f344b0,0x7881c257 } },
    /* 97 */
    { { 0xe0bcf3ff,0x93399b51,0x127f74f6,0x0d02cbc5,0xdd01d968,0x8fb465a2,
        0xa30e8940,0x15e6e319 },
      { 0x3e0e05f4,0x646d6e0d,0x43588404,0xfad7bddc,0xc4f850d3,0xbe61c7d1,
        0x191172ce,0x0e55facf } },
    /* 98 */
    { { 0xf8787564,0x7e9d9806,0x31e85ce6,0x1a331721,0xb819e8d6,0x6b0158ca,
        0x6fe96577,0xd73d0976 },
      { 0x1eb7206e,0x42483425,0xc618bb42,0xa519290f,0x5e30a520,0x5dcbb859,
        0x8f15a50b,0x9250a374 } },
    /* 99 */
    { { 0xbe577410,0xcaff08f8,0x5077a8c6,0xfd408a03,0xec0a63a4,0xf1f63289,
        0xc1cc8c0b,0x77414082 },
      { 0xeb0991cd,0x05a40fa6,0x49fdc296,0xc1ca0866,0xb324fd40,0x3a68a3c7,
        0x12eb20b9,0x8cb04f4d } },
    /* 100 */
    { { 0x6906171c,0xb1c2d055,0xb0240c3f,0x9073e9cd,0xd8906841,0xdb8e6b4f,
        0x47123b51,0xe4e429ef },
      { 0x38ec36f4,0x0b8dd53c,0xff4b6a27,0xf9d2dc01,0x879a9a48,0x5d066e07,
        0x3c6e6552,0x37bca2ff } },
    /* 101 */
    { { 0xdf562470,0x4cd2e3c7,0xc0964ac9,0x44f272a2,0x80c793be,0x7c6d5df9,
        0x3002b22a,0x59913edc },
      { 0x5750592a,0x7a139a83,0xe783de02,0x99e01d80,0xea05d64f,0xcf8c0375,
        0xb013e226,0x43786e4a } },
    /* 102 */
    { { 0x9e56b5a6,0xff32b0ed,0xd9fc68f9,0x0750d9a6,0x597846a7,0xec15e845,
        0xb7e79e7a,0x8638ca98 },
      { 0x0afc24b2,0x2f5ae096,0x4dace8f2,0x05398eaf,0xaecba78f,0x3b765dd0,
        0x7b3aa6f0,0x1ecdd36a } },
    /* 103 */
    { { 0x6c5ff2f3,0x5d3acd62,0x2873a978,0xa2d516c0,0xd2110d54,0xad94c9fa,
        0xd459f32d,0xd85d0f85 },
      { 0x10b11da3,0x9f700b8d,0xa78318c4,0xd2c22c30,0x9208decd,0x556988f4,
        0xb4ed3c62,0xa04f19c3 } },
    /* 104 */
    { { 0xed7f93bd,0x087924c8,0x392f51f6,0xcb64ac5d,0x821b71af,0x7cae330a,
        0x5c0950b0,0x92b2eeea },
      { 0x85b6e235,0x85ac4c94,0x2936c0f0,0xab2ca4a9,0xe0508891,0x80faa6b3,
        0x5834276c,0x1ee78221 } },
    /* 105 */
    { { 0xe63e79f7,0xa60a2e00,0xf399d906,0xf590e7b2,0x6607c09d,0x9021054a,
        0x57a6e150,0xf3f2ced8 },
      { 0xf10d9b55,0x200510f3,0xd8642648,0x9d2fcfac,0xe8bd0e7c,0xe5631aa7,
        0x3da3e210,0x0f56a454 } },
    /* 106 */
    { { 0x1043e0df,0x5b21bffa,0x9c007e6d,0x6c74b6cc,0xd4a8517a,0x1a656ec0,
        0x1969e263,0xbd8f1741 },
      { 0xbeb7494a,0x8a9bbb86,0x45f3b838,0x1567d46f,0xa4e5a79a,0xdf7a12a7,
        0x30ccfa09,0x2d1a1c35 } },
    /* 107 */
    { { 0x506508da,0x192e3813,0xa1d795a7,0x336180c4,0x7a9944b3,0xcddb5949,
        0xb91fba46,0xa107a65e },
      { 0x0f94d639,0xe6d1d1c5,0x8a58b7d7,0x8b4af375,0xbd37ca1c,0x1a7c5584,
        0xf87a9af2,0x183d760a } },
    /* 108 */
    { { 0x0dde59a4,0x29d69711,0x0e8bef87,0xf1ad8d07,0x4f2ebe78,0x229b4963,
        0xc269d754,0x1d44179d },
      { 0x8390d30e,0xb32dc0cf,0x0de8110c,0x0a3b2753,0x2bc0339a,0x31af1dc5,
        0x9606d262,0x771f9cc2 } },
    /* 109 */
    { { 0x85040739,0x99993e77,0x8026a939,0x44539db9,0xf5f8fc26,0xcf40f6f2,
        0x0362718e,0x64427a31 },
      { 0x85428aa8,0x4f4f2d87,0xebfb49a8,0x7b7adc3f,0xf23d01ac,0x201b2c6d,
        0x6ae90d6d,0x49d9b749 } },
    /* 110 */
    { { 0x435d1099,0xcc78d8bc,0x8e8d1a08,0x2adbcd4e,0x2cb68a41,0x02c2e2a0,
        0x3f605445,0x9037d81b },
      { 0x074c7b61,0x7cdbac27,0x57bfd72e,0xfe2031ab,0x596d5352,0x61ccec96,
        0x7cc0639c,0x08c3de6a } },
    /* 111 */
    { { 0xf6d552ab,0x20fdd020,0x05cd81f1,0x56baff98,0x91351291,0x06fb7c3e,
        0x45796b2f,0xc6909442 },
      { 0x41231bd1,0x17b3ae9c,0x5cc58205,0x1eac6e87,0xf9d6a122,0x208837ab,
        0xcafe3ac0,0x3fa3db02 } },
    /* 112 */
    { { 0x05058880,0xd75a3e65,0x643943f2,0x7da365ef,0xfab24925,0x4147861c,
        0xfdb808ff,0xc5c4bdb0 },
      { 0xb272b56b,0x73513e34,0x11b9043a,0xc8327e95,0xf8844969,0xfd8ce37d,
        0x46c2b6b5,0x2d56db94 } },
    /* 113 */
    { { 0xff46ac6b,0x2461782f,0x07a2e425,0xd19f7926,0x09a48de1,0xfafea3c4,
        0xe503ba42,0x0f56bd9d },
      { 0x345cda49,0x137d4ed1,0x816f299d,0x821158fc,0xaeb43402,0xe7c6a54a,
        0x1173b5f1,0x4003bb9d } },
    /* 114 */
    { { 0xa0803387,0x3b8e8189,0x39cbd404,0xece115f5,0xd2877f21,0x4297208d,
        0xa07f2f9e,0x53765522 },
      { 0xa8a4182d,0xa4980a21,0x3219df79,0xa2bbd07a,0x1a19a2d4,0x674d0a2e,
        0x6c5d4549,0x7a056f58 } },
    /* 115 */
    { { 0x9d8a2a47,0x646b2558,0xc3df2773,0x5b582948,0xabf0d539,0x51ec000e,
        0x7a1a2675,0x77d482f1 },
      { 0x87853948,0xb8a1bd95,0x6cfbffee,0xa6f817bd,0x80681e47,0xab6ec057,
        0x2b38b0e4,0x4115012b } },
    /* 116 */
    { { 0x6de28ced,0x3c73f0f4,0x9b13ec47,0x1d5da760,0x6e5c6392,0x61b8ce9e,
        0xfbea0946,0xcdf04572 },
      { 0x6c53c3b0,0x1cb3c58b,0x447b843c,0x97fe3c10,0x2cb9780e,0xfb2b8ae1,
        0x97383109,0xee703dda } },
    /* 117 */
    { { 0xff57e43a,0x34515140,0xb1b811b8,0xd44660d3,0x8f42b986,0x2b3b5dff,
        0xa162ce21,0x2a0ad89d },
      { 0x6bc277ba,0x64e4a694,0xc141c276,0xc788c954,0xcabf6274,0x141aa64c,
        0xac2b4659,0xd62d0b67 } },
    /* 118 */
    { { 0x2c054ac4,0x39c5d87b,0xf27df788,0x57005859,0xb18128d6,0xedf7cbf3,
        0x991c2426,0xb39a23f2 },
      { 0xf0b16ae5,0x95284a15,0xa136f51b,0x0c6a05b1,0xf2700783,0x1d63c137,
        0xc0674cc5,0x04ed0092 } },
    /* 119 */
    { { 0x9ae90393,0x1f4185d1,0x4a3d64e6,0x3047b429,0x9854fc14,0xae0001a6,
        0x0177c387,0xa0a91fc1 },
      { 0xae2c831e,0xff0a3f01,0x2b727e16,0xbb76ae82,0x5a3075b4,0x8f12c8a1,
        0x9ed20c41,0x084cf988 } },
    /* 120 */
    { { 0xfca6becf,0xd98509de,0x7dffb328,0x2fceae80,0x4778e8b9,0x5d8a15c4,
        0x73abf77e,0xd57955b2 },
      { 0x31b5d4f1,0x210da79e,0x3cfa7a1c,0xaa52f04b,0xdc27c20b,0xd4d12089,
        0x02d141f1,0x8e14ea42 } },
    /* 121 */
    { { 0xf2897042,0xeed50345,0x43402c4a,0x8d05331f,0xc8bdfb21,0xc8d9c194,
        0x2aa4d158,0x597e1a37 },
      { 0xcf0bd68c,0x0327ec1a,0xab024945,0x6d4be0dc,0xc9fe3e84,0x5b9c8d7a,
        0x199b4dea,0xca3f0236 } },
    /* 122 */
    { { 0x6170bd20,0x592a10b5,0x6d3f5de7,0x0ea897f1,0x44b2ade2,0xa3363ff1,
        0x309c07e4,0xbde7fd7e },
      { 0xb8f5432c,0x516bb6d2,0xe043444b,0x210dc1cb,0xf8f95b5a,0x3db01e6f,
        0x0a7dd198,0xb623ad0e } },
    /* 123 */
    { { 0x60c7b65b,0xa75bd675,0x23a4a289,0xab8c5590,0xd7b26795,0xf8220fd0,
        0x58ec137b,0xd6aa2e46 },
      { 0x5138bb85,0x10abc00b,0xd833a95c,0x8c31d121,0x1702a32e,0xb24ff00b,
        0x2dcc513a,0x111662e0 } },
    /* 124 */
    { { 0xefb42b87,0x78114015,0x1b6c4dff,0xbd9f5d70,0xa7d7c129,0x66ecccd7,
        0x94b750f8,0xdb3ee1cb },
      { 0xf34837cf,0xb26f3db0,0xb9578d4f,0xe7eed18b,0x7c56657d,0x5d2cdf93,
        0x52206a59,0x886a6442 } },
    /* 125 */
    { { 0x65b569ea,0x3c234cfb,0xf72119c1,0x20011141,0xa15a619e,0x8badc85d,
        0x018a17bc,0xa70cf4eb },
      { 0x8c4a6a65,0x224f97ae,0x0134378f,0x36e5cf27,0x4f7e0960,0xbe3a609e,
        0xd1747b77,0xaa4772ab } },
    /* 126 */
    { { 0x7aa60cc0,0x67676131,0x0368115f,0xc7916361,0xbbc1bb5a,0xded98bb4,
        0x30faf974,0x611a6ddc },
      { 0xc15ee47a,0x30e78cbc,0x4e0d96a5,0x2e896282,0x3dd9ed88,0x36f35adf,
        0x16429c88,0x5cfffaf8 } },
    /* 127 */
    { { 0x9b7a99cd,0xc0d54cff,0x843c45a1,0x7bf3b99d,0x62c739e1,0x038a908f,
        0x7dc1994c,0x6e5a6b23 },
      { 0x0ba5db77,0xef8b454e,0xacf60d63,0xb7b8807f,0x76608378,0xe591c0c6,
        0x242dabcc,0x481a238d } },
    /* 128 */
    { { 0x35d0b34a,0xe3417bc0,0x8327c0a7,0x440b386b,0xac0362d1,0x8fb7262d,
        0xe0cdf943,0x2c41114c },
      { 0xad95a0b1,0x2ba5cef1,0x67d54362,0xc09b37a8,0x01e486c9,0x26d6cdd2,
        0x42ff9297,0x20477abf } },
    /* 129 */
    { { 0x18d65dbf,0x2f75173c,0x339edad8,0x77bf940e,0xdcf1001c,0x7022d26b,
        0xc77396b6,0xac66409a },
      { 0xc6261cc3,0x8b0bb36f,0x190e7e90,0x213f7bc9,0xa45e6c10,0x6541ceba,
        0xcc122f85,0xce8e6975 } },
    /* 130 */
    { { 0xbc0a67d2,0x0f121b41,0x444d248a,0x62d4760a,0x659b4737,0x0e044f1d,
        0x250bb4a8,0x08fde365 },
      { 0x848bf287,0xaceec3da,0xd3369d6e,0xc2a62182,0x92449482,0x3582dfdc,
        0x565d6cd7,0x2f7e2fd2 } },
    /* 131 */
    { { 0xc3770fa7,0xae4b92db,0x379043f9,0x095e8d5c,0x17761171,0x54f34e9d,
        0x907702ae,0xc65be92e },
      { 0xf6fd0a40,0x2758a303,0xbcce784b,0xe7d822e3,0x4f9767bf,0x7ae4f585,
        0xd1193b3a,0x4bff8e47 } },
    /* 132 */
    { { 0x00ff1480,0xcd41d21f,0x0754db16,0x2ab8fb7d,0xbbe0f3ea,0xac81d2ef,
        0x5772967d,0x3e4e4ae6 },
      { 0x3c5303e6,0x7e18f36d,0x92262397,0x3bd9994b,0x1324c3c0,0x9ed70e26,
        0x58ec6028,0x5388aefd } },
    /* 133 */
    { { 0x5e5d7713,0xad1317eb,0x75de49da,0x09b985ee,0xc74fb261,0x32f5bc4f,
        0x4f75be0e,0x5cf908d1 },
      { 0x8e657b12,0x76043510,0xb96ed9e6,0xbfd421a5,0x8970ccc2,0x0e29f51f,
        0x60f00ce2,0xa698ba40 } },
    /* 134 */
    { { 0xef748fec,0x73db1686,0x7e9d2cf9,0xe6e755a2,0xce265eff,0x630b6544,
        0x7aebad8d,0xb142ef8a },
      { 0x17d5770a,0xad31af9f,0x2cb3412f,0x66af3b67,0xdf3359de,0x6bd60d1b,
        0x58515075,0xd1896a96 } },
    /* 135 */
    { { 0x33c41c08,0xec5957ab,0x5468e2e1,0x87de94ac,0xac472f6c,0x18816b73,
        0x7981da39,0x267b0e0b },
      { 0x8e62b988,0x6e554e5d,0x116d21e7,0xd8ddc755,0x3d2a6f99,0x4610faf0,
        0xa1119393,0xb54e287a } },
    /* 136 */
    { { 0x178a876b,0x0a0122b5,0x085104b4,0x51ff96ff,0x14f29f76,0x050b31ab,
        0x5f87d4e6,0x84abb28b },
      { 0x8270790a,0xd5ed439f,0x85e3f46b,0x2d6cb59d,0x6c1e2212,0x75f55c1b,
        0x17655640,0xe5436f67 } },
    /* 137 */
    { { 0x2286e8d5,0x53f9025e,0x864453be,0x353c95b4,0xe408e3a0,0xd832f5bd,
        0x5b9ce99e,0x0404f68b },
      { 0xa781e8e5,0xcad33bde,0x163c2f5b,0x3cdf5018,0x0119caa3,0x57576960,
        0x0ac1c701,0x3a4263df } },
    /* 138 */
    { { 0x9aeb596d,0xc2965ecc,0x023c92b4,0x01ea03e7,0x2e013961,0x4704b4b6,
        0x905ea367,0x0ca8fd3f },
      { 0x551b2b61,0x92523a42,0x390fcd06,0x1eb7a89c,0x0392a63e,0xe7f1d2be,
        0x4ddb0c33,0x96dca264 } },
    /* 139 */
    { { 0x387510af,0x203bb43a,0xa9a36a01,0x846feaa8,0x2f950378,0xd23a5770,
        0x3aad59dc,0x4363e212 },
      { 0x40246a47,0xca43a1c7,0xe55dd24d,0xb362b8d2,0x5d8faf96,0xf9b08604,
        0xd8bb98c4,0x840e115c } },
    /* 140 */
    { { 0x1023e8a7,0xf12205e2,0xd8dc7a0b,0xc808a8cd,0x163a5ddf,0xe292a272,
        0x30ded6d4,0x5e0d6abd },
      { 0x7cfc0f64,0x07a721c2,0x0e55ed88,0x42eec01d,0x1d1f9db2,0x26a7bef9,
        0x2945a25a,0x7dea48f4 } },
    /* 141 */
    { { 0xe5060a81,0xabdf6f1c,0xf8f95615,0xe79f9c72,0x06ac268b,0xcfd36c54,
        0xebfd16d1,0xabc2a2be },
      { 0xd3e2eac7,0x8ac66f91,0xd2dd0466,0x6f10ba63,0x0282d31b,0x6790e377,
        0x6c7eefc1,0x4ea35394 } },
    /* 142 */
    { { 0x5266309d,0xed8a2f8d,0x81945a3e,0x0a51c6c0,0x578c5dc1,0xcecaf45a,
        0x1c94ffc3,0x3a76e689 },
      { 0x7d7b0d0f,0x9aace8a4,0x8f584a5f,0x963ace96,0x4e697fbe,0x51a30c72,
        0x465e6464,0x8212a10a } },
    /* 143 */
    { { 0xcfab8caa,0xef7c61c3,0x0e142390,0x18eb8e84,0x7e9733ca,0xcd1dff67,
        0x599cb164,0xaa7cab71 },
      { 0xbc837bd1,0x02fc9273,0xc36af5d7,0xc06407d0,0xf423da49,0x17621292,
        0xfe0617c3,0x40e38073 } },
    /* 144 */
    { { 0xa7bf9b7c,0xf4f80824,0x3fbe30d0,0x365d2320,0x97cf9ce3,0xbfbe5320,
        0xb3055526,0xe3604700 },
      { 0x6cc6c2c7,0x4dcb9911,0xba4cbee6,0x72683708,0x637ad9ec,0xdcded434,
        0xa3dee15f,0x6542d677 } },
    /* 145 */
    { { 0x7b6c377a,0x3f32b6d0,0x903448be,0x6cb03847,0x20da8af7,0xd6fdd3a8,
        0x09bb6f21,0xa6534aee },
      { 0x1035facf,0x30a1780d,0x9dcb47e6,0x35e55a33,0xc447f393,0x6ea50fe1,
        0xdc9aef22,0xf3cb672f } },
    /* 146 */
    { { 0x3b55fd83,0xeb3719fe,0x875ddd10,0xe0d7a46c,0x05cea784,0x33ac9fa9,
        0xaae870e7,0x7cafaa2e },
      { 0x1d53b338,0x9b814d04,0xef87e6c6,0xe0acc0a0,0x11672b0f,0xfb93d108,
        0xb9bd522e,0x0aab13c1 } },
    /* 147 */
    { { 0xd2681297,0xddcce278,0xb509546a,0xcb350eb1,0x7661aaf2,0x2dc43173,
        0x847012e9,0x4b91a602 },
      { 0x72f8ddcf,0xdcff1095,0x9a911af4,0x08ebf61e,0xc372430e,0x48f4360a,
        0x72321cab,0x49534c53 } },
    /* 148 */
    { { 0xf07b7e9d,0x83df7d71,0x13cd516f,0xa478efa3,0x6c047ee3,0x78ef264b,
        0xd65ac5ee,0xcaf46c4f },
      { 0x92aa8266,0xa04d0c77,0x913684bb,0xedf45466,0xae4b16b0,0x56e65168,
        0x04c6770f,0x14ce9e57 } },
    /* 149 */
    { { 0x965e8f91,0x99445e3e,0xcb0f2492,0xd3aca1ba,0x90c8a0a0,0xd31cc70f,
        0x3e4c9a71,0x1bb708a5 },
      { 0x558bdd7a,0xd5ca9e69,0x018a26b1,0x734a0508,0x4c9cf1ec,0xb093aa71,
        0xda300102,0xf9d126f2 } },
    /* 150 */
    { { 0xaff9563e,0x749bca7a,0xb49914a0,0xdd077afe,0xbf5f1671,0xe27a0311,
        0x729ecc69,0x807afcb9 },
      { 0xc9b08b77,0x7f8a9337,0x443c7e38,0x86c3a785,0x476fd8ba,0x85fafa59,
        0x6568cd8c,0x751adcd1 } },
    /* 151 */
    { { 0x10715c0d,0x8aea38b4,0x8f7697f7,0xd113ea71,0x93fbf06d,0x665eab14,
        0x2537743f,0x29ec4468 },
      { 0xb50bebbc,0x3d94719c,0xe4505422,0x399ee5bf,0x8d2dedb1,0x90cd5b3a,
        0x92a4077d,0xff9370e3 } },
    /* 152 */
    { { 0xc6b75b65,0x59a2d69b,0x266651c5,0x4188f8d5,0x3de9d7d2,0x28a9f33e,
        0xa2a9d01a,0x9776478b },
      { 0x929af2c7,0x8852622d,0x4e690923,0x334f5d6d,0xa89a51e9,0xce6cc7e5,
        0xac2f82fa,0x74a6313f } },
    /* 153 */
    { { 0xb75f079c,0xb2f4dfdd,0x18e36fbb,0x85b07c95,0xe7cd36dd,0x1b6cfcf0,
        0x0ff4863d,0xab75be15 },
      { 0x173fc9b7,0x81b367c0,0xd2594fd0,0xb90a7420,0xc4091236,0x15fdbf03,
        0x0b4459f6,0x4ebeac2e } },
    /* 154 */
    { { 0x5c9f2c53,0xeb6c5fe7,0x8eae9411,0xd2522011,0xf95ac5d8,0xc8887633,
        0x2c1baffc,0xdf99887b },
      { 0x850aaecb,0xbb78eed2,0x01d6a272,0x9d49181b,0xb1cdbcac,0x978dd511,
        0x779f4058,0x27b040a7 } },
    /* 155 */
    { { 0xf73b2eb2,0x90405db7,0x8e1b2118,0xe0df8508,0x5962327e,0x501b7152,
        0xe4cfa3f5,0xb393dd37 },
      { 0x3fd75165,0xa1230e7b,0xbcd33554,0xd66344c2,0x0f7b5022,0x6c36f1be,
        0xd0463419,0x09588c12 } },
    /* 156 */
    { { 0x02601c3b,0xe086093f,0xcf5c335f,0xfb0252f8,0x894aff28,0x955cf280,
        0xdb9f648b,0x81c879a9 },
      { 0xc6f56c51,0x040e687c,0x3f17618c,0xfed47169,0x9059353b,0x44f88a41,
        0x5fc11bc4,0xfa0d48f5 } },
    /* 157 */
    { { 0xe1608e4d,0xbc6e1c9d,0x3582822c,0x010dda11,0x157ec2d7,0xf6b7ddc1,
        0xb6a367d6,0x8ea0e156 },
      { 0x2383b3b4,0xa354e02f,0x3f01f53c,0x69966b94,0x2de03ca5,0x4ff6632b,
        0xfa00b5ac,0x3f5ab924 } },
    /* 158 */
    { { 0x59739efb,0x337bb0d9,0xe7ebec0d,0xc751b0f4,0x411a67d1,0x2da52dd6,
        0x2b74256e,0x8bc76887 },
      { 0x82d3d253,0xa5be3b72,0xf58d779f,0xa9f679a1,0xe16767bb,0xa1cac168,
        0x60fcf34f,0xb386f190 } },
    /* 159 */
    { { 0x2fedcfc2,0x31f3c135,0x62f8af0d,0x5396bf62,0xe57288c2,0x9a02b4ea,
        0x1b069c4d,0x4cb460f7 },
      { 0x5b8095ea,0xae67b4d3,0x6fc07603,0x92bbf859,0xb614a165,0xe1475f66,
        0x95ef5223,0x52c0d508 } },
    /* 160 */
    { { 0x15339848,0x231c210e,0x70778c8d,0xe87a28e8,0x6956e170,0x9d1de661,
        0x2bb09c0b,0x4ac3c938 },
      { 0x6998987d,0x19be0551,0xae09f4d6,0x8b2376c4,0x1a3f933d,0x1de0b765,
        0xe39705f4,0x380d94c7 } },
    /* 161 */
    { { 0x81542e75,0x01a355aa,0xee01b9b7,0x96c724a1,0x624d7087,0x6b3a2977,
        0xde2637af,0x2ce3e171 },
      { 0xf5d5bc1a,0xcfefeb49,0x2777e2b5,0xa655607e,0x9513756c,0x4feaac2f,
        0x0b624e4d,0x2e6cd852 } },
    /* 162 */
    { { 0x8c31c31d,0x3685954b,0x5bf21a0c,0x68533d00,0x75c79ec9,0x0bd7626e,
        0x42c69d54,0xca177547 },
      { 0xf6d2dbb2,0xcc6edaff,0x174a9d18,0xfd0d8cbd,0xaa4578e8,0x875e8793,
        0x9cab2ce6,0xa976a713 } },
    /* 163 */
    { { 0x93fb353d,0x0a651f1b,0x57fcfa72,0xd75cab8b,0x31b15281,0xaa88cfa7,
        0x0a1f4999,0x8720a717 },
      { 0x693e1b90,0x8c3e8d37,0x16f6dfc3,0xd345dc0b,0xb52a8742,0x8ea8d00a,
        0xc769893c,0x9719ef29 } },
    /* 164 */
    { { 0x58e35909,0x820eed8d,0x33ddc116,0x9366d8dc,0x6e205026,0xd7f999d0,
        0xe15704c1,0xa5072976 },
      { 0xc4e70b2e,0x002a37ea,0x6890aa8a,0x84dcf657,0x645b2a5c,0xcd71bf18,
        0xf7b77725,0x99389c9d } },
    /* 165 */
    { { 0x7ada7a4b,0x238c08f2,0xfd389366,0x3abe9d03,0x766f512c,0x6b672e89,
        0x202c82e4,0xa88806aa },
      { 0xd380184e,0x6602044a,0x126a8b85,0xa8cb78c4,0xad844f17,0x79d670c0,
        0x4738dcfe,0x0043bffb } },
    /* 166 */
    { { 0x36d5192e,0x8d59b5dc,0x4590b2af,0xacf885d3,0x11601781,0x83566d0a,
        0xba6c4866,0x52f3ef01 },
      { 0x0edcb64d,0x3986732a,0x8068379f,0x0a482c23,0x7040f309,0x16cbe5fa,
        0x9ef27e75,0x3296bd89 } },
    /* 167 */
    { { 0x454d81d7,0x476aba89,0x51eb9b3c,0x9eade7ef,0x81c57986,0x619a21cd,
        0xaee571e9,0x3b90febf },
      { 0x5496f7cb,0x9393023e,0x7fb51bc4,0x55be41d8,0x99beb5ce,0x03f1dd48,
        0x9f810b18,0x6e88069d } },
    /* 168 */
    { { 0xb43ea1db,0xce37ab11,0x5259d292,0x0a7ff1a9,0x8f84f186,0x851b0221,
        0xdefaad13,0xa7222bea },
      { 0x2b0a9144,0xa2ac78ec,0xf2fa59c5,0x5a024051,0x6147ce38,0x91d1eca5,
        0xbc2ac690,0xbe94d523 } },
    /* 169 */
    { { 0x0b226ce7,0x72f4945e,0x967e8b70,0xb8afd747,0x85a6c63e,0xedea46f1,
        0x9be8c766,0x7782defe },
      { 0x3db38626,0x760d2aa4,0x76f67ad1,0x460ae787,0x54499cdb,0x341b86fc,
        0xa2892e4b,0x03838567 } },
    /* 170 */
    { { 0x79ec1a0f,0x2d8daefd,0xceb39c97,0x3bbcd6fd,0x58f61a95,0xf5575ffc,
        0xadf7b420,0xdbd986c4 },
      { 0x15f39eb7,0x81aa8814,0xb98d976c,0x6ee2fcf5,0xcf2f717d,0x5465475d,
        0x6860bbd0,0x8e24d3c4 } },
    /* 171 */
    { { 0x9a587390,0x749d8e54,0x0cbec588,0x12bb194f,0xb25983c6,0x46e07da4,
        0x407bafc8,0x541a99c4 },
      { 0x624c8842,0xdb241692,0xd86c05ff,0x6044c12a,0x4f7fcf62,0xc59d14b4,
        0xf57d35d1,0xc0092c49 } },
    /* 172 */
    { { 0xdf2e61ef,0xd3cc75c3,0x2e1b35ca,0x7e8841c8,0x909f29f4,0xc62d30d1,
        0x7286944d,0x75e40634 },
      { 0xbbc237d0,0xe7d41fc5,0xec4f01c9,0xc9537bf0,0x282bd534,0x91c51a16,
        0xc7848586,0x5b7cb658 } },
    /* 173 */
    { { 0x8a28ead1,0x964a7084,0xfd3b47f6,0x802dc508,0x767e5b39,0x9ae4bfd1,
        0x8df097a1,0x7ae13eba },
      { 0xeadd384e,0xfd216ef8,0xb6b2ff06,0x0361a2d9,0x4bcdb5f3,0x204b9878,
        0xe2a8e3fd,0x787d8074 } },
    /* 174 */
    { { 0x757fbb1c,0xc5e25d6b,0xca201deb,0xe47bddb2,0x6d2233ff,0x4a55e9a3,
        0x9ef28484,0x5c222819 },
      { 0x88315250,0x773d4a85,0x827097c1,0x21b21a2b,0xdef5d33f,0xab7c4ea1,
        0xbaf0f2b0,0xe45d37ab } },
    /* 175 */
    { { 0x28511c8a,0xd2df1e34,0xbdca6cd3,0xebb229c8,0x627c39a7,0x578a71a7,
        0x84dfb9d3,0xed7bc122 },
      { 0x93dea561,0xcf22a6df,0xd48f0ed1,0x5443f18d,0x5bad23e8,0xd8b86140,
        0x45ca6d27,0xaac97cc9 } },
    /* 176 */
    { { 0xa16bd00a,0xeb54ea74,0xf5c0bcc1,0xd839e9ad,0x1f9bfc06,0x092bb7f1,
        0x1163dc4e,0x318f97b3 },
      { 0xc30d7138,0xecc0c5be,0xabc30220,0x44e8df23,0xb0223606,0x2bb7972f,
        0x9a84ff4d,0xfa41faa1 } },
    /* 177 */
    { { 0xa6642269,0x4402d974,0x9bb783bd,0xc81814ce,0x7941e60b,0x398d38e4,
        0x1d26e9e2,0x38bb6b2c },
      { 0x6a577f87,0xc64e4a25,0xdc11fe1c,0x8b52d253,0x62280728,0xff336abf,
        0xce7601a5,0x94dd0905 } },
    /* 178 */
    { { 0xde93f92a,0x156cf7dc,0x89b5f315,0xa01333cb,0xc995e750,0x02404df9,
        0xd25c2ae9,0x92077867 },
      { 0x0bf39d44,0xe2471e01,0x96bb53d7,0x5f2c9020,0x5c9c3d8f,0x4c44b7b3,
        0xd29beb51,0x81e8428b } },
    /* 179 */
    { { 0xc477199f,0x6dd9c2ba,0x6b5ecdd9,0x8cb8eeee,0xee40fd0e,0x8af7db3f,
        0xdbbfa4b1,0x1b94ab62 },
      { 0xce47f143,0x44f0d8b3,0x63f46163,0x51e623fc,0xcc599383,0xf18f270f,
        0x055590ee,0x06a38e28 } },
    /* 180 */
    { { 0xb3355b49,0x2e5b0139,0xb4ebf99b,0x20e26560,0xd269f3dc,0xc08ffa6b,
        0x83d9d4f8,0xa7b36c20 },
      { 0x1b3e8830,0x64d15c3a,0xa89f9c0b,0xd5fceae1,0xe2d16930,0xcfeee4a2,
        0xa2822a20,0xbe54c6b4 } },
    /* 181 */
    { { 0x8d91167c,0xd6cdb3df,0xe7a6625e,0x517c3f79,0x346ac7f4,0x7105648f,
        0xeae022bb,0xbf30a5ab },
      { 0x93828a68,0x8e7785be,0x7f3ef036,0x5161c332,0x592146b2,0xe11b5feb,
        0x2732d13a,0xd1c820de } },
    /* 182 */
    { { 0x9038b363,0x043e1347,0x6b05e519,0x58c11f54,0x6026cad1,0x4fe57abe,
        0x68a18da3,0xb7d17bed },
      { 0xe29c2559,0x44ca5891,0x5bfffd84,0x4f7a0376,0x74e46948,0x498de4af,
        0x6412cc64,0x3997fd5e } },
    /* 183 */
    { { 0x8bd61507,0xf2074682,0x34a64d2a,0x29e132d5,0x8a8a15e3,0xffeddfb0,
        0x3c6c13e8,0x0eeb8929 },
      { 0xa7e259f8,0xe9b69a3e,0xd13e7e67,0xce1db7e6,0xad1fa685,0x277318f6,
        0xc922b6ef,0x228916f8 } },
    /* 184 */
    { { 0x0a12ab5b,0x959ae25b,0x957bc136,0xcc11171f,0xd16e2b0c,0x8058429e,
        0x6e93097e,0xec05ad1d },
      { 0xac3f3708,0x157ba5be,0x30b59d77,0x31baf935,0x118234e5,0x47b55237,
        0x7ff11b37,0x7d314156 } },
    /* 185 */
    { { 0xf6dfefab,0x7bd9c05c,0xdcb37707,0xbe2f2268,0x3a38bb95,0xe53ead97,
        0x9bc1d7a3,0xe9ce66fc },
      { 0x6f6a02a1,0x75aa1576,0x60e600ed,0x38c087df,0x68cdc1b9,0xf8947f34,
        0x72280651,0xd9650b01 } },
    /* 186 */
    { { 0x5a057e60,0x504b4c4a,0x8def25e4,0xcbccc3be,0x17c1ccbd,0xa6353208,
        0x804eb7a2,0x14d6699a },
      { 0xdb1f411a,0x2c8a8415,0xf80d769c,0x09fbaf0b,0x1c2f77ad,0xb4deef90,
        0x0d43598a,0x6f4c6841 } },
    /* 187 */
    { { 0x96c24a96,0x8726df4e,0xfcbd99a3,0x534dbc85,0x8b2ae30a,0x3c466ef2,
        0x61189abb,0x4c4350fd },
      { 0xf855b8da,0x2967f716,0x463c38a1,0x41a42394,0xeae93343,0xc37e1413,
        0x5a3118b5,0xa726d242 } },
    /* 188 */
    { { 0x948c1086,0xdae6b3ee,0xcbd3a2e1,0xf1de503d,0x03d022f3,0x3f35ed3f,
        0xcc6cf392,0x13639e82 },
      { 0xcdafaa86,0x9ac938fb,0x2654a258,0xf45bc5fb,0x45051329,0x1963b26e,
        0xc1a335a3,0xca9365e1 } },
    /* 189 */
    { { 0x4c3b2d20,0x3615ac75,0x904e241b,0x742a5417,0xcc9d071d,0xb08521c4,
        0x970b72a5,0x9ce29c34 },
      { 0x6d3e0ad6,0x8cc81f73,0xf2f8434c,0x8060da9e,0x6ce862d9,0x35ed1d1a,
        0xab42af98,0x48c4abd7 } },
    /* 190 */
    { { 0x40c7485a,0xd221b0cc,0xe5274dbf,0xead455bb,0x9263d2e8,0x493c7698,
        0xf67b33cb,0x78017c32 },
      { 0x930cb5ee,0xb9d35769,0x0c408ed2,0xc0d14e94,0x272f1a4d,0xf8b7bf55,
        0xde5c1c04,0x53cd0454 } },
    /* 191 */
    { { 0x5d28ccac,0xbcd585fa,0x005b746e,0x5f823e56,0xcd0123aa,0x7c79f0a1,
        0xd3d7fa8f,0xeea465c1 },
      { 0x0551803b,0x7810659f,0x7ce6af70,0x6c0b599f,0x29288e70,0x4195a770,
        0x7ae69193,0x1b6e42a4 } },
    /* 192 */
    { { 0xf67d04c3,0x2e80937c,0x89eeb811,0x1e312be2,0x92594d60,0x56b5d887,
        0x187fbd3d,0x0224da14 },
      { 0x0c5fe36f,0x87abb863,0x4ef51f5f,0x580f3c60,0xb3b429ec,0x964fb1bf,
        0x42bfff33,0x60838ef0 } },
    /* 193 */
    { { 0x7e0bbe99,0x432cb2f2,0x04aa39ee,0x7bda44f3,0x9fa93903,0x5f497c7a,
        0x2d331643,0x636eb202 },
      { 0x93ae00aa,0xfcfd0e61,0x31ae6d2f,0x875a00fe,0x9f93901c,0xf43658a2,
        0x39218bac,0x8844eeb6 } },
    /* 194 */
    { { 0x6b3bae58,0x114171d2,0x17e39f3e,0x7db3df71,0x81a8eada,0xcd37bc7f,
        0x51fb789e,0x27ba83dc },
      { 0xfbf54de5,0xa7df439f,0xb5fe1a71,0x7277030b,0xdb297a48,0x42ee8e35,
        0x87f3a4ab,0xadb62d34 } },
    /* 195 */
    { { 0xa175df2a,0x9b1168a2,0x618c32e9,0x082aa04f,0x146b0916,0xc9e4f2e7,
        0x75e7c8b2,0xb990fd76 },
      { 0x4df37313,0x0829d96b,0xd0b40789,0x1c205579,0x78087711,0x66c9ae4a,
        0x4d10d18d,0x81707ef9 } },
    /* 196 */
    { { 0x03d6ff96,0x97d7cab2,0x0d843360,0x5b851bfc,0xd042db4b,0x268823c4,
        0xd5a8aa5c,0x3792daea },
      { 0x941afa0b,0x52818865,0x42d83671,0xf3e9e741,0x5be4e0a7,0x17c82527,
        0x94b001ba,0x5abd635e } },
    /* 197 */
    { { 0x0ac4927c,0x727fa84e,0xa7c8cf23,0xe3886035,0x4adca0df,0xa4bcd5ea,
        0x846ab610,0x5995bf21 },
      { 0x829dfa33,0xe90f860b,0x958fc18b,0xcaafe2ae,0x78630366,0x9b3baf44,
        0xd483411e,0x44c32ca2 } },
    /* 198 */
    { { 0xe40ed80c,0xa74a97f1,0x31d2ca82,0x5f938cb1,0x7c2d6ad9,0x53f2124b,
        0x8082a54c,0x1f2162fb },
      { 0x720b173e,0x7e467cc5,0x085f12f9,0x40e8a666,0x4c9d65dc,0x8cebc20e,
        0xc3e907c9,0x8f1d402b } },
    /* 199 */
    { { 0xfbc4058a,0x4f592f9c,0x292f5670,0xb15e14b6,0xbc1d8c57,0xc55cfe37,
        0x926edbf9,0xb1980f43 },
      { 0x32c76b09,0x98c33e09,0x33b07f78,0x1df5279d,0x863bb461,0x6f08ead4,
        0x37448e45,0x2828ad9b } },
    /* 200 */
    { { 0xc4cf4ac5,0x696722c4,0xdde64afb,0xf5ac1a3f,0xe0890832,0x0551baa2,
        0x5a14b390,0x4973f127 },
      { 0x322eac5d,0xe59d8335,0x0bd9b568,0x5e07eef5,0xa2588393,0xab36720f,
        0xdb168ac7,0x6dac8ed0 } },
    /* 201 */
    { { 0xeda835ef,0xf7b545ae,0x1d10ed51,0x4aa113d2,0x13741b09,0x035a65e0,
        0x20b9de4c,0x4b23ef59 },
      { 0x3c4c7341,0xe82bb680,0x3f58bc37,0xd457706d,0xa51e3ee8,0x73527863,
        0xddf49a4e,0x4dd71534 } },
    /* 202 */
    { { 0x95476cd9,0xbf944672,0xe31a725b,0x648d072f,0xfc4b67e0,0x1441c8b8,
        0x2f4a4dbb,0xfd317000 },
      { 0x8995d0e1,0x1cb43ff4,0x0ef729aa,0x76e695d1,0x41798982,0xe0d5f976,
        0x9569f365,0x14fac58c } },
    /* 203 */
    { { 0xf312ae18,0xad9a0065,0xfcc93fc9,0x51958dc0,0x8a7d2846,0xd9a14240,
        0x36abda50,0xed7c7651 },
      { 0x25d4abbc,0x46270f1a,0xf1a113ea,0x9b5dd8f3,0x5b51952f,0xc609b075,
        0x4d2e9f53,0xfefcb7f7 } },
    /* 204 */
    { { 0xba119185,0xbd09497a,0xaac45ba4,0xd54e8c30,0xaa521179,0x492479de,
        0x87e0d80b,0x1801a57e },
      { 0xfcafffb0,0x073d3f8d,0xae255240,0x6cf33c0b,0x5b5fdfbc,0x781d763b,
        0x1ead1064,0x9f8fc11e } },
    /* 205 */
    { { 0x5e69544c,0x1583a171,0xf04b7813,0x0eaf8567,0x278a4c32,0x1e22a8fd,
        0x3d3a69a9,0xa9d3809d },
      { 0x59a2da3b,0x936c2c2c,0x1895c847,0x38ccbcf6,0x63d50869,0x5e65244e,
        0xe1178ef7,0x3006b9ae } },
    /* 206 */
    { { 0xc9eead28,0x0bb1f2b0,0x89f4dfbc,0x7eef635d,0xb2ce8939,0x074757fd,
        0x45f8f761,0x0ab85fd7 },
      { 0x3e5b4549,0xecda7c93,0x97922f21,0x4be2bb5c,0xb43b8040,0x261a1274,
        0x11e942c2,0xb122d675 } },
    /* 207 */
    { { 0x66a5ae7a,0x3be607be,0x76adcbe3,0x01e703fa,0x4eb6e5c5,0xaf904301,
        0x097dbaec,0x9f599dc1 },
      { 0x0ff250ed,0x6d75b718,0x349a20dc,0x8eb91574,0x10b227a3,0x425605a4,
        0x8a294b78,0x7d5528e0 } },
    /* 208 */
    { { 0x20c26def,0xf0f58f66,0x582b2d1e,0x025585ea,0x01ce3881,0xfbe7d79b,
        0x303f1730,0x28ccea01 },
      { 0x79644ba5,0xd1dabcd1,0x06fff0b8,0x1fc643e8,0x66b3e17b,0xa60a76fc,
        0xa1d013bf,0xc18baf48 } },
    /* 209 */
    { { 0x5dc4216d,0x34e638c8,0x206142ac,0x00c01067,0x95f5064a,0xd453a171,
        0xb7a9596b,0x9def809d },
      { 0x67ab8d2c,0x41e8642e,0x6237a2b6,0xb4240433,0x64c4218b,0x7d506a6d,
        0x68808ce5,0x0357f8b0 } },
    /* 210 */
    { { 0x4cd2cc88,0x8e9dbe64,0xf0b8f39d,0xcc61c28d,0xcd30a0c8,0x4a309874,
        0x1b489887,0xe4a01add },
      { 0xf57cd8f9,0x2ed1eeac,0xbd594c48,0x1b767d3e,0x7bd2f787,0xa7295c71,
        0xce10cc30,0x466d7d79 } },
    /* 211 */
    { { 0x9dada2c7,0x47d31892,0x8f9aa27d,0x4fa0a6c3,0x820a59e1,0x90e4fd28,
        0x451ead1a,0xc672a522 },
      { 0x5d86b655,0x30607cc8,0xf9ad4af1,0xf0235d3b,0x571172a6,0x99a08680,
        0xf2a67513,0x5e3d64fa } },
    /* 212 */
    { { 0x9b3b4416,0xaa6410c7,0xeab26d99,0xcd8fcf85,0xdb656a74,0x5ebff74a,
        0xeb8e42fc,0x6c8a7a95 },
      { 0xb02a63bd,0x10c60ba7,0x8b8f0047,0x6b2f2303,0x312d90b0,0x8c6c3738,
        0xad82ca91,0x348ae422 } },
    /* 213 */
    { { 0x5ccda2fb,0x7f474663,0x8e0726d2,0x22accaa1,0x492b1f20,0x85adf782,
        0xd9ef2d2e,0xc1074de0 },
      { 0xae9a65b3,0xfcf3ce44,0x05d7151b,0xfd71e4ac,0xce6a9788,0xd4711f50,
        0xc9e54ffc,0xfbadfbdb } },
    /* 214 */
    { { 0x20a99363,0x1713f1cd,0x6cf22775,0xb915658f,0x24d359b2,0x968175cd,
        0x83716fcd,0xb7f976b4 },
      { 0x5d6dbf74,0x5758e24d,0x71c3af36,0x8d23bafd,0x0243dfe3,0x48f47760,
        0xcafcc805,0xf4d41b2e } },
    /* 215 */
    { { 0xfdabd48d,0x51f1cf28,0x32c078a4,0xce81be36,0x117146e9,0x6ace2974,
        0xe0160f10,0x180824ea },
      { 0x66e58358,0x0387698b,0xce6ca358,0x63568752,0x5e41e6c5,0x82380e34,
        0x83cf6d25,0x67e5f639 } },
    /* 216 */
    { { 0xcf4899ef,0xf89ccb8d,0x9ebb44c0,0x949015f0,0xb2598ec9,0x546f9276,
        0x04c11fc6,0x9fef789a },
      { 0x53d2a071,0x6d367ecf,0xa4519b09,0xb10e1a7f,0x611e2eef,0xca6b3fb0,
        0xa99c4e20,0xbc80c181 } },
    /* 217 */
    { { 0xe5eb82e6,0x972536f8,0xf56cb920,0x1a484fc7,0x50b5da5e,0xc78e2171,
        0x9f8cdf10,0x49270e62 },
      { 0xea6b50ad,0x1a39b7bb,0xa2388ffc,0x9a0284c1,0x8107197b,0x5403eb17,
        0x61372f7f,0xd2ee52f9 } },
    /* 218 */
    { { 0x88e0362a,0xd37cd285,0x8fa5d94d,0x442fa8a7,0xa434a526,0xaff836e5,
        0xe5abb733,0xdfb478be },
      { 0x673eede6,0xa91f1ce7,0x2b5b2f04,0xa5390ad4,0x5530da2f,0x5e66f7bf,
        0x08df473a,0xd9a140b4 } },
    /* 219 */
    { { 0x6e8ea498,0x0e0221b5,0x3563ee09,0x62347829,0x335d2ade,0xe06b8391,
        0x623f4b1a,0x760c058d },
      { 0xc198aa79,0x0b89b58c,0xf07aba7f,0xf74890d2,0xfde2556a,0x4e204110,
        0x8f190409,0x7141982d } },
    /* 220 */
    { { 0x4d4b0f45,0x6f0a0e33,0x392a94e1,0xd9280b38,0xb3c61d5e,0x3af324c6,
        0x89d54e47,0x3af9d1ce },
      { 0x20930371,0xfd8f7981,0x21c17097,0xeda2664c,0xdc42309b,0x0e9545dc,
        0x73957dd6,0xb1f815c3 } },
    /* 221 */
    { { 0x89fec44a,0x84faa78e,0x3caa4caf,0xc8c2ae47,0xc1b6a624,0x691c807d,
        0x1543f052,0xa41aed14 },
      { 0x7d5ffe04,0x42435399,0x625b6e20,0x8bacb2df,0x87817775,0x85d660be,
        0x86fb60ef,0xd6e9c1dd } },
    /* 222 */
    { { 0xc6853264,0x3aa2e97e,0xe2304a0b,0x771533b7,0xb8eae9be,0x1b912bb7,
        0xae9bf8c2,0x9c9c6e10 },
      { 0xe030b74c,0xa2309a59,0x6a631e90,0x4ed7494d,0xa49b79f2,0x89f44b23,
        0x40fa61b6,0x566bd596 } },
    /* 223 */
    { { 0xc18061f3,0x066c0118,0x7c83fc70,0x190b25d3,0x27273245,0xf05fc8e0,
        0xf525345e,0xcf2c7390 },
      { 0x10eb30cf,0xa09bceb4,0x0d77703a,0xcfd2ebba,0x150ff255,0xe842c43a,
        0x8aa20979,0x02f51755 } },
    /* 224 */
    { { 0xaddb7d07,0x396ef794,0x24455500,0x0b4fc742,0xc78aa3ce,0xfaff8eac,
        0xe8d4d97d,0x14e9ada5 },
      { 0x2f7079e2,0xdaa480a1,0xe4b0800e,0x45baa3cd,0x7838157d,0x01765e2d,
        0x8e9d9ae8,0xa0ad4fab } },
    /* 225 */
    { { 0x4a653618,0x0bfb7621,0x31eaaa5f,0x1872813c,0x44949d5e,0x1553e737,
        0x6e56ed1e,0xbcd530b8 },
      { 0x32e9c47b,0x169be853,0xb50059ab,0xdc2776fe,0x192bfbb4,0xcdba9761,
        0x6979341d,0x909283cf } },
    /* 226 */
    { { 0x76e81a13,0x67b00324,0x62171239,0x9bee1a99,0xd32e19d6,0x08ed361b,
        0xace1549a,0x35eeb7c9 },
      { 0x7e4e5bdc,0x1280ae5a,0xb6ceec6e,0x2dcd2cd3,0x6e266bc1,0x52e4224c,
        0x448ae864,0x9a8b2cf4 } },
    /* 227 */
    { { 0x09d03b59,0xf6471bf2,0xb65af2ab,0xc90e62a3,0xebd5eec9,0xff7ff168,
        0xd4491379,0x6bdb60f4 },
      { 0x8a55bc30,0xdadafebc,0x10097fe0,0xc79ead16,0x4c1e3bdd,0x42e19741,
        0x94ba08a9,0x01ec3cfd } },
    /* 228 */
    { { 0xdc9485c2,0xba6277eb,0x22fb10c7,0x48cc9a79,0x70a28d8a,0x4f61d60f,
        0x475464f6,0xd1acb1c0 },
      { 0x26f36612,0xd26902b1,0xe0618d8b,0x59c3a44e,0x308357ee,0x4df8a813,
        0x405626c2,0x7dcd079d } },
    /* 229 */
    { { 0xf05a4b48,0x5ce7d4d3,0x37230772,0xadcd2952,0x812a915a,0xd18f7971,
        0x377d19b8,0x0bf53589 },
      { 0x6c68ea73,0x35ecd95a,0x823a584d,0xc7f3bbca,0xf473a723,0x9fb674c6,
        0xe16686fc,0xd28be4d9 } },
    /* 230 */
    { { 0x38fa8e4b,0x5d2b9906,0x893fd8fc,0x559f186e,0x436fb6fc,0x3a6de2aa,
        0x510f88ce,0xd76007aa },
      { 0x523a4988,0x2d10aab6,0x74dd0273,0xb455cf44,0xa3407278,0x7f467082,
        0xb303bb01,0xf2b52f68 } },
    /* 231 */
    { { 0x9835b4ca,0x0d57eafa,0xbb669cbc,0x2d2232fc,0xc6643198,0x8eeeb680,
        0xcc5aed3a,0xd8dbe98e },
      { 0xc5a02709,0xcba9be3f,0xf5ba1fa8,0x30be68e5,0xf10ea852,0xfebd43cd,
        0xee559705,0xe01593a3 } },
    /* 232 */
    { { 0xea75a0a6,0xd3e5af50,0x57858033,0x512226ac,0xd0176406,0x6fe6d50f,
        0xaeb8ef06,0xafec07b1 },
      { 0x80bb0a31,0x7fb99567,0x37309aae,0x6f1af3cc,0x01abf389,0x9153a15a,
        0x6e2dbfdd,0xa71b9354 } },
    /* 233 */
    { { 0x18f593d2,0xbf8e12e0,0xa078122b,0xd1a90428,0x0ba4f2ad,0x150505db,
        0x628523d9,0x53a2005c },
      { 0xe7f2b935,0x07c8b639,0xc182961a,0x2bff975a,0x7518ca2c,0x86bceea7,
        0x3d588e3d,0xbf47d19b } },
    /* 234 */
    { { 0xdd7665d5,0x672967a7,0x2f2f4de5,0x4e303057,0x80d4903f,0x144005ae,
        0x39c9a1b6,0x001c2c7f },
      { 0x69efc6d6,0x143a8014,0x7bc7a724,0xc810bdaa,0xa78150a4,0x5f65670b,
        0x86ffb99b,0xfdadf8e7 } },
    /* 235 */
    { { 0xffc00785,0xfd38cb88,0x3b48eb67,0x77fa7591,0xbf368fbc,0x0454d055,
        0x5aa43c94,0x3a838e4d },
      { 0x3e97bb9a,0x56166329,0x441d94d9,0x9eb93363,0x0adb2a83,0x515591a6,
        0x873e1da3,0x3cdb8257 } },
    /* 236 */
    { { 0x7de77eab,0x137140a9,0x41648109,0xf7e1c50d,0xceb1d0df,0x762dcad2,
        0xf1f57fba,0x5a60cc89 },
      { 0x40d45673,0x80b36382,0x5913c655,0x1b82be19,0xdd64b741,0x057284b8,
        0xdbfd8fc0,0x922ff56f } },
    /* 237 */
    { { 0xc9a129a1,0x1b265dee,0xcc284e04,0xa5b1ce57,0xcebfbe3c,0x04380c46,
        0xf6c5cd62,0x72919a7d },
      { 0x8fb90f9a,0x298f453a,0x88e4031b,0xd719c00b,0x796f1856,0xe32c0e77,
        0x3624089a,0x5e791780 } },
    /* 238 */
    { { 0x7f63cdfb,0x5c16ec55,0xf1cae4fd,0x8e6a3571,0x560597ca,0xfce26bea,
        0xe24c2fab,0x4e0a5371 },
      { 0xa5765357,0x276a40d3,0x0d73a2b4,0x3c89af44,0x41d11a32,0xb8f370ae,
        0xd56604ee,0xf5ff7818 } },
    /* 239 */
    { { 0x1a09df21,0xfbf3e3fe,0xe66e8e47,0x26d5d28e,0x29c89015,0x2096bd0a,
        0x533f5e64,0xe41df0e9 },
      { 0xb3ba9e3f,0x305fda40,0x2604d895,0xf2340ceb,0x7f0367c7,0x0866e192,
        0xac4f155f,0x8edd7d6e } },
    /* 240 */
    { { 0x0bfc8ff3,0xc9a1dc0e,0xe936f42f,0x14efd82b,0xcca381ef,0x67016f7c,
        0xed8aee96,0x1432c1ca },
      { 0x70b23c26,0xec684829,0x0735b273,0xa64fe873,0xeaef0f5a,0xe389f6e5,
        0x5ac8d2c6,0xcaef480b } },
    /* 241 */
    { { 0x75315922,0x5245c978,0x3063cca5,0xd8295171,0xb64ef2cb,0xf3ce60d0,
        0x8efae236,0xd0ba177e },
      { 0xb1b3af60,0x53a9ae8f,0x3d2da20e,0x1a796ae5,0xdf9eef28,0x01d63605,
        0x1c54ae16,0xf31c957c } },
    /* 242 */
    { { 0x49cc4597,0xc0f58d52,0xbae0a028,0xdc5015b0,0x734a814a,0xefc5fc55,
        0x96e17c3a,0x013404cb },
      { 0xc9a824bf,0xb29e2585,0x001eaed7,0xd593185e,0x61ef68ac,0x8d6ee682,
        0x91933e6c,0x6f377c4b } },
    /* 243 */
    { { 0xa8333fd2,0x9f93bad1,0x5a2a95b8,0xa8930202,0xeaf75ace,0x211e5037,
        0xd2d09506,0x6dba3e4e },
      { 0xd04399cd,0xa48ef98c,0xe6b73ade,0x1811c66e,0xc17ecaf3,0x72f60752,
        0x3becf4a7,0xf13cf342 } },
    /* 244 */
    { { 0xa919e2eb,0xceeb9ec0,0xf62c0f68,0x83a9a195,0x7aba2299,0xcfba3bb6,
        0x274bbad3,0xc83fa9a9 },
      { 0x62fa1ce0,0x0d7d1b0b,0x3418efbf,0xe58b60f5,0x52706f04,0xbfa8ef9e,
        0x5d702683,0xb49d70f4 } },
    /* 245 */
    { { 0xfad5513b,0x914c7510,0xb1751e2d,0x05f32eec,0xd9fb9d59,0x6d850418,
        0x0c30f1cf,0x59cfadbb },
      { 0x55cb7fd6,0xe167ac23,0x820426a3,0x249367b8,0x90a78864,0xeaeec58c,
        0x354a4b67,0x5babf362 } },
    /* 246 */
    { { 0xee424865,0x37c981d1,0xf2e5577f,0x8b002878,0xb9e0c058,0x702970f1,
        0x9026c8f0,0x6188c6a7 },
      { 0xd0f244da,0x06f9a19b,0xfb080873,0x1ecced5c,0x9f213637,0x35470f9b,
        0xdf50b9d9,0x993fe475 } },
    /* 247 */
    { { 0x9b2c3609,0x68e31cdf,0x2c46d4ea,0x84eb19c0,0x9a775101,0x7ac9ec1a,
        0x4c80616b,0x81f76466 },
      { 0x75fbe978,0x1d7c2a5a,0xf183b356,0x6743fed3,0x501dd2bf,0x838d1f04,
        0x5fe9060d,0x564a812a } },
    /* 248 */
    { { 0xfa817d1d,0x7a5a64f4,0xbea82e0f,0x55f96844,0xcd57f9aa,0xb5ff5a0f,
        0x00e51d6c,0x226bf3cf },
      { 0x2f2833cf,0xd6d1a9f9,0x4f4f89a8,0x20a0a35a,0x8f3f7f77,0x11536c49,
        0xff257836,0x68779f47 } },
    /* 249 */
    { { 0x73043d08,0x79b0c1c1,0x1fc020fa,0xa5446774,0x9a6d26d0,0xd3767e28,
        0xeb092e0b,0x97bcb0d1 },
      { 0xf32ed3c3,0x2ab6eaa8,0xb281bc48,0xc8a4f151,0xbfa178f3,0x4d1bf4f3,
        0x0a784655,0xa872ffe8 } },
    /* 250 */
    { { 0xa32b2086,0xb1ab7935,0x8160f486,0xe1eb710e,0x3b6ae6be,0x9bd0cd91,
        0xb732a36a,0x02812bfc },
      { 0xcf605318,0xa63fd7ca,0xfdfd6d1d,0x646e5d50,0x2102d619,0xa1d68398,
        0xfe5396af,0x07391cc9 } },
    /* 251 */
    { { 0x8b80d02b,0xc50157f0,0x62877f7f,0x6b8333d1,0x78d542ae,0x7aca1af8,
        0x7e6d2a08,0x355d2adc },
      { 0x287386e1,0xb41f335a,0xf8e43275,0xfd272a94,0xe79989ea,0x286ca2cd,
        0x7c2a3a79,0x3dc2b1e3 } },
    /* 252 */
    { { 0x04581352,0xd689d21c,0x376782be,0x0a00c825,0x9fed701f,0x203bd590,
        0x3ccd846b,0xc4786910 },
      { 0x24c768ed,0x5dba7708,0x6841f657,0x72feea02,0x6accce0e,0x73313ed5,
        0xd5bb4d32,0xccc42968 } },
    /* 253 */
    { { 0x3d7620b9,0x94e50de1,0x5992a56a,0xd89a5c8a,0x675487c9,0xdc007640,
        0xaa4871cf,0xe147eb42 },
      { 0xacf3ae46,0x274ab4ee,0x50350fbe,0xfd4936fb,0x48c840ea,0xdf2afe47,
        0x080e96e3,0x239ac047 } },
    /* 254 */
    { { 0x2bfee8d4,0x481d1f35,0xfa7b0fec,0xce80b5cf,0x2ce9af3c,0x105c4c9e,
        0xf5f7e59d,0xc55fa1a3 },
      { 0x8257c227,0x3186f14e,0x342be00b,0xc5b1653f,0xaa904fb2,0x09afc998,
        0xd4f4b699,0x094cd99c } },
    /* 255 */
    { { 0xd703beba,0x8a981c84,0x32ceb291,0x8631d150,0xe3bd49ec,0xa445f2c9,
        0x42abad33,0xb90a30b6 },
      { 0xb4a5abf9,0xb465404f,0x75db7603,0x004750c3,0xca35d89f,0x6f9a42cc,
        0x1b7924f7,0x019f8b9a } },
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
static int sp_256_ecc_mulmod_base_8(sp_point_256* r, const sp_digit* k,
        int map, int ct, void* heap)
{
    return sp_256_ecc_mulmod_stripe_8(r, &p256_base, p256_table,
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
    sp_digit kd[8];
#endif
    sp_point_256* point;
    sp_digit* k = NULL;
    int err = MP_OKAY;

    err = sp_256_point_new_8(heap, p, point);
#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (err == MP_OKAY) {
        k = (sp_digit*)XMALLOC(sizeof(sp_digit) * 8, heap,
                                                              DYNAMIC_TYPE_ECC);
        if (k == NULL) {
            err = MEMORY_E;
        }
    }
#else
    k = kd;
#endif
    if (err == MP_OKAY) {
        sp_256_from_mp(k, 8, km);

            err = sp_256_ecc_mulmod_base_8(point, k, map, 1, heap);
    }
    if (err == MP_OKAY) {
        err = sp_256_point_to_ecc_point_8(point, r);
    }

#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (k != NULL) {
        XFREE(k, heap, DYNAMIC_TYPE_ECC);
    }
#endif
    sp_256_point_free_8(point, 0, heap);

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
static int sp_256_iszero_8(const sp_digit* a)
{
    return (a[0] | a[1] | a[2] | a[3] | a[4] | a[5] | a[6] | a[7]) == 0;
}

#endif /* WOLFSSL_VALIDATE_ECC_KEYGEN || HAVE_ECC_SIGN || HAVE_ECC_VERIFY */
/* Add 1 to a. (a = a + 1)
 *
 * a  A single precision integer.
 */
SP_NOINLINE static void sp_256_add_one_8(sp_digit* a)
{
    __asm__ __volatile__ (
        "mov	r2, #1\n\t"
        "ldr	r1, [%[a], #0]\n\t"
        "adds	r1, r1, r2\n\t"
        "mov	r2, #0\n\t"
        "str	r1, [%[a], #0]\n\t"
        "ldr	r1, [%[a], #4]\n\t"
        "adcs	r1, r1, r2\n\t"
        "str	r1, [%[a], #4]\n\t"
        "ldr	r1, [%[a], #8]\n\t"
        "adcs	r1, r1, r2\n\t"
        "str	r1, [%[a], #8]\n\t"
        "ldr	r1, [%[a], #12]\n\t"
        "adcs	r1, r1, r2\n\t"
        "str	r1, [%[a], #12]\n\t"
        "ldr	r1, [%[a], #16]\n\t"
        "adcs	r1, r1, r2\n\t"
        "str	r1, [%[a], #16]\n\t"
        "ldr	r1, [%[a], #20]\n\t"
        "adcs	r1, r1, r2\n\t"
        "str	r1, [%[a], #20]\n\t"
        "ldr	r1, [%[a], #24]\n\t"
        "adcs	r1, r1, r2\n\t"
        "str	r1, [%[a], #24]\n\t"
        "ldr	r1, [%[a], #28]\n\t"
        "adcs	r1, r1, r2\n\t"
        "str	r1, [%[a], #28]\n\t"
        :
        : [a] "r" (a)
        : "memory", "r1", "r2"
    );
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
        if (s >= 24U) {
            r[j] &= 0xffffffff;
            s = 32U - s;
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
static int sp_256_ecc_gen_k_8(WC_RNG* rng, sp_digit* k)
{
    int err;
    byte buf[32];

    do {
        err = wc_RNG_GenerateBlock(rng, buf, sizeof(buf));
        if (err == 0) {
            sp_256_from_bin(k, 8, buf, (int)sizeof(buf));
            if (sp_256_cmp_8(k, p256_order2) < 0) {
                sp_256_add_one_8(k);
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
    sp_digit kd[8];
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

    err = sp_256_point_new_8(heap, p, point);
#ifdef WOLFSSL_VALIDATE_ECC_KEYGEN
    if (err == MP_OKAY) {
        err = sp_256_point_new_8(heap, inf, infinity);
    }
#endif
#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (err == MP_OKAY) {
        k = (sp_digit*)XMALLOC(sizeof(sp_digit) * 8, heap,
                                                              DYNAMIC_TYPE_ECC);
        if (k == NULL) {
            err = MEMORY_E;
        }
    }
#else
    k = kd;
#endif

    if (err == MP_OKAY) {
        err = sp_256_ecc_gen_k_8(rng, k);
    }
    if (err == MP_OKAY) {
            err = sp_256_ecc_mulmod_base_8(point, k, 1, 1, NULL);
    }

#ifdef WOLFSSL_VALIDATE_ECC_KEYGEN
    if (err == MP_OKAY) {
            err = sp_256_ecc_mulmod_8(infinity, point, p256_order, 1, 1, NULL);
    }
    if (err == MP_OKAY) {
        if (sp_256_iszero_8(point->x) || sp_256_iszero_8(point->y)) {
            err = ECC_INF_E;
        }
    }
#endif

    if (err == MP_OKAY) {
        err = sp_256_to_mp(k, priv);
    }
    if (err == MP_OKAY) {
        err = sp_256_point_to_ecc_point_8(point, pub);
    }

#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (k != NULL) {
        XFREE(k, heap, DYNAMIC_TYPE_ECC);
    }
#endif
#ifdef WOLFSSL_VALIDATE_ECC_KEYGEN
    sp_256_point_free_8(infinity, 1, heap);
#endif
    sp_256_point_free_8(point, 1, heap);

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

    j = 256 / 8 - 1;
    a[j] = 0;
    for (i=0; i<8 && j>=0; i++) {
        b = 0;
        /* lint allow cast of mismatch sp_digit and int */
        a[j--] |= (byte)(r[i] << s); /*lint !e9033*/
        b += 8 - s;
        if (j < 0) {
            break;
        }
        while (b < 32) {
            a[j--] = (byte)(r[i] >> b);
            b += 8;
            if (j < 0) {
                break;
            }
        }
        s = 8 - (b - 32);
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
    sp_digit kd[8];
#endif
    sp_point_256* point = NULL;
    sp_digit* k = NULL;
    int err = MP_OKAY;

    if (*outLen < 32U) {
        err = BUFFER_E;
    }

    if (err == MP_OKAY) {
        err = sp_256_point_new_8(heap, p, point);
    }
#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (err == MP_OKAY) {
        k = (sp_digit*)XMALLOC(sizeof(sp_digit) * 8, heap,
                                                              DYNAMIC_TYPE_ECC);
        if (k == NULL)
            err = MEMORY_E;
    }
#else
    k = kd;
#endif

    if (err == MP_OKAY) {
        sp_256_from_mp(k, 8, priv);
        sp_256_point_from_ecc_point_8(point, pub);
            err = sp_256_ecc_mulmod_8(point, point, k, 1, 1, heap);
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
    sp_256_point_free_8(point, 0, heap);

    return err;
}
#endif /* HAVE_ECC_DHE */

#if defined(HAVE_ECC_SIGN) || defined(HAVE_ECC_VERIFY)
/* Multiply a and b into r. (r = a * b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A single precision integer.
 */
SP_NOINLINE static void sp_256_mul_8(sp_digit* r, const sp_digit* a,
        const sp_digit* b)
{
    sp_digit tmp[8];

    __asm__ __volatile__ (
        /* A[0] * B[0] */
        "ldr	r6, [%[a], #0]\n\t"
        "ldr	r8, [%[b], #0]\n\t"
        "umull	r3, r4, r6, r8\n\t"
        "mov	r5, #0\n\t"
        "str	r3, [%[tmp], #0]\n\t"
        "mov	r3, #0\n\t"
        /* A[0] * B[1] */
        "ldr	r8, [%[b], #4]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r4, r4, r6\n\t"
        "adc	r5, r5, r8\n\t"
        /* A[1] * B[0] */
        "ldr	r6, [%[a], #4]\n\t"
        "ldr	r8, [%[b], #0]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r4, r4, r6\n\t"
        "adcs 	r5, r5, r8\n\t"
        "adc	r3, r3, #0\n\t"
        "str	r4, [%[tmp], #4]\n\t"
        "mov	r4, #0\n\t"
        /* A[0] * B[2] */
        "ldr	r6, [%[a], #0]\n\t"
        "ldr	r8, [%[b], #8]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r5, r5, r6\n\t"
        "adcs 	r3, r3, r8\n\t"
        "adc	r4, r4, #0\n\t"
        /* A[1] * B[1] */
        "ldr	r6, [%[a], #4]\n\t"
        "ldr	r8, [%[b], #4]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r5, r5, r6\n\t"
        "adcs 	r3, r3, r8\n\t"
        "adc	r4, r4, #0\n\t"
        /* A[2] * B[0] */
        "ldr	r6, [%[a], #8]\n\t"
        "ldr	r8, [%[b], #0]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r5, r5, r6\n\t"
        "adcs 	r3, r3, r8\n\t"
        "adc	r4, r4, #0\n\t"
        "str	r5, [%[tmp], #8]\n\t"
        "mov	r5, #0\n\t"
        /* A[0] * B[3] */
        "ldr	r6, [%[a], #0]\n\t"
        "ldr	r8, [%[b], #12]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r3, r3, r6\n\t"
        "adcs 	r4, r4, r8\n\t"
        "adc	r5, r5, #0\n\t"
        /* A[1] * B[2] */
        "ldr	r6, [%[a], #4]\n\t"
        "ldr	r8, [%[b], #8]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r3, r3, r6\n\t"
        "adcs 	r4, r4, r8\n\t"
        "adc	r5, r5, #0\n\t"
        /* A[2] * B[1] */
        "ldr	r6, [%[a], #8]\n\t"
        "ldr	r8, [%[b], #4]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r3, r3, r6\n\t"
        "adcs 	r4, r4, r8\n\t"
        "adc	r5, r5, #0\n\t"
        /* A[3] * B[0] */
        "ldr	r6, [%[a], #12]\n\t"
        "ldr	r8, [%[b], #0]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r3, r3, r6\n\t"
        "adcs 	r4, r4, r8\n\t"
        "adc	r5, r5, #0\n\t"
        "str	r3, [%[tmp], #12]\n\t"
        "mov	r3, #0\n\t"
        /* A[0] * B[4] */
        "ldr	r6, [%[a], #0]\n\t"
        "ldr	r8, [%[b], #16]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r4, r4, r6\n\t"
        "adcs 	r5, r5, r8\n\t"
        "adc	r3, r3, #0\n\t"
        /* A[1] * B[3] */
        "ldr	r6, [%[a], #4]\n\t"
        "ldr	r8, [%[b], #12]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r4, r4, r6\n\t"
        "adcs 	r5, r5, r8\n\t"
        "adc	r3, r3, #0\n\t"
        /* A[2] * B[2] */
        "ldr	r6, [%[a], #8]\n\t"
        "ldr	r8, [%[b], #8]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r4, r4, r6\n\t"
        "adcs 	r5, r5, r8\n\t"
        "adc	r3, r3, #0\n\t"
        /* A[3] * B[1] */
        "ldr	r6, [%[a], #12]\n\t"
        "ldr	r8, [%[b], #4]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r4, r4, r6\n\t"
        "adcs 	r5, r5, r8\n\t"
        "adc	r3, r3, #0\n\t"
        /* A[4] * B[0] */
        "ldr	r6, [%[a], #16]\n\t"
        "ldr	r8, [%[b], #0]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r4, r4, r6\n\t"
        "adcs 	r5, r5, r8\n\t"
        "adc	r3, r3, #0\n\t"
        "str	r4, [%[tmp], #16]\n\t"
        "mov	r4, #0\n\t"
        /* A[0] * B[5] */
        "ldr	r6, [%[a], #0]\n\t"
        "ldr	r8, [%[b], #20]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r5, r5, r6\n\t"
        "adcs 	r3, r3, r8\n\t"
        "adc	r4, r4, #0\n\t"
        /* A[1] * B[4] */
        "ldr	r6, [%[a], #4]\n\t"
        "ldr	r8, [%[b], #16]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r5, r5, r6\n\t"
        "adcs 	r3, r3, r8\n\t"
        "adc	r4, r4, #0\n\t"
        /* A[2] * B[3] */
        "ldr	r6, [%[a], #8]\n\t"
        "ldr	r8, [%[b], #12]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r5, r5, r6\n\t"
        "adcs 	r3, r3, r8\n\t"
        "adc	r4, r4, #0\n\t"
        /* A[3] * B[2] */
        "ldr	r6, [%[a], #12]\n\t"
        "ldr	r8, [%[b], #8]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r5, r5, r6\n\t"
        "adcs 	r3, r3, r8\n\t"
        "adc	r4, r4, #0\n\t"
        /* A[4] * B[1] */
        "ldr	r6, [%[a], #16]\n\t"
        "ldr	r8, [%[b], #4]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r5, r5, r6\n\t"
        "adcs 	r3, r3, r8\n\t"
        "adc	r4, r4, #0\n\t"
        /* A[5] * B[0] */
        "ldr	r6, [%[a], #20]\n\t"
        "ldr	r8, [%[b], #0]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r5, r5, r6\n\t"
        "adcs 	r3, r3, r8\n\t"
        "adc	r4, r4, #0\n\t"
        "str	r5, [%[tmp], #20]\n\t"
        "mov	r5, #0\n\t"
        /* A[0] * B[6] */
        "ldr	r6, [%[a], #0]\n\t"
        "ldr	r8, [%[b], #24]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r3, r3, r6\n\t"
        "adcs 	r4, r4, r8\n\t"
        "adc	r5, r5, #0\n\t"
        /* A[1] * B[5] */
        "ldr	r6, [%[a], #4]\n\t"
        "ldr	r8, [%[b], #20]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r3, r3, r6\n\t"
        "adcs 	r4, r4, r8\n\t"
        "adc	r5, r5, #0\n\t"
        /* A[2] * B[4] */
        "ldr	r6, [%[a], #8]\n\t"
        "ldr	r8, [%[b], #16]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r3, r3, r6\n\t"
        "adcs 	r4, r4, r8\n\t"
        "adc	r5, r5, #0\n\t"
        /* A[3] * B[3] */
        "ldr	r6, [%[a], #12]\n\t"
        "ldr	r8, [%[b], #12]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r3, r3, r6\n\t"
        "adcs 	r4, r4, r8\n\t"
        "adc	r5, r5, #0\n\t"
        /* A[4] * B[2] */
        "ldr	r6, [%[a], #16]\n\t"
        "ldr	r8, [%[b], #8]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r3, r3, r6\n\t"
        "adcs 	r4, r4, r8\n\t"
        "adc	r5, r5, #0\n\t"
        /* A[5] * B[1] */
        "ldr	r6, [%[a], #20]\n\t"
        "ldr	r8, [%[b], #4]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r3, r3, r6\n\t"
        "adcs 	r4, r4, r8\n\t"
        "adc	r5, r5, #0\n\t"
        /* A[6] * B[0] */
        "ldr	r6, [%[a], #24]\n\t"
        "ldr	r8, [%[b], #0]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r3, r3, r6\n\t"
        "adcs 	r4, r4, r8\n\t"
        "adc	r5, r5, #0\n\t"
        "str	r3, [%[tmp], #24]\n\t"
        "mov	r3, #0\n\t"
        /* A[0] * B[7] */
        "ldr	r6, [%[a], #0]\n\t"
        "ldr	r8, [%[b], #28]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r4, r4, r6\n\t"
        "adcs 	r5, r5, r8\n\t"
        "adc	r3, r3, #0\n\t"
        /* A[1] * B[6] */
        "ldr	r6, [%[a], #4]\n\t"
        "ldr	r8, [%[b], #24]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r4, r4, r6\n\t"
        "adcs 	r5, r5, r8\n\t"
        "adc	r3, r3, #0\n\t"
        /* A[2] * B[5] */
        "ldr	r6, [%[a], #8]\n\t"
        "ldr	r8, [%[b], #20]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r4, r4, r6\n\t"
        "adcs 	r5, r5, r8\n\t"
        "adc	r3, r3, #0\n\t"
        /* A[3] * B[4] */
        "ldr	r6, [%[a], #12]\n\t"
        "ldr	r8, [%[b], #16]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r4, r4, r6\n\t"
        "adcs 	r5, r5, r8\n\t"
        "adc	r3, r3, #0\n\t"
        /* A[4] * B[3] */
        "ldr	r6, [%[a], #16]\n\t"
        "ldr	r8, [%[b], #12]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r4, r4, r6\n\t"
        "adcs 	r5, r5, r8\n\t"
        "adc	r3, r3, #0\n\t"
        /* A[5] * B[2] */
        "ldr	r6, [%[a], #20]\n\t"
        "ldr	r8, [%[b], #8]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r4, r4, r6\n\t"
        "adcs 	r5, r5, r8\n\t"
        "adc	r3, r3, #0\n\t"
        /* A[6] * B[1] */
        "ldr	r6, [%[a], #24]\n\t"
        "ldr	r8, [%[b], #4]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r4, r4, r6\n\t"
        "adcs 	r5, r5, r8\n\t"
        "adc	r3, r3, #0\n\t"
        /* A[7] * B[0] */
        "ldr	r6, [%[a], #28]\n\t"
        "ldr	r8, [%[b], #0]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r4, r4, r6\n\t"
        "adcs 	r5, r5, r8\n\t"
        "adc	r3, r3, #0\n\t"
        "str	r4, [%[tmp], #28]\n\t"
        "mov	r4, #0\n\t"
        /* A[1] * B[7] */
        "ldr	r6, [%[a], #4]\n\t"
        "ldr	r8, [%[b], #28]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r5, r5, r6\n\t"
        "adcs 	r3, r3, r8\n\t"
        "adc	r4, r4, #0\n\t"
        /* A[2] * B[6] */
        "ldr	r6, [%[a], #8]\n\t"
        "ldr	r8, [%[b], #24]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r5, r5, r6\n\t"
        "adcs 	r3, r3, r8\n\t"
        "adc	r4, r4, #0\n\t"
        /* A[3] * B[5] */
        "ldr	r6, [%[a], #12]\n\t"
        "ldr	r8, [%[b], #20]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r5, r5, r6\n\t"
        "adcs 	r3, r3, r8\n\t"
        "adc	r4, r4, #0\n\t"
        /* A[4] * B[4] */
        "ldr	r6, [%[a], #16]\n\t"
        "ldr	r8, [%[b], #16]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r5, r5, r6\n\t"
        "adcs 	r3, r3, r8\n\t"
        "adc	r4, r4, #0\n\t"
        /* A[5] * B[3] */
        "ldr	r6, [%[a], #20]\n\t"
        "ldr	r8, [%[b], #12]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r5, r5, r6\n\t"
        "adcs 	r3, r3, r8\n\t"
        "adc	r4, r4, #0\n\t"
        /* A[6] * B[2] */
        "ldr	r6, [%[a], #24]\n\t"
        "ldr	r8, [%[b], #8]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r5, r5, r6\n\t"
        "adcs 	r3, r3, r8\n\t"
        "adc	r4, r4, #0\n\t"
        /* A[7] * B[1] */
        "ldr	r6, [%[a], #28]\n\t"
        "ldr	r8, [%[b], #4]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r5, r5, r6\n\t"
        "adcs 	r3, r3, r8\n\t"
        "adc	r4, r4, #0\n\t"
        "str	r5, [%[r], #32]\n\t"
        "mov	r5, #0\n\t"
        /* A[2] * B[7] */
        "ldr	r6, [%[a], #8]\n\t"
        "ldr	r8, [%[b], #28]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r3, r3, r6\n\t"
        "adcs 	r4, r4, r8\n\t"
        "adc	r5, r5, #0\n\t"
        /* A[3] * B[6] */
        "ldr	r6, [%[a], #12]\n\t"
        "ldr	r8, [%[b], #24]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r3, r3, r6\n\t"
        "adcs 	r4, r4, r8\n\t"
        "adc	r5, r5, #0\n\t"
        /* A[4] * B[5] */
        "ldr	r6, [%[a], #16]\n\t"
        "ldr	r8, [%[b], #20]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r3, r3, r6\n\t"
        "adcs 	r4, r4, r8\n\t"
        "adc	r5, r5, #0\n\t"
        /* A[5] * B[4] */
        "ldr	r6, [%[a], #20]\n\t"
        "ldr	r8, [%[b], #16]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r3, r3, r6\n\t"
        "adcs 	r4, r4, r8\n\t"
        "adc	r5, r5, #0\n\t"
        /* A[6] * B[3] */
        "ldr	r6, [%[a], #24]\n\t"
        "ldr	r8, [%[b], #12]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r3, r3, r6\n\t"
        "adcs 	r4, r4, r8\n\t"
        "adc	r5, r5, #0\n\t"
        /* A[7] * B[2] */
        "ldr	r6, [%[a], #28]\n\t"
        "ldr	r8, [%[b], #8]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r3, r3, r6\n\t"
        "adcs 	r4, r4, r8\n\t"
        "adc	r5, r5, #0\n\t"
        "str	r3, [%[r], #36]\n\t"
        "mov	r3, #0\n\t"
        /* A[3] * B[7] */
        "ldr	r6, [%[a], #12]\n\t"
        "ldr	r8, [%[b], #28]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r4, r4, r6\n\t"
        "adcs 	r5, r5, r8\n\t"
        "adc	r3, r3, #0\n\t"
        /* A[4] * B[6] */
        "ldr	r6, [%[a], #16]\n\t"
        "ldr	r8, [%[b], #24]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r4, r4, r6\n\t"
        "adcs 	r5, r5, r8\n\t"
        "adc	r3, r3, #0\n\t"
        /* A[5] * B[5] */
        "ldr	r6, [%[a], #20]\n\t"
        "ldr	r8, [%[b], #20]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r4, r4, r6\n\t"
        "adcs 	r5, r5, r8\n\t"
        "adc	r3, r3, #0\n\t"
        /* A[6] * B[4] */
        "ldr	r6, [%[a], #24]\n\t"
        "ldr	r8, [%[b], #16]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r4, r4, r6\n\t"
        "adcs 	r5, r5, r8\n\t"
        "adc	r3, r3, #0\n\t"
        /* A[7] * B[3] */
        "ldr	r6, [%[a], #28]\n\t"
        "ldr	r8, [%[b], #12]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r4, r4, r6\n\t"
        "adcs 	r5, r5, r8\n\t"
        "adc	r3, r3, #0\n\t"
        "str	r4, [%[r], #40]\n\t"
        "mov	r4, #0\n\t"
        /* A[4] * B[7] */
        "ldr	r6, [%[a], #16]\n\t"
        "ldr	r8, [%[b], #28]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r5, r5, r6\n\t"
        "adcs 	r3, r3, r8\n\t"
        "adc	r4, r4, #0\n\t"
        /* A[5] * B[6] */
        "ldr	r6, [%[a], #20]\n\t"
        "ldr	r8, [%[b], #24]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r5, r5, r6\n\t"
        "adcs 	r3, r3, r8\n\t"
        "adc	r4, r4, #0\n\t"
        /* A[6] * B[5] */
        "ldr	r6, [%[a], #24]\n\t"
        "ldr	r8, [%[b], #20]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r5, r5, r6\n\t"
        "adcs 	r3, r3, r8\n\t"
        "adc	r4, r4, #0\n\t"
        /* A[7] * B[4] */
        "ldr	r6, [%[a], #28]\n\t"
        "ldr	r8, [%[b], #16]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r5, r5, r6\n\t"
        "adcs 	r3, r3, r8\n\t"
        "adc	r4, r4, #0\n\t"
        "str	r5, [%[r], #44]\n\t"
        "mov	r5, #0\n\t"
        /* A[5] * B[7] */
        "ldr	r6, [%[a], #20]\n\t"
        "ldr	r8, [%[b], #28]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r3, r3, r6\n\t"
        "adcs 	r4, r4, r8\n\t"
        "adc	r5, r5, #0\n\t"
        /* A[6] * B[6] */
        "ldr	r6, [%[a], #24]\n\t"
        "ldr	r8, [%[b], #24]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r3, r3, r6\n\t"
        "adcs 	r4, r4, r8\n\t"
        "adc	r5, r5, #0\n\t"
        /* A[7] * B[5] */
        "ldr	r6, [%[a], #28]\n\t"
        "ldr	r8, [%[b], #20]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r3, r3, r6\n\t"
        "adcs 	r4, r4, r8\n\t"
        "adc	r5, r5, #0\n\t"
        "str	r3, [%[r], #48]\n\t"
        "mov	r3, #0\n\t"
        /* A[6] * B[7] */
        "ldr	r6, [%[a], #24]\n\t"
        "ldr	r8, [%[b], #28]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r4, r4, r6\n\t"
        "adcs 	r5, r5, r8\n\t"
        "adc	r3, r3, #0\n\t"
        /* A[7] * B[6] */
        "ldr	r6, [%[a], #28]\n\t"
        "ldr	r8, [%[b], #24]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r4, r4, r6\n\t"
        "adcs 	r5, r5, r8\n\t"
        "adc	r3, r3, #0\n\t"
        "str	r4, [%[r], #52]\n\t"
        "mov	r4, #0\n\t"
        /* A[7] * B[7] */
        "ldr	r6, [%[a], #28]\n\t"
        "ldr	r8, [%[b], #28]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r5, r5, r6\n\t"
        "adc	r3, r3, r8\n\t"
        "str	r5, [%[r], #56]\n\t"
        "str	r3, [%[r], #60]\n\t"
        /* Transfer tmp to r */
        "ldr	r3, [%[tmp], #0]\n\t"
        "ldr	r4, [%[tmp], #4]\n\t"
        "ldr	r5, [%[tmp], #8]\n\t"
        "ldr	r6, [%[tmp], #12]\n\t"
        "str	r3, [%[r], #0]\n\t"
        "str	r4, [%[r], #4]\n\t"
        "str	r5, [%[r], #8]\n\t"
        "str	r6, [%[r], #12]\n\t"
        "ldr	r3, [%[tmp], #16]\n\t"
        "ldr	r4, [%[tmp], #20]\n\t"
        "ldr	r5, [%[tmp], #24]\n\t"
        "ldr	r6, [%[tmp], #28]\n\t"
        "str	r3, [%[r], #16]\n\t"
        "str	r4, [%[r], #20]\n\t"
        "str	r5, [%[r], #24]\n\t"
        "str	r6, [%[r], #28]\n\t"
        :
        : [r] "r" (r), [a] "r" (a), [b] "r" (b), [tmp] "r" (tmp)
        : "memory", "r3", "r4", "r5", "r6", "r8"
    );
}

#endif
#if defined(HAVE_ECC_SIGN) || defined(HAVE_ECC_VERIFY)
#ifdef WOLFSSL_SP_SMALL
/* Sub b from a into a. (a -= b)
 *
 * a  A single precision integer.
 * b  A single precision integer.
 */
SP_NOINLINE static sp_digit sp_256_sub_in_place_8(sp_digit* a,
        const sp_digit* b)
{
    sp_digit c = 0;
    __asm__ __volatile__ (
        "mov	r8, %[a]\n\t"
        "add	r8, r8, #32\n\t"
        "\n1:\n\t"
        "mov	r5, #0\n\t"
        "subs	r5, r5, %[c]\n\t"
        "ldr	r3, [%[a]]\n\t"
        "ldr	r4, [%[a], #4]\n\t"
        "ldr	r5, [%[b]]\n\t"
        "ldr	r6, [%[b], #4]\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "str	r3, [%[a]]\n\t"
        "str	r4, [%[a], #4]\n\t"
        "sbc	%[c], %[c], %[c]\n\t"
        "add	%[a], %[a], #8\n\t"
        "add	%[b], %[b], #8\n\t"
        "cmp	%[a], r8\n\t"
        "bne	1b\n\t"
        : [c] "+r" (c), [a] "+r" (a), [b] "+r" (b)
        :
        : "memory", "r3", "r4", "r5", "r6", "r8"
    );

    return c;
}

#else
/* Sub b from a into r. (r = a - b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A single precision integer.
 */
SP_NOINLINE static sp_digit sp_256_sub_in_place_8(sp_digit* a,
        const sp_digit* b)
{
    sp_digit c = 0;

    __asm__ __volatile__ (
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "subs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "sbc	%[c], %[c], %[c]\n\t"
        : [c] "+r" (c), [a] "+r" (a), [b] "+r" (b)
        :
        : "memory", "r3", "r4", "r5", "r6"
    );

    return c;
}

#endif /* WOLFSSL_SP_SMALL */
/* Mul a by digit b into r. (r = a * b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A single precision digit.
 */
SP_NOINLINE static void sp_256_mul_d_8(sp_digit* r, const sp_digit* a,
        sp_digit b)
{
    __asm__ __volatile__ (
        "add	r9, %[a], #32\n\t"
        /* A[0] * B */
        "ldr	r6, [%[a]], #4\n\t"
        "umull	r5, r3, r6, %[b]\n\t"
        "mov	r4, #0\n\t"
        "str	r5, [%[r]], #4\n\t"
        /* A[0] * B - Done */
        "\n1:\n\t"
        "mov	r5, #0\n\t"
        /* A[] * B */
        "ldr	r6, [%[a]], #4\n\t"
        "umull	r6, r8, r6, %[b]\n\t"
        "adds	r3, r3, r6\n\t"
        "adcs 	r4, r4, r8\n\t"
        "adc	r5, r5, #0\n\t"
        /* A[] * B - Done */
        "str	r3, [%[r]], #4\n\t"
        "mov	r3, r4\n\t"
        "mov	r4, r5\n\t"
        "cmp	%[a], r9\n\t"
        "blt	1b\n\t"
        "str	r3, [%[r]]\n\t"
        : [r] "+r" (r), [a] "+r" (a)
        : [b] "r" (b)
        : "memory", "r3", "r4", "r5", "r6", "r8", "r9"
    );
}

/* Divide the double width number (d1|d0) by the dividend. (d1|d0 / div)
 *
 * d1   The high order half of the number to divide.
 * d0   The low order half of the number to divide.
 * div  The dividend.
 * returns the result of the division.
 *
 * Note that this is an approximate div. It may give an answer 1 larger.
 */
SP_NOINLINE static sp_digit div_256_word_8(sp_digit d1, sp_digit d0,
        sp_digit div)
{
    sp_digit r = 0;

    __asm__ __volatile__ (
        "lsr	r6, %[div], #16\n\t"
        "add	r6, r6, #1\n\t"
        "udiv	r4, %[d1], r6\n\t"
        "lsl	r8, r4, #16\n\t"
        "umull	r4, r5, %[div], r8\n\t"
        "subs	%[d0], %[d0], r4\n\t"
        "sbc	%[d1], %[d1], r5\n\t"
        "udiv	r5, %[d1], r6\n\t"
        "lsl	r4, r5, #16\n\t"
        "add	r8, r8, r4\n\t"
        "umull	r4, r5, %[div], r4\n\t"
        "subs	%[d0], %[d0], r4\n\t"
        "sbc	%[d1], %[d1], r5\n\t"
        "lsl	r4, %[d1], #16\n\t"
        "orr	r4, r4, %[d0], lsr #16\n\t"
        "udiv	r4, r4, r6\n\t"
        "add	r8, r8, r4\n\t"
        "umull	r4, r5, %[div], r4\n\t"
        "subs	%[d0], %[d0], r4\n\t"
        "sbc	%[d1], %[d1], r5\n\t"
        "lsl	r4, %[d1], #16\n\t"
        "orr	r4, r4, %[d0], lsr #16\n\t"
        "udiv	r4, r4, r6\n\t"
        "add	r8, r8, r4\n\t"
        "umull	r4, r5, %[div], r4\n\t"
        "subs	%[d0], %[d0], r4\n\t"
        "sbc	%[d1], %[d1], r5\n\t"
        "udiv	r4, %[d0], %[div]\n\t"
        "add	r8, r8, r4\n\t"
        "mov	%[r], r8\n\t"
        : [r] "+r" (r)
        : [d1] "r" (d1), [d0] "r" (d0), [div] "r" (div)
        : "r4", "r5", "r6", "r8"
    );
    return r;
}

/* AND m into each word of a and store in r.
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * m  Mask to AND against each digit.
 */
static void sp_256_mask_8(sp_digit* r, const sp_digit* a, sp_digit m)
{
#ifdef WOLFSSL_SP_SMALL
    int i;

    for (i=0; i<8; i++) {
        r[i] = a[i] & m;
    }
#else
    r[0] = a[0] & m;
    r[1] = a[1] & m;
    r[2] = a[2] & m;
    r[3] = a[3] & m;
    r[4] = a[4] & m;
    r[5] = a[5] & m;
    r[6] = a[6] & m;
    r[7] = a[7] & m;
#endif
}

/* Divide d in a and put remainder into r (m*d + r = a)
 * m is not calculated as it is not needed at this time.
 *
 * a  Nmber to be divided.
 * d  Number to divide with.
 * m  Multiplier result.
 * r  Remainder from the division.
 * returns MP_OKAY indicating success.
 */
static WC_INLINE int sp_256_div_8(const sp_digit* a, const sp_digit* d, sp_digit* m,
        sp_digit* r)
{
    sp_digit t1[16], t2[9];
    sp_digit div, r1;
    int i;

    (void)m;

    div = d[7];
    XMEMCPY(t1, a, sizeof(*t1) * 2 * 8);
    for (i=7; i>=0; i--) {
        r1 = div_256_word_8(t1[8 + i], t1[8 + i - 1], div);

        sp_256_mul_d_8(t2, d, r1);
        t1[8 + i] += sp_256_sub_in_place_8(&t1[i], t2);
        t1[8 + i] -= t2[8];
        sp_256_mask_8(t2, d, t1[8 + i]);
        t1[8 + i] += sp_256_add_8(&t1[i], &t1[i], t2);
        sp_256_mask_8(t2, d, t1[8 + i]);
        t1[8 + i] += sp_256_add_8(&t1[i], &t1[i], t2);
    }

    r1 = sp_256_cmp_8(t1, d) >= 0;
    sp_256_cond_sub_8(r, t1, d, (sp_digit)0 - r1);

    return MP_OKAY;
}

/* Reduce a modulo m into r. (r = a mod m)
 *
 * r  A single precision number that is the reduced result.
 * a  A single precision number that is to be reduced.
 * m  A single precision number that is the modulus to reduce with.
 * returns MP_OKAY indicating success.
 */
static WC_INLINE int sp_256_mod_8(sp_digit* r, const sp_digit* a, const sp_digit* m)
{
    return sp_256_div_8(a, m, NULL, r);
}

#endif
#if defined(HAVE_ECC_SIGN) || defined(HAVE_ECC_VERIFY)
/* Square a and put result in r. (r = a * a)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 */
SP_NOINLINE static void sp_256_sqr_8(sp_digit* r, const sp_digit* a)
{
    sp_digit tmp[8];
    __asm__ __volatile__ (
        /* A[0] * A[0] */
        "ldr	r6, [%[a], #0]\n\t"
        "umull	r3, r4, r6, r6\n\t"
        "mov	r5, #0\n\t"
        "str	r3, [%[tmp], #0]\n\t"
        "mov	r3, #0\n\t"
        /* A[0] * A[1] */
        "ldr	r8, [%[a], #4]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r4, r4, r6\n\t"
        "adc	r5, r5, r8\n\t"
        "adds	r4, r4, r6\n\t"
        "adcs 	r5, r5, r8\n\t"
        "adc	r3, r3, #0\n\t"
        "str	r4, [%[tmp], #4]\n\t"
        "mov	r4, #0\n\t"
        /* A[0] * A[2] */
        "ldr	r6, [%[a], #0]\n\t"
        "ldr	r8, [%[a], #8]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r5, r5, r6\n\t"
        "adc	r3, r3, r8\n\t"
        "adds	r5, r5, r6\n\t"
        "adcs 	r3, r3, r8\n\t"
        "adc	r4, r4, #0\n\t"
        /* A[1] * A[1] */
        "ldr	r6, [%[a], #4]\n\t"
        "umull	r6, r8, r6, r6\n\t"
        "adds	r5, r5, r6\n\t"
        "adcs	r3, r3, r8\n\t"
        "adc	r4, r4, #0\n\t"
        "str	r5, [%[tmp], #8]\n\t"
        "mov	r5, #0\n\t"
        /* A[0] * A[3] */
        "ldr	r6, [%[a], #0]\n\t"
        "ldr	r8, [%[a], #12]\n\t"
        "umull	r9, r10, r6, r8\n\t"
        "mov	r11, #0\n\t"
        /* A[1] * A[2] */
        "ldr	r6, [%[a], #4]\n\t"
        "ldr	r8, [%[a], #8]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r9, r9, r6\n\t"
        "adcs 	r10, r10, r8\n\t"
        "adc	r11, r11, #0\n\t"
        "adds	r9, r9, r9\n\t"
        "adcs	r10, r10, r10\n\t"
        "adc	r11, r11, r11\n\t"
        "adds	r3, r3, r9\n\t"
        "adcs	r4, r4, r10\n\t"
        "adc	r5, r5, r11\n\t"
        "str	r3, [%[tmp], #12]\n\t"
        "mov	r3, #0\n\t"
        /* A[0] * A[4] */
        "ldr	r6, [%[a], #0]\n\t"
        "ldr	r8, [%[a], #16]\n\t"
        "umull	r9, r10, r6, r8\n\t"
        "mov	r11, #0\n\t"
        /* A[1] * A[3] */
        "ldr	r6, [%[a], #4]\n\t"
        "ldr	r8, [%[a], #12]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r9, r9, r6\n\t"
        "adcs 	r10, r10, r8\n\t"
        "adc	r11, r11, #0\n\t"
        /* A[2] * A[2] */
        "ldr	r6, [%[a], #8]\n\t"
        "umull	r6, r8, r6, r6\n\t"
        "adds	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "adc	r3, r3, #0\n\t"
        "adds	r9, r9, r9\n\t"
        "adcs	r10, r10, r10\n\t"
        "adc	r11, r11, r11\n\t"
        "adds	r4, r4, r9\n\t"
        "adcs	r5, r5, r10\n\t"
        "adc	r3, r3, r11\n\t"
        "str	r4, [%[tmp], #16]\n\t"
        "mov	r4, #0\n\t"
        /* A[0] * A[5] */
        "ldr	r6, [%[a], #0]\n\t"
        "ldr	r8, [%[a], #20]\n\t"
        "umull	r9, r10, r6, r8\n\t"
        "mov	r11, #0\n\t"
        /* A[1] * A[4] */
        "ldr	r6, [%[a], #4]\n\t"
        "ldr	r8, [%[a], #16]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r9, r9, r6\n\t"
        "adcs 	r10, r10, r8\n\t"
        "adc	r11, r11, #0\n\t"
        /* A[2] * A[3] */
        "ldr	r6, [%[a], #8]\n\t"
        "ldr	r8, [%[a], #12]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r9, r9, r6\n\t"
        "adcs 	r10, r10, r8\n\t"
        "adc	r11, r11, #0\n\t"
        "adds	r9, r9, r9\n\t"
        "adcs	r10, r10, r10\n\t"
        "adc	r11, r11, r11\n\t"
        "adds	r5, r5, r9\n\t"
        "adcs	r3, r3, r10\n\t"
        "adc	r4, r4, r11\n\t"
        "str	r5, [%[tmp], #20]\n\t"
        "mov	r5, #0\n\t"
        /* A[0] * A[6] */
        "ldr	r6, [%[a], #0]\n\t"
        "ldr	r8, [%[a], #24]\n\t"
        "umull	r9, r10, r6, r8\n\t"
        "mov	r11, #0\n\t"
        /* A[1] * A[5] */
        "ldr	r6, [%[a], #4]\n\t"
        "ldr	r8, [%[a], #20]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r9, r9, r6\n\t"
        "adcs 	r10, r10, r8\n\t"
        "adc	r11, r11, #0\n\t"
        /* A[2] * A[4] */
        "ldr	r6, [%[a], #8]\n\t"
        "ldr	r8, [%[a], #16]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r9, r9, r6\n\t"
        "adcs 	r10, r10, r8\n\t"
        "adc	r11, r11, #0\n\t"
        /* A[3] * A[3] */
        "ldr	r6, [%[a], #12]\n\t"
        "umull	r6, r8, r6, r6\n\t"
        "adds	r3, r3, r6\n\t"
        "adcs	r4, r4, r8\n\t"
        "adc	r5, r5, #0\n\t"
        "adds	r9, r9, r9\n\t"
        "adcs	r10, r10, r10\n\t"
        "adc	r11, r11, r11\n\t"
        "adds	r3, r3, r9\n\t"
        "adcs	r4, r4, r10\n\t"
        "adc	r5, r5, r11\n\t"
        "str	r3, [%[tmp], #24]\n\t"
        "mov	r3, #0\n\t"
        /* A[0] * A[7] */
        "ldr	r6, [%[a], #0]\n\t"
        "ldr	r8, [%[a], #28]\n\t"
        "umull	r9, r10, r6, r8\n\t"
        "mov	r11, #0\n\t"
        /* A[1] * A[6] */
        "ldr	r6, [%[a], #4]\n\t"
        "ldr	r8, [%[a], #24]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r9, r9, r6\n\t"
        "adcs 	r10, r10, r8\n\t"
        "adc	r11, r11, #0\n\t"
        /* A[2] * A[5] */
        "ldr	r6, [%[a], #8]\n\t"
        "ldr	r8, [%[a], #20]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r9, r9, r6\n\t"
        "adcs 	r10, r10, r8\n\t"
        "adc	r11, r11, #0\n\t"
        /* A[3] * A[4] */
        "ldr	r6, [%[a], #12]\n\t"
        "ldr	r8, [%[a], #16]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r9, r9, r6\n\t"
        "adcs 	r10, r10, r8\n\t"
        "adc	r11, r11, #0\n\t"
        "adds	r9, r9, r9\n\t"
        "adcs	r10, r10, r10\n\t"
        "adc	r11, r11, r11\n\t"
        "adds	r4, r4, r9\n\t"
        "adcs	r5, r5, r10\n\t"
        "adc	r3, r3, r11\n\t"
        "str	r4, [%[tmp], #28]\n\t"
        "mov	r4, #0\n\t"
        /* A[1] * A[7] */
        "ldr	r6, [%[a], #4]\n\t"
        "ldr	r8, [%[a], #28]\n\t"
        "umull	r9, r10, r6, r8\n\t"
        "mov	r11, #0\n\t"
        /* A[2] * A[6] */
        "ldr	r6, [%[a], #8]\n\t"
        "ldr	r8, [%[a], #24]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r9, r9, r6\n\t"
        "adcs 	r10, r10, r8\n\t"
        "adc	r11, r11, #0\n\t"
        /* A[3] * A[5] */
        "ldr	r6, [%[a], #12]\n\t"
        "ldr	r8, [%[a], #20]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r9, r9, r6\n\t"
        "adcs 	r10, r10, r8\n\t"
        "adc	r11, r11, #0\n\t"
        /* A[4] * A[4] */
        "ldr	r6, [%[a], #16]\n\t"
        "umull	r6, r8, r6, r6\n\t"
        "adds	r5, r5, r6\n\t"
        "adcs	r3, r3, r8\n\t"
        "adc	r4, r4, #0\n\t"
        "adds	r9, r9, r9\n\t"
        "adcs	r10, r10, r10\n\t"
        "adc	r11, r11, r11\n\t"
        "adds	r5, r5, r9\n\t"
        "adcs	r3, r3, r10\n\t"
        "adc	r4, r4, r11\n\t"
        "str	r5, [%[r], #32]\n\t"
        "mov	r5, #0\n\t"
        /* A[2] * A[7] */
        "ldr	r6, [%[a], #8]\n\t"
        "ldr	r8, [%[a], #28]\n\t"
        "umull	r9, r10, r6, r8\n\t"
        "mov	r11, #0\n\t"
        /* A[3] * A[6] */
        "ldr	r6, [%[a], #12]\n\t"
        "ldr	r8, [%[a], #24]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r9, r9, r6\n\t"
        "adcs 	r10, r10, r8\n\t"
        "adc	r11, r11, #0\n\t"
        /* A[4] * A[5] */
        "ldr	r6, [%[a], #16]\n\t"
        "ldr	r8, [%[a], #20]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r9, r9, r6\n\t"
        "adcs 	r10, r10, r8\n\t"
        "adc	r11, r11, #0\n\t"
        "adds	r9, r9, r9\n\t"
        "adcs	r10, r10, r10\n\t"
        "adc	r11, r11, r11\n\t"
        "adds	r3, r3, r9\n\t"
        "adcs	r4, r4, r10\n\t"
        "adc	r5, r5, r11\n\t"
        "str	r3, [%[r], #36]\n\t"
        "mov	r3, #0\n\t"
        /* A[3] * A[7] */
        "ldr	r6, [%[a], #12]\n\t"
        "ldr	r8, [%[a], #28]\n\t"
        "umull	r9, r10, r6, r8\n\t"
        "mov	r11, #0\n\t"
        /* A[4] * A[6] */
        "ldr	r6, [%[a], #16]\n\t"
        "ldr	r8, [%[a], #24]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r9, r9, r6\n\t"
        "adcs 	r10, r10, r8\n\t"
        "adc	r11, r11, #0\n\t"
        /* A[5] * A[5] */
        "ldr	r6, [%[a], #20]\n\t"
        "umull	r6, r8, r6, r6\n\t"
        "adds	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "adc	r3, r3, #0\n\t"
        "adds	r9, r9, r9\n\t"
        "adcs	r10, r10, r10\n\t"
        "adc	r11, r11, r11\n\t"
        "adds	r4, r4, r9\n\t"
        "adcs	r5, r5, r10\n\t"
        "adc	r3, r3, r11\n\t"
        "str	r4, [%[r], #40]\n\t"
        "mov	r4, #0\n\t"
        /* A[4] * A[7] */
        "ldr	r6, [%[a], #16]\n\t"
        "ldr	r8, [%[a], #28]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r5, r5, r6\n\t"
        "adcs 	r3, r3, r8\n\t"
        "adc	r4, r4, #0\n\t"
        "adds	r5, r5, r6\n\t"
        "adcs 	r3, r3, r8\n\t"
        "adc	r4, r4, #0\n\t"
        /* A[5] * A[6] */
        "ldr	r6, [%[a], #20]\n\t"
        "ldr	r8, [%[a], #24]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r5, r5, r6\n\t"
        "adcs 	r3, r3, r8\n\t"
        "adc	r4, r4, #0\n\t"
        "adds	r5, r5, r6\n\t"
        "adcs 	r3, r3, r8\n\t"
        "adc	r4, r4, #0\n\t"
        "str	r5, [%[r], #44]\n\t"
        "mov	r5, #0\n\t"
        /* A[5] * A[7] */
        "ldr	r6, [%[a], #20]\n\t"
        "ldr	r8, [%[a], #28]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r3, r3, r6\n\t"
        "adcs 	r4, r4, r8\n\t"
        "adc	r5, r5, #0\n\t"
        "adds	r3, r3, r6\n\t"
        "adcs 	r4, r4, r8\n\t"
        "adc	r5, r5, #0\n\t"
        /* A[6] * A[6] */
        "ldr	r6, [%[a], #24]\n\t"
        "umull	r6, r8, r6, r6\n\t"
        "adds	r3, r3, r6\n\t"
        "adcs	r4, r4, r8\n\t"
        "adc	r5, r5, #0\n\t"
        "str	r3, [%[r], #48]\n\t"
        "mov	r3, #0\n\t"
        /* A[6] * A[7] */
        "ldr	r6, [%[a], #24]\n\t"
        "ldr	r8, [%[a], #28]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r4, r4, r6\n\t"
        "adcs 	r5, r5, r8\n\t"
        "adc	r3, r3, #0\n\t"
        "adds	r4, r4, r6\n\t"
        "adcs 	r5, r5, r8\n\t"
        "adc	r3, r3, #0\n\t"
        "str	r4, [%[r], #52]\n\t"
        "mov	r4, #0\n\t"
        /* A[7] * A[7] */
        "ldr	r6, [%[a], #28]\n\t"
        "umull	r6, r8, r6, r6\n\t"
        "adds	r5, r5, r6\n\t"
        "adc	r3, r3, r8\n\t"
        "str	r5, [%[r], #56]\n\t"
        "str	r3, [%[r], #60]\n\t"
        /* Transfer tmp to r */
        "ldr	r3, [%[tmp], #0]\n\t"
        "ldr	r4, [%[tmp], #4]\n\t"
        "ldr	r5, [%[tmp], #8]\n\t"
        "ldr	r6, [%[tmp], #12]\n\t"
        "str	r3, [%[r], #0]\n\t"
        "str	r4, [%[r], #4]\n\t"
        "str	r5, [%[r], #8]\n\t"
        "str	r6, [%[r], #12]\n\t"
        "ldr	r3, [%[tmp], #16]\n\t"
        "ldr	r4, [%[tmp], #20]\n\t"
        "ldr	r5, [%[tmp], #24]\n\t"
        "ldr	r6, [%[tmp], #28]\n\t"
        "str	r3, [%[r], #16]\n\t"
        "str	r4, [%[r], #20]\n\t"
        "str	r5, [%[r], #24]\n\t"
        "str	r6, [%[r], #28]\n\t"
        :
        : [r] "r" (r), [a] "r" (a), [tmp] "r" (tmp)
        : "memory", "r3", "r4", "r5", "r6", "r8", "r9", "r10", "r11"
    );
}

#ifdef WOLFSSL_SP_SMALL
/* Order-2 for the P256 curve. */
static const uint32_t p256_order_minus_2[8] = {
    0xfc63254fU,0xf3b9cac2U,0xa7179e84U,0xbce6faadU,0xffffffffU,0xffffffffU,
    0x00000000U,0xffffffffU
};
#else
/* The low half of the order-2 of the P256 curve. */
static const uint32_t p256_order_low[4] = {
    0xfc63254fU,0xf3b9cac2U,0xa7179e84U,0xbce6faadU
};
#endif /* WOLFSSL_SP_SMALL */

/* Multiply two number mod the order of P256 curve. (r = a * b mod order)
 *
 * r  Result of the multiplication.
 * a  First operand of the multiplication.
 * b  Second operand of the multiplication.
 */
static void sp_256_mont_mul_order_8(sp_digit* r, const sp_digit* a, const sp_digit* b)
{
    sp_256_mul_8(r, a, b);
    sp_256_mont_reduce_order_8(r, p256_order, p256_mp_order);
}

/* Square number mod the order of P256 curve. (r = a * a mod order)
 *
 * r  Result of the squaring.
 * a  Number to square.
 */
static void sp_256_mont_sqr_order_8(sp_digit* r, const sp_digit* a)
{
    sp_256_sqr_8(r, a);
    sp_256_mont_reduce_order_8(r, p256_order, p256_mp_order);
}

#ifndef WOLFSSL_SP_SMALL
/* Square number mod the order of P256 curve a number of times.
 * (r = a ^ n mod order)
 *
 * r  Result of the squaring.
 * a  Number to square.
 */
static void sp_256_mont_sqr_n_order_8(sp_digit* r, const sp_digit* a, int n)
{
    int i;

    sp_256_mont_sqr_order_8(r, a);
    for (i=1; i<n; i++) {
        sp_256_mont_sqr_order_8(r, r);
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
typedef struct sp_256_mont_inv_order_8_ctx {
    int state;
    int i;
} sp_256_mont_inv_order_8_ctx;
static int sp_256_mont_inv_order_8_nb(sp_ecc_ctx_t* sp_ctx, sp_digit* r, const sp_digit* a,
        sp_digit* t)
{
    int err = FP_WOULDBLOCK;
    sp_256_mont_inv_order_8_ctx* ctx = (sp_256_mont_inv_order_8_ctx*)sp_ctx;
    
    typedef char ctx_size_test[sizeof(sp_256_mont_inv_order_8_ctx) >= sizeof(*sp_ctx) ? -1 : 1];
    (void)sizeof(ctx_size_test);

    switch (ctx->state) {
    case 0:
        XMEMCPY(t, a, sizeof(sp_digit) * 8);
        ctx->i = 254;
        ctx->state = 1;
        break;
    case 1:
        sp_256_mont_sqr_order_8(t, t);
        ctx->state = 2;
        break;
    case 2:
        if ((p256_order_minus_2[ctx->i / 32] & ((sp_int_digit)1 << (ctx->i % 32))) != 0) {
            sp_256_mont_mul_order_8(t, t, a);
        }
        ctx->i--;
        ctx->state = (ctx->i == 0) ? 3 : 1;
        break;
    case 3:
        XMEMCPY(r, t, sizeof(sp_digit) * 8U);
        err = MP_OKAY;
        break;
    }
    return err;
}
#endif /* WOLFSSL_SP_NONBLOCK */

static void sp_256_mont_inv_order_8(sp_digit* r, const sp_digit* a,
        sp_digit* td)
{
#ifdef WOLFSSL_SP_SMALL
    sp_digit* t = td;
    int i;

    XMEMCPY(t, a, sizeof(sp_digit) * 8);
    for (i=254; i>=0; i--) {
        sp_256_mont_sqr_order_8(t, t);
        if ((p256_order_minus_2[i / 32] & ((sp_int_digit)1 << (i % 32))) != 0) {
            sp_256_mont_mul_order_8(t, t, a);
        }
    }
    XMEMCPY(r, t, sizeof(sp_digit) * 8U);
#else
    sp_digit* t = td;
    sp_digit* t2 = td + 2 * 8;
    sp_digit* t3 = td + 4 * 8;
    int i;

    /* t = a^2 */
    sp_256_mont_sqr_order_8(t, a);
    /* t = a^3 = t * a */
    sp_256_mont_mul_order_8(t, t, a);
    /* t2= a^c = t ^ 2 ^ 2 */
    sp_256_mont_sqr_n_order_8(t2, t, 2);
    /* t3= a^f = t2 * t */
    sp_256_mont_mul_order_8(t3, t2, t);
    /* t2= a^f0 = t3 ^ 2 ^ 4 */
    sp_256_mont_sqr_n_order_8(t2, t3, 4);
    /* t = a^ff = t2 * t3 */
    sp_256_mont_mul_order_8(t, t2, t3);
    /* t3= a^ff00 = t ^ 2 ^ 8 */
    sp_256_mont_sqr_n_order_8(t2, t, 8);
    /* t = a^ffff = t2 * t */
    sp_256_mont_mul_order_8(t, t2, t);
    /* t2= a^ffff0000 = t ^ 2 ^ 16 */
    sp_256_mont_sqr_n_order_8(t2, t, 16);
    /* t = a^ffffffff = t2 * t */
    sp_256_mont_mul_order_8(t, t2, t);
    /* t2= a^ffffffff0000000000000000 = t ^ 2 ^ 64  */
    sp_256_mont_sqr_n_order_8(t2, t, 64);
    /* t2= a^ffffffff00000000ffffffff = t2 * t */
    sp_256_mont_mul_order_8(t2, t2, t);
    /* t2= a^ffffffff00000000ffffffff00000000 = t2 ^ 2 ^ 32  */
    sp_256_mont_sqr_n_order_8(t2, t2, 32);
    /* t2= a^ffffffff00000000ffffffffffffffff = t2 * t */
    sp_256_mont_mul_order_8(t2, t2, t);
    /* t2= a^ffffffff00000000ffffffffffffffffbce6 */
    for (i=127; i>=112; i--) {
        sp_256_mont_sqr_order_8(t2, t2);
        if (((sp_digit)p256_order_low[i / 32] & ((sp_int_digit)1 << (i % 32))) != 0) {
            sp_256_mont_mul_order_8(t2, t2, a);
        }
    }
    /* t2= a^ffffffff00000000ffffffffffffffffbce6f */
    sp_256_mont_sqr_n_order_8(t2, t2, 4);
    sp_256_mont_mul_order_8(t2, t2, t3);
    /* t2= a^ffffffff00000000ffffffffffffffffbce6faada7179e84 */
    for (i=107; i>=64; i--) {
        sp_256_mont_sqr_order_8(t2, t2);
        if (((sp_digit)p256_order_low[i / 32] & ((sp_int_digit)1 << (i % 32))) != 0) {
            sp_256_mont_mul_order_8(t2, t2, a);
        }
    }
    /* t2= a^ffffffff00000000ffffffffffffffffbce6faada7179e84f */
    sp_256_mont_sqr_n_order_8(t2, t2, 4);
    sp_256_mont_mul_order_8(t2, t2, t3);
    /* t2= a^ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2 */
    for (i=59; i>=32; i--) {
        sp_256_mont_sqr_order_8(t2, t2);
        if (((sp_digit)p256_order_low[i / 32] & ((sp_int_digit)1 << (i % 32))) != 0) {
            sp_256_mont_mul_order_8(t2, t2, a);
        }
    }
    /* t2= a^ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2f */
    sp_256_mont_sqr_n_order_8(t2, t2, 4);
    sp_256_mont_mul_order_8(t2, t2, t3);
    /* t2= a^ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc63254 */
    for (i=27; i>=0; i--) {
        sp_256_mont_sqr_order_8(t2, t2);
        if (((sp_digit)p256_order_low[i / 32] & ((sp_int_digit)1 << (i % 32))) != 0) {
            sp_256_mont_mul_order_8(t2, t2, a);
        }
    }
    /* t2= a^ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632540 */
    sp_256_mont_sqr_n_order_8(t2, t2, 4);
    /* r = a^ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc63254f */
    sp_256_mont_mul_order_8(r, t2, t3);
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
        sp_256_ecc_mulmod_8_ctx mulmod_ctx;
        sp_256_mont_inv_order_8_ctx mont_inv_order_ctx;
    };
    sp_digit e[2*8];
    sp_digit x[2*8];
    sp_digit k[2*8];
    sp_digit r[2*8];
    sp_digit tmp[3 * 2*8];
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

        sp_256_from_bin(ctx->e, 8, hash, (int)hashLen);

        ctx->i = SP_ECC_MAX_SIG_GEN;
        ctx->state = 1;
        break;
    case 1: /* GEN */
        sp_256_from_mp(ctx->x, 8, priv);
        /* New random point. */
        if (km == NULL || mp_iszero(km)) {
            err = sp_256_ecc_gen_k_8(rng, ctx->k);
        }
        else {
            sp_256_from_mp(ctx->k, 8, km);
            mp_zero(km);
        }
        XMEMSET(&ctx->mulmod_ctx, 0, sizeof(ctx->mulmod_ctx));
        ctx->state = 2;
        break; 
    case 2: /* MULMOD */
        err = sp_256_ecc_mulmod_8_nb((sp_ecc_ctx_t*)&ctx->mulmod_ctx, 
            &ctx->point, &p256_base, ctx->k, 1, 1, heap);
        if (err == MP_OKAY) {
            ctx->state = 3;
        }
        break;
    case 3: /* MODORDER */
    {
        int32_t c;
        /* r = point->x mod order */
        XMEMCPY(ctx->r, ctx->point.x, sizeof(sp_digit) * 8U);
        sp_256_norm_8(ctx->r);
        c = sp_256_cmp_8(ctx->r, p256_order);
        sp_256_cond_sub_8(ctx->r, ctx->r, p256_order, 0L - (sp_digit)(c >= 0));
        sp_256_norm_8(ctx->r);
        ctx->state = 4;
        break;
    }
    case 4: /* KMODORDER */
        /* Conv k to Montgomery form (mod order) */
        sp_256_mul_8(ctx->k, ctx->k, p256_norm_order);
        err = sp_256_mod_8(ctx->k, ctx->k, p256_order);
        if (err == MP_OKAY) {
            sp_256_norm_8(ctx->k);
            XMEMSET(&ctx->mont_inv_order_ctx, 0, sizeof(ctx->mont_inv_order_ctx));
            ctx->state = 5;
        }
        break;
    case 5: /* KINV */
        /* kInv = 1/k mod order */
        err = sp_256_mont_inv_order_8_nb((sp_ecc_ctx_t*)&ctx->mont_inv_order_ctx, ctx->kInv, ctx->k, ctx->tmp);
        if (err == MP_OKAY) {
            XMEMSET(&ctx->mont_inv_order_ctx, 0, sizeof(ctx->mont_inv_order_ctx));
            ctx->state = 6;
        }
        break;
    case 6: /* KINVNORM */
        sp_256_norm_8(ctx->kInv);
        ctx->state = 7;
        break;
    case 7: /* R */
        /* s = r * x + e */
        sp_256_mul_8(ctx->x, ctx->x, ctx->r);
        ctx->state = 8;
        break;
    case 8: /* S1 */
        err = sp_256_mod_8(ctx->x, ctx->x, p256_order);
        if (err == MP_OKAY)
            ctx->state = 9;
        break;
    case 9: /* S2 */
    {
        sp_digit carry;
        int32_t c;
        sp_256_norm_8(ctx->x);
        carry = sp_256_add_8(ctx->s, ctx->e, ctx->x);
        sp_256_cond_sub_8(ctx->s, ctx->s, p256_order, 0 - carry);
        sp_256_norm_8(ctx->s);
        c = sp_256_cmp_8(ctx->s, p256_order);
        sp_256_cond_sub_8(ctx->s, ctx->s, p256_order, 0L - (sp_digit)(c >= 0));
        sp_256_norm_8(ctx->s);

        /* s = s * k^-1 mod order */
        sp_256_mont_mul_order_8(ctx->s, ctx->s, ctx->kInv);
        sp_256_norm_8(ctx->s);

        /* Check that signature is usable. */
        if (sp_256_iszero_8(ctx->s) == 0) {
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
        XMEMSET(ctx->e, 0, sizeof(sp_digit) * 2U * 8U);
        XMEMSET(ctx->x, 0, sizeof(sp_digit) * 2U * 8U);
        XMEMSET(ctx->k, 0, sizeof(sp_digit) * 2U * 8U);
        XMEMSET(ctx->r, 0, sizeof(sp_digit) * 2U * 8U);
        XMEMSET(ctx->tmp, 0, sizeof(sp_digit) * 3U * 2U * 8U);
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
    sp_digit ed[2*8];
    sp_digit xd[2*8];
    sp_digit kd[2*8];
    sp_digit rd[2*8];
    sp_digit td[3 * 2*8];
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
    int32_t c;
    int i;

    (void)heap;

    err = sp_256_point_new_8(heap, p, point);
#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (err == MP_OKAY) {
        d = (sp_digit*)XMALLOC(sizeof(sp_digit) * 7 * 2 * 8, heap,
                                                              DYNAMIC_TYPE_ECC);
        if (d == NULL) {
            err = MEMORY_E;
        }
    }
#endif

    if (err == MP_OKAY) {
#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
        e = d + 0 * 8;
        x = d + 2 * 8;
        k = d + 4 * 8;
        r = d + 6 * 8;
        tmp = d + 8 * 8;
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

        sp_256_from_bin(e, 8, hash, (int)hashLen);
    }

    for (i = SP_ECC_MAX_SIG_GEN; err == MP_OKAY && i > 0; i--) {
        sp_256_from_mp(x, 8, priv);

        /* New random point. */
        if (km == NULL || mp_iszero(km)) {
            err = sp_256_ecc_gen_k_8(rng, k);
        }
        else {
            sp_256_from_mp(k, 8, km);
            mp_zero(km);
        }
        if (err == MP_OKAY) {
                err = sp_256_ecc_mulmod_base_8(point, k, 1, 1, NULL);
        }

        if (err == MP_OKAY) {
            /* r = point->x mod order */
            XMEMCPY(r, point->x, sizeof(sp_digit) * 8U);
            sp_256_norm_8(r);
            c = sp_256_cmp_8(r, p256_order);
            sp_256_cond_sub_8(r, r, p256_order, 0L - (sp_digit)(c >= 0));
            sp_256_norm_8(r);

            /* Conv k to Montgomery form (mod order) */
                sp_256_mul_8(k, k, p256_norm_order);
            err = sp_256_mod_8(k, k, p256_order);
        }
        if (err == MP_OKAY) {
            sp_256_norm_8(k);
            /* kInv = 1/k mod order */
                sp_256_mont_inv_order_8(kInv, k, tmp);
            sp_256_norm_8(kInv);

            /* s = r * x + e */
                sp_256_mul_8(x, x, r);
            err = sp_256_mod_8(x, x, p256_order);
        }
        if (err == MP_OKAY) {
            sp_256_norm_8(x);
            carry = sp_256_add_8(s, e, x);
            sp_256_cond_sub_8(s, s, p256_order, 0 - carry);
            sp_256_norm_8(s);
            c = sp_256_cmp_8(s, p256_order);
            sp_256_cond_sub_8(s, s, p256_order, 0L - (sp_digit)(c >= 0));
            sp_256_norm_8(s);

            /* s = s * k^-1 mod order */
                sp_256_mont_mul_order_8(s, s, kInv);
            sp_256_norm_8(s);

            /* Check that signature is usable. */
            if (sp_256_iszero_8(s) == 0) {
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
        XMEMSET(d, 0, sizeof(sp_digit) * 8 * 8);
        XFREE(d, heap, DYNAMIC_TYPE_ECC);
    }
#else
    XMEMSET(e, 0, sizeof(sp_digit) * 2U * 8U);
    XMEMSET(x, 0, sizeof(sp_digit) * 2U * 8U);
    XMEMSET(k, 0, sizeof(sp_digit) * 2U * 8U);
    XMEMSET(r, 0, sizeof(sp_digit) * 2U * 8U);
    XMEMSET(r, 0, sizeof(sp_digit) * 2U * 8U);
    XMEMSET(tmp, 0, sizeof(sp_digit) * 3U * 2U * 8U);
#endif
    sp_256_point_free_8(point, 1, heap);

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
        sp_256_ecc_mulmod_8_ctx mulmod_ctx;
        sp_256_mont_inv_order_8_ctx mont_inv_order_ctx;
        sp_256_proj_point_dbl_8_ctx dbl_ctx;
        sp_256_proj_point_add_8_ctx add_ctx;
    };
    sp_digit u1[2*8];
    sp_digit u2[2*8];
    sp_digit s[2*8];
    sp_digit tmp[2*8 * 5];
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

        sp_256_from_bin(ctx->u1, 8, hash, (int)hashLen);
        sp_256_from_mp(ctx->u2, 8, r);
        sp_256_from_mp(ctx->s, 8, sm);
        sp_256_from_mp(ctx->p2.x, 8, pX);
        sp_256_from_mp(ctx->p2.y, 8, pY);
        sp_256_from_mp(ctx->p2.z, 8, pZ);
        ctx->state = 1;
        break;
    case 1: /* NORMS0 */
        sp_256_mul_8(ctx->s, ctx->s, p256_norm_order);
        err = sp_256_mod_8(ctx->s, ctx->s, p256_order);
        if (err == MP_OKAY)
            ctx->state = 2;
        break;
    case 2: /* NORMS1 */
        sp_256_norm_8(ctx->s);
        XMEMSET(&ctx->mont_inv_order_ctx, 0, sizeof(ctx->mont_inv_order_ctx));
        ctx->state = 3;
        break;
    case 3: /* NORMS2 */
        err = sp_256_mont_inv_order_8_nb((sp_ecc_ctx_t*)&ctx->mont_inv_order_ctx, ctx->s, ctx->s, ctx->tmp);
        if (err == MP_OKAY) {
            ctx->state = 4;
        }
        break;
    case 4: /* NORMS3 */
        sp_256_mont_mul_order_8(ctx->u1, ctx->u1, ctx->s);
        ctx->state = 5;
        break;
    case 5: /* NORMS4 */
        sp_256_mont_mul_order_8(ctx->u2, ctx->u2, ctx->s);
        XMEMSET(&ctx->mulmod_ctx, 0, sizeof(ctx->mulmod_ctx));
        ctx->state = 6;
        break;
    case 6: /* MULBASE */
        err = sp_256_ecc_mulmod_8_nb((sp_ecc_ctx_t*)&ctx->mulmod_ctx, &ctx->p1, &p256_base, ctx->u1, 0, 0, heap);
        if (err == MP_OKAY) {
            XMEMSET(&ctx->mulmod_ctx, 0, sizeof(ctx->mulmod_ctx));
            ctx->state = 7;
        }
        break;
    case 7: /* MULMOD */
        err = sp_256_ecc_mulmod_8_nb((sp_ecc_ctx_t*)&ctx->mulmod_ctx, &ctx->p2, &ctx->p2, ctx->u2, 0, 0, heap);
        if (err == MP_OKAY) {
            XMEMSET(&ctx->add_ctx, 0, sizeof(ctx->add_ctx));
            ctx->state = 8;
        }
        break;
    case 8: /* ADD */
        err = sp_256_proj_point_add_8_nb((sp_ecc_ctx_t*)&ctx->add_ctx, &ctx->p1, &ctx->p1, &ctx->p2, ctx->tmp);
        if (err == MP_OKAY)
            ctx->state = 9;
        break;
    case 9: /* DBLPREP */
        if (sp_256_iszero_8(ctx->p1.z)) {
            if (sp_256_iszero_8(ctx->p1.x) && sp_256_iszero_8(ctx->p1.y)) {
                XMEMSET(&ctx->dbl_ctx, 0, sizeof(ctx->dbl_ctx));
                ctx->state = 10;
                break;
            }
            else {
                /* Y ordinate is not used from here - don't set. */
                int i;
                for (i=0; i<8; i++) {
                    ctx->p1.x[i] = 0;
                }
                XMEMCPY(ctx->p1.z, p256_norm_mod, sizeof(p256_norm_mod));
            }
        }
        ctx->state = 11;
        break;
    case 10: /* DBL */
        err = sp_256_proj_point_dbl_8_nb((sp_ecc_ctx_t*)&ctx->dbl_ctx, &ctx->p1, 
            &ctx->p2, ctx->tmp);
        if (err == MP_OKAY) {
            ctx->state = 11;
        }
        break;
    case 11: /* MONT */
        /* (r + n*order).z'.z' mod prime == (u1.G + u2.Q)->x' */
        /* Reload r and convert to Montgomery form. */
        sp_256_from_mp(ctx->u2, 8, r);
        err = sp_256_mod_mul_norm_8(ctx->u2, ctx->u2, p256_mod);
        if (err == MP_OKAY)
            ctx->state = 12;
        break;
    case 12: /* SQR */
        /* u1 = r.z'.z' mod prime */
        sp_256_mont_sqr_8(ctx->p1.z, ctx->p1.z, p256_mod, p256_mp_mod);
        ctx->state = 13;
        break;
    case 13: /* MUL */
        sp_256_mont_mul_8(ctx->u1, ctx->u2, ctx->p1.z, p256_mod, p256_mp_mod);
        ctx->state = 14;
        break;
    case 14: /* RES */
        err = MP_OKAY; /* math okay, now check result */
        *res = (int)(sp_256_cmp_8(ctx->p1.x, ctx->u1) == 0);
        if (*res == 0) {
            sp_digit carry;
            int32_t c;

            /* Reload r and add order. */
            sp_256_from_mp(ctx->u2, 8, r);
            carry = sp_256_add_8(ctx->u2, ctx->u2, p256_order);
            /* Carry means result is greater than mod and is not valid. */
            if (carry == 0) {
                sp_256_norm_8(ctx->u2);

                /* Compare with mod and if greater or equal then not valid. */
                c = sp_256_cmp_8(ctx->u2, p256_mod);
                if (c < 0) {
                    /* Convert to Montogomery form */
                    err = sp_256_mod_mul_norm_8(ctx->u2, ctx->u2, p256_mod);
                    if (err == MP_OKAY) {
                        /* u1 = (r + 1*order).z'.z' mod prime */
                        sp_256_mont_mul_8(ctx->u1, ctx->u2, ctx->p1.z, p256_mod,
                                                                  p256_mp_mod);
                        *res = (int)(sp_256_cmp_8(ctx->p1.x, ctx->u1) == 0);
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
    sp_digit u1d[2*8];
    sp_digit u2d[2*8];
    sp_digit sd[2*8];
    sp_digit tmpd[2*8 * 5];
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
    int32_t c;
    int err;

    err = sp_256_point_new_8(heap, p1d, p1);
    if (err == MP_OKAY) {
        err = sp_256_point_new_8(heap, p2d, p2);
    }
#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (err == MP_OKAY) {
        d = (sp_digit*)XMALLOC(sizeof(sp_digit) * 16 * 8, heap,
                                                              DYNAMIC_TYPE_ECC);
        if (d == NULL) {
            err = MEMORY_E;
        }
    }
#endif

    if (err == MP_OKAY) {
#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
        u1  = d + 0 * 8;
        u2  = d + 2 * 8;
        s   = d + 4 * 8;
        tmp = d + 6 * 8;
#else
        u1 = u1d;
        u2 = u2d;
        s  = sd;
        tmp = tmpd;
#endif

        if (hashLen > 32U) {
            hashLen = 32U;
        }

        sp_256_from_bin(u1, 8, hash, (int)hashLen);
        sp_256_from_mp(u2, 8, r);
        sp_256_from_mp(s, 8, sm);
        sp_256_from_mp(p2->x, 8, pX);
        sp_256_from_mp(p2->y, 8, pY);
        sp_256_from_mp(p2->z, 8, pZ);

        {
            sp_256_mul_8(s, s, p256_norm_order);
        }
        err = sp_256_mod_8(s, s, p256_order);
    }
    if (err == MP_OKAY) {
        sp_256_norm_8(s);
        {
            sp_256_mont_inv_order_8(s, s, tmp);
            sp_256_mont_mul_order_8(u1, u1, s);
            sp_256_mont_mul_order_8(u2, u2, s);
        }

            err = sp_256_ecc_mulmod_base_8(p1, u1, 0, 0, heap);
    }
    if (err == MP_OKAY) {
            err = sp_256_ecc_mulmod_8(p2, p2, u2, 0, 0, heap);
    }

    if (err == MP_OKAY) {
        {
            sp_256_proj_point_add_8(p1, p1, p2, tmp);
            if (sp_256_iszero_8(p1->z)) {
                if (sp_256_iszero_8(p1->x) && sp_256_iszero_8(p1->y)) {
                    sp_256_proj_point_dbl_8(p1, p2, tmp);
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
                    p1->x[7] = 0;
                    XMEMCPY(p1->z, p256_norm_mod, sizeof(p256_norm_mod));
                }
            }
        }

        /* (r + n*order).z'.z' mod prime == (u1.G + u2.Q)->x' */
        /* Reload r and convert to Montgomery form. */
        sp_256_from_mp(u2, 8, r);
        err = sp_256_mod_mul_norm_8(u2, u2, p256_mod);
    }

    if (err == MP_OKAY) {
        /* u1 = r.z'.z' mod prime */
        sp_256_mont_sqr_8(p1->z, p1->z, p256_mod, p256_mp_mod);
        sp_256_mont_mul_8(u1, u2, p1->z, p256_mod, p256_mp_mod);
        *res = (int)(sp_256_cmp_8(p1->x, u1) == 0);
        if (*res == 0) {
            /* Reload r and add order. */
            sp_256_from_mp(u2, 8, r);
            carry = sp_256_add_8(u2, u2, p256_order);
            /* Carry means result is greater than mod and is not valid. */
            if (carry == 0) {
                sp_256_norm_8(u2);

                /* Compare with mod and if greater or equal then not valid. */
                c = sp_256_cmp_8(u2, p256_mod);
                if (c < 0) {
                    /* Convert to Montogomery form */
                    err = sp_256_mod_mul_norm_8(u2, u2, p256_mod);
                    if (err == MP_OKAY) {
                        /* u1 = (r + 1*order).z'.z' mod prime */
                        sp_256_mont_mul_8(u1, u2, p1->z, p256_mod,
                                                                  p256_mp_mod);
                        *res = (int)(sp_256_cmp_8(p1->x, u1) == 0);
                    }
                }
            }
        }
    }

#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (d != NULL)
        XFREE(d, heap, DYNAMIC_TYPE_ECC);
#endif
    sp_256_point_free_8(p1, 0, heap);
    sp_256_point_free_8(p2, 0, heap);

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
static int sp_256_ecc_is_point_8(sp_point_256* point, void* heap)
{
#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    sp_digit* d = NULL;
#else
    sp_digit t1d[2*8];
    sp_digit t2d[2*8];
#endif
    sp_digit* t1;
    sp_digit* t2;
    int err = MP_OKAY;

#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    d = (sp_digit*)XMALLOC(sizeof(sp_digit) * 8 * 4, heap, DYNAMIC_TYPE_ECC);
    if (d == NULL) {
        err = MEMORY_E;
    }
#endif
    (void)heap;

    if (err == MP_OKAY) {
#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
        t1 = d + 0 * 8;
        t2 = d + 2 * 8;
#else
        t1 = t1d;
        t2 = t2d;
#endif

        sp_256_sqr_8(t1, point->y);
        (void)sp_256_mod_8(t1, t1, p256_mod);
        sp_256_sqr_8(t2, point->x);
        (void)sp_256_mod_8(t2, t2, p256_mod);
        sp_256_mul_8(t2, t2, point->x);
        (void)sp_256_mod_8(t2, t2, p256_mod);
        (void)sp_256_sub_8(t2, p256_mod, t2);
        sp_256_mont_add_8(t1, t1, t2, p256_mod);

        sp_256_mont_add_8(t1, t1, point->x, p256_mod);
        sp_256_mont_add_8(t1, t1, point->x, p256_mod);
        sp_256_mont_add_8(t1, t1, point->x, p256_mod);

        if (sp_256_cmp_8(t1, p256_b) != 0) {
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

    err = sp_256_point_new_8(NULL, pubd, pub);
    if (err == MP_OKAY) {
        sp_256_from_mp(pub->x, 8, pX);
        sp_256_from_mp(pub->y, 8, pY);
        sp_256_from_bin(pub->z, 8, one, (int)sizeof(one));

        err = sp_256_ecc_is_point_8(pub, NULL);
    }

    sp_256_point_free_8(pub, 0, NULL);

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
    sp_digit privd[8];
    sp_point_256 pubd;
    sp_point_256 pd;
#endif
    sp_digit* priv = NULL;
    sp_point_256* pub;
    sp_point_256* p = NULL;
    byte one[1] = { 1 };
    int err;

    err = sp_256_point_new_8(heap, pubd, pub);
    if (err == MP_OKAY) {
        err = sp_256_point_new_8(heap, pd, p);
    }
#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (err == MP_OKAY) {
        priv = (sp_digit*)XMALLOC(sizeof(sp_digit) * 8, heap,
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

        sp_256_from_mp(pub->x, 8, pX);
        sp_256_from_mp(pub->y, 8, pY);
        sp_256_from_bin(pub->z, 8, one, (int)sizeof(one));
        sp_256_from_mp(priv, 8, privm);

        /* Check point at infinitiy. */
        if ((sp_256_iszero_8(pub->x) != 0) &&
            (sp_256_iszero_8(pub->y) != 0)) {
            err = ECC_INF_E;
        }
    }

    if (err == MP_OKAY) {
        /* Check range of X and Y */
        if (sp_256_cmp_8(pub->x, p256_mod) >= 0 ||
            sp_256_cmp_8(pub->y, p256_mod) >= 0) {
            err = ECC_OUT_OF_RANGE_E;
        }
    }

    if (err == MP_OKAY) {
        /* Check point is on curve */
        err = sp_256_ecc_is_point_8(pub, heap);
    }

    if (err == MP_OKAY) {
        /* Point * order = infinity */
            err = sp_256_ecc_mulmod_8(p, pub, p256_order, 1, 1, heap);
    }
    if (err == MP_OKAY) {
        /* Check result is infinity */
        if ((sp_256_iszero_8(p->x) == 0) ||
            (sp_256_iszero_8(p->y) == 0)) {
            err = ECC_INF_E;
        }
    }

    if (err == MP_OKAY) {
        /* Base * private = point */
            err = sp_256_ecc_mulmod_base_8(p, priv, 1, 1, heap);
    }
    if (err == MP_OKAY) {
        /* Check result is public key */
        if (sp_256_cmp_8(p->x, pub->x) != 0 ||
            sp_256_cmp_8(p->y, pub->y) != 0) {
            err = ECC_PRIV_KEY_E;
        }
    }

#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (priv != NULL) {
        XFREE(priv, heap, DYNAMIC_TYPE_ECC);
    }
#endif
    sp_256_point_free_8(p, 0, heap);
    sp_256_point_free_8(pub, 0, heap);

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
    sp_digit tmpd[2 * 8 * 5];
    sp_point_256 pd;
    sp_point_256 qd;
#endif
    sp_digit* tmp;
    sp_point_256* p;
    sp_point_256* q = NULL;
    int err;

    err = sp_256_point_new_8(NULL, pd, p);
    if (err == MP_OKAY) {
        err = sp_256_point_new_8(NULL, qd, q);
    }
#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (err == MP_OKAY) {
        tmp = (sp_digit*)XMALLOC(sizeof(sp_digit) * 2 * 8 * 5, NULL,
                                                              DYNAMIC_TYPE_ECC);
        if (tmp == NULL) {
            err = MEMORY_E;
        }
    }
#else
    tmp = tmpd;
#endif

    if (err == MP_OKAY) {
        sp_256_from_mp(p->x, 8, pX);
        sp_256_from_mp(p->y, 8, pY);
        sp_256_from_mp(p->z, 8, pZ);
        sp_256_from_mp(q->x, 8, qX);
        sp_256_from_mp(q->y, 8, qY);
        sp_256_from_mp(q->z, 8, qZ);

            sp_256_proj_point_add_8(p, p, q, tmp);
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
    sp_256_point_free_8(q, 0, NULL);
    sp_256_point_free_8(p, 0, NULL);

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
    sp_digit tmpd[2 * 8 * 2];
    sp_point_256 pd;
#endif
    sp_digit* tmp;
    sp_point_256* p;
    int err;

    err = sp_256_point_new_8(NULL, pd, p);
#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (err == MP_OKAY) {
        tmp = (sp_digit*)XMALLOC(sizeof(sp_digit) * 2 * 8 * 2, NULL,
                                                              DYNAMIC_TYPE_ECC);
        if (tmp == NULL) {
            err = MEMORY_E;
        }
    }
#else
    tmp = tmpd;
#endif

    if (err == MP_OKAY) {
        sp_256_from_mp(p->x, 8, pX);
        sp_256_from_mp(p->y, 8, pY);
        sp_256_from_mp(p->z, 8, pZ);

            sp_256_proj_point_dbl_8(p, p, tmp);
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
    sp_256_point_free_8(p, 0, NULL);

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
    sp_digit tmpd[2 * 8 * 4];
    sp_point_256 pd;
#endif
    sp_digit* tmp;
    sp_point_256* p;
    int err;

    err = sp_256_point_new_8(NULL, pd, p);
#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (err == MP_OKAY) {
        tmp = (sp_digit*)XMALLOC(sizeof(sp_digit) * 2 * 8 * 4, NULL,
                                                              DYNAMIC_TYPE_ECC);
        if (tmp == NULL) {
            err = MEMORY_E;
        }
    }
#else
    tmp = tmpd;
#endif
    if (err == MP_OKAY) {
        sp_256_from_mp(p->x, 8, pX);
        sp_256_from_mp(p->y, 8, pY);
        sp_256_from_mp(p->z, 8, pZ);

        sp_256_map_8(p, p, tmp);
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
    sp_256_point_free_8(p, 0, NULL);

    return err;
}
#endif /* WOLFSSL_PUBLIC_ECC_ADD_DBL */
#ifdef HAVE_COMP_KEY
/* Find the square root of a number mod the prime of the curve.
 *
 * y  The number to operate on and the result.
 * returns MEMORY_E if dynamic memory allocation fails and MP_OKAY otherwise.
 */
static int sp_256_mont_sqrt_8(sp_digit* y)
{
#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    sp_digit* d;
#else
    sp_digit t1d[2 * 8];
    sp_digit t2d[2 * 8];
#endif
    sp_digit* t1;
    sp_digit* t2;
    int err = MP_OKAY;

#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    d = (sp_digit*)XMALLOC(sizeof(sp_digit) * 4 * 8, NULL, DYNAMIC_TYPE_ECC);
    if (d == NULL) {
        err = MEMORY_E;
    }
#endif

    if (err == MP_OKAY) {
#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
        t1 = d + 0 * 8;
        t2 = d + 2 * 8;
#else
        t1 = t1d;
        t2 = t2d;
#endif

        {
            /* t2 = y ^ 0x2 */
            sp_256_mont_sqr_8(t2, y, p256_mod, p256_mp_mod);
            /* t1 = y ^ 0x3 */
            sp_256_mont_mul_8(t1, t2, y, p256_mod, p256_mp_mod);
            /* t2 = y ^ 0xc */
            sp_256_mont_sqr_n_8(t2, t1, 2, p256_mod, p256_mp_mod);
            /* t1 = y ^ 0xf */
            sp_256_mont_mul_8(t1, t1, t2, p256_mod, p256_mp_mod);
            /* t2 = y ^ 0xf0 */
            sp_256_mont_sqr_n_8(t2, t1, 4, p256_mod, p256_mp_mod);
            /* t1 = y ^ 0xff */
            sp_256_mont_mul_8(t1, t1, t2, p256_mod, p256_mp_mod);
            /* t2 = y ^ 0xff00 */
            sp_256_mont_sqr_n_8(t2, t1, 8, p256_mod, p256_mp_mod);
            /* t1 = y ^ 0xffff */
            sp_256_mont_mul_8(t1, t1, t2, p256_mod, p256_mp_mod);
            /* t2 = y ^ 0xffff0000 */
            sp_256_mont_sqr_n_8(t2, t1, 16, p256_mod, p256_mp_mod);
            /* t1 = y ^ 0xffffffff */
            sp_256_mont_mul_8(t1, t1, t2, p256_mod, p256_mp_mod);
            /* t1 = y ^ 0xffffffff00000000 */
            sp_256_mont_sqr_n_8(t1, t1, 32, p256_mod, p256_mp_mod);
            /* t1 = y ^ 0xffffffff00000001 */
            sp_256_mont_mul_8(t1, t1, y, p256_mod, p256_mp_mod);
            /* t1 = y ^ 0xffffffff00000001000000000000000000000000 */
            sp_256_mont_sqr_n_8(t1, t1, 96, p256_mod, p256_mp_mod);
            /* t1 = y ^ 0xffffffff00000001000000000000000000000001 */
            sp_256_mont_mul_8(t1, t1, y, p256_mod, p256_mp_mod);
            sp_256_mont_sqr_n_8(y, t1, 94, p256_mod, p256_mp_mod);
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
    sp_digit xd[2 * 8];
    sp_digit yd[2 * 8];
#endif
    sp_digit* x = NULL;
    sp_digit* y = NULL;
    int err = MP_OKAY;

#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    d = (sp_digit*)XMALLOC(sizeof(sp_digit) * 4 * 8, NULL, DYNAMIC_TYPE_ECC);
    if (d == NULL) {
        err = MEMORY_E;
    }
#endif

    if (err == MP_OKAY) {
#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
        x = d + 0 * 8;
        y = d + 2 * 8;
#else
        x = xd;
        y = yd;
#endif

        sp_256_from_mp(x, 8, xm);
        err = sp_256_mod_mul_norm_8(x, x, p256_mod);
    }
    if (err == MP_OKAY) {
        /* y = x^3 */
        {
            sp_256_mont_sqr_8(y, x, p256_mod, p256_mp_mod);
            sp_256_mont_mul_8(y, y, x, p256_mod, p256_mp_mod);
        }
        /* y = x^3 - 3x */
        sp_256_mont_sub_8(y, y, x, p256_mod);
        sp_256_mont_sub_8(y, y, x, p256_mod);
        sp_256_mont_sub_8(y, y, x, p256_mod);
        /* y = x^3 - 3x + b */
        err = sp_256_mod_mul_norm_8(x, p256_b, p256_mod);
    }
    if (err == MP_OKAY) {
        sp_256_mont_add_8(y, y, x, p256_mod);
        /* y = sqrt(x^3 - 3x + b) */
        err = sp_256_mont_sqrt_8(y);
    }
    if (err == MP_OKAY) {
        XMEMSET(y + 8, 0, 8U * sizeof(sp_digit));
        sp_256_mont_reduce_8(y, p256_mod, p256_mp_mod);
        if ((((word32)y[0] ^ (word32)odd) & 1U) != 0U) {
            sp_256_mont_sub_8(y, p256_mod, y, p256_mod);
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
    sp_digit x[2 * 12];
    sp_digit y[2 * 12];
    sp_digit z[2 * 12];
    int infinity;
} sp_point_384;

/* The modulus (prime) of the curve P384. */
static const sp_digit p384_mod[12] = {
    0xffffffff,0x00000000,0x00000000,0xffffffff,0xfffffffe,0xffffffff,
    0xffffffff,0xffffffff,0xffffffff,0xffffffff,0xffffffff,0xffffffff
};
/* The Montogmery normalizer for modulus of the curve P384. */
static const sp_digit p384_norm_mod[12] = {
    0x00000001,0xffffffff,0xffffffff,0x00000000,0x00000001,0x00000000,
    0x00000000,0x00000000,0x00000000,0x00000000,0x00000000,0x00000000
};
/* The Montogmery multiplier for modulus of the curve P384. */
static sp_digit p384_mp_mod = 0x00000001;
#if defined(WOLFSSL_VALIDATE_ECC_KEYGEN) || defined(HAVE_ECC_SIGN) || \
                                            defined(HAVE_ECC_VERIFY)
/* The order of the curve P384. */
static const sp_digit p384_order[12] = {
    0xccc52973,0xecec196a,0x48b0a77a,0x581a0db2,0xf4372ddf,0xc7634d81,
    0xffffffff,0xffffffff,0xffffffff,0xffffffff,0xffffffff,0xffffffff
};
#endif
/* The order of the curve P384 minus 2. */
static const sp_digit p384_order2[12] = {
    0xccc52971,0xecec196a,0x48b0a77a,0x581a0db2,0xf4372ddf,0xc7634d81,
    0xffffffff,0xffffffff,0xffffffff,0xffffffff,0xffffffff,0xffffffff
};
#if defined(HAVE_ECC_SIGN) || defined(HAVE_ECC_VERIFY)
/* The Montogmery normalizer for order of the curve P384. */
static const sp_digit p384_norm_order[12] = {
    0x333ad68d,0x1313e695,0xb74f5885,0xa7e5f24d,0x0bc8d220,0x389cb27e,
    0x00000000,0x00000000,0x00000000,0x00000000,0x00000000,0x00000000
};
#endif
#if defined(HAVE_ECC_SIGN) || defined(HAVE_ECC_VERIFY)
/* The Montogmery multiplier for order of the curve P384. */
static sp_digit p384_mp_order = 0xe88fdc45;
#endif
/* The base point of curve P384. */
static const sp_point_384 p384_base = {
    /* X ordinate */
    {
        0x72760ab7,0x3a545e38,0xbf55296c,0x5502f25d,0x82542a38,0x59f741e0,
        0x8ba79b98,0x6e1d3b62,0xf320ad74,0x8eb1c71e,0xbe8b0537,0xaa87ca22,
        0L, 0L, 0L, 0L, 0L, 0L, 0L, 0L, 0L, 0L, 0L, 0L
    },
    /* Y ordinate */
    {
        0x90ea0e5f,0x7a431d7c,0x1d7e819d,0x0a60b1ce,0xb5f0b8c0,0xe9da3113,
        0x289a147c,0xf8f41dbd,0x9292dc29,0x5d9e98bf,0x96262c6f,0x3617de4a,
        0L, 0L, 0L, 0L, 0L, 0L, 0L, 0L, 0L, 0L, 0L, 0L
    },
    /* Z ordinate */
    {
        0x00000001,0x00000000,0x00000000,0x00000000,0x00000000,0x00000000,
        0x00000000,0x00000000,0x00000000,0x00000000,0x00000000,0x00000000,
        0L, 0L, 0L, 0L, 0L, 0L, 0L, 0L, 0L, 0L, 0L, 0L
    },
    /* infinity */
    0
};
#if defined(HAVE_ECC_CHECK_KEY) || defined(HAVE_COMP_KEY)
static const sp_digit p384_b[12] = {
    0xd3ec2aef,0x2a85c8ed,0x8a2ed19d,0xc656398d,0x5013875a,0x0314088f,
    0xfe814112,0x181d9c6e,0xe3f82d19,0x988e056b,0xe23ee7e4,0xb3312fa7
};
#endif

static int sp_384_point_new_ex_12(void* heap, sp_point_384* sp, sp_point_384** p)
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
#define sp_384_point_new_12(heap, sp, p) sp_384_point_new_ex_12((heap), NULL, &(p))
#else
/* Set pointer to data and return no error. */
#define sp_384_point_new_12(heap, sp, p) sp_384_point_new_ex_12((heap), &(sp), &(p))
#endif


static void sp_384_point_free_12(sp_point_384* p, int clear, void* heap)
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
static int sp_384_mod_mul_norm_12(sp_digit* r, const sp_digit* a, const sp_digit* m)
{
#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    int64_t* t;
#else
    int64_t t[12];
#endif
    int64_t o;
    int err = MP_OKAY;

    (void)m;

#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    t = (int64_t*)XMALLOC(sizeof(int64_t) * 12, NULL, DYNAMIC_TYPE_ECC);
    if (t == NULL) {
        err = MEMORY_E;
    }
#endif

    if (err == MP_OKAY) {
        /*  1  0  0  0  0  0  0  0  1  1  0 -1 */
        t[0] = 0 + (uint64_t)a[0] + (uint64_t)a[8] + (uint64_t)a[9] - (uint64_t)a[11];
        /* -1  1  0  0  0  0  0  0 -1  0  1  1 */
        t[1] = 0 - (uint64_t)a[0] + (uint64_t)a[1] - (uint64_t)a[8] + (uint64_t)a[10] + (uint64_t)a[11];
        /*  0 -1  1  0  0  0  0  0  0 -1  0  1 */
        t[2] = 0 - (uint64_t)a[1] + (uint64_t)a[2] - (uint64_t)a[9] + (uint64_t)a[11];
        /*  1  0 -1  1  0  0  0  0  1  1 -1 -1 */
        t[3] = 0 + (uint64_t)a[0] - (uint64_t)a[2] + (uint64_t)a[3] + (uint64_t)a[8] + (uint64_t)a[9] - (uint64_t)a[10] - (uint64_t)a[11];
        /*  1  1  0 -1  1  0  0  0  1  2  1 -2 */
        t[4] = 0 + (uint64_t)a[0] + (uint64_t)a[1] - (uint64_t)a[3] + (uint64_t)a[4] + (uint64_t)a[8] + 2 * (uint64_t)a[9] + (uint64_t)a[10] -  2 * (uint64_t)a[11];
        /*  0  1  1  0 -1  1  0  0  0  1  2  1 */
        t[5] = 0 + (uint64_t)a[1] + (uint64_t)a[2] - (uint64_t)a[4] + (uint64_t)a[5] + (uint64_t)a[9] + 2 * (uint64_t)a[10] + (uint64_t)a[11];
        /*  0  0  1  1  0 -1  1  0  0  0  1  2 */
        t[6] = 0 + (uint64_t)a[2] + (uint64_t)a[3] - (uint64_t)a[5] + (uint64_t)a[6] + (uint64_t)a[10] + 2 * (uint64_t)a[11];
        /*  0  0  0  1  1  0 -1  1  0  0  0  1 */
        t[7] = 0 + (uint64_t)a[3] + (uint64_t)a[4] - (uint64_t)a[6] + (uint64_t)a[7] + (uint64_t)a[11];
        /*  0  0  0  0  1  1  0 -1  1  0  0  0 */
        t[8] = 0 + (uint64_t)a[4] + (uint64_t)a[5] - (uint64_t)a[7] + (uint64_t)a[8];
        /*  0  0  0  0  0  1  1  0 -1  1  0  0 */
        t[9] = 0 + (uint64_t)a[5] + (uint64_t)a[6] - (uint64_t)a[8] + (uint64_t)a[9];
        /*  0  0  0  0  0  0  1  1  0 -1  1  0 */
        t[10] = 0 + (uint64_t)a[6] + (uint64_t)a[7] - (uint64_t)a[9] + (uint64_t)a[10];
        /*  0  0  0  0  0  0  0  1  1  0 -1  1 */
        t[11] = 0 + (uint64_t)a[7] + (uint64_t)a[8] - (uint64_t)a[10] + (uint64_t)a[11];

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
        r[1] = t[1];
        r[2] = t[2];
        r[3] = t[3];
        r[4] = t[4];
        r[5] = t[5];
        r[6] = t[6];
        r[7] = t[7];
        r[8] = t[8];
        r[9] = t[9];
        r[10] = t[10];
        r[11] = t[11];
    }

#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (t != NULL)
        XFREE(t, NULL, DYNAMIC_TYPE_ECC);
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
#if DIGIT_BIT == 32
    int j;

    XMEMCPY(r, a->dp, sizeof(sp_digit) * a->used);

    for (j = a->used; j < size; j++) {
        r[j] = 0;
    }
#elif DIGIT_BIT > 32
    int i, j = 0;
    word32 s = 0;

    r[0] = 0;
    for (i = 0; i < a->used && j < size; i++) {
        r[j] |= ((sp_digit)a->dp[i] << s);
        r[j] &= 0xffffffff;
        s = 32U - s;
        if (j + 1 >= size) {
            break;
        }
        /* lint allow cast of mismatch word32 and mp_digit */
        r[++j] = (sp_digit)(a->dp[i] >> s); /*lint !e9033*/
        while ((s + 32U) <= (word32)DIGIT_BIT) {
            s += 32U;
            r[j] &= 0xffffffff;
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
        if (s + DIGIT_BIT >= 32) {
            r[j] &= 0xffffffff;
            if (j + 1 >= size) {
                break;
            }
            s = 32 - s;
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
static void sp_384_point_from_ecc_point_12(sp_point_384* p, const ecc_point* pm)
{
    XMEMSET(p->x, 0, sizeof(p->x));
    XMEMSET(p->y, 0, sizeof(p->y));
    XMEMSET(p->z, 0, sizeof(p->z));
    sp_384_from_mp(p->x, 12, pm->x);
    sp_384_from_mp(p->y, 12, pm->y);
    sp_384_from_mp(p->z, 12, pm->z);
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
#if DIGIT_BIT == 32
        XMEMCPY(r->dp, a, sizeof(sp_digit) * 12);
        r->used = 12;
        mp_clamp(r);
#elif DIGIT_BIT < 32
        int i, j = 0, s = 0;

        r->dp[0] = 0;
        for (i = 0; i < 12; i++) {
            r->dp[j] |= (mp_digit)(a[i] << s);
            r->dp[j] &= (1L << DIGIT_BIT) - 1;
            s = DIGIT_BIT - s;
            r->dp[++j] = (mp_digit)(a[i] >> s);
            while (s + DIGIT_BIT <= 32) {
                s += DIGIT_BIT;
                r->dp[j++] &= (1L << DIGIT_BIT) - 1;
                if (s == SP_WORD_SIZE) {
                    r->dp[j] = 0;
                }
                else {
                    r->dp[j] = (mp_digit)(a[i] >> s);
                }
            }
            s = 32 - s;
        }
        r->used = (384 + DIGIT_BIT - 1) / DIGIT_BIT;
        mp_clamp(r);
#else
        int i, j = 0, s = 0;

        r->dp[0] = 0;
        for (i = 0; i < 12; i++) {
            r->dp[j] |= ((mp_digit)a[i]) << s;
            if (s + 32 >= DIGIT_BIT) {
    #if DIGIT_BIT != 32 && DIGIT_BIT != 64
                r->dp[j] &= (1L << DIGIT_BIT) - 1;
    #endif
                s = DIGIT_BIT - s;
                r->dp[++j] = a[i] >> s;
                s = 32 - s;
            }
            else {
                s += 32;
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
static int sp_384_point_to_ecc_point_12(const sp_point_384* p, ecc_point* pm)
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

/* Multiply a and b into r. (r = a * b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A single precision integer.
 */
SP_NOINLINE static void sp_384_mul_12(sp_digit* r, const sp_digit* a,
        const sp_digit* b)
{
    sp_digit tmp[12 * 2];
    __asm__ __volatile__ (
        "mov	r3, #0\n\t"
        "mov	r4, #0\n\t"
        "mov	r9, r3\n\t"
        "mov	r12, %[r]\n\t"
        "mov	r10, %[a]\n\t"
        "mov	r11, %[b]\n\t"
        "mov	r6, #48\n\t"
        "add	r6, r6, r10\n\t"
        "mov	r14, r6\n\t"
        "\n1:\n\t"
        "mov	%[r], #0\n\t"
        "mov	r5, #0\n\t"
        "mov	r6, #44\n\t"
        "mov	%[a], r9\n\t"
        "subs	%[a], %[a], r6\n\t"
        "sbc	r6, r6, r6\n\t"
        "mvn	r6, r6\n\t"
        "and	%[a], %[a], r6\n\t"
        "mov	%[b], r9\n\t"
        "sub	%[b], %[b], %[a]\n\t"
        "add	%[a], %[a], r10\n\t"
        "add	%[b], %[b], r11\n\t"
        "\n2:\n\t"
        /* Multiply Start */
        "ldr	r6, [%[a]]\n\t"
        "ldr	r8, [%[b]]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r3, r3, r6\n\t"
        "adcs 	r4, r4, r8\n\t"
        "adc	r5, r5, %[r]\n\t"
        /* Multiply Done */
        "add	%[a], %[a], #4\n\t"
        "sub	%[b], %[b], #4\n\t"
        "cmp	%[a], r14\n\t"
        "beq	3f\n\t"
        "mov	r6, r9\n\t"
        "add	r6, r6, r10\n\t"
        "cmp	%[a], r6\n\t"
        "ble	2b\n\t"
        "\n3:\n\t"
        "mov	%[r], r12\n\t"
        "mov	r8, r9\n\t"
        "str	r3, [%[r], r8]\n\t"
        "mov	r3, r4\n\t"
        "mov	r4, r5\n\t"
        "add	r8, r8, #4\n\t"
        "mov	r9, r8\n\t"
        "mov	r6, #88\n\t"
        "cmp	r8, r6\n\t"
        "ble	1b\n\t"
        "str	r3, [%[r], r8]\n\t"
        "mov	%[a], r10\n\t"
        "mov	%[b], r11\n\t"
        :
        : [r] "r" (tmp), [a] "r" (a), [b] "r" (b)
        : "memory", "r3", "r4", "r5", "r6", "r8", "r9", "r10", "r11", "r12", "r14"
    );

    XMEMCPY(r, tmp, sizeof(tmp));
}

/* Conditionally subtract b from a using the mask m.
 * m is -1 to subtract and 0 when not copying.
 *
 * r  A single precision number representing condition subtract result.
 * a  A single precision number to subtract from.
 * b  A single precision number to subtract.
 * m  Mask value to apply.
 */
SP_NOINLINE static sp_digit sp_384_cond_sub_12(sp_digit* r, const sp_digit* a,
        const sp_digit* b, sp_digit m)
{
    sp_digit c = 0;

    __asm__ __volatile__ (
        "mov	r5, #48\n\t"
        "mov	r9, r5\n\t"
        "mov	r8, #0\n\t"
        "\n1:\n\t"
        "ldr	r6, [%[b], r8]\n\t"
        "and	r6, r6, %[m]\n\t"
        "mov	r5, #0\n\t"
        "subs	r5, r5, %[c]\n\t"
        "ldr	r5, [%[a], r8]\n\t"
        "sbcs	r5, r5, r6\n\t"
        "sbcs	%[c], %[c], %[c]\n\t"
        "str	r5, [%[r], r8]\n\t"
        "add	r8, r8, #4\n\t"
        "cmp	r8, r9\n\t"
        "blt	1b\n\t"
        : [c] "+r" (c)
        : [r] "r" (r), [a] "r" (a), [b] "r" (b), [m] "r" (m)
        : "memory", "r5", "r6", "r8", "r9"
    );

    return c;
}

#define sp_384_mont_reduce_order_12   sp_384_mont_reduce_12

/* Reduce the number back to 384 bits using Montgomery reduction.
 *
 * a   A single precision number to reduce in place.
 * m   The single precision number representing the modulus.
 * mp  The digit representing the negative inverse of m mod 2^n.
 */
SP_NOINLINE static void sp_384_mont_reduce_12(sp_digit* a, const sp_digit* m,
        sp_digit mp)
{
    sp_digit ca = 0;

    __asm__ __volatile__ (
        "mov	r9, %[mp]\n\t"
        "mov	r12, %[m]\n\t"
        "mov	r10, %[a]\n\t"
        "mov	r4, #0\n\t"
        "add	r11, r10, #48\n\t"
        "\n1:\n\t"
        /* mu = a[i] * mp */
        "mov	%[mp], r9\n\t"
        "ldr	%[a], [r10]\n\t"
        "mul	%[mp], %[mp], %[a]\n\t"
        "mov	%[m], r12\n\t"
        "add	r14, r10, #40\n\t"
        "\n2:\n\t"
        /* a[i+j] += m[j] * mu */
        "ldr	%[a], [r10]\n\t"
        "mov	r5, #0\n\t"
        /* Multiply m[j] and mu - Start */
        "ldr	r8, [%[m]], #4\n\t"
        "umull	r6, r8, %[mp], r8\n\t"
        "adds	%[a], %[a], r6\n\t"
        "adc	r5, r5, r8\n\t"
        /* Multiply m[j] and mu - Done */
        "adds	r4, r4, %[a]\n\t"
        "adc	r5, r5, #0\n\t"
        "str	r4, [r10], #4\n\t"
        /* a[i+j+1] += m[j+1] * mu */
        "ldr	%[a], [r10]\n\t"
        "mov	r4, #0\n\t"
        /* Multiply m[j] and mu - Start */
        "ldr	r8, [%[m]], #4\n\t"
        "umull	r6, r8, %[mp], r8\n\t"
        "adds	%[a], %[a], r6\n\t"
        "adc	r4, r4, r8\n\t"
        /* Multiply m[j] and mu - Done */
        "adds	r5, r5, %[a]\n\t"
        "adc	r4, r4, #0\n\t"
        "str	r5, [r10], #4\n\t"
        "cmp	r10, r14\n\t"
        "blt	2b\n\t"
        /* a[i+10] += m[10] * mu */
        "ldr	%[a], [r10]\n\t"
        "mov	r5, #0\n\t"
        /* Multiply m[j] and mu - Start */
        "ldr	r8, [%[m]], #4\n\t"
        "umull	r6, r8, %[mp], r8\n\t"
        "adds	%[a], %[a], r6\n\t"
        "adc	r5, r5, r8\n\t"
        /* Multiply m[j] and mu - Done */
        "adds	r4, r4, %[a]\n\t"
        "adc	r5, r5, #0\n\t"
        "str	r4, [r10], #4\n\t"
        /* a[i+11] += m[11] * mu */
        "mov	r4, %[ca]\n\t"
        "mov	%[ca], #0\n\t"
        /* Multiply m[11] and mu - Start */
        "ldr	r8, [%[m]]\n\t"
        "umull	r6, r8, %[mp], r8\n\t"
        "adds	r5, r5, r6\n\t"
        "adcs 	r4, r4, r8\n\t"
        "adc	%[ca], %[ca], #0\n\t"
        /* Multiply m[11] and mu - Done */
        "ldr	r6, [r10]\n\t"
        "ldr	r8, [r10, #4]\n\t"
        "adds	r6, r6, r5\n\t"
        "adcs	r8, r8, r4\n\t"
        "adc	%[ca], %[ca], #0\n\t"
        "str	r6, [r10]\n\t"
        "str	r8, [r10, #4]\n\t"
        /* Next word in a */
        "sub	r10, r10, #40\n\t"
        "cmp	r10, r11\n\t"
        "blt	1b\n\t"
        "mov	%[a], r10\n\t"
        "mov	%[m], r12\n\t"
        : [ca] "+r" (ca), [a] "+r" (a)
        : [m] "r" (m), [mp] "r" (mp)
        : "memory", "r4", "r5", "r6", "r8", "r9", "r10", "r11", "r12", "r14"
    );

    sp_384_cond_sub_12(a - 12, a, m, (sp_digit)0 - ca);
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
static void sp_384_mont_mul_12(sp_digit* r, const sp_digit* a, const sp_digit* b,
        const sp_digit* m, sp_digit mp)
{
    sp_384_mul_12(r, a, b);
    sp_384_mont_reduce_12(r, m, mp);
}

/* Square a and put result in r. (r = a * a)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 */
SP_NOINLINE static void sp_384_sqr_12(sp_digit* r, const sp_digit* a)
{
    __asm__ __volatile__ (
        "mov	r3, #0\n\t"
        "mov	r4, #0\n\t"
        "mov	r5, #0\n\t"
        "mov	r9, r3\n\t"
        "mov	r12, %[r]\n\t"
        "mov	r6, #96\n\t"
        "neg	r6, r6\n\t"
        "add	sp, sp, r6\n\t"
        "mov	r11, sp\n\t"
        "mov	r10, %[a]\n\t"
        "\n1:\n\t"
        "mov	%[r], #0\n\t"
        "mov	r6, #44\n\t"
        "mov	%[a], r9\n\t"
        "subs	%[a], %[a], r6\n\t"
        "sbc	r6, r6, r6\n\t"
        "mvn	r6, r6\n\t"
        "and	%[a], %[a], r6\n\t"
        "mov	r2, r9\n\t"
        "sub	r2, r2, %[a]\n\t"
        "add	%[a], %[a], r10\n\t"
        "add	r2, r2, r10\n\t"
        "\n2:\n\t"
        "cmp	r2, %[a]\n\t"
        "beq	4f\n\t"
        /* Multiply * 2: Start */
        "ldr	r6, [%[a]]\n\t"
        "ldr	r8, [r2]\n\t"
        "umull	r6, r8, r6, r8\n\t"
        "adds	r3, r3, r6\n\t"
        "adcs 	r4, r4, r8\n\t"
        "adc	r5, r5, %[r]\n\t"
        "adds	r3, r3, r6\n\t"
        "adcs 	r4, r4, r8\n\t"
        "adc	r5, r5, %[r]\n\t"
        /* Multiply * 2: Done */
        "bal	5f\n\t"
        "\n4:\n\t"
        /* Square: Start */
        "ldr	r6, [%[a]]\n\t"
        "umull	r6, r8, r6, r6\n\t"
        "adds	r3, r3, r6\n\t"
        "adcs	r4, r4, r8\n\t"
        "adc	r5, r5, %[r]\n\t"
        /* Square: Done */
        "\n5:\n\t"
        "add	%[a], %[a], #4\n\t"
        "sub	r2, r2, #4\n\t"
        "mov	r6, #48\n\t"
        "add	r6, r6, r10\n\t"
        "cmp	%[a], r6\n\t"
        "beq	3f\n\t"
        "cmp	%[a], r2\n\t"
        "bgt	3f\n\t"
        "mov	r8, r9\n\t"
        "add	r8, r8, r10\n\t"
        "cmp	%[a], r8\n\t"
        "ble	2b\n\t"
        "\n3:\n\t"
        "mov	%[r], r11\n\t"
        "mov	r8, r9\n\t"
        "str	r3, [%[r], r8]\n\t"
        "mov	r3, r4\n\t"
        "mov	r4, r5\n\t"
        "mov	r5, #0\n\t"
        "add	r8, r8, #4\n\t"
        "mov	r9, r8\n\t"
        "mov	r6, #88\n\t"
        "cmp	r8, r6\n\t"
        "ble	1b\n\t"
        "mov	%[a], r10\n\t"
        "str	r3, [%[r], r8]\n\t"
        "mov	%[r], r12\n\t"
        "mov	%[a], r11\n\t"
        "mov	r3, #92\n\t"
        "\n4:\n\t"
        "ldr	r6, [%[a], r3]\n\t"
        "str	r6, [%[r], r3]\n\t"
        "subs	r3, r3, #4\n\t"
        "bge	4b\n\t"
        "mov	r6, #96\n\t"
        "add	sp, sp, r6\n\t"
        :
        : [r] "r" (r), [a] "r" (a)
        : "memory", "r2", "r3", "r4", "r5", "r6", "r8", "r9", "r10", "r11", "r12"
    );
}

/* Square the Montgomery form number. (r = a * a mod m)
 *
 * r   Result of squaring.
 * a   Number to square in Montogmery form.
 * m   Modulus (prime).
 * mp  Montogmery mulitplier.
 */
static void sp_384_mont_sqr_12(sp_digit* r, const sp_digit* a, const sp_digit* m,
        sp_digit mp)
{
    sp_384_sqr_12(r, a);
    sp_384_mont_reduce_12(r, m, mp);
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
static void sp_384_mont_sqr_n_12(sp_digit* r, const sp_digit* a, int n,
        const sp_digit* m, sp_digit mp)
{
    sp_384_mont_sqr_12(r, a, m, mp);
    for (; n > 1; n--) {
        sp_384_mont_sqr_12(r, r, m, mp);
    }
}

#endif /* !WOLFSSL_SP_SMALL || HAVE_COMP_KEY */
#ifdef WOLFSSL_SP_SMALL
/* Mod-2 for the P384 curve. */
static const uint32_t p384_mod_minus_2[12] = {
    0xfffffffdU,0x00000000U,0x00000000U,0xffffffffU,0xfffffffeU,0xffffffffU,
    0xffffffffU,0xffffffffU,0xffffffffU,0xffffffffU,0xffffffffU,0xffffffffU
};
#endif /* !WOLFSSL_SP_SMALL */

/* Invert the number, in Montgomery form, modulo the modulus (prime) of the
 * P384 curve. (r = 1 / a mod m)
 *
 * r   Inverse result.
 * a   Number to invert.
 * td  Temporary data.
 */
static void sp_384_mont_inv_12(sp_digit* r, const sp_digit* a, sp_digit* td)
{
#ifdef WOLFSSL_SP_SMALL
    sp_digit* t = td;
    int i;

    XMEMCPY(t, a, sizeof(sp_digit) * 12);
    for (i=382; i>=0; i--) {
        sp_384_mont_sqr_12(t, t, p384_mod, p384_mp_mod);
        if (p384_mod_minus_2[i / 32] & ((sp_digit)1 << (i % 32)))
            sp_384_mont_mul_12(t, t, a, p384_mod, p384_mp_mod);
    }
    XMEMCPY(r, t, sizeof(sp_digit) * 12);
#else
    sp_digit* t1 = td;
    sp_digit* t2 = td + 2 * 12;
    sp_digit* t3 = td + 4 * 12;
    sp_digit* t4 = td + 6 * 12;
    sp_digit* t5 = td + 8 * 12;

    /* 0x2 */
    sp_384_mont_sqr_12(t1, a, p384_mod, p384_mp_mod);
    /* 0x3 */
    sp_384_mont_mul_12(t5, t1, a, p384_mod, p384_mp_mod);
    /* 0xc */
    sp_384_mont_sqr_n_12(t1, t5, 2, p384_mod, p384_mp_mod);
    /* 0xf */
    sp_384_mont_mul_12(t2, t5, t1, p384_mod, p384_mp_mod);
    /* 0x1e */
    sp_384_mont_sqr_12(t1, t2, p384_mod, p384_mp_mod);
    /* 0x1f */
    sp_384_mont_mul_12(t4, t1, a, p384_mod, p384_mp_mod);
    /* 0x3e0 */
    sp_384_mont_sqr_n_12(t1, t4, 5, p384_mod, p384_mp_mod);
    /* 0x3ff */
    sp_384_mont_mul_12(t2, t4, t1, p384_mod, p384_mp_mod);
    /* 0x7fe0 */
    sp_384_mont_sqr_n_12(t1, t2, 5, p384_mod, p384_mp_mod);
    /* 0x7fff */
    sp_384_mont_mul_12(t4, t4, t1, p384_mod, p384_mp_mod);
    /* 0x3fff8000 */
    sp_384_mont_sqr_n_12(t1, t4, 15, p384_mod, p384_mp_mod);
    /* 0x3fffffff */
    sp_384_mont_mul_12(t2, t4, t1, p384_mod, p384_mp_mod);
    /* 0xfffffffc */
    sp_384_mont_sqr_n_12(t3, t2, 2, p384_mod, p384_mp_mod);
    /* 0xfffffffd */
    sp_384_mont_mul_12(r, t3, a, p384_mod, p384_mp_mod);
    /* 0xffffffff */
    sp_384_mont_mul_12(t3, t5, t3, p384_mod, p384_mp_mod);
    /* 0xfffffffc0000000 */
    sp_384_mont_sqr_n_12(t1, t2, 30, p384_mod, p384_mp_mod);
    /* 0xfffffffffffffff */
    sp_384_mont_mul_12(t2, t2, t1, p384_mod, p384_mp_mod);
    /* 0xfffffffffffffff000000000000000 */
    sp_384_mont_sqr_n_12(t1, t2, 60, p384_mod, p384_mp_mod);
    /* 0xffffffffffffffffffffffffffffff */
    sp_384_mont_mul_12(t2, t2, t1, p384_mod, p384_mp_mod);
    /* 0xffffffffffffffffffffffffffffff000000000000000000000000000000 */
    sp_384_mont_sqr_n_12(t1, t2, 120, p384_mod, p384_mp_mod);
    /* 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff */
    sp_384_mont_mul_12(t2, t2, t1, p384_mod, p384_mp_mod);
    /* 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8000 */
    sp_384_mont_sqr_n_12(t1, t2, 15, p384_mod, p384_mp_mod);
    /* 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff */
    sp_384_mont_mul_12(t2, t4, t1, p384_mod, p384_mp_mod);
    /* 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe00000000 */
    sp_384_mont_sqr_n_12(t1, t2, 33, p384_mod, p384_mp_mod);
    /* 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff */
    sp_384_mont_mul_12(t2, t3, t1, p384_mod, p384_mp_mod);
    /* 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff000000000000000000000000 */
    sp_384_mont_sqr_n_12(t1, t2, 96, p384_mod, p384_mp_mod);
    /* 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff0000000000000000fffffffd */
    sp_384_mont_mul_12(r, r, t1, p384_mod, p384_mp_mod);

#endif /* WOLFSSL_SP_SMALL */
}

/* Compare a with b in constant time.
 *
 * a  A single precision integer.
 * b  A single precision integer.
 * return -ve, 0 or +ve if a is less than, equal to or greater than b
 * respectively.
 */
SP_NOINLINE static int32_t sp_384_cmp_12(const sp_digit* a, const sp_digit* b)
{
    sp_digit r = 0;


    __asm__ __volatile__ (
        "mov	r3, #0\n\t"
        "mvn	r3, r3\n\t"
        "mov	r6, #44\n\t"
        "\n1:\n\t"
        "ldr	r8, [%[a], r6]\n\t"
        "ldr	r5, [%[b], r6]\n\t"
        "and	r8, r8, r3\n\t"
        "and	r5, r5, r3\n\t"
        "mov	r4, r8\n\t"
        "subs	r8, r8, r5\n\t"
        "sbc	r8, r8, r8\n\t"
        "add	%[r], %[r], r8\n\t"
        "mvn	r8, r8\n\t"
        "and	r3, r3, r8\n\t"
        "subs	r5, r5, r4\n\t"
        "sbc	r8, r8, r8\n\t"
        "sub	%[r], %[r], r8\n\t"
        "mvn	r8, r8\n\t"
        "and	r3, r3, r8\n\t"
        "sub	r6, r6, #4\n\t"
        "cmp	r6, #0\n\t"
        "bge	1b\n\t"
        : [r] "+r" (r)
        : [a] "r" (a), [b] "r" (b)
        : "r3", "r4", "r5", "r6", "r8"
    );

    return r;
}

/* Normalize the values in each word to 32.
 *
 * a  Array of sp_digit to normalize.
 */
#define sp_384_norm_12(a)

/* Map the Montgomery form projective coordinate point to an affine point.
 *
 * r  Resulting affine coordinate point.
 * p  Montgomery form projective coordinate point.
 * t  Temporary ordinate data.
 */
static void sp_384_map_12(sp_point_384* r, const sp_point_384* p, sp_digit* t)
{
    sp_digit* t1 = t;
    sp_digit* t2 = t + 2*12;
    int32_t n;

    sp_384_mont_inv_12(t1, p->z, t + 2*12);

    sp_384_mont_sqr_12(t2, t1, p384_mod, p384_mp_mod);
    sp_384_mont_mul_12(t1, t2, t1, p384_mod, p384_mp_mod);

    /* x /= z^2 */
    sp_384_mont_mul_12(r->x, p->x, t2, p384_mod, p384_mp_mod);
    XMEMSET(r->x + 12, 0, sizeof(r->x) / 2U);
    sp_384_mont_reduce_12(r->x, p384_mod, p384_mp_mod);
    /* Reduce x to less than modulus */
    n = sp_384_cmp_12(r->x, p384_mod);
    sp_384_cond_sub_12(r->x, r->x, p384_mod, 0 - ((n >= 0) ?
                (sp_digit)1 : (sp_digit)0));
    sp_384_norm_12(r->x);

    /* y /= z^3 */
    sp_384_mont_mul_12(r->y, p->y, t1, p384_mod, p384_mp_mod);
    XMEMSET(r->y + 12, 0, sizeof(r->y) / 2U);
    sp_384_mont_reduce_12(r->y, p384_mod, p384_mp_mod);
    /* Reduce y to less than modulus */
    n = sp_384_cmp_12(r->y, p384_mod);
    sp_384_cond_sub_12(r->y, r->y, p384_mod, 0 - ((n >= 0) ?
                (sp_digit)1 : (sp_digit)0));
    sp_384_norm_12(r->y);

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
SP_NOINLINE static sp_digit sp_384_add_12(sp_digit* r, const sp_digit* a,
        const sp_digit* b)
{
    sp_digit c = 0;

    __asm__ __volatile__ (
        "mov	r6, %[a]\n\t"
        "mov	r8, #0\n\t"
        "add	r6, r6, #48\n\t"
        "sub	r8, r8, #1\n\t"
        "\n1:\n\t"
        "adds	%[c], %[c], r8\n\t"
        "ldr	r4, [%[a]]\n\t"
        "ldr	r5, [%[b]]\n\t"
        "adcs	r4, r4, r5\n\t"
        "str	r4, [%[r]]\n\t"
        "mov	%[c], #0\n\t"
        "adc	%[c], %[c], %[c]\n\t"
        "add	%[a], %[a], #4\n\t"
        "add	%[b], %[b], #4\n\t"
        "add	%[r], %[r], #4\n\t"
        "cmp	%[a], r6\n\t"
        "bne	1b\n\t"
        : [c] "+r" (c), [r] "+r" (r), [a] "+r" (a), [b] "+r" (b)
        :
        : "memory", "r4", "r5", "r6", "r8"
    );

    return c;
}

#else
/* Add b to a into r. (r = a + b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A single precision integer.
 */
SP_NOINLINE static sp_digit sp_384_add_12(sp_digit* r, const sp_digit* a,
        const sp_digit* b)
{
    sp_digit c = 0;

    __asm__ __volatile__ (
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adds	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "ldm	%[a]!, {r4, r5}\n\t"
        "ldm	%[b]!, {r6, r8}\n\t"
        "adcs	r4, r4, r6\n\t"
        "adcs	r5, r5, r8\n\t"
        "stm	%[r]!, {r4, r5}\n\t"
        "mov	%[c], #0\n\t"
        "adc	%[c], %[c], %[c]\n\t"
        : [c] "+r" (c), [r] "+r" (r), [a] "+r" (a), [b] "+r" (b)
        :
        : "memory", "r4", "r5", "r6", "r8"
    );

    return c;
}

#endif /* WOLFSSL_SP_SMALL */
/* Add two Montgomery form numbers (r = a + b % m).
 *
 * r   Result of addition.
 * a   First number to add in Montogmery form.
 * b   Second number to add in Montogmery form.
 * m   Modulus (prime).
 */
SP_NOINLINE static void sp_384_mont_add_12(sp_digit* r, const sp_digit* a, const sp_digit* b,
        const sp_digit* m)
{
    sp_digit o;

    o = sp_384_add_12(r, a, b);
    sp_384_cond_sub_12(r, r, m, 0 - o);
}

/* Double a Montgomery form number (r = a + a % m).
 *
 * r   Result of doubling.
 * a   Number to double in Montogmery form.
 * m   Modulus (prime).
 */
SP_NOINLINE static void sp_384_mont_dbl_12(sp_digit* r, const sp_digit* a, const sp_digit* m)
{
    sp_digit o;

    o = sp_384_add_12(r, a, a);
    sp_384_cond_sub_12(r, r, m, 0 - o);
}

/* Triple a Montgomery form number (r = a + a + a % m).
 *
 * r   Result of Tripling.
 * a   Number to triple in Montogmery form.
 * m   Modulus (prime).
 */
SP_NOINLINE static void sp_384_mont_tpl_12(sp_digit* r, const sp_digit* a, const sp_digit* m)
{
    sp_digit o;

    o = sp_384_add_12(r, a, a);
    sp_384_cond_sub_12(r, r, m, 0 - o);
    o = sp_384_add_12(r, r, a);
    sp_384_cond_sub_12(r, r, m, 0 - o);
}

#ifdef WOLFSSL_SP_SMALL
/* Sub b from a into r. (r = a - b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A single precision integer.
 */
SP_NOINLINE static sp_digit sp_384_sub_12(sp_digit* r, const sp_digit* a,
        const sp_digit* b)
{
    sp_digit c = 0;

    __asm__ __volatile__ (
        "mov	r6, %[a]\n\t"
        "add	r6, r6, #48\n\t"
        "\n1:\n\t"
        "mov	r5, #0\n\t"
        "subs	r5, r5, %[c]\n\t"
        "ldr	r4, [%[a]]\n\t"
        "ldr	r5, [%[b]]\n\t"
        "sbcs	r4, r4, r5\n\t"
        "str	r4, [%[r]]\n\t"
        "sbc	%[c], %[c], %[c]\n\t"
        "add	%[a], %[a], #4\n\t"
        "add	%[b], %[b], #4\n\t"
        "add	%[r], %[r], #4\n\t"
        "cmp	%[a], r6\n\t"
        "bne	1b\n\t"
        : [c] "+r" (c), [r] "+r" (r), [a] "+r" (a), [b] "+r" (b)
        :
        : "memory", "r4", "r5", "r6"
    );

    return c;
}

#else
/* Sub b from a into r. (r = a - b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A single precision integer.
 */
SP_NOINLINE static sp_digit sp_384_sub_12(sp_digit* r, const sp_digit* a,
        const sp_digit* b)
{
    sp_digit c = 0;

    __asm__ __volatile__ (
        "ldr	r4, [%[a], #0]\n\t"
        "ldr	r5, [%[a], #4]\n\t"
        "ldr	r6, [%[b], #0]\n\t"
        "ldr	r8, [%[b], #4]\n\t"
        "subs	r4, r4, r6\n\t"
        "sbcs	r5, r5, r8\n\t"
        "str	r4, [%[r], #0]\n\t"
        "str	r5, [%[r], #4]\n\t"
        "ldr	r4, [%[a], #8]\n\t"
        "ldr	r5, [%[a], #12]\n\t"
        "ldr	r6, [%[b], #8]\n\t"
        "ldr	r8, [%[b], #12]\n\t"
        "sbcs	r4, r4, r6\n\t"
        "sbcs	r5, r5, r8\n\t"
        "str	r4, [%[r], #8]\n\t"
        "str	r5, [%[r], #12]\n\t"
        "ldr	r4, [%[a], #16]\n\t"
        "ldr	r5, [%[a], #20]\n\t"
        "ldr	r6, [%[b], #16]\n\t"
        "ldr	r8, [%[b], #20]\n\t"
        "sbcs	r4, r4, r6\n\t"
        "sbcs	r5, r5, r8\n\t"
        "str	r4, [%[r], #16]\n\t"
        "str	r5, [%[r], #20]\n\t"
        "ldr	r4, [%[a], #24]\n\t"
        "ldr	r5, [%[a], #28]\n\t"
        "ldr	r6, [%[b], #24]\n\t"
        "ldr	r8, [%[b], #28]\n\t"
        "sbcs	r4, r4, r6\n\t"
        "sbcs	r5, r5, r8\n\t"
        "str	r4, [%[r], #24]\n\t"
        "str	r5, [%[r], #28]\n\t"
        "ldr	r4, [%[a], #32]\n\t"
        "ldr	r5, [%[a], #36]\n\t"
        "ldr	r6, [%[b], #32]\n\t"
        "ldr	r8, [%[b], #36]\n\t"
        "sbcs	r4, r4, r6\n\t"
        "sbcs	r5, r5, r8\n\t"
        "str	r4, [%[r], #32]\n\t"
        "str	r5, [%[r], #36]\n\t"
        "ldr	r4, [%[a], #40]\n\t"
        "ldr	r5, [%[a], #44]\n\t"
        "ldr	r6, [%[b], #40]\n\t"
        "ldr	r8, [%[b], #44]\n\t"
        "sbcs	r4, r4, r6\n\t"
        "sbcs	r5, r5, r8\n\t"
        "str	r4, [%[r], #40]\n\t"
        "str	r5, [%[r], #44]\n\t"
        "sbc	%[c], %[c], %[c]\n\t"
        : [c] "+r" (c), [r] "+r" (r), [a] "+r" (a), [b] "+r" (b)
        :
        : "memory", "r4", "r5", "r6", "r8"
    );

    return c;
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
SP_NOINLINE static sp_digit sp_384_cond_add_12(sp_digit* r, const sp_digit* a, const sp_digit* b,
        sp_digit m)
{
    sp_digit c = 0;

    __asm__ __volatile__ (
        "mov	r5, #48\n\t"
        "mov	r9, r5\n\t"
        "mov	r8, #0\n\t"
        "\n1:\n\t"
        "ldr	r6, [%[b], r8]\n\t"
        "and	r6, r6, %[m]\n\t"
        "adds	r5, %[c], #-1\n\t"
        "ldr	r5, [%[a], r8]\n\t"
        "adcs	r5, r5, r6\n\t"
        "mov	%[c], #0\n\t"
        "adcs	%[c], %[c], %[c]\n\t"
        "str	r5, [%[r], r8]\n\t"
        "add	r8, r8, #4\n\t"
        "cmp	r8, r9\n\t"
        "blt	1b\n\t"
        : [c] "+r" (c)
        : [r] "r" (r), [a] "r" (a), [b] "r" (b), [m] "r" (m)
        : "memory", "r5", "r6", "r8", "r9"
    );

    return c;
}

/* Subtract two Montgomery form numbers (r = a - b % m).
 *
 * r   Result of subtration.
 * a   Number to subtract from in Montogmery form.
 * b   Number to subtract with in Montogmery form.
 * m   Modulus (prime).
 */
SP_NOINLINE static void sp_384_mont_sub_12(sp_digit* r, const sp_digit* a, const sp_digit* b,
        const sp_digit* m)
{
    sp_digit o;

    o = sp_384_sub_12(r, a, b);
    sp_384_cond_add_12(r, r, m, o);
}

static void sp_384_rshift1_12(sp_digit* r, sp_digit* a)
{
    __asm__ __volatile__ (
        "ldr	r2, [%[a]]\n\t"
        "ldr	r3, [%[a], #4]\n\t"
        "lsr	r2, r2, #1\n\t"
        "lsl	r5, r3, #31\n\t"
        "lsr	r3, r3, #1\n\t"
        "orr	r2, r2, r5\n\t"
        "ldr	r4, [%[a], #8]\n\t"
        "str	r2, [%[r], #0]\n\t"
        "lsl	r5, r4, #31\n\t"
        "lsr	r4, r4, #1\n\t"
        "orr	r3, r3, r5\n\t"
        "ldr	r2, [%[a], #12]\n\t"
        "str	r3, [%[r], #4]\n\t"
        "lsl	r5, r2, #31\n\t"
        "lsr	r2, r2, #1\n\t"
        "orr	r4, r4, r5\n\t"
        "ldr	r3, [%[a], #16]\n\t"
        "str	r4, [%[r], #8]\n\t"
        "lsl	r5, r3, #31\n\t"
        "lsr	r3, r3, #1\n\t"
        "orr	r2, r2, r5\n\t"
        "ldr	r4, [%[a], #20]\n\t"
        "str	r2, [%[r], #12]\n\t"
        "lsl	r5, r4, #31\n\t"
        "lsr	r4, r4, #1\n\t"
        "orr	r3, r3, r5\n\t"
        "ldr	r2, [%[a], #24]\n\t"
        "str	r3, [%[r], #16]\n\t"
        "lsl	r5, r2, #31\n\t"
        "lsr	r2, r2, #1\n\t"
        "orr	r4, r4, r5\n\t"
        "ldr	r3, [%[a], #28]\n\t"
        "str	r4, [%[r], #20]\n\t"
        "lsl	r5, r3, #31\n\t"
        "lsr	r3, r3, #1\n\t"
        "orr	r2, r2, r5\n\t"
        "ldr	r4, [%[a], #32]\n\t"
        "str	r2, [%[r], #24]\n\t"
        "lsl	r5, r4, #31\n\t"
        "lsr	r4, r4, #1\n\t"
        "orr	r3, r3, r5\n\t"
        "ldr	r2, [%[a], #36]\n\t"
        "str	r3, [%[r], #28]\n\t"
        "lsl	r5, r2, #31\n\t"
        "lsr	r2, r2, #1\n\t"
        "orr	r4, r4, r5\n\t"
        "ldr	r3, [%[a], #40]\n\t"
        "str	r4, [%[r], #32]\n\t"
        "lsl	r5, r3, #31\n\t"
        "lsr	r3, r3, #1\n\t"
        "orr	r2, r2, r5\n\t"
        "ldr	r4, [%[a], #44]\n\t"
        "str	r2, [%[r], #36]\n\t"
        "lsl	r5, r4, #31\n\t"
        "lsr	r4, r4, #1\n\t"
        "orr	r3, r3, r5\n\t"
        "str	r3, [%[r], #40]\n\t"
        "str	r4, [%[r], #44]\n\t"
        :
        : [r] "r" (r), [a] "r" (a)
        : "memory", "r2", "r3", "r4", "r5"
    );
}

/* Divide the number by 2 mod the modulus (prime). (r = a / 2 % m)
 *
 * r  Result of division by 2.
 * a  Number to divide.
 * m  Modulus (prime).
 */
SP_NOINLINE static void sp_384_div2_12(sp_digit* r, const sp_digit* a, const sp_digit* m)
{
    sp_digit o;

    o = sp_384_cond_add_12(r, a, m, 0 - (a[0] & 1));
    sp_384_rshift1_12(r, r);
    r[11] |= o << 31;
}

/* Double the Montgomery form projective point p.
 *
 * r  Result of doubling point.
 * p  Point to double.
 * t  Temporary ordinate data.
 */
#ifdef WOLFSSL_SP_NONBLOCK
typedef struct sp_384_proj_point_dbl_12_ctx {
    int state;
    sp_digit* t1;
    sp_digit* t2;
    sp_digit* x;
    sp_digit* y;
    sp_digit* z;
} sp_384_proj_point_dbl_12_ctx;

static int sp_384_proj_point_dbl_12_nb(sp_ecc_ctx_t* sp_ctx, sp_point_384* r, const sp_point_384* p, sp_digit* t)
{
    int err = FP_WOULDBLOCK;
    sp_384_proj_point_dbl_12_ctx* ctx = (sp_384_proj_point_dbl_12_ctx*)sp_ctx->data;

    typedef char ctx_size_test[sizeof(sp_384_proj_point_dbl_12_ctx) >= sizeof(*sp_ctx) ? -1 : 1];
    (void)sizeof(ctx_size_test);

    switch (ctx->state) {
    case 0:
        ctx->t1 = t;
        ctx->t2 = t + 2*12;
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
        sp_384_mont_sqr_12(ctx->t1, p->z, p384_mod, p384_mp_mod);
        ctx->state = 2;
        break;
    case 2:
        /* Z = Y * Z */
        sp_384_mont_mul_12(ctx->z, p->y, p->z, p384_mod, p384_mp_mod);
        ctx->state = 3;
        break;
    case 3:
        /* Z = 2Z */
        sp_384_mont_dbl_12(ctx->z, ctx->z, p384_mod);
        ctx->state = 4;
        break;
    case 4:
        /* T2 = X - T1 */
        sp_384_mont_sub_12(ctx->t2, p->x, ctx->t1, p384_mod);
        ctx->state = 5;
        break;
    case 5:
        /* T1 = X + T1 */
        sp_384_mont_add_12(ctx->t1, p->x, ctx->t1, p384_mod);
        ctx->state = 6;
        break;
    case 6:
        /* T2 = T1 * T2 */
        sp_384_mont_mul_12(ctx->t2, ctx->t1, ctx->t2, p384_mod, p384_mp_mod);
        ctx->state = 7;
        break;
    case 7:
        /* T1 = 3T2 */
        sp_384_mont_tpl_12(ctx->t1, ctx->t2, p384_mod);
        ctx->state = 8;
        break;
    case 8:
        /* Y = 2Y */
        sp_384_mont_dbl_12(ctx->y, p->y, p384_mod);
        ctx->state = 9;
        break;
    case 9:
        /* Y = Y * Y */
        sp_384_mont_sqr_12(ctx->y, ctx->y, p384_mod, p384_mp_mod);
        ctx->state = 10;
        break;
    case 10:
        /* T2 = Y * Y */
        sp_384_mont_sqr_12(ctx->t2, ctx->y, p384_mod, p384_mp_mod);
        ctx->state = 11;
        break;
    case 11:
        /* T2 = T2/2 */
        sp_384_div2_12(ctx->t2, ctx->t2, p384_mod);
        ctx->state = 12;
        break;
    case 12:
        /* Y = Y * X */
        sp_384_mont_mul_12(ctx->y, ctx->y, p->x, p384_mod, p384_mp_mod);
        ctx->state = 13;
        break;
    case 13:
        /* X = T1 * T1 */
        sp_384_mont_sqr_12(ctx->x, ctx->t1, p384_mod, p384_mp_mod);
        ctx->state = 14;
        break;
    case 14:
        /* X = X - Y */
        sp_384_mont_sub_12(ctx->x, ctx->x, ctx->y, p384_mod);
        ctx->state = 15;
        break;
    case 15:
        /* X = X - Y */
        sp_384_mont_sub_12(ctx->x, ctx->x, ctx->y, p384_mod);
        ctx->state = 16;
        break;
    case 16:
        /* Y = Y - X */
        sp_384_mont_sub_12(ctx->y, ctx->y, ctx->x, p384_mod);
        ctx->state = 17;
        break;
    case 17:
        /* Y = Y * T1 */
        sp_384_mont_mul_12(ctx->y, ctx->y, ctx->t1, p384_mod, p384_mp_mod);
        ctx->state = 18;
        break;
    case 18:
        /* Y = Y - T2 */
        sp_384_mont_sub_12(ctx->y, ctx->y, ctx->t2, p384_mod);
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

static void sp_384_proj_point_dbl_12(sp_point_384* r, const sp_point_384* p, sp_digit* t)
{
    sp_digit* t1 = t;
    sp_digit* t2 = t + 2*12;
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
    sp_384_mont_sqr_12(t1, p->z, p384_mod, p384_mp_mod);
    /* Z = Y * Z */
    sp_384_mont_mul_12(z, p->y, p->z, p384_mod, p384_mp_mod);
    /* Z = 2Z */
    sp_384_mont_dbl_12(z, z, p384_mod);
    /* T2 = X - T1 */
    sp_384_mont_sub_12(t2, p->x, t1, p384_mod);
    /* T1 = X + T1 */
    sp_384_mont_add_12(t1, p->x, t1, p384_mod);
    /* T2 = T1 * T2 */
    sp_384_mont_mul_12(t2, t1, t2, p384_mod, p384_mp_mod);
    /* T1 = 3T2 */
    sp_384_mont_tpl_12(t1, t2, p384_mod);
    /* Y = 2Y */
    sp_384_mont_dbl_12(y, p->y, p384_mod);
    /* Y = Y * Y */
    sp_384_mont_sqr_12(y, y, p384_mod, p384_mp_mod);
    /* T2 = Y * Y */
    sp_384_mont_sqr_12(t2, y, p384_mod, p384_mp_mod);
    /* T2 = T2/2 */
    sp_384_div2_12(t2, t2, p384_mod);
    /* Y = Y * X */
    sp_384_mont_mul_12(y, y, p->x, p384_mod, p384_mp_mod);
    /* X = T1 * T1 */
    sp_384_mont_sqr_12(x, t1, p384_mod, p384_mp_mod);
    /* X = X - Y */
    sp_384_mont_sub_12(x, x, y, p384_mod);
    /* X = X - Y */
    sp_384_mont_sub_12(x, x, y, p384_mod);
    /* Y = Y - X */
    sp_384_mont_sub_12(y, y, x, p384_mod);
    /* Y = Y * T1 */
    sp_384_mont_mul_12(y, y, t1, p384_mod, p384_mp_mod);
    /* Y = Y - T2 */
    sp_384_mont_sub_12(y, y, t2, p384_mod);
}

/* Compare two numbers to determine if they are equal.
 * Constant time implementation.
 *
 * a  First number to compare.
 * b  Second number to compare.
 * returns 1 when equal and 0 otherwise.
 */
static int sp_384_cmp_equal_12(const sp_digit* a, const sp_digit* b)
{
    return ((a[0] ^ b[0]) | (a[1] ^ b[1]) | (a[2] ^ b[2]) | (a[3] ^ b[3]) |
            (a[4] ^ b[4]) | (a[5] ^ b[5]) | (a[6] ^ b[6]) | (a[7] ^ b[7]) |
            (a[8] ^ b[8]) | (a[9] ^ b[9]) | (a[10] ^ b[10]) | (a[11] ^ b[11])) == 0;
}

/* Add two Montgomery form projective points.
 *
 * r  Result of addition.
 * p  First point to add.
 * q  Second point to add.
 * t  Temporary ordinate data.
 */

#ifdef WOLFSSL_SP_NONBLOCK
typedef struct sp_384_proj_point_add_12_ctx {
    int state;
    sp_384_proj_point_dbl_12_ctx dbl_ctx;
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
} sp_384_proj_point_add_12_ctx;

static int sp_384_proj_point_add_12_nb(sp_ecc_ctx_t* sp_ctx, sp_point_384* r, 
    const sp_point_384* p, const sp_point_384* q, sp_digit* t)
{
    int err = FP_WOULDBLOCK;
    sp_384_proj_point_add_12_ctx* ctx = (sp_384_proj_point_add_12_ctx*)sp_ctx->data;

    /* Ensure only the first point is the same as the result. */
    if (q == r) {
        const sp_point_384* a = p;
        p = q;
        q = a;
    }

    typedef char ctx_size_test[sizeof(sp_384_proj_point_add_12_ctx) >= sizeof(*sp_ctx) ? -1 : 1];
    (void)sizeof(ctx_size_test);

    switch (ctx->state) {
    case 0: /* INIT */
        ctx->t1 = t;
        ctx->t2 = t + 2*12;
        ctx->t3 = t + 4*12;
        ctx->t4 = t + 6*12;
        ctx->t5 = t + 8*12;

        ctx->state = 1;
        break;
    case 1:
        /* Check double */
        (void)sp_384_sub_12(ctx->t1, p384_mod, q->y);
        sp_384_norm_12(ctx->t1);
        if ((sp_384_cmp_equal_12(p->x, q->x) & sp_384_cmp_equal_12(p->z, q->z) &
            (sp_384_cmp_equal_12(p->y, q->y) | sp_384_cmp_equal_12(p->y, ctx->t1))) != 0)
        {
            XMEMSET(&ctx->dbl_ctx, 0, sizeof(ctx->dbl_ctx));
            ctx->state = 2;
        }
        else {
            ctx->state = 3;
        }
        break;
    case 2:
        err = sp_384_proj_point_dbl_12_nb((sp_ecc_ctx_t*)&ctx->dbl_ctx, r, p, t);
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
        for (i=0; i<12; i++) {
            r->x[i] = ctx->ap[p->infinity]->x[i];
        }
        for (i=0; i<12; i++) {
            r->y[i] = ctx->ap[p->infinity]->y[i];
        }
        for (i=0; i<12; i++) {
            r->z[i] = ctx->ap[p->infinity]->z[i];
        }
        r->infinity = ctx->ap[p->infinity]->infinity;

        ctx->state = 4;
        break;
    }
    case 4:
        /* U1 = X1*Z2^2 */
        sp_384_mont_sqr_12(ctx->t1, q->z, p384_mod, p384_mp_mod);
        ctx->state = 5;
        break;
    case 5:
        sp_384_mont_mul_12(ctx->t3, ctx->t1, q->z, p384_mod, p384_mp_mod);
        ctx->state = 6;
        break;
    case 6:
        sp_384_mont_mul_12(ctx->t1, ctx->t1, ctx->x, p384_mod, p384_mp_mod);
        ctx->state = 7;
        break;
    case 7:
        /* U2 = X2*Z1^2 */
        sp_384_mont_sqr_12(ctx->t2, ctx->z, p384_mod, p384_mp_mod);
        ctx->state = 8;
        break;
    case 8:
        sp_384_mont_mul_12(ctx->t4, ctx->t2, ctx->z, p384_mod, p384_mp_mod);
        ctx->state = 9;
        break;
    case 9:
        sp_384_mont_mul_12(ctx->t2, ctx->t2, q->x, p384_mod, p384_mp_mod);
        ctx->state = 10;
        break;
    case 10:
        /* S1 = Y1*Z2^3 */
        sp_384_mont_mul_12(ctx->t3, ctx->t3, ctx->y, p384_mod, p384_mp_mod);
        ctx->state = 11;
        break;
    case 11:
        /* S2 = Y2*Z1^3 */
        sp_384_mont_mul_12(ctx->t4, ctx->t4, q->y, p384_mod, p384_mp_mod);
        ctx->state = 12;
        break;
    case 12:
        /* H = U2 - U1 */
        sp_384_mont_sub_12(ctx->t2, ctx->t2, ctx->t1, p384_mod);
        ctx->state = 13;
        break;
    case 13:
        /* R = S2 - S1 */
        sp_384_mont_sub_12(ctx->t4, ctx->t4, ctx->t3, p384_mod);
        ctx->state = 14;
        break;
    case 14:
        /* Z3 = H*Z1*Z2 */
        sp_384_mont_mul_12(ctx->z, ctx->z, q->z, p384_mod, p384_mp_mod);
        ctx->state = 15;
        break;
    case 15:
        sp_384_mont_mul_12(ctx->z, ctx->z, ctx->t2, p384_mod, p384_mp_mod);
        ctx->state = 16;
        break;
    case 16:
        /* X3 = R^2 - H^3 - 2*U1*H^2 */
        sp_384_mont_sqr_12(ctx->x, ctx->t4, p384_mod, p384_mp_mod);
        ctx->state = 17;
        break;
    case 17:
        sp_384_mont_sqr_12(ctx->t5, ctx->t2, p384_mod, p384_mp_mod);
        ctx->state = 18;
        break;
    case 18:
        sp_384_mont_mul_12(ctx->y, ctx->t1, ctx->t5, p384_mod, p384_mp_mod);
        ctx->state = 19;
        break;
    case 19:
        sp_384_mont_mul_12(ctx->t5, ctx->t5, ctx->t2, p384_mod, p384_mp_mod);
        ctx->state = 20;
        break;
    case 20:
        sp_384_mont_sub_12(ctx->x, ctx->x, ctx->t5, p384_mod);
        ctx->state = 21;
        break;
    case 21:
        sp_384_mont_dbl_12(ctx->t1, ctx->y, p384_mod);
        ctx->state = 22;
        break;
    case 22:
        sp_384_mont_sub_12(ctx->x, ctx->x, ctx->t1, p384_mod);
        ctx->state = 23;
        break;
    case 23:
        /* Y3 = R*(U1*H^2 - X3) - S1*H^3 */
        sp_384_mont_sub_12(ctx->y, ctx->y, ctx->x, p384_mod);
        ctx->state = 24;
        break;
    case 24:
        sp_384_mont_mul_12(ctx->y, ctx->y, ctx->t4, p384_mod, p384_mp_mod);
        ctx->state = 25;
        break;
    case 25:
        sp_384_mont_mul_12(ctx->t5, ctx->t5, ctx->t3, p384_mod, p384_mp_mod);
        ctx->state = 26;
        break;
    case 26:
        sp_384_mont_sub_12(ctx->y, ctx->y, ctx->t5, p384_mod);
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

static void sp_384_proj_point_add_12(sp_point_384* r, const sp_point_384* p, const sp_point_384* q,
        sp_digit* t)
{
    const sp_point_384* ap[2];
    sp_point_384* rp[2];
    sp_digit* t1 = t;
    sp_digit* t2 = t + 2*12;
    sp_digit* t3 = t + 4*12;
    sp_digit* t4 = t + 6*12;
    sp_digit* t5 = t + 8*12;
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
    (void)sp_384_sub_12(t1, p384_mod, q->y);
    sp_384_norm_12(t1);
    if ((sp_384_cmp_equal_12(p->x, q->x) & sp_384_cmp_equal_12(p->z, q->z) &
        (sp_384_cmp_equal_12(p->y, q->y) | sp_384_cmp_equal_12(p->y, t1))) != 0) {
        sp_384_proj_point_dbl_12(r, p, t);
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
        for (i=0; i<12; i++) {
            r->x[i] = ap[p->infinity]->x[i];
        }
        for (i=0; i<12; i++) {
            r->y[i] = ap[p->infinity]->y[i];
        }
        for (i=0; i<12; i++) {
            r->z[i] = ap[p->infinity]->z[i];
        }
        r->infinity = ap[p->infinity]->infinity;

        /* U1 = X1*Z2^2 */
        sp_384_mont_sqr_12(t1, q->z, p384_mod, p384_mp_mod);
        sp_384_mont_mul_12(t3, t1, q->z, p384_mod, p384_mp_mod);
        sp_384_mont_mul_12(t1, t1, x, p384_mod, p384_mp_mod);
        /* U2 = X2*Z1^2 */
        sp_384_mont_sqr_12(t2, z, p384_mod, p384_mp_mod);
        sp_384_mont_mul_12(t4, t2, z, p384_mod, p384_mp_mod);
        sp_384_mont_mul_12(t2, t2, q->x, p384_mod, p384_mp_mod);
        /* S1 = Y1*Z2^3 */
        sp_384_mont_mul_12(t3, t3, y, p384_mod, p384_mp_mod);
        /* S2 = Y2*Z1^3 */
        sp_384_mont_mul_12(t4, t4, q->y, p384_mod, p384_mp_mod);
        /* H = U2 - U1 */
        sp_384_mont_sub_12(t2, t2, t1, p384_mod);
        /* R = S2 - S1 */
        sp_384_mont_sub_12(t4, t4, t3, p384_mod);
        /* Z3 = H*Z1*Z2 */
        sp_384_mont_mul_12(z, z, q->z, p384_mod, p384_mp_mod);
        sp_384_mont_mul_12(z, z, t2, p384_mod, p384_mp_mod);
        /* X3 = R^2 - H^3 - 2*U1*H^2 */
        sp_384_mont_sqr_12(x, t4, p384_mod, p384_mp_mod);
        sp_384_mont_sqr_12(t5, t2, p384_mod, p384_mp_mod);
        sp_384_mont_mul_12(y, t1, t5, p384_mod, p384_mp_mod);
        sp_384_mont_mul_12(t5, t5, t2, p384_mod, p384_mp_mod);
        sp_384_mont_sub_12(x, x, t5, p384_mod);
        sp_384_mont_dbl_12(t1, y, p384_mod);
        sp_384_mont_sub_12(x, x, t1, p384_mod);
        /* Y3 = R*(U1*H^2 - X3) - S1*H^3 */
        sp_384_mont_sub_12(y, y, x, p384_mod);
        sp_384_mont_mul_12(y, y, t4, p384_mod, p384_mp_mod);
        sp_384_mont_mul_12(t5, t5, t3, p384_mod, p384_mp_mod);
        sp_384_mont_sub_12(y, y, t5, p384_mod);
    }
}

#ifndef WC_NO_CACHE_RESISTANT
/* Touch each possible point that could be being copied.
 *
 * r      Point to copy into.
 * table  Table - start of the entires to access
 * idx    Index of entry to retrieve.
 */
static void sp_384_get_point_16_12(sp_point_384* r, const sp_point_384* table,
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
    r->x[7] = 0;
    r->x[8] = 0;
    r->x[9] = 0;
    r->x[10] = 0;
    r->x[11] = 0;
    r->y[0] = 0;
    r->y[1] = 0;
    r->y[2] = 0;
    r->y[3] = 0;
    r->y[4] = 0;
    r->y[5] = 0;
    r->y[6] = 0;
    r->y[7] = 0;
    r->y[8] = 0;
    r->y[9] = 0;
    r->y[10] = 0;
    r->y[11] = 0;
    r->z[0] = 0;
    r->z[1] = 0;
    r->z[2] = 0;
    r->z[3] = 0;
    r->z[4] = 0;
    r->z[5] = 0;
    r->z[6] = 0;
    r->z[7] = 0;
    r->z[8] = 0;
    r->z[9] = 0;
    r->z[10] = 0;
    r->z[11] = 0;
    for (i = 1; i < 16; i++) {
        mask = 0 - (i == idx);
        r->x[0] |= mask & table[i].x[0];
        r->x[1] |= mask & table[i].x[1];
        r->x[2] |= mask & table[i].x[2];
        r->x[3] |= mask & table[i].x[3];
        r->x[4] |= mask & table[i].x[4];
        r->x[5] |= mask & table[i].x[5];
        r->x[6] |= mask & table[i].x[6];
        r->x[7] |= mask & table[i].x[7];
        r->x[8] |= mask & table[i].x[8];
        r->x[9] |= mask & table[i].x[9];
        r->x[10] |= mask & table[i].x[10];
        r->x[11] |= mask & table[i].x[11];
        r->y[0] |= mask & table[i].y[0];
        r->y[1] |= mask & table[i].y[1];
        r->y[2] |= mask & table[i].y[2];
        r->y[3] |= mask & table[i].y[3];
        r->y[4] |= mask & table[i].y[4];
        r->y[5] |= mask & table[i].y[5];
        r->y[6] |= mask & table[i].y[6];
        r->y[7] |= mask & table[i].y[7];
        r->y[8] |= mask & table[i].y[8];
        r->y[9] |= mask & table[i].y[9];
        r->y[10] |= mask & table[i].y[10];
        r->y[11] |= mask & table[i].y[11];
        r->z[0] |= mask & table[i].z[0];
        r->z[1] |= mask & table[i].z[1];
        r->z[2] |= mask & table[i].z[2];
        r->z[3] |= mask & table[i].z[3];
        r->z[4] |= mask & table[i].z[4];
        r->z[5] |= mask & table[i].z[5];
        r->z[6] |= mask & table[i].z[6];
        r->z[7] |= mask & table[i].z[7];
        r->z[8] |= mask & table[i].z[8];
        r->z[9] |= mask & table[i].z[9];
        r->z[10] |= mask & table[i].z[10];
        r->z[11] |= mask & table[i].z[11];
    }
}
#endif /* !WC_NO_CACHE_RESISTANT */
/* Multiply the point by the scalar and return the result.
 * If map is true then convert result to affine coordinates.
 *
 * Simple, smaller code size and memory size, of windowing.
 * Calculate uindow of 4 bits.
 * Only add points from table.
 *
 * r     Resulting point.
 * g     Point to multiply.
 * k     Scalar to multiply by.
 * map   Indicates whether to convert result to affine.
 * ct    Constant time required.
 * heap  Heap to use for allocation.
 * returns MEMORY_E when memory allocation fails and MP_OKAY on success.
 */
static int sp_384_ecc_mulmod_fast_12(sp_point_384* r, const sp_point_384* g, const sp_digit* k,
        int map, int ct, void* heap)
{
#if (!defined(WOLFSSL_SP_SMALL) && !defined(WOLFSSL_SMALL_STACK)) || defined(WOLFSSL_SP_NO_MALLOC)
    sp_point_384 td[16];
    sp_point_384 rtd;
    sp_digit tmpd[2 * 12 * 6];
#ifndef WC_NO_CACHE_RESISTANT
    sp_point_384 pd;
#endif
#endif
    sp_point_384* t;
    sp_point_384* rt;
#ifndef WC_NO_CACHE_RESISTANT
    sp_point_384* p;
#endif
    sp_digit* tmp;
    sp_digit n;
    int i;
    int c, y;
    int err;

    /* Constant time used for cache attack resistance implementation. */
    (void)ct;
    (void)heap;

    err = sp_384_point_new_12(heap, rtd, rt);
#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
#ifndef WC_NO_CACHE_RESISTANT
    t = (sp_point_384*)XMALLOC(sizeof(sp_point_384) * 17, heap, DYNAMIC_TYPE_ECC);
#else
    t = (sp_point_384*)XMALLOC(sizeof(sp_point_384) * 16, heap, DYNAMIC_TYPE_ECC);
#endif
    if (t == NULL)
        err = MEMORY_E;
    tmp = (sp_digit*)XMALLOC(sizeof(sp_digit) * 2 * 12 * 6, heap,
                             DYNAMIC_TYPE_ECC);
    if (tmp == NULL)
        err = MEMORY_E;
#else
    t = td;
    tmp = tmpd;
#endif

    if (err == MP_OKAY) {
#ifndef WC_NO_CACHE_RESISTANT
    #if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
        p = t + 16;
    #else
        p = &pd;
    #endif
#endif
        /* t[0] = {0, 0, 1} * norm */
        XMEMSET(&t[0], 0, sizeof(t[0]));
        t[0].infinity = 1;
        /* t[1] = {g->x, g->y, g->z} * norm */
        (void)sp_384_mod_mul_norm_12(t[1].x, g->x, p384_mod);
        (void)sp_384_mod_mul_norm_12(t[1].y, g->y, p384_mod);
        (void)sp_384_mod_mul_norm_12(t[1].z, g->z, p384_mod);
        t[1].infinity = 0;
        sp_384_proj_point_dbl_12(&t[ 2], &t[ 1], tmp);
        t[ 2].infinity = 0;
        sp_384_proj_point_add_12(&t[ 3], &t[ 2], &t[ 1], tmp);
        t[ 3].infinity = 0;
        sp_384_proj_point_dbl_12(&t[ 4], &t[ 2], tmp);
        t[ 4].infinity = 0;
        sp_384_proj_point_add_12(&t[ 5], &t[ 3], &t[ 2], tmp);
        t[ 5].infinity = 0;
        sp_384_proj_point_dbl_12(&t[ 6], &t[ 3], tmp);
        t[ 6].infinity = 0;
        sp_384_proj_point_add_12(&t[ 7], &t[ 4], &t[ 3], tmp);
        t[ 7].infinity = 0;
        sp_384_proj_point_dbl_12(&t[ 8], &t[ 4], tmp);
        t[ 8].infinity = 0;
        sp_384_proj_point_add_12(&t[ 9], &t[ 5], &t[ 4], tmp);
        t[ 9].infinity = 0;
        sp_384_proj_point_dbl_12(&t[10], &t[ 5], tmp);
        t[10].infinity = 0;
        sp_384_proj_point_add_12(&t[11], &t[ 6], &t[ 5], tmp);
        t[11].infinity = 0;
        sp_384_proj_point_dbl_12(&t[12], &t[ 6], tmp);
        t[12].infinity = 0;
        sp_384_proj_point_add_12(&t[13], &t[ 7], &t[ 6], tmp);
        t[13].infinity = 0;
        sp_384_proj_point_dbl_12(&t[14], &t[ 7], tmp);
        t[14].infinity = 0;
        sp_384_proj_point_add_12(&t[15], &t[ 8], &t[ 7], tmp);
        t[15].infinity = 0;

        i = 10;
        n = k[i+1] << 0;
        c = 28;
        y = n >> 28;
    #ifndef WC_NO_CACHE_RESISTANT
        if (ct) {
            sp_384_get_point_16_12(rt, t, y);
            rt->infinity = !y;
        }
        else
    #endif
        {
            XMEMCPY(rt, &t[y], sizeof(sp_point_384));
        }
        n <<= 4;
        for (; i>=0 || c>=4; ) {
            if (c < 4) {
                n |= k[i--];
                c += 32;
            }
            y = (n >> 28) & 0xf;
            n <<= 4;
            c -= 4;

            sp_384_proj_point_dbl_12(rt, rt, tmp);
            sp_384_proj_point_dbl_12(rt, rt, tmp);
            sp_384_proj_point_dbl_12(rt, rt, tmp);
            sp_384_proj_point_dbl_12(rt, rt, tmp);

    #ifndef WC_NO_CACHE_RESISTANT
            if (ct) {
                sp_384_get_point_16_12(p, t, y);
                p->infinity = !y;
                sp_384_proj_point_add_12(rt, rt, p, tmp);
            }
            else
    #endif
            {
                sp_384_proj_point_add_12(rt, rt, &t[y], tmp);
            }
        }

        if (map != 0) {
            sp_384_map_12(r, rt, tmp);
        }
        else {
            XMEMCPY(r, rt, sizeof(sp_point_384));
        }
    }

#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (tmp != NULL) {
        XMEMSET(tmp, 0, sizeof(sp_digit) * 2 * 12 * 6);
        XFREE(tmp, heap, DYNAMIC_TYPE_ECC);
    }
    if (t != NULL) {
        XMEMSET(t, 0, sizeof(sp_point_384) * 16);
        XFREE(t, heap, DYNAMIC_TYPE_ECC);
    }
#else
    ForceZero(tmpd, sizeof(tmpd));
    ForceZero(td, sizeof(td));
#endif
    sp_384_point_free_12(rt, 1, heap);

    return err;
}

/* A table entry for pre-computed points. */
typedef struct sp_table_entry_384 {
    sp_digit x[12];
    sp_digit y[12];
} sp_table_entry_384;

#ifdef FP_ECC
/* Double the Montgomery form projective point p a number of times.
 *
 * r  Result of repeated doubling of point.
 * p  Point to double.
 * n  Number of times to double
 * t  Temporary ordinate data.
 */
static void sp_384_proj_point_dbl_n_12(sp_point_384* p, int n, sp_digit* t)
{
    sp_digit* w = t;
    sp_digit* a = t + 2*12;
    sp_digit* b = t + 4*12;
    sp_digit* t1 = t + 6*12;
    sp_digit* t2 = t + 8*12;
    sp_digit* x;
    sp_digit* y;
    sp_digit* z;

    x = p->x;
    y = p->y;
    z = p->z;

    /* Y = 2*Y */
    sp_384_mont_dbl_12(y, y, p384_mod);
    /* W = Z^4 */
    sp_384_mont_sqr_12(w, z, p384_mod, p384_mp_mod);
    sp_384_mont_sqr_12(w, w, p384_mod, p384_mp_mod);

#ifndef WOLFSSL_SP_SMALL
    while (--n > 0)
#else
    while (--n >= 0)
#endif
    {
        /* A = 3*(X^2 - W) */
        sp_384_mont_sqr_12(t1, x, p384_mod, p384_mp_mod);
        sp_384_mont_sub_12(t1, t1, w, p384_mod);
        sp_384_mont_tpl_12(a, t1, p384_mod);
        /* B = X*Y^2 */
        sp_384_mont_sqr_12(t1, y, p384_mod, p384_mp_mod);
        sp_384_mont_mul_12(b, t1, x, p384_mod, p384_mp_mod);
        /* X = A^2 - 2B */
        sp_384_mont_sqr_12(x, a, p384_mod, p384_mp_mod);
        sp_384_mont_dbl_12(t2, b, p384_mod);
        sp_384_mont_sub_12(x, x, t2, p384_mod);
        /* Z = Z*Y */
        sp_384_mont_mul_12(z, z, y, p384_mod, p384_mp_mod);
        /* t2 = Y^4 */
        sp_384_mont_sqr_12(t1, t1, p384_mod, p384_mp_mod);
#ifdef WOLFSSL_SP_SMALL
        if (n != 0)
#endif
        {
            /* W = W*Y^4 */
            sp_384_mont_mul_12(w, w, t1, p384_mod, p384_mp_mod);
        }
        /* y = 2*A*(B - X) - Y^4 */
        sp_384_mont_sub_12(y, b, x, p384_mod);
        sp_384_mont_mul_12(y, y, a, p384_mod, p384_mp_mod);
        sp_384_mont_dbl_12(y, y, p384_mod);
        sp_384_mont_sub_12(y, y, t1, p384_mod);
    }
#ifndef WOLFSSL_SP_SMALL
    /* A = 3*(X^2 - W) */
    sp_384_mont_sqr_12(t1, x, p384_mod, p384_mp_mod);
    sp_384_mont_sub_12(t1, t1, w, p384_mod);
    sp_384_mont_tpl_12(a, t1, p384_mod);
    /* B = X*Y^2 */
    sp_384_mont_sqr_12(t1, y, p384_mod, p384_mp_mod);
    sp_384_mont_mul_12(b, t1, x, p384_mod, p384_mp_mod);
    /* X = A^2 - 2B */
    sp_384_mont_sqr_12(x, a, p384_mod, p384_mp_mod);
    sp_384_mont_dbl_12(t2, b, p384_mod);
    sp_384_mont_sub_12(x, x, t2, p384_mod);
    /* Z = Z*Y */
    sp_384_mont_mul_12(z, z, y, p384_mod, p384_mp_mod);
    /* t2 = Y^4 */
    sp_384_mont_sqr_12(t1, t1, p384_mod, p384_mp_mod);
    /* y = 2*A*(B - X) - Y^4 */
    sp_384_mont_sub_12(y, b, x, p384_mod);
    sp_384_mont_mul_12(y, y, a, p384_mod, p384_mp_mod);
    sp_384_mont_dbl_12(y, y, p384_mod);
    sp_384_mont_sub_12(y, y, t1, p384_mod);
#endif
    /* Y = Y/2 */
    sp_384_div2_12(y, y, p384_mod);
}

/* Convert the projective point to affine.
 * Ordinates are in Montgomery form.
 *
 * a  Point to convert.
 * t  Temporary data.
 */
static void sp_384_proj_to_affine_12(sp_point_384* a, sp_digit* t)
{
    sp_digit* t1 = t;
    sp_digit* t2 = t + 2 * 12;
    sp_digit* tmp = t + 4 * 12;

    sp_384_mont_inv_12(t1, a->z, tmp);

    sp_384_mont_sqr_12(t2, t1, p384_mod, p384_mp_mod);
    sp_384_mont_mul_12(t1, t2, t1, p384_mod, p384_mp_mod);

    sp_384_mont_mul_12(a->x, a->x, t2, p384_mod, p384_mp_mod);
    sp_384_mont_mul_12(a->y, a->y, t1, p384_mod, p384_mp_mod);
    XMEMCPY(a->z, p384_norm_mod, sizeof(p384_norm_mod));
}

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
static void sp_384_proj_point_add_qz1_12(sp_point_384* r, const sp_point_384* p,
        const sp_point_384* q, sp_digit* t)
{
    const sp_point_384* ap[2];
    sp_point_384* rp[2];
    sp_digit* t1 = t;
    sp_digit* t2 = t + 2*12;
    sp_digit* t3 = t + 4*12;
    sp_digit* t4 = t + 6*12;
    sp_digit* t5 = t + 8*12;
    sp_digit* x;
    sp_digit* y;
    sp_digit* z;
    int i;

    /* Check double */
    (void)sp_384_sub_12(t1, p384_mod, q->y);
    sp_384_norm_12(t1);
    if ((sp_384_cmp_equal_12(p->x, q->x) & sp_384_cmp_equal_12(p->z, q->z) &
        (sp_384_cmp_equal_12(p->y, q->y) | sp_384_cmp_equal_12(p->y, t1))) != 0) {
        sp_384_proj_point_dbl_12(r, p, t);
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
        for (i=0; i<12; i++) {
            r->x[i] = ap[p->infinity]->x[i];
        }
        for (i=0; i<12; i++) {
            r->y[i] = ap[p->infinity]->y[i];
        }
        for (i=0; i<12; i++) {
            r->z[i] = ap[p->infinity]->z[i];
        }
        r->infinity = ap[p->infinity]->infinity;

        /* U2 = X2*Z1^2 */
        sp_384_mont_sqr_12(t2, z, p384_mod, p384_mp_mod);
        sp_384_mont_mul_12(t4, t2, z, p384_mod, p384_mp_mod);
        sp_384_mont_mul_12(t2, t2, q->x, p384_mod, p384_mp_mod);
        /* S2 = Y2*Z1^3 */
        sp_384_mont_mul_12(t4, t4, q->y, p384_mod, p384_mp_mod);
        /* H = U2 - X1 */
        sp_384_mont_sub_12(t2, t2, x, p384_mod);
        /* R = S2 - Y1 */
        sp_384_mont_sub_12(t4, t4, y, p384_mod);
        /* Z3 = H*Z1 */
        sp_384_mont_mul_12(z, z, t2, p384_mod, p384_mp_mod);
        /* X3 = R^2 - H^3 - 2*X1*H^2 */
        sp_384_mont_sqr_12(t1, t4, p384_mod, p384_mp_mod);
        sp_384_mont_sqr_12(t5, t2, p384_mod, p384_mp_mod);
        sp_384_mont_mul_12(t3, x, t5, p384_mod, p384_mp_mod);
        sp_384_mont_mul_12(t5, t5, t2, p384_mod, p384_mp_mod);
        sp_384_mont_sub_12(x, t1, t5, p384_mod);
        sp_384_mont_dbl_12(t1, t3, p384_mod);
        sp_384_mont_sub_12(x, x, t1, p384_mod);
        /* Y3 = R*(X1*H^2 - X3) - Y1*H^3 */
        sp_384_mont_sub_12(t3, t3, x, p384_mod);
        sp_384_mont_mul_12(t3, t3, t4, p384_mod, p384_mp_mod);
        sp_384_mont_mul_12(t5, t5, y, p384_mod, p384_mp_mod);
        sp_384_mont_sub_12(y, t3, t5, p384_mod);
    }
}

#ifdef WOLFSSL_SP_SMALL
#ifdef FP_ECC
/* Generate the pre-computed table of points for the base point.
 *
 * a      The base point.
 * table  Place to store generated point data.
 * tmp    Temporary data.
 * heap  Heap to use for allocation.
 */
static int sp_384_gen_stripe_table_12(const sp_point_384* a,
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

    err = sp_384_point_new_12(heap, td, t);
    if (err == MP_OKAY) {
        err = sp_384_point_new_12(heap, s1d, s1);
    }
    if (err == MP_OKAY) {
        err = sp_384_point_new_12(heap, s2d, s2);
    }

    if (err == MP_OKAY) {
        err = sp_384_mod_mul_norm_12(t->x, a->x, p384_mod);
    }
    if (err == MP_OKAY) {
        err = sp_384_mod_mul_norm_12(t->y, a->y, p384_mod);
    }
    if (err == MP_OKAY) {
        err = sp_384_mod_mul_norm_12(t->z, a->z, p384_mod);
    }
    if (err == MP_OKAY) {
        t->infinity = 0;
        sp_384_proj_to_affine_12(t, tmp);

        XMEMCPY(s1->z, p384_norm_mod, sizeof(p384_norm_mod));
        s1->infinity = 0;
        XMEMCPY(s2->z, p384_norm_mod, sizeof(p384_norm_mod));
        s2->infinity = 0;

        /* table[0] = {0, 0, infinity} */
        XMEMSET(&table[0], 0, sizeof(sp_table_entry_384));
        /* table[1] = Affine version of 'a' in Montgomery form */
        XMEMCPY(table[1].x, t->x, sizeof(table->x));
        XMEMCPY(table[1].y, t->y, sizeof(table->y));

        for (i=1; i<4; i++) {
            sp_384_proj_point_dbl_n_12(t, 96, tmp);
            sp_384_proj_to_affine_12(t, tmp);
            XMEMCPY(table[1<<i].x, t->x, sizeof(table->x));
            XMEMCPY(table[1<<i].y, t->y, sizeof(table->y));
        }

        for (i=1; i<4; i++) {
            XMEMCPY(s1->x, table[1<<i].x, sizeof(table->x));
            XMEMCPY(s1->y, table[1<<i].y, sizeof(table->y));
            for (j=(1<<i)+1; j<(1<<(i+1)); j++) {
                XMEMCPY(s2->x, table[j-(1<<i)].x, sizeof(table->x));
                XMEMCPY(s2->y, table[j-(1<<i)].y, sizeof(table->y));
                sp_384_proj_point_add_qz1_12(t, s1, s2, tmp);
                sp_384_proj_to_affine_12(t, tmp);
                XMEMCPY(table[j].x, t->x, sizeof(table->x));
                XMEMCPY(table[j].y, t->y, sizeof(table->y));
            }
        }
    }

    sp_384_point_free_12(s2, 0, heap);
    sp_384_point_free_12(s1, 0, heap);
    sp_384_point_free_12( t, 0, heap);

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
static void sp_384_get_entry_16_12(sp_point_384* r,
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
    r->x[7] = 0;
    r->x[8] = 0;
    r->x[9] = 0;
    r->x[10] = 0;
    r->x[11] = 0;
    r->y[0] = 0;
    r->y[1] = 0;
    r->y[2] = 0;
    r->y[3] = 0;
    r->y[4] = 0;
    r->y[5] = 0;
    r->y[6] = 0;
    r->y[7] = 0;
    r->y[8] = 0;
    r->y[9] = 0;
    r->y[10] = 0;
    r->y[11] = 0;
    for (i = 1; i < 16; i++) {
        mask = 0 - (i == idx);
        r->x[0] |= mask & table[i].x[0];
        r->x[1] |= mask & table[i].x[1];
        r->x[2] |= mask & table[i].x[2];
        r->x[3] |= mask & table[i].x[3];
        r->x[4] |= mask & table[i].x[4];
        r->x[5] |= mask & table[i].x[5];
        r->x[6] |= mask & table[i].x[6];
        r->x[7] |= mask & table[i].x[7];
        r->x[8] |= mask & table[i].x[8];
        r->x[9] |= mask & table[i].x[9];
        r->x[10] |= mask & table[i].x[10];
        r->x[11] |= mask & table[i].x[11];
        r->y[0] |= mask & table[i].y[0];
        r->y[1] |= mask & table[i].y[1];
        r->y[2] |= mask & table[i].y[2];
        r->y[3] |= mask & table[i].y[3];
        r->y[4] |= mask & table[i].y[4];
        r->y[5] |= mask & table[i].y[5];
        r->y[6] |= mask & table[i].y[6];
        r->y[7] |= mask & table[i].y[7];
        r->y[8] |= mask & table[i].y[8];
        r->y[9] |= mask & table[i].y[9];
        r->y[10] |= mask & table[i].y[10];
        r->y[11] |= mask & table[i].y[11];
    }
}
#endif /* !WC_NO_CACHE_RESISTANT */
/* Multiply the point by the scalar and return the result.
 * If map is true then convert result to affine coordinates.
 *
 * Implementation uses striping of bits.
 * Choose bits 4 bits apart.
 *
 * r      Resulting point.
 * k      Scalar to multiply by.
 * table  Pre-computed table.
 * map    Indicates whether to convert result to affine.
 * ct     Constant time required.
 * heap   Heap to use for allocation.
 * returns MEMORY_E when memory allocation fails and MP_OKAY on success.
 */
static int sp_384_ecc_mulmod_stripe_12(sp_point_384* r, const sp_point_384* g,
        const sp_table_entry_384* table, const sp_digit* k, int map,
        int ct, void* heap)
{
#if (!defined(WOLFSSL_SP_SMALL) && !defined(WOLFSSL_SMALL_STACK)) || defined(WOLFSSL_SP_NO_MALLOC)
    sp_point_384 rtd;
    sp_point_384 pd;
    sp_digit td[2 * 12 * 6];
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


    err = sp_384_point_new_12(heap, rtd, rt);
    if (err == MP_OKAY) {
        err = sp_384_point_new_12(heap, pd, p);
    }
#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    t = (sp_digit*)XMALLOC(sizeof(sp_digit) * 2 * 12 * 6, heap,
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
        for (j=0,x=95; j<4; j++,x+=96) {
            y |= ((k[x / 32] >> (x % 32)) & 1) << j;
        }
    #ifndef WC_NO_CACHE_RESISTANT
        if (ct) {
            sp_384_get_entry_16_12(rt, table, y);
        } else
    #endif
        {
            XMEMCPY(rt->x, table[y].x, sizeof(table[y].x));
            XMEMCPY(rt->y, table[y].y, sizeof(table[y].y));
        }
        rt->infinity = !y;
        for (i=94; i>=0; i--) {
            y = 0;
            for (j=0,x=i; j<4; j++,x+=96) {
                y |= ((k[x / 32] >> (x % 32)) & 1) << j;
            }

            sp_384_proj_point_dbl_12(rt, rt, t);
        #ifndef WC_NO_CACHE_RESISTANT
            if (ct) {
                sp_384_get_entry_16_12(p, table, y);
            }
            else
        #endif
            {
                XMEMCPY(p->x, table[y].x, sizeof(table[y].x));
                XMEMCPY(p->y, table[y].y, sizeof(table[y].y));
            }
            p->infinity = !y;
            sp_384_proj_point_add_qz1_12(rt, rt, p, t);
        }

        if (map != 0) {
            sp_384_map_12(r, rt, t);
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
    sp_384_point_free_12(p, 0, heap);
    sp_384_point_free_12(rt, 0, heap);

    return err;
}

#ifdef FP_ECC
#ifndef FP_ENTRIES
    #define FP_ENTRIES 16
#endif

typedef struct sp_cache_384_t {
    sp_digit x[12];
    sp_digit y[12];
    sp_table_entry_384 table[16];
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

        if (sp_384_cmp_equal_12(g->x, sp_cache_384[i].x) &
                           sp_384_cmp_equal_12(g->y, sp_cache_384[i].y)) {
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
static int sp_384_ecc_mulmod_12(sp_point_384* r, const sp_point_384* g, const sp_digit* k,
        int map, int ct, void* heap)
{
#ifndef FP_ECC
    return sp_384_ecc_mulmod_fast_12(r, g, k, map, ct, heap);
#else
    sp_digit tmp[2 * 12 * 7];
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
            sp_384_gen_stripe_table_12(g, cache->table, tmp, heap);

#ifndef HAVE_THREAD_LS
        wc_UnLockMutex(&sp_cache_384_lock);
#endif /* HAVE_THREAD_LS */

        if (cache->cnt < 2) {
            err = sp_384_ecc_mulmod_fast_12(r, g, k, map, ct, heap);
        }
        else {
            err = sp_384_ecc_mulmod_stripe_12(r, g, cache->table, k,
                    map, ct, heap);
        }
    }

    return err;
#endif
}

#else
#ifdef FP_ECC
/* Generate the pre-computed table of points for the base point.
 *
 * a      The base point.
 * table  Place to store generated point data.
 * tmp    Temporary data.
 * heap  Heap to use for allocation.
 */
static int sp_384_gen_stripe_table_12(const sp_point_384* a,
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

    err = sp_384_point_new_12(heap, td, t);
    if (err == MP_OKAY) {
        err = sp_384_point_new_12(heap, s1d, s1);
    }
    if (err == MP_OKAY) {
        err = sp_384_point_new_12(heap, s2d, s2);
    }

    if (err == MP_OKAY) {
        err = sp_384_mod_mul_norm_12(t->x, a->x, p384_mod);
    }
    if (err == MP_OKAY) {
        err = sp_384_mod_mul_norm_12(t->y, a->y, p384_mod);
    }
    if (err == MP_OKAY) {
        err = sp_384_mod_mul_norm_12(t->z, a->z, p384_mod);
    }
    if (err == MP_OKAY) {
        t->infinity = 0;
        sp_384_proj_to_affine_12(t, tmp);

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
            sp_384_proj_point_dbl_n_12(t, 48, tmp);
            sp_384_proj_to_affine_12(t, tmp);
            XMEMCPY(table[1<<i].x, t->x, sizeof(table->x));
            XMEMCPY(table[1<<i].y, t->y, sizeof(table->y));
        }

        for (i=1; i<8; i++) {
            XMEMCPY(s1->x, table[1<<i].x, sizeof(table->x));
            XMEMCPY(s1->y, table[1<<i].y, sizeof(table->y));
            for (j=(1<<i)+1; j<(1<<(i+1)); j++) {
                XMEMCPY(s2->x, table[j-(1<<i)].x, sizeof(table->x));
                XMEMCPY(s2->y, table[j-(1<<i)].y, sizeof(table->y));
                sp_384_proj_point_add_qz1_12(t, s1, s2, tmp);
                sp_384_proj_to_affine_12(t, tmp);
                XMEMCPY(table[j].x, t->x, sizeof(table->x));
                XMEMCPY(table[j].y, t->y, sizeof(table->y));
            }
        }
    }

    sp_384_point_free_12(s2, 0, heap);
    sp_384_point_free_12(s1, 0, heap);
    sp_384_point_free_12( t, 0, heap);

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
static void sp_384_get_entry_256_12(sp_point_384* r,
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
    r->x[7] = 0;
    r->x[8] = 0;
    r->x[9] = 0;
    r->x[10] = 0;
    r->x[11] = 0;
    r->y[0] = 0;
    r->y[1] = 0;
    r->y[2] = 0;
    r->y[3] = 0;
    r->y[4] = 0;
    r->y[5] = 0;
    r->y[6] = 0;
    r->y[7] = 0;
    r->y[8] = 0;
    r->y[9] = 0;
    r->y[10] = 0;
    r->y[11] = 0;
    for (i = 1; i < 256; i++) {
        mask = 0 - (i == idx);
        r->x[0] |= mask & table[i].x[0];
        r->x[1] |= mask & table[i].x[1];
        r->x[2] |= mask & table[i].x[2];
        r->x[3] |= mask & table[i].x[3];
        r->x[4] |= mask & table[i].x[4];
        r->x[5] |= mask & table[i].x[5];
        r->x[6] |= mask & table[i].x[6];
        r->x[7] |= mask & table[i].x[7];
        r->x[8] |= mask & table[i].x[8];
        r->x[9] |= mask & table[i].x[9];
        r->x[10] |= mask & table[i].x[10];
        r->x[11] |= mask & table[i].x[11];
        r->y[0] |= mask & table[i].y[0];
        r->y[1] |= mask & table[i].y[1];
        r->y[2] |= mask & table[i].y[2];
        r->y[3] |= mask & table[i].y[3];
        r->y[4] |= mask & table[i].y[4];
        r->y[5] |= mask & table[i].y[5];
        r->y[6] |= mask & table[i].y[6];
        r->y[7] |= mask & table[i].y[7];
        r->y[8] |= mask & table[i].y[8];
        r->y[9] |= mask & table[i].y[9];
        r->y[10] |= mask & table[i].y[10];
        r->y[11] |= mask & table[i].y[11];
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
static int sp_384_ecc_mulmod_stripe_12(sp_point_384* r, const sp_point_384* g,
        const sp_table_entry_384* table, const sp_digit* k, int map,
        int ct, void* heap)
{
#if (!defined(WOLFSSL_SP_SMALL) && !defined(WOLFSSL_SMALL_STACK)) || defined(WOLFSSL_SP_NO_MALLOC)
    sp_point_384 rtd;
    sp_point_384 pd;
    sp_digit td[2 * 12 * 6];
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


    err = sp_384_point_new_12(heap, rtd, rt);
    if (err == MP_OKAY) {
        err = sp_384_point_new_12(heap, pd, p);
    }
#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    t = (sp_digit*)XMALLOC(sizeof(sp_digit) * 2 * 12 * 6, heap,
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
            y |= ((k[x / 32] >> (x % 32)) & 1) << j;
        }
    #ifndef WC_NO_CACHE_RESISTANT
        if (ct) {
            sp_384_get_entry_256_12(rt, table, y);
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
                y |= ((k[x / 32] >> (x % 32)) & 1) << j;
            }

            sp_384_proj_point_dbl_12(rt, rt, t);
        #ifndef WC_NO_CACHE_RESISTANT
            if (ct) {
                sp_384_get_entry_256_12(p, table, y);
            }
            else
        #endif
            {
                XMEMCPY(p->x, table[y].x, sizeof(table[y].x));
                XMEMCPY(p->y, table[y].y, sizeof(table[y].y));
            }
            p->infinity = !y;
            sp_384_proj_point_add_qz1_12(rt, rt, p, t);
        }

        if (map != 0) {
            sp_384_map_12(r, rt, t);
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
    sp_384_point_free_12(p, 0, heap);
    sp_384_point_free_12(rt, 0, heap);

    return err;
}

#ifdef FP_ECC
#ifndef FP_ENTRIES
    #define FP_ENTRIES 16
#endif

typedef struct sp_cache_384_t {
    sp_digit x[12];
    sp_digit y[12];
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

        if (sp_384_cmp_equal_12(g->x, sp_cache_384[i].x) &
                           sp_384_cmp_equal_12(g->y, sp_cache_384[i].y)) {
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
static int sp_384_ecc_mulmod_12(sp_point_384* r, const sp_point_384* g, const sp_digit* k,
        int map, int ct, void* heap)
{
#ifndef FP_ECC
    return sp_384_ecc_mulmod_fast_12(r, g, k, map, ct, heap);
#else
    sp_digit tmp[2 * 12 * 7];
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
            sp_384_gen_stripe_table_12(g, cache->table, tmp, heap);

#ifndef HAVE_THREAD_LS
        wc_UnLockMutex(&sp_cache_384_lock);
#endif /* HAVE_THREAD_LS */

        if (cache->cnt < 2) {
            err = sp_384_ecc_mulmod_fast_12(r, g, k, map, ct, heap);
        }
        else {
            err = sp_384_ecc_mulmod_stripe_12(r, g, cache->table, k,
                    map, ct, heap);
        }
    }

    return err;
#endif
}

#endif /* WOLFSSL_SP_SMALL */
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
    sp_digit kd[12];
#endif
    sp_point_384* point;
    sp_digit* k = NULL;
    int err = MP_OKAY;

    err = sp_384_point_new_12(heap, p, point);
#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (err == MP_OKAY) {
        k = (sp_digit*)XMALLOC(sizeof(sp_digit) * 12, heap,
                                                              DYNAMIC_TYPE_ECC);
        if (k == NULL)
            err = MEMORY_E;
    }
#else
    k = kd;
#endif
    if (err == MP_OKAY) {
        sp_384_from_mp(k, 12, km);
        sp_384_point_from_ecc_point_12(point, gm);

            err = sp_384_ecc_mulmod_12(point, point, k, map, 1, heap);
    }
    if (err == MP_OKAY) {
        err = sp_384_point_to_ecc_point_12(point, r);
    }

#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (k != NULL) {
        XFREE(k, heap, DYNAMIC_TYPE_ECC);
    }
#endif
    sp_384_point_free_12(point, 0, heap);

    return err;
}

#ifdef WOLFSSL_SP_SMALL
static const sp_table_entry_384 p384_table[16] = {
    /* 0 */
    { { 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00 },
      { 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00 } },
    /* 1 */
    { { 0x49c0b528,0x3dd07566,0xa0d6ce38,0x20e378e2,0x541b4d6e,0x879c3afc,
        0x59a30eff,0x64548684,0x614ede2b,0x812ff723,0x299e1513,0x4d3aadc2 },
      { 0x4b03a4fe,0x23043dad,0x7bb4a9ac,0xa1bfa8bf,0x2e83b050,0x8bade756,
        0x68f4ffd9,0xc6c35219,0x3969a840,0xdd800226,0x5a15c5e9,0x2b78abc2 } },
    /* 2 */
    { { 0xf26feef9,0x24480c57,0x3a0e1240,0xc31a2694,0x273e2bc7,0x735002c3,
        0x3ef1ed4c,0x8c42e9c5,0x7f4948e8,0x028babf6,0x8a978632,0x6a502f43 },
      { 0xb74536fe,0xf5f13a46,0xd8a9f0eb,0x1d218bab,0x37232768,0x30f36bcc,
        0x576e8c18,0xc5317b31,0x9bbcb766,0xef1d57a6,0xb3e3d4dc,0x917c4930 } },
    /* 3 */
    { { 0xe349ddd0,0x11426e2e,0x9b2fc250,0x9f117ef9,0xec0174a6,0xff36b480,
        0x18458466,0x4f4bde76,0x05806049,0x2f2edb6d,0x19dfca92,0x8adc75d1 },
      { 0xb7d5a7ce,0xa619d097,0xa34411e9,0x874275e5,0x0da4b4ef,0x5403e047,
        0x77901d8f,0x2ebaafd9,0xa747170f,0x5e63ebce,0x7f9d8036,0x12a36944 } },
    /* 4 */
    { { 0x2f9fbe67,0x378205de,0x7f728e44,0xc4afcb83,0x682e00f1,0xdbcec06c,
        0x114d5423,0xf2a145c3,0x7a52463e,0xa01d9874,0x7d717b0a,0xfc0935b1 },
      { 0xd4d01f95,0x9653bc4f,0x9560ad34,0x9aa83ea8,0xaf8e3f3f,0xf77943dc,
        0xe86fe16e,0x70774a10,0xbf9ffdcf,0x6b62e6f1,0x588745c9,0x8a72f39e } },
    /* 5 */
    { { 0x2341c342,0x73ade4da,0xea704422,0xdd326e54,0x3741cef3,0x336c7d98,
        0x59e61549,0x1eafa00d,0xbd9a3efd,0xcd3ed892,0xc5c6c7e4,0x03faf26c },
      { 0x3045f8ac,0x087e2fcf,0x174f1e73,0x14a65532,0xfe0af9a7,0x2cf84f28,
        0x2cdc935b,0xddfd7a84,0x6929c895,0x4c0f117b,0x4c8bcfcc,0x356572d6 } },
    /* 6 */
    { { 0x3f3b236f,0xfab08607,0x81e221da,0x19e9d41d,0x3927b428,0xf3f6571e,
        0x7550f1f6,0x4348a933,0xa85e62f0,0x7167b996,0x7f5452bf,0x62d43759 },
      { 0xf2955926,0xd85feb9e,0x6df78353,0x440a561f,0x9ca36b59,0x389668ec,
        0xa22da016,0x052bf1a1,0xf6093254,0xbdfbff72,0xe22209f3,0x94e50f28 } },
    /* 7 */
    { { 0x3062e8af,0x90b2e5b3,0xe8a3d369,0xa8572375,0x201db7b1,0x3fe1b00b,
        0xee651aa2,0xe926def0,0xb9b10ad7,0x6542c9be,0xa2fcbe74,0x098e309b },
      { 0xfff1d63f,0x779deeb3,0x20bfd374,0x23d0e80a,0x8768f797,0x8452bb3b,
        0x1f952856,0xcf75bb4d,0x29ea3faa,0x8fe6b400,0x81373a53,0x12bd3e40 } },
    /* 8 */
    { { 0x16973cf4,0x070d34e1,0x7e4f34f7,0x20aee08b,0x5eb8ad29,0x269af9b9,
        0xa6a45dda,0xdde0a036,0x63df41e0,0xa18b528e,0xa260df2a,0x03cc71b2 },
      { 0xa06b1dd7,0x24a6770a,0x9d2675d3,0x5bfa9c11,0x96844432,0x73c1e2a1,
        0x131a6cf0,0x3660558d,0x2ee79454,0xb0289c83,0xc6d8ddcd,0xa6aefb01 } },
    /* 9 */
    { { 0x01ab5245,0xba1464b4,0xc48d93ff,0x9b8d0b6d,0x93ad272c,0x939867dc,
        0xae9fdc77,0xbebe085e,0x894ea8bd,0x73ae5103,0x39ac22e1,0x740fc89a },
      { 0x28e23b23,0x5e28b0a3,0xe13104d0,0x2352722e,0xb0a2640d,0xf4667a18,
        0x49bb37c3,0xac74a72e,0xe81e183a,0x79f734f0,0x3fd9c0eb,0xbffe5b6c } },
    /* 10 */
    { { 0x00623f3b,0x03cf2922,0x5f29ebff,0x095c7111,0x80aa6823,0x42d72247,
        0x7458c0b0,0x044c7ba1,0x0959ec20,0xca62f7ef,0xf8ca929f,0x40ae2ab7 },
      { 0xa927b102,0xb8c5377a,0xdc031771,0x398a86a0,0xc216a406,0x04908f9d,
        0x918d3300,0xb423a73a,0xe0b94739,0x634b0ff1,0x2d69f697,0xe29de725 } },
    /* 11 */
    { { 0x8435af04,0x744d1400,0xfec192da,0x5f255b1d,0x336dc542,0x1f17dc12,
        0x636a68a8,0x5c90c2a7,0x7704ca1e,0x960c9eb7,0x6fb3d65a,0x9de8cf1e },
      { 0x511d3d06,0xc60fee0d,0xf9eb52c7,0x466e2313,0x206b0914,0x743c0f5f,
        0x2191aa4d,0x42f55bac,0xffebdbc2,0xcefc7c8f,0xe6e8ed1c,0xd4fa6081 } },
    /* 12 */
    { { 0x98683186,0x867db639,0xddcc4ea9,0xfb5cf424,0xd4f0e7bd,0xcc9a7ffe,
        0x7a779f7e,0x7c57f71c,0xd6b25ef2,0x90774079,0xb4081680,0x90eae903 },
      { 0x0ee1fceb,0xdf2aae5e,0xe86c1a1f,0x3ff1da24,0xca193edf,0x80f587d6,
        0xdc9b9d6a,0xa5695523,0x85920303,0x7b840900,0xba6dbdef,0x1efa4dfc } },
    /* 13 */
    { { 0xe0540015,0xfbd838f9,0xc39077dc,0x2c323946,0xad619124,0x8b1fb9e6,
        0x0ca62ea8,0x9612440c,0x2dbe00ff,0x9ad9b52c,0xae197643,0xf52abaa1 },
      { 0x2cac32ad,0xd0e89894,0x62a98f91,0xdfb79e42,0x276f55cb,0x65452ecf,
        0x7ad23e12,0xdb1ac0d2,0xde4986f0,0xf68c5f6a,0x82ce327d,0x389ac37b } },
    /* 14 */
    { { 0xb8a9e8c9,0xcd96866d,0x5bb8091e,0xa11963b8,0x045b3cd2,0xc7f90d53,
        0x80f36504,0x755a72b5,0x21d3751c,0x46f8b399,0x53c193de,0x4bffdc91 },
      { 0xb89554e7,0xcd15c049,0xf7a26be6,0x353c6754,0xbd41d970,0x79602370,
        0x12b176c0,0xde16470b,0x40c8809d,0x56ba1175,0xe435fb1e,0xe2db35c3 } },
    /* 15 */
    { { 0x6328e33f,0xd71e4aab,0xaf8136d1,0x5486782b,0x86d57231,0x07a4995f,
        0x1651a968,0xf1f0a5bd,0x76803b6d,0xa5dc5b24,0x42dda935,0x5c587cbc },
      { 0xbae8b4c0,0x2b6cdb32,0xb1331138,0x66d1598b,0x5d7e9614,0x4a23b2d2,
        0x74a8c05d,0x93e402a6,0xda7ce82e,0x45ac94e6,0xe463d465,0xeb9f8281 } },
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
static int sp_384_ecc_mulmod_base_12(sp_point_384* r, const sp_digit* k,
        int map, int ct, void* heap)
{
    return sp_384_ecc_mulmod_stripe_12(r, &p384_base, p384_table,
                                      k, map, ct, heap);
}

#else
static const sp_table_entry_384 p384_table[256] = {
    /* 0 */
    { { 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00 },
      { 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00 } },
    /* 1 */
    { { 0x49c0b528,0x3dd07566,0xa0d6ce38,0x20e378e2,0x541b4d6e,0x879c3afc,
        0x59a30eff,0x64548684,0x614ede2b,0x812ff723,0x299e1513,0x4d3aadc2 },
      { 0x4b03a4fe,0x23043dad,0x7bb4a9ac,0xa1bfa8bf,0x2e83b050,0x8bade756,
        0x68f4ffd9,0xc6c35219,0x3969a840,0xdd800226,0x5a15c5e9,0x2b78abc2 } },
    /* 2 */
    { { 0x2b0c535b,0x29864753,0x70506296,0x90dd6953,0x216ab9ac,0x038cd6b4,
        0xbe12d76a,0x3df9b7b7,0x5f347bdb,0x13f4d978,0x13e94489,0x222c5c9c },
      { 0x2680dc64,0x5f8e796f,0x58352417,0x120e7cb7,0xd10740b8,0x254b5d8a,
        0x5337dee6,0xc38b8efb,0x94f02247,0xf688c2e1,0x6c25bc4c,0x7b5c75f3 } },
    /* 3 */
    { { 0x9edffea5,0xe26a3cc3,0x37d7e9fc,0x35bbfd1c,0x9bde3ef6,0xf0e7700d,
        0x1a538f5a,0x0380eb47,0x05bf9eb3,0x2e9da8bb,0x1a460c3e,0xdbb93c73 },
      { 0xf526b605,0x37dba260,0xfd785537,0x95d4978e,0xed72a04a,0x24ed793a,
        0x76005b1a,0x26948377,0x9e681f82,0x99f557b9,0xd64954ef,0xae5f9557 } },
    /* 4 */
    { { 0xf26feef9,0x24480c57,0x3a0e1240,0xc31a2694,0x273e2bc7,0x735002c3,
        0x3ef1ed4c,0x8c42e9c5,0x7f4948e8,0x028babf6,0x8a978632,0x6a502f43 },
      { 0xb74536fe,0xf5f13a46,0xd8a9f0eb,0x1d218bab,0x37232768,0x30f36bcc,
        0x576e8c18,0xc5317b31,0x9bbcb766,0xef1d57a6,0xb3e3d4dc,0x917c4930 } },
    /* 5 */
    { { 0xe349ddd0,0x11426e2e,0x9b2fc250,0x9f117ef9,0xec0174a6,0xff36b480,
        0x18458466,0x4f4bde76,0x05806049,0x2f2edb6d,0x19dfca92,0x8adc75d1 },
      { 0xb7d5a7ce,0xa619d097,0xa34411e9,0x874275e5,0x0da4b4ef,0x5403e047,
        0x77901d8f,0x2ebaafd9,0xa747170f,0x5e63ebce,0x7f9d8036,0x12a36944 } },
    /* 6 */
    { { 0x4fc52870,0x28f9c07a,0x1a53a961,0xce0b3748,0x0e1828d9,0xd550fa18,
        0x6adb225a,0xa24abaf7,0x6e58a348,0xd11ed0a5,0x948acb62,0xf3d811e6 },
      { 0x4c61ed22,0x8618dd77,0x80b47c9d,0x0bb747f9,0xde6b8559,0x22bf796f,
        0x680a21e9,0xfdfd1c6d,0x2af2c9dd,0xc0db1577,0xc1e90f3d,0xa09379e6 } },
    /* 7 */
    { { 0xe085c629,0x386c66ef,0x095bc89a,0x5fc2a461,0x203f4b41,0x1353d631,
        0x7e4bd8f5,0x7ca1972b,0xa7df8ce9,0xb077380a,0xee7e4ea3,0xd8a90389 },
      { 0xe7b14461,0x1bc74dc7,0x0c9c4f78,0xdc2cb014,0x84ef0a10,0x52b4b3a6,
        0x20327fe2,0xbde6ea5d,0x660f9615,0xb71ec435,0xb8ad8173,0xeede5a04 } },
    /* 8 */
    { { 0x893b9a2d,0x5584cbb3,0x00850c5d,0x820c660b,0x7df2d43d,0x4126d826,
        0x0109e801,0xdd5bbbf0,0x38172f1c,0x85b92ee3,0xf31430d9,0x609d4f93 },
      { 0xeadaf9d6,0x1e059a07,0x0f125fb0,0x70e6536c,0x560f20e7,0xd6220751,
        0x7aaf3a9a,0xa59489ae,0x64bae14e,0x7b70e2f6,0x76d08249,0x0dd03701 } },
    /* 9 */
    { { 0x8510521f,0x4cc13be8,0xf724cc17,0x87315ba9,0x353dc263,0xb49d83bb,
        0x0c279257,0x8b677efe,0xc93c9537,0x510a1c1c,0xa4702c99,0x33e30cd8 },
      { 0x2208353f,0xf0ffc89d,0xced42b2b,0x0170fa8d,0x26e2a5f5,0x090851ed,
        0xecb52c96,0x81276455,0x7fe1adf4,0x0646c4e1,0xb0868eab,0x513f047e } },
    /* 10 */
    { { 0xdf5bdf53,0xc07611f4,0x58b11a6d,0x45d331a7,0x1c4ee394,0x58965daf,
        0x5a5878d1,0xba8bebe7,0x82dd3025,0xaecc0a18,0xa923eb8b,0xcf2a3899 },
      { 0xd24fd048,0xf98c9281,0x8bbb025d,0x841bfb59,0xc9ab9d53,0xb8ddf8ce,
        0x7fef044e,0x538a4cb6,0x23236662,0x092ac21f,0x0b66f065,0xa919d385 } },
    /* 11 */
    { { 0x85d480d8,0x3db03b40,0x1b287a7d,0x8cd9f479,0x4a8f3bae,0x8f24dc75,
        0x3db41892,0x482eb800,0x9c56e0f5,0x38bf9eb3,0x9a91dc6f,0x8b977320 },
      { 0x7209cfc2,0xa31b05b2,0x05b2db70,0x4c49bf85,0xd619527b,0x56462498,
        0x1fac51ba,0x3fe51039,0xab4b8342,0xfb04f55e,0x04c6eabf,0xc07c10dc } },
    /* 12 */
    { { 0xdb32f048,0xad22fe4c,0x475ed6df,0x5f23bf91,0xaa66b6cb,0xa50ce0c0,
        0xf03405c0,0xdf627a89,0xf95e2d6a,0x3674837d,0xba42e64e,0x081c95b6 },
      { 0xe71d6ceb,0xeba3e036,0x6c6b0271,0xb45bcccf,0x0684701d,0x67b47e63,
        0xe712523f,0x60f8f942,0x5cd47adc,0x82423472,0x87649cbb,0x83027d79 } },
    /* 13 */
    { { 0x3615b0b8,0xb3929ea6,0xa54dac41,0xb41441fd,0xb5b6a368,0x8995d556,
        0x167ef05e,0xa80d4529,0x6d25a27f,0xf6bcb4a1,0x7bd55b68,0x210d6a4c },
      { 0x25351130,0xf3804abb,0x903e37eb,0x1d2df699,0x084c25c8,0x5f201efc,
        0xa1c68e91,0x31a28c87,0x563f62a5,0x81dad253,0xd6c415d4,0x5dd6de70 } },
    /* 14 */
    { { 0x846612ce,0x29f470fd,0xda18d997,0x986f3eec,0x2f34af86,0x6b84c161,
        0x46ddaf8b,0x5ef0a408,0xe49e795f,0x14405a00,0xaa2f7a37,0x5f491b16 },
      { 0xdb41b38d,0xc7f07ae4,0x18fbfcaa,0xef7d119e,0x14443b19,0x3a18e076,
        0x79a19926,0x4356841a,0xe2226fbe,0x91f4a91c,0x3cc88721,0xdc77248c } },
    /* 15 */
    { { 0xe4b1ec9d,0xd570ff1a,0xe7eef706,0x21d23e0e,0xca19e086,0x3cde40f4,
        0xcd4bb270,0x7d6523c4,0xbf13aa6c,0x16c1f06c,0xd14c4b60,0x5aa7245a },
      { 0x44b74de8,0x37f81467,0x620a934e,0x839e7a17,0xde8b1aa1,0xf74d14e8,
        0xf30d75e2,0x8789fa51,0xc81c261e,0x09b24052,0x33c565ee,0x654e2678 } },
    /* 16 */
    { { 0x2f9fbe67,0x378205de,0x7f728e44,0xc4afcb83,0x682e00f1,0xdbcec06c,
        0x114d5423,0xf2a145c3,0x7a52463e,0xa01d9874,0x7d717b0a,0xfc0935b1 },
      { 0xd4d01f95,0x9653bc4f,0x9560ad34,0x9aa83ea8,0xaf8e3f3f,0xf77943dc,
        0xe86fe16e,0x70774a10,0xbf9ffdcf,0x6b62e6f1,0x588745c9,0x8a72f39e } },
    /* 17 */
    { { 0x2341c342,0x73ade4da,0xea704422,0xdd326e54,0x3741cef3,0x336c7d98,
        0x59e61549,0x1eafa00d,0xbd9a3efd,0xcd3ed892,0xc5c6c7e4,0x03faf26c },
      { 0x3045f8ac,0x087e2fcf,0x174f1e73,0x14a65532,0xfe0af9a7,0x2cf84f28,
        0x2cdc935b,0xddfd7a84,0x6929c895,0x4c0f117b,0x4c8bcfcc,0x356572d6 } },
    /* 18 */
    { { 0x7d8c1bba,0x7ecbac01,0x90b0f3d5,0x6058f9c3,0xf6197d0f,0xaee116e3,
        0x4033b128,0xc4dd7068,0xc209b983,0xf084dba6,0x831dbc4a,0x97c7c2cf },
      { 0xf96010e8,0x2f4e61dd,0x529faa17,0xd97e4e20,0x69d37f20,0x4ee66660,
        0x3d366d72,0xccc139ed,0x13488e0f,0x690b6ee2,0xf3a6d533,0x7cad1dc5 } },
    /* 19 */
    { { 0xda57a41f,0x660a9a81,0xec0039b6,0xe74a0412,0x5e1dad15,0x42343c6b,
        0x46681d4c,0x284f3ff5,0x63749e89,0xb51087f1,0x6f9f2f13,0x070f23cc },
      { 0x5d186e14,0x542211da,0xfddb0dff,0x84748f37,0xdb1f4180,0x41a3aab4,
        0xa6402d0e,0x25ed667b,0x02f58355,0x2f2924a9,0xfa44a689,0x5844ee7c } },
    /* 20 */
    { { 0x3f3b236f,0xfab08607,0x81e221da,0x19e9d41d,0x3927b428,0xf3f6571e,
        0x7550f1f6,0x4348a933,0xa85e62f0,0x7167b996,0x7f5452bf,0x62d43759 },
      { 0xf2955926,0xd85feb9e,0x6df78353,0x440a561f,0x9ca36b59,0x389668ec,
        0xa22da016,0x052bf1a1,0xf6093254,0xbdfbff72,0xe22209f3,0x94e50f28 } },
    /* 21 */
    { { 0x3062e8af,0x90b2e5b3,0xe8a3d369,0xa8572375,0x201db7b1,0x3fe1b00b,
        0xee651aa2,0xe926def0,0xb9b10ad7,0x6542c9be,0xa2fcbe74,0x098e309b },
      { 0xfff1d63f,0x779deeb3,0x20bfd374,0x23d0e80a,0x8768f797,0x8452bb3b,
        0x1f952856,0xcf75bb4d,0x29ea3faa,0x8fe6b400,0x81373a53,0x12bd3e40 } },
    /* 22 */
    { { 0x104cbba5,0xc023780d,0xfa35dd4c,0x6207e747,0x1ca9b6a3,0x35c23928,
        0x97987b10,0x4ff19be8,0x8022eee8,0xb8476bbf,0xd3bbe74d,0xaa0a4a14 },
      { 0x187d4543,0x20f94331,0x79f6e066,0x32153870,0xac7e82e1,0x83b0f74e,
        0x828f06ab,0xa7748ba2,0xc26ef35f,0xc5f0298a,0x8e9a7dbd,0x0f0c5070 } },
    /* 23 */
    { { 0xdef029dd,0x0c5c244c,0x850661b8,0x3dabc687,0xfe11d981,0x9992b865,
        0x6274dbad,0xe9801b8f,0x098da242,0xe54e6319,0x91a53d08,0x9929a91a },
      { 0x35285887,0x37bffd72,0xf1418102,0xbc759425,0xfd2e6e20,0x9280cc35,
        0xfbc42ee5,0x735c600c,0x8837619a,0xb7ad2864,0xa778c57b,0xa3627231 } },
    /* 24 */
    { { 0x91361ed8,0xae799b5c,0x6c63366c,0x47d71b75,0x1b265a6a,0x54cdd521,
        0x98d77b74,0xe0215a59,0xbab29db0,0x4424d9b7,0x7fd9e536,0x8b0ffacc },
      { 0x37b5d9ef,0x46d85d12,0xbfa91747,0x5b106d62,0x5f99ba2d,0xed0479f8,
        0x1d104de4,0x0e6f3923,0x25e8983f,0x83a84c84,0xf8105a70,0xa9507e0a } },
    /* 25 */
    { { 0x14cf381c,0xf6c68a6e,0xc22e31cc,0xaf9d27bd,0xaa8a5ccb,0x23568d4d,
        0xe338e4d2,0xe431eec0,0x8f52ad1f,0xf1a828fe,0xe86acd80,0xdb6a0579 },
      { 0x4507832a,0x2885672e,0x887e5289,0x73fc275f,0x05610d08,0x65f80278,
        0x075ff5b0,0x8d9b4554,0x09f712b5,0x3a8e8fb1,0x2ebe9cf2,0x39f0ac86 } },
    /* 26 */
    { { 0x4c52edf5,0xd8fabf78,0xa589ae53,0xdcd737e5,0xd791ab17,0x94918bf0,
        0xbcff06c9,0xb5fbd956,0xdca46d45,0xf6d3032e,0x41a3e486,0x2cdff7e1 },
      { 0x61f47ec8,0x6674b3ba,0xeef84608,0x8a882163,0x4c687f90,0xa257c705,
        0xf6cdf227,0xe30cb2ed,0x7f6ea846,0x2c4c64ca,0xcc6bcd3c,0x186fa17c } },
    /* 27 */
    { { 0x1dfcb91e,0x48a3f536,0x646d358a,0x83595e13,0x91128798,0xbd15827b,
        0x2187757a,0x3ce612b8,0x61bd7372,0x873150a1,0xb662f568,0xf4684530 },
      { 0x401896f6,0x8833950b,0x77f3e090,0xe11cb89a,0x48e7f4a5,0xb2f12cac,
        0xf606677e,0x313dd769,0x16579f93,0xfdcf08b3,0x46b8f22b,0x6429cec9 } },
    /* 28 */
    { { 0xbb75f9a4,0x4984dd54,0x29d3b570,0x4aef06b9,0x3d6e4c1e,0xb5f84ca2,
        0xb083ef35,0x24c61c11,0x392ca9ff,0xce4a7392,0x6730a800,0x865d6517 },
      { 0x722b4a2b,0xca3dfe76,0x7b083e0e,0x12c04bf9,0x1b86b8a5,0x803ce5b5,
        0x6a7e3e0c,0x3fc7632d,0xc81adbe4,0xc89970c2,0x120e16b1,0x3cbcd3ad } },
    /* 29 */
    { { 0xec30ce93,0xfbfb4cc7,0xb72720a2,0x10ed6c7d,0x47b55500,0xec675bf7,
        0x333ff7c3,0x90725903,0x5075bfc0,0xc7c3973e,0x07acf31b,0xb049ecb0 },
      { 0x4f58839c,0xb4076eaf,0xa2b05e4f,0x101896da,0xab40c66e,0x3f6033b0,
        0xc8d864ba,0x19ee9eeb,0x47bf6d2a,0xeb6cf155,0xf826477d,0x8e5a9663 } },
    /* 30 */
    { { 0xf7fbd5e1,0x69e62fdd,0x76912b1d,0x38ecfe54,0xd1da3bfb,0x845a3d56,
        0x1c86f0d4,0x0494950e,0x3bc36ce8,0x83cadbf9,0x4fccc8d1,0x41fce572 },
      { 0x8332c144,0x05f939c2,0x0871e46e,0xb17f248b,0x66e8aff6,0x3d8534e2,
        0x3b85c629,0x1d06f1dc,0xa3131b73,0xdb06a32e,0x8b3f64e5,0xf295184d } },
    /* 31 */
    { { 0x36ddc103,0xd9653ff7,0x95ef606f,0x25f43e37,0xfe06dce8,0x09e301fc,
        0x30b6eebf,0x85af2341,0x0ff56b20,0x79b12b53,0xfe9a3c6b,0x9b4fb499 },
      { 0x51d27ac2,0x0154f892,0x56ca5389,0xd33167e3,0xafc065a6,0x7828ec1f,
        0x7f746c9b,0x0959a258,0x0c44f837,0xb18f1be3,0xc4132fdb,0xa7946117 } },
    /* 32 */
    { { 0x5e3c647b,0xc0426b77,0x8cf05348,0xbfcbd939,0x172c0d3d,0x31d312e3,
        0xee754737,0x5f49fde6,0x6da7ee61,0x895530f0,0xe8b3a5fb,0xcf281b0a },
      { 0x41b8a543,0xfd149735,0x3080dd30,0x41a625a7,0x653908cf,0xe2baae07,
        0xba02a278,0xc3d01436,0x7b21b8f8,0xa0d0222e,0xd7ec1297,0xfdc270e9 } },
    /* 33 */
    { { 0xbc7f41d6,0x00873c0c,0x1b7ad641,0xd976113e,0x238443fb,0x2a536ff4,
        0x41e62e45,0x030d00e2,0x5f545fc6,0x532e9867,0x8e91208c,0xcd033108 },
      { 0x9797612c,0xd1a04c99,0xeea674e2,0xd4393e02,0xe19742a1,0xd56fa69e,
        0x85f0590e,0xdd2ab480,0x48a2243d,0xa5cefc52,0x54383f41,0x48cc67b6 } },
    /* 34 */
    { { 0xfc14ab48,0x4e50430e,0x26706a74,0x195b7f4f,0xcc881ff6,0x2fe8a228,
        0xd945013d,0xb1b968e2,0x4b92162b,0x936aa579,0x364e754a,0x4fb766b7 },
      { 0x31e1ff7f,0x13f93bca,0xce4f2691,0x696eb5ca,0xa2b09e02,0xff754bf8,
        0xe58e3ff8,0x58f13c9c,0x1678c0b0,0xb757346f,0xa86692b3,0xd54200db } },
    /* 35 */
    { { 0x6dda1265,0x9a030bbd,0xe89718dd,0xf7b4f3fc,0x936065b8,0xa6a4931f,
        0x5f72241c,0xbce72d87,0x65775857,0x6cbb51cb,0x4e993675,0xc7161815 },
      { 0x2ee32189,0xe81a0f79,0x277dc0b2,0xef2fab26,0xb71f469f,0x9e64f6fe,
        0xdfdaf859,0xb448ce33,0xbe6b5df1,0x3f5c1c4c,0x1de45f7b,0xfb8dfb00 } },
    /* 36 */
    { { 0x4d5bb921,0xc7345fa7,0x4d2b667e,0x5c7e04be,0x282d7a3e,0x47ed3a80,
        0x7e47b2a4,0x5c2777f8,0x08488e2e,0x89b3b100,0xb2eb5b45,0x9aad77c2 },
      { 0xdaac34ae,0xd681bca7,0x26afb326,0x2452e4e5,0x41a1ee14,0x0c887924,
        0xc2407ade,0x743b04d4,0xfc17a2ac,0xcb5e999b,0x4a701a06,0x4dca2f82 } },
    /* 37 */
    { { 0x1127bc1a,0x68e31ca6,0x17ead3be,0xa3edd59b,0xe25f5a15,0x67b6b645,
        0xa420e15e,0x76221794,0x4b1e872e,0x794fd83b,0xb2dece1b,0x7cab3f03 },
      { 0xca9b3586,0x7119bf15,0x4d250bd7,0xa5545924,0xcc6bcf24,0x173633ea,
        0xb1b6f884,0x9bd308c2,0x447d38c3,0x3bae06f5,0xf341fe1c,0x54dcc135 } },
    /* 38 */
    { { 0x943caf0d,0x56d3598d,0x225ff133,0xce044ea9,0x563fadea,0x9edf6a7c,
        0x73e8dc27,0x632eb944,0x3190dcab,0x814b467e,0x6dbb1e31,0x2d4f4f31 },
      { 0xa143b7ca,0x8d69811c,0xde7cf950,0x4ec1ac32,0x37b5fe82,0x223ab5fd,
        0x9390f1d9,0xe82616e4,0x75804610,0xabff4b20,0x875b08f0,0x11b9be15 } },
    /* 39 */
    { { 0x3bbe682c,0x4ae31a3d,0x74eef2dd,0xbc7c5d26,0x3c47dd40,0x92afd10a,
        0xc14ab9e1,0xec7e0a3b,0xb2e495e4,0x6a6c3dd1,0x309bcd85,0x085ee5e9 },
      { 0x8c2e67fd,0xf381a908,0xe261eaf2,0x32083a80,0x96deee15,0x0fcd6a49,
        0x5e524c79,0xe3b8fb03,0x1d5b08b9,0x8dc360d9,0x7f26719f,0x3a06e2c8 } },
    /* 40 */
    { { 0x7237cac0,0x5cd9f5a8,0x43586794,0x93f0b59d,0xe94f6c4e,0x4384a764,
        0xb62782d3,0x8304ed2b,0xcde06015,0x0b8db8b3,0x5dbe190f,0x4336dd53 },
      { 0x92ab473a,0x57443553,0xbe5ed046,0x031c7275,0x21909aa4,0x3e78678c,
        0x99202ddb,0x4ab7e04f,0x6977e635,0x2648d206,0x093198be,0xd427d184 } },
    /* 41 */
    { { 0x0f9b5a31,0x822848f5,0xbaadb62a,0xbb003468,0x3357559c,0x233a0472,
        0x79aee843,0x49ef6880,0xaeb9e1e3,0xa89867a0,0x1f6f9a55,0xc151931b },
      { 0xad74251e,0xd264eb0b,0x4abf295e,0x37b9b263,0x04960d10,0xb600921b,
        0x4da77dc0,0x0de53dbc,0xd2b18697,0x01d9bab3,0xf7156ddf,0xad54ec7a } },
    /* 42 */
    { { 0x79efdc58,0x8e74dc35,0x4ff68ddb,0x456bd369,0xd32096a5,0x724e74cc,
        0x386783d0,0xe41cff42,0x7c70d8a4,0xa04c7f21,0xe61a19a2,0x41199d2f },
      { 0x29c05dd2,0xd389a3e0,0xe7e3fda9,0x535f2a6b,0x7c2b4df8,0x26ecf72d,
        0xfe745294,0x678275f4,0x9d23f519,0x6319c9cc,0x88048fc4,0x1e05a02d } },
    /* 43 */
    { { 0xd4d5ffe8,0x75cc8e2e,0xdbea17f2,0xf8bb4896,0xcee3cb4a,0x35059790,
        0xa47c6165,0x4c06ee85,0x92935d2f,0xf98fff25,0x32ffd7c7,0x34c4a572 },
      { 0xea0376a2,0xc4b14806,0x4f115e02,0x2ea5e750,0x1e55d7c0,0x532d76e2,
        0xf31044da,0x68dc9411,0x71b77993,0x9272e465,0x93a8cfd5,0xadaa38bb } },
    /* 44 */
    { { 0x7d4ed72a,0x4bf0c712,0xba1f79a3,0xda0e9264,0xf4c39ea4,0x48c0258b,
        0x2a715138,0xa5394ed8,0xbf06c660,0x4af511ce,0xec5c37cd,0xfcebceef },
      { 0x779ae8c1,0xf23b75aa,0xad1e606e,0xdeff59cc,0x22755c82,0xf3f526fd,
        0xbb32cefd,0x64c5ab44,0x915bdefd,0xa96e11a2,0x1143813e,0xab19746a } },
    /* 45 */
    { { 0xec837d7d,0x43c78585,0xb8ee0ba4,0xca5b6fbc,0xd5dbb5ee,0x34e924d9,
        0xbb4f1ca5,0x3f4fa104,0x398640f7,0x15458b72,0xd7f407ea,0x4231faa9 },
      { 0xf96e6896,0x53e0661e,0xd03b0f9d,0x554e4c69,0x9c7858d1,0xd4fcb07b,
        0x52cb04fa,0x7e952793,0x8974e7f7,0x5f5f1574,0x6b6d57c8,0x2e3fa558 } },
    /* 46 */
    { { 0x6a9951a8,0x42cd4803,0x42792ad0,0xa8b15b88,0xabb29a73,0x18e8bcf9,
        0x409933e8,0xbfd9a092,0xefb88dc4,0x760a3594,0x40724458,0x14418863 },
      { 0x99caedc7,0x162a56ee,0x91d101c9,0x8fb12ecd,0x393202da,0xea671967,
        0xa4ccd796,0x1aac8c4a,0x1cf185a8,0x7db05036,0x8cfd095a,0x0c9f86cd } },
    /* 47 */
    { { 0x10b2a556,0x9a728147,0x327b70b2,0x767ca964,0x5e3799b7,0x04ed9e12,
        0x22a3eb2a,0x6781d2dc,0x0d9450ac,0x5bd116eb,0xa7ebe08a,0xeccac1fc },
      { 0xdc2d6e94,0xde68444f,0x35ecf21b,0x3621f429,0x29e03a2c,0x14e2d543,
        0x7d3e7f0a,0x53e42cd5,0x73ed00b9,0xbba26c09,0xc57d2272,0x00297c39 } },
    /* 48 */
    { { 0xb8243a7d,0x3aaaab10,0x8fa58c5b,0x6eeef93e,0x9ae7f764,0xf866fca3,
        0x61ab04d3,0x64105a26,0x03945d66,0xa3578d8a,0x791b848c,0xb08cd3e4 },
      { 0x756d2411,0x45edc5f8,0xa755128c,0xd4a790d9,0x49e5f6a0,0xc2cf0963,
        0xf649beaa,0xc66d267d,0x8467039e,0x3ce6d968,0x42f7816f,0x50046c6b } },
    /* 49 */
    { { 0x66425043,0x92ae1602,0xf08db890,0x1ff66afd,0x8f162ce5,0x386f5a7f,
        0xfcf5598f,0x18d2dea0,0x1a8ca18e,0x78372b3a,0x8cd0e6f7,0xdf0d20eb },
      { 0x75bb4045,0x7edd5e1d,0xb96d94b7,0x252a47ce,0x2c626776,0xbdb29358,
        0x40dd1031,0x853c3943,0x7d5f47fd,0x9dc9becf,0xbae4044a,0x27c2302f } },
    /* 50 */
    { { 0x8f2d49ce,0x2d1d208a,0x162df0a2,0x0d91aa02,0x09a07f65,0x9c5cce87,
        0x84339012,0xdf07238b,0x419442cd,0x5028e2c8,0x72062aba,0x2dcbd358 },
      { 0xe4680967,0xb5fbc3cb,0x9f92d72c,0x2a7bc645,0x116c369d,0x806c76e1,
        0x3177e8d8,0x5c50677a,0x4569df57,0x753739eb,0x36c3f40b,0x2d481ef6 } },
    /* 51 */
    { { 0xfea1103e,0x1a2d39fd,0x95f81b17,0xeaae5592,0xf59b264a,0xdbd0aa18,
        0xcb592ee0,0x90c39c1a,0x9750cca3,0xdf62f80d,0xdf97cc6c,0xda4d8283 },
      { 0x1e201067,0x0a6dd346,0x69fb1f6b,0x1531f859,0x1d60121f,0x4895e552,
        0x4c041c91,0x0b21aab0,0xbcc1ccf8,0x9d896c46,0x3141bde7,0xd24da3b3 } },
    /* 52 */
    { { 0x53b0a354,0x575a0537,0x0c6ddcd8,0x392ff2f4,0x56157b94,0x0b8e8cff,
        0x3b1b80d1,0x073e57bd,0x3fedee15,0x2a75e0f0,0xaa8e6f19,0x752380e4 },
      { 0x6558ffe9,0x1f4e227c,0x19ec5415,0x3a348618,0xf7997085,0xab382d5e,
        0xddc46ac2,0x5e6deaff,0xfc8d094c,0xe5144078,0xf60e37c6,0xf674fe51 } },
    /* 53 */
    { { 0xaf63408f,0x6fb87ae5,0xcd75a737,0xa39c36a9,0xcf4c618d,0x7833313f,
        0xf034c88d,0xfbcd4482,0x39b35288,0x4469a761,0x66b5d9c9,0x77a711c5 },
      { 0x944f8d65,0x4a695dc7,0x161aaba8,0xe6da5f65,0x24601669,0x8654e9c3,
        0x28ae7491,0xbc8b93f5,0x8f5580d8,0x5f1d1e83,0xcea32cc8,0x8ccf9a1a } },
    /* 54 */
    { { 0x7196fee2,0x28ab110c,0x874c8945,0x75799d63,0x29aedadd,0xa2629348,
        0x2be88ff4,0x9714cc7b,0xd58d60d6,0xf71293cf,0x32a564e9,0xda6b6cb3 },
      { 0x3dd821c2,0xf43fddb1,0x90dd323d,0xf2f2785f,0x048489f8,0x91246419,
        0xd24c6749,0x61660f26,0xc803c15c,0x961d9e8c,0xfaadc4c9,0x631c6158 } },
    /* 55 */
    { { 0xfd752366,0xacf2ebe0,0x139be88b,0xb93c340e,0x0f20179e,0x98f66485,
        0xff1da785,0x14820254,0x4f85c16e,0x5278e276,0x7aab1913,0xa246ee45 },
      { 0x53763b33,0x43861eb4,0x45c0bc0d,0xc49f03fc,0xad6b1ea1,0xafff16bc,
        0x6fd49c99,0xce33908b,0xf7fde8c3,0x5c51e9bf,0xff142c5e,0x076a7a39 } },
    /* 56 */
    { { 0x9e338d10,0x04639dfe,0xf42b411b,0x8ee6996f,0xa875cef2,0x960461d1,
        0x95b4d0ba,0x1057b6d6,0xa906e0bc,0x27639252,0xe1c20f8a,0x2c19f09a },
      { 0xeef4c43d,0x5b8fc3f0,0x07a84aa9,0xe2e1b1a8,0x835d2bdb,0x5f455528,
        0x207132dd,0x0f4aee4d,0x3907f675,0xe9f8338c,0x0e0531f0,0x7a874dc9 } },
    /* 57 */
    { { 0x97c27050,0x84b22d45,0x59e70bf8,0xbd0b8df7,0x79738b9b,0xb4d67405,
        0xcd917c4f,0x47f4d5f5,0x13ce6e33,0x9099c4ce,0x521d0f8b,0x942bfd39 },
      { 0xa43b566d,0x5028f0f6,0x21bff7de,0xaf6e8669,0xc44232cd,0x83f6f856,
        0xf915069a,0x65680579,0xecfecb85,0xd12095a2,0xdb01ba16,0xcf7f06ae } },
    /* 58 */
    { { 0x8ef96c80,0x0f56e3c4,0x3ddb609c,0xd521f2b3,0x7dc1450d,0x2be94102,
        0x02a91fe2,0x2d21a071,0x1efa37de,0x2e6f74fa,0x156c28a1,0x9a9a90b8 },
      { 0x9dc7dfcb,0xc54ea9ea,0x2c2c1d62,0xc74e66fc,0x49d3e067,0x9f23f967,
        0x54dd38ad,0x1c7c3a46,0x5946cee3,0xc7005884,0x45cc045d,0x89856368 } },
    /* 59 */
    { { 0xfce73946,0x29da7cd4,0x23168563,0x8f697db5,0xcba92ec6,0x8e235e9c,
        0x9f91d3ea,0x55d4655f,0xaa50a6cd,0xf3689f23,0x21e6a1a0,0xdcf21c26 },
      { 0x61b818bf,0xcffbc82e,0xda47a243,0xc74a2f96,0x8bc1a0cf,0x234e980a,
        0x7929cb6d,0xf35fd6b5,0xefe17d6c,0x81468e12,0x58b2dafb,0xddea6ae5 } },
    /* 60 */
    { { 0x7e787b2e,0x294de887,0x39a9310d,0x258acc1f,0xac14265d,0x92d9714a,
        0x708b48a0,0x18b5591c,0xe1abbf71,0x27cc6bb0,0x568307b9,0xc0581fa3 },
      { 0xf24d4d58,0x9e0f58a3,0xe0ce2327,0xfebe9bb8,0x9d1be702,0x91fd6a41,
        0xfacac993,0x9a7d8a45,0x9e50d66d,0xabc0a08c,0x06498201,0x02c342f7 } },
    /* 61 */
    { { 0x157bdbc2,0xccd71407,0xad0e1605,0x72fa89c6,0xb92a015f,0xb1d3da2b,
        0xa0a3fe56,0x8ad9e7cd,0x24f06737,0x160edcbd,0x61275be6,0x79d4db33 },
      { 0x5f3497c4,0xd3d31fd9,0x04192fb0,0x8cafeaee,0x13a50af3,0xe13ca745,
        0x8c85aae5,0x18826167,0x9eb556ff,0xce06cea8,0xbdb549f3,0x2eef1995 } },
    /* 62 */
    { { 0x50596edc,0x8ed7d3eb,0x905243a2,0xaa359362,0xa4b6d02b,0xa212c2c2,
        0xc4fbec68,0x611fd727,0xb84f733d,0x8a0b8ff7,0x5f0daf0e,0xd85a6b90 },
      { 0xd4091cf7,0x60e899f5,0x2eff2768,0x4fef2b67,0x10c33964,0xc1f195cb,
        0x93626a8f,0x8275d369,0x0d6c840a,0xc77904f4,0x7a868acd,0x88d8b7fd } },
    /* 63 */
    { { 0x7bd98425,0x85f23723,0xc70b154e,0xd4463992,0x96687a2e,0xcbb00ee2,
        0xc83214fd,0x905fdbf7,0x13593684,0x2019d293,0xef51218e,0x0428c393 },
      { 0x981e909a,0x40c7623f,0x7be192da,0x92513385,0x4010907e,0x48fe480f,
        0x3120b459,0xdd7a187c,0xa1fd8f3c,0xc9d7702d,0xe358efc5,0x66e4753b } },
    /* 64 */
    { { 0x16973cf4,0x070d34e1,0x7e4f34f7,0x20aee08b,0x5eb8ad29,0x269af9b9,
        0xa6a45dda,0xdde0a036,0x63df41e0,0xa18b528e,0xa260df2a,0x03cc71b2 },
      { 0xa06b1dd7,0x24a6770a,0x9d2675d3,0x5bfa9c11,0x96844432,0x73c1e2a1,
        0x131a6cf0,0x3660558d,0x2ee79454,0xb0289c83,0xc6d8ddcd,0xa6aefb01 } },
    /* 65 */
    { { 0x01ab5245,0xba1464b4,0xc48d93ff,0x9b8d0b6d,0x93ad272c,0x939867dc,
        0xae9fdc77,0xbebe085e,0x894ea8bd,0x73ae5103,0x39ac22e1,0x740fc89a },
      { 0x28e23b23,0x5e28b0a3,0xe13104d0,0x2352722e,0xb0a2640d,0xf4667a18,
        0x49bb37c3,0xac74a72e,0xe81e183a,0x79f734f0,0x3fd9c0eb,0xbffe5b6c } },
    /* 66 */
    { { 0xc6a2123f,0xb1a358f5,0xfe28df6d,0x927b2d95,0xf199d2f9,0x89702753,
        0x1a3f82dc,0x0a73754c,0x777affe1,0x063d029d,0xdae6d34d,0x5439817e },
      { 0x6b8b83c4,0xf7979eef,0x9d945682,0x615cb214,0xc5e57eae,0x8f0e4fac,
        0x113047dd,0x042b89b8,0x93f36508,0x888356dc,0x5fd1f32f,0xbf008d18 } },
    /* 67 */
    { { 0x4e8068db,0x8012aa24,0xa5729a47,0xc72cc641,0x43f0691d,0x3c33df2c,
        0x1d92145f,0xfa057347,0xb97f7946,0xaefc0f2f,0x2f8121bf,0x813d75cb },
      { 0x4383bba6,0x05613c72,0xa4224b3f,0xa924ce70,0x5f2179a6,0xe59cecbe,
        0x79f62b61,0x78e2e8aa,0x53ad8079,0x3ac2cc3b,0xd8f4fa96,0x55518d71 } },
    /* 68 */
    { { 0x00623f3b,0x03cf2922,0x5f29ebff,0x095c7111,0x80aa6823,0x42d72247,
        0x7458c0b0,0x044c7ba1,0x0959ec20,0xca62f7ef,0xf8ca929f,0x40ae2ab7 },
      { 0xa927b102,0xb8c5377a,0xdc031771,0x398a86a0,0xc216a406,0x04908f9d,
        0x918d3300,0xb423a73a,0xe0b94739,0x634b0ff1,0x2d69f697,0xe29de725 } },
    /* 69 */
    { { 0x8435af04,0x744d1400,0xfec192da,0x5f255b1d,0x336dc542,0x1f17dc12,
        0x636a68a8,0x5c90c2a7,0x7704ca1e,0x960c9eb7,0x6fb3d65a,0x9de8cf1e },
      { 0x511d3d06,0xc60fee0d,0xf9eb52c7,0x466e2313,0x206b0914,0x743c0f5f,
        0x2191aa4d,0x42f55bac,0xffebdbc2,0xcefc7c8f,0xe6e8ed1c,0xd4fa6081 } },
    /* 70 */
    { { 0xb0ab9645,0xb5e405d3,0xd5f1f711,0xaeec7f98,0x585c2a6e,0x8ad42311,
        0x512c6944,0x045acb9e,0xa90db1c6,0xae106c4e,0x898e6563,0xb89f33d5 },
      { 0x7fed2ce4,0x43b07cd9,0xdd815b20,0xf9934e17,0x0a81a349,0x6778d4d5,
        0x52918061,0x9e616ade,0xd7e67112,0xfa06db06,0x88488091,0x1da23cf1 } },
    /* 71 */
    { { 0x42f2c4b5,0x821c46b3,0x66059e47,0x931513ef,0x66f50cd1,0x7030ae43,
        0x43e7b127,0x43b536c9,0x5fca5360,0x006258cf,0x6b557abf,0xe4e3ee79 },
      { 0x24c8b22f,0xbb6b3900,0xfcbf1054,0x2eb5e2c1,0x567492af,0x937b18c9,
        0xacf53957,0xf09432e4,0x1dbf3a56,0x585f5a9d,0xbe0887cf,0xf86751fd } },
    /* 72 */
    { { 0x9d10e0b2,0x157399cb,0x60dc51b7,0x1c0d5956,0x1f583090,0x1d496b8a,
        0x88590484,0x6658bc26,0x03213f28,0x88c08ab7,0x7ae58de4,0x8d2e0f73 },
      { 0x486cfee6,0x9b79bc95,0xe9e5bc57,0x036a26c7,0xcd8ae97a,0x1ad03601,
        0xff3a0494,0x06907f87,0x2c7eb584,0x078f4bbf,0x7e8d0a5a,0xe3731bf5 } },
    /* 73 */
    { { 0xe1cd0abe,0x72f2282b,0x87efefa2,0xd4f9015e,0x6c3834bd,0x9d189806,
        0xb8a29ced,0x9c8cdcc1,0xfee82ebc,0x0601b9f4,0x7206a756,0x371052bc },
      { 0x46f32562,0x76fa1092,0x17351bb4,0xdaad534c,0xb3636bb5,0xc3d64c37,
        0x45d54e00,0x038a8c51,0x32c09e7c,0x301e6180,0x95735151,0x9764eae7 } },
    /* 74 */
    { { 0xcbd5256a,0x8791b19f,0x6ca13a3b,0x4007e0f2,0x4cf06904,0x03b79460,
        0xb6c17589,0xb18a9c22,0x81d45908,0xa1cb7d7d,0x21bb68f1,0x6e13fa9d },
      { 0xa71e6e16,0x47183c62,0xe18749ed,0x5cf0ef8e,0x2e5ed409,0x2c9c7f9b,
        0xe6e117e1,0x042eeacc,0x13fb5a7f,0xb86d4816,0xc9e5feb1,0xea1cf0ed } },
    /* 75 */
    { { 0xcea4cc9b,0x6e6573c9,0xafcec8f3,0x5417961d,0xa438b6f6,0x804bf02a,
        0xdcd4ea88,0xb894b03c,0x3799571f,0xd0f807e9,0x862156e8,0x3466a7f5 },
      { 0x56515664,0x51e59acd,0xa3c5eb0b,0x55b0f93c,0x6a4279db,0x84a06b02,
        0xc5fae08e,0x5c850579,0xa663a1a2,0xcf07b8db,0xf46ffc8d,0x49a36bbc } },
    /* 76 */
    { { 0x46d93106,0xe47f5acc,0xaa897c9c,0x65b7ade0,0x12d7e4be,0x37cf4c94,
        0xd4b2caa9,0xa2ae9b80,0xe60357a3,0x5e7ce09c,0xc8ecd5f9,0x29f77667 },
      { 0xa8a0b1c5,0xdf6868f5,0x62978ad8,0x240858cf,0xdc0002a1,0x0f7ac101,
        0xffe9aa05,0x1d28a9d7,0x5b962c97,0x744984d6,0x3d28c8b2,0xa8a7c00b } },
    /* 77 */
    { { 0xae11a338,0x7c58a852,0xd1af96e7,0xa78613f1,0x5355cc73,0x7e9767d2,
        0x792a2de6,0x6ba37009,0x124386b2,0x7d60f618,0x11157674,0xab09b531 },
      { 0x98eb9dd0,0x95a04841,0x15070328,0xe6c17acc,0x489c6e49,0xafc6da45,
        0xbb211530,0xab45a60a,0x7d7ea933,0xc58d6592,0x095642c6,0xa3ef3c65 } },
    /* 78 */
    { { 0xdf010879,0x89d420e9,0x39576179,0x9d25255d,0xe39513b6,0x9cdefd50,
        0xd5d1c313,0xe4efe45b,0x3f7af771,0xc0149de7,0x340ab06b,0x55a6b4f4 },
      { 0xebeaf771,0xf1325251,0x878d4288,0x2ab44128,0x18e05afe,0xfcd5832e,
        0xcc1fb62b,0xef52a348,0xc1c4792a,0x2bd08274,0x877c6dc7,0x345c5846 } },
    /* 79 */
    { { 0xbea65e90,0xde15ceb0,0x2416d99c,0x0987f72b,0xfd863dec,0x44db578d,
        0xac6a3578,0xf617b74b,0xdb48e999,0x9e62bd7a,0xeab1a1be,0x877cae61 },
      { 0x3a358610,0x23adddaa,0x325e2b07,0x2fc4d6d1,0x1585754e,0x897198f5,
        0xb392b584,0xf741852c,0xb55f7de1,0x9927804c,0x1aa8efae,0xe9e6c4ed } },
    /* 80 */
    { { 0x98683186,0x867db639,0xddcc4ea9,0xfb5cf424,0xd4f0e7bd,0xcc9a7ffe,
        0x7a779f7e,0x7c57f71c,0xd6b25ef2,0x90774079,0xb4081680,0x90eae903 },
      { 0x0ee1fceb,0xdf2aae5e,0xe86c1a1f,0x3ff1da24,0xca193edf,0x80f587d6,
        0xdc9b9d6a,0xa5695523,0x85920303,0x7b840900,0xba6dbdef,0x1efa4dfc } },
    /* 81 */
    { { 0xe0540015,0xfbd838f9,0xc39077dc,0x2c323946,0xad619124,0x8b1fb9e6,
        0x0ca62ea8,0x9612440c,0x2dbe00ff,0x9ad9b52c,0xae197643,0xf52abaa1 },
      { 0x2cac32ad,0xd0e89894,0x62a98f91,0xdfb79e42,0x276f55cb,0x65452ecf,
        0x7ad23e12,0xdb1ac0d2,0xde4986f0,0xf68c5f6a,0x82ce327d,0x389ac37b } },
    /* 82 */
    { { 0xf8e60f5b,0x511188b4,0x48aa2ada,0x7fe67015,0x381abca2,0xdb333cb8,
        0xdaf3fc97,0xb15e6d9d,0x36aabc03,0x4b24f6eb,0x72a748b4,0xc59789df },
      { 0x29cf5279,0x26fcb8a5,0x01ad9a6c,0x7a3c6bfc,0x4b8bac9b,0x866cf88d,
        0x9c80d041,0xf4c89989,0x70add148,0xf0a04241,0x45d81a41,0x5a02f479 } },
    /* 83 */
    { { 0xc1c90202,0xfa5c877c,0xf8ac7570,0xd099d440,0xd17881f7,0x428a5b1b,
        0x5b2501d7,0x61e267db,0xf2e4465b,0xf889bf04,0x76aa4cb8,0x4da3ae08 },
      { 0xe3e66861,0x3ef0fe26,0x3318b86d,0x5e772953,0x747396df,0xc3c35fbc,
        0x439ffd37,0x5115a29c,0xb2d70374,0xbfc4bd97,0x56246b9d,0x088630ea } },
    /* 84 */
    { { 0xb8a9e8c9,0xcd96866d,0x5bb8091e,0xa11963b8,0x045b3cd2,0xc7f90d53,
        0x80f36504,0x755a72b5,0x21d3751c,0x46f8b399,0x53c193de,0x4bffdc91 },
      { 0xb89554e7,0xcd15c049,0xf7a26be6,0x353c6754,0xbd41d970,0x79602370,
        0x12b176c0,0xde16470b,0x40c8809d,0x56ba1175,0xe435fb1e,0xe2db35c3 } },
    /* 85 */
    { { 0x6328e33f,0xd71e4aab,0xaf8136d1,0x5486782b,0x86d57231,0x07a4995f,
        0x1651a968,0xf1f0a5bd,0x76803b6d,0xa5dc5b24,0x42dda935,0x5c587cbc },
      { 0xbae8b4c0,0x2b6cdb32,0xb1331138,0x66d1598b,0x5d7e9614,0x4a23b2d2,
        0x74a8c05d,0x93e402a6,0xda7ce82e,0x45ac94e6,0xe463d465,0xeb9f8281 } },
    /* 86 */
    { { 0xfecf5b9b,0x34e0f9d1,0xf206966a,0xa115b12b,0x1eaa0534,0x5591cf3b,
        0xfb1558f9,0x5f0293cb,0x1bc703a5,0x1c8507a4,0x862c1f81,0x92e6b81c },
      { 0xcdaf24e3,0xcc9ebc66,0x72fcfc70,0x68917ecd,0x8157ba48,0x6dc9a930,
        0xb06ab2b2,0x5d425c08,0x36e929c4,0x362f8ce7,0x62e89324,0x09f6f57c } },
    /* 87 */
    { { 0xd29375fb,0x1c7d6b78,0xe35d1157,0xfabd851e,0x4243ea47,0xf6f62dcd,
        0x8fe30b0f,0x1dd92460,0xffc6e709,0x08166dfa,0x0881e6a7,0xc6c4c693 },
      { 0xd6a53fb0,0x20368f87,0x9eb4d1f9,0x38718e9f,0xafd7e790,0x03f08acd,
        0x72fe2a1c,0x0835eb44,0x88076e5d,0x7e050903,0xa638e731,0x538f765e } },
    /* 88 */
    { { 0xc2663b4b,0x0e0249d9,0x47cd38dd,0xe700ab5b,0x2c46559f,0xb192559d,
        0x4bcde66d,0x8f9f74a8,0x3e2aced5,0xad161523,0x3dd03a5b,0xc155c047 },
      { 0x3be454eb,0x346a8799,0x83b7dccd,0x66ee94db,0xab9d2abe,0x1f6d8378,
        0x7733f355,0x4a396dd2,0xf53553c2,0x419bd40a,0x731dd943,0xd0ead98d } },
    /* 89 */
    { { 0xec142408,0x908e0b0e,0x4114b310,0x98943cb9,0x1742b1d7,0x03dbf7d8,
        0x693412f4,0xd270df6b,0x8f69e20c,0xc5065494,0x697e43a1,0xa76a90c3 },
      { 0x4624825a,0xe0fa3384,0x8acc34c2,0x82e48c0b,0xe9a14f2b,0x7b24bd14,
        0x4db30803,0x4f5dd5e2,0x932da0a3,0x0c77a9e7,0x74c653dc,0x20db90f2 } },
    /* 90 */
    { { 0x0e6c5fd9,0x261179b7,0x6c982eea,0xf8bec123,0xd4957b7e,0x47683338,
        0x0a72f66a,0xcc47e664,0x1bad9350,0xbd54bf6a,0xf454e95a,0xdfbf4c6a },
      { 0x6907f4fa,0x3f7a7afa,0x865ca735,0x7311fae0,0x2a496ada,0x24737ab8,
        0x15feb79b,0x13e425f1,0xa1b93c21,0xe9e97c50,0x4ddd3eb5,0xb26b6eac } },
    /* 91 */
    { { 0x2a2e5f2b,0x81cab9f5,0xbf385ac4,0xf93caf29,0xc909963a,0xf4bf35c3,
        0x74c9143c,0x081e7300,0xc281b4c5,0x3ea57fa8,0x9b340741,0xe497905c },
      { 0x55ab3cfb,0xf556dd8a,0x518db6ad,0xd444b96b,0x5ef4b955,0x34f5425a,
        0xecd26aa3,0xdda7a3ac,0xda655e97,0xb57da11b,0xc2024c70,0x02da3eff } },
    /* 92 */
    { { 0x6481d0d9,0xe24b0036,0x818fdfe2,0x3740dbe5,0x190fda00,0xc1fc1f45,
        0x3cf27fde,0x329c9280,0x6934f43e,0x7435cb53,0x7884e8fe,0x2b505a5d },
      { 0x711adcc9,0x6cfcc6a6,0x531e21e1,0xf034325c,0x9b2a8a99,0xa2f4a967,
        0x3c21bdff,0x9d5f3842,0x31b57d66,0xb25c7811,0x0b8093b9,0xdb5344d8 } },
    /* 93 */
    { { 0xae50a2f5,0x0d72e667,0xe4a861d1,0x9b7f8d8a,0x330df1cb,0xa129f70f,
        0xe04fefc3,0xe90aa5d7,0xe72c3ae1,0xff561ecb,0xcdb955fa,0x0d8fb428 },
      { 0xd7663784,0xd2235f73,0x7e2c456a,0xc05baec6,0x2adbfccc,0xe5c292e4,
        0xefb110d5,0x4fd17988,0xd19d49f3,0x27e57734,0x84f679fe,0x188ac4ce } },
    /* 94 */
    { { 0xa796c53e,0x7ee344cf,0x0868009b,0xbbf6074d,0x474a1295,0x1f1594f7,
        0xac11632d,0x66776edc,0x04e2fa5a,0x1862278b,0xc854a89a,0x52665cf2 },
      { 0x8104ab58,0x7e376464,0x7204fd6d,0x16775913,0x44ea1199,0x86ca06a5,
        0x1c9240dd,0xaa3f765b,0x24746149,0x5f8501a9,0xdcd251d7,0x7b982e30 } },
    /* 95 */
    { { 0xc15f3060,0xe44e9efc,0xa87ebbe6,0x5ad62f2e,0xc79500d4,0x36499d41,
        0x336fa9d1,0xa66d6dc0,0x5afd3b1f,0xf8afc495,0xe5c9822b,0x1d8ccb24 },
      { 0x79d7584b,0x4031422b,0xea3f20dd,0xc54a0580,0x958468c5,0x3f837c8f,
        0xfbea7735,0x3d82f110,0x7dffe2fc,0x679a8778,0x20704803,0x48eba63b } },
    /* 96 */
    { { 0xdf46e2f6,0x89b10d41,0x19514367,0x13ab57f8,0x1d469c87,0x067372b9,
        0x4f6c5798,0x0c195afa,0x272c9acf,0xea43a12a,0x678abdac,0x9dadd8cb },
      { 0xe182579a,0xcce56c6b,0x2d26c2d8,0x86febadb,0x2a44745c,0x1c668ee1,
        0x98dc047a,0x580acd86,0x51b9ec2d,0x5a2b79cc,0x4054f6a0,0x007da608 } },
    /* 97 */
    { { 0x17b00dd0,0x9e3ca352,0x0e81a7a6,0x046779cb,0xd482d871,0xb999fef3,
        0xd9233fbc,0xe6f38134,0xf48cd0e0,0x112c3001,0x3c6c66ae,0x934e7576 },
      { 0xd73234dc,0xb44d4fc3,0x864eafc1,0xfcae2062,0x26bef21a,0x843afe25,
        0xf3b75fdf,0x61355107,0x794c2e6b,0x8367a5aa,0x8548a372,0x3d2629b1 } },
    /* 98 */
    { { 0x437cfaf8,0x6230618f,0x2032c299,0x5b8742cb,0x2293643a,0x949f7247,
        0x09464f79,0xb8040f1a,0x4f254143,0x049462d2,0x366c7e76,0xabd6b522 },
      { 0xd5338f55,0x119b392b,0x01495a0c,0x1a80a9ce,0xf8d7537e,0xf3118ca7,
        0x6bf4b762,0xb715adc2,0xa8482b6c,0x24506165,0x96a7c84d,0xd958d7c6 } },
    /* 99 */
    { { 0xbdc21f31,0x9ad8aa87,0x8063e58c,0xadb3cab4,0xb07dd7b8,0xefd86283,
        0x1be7c6b4,0xc7b9b762,0x015582de,0x2ef58741,0x299addf3,0xc970c52e },
      { 0x22f24d66,0x78f02e2a,0x74cc100a,0xefec1d10,0x09316e1a,0xaf2a6a39,
        0x5849dd49,0xce7c2205,0x96bffc4c,0x9c1fe75c,0x7ba06ec0,0xcad98fd2 } },
    /* 100 */
    { { 0xb648b73e,0xed76e2d0,0x1cfd285e,0xa9f92ce5,0x2ed13de1,0xa8c86c06,
        0xa5191a93,0x1d3a574e,0x1ad1b8bf,0x385cdf8b,0x47d2cfe3,0xbbecc28a },
      { 0x69cec548,0x98d326c0,0xf240a0b2,0x4f5bc1dd,0x29057236,0x241a7062,
        0xc68294a4,0x0fc6e9c5,0xa319f17a,0x4d04838b,0x9ffc1c6f,0x8b612cf1 } },
    /* 101 */
    { { 0x4c3830eb,0x9bb0b501,0x8ee0d0c5,0x3d08f83c,0x79ba9389,0xa4a62642,
        0x9cbc2914,0x5d5d4044,0x074c46f0,0xae9eb83e,0x74ead7d6,0x63bb758f },
      { 0xc6bb29e0,0x1c40d2ea,0x4b02f41e,0x95aa2d87,0x53cb199a,0x92989175,
        0x51584f6d,0xdd91bafe,0x31a1aaec,0x3715efb9,0x46780f9e,0xc1b6ae5b } },
    /* 102 */
    { { 0x42772f41,0xcded3e4b,0x3bcb79d1,0x3a700d5d,0x80feee60,0x4430d50e,
        0xf5e5d4bb,0x444ef1fc,0xe6e358ff,0xc660194f,0x6a91b43c,0xe68a2f32 },
      { 0x977fe4d2,0x5842775c,0x7e2a41eb,0x78fdef5c,0xff8df00e,0x5f3bec02,
        0x5852525d,0xf4b840cd,0x4e6988bd,0x0870483a,0xcc64b837,0x39499e39 } },
    /* 103 */
    { { 0xb08df5fe,0xfc05de80,0x63ba0362,0x0c12957c,0xd5cf1428,0xea379414,
        0x54ef6216,0xc559132a,0xb9e65cf8,0x33d5f12f,0x1695d663,0x09c60278 },
      { 0x61f7a2fb,0x3ac1ced4,0xd4f5eeb8,0xdd838444,0x8318fcad,0x82a38c6c,
        0xe9f1a864,0x315be2e5,0x442daf47,0x317b5771,0x95aa5f9e,0x81b5904a } },
    /* 104 */
    { { 0x8b21d232,0x6b6b1c50,0x8c2cba75,0x87f3dbc0,0xae9f0faf,0xa7e74b46,
        0xbb7b8079,0x036a0985,0x8d974a25,0x4f185b90,0xd9af5ec9,0x5aa7cef0 },
      { 0x57dcfffc,0xe0566a70,0xb8453225,0x6ea311da,0x23368aa9,0x72ea1a8d,
        0x48cd552d,0xed9b2083,0xc80ea435,0xb987967c,0x6c104173,0xad735c75 } },
    /* 105 */
    { { 0xcee76ef4,0xaea85ab3,0xaf1d2b93,0x44997444,0xeacb923f,0x0851929b,
        0x51e3bc0c,0xb080b590,0x59be68a2,0xc4ee1d86,0x64b26cda,0xf00de219 },
      { 0xf2e90d4d,0x8d7fb5c0,0x77d9ec64,0x00e219a7,0x5d1c491c,0xc4e6febd,
        0x1a8f4585,0x080e3754,0x48d2af9c,0x4a9b86c8,0xb6679851,0x2ed70db6 } },
    /* 106 */
    { { 0x586f25cb,0xaee44116,0xa0fcf70f,0xf7b6861f,0x18a350e8,0x55d2cd20,
        0x92dc286f,0x861bf3e5,0x6226aba7,0x9ab18ffa,0xa9857b03,0xd15827be },
      { 0x92e6acef,0x26c1f547,0xac1fbac3,0x422c63c8,0xfcbfd71d,0xa2d8760d,
        0xb2511224,0x35f6a539,0x048d1a21,0xbaa88fa1,0xebf999db,0x49f1abe9 } },
    /* 107 */
    { { 0xf7492b73,0x16f9f4f4,0xcb392b1a,0xcf28ec1e,0x69ca6ffc,0x45b130d4,
        0xb72efa58,0x28ba8d40,0x5ca066f5,0xace987c7,0x4ad022eb,0x3e399246 },
      { 0x752555bb,0x63a2d84e,0x9c2ae394,0xaaa93b4a,0xc89539ca,0xcd80424e,
        0xaa119a99,0x6d6b5a6d,0x379f2629,0xbd50334c,0xef3cc7d3,0x899e925e } },
    /* 108 */
    { { 0xbf825dc4,0xb7ff3651,0x40b9c462,0x0f741cc4,0x5cc4fb5b,0x771ff5a9,
        0x47fd56fe,0xcb9e9c9b,0x5626c0d3,0xbdf053db,0xf7e14098,0xa97ce675 },
      { 0x6c934f5e,0x68afe5a3,0xccefc46f,0x6cd5e148,0xd7a88586,0xc7758570,
        0xdd558d40,0x49978f5e,0x64ae00c1,0xa1d5088a,0xf1d65bb2,0x58f2a720 } },
    /* 109 */
    { { 0x3e4daedb,0x66fdda4a,0x65d1b052,0x38318c12,0x4c4bbf5c,0x28d910a2,
        0x78a9cd14,0x762fe5c4,0xd2cc0aee,0x08e5ebaa,0xca0c654c,0xd2cdf257 },
      { 0x08b717d2,0x48f7c58b,0x386cd07a,0x3807184a,0xae7d0112,0x3240f626,
        0xc43917b0,0x03e9361b,0x20aea018,0xf261a876,0x7e1e6372,0x53f556a4 } },
    /* 110 */
    { { 0x2f512a90,0xc84cee56,0x1b0ea9f1,0x24b3c004,0xe26cc1ea,0x0ee15d2d,
        0xf0c9ef7d,0xd848762c,0xd5341435,0x1026e9c5,0xfdb16b31,0x8f5b73dc },
      { 0xd2c75d95,0x1f69bef2,0xbe064dda,0x8d33d581,0x57ed35e6,0x8c024c12,
        0xc309c281,0xf8d435f9,0xd6960193,0xfd295061,0xe9e49541,0x66618d78 } },
    /* 111 */
    { { 0x8ce382de,0x571cfd45,0xde900dde,0x175806ee,0x34aba3b5,0x61849965,
        0xde7aec95,0xe899778a,0xff4aa97f,0xe8f00f6e,0x010b0c6d,0xae971cb5 },
      { 0x3af788f1,0x1827eebc,0xe413fe2d,0xd46229ff,0x4741c9b4,0x8a15455b,
        0xf8e424eb,0x5f02e690,0xdae87712,0x40a1202e,0x64944f6d,0x49b3bda2 } },
    /* 112 */
    { { 0x035b2d69,0xd63c6067,0x6bed91b0,0xb507150d,0x7afb39b2,0x1f35f82f,
        0x16012b66,0xb9bd9c01,0xed0a5f50,0x00d97960,0x2716f7c9,0xed705451 },
      { 0x127abdb4,0x1576eff4,0xf01e701c,0x6850d698,0x3fc87e2f,0x9fa7d749,
        0xb0ce3e48,0x0b6bcc6f,0xf7d8c1c0,0xf4fbe1f5,0x02719cc6,0xcf75230e } },
    /* 113 */
    { { 0x722d94ed,0x6761d6c2,0x3718820e,0xd1ec3f21,0x25d0e7c6,0x65a40b70,
        0xbaf3cf31,0xd67f830e,0xb93ea430,0x633b3807,0x0bc96c69,0x17faa0ea },
      { 0xdf866b98,0xe6bf3482,0xa9db52d4,0x205c1ee9,0xff9ab869,0x51ef9bbd,
        0x75eeb985,0x3863dad1,0xd3cf442a,0xef216c3b,0xf9c8e321,0x3fb228e3 } },
    /* 114 */
    { { 0x0760ac07,0x94f9b70c,0x9d79bf4d,0xf3c9ccae,0xc5ffc83d,0x73cea084,
        0xdc49c38e,0xef50f943,0xbc9e7330,0xf467a2ae,0x44ea7fba,0x5ee534b6 },
      { 0x03609e7f,0x20cb6272,0x62fdc9f0,0x09844355,0x0f1457f7,0xaf5c8e58,
        0xb4b25941,0xd1f50a6c,0x2ec82395,0x77cb247c,0xda3dca33,0xa5f3e1e5 } },
    /* 115 */
    { { 0x7d85fa94,0x023489d6,0x2db9ce47,0x0ba40537,0xaed7aad1,0x0fdf7a1f,
        0x9a4ccb40,0xa57b0d73,0x5b18967c,0x48fcec99,0xb7274d24,0xf30b5b6e },
      { 0xc81c5338,0x7ccb4773,0xa3ed6bd0,0xb85639e6,0x1d56eada,0x7d9df95f,
        0x0a1607ad,0xe256d57f,0x957574d6,0x6da7ffdc,0x01c7a8c4,0x65f84046 } },
    /* 116 */
    { { 0xcba1e7f1,0x8d45d0cb,0x02b55f64,0xef0a08c0,0x17e19892,0x771ca31b,
        0x4885907e,0xe1843ecb,0x364ce16a,0x67797ebc,0x8df4b338,0x816d2b2d },
      { 0x39aa8671,0xe870b0e5,0xc102b5f5,0x9f0db3e4,0x1720c697,0x34296659,
        0x613c0d2a,0x0ad4c89e,0x418ddd61,0x1af900b2,0xd336e20e,0xe087ca72 } },
    /* 117 */
    { { 0xaba10079,0x222831ff,0x6d64fff2,0x0dc5f87b,0x3e8cb330,0x44547907,
        0x702a33fb,0xe815aaa2,0x5fba3215,0x338d6b2e,0x79f549c8,0x0f7535cb },
      { 0x2ee95923,0x471ecd97,0xc6d1c09f,0x1e868b37,0xc666ef4e,0x2bc7b8ec,
        0x808a4bfc,0xf5416589,0x3fbc4d2e,0xf23e9ee2,0x2d75125b,0x4357236c } },
    /* 118 */
    { { 0xba9cdb1b,0xfe176d95,0x2f82791e,0x45a1ca01,0x4de4cca2,0x97654af2,
        0x5cc4bcb9,0xbdbf9d0e,0xad97ac0a,0xf6a7df50,0x61359fd6,0xc52112b0 },
      { 0x4f05eae3,0x696d9ce3,0xe943ac2b,0x903adc02,0x0848be17,0xa9075347,
        0x2a3973e5,0x1e20f170,0x6feb67e9,0xe1aacc1c,0xe16bc6b9,0x2ca0ac32 } },
    /* 119 */
    { { 0xef871eb5,0xffea12e4,0xa8bf0a7a,0x94c2f25d,0x78134eaa,0x4d1e4c2a,
        0x0360fb10,0x11ed16fb,0x85fc11be,0x4029b6db,0xf4d390fa,0x5e9f7ab7 },
      { 0x30646612,0x5076d72f,0xdda1d0d8,0xa0afed1d,0x85a1d103,0x29022257,
        0x4e276bcd,0xcb499e17,0x51246c3d,0x16d1da71,0x589a0443,0xc72d56d3 } },
    /* 120 */
    { { 0xdae5bb45,0xdf5ffc74,0x261bd6dc,0x99068c4a,0xaa98ec7b,0xdc0afa7a,
        0xf121e96d,0xedd2ee00,0x1414045c,0x163cc7be,0x335af50e,0xb0b1bbce },
      { 0x01a06293,0xd440d785,0x6552e644,0xcdebab7c,0x8c757e46,0x48cb8dbc,
        0x3cabe3cb,0x81f9cf78,0xb123f59a,0xddd02611,0xeeb3784d,0x3dc7b88e } },
    /* 121 */
    { { 0xc4741456,0xe1b8d398,0x6032a121,0xa9dfa902,0x1263245b,0x1cbfc86d,
        0x5244718c,0xf411c762,0x05b0fc54,0x96521d54,0xdbaa4985,0x1afab46e },
      { 0x8674b4ad,0xa75902ba,0x5ad87d12,0x486b43ad,0x36e0d099,0x72b1c736,
        0xbb6cd6d6,0x39890e07,0x59bace4e,0x8128999c,0x7b535e33,0xd8da430b } },
    /* 122 */
    { { 0xc6b75791,0x39f65642,0x21806bfb,0x050947a6,0x1362ef84,0x0ca3e370,
        0x8c3d2391,0x9bc60aed,0x732e1ddc,0x9b488671,0xa98ee077,0x12d10d9e },
      { 0x3651b7dc,0xb6f2822d,0x80abd138,0x6345a5ba,0x472d3c84,0x62033262,
        0xacc57527,0xd54a1d40,0x424447cb,0x6ea46b3a,0x2fb1a496,0x5bc41057 } },
    /* 123 */
    { { 0xa751cd0e,0xe70c57a3,0xeba3c7d6,0x190d8419,0x9d47d55a,0xb1c3bee7,
        0xf912c6d8,0xda941266,0x407a6ad6,0x12e9aacc,0x6e838911,0xd6ce5f11 },
      { 0x70e1f2ce,0x063ca97b,0x8213d434,0xa3e47c72,0x84df810a,0xa016e241,
        0xdfd881a4,0x688ad7b0,0xa89bf0ad,0xa37d99fc,0xa23c2d23,0xd8e3f339 } },
    /* 124 */
    { { 0x750bed6f,0xbdf53163,0x83e68b0a,0x808abc32,0x5bb08a33,0x85a36627,
        0x6b0e4abe,0xf72a3a0f,0xfaf0c6ad,0xf7716d19,0x5379b25f,0x22dcc020 },
      { 0xf9a56e11,0x7400bf8d,0x56a47f21,0x6cb8bad7,0x7a6eb644,0x7c97176f,
        0xd1f5b646,0xe8fd84f7,0x44ddb054,0x98320a94,0x1dde86f5,0x07071ba3 } },
    /* 125 */
    { { 0x98f8fcb9,0x6fdfa0e5,0x94d0d70c,0x89cec8e0,0x106d20a8,0xa0899397,
        0xba8acc9c,0x915bfb9a,0x5507e01c,0x1370c94b,0x8a821ffb,0x83246a60 },
      { 0xbe3c378f,0xa8273a9f,0x35a25be9,0x7e544789,0x4dd929d7,0x6cfa4972,
        0x365bd878,0x987fed9d,0x5c29a7ae,0x4982ac94,0x5ddd7ec5,0x4589a5d7 } },
    /* 126 */
    { { 0xa95540a9,0x9fabb174,0x0162c5b0,0x7cfb886f,0xea3dee18,0x17be766b,
        0xe88e624c,0xff7da41f,0x8b919c38,0xad0b71eb,0xf31ff9a9,0x86a522e0 },
      { 0x868bc259,0xbc8e6f72,0x3ccef9e4,0x6130c638,0x9a466555,0x09f1f454,
        0x19b2bfb4,0x8e6c0f09,0x0ca7bb22,0x945c46c9,0x4dafb67b,0xacd87168 } },
    /* 127 */
    { { 0x10c53841,0x090c72ca,0x55a4fced,0xc20ae01b,0xe10234ad,0x03f7ebd5,
        0x85892064,0xb3f42a6a,0xb4a14722,0xbdbc30c0,0x8ca124cc,0x971bc437 },
      { 0x517ff2ff,0x6f79f46d,0xecba947b,0x6a9c96e2,0x62925122,0x5e79f2f4,
        0x6a4e91f1,0x30a96bb1,0x2d4c72da,0x1147c923,0x5811e4df,0x65bc311f } },
    /* 128 */
    { { 0x139b3239,0x87c7dd7d,0x4d833bae,0x8b57824e,0x9fff0015,0xbcbc4878,
        0x909eaf1a,0x8ffcef8b,0xf1443a78,0x9905f4ee,0xe15cbfed,0x020dd4a2 },
      { 0xa306d695,0xca2969ec,0xb93caf60,0xdf940cad,0x87ea6e39,0x67f7fab7,
        0xf98c4fe5,0x0d0ee10f,0xc19cb91e,0xc646879a,0x7d1d7ab4,0x4b4ea50c } },
    /* 129 */
    { { 0x7a0db57e,0x19e40945,0x9a8c9702,0xe6017cad,0x1be5cff9,0xdbf739e5,
        0xa7a938a2,0x3646b3cd,0x68350dfc,0x04511085,0x56e098b5,0xad3bd6f3 },
      { 0xee2e3e3e,0x935ebabf,0x473926cb,0xfbd01702,0x9e9fb5aa,0x7c735b02,
        0x2e3feff0,0xc52a1b85,0x046b405a,0x9199abd3,0x39039971,0xe306fcec } },
    /* 130 */
    { { 0x23e4712c,0xd6d9aec8,0xc3c198ee,0x7ca8376c,0x31bebd8a,0xe6d83187,
        0xd88bfef3,0xed57aff3,0xcf44edc7,0x72a645ee,0x5cbb1517,0xd4e63d0b },
      { 0xceee0ecf,0x98ce7a1c,0x5383ee8e,0x8f012633,0xa6b455e8,0x3b879078,
        0xc7658c06,0xcbcd3d96,0x0783336a,0x721d6fe7,0x5a677136,0xf21a7263 } },
    /* 131 */
    { { 0x9586ba11,0x19d8b3cd,0x8a5c0480,0xd9e0aeb2,0x2230ef5c,0xe4261dbf,
        0x02e6bf09,0x095a9dee,0x80dc7784,0x8963723c,0x145157b1,0x5c97dbaf },
      { 0x4bc4503e,0x97e74434,0x85a6b370,0x0fb1cb31,0xcd205d4b,0x3e8df2be,
        0xf8f765da,0x497dd1bc,0x6c988a1a,0x92ef95c7,0x64dc4cfa,0x3f924baa } },
    /* 132 */
    { { 0x7268b448,0x6bf1b8dd,0xefd79b94,0xd4c28ba1,0xe4e3551f,0x2fa1f8c8,
        0x5c9187a9,0x769e3ad4,0x40326c0d,0x28843b4d,0x50d5d669,0xfefc8094 },
      { 0x90339366,0x30c85bfd,0x5ccf6c3a,0x4eeb56f1,0x28ccd1dc,0x0e72b149,
        0xf2ce978e,0x73ee85b5,0x3165bb23,0xcdeb2bf3,0x4e410abf,0x8106c923 } },
    /* 133 */
    { { 0x7d02f4ee,0xc8df0161,0x18e21225,0x8a781547,0x6acf9e40,0x4ea895eb,
        0x6e5a633d,0x8b000cb5,0x7e981ffb,0xf31d86d5,0x4475bc32,0xf5c8029c },
      { 0x1b568973,0x764561ce,0xa62996ec,0x2f809b81,0xda085408,0x9e513d64,
        0xe61ce309,0xc27d815d,0x272999e0,0x0da6ff99,0xfead73f7,0xbd284779 } },
    /* 134 */
    { { 0x9b1cdf2b,0x6033c2f9,0xbc5fa151,0x2a99cf06,0x12177b3b,0x7d27d259,
        0xc4485483,0xb1f15273,0x102e2297,0x5fd57d81,0xc7f6acb7,0x3d43e017 },
      { 0x3a70eb28,0x41a8bb0b,0x3e80b06b,0x67de2d8e,0x70c28de5,0x09245a41,
        0xa7b26023,0xad7dbcb1,0x2cbc6c1e,0x70b08a35,0x9b33041f,0xb504fb66 } },
    /* 135 */
    { { 0xf97a27c2,0xa8e85ab5,0xc10a011b,0x6ac5ec8b,0xffbcf161,0x55745533,
        0x65790a60,0x01780e85,0x99ee75b0,0xe451bf85,0x39c29881,0x8907a63b },
      { 0x260189ed,0x76d46738,0x47bd35cb,0x284a4436,0x20cab61e,0xd74e8c40,
        0x416cf20a,0x6264bf8c,0x5fd820ce,0xfa5a6c95,0xf24bb5fc,0xfa7154d0 } },
    /* 136 */
    { { 0x9b3f5034,0x18482cec,0xcd9e68fd,0x962d445a,0x95746f23,0x266fb1d6,
        0x58c94a4b,0xc66ade5a,0xed68a5b6,0xdbbda826,0x7ab0d6ae,0x05664a4d },
      { 0x025e32fc,0xbcd4fe51,0xa96df252,0x61a5aebf,0x31592a31,0xd88a07e2,
        0x98905517,0x5d9d94de,0x5fd440e7,0x96bb4010,0xe807db4c,0x1b0c47a2 } },
    /* 137 */
    { { 0x08223878,0x5c2a6ac8,0xe65a5558,0xba08c269,0x9bbc27fd,0xd22b1b9b,
        0x72b9607d,0x919171bf,0xe588dc58,0x9ab455f9,0x23662d93,0x6d54916e },
      { 0x3b1de0c1,0x8da8e938,0x804f278f,0xa84d186a,0xd3461695,0xbf4988cc,
        0xe10eb0cb,0xf5eae3be,0xbf2a66ed,0x1ff8b68f,0xc305b570,0xa68daf67 } },
    /* 138 */
    { { 0x44b2e045,0xc1004cff,0x4b1c05d4,0x91b5e136,0x88a48a07,0x53ae4090,
        0xea11bb1a,0x73fb2995,0x3d93a4ea,0x32048570,0x3bfc8a5f,0xcce45de8 },
      { 0xc2b3106e,0xaff4a97e,0xb6848b4f,0x9069c630,0xed76241c,0xeda837a6,
        0x6cc3f6cf,0x8a0daf13,0x3da018a8,0x199d049d,0xd9093ba3,0xf867c6b1 } },
    /* 139 */
    { { 0x56527296,0xe4d42a56,0xce71178d,0xae26c73d,0x6c251664,0x70a0adac,
        0x5dc0ae1d,0x813483ae,0xdaab2daf,0x7574eacd,0xc2d55f4f,0xc56b52dc },
      { 0x95f32923,0x872bc167,0x5bdd2a89,0x4be17581,0xa7699f00,0x9b57f1e7,
        0x3ac2de02,0x5fcd9c72,0x92377739,0x83af3ba1,0xfc50b97f,0xa64d4e2b } },
    /* 140 */
    { { 0x0e552b40,0x2172dae2,0xd34d52e8,0x62f49725,0x07958f98,0x7930ee40,
        0x751fdd74,0x56da2a90,0xf53e48c3,0xf1192834,0x8e53c343,0x34d2ac26 },
      { 0x13111286,0x1073c218,0xda9d9827,0x201dac14,0xee95d378,0xec2c29db,
        0x1f3ee0b1,0x9316f119,0x544ce71c,0x7890c9f0,0x27612127,0xd77138af } },
    /* 141 */
    { { 0x3b4ad1cd,0x78045e6d,0x4aa49bc1,0xcd86b94e,0xfd677a16,0x57e51f1d,
        0xfa613697,0xd9290935,0x34f4d893,0x7a3f9593,0x5d5fcf9b,0x8c9c248b },
      { 0x6f70d4e9,0x9f23a482,0x63190ae9,0x17273454,0x5b081a48,0x4bdd7c13,
        0x28d65271,0x1e2de389,0xe5841d1f,0x0bbaaa25,0x746772e5,0xc4c18a79 } },
    /* 142 */
    { { 0x593375ac,0x10ee2681,0x7dd5e113,0x4f3288be,0x240f3538,0x9a97b2fb,
        0x1de6b1e2,0xfa11089f,0x1351bc58,0x516da562,0x2dfa85b5,0x573b6119 },
      { 0x6cba7df5,0x89e96683,0x8c28ab40,0xf299be15,0xad43fcbf,0xe91c9348,
        0x9a1cefb3,0xe9bbc7cc,0x738b2775,0xc8add876,0x775eaa01,0x6e3b1f2e } },
    /* 143 */
    { { 0xb677788b,0x0365a888,0x3fd6173c,0x634ae8c4,0x9e498dbe,0x30498761,
        0xc8f779ab,0x08c43e6d,0x4c09aca9,0x068ae384,0x2018d170,0x2380c70b },
      { 0xa297c5ec,0xcf77fbc3,0xca457948,0xdacbc853,0x336bec7e,0x3690de04,
        0x14eec461,0x26bbac64,0x1f713abf,0xd1c23c7e,0xe6fd569e,0xf08bbfcd } },
    /* 144 */
    { { 0x84770ee3,0x5f8163f4,0x744a1706,0x0e0c7f94,0xe1b2d46d,0x9c8f05f7,
        0xd01fd99a,0x417eafe7,0x11440e5b,0x2ba15df5,0x91a6fbcf,0xdc5c552a },
      { 0xa270f721,0x86271d74,0xa004485b,0x32c0a075,0x8defa075,0x9d1a87e3,
        0xbf0d20fe,0xb590a7ac,0x8feda1f5,0x430c41c2,0x58f6ec24,0x454d2879 } },
    /* 145 */
    { { 0x7c525435,0x52b7a635,0x37c4bdbc,0x3d9ef57f,0xdffcc475,0x2bb93e9e,
        0x7710f3be,0xf7b8ba98,0x21b727de,0x42ee86da,0x2e490d01,0x55ac3f19 },
      { 0xc0c1c390,0x487e3a6e,0x446cde7b,0x036fb345,0x496ae951,0x089eb276,
        0x71ed1234,0xedfed4d9,0x900f0b46,0x661b0dd5,0x8582f0d3,0x11bd6f1b } },
    /* 146 */
    { { 0x076bc9d1,0x5cf9350f,0xcf3cd2c3,0x15d903be,0x25af031c,0x21cfc8c2,
        0x8b1cc657,0xe0ad3248,0x70014e87,0xdd9fb963,0x297f1658,0xf0f3a5a1 },
      { 0xf1f703aa,0xbb908fba,0x2f6760ba,0x2f9cc420,0x66a38b51,0x00ceec66,
        0x05d645da,0x4deda330,0xf7de3394,0xb9cf5c72,0x1ad4c906,0xaeef6502 } },
    /* 147 */
    { { 0x7a19045d,0x0583c8b1,0xd052824c,0xae7c3102,0xff6cfa58,0x2a234979,
        0x62c733c0,0xfe9dffc9,0x9c0c4b09,0x3a7fa250,0x4fe21805,0x516437bb },
      { 0xc2a23ddb,0x9454e3d5,0x289c104e,0x0726d887,0x4fd15243,0x8977d918,
        0x6d7790ba,0xc559e73f,0x465af85f,0x8fd3e87d,0x5feee46b,0xa2615c74 } },
    /* 148 */
    { { 0x4335167d,0xc8d607a8,0xe0f5c887,0x8b42d804,0x398d11f9,0x5f9f13df,
        0x20740c67,0x5aaa5087,0xa3d9234b,0x83da9a6a,0x2a54bad1,0xbd3a5c4e },
      { 0x2db0f658,0xdd13914c,0x5a3f373a,0x29dcb66e,0x5245a72b,0xbfd62df5,
        0x91e40847,0x19d18023,0xb136b1ae,0xd9df74db,0x3f93bc5b,0x72a06b6b } },
    /* 149 */
    { { 0xad19d96f,0x6da19ec3,0xfb2a4099,0xb342daa4,0x662271ea,0x0e61633a,
        0xce8c054b,0x3bcece81,0x8bd62dc6,0x7cc8e061,0xee578d8b,0xae189e19 },
      { 0xdced1eed,0x73e7a25d,0x7875d3ab,0xc1257f0a,0x1cfef026,0x2cb2d5a2,
        0xb1fdf61c,0xd98ef39b,0x24e83e6c,0xcd8e6f69,0xc7b7088b,0xd71e7076 } },
    /* 150 */
    { { 0x9d4245bf,0x33936830,0x2ac2953b,0x22d96217,0x56c3c3cd,0xb3bf5a82,
        0x0d0699e8,0x50c9be91,0x8f366459,0xec094463,0x513b7c35,0x6c056dba },
      { 0x045ab0e3,0x687a6a83,0x445c9295,0x8d40b57f,0xa16f5954,0x0f345048,
        0x3d8f0a87,0x64b5c639,0x9f71c5e2,0x106353a2,0x874f0dd4,0xdd58b475 } },
    /* 151 */
    { { 0x62230c72,0x67ec084f,0x481385e3,0xf14f6cca,0x4cda7774,0xf58bb407,
        0xaa2dbb6b,0xe15011b1,0x0c035ab1,0xd488369d,0x8245f2fd,0xef83c24a },
      { 0x9fdc2538,0xfb57328f,0x191fe46a,0x79808293,0x32ede548,0xe28f5c44,
        0xea1a022c,0x1b3cda99,0x3df2ec7f,0x39e639b7,0x760e9a18,0x77b6272b } },
    /* 152 */
    { { 0xa65d56d5,0x2b1d51bd,0x7ea696e0,0x3a9b71f9,0x9904f4c4,0x95250ecc,
        0xe75774b7,0x8bc4d6eb,0xeaeeb9aa,0x0e343f8a,0x930e04cb,0xc473c1d1 },
      { 0x064cd8ae,0x282321b1,0x5562221c,0xf4b4371e,0xd1bf1221,0xc1cc81ec,
        0xe2c8082f,0xa52a07a9,0xba64a958,0x350d8e59,0x6fb32c9a,0x29e4f3de } },
    /* 153 */
    { { 0xba89aaa5,0x0aa9d56c,0xc4c6059e,0xf0208ac0,0xbd6ddca4,0x7400d9c6,
        0xf2c2f74a,0xb384e475,0xb1562dd3,0x4c1061fc,0x2e153b8d,0x3924e248 },
      { 0x849808ab,0xf38b8d98,0xa491aa36,0x29bf3260,0x88220ede,0x85159ada,
        0xbe5bc422,0x8b47915b,0xd7300967,0xa934d72e,0x2e515d0d,0xc4f30398 } },
    /* 154 */
    { { 0x1b1de38b,0xe3e9ee42,0x42636760,0xa124e25a,0x90165b1a,0x90bf73c0,
        0x146434c5,0x21802a34,0x2e1fa109,0x54aa83f2,0xed9c51e9,0x1d4bd03c },
      { 0x798751e6,0xc2d96a38,0x8c3507f5,0xed27235f,0xc8c24f88,0xb5fb80e2,
        0xd37f4f78,0xf873eefa,0xf224ba96,0x7229fd74,0x9edd7149,0x9dcd9199 } },
    /* 155 */
    { { 0x4e94f22a,0xee9f81a6,0xf71ec341,0xe5609892,0xa998284e,0x6c818ddd,
        0x3b54b098,0x9fd47295,0x0e8a7cc9,0x47a6ac03,0xb207a382,0xde684e5e },
      { 0x2b6b956b,0x4bdd1ecd,0xf01b3583,0x09084414,0x55233b14,0xe2f80b32,
        0xef5ebc5e,0x5a0fec54,0xbf8b29a2,0x74cf25e6,0x7f29e014,0x1c757fa0 } },
    /* 156 */
    { { 0xeb0fdfe4,0x1bcb5c4a,0xf0899367,0xd7c649b3,0x05bc083b,0xaef68e3f,
        0xa78aa607,0x57a06e46,0x21223a44,0xa2136ecc,0x52f5a50b,0x89bd6484 },
      { 0x4455f15a,0x724411b9,0x08a9c0fd,0x23dfa970,0x6db63bef,0x7b0da4d1,
        0xfb162443,0x6f8a7ec1,0xe98284fb,0xc1ac9cee,0x33566022,0x085a582b } },
    /* 157 */
    { { 0xec1f138a,0x15cb61f9,0x668f0c28,0x11c9a230,0xdf93f38f,0xac829729,
        0x4048848d,0xcef25698,0x2bba8fbf,0x3f686da0,0x111c619a,0xed5fea78 },
      { 0xd6d1c833,0x9b4f73bc,0x86e7bf80,0x50951606,0x042b1d51,0xa2a73508,
        0x5fb89ec2,0x9ef6ea49,0x5ef8b892,0xf1008ce9,0x9ae8568b,0x78a7e684 } },
    /* 158 */
    { { 0x10470cd8,0x3fe83a7c,0xf86df000,0x92734682,0xda9409b5,0xb5dac06b,
        0x94939c5f,0x1e7a9660,0x5cc116dc,0xdec6c150,0x66bac8cc,0x1a52b408 },
      { 0x6e864045,0x5303a365,0x9139efc1,0x45eae72a,0x6f31d54f,0x83bec646,
        0x6e958a6d,0x2fb4a86f,0x4ff44030,0x6760718e,0xe91ae0df,0x008117e3 } },
    /* 159 */
    { { 0x384310a2,0x5d5833ba,0x1fd6c9fc,0xbdfb4edc,0x849c4fb8,0xb9a4f102,
        0x581c1e1f,0xe5fb239a,0xd0a9746d,0xba44b2e7,0x3bd942b9,0x78f7b768 },
      { 0xc87607ae,0x076c8ca1,0xd5caaa7e,0x82b23c2e,0x2763e461,0x6a581f39,
        0x3886df11,0xca8a5e4a,0x264e7f22,0xc87e90cf,0x215cfcfc,0x04f74870 } },
    /* 160 */
    { { 0x141d161c,0x5285d116,0x93c4ed17,0x67cd2e0e,0x7c36187e,0x12c62a64,
        0xed2584ca,0xf5329539,0x42fbbd69,0xc4c777c4,0x1bdfc50a,0x107de776 },
      { 0xe96beebd,0x9976dcc5,0xa865a151,0xbe2aff95,0x9d8872af,0x0e0a9da1,
        0xa63c17cc,0x5e357a3d,0xe15cc67c,0xd31fdfd8,0x7970c6d8,0xc44bbefd } },
    /* 161 */
    { { 0x4c0c62f1,0x703f83e2,0x4e195572,0x9b1e28ee,0xfe26cced,0x6a82858b,
        0xc43638fa,0xd381c84b,0xa5ba43d8,0x94f72867,0x10b82743,0x3b4a783d },
      { 0x7576451e,0xee1ad7b5,0x14b6b5c8,0xc3d0b597,0xfcacc1b8,0x3dc30954,
        0x472c9d7b,0x55df110e,0x02f8a328,0x97c86ed7,0x88dc098f,0xd0433413 } },
    /* 162 */
    { { 0x2ca8f2fe,0x1a60d152,0x491bd41f,0x61640948,0x58dfe035,0x6dae29a5,
        0x278e4863,0x9a615bea,0x9ad7c8e5,0xbbdb4477,0x2ceac2fc,0x1c706630 },
      { 0x99699b4b,0x5e2b54c6,0x239e17e8,0xb509ca6d,0xea063a82,0x728165fe,
        0xb6a22e02,0x6b5e609d,0xb26ee1df,0x12813905,0x439491fa,0x07b9f722 } },
    /* 163 */
    { { 0x48ff4e49,0x1592ec14,0x6d644129,0x3e4e9f17,0x1156acc0,0x7acf8288,
        0xbb092b0b,0x5aa34ba8,0x7d38393d,0xcd0f9022,0xea4f8187,0x416724dd },
      { 0xc0139e73,0x3c4e641c,0x91e4d87d,0xe0fe46cf,0xcab61f8a,0xedb3c792,
        0xd3868753,0x4cb46de4,0x20f1098a,0xe449c21d,0xf5b8ea6e,0x5e5fd059 } },
    /* 164 */
    { { 0x75856031,0x7fcadd46,0xeaf2fbd0,0x89c7a4cd,0x7a87c480,0x1af523ce,
        0x61d9ae90,0xe5fc1095,0xbcdb95f5,0x3fb5864f,0xbb5b2c7d,0xbeb5188e },
      { 0x3ae65825,0x3d1563c3,0x0e57d641,0x116854c4,0x1942ebd3,0x11f73d34,
        0xc06955b3,0x24dc5904,0x995a0a62,0x8a0d4c83,0x5d577b7d,0xfb26b86d } },
    /* 165 */
    { { 0xc686ae17,0xc53108e7,0xd1c1da56,0x9090d739,0x9aec50ae,0x4583b013,
        0xa49a6ab2,0xdd9a088b,0xf382f850,0x28192eea,0xf5fe910e,0xcc8df756 },
      { 0x9cab7630,0x877823a3,0xfb8e7fc1,0x64984a9a,0x364bfc16,0x5448ef9c,
        0xc44e2a9a,0xbbb4f871,0x435c95e9,0x901a41ab,0xaaa50a06,0xc6c23e5f } },
    /* 166 */
    { { 0x9034d8dd,0xb78016c1,0x0b13e79b,0x856bb44b,0xb3241a05,0x85c6409a,
        0x2d78ed21,0x8d2fe19a,0x726eddf2,0xdcc7c26d,0x25104f04,0x3ccaff5f },
      { 0x6b21f843,0x397d7edc,0xe975de4c,0xda88e4dd,0x4f5ab69e,0x5273d396,
        0x9aae6cc0,0x537680e3,0x3e6f9461,0xf749cce5,0x957bffd3,0x021ddbd9 } },
    /* 167 */
    { { 0x777233cf,0x7b64585f,0x0942a6f0,0xfe6771f6,0xdfe6eef0,0x636aba7a,
        0x86038029,0x63bbeb56,0xde8fcf36,0xacee5842,0xd4a20524,0x48d9aa99 },
      { 0x0da5e57a,0xcff7a74c,0xe549d6c9,0xc232593c,0xf0f2287b,0x68504bcc,
        0xbc8360b5,0x6d7d098d,0x5b402f41,0xeac5f149,0xb87d1bf1,0x61936f11 } },
    /* 168 */
    { { 0xb8153a9d,0xaa9da167,0x9e83ecf0,0xa49fe3ac,0x1b661384,0x14c18f8e,
        0x38434de1,0x61c24dab,0x283dae96,0x3d973c3a,0x82754fc9,0xc99baa01 },
      { 0x4c26b1e3,0x477d198f,0xa7516202,0x12e8e186,0x362addfa,0x386e52f6,
        0xc3962853,0x31e8f695,0x6aaedb60,0xdec2af13,0x29cf74ac,0xfcfdb4c6 } },
    /* 169 */
    { { 0xcca40298,0x6b3ee958,0xf2f5d195,0xc3878153,0xed2eae5b,0x0c565630,
        0x3a697cf2,0xd089b37e,0xad5029ea,0xc2ed2ac7,0x0f0dda6a,0x7e5cdfad },
      { 0xd9b86202,0xf98426df,0x4335e054,0xed1960b1,0x3f14639e,0x1fdb0246,
        0x0db6c670,0x17f709c3,0x773421e1,0xbfc687ae,0x26c1a8ac,0x13fefc4a } },
    /* 170 */
    { { 0x7ffa0a5f,0xe361a198,0xc63fe109,0xf4b26102,0x6c74e111,0x264acbc5,
        0x77abebaf,0x4af445fa,0x24cddb75,0x448c4fdd,0x44506eea,0x0b13157d },
      { 0x72e9993d,0x22a6b159,0x85e5ecbe,0x2c3c57e4,0xfd83e1a1,0xa673560b,
        0xc3b8c83b,0x6be23f82,0x40bbe38e,0x40b13a96,0xad17399b,0x66eea033 } },
    /* 171 */
    { { 0xb4c6c693,0x49fc6e95,0x36af7d38,0xefc735de,0x35fe42fc,0xe053343d,
        0x6a9ab7c3,0xf0aa427c,0x4a0fcb24,0xc79f0436,0x93ebbc50,0x16287243 },
      { 0x16927e1e,0x5c3d6bd0,0x673b984c,0x40158ed2,0x4cd48b9a,0xa7f86fc8,
        0x60ea282d,0x1643eda6,0xe2a1beed,0x45b393ea,0x19571a94,0x664c839e } },
    /* 172 */
    { { 0x27eeaf94,0x57745750,0xea99e1e7,0x2875c925,0x5086adea,0xc127e7ba,
        0x86fe424f,0x765252a0,0x2b6c0281,0x1143cc6c,0xd671312d,0xc9bb2989 },
      { 0x51acb0a5,0x880c337c,0xd3c60f78,0xa3710915,0x9262b6ed,0x496113c0,
        0x9ce48182,0x5d25d9f8,0xb3813586,0x53b6ad72,0x4c0e159c,0x0ea3bebc } },
    /* 173 */
    { { 0xc5e49bea,0xcaba450a,0x7c05da59,0x684e5415,0xde7ac36c,0xa2e9cab9,
        0x2e6f957b,0x4ca79b5f,0x09b817b1,0xef7b0247,0x7d89df0f,0xeb304990 },
      { 0x46fe5096,0x508f7307,0x2e04eaaf,0x695810e8,0x3512f76c,0x88ef1bd9,
        0x3ebca06b,0x77661351,0xccf158b7,0xf7d4863a,0x94ee57da,0xb2a81e44 } },
    /* 174 */
    { { 0x6d53e6ba,0xff288e5b,0x14484ea2,0xa90de1a9,0xed33c8ec,0x2fadb60c,
        0x28b66a40,0x579d6ef3,0xec24372d,0x4f2dd6dd,0x1d66ec7d,0xe9e33fc9 },
      { 0x039eab6e,0x110899d2,0x3e97bb5e,0xa31a667a,0xcfdce68e,0x6200166d,
        0x5137d54b,0xbe83ebae,0x4800acdf,0x085f7d87,0x0c6f8c86,0xcf4ab133 } },
    /* 175 */
    { { 0x931e08fb,0x03f65845,0x1506e2c0,0x6438551e,0x9c36961f,0x5791f0dc,
        0xe3dcc916,0x68107b29,0xf495d2ca,0x83242374,0x6ee5895b,0xd8cfb663 },
      { 0xa0349b1b,0x525e0f16,0x4a0fab86,0x33cd2c6c,0x2af8dda9,0x46c12ee8,
        0x71e97ad3,0x7cc424ba,0x37621eb0,0x69766ddf,0xa5f0d390,0x95565f56 } },
    /* 176 */
    { { 0x1a0f5e94,0xe0e7bbf2,0x1d82d327,0xf771e115,0xceb111fa,0x10033e3d,
        0xd3426638,0xd269744d,0x00d01ef6,0xbdf2d9da,0xa049ceaf,0x1cb80c71 },
      { 0x9e21c677,0x17f18328,0x19c8f98b,0x6452af05,0x80b67997,0x35b9c5f7,
        0x40f8f3d4,0x5c2e1cbe,0x66d667ca,0x43f91656,0xcf9d6e79,0x9faaa059 } },
    /* 177 */
    { { 0x0a078fe6,0x8ad24618,0x464fd1dd,0xf6cc73e6,0xc3e37448,0x4d2ce34d,
        0xe3271b5f,0x624950c5,0xefc5af72,0x62910f5e,0xaa132bc6,0x8b585bf8 },
      { 0xa839327f,0x11723985,0x4aac252f,0x34e2d27d,0x6296cc4e,0x402f59ef,
        0x47053de9,0x00ae055c,0x28b4f09b,0xfc22a972,0xfa0c180e,0xa9e86264 } },
    /* 178 */
    { { 0xbc310ecc,0x0b7b6224,0x67fa14ed,0x8a1a74f1,0x7214395c,0x87dd0960,
        0xf5c91128,0xdf1b3d09,0x86b264a8,0x39ff23c6,0x3e58d4c5,0xdc2d49d0 },
      { 0xa9d6f501,0x2152b7d3,0xc04094f7,0xf4c32e24,0xd938990f,0xc6366596,
        0x94fb207f,0x084d078f,0x328594cb,0xfd99f1d7,0xcb2d96b3,0x36defa64 } },
    /* 179 */
    { { 0x13ed7cbe,0x4619b781,0x9784bd0e,0x95e50015,0x2c7705fe,0x2a32251c,
        0x5f0dd083,0xa376af99,0x0361a45b,0x55425c6c,0x1f291e7b,0x812d2cef },
      { 0x5fd94972,0xccf581a0,0xe56dc383,0x26e20e39,0x63dbfbf0,0x0093685d,
        0x36b8c575,0x1fc164cc,0x390ef5e7,0xb9c5ab81,0x26908c66,0x40086beb } },
    /* 180 */
    { { 0x37e3c115,0xe5e54f79,0xc1445a8a,0x69b8ee8c,0xb7659709,0x79aedff2,
        0x1b46fbe6,0xe288e163,0xd18d7bb7,0xdb4844f0,0x48aa6424,0xe0ea23d0 },
      { 0xf3d80a73,0x714c0e4e,0x3bd64f98,0x87a0aa9e,0x2ec63080,0x8844b8a8,
        0x255d81a3,0xe0ac9c30,0x455397fc,0x86151237,0x2f820155,0x0b979464 } },
    /* 181 */
    { { 0x4ae03080,0x127a255a,0x580a89fb,0x232306b4,0x6416f539,0x04e8cd6a,
        0x13b02a0e,0xaeb70dee,0x4c09684a,0xa3038cf8,0x28e433ee,0xa710ec3c },
      { 0x681b1f7d,0x77a72567,0x2fc28170,0x86fbce95,0xf5735ac8,0xd3408683,
        0x6bd68e93,0x3a324e2a,0xc027d155,0x7ec74353,0xd4427177,0xab60354c } },
    /* 182 */
    { { 0xef4c209d,0x32a5342a,0x08d62704,0x2ba75274,0xc825d5fe,0x4bb4af6f,
        0xd28e7ff1,0x1c3919ce,0xde0340f6,0x1dfc2fdc,0x29f33ba9,0xc6580baf },
      { 0x41d442cb,0xae121e75,0x3a4724e4,0x4c7727fd,0x524f3474,0xe556d6a4,
        0x785642a2,0x87e13cc7,0xa17845fd,0x182efbb1,0x4e144857,0xdcec0cf1 } },
    /* 183 */
    { { 0xe9539819,0x1cb89541,0x9d94dbf1,0xc8cb3b4f,0x417da578,0x1d353f63,
        0x8053a09e,0xb7a697fb,0xc35d8b78,0x8d841731,0xb656a7a9,0x85748d6f },
      { 0xc1859c5d,0x1fd03947,0x535d22a2,0x6ce965c1,0x0ca3aadc,0x1966a13e,
        0x4fb14eff,0x9802e41d,0x76dd3fcd,0xa9048cbb,0xe9455bba,0x89b182b5 } },
    /* 184 */
    { { 0x43360710,0xd777ad6a,0x55e9936b,0x841287ef,0x04a21b24,0xbaf5c670,
        0x35ad86f1,0xf2c0725f,0xc707e72e,0x338fa650,0xd8883e52,0x2bf8ed2e },
      { 0xb56e0d6a,0xb0212cf4,0x6843290c,0x50537e12,0x98b3dc6f,0xd8b184a1,
        0x0210b722,0xd2be9a35,0x559781ee,0x407406db,0x0bc18534,0x5a78d591 } },
    /* 185 */
    { { 0xd748b02c,0x4d57aa2a,0xa12b3b95,0xbe5b3451,0x64711258,0xadca7a45,
        0x322153db,0x597e091a,0x32eb1eab,0xf3271006,0x2873f301,0xbd9adcba },
      { 0x38543f7f,0xd1dc79d1,0x921b1fef,0x00022092,0x1e5df8ed,0x86db3ef5,
        0x9e6b944a,0x888cae04,0x791a32b4,0x71bd29ec,0xa6d1c13e,0xd3516206 } },
    /* 186 */
    { { 0x55924f43,0x2ef6b952,0x4f9de8d5,0xd2f401ae,0xadc68042,0xfc73e8d7,
        0x0d9d1bb4,0x627ea70c,0xbbf35679,0xc3bb3e3e,0xd882dee4,0x7e8a254a },
      { 0xb5924407,0x08906f50,0xa1ad444a,0xf14a0e61,0x65f3738e,0xaa0efa21,
        0xae71f161,0xd60c7dd6,0xf175894d,0x9e8390fa,0x149f4c00,0xd115cd20 } },
    /* 187 */
    { { 0xa52abf77,0x2f2e2c1d,0x54232568,0xc2a0dca5,0x54966dcc,0xed423ea2,
        0xcd0dd039,0xe48c93c7,0x176405c7,0x1e54a225,0x70d58f2e,0x1efb5b16 },
      { 0x94fb1471,0xa751f9d9,0x67d2941d,0xfdb31e1f,0x53733698,0xa6c74eb2,
        0x89a0f64a,0xd3155d11,0xa4b8d2b6,0x4414cfe4,0xf7a8e9e3,0x8d5a4be8 } },
    /* 188 */
    { { 0x52669e98,0x5c96b4d4,0x8fd42a03,0x4547f922,0xd285174e,0xcf5c1319,
        0x064bffa0,0x805cd1ae,0x246d27e7,0x50e8bc4f,0xd5781e11,0xf89ef98f },
      { 0xdee0b63f,0xb4ff95f6,0x222663a4,0xad850047,0x4d23ce9c,0x02691860,
        0x50019f59,0x3e5309ce,0x69a508ae,0x27e6f722,0x267ba52c,0xe9376652 } },
    /* 189 */
    { { 0xc0368708,0xa04d289c,0x5e306e1d,0xc458872f,0x33112fea,0x76fa23de,
        0x6efde42e,0x718e3974,0x1d206091,0xf0c98cdc,0x14a71987,0x5fa3ca62 },
      { 0xdcaa9f2a,0xeee8188b,0x589a860d,0x312cc732,0xc63aeb1f,0xf9808dd6,
        0x4ea62b53,0x70fd43db,0x890b6e97,0x2c2bfe34,0xfa426aa6,0x105f863c } },
    /* 190 */
    { { 0xb38059ad,0x0b29795d,0x90647ea0,0x5686b77e,0xdb473a3e,0xeff0470e,
        0xf9b6d1e2,0x278d2340,0xbd594ec7,0xebbff95b,0xd3a7f23d,0xf4b72334 },
      { 0xa5a83f0b,0x2a285980,0x9716a8b3,0x0786c41a,0x22511812,0x138901bd,
        0xe2fede6e,0xd1b55221,0xdf4eb590,0x0806e264,0x762e462e,0x6c4c897e } },
    /* 191 */
    { { 0xb4b41d9d,0xd10b905f,0x4523a65b,0x826ca466,0xb699fa37,0x535bbd13,
        0x73bc8f90,0x5b9933d7,0xcd2118ad,0x9332d61f,0xd4a65fd0,0x158c693e },
      { 0xe6806e63,0x4ddfb2a8,0xb5de651b,0xe31ed3ec,0x819bc69a,0xf9460e51,
        0x2c76b1f8,0x6229c0d6,0x901970a3,0xbb78f231,0x9cee72b8,0x31f3820f } },
    /* 192 */
    { { 0xc09e1c72,0xe931caf2,0x12990cf4,0x0715f298,0x943262d8,0x33aad81d,
        0x73048d3f,0x5d292b7a,0xdc7415f6,0xb152aaa4,0x0fd19587,0xc3d10fd9 },
      { 0x75ddadd0,0xf76b35c5,0x1e7b694c,0x9f5f4a51,0xc0663025,0x2f1ab7eb,
        0x920260b0,0x01c9cc87,0x05d39da6,0xc4b1f61a,0xeb4a9c4e,0x6dcd76c4 } },
    /* 193 */
    { { 0xfdc83f01,0x0ba0916f,0x9553e4f9,0x354c8b44,0xffc5e622,0xa6cc511a,
        0xe95be787,0xb954726a,0x75b41a62,0xcb048115,0xebfde989,0xfa2ae6cd },
      { 0x0f24659a,0x6376bbc7,0x4c289c43,0x13a999fd,0xec9abd8b,0xc7134184,
        0xa789ab04,0x28c02bf6,0xd3e526ec,0xff841ebc,0x640893a8,0x442b191e } },
    /* 194 */
    { { 0xfa2b6e20,0x4cac6c62,0xf6d69861,0x97f29e9b,0xbc96d12d,0x228ab1db,
        0x5e8e108d,0x6eb91327,0x40771245,0xd4b3d4d1,0xca8a803a,0x61b20623 },
      { 0xa6a560b1,0x2c2f3b41,0x3859fcf4,0x879e1d40,0x024dbfc3,0x7cdb5145,
        0x3bfa5315,0x55d08f15,0xaa93823a,0x2f57d773,0xc6a2c9a2,0xa97f259c } },
    /* 195 */
    { { 0xe58edbbb,0xc306317b,0x79dfdf13,0x25ade51c,0x16d83dd6,0x6b5beaf1,
        0x1dd8f925,0xe8038a44,0xb2a87b6b,0x7f00143c,0xf5b438de,0xa885d00d },
      { 0xcf9e48bd,0xe9f76790,0xa5162768,0xf0bdf9f0,0xad7b57cb,0x0436709f,
        0xf7c15db7,0x7e151c12,0x5d90ee3b,0x3514f022,0x2c361a8d,0x2e84e803 } },
    /* 196 */
    { { 0x563ec8d8,0x2277607d,0xe3934cb7,0xa661811f,0xf58fd5de,0x3ca72e7a,
        0x62294c6a,0x7989da04,0xf6bbefe9,0x88b3708b,0x53ed7c82,0x0d524cf7 },
      { 0x2f30c073,0x69f699ca,0x9dc1dcf3,0xf0fa264b,0x05f0aaf6,0x44ca4568,
        0xd19b9baf,0x0f5b23c7,0xeabd1107,0x39193f41,0x2a7c9b83,0x9e3e10ad } },
    /* 197 */
    { { 0xd4ae972f,0xa90824f0,0xc6e846e7,0x43eef02b,0x29d2160a,0x7e460612,
        0xfe604e91,0x29a178ac,0x4eb184b2,0x23056f04,0xeb54cdf4,0x4fcad55f },
      { 0xae728d15,0xa0ff96f3,0xc6a00331,0x8a2680c6,0x7ee52556,0x5f84cae0,
        0xc5a65dad,0x5e462c3a,0xe2d23f4f,0x5d2b81df,0xc5b1eb07,0x6e47301b } },
    /* 198 */
    { { 0xaf8219b9,0x77411d68,0x51b1907a,0xcb883ce6,0x101383b5,0x25c87e57,
        0x982f970d,0x9c7d9859,0x118305d2,0xaa6abca5,0x9013a5db,0x725fed2f },
      { 0xababd109,0x487cdbaf,0x87586528,0xc0f8cf56,0x8ad58254,0xa02591e6,
        0xdebbd526,0xc071b1d1,0x961e7e31,0x927dfe8b,0x9263dfe1,0x55f895f9 } },
    /* 199 */
    { { 0xb175645b,0xf899b00d,0xb65b4b92,0x51f3a627,0xb67399ef,0xa2f3ac8d,
        0xe400bc20,0xe717867f,0x1967b952,0x42cc9020,0x3ecd1de1,0x3d596751 },
      { 0xdb979775,0xd41ebcde,0x6a2e7e88,0x99ba61bc,0x321504f2,0x039149a5,
        0x27ba2fad,0xe7dc2314,0xb57d8368,0x9f556308,0x57da80a7,0x2b6d16c9 } },
    /* 200 */
    { { 0x279ad982,0x84af5e76,0x9c8b81a6,0x9bb4c92d,0x0e698e67,0xd79ad44e,
        0x265fc167,0xe8be9048,0x0c3a4ccc,0xf135f7e6,0xb8863a33,0xa0a10d38 },
      { 0xd386efd9,0xe197247c,0xb52346c2,0x0eefd3f9,0x78607bc8,0xc22415f9,
        0x508674ce,0xa2a8f862,0xc8c9d607,0xa72ad09e,0x50fa764f,0xcd9f0ede } },
    /* 201 */
    { { 0xd1a46d4d,0x063391c7,0x9eb01693,0x2df51c11,0x849e83de,0xc5849800,
        0x8ad08382,0x48fd09aa,0xaa742736,0xa405d873,0xe1f9600c,0xee49e61e },
      { 0x48c76f73,0xd76676be,0x01274b2a,0xd9c100f6,0x83f8718d,0x110bb67c,
        0x02fc0d73,0xec85a420,0x744656ad,0xc0449e1e,0x37d9939b,0x28ce7376 } },
    /* 202 */
    { { 0x44544ac7,0x97e9af72,0xba010426,0xf2c658d5,0xfb3adfbd,0x732dec39,
        0xa2df0b07,0xd12faf91,0x2171e208,0x8ac26725,0x5b24fa54,0xf820cdc8 },
      { 0x94f4cf77,0x307a6eea,0x944a33c6,0x18c783d2,0x0b741ac5,0x4b939d4c,
        0x3ffbb6e4,0x1d7acd15,0x7a255e44,0x06a24858,0xce336d50,0x14fbc494 } },
    /* 203 */
    { { 0x51584e3c,0x9b920c0c,0xf7e54027,0xc7733c59,0x88422bbe,0xe24ce139,
        0x523bd6ab,0x11ada812,0xb88e6def,0xde068800,0xfe8c582d,0x7b872671 },
      { 0x7de53510,0x4e746f28,0xf7971968,0x492f8b99,0x7d928ac2,0x1ec80bc7,
        0x432eb1b5,0xb3913e48,0x32028f6e,0xad084866,0x8fc2f38b,0x122bb835 } },
    /* 204 */
    { { 0x3b0b29c3,0x0a9f3b1e,0x4fa44151,0x837b6432,0x17b28ea7,0xb9905c92,
        0x98451750,0xf39bc937,0xce8b6da1,0xcd383c24,0x010620b2,0x299f57db },
      { 0x58afdce3,0x7b6ac396,0x3d05ef47,0xa15206b3,0xb9bb02ff,0xa0ae37e2,
        0x9db3964c,0x107760ab,0x67954bea,0xe29de9a0,0x431c3f82,0x446a1ad8 } },
    /* 205 */
    { { 0x5c6b8195,0xc6fecea0,0xf49e71b9,0xd744a7c5,0x177a7ae7,0xa8e96acc,
        0x358773a7,0x1a05746c,0x37567369,0xa4162146,0x87d1c971,0xaa0217f7 },
      { 0x77fd3226,0x61e9d158,0xe4f600be,0x0f6f2304,0x7a6dff07,0xa9c4cebc,
        0x09f12a24,0xd15afa01,0x8c863ee9,0x2bbadb22,0xe5eb8c78,0xa28290e4 } },
    /* 206 */
    { { 0x3e9de330,0x55b87fa0,0x195c145b,0x12b26066,0xa920bef0,0xe08536e0,
        0x4d195adc,0x7bff6f2c,0x945f4187,0x7f319e9d,0xf892ce47,0xf9848863 },
      { 0x4fe37657,0xd0efc1d3,0x5cf0e45a,0x3c58de82,0x8b0ccbbe,0x626ad21a,
        0xaf952fc5,0xd2a31208,0xeb437357,0x81791995,0x98e95d4f,0x5f19d30f } },
    /* 207 */
    { { 0x0e6865bb,0x72e83d9a,0xf63456a6,0x22f5af3b,0x463c8d9e,0x409e9c73,
        0xdfe6970e,0x40e9e578,0x711b91ca,0x876b6efa,0x942625a3,0x895512cf },
      { 0xcb4e462b,0x84c8eda8,0x4412e7c8,0x84c0154a,0xceb7b71f,0x04325db1,
        0x66f70877,0x1537dde3,0x1992b9ac,0xf3a09399,0xd498ae77,0xa7316606 } },
    /* 208 */
    { { 0xcad260f5,0x13990d2f,0xeec0e8c0,0x76c3be29,0x0f7bd7d5,0x7dc5bee0,
        0xefebda4b,0x9be167d2,0x9122b87e,0xcce3dde6,0x82b5415c,0x75a28b09 },
      { 0xe84607a6,0xf6810bcd,0x6f4dbf0d,0xc6d58128,0x1b4dafeb,0xfead577d,
        0x066b28eb,0x9bc440b2,0x8b17e84b,0x53f1da97,0xcda9a575,0x0459504b } },
    /* 209 */
    { { 0x329e5836,0x13e39a02,0xf717269d,0x2c9e7d51,0xf26c963b,0xc5ac58d6,
        0x79967bf5,0x3b0c6c43,0x55908d9d,0x60bbea3f,0xf07c9ad1,0xd84811e7 },
      { 0x5bd20e4a,0xfe7609a7,0x0a70baa8,0xe4325dd2,0xb3600386,0x3711f370,
        0xd0924302,0x97f9562f,0x4acc4436,0x040dc0c3,0xde79cdd4,0xfd6d725c } },
    /* 210 */
    { { 0xcf13eafb,0xb3efd0e3,0x5aa0ae5f,0x21009cbb,0x79022279,0xe480c553,
        0xb2fc9a6d,0x755cf334,0x07096ae7,0x8564a5bf,0xbd238139,0xddd649d0 },
      { 0x8a045041,0xd0de10b1,0xc957d572,0x6e05b413,0x4e0fb25c,0x5c5ff806,
        0x641162fb,0xd933179b,0xe57439f9,0x42d48485,0x8a8d72aa,0x70c5bd0a } },
    /* 211 */
    { { 0x97bdf646,0xa7671738,0xab329f7c,0xaa1485b4,0xf8f25fdf,0xce3e11d6,
        0xc6221824,0x76a3fc7e,0xf3924740,0x045f281f,0x96d13a9a,0x24557d4e },
      { 0xdd4c27cd,0x875c804b,0x0f5c7fea,0x11c5f0f4,0xdc55ff7e,0xac8c880b,
        0x1103f101,0x2acddec5,0xf99faa89,0x38341a21,0xce9d6b57,0xc7b67a2c } },
    /* 212 */
    { { 0x8e357586,0x9a0d724f,0xdf648da0,0x1d7f4ff5,0xfdee62a5,0x9c3e6c9b,
        0x0389b372,0x0499cef0,0x98eab879,0xe904050d,0x6c051617,0xe8eef1b6 },
      { 0xc37e3ca9,0xebf5bfeb,0xa4e0b91d,0x7c5e946d,0x2c4bea28,0x79097314,
        0xee67b2b7,0x81f6c109,0xdafc5ede,0xaf237d9b,0x2abb04c7,0xd2e60201 } },
    /* 213 */
    { { 0x8a4f57bf,0x6156060c,0xff11182a,0xf9758696,0x6296ef00,0x8336773c,
        0xff666899,0x9c054bce,0x719cd11c,0xd6a11611,0xdbe1acfa,0x9824a641 },
      { 0xba89fd01,0x0b7b7a5f,0x889f79d8,0xf8d3b809,0xf578285c,0xc5e1ea08,
        0xae6d8288,0x7ac74536,0x7521ef5f,0x5d37a200,0xb260a25d,0x5ecc4184 } },
    /* 214 */
    { { 0xa708c8d3,0xddcebb19,0xc63f81ec,0xe63ed04f,0x11873f95,0xd045f5a0,
        0x79f276d5,0x3b5ad544,0x425ae5b3,0x81272a3d,0x10ce1605,0x8bfeb501 },
      { 0x888228bf,0x4233809c,0xb2aff7df,0x4bd82acf,0x0cbd4a7f,0x9c68f180,
        0x6b44323d,0xfcd77124,0x891db957,0x60c0fcf6,0x04da8f7f,0xcfbb4d89 } },
    /* 215 */
    { { 0x3b26139a,0x9a6a5df9,0xb2cc7eb8,0x3e076a83,0x5a964bcd,0x47a8e82d,
        0xb9278d6b,0x8a4e2a39,0xe4443549,0x93506c98,0xf1e0d566,0x06497a8f },
      { 0x2b1efa05,0x3dee8d99,0x45393e33,0x2da63ca8,0xcf0579ad,0xa4af7277,
        0x3236d8ea,0xaf4b4639,0x32b617f5,0x6ccad95b,0xb88bb124,0xce76d8b8 } },
    /* 216 */
    { { 0x083843dc,0x63d2537a,0x1e4153b4,0x89eb3514,0xea9afc94,0x5175ebc4,
        0x8ed1aed7,0x7a652580,0xd85e8297,0x67295611,0xb584b73d,0x8dd2d68b },
      { 0x0133c3a4,0x237139e6,0x4bd278ea,0x9de838ab,0xc062fcd9,0xe829b072,
        0x63ba8706,0x70730d4f,0xd3cd05ec,0x6080483f,0x0c85f84d,0x872ab5b8 } },
    /* 217 */
    { { 0x999d4d49,0xfc0776d3,0xec3f45e7,0xa3eb59de,0x0dae1fc1,0xbc990e44,
        0xa15371ff,0x33596b1e,0x9bc7ab25,0xd447dcb2,0x35979582,0xcd5b63e9 },
      { 0x77d1ff11,0xae3366fa,0xedee6903,0x59f28f05,0xa4433bf2,0x6f43fed1,
        0xdf9ce00e,0x15409c9b,0xaca9c5dc,0x21b5cded,0x82d7bdb4,0xf9f33595 } },
    /* 218 */
    { { 0x9422c792,0x95944378,0xc958b8bf,0x239ea923,0xdf076541,0x4b61a247,
        0xbb9fc544,0x4d29ce85,0x0b424559,0x9a692a67,0x0e486900,0x6e0ca5a0 },
      { 0x85b3bece,0x6b79a782,0xc61f9892,0x41f35e39,0xae747f82,0xff82099a,
        0xd0ca59d6,0x58c8ae3f,0x99406b5f,0x4ac930e2,0x9df24243,0x2ce04eb9 } },
    /* 219 */
    { { 0x1ac37b82,0x4366b994,0x25b04d83,0xff0c728d,0x19c47b7c,0x1f551361,
        0xbeff13e7,0xdbf2d5ed,0xe12a683d,0xf78efd51,0x989cf9c4,0x82cd85b9 },
      { 0xe0cb5d37,0xe23c6db6,0x72ee1a15,0x818aeebd,0x28771b14,0x8212aafd,
        0x1def817d,0x7bc221d9,0x9445c51f,0xdac403a2,0x12c3746b,0x711b0517 } },
    /* 220 */
    { { 0x5ea99ecc,0x0ed9ed48,0xb8cab5e1,0xf799500d,0xb570cbdc,0xa8ec87dc,
        0xd35dfaec,0x52cfb2c2,0x6e4d80a4,0x8d31fae2,0xdcdeabe5,0xe6a37dc9 },
      { 0x1deca452,0x5d365a34,0x0d68b44e,0x09a5f8a5,0xa60744b1,0x59238ea5,
        0xbb4249e9,0xf2fedc0d,0xa909b2e3,0xe395c74e,0x39388250,0xe156d1a5 } },
    /* 221 */
    { { 0x47181ae9,0xd796b3d0,0x44197808,0xbaf44ba8,0x34cf3fac,0xe6933094,
        0xc3bd5c46,0x41aa6ade,0xeed947c6,0x4fda75d8,0x9ea5a525,0xacd9d412 },
      { 0xd430301b,0x65cc55a3,0x7b52ea49,0x3c9a5bcf,0x159507f0,0x22d319cf,
        0xde74a8dd,0x2ee0b9b5,0x877ac2b6,0x20c26a1e,0x92e7c314,0x387d73da } },
    /* 222 */
    { { 0x8cd3fdac,0x13c4833e,0x332e5b8e,0x76fcd473,0xe2fe1fd3,0xff671b4b,
        0x5d98d8ec,0x4d734e8b,0x514bbc11,0xb1ead3c6,0x7b390494,0xd14ca858 },
      { 0x5d2d37e9,0x95a443af,0x00464622,0x73c6ea73,0x15755044,0xa44aeb4b,
        0xfab58fee,0xba3f8575,0xdc680a6f,0x9779dbc9,0x7b37ddfc,0xe1ee5f5a } },
    /* 223 */
    { { 0x12d29f46,0xcd0b4648,0x0ed53137,0x93295b0b,0x80bef6c9,0xbfe26094,
        0x54248b00,0xa6565788,0x80e7f9c4,0x69c43fca,0xbe141ea1,0x2190837b },
      { 0xa1b26cfb,0x875e159a,0x7affe852,0x90ca9f87,0x92ca598e,0x15e6550d,
        0x1938ad11,0xe3e0945d,0x366ef937,0xef7636bb,0xb39869e5,0xb6034d0b } },
    /* 224 */
    { { 0x26d8356e,0x4d255e30,0xd314626f,0xf83666ed,0xd0c8ed64,0x421ddf61,
        0x26677b61,0x96e473c5,0x9e9b18b3,0xdad4af7e,0xa9393f75,0xfceffd4a },
      { 0x11c731d5,0x843138a1,0xb2f141d9,0x05bcb3a1,0x617b7671,0x20e1fa95,
        0x88ccec7b,0xbefce812,0x90f1b568,0x582073dc,0x1f055cb7,0xf572261a } },
    /* 225 */
    { { 0x36973088,0xf3148277,0x86a9f980,0xc008e708,0xe046c261,0x1b795947,
        0xca76bca0,0xdf1e6a7d,0x71acddf0,0xabafd886,0x1364d8f4,0xff7054d9 },
      { 0xe2260594,0x2cf63547,0xd73b277e,0x468a5372,0xef9bd35e,0xc7419e24,
        0x24043cc3,0x2b4a1c20,0x890b39cd,0xa28f047a,0x46f9a2e3,0xdca2cea1 } },
    /* 226 */
    { { 0x53277538,0xab788736,0xcf697738,0xa734e225,0x6b22e2c1,0x66ee1d1e,
        0xebe1d212,0x2c615389,0x02bb0766,0xf36cad40,0x3e64f207,0x120885c3 },
      { 0x90fbfec2,0x59e77d56,0xd7a574ae,0xf9e781aa,0x5d045e53,0x801410b0,
        0xa91b5f0e,0xd3b5f0aa,0x7fbb3521,0xb3d1df00,0xc72bee9a,0x11c4b33e } },
    /* 227 */
    { { 0x83c3a7f3,0xd32b9832,0x88d8a354,0x8083abcf,0x50f4ec5a,0xdeb16404,
        0x641e2907,0x18d747f0,0xf1bbf03e,0x4e8978ae,0x88a0cd89,0x932447dc },
      { 0xcf3d5897,0x561e0feb,0x13600e6d,0xfc3a682f,0xd16a6b73,0xc78b9d73,
        0xd29bf580,0xe713fede,0x08d69e5c,0x0a225223,0x1ff7fda4,0x3a924a57 } },
    /* 228 */
    { { 0xb4093bee,0xfb64554c,0xa58c6ec0,0xa6d65a25,0x43d0ed37,0x4126994d,
        0x55152d44,0xa5689a51,0x284caa8d,0xb8e5ea8c,0xd1f25538,0x33f05d4f },
      { 0x1b615d6e,0xe0fdfe09,0x705507da,0x2ded7e8f,0x17bbcc80,0xdd5631e5,
        0x267fd11f,0x4f87453e,0xff89d62d,0xc6da723f,0xe3cda21d,0x55cbcae2 } },
    /* 229 */
    { { 0x6b4e84f3,0x336bc94e,0x4ef72c35,0x72863031,0xeeb57f99,0x6d85fdee,
        0xa42ece1b,0x7f4e3272,0x36f0320a,0x7f86cbb5,0x923331e6,0xf09b6a2b },
      { 0x56778435,0x21d3ecf1,0x8323b2d2,0x2977ba99,0x1704bc0f,0x6a1b57fb,
        0x389f048a,0xd777cf8b,0xac6b42cd,0x9ce2174f,0x09e6c55a,0x404e2bff } },
    /* 230 */
    { { 0x204c5ddb,0x9b9b135e,0x3eff550e,0x9dbfe044,0xec3be0f6,0x35eab4bf,
        0x0a43e56f,0x8b4c3f0d,0x0e73f9b3,0x4c1c6673,0x2c78c905,0x92ed38bd },
      { 0xa386e27c,0xc7003f6a,0xaced8507,0xb9c4f46f,0x59df5464,0xea024ec8,
        0x429572ea,0x4af96152,0xe1fc1194,0x279cd5e2,0x281e358c,0xaa376a03 } },
    /* 231 */
    { { 0x3cdbc95c,0x07859223,0xef2e337a,0xaae1aa6a,0x472a8544,0xc040108d,
        0x8d037b7d,0x80c853e6,0x8c7eee24,0xd221315c,0x8ee47752,0x195d3856 },
      { 0xdacd7fbe,0xd4b1ba03,0xd3e0c52b,0x4b5ac61e,0x6aab7b52,0x68d3c052,
        0x660e3fea,0xf0d7248c,0x3145efb4,0xafdb3f89,0x8f40936d,0xa73fd9a3 } },
    /* 232 */
    { { 0xbb1b17ce,0x891b9ef3,0xc6127f31,0x14023667,0x305521fd,0x12b2e58d,
        0xe3508088,0x3a47e449,0xff751507,0xe49fc84b,0x5310d16e,0x4023f722 },
      { 0xb73399fa,0xa608e5ed,0xd532aa3e,0xf12632d8,0x845e8415,0x13a2758e,
        0x1fc2d861,0xae4b6f85,0x339d02f2,0x3879f5b1,0x80d99ebd,0x446d22a6 } },
    /* 233 */
    { { 0x4be164f1,0x0f502302,0x88b81920,0x8d09d2d6,0x984aceff,0x514056f1,
        0x75e9e80d,0xa5c4ddf0,0xdf496a93,0x38cb47e6,0x38df6bf7,0x899e1d6b },
      { 0xb59eb2a6,0x69e87e88,0x9b47f38b,0x280d9d63,0x3654e955,0x599411ea,
        0x969aa581,0xcf8dd4fd,0x530742a7,0xff5c2baf,0x1a373085,0xa4391536 } },
    /* 234 */
    { { 0xa8a4bdd2,0x6ace72a3,0xb68ef702,0xc656cdd1,0x90c4dad8,0xd4a33e7e,
        0x9d951c50,0x4aece08a,0x085d68e6,0xea8005ae,0x6f7502b8,0xfdd7a7d7 },
      { 0x98d6fa45,0xce6fb0a6,0x1104eb8c,0x228f8672,0xda09d7dc,0xd23d8787,
        0x2ae93065,0x5521428b,0xea56c366,0x95faba3d,0x0a88aca5,0xedbe5039 } },
    /* 235 */
    { { 0xbfb26c82,0xd64da0ad,0x952c2f9c,0xe5d70b3c,0xf7e77f68,0xf5e8f365,
        0x08f2d695,0x7234e002,0xd12e7be6,0xfaf900ee,0x4acf734e,0x27dc6934 },
      { 0xc260a46a,0x80e4ff5e,0x2dc31c28,0x7da5ebce,0xca69f552,0x485c5d73,
        0x69cc84c2,0xcdfb6b29,0xed6d4eca,0x031c5afe,0x22247637,0xc7bbf4c8 } },
    /* 236 */
    { { 0x49fe01b2,0x9d5b72c7,0x793a91b8,0x34785186,0xcf460438,0xa3ba3c54,
        0x3ab21b6f,0x73e8e43d,0xbe57b8ab,0x50cde8e0,0xdd204264,0x6488b3a7 },
      { 0xdddc4582,0xa9e398b3,0x5bec46fe,0x1698c1a9,0x156d3843,0x7f1446ef,
        0x770329a2,0x3fd25dd8,0x2c710668,0x05b1221a,0xa72ee6cf,0x65b2dc2a } },
    /* 237 */
    { { 0xcd021d63,0x21a885f7,0xfea61f08,0x3f344b15,0xc5cf73e6,0xad5ba6dd,
        0x227a8b23,0x154d0d8f,0xdc559311,0x9b74373c,0x98620fa1,0x4feab715 },
      { 0x7d9ec924,0x5098938e,0x6d47e550,0x84d54a5e,0x1b617506,0x1a2d1bdc,
        0x615868a4,0x99fe1782,0x3005a924,0x171da780,0x7d8f79b6,0xa70bf5ed } },
    /* 238 */
    { { 0xfe2216c5,0x0bc1250d,0x7601b351,0x2c37e250,0xd6f06b7e,0xb6300175,
        0x8bfeb9b7,0x4dde8ca1,0xb82f843d,0x4f210432,0xb1ac0afd,0x8d70e2f9 },
      { 0xaae91abb,0x25c73b78,0x863028f2,0x0230dca3,0xe5cf30b7,0x8b923ecf,
        0x5506f265,0xed754ec2,0x729a5e39,0x8e41b88c,0xbabf889b,0xee67cec2 } },
    /* 239 */
    { { 0x1be46c65,0xe183acf5,0xe7565d7a,0x9789538f,0xd9627b4e,0x87873391,
        0x9f1d9187,0xbf4ac4c1,0x4691f5c8,0x5db99f63,0x74a1fb98,0xa68df803 },
      { 0xbf92b5fa,0x3c448ed1,0x3e0bdc32,0xa098c841,0x79bf016c,0x8e74cd55,
        0x115e244d,0x5df0d09c,0x3410b66e,0x9418ad01,0x17a02130,0x8b6124cb } },
    /* 240 */
    { { 0xc26e3392,0x425ec3af,0xa1722e00,0xc07f8470,0xe2356b43,0xdcc28190,
        0xb1ef59a6,0x4ed97dff,0xc63028c1,0xc22b3ad1,0x68c18988,0x070723c2 },
      { 0x4cf49e7d,0x70da302f,0x3f12a522,0xc5e87c93,0x18594148,0x74acdd1d,
        0xca74124c,0xad5f73ab,0xd69fd478,0xe72e4a3e,0x7b117cc3,0x61593868 } },
    /* 241 */
    { { 0xa9aa0486,0x7b7b9577,0xa063d557,0x6e41fb35,0xda9047d7,0xb017d5c7,
        0x68a87ba9,0x8c748280,0xdf08ad93,0xab45fa5c,0x4c288a28,0xcd9fb217 },
      { 0x5747843d,0x59544642,0xa56111e3,0x34d64c6c,0x4bfce8d5,0x12e47ea1,
        0x6169267f,0x17740e05,0xeed03fb5,0x5c49438e,0x4fc3f513,0x9da30add } },
    /* 242 */
    { { 0xccfa5200,0xc4e85282,0x6a19b13d,0x2707608f,0xf5726e2f,0xdcb9a53d,
        0xe9427de5,0x612407c9,0xd54d582a,0x3e5a17e1,0x655ae118,0xb99877de },
      { 0x015254de,0x6f0e972b,0xf0a6f7c5,0x92a56db1,0xa656f8b2,0xd297e4e1,
        0xad981983,0x99fe0052,0x07cfed84,0xd3652d2f,0x843c1738,0xc784352e } },
    /* 243 */
    { { 0x7e9b2d8a,0x6ee90af0,0x57cf1964,0xac8d7018,0x71f28efc,0xf6ed9031,
        0x6812b20e,0x7f70d5a9,0xf1c61eee,0x27b557f4,0xc6263758,0xf1c9bd57 },
      { 0x2a1a6194,0x5cf7d014,0x1890ab84,0xdd614e0b,0x0e93c2a6,0x3ef9de10,
        0xe0cd91c5,0xf98cf575,0x14befc32,0x504ec0c6,0x6279d68c,0xd0513a66 } },
    /* 244 */
    { { 0xa859fb6a,0xa8eadbad,0xdb283666,0xcf8346e7,0x3e22e355,0x7b35e61a,
        0x99639c6b,0x293ece2c,0x56f241c8,0xfa0162e2,0xbf7a1dda,0xd2e6c7b9 },
      { 0x40075e63,0xd0de6253,0xf9ec8286,0x2405aa61,0x8fe45494,0x2237830a,
        0x364e9c8c,0x4fd01ac7,0x904ba750,0x4d9c3d21,0xaf1b520b,0xd589be14 } },
    /* 245 */
    { { 0x4662e53b,0x13576a4f,0xf9077676,0x35ec2f51,0x97c0af97,0x66297d13,
        0x9e598b58,0xed3201fe,0x5e70f604,0x49bc752a,0xbb12d951,0xb54af535 },
      { 0x212c1c76,0x36ea4c2b,0xeb250dfd,0x18f5bbc7,0x9a0a1a46,0xa0d466cc,
        0xdac2d917,0x52564da4,0x8e95fab5,0x206559f4,0x9ca67a33,0x7487c190 } },
    /* 246 */
    { { 0xdde98e9c,0x75abfe37,0x2a411199,0x99b90b26,0xdcdb1f7c,0x1b410996,
        0x8b3b5675,0xab346f11,0xf1f8ae1e,0x04852193,0x6b8b98c1,0x1ec4d227 },
      { 0x45452baa,0xba3bc926,0xacc4a572,0x387d1858,0xe51f171e,0x9478eff6,
        0x931e1c00,0xf357077d,0xe54c8ca8,0xffee77cd,0x551dc9a4,0xfb4892ff } },
    /* 247 */
    { { 0x2db8dff8,0x5b1bdad0,0x5a2285a2,0xd462f4fd,0xda00b461,0x1d6aad8e,
        0x41306d1b,0x43fbefcf,0x6a13fe19,0x428e86f3,0x17f89404,0xc8b2f118 },
      { 0xf0d51afb,0x762528aa,0x549b1d06,0xa3e2fea4,0xea3ddf66,0x86fad8f2,
        0x4fbdd206,0x0d9ccc4b,0xc189ff5a,0xcde97d4c,0x199f19a6,0xc36793d6 } },
    /* 248 */
    { { 0x51b85197,0xea38909b,0xb4c92895,0xffb17dd0,0x1ddb3f3f,0x0eb0878b,
        0xc57cf0f2,0xb05d28ff,0x1abd57e2,0xd8bde2e7,0xc40c1b20,0x7f2be28d },
      { 0x299a2d48,0x6554dca2,0x8377982d,0x5130ba2e,0x1071971a,0x8863205f,
        0x7cf2825d,0x15ee6282,0x03748f2b,0xd4b6c57f,0x430385a0,0xa9e3f4da } },
    /* 249 */
    { { 0x83fbc9c6,0x33eb7cec,0x4541777e,0x24a311c7,0x4f0767fc,0xc81377f7,
        0x4ab702da,0x12adae36,0x2a779696,0xb7fcb6db,0x01cea6ad,0x4a6fb284 },
      { 0xcdfc73de,0x5e8b1d2a,0x1b02fd32,0xd0efae8d,0xd81d8519,0x3f99c190,
        0xfc808971,0x3c18f7fa,0x51b7ae7b,0x41f713e7,0xf07fc3f8,0x0a4b3435 } },
    /* 250 */
    { { 0x019b7d2e,0x7dda3c4c,0xd4dc4b89,0x631c8d1a,0x1cdb313c,0x5489cd6e,
        0x4c07bb06,0xd44aed10,0x75f000d1,0x8f97e13a,0xdda5df4d,0x0e9ee64f },
      { 0x3e346910,0xeaa99f3b,0xfa294ad7,0x622f6921,0x0d0b2fe9,0x22aaa20d,
        0x1e5881ba,0x4fed2f99,0xc1571802,0x9af3b2d6,0xdc7ee17c,0x919e67a8 } },
    /* 251 */
    { { 0x76250533,0xc724fe4c,0x7d817ef8,0x8a2080e5,0x172c9751,0xa2afb0f4,
        0x17c0702e,0x9b10cdeb,0xc9b7e3e9,0xbf3975e3,0x1cd0cdc5,0x206117df },
      { 0xbe05ebd5,0xfb049e61,0x16c782c0,0xeb0bb55c,0xab7fed09,0x13a331b8,
        0x632863f0,0xf6c58b1d,0x4d3b6195,0x6264ef6e,0x9a53f116,0x92c51b63 } },
    /* 252 */
    { { 0x288b364d,0xa57c7bc8,0x7b41e5c4,0x4a562e08,0x698a9a11,0x699d21c6,
        0xf3f849b9,0xa4ed9581,0x9eb726ba,0xa223eef3,0xcc2884f9,0x13159c23 },
      { 0x3a3f4963,0x73931e58,0x0ada6a81,0x96500389,0x5ab2950b,0x3ee8a1c6,
        0x775fab52,0xeedf4949,0x4f2671b6,0x63d652e1,0x3c4e2f55,0xfed4491c } },
    /* 253 */
    { { 0xf4eb453e,0x335eadc3,0xcadd1a5b,0x5ff74b63,0x5d84a91a,0x6933d0d7,
        0xb49ba337,0x9ca3eeb9,0xc04c15b8,0x1f6facce,0xdc09a7e4,0x4ef19326 },
      { 0x3dca3233,0x53d2d324,0xa2259d4b,0x0ee40590,0x5546f002,0x18c22edb,
        0x09ea6b71,0x92429801,0xb0e91e61,0xaada0add,0x99963c50,0x5fe53ef4 } },
    /* 254 */
    { { 0x90c28c65,0x372dd06b,0x119ce47d,0x1765242c,0x6b22fc82,0xc041fb80,
        0xb0a7ccc1,0x667edf07,0x1261bece,0xc79599e7,0x19cff22a,0xbc69d9ba },
      { 0x13c06819,0x009d77cd,0xe282b79d,0x635a66ae,0x225b1be8,0x4edac4a6,
        0x524008f9,0x57d4f4e4,0xb056af84,0xee299ac5,0x3a0bc386,0xcc38444c } },
    /* 255 */
    { { 0xcd4c2356,0x490643b1,0x750547be,0x740a4851,0xd4944c04,0x643eaf29,
        0x299a98a0,0xba572479,0xee05fdf9,0x48b29f16,0x089b2d7b,0x33fb4f61 },
      { 0xa950f955,0x86704902,0xfedc3ddf,0x97e1034d,0x05fbb6a2,0x211320b6,
        0x432299bb,0x23d7b93f,0x8590e4a3,0x1fe1a057,0xf58c0ce6,0x8e1d0586 } },
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
static int sp_384_ecc_mulmod_base_12(sp_point_384* r, const sp_digit* k,
        int map, int ct, void* heap)
{
    return sp_384_ecc_mulmod_stripe_12(r, &p384_base, p384_table,
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
    sp_digit kd[12];
#endif
    sp_point_384* point;
    sp_digit* k = NULL;
    int err = MP_OKAY;

    err = sp_384_point_new_12(heap, p, point);
#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (err == MP_OKAY) {
        k = (sp_digit*)XMALLOC(sizeof(sp_digit) * 12, heap,
                                                              DYNAMIC_TYPE_ECC);
        if (k == NULL) {
            err = MEMORY_E;
        }
    }
#else
    k = kd;
#endif
    if (err == MP_OKAY) {
        sp_384_from_mp(k, 12, km);

            err = sp_384_ecc_mulmod_base_12(point, k, map, 1, heap);
    }
    if (err == MP_OKAY) {
        err = sp_384_point_to_ecc_point_12(point, r);
    }

#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (k != NULL) {
        XFREE(k, heap, DYNAMIC_TYPE_ECC);
    }
#endif
    sp_384_point_free_12(point, 0, heap);

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
static int sp_384_iszero_12(const sp_digit* a)
{
    return (a[0] | a[1] | a[2] | a[3] | a[4] | a[5] | a[6] | a[7] |
            a[8] | a[9] | a[10] | a[11]) == 0;
}

#endif /* WOLFSSL_VALIDATE_ECC_KEYGEN || HAVE_ECC_SIGN || HAVE_ECC_VERIFY */
/* Add 1 to a. (a = a + 1)
 *
 * a  A single precision integer.
 */
SP_NOINLINE static void sp_384_add_one_12(sp_digit* a)
{
    __asm__ __volatile__ (
        "mov	r2, #1\n\t"
        "ldr	r1, [%[a], #0]\n\t"
        "adds	r1, r1, r2\n\t"
        "mov	r2, #0\n\t"
        "str	r1, [%[a], #0]\n\t"
        "ldr	r1, [%[a], #4]\n\t"
        "adcs	r1, r1, r2\n\t"
        "str	r1, [%[a], #4]\n\t"
        "ldr	r1, [%[a], #8]\n\t"
        "adcs	r1, r1, r2\n\t"
        "str	r1, [%[a], #8]\n\t"
        "ldr	r1, [%[a], #12]\n\t"
        "adcs	r1, r1, r2\n\t"
        "str	r1, [%[a], #12]\n\t"
        "ldr	r1, [%[a], #16]\n\t"
        "adcs	r1, r1, r2\n\t"
        "str	r1, [%[a], #16]\n\t"
        "ldr	r1, [%[a], #20]\n\t"
        "adcs	r1, r1, r2\n\t"
        "str	r1, [%[a], #20]\n\t"
        "ldr	r1, [%[a], #24]\n\t"
        "adcs	r1, r1, r2\n\t"
        "str	r1, [%[a], #24]\n\t"
        "ldr	r1, [%[a], #28]\n\t"
        "adcs	r1, r1, r2\n\t"
        "str	r1, [%[a], #28]\n\t"
        "ldr	r1, [%[a], #32]\n\t"
        "adcs	r1, r1, r2\n\t"
        "str	r1, [%[a], #32]\n\t"
        "ldr	r1, [%[a], #36]\n\t"
        "adcs	r1, r1, r2\n\t"
        "str	r1, [%[a], #36]\n\t"
        "ldr	r1, [%[a], #40]\n\t"
        "adcs	r1, r1, r2\n\t"
        "str	r1, [%[a], #40]\n\t"
        "ldr	r1, [%[a], #44]\n\t"
        "adcs	r1, r1, r2\n\t"
        "str	r1, [%[a], #44]\n\t"
        :
        : [a] "r" (a)
        : "memory", "r1", "r2"
    );
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
        if (s >= 24U) {
            r[j] &= 0xffffffff;
            s = 32U - s;
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
static int sp_384_ecc_gen_k_12(WC_RNG* rng, sp_digit* k)
{
    int err;
    byte buf[48];

    do {
        err = wc_RNG_GenerateBlock(rng, buf, sizeof(buf));
        if (err == 0) {
            sp_384_from_bin(k, 12, buf, (int)sizeof(buf));
            if (sp_384_cmp_12(k, p384_order2) < 0) {
                sp_384_add_one_12(k);
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
    sp_digit kd[12];
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

    err = sp_384_point_new_12(heap, p, point);
#ifdef WOLFSSL_VALIDATE_ECC_KEYGEN
    if (err == MP_OKAY) {
        err = sp_384_point_new_12(heap, inf, infinity);
    }
#endif
#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (err == MP_OKAY) {
        k = (sp_digit*)XMALLOC(sizeof(sp_digit) * 12, heap,
                                                              DYNAMIC_TYPE_ECC);
        if (k == NULL) {
            err = MEMORY_E;
        }
    }
#else
    k = kd;
#endif

    if (err == MP_OKAY) {
        err = sp_384_ecc_gen_k_12(rng, k);
    }
    if (err == MP_OKAY) {
            err = sp_384_ecc_mulmod_base_12(point, k, 1, 1, NULL);
    }

#ifdef WOLFSSL_VALIDATE_ECC_KEYGEN
    if (err == MP_OKAY) {
            err = sp_384_ecc_mulmod_12(infinity, point, p384_order, 1, 1, NULL);
    }
    if (err == MP_OKAY) {
        if (sp_384_iszero_12(point->x) || sp_384_iszero_12(point->y)) {
            err = ECC_INF_E;
        }
    }
#endif

    if (err == MP_OKAY) {
        err = sp_384_to_mp(k, priv);
    }
    if (err == MP_OKAY) {
        err = sp_384_point_to_ecc_point_12(point, pub);
    }

#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (k != NULL) {
        XFREE(k, heap, DYNAMIC_TYPE_ECC);
    }
#endif
#ifdef WOLFSSL_VALIDATE_ECC_KEYGEN
    sp_384_point_free_12(infinity, 1, heap);
#endif
    sp_384_point_free_12(point, 1, heap);

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

    j = 384 / 8 - 1;
    a[j] = 0;
    for (i=0; i<12 && j>=0; i++) {
        b = 0;
        /* lint allow cast of mismatch sp_digit and int */
        a[j--] |= (byte)(r[i] << s); /*lint !e9033*/
        b += 8 - s;
        if (j < 0) {
            break;
        }
        while (b < 32) {
            a[j--] = (byte)(r[i] >> b);
            b += 8;
            if (j < 0) {
                break;
            }
        }
        s = 8 - (b - 32);
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
    sp_digit kd[12];
#endif
    sp_point_384* point = NULL;
    sp_digit* k = NULL;
    int err = MP_OKAY;

    if (*outLen < 48U) {
        err = BUFFER_E;
    }

    if (err == MP_OKAY) {
        err = sp_384_point_new_12(heap, p, point);
    }
#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (err == MP_OKAY) {
        k = (sp_digit*)XMALLOC(sizeof(sp_digit) * 12, heap,
                                                              DYNAMIC_TYPE_ECC);
        if (k == NULL)
            err = MEMORY_E;
    }
#else
    k = kd;
#endif

    if (err == MP_OKAY) {
        sp_384_from_mp(k, 12, priv);
        sp_384_point_from_ecc_point_12(point, pub);
            err = sp_384_ecc_mulmod_12(point, point, k, 1, 1, heap);
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
    sp_384_point_free_12(point, 0, heap);

    return err;
}
#endif /* HAVE_ECC_DHE */

#if defined(HAVE_ECC_SIGN) || defined(HAVE_ECC_VERIFY)
#endif
#if defined(HAVE_ECC_SIGN) || defined(HAVE_ECC_VERIFY)
#ifdef WOLFSSL_SP_SMALL
/* Sub b from a into a. (a -= b)
 *
 * a  A single precision integer.
 * b  A single precision integer.
 */
SP_NOINLINE static sp_digit sp_384_sub_in_place_12(sp_digit* a,
        const sp_digit* b)
{
    sp_digit c = 0;
    __asm__ __volatile__ (
        "mov	r8, %[a]\n\t"
        "add	r8, r8, #48\n\t"
        "\n1:\n\t"
        "mov	r5, #0\n\t"
        "subs	r5, r5, %[c]\n\t"
        "ldr	r3, [%[a]]\n\t"
        "ldr	r4, [%[a], #4]\n\t"
        "ldr	r5, [%[b]]\n\t"
        "ldr	r6, [%[b], #4]\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "str	r3, [%[a]]\n\t"
        "str	r4, [%[a], #4]\n\t"
        "sbc	%[c], %[c], %[c]\n\t"
        "add	%[a], %[a], #8\n\t"
        "add	%[b], %[b], #8\n\t"
        "cmp	%[a], r8\n\t"
        "bne	1b\n\t"
        : [c] "+r" (c), [a] "+r" (a), [b] "+r" (b)
        :
        : "memory", "r3", "r4", "r5", "r6", "r8"
    );

    return c;
}

#else
/* Sub b from a into r. (r = a - b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A single precision integer.
 */
SP_NOINLINE static sp_digit sp_384_sub_in_place_12(sp_digit* a,
        const sp_digit* b)
{
    sp_digit c = 0;

    __asm__ __volatile__ (
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "subs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "ldm	%[a], {r3, r4}\n\t"
        "ldm	%[b]!, {r5, r6}\n\t"
        "sbcs	r3, r3, r5\n\t"
        "sbcs	r4, r4, r6\n\t"
        "stm	%[a]!, {r3, r4}\n\t"
        "sbc	%[c], %[c], %[c]\n\t"
        : [c] "+r" (c), [a] "+r" (a), [b] "+r" (b)
        :
        : "memory", "r3", "r4", "r5", "r6"
    );

    return c;
}

#endif /* WOLFSSL_SP_SMALL */
/* Mul a by digit b into r. (r = a * b)
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * b  A single precision digit.
 */
SP_NOINLINE static void sp_384_mul_d_12(sp_digit* r, const sp_digit* a,
        sp_digit b)
{
    __asm__ __volatile__ (
        "add	r9, %[a], #48\n\t"
        /* A[0] * B */
        "ldr	r6, [%[a]], #4\n\t"
        "umull	r5, r3, r6, %[b]\n\t"
        "mov	r4, #0\n\t"
        "str	r5, [%[r]], #4\n\t"
        /* A[0] * B - Done */
        "\n1:\n\t"
        "mov	r5, #0\n\t"
        /* A[] * B */
        "ldr	r6, [%[a]], #4\n\t"
        "umull	r6, r8, r6, %[b]\n\t"
        "adds	r3, r3, r6\n\t"
        "adcs 	r4, r4, r8\n\t"
        "adc	r5, r5, #0\n\t"
        /* A[] * B - Done */
        "str	r3, [%[r]], #4\n\t"
        "mov	r3, r4\n\t"
        "mov	r4, r5\n\t"
        "cmp	%[a], r9\n\t"
        "blt	1b\n\t"
        "str	r3, [%[r]]\n\t"
        : [r] "+r" (r), [a] "+r" (a)
        : [b] "r" (b)
        : "memory", "r3", "r4", "r5", "r6", "r8", "r9"
    );
}

/* Divide the double width number (d1|d0) by the dividend. (d1|d0 / div)
 *
 * d1   The high order half of the number to divide.
 * d0   The low order half of the number to divide.
 * div  The dividend.
 * returns the result of the division.
 *
 * Note that this is an approximate div. It may give an answer 1 larger.
 */
SP_NOINLINE static sp_digit div_384_word_12(sp_digit d1, sp_digit d0,
        sp_digit div)
{
    sp_digit r = 0;

    __asm__ __volatile__ (
        "lsr	r6, %[div], #16\n\t"
        "add	r6, r6, #1\n\t"
        "udiv	r4, %[d1], r6\n\t"
        "lsl	r8, r4, #16\n\t"
        "umull	r4, r5, %[div], r8\n\t"
        "subs	%[d0], %[d0], r4\n\t"
        "sbc	%[d1], %[d1], r5\n\t"
        "udiv	r5, %[d1], r6\n\t"
        "lsl	r4, r5, #16\n\t"
        "add	r8, r8, r4\n\t"
        "umull	r4, r5, %[div], r4\n\t"
        "subs	%[d0], %[d0], r4\n\t"
        "sbc	%[d1], %[d1], r5\n\t"
        "lsl	r4, %[d1], #16\n\t"
        "orr	r4, r4, %[d0], lsr #16\n\t"
        "udiv	r4, r4, r6\n\t"
        "add	r8, r8, r4\n\t"
        "umull	r4, r5, %[div], r4\n\t"
        "subs	%[d0], %[d0], r4\n\t"
        "sbc	%[d1], %[d1], r5\n\t"
        "lsl	r4, %[d1], #16\n\t"
        "orr	r4, r4, %[d0], lsr #16\n\t"
        "udiv	r4, r4, r6\n\t"
        "add	r8, r8, r4\n\t"
        "umull	r4, r5, %[div], r4\n\t"
        "subs	%[d0], %[d0], r4\n\t"
        "sbc	%[d1], %[d1], r5\n\t"
        "udiv	r4, %[d0], %[div]\n\t"
        "add	r8, r8, r4\n\t"
        "mov	%[r], r8\n\t"
        : [r] "+r" (r)
        : [d1] "r" (d1), [d0] "r" (d0), [div] "r" (div)
        : "r4", "r5", "r6", "r8"
    );
    return r;
}

/* AND m into each word of a and store in r.
 *
 * r  A single precision integer.
 * a  A single precision integer.
 * m  Mask to AND against each digit.
 */
static void sp_384_mask_12(sp_digit* r, const sp_digit* a, sp_digit m)
{
#ifdef WOLFSSL_SP_SMALL
    int i;

    for (i=0; i<12; i++) {
        r[i] = a[i] & m;
    }
#else
    r[0] = a[0] & m;
    r[1] = a[1] & m;
    r[2] = a[2] & m;
    r[3] = a[3] & m;
    r[4] = a[4] & m;
    r[5] = a[5] & m;
    r[6] = a[6] & m;
    r[7] = a[7] & m;
    r[8] = a[8] & m;
    r[9] = a[9] & m;
    r[10] = a[10] & m;
    r[11] = a[11] & m;
#endif
}

/* Divide d in a and put remainder into r (m*d + r = a)
 * m is not calculated as it is not needed at this time.
 *
 * a  Nmber to be divided.
 * d  Number to divide with.
 * m  Multiplier result.
 * r  Remainder from the division.
 * returns MP_OKAY indicating success.
 */
static WC_INLINE int sp_384_div_12(const sp_digit* a, const sp_digit* d, sp_digit* m,
        sp_digit* r)
{
    sp_digit t1[24], t2[13];
    sp_digit div, r1;
    int i;

    (void)m;

    div = d[11];
    XMEMCPY(t1, a, sizeof(*t1) * 2 * 12);
    for (i=11; i>=0; i--) {
        r1 = div_384_word_12(t1[12 + i], t1[12 + i - 1], div);

        sp_384_mul_d_12(t2, d, r1);
        t1[12 + i] += sp_384_sub_in_place_12(&t1[i], t2);
        t1[12 + i] -= t2[12];
        sp_384_mask_12(t2, d, t1[12 + i]);
        t1[12 + i] += sp_384_add_12(&t1[i], &t1[i], t2);
        sp_384_mask_12(t2, d, t1[12 + i]);
        t1[12 + i] += sp_384_add_12(&t1[i], &t1[i], t2);
    }

    r1 = sp_384_cmp_12(t1, d) >= 0;
    sp_384_cond_sub_12(r, t1, d, (sp_digit)0 - r1);

    return MP_OKAY;
}

/* Reduce a modulo m into r. (r = a mod m)
 *
 * r  A single precision number that is the reduced result.
 * a  A single precision number that is to be reduced.
 * m  A single precision number that is the modulus to reduce with.
 * returns MP_OKAY indicating success.
 */
static WC_INLINE int sp_384_mod_12(sp_digit* r, const sp_digit* a, const sp_digit* m)
{
    return sp_384_div_12(a, m, NULL, r);
}

#endif
#if defined(HAVE_ECC_SIGN) || defined(HAVE_ECC_VERIFY)
#ifdef WOLFSSL_SP_SMALL
/* Order-2 for the P384 curve. */
static const uint32_t p384_order_minus_2[12] = {
    0xccc52971U,0xecec196aU,0x48b0a77aU,0x581a0db2U,0xf4372ddfU,0xc7634d81U,
    0xffffffffU,0xffffffffU,0xffffffffU,0xffffffffU,0xffffffffU,0xffffffffU
};
#else
/* The low half of the order-2 of the P384 curve. */
static const uint32_t p384_order_low[6] = {
    0xccc52971U,0xecec196aU,0x48b0a77aU,0x581a0db2U,0xf4372ddfU,0xc7634d81U
    
};
#endif /* WOLFSSL_SP_SMALL */

/* Multiply two number mod the order of P384 curve. (r = a * b mod order)
 *
 * r  Result of the multiplication.
 * a  First operand of the multiplication.
 * b  Second operand of the multiplication.
 */
static void sp_384_mont_mul_order_12(sp_digit* r, const sp_digit* a, const sp_digit* b)
{
    sp_384_mul_12(r, a, b);
    sp_384_mont_reduce_order_12(r, p384_order, p384_mp_order);
}

/* Square number mod the order of P384 curve. (r = a * a mod order)
 *
 * r  Result of the squaring.
 * a  Number to square.
 */
static void sp_384_mont_sqr_order_12(sp_digit* r, const sp_digit* a)
{
    sp_384_sqr_12(r, a);
    sp_384_mont_reduce_order_12(r, p384_order, p384_mp_order);
}

#ifndef WOLFSSL_SP_SMALL
/* Square number mod the order of P384 curve a number of times.
 * (r = a ^ n mod order)
 *
 * r  Result of the squaring.
 * a  Number to square.
 */
static void sp_384_mont_sqr_n_order_12(sp_digit* r, const sp_digit* a, int n)
{
    int i;

    sp_384_mont_sqr_order_12(r, a);
    for (i=1; i<n; i++) {
        sp_384_mont_sqr_order_12(r, r);
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
typedef struct sp_384_mont_inv_order_12_ctx {
    int state;
    int i;
} sp_384_mont_inv_order_12_ctx;
static int sp_384_mont_inv_order_12_nb(sp_ecc_ctx_t* sp_ctx, sp_digit* r, const sp_digit* a,
        sp_digit* t)
{
    int err = FP_WOULDBLOCK;
    sp_384_mont_inv_order_12_ctx* ctx = (sp_384_mont_inv_order_12_ctx*)sp_ctx;
    
    typedef char ctx_size_test[sizeof(sp_384_mont_inv_order_12_ctx) >= sizeof(*sp_ctx) ? -1 : 1];
    (void)sizeof(ctx_size_test);

    switch (ctx->state) {
    case 0:
        XMEMCPY(t, a, sizeof(sp_digit) * 12);
        ctx->i = 382;
        ctx->state = 1;
        break;
    case 1:
        sp_384_mont_sqr_order_12(t, t);
        ctx->state = 2;
        break;
    case 2:
        if ((p384_order_minus_2[ctx->i / 32] & ((sp_int_digit)1 << (ctx->i % 32))) != 0) {
            sp_384_mont_mul_order_12(t, t, a);
        }
        ctx->i--;
        ctx->state = (ctx->i == 0) ? 3 : 1;
        break;
    case 3:
        XMEMCPY(r, t, sizeof(sp_digit) * 12U);
        err = MP_OKAY;
        break;
    }
    return err;
}
#endif /* WOLFSSL_SP_NONBLOCK */

static void sp_384_mont_inv_order_12(sp_digit* r, const sp_digit* a,
        sp_digit* td)
{
#ifdef WOLFSSL_SP_SMALL
    sp_digit* t = td;
    int i;

    XMEMCPY(t, a, sizeof(sp_digit) * 12);
    for (i=382; i>=0; i--) {
        sp_384_mont_sqr_order_12(t, t);
        if ((p384_order_minus_2[i / 32] & ((sp_int_digit)1 << (i % 32))) != 0) {
            sp_384_mont_mul_order_12(t, t, a);
        }
    }
    XMEMCPY(r, t, sizeof(sp_digit) * 12U);
#else
    sp_digit* t = td;
    sp_digit* t2 = td + 2 * 12;
    sp_digit* t3 = td + 4 * 12;
    int i;

    /* t = a^2 */
    sp_384_mont_sqr_order_12(t, a);
    /* t = a^3 = t * a */
    sp_384_mont_mul_order_12(t, t, a);
    /* t2= a^c = t ^ 2 ^ 2 */
    sp_384_mont_sqr_n_order_12(t2, t, 2);
    /* t = a^f = t2 * t */
    sp_384_mont_mul_order_12(t, t2, t);
    /* t2= a^f0 = t ^ 2 ^ 4 */
    sp_384_mont_sqr_n_order_12(t2, t, 4);
    /* t = a^ff = t2 * t */
    sp_384_mont_mul_order_12(t, t2, t);
    /* t2= a^ff00 = t ^ 2 ^ 8 */
    sp_384_mont_sqr_n_order_12(t2, t, 8);
    /* t3= a^ffff = t2 * t */
    sp_384_mont_mul_order_12(t3, t2, t);
    /* t2= a^ffff0000 = t3 ^ 2 ^ 16 */
    sp_384_mont_sqr_n_order_12(t2, t3, 16);
    /* t = a^ffffffff = t2 * t3 */
    sp_384_mont_mul_order_12(t, t2, t3);
    /* t2= a^ffffffff0000 = t ^ 2 ^ 16  */
    sp_384_mont_sqr_n_order_12(t2, t, 16);
    /* t = a^ffffffffffff = t2 * t3 */
    sp_384_mont_mul_order_12(t, t2, t3);
    /* t2= a^ffffffffffff000000000000 = t ^ 2 ^ 48  */
    sp_384_mont_sqr_n_order_12(t2, t, 48);
    /* t= a^fffffffffffffffffffffffff = t2 * t */
    sp_384_mont_mul_order_12(t, t2, t);
    /* t2= a^ffffffffffffffffffffffff000000000000000000000000 */
    sp_384_mont_sqr_n_order_12(t2, t, 96);
    /* t2= a^ffffffffffffffffffffffffffffffffffffffffffffffff = t2 * t */
    sp_384_mont_mul_order_12(t2, t2, t);
    for (i=191; i>=1; i--) {
        sp_384_mont_sqr_order_12(t2, t2);
        if (((sp_digit)p384_order_low[i / 32] & ((sp_int_digit)1 << (i % 32))) != 0) {
            sp_384_mont_mul_order_12(t2, t2, a);
        }
    }
    sp_384_mont_sqr_order_12(t2, t2);
    sp_384_mont_mul_order_12(r, t2, a);
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
        sp_384_ecc_mulmod_12_ctx mulmod_ctx;
        sp_384_mont_inv_order_12_ctx mont_inv_order_ctx;
    };
    sp_digit e[2*12];
    sp_digit x[2*12];
    sp_digit k[2*12];
    sp_digit r[2*12];
    sp_digit tmp[3 * 2*12];
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

        sp_384_from_bin(ctx->e, 12, hash, (int)hashLen);

        ctx->i = SP_ECC_MAX_SIG_GEN;
        ctx->state = 1;
        break;
    case 1: /* GEN */
        sp_384_from_mp(ctx->x, 12, priv);
        /* New random point. */
        if (km == NULL || mp_iszero(km)) {
            err = sp_384_ecc_gen_k_12(rng, ctx->k);
        }
        else {
            sp_384_from_mp(ctx->k, 12, km);
            mp_zero(km);
        }
        XMEMSET(&ctx->mulmod_ctx, 0, sizeof(ctx->mulmod_ctx));
        ctx->state = 2;
        break; 
    case 2: /* MULMOD */
        err = sp_384_ecc_mulmod_12_nb((sp_ecc_ctx_t*)&ctx->mulmod_ctx, 
            &ctx->point, &p384_base, ctx->k, 1, 1, heap);
        if (err == MP_OKAY) {
            ctx->state = 3;
        }
        break;
    case 3: /* MODORDER */
    {
        int32_t c;
        /* r = point->x mod order */
        XMEMCPY(ctx->r, ctx->point.x, sizeof(sp_digit) * 12U);
        sp_384_norm_12(ctx->r);
        c = sp_384_cmp_12(ctx->r, p384_order);
        sp_384_cond_sub_12(ctx->r, ctx->r, p384_order, 0L - (sp_digit)(c >= 0));
        sp_384_norm_12(ctx->r);
        ctx->state = 4;
        break;
    }
    case 4: /* KMODORDER */
        /* Conv k to Montgomery form (mod order) */
        sp_384_mul_12(ctx->k, ctx->k, p384_norm_order);
        err = sp_384_mod_12(ctx->k, ctx->k, p384_order);
        if (err == MP_OKAY) {
            sp_384_norm_12(ctx->k);
            XMEMSET(&ctx->mont_inv_order_ctx, 0, sizeof(ctx->mont_inv_order_ctx));
            ctx->state = 5;
        }
        break;
    case 5: /* KINV */
        /* kInv = 1/k mod order */
        err = sp_384_mont_inv_order_12_nb((sp_ecc_ctx_t*)&ctx->mont_inv_order_ctx, ctx->kInv, ctx->k, ctx->tmp);
        if (err == MP_OKAY) {
            XMEMSET(&ctx->mont_inv_order_ctx, 0, sizeof(ctx->mont_inv_order_ctx));
            ctx->state = 6;
        }
        break;
    case 6: /* KINVNORM */
        sp_384_norm_12(ctx->kInv);
        ctx->state = 7;
        break;
    case 7: /* R */
        /* s = r * x + e */
        sp_384_mul_12(ctx->x, ctx->x, ctx->r);
        ctx->state = 8;
        break;
    case 8: /* S1 */
        err = sp_384_mod_12(ctx->x, ctx->x, p384_order);
        if (err == MP_OKAY)
            ctx->state = 9;
        break;
    case 9: /* S2 */
    {
        sp_digit carry;
        int32_t c;
        sp_384_norm_12(ctx->x);
        carry = sp_384_add_12(ctx->s, ctx->e, ctx->x);
        sp_384_cond_sub_12(ctx->s, ctx->s, p384_order, 0 - carry);
        sp_384_norm_12(ctx->s);
        c = sp_384_cmp_12(ctx->s, p384_order);
        sp_384_cond_sub_12(ctx->s, ctx->s, p384_order, 0L - (sp_digit)(c >= 0));
        sp_384_norm_12(ctx->s);

        /* s = s * k^-1 mod order */
        sp_384_mont_mul_order_12(ctx->s, ctx->s, ctx->kInv);
        sp_384_norm_12(ctx->s);

        /* Check that signature is usable. */
        if (sp_384_iszero_12(ctx->s) == 0) {
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
        XMEMSET(ctx->e, 0, sizeof(sp_digit) * 2U * 12U);
        XMEMSET(ctx->x, 0, sizeof(sp_digit) * 2U * 12U);
        XMEMSET(ctx->k, 0, sizeof(sp_digit) * 2U * 12U);
        XMEMSET(ctx->r, 0, sizeof(sp_digit) * 2U * 12U);
        XMEMSET(ctx->tmp, 0, sizeof(sp_digit) * 3U * 2U * 12U);
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
    sp_digit ed[2*12];
    sp_digit xd[2*12];
    sp_digit kd[2*12];
    sp_digit rd[2*12];
    sp_digit td[3 * 2*12];
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
    int32_t c;
    int i;

    (void)heap;

    err = sp_384_point_new_12(heap, p, point);
#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (err == MP_OKAY) {
        d = (sp_digit*)XMALLOC(sizeof(sp_digit) * 7 * 2 * 12, heap,
                                                              DYNAMIC_TYPE_ECC);
        if (d == NULL) {
            err = MEMORY_E;
        }
    }
#endif

    if (err == MP_OKAY) {
#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
        e = d + 0 * 12;
        x = d + 2 * 12;
        k = d + 4 * 12;
        r = d + 6 * 12;
        tmp = d + 8 * 12;
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

        sp_384_from_bin(e, 12, hash, (int)hashLen);
    }

    for (i = SP_ECC_MAX_SIG_GEN; err == MP_OKAY && i > 0; i--) {
        sp_384_from_mp(x, 12, priv);

        /* New random point. */
        if (km == NULL || mp_iszero(km)) {
            err = sp_384_ecc_gen_k_12(rng, k);
        }
        else {
            sp_384_from_mp(k, 12, km);
            mp_zero(km);
        }
        if (err == MP_OKAY) {
                err = sp_384_ecc_mulmod_base_12(point, k, 1, 1, NULL);
        }

        if (err == MP_OKAY) {
            /* r = point->x mod order */
            XMEMCPY(r, point->x, sizeof(sp_digit) * 12U);
            sp_384_norm_12(r);
            c = sp_384_cmp_12(r, p384_order);
            sp_384_cond_sub_12(r, r, p384_order, 0L - (sp_digit)(c >= 0));
            sp_384_norm_12(r);

            /* Conv k to Montgomery form (mod order) */
                sp_384_mul_12(k, k, p384_norm_order);
            err = sp_384_mod_12(k, k, p384_order);
        }
        if (err == MP_OKAY) {
            sp_384_norm_12(k);
            /* kInv = 1/k mod order */
                sp_384_mont_inv_order_12(kInv, k, tmp);
            sp_384_norm_12(kInv);

            /* s = r * x + e */
                sp_384_mul_12(x, x, r);
            err = sp_384_mod_12(x, x, p384_order);
        }
        if (err == MP_OKAY) {
            sp_384_norm_12(x);
            carry = sp_384_add_12(s, e, x);
            sp_384_cond_sub_12(s, s, p384_order, 0 - carry);
            sp_384_norm_12(s);
            c = sp_384_cmp_12(s, p384_order);
            sp_384_cond_sub_12(s, s, p384_order, 0L - (sp_digit)(c >= 0));
            sp_384_norm_12(s);

            /* s = s * k^-1 mod order */
                sp_384_mont_mul_order_12(s, s, kInv);
            sp_384_norm_12(s);

            /* Check that signature is usable. */
            if (sp_384_iszero_12(s) == 0) {
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
        XMEMSET(d, 0, sizeof(sp_digit) * 8 * 12);
        XFREE(d, heap, DYNAMIC_TYPE_ECC);
    }
#else
    XMEMSET(e, 0, sizeof(sp_digit) * 2U * 12U);
    XMEMSET(x, 0, sizeof(sp_digit) * 2U * 12U);
    XMEMSET(k, 0, sizeof(sp_digit) * 2U * 12U);
    XMEMSET(r, 0, sizeof(sp_digit) * 2U * 12U);
    XMEMSET(r, 0, sizeof(sp_digit) * 2U * 12U);
    XMEMSET(tmp, 0, sizeof(sp_digit) * 3U * 2U * 12U);
#endif
    sp_384_point_free_12(point, 1, heap);

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
        sp_384_ecc_mulmod_12_ctx mulmod_ctx;
        sp_384_mont_inv_order_12_ctx mont_inv_order_ctx;
        sp_384_proj_point_dbl_12_ctx dbl_ctx;
        sp_384_proj_point_add_12_ctx add_ctx;
    };
    sp_digit u1[2*12];
    sp_digit u2[2*12];
    sp_digit s[2*12];
    sp_digit tmp[2*12 * 5];
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

        sp_384_from_bin(ctx->u1, 12, hash, (int)hashLen);
        sp_384_from_mp(ctx->u2, 12, r);
        sp_384_from_mp(ctx->s, 12, sm);
        sp_384_from_mp(ctx->p2.x, 12, pX);
        sp_384_from_mp(ctx->p2.y, 12, pY);
        sp_384_from_mp(ctx->p2.z, 12, pZ);
        ctx->state = 1;
        break;
    case 1: /* NORMS0 */
        sp_384_mul_12(ctx->s, ctx->s, p384_norm_order);
        err = sp_384_mod_12(ctx->s, ctx->s, p384_order);
        if (err == MP_OKAY)
            ctx->state = 2;
        break;
    case 2: /* NORMS1 */
        sp_384_norm_12(ctx->s);
        XMEMSET(&ctx->mont_inv_order_ctx, 0, sizeof(ctx->mont_inv_order_ctx));
        ctx->state = 3;
        break;
    case 3: /* NORMS2 */
        err = sp_384_mont_inv_order_12_nb((sp_ecc_ctx_t*)&ctx->mont_inv_order_ctx, ctx->s, ctx->s, ctx->tmp);
        if (err == MP_OKAY) {
            ctx->state = 4;
        }
        break;
    case 4: /* NORMS3 */
        sp_384_mont_mul_order_12(ctx->u1, ctx->u1, ctx->s);
        ctx->state = 5;
        break;
    case 5: /* NORMS4 */
        sp_384_mont_mul_order_12(ctx->u2, ctx->u2, ctx->s);
        XMEMSET(&ctx->mulmod_ctx, 0, sizeof(ctx->mulmod_ctx));
        ctx->state = 6;
        break;
    case 6: /* MULBASE */
        err = sp_384_ecc_mulmod_12_nb((sp_ecc_ctx_t*)&ctx->mulmod_ctx, &ctx->p1, &p384_base, ctx->u1, 0, 0, heap);
        if (err == MP_OKAY) {
            XMEMSET(&ctx->mulmod_ctx, 0, sizeof(ctx->mulmod_ctx));
            ctx->state = 7;
        }
        break;
    case 7: /* MULMOD */
        err = sp_384_ecc_mulmod_12_nb((sp_ecc_ctx_t*)&ctx->mulmod_ctx, &ctx->p2, &ctx->p2, ctx->u2, 0, 0, heap);
        if (err == MP_OKAY) {
            XMEMSET(&ctx->add_ctx, 0, sizeof(ctx->add_ctx));
            ctx->state = 8;
        }
        break;
    case 8: /* ADD */
        err = sp_384_proj_point_add_12_nb((sp_ecc_ctx_t*)&ctx->add_ctx, &ctx->p1, &ctx->p1, &ctx->p2, ctx->tmp);
        if (err == MP_OKAY)
            ctx->state = 9;
        break;
    case 9: /* DBLPREP */
        if (sp_384_iszero_12(ctx->p1.z)) {
            if (sp_384_iszero_12(ctx->p1.x) && sp_384_iszero_12(ctx->p1.y)) {
                XMEMSET(&ctx->dbl_ctx, 0, sizeof(ctx->dbl_ctx));
                ctx->state = 10;
                break;
            }
            else {
                /* Y ordinate is not used from here - don't set. */
                int i;
                for (i=0; i<12; i++) {
                    ctx->p1.x[i] = 0;
                }
                XMEMCPY(ctx->p1.z, p384_norm_mod, sizeof(p384_norm_mod));
            }
        }
        ctx->state = 11;
        break;
    case 10: /* DBL */
        err = sp_384_proj_point_dbl_12_nb((sp_ecc_ctx_t*)&ctx->dbl_ctx, &ctx->p1, 
            &ctx->p2, ctx->tmp);
        if (err == MP_OKAY) {
            ctx->state = 11;
        }
        break;
    case 11: /* MONT */
        /* (r + n*order).z'.z' mod prime == (u1.G + u2.Q)->x' */
        /* Reload r and convert to Montgomery form. */
        sp_384_from_mp(ctx->u2, 12, r);
        err = sp_384_mod_mul_norm_12(ctx->u2, ctx->u2, p384_mod);
        if (err == MP_OKAY)
            ctx->state = 12;
        break;
    case 12: /* SQR */
        /* u1 = r.z'.z' mod prime */
        sp_384_mont_sqr_12(ctx->p1.z, ctx->p1.z, p384_mod, p384_mp_mod);
        ctx->state = 13;
        break;
    case 13: /* MUL */
        sp_384_mont_mul_12(ctx->u1, ctx->u2, ctx->p1.z, p384_mod, p384_mp_mod);
        ctx->state = 14;
        break;
    case 14: /* RES */
        err = MP_OKAY; /* math okay, now check result */
        *res = (int)(sp_384_cmp_12(ctx->p1.x, ctx->u1) == 0);
        if (*res == 0) {
            sp_digit carry;
            int32_t c;

            /* Reload r and add order. */
            sp_384_from_mp(ctx->u2, 12, r);
            carry = sp_384_add_12(ctx->u2, ctx->u2, p384_order);
            /* Carry means result is greater than mod and is not valid. */
            if (carry == 0) {
                sp_384_norm_12(ctx->u2);

                /* Compare with mod and if greater or equal then not valid. */
                c = sp_384_cmp_12(ctx->u2, p384_mod);
                if (c < 0) {
                    /* Convert to Montogomery form */
                    err = sp_384_mod_mul_norm_12(ctx->u2, ctx->u2, p384_mod);
                    if (err == MP_OKAY) {
                        /* u1 = (r + 1*order).z'.z' mod prime */
                        sp_384_mont_mul_12(ctx->u1, ctx->u2, ctx->p1.z, p384_mod,
                                                                  p384_mp_mod);
                        *res = (int)(sp_384_cmp_12(ctx->p1.x, ctx->u1) == 0);
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
    sp_digit u1d[2*12];
    sp_digit u2d[2*12];
    sp_digit sd[2*12];
    sp_digit tmpd[2*12 * 5];
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
    int32_t c;
    int err;

    err = sp_384_point_new_12(heap, p1d, p1);
    if (err == MP_OKAY) {
        err = sp_384_point_new_12(heap, p2d, p2);
    }
#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (err == MP_OKAY) {
        d = (sp_digit*)XMALLOC(sizeof(sp_digit) * 16 * 12, heap,
                                                              DYNAMIC_TYPE_ECC);
        if (d == NULL) {
            err = MEMORY_E;
        }
    }
#endif

    if (err == MP_OKAY) {
#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
        u1  = d + 0 * 12;
        u2  = d + 2 * 12;
        s   = d + 4 * 12;
        tmp = d + 6 * 12;
#else
        u1 = u1d;
        u2 = u2d;
        s  = sd;
        tmp = tmpd;
#endif

        if (hashLen > 48U) {
            hashLen = 48U;
        }

        sp_384_from_bin(u1, 12, hash, (int)hashLen);
        sp_384_from_mp(u2, 12, r);
        sp_384_from_mp(s, 12, sm);
        sp_384_from_mp(p2->x, 12, pX);
        sp_384_from_mp(p2->y, 12, pY);
        sp_384_from_mp(p2->z, 12, pZ);

        {
            sp_384_mul_12(s, s, p384_norm_order);
        }
        err = sp_384_mod_12(s, s, p384_order);
    }
    if (err == MP_OKAY) {
        sp_384_norm_12(s);
        {
            sp_384_mont_inv_order_12(s, s, tmp);
            sp_384_mont_mul_order_12(u1, u1, s);
            sp_384_mont_mul_order_12(u2, u2, s);
        }

            err = sp_384_ecc_mulmod_base_12(p1, u1, 0, 0, heap);
    }
    if (err == MP_OKAY) {
            err = sp_384_ecc_mulmod_12(p2, p2, u2, 0, 0, heap);
    }

    if (err == MP_OKAY) {
        {
            sp_384_proj_point_add_12(p1, p1, p2, tmp);
            if (sp_384_iszero_12(p1->z)) {
                if (sp_384_iszero_12(p1->x) && sp_384_iszero_12(p1->y)) {
                    sp_384_proj_point_dbl_12(p1, p2, tmp);
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
                    p1->x[7] = 0;
                    p1->x[8] = 0;
                    p1->x[9] = 0;
                    p1->x[10] = 0;
                    p1->x[11] = 0;
                    XMEMCPY(p1->z, p384_norm_mod, sizeof(p384_norm_mod));
                }
            }
        }

        /* (r + n*order).z'.z' mod prime == (u1.G + u2.Q)->x' */
        /* Reload r and convert to Montgomery form. */
        sp_384_from_mp(u2, 12, r);
        err = sp_384_mod_mul_norm_12(u2, u2, p384_mod);
    }

    if (err == MP_OKAY) {
        /* u1 = r.z'.z' mod prime */
        sp_384_mont_sqr_12(p1->z, p1->z, p384_mod, p384_mp_mod);
        sp_384_mont_mul_12(u1, u2, p1->z, p384_mod, p384_mp_mod);
        *res = (int)(sp_384_cmp_12(p1->x, u1) == 0);
        if (*res == 0) {
            /* Reload r and add order. */
            sp_384_from_mp(u2, 12, r);
            carry = sp_384_add_12(u2, u2, p384_order);
            /* Carry means result is greater than mod and is not valid. */
            if (carry == 0) {
                sp_384_norm_12(u2);

                /* Compare with mod and if greater or equal then not valid. */
                c = sp_384_cmp_12(u2, p384_mod);
                if (c < 0) {
                    /* Convert to Montogomery form */
                    err = sp_384_mod_mul_norm_12(u2, u2, p384_mod);
                    if (err == MP_OKAY) {
                        /* u1 = (r + 1*order).z'.z' mod prime */
                        sp_384_mont_mul_12(u1, u2, p1->z, p384_mod,
                                                                  p384_mp_mod);
                        *res = (int)(sp_384_cmp_12(p1->x, u1) == 0);
                    }
                }
            }
        }
    }

#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (d != NULL)
        XFREE(d, heap, DYNAMIC_TYPE_ECC);
#endif
    sp_384_point_free_12(p1, 0, heap);
    sp_384_point_free_12(p2, 0, heap);

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
static int sp_384_ecc_is_point_12(sp_point_384* point, void* heap)
{
#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    sp_digit* d = NULL;
#else
    sp_digit t1d[2*12];
    sp_digit t2d[2*12];
#endif
    sp_digit* t1;
    sp_digit* t2;
    int err = MP_OKAY;

#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    d = (sp_digit*)XMALLOC(sizeof(sp_digit) * 12 * 4, heap, DYNAMIC_TYPE_ECC);
    if (d == NULL) {
        err = MEMORY_E;
    }
#endif
    (void)heap;

    if (err == MP_OKAY) {
#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
        t1 = d + 0 * 12;
        t2 = d + 2 * 12;
#else
        t1 = t1d;
        t2 = t2d;
#endif

        sp_384_sqr_12(t1, point->y);
        (void)sp_384_mod_12(t1, t1, p384_mod);
        sp_384_sqr_12(t2, point->x);
        (void)sp_384_mod_12(t2, t2, p384_mod);
        sp_384_mul_12(t2, t2, point->x);
        (void)sp_384_mod_12(t2, t2, p384_mod);
        (void)sp_384_sub_12(t2, p384_mod, t2);
        sp_384_mont_add_12(t1, t1, t2, p384_mod);

        sp_384_mont_add_12(t1, t1, point->x, p384_mod);
        sp_384_mont_add_12(t1, t1, point->x, p384_mod);
        sp_384_mont_add_12(t1, t1, point->x, p384_mod);

        if (sp_384_cmp_12(t1, p384_b) != 0) {
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

    err = sp_384_point_new_12(NULL, pubd, pub);
    if (err == MP_OKAY) {
        sp_384_from_mp(pub->x, 12, pX);
        sp_384_from_mp(pub->y, 12, pY);
        sp_384_from_bin(pub->z, 12, one, (int)sizeof(one));

        err = sp_384_ecc_is_point_12(pub, NULL);
    }

    sp_384_point_free_12(pub, 0, NULL);

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
    sp_digit privd[12];
    sp_point_384 pubd;
    sp_point_384 pd;
#endif
    sp_digit* priv = NULL;
    sp_point_384* pub;
    sp_point_384* p = NULL;
    byte one[1] = { 1 };
    int err;

    err = sp_384_point_new_12(heap, pubd, pub);
    if (err == MP_OKAY) {
        err = sp_384_point_new_12(heap, pd, p);
    }
#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (err == MP_OKAY) {
        priv = (sp_digit*)XMALLOC(sizeof(sp_digit) * 12, heap,
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

        sp_384_from_mp(pub->x, 12, pX);
        sp_384_from_mp(pub->y, 12, pY);
        sp_384_from_bin(pub->z, 12, one, (int)sizeof(one));
        sp_384_from_mp(priv, 12, privm);

        /* Check point at infinitiy. */
        if ((sp_384_iszero_12(pub->x) != 0) &&
            (sp_384_iszero_12(pub->y) != 0)) {
            err = ECC_INF_E;
        }
    }

    if (err == MP_OKAY) {
        /* Check range of X and Y */
        if (sp_384_cmp_12(pub->x, p384_mod) >= 0 ||
            sp_384_cmp_12(pub->y, p384_mod) >= 0) {
            err = ECC_OUT_OF_RANGE_E;
        }
    }

    if (err == MP_OKAY) {
        /* Check point is on curve */
        err = sp_384_ecc_is_point_12(pub, heap);
    }

    if (err == MP_OKAY) {
        /* Point * order = infinity */
            err = sp_384_ecc_mulmod_12(p, pub, p384_order, 1, 1, heap);
    }
    if (err == MP_OKAY) {
        /* Check result is infinity */
        if ((sp_384_iszero_12(p->x) == 0) ||
            (sp_384_iszero_12(p->y) == 0)) {
            err = ECC_INF_E;
        }
    }

    if (err == MP_OKAY) {
        /* Base * private = point */
            err = sp_384_ecc_mulmod_base_12(p, priv, 1, 1, heap);
    }
    if (err == MP_OKAY) {
        /* Check result is public key */
        if (sp_384_cmp_12(p->x, pub->x) != 0 ||
            sp_384_cmp_12(p->y, pub->y) != 0) {
            err = ECC_PRIV_KEY_E;
        }
    }

#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (priv != NULL) {
        XFREE(priv, heap, DYNAMIC_TYPE_ECC);
    }
#endif
    sp_384_point_free_12(p, 0, heap);
    sp_384_point_free_12(pub, 0, heap);

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
    sp_digit tmpd[2 * 12 * 5];
    sp_point_384 pd;
    sp_point_384 qd;
#endif
    sp_digit* tmp;
    sp_point_384* p;
    sp_point_384* q = NULL;
    int err;

    err = sp_384_point_new_12(NULL, pd, p);
    if (err == MP_OKAY) {
        err = sp_384_point_new_12(NULL, qd, q);
    }
#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (err == MP_OKAY) {
        tmp = (sp_digit*)XMALLOC(sizeof(sp_digit) * 2 * 12 * 5, NULL,
                                                              DYNAMIC_TYPE_ECC);
        if (tmp == NULL) {
            err = MEMORY_E;
        }
    }
#else
    tmp = tmpd;
#endif

    if (err == MP_OKAY) {
        sp_384_from_mp(p->x, 12, pX);
        sp_384_from_mp(p->y, 12, pY);
        sp_384_from_mp(p->z, 12, pZ);
        sp_384_from_mp(q->x, 12, qX);
        sp_384_from_mp(q->y, 12, qY);
        sp_384_from_mp(q->z, 12, qZ);

            sp_384_proj_point_add_12(p, p, q, tmp);
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
    sp_384_point_free_12(q, 0, NULL);
    sp_384_point_free_12(p, 0, NULL);

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
    sp_digit tmpd[2 * 12 * 2];
    sp_point_384 pd;
#endif
    sp_digit* tmp;
    sp_point_384* p;
    int err;

    err = sp_384_point_new_12(NULL, pd, p);
#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (err == MP_OKAY) {
        tmp = (sp_digit*)XMALLOC(sizeof(sp_digit) * 2 * 12 * 2, NULL,
                                                              DYNAMIC_TYPE_ECC);
        if (tmp == NULL) {
            err = MEMORY_E;
        }
    }
#else
    tmp = tmpd;
#endif

    if (err == MP_OKAY) {
        sp_384_from_mp(p->x, 12, pX);
        sp_384_from_mp(p->y, 12, pY);
        sp_384_from_mp(p->z, 12, pZ);

            sp_384_proj_point_dbl_12(p, p, tmp);
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
    sp_384_point_free_12(p, 0, NULL);

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
    sp_digit tmpd[2 * 12 * 6];
    sp_point_384 pd;
#endif
    sp_digit* tmp;
    sp_point_384* p;
    int err;

    err = sp_384_point_new_12(NULL, pd, p);
#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    if (err == MP_OKAY) {
        tmp = (sp_digit*)XMALLOC(sizeof(sp_digit) * 2 * 12 * 6, NULL,
                                                              DYNAMIC_TYPE_ECC);
        if (tmp == NULL) {
            err = MEMORY_E;
        }
    }
#else
    tmp = tmpd;
#endif
    if (err == MP_OKAY) {
        sp_384_from_mp(p->x, 12, pX);
        sp_384_from_mp(p->y, 12, pY);
        sp_384_from_mp(p->z, 12, pZ);

        sp_384_map_12(p, p, tmp);
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
    sp_384_point_free_12(p, 0, NULL);

    return err;
}
#endif /* WOLFSSL_PUBLIC_ECC_ADD_DBL */
#ifdef HAVE_COMP_KEY
/* Find the square root of a number mod the prime of the curve.
 *
 * y  The number to operate on and the result.
 * returns MEMORY_E if dynamic memory allocation fails and MP_OKAY otherwise.
 */
static int sp_384_mont_sqrt_12(sp_digit* y)
{
#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    sp_digit* d;
#else
    sp_digit t1d[2 * 12];
    sp_digit t2d[2 * 12];
    sp_digit t3d[2 * 12];
    sp_digit t4d[2 * 12];
    sp_digit t5d[2 * 12];
#endif
    sp_digit* t1;
    sp_digit* t2;
    sp_digit* t3;
    sp_digit* t4;
    sp_digit* t5;
    int err = MP_OKAY;

#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    d = (sp_digit*)XMALLOC(sizeof(sp_digit) * 5 * 2 * 12, NULL, DYNAMIC_TYPE_ECC);
    if (d == NULL) {
        err = MEMORY_E;
    }
#endif

    if (err == MP_OKAY) {
#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
        t1 = d + 0 * 12;
        t2 = d + 2 * 12;
        t3 = d + 4 * 12;
        t4 = d + 6 * 12;
        t5 = d + 8 * 12;
#else
        t1 = t1d;
        t2 = t2d;
        t3 = t3d;
        t4 = t4d;
        t5 = t5d;
#endif

        {
            /* t2 = y ^ 0x2 */
            sp_384_mont_sqr_12(t2, y, p384_mod, p384_mp_mod);
            /* t1 = y ^ 0x3 */
            sp_384_mont_mul_12(t1, t2, y, p384_mod, p384_mp_mod);
            /* t5 = y ^ 0xc */
            sp_384_mont_sqr_n_12(t5, t1, 2, p384_mod, p384_mp_mod);
            /* t1 = y ^ 0xf */
            sp_384_mont_mul_12(t1, t1, t5, p384_mod, p384_mp_mod);
            /* t2 = y ^ 0x1e */
            sp_384_mont_sqr_12(t2, t1, p384_mod, p384_mp_mod);
            /* t3 = y ^ 0x1f */
            sp_384_mont_mul_12(t3, t2, y, p384_mod, p384_mp_mod);
            /* t2 = y ^ 0x3e0 */
            sp_384_mont_sqr_n_12(t2, t3, 5, p384_mod, p384_mp_mod);
            /* t1 = y ^ 0x3ff */
            sp_384_mont_mul_12(t1, t3, t2, p384_mod, p384_mp_mod);
            /* t2 = y ^ 0x7fe0 */
            sp_384_mont_sqr_n_12(t2, t1, 5, p384_mod, p384_mp_mod);
            /* t3 = y ^ 0x7fff */
            sp_384_mont_mul_12(t3, t3, t2, p384_mod, p384_mp_mod);
            /* t2 = y ^ 0x3fff800 */
            sp_384_mont_sqr_n_12(t2, t3, 15, p384_mod, p384_mp_mod);
            /* t4 = y ^ 0x3ffffff */
            sp_384_mont_mul_12(t4, t3, t2, p384_mod, p384_mp_mod);
            /* t2 = y ^ 0xffffffc000000 */
            sp_384_mont_sqr_n_12(t2, t4, 30, p384_mod, p384_mp_mod);
            /* t1 = y ^ 0xfffffffffffff */
            sp_384_mont_mul_12(t1, t4, t2, p384_mod, p384_mp_mod);
            /* t2 = y ^ 0xfffffffffffffff000000000000000 */
            sp_384_mont_sqr_n_12(t2, t1, 60, p384_mod, p384_mp_mod);
            /* t1 = y ^ 0xffffffffffffffffffffffffffffff */
            sp_384_mont_mul_12(t1, t1, t2, p384_mod, p384_mp_mod);
            /* t2 = y ^ 0xffffffffffffffffffffffffffffff000000000000000000000000000000 */
            sp_384_mont_sqr_n_12(t2, t1, 120, p384_mod, p384_mp_mod);
            /* t1 = y ^ 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff */
            sp_384_mont_mul_12(t1, t1, t2, p384_mod, p384_mp_mod);
            /* t2 = y ^ 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8000 */
            sp_384_mont_sqr_n_12(t2, t1, 15, p384_mod, p384_mp_mod);
            /* t1 = y ^ 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff */
            sp_384_mont_mul_12(t1, t3, t2, p384_mod, p384_mp_mod);
            /* t2 = y ^ 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff80000000 */
            sp_384_mont_sqr_n_12(t2, t1, 31, p384_mod, p384_mp_mod);
            /* t1 = y ^ 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbfffffff */
            sp_384_mont_mul_12(t1, t4, t2, p384_mod, p384_mp_mod);
            /* t2 = y ^ 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbfffffff0 */
            sp_384_mont_sqr_n_12(t2, t1, 4, p384_mod, p384_mp_mod);
            /* t1 = y ^ 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbfffffffc */
            sp_384_mont_mul_12(t1, t5, t2, p384_mod, p384_mp_mod);
            /* t2 = y ^ 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff0000000000000000 */
            sp_384_mont_sqr_n_12(t2, t1, 62, p384_mod, p384_mp_mod);
            /* t1 = y ^ 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff0000000000000001 */
            sp_384_mont_mul_12(t1, y, t2, p384_mod, p384_mp_mod);
            /* t2 = y ^ 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbfffffffc00000000000000040000000 */
            sp_384_mont_sqr_n_12(y, t1, 30, p384_mod, p384_mp_mod);
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
    sp_digit xd[2 * 12];
    sp_digit yd[2 * 12];
#endif
    sp_digit* x = NULL;
    sp_digit* y = NULL;
    int err = MP_OKAY;

#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
    d = (sp_digit*)XMALLOC(sizeof(sp_digit) * 4 * 12, NULL, DYNAMIC_TYPE_ECC);
    if (d == NULL) {
        err = MEMORY_E;
    }
#endif

    if (err == MP_OKAY) {
#if (defined(WOLFSSL_SP_SMALL) || defined(WOLFSSL_SMALL_STACK)) && !defined(WOLFSSL_SP_NO_MALLOC)
        x = d + 0 * 12;
        y = d + 2 * 12;
#else
        x = xd;
        y = yd;
#endif

        sp_384_from_mp(x, 12, xm);
        err = sp_384_mod_mul_norm_12(x, x, p384_mod);
    }
    if (err == MP_OKAY) {
        /* y = x^3 */
        {
            sp_384_mont_sqr_12(y, x, p384_mod, p384_mp_mod);
            sp_384_mont_mul_12(y, y, x, p384_mod, p384_mp_mod);
        }
        /* y = x^3 - 3x */
        sp_384_mont_sub_12(y, y, x, p384_mod);
        sp_384_mont_sub_12(y, y, x, p384_mod);
        sp_384_mont_sub_12(y, y, x, p384_mod);
        /* y = x^3 - 3x + b */
        err = sp_384_mod_mul_norm_12(x, p384_b, p384_mod);
    }
    if (err == MP_OKAY) {
        sp_384_mont_add_12(y, y, x, p384_mod);
        /* y = sqrt(x^3 - 3x + b) */
        err = sp_384_mont_sqrt_12(y);
    }
    if (err == MP_OKAY) {
        XMEMSET(y + 12, 0, 12U * sizeof(sp_digit));
        sp_384_mont_reduce_12(y, p384_mod, p384_mp_mod);
        if ((((word32)y[0] ^ (word32)odd) & 1U) != 0U) {
            sp_384_mont_sub_12(y, p384_mod, y, p384_mod);
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
#endif /* WOLFSSL_SP_ARM_CORTEX_M_ASM */
#endif /* WOLFSSL_HAVE_SP_RSA || WOLFSSL_HAVE_SP_DH || WOLFSSL_HAVE_SP_ECC */
