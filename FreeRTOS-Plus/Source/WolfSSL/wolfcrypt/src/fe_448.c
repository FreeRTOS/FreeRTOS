/* fe_448.c
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

/* Based On Daniel J Bernstein's curve25519 Public Domain ref10 work.
 * Small implementation based on Daniel Beer's curve25519 public domain work.
 * Reworked for curve448 by Sean Parkinson.
 */

#ifdef HAVE_CONFIG_H
    #include <config.h>
#endif

#include <wolfssl/wolfcrypt/settings.h>

#if defined(HAVE_CURVE448) || defined(HAVE_ED448)

#include <wolfssl/wolfcrypt/fe_448.h>
#include <stdint.h>

#ifdef NO_INLINE
    #include <wolfssl/wolfcrypt/misc.h>
#else
    #define WOLFSSL_MISC_INCLUDED
    #include <wolfcrypt/src/misc.c>
#endif

#if defined(CURVE448_SMALL) || defined(ED448_SMALL)

/* Initialize the field element operations.
 */
void fe448_init(void)
{
}

/* Normalize the field element.
 * Ensure result is in range: 0..2^448-2^224-2
 *
 * a  [in]  Field element in range 0..2^448-1.
 */
void fe448_norm(uint8_t* a)
{
    int i;
    int16_t c = 0;
    int16_t o = 0;

    for (i = 0; i < 56; i++) {
        c += a[i];
        if ((i == 0) || (i == 28))
            c += 1;
        c >>= 8;
    }

    for (i = 0; i < 56; i++) {
        if ((i == 0) || (i == 28)) o += c;
        o += a[i];
        a[i] = (uint8_t)o;
        o >>= 8;
    }
}

/* Copy one field element into another: d = a.
 *
 * d  [in]  Destination field element.
 * a  [in]  Source field element.
 */
void fe448_copy(uint8_t* d, const uint8_t* a)
{
    int i;
    for (i = 0; i < 56; i++) {
         d[i] = a[i];
    }
}

/* Conditionally swap the elements.
 * Constant time implementation.
 *
 * a  [in]  First field element.
 * b  [in]  Second field element.
 * c  [in]  Swap when 1. Valid values: 0, 1.
 */
static void fe448_cswap(uint8_t* a, uint8_t* b, int c)
{
    int i;
    uint8_t mask = -(uint8_t)c;
    uint8_t t[56];

    for (i = 0; i < 56; i++)
        t[i] = (a[i] ^ b[i]) & mask;
    for (i = 0; i < 56; i++)
        a[i] ^= t[i];
    for (i = 0; i < 56; i++)
        b[i] ^= t[i];
}

/* Add two field elements. r = (a + b) mod (2^448 - 2^224 - 1)
 *
 * r  [in]  Field element to hold sum.
 * a  [in]  Field element to add.
 * b  [in]  Field element to add.
 */
void fe448_add(uint8_t* r, const uint8_t* a, const uint8_t* b)
{
    int i;
    int16_t c = 0;
    int16_t o = 0;

    for (i = 0; i < 56; i++) {
        c += a[i];
        c += b[i];
        r[i] = (uint8_t)c;
        c >>= 8;
    }

    for (i = 0; i < 56; i++) {
        if ((i == 0) || (i == 28)) o += c;
        o += r[i];
        r[i] = (uint8_t)o;
        o >>= 8;
    }
}

/* Subtract a field element from another. r = (a - b) mod (2^448 - 2^224 - 1)
 *
 * r  [in]  Field element to hold difference.
 * a  [in]  Field element to subtract from.
 * b  [in]  Field element to subtract.
 */
void fe448_sub(uint8_t* r, const uint8_t* a, const uint8_t* b)
{
    int i;
    int16_t c = 0;
    int16_t o = 0;

    for (i = 0; i < 56; i++) {
        if (i == 28)
            c += 0x1fc;
        else
            c += 0x1fe;
        c += a[i];
        c -= b[i];
        r[i] = (uint8_t)c;
        c >>= 8;
    }

    for (i = 0; i < 56; i++) {
        if ((i == 0) || (i == 28)) o += c;
        o += r[i];
        r[i] = (uint8_t)o;
        o >>= 8;
    }
}

/* Mulitply a field element by 39081. r = (39081 * a) mod (2^448 - 2^224 - 1)
 *
 * r  [in]  Field element to hold result.
 * a  [in]  Field element to multiply.
 */
void fe448_mul39081(uint8_t* r, const uint8_t* a)
{
    int i;
    int32_t c = 0;
    int32_t o = 0;

    for (i = 0; i < 56; i++) {
        c += a[i] * (int32_t)39081;
        r[i] = (uint8_t)c;
        c >>= 8;
    }

    for (i = 0; i < 56; i++) {
        if ((i == 0) || (i == 28)) o += c;
        o += r[i];
        r[i] = (uint8_t)o;
        o >>= 8;
    }
}

/* Mulitply two field elements. r = (a * b) mod (2^448 - 2^224 - 1)
 *
 * r  [in]  Field element to hold result.
 * a  [in]  Field element to multiply.
 * b  [in]  Field element to multiply.
 */
void fe448_mul(uint8_t* r, const uint8_t* a, const uint8_t* b)
{
    int i, k;
    int32_t c = 0;
    int16_t o = 0, cc = 0;
    uint8_t t[112];

    for (k = 0; k < 56; k++) {
        i = 0;
        for (; i <= k; i++) {
            c += (int32_t)a[i] * b[k - i];
        }
        t[k] = (uint8_t)c;
        c >>= 8;
    }
    for (; k < 111; k++) {
        i = k - 55;
        for (; i < 56; i++) {
            c += (int32_t)a[i] * b[k - i];
        }
        t[k] = (uint8_t)c;
        c >>= 8;
    }
    t[k] = (uint8_t)c;

    for (i = 0; i < 28; i++) {
        o += t[i];
        o += t[i + 56];
        o += t[i + 84];
        r[i] = (uint8_t)o;
        o >>= 8;
    }
    for (i = 28; i < 56; i++) {
        o += t[i];
        o += t[i + 56];
        o += t[i + 28];
        o += t[i + 56];
        r[i] = (uint8_t)o;
        o >>= 8;
    }
    for (i = 0; i < 56; i++) {
        if ((i == 0) || (i == 28)) cc += o;
        cc += r[i];
        r[i] = (uint8_t)cc;
        cc >>= 8;
    }
}

/* Square a field element. r = (a * a) mod (2^448 - 2^224 - 1)
 *
 * r  [in]  Field element to hold result.
 * a  [in]  Field element to square.
 */
void fe448_sqr(uint8_t* r, const uint8_t* a)
{
    int i, k;
    int32_t c = 0;
    int32_t p;
    int16_t o = 0, cc = 0;
    uint8_t t[112];

    for (k = 0; k < 56; k++) {
        i = 0;
        for (; i <= k; i++) {
            if (k - i < i)
                break;
            p = (int32_t)a[i] * a[k - i];
            if (k - i != i)
                p *= 2;
            c += p;
        }
        t[k] = (uint8_t)c;
        c >>= 8;
    }
    for (; k < 111; k++) {
         i = k - 55;
        for (; i < 56; i++) {
            if (k - i < i)
                break;
            p = (int32_t)a[i] * a[k - i];
            if (k - i != i)
                p *= 2;
            c += p;
        }
        t[k] = (uint8_t)c;
        c >>= 8;
    }
    t[k] = (uint8_t)c;

    for (i = 0; i < 28; i++) {
        o += t[i];
        o += t[i + 56];
        o += t[i + 84];
        r[i] = (uint8_t)o;
        o >>= 8;
    }
    for (i = 28; i < 56; i++) {
        o += t[i];
        o += t[i + 56];
        o += t[i + 28];
        o += t[i + 56];
        r[i] = (uint8_t)o;
        o >>= 8;
    }
    for (i = 0; i < 56; i++) {
        if ((i == 0) || (i == 28)) cc += o;
        cc += r[i];
        r[i] = (uint8_t)cc;
        cc >>= 8;
    }
    fe448_norm(r);
}

/* Invert the field element. (r * a) mod (2^448 - 2^224 - 1) = 1
 * Constant time implementation - using Fermat's little theorem:
 *   a^(p-1) mod p = 1 => a^(p-2) mod p = 1/a
 * For curve448: p - 2 = 2^448 - 2^224 - 3
 *
 * r  [in]  Field element to hold result.
 * a  [in]  Field element to invert.
 */
void fe448_invert(uint8_t* r, const uint8_t* a)
{
    int i;
    uint8_t t[56];

    fe448_sqr(t, a);
    fe448_mul(t, t, a);
    for (i = 0; i < 221; i++) {
        fe448_sqr(t, t);
        fe448_mul(t, t, a);
    }
    fe448_sqr(t, t);
    for (i = 0; i < 222; i++) {
        fe448_sqr(t, t);
        fe448_mul(t, t, a);
    }
    fe448_sqr(t, t);
    fe448_sqr(t, t);
    fe448_mul(r, t, a);
}

/* Scalar multiply the point by a number. r = n.a
 * Uses Montogmery ladder and only requires the x-ordinate.
 *
 * r  [in]  Field element to hold result.
 * n  [in]  Scalar as an array of bytes.
 * a  [in]  Point to multiply - x-ordinate only.
 */
int curve448(byte* r, const byte* n, const byte* a)
{
    uint8_t x1[56];
    uint8_t x2[56] = {1};
    uint8_t z2[56] = {0};
    uint8_t x3[56];
    uint8_t z3[56] = {1};
    uint8_t t0[56];
    uint8_t t1[56];
    int i;
    unsigned int swap;
    unsigned int b;

    fe448_copy(x1, a);
    fe448_copy(x3, a);

    swap = 0;
    for (i = 447; i >= 0; --i) {
        b = (n[i >> 3] >> (i & 7)) & 1;
        swap ^= b;
        fe448_cswap(x2, x3, swap);
        fe448_cswap(z2, z3, swap);
        swap = b;

        /* Montgomery Ladder - double and add */
        fe448_add(t0, x2, z2);
        fe448_add(t1, x3, z3);
        fe448_sub(x2, x2, z2);
        fe448_sub(x3, x3, z3);
        fe448_mul(t1, t1, x2);
        fe448_mul(z3, x3, t0);
        fe448_sqr(t0, t0);
        fe448_sqr(x2, x2);
        fe448_add(x3, z3, t1);
        fe448_sqr(x3, x3);
        fe448_sub(z3, z3, t1);
        fe448_sqr(z3, z3);
        fe448_mul(z3, z3, x1);
        fe448_sub(t1, t0, x2);
        fe448_mul(x2, t0, x2);
        fe448_mul39081(z2, t1);
        fe448_add(z2, t0, z2);
        fe448_mul(z2, z2, t1);
    }
    fe448_cswap(x2, x3, swap);
    fe448_cswap(z2, z3, swap);

    fe448_invert(z2, z2);
    fe448_mul(r, x2, z2);
    fe448_norm(r);

    return 0;
}

#ifdef HAVE_ED448
/* Check whether field element is not 0.
 * Field element must have been normalized before call.
 *
 * a  [in]  Field element.
 * returns 0 when zero, and any other value otherwise.
 */
int fe448_isnonzero(const uint8_t* a)
{
    int i;
    uint8_t c = 0;
    for (i = 0; i < 56; i++)
        c |= a[i];
    return c;
}

/* Negates the field element. r = -a mod (2^448 - 2^224 - 1)
 * Add 0x200 to each element and subtract 2 from next.
 * Top element overflow handled by subtracting 2 from index 0 and 28.
 *
 * r  [in]  Field element to hold result.
 * a  [in]  Field element.
 */
void fe448_neg(uint8_t* r, const uint8_t* a)
{
    int i;
    int16_t c = 0;
    int16_t o = 0;

    for (i = 0; i < 56; i++) {
        if (i == 28)
            c += 0x1fc;
        else
            c += 0x1fe;
        c -= a[i];
        r[i] = (uint8_t)c;
        c >>= 8;
    }

    for (i = 0; i < 56; i++) {
        if ((i == 0) || (i == 28)) o += c;
        o += r[i];
        r[i] = (uint8_t)o;
        o >>= 8;
    }
}

/* Raise field element to (p-3) / 4: 2^446 - 2^222 - 1
 * Used for calcualting y-ordinate from x-ordinate for Ed448.
 *
 * r  [in]  Field element to hold result.
 * a  [in]  Field element to exponentiate.
 */
void fe448_pow_2_446_222_1(uint8_t* r, const uint8_t* a)
{
    int i;
    uint8_t t[56];

    fe448_sqr(t, a);
    fe448_mul(t, t, a);
    for (i = 0; i < 221; i++) {
        fe448_sqr(t, t);
        fe448_mul(t, t, a);
    }
    fe448_sqr(t, t);
    for (i = 0; i < 221; i++) {
        fe448_sqr(t, t);
        fe448_mul(t, t, a);
    }
    fe448_sqr(t, t);
    fe448_mul(r, t, a);
}

/* Constant time, conditional move of b into a.
 * a is not changed if the condition is 0.
 *
 * a  A field element.
 * b  A field element.
 * c  If 1 then copy and if 0 then don't copy.
 */
void fe448_cmov(uint8_t* a, const uint8_t* b, int c)
{
    int i;
    uint8_t m = -(uint8_t)c;
    uint8_t t[56];

    for (i = 0; i < 56; i++)
        t[i] = m & (a[i] ^ b[i]);
    for (i = 0; i < 56; i++)
        a[i] ^= t[i];
}

#endif /* HAVE_ED448 */
#elif defined(CURVED448_128BIT)

/* Initialize the field element operations.
 */
void fe448_init(void)
{
}

/* Convert the field element from a byte array to an array of 56-bits.
 *
 * r  [in]  Array to encode into.
 * b  [in]  Byte array.
 */
void fe448_from_bytes(int64_t* r, const unsigned char* b)
{
    r[ 0] =  ((int64_t) (b[ 0]) <<  0)
          |  ((int64_t) (b[ 1]) <<  8)
          |  ((int64_t) (b[ 2]) << 16)
          |  ((int64_t) (b[ 3]) << 24)
          |  ((int64_t) (b[ 4]) << 32)
          |  ((int64_t) (b[ 5]) << 40)
          |  ((int64_t) (b[ 6]) << 48);
    r[ 1] =  ((int64_t) (b[ 7]) <<  0)
          |  ((int64_t) (b[ 8]) <<  8)
          |  ((int64_t) (b[ 9]) << 16)
          |  ((int64_t) (b[10]) << 24)
          |  ((int64_t) (b[11]) << 32)
          |  ((int64_t) (b[12]) << 40)
          |  ((int64_t) (b[13]) << 48);
    r[ 2] =  ((int64_t) (b[14]) <<  0)
          |  ((int64_t) (b[15]) <<  8)
          |  ((int64_t) (b[16]) << 16)
          |  ((int64_t) (b[17]) << 24)
          |  ((int64_t) (b[18]) << 32)
          |  ((int64_t) (b[19]) << 40)
          |  ((int64_t) (b[20]) << 48);
    r[ 3] =  ((int64_t) (b[21]) <<  0)
          |  ((int64_t) (b[22]) <<  8)
          |  ((int64_t) (b[23]) << 16)
          |  ((int64_t) (b[24]) << 24)
          |  ((int64_t) (b[25]) << 32)
          |  ((int64_t) (b[26]) << 40)
          |  ((int64_t) (b[27]) << 48);
    r[ 4] =  ((int64_t) (b[28]) <<  0)
          |  ((int64_t) (b[29]) <<  8)
          |  ((int64_t) (b[30]) << 16)
          |  ((int64_t) (b[31]) << 24)
          |  ((int64_t) (b[32]) << 32)
          |  ((int64_t) (b[33]) << 40)
          |  ((int64_t) (b[34]) << 48);
    r[ 5] =  ((int64_t) (b[35]) <<  0)
          |  ((int64_t) (b[36]) <<  8)
          |  ((int64_t) (b[37]) << 16)
          |  ((int64_t) (b[38]) << 24)
          |  ((int64_t) (b[39]) << 32)
          |  ((int64_t) (b[40]) << 40)
          |  ((int64_t) (b[41]) << 48);
    r[ 6] =  ((int64_t) (b[42]) <<  0)
          |  ((int64_t) (b[43]) <<  8)
          |  ((int64_t) (b[44]) << 16)
          |  ((int64_t) (b[45]) << 24)
          |  ((int64_t) (b[46]) << 32)
          |  ((int64_t) (b[47]) << 40)
          |  ((int64_t) (b[48]) << 48);
    r[ 7] =  ((int64_t) (b[49]) <<  0)
          |  ((int64_t) (b[50]) <<  8)
          |  ((int64_t) (b[51]) << 16)
          |  ((int64_t) (b[52]) << 24)
          |  ((int64_t) (b[53]) << 32)
          |  ((int64_t) (b[54]) << 40)
          |  ((int64_t) (b[55]) << 48);
}

/* Convert the field element to a byte array from an array of 56-bits.
 *
 * b  [in]  Byte array.
 * a  [in]  Array to encode into.
 */
void fe448_to_bytes(unsigned char* b, const int64_t* a)
{
    int128_t t;
    /* Mod */
    int64_t in0 = a[0];
    int64_t in1 = a[1];
    int64_t in2 = a[2];
    int64_t in3 = a[3];
    int64_t in4 = a[4];
    int64_t in5 = a[5];
    int64_t in6 = a[6];
    int64_t in7 = a[7];
    int64_t o = in7 >> 56;
    in7 -= o << 56;
    in0 += o;
    in4 += o;
    o = (in0 + 1) >> 56;
    o = (o + in1) >> 56;
    o = (o + in2) >> 56;
    o = (o + in3) >> 56;
    o = (o + in4 + 1) >> 56;
    o = (o + in5) >> 56;
    o = (o + in6) >> 56;
    o = (o + in7) >> 56;
    in0 += o;
    in4 += o;
    in7 -= o << 56;
    o = (int64_t)(in0  >> 56); in1  += o; t = o << 56; in0  -= t;
    o = (int64_t)(in1  >> 56); in2  += o; t = o << 56; in1  -= t;
    o = (int64_t)(in2  >> 56); in3  += o; t = o << 56; in2  -= t;
    o = (int64_t)(in3  >> 56); in4  += o; t = o << 56; in3  -= t;
    o = (int64_t)(in4  >> 56); in5  += o; t = o << 56; in4  -= t;
    o = (int64_t)(in5  >> 56); in6  += o; t = o << 56; in5  -= t;
    o = (int64_t)(in6  >> 56); in7  += o; t = o << 56; in6  -= t;
    o = (int64_t)(in7  >> 56); in0  += o;
                    in4  += o; t = o << 56; in7  -= t;

    /* Output as bytes */
    b[ 0] = (in0  >>  0);
    b[ 1] = (in0  >>  8);
    b[ 2] = (in0  >> 16);
    b[ 3] = (in0  >> 24);
    b[ 4] = (in0  >> 32);
    b[ 5] = (in0  >> 40);
    b[ 6] = (in0  >> 48);
    b[ 7] = (in1  >>  0);
    b[ 8] = (in1  >>  8);
    b[ 9] = (in1  >> 16);
    b[10] = (in1  >> 24);
    b[11] = (in1  >> 32);
    b[12] = (in1  >> 40);
    b[13] = (in1  >> 48);
    b[14] = (in2  >>  0);
    b[15] = (in2  >>  8);
    b[16] = (in2  >> 16);
    b[17] = (in2  >> 24);
    b[18] = (in2  >> 32);
    b[19] = (in2  >> 40);
    b[20] = (in2  >> 48);
    b[21] = (in3  >>  0);
    b[22] = (in3  >>  8);
    b[23] = (in3  >> 16);
    b[24] = (in3  >> 24);
    b[25] = (in3  >> 32);
    b[26] = (in3  >> 40);
    b[27] = (in3  >> 48);
    b[28] = (in4  >>  0);
    b[29] = (in4  >>  8);
    b[30] = (in4  >> 16);
    b[31] = (in4  >> 24);
    b[32] = (in4  >> 32);
    b[33] = (in4  >> 40);
    b[34] = (in4  >> 48);
    b[35] = (in5  >>  0);
    b[36] = (in5  >>  8);
    b[37] = (in5  >> 16);
    b[38] = (in5  >> 24);
    b[39] = (in5  >> 32);
    b[40] = (in5  >> 40);
    b[41] = (in5  >> 48);
    b[42] = (in6  >>  0);
    b[43] = (in6  >>  8);
    b[44] = (in6  >> 16);
    b[45] = (in6  >> 24);
    b[46] = (in6  >> 32);
    b[47] = (in6  >> 40);
    b[48] = (in6  >> 48);
    b[49] = (in7  >>  0);
    b[50] = (in7  >>  8);
    b[51] = (in7  >> 16);
    b[52] = (in7  >> 24);
    b[53] = (in7  >> 32);
    b[54] = (in7  >> 40);
    b[55] = (in7  >> 48);
}

/* Set the field element to 0.
 *
 * a  [in]  Field element.
 */
void fe448_1(int64_t* a)
{
    a[0] = 1;
    a[1] = 0;
    a[2] = 0;
    a[3] = 0;
    a[4] = 0;
    a[5] = 0;
    a[6] = 0;
    a[7] = 0;
}

/* Set the field element to 0.
 *
 * a  [in]  Field element.
 */
void fe448_0(int64_t* a)
{
    a[0] = 0;
    a[1] = 0;
    a[2] = 0;
    a[3] = 0;
    a[4] = 0;
    a[5] = 0;
    a[6] = 0;
    a[7] = 0;
}

/* Copy one field element into another: d = a.
 *
 * d  [in]  Destination field element.
 * a  [in]  Source field element.
 */
void fe448_copy(int64_t* d, const int64_t* a)
{
    d[0] = a[0];
    d[1] = a[1];
    d[2] = a[2];
    d[3] = a[3];
    d[4] = a[4];
    d[5] = a[5];
    d[6] = a[6];
    d[7] = a[7];
}

/* Conditionally swap the elements.
 * Constant time implementation.
 *
 * a  [in]  First field element.
 * b  [in]  Second field element.
 * c  [in]  Swap when 1. Valid values: 0, 1.
 */
static void fe448_cswap(int64_t* a, int64_t* b, int c)
{
    int64_t mask = -(int64_t)c;
    int64_t t0 = (a[0] ^ b[0]) & mask;
    int64_t t1 = (a[1] ^ b[1]) & mask;
    int64_t t2 = (a[2] ^ b[2]) & mask;
    int64_t t3 = (a[3] ^ b[3]) & mask;
    int64_t t4 = (a[4] ^ b[4]) & mask;
    int64_t t5 = (a[5] ^ b[5]) & mask;
    int64_t t6 = (a[6] ^ b[6]) & mask;
    int64_t t7 = (a[7] ^ b[7]) & mask;
    a[0] ^= t0;
    a[1] ^= t1;
    a[2] ^= t2;
    a[3] ^= t3;
    a[4] ^= t4;
    a[5] ^= t5;
    a[6] ^= t6;
    a[7] ^= t7;
    b[0] ^= t0;
    b[1] ^= t1;
    b[2] ^= t2;
    b[3] ^= t3;
    b[4] ^= t4;
    b[5] ^= t5;
    b[6] ^= t6;
    b[7] ^= t7;
}

/* Add two field elements. r = (a + b) mod (2^448 - 2^224 - 1)
 *
 * r  [in]  Field element to hold sum.
 * a  [in]  Field element to add.
 * b  [in]  Field element to add.
 */
void fe448_add(int64_t* r, const int64_t* a, const int64_t* b)
{
    r[0] = a[0] + b[0];
    r[1] = a[1] + b[1];
    r[2] = a[2] + b[2];
    r[3] = a[3] + b[3];
    r[4] = a[4] + b[4];
    r[5] = a[5] + b[5];
    r[6] = a[6] + b[6];
    r[7] = a[7] + b[7];
}

/* Subtract a field element from another. r = (a - b) mod (2^448 - 2^224 - 1)
 *
 * r  [in]  Field element to hold difference.
 * a  [in]  Field element to subtract from.
 * b  [in]  Field element to subtract.
 */
void fe448_sub(int64_t* r, const int64_t* a, const int64_t* b)
{
    r[0] = a[0] - b[0];
    r[1] = a[1] - b[1];
    r[2] = a[2] - b[2];
    r[3] = a[3] - b[3];
    r[4] = a[4] - b[4];
    r[5] = a[5] - b[5];
    r[6] = a[6] - b[6];
    r[7] = a[7] - b[7];
}

/* Mulitply a field element by 39081. r = (39081 * a) mod (2^448 - 2^224 - 1)
 *
 * r  [in]  Field element to hold result.
 * a  [in]  Field element to multiply.
 */
void fe448_mul39081(int64_t* r, const int64_t* a)
{
    int128_t t;
    int64_t o;
    int128_t t0 = a[0] * (int128_t)39081;
    int128_t t1 = a[1] * (int128_t)39081;
    int128_t t2 = a[2] * (int128_t)39081;
    int128_t t3 = a[3] * (int128_t)39081;
    int128_t t4 = a[4] * (int128_t)39081;
    int128_t t5 = a[5] * (int128_t)39081;
    int128_t t6 = a[6] * (int128_t)39081;
    int128_t t7 = a[7] * (int128_t)39081;
    o = (int64_t)(t0  >> 56); t1  += o; t = (int128_t)o << 56; t0  -= t;
    o = (int64_t)(t1  >> 56); t2  += o; t = (int128_t)o << 56; t1  -= t;
    o = (int64_t)(t2  >> 56); t3  += o; t = (int128_t)o << 56; t2  -= t;
    o = (int64_t)(t3  >> 56); t4  += o; t = (int128_t)o << 56; t3  -= t;
    o = (int64_t)(t4  >> 56); t5  += o; t = (int128_t)o << 56; t4  -= t;
    o = (int64_t)(t5  >> 56); t6  += o; t = (int128_t)o << 56; t5  -= t;
    o = (int64_t)(t6  >> 56); t7  += o; t = (int128_t)o << 56; t6  -= t;
    o = (int64_t)(t7  >> 56); t0  += o;
                   t4  += o; t = (int128_t)o << 56; t7  -= t;

    /* Store */
    r[0] = (int64_t)t0;
    r[1] = (int64_t)t1;
    r[2] = (int64_t)t2;
    r[3] = (int64_t)t3;
    r[4] = (int64_t)t4;
    r[5] = (int64_t)t5;
    r[6] = (int64_t)t6;
    r[7] = (int64_t)t7;
}

/* Mulitply two field elements. r = (a * b) mod (2^448 - 2^224 - 1)
 *
 * r  [in]  Field element to hold result.
 * a  [in]  Field element to multiply.
 * b  [in]  Field element to multiply.
 */
void fe448_mul(int64_t* r, const int64_t* a, const int64_t* b)
{
    int128_t t;
    int64_t o;
    int128_t t0   = (int128_t)a[ 0] * b[ 0];
    int128_t t1   = (int128_t)a[ 0] * b[ 1];
    int128_t t101 = (int128_t)a[ 1] * b[ 0];
    int128_t t2   = (int128_t)a[ 0] * b[ 2];
    int128_t t102 = (int128_t)a[ 1] * b[ 1];
    int128_t t202 = (int128_t)a[ 2] * b[ 0];
    int128_t t3   = (int128_t)a[ 0] * b[ 3];
    int128_t t103 = (int128_t)a[ 1] * b[ 2];
    int128_t t203 = (int128_t)a[ 2] * b[ 1];
    int128_t t303 = (int128_t)a[ 3] * b[ 0];
    int128_t t4   = (int128_t)a[ 0] * b[ 4];
    int128_t t104 = (int128_t)a[ 1] * b[ 3];
    int128_t t204 = (int128_t)a[ 2] * b[ 2];
    int128_t t304 = (int128_t)a[ 3] * b[ 1];
    int128_t t404 = (int128_t)a[ 4] * b[ 0];
    int128_t t5   = (int128_t)a[ 0] * b[ 5];
    int128_t t105 = (int128_t)a[ 1] * b[ 4];
    int128_t t205 = (int128_t)a[ 2] * b[ 3];
    int128_t t305 = (int128_t)a[ 3] * b[ 2];
    int128_t t405 = (int128_t)a[ 4] * b[ 1];
    int128_t t505 = (int128_t)a[ 5] * b[ 0];
    int128_t t6   = (int128_t)a[ 0] * b[ 6];
    int128_t t106 = (int128_t)a[ 1] * b[ 5];
    int128_t t206 = (int128_t)a[ 2] * b[ 4];
    int128_t t306 = (int128_t)a[ 3] * b[ 3];
    int128_t t406 = (int128_t)a[ 4] * b[ 2];
    int128_t t506 = (int128_t)a[ 5] * b[ 1];
    int128_t t606 = (int128_t)a[ 6] * b[ 0];
    int128_t t7   = (int128_t)a[ 0] * b[ 7];
    int128_t t107 = (int128_t)a[ 1] * b[ 6];
    int128_t t207 = (int128_t)a[ 2] * b[ 5];
    int128_t t307 = (int128_t)a[ 3] * b[ 4];
    int128_t t407 = (int128_t)a[ 4] * b[ 3];
    int128_t t507 = (int128_t)a[ 5] * b[ 2];
    int128_t t607 = (int128_t)a[ 6] * b[ 1];
    int128_t t707 = (int128_t)a[ 7] * b[ 0];
    int128_t t8   = (int128_t)a[ 1] * b[ 7];
    int128_t t108 = (int128_t)a[ 2] * b[ 6];
    int128_t t208 = (int128_t)a[ 3] * b[ 5];
    int128_t t308 = (int128_t)a[ 4] * b[ 4];
    int128_t t408 = (int128_t)a[ 5] * b[ 3];
    int128_t t508 = (int128_t)a[ 6] * b[ 2];
    int128_t t608 = (int128_t)a[ 7] * b[ 1];
    int128_t t9   = (int128_t)a[ 2] * b[ 7];
    int128_t t109 = (int128_t)a[ 3] * b[ 6];
    int128_t t209 = (int128_t)a[ 4] * b[ 5];
    int128_t t309 = (int128_t)a[ 5] * b[ 4];
    int128_t t409 = (int128_t)a[ 6] * b[ 3];
    int128_t t509 = (int128_t)a[ 7] * b[ 2];
    int128_t t10  = (int128_t)a[ 3] * b[ 7];
    int128_t t110 = (int128_t)a[ 4] * b[ 6];
    int128_t t210 = (int128_t)a[ 5] * b[ 5];
    int128_t t310 = (int128_t)a[ 6] * b[ 4];
    int128_t t410 = (int128_t)a[ 7] * b[ 3];
    int128_t t11  = (int128_t)a[ 4] * b[ 7];
    int128_t t111 = (int128_t)a[ 5] * b[ 6];
    int128_t t211 = (int128_t)a[ 6] * b[ 5];
    int128_t t311 = (int128_t)a[ 7] * b[ 4];
    int128_t t12  = (int128_t)a[ 5] * b[ 7];
    int128_t t112 = (int128_t)a[ 6] * b[ 6];
    int128_t t212 = (int128_t)a[ 7] * b[ 5];
    int128_t t13  = (int128_t)a[ 6] * b[ 7];
    int128_t t113 = (int128_t)a[ 7] * b[ 6];
    int128_t t14  = (int128_t)a[ 7] * b[ 7];
    t1  += t101;
    t2  += t102; t2  += t202;
    t3  += t103; t3  += t203; t3  += t303;
    t4  += t104; t4  += t204; t4  += t304; t4  += t404;
    t5  += t105; t5  += t205; t5  += t305; t5  += t405; t5  += t505;
    t6  += t106; t6  += t206; t6  += t306; t6  += t406; t6  += t506;
    t6  += t606;
    t7  += t107; t7  += t207; t7  += t307; t7  += t407; t7  += t507;
    t7  += t607;
    t7  += t707;
    t8  += t108; t8  += t208; t8  += t308; t8  += t408; t8  += t508;
    t8  += t608;
    t9  += t109; t9  += t209; t9  += t309; t9  += t409; t9  += t509;
    t10 += t110; t10 += t210; t10 += t310; t10 += t410;
    t11 += t111; t11 += t211; t11 += t311;
    t12 += t112; t12 += t212;
    t13 += t113;

    /* Reduce */
    t0  += t8  + t12;
    t1  += t9  + t13;
    t2  += t10 + t14;
    t3  += t11;
    t4  += t12 + t8  + t12;
    t5  += t13 + t9  + t13;
    t6  += t14 + t10 + t14;
    t7  +=       t11;
    o = t7  >> 56; t0  += o;
                   t4  += o; t = (int128_t)o << 56; t7  -= t;
    o = (int64_t)(t0  >> 56); t1  += o; t = (int128_t)o << 56; t0  -= t;
    o = (int64_t)(t1  >> 56); t2  += o; t = (int128_t)o << 56; t1  -= t;
    o = (int64_t)(t2  >> 56); t3  += o; t = (int128_t)o << 56; t2  -= t;
    o = (int64_t)(t3  >> 56); t4  += o; t = (int128_t)o << 56; t3  -= t;
    o = (int64_t)(t4  >> 56); t5  += o; t = (int128_t)o << 56; t4  -= t;
    o = (int64_t)(t5  >> 56); t6  += o; t = (int128_t)o << 56; t5  -= t;
    o = (int64_t)(t6  >> 56); t7  += o; t = (int128_t)o << 56; t6  -= t;
    o = (int64_t)(t7  >> 56); t0  += o;
                   t4  += o; t = (int128_t)o << 56; t7  -= t;

    /* Store */
    r[0] = (int64_t)t0;
    r[1] = (int64_t)t1;
    r[2] = (int64_t)t2;
    r[3] = (int64_t)t3;
    r[4] = (int64_t)t4;
    r[5] = (int64_t)t5;
    r[6] = (int64_t)t6;
    r[7] = (int64_t)t7;
}

/* Square a field element. r = (a * a) mod (2^448 - 2^224 - 1)
 *
 * r  [in]  Field element to hold result.
 * a  [in]  Field element to square.
 */
void fe448_sqr(int64_t* r, const int64_t* a)
{
    int128_t t;
    int64_t o;
    int128_t t0   =     (int128_t)a[ 0] * a[ 0];
    int128_t t1   = 2 * (int128_t)a[ 0] * a[ 1];
    int128_t t2   = 2 * (int128_t)a[ 0] * a[ 2];
    int128_t t102 =     (int128_t)a[ 1] * a[ 1];
    int128_t t3   = 2 * (int128_t)a[ 0] * a[ 3];
    int128_t t103 = 2 * (int128_t)a[ 1] * a[ 2];
    int128_t t4   = 2 * (int128_t)a[ 0] * a[ 4];
    int128_t t104 = 2 * (int128_t)a[ 1] * a[ 3];
    int128_t t204 =     (int128_t)a[ 2] * a[ 2];
    int128_t t5   = 2 * (int128_t)a[ 0] * a[ 5];
    int128_t t105 = 2 * (int128_t)a[ 1] * a[ 4];
    int128_t t205 = 2 * (int128_t)a[ 2] * a[ 3];
    int128_t t6   = 2 * (int128_t)a[ 0] * a[ 6];
    int128_t t106 = 2 * (int128_t)a[ 1] * a[ 5];
    int128_t t206 = 2 * (int128_t)a[ 2] * a[ 4];
    int128_t t306 =     (int128_t)a[ 3] * a[ 3];
    int128_t t7   = 2 * (int128_t)a[ 0] * a[ 7];
    int128_t t107 = 2 * (int128_t)a[ 1] * a[ 6];
    int128_t t207 = 2 * (int128_t)a[ 2] * a[ 5];
    int128_t t307 = 2 * (int128_t)a[ 3] * a[ 4];
    int128_t t8   = 2 * (int128_t)a[ 1] * a[ 7];
    int128_t t108 = 2 * (int128_t)a[ 2] * a[ 6];
    int128_t t208 = 2 * (int128_t)a[ 3] * a[ 5];
    int128_t t308 =     (int128_t)a[ 4] * a[ 4];
    int128_t t9   = 2 * (int128_t)a[ 2] * a[ 7];
    int128_t t109 = 2 * (int128_t)a[ 3] * a[ 6];
    int128_t t209 = 2 * (int128_t)a[ 4] * a[ 5];
    int128_t t10  = 2 * (int128_t)a[ 3] * a[ 7];
    int128_t t110 = 2 * (int128_t)a[ 4] * a[ 6];
    int128_t t210 =     (int128_t)a[ 5] * a[ 5];
    int128_t t11  = 2 * (int128_t)a[ 4] * a[ 7];
    int128_t t111 = 2 * (int128_t)a[ 5] * a[ 6];
    int128_t t12  = 2 * (int128_t)a[ 5] * a[ 7];
    int128_t t112 =     (int128_t)a[ 6] * a[ 6];
    int128_t t13  = 2 * (int128_t)a[ 6] * a[ 7];
    int128_t t14  =     (int128_t)a[ 7] * a[ 7];
    t2  += t102;
    t3  += t103;
    t4  += t104; t4  += t204;
    t5  += t105; t5  += t205;
    t6  += t106; t6  += t206; t6  += t306;
    t7  += t107; t7  += t207; t7  += t307;
    t8  += t108; t8  += t208; t8  += t308;
    t9  += t109; t9  += t209;
    t10 += t110; t10 += t210;
    t11 += t111;
    t12 += t112;

    /* Reduce */
    t0  += t8  + t12;
    t1  += t9  + t13;
    t2  += t10 + t14;
    t3  += t11;
    t4  += t12 + t8  + t12;
    t5  += t13 + t9  + t13;
    t6  += t14 + t10 + t14;
    t7  +=       t11;
    o = t7  >> 56; t0  += o;
                   t4  += o; t = (int128_t)o << 56; t7  -= t;
    o = (int64_t)(t0  >> 56); t1  += o; t = (int128_t)o << 56; t0  -= t;
    o = (int64_t)(t1  >> 56); t2  += o; t = (int128_t)o << 56; t1  -= t;
    o = (int64_t)(t2  >> 56); t3  += o; t = (int128_t)o << 56; t2  -= t;
    o = (int64_t)(t3  >> 56); t4  += o; t = (int128_t)o << 56; t3  -= t;
    o = (int64_t)(t4  >> 56); t5  += o; t = (int128_t)o << 56; t4  -= t;
    o = (int64_t)(t5  >> 56); t6  += o; t = (int128_t)o << 56; t5  -= t;
    o = (int64_t)(t6  >> 56); t7  += o; t = (int128_t)o << 56; t6  -= t;
    o = (int64_t)(t7  >> 56); t0  += o;
                   t4  += o; t = (int128_t)o << 56; t7  -= t;

    /* Store */
    r[0] = (int64_t)t0;
    r[1] = (int64_t)t1;
    r[2] = (int64_t)t2;
    r[3] = (int64_t)t3;
    r[4] = (int64_t)t4;
    r[5] = (int64_t)t5;
    r[6] = (int64_t)t6;
    r[7] = (int64_t)t7;
}

/* Invert the field element. (r * a) mod (2^448 - 2^224 - 1) = 1
 * Constant time implementation - using Fermat's little theorem:
 *   a^(p-1) mod p = 1 => a^(p-2) mod p = 1/a
 * For curve448: p - 2 = 2^448 - 2^224 - 3
 *
 * r  [in]  Field element to hold result.
 * a  [in]  Field element to invert.
 */
void fe448_invert(int64_t* r, const int64_t* a)
{
    int64_t t1[8];
    int64_t t2[8];
    int64_t t3[8];
    int64_t t4[8];
    int i;

    fe448_sqr(t1, a);
    /* t1 = 2 */
    fe448_mul(t1, t1, a);
    /* t1 = 3 */
    fe448_sqr(t2, t1); for (i = 1; i < 2; ++i) fe448_sqr(t2, t2);
    /* t2 = c */
    fe448_mul(t3, t2, a);
    /* t3 = d */
    fe448_mul(t1, t2, t1);
    /* t1 = f */
    fe448_sqr(t2, t1);
    /* t2 = 1e */
    fe448_mul(t4, t2, a);
    /* t4 = 1f */
    fe448_sqr(t2, t4); for (i = 1; i < 5; ++i) fe448_sqr(t2, t2);
    /* t2 = 3e0 */
    fe448_mul(t1, t2, t4);
    /* t1 = 3ff */
    fe448_sqr(t2, t1); for (i = 1; i < 10; ++i) fe448_sqr(t2, t2);
    /* t2 = ffc00 */
    fe448_mul(t1, t2, t1);
    /* t1 = fffff */
    fe448_sqr(t2, t1); for (i = 1; i < 5; ++i) fe448_sqr(t2, t2);
    /* t2 = 1ffffe0 */
    fe448_mul(t1, t2, t4);
    /* t1 = 1ffffff */
    fe448_sqr(t2, t1); for (i = 1; i < 25; ++i) fe448_sqr(t2, t2);
    /* t2 = 3fffffe000000 */
    fe448_mul(t1, t2, t1);
    /* t1 = 3ffffffffffff */
    fe448_sqr(t2, t1); for (i = 1; i < 5; ++i) fe448_sqr(t2, t2);
    /* t2 = 7fffffffffffe0 */
    fe448_mul(t1, t2, t4);
    /* t1 = 7fffffffffffff */
    fe448_sqr(t2, t1); for (i = 1; i < 55; ++i) fe448_sqr(t2, t2);
    /* t2 = 3fffffffffffff80000000000000 */
    fe448_mul(t1, t2, t1);
    /* t1 = 3fffffffffffffffffffffffffff */
    fe448_sqr(t2, t1); for (i = 1; i < 110; ++i) fe448_sqr(t2, t2);
    /* t2 = fffffffffffffffffffffffffffc000000000000000000000000000 */
    fe448_mul(t1, t2, t1);
    /* t1 = fffffffffffffffffffffffffffffffffffffffffffffffffffffff */
    fe448_sqr(t2, t1); for (i = 1; i < 4; ++i) fe448_sqr(t2, t2);
    /* t2 = fffffffffffffffffffffffffffffffffffffffffffffffffffffff0 */
    fe448_mul(t3, t3, t2);
    /* t3 = fffffffffffffffffffffffffffffffffffffffffffffffffffffffd */
    fe448_mul(t1, t3, a);
    /* t1 = fffffffffffffffffffffffffffffffffffffffffffffffffffffffe */
    fe448_sqr(t1, t1); for (i = 1; i < 224; ++i) fe448_sqr(t1, t1);
    /* t1 = fffffffffffffffffffffffffffffffffffffffffffffffffffffffe00000000000000000000000000000000000000000000000000000000 */
    fe448_mul(r, t3, t1);
    /* r = fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffffffffffffffffffffffffffffffffffffffffffffffffffffd */
}

/* Scalar multiply the point by a number. r = n.a
 * Uses Montogmery ladder and only requires the x-ordinate.
 *
 * r  [in]  Field element to hold result.
 * n  [in]  Scalar as an array of bytes.
 * a  [in]  Point to multiply - x-ordinate only.
 */
int curve448(byte* r, const byte* n, const byte* a)
{
    int64_t x1[8];
    int64_t x2[8];
    int64_t z2[8];
    int64_t x3[8];
    int64_t z3[8];
    int64_t t0[8];
    int64_t t1[8];
    int i;
    unsigned int swap;
    unsigned int b;

    fe448_from_bytes(x1, a);
    fe448_1(x2);
    fe448_0(z2);
    fe448_copy(x3, x1);
    fe448_1(z3);

    swap = 0;
    for (i = 447; i >= 0; --i) {
        b = (n[i >> 3] >> (i & 7)) & 1;
        swap ^= b;
        fe448_cswap(x2, x3, swap);
        fe448_cswap(z2, z3, swap);
        swap = b;

        /* Montgomery Ladder - double and add */
        fe448_add(t0, x2, z2);
        fe448_reduce(t0);
        fe448_add(t1, x3, z3);
        fe448_reduce(t1);
        fe448_sub(x2, x2, z2);
        fe448_sub(x3, x3, z3);
        fe448_mul(t1, t1, x2);
        fe448_mul(z3, x3, t0);
        fe448_sqr(t0, t0);
        fe448_sqr(x2, x2);
        fe448_add(x3, z3, t1);
        fe448_reduce(x3);
        fe448_sqr(x3, x3);
        fe448_sub(z3, z3, t1);
        fe448_sqr(z3, z3);
        fe448_mul(z3, z3, x1);
        fe448_sub(t1, t0, x2);
        fe448_mul(x2, t0, x2);
        fe448_mul39081(z2, t1);
        fe448_add(z2, t0, z2);
        fe448_mul(z2, z2, t1);
    }
    /* Last two bits are 0 - no final swap check required. */

    fe448_invert(z2, z2);
    fe448_mul(x2, x2, z2);
    fe448_to_bytes(r, x2);

    return 0;
}

#ifdef HAVE_ED448
/* Check whether field element is not 0.
 * Must convert to a normalized form before checking.
 *
 * a  [in]  Field element.
 * returns 0 when zero, and any other value otherwise.
 */
int fe448_isnonzero(const int64_t* a)
{
    uint8_t b[56];
    int i;
    uint8_t c = 0;
    fe448_to_bytes(b, a);
    for (i = 0; i < 56; i++)
        c |= b[i];
    return c;
}

/* Check whether field element is negative.
 * Must convert to a normalized form before checking.
 *
 * a  [in]  Field element.
 * returns 1 when negative, and 0 otherwise.
 */
int fe448_isnegative(const int64_t* a)
{
    uint8_t b[56];
    fe448_to_bytes(b, a);
    return b[0] & 1;
}

/* Negates the field element. r = -a
 *
 * r  [in]  Field element to hold result.
 * a  [in]  Field element.
 */
void fe448_neg(int64_t* r, const int64_t* a)
{
    r[0] = -a[0];
    r[1] = -a[1];
    r[2] = -a[2];
    r[3] = -a[3];
    r[4] = -a[4];
    r[5] = -a[5];
    r[6] = -a[6];
    r[7] = -a[7];
}

/* Raise field element to (p-3) / 4: 2^446 - 2^222 - 1
 * Used for calcualting y-ordinate from x-ordinate for Ed448.
 *
 * r  [in]  Field element to hold result.
 * a  [in]  Field element to exponentiate.
 */
void fe448_pow_2_446_222_1(int64_t* r, const int64_t* a)
{
    int64_t t1[8];
    int64_t t2[8];
    int64_t t3[8];
    int64_t t4[8];
    int64_t t5[8];
    int i;

    fe448_sqr(t3, a);
    /* t3 = 2 */
    fe448_mul(t1, t3, a);
    /* t1 = 3 */
    fe448_sqr(t5, t1);
    /* t5 = 6 */
    fe448_mul(t5, t5, a);
    /* t5 = 7 */
    fe448_sqr(t2, t1); for (i = 1; i < 2; ++i) fe448_sqr(t2, t2);
    /* t2 = c */
    fe448_mul(t3, t2, t3);
    /* t3 = e */
    fe448_mul(t1, t2, t1);
    /* t1 = f */
    fe448_sqr(t2, t1); for (i = 1; i < 3; ++i) fe448_sqr(t2, t2);
    /* t2 = 78 */
    fe448_mul(t5, t2, t5);
    /* t5 = 7f */
    fe448_sqr(t2, t1); for (i = 1; i < 4; ++i) fe448_sqr(t2, t2);
    /* t2 = f0 */
    fe448_mul(t1, t2, t1);
    /* t1 = ff */
    fe448_mul(t3, t3, t2);
    /* t3 = fe */
    fe448_sqr(t2, t1); for (i = 1; i < 7; ++i) fe448_sqr(t2, t2);
    /* t2 = 7f80 */
    fe448_mul(t5, t2, t5);
    /* t5 = 7fff */
    fe448_sqr(t2, t1); for (i = 1; i < 8; ++i) fe448_sqr(t2, t2);
    /* t2 = ff00 */
    fe448_mul(t1, t2, t1);
    /* t1 = ffff */
    fe448_mul(t3, t3, t2);
    /* t3 = fffe */
    fe448_sqr(t2, t5); for (i = 1; i < 15; ++i) fe448_sqr(t2, t2);
    /* t2 = 3fff8000 */
    fe448_mul(t5, t2, t5);
    /* t5 = 3fffffff */
    fe448_sqr(t2, t1); for (i = 1; i < 16; ++i) fe448_sqr(t2, t2);
    /* t2 = ffff0000 */
    fe448_mul(t1, t2, t1);
    /* t1 = ffffffff */
    fe448_mul(t3, t3, t2);
    /* t3 = fffffffe */
    fe448_sqr(t2, t1); for (i = 1; i < 32; ++i) fe448_sqr(t2, t2);
    /* t2 = ffffffff00000000 */
    fe448_mul(t2, t2, t1);
    /* t2 = ffffffffffffffff */
    fe448_sqr(t1, t2); for (i = 1; i < 64; ++i) fe448_sqr(t1, t1);
    /* t1 = ffffffffffffffff0000000000000000 */
    fe448_mul(t1, t1, t2);
    /* t1 = ffffffffffffffffffffffffffffffff */
    fe448_sqr(t1, t1); for (i = 1; i < 64; ++i) fe448_sqr(t1, t1);
    /* t1 = ffffffffffffffffffffffffffffffff0000000000000000 */
    fe448_mul(t4, t1, t2);
    /* t4 = ffffffffffffffffffffffffffffffffffffffffffffffff */
    fe448_sqr(t2, t4); for (i = 1; i < 32; ++i) fe448_sqr(t2, t2);
    /* t2 = ffffffffffffffffffffffffffffffffffffffffffffffff00000000 */
    fe448_mul(t3, t3, t2);
    /* t3 = fffffffffffffffffffffffffffffffffffffffffffffffffffffffe */
    fe448_sqr(t1, t3); for (i = 1; i < 192; ++i) fe448_sqr(t1, t1);
    /* t1 = fffffffffffffffffffffffffffffffffffffffffffffffffffffffe000000000000000000000000000000000000000000000000 */
    fe448_mul(t1, t1, t4);
    /* t1 = fffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffffffffffffffffffffffffffffffffffffffffffff */
    fe448_sqr(t1, t1); for (i = 1; i < 30; ++i) fe448_sqr(t1, t1);
    /* t1 = 3fffffffffffffffffffffffffffffffffffffffffffffffffffffffbfffffffffffffffffffffffffffffffffffffffffffffffc0000000 */
    fe448_mul(r, t5, t1);
    /* r = 3fffffffffffffffffffffffffffffffffffffffffffffffffffffffbfffffffffffffffffffffffffffffffffffffffffffffffffffffff */
}

/* Constant time, conditional move of b into a.
 * a is not changed if the condition is 0.
 *
 * a  A field element.
 * b  A field element.
 * c  If 1 then copy and if 0 then don't copy.
 */
void fe448_cmov(int64_t* a, const int64_t* b, int c)
{
    int64_t m = -(int64_t)c;
    int64_t t0 = m & (a[0] ^ b[0]);
    int64_t t1 = m & (a[1] ^ b[1]);
    int64_t t2 = m & (a[2] ^ b[2]);
    int64_t t3 = m & (a[3] ^ b[3]);
    int64_t t4 = m & (a[4] ^ b[4]);
    int64_t t5 = m & (a[5] ^ b[5]);
    int64_t t6 = m & (a[6] ^ b[6]);
    int64_t t7 = m & (a[7] ^ b[7]);

    a[0] ^= t0;
    a[1] ^= t1;
    a[2] ^= t2;
    a[3] ^= t3;
    a[4] ^= t4;
    a[5] ^= t5;
    a[6] ^= t6;
    a[7] ^= t7;
}

#endif /* HAVE_ED448 */
#else

/* Initialize the field element operations.
 */
void fe448_init(void)
{
}

/* Convert the field element from a byte array to an array of 28-bits.
 *
 * r  [in]  Array to encode into.
 * b  [in]  Byte array.
 */
void fe448_from_bytes(int32_t* r, const unsigned char* b)
{
    r[ 0] =  (((int32_t)((b[ 0]        ) >>  0)) <<  0)
          |  (((int32_t)((b[ 1]        ) >>  0)) <<  8)
          |  (((int32_t)((b[ 2]        ) >>  0)) << 16)
          | ((((int32_t)((b[ 3] & 0xf )) >>  0)) << 24);
    r[ 1] =  (((int32_t)((b[ 3]        ) >>  4)) <<  0)
          |  (((int32_t)((b[ 4]        ) >>  0)) <<  4)
          |  (((int32_t)((b[ 5]        ) >>  0)) << 12)
          |  (((int32_t)((b[ 6]        ) >>  0)) << 20);
    r[ 2] =  (((int32_t)((b[ 7]        ) >>  0)) <<  0)
          |  (((int32_t)((b[ 8]        ) >>  0)) <<  8)
          |  (((int32_t)((b[ 9]        ) >>  0)) << 16)
          | ((((int32_t)((b[10] & 0xf )) >>  0)) << 24);
    r[ 3] =  (((int32_t)((b[10]        ) >>  4)) <<  0)
          |  (((int32_t)((b[11]        ) >>  0)) <<  4)
          |  (((int32_t)((b[12]        ) >>  0)) << 12)
          |  (((int32_t)((b[13]        ) >>  0)) << 20);
    r[ 4] =  (((int32_t)((b[14]        ) >>  0)) <<  0)
          |  (((int32_t)((b[15]        ) >>  0)) <<  8)
          |  (((int32_t)((b[16]        ) >>  0)) << 16)
          | ((((int32_t)((b[17] & 0xf )) >>  0)) << 24);
    r[ 5] =  (((int32_t)((b[17]        ) >>  4)) <<  0)
          |  (((int32_t)((b[18]        ) >>  0)) <<  4)
          |  (((int32_t)((b[19]        ) >>  0)) << 12)
          |  (((int32_t)((b[20]        ) >>  0)) << 20);
    r[ 6] =  (((int32_t)((b[21]        ) >>  0)) <<  0)
          |  (((int32_t)((b[22]        ) >>  0)) <<  8)
          |  (((int32_t)((b[23]        ) >>  0)) << 16)
          | ((((int32_t)((b[24] & 0xf )) >>  0)) << 24);
    r[ 7] =  (((int32_t)((b[24]        ) >>  4)) <<  0)
          |  (((int32_t)((b[25]        ) >>  0)) <<  4)
          |  (((int32_t)((b[26]        ) >>  0)) << 12)
          |  (((int32_t)((b[27]        ) >>  0)) << 20);
    r[ 8] =  (((int32_t)((b[28]        ) >>  0)) <<  0)
          |  (((int32_t)((b[29]        ) >>  0)) <<  8)
          |  (((int32_t)((b[30]        ) >>  0)) << 16)
          | ((((int32_t)((b[31] & 0xf )) >>  0)) << 24);
    r[ 9] =  (((int32_t)((b[31]        ) >>  4)) <<  0)
          |  (((int32_t)((b[32]        ) >>  0)) <<  4)
          |  (((int32_t)((b[33]        ) >>  0)) << 12)
          |  (((int32_t)((b[34]        ) >>  0)) << 20);
    r[10] =  (((int32_t)((b[35]        ) >>  0)) <<  0)
          |  (((int32_t)((b[36]        ) >>  0)) <<  8)
          |  (((int32_t)((b[37]        ) >>  0)) << 16)
          | ((((int32_t)((b[38] & 0xf )) >>  0)) << 24);
    r[11] =  (((int32_t)((b[38]        ) >>  4)) <<  0)
          |  (((int32_t)((b[39]        ) >>  0)) <<  4)
          |  (((int32_t)((b[40]        ) >>  0)) << 12)
          |  (((int32_t)((b[41]        ) >>  0)) << 20);
    r[12] =  (((int32_t)((b[42]        ) >>  0)) <<  0)
          |  (((int32_t)((b[43]        ) >>  0)) <<  8)
          |  (((int32_t)((b[44]        ) >>  0)) << 16)
          | ((((int32_t)((b[45] & 0xf )) >>  0)) << 24);
    r[13] =  (((int32_t)((b[45]        ) >>  4)) <<  0)
          |  (((int32_t)((b[46]        ) >>  0)) <<  4)
          |  (((int32_t)((b[47]        ) >>  0)) << 12)
          |  (((int32_t)((b[48]        ) >>  0)) << 20);
    r[14] =  (((int32_t)((b[49]        ) >>  0)) <<  0)
          |  (((int32_t)((b[50]        ) >>  0)) <<  8)
          |  (((int32_t)((b[51]        ) >>  0)) << 16)
          | ((((int32_t)((b[52] & 0xf )) >>  0)) << 24);
    r[15] =  (((int32_t)((b[52]        ) >>  4)) <<  0)
          |  (((int32_t)((b[53]        ) >>  0)) <<  4)
          |  (((int32_t)((b[54]        ) >>  0)) << 12)
          |  (((int32_t)((b[55]        ) >>  0)) << 20);
}

/* Convert the field element to a byte array from an array of 28-bits.
 *
 * b  [in]  Byte array.
 * a  [in]  Array to encode into.
 */
void fe448_to_bytes(unsigned char* b, const int32_t* a)
{
    int64_t t;
    /* Mod */
    int32_t in0 = a[0];
    int32_t in1 = a[1];
    int32_t in2 = a[2];
    int32_t in3 = a[3];
    int32_t in4 = a[4];
    int32_t in5 = a[5];
    int32_t in6 = a[6];
    int32_t in7 = a[7];
    int32_t in8 = a[8];
    int32_t in9 = a[9];
    int32_t in10 = a[10];
    int32_t in11 = a[11];
    int32_t in12 = a[12];
    int32_t in13 = a[13];
    int32_t in14 = a[14];
    int32_t in15 = a[15];
    int32_t o = in15 >> 28;
    in15 -= o << 28;
    in0 += o;
    in8 += o;
    o = (in0 + 1) >> 28;
    o = (o + in1) >> 28;
    o = (o + in2) >> 28;
    o = (o + in3) >> 28;
    o = (o + in4) >> 28;
    o = (o + in5) >> 28;
    o = (o + in6) >> 28;
    o = (o + in7) >> 28;
    o = (o + in8 + 1) >> 28;
    o = (o + in9) >> 28;
    o = (o + in10) >> 28;
    o = (o + in11) >> 28;
    o = (o + in12) >> 28;
    o = (o + in13) >> 28;
    o = (o + in14) >> 28;
    o = (o + in15) >> 28;
    in0 += o;
    in8 += o;
    in15 -= o << 28;
    o = (int32_t)(in0  >> 28); in1  += o; t = o << 28; in0  -= t;
    o = (int32_t)(in1  >> 28); in2  += o; t = o << 28; in1  -= t;
    o = (int32_t)(in2  >> 28); in3  += o; t = o << 28; in2  -= t;
    o = (int32_t)(in3  >> 28); in4  += o; t = o << 28; in3  -= t;
    o = (int32_t)(in4  >> 28); in5  += o; t = o << 28; in4  -= t;
    o = (int32_t)(in5  >> 28); in6  += o; t = o << 28; in5  -= t;
    o = (int32_t)(in6  >> 28); in7  += o; t = o << 28; in6  -= t;
    o = (int32_t)(in7  >> 28); in8  += o; t = o << 28; in7  -= t;
    o = (int32_t)(in8  >> 28); in9  += o; t = o << 28; in8  -= t;
    o = (int32_t)(in9  >> 28); in10 += o; t = o << 28; in9  -= t;
    o = (int32_t)(in10 >> 28); in11 += o; t = o << 28; in10 -= t;
    o = (int32_t)(in11 >> 28); in12 += o; t = o << 28; in11 -= t;
    o = (int32_t)(in12 >> 28); in13 += o; t = o << 28; in12 -= t;
    o = (int32_t)(in13 >> 28); in14 += o; t = o << 28; in13 -= t;
    o = (int32_t)(in14 >> 28); in15 += o; t = o << 28; in14 -= t;
    o = (int32_t)(in15 >> 28); in0  += o;
                    in8  += o; t = o << 28; in15 -= t;

    /* Output as bytes */
    b[ 0] = (in0  >>  0);
    b[ 1] = (in0  >>  8);
    b[ 2] = (in0  >> 16);
    b[ 3] = (in0  >> 24) + ((in1  >>  0) <<  4);
    b[ 4] = (in1  >>  4);
    b[ 5] = (in1  >> 12);
    b[ 6] = (in1  >> 20);
    b[ 7] = (in2  >>  0);
    b[ 8] = (in2  >>  8);
    b[ 9] = (in2  >> 16);
    b[10] = (in2  >> 24) + ((in3  >>  0) <<  4);
    b[11] = (in3  >>  4);
    b[12] = (in3  >> 12);
    b[13] = (in3  >> 20);
    b[14] = (in4  >>  0);
    b[15] = (in4  >>  8);
    b[16] = (in4  >> 16);
    b[17] = (in4  >> 24) + ((in5  >>  0) <<  4);
    b[18] = (in5  >>  4);
    b[19] = (in5  >> 12);
    b[20] = (in5  >> 20);
    b[21] = (in6  >>  0);
    b[22] = (in6  >>  8);
    b[23] = (in6  >> 16);
    b[24] = (in6  >> 24) + ((in7  >>  0) <<  4);
    b[25] = (in7  >>  4);
    b[26] = (in7  >> 12);
    b[27] = (in7  >> 20);
    b[28] = (in8  >>  0);
    b[29] = (in8  >>  8);
    b[30] = (in8  >> 16);
    b[31] = (in8  >> 24) + ((in9  >>  0) <<  4);
    b[32] = (in9  >>  4);
    b[33] = (in9  >> 12);
    b[34] = (in9  >> 20);
    b[35] = (in10 >>  0);
    b[36] = (in10 >>  8);
    b[37] = (in10 >> 16);
    b[38] = (in10 >> 24) + ((in11 >>  0) <<  4);
    b[39] = (in11 >>  4);
    b[40] = (in11 >> 12);
    b[41] = (in11 >> 20);
    b[42] = (in12 >>  0);
    b[43] = (in12 >>  8);
    b[44] = (in12 >> 16);
    b[45] = (in12 >> 24) + ((in13 >>  0) <<  4);
    b[46] = (in13 >>  4);
    b[47] = (in13 >> 12);
    b[48] = (in13 >> 20);
    b[49] = (in14 >>  0);
    b[50] = (in14 >>  8);
    b[51] = (in14 >> 16);
    b[52] = (in14 >> 24) + ((in15 >>  0) <<  4);
    b[53] = (in15 >>  4);
    b[54] = (in15 >> 12);
    b[55] = (in15 >> 20);
}

/* Set the field element to 0.
 *
 * a  [in]  Field element.
 */
void fe448_1(int32_t* a)
{
    a[0] = 1;
    a[1] = 0;
    a[2] = 0;
    a[3] = 0;
    a[4] = 0;
    a[5] = 0;
    a[6] = 0;
    a[7] = 0;
    a[8] = 0;
    a[9] = 0;
    a[10] = 0;
    a[11] = 0;
    a[12] = 0;
    a[13] = 0;
    a[14] = 0;
    a[15] = 0;
}

/* Set the field element to 0.
 *
 * a  [in]  Field element.
 */
void fe448_0(int32_t* a)
{
    a[0] = 0;
    a[1] = 0;
    a[2] = 0;
    a[3] = 0;
    a[4] = 0;
    a[5] = 0;
    a[6] = 0;
    a[7] = 0;
    a[8] = 0;
    a[9] = 0;
    a[10] = 0;
    a[11] = 0;
    a[12] = 0;
    a[13] = 0;
    a[14] = 0;
    a[15] = 0;
}

/* Copy one field element into another: d = a.
 *
 * d  [in]  Destination field element.
 * a  [in]  Source field element.
 */
void fe448_copy(int32_t* d, const int32_t* a)
{
    d[0] = a[0];
    d[1] = a[1];
    d[2] = a[2];
    d[3] = a[3];
    d[4] = a[4];
    d[5] = a[5];
    d[6] = a[6];
    d[7] = a[7];
    d[8] = a[8];
    d[9] = a[9];
    d[10] = a[10];
    d[11] = a[11];
    d[12] = a[12];
    d[13] = a[13];
    d[14] = a[14];
    d[15] = a[15];
}

/* Conditionally swap the elements.
 * Constant time implementation.
 *
 * a  [in]  First field element.
 * b  [in]  Second field element.
 * c  [in]  Swap when 1. Valid values: 0, 1.
 */
static void fe448_cswap(int32_t* a, int32_t* b, int c)
{
    int32_t mask = -(int32_t)c;
    int32_t t0 = (a[0] ^ b[0]) & mask;
    int32_t t1 = (a[1] ^ b[1]) & mask;
    int32_t t2 = (a[2] ^ b[2]) & mask;
    int32_t t3 = (a[3] ^ b[3]) & mask;
    int32_t t4 = (a[4] ^ b[4]) & mask;
    int32_t t5 = (a[5] ^ b[5]) & mask;
    int32_t t6 = (a[6] ^ b[6]) & mask;
    int32_t t7 = (a[7] ^ b[7]) & mask;
    int32_t t8 = (a[8] ^ b[8]) & mask;
    int32_t t9 = (a[9] ^ b[9]) & mask;
    int32_t t10 = (a[10] ^ b[10]) & mask;
    int32_t t11 = (a[11] ^ b[11]) & mask;
    int32_t t12 = (a[12] ^ b[12]) & mask;
    int32_t t13 = (a[13] ^ b[13]) & mask;
    int32_t t14 = (a[14] ^ b[14]) & mask;
    int32_t t15 = (a[15] ^ b[15]) & mask;
    a[0] ^= t0;
    a[1] ^= t1;
    a[2] ^= t2;
    a[3] ^= t3;
    a[4] ^= t4;
    a[5] ^= t5;
    a[6] ^= t6;
    a[7] ^= t7;
    a[8] ^= t8;
    a[9] ^= t9;
    a[10] ^= t10;
    a[11] ^= t11;
    a[12] ^= t12;
    a[13] ^= t13;
    a[14] ^= t14;
    a[15] ^= t15;
    b[0] ^= t0;
    b[1] ^= t1;
    b[2] ^= t2;
    b[3] ^= t3;
    b[4] ^= t4;
    b[5] ^= t5;
    b[6] ^= t6;
    b[7] ^= t7;
    b[8] ^= t8;
    b[9] ^= t9;
    b[10] ^= t10;
    b[11] ^= t11;
    b[12] ^= t12;
    b[13] ^= t13;
    b[14] ^= t14;
    b[15] ^= t15;
}

/* Add two field elements. r = (a + b) mod (2^448 - 2^224 - 1)
 *
 * r  [in]  Field element to hold sum.
 * a  [in]  Field element to add.
 * b  [in]  Field element to add.
 */
void fe448_add(int32_t* r, const int32_t* a, const int32_t* b)
{
    r[0] = a[0] + b[0];
    r[1] = a[1] + b[1];
    r[2] = a[2] + b[2];
    r[3] = a[3] + b[3];
    r[4] = a[4] + b[4];
    r[5] = a[5] + b[5];
    r[6] = a[6] + b[6];
    r[7] = a[7] + b[7];
    r[8] = a[8] + b[8];
    r[9] = a[9] + b[9];
    r[10] = a[10] + b[10];
    r[11] = a[11] + b[11];
    r[12] = a[12] + b[12];
    r[13] = a[13] + b[13];
    r[14] = a[14] + b[14];
    r[15] = a[15] + b[15];
}

/* Subtract a field element from another. r = (a - b) mod (2^448 - 2^224 - 1)
 *
 * r  [in]  Field element to hold difference.
 * a  [in]  Field element to subtract from.
 * b  [in]  Field element to subtract.
 */
void fe448_sub(int32_t* r, const int32_t* a, const int32_t* b)
{
    r[0] = a[0] - b[0];
    r[1] = a[1] - b[1];
    r[2] = a[2] - b[2];
    r[3] = a[3] - b[3];
    r[4] = a[4] - b[4];
    r[5] = a[5] - b[5];
    r[6] = a[6] - b[6];
    r[7] = a[7] - b[7];
    r[8] = a[8] - b[8];
    r[9] = a[9] - b[9];
    r[10] = a[10] - b[10];
    r[11] = a[11] - b[11];
    r[12] = a[12] - b[12];
    r[13] = a[13] - b[13];
    r[14] = a[14] - b[14];
    r[15] = a[15] - b[15];
}

void fe448_reduce(int32_t* a)
{
    int64_t o;

    o = a[0 ] >> 28; a[1 ] += o; a[0 ] -= o << 28;
    o = a[1 ] >> 28; a[2 ] += o; a[1 ] -= o << 28;
    o = a[2 ] >> 28; a[3 ] += o; a[2 ] -= o << 28;
    o = a[3 ] >> 28; a[4 ] += o; a[3 ] -= o << 28;
    o = a[4 ] >> 28; a[5 ] += o; a[4 ] -= o << 28;
    o = a[5 ] >> 28; a[6 ] += o; a[5 ] -= o << 28;
    o = a[6 ] >> 28; a[7 ] += o; a[6 ] -= o << 28;
    o = a[7 ] >> 28; a[8 ] += o; a[7 ] -= o << 28;
    o = a[8 ] >> 28; a[9 ] += o; a[8 ] -= o << 28;
    o = a[9 ] >> 28; a[10] += o; a[9 ] -= o << 28;
    o = a[10] >> 28; a[11] += o; a[10] -= o << 28;
    o = a[11] >> 28; a[12] += o; a[11] -= o << 28;
    o = a[12] >> 28; a[13] += o; a[12] -= o << 28;
    o = a[13] >> 28; a[14] += o; a[13] -= o << 28;
    o = a[14] >> 28; a[15] += o; a[14] -= o << 28;
    o = a[15] >> 28; a[0]  += o;
                     a[8]  += o; a[15] -= o << 28;
}
/* Mulitply a field element by 39081. r = (39081 * a) mod (2^448 - 2^224 - 1)
 *
 * r  [in]  Field element to hold result.
 * a  [in]  Field element to multiply.
 */
void fe448_mul39081(int32_t* r, const int32_t* a)
{
    int64_t t;
    int32_t o;
    int64_t t0 = a[0] * (int64_t)39081;
    int64_t t1 = a[1] * (int64_t)39081;
    int64_t t2 = a[2] * (int64_t)39081;
    int64_t t3 = a[3] * (int64_t)39081;
    int64_t t4 = a[4] * (int64_t)39081;
    int64_t t5 = a[5] * (int64_t)39081;
    int64_t t6 = a[6] * (int64_t)39081;
    int64_t t7 = a[7] * (int64_t)39081;
    int64_t t8 = a[8] * (int64_t)39081;
    int64_t t9 = a[9] * (int64_t)39081;
    int64_t t10 = a[10] * (int64_t)39081;
    int64_t t11 = a[11] * (int64_t)39081;
    int64_t t12 = a[12] * (int64_t)39081;
    int64_t t13 = a[13] * (int64_t)39081;
    int64_t t14 = a[14] * (int64_t)39081;
    int64_t t15 = a[15] * (int64_t)39081;
    o = (int32_t)(t0  >> 28); t1  += o; t = (int64_t)o << 28; t0  -= t;
    o = (int32_t)(t1  >> 28); t2  += o; t = (int64_t)o << 28; t1  -= t;
    o = (int32_t)(t2  >> 28); t3  += o; t = (int64_t)o << 28; t2  -= t;
    o = (int32_t)(t3  >> 28); t4  += o; t = (int64_t)o << 28; t3  -= t;
    o = (int32_t)(t4  >> 28); t5  += o; t = (int64_t)o << 28; t4  -= t;
    o = (int32_t)(t5  >> 28); t6  += o; t = (int64_t)o << 28; t5  -= t;
    o = (int32_t)(t6  >> 28); t7  += o; t = (int64_t)o << 28; t6  -= t;
    o = (int32_t)(t7  >> 28); t8  += o; t = (int64_t)o << 28; t7  -= t;
    o = (int32_t)(t8  >> 28); t9  += o; t = (int64_t)o << 28; t8  -= t;
    o = (int32_t)(t9  >> 28); t10 += o; t = (int64_t)o << 28; t9  -= t;
    o = (int32_t)(t10 >> 28); t11 += o; t = (int64_t)o << 28; t10 -= t;
    o = (int32_t)(t11 >> 28); t12 += o; t = (int64_t)o << 28; t11 -= t;
    o = (int32_t)(t12 >> 28); t13 += o; t = (int64_t)o << 28; t12 -= t;
    o = (int32_t)(t13 >> 28); t14 += o; t = (int64_t)o << 28; t13 -= t;
    o = (int32_t)(t14 >> 28); t15 += o; t = (int64_t)o << 28; t14 -= t;
    o = (int32_t)(t15 >> 28); t0  += o;
                   t8  += o; t = (int64_t)o << 28; t15 -= t;

    /* Store */
    r[0] = (int32_t)t0;
    r[1] = (int32_t)t1;
    r[2] = (int32_t)t2;
    r[3] = (int32_t)t3;
    r[4] = (int32_t)t4;
    r[5] = (int32_t)t5;
    r[6] = (int32_t)t6;
    r[7] = (int32_t)t7;
    r[8] = (int32_t)t8;
    r[9] = (int32_t)t9;
    r[10] = (int32_t)t10;
    r[11] = (int32_t)t11;
    r[12] = (int32_t)t12;
    r[13] = (int32_t)t13;
    r[14] = (int32_t)t14;
    r[15] = (int32_t)t15;
}

/* Mulitply two field elements. r = a * b
 *
 * r  [in]  Field element to hold result.
 * a  [in]  Field element to multiply.
 * b  [in]  Field element to multiply.
 */
static WC_INLINE void fe448_mul_8(int32_t* r, const int32_t* a, const int32_t* b)
{
    int64_t t;
    int64_t t0   = (int64_t)a[ 0] * b[ 0];
    int64_t t1   = (int64_t)a[ 0] * b[ 1];
    int64_t t101 = (int64_t)a[ 1] * b[ 0];
    int64_t t2   = (int64_t)a[ 0] * b[ 2];
    int64_t t102 = (int64_t)a[ 1] * b[ 1];
    int64_t t202 = (int64_t)a[ 2] * b[ 0];
    int64_t t3   = (int64_t)a[ 0] * b[ 3];
    int64_t t103 = (int64_t)a[ 1] * b[ 2];
    int64_t t203 = (int64_t)a[ 2] * b[ 1];
    int64_t t303 = (int64_t)a[ 3] * b[ 0];
    int64_t t4   = (int64_t)a[ 0] * b[ 4];
    int64_t t104 = (int64_t)a[ 1] * b[ 3];
    int64_t t204 = (int64_t)a[ 2] * b[ 2];
    int64_t t304 = (int64_t)a[ 3] * b[ 1];
    int64_t t404 = (int64_t)a[ 4] * b[ 0];
    int64_t t5   = (int64_t)a[ 0] * b[ 5];
    int64_t t105 = (int64_t)a[ 1] * b[ 4];
    int64_t t205 = (int64_t)a[ 2] * b[ 3];
    int64_t t305 = (int64_t)a[ 3] * b[ 2];
    int64_t t405 = (int64_t)a[ 4] * b[ 1];
    int64_t t505 = (int64_t)a[ 5] * b[ 0];
    int64_t t6   = (int64_t)a[ 0] * b[ 6];
    int64_t t106 = (int64_t)a[ 1] * b[ 5];
    int64_t t206 = (int64_t)a[ 2] * b[ 4];
    int64_t t306 = (int64_t)a[ 3] * b[ 3];
    int64_t t406 = (int64_t)a[ 4] * b[ 2];
    int64_t t506 = (int64_t)a[ 5] * b[ 1];
    int64_t t606 = (int64_t)a[ 6] * b[ 0];
    int64_t t7   = (int64_t)a[ 0] * b[ 7];
    int64_t t107 = (int64_t)a[ 1] * b[ 6];
    int64_t t207 = (int64_t)a[ 2] * b[ 5];
    int64_t t307 = (int64_t)a[ 3] * b[ 4];
    int64_t t407 = (int64_t)a[ 4] * b[ 3];
    int64_t t507 = (int64_t)a[ 5] * b[ 2];
    int64_t t607 = (int64_t)a[ 6] * b[ 1];
    int64_t t707 = (int64_t)a[ 7] * b[ 0];
    int64_t t8   = (int64_t)a[ 1] * b[ 7];
    int64_t t108 = (int64_t)a[ 2] * b[ 6];
    int64_t t208 = (int64_t)a[ 3] * b[ 5];
    int64_t t308 = (int64_t)a[ 4] * b[ 4];
    int64_t t408 = (int64_t)a[ 5] * b[ 3];
    int64_t t508 = (int64_t)a[ 6] * b[ 2];
    int64_t t608 = (int64_t)a[ 7] * b[ 1];
    int64_t t9   = (int64_t)a[ 2] * b[ 7];
    int64_t t109 = (int64_t)a[ 3] * b[ 6];
    int64_t t209 = (int64_t)a[ 4] * b[ 5];
    int64_t t309 = (int64_t)a[ 5] * b[ 4];
    int64_t t409 = (int64_t)a[ 6] * b[ 3];
    int64_t t509 = (int64_t)a[ 7] * b[ 2];
    int64_t t10  = (int64_t)a[ 3] * b[ 7];
    int64_t t110 = (int64_t)a[ 4] * b[ 6];
    int64_t t210 = (int64_t)a[ 5] * b[ 5];
    int64_t t310 = (int64_t)a[ 6] * b[ 4];
    int64_t t410 = (int64_t)a[ 7] * b[ 3];
    int64_t t11  = (int64_t)a[ 4] * b[ 7];
    int64_t t111 = (int64_t)a[ 5] * b[ 6];
    int64_t t211 = (int64_t)a[ 6] * b[ 5];
    int64_t t311 = (int64_t)a[ 7] * b[ 4];
    int64_t t12  = (int64_t)a[ 5] * b[ 7];
    int64_t t112 = (int64_t)a[ 6] * b[ 6];
    int64_t t212 = (int64_t)a[ 7] * b[ 5];
    int64_t t13  = (int64_t)a[ 6] * b[ 7];
    int64_t t113 = (int64_t)a[ 7] * b[ 6];
    int64_t t14  = (int64_t)a[ 7] * b[ 7];
    t1  += t101;
    t2  += t102; t2  += t202;
    t3  += t103; t3  += t203; t3  += t303;
    t4  += t104; t4  += t204; t4  += t304; t4  += t404;
    t5  += t105; t5  += t205; t5  += t305; t5  += t405; t5  += t505;
    t6  += t106; t6  += t206; t6  += t306; t6  += t406; t6  += t506;
    t6  += t606;
    t7  += t107; t7  += t207; t7  += t307; t7  += t407; t7  += t507;
    t7  += t607;
    t7  += t707;
    t8  += t108; t8  += t208; t8  += t308; t8  += t408; t8  += t508;
    t8  += t608;
    t9  += t109; t9  += t209; t9  += t309; t9  += t409; t9  += t509;
    t10 += t110; t10 += t210; t10 += t310; t10 += t410;
    t11 += t111; t11 += t211; t11 += t311;
    t12 += t112; t12 += t212;
    t13 += t113;
    int64_t o = t14 >> 28;
    int64_t t15 = o;
    t14 -= o << 28;
    o = (int32_t)(t0  >> 28); t1  += o; t = (int64_t)o << 28; t0  -= t;
    o = (int32_t)(t1  >> 28); t2  += o; t = (int64_t)o << 28; t1  -= t;
    o = (int32_t)(t2  >> 28); t3  += o; t = (int64_t)o << 28; t2  -= t;
    o = (int32_t)(t3  >> 28); t4  += o; t = (int64_t)o << 28; t3  -= t;
    o = (int32_t)(t4  >> 28); t5  += o; t = (int64_t)o << 28; t4  -= t;
    o = (int32_t)(t5  >> 28); t6  += o; t = (int64_t)o << 28; t5  -= t;
    o = (int32_t)(t6  >> 28); t7  += o; t = (int64_t)o << 28; t6  -= t;
    o = (int32_t)(t7  >> 28); t8  += o; t = (int64_t)o << 28; t7  -= t;
    o = (int32_t)(t8  >> 28); t9  += o; t = (int64_t)o << 28; t8  -= t;
    o = (int32_t)(t9  >> 28); t10 += o; t = (int64_t)o << 28; t9  -= t;
    o = (int32_t)(t10 >> 28); t11 += o; t = (int64_t)o << 28; t10 -= t;
    o = (int32_t)(t11 >> 28); t12 += o; t = (int64_t)o << 28; t11 -= t;
    o = (int32_t)(t12 >> 28); t13 += o; t = (int64_t)o << 28; t12 -= t;
    o = (int32_t)(t13 >> 28); t14 += o; t = (int64_t)o << 28; t13 -= t;
    o = (int32_t)(t14 >> 28); t15 += o; t = (int64_t)o << 28; t14 -= t;
    o = (int32_t)(t15 >> 28); t0  += o;
                   t8  += o; t = (int64_t)o << 28; t15 -= t;

    /* Store */
    r[0] = (int32_t)t0;
    r[1] = (int32_t)t1;
    r[2] = (int32_t)t2;
    r[3] = (int32_t)t3;
    r[4] = (int32_t)t4;
    r[5] = (int32_t)t5;
    r[6] = (int32_t)t6;
    r[7] = (int32_t)t7;
    r[8] = (int32_t)t8;
    r[9] = (int32_t)t9;
    r[10] = (int32_t)t10;
    r[11] = (int32_t)t11;
    r[12] = (int32_t)t12;
    r[13] = (int32_t)t13;
    r[14] = (int32_t)t14;
    r[15] = (int32_t)t15;
}

/* Mulitply two field elements. r = (a * b) mod (2^448 - 2^224 - 1)
 *
 * r  [in]  Field element to hold result.
 * a  [in]  Field element to multiply.
 * b  [in]  Field element to multiply.
 */
void fe448_mul(int32_t* r, const int32_t* a, const int32_t* b)
{
    int32_t r0[16];
    int32_t r1[16];
    int32_t* a1 = r1;
    int32_t b1[8];
    int32_t r2[16];
    a1[0] = a[0] + a[8];
    a1[1] = a[1] + a[9];
    a1[2] = a[2] + a[10];
    a1[3] = a[3] + a[11];
    a1[4] = a[4] + a[12];
    a1[5] = a[5] + a[13];
    a1[6] = a[6] + a[14];
    a1[7] = a[7] + a[15];
    b1[0] = b[0] + b[8];
    b1[1] = b[1] + b[9];
    b1[2] = b[2] + b[10];
    b1[3] = b[3] + b[11];
    b1[4] = b[4] + b[12];
    b1[5] = b[5] + b[13];
    b1[6] = b[6] + b[14];
    b1[7] = b[7] + b[15];
    fe448_mul_8(r2, a + 8, b + 8);
    fe448_mul_8(r0, a, b);
    fe448_mul_8(r1, a1, b1);
    r[ 0] = r0[ 0] + r2[ 0] + r1[ 8] - r0[ 8];
    r[ 1] = r0[ 1] + r2[ 1] + r1[ 9] - r0[ 9];
    r[ 2] = r0[ 2] + r2[ 2] + r1[10] - r0[10];
    r[ 3] = r0[ 3] + r2[ 3] + r1[11] - r0[11];
    r[ 4] = r0[ 4] + r2[ 4] + r1[12] - r0[12];
    r[ 5] = r0[ 5] + r2[ 5] + r1[13] - r0[13];
    r[ 6] = r0[ 6] + r2[ 6] + r1[14] - r0[14];
    r[ 7] = r0[ 7] + r2[ 7] + r1[15] - r0[15];
    r[ 8] = r2[ 8]          + r1[ 0] - r0[ 0] + r1[ 8];
    r[ 9] = r2[ 9]          + r1[ 1] - r0[ 1] + r1[ 9];
    r[10] = r2[10]          + r1[ 2] - r0[ 2] + r1[10];
    r[11] = r2[11]          + r1[ 3] - r0[ 3] + r1[11];
    r[12] = r2[12]          + r1[ 4] - r0[ 4] + r1[12];
    r[13] = r2[13]          + r1[ 5] - r0[ 5] + r1[13];
    r[14] = r2[14]          + r1[ 6] - r0[ 6] + r1[14];
    r[15] = r2[15]          + r1[ 7] - r0[ 7] + r1[15];
}

/* Square a field element. r = a * a
 *
 * r  [in]  Field element to hold result.
 * a  [in]  Field element to square.
 */
static WC_INLINE void fe448_sqr_8(int32_t* r, const int32_t* a)
{
    int64_t t;
    int64_t t0   =     (int64_t)a[ 0] * a[ 0];
    int64_t t1   = 2 * (int64_t)a[ 0] * a[ 1];
    int64_t t2   = 2 * (int64_t)a[ 0] * a[ 2];
    int64_t t102 =     (int64_t)a[ 1] * a[ 1];
    int64_t t3   = 2 * (int64_t)a[ 0] * a[ 3];
    int64_t t103 = 2 * (int64_t)a[ 1] * a[ 2];
    int64_t t4   = 2 * (int64_t)a[ 0] * a[ 4];
    int64_t t104 = 2 * (int64_t)a[ 1] * a[ 3];
    int64_t t204 =     (int64_t)a[ 2] * a[ 2];
    int64_t t5   = 2 * (int64_t)a[ 0] * a[ 5];
    int64_t t105 = 2 * (int64_t)a[ 1] * a[ 4];
    int64_t t205 = 2 * (int64_t)a[ 2] * a[ 3];
    int64_t t6   = 2 * (int64_t)a[ 0] * a[ 6];
    int64_t t106 = 2 * (int64_t)a[ 1] * a[ 5];
    int64_t t206 = 2 * (int64_t)a[ 2] * a[ 4];
    int64_t t306 =     (int64_t)a[ 3] * a[ 3];
    int64_t t7   = 2 * (int64_t)a[ 0] * a[ 7];
    int64_t t107 = 2 * (int64_t)a[ 1] * a[ 6];
    int64_t t207 = 2 * (int64_t)a[ 2] * a[ 5];
    int64_t t307 = 2 * (int64_t)a[ 3] * a[ 4];
    int64_t t8   = 2 * (int64_t)a[ 1] * a[ 7];
    int64_t t108 = 2 * (int64_t)a[ 2] * a[ 6];
    int64_t t208 = 2 * (int64_t)a[ 3] * a[ 5];
    int64_t t308 =     (int64_t)a[ 4] * a[ 4];
    int64_t t9   = 2 * (int64_t)a[ 2] * a[ 7];
    int64_t t109 = 2 * (int64_t)a[ 3] * a[ 6];
    int64_t t209 = 2 * (int64_t)a[ 4] * a[ 5];
    int64_t t10  = 2 * (int64_t)a[ 3] * a[ 7];
    int64_t t110 = 2 * (int64_t)a[ 4] * a[ 6];
    int64_t t210 =     (int64_t)a[ 5] * a[ 5];
    int64_t t11  = 2 * (int64_t)a[ 4] * a[ 7];
    int64_t t111 = 2 * (int64_t)a[ 5] * a[ 6];
    int64_t t12  = 2 * (int64_t)a[ 5] * a[ 7];
    int64_t t112 =     (int64_t)a[ 6] * a[ 6];
    int64_t t13  = 2 * (int64_t)a[ 6] * a[ 7];
    int64_t t14  =     (int64_t)a[ 7] * a[ 7];
    t2  += t102;
    t3  += t103;
    t4  += t104; t4  += t204;
    t5  += t105; t5  += t205;
    t6  += t106; t6  += t206; t6  += t306;
    t7  += t107; t7  += t207; t7  += t307;
    t8  += t108; t8  += t208; t8  += t308;
    t9  += t109; t9  += t209;
    t10 += t110; t10 += t210;
    t11 += t111;
    t12 += t112;
    int64_t o = t14 >> 28;
    int64_t t15 = o;
    t14 -= o << 28;
    o = (int32_t)(t0  >> 28); t1  += o; t = (int64_t)o << 28; t0  -= t;
    o = (int32_t)(t1  >> 28); t2  += o; t = (int64_t)o << 28; t1  -= t;
    o = (int32_t)(t2  >> 28); t3  += o; t = (int64_t)o << 28; t2  -= t;
    o = (int32_t)(t3  >> 28); t4  += o; t = (int64_t)o << 28; t3  -= t;
    o = (int32_t)(t4  >> 28); t5  += o; t = (int64_t)o << 28; t4  -= t;
    o = (int32_t)(t5  >> 28); t6  += o; t = (int64_t)o << 28; t5  -= t;
    o = (int32_t)(t6  >> 28); t7  += o; t = (int64_t)o << 28; t6  -= t;
    o = (int32_t)(t7  >> 28); t8  += o; t = (int64_t)o << 28; t7  -= t;
    o = (int32_t)(t8  >> 28); t9  += o; t = (int64_t)o << 28; t8  -= t;
    o = (int32_t)(t9  >> 28); t10 += o; t = (int64_t)o << 28; t9  -= t;
    o = (int32_t)(t10 >> 28); t11 += o; t = (int64_t)o << 28; t10 -= t;
    o = (int32_t)(t11 >> 28); t12 += o; t = (int64_t)o << 28; t11 -= t;
    o = (int32_t)(t12 >> 28); t13 += o; t = (int64_t)o << 28; t12 -= t;
    o = (int32_t)(t13 >> 28); t14 += o; t = (int64_t)o << 28; t13 -= t;
    o = (int32_t)(t14 >> 28); t15 += o; t = (int64_t)o << 28; t14 -= t;
    o = (int32_t)(t15 >> 28); t0  += o;
                   t8  += o; t = (int64_t)o << 28; t15 -= t;

    /* Store */
    r[0] = (int32_t)t0;
    r[1] = (int32_t)t1;
    r[2] = (int32_t)t2;
    r[3] = (int32_t)t3;
    r[4] = (int32_t)t4;
    r[5] = (int32_t)t5;
    r[6] = (int32_t)t6;
    r[7] = (int32_t)t7;
    r[8] = (int32_t)t8;
    r[9] = (int32_t)t9;
    r[10] = (int32_t)t10;
    r[11] = (int32_t)t11;
    r[12] = (int32_t)t12;
    r[13] = (int32_t)t13;
    r[14] = (int32_t)t14;
    r[15] = (int32_t)t15;
}

/* Square a field element. r = (a * a) mod (2^448 - 2^224 - 1)
 *
 * r  [in]  Field element to hold result.
 * a  [in]  Field element to square.
 */
void fe448_sqr(int32_t* r, const int32_t* a)
{
    int32_t r0[16];
    int32_t r1[16];
    int32_t* a1 = r1;
    int32_t r2[16];
    a1[0] = a[0] + a[8];
    a1[1] = a[1] + a[9];
    a1[2] = a[2] + a[10];
    a1[3] = a[3] + a[11];
    a1[4] = a[4] + a[12];
    a1[5] = a[5] + a[13];
    a1[6] = a[6] + a[14];
    a1[7] = a[7] + a[15];
    fe448_sqr_8(r2, a + 8);
    fe448_sqr_8(r0, a);
    fe448_sqr_8(r1, a1);
    r[ 0] = r0[ 0] + r2[ 0] + r1[ 8] - r0[ 8];
    r[ 1] = r0[ 1] + r2[ 1] + r1[ 9] - r0[ 9];
    r[ 2] = r0[ 2] + r2[ 2] + r1[10] - r0[10];
    r[ 3] = r0[ 3] + r2[ 3] + r1[11] - r0[11];
    r[ 4] = r0[ 4] + r2[ 4] + r1[12] - r0[12];
    r[ 5] = r0[ 5] + r2[ 5] + r1[13] - r0[13];
    r[ 6] = r0[ 6] + r2[ 6] + r1[14] - r0[14];
    r[ 7] = r0[ 7] + r2[ 7] + r1[15] - r0[15];
    r[ 8] = r2[ 8]          + r1[ 0] - r0[ 0] + r1[ 8];
    r[ 9] = r2[ 9]          + r1[ 1] - r0[ 1] + r1[ 9];
    r[10] = r2[10]          + r1[ 2] - r0[ 2] + r1[10];
    r[11] = r2[11]          + r1[ 3] - r0[ 3] + r1[11];
    r[12] = r2[12]          + r1[ 4] - r0[ 4] + r1[12];
    r[13] = r2[13]          + r1[ 5] - r0[ 5] + r1[13];
    r[14] = r2[14]          + r1[ 6] - r0[ 6] + r1[14];
    r[15] = r2[15]          + r1[ 7] - r0[ 7] + r1[15];
}

/* Invert the field element. (r * a) mod (2^448 - 2^224 - 1) = 1
 * Constant time implementation - using Fermat's little theorem:
 *   a^(p-1) mod p = 1 => a^(p-2) mod p = 1/a
 * For curve448: p - 2 = 2^448 - 2^224 - 3
 *
 * r  [in]  Field element to hold result.
 * a  [in]  Field element to invert.
 */
void fe448_invert(int32_t* r, const int32_t* a)
{
    int32_t t1[16];
    int32_t t2[16];
    int32_t t3[16];
    int32_t t4[16];
    int i;

    fe448_sqr(t1, a);
    /* t1 = 2 */
    fe448_mul(t1, t1, a);
    /* t1 = 3 */
    fe448_sqr(t2, t1); for (i = 1; i < 2; ++i) fe448_sqr(t2, t2);
    /* t2 = c */
    fe448_mul(t3, t2, a);
    /* t3 = d */
    fe448_mul(t1, t2, t1);
    /* t1 = f */
    fe448_sqr(t2, t1);
    /* t2 = 1e */
    fe448_mul(t4, t2, a);
    /* t4 = 1f */
    fe448_sqr(t2, t4); for (i = 1; i < 5; ++i) fe448_sqr(t2, t2);
    /* t2 = 3e0 */
    fe448_mul(t1, t2, t4);
    /* t1 = 3ff */
    fe448_sqr(t2, t1); for (i = 1; i < 10; ++i) fe448_sqr(t2, t2);
    /* t2 = ffc00 */
    fe448_mul(t1, t2, t1);
    /* t1 = fffff */
    fe448_sqr(t2, t1); for (i = 1; i < 5; ++i) fe448_sqr(t2, t2);
    /* t2 = 1ffffe0 */
    fe448_mul(t1, t2, t4);
    /* t1 = 1ffffff */
    fe448_sqr(t2, t1); for (i = 1; i < 25; ++i) fe448_sqr(t2, t2);
    /* t2 = 3fffffe000000 */
    fe448_mul(t1, t2, t1);
    /* t1 = 3ffffffffffff */
    fe448_sqr(t2, t1); for (i = 1; i < 5; ++i) fe448_sqr(t2, t2);
    /* t2 = 7fffffffffffe0 */
    fe448_mul(t1, t2, t4);
    /* t1 = 7fffffffffffff */
    fe448_sqr(t2, t1); for (i = 1; i < 55; ++i) fe448_sqr(t2, t2);
    /* t2 = 3fffffffffffff80000000000000 */
    fe448_mul(t1, t2, t1);
    /* t1 = 3fffffffffffffffffffffffffff */
    fe448_sqr(t2, t1); for (i = 1; i < 110; ++i) fe448_sqr(t2, t2);
    /* t2 = fffffffffffffffffffffffffffc000000000000000000000000000 */
    fe448_mul(t1, t2, t1);
    /* t1 = fffffffffffffffffffffffffffffffffffffffffffffffffffffff */
    fe448_sqr(t2, t1); for (i = 1; i < 4; ++i) fe448_sqr(t2, t2);
    /* t2 = fffffffffffffffffffffffffffffffffffffffffffffffffffffff0 */
    fe448_mul(t3, t3, t2);
    /* t3 = fffffffffffffffffffffffffffffffffffffffffffffffffffffffd */
    fe448_mul(t1, t3, a);
    /* t1 = fffffffffffffffffffffffffffffffffffffffffffffffffffffffe */
    fe448_sqr(t1, t1); for (i = 1; i < 224; ++i) fe448_sqr(t1, t1);
    /* t1 = fffffffffffffffffffffffffffffffffffffffffffffffffffffffe00000000000000000000000000000000000000000000000000000000 */
    fe448_mul(r, t3, t1);
    /* r = fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffffffffffffffffffffffffffffffffffffffffffffffffffffd */
}

/* Scalar multiply the point by a number. r = n.a
 * Uses Montogmery ladder and only requires the x-ordinate.
 *
 * r  [in]  Field element to hold result.
 * n  [in]  Scalar as an array of bytes.
 * a  [in]  Point to multiply - x-ordinate only.
 */
int curve448(byte* r, const byte* n, const byte* a)
{
    int32_t x1[16];
    int32_t x2[16];
    int32_t z2[16];
    int32_t x3[16];
    int32_t z3[16];
    int32_t t0[16];
    int32_t t1[16];
    int i;
    unsigned int swap;
    unsigned int b;

    fe448_from_bytes(x1, a);
    fe448_1(x2);
    fe448_0(z2);
    fe448_copy(x3, x1);
    fe448_1(z3);

    swap = 0;
    for (i = 447; i >= 0; --i) {
        b = (n[i >> 3] >> (i & 7)) & 1;
        swap ^= b;
        fe448_cswap(x2, x3, swap);
        fe448_cswap(z2, z3, swap);
        swap = b;

        /* Montgomery Ladder - double and add */
        fe448_add(t0, x2, z2);
        fe448_reduce(t0);
        fe448_add(t1, x3, z3);
        fe448_reduce(t1);
        fe448_sub(x2, x2, z2);
        fe448_sub(x3, x3, z3);
        fe448_mul(t1, t1, x2);
        fe448_mul(z3, x3, t0);
        fe448_sqr(t0, t0);
        fe448_sqr(x2, x2);
        fe448_add(x3, z3, t1);
        fe448_reduce(x3);
        fe448_sqr(x3, x3);
        fe448_sub(z3, z3, t1);
        fe448_sqr(z3, z3);
        fe448_mul(z3, z3, x1);
        fe448_sub(t1, t0, x2);
        fe448_mul(x2, t0, x2);
        fe448_mul39081(z2, t1);
        fe448_add(z2, t0, z2);
        fe448_mul(z2, z2, t1);
    }
    /* Last two bits are 0 - no final swap check required. */

    fe448_invert(z2, z2);
    fe448_mul(x2, x2, z2);
    fe448_to_bytes(r, x2);

    return 0;
}

#ifdef HAVE_ED448
/* Check whether field element is not 0.
 * Must convert to a normalized form before checking.
 *
 * a  [in]  Field element.
 * returns 0 when zero, and any other value otherwise.
 */
int fe448_isnonzero(const int32_t* a)
{
    uint8_t b[56];
    int i;
    uint8_t c = 0;
    fe448_to_bytes(b, a);
    for (i = 0; i < 56; i++)
        c |= b[i];
    return c;
}

/* Check whether field element is negative.
 * Must convert to a normalized form before checking.
 *
 * a  [in]  Field element.
 * returns 1 when negative, and 0 otherwise.
 */
int fe448_isnegative(const int32_t* a)
{
    uint8_t b[56];
    fe448_to_bytes(b, a);
    return b[0] & 1;
}

/* Negates the field element. r = -a
 *
 * r  [in]  Field element to hold result.
 * a  [in]  Field element.
 */
void fe448_neg(int32_t* r, const int32_t* a)
{
    r[0] = -a[0];
    r[1] = -a[1];
    r[2] = -a[2];
    r[3] = -a[3];
    r[4] = -a[4];
    r[5] = -a[5];
    r[6] = -a[6];
    r[7] = -a[7];
    r[8] = -a[8];
    r[9] = -a[9];
    r[10] = -a[10];
    r[11] = -a[11];
    r[12] = -a[12];
    r[13] = -a[13];
    r[14] = -a[14];
    r[15] = -a[15];
}

/* Raise field element to (p-3) / 4: 2^446 - 2^222 - 1
 * Used for calcualting y-ordinate from x-ordinate for Ed448.
 *
 * r  [in]  Field element to hold result.
 * a  [in]  Field element to exponentiate.
 */
void fe448_pow_2_446_222_1(int32_t* r, const int32_t* a)
{
    int32_t t1[16];
    int32_t t2[16];
    int32_t t3[16];
    int32_t t4[16];
    int32_t t5[16];
    int i;

    fe448_sqr(t3, a);
    /* t3 = 2 */
    fe448_mul(t1, t3, a);
    /* t1 = 3 */
    fe448_sqr(t5, t1);
    /* t5 = 6 */
    fe448_mul(t5, t5, a);
    /* t5 = 7 */
    fe448_sqr(t2, t1); for (i = 1; i < 2; ++i) fe448_sqr(t2, t2);
    /* t2 = c */
    fe448_mul(t3, t2, t3);
    /* t3 = e */
    fe448_mul(t1, t2, t1);
    /* t1 = f */
    fe448_sqr(t2, t1); for (i = 1; i < 3; ++i) fe448_sqr(t2, t2);
    /* t2 = 78 */
    fe448_mul(t5, t2, t5);
    /* t5 = 7f */
    fe448_sqr(t2, t1); for (i = 1; i < 4; ++i) fe448_sqr(t2, t2);
    /* t2 = f0 */
    fe448_mul(t1, t2, t1);
    /* t1 = ff */
    fe448_mul(t3, t3, t2);
    /* t3 = fe */
    fe448_sqr(t2, t1); for (i = 1; i < 7; ++i) fe448_sqr(t2, t2);
    /* t2 = 7f80 */
    fe448_mul(t5, t2, t5);
    /* t5 = 7fff */
    fe448_sqr(t2, t1); for (i = 1; i < 8; ++i) fe448_sqr(t2, t2);
    /* t2 = ff00 */
    fe448_mul(t1, t2, t1);
    /* t1 = ffff */
    fe448_mul(t3, t3, t2);
    /* t3 = fffe */
    fe448_sqr(t2, t5); for (i = 1; i < 15; ++i) fe448_sqr(t2, t2);
    /* t2 = 3fff8000 */
    fe448_mul(t5, t2, t5);
    /* t5 = 3fffffff */
    fe448_sqr(t2, t1); for (i = 1; i < 16; ++i) fe448_sqr(t2, t2);
    /* t2 = ffff0000 */
    fe448_mul(t1, t2, t1);
    /* t1 = ffffffff */
    fe448_mul(t3, t3, t2);
    /* t3 = fffffffe */
    fe448_sqr(t2, t1); for (i = 1; i < 32; ++i) fe448_sqr(t2, t2);
    /* t2 = ffffffff00000000 */
    fe448_mul(t2, t2, t1);
    /* t2 = ffffffffffffffff */
    fe448_sqr(t1, t2); for (i = 1; i < 64; ++i) fe448_sqr(t1, t1);
    /* t1 = ffffffffffffffff0000000000000000 */
    fe448_mul(t1, t1, t2);
    /* t1 = ffffffffffffffffffffffffffffffff */
    fe448_sqr(t1, t1); for (i = 1; i < 64; ++i) fe448_sqr(t1, t1);
    /* t1 = ffffffffffffffffffffffffffffffff0000000000000000 */
    fe448_mul(t4, t1, t2);
    /* t4 = ffffffffffffffffffffffffffffffffffffffffffffffff */
    fe448_sqr(t2, t4); for (i = 1; i < 32; ++i) fe448_sqr(t2, t2);
    /* t2 = ffffffffffffffffffffffffffffffffffffffffffffffff00000000 */
    fe448_mul(t3, t3, t2);
    /* t3 = fffffffffffffffffffffffffffffffffffffffffffffffffffffffe */
    fe448_sqr(t1, t3); for (i = 1; i < 192; ++i) fe448_sqr(t1, t1);
    /* t1 = fffffffffffffffffffffffffffffffffffffffffffffffffffffffe000000000000000000000000000000000000000000000000 */
    fe448_mul(t1, t1, t4);
    /* t1 = fffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffffffffffffffffffffffffffffffffffffffffffff */
    fe448_sqr(t1, t1); for (i = 1; i < 30; ++i) fe448_sqr(t1, t1);
    /* t1 = 3fffffffffffffffffffffffffffffffffffffffffffffffffffffffbfffffffffffffffffffffffffffffffffffffffffffffffc0000000 */
    fe448_mul(r, t5, t1);
    /* r = 3fffffffffffffffffffffffffffffffffffffffffffffffffffffffbfffffffffffffffffffffffffffffffffffffffffffffffffffffff */
}

/* Constant time, conditional move of b into a.
 * a is not changed if the condition is 0.
 *
 * a  A field element.
 * b  A field element.
 * c  If 1 then copy and if 0 then don't copy.
 */
void fe448_cmov(int32_t* a, const int32_t* b, int c)
{
    int32_t m = -(int32_t)c;
    int32_t t0 = m & (a[0] ^ b[0]);
    int32_t t1 = m & (a[1] ^ b[1]);
    int32_t t2 = m & (a[2] ^ b[2]);
    int32_t t3 = m & (a[3] ^ b[3]);
    int32_t t4 = m & (a[4] ^ b[4]);
    int32_t t5 = m & (a[5] ^ b[5]);
    int32_t t6 = m & (a[6] ^ b[6]);
    int32_t t7 = m & (a[7] ^ b[7]);
    int32_t t8 = m & (a[8] ^ b[8]);
    int32_t t9 = m & (a[9] ^ b[9]);
    int32_t t10 = m & (a[10] ^ b[10]);
    int32_t t11 = m & (a[11] ^ b[11]);
    int32_t t12 = m & (a[12] ^ b[12]);
    int32_t t13 = m & (a[13] ^ b[13]);
    int32_t t14 = m & (a[14] ^ b[14]);
    int32_t t15 = m & (a[15] ^ b[15]);

    a[0] ^= t0;
    a[1] ^= t1;
    a[2] ^= t2;
    a[3] ^= t3;
    a[4] ^= t4;
    a[5] ^= t5;
    a[6] ^= t6;
    a[7] ^= t7;
    a[8] ^= t8;
    a[9] ^= t9;
    a[10] ^= t10;
    a[11] ^= t11;
    a[12] ^= t12;
    a[13] ^= t13;
    a[14] ^= t14;
    a[15] ^= t15;
}

#endif /* HAVE_ED448 */
#endif

#endif /* HAVE_CURVE448 || HAVE_ED448 */
