/* idea.c
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


#ifdef HAVE_CONFIG_H
    #include <config.h>
#endif

#include <wolfssl/wolfcrypt/settings.h>

#ifdef HAVE_IDEA

#include <wolfssl/wolfcrypt/idea.h>

#include <wolfssl/wolfcrypt/error-crypt.h>
#include <wolfssl/wolfcrypt/logging.h>

#ifdef NO_INLINE
    #include <wolfssl/wolfcrypt/misc.h>
#else
    #define WOLFSSL_MISC_INCLUDED
    #include <wolfcrypt/src/misc.c>
#endif

/* multiplication of x and y modulo 2^16+1
 * IDEA specify a special case when an entry value is 0 ( x or y)
 * then it must be replaced by 2^16
 */
static WC_INLINE word16 idea_mult(word16 x, word16 y)
{
    long mul, res;

    mul = (long)x * (long)y;
    if (mul) {
        res = (mul & IDEA_MASK) - ((word32)mul >> 16);
        if (res <= 0)
            res += IDEA_MODULO;

        return (word16) (res & IDEA_MASK);
    }

    if (!x)
        return ((IDEA_MODULO - y) & IDEA_MASK);

    /* !y */
    return ((IDEA_MODULO - x) & IDEA_MASK);
}

/* compute 1/a modulo 2^16+1 using Extended euclidean algorithm
 * adapted from fp_invmod */
static WC_INLINE word16 idea_invmod(word16 x)
{
    int   u, v, b, d;

    if (x <= 1)
        return x;

    u = IDEA_MODULO;
    v = x;
    d = 1;
    b = 0;

    do {
        while (!(u & 1)) {
            u >>= 1;
            if (b & 1)
                b -= IDEA_MODULO;
            b >>= 1;
        }

        while (!(v & 1)) {
            v >>= 1;
            if (d & 1) {
                d -= IDEA_MODULO;
            }
            d >>= 1;
        }

        if (u >= v) {
            u -= v;
            b -= d;
        } else {
            v -= u;
            d -= b;
        }
    } while (u != 0);

    /* d is now the inverse, put positive value if required */
    while (d < 0)
        d += IDEA_MODULO;

    /* d must be < IDEA_MODULO */
    while (d >= (int)IDEA_MODULO)
        d -= IDEA_MODULO;

    return (word16)(d & IDEA_MASK);
}

/* generate the 52 16-bits key sub-blocks from the 128 key */
int wc_IdeaSetKey(Idea *idea, const byte* key, word16 keySz,
                  const byte *iv, int dir)
{
    word16  idx = 0;
    word32  t;
    short   i;

    if (idea == NULL || key == NULL || keySz != IDEA_KEY_SIZE ||
        (dir != IDEA_ENCRYPTION && dir != IDEA_DECRYPTION))
        return BAD_FUNC_ARG;

    /* initial key schedule for 0 -> 7 */
    for (i = 0; i < IDEA_ROUNDS; i++) {
        idea->skey[i]  = (word16)key[idx++] << 8;
        idea->skey[i] |= (word16)key[idx++];
    }

    /* shift phase key schedule for 8 -> 51 */
    for (i = IDEA_ROUNDS; i < IDEA_SK_NUM; i++) {
        t  = (word32)idea->skey[((i+1) & 7) ? i-7 : i-15] << 9;
        t |= (word32)idea->skey[((i+2) & 7) < 2 ? i-14 : i-6] >> 7;
        idea->skey[i] = (word16)(t & IDEA_MASK);
    }

    /* compute decryption key from encryption key */
    if (dir == IDEA_DECRYPTION) {
        word16  enckey[IDEA_SK_NUM];

        /* put encryption key in tmp buffer */
        XMEMCPY(enckey, idea->skey, sizeof(idea->skey));

        idx = 0;

        idea->skey[6*IDEA_ROUNDS]   = idea_invmod(enckey[idx++]);
        idea->skey[6*IDEA_ROUNDS+1] = (IDEA_2EXP16 - enckey[idx++]) & IDEA_MASK;
        idea->skey[6*IDEA_ROUNDS+2] = (IDEA_2EXP16 - enckey[idx++]) & IDEA_MASK;
        idea->skey[6*IDEA_ROUNDS+3] = idea_invmod(enckey[idx++]);

        for (i = 6*(IDEA_ROUNDS-1); i >= 0; i -= 6) {
            idea->skey[i+4] = enckey[idx++];
            idea->skey[i+5] = enckey[idx++];

            idea->skey[i] = idea_invmod(enckey[idx++]);
            if (i) {
                idea->skey[i+2] = (IDEA_2EXP16 - enckey[idx++]) & IDEA_MASK;
                idea->skey[i+1] = (IDEA_2EXP16 - enckey[idx++]) & IDEA_MASK;
            }
            else {
                idea->skey[1] = (IDEA_2EXP16 - enckey[idx++]) & IDEA_MASK;
                idea->skey[2] = (IDEA_2EXP16 - enckey[idx++]) & IDEA_MASK;
            }

            idea->skey[i+3] = idea_invmod(enckey[idx++]);
        }

        /* erase temporary buffer */
        ForceZero(enckey, sizeof(enckey));
    }

    /* set the iv */
    return wc_IdeaSetIV(idea, iv);
}

/* set the IV in the Idea key structure */
int wc_IdeaSetIV(Idea *idea, const byte* iv)
{
    if (idea == NULL)
        return BAD_FUNC_ARG;

    if (iv != NULL)
        XMEMCPY(idea->reg, iv, IDEA_BLOCK_SIZE);
    else
        XMEMSET(idea->reg, 0, IDEA_BLOCK_SIZE);

    return 0;
}

/* encryption/decryption for a block (64 bits)
 */
int wc_IdeaCipher(Idea *idea, byte* out, const byte* in)
{
    word32 t1, t2;
    word16 i, skey_idx = 0, idx = 0;
    word16 x[4];

    if (idea == NULL || out == NULL || in == NULL) {
        return BAD_FUNC_ARG;
    }

    /* put input byte block in word16 */
    for (i = 0; i < IDEA_BLOCK_SIZE/2; i++) {
        x[i]  = (word16)in[idx++] << 8;
        x[i] |= (word16)in[idx++];
    }

    for (i = 0; i < IDEA_ROUNDS; i++) {
        x[0] = idea_mult(x[0], idea->skey[skey_idx++]);
        x[1] = ((word32)x[1] + (word32)idea->skey[skey_idx++]) & IDEA_MASK;
        x[2] = ((word32)x[2] + (word32)idea->skey[skey_idx++]) & IDEA_MASK;
        x[3] = idea_mult(x[3], idea->skey[skey_idx++]);

        t2 = x[0] ^ x[2];
        t2 = idea_mult((word16)t2, idea->skey[skey_idx++]);
        t1 = (t2 + (x[1] ^ x[3])) & IDEA_MASK;
        t1 = idea_mult((word16)t1, idea->skey[skey_idx++]);
        t2 = (t1 + t2) & IDEA_MASK;

        x[0] ^= t1;
        x[3] ^= t2;

        t2 ^= x[1];
        x[1] = x[2] ^ (word16)t1;
        x[2] = (word16)t2;
    }

    x[0] = idea_mult(x[0], idea->skey[skey_idx++]);
    out[0] = (x[0] >> 8) & 0xFF;
    out[1] = x[0] & 0xFF;

    x[2] = ((word32)x[2] + (word32)idea->skey[skey_idx++]) & IDEA_MASK;
    out[2] = (x[2] >> 8) & 0xFF;
    out[3] = x[2] & 0xFF;

    x[1] = ((word32)x[1] + (word32)idea->skey[skey_idx++]) & IDEA_MASK;
    out[4] = (x[1] >> 8) & 0xFF;
    out[5] = x[1] & 0xFF;

    x[3] = idea_mult(x[3], idea->skey[skey_idx++]);
    out[6] = (x[3] >> 8) & 0xFF;
    out[7] = x[3] & 0xFF;

    return 0;
}

int wc_IdeaCbcEncrypt(Idea *idea, byte* out, const byte* in, word32 len)
{
    int  blocks;
    int  ret;

    if (idea == NULL || out == NULL || in == NULL)
        return BAD_FUNC_ARG;

    blocks = len / IDEA_BLOCK_SIZE;
    while (blocks--) {
        xorbuf((byte*)idea->reg, in, IDEA_BLOCK_SIZE);
        ret = wc_IdeaCipher(idea, (byte*)idea->reg, (byte*)idea->reg);
        if (ret != 0) {
            return ret;
        }

        XMEMCPY(out, idea->reg, IDEA_BLOCK_SIZE);

        out += IDEA_BLOCK_SIZE;
        in  += IDEA_BLOCK_SIZE;
    }

    return 0;
}

int wc_IdeaCbcDecrypt(Idea *idea, byte* out, const byte* in, word32 len)
{
    int  blocks;
    int  ret;

    if (idea == NULL || out == NULL || in == NULL)
        return BAD_FUNC_ARG;

    blocks = len / IDEA_BLOCK_SIZE;
    while (blocks--) {
        XMEMCPY((byte*)idea->tmp, in, IDEA_BLOCK_SIZE);
        ret = wc_IdeaCipher(idea, out, (byte*)idea->tmp);
        if (ret != 0) {
            return ret;
        }

        xorbuf(out, (byte*)idea->reg, IDEA_BLOCK_SIZE);
        XMEMCPY(idea->reg, idea->tmp, IDEA_BLOCK_SIZE);

        out += IDEA_BLOCK_SIZE;
        in  += IDEA_BLOCK_SIZE;
    }

    return 0;
}

#endif /* HAVE_IDEA */
