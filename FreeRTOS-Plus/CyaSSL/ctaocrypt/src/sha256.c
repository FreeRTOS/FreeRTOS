/* sha256.c
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


/* code submitted by raphael.huck@efixo.com */

#ifdef HAVE_CONFIG_H
    #include <config.h>
#endif

#ifndef NO_SHA256

#include <cyassl/ctaocrypt/sha256.h>
#ifdef NO_INLINE
    #include <cyassl/ctaocrypt/misc.h>
#else
    #include <ctaocrypt/src/misc.c>
#endif


#ifndef min

    static INLINE word32 min(word32 a, word32 b)
    {
        return a > b ? b : a;
    }

#endif /* min */


void InitSha256(Sha256* sha256)
{
    sha256->digest[0] = 0x6A09E667L;
    sha256->digest[1] = 0xBB67AE85L;
    sha256->digest[2] = 0x3C6EF372L;
    sha256->digest[3] = 0xA54FF53AL;
    sha256->digest[4] = 0x510E527FL;
    sha256->digest[5] = 0x9B05688CL;
    sha256->digest[6] = 0x1F83D9ABL;
    sha256->digest[7] = 0x5BE0CD19L;

    sha256->buffLen = 0;
    sha256->loLen   = 0;
    sha256->hiLen   = 0;
}

static const word32 K[64] = {
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

#define Ch(x,y,z)       (z ^ (x & (y ^ z)))
#define Maj(x,y,z)      (((x | y) & z) | (x & y))
#define S(x, n)         rotrFixed(x, n)
#define R(x, n)         (((x)&0xFFFFFFFFL)>>(n))
#define Sigma0(x)       (S(x, 2) ^ S(x, 13) ^ S(x, 22))
#define Sigma1(x)       (S(x, 6) ^ S(x, 11) ^ S(x, 25))
#define Gamma0(x)       (S(x, 7) ^ S(x, 18) ^ R(x, 3))
#define Gamma1(x)       (S(x, 17) ^ S(x, 19) ^ R(x, 10))

#define RND(a,b,c,d,e,f,g,h,i) \
     t0 = h + Sigma1(e) + Ch(e, f, g) + K[i] + W[i]; \
     t1 = Sigma0(a) + Maj(a, b, c); \
     d += t0; \
     h  = t0 + t1;


static void Transform(Sha256* sha256)
{
    word32 S[8], W[64], t0, t1;
    int i;

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
}


static INLINE void AddLength(Sha256* sha256, word32 len)
{
    word32 tmp = sha256->loLen;
    if ( (sha256->loLen += len) < tmp)
        sha256->hiLen++;                       /* carry low to high */
}


void Sha256Update(Sha256* sha256, const byte* data, word32 len)
{
    /* do block size increments */
    byte* local = (byte*)sha256->buffer;

    while (len) {
        word32 add = min(len, SHA256_BLOCK_SIZE - sha256->buffLen);
        XMEMCPY(&local[sha256->buffLen], data, add);

        sha256->buffLen += add;
        data            += add;
        len             -= add;

        if (sha256->buffLen == SHA256_BLOCK_SIZE) {
            #ifdef LITTLE_ENDIAN_ORDER
                ByteReverseBytes(local, local, SHA256_BLOCK_SIZE);
            #endif
            Transform(sha256);
            AddLength(sha256, SHA256_BLOCK_SIZE);
            sha256->buffLen = 0;
        }
    }
}


void Sha256Final(Sha256* sha256, byte* hash)
{
    byte* local = (byte*)sha256->buffer;

    AddLength(sha256, sha256->buffLen);  /* before adding pads */

    local[sha256->buffLen++] = 0x80;  /* add 1 */

    /* pad with zeros */
    if (sha256->buffLen > SHA256_PAD_SIZE) {
        XMEMSET(&local[sha256->buffLen], 0, SHA256_BLOCK_SIZE - sha256->buffLen);
        sha256->buffLen += SHA256_BLOCK_SIZE - sha256->buffLen;

        #ifdef LITTLE_ENDIAN_ORDER
            ByteReverseBytes(local, local, SHA256_BLOCK_SIZE);
        #endif
        Transform(sha256);
        sha256->buffLen = 0;
    }
    XMEMSET(&local[sha256->buffLen], 0, SHA256_PAD_SIZE - sha256->buffLen);

    /* put lengths in bits */
    sha256->hiLen = (sha256->loLen >> (8*sizeof(sha256->loLen) - 3)) +
                 (sha256->hiLen << 3);
    sha256->loLen = sha256->loLen << 3;

    /* store lengths */
    #ifdef LITTLE_ENDIAN_ORDER
        ByteReverseBytes(local, local, SHA256_BLOCK_SIZE);
    #endif
    /* ! length ordering dependent on digest endian type ! */
    XMEMCPY(&local[SHA256_PAD_SIZE], &sha256->hiLen, sizeof(word32));
    XMEMCPY(&local[SHA256_PAD_SIZE + sizeof(word32)], &sha256->loLen,
            sizeof(word32));

    Transform(sha256);
    #ifdef LITTLE_ENDIAN_ORDER
        ByteReverseWords(sha256->digest, sha256->digest, SHA256_DIGEST_SIZE);
    #endif
    XMEMCPY(hash, sha256->digest, SHA256_DIGEST_SIZE);

    InitSha256(sha256);  /* reset state */
}


#endif /* NO_SHA256 */

