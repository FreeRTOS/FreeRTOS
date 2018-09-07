/* chacha.c
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
 *
 *  based from
 *  chacha-ref.c version 20080118
 *  D. J. Bernstein
 *  Public domain.
 */


#ifdef HAVE_CONFIG_H
    #include <config.h>
#endif

#include <wolfssl/wolfcrypt/settings.h>

#ifdef HAVE_CHACHA

#include <wolfssl/wolfcrypt/chacha.h>
#include <wolfssl/wolfcrypt/error-crypt.h>
#include <wolfssl/wolfcrypt/logging.h>
#ifdef NO_INLINE
    #include <wolfssl/wolfcrypt/misc.h>
#else
    #include <wolfcrypt/src/misc.c>
#endif

#ifdef CHACHA_AEAD_TEST
    #include <stdio.h>
#endif

#ifdef BIG_ENDIAN_ORDER
    #define LITTLE32(x) ByteReverseWord32(x)
#else
    #define LITTLE32(x) (x)
#endif

/* Number of rounds */
#define ROUNDS  20

#define U32C(v) (v##U)
#define U32V(v) ((word32)(v) & U32C(0xFFFFFFFF))
#define U8TO32_LITTLE(p) LITTLE32(((word32*)(p))[0])

#define ROTATE(v,c) rotlFixed(v, c)
#define XOR(v,w)    ((v) ^ (w))
#define PLUS(v,w)   (U32V((v) + (w)))
#define PLUSONE(v)  (PLUS((v),1))

#define QUARTERROUND(a,b,c,d) \
  x[a] = PLUS(x[a],x[b]); x[d] = ROTATE(XOR(x[d],x[a]),16); \
  x[c] = PLUS(x[c],x[d]); x[b] = ROTATE(XOR(x[b],x[c]),12); \
  x[a] = PLUS(x[a],x[b]); x[d] = ROTATE(XOR(x[d],x[a]), 8); \
  x[c] = PLUS(x[c],x[d]); x[b] = ROTATE(XOR(x[b],x[c]), 7);


/**
  * Set up iv(nonce). Earlier versions used 64 bits instead of 96, this version
  * uses the typical AEAD 96 bit nonce and can do record sizes of 256 GB.
  */
int wc_Chacha_SetIV(ChaCha* ctx, const byte* inIv, word32 counter)
{
    word32 temp[3];       /* used for alignment of memory */

#ifdef CHACHA_AEAD_TEST
    word32 i;
    printf("NONCE : ");
    for (i = 0; i < 12; i++) {
        printf("%02x", inIv[i]);
    }
    printf("\n\n");
#endif

    if (ctx == NULL)
        return BAD_FUNC_ARG;

    XMEMCPY(temp, inIv, 12);

    ctx->X[12] = LITTLE32(counter); /* block counter */
    ctx->X[13] = LITTLE32(temp[0]); /* fixed variable from nonce */
    ctx->X[14] = LITTLE32(temp[1]); /* counter from nonce */
    ctx->X[15] = LITTLE32(temp[2]); /* counter from nonce */

    return 0;
}

/* "expand 32-byte k" as unsigned 32 byte */
static const word32 sigma[4] = {0x61707865, 0x3320646e, 0x79622d32, 0x6b206574};
/* "expand 16-byte k" as unsigned 16 byte */
static const word32 tau[4] = {0x61707865, 0x3120646e, 0x79622d36, 0x6b206574};

/**
  * Key setup. 8 word iv (nonce)
  */
int wc_Chacha_SetKey(ChaCha* ctx, const byte* key, word32 keySz)
{
    const word32* constants;
    const byte*   k;

#ifdef XSTREAM_ALIGN
    word32 alignKey[8];
#endif

    if (ctx == NULL)
        return BAD_FUNC_ARG;

    if (keySz != 16 && keySz != 32)
        return BAD_FUNC_ARG;

#ifdef XSTREAM_ALIGN
    if ((wolfssl_word)key % 4) {
        WOLFSSL_MSG("wc_ChachaSetKey unaligned key");
        XMEMCPY(alignKey, key, keySz);
        k = (byte*)alignKey;
    }
    else {
        k = key;
    }
#else
    k = key;
#endif /* XSTREAM_ALIGN */

#ifdef CHACHA_AEAD_TEST
    word32 i;
    printf("ChaCha key used :\n");
    for (i = 0; i < keySz; i++) {
        printf("%02x", key[i]);
        if ((i + 1) % 8 == 0)
           printf("\n");
    }
    printf("\n\n");
#endif

    ctx->X[4] = U8TO32_LITTLE(k +  0);
    ctx->X[5] = U8TO32_LITTLE(k +  4);
    ctx->X[6] = U8TO32_LITTLE(k +  8);
    ctx->X[7] = U8TO32_LITTLE(k + 12);
    if (keySz == 32) {
        k += 16;
        constants = sigma;
    }
    else {
        constants = tau;
    }
    ctx->X[ 8] = U8TO32_LITTLE(k +  0);
    ctx->X[ 9] = U8TO32_LITTLE(k +  4);
    ctx->X[10] = U8TO32_LITTLE(k +  8);
    ctx->X[11] = U8TO32_LITTLE(k + 12);
    ctx->X[ 0] = constants[0];
    ctx->X[ 1] = constants[1];
    ctx->X[ 2] = constants[2];
    ctx->X[ 3] = constants[3];

    return 0;
}

/**
  * Converts word into bytes with rotations having been done.
  */
static INLINE void wc_Chacha_wordtobyte(word32 output[16], const word32 input[16])
{
    word32 x[16];
    word32 i;

    for (i = 0; i < 16; i++) {
        x[i] = input[i];
    }

    for (i = (ROUNDS); i > 0; i -= 2) {
        QUARTERROUND(0, 4,  8, 12)
        QUARTERROUND(1, 5,  9, 13)
        QUARTERROUND(2, 6, 10, 14)
        QUARTERROUND(3, 7, 11, 15)
        QUARTERROUND(0, 5, 10, 15)
        QUARTERROUND(1, 6, 11, 12)
        QUARTERROUND(2, 7,  8, 13)
        QUARTERROUND(3, 4,  9, 14)
    }

    for (i = 0; i < 16; i++) {
        x[i] = PLUS(x[i], input[i]);
    }

    for (i = 0; i < 16; i++) {
        output[i] = LITTLE32(x[i]);
    }
}

/**
  * Encrypt a stream of bytes
  */
static void wc_Chacha_encrypt_bytes(ChaCha* ctx, const byte* m, byte* c,
                                 word32 bytes)
{
    byte*  output;
    word32 temp[16]; /* used to make sure aligned */
    word32 i;

    output = (byte*)temp;

    if (!bytes) return;
    for (;;) {
        wc_Chacha_wordtobyte(temp, ctx->X);
        ctx->X[12] = PLUSONE(ctx->X[12]);
        if (bytes <= 64) {
            for (i = 0; i < bytes; ++i) {
                c[i] = m[i] ^ output[i];
            }
            return;
        }
        for (i = 0; i < 64; ++i) {
            c[i] = m[i] ^ output[i];
        }
        bytes -= 64;
        c += 64;
        m += 64;
    }
}

/**
  * API to encrypt/decrypt a message of any size.
  */
int wc_Chacha_Process(ChaCha* ctx, byte* output, const byte* input, word32 msglen)
{
    if (ctx == NULL)
        return BAD_FUNC_ARG;

    wc_Chacha_encrypt_bytes(ctx, input, output, msglen);

    return 0;
}

#endif /* HAVE_CHACHA*/

