/* chacha.c
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
/*

DESCRIPTION
This library contains implementation for the ChaCha20 stream cipher.

Based from chacha-ref.c version 20080118
D. J. Bernstein
Public domain.

*/
#ifdef WOLFSSL_ARMASM
    /* implementation is located in wolfcrypt/src/port/arm/armv8-chacha.c */

#else
#ifdef HAVE_CONFIG_H
    #include <config.h>
#endif

#include <wolfssl/wolfcrypt/settings.h>

#if defined(HAVE_CHACHA) && !defined(WOLFSSL_ARMASM)

#include <wolfssl/wolfcrypt/chacha.h>
#include <wolfssl/wolfcrypt/error-crypt.h>
#include <wolfssl/wolfcrypt/logging.h>
#include <wolfssl/wolfcrypt/cpuid.h>
#ifdef NO_INLINE
    #include <wolfssl/wolfcrypt/misc.h>
#else
    #define WOLFSSL_MISC_INCLUDED
    #include <wolfcrypt/src/misc.c>
#endif

#ifdef CHACHA_AEAD_TEST
    #include <stdio.h>
#endif

#ifdef USE_INTEL_CHACHA_SPEEDUP
    #include <emmintrin.h>
    #include <immintrin.h>

    #if defined(__GNUC__) && ((__GNUC__ < 4) || \
                              (__GNUC__ == 4 && __GNUC_MINOR__ <= 8))
        #undef  NO_AVX2_SUPPORT
        #define NO_AVX2_SUPPORT
    #endif
    #if defined(__clang__) && ((__clang_major__ < 3) || \
                               (__clang_major__ == 3 && __clang_minor__ <= 5))
        #undef  NO_AVX2_SUPPORT
        #define NO_AVX2_SUPPORT
    #elif defined(__clang__) && defined(NO_AVX2_SUPPORT)
        #undef NO_AVX2_SUPPORT
    #endif

    #ifndef NO_AVX2_SUPPORT
        #define HAVE_INTEL_AVX2
    #endif

    static int cpuidFlagsSet = 0;
    static int cpuidFlags = 0;
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
    word32 temp[CHACHA_IV_WORDS];/* used for alignment of memory */


    if (ctx == NULL || inIv == NULL)
        return BAD_FUNC_ARG;

    XMEMCPY(temp, inIv, CHACHA_IV_BYTES);

    ctx->left = 0; /* resets state */
    ctx->X[CHACHA_MATRIX_CNT_IV+0] = counter;           /* block counter */
    ctx->X[CHACHA_MATRIX_CNT_IV+1] = LITTLE32(temp[0]); /* fixed variable from nonce */
    ctx->X[CHACHA_MATRIX_CNT_IV+2] = LITTLE32(temp[1]); /* counter from nonce */
    ctx->X[CHACHA_MATRIX_CNT_IV+3] = LITTLE32(temp[2]); /* counter from nonce */

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

    if (ctx == NULL || key == NULL)
        return BAD_FUNC_ARG;

    if (keySz != (CHACHA_MAX_KEY_SZ/2) && keySz != CHACHA_MAX_KEY_SZ)
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
    if (keySz == CHACHA_MAX_KEY_SZ) {
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
    ctx->left = 0; /* resets state */

    return 0;
}

/**
  * Converts word into bytes with rotations having been done.
  */
static WC_INLINE void wc_Chacha_wordtobyte(word32 output[CHACHA_CHUNK_WORDS],
    const word32 input[CHACHA_CHUNK_WORDS])
{
    word32 x[CHACHA_CHUNK_WORDS];
    word32 i;

    for (i = 0; i < CHACHA_CHUNK_WORDS; i++) {
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

    for (i = 0; i < CHACHA_CHUNK_WORDS; i++) {
        x[i] = PLUS(x[i], input[i]);
    }

    for (i = 0; i < CHACHA_CHUNK_WORDS; i++) {
        output[i] = LITTLE32(x[i]);
    }
}

#ifdef __cplusplus
    extern "C" {
#endif

extern void chacha_encrypt_x64(ChaCha* ctx, const byte* m, byte* c,
                               word32 bytes);
extern void chacha_encrypt_avx1(ChaCha* ctx, const byte* m, byte* c,
                                word32 bytes);
extern void chacha_encrypt_avx2(ChaCha* ctx, const byte* m, byte* c,
                                word32 bytes);

#ifdef __cplusplus
    }  /* extern "C" */
#endif


/**
  * Encrypt a stream of bytes
  */
static void wc_Chacha_encrypt_bytes(ChaCha* ctx, const byte* m, byte* c,
                                    word32 bytes)
{
    byte*  output;
    word32 temp[CHACHA_CHUNK_WORDS]; /* used to make sure aligned */
    word32 i;

    /* handle left overs */
    if (bytes > 0 && ctx->left > 0) {
        wc_Chacha_wordtobyte(temp, ctx->X); /* recreate the stream */
        output = (byte*)temp + CHACHA_CHUNK_BYTES - ctx->left;
        for (i = 0; i < bytes && i < ctx->left; i++) {
            c[i] = (byte)(m[i] ^ output[i]);
        }
        ctx->left = ctx->left - i;

        /* Used up all of the stream that was left, increment the counter */
        if (ctx->left == 0) {
            ctx->X[CHACHA_MATRIX_CNT_IV] = PLUSONE(ctx->X[CHACHA_MATRIX_CNT_IV]);
        }
        bytes = bytes - i;
        c += i;
        m += i;
    }

    output = (byte*)temp;
    while (bytes >= CHACHA_CHUNK_BYTES) {
        wc_Chacha_wordtobyte(temp, ctx->X);
        ctx->X[CHACHA_MATRIX_CNT_IV] = PLUSONE(ctx->X[CHACHA_MATRIX_CNT_IV]);
        for (i = 0; i < CHACHA_CHUNK_BYTES; ++i) {
            c[i] = (byte)(m[i] ^ output[i]);
        }
        bytes -= CHACHA_CHUNK_BYTES;
        c += CHACHA_CHUNK_BYTES;
        m += CHACHA_CHUNK_BYTES;
    }

    if (bytes) {
        /* in this case there will always be some left over since bytes is less
         * than CHACHA_CHUNK_BYTES, so do not increment counter after getting
         * stream in order for the stream to be recreated on next call */
        wc_Chacha_wordtobyte(temp, ctx->X);
        for (i = 0; i < bytes; ++i) {
            c[i] = m[i] ^ output[i];
        }
        ctx->left = CHACHA_CHUNK_BYTES - i;
    }
}


/**
  * API to encrypt/decrypt a message of any size.
  */
int wc_Chacha_Process(ChaCha* ctx, byte* output, const byte* input,
                      word32 msglen)
{
    if (ctx == NULL || input == NULL || output == NULL)
        return BAD_FUNC_ARG;

#ifdef USE_INTEL_CHACHA_SPEEDUP
    if (!cpuidFlagsSet) {
        cpuidFlags = cpuid_get_flags();
        cpuidFlagsSet = 1;
    }

    #ifdef HAVE_INTEL_AVX2
    if (IS_INTEL_AVX2(cpuidFlags)) {
        chacha_encrypt_avx2(ctx, input, output, msglen);
        return 0;
    }
    #endif
    if (IS_INTEL_AVX1(cpuidFlags)) {
        chacha_encrypt_avx1(ctx, input, output, msglen);
        return 0;
    }
    else {
        chacha_encrypt_x64(ctx, input, output, msglen);
        return 0;
    }
#endif
    wc_Chacha_encrypt_bytes(ctx, input, output, msglen);

    return 0;
}

#endif /* HAVE_CHACHA*/

#endif /* WOLFSSL_ARMASM */
