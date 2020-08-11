/* chacha.h
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

/*!
    \file wolfssl/wolfcrypt/chacha.h
*/


#ifndef WOLF_CRYPT_CHACHA_H
#define WOLF_CRYPT_CHACHA_H

#include <wolfssl/wolfcrypt/types.h>

#ifdef HAVE_CHACHA

#ifdef __cplusplus
    extern "C" {
#endif

/* Size of the IV */
#define CHACHA_IV_WORDS    3
#define CHACHA_IV_BYTES    (CHACHA_IV_WORDS * sizeof(word32))

/* Size of ChaCha chunks */
#define CHACHA_CHUNK_WORDS 16
#define CHACHA_CHUNK_BYTES (CHACHA_CHUNK_WORDS * sizeof(word32))

#ifdef WOLFSSL_X86_64_BUILD
#if defined(USE_INTEL_SPEEDUP) && !defined(NO_CHACHA_ASM)
    #define USE_INTEL_CHACHA_SPEEDUP
    #define HAVE_INTEL_AVX1
#endif
#endif

enum {
	CHACHA_ENC_TYPE = WC_CIPHER_CHACHA,    /* cipher unique type */
    CHACHA_MAX_KEY_SZ = 32,
};

typedef struct ChaCha {
    word32 X[CHACHA_CHUNK_WORDS];           /* state of cipher */
    word32 left;                            /* number of bytes leftover */
#ifdef HAVE_INTEL_AVX1
    /* vpshufd reads 16 bytes but we only use bottom 4. */
    byte extra[12];
#endif
} ChaCha;

/**
  * IV(nonce) changes with each record
  * counter is for what value the block counter should start ... usually 0
  */
WOLFSSL_API int wc_Chacha_SetIV(ChaCha* ctx, const byte* inIv, word32 counter);

WOLFSSL_API int wc_Chacha_Process(ChaCha* ctx, byte* cipher, const byte* plain,
                              word32 msglen);
WOLFSSL_API int wc_Chacha_SetKey(ChaCha* ctx, const byte* key, word32 keySz);

#ifdef __cplusplus
    } /* extern "C" */
#endif

#endif /* HAVE_CHACHA */
#endif /* WOLF_CRYPT_CHACHA_H */

