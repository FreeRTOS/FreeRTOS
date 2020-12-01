/* idea.h
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

/*!
    \file wolfssl/wolfcrypt/idea.h
*/

#ifndef WOLF_CRYPT_IDEA_H
#define WOLF_CRYPT_IDEA_H

#include <wolfssl/wolfcrypt/types.h>

#ifdef HAVE_IDEA

#ifdef __cplusplus
    extern "C" {
#endif

enum {
    IDEA_MODULO     = 0x10001,             /* 2^16+1 */
    IDEA_2EXP16     = 0x10000,             /* 2^16 */
    IDEA_MASK       = 0xFFFF,              /* 16 bits set to one */
    IDEA_ROUNDS     = 8,                   /* number of rounds for IDEA */
    IDEA_SK_NUM     = (6*IDEA_ROUNDS + 4), /* number of subkeys */
    IDEA_KEY_SIZE   = 16,                  /* size of key in bytes */
    IDEA_BLOCK_SIZE = 8,                   /* size of IDEA blocks in bytes */
    IDEA_IV_SIZE    = 8,                   /* size of IDEA IV in bytes */
    IDEA_ENCRYPTION = 0,
    IDEA_DECRYPTION = 1
};

/* IDEA encryption and decryption */
typedef struct Idea {
    word32  reg[IDEA_BLOCK_SIZE / sizeof(word32)]; /* for CBC mode */
    word32  tmp[IDEA_BLOCK_SIZE / sizeof(word32)]; /* for CBC mode */
    word16  skey[IDEA_SK_NUM]; /* 832 bits expanded key */
} Idea;

WOLFSSL_API int wc_IdeaSetKey(Idea *idea, const byte* key, word16 keySz,
                              const byte *iv, int dir);
WOLFSSL_API int wc_IdeaSetIV(Idea *idea, const byte* iv);
WOLFSSL_API int wc_IdeaCipher(Idea *idea, byte* out, const byte* in);
WOLFSSL_API int wc_IdeaCbcEncrypt(Idea *idea, byte* out,
                                  const byte* in, word32 len);
WOLFSSL_API int wc_IdeaCbcDecrypt(Idea *idea, byte* out,
                                  const byte* in, word32 len);
#ifdef __cplusplus
    } /* extern "C" */
#endif

#endif /* HAVE_IDEA */
#endif /* WOLF_CRYPT_IDEA_H */
