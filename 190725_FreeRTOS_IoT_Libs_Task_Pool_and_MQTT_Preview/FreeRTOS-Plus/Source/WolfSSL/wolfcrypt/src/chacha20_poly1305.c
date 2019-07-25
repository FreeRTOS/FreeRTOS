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
 */


#ifdef HAVE_CONFIG_H
    #include <config.h>
#endif

#include <wolfssl/wolfcrypt/settings.h>

#if defined(HAVE_CHACHA) && defined(HAVE_POLY1305)

#include <wolfssl/wolfcrypt/chacha20_poly1305.h>
#include <wolfssl/wolfcrypt/error-crypt.h>
#include <wolfssl/wolfcrypt/logging.h>
#include <wolfssl/wolfcrypt/chacha.h>
#include <wolfssl/wolfcrypt/poly1305.h>

#ifdef NO_INLINE
#include <wolfssl/wolfcrypt/misc.h>
#else
#include <wolfcrypt/src/misc.c>
#endif

#ifdef CHACHA_AEAD_TEST
#include <stdio.h>
#endif

#define CHACHA20_POLY1305_AEAD_INITIAL_COUNTER  0
#define CHACHA20_POLY1305_MAC_PADDING_ALIGNMENT 16

static void word32ToLittle64(const word32 inLittle32, byte outLittle64[8]);
static int calculateAuthTag(
                  const byte inAuthKey[CHACHA20_POLY1305_AEAD_KEYSIZE],
                  const byte* inAAD, const word32 inAADLen,
                  const byte *inCiphertext, const word32 inCiphertextLen,
                  byte outAuthTag[CHACHA20_POLY1305_AEAD_AUTHTAG_SIZE]);

int wc_ChaCha20Poly1305_Encrypt(
                const byte inKey[CHACHA20_POLY1305_AEAD_KEYSIZE],
                const byte inIV[CHACHA20_POLY1305_AEAD_IV_SIZE],
                const byte* inAAD, const word32 inAADLen,
                const byte* inPlaintext, const word32 inPlaintextLen,
                byte* outCiphertext,
                byte outAuthTag[CHACHA20_POLY1305_AEAD_AUTHTAG_SIZE])
{
    int err;
    byte poly1305Key[CHACHA20_POLY1305_AEAD_KEYSIZE];
    ChaCha chaChaCtx;

    /* Validate function arguments */

    if (!inKey || !inIV ||
        !inPlaintext || !inPlaintextLen ||
        !outCiphertext ||
        !outAuthTag)
    {
        return BAD_FUNC_ARG;
    }

    XMEMSET(poly1305Key, 0, sizeof(poly1305Key));

    /* Create the Poly1305 key */
    err = wc_Chacha_SetKey(&chaChaCtx, inKey, CHACHA20_POLY1305_AEAD_KEYSIZE);
    if (err != 0) return err;

    err = wc_Chacha_SetIV(&chaChaCtx, inIV,
                           CHACHA20_POLY1305_AEAD_INITIAL_COUNTER);
    if (err != 0) return err;

    err = wc_Chacha_Process(&chaChaCtx, poly1305Key, poly1305Key,
                             CHACHA20_POLY1305_AEAD_KEYSIZE);
    if (err != 0) return err;

    /* Encrypt the plaintext using ChaCha20 */
    err = wc_Chacha_Process(&chaChaCtx, outCiphertext, inPlaintext,
                            inPlaintextLen);
    /* Calculate the Poly1305 auth tag */
    if (err == 0)
        err = calculateAuthTag(poly1305Key,
                               inAAD, inAADLen,
                               outCiphertext, inPlaintextLen,
                               outAuthTag);
    ForceZero(poly1305Key, sizeof(poly1305Key));

    return err;
}


int wc_ChaCha20Poly1305_Decrypt(
                const byte inKey[CHACHA20_POLY1305_AEAD_KEYSIZE],
                const byte inIV[CHACHA20_POLY1305_AEAD_IV_SIZE],
                const byte* inAAD, const word32 inAADLen,
                const byte* inCiphertext, const word32 inCiphertextLen,
                const byte inAuthTag[CHACHA20_POLY1305_AEAD_AUTHTAG_SIZE],
                byte* outPlaintext)
{
    int err;
    byte poly1305Key[CHACHA20_POLY1305_AEAD_KEYSIZE];
    ChaCha chaChaCtx;
    byte calculatedAuthTag[CHACHA20_POLY1305_AEAD_AUTHTAG_SIZE];

    /* Validate function arguments */

    if (!inKey || !inIV ||
        !inCiphertext || !inCiphertextLen ||
        !inAuthTag ||
        !outPlaintext)
    {
        return BAD_FUNC_ARG;
    }

    XMEMSET(calculatedAuthTag, 0, sizeof(calculatedAuthTag));
    XMEMSET(poly1305Key, 0, sizeof(poly1305Key));

    /* Create the Poly1305 key */
    err = wc_Chacha_SetKey(&chaChaCtx, inKey, CHACHA20_POLY1305_AEAD_KEYSIZE);
    if (err != 0) return err;

    err = wc_Chacha_SetIV(&chaChaCtx, inIV,
                           CHACHA20_POLY1305_AEAD_INITIAL_COUNTER);
    if (err != 0) return err;

    err = wc_Chacha_Process(&chaChaCtx, poly1305Key, poly1305Key,
                             CHACHA20_POLY1305_AEAD_KEYSIZE);
    if (err != 0) return err;

    /* Calculate the Poly1305 auth tag */
    err = calculateAuthTag(poly1305Key,
                           inAAD, inAADLen,
                           inCiphertext, inCiphertextLen,
                           calculatedAuthTag);

    /* Compare the calculated auth tag with the received one */
    if (err == 0 && ConstantCompare(inAuthTag, calculatedAuthTag,
                                    CHACHA20_POLY1305_AEAD_AUTHTAG_SIZE) != 0)
    {
        err = MAC_CMP_FAILED_E;
    }

    /* Decrypt the received ciphertext */
    if (err == 0)
        err = wc_Chacha_Process(&chaChaCtx, outPlaintext, inCiphertext,
                                inCiphertextLen);
    ForceZero(poly1305Key, sizeof(poly1305Key));

    return err;
}


static int calculateAuthTag(
                const byte inAuthKey[CHACHA20_POLY1305_AEAD_KEYSIZE],
                const byte *inAAD, const word32 inAADLen,
                const byte *inCiphertext, const word32 inCiphertextLen,
                 byte outAuthTag[CHACHA20_POLY1305_AEAD_AUTHTAG_SIZE])
{
    int err;
    Poly1305 poly1305Ctx;
    byte padding[CHACHA20_POLY1305_MAC_PADDING_ALIGNMENT - 1];
    word32 paddingLen;
    byte little64[8];

    XMEMSET(padding, 0, sizeof(padding));

    /* Initialize Poly1305 */

    err = wc_Poly1305SetKey(&poly1305Ctx, inAuthKey,
                            CHACHA20_POLY1305_AEAD_KEYSIZE);
    if (err)
    {
        return err;
    }

    /* Create the authTag by MAC'ing the following items: */

    /* -- AAD */

    if (inAAD && inAADLen)
    {
        err = wc_Poly1305Update(&poly1305Ctx, inAAD, inAADLen);

        /* -- padding1: pad the AAD to 16 bytes */

        paddingLen = -inAADLen & (CHACHA20_POLY1305_MAC_PADDING_ALIGNMENT - 1);
        if (paddingLen)
        {
            err += wc_Poly1305Update(&poly1305Ctx, padding, paddingLen);
        }

        if (err)
        {
            return err;
        }
    }

    /* -- Ciphertext */

    err = wc_Poly1305Update(&poly1305Ctx, inCiphertext, inCiphertextLen);
    if (err)
    {
        return err;
    }

    /* -- padding2: pad the ciphertext to 16 bytes */

    paddingLen = -inCiphertextLen &
                                  (CHACHA20_POLY1305_MAC_PADDING_ALIGNMENT - 1);
    if (paddingLen)
    {
        err = wc_Poly1305Update(&poly1305Ctx, padding, paddingLen);
        if (err)
        {
            return err;
        }
    }

    /* -- AAD length as a 64-bit little endian integer */

    word32ToLittle64(inAADLen, little64);

    err = wc_Poly1305Update(&poly1305Ctx, little64, sizeof(little64));
    if (err)
    {
        return err;
    }

    /* -- Ciphertext length as a 64-bit little endian integer */

    word32ToLittle64(inCiphertextLen, little64);

    err = wc_Poly1305Update(&poly1305Ctx, little64, sizeof(little64));
    if (err)
    {
        return err;
    }

    /* Finalize the auth tag */

    err = wc_Poly1305Final(&poly1305Ctx, outAuthTag);

    return err;
}


static void word32ToLittle64(const word32 inLittle32, byte outLittle64[8])
{
    XMEMSET(outLittle64, 0, 8);

    outLittle64[0] = (inLittle32 & 0x000000FF);
    outLittle64[1] = (inLittle32 & 0x0000FF00) >> 8;
    outLittle64[2] = (inLittle32 & 0x00FF0000) >> 16;
    outLittle64[3] = (inLittle32 & 0xFF000000) >> 24;
}


#endif /* HAVE_CHACHA && HAVE_POLY1305 */
