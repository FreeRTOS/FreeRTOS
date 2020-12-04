/* cmac.c
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

#if defined(WOLFSSL_CMAC) && !defined(NO_AES) && defined(WOLFSSL_AES_DIRECT)

#if defined(HAVE_FIPS) && \
	defined(HAVE_FIPS_VERSION) && (HAVE_FIPS_VERSION >= 2)

    /* set NO_WRAPPERS before headers, use direct internal f()s not wrappers */
    #define FIPS_NO_WRAPPERS

    #ifdef USE_WINDOWS_API
        #pragma code_seg(".fipsA$n")
        #pragma const_seg(".fipsB$n")
    #endif
#endif

#ifdef NO_INLINE
    #include <wolfssl/wolfcrypt/misc.h>
#else
    #define WOLFSSL_MISC_INCLUDED
    #include <wolfcrypt/src/misc.c>
#endif

#include <wolfssl/wolfcrypt/error-crypt.h>
#include <wolfssl/wolfcrypt/aes.h>
#include <wolfssl/wolfcrypt/cmac.h>


static void ShiftAndXorRb(byte* out, byte* in)
{
    int i, j, xorRb;
    int mask = 0, last = 0;
    byte Rb = 0x87;

    xorRb = (in[0] & 0x80) != 0;

    for (i = 1, j = AES_BLOCK_SIZE - 1; i <= AES_BLOCK_SIZE; i++, j--) {
        last = (in[j] & 0x80) ? 1 : 0;
        out[j] = (byte)((in[j] << 1) | mask);
        mask = last;
        if (xorRb) {
            out[j] ^= Rb;
            Rb = 0;
        }
    }
}


int wc_InitCmac(Cmac* cmac, const byte* key, word32 keySz,
                int type, void* unused)
{
    int ret;

    (void)unused;

    if (cmac == NULL || key == NULL || keySz == 0 || type != WC_CMAC_AES)
        return BAD_FUNC_ARG;

    XMEMSET(cmac, 0, sizeof(Cmac));
    ret = wc_AesSetKey(&cmac->aes, key, keySz, NULL, AES_ENCRYPTION);
    if (ret == 0) {
        byte l[AES_BLOCK_SIZE];

        XMEMSET(l, 0, AES_BLOCK_SIZE);
        wc_AesEncryptDirect(&cmac->aes, l, l);
        ShiftAndXorRb(cmac->k1, l);
        ShiftAndXorRb(cmac->k2, cmac->k1);
        ForceZero(l, AES_BLOCK_SIZE);
    }
    return ret;
}


int wc_CmacUpdate(Cmac* cmac, const byte* in, word32 inSz)
{
    if ((cmac == NULL) || (in == NULL && inSz != 0))
        return BAD_FUNC_ARG;

    while (inSz != 0) {
        word32 add = min(inSz, AES_BLOCK_SIZE - cmac->bufferSz);
        XMEMCPY(&cmac->buffer[cmac->bufferSz], in, add);

        cmac->bufferSz += add;
        in += add;
        inSz -= add;

        if (cmac->bufferSz == AES_BLOCK_SIZE && inSz != 0) {
            if (cmac->totalSz != 0)
                xorbuf(cmac->buffer, cmac->digest, AES_BLOCK_SIZE);
            wc_AesEncryptDirect(&cmac->aes,
                                cmac->digest,
                                cmac->buffer);
            cmac->totalSz += AES_BLOCK_SIZE;
            cmac->bufferSz = 0;
        }
    }

    return 0;
}


int wc_CmacFinal(Cmac* cmac, byte* out, word32* outSz)
{
    const byte* subKey;

    if (cmac == NULL || out == NULL || outSz == NULL)
        return BAD_FUNC_ARG;

    if (*outSz < WC_CMAC_TAG_MIN_SZ || *outSz > WC_CMAC_TAG_MAX_SZ)
        return BUFFER_E;

    if (cmac->bufferSz == AES_BLOCK_SIZE) {
        subKey = cmac->k1;
    }
    else {
        word32 remainder = AES_BLOCK_SIZE - cmac->bufferSz;

        if (remainder == 0)
            remainder = AES_BLOCK_SIZE;

        if (remainder > 1)
            XMEMSET(cmac->buffer + AES_BLOCK_SIZE - remainder, 0, remainder);
        cmac->buffer[AES_BLOCK_SIZE - remainder] = 0x80;
        subKey = cmac->k2;
    }
    xorbuf(cmac->buffer, cmac->digest, AES_BLOCK_SIZE);
    xorbuf(cmac->buffer, subKey, AES_BLOCK_SIZE);
    wc_AesEncryptDirect(&cmac->aes, cmac->digest, cmac->buffer);

    XMEMCPY(out, cmac->digest, *outSz);

    ForceZero(cmac, sizeof(Cmac));

    return 0;
}


int wc_AesCmacGenerate(byte* out, word32* outSz,
                       const byte* in, word32 inSz,
                       const byte* key, word32 keySz)
{
    Cmac cmac;
    int ret;

    if (out == NULL || (in == NULL && inSz > 0) || key == NULL || keySz == 0)
        return BAD_FUNC_ARG;

    ret = wc_InitCmac(&cmac, key, keySz, WC_CMAC_AES, NULL);
    if (ret != 0)
        return ret;

    ret = wc_CmacUpdate(&cmac, in, inSz);
    if (ret != 0)
        return ret;

    ret = wc_CmacFinal(&cmac, out, outSz);
    if (ret != 0)
        return ret;

    return 0;
}


int wc_AesCmacVerify(const byte* check, word32 checkSz,
                     const byte* in, word32 inSz,
                     const byte* key, word32 keySz)
{
    byte a[AES_BLOCK_SIZE];
    word32 aSz = sizeof(a);
    int result;
    int compareRet;

    if (check == NULL || checkSz == 0 || (in == NULL && inSz != 0) ||
        key == NULL || keySz == 0)

        return BAD_FUNC_ARG;

    XMEMSET(a, 0, aSz);
    result = wc_AesCmacGenerate(a, &aSz, in, inSz, key, keySz);
    compareRet = ConstantCompare(check, a, min(checkSz, aSz));

    if (result == 0)
        result = compareRet ? 1 : 0;

    return result;
}


#endif /* WOLFSSL_CMAC && NO_AES && WOLFSSL_AES_DIRECT */
