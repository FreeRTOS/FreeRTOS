/* xil-aesgcm.c
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


#ifdef HAVE_CONFIG_H
    #include <config.h>
#endif

#include <wolfssl/wolfcrypt/settings.h>

#if !defined(NO_AES) && defined(WOLFSSL_XILINX_CRYPT)

#include <wolfssl/wolfcrypt/aes.h>


#ifdef HAVE_AESGCM
/* Make calls to Xilinx hardened AES-GCM crypto */

#include <wolfssl/wolfcrypt/error-crypt.h>
#include <wolfssl/wolfcrypt/logging.h>

#ifdef NO_INLINE
    #include <wolfssl/wolfcrypt/misc.h>
#else
    #define WOLFSSL_MISC_INCLUDED
    #include <wolfcrypt/src/misc.c>
#endif

#include "xparameters.h"

enum {
    AEAD_NONCE_SZ       = 12,
    AES_GCM_AUTH_SZ     = 16, /* AES-GCM Auth Tag length    */
};


int  wc_AesGcmSetKey_ex(Aes* aes, const byte* key, word32 len, word32 kup)
{
    XCsuDma_Config* con;

    if (aes == NULL || key == NULL) {
        return BAD_FUNC_ARG;
    }

    if (len != 32) {
        WOLFSSL_MSG("Expecting a 256 bit key");
        return BAD_FUNC_ARG;
    }

    if ((con = XCsuDma_LookupConfig(0)) == NULL) {
        WOLFSSL_MSG("Failed to look up config");
        return MEMORY_E;
    }

    /* XST_SUCCESS comes from Xilinx header file */
    if (XCsuDma_CfgInitialize(&(aes->dma), con, con->BaseAddress) !=
            XST_SUCCESS) {
        WOLFSSL_MSG("Failed to initialize hardware");
        return MEMORY_E;
    }

    aes->keylen = len;
    aes->kup    = kup;
    XMEMCPY((byte*)(aes->key_init), key, len);

    return 0;
}



int  wc_AesGcmEncrypt(Aes* aes, byte* out,
                                   const byte* in, word32 sz,
                                   const byte* iv, word32 ivSz,
                                   byte* authTag, word32 authTagSz,
                                   const byte* authIn, word32 authInSz)
{
    byte* tmp;
    byte scratch[AES_BLOCK_SIZE];
    byte initalCounter[AES_BLOCK_SIZE];

    if ((in == NULL && sz > 0) || iv == NULL || authTag == NULL ||
            authTagSz > AES_GCM_AUTH_SZ) {
        return BAD_FUNC_ARG;
    }

    if (ivSz != AEAD_NONCE_SZ) {
        WOLFSSL_MSG("Expecting an IV size of 12");
        return BAD_FUNC_ARG;
    }

    /* API expects that output is size of input + 16 byte tag. A temporary
     * buffer is created to keep AES encrypt from writing over the end of
     * out buffer. */
    if (in != NULL) {
        if (aes->keylen != 32) {
            WOLFSSL_MSG("Expecting 256 bit AES key");
            return BAD_FUNC_ARG;
        }

        tmp = (byte*)XMALLOC(sz + AES_GCM_AUTH_SZ, aes->heap,
            DYNAMIC_TYPE_TMP_BUFFER);
        if (tmp == NULL) {
            return MEMORY_E;
        }

        XSecure_AesInitialize(&(aes->xilAes), &(aes->dma), aes->kup, (word32*)iv,
            aes->key_init);
        XSecure_AesEncryptData(&(aes->xilAes), tmp, in, sz);
        XMEMCPY(out, tmp, sz);
        XMEMCPY(authTag, tmp + sz, authTagSz);
        XFREE(tmp, aes->heap, DYNAMIC_TYPE_TMP_BUFFER);
    }

    /* handle completing tag with any additional data */
    if (authIn != NULL) {
        /* @TODO avoid hashing out again since Xilinx call already does */
        XMEMSET(initalCounter, 0, AES_BLOCK_SIZE);
        XMEMCPY(initalCounter, iv, ivSz);
        initalCounter[AES_BLOCK_SIZE - 1] = 1;
        GHASH(aes, authIn, authInSz, out, sz, authTag, authTagSz);
        wc_AesEncryptDirect(aes, scratch, initalCounter);
        xorbuf(authTag, scratch, authTagSz);
    }

    return 0;
}


int  wc_AesGcmDecrypt(Aes* aes, byte* out,
                                   const byte* in, word32 sz,
                                   const byte* iv, word32 ivSz,
                                   const byte* authTag, word32 authTagSz,
                                   const byte* authIn, word32 authInSz)
{
    byte* tag;
    byte buf[AES_GCM_AUTH_SZ];
    byte scratch[AES_BLOCK_SIZE];
    byte initalCounter[AES_BLOCK_SIZE];

    if (in == NULL || iv == NULL || authTag == NULL ||
            authTagSz < AES_GCM_AUTH_SZ) {
        return BAD_FUNC_ARG;
    }

    if (ivSz != AEAD_NONCE_SZ) {
        WOLFSSL_MSG("Expecting an IV size of 12");
        return BAD_FUNC_ARG;
    }

    /* account for additional data */
    if (authIn != NULL && authInSz > 0) {
        XMEMSET(initalCounter, 0, AES_BLOCK_SIZE);
        XMEMCPY(initalCounter, iv, ivSz);
        initalCounter[AES_BLOCK_SIZE - 1] = 1;
        tag = buf;
        GHASH(aes, NULL, 0, in, sz, tag, AES_GCM_AUTH_SZ);
        wc_AesEncryptDirect(aes, scratch, initalCounter);
        xorbuf(tag, scratch, AES_GCM_AUTH_SZ);
    }
    else {
        tag = authTag;
    }

    /* calls to hardened crypto */
    XSecure_AesInitialize(&(aes->xilAes), &(aes->dma), aes->kup,
                (word32*)iv, aes->key_init);
    XSecure_AesDecryptData(&(aes->xilAes), out, in, sz, tag);

    /* account for additional data */
    if (authIn != NULL && authInSz > 0) {
        GHASH(aes, authIn, authInSz, in, sz, tag, AES_GCM_AUTH_SZ);
        wc_AesEncryptDirect(aes, scratch, initalCounter);
        xorbuf(tag, scratch, AES_GCM_AUTH_SZ);
        if (ConstantCompare(authTag, tag, authTagSz) != 0) {
            return AES_GCM_AUTH_E;
        }
    }

    return 0;

}
#endif /* HAVE_AESGCM */

#endif
