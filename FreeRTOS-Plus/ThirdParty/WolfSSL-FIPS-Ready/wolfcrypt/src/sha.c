/* sha.c
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

#if !defined(NO_SHA)

#if defined(HAVE_FIPS) && \
	defined(HAVE_FIPS_VERSION) && (HAVE_FIPS_VERSION >= 2)

    /* set NO_WRAPPERS before headers, use direct internal f()s not wrappers */
    #define FIPS_NO_WRAPPERS

    #ifdef USE_WINDOWS_API
        #pragma code_seg(".fipsA$j")
        #pragma const_seg(".fipsB$j")
    #endif
#endif

#include <wolfssl/wolfcrypt/sha.h>
#include <wolfssl/wolfcrypt/error-crypt.h>
#include <wolfssl/wolfcrypt/hash.h>

#ifdef WOLF_CRYPTO_CB
    #include <wolfssl/wolfcrypt/cryptocb.h>
#endif

/* fips wrapper calls, user can call direct */
#if defined(HAVE_FIPS) && \
    (!defined(HAVE_FIPS_VERSION) || (HAVE_FIPS_VERSION < 2))

    int wc_InitSha(wc_Sha* sha)
    {
        if (sha == NULL) {
            return BAD_FUNC_ARG;
        }
        return InitSha_fips(sha);
    }
    int wc_InitSha_ex(wc_Sha* sha, void* heap, int devId)
    {
        (void)heap;
        (void)devId;
        if (sha == NULL) {
            return BAD_FUNC_ARG;
        }
        return InitSha_fips(sha);
    }

    int wc_ShaUpdate(wc_Sha* sha, const byte* data, word32 len)
    {
        if (sha == NULL || (data == NULL && len > 0)) {
            return BAD_FUNC_ARG;
        }
        return ShaUpdate_fips(sha, data, len);
    }

    int wc_ShaFinal(wc_Sha* sha, byte* out)
    {
        if (sha == NULL || out == NULL) {
            return BAD_FUNC_ARG;
        }
        return ShaFinal_fips(sha,out);
    }
    void wc_ShaFree(wc_Sha* sha)
    {
        (void)sha;
        /* Not supported in FIPS */
    }

#else /* else build without fips, or for FIPS v2 */


#if defined(WOLFSSL_TI_HASH)
    /* #include <wolfcrypt/src/port/ti/ti-hash.c> included by wc_port.c */

#else

#include <wolfssl/wolfcrypt/logging.h>
#ifdef NO_INLINE
    #include <wolfssl/wolfcrypt/misc.h>
#else
    #define WOLFSSL_MISC_INCLUDED
    #include <wolfcrypt/src/misc.c>
#endif


/* Hardware Acceleration */
#if defined(WOLFSSL_PIC32MZ_HASH)
    #include <wolfssl/wolfcrypt/port/pic32/pic32mz-crypt.h>

#elif defined(STM32_HASH)

    /* Supports CubeMX HAL or Standard Peripheral Library */
    int wc_InitSha_ex(wc_Sha* sha, void* heap, int devId)
    {
        if (sha == NULL) {
            return BAD_FUNC_ARG;
        }

        (void)devId;
        (void)heap;

        wc_Stm32_Hash_Init(&sha->stmCtx);

        return 0;
    }

    int wc_ShaUpdate(wc_Sha* sha, const byte* data, word32 len)
    {
        int ret;

        if (sha == NULL || (data == NULL && len > 0)) {
            return BAD_FUNC_ARG;
        }

        ret = wolfSSL_CryptHwMutexLock();
        if (ret == 0) {
            ret = wc_Stm32_Hash_Update(&sha->stmCtx, HASH_AlgoSelection_SHA1,
                data, len);
            wolfSSL_CryptHwMutexUnLock();
        }
        return ret;
    }

    int wc_ShaFinal(wc_Sha* sha, byte* hash)
    {
        int ret;

        if (sha == NULL || hash == NULL) {
            return BAD_FUNC_ARG;
        }

        ret = wolfSSL_CryptHwMutexLock();
        if (ret == 0) {
            ret = wc_Stm32_Hash_Final(&sha->stmCtx, HASH_AlgoSelection_SHA1,
                hash, WC_SHA_DIGEST_SIZE);
            wolfSSL_CryptHwMutexUnLock();
        }

        (void)wc_InitSha(sha);  /* reset state */

        return ret;
    }


#elif defined(FREESCALE_LTC_SHA)

    #include "fsl_ltc.h"
    int wc_InitSha_ex(wc_Sha* sha, void* heap, int devId)
    {
        if (sha == NULL) {
            return BAD_FUNC_ARG;
        }

        (void)devId;
        (void)heap;

        LTC_HASH_Init(LTC_BASE, &sha->ctx, kLTC_Sha1, NULL, 0);
        return 0;
    }

    int wc_ShaUpdate(wc_Sha* sha, const byte* data, word32 len)
    {
        LTC_HASH_Update(&sha->ctx, data, len);
        return 0;
    }

    int wc_ShaFinal(wc_Sha* sha, byte* hash)
    {
        uint32_t hashlen = WC_SHA_DIGEST_SIZE;
        LTC_HASH_Finish(&sha->ctx, hash, &hashlen);
        return wc_InitSha(sha);  /* reset state */
    }


#elif defined(FREESCALE_MMCAU_SHA)

    #ifdef FREESCALE_MMCAU_CLASSIC_SHA
        #include "cau_api.h"
    #else
        #include "fsl_mmcau.h"
    #endif

    #define USE_SHA_SOFTWARE_IMPL /* Only for API's, actual transform is here */

    #define XTRANSFORM(S,B)       Transform((S),(B))
    #define XTRANSFORM_LEN(S,B,L) Transform_Len((S),(B),(L))

    #ifndef WC_HASH_DATA_ALIGNMENT
        /* these hardware API's require 4 byte (word32) alignment */
        #define WC_HASH_DATA_ALIGNMENT 4
    #endif

    static int InitSha(wc_Sha* sha)
    {
        int ret = 0;
        ret = wolfSSL_CryptHwMutexLock();
        if (ret != 0) {
            return ret;
        }
    #ifdef FREESCALE_MMCAU_CLASSIC_SHA
        cau_sha1_initialize_output(sha->digest);
    #else
        MMCAU_SHA1_InitializeOutput((uint32_t*)sha->digest);
    #endif
        wolfSSL_CryptHwMutexUnLock();

        sha->buffLen = 0;
        sha->loLen   = 0;
        sha->hiLen   = 0;

        return ret;
    }

    static int Transform(wc_Sha* sha, const byte* data)
    {
        int ret = wolfSSL_CryptHwMutexLock();
        if (ret == 0) {
    #ifdef FREESCALE_MMCAU_CLASSIC_SHA
            cau_sha1_hash_n((byte*)data, 1, sha->digest);
    #else
            MMCAU_SHA1_HashN((byte*)data, 1, (uint32_t*)sha->digest);
    #endif
            wolfSSL_CryptHwMutexUnLock();
        }
        return ret;
    }

    static int Transform_Len(wc_Sha* sha, const byte* data, word32 len)
    {
        int ret = wolfSSL_CryptHwMutexLock();
        if (ret == 0) {
        #if defined(WC_HASH_DATA_ALIGNMENT) && WC_HASH_DATA_ALIGNMENT > 0
            if ((size_t)data % WC_HASH_DATA_ALIGNMENT) {
                /* data pointer is NOT aligned,
                 * so copy and perform one block at a time */
                byte* local = (byte*)sha->buffer;
                while (len >= WC_SHA_BLOCK_SIZE) {
                    XMEMCPY(local, data, WC_SHA_BLOCK_SIZE);
                #ifdef FREESCALE_MMCAU_CLASSIC_SHA
                    cau_sha1_hash_n(local, 1, sha->digest);
                #else
                    MMCAU_SHA1_HashN(local, 1, sha->digest);
                #endif
                    data += WC_SHA_BLOCK_SIZE;
                    len  -= WC_SHA_BLOCK_SIZE;
                }
            }
            else
        #endif
            {
    #ifdef FREESCALE_MMCAU_CLASSIC_SHA
            cau_sha1_hash_n((byte*)data, len/WC_SHA_BLOCK_SIZE, sha->digest);
    #else
            MMCAU_SHA1_HashN((byte*)data, len/WC_SHA_BLOCK_SIZE,
                (uint32_t*)sha->digest);
    #endif
            }
            wolfSSL_CryptHwMutexUnLock();
        }
        return ret;
    }

#elif defined(WOLFSSL_IMX6_CAAM) && !defined(NO_IMX6_CAAM_HASH)
    /* wolfcrypt/src/port/caam/caam_sha.c */

#elif defined(WOLFSSL_ESP32WROOM32_CRYPT) && \
     !defined(NO_WOLFSSL_ESP32WROOM32_CRYPT_HASH)

    #include "wolfssl/wolfcrypt/port/Espressif/esp32-crypt.h"

    #define USE_SHA_SOFTWARE_IMPL

    static int InitSha(wc_Sha* sha)
    {
        int ret = 0;

        sha->digest[0] = 0x67452301L;
        sha->digest[1] = 0xEFCDAB89L;
        sha->digest[2] = 0x98BADCFEL;
        sha->digest[3] = 0x10325476L;
        sha->digest[4] = 0xC3D2E1F0L;

        sha->buffLen = 0;
        sha->loLen   = 0;
        sha->hiLen   = 0;

        /* always start firstblock = 1 when using hw engine */
        sha->ctx.isfirstblock = 1;
        sha->ctx.sha_type = SHA1;
        if(sha->ctx.mode == ESP32_SHA_HW){
            /* release hw engine */
            esp_sha_hw_unlock();
        }
        /* always set mode as INIT
        *  whether using HW or SW is determined at first call of update()
        */
        sha->ctx.mode = ESP32_SHA_INIT;

        return ret;
    }

#elif defined(WOLFSSL_RENESAS_TSIP_CRYPT) && \
    !defined(NO_WOLFSSL_RENESAS_TSIP_CRYPT_HASH)

    /* implemented in wolfcrypt/src/port/Renesas/renesas_tsip_sha.c */

#else
    /* Software implementation */
    #define USE_SHA_SOFTWARE_IMPL

    static int InitSha(wc_Sha* sha)
    {
        int ret = 0;

        sha->digest[0] = 0x67452301L;
        sha->digest[1] = 0xEFCDAB89L;
        sha->digest[2] = 0x98BADCFEL;
        sha->digest[3] = 0x10325476L;
        sha->digest[4] = 0xC3D2E1F0L;

        sha->buffLen = 0;
        sha->loLen   = 0;
        sha->hiLen   = 0;
    #if defined(WOLFSSL_HASH_FLAGS) || defined(WOLF_CRYPTO_CB)
        sha->flags = 0;
    #endif

        return ret;
    }
#endif /* End Hardware Acceleration */

/* Software implementation */
#ifdef USE_SHA_SOFTWARE_IMPL

static WC_INLINE void AddLength(wc_Sha* sha, word32 len)
{
    word32 tmp = sha->loLen;
    if ((sha->loLen += len) < tmp)
        sha->hiLen++;                       /* carry low to high */
}

/* Check if custom wc_Sha transform is used */
#ifndef XTRANSFORM
    #define XTRANSFORM(S,B)   Transform((S),(B))

    #define blk0(i) (W[i] = *((word32*)&data[i*sizeof(word32)]))
    #define blk1(i) (W[(i)&15] = \
        rotlFixed(W[((i)+13)&15]^W[((i)+8)&15]^W[((i)+2)&15]^W[(i)&15],1))

    #define f1(x,y,z) ((z)^((x) &((y)^(z))))
    #define f2(x,y,z) ((x)^(y)^(z))
    #define f3(x,y,z) (((x)&(y))|((z)&((x)|(y))))
    #define f4(x,y,z) ((x)^(y)^(z))

    #ifdef WOLFSSL_NUCLEUS_1_2
        /* nucleus.h also defines R1-R4 */
        #undef R1
        #undef R2
        #undef R3
        #undef R4
    #endif

    /* (R0+R1), R2, R3, R4 are the different operations used in SHA1 */
    #define R0(v,w,x,y,z,i) (z)+= f1((w),(x),(y)) + blk0((i)) + 0x5A827999+ \
        rotlFixed((v),5); (w) = rotlFixed((w),30);
    #define R1(v,w,x,y,z,i) (z)+= f1((w),(x),(y)) + blk1((i)) + 0x5A827999+ \
        rotlFixed((v),5); (w) = rotlFixed((w),30);
    #define R2(v,w,x,y,z,i) (z)+= f2((w),(x),(y)) + blk1((i)) + 0x6ED9EBA1+ \
        rotlFixed((v),5); (w) = rotlFixed((w),30);
    #define R3(v,w,x,y,z,i) (z)+= f3((w),(x),(y)) + blk1((i)) + 0x8F1BBCDC+ \
        rotlFixed((v),5); (w) = rotlFixed((w),30);
    #define R4(v,w,x,y,z,i) (z)+= f4((w),(x),(y)) + blk1((i)) + 0xCA62C1D6+ \
        rotlFixed((v),5); (w) = rotlFixed((w),30);

    static int Transform(wc_Sha* sha, const byte* data)
    {
        word32 W[WC_SHA_BLOCK_SIZE / sizeof(word32)];

        /* Copy context->state[] to working vars */
        word32 a = sha->digest[0];
        word32 b = sha->digest[1];
        word32 c = sha->digest[2];
        word32 d = sha->digest[3];
        word32 e = sha->digest[4];

    #ifdef USE_SLOW_SHA
        word32 t, i;

        for (i = 0; i < 16; i++) {
            R0(a, b, c, d, e, i);
            t = e; e = d; d = c; c = b; b = a; a = t;
        }

        for (; i < 20; i++) {
            R1(a, b, c, d, e, i);
            t = e; e = d; d = c; c = b; b = a; a = t;
        }

        for (; i < 40; i++) {
            R2(a, b, c, d, e, i);
            t = e; e = d; d = c; c = b; b = a; a = t;
        }

        for (; i < 60; i++) {
            R3(a, b, c, d, e, i);
            t = e; e = d; d = c; c = b; b = a; a = t;
        }

        for (; i < 80; i++) {
            R4(a, b, c, d, e, i);
            t = e; e = d; d = c; c = b; b = a; a = t;
        }
    #else
        /* nearly 1 K bigger in code size but 25% faster */
        /* 4 rounds of 20 operations each. Loop unrolled. */
        R0(a,b,c,d,e, 0); R0(e,a,b,c,d, 1); R0(d,e,a,b,c, 2); R0(c,d,e,a,b, 3);
        R0(b,c,d,e,a, 4); R0(a,b,c,d,e, 5); R0(e,a,b,c,d, 6); R0(d,e,a,b,c, 7);
        R0(c,d,e,a,b, 8); R0(b,c,d,e,a, 9); R0(a,b,c,d,e,10); R0(e,a,b,c,d,11);
        R0(d,e,a,b,c,12); R0(c,d,e,a,b,13); R0(b,c,d,e,a,14); R0(a,b,c,d,e,15);

        R1(e,a,b,c,d,16); R1(d,e,a,b,c,17); R1(c,d,e,a,b,18); R1(b,c,d,e,a,19);

        R2(a,b,c,d,e,20); R2(e,a,b,c,d,21); R2(d,e,a,b,c,22); R2(c,d,e,a,b,23);
        R2(b,c,d,e,a,24); R2(a,b,c,d,e,25); R2(e,a,b,c,d,26); R2(d,e,a,b,c,27);
        R2(c,d,e,a,b,28); R2(b,c,d,e,a,29); R2(a,b,c,d,e,30); R2(e,a,b,c,d,31);
        R2(d,e,a,b,c,32); R2(c,d,e,a,b,33); R2(b,c,d,e,a,34); R2(a,b,c,d,e,35);
        R2(e,a,b,c,d,36); R2(d,e,a,b,c,37); R2(c,d,e,a,b,38); R2(b,c,d,e,a,39);

        R3(a,b,c,d,e,40); R3(e,a,b,c,d,41); R3(d,e,a,b,c,42); R3(c,d,e,a,b,43);
        R3(b,c,d,e,a,44); R3(a,b,c,d,e,45); R3(e,a,b,c,d,46); R3(d,e,a,b,c,47);
        R3(c,d,e,a,b,48); R3(b,c,d,e,a,49); R3(a,b,c,d,e,50); R3(e,a,b,c,d,51);
        R3(d,e,a,b,c,52); R3(c,d,e,a,b,53); R3(b,c,d,e,a,54); R3(a,b,c,d,e,55);
        R3(e,a,b,c,d,56); R3(d,e,a,b,c,57); R3(c,d,e,a,b,58); R3(b,c,d,e,a,59);

        R4(a,b,c,d,e,60); R4(e,a,b,c,d,61); R4(d,e,a,b,c,62); R4(c,d,e,a,b,63);
        R4(b,c,d,e,a,64); R4(a,b,c,d,e,65); R4(e,a,b,c,d,66); R4(d,e,a,b,c,67);
        R4(c,d,e,a,b,68); R4(b,c,d,e,a,69); R4(a,b,c,d,e,70); R4(e,a,b,c,d,71);
        R4(d,e,a,b,c,72); R4(c,d,e,a,b,73); R4(b,c,d,e,a,74); R4(a,b,c,d,e,75);
        R4(e,a,b,c,d,76); R4(d,e,a,b,c,77); R4(c,d,e,a,b,78); R4(b,c,d,e,a,79);
    #endif

        /* Add the working vars back into digest state[] */
        sha->digest[0] += a;
        sha->digest[1] += b;
        sha->digest[2] += c;
        sha->digest[3] += d;
        sha->digest[4] += e;

        (void)data; /* Not used */

        return 0;
    }
#endif /* !USE_CUSTOM_SHA_TRANSFORM */


int wc_InitSha_ex(wc_Sha* sha, void* heap, int devId)
{
    int ret = 0;

    if (sha == NULL)
        return BAD_FUNC_ARG;

    sha->heap = heap;
#ifdef WOLF_CRYPTO_CB
    sha->devId = devId;
#endif

#if defined(WOLFSSL_ESP32WROOM32_CRYPT) && \
    !defined(NO_WOLFSSL_ESP32WROOM32_CRYPT_HASH)
    sha->ctx.mode = ESP32_SHA_INIT;
    sha->ctx.isfirstblock = 1;
#endif
    ret = InitSha(sha);
    if (ret != 0)
        return ret;

#if defined(WOLFSSL_ASYNC_CRYPT) && defined(WC_ASYNC_ENABLE_SHA)
    ret = wolfAsync_DevCtxInit(&sha->asyncDev, WOLFSSL_ASYNC_MARKER_SHA,
                                                            sha->heap, devId);
#else
    (void)devId;
#endif /* WOLFSSL_ASYNC_CRYPT */

    return ret;
}

/* do block size increments/updates */
int wc_ShaUpdate(wc_Sha* sha, const byte* data, word32 len)
{
    int ret = 0;
    word32 blocksLen;
    byte* local;

    if (sha == NULL || (data == NULL && len > 0)) {
        return BAD_FUNC_ARG;
    }

#ifdef WOLF_CRYPTO_CB
    if (sha->devId != INVALID_DEVID) {
        ret = wc_CryptoCb_ShaHash(sha, data, len, NULL);
        if (ret != CRYPTOCB_UNAVAILABLE)
            return ret;
        ret = 0; /* reset ret */
        /* fall-through when unavailable */
    }
#endif
#if defined(WOLFSSL_ASYNC_CRYPT) && defined(WC_ASYNC_ENABLE_SHA)
    if (sha->asyncDev.marker == WOLFSSL_ASYNC_MARKER_SHA) {
    #if defined(HAVE_INTEL_QA)
        return IntelQaSymSha(&sha->asyncDev, NULL, data, len);
    #endif
    }
#endif /* WOLFSSL_ASYNC_CRYPT */

    /* check that internal buffLen is valid */
    if (sha->buffLen >= WC_SHA_BLOCK_SIZE)
        return BUFFER_E;

    if (data == NULL && len == 0) {
        /* valid, but do nothing */
        return 0;
    }

    /* add length for final */
    AddLength(sha, len);

    local = (byte*)sha->buffer;

    /* process any remainder from previous operation */
    if (sha->buffLen > 0) {
        blocksLen = min(len, WC_SHA_BLOCK_SIZE - sha->buffLen);
        XMEMCPY(&local[sha->buffLen], data, blocksLen);

        sha->buffLen += blocksLen;
        data         += blocksLen;
        len          -= blocksLen;

        if (sha->buffLen == WC_SHA_BLOCK_SIZE) {
        #if defined(LITTLE_ENDIAN_ORDER) && !defined(FREESCALE_MMCAU_SHA)
            ByteReverseWords(sha->buffer, sha->buffer, WC_SHA_BLOCK_SIZE);
        #endif

        #if defined(WOLFSSL_ESP32WROOM32_CRYPT) && \
            !defined(NO_WOLFSSL_ESP32WROOM32_CRYPT_HASH)
            if (sha->ctx.mode == ESP32_SHA_INIT) {
                esp_sha_try_hw_lock(&sha->ctx);
            }
            if (sha->ctx.mode == ESP32_SHA_SW) {
                ret = XTRANSFORM(sha, (const byte*)local);
            } else {
                esp_sha_process(sha, (const byte*)local);
            }
        #else
            ret = XTRANSFORM(sha, (const byte*)local);
        #endif
            if (ret != 0)
                return ret;

            sha->buffLen = 0;
        }
    }

    /* process blocks */
#ifdef XTRANSFORM_LEN
    /* get number of blocks */
    /* 64-1 = 0x3F (~ Inverted = 0xFFFFFFC0) */
    /* len (masked by 0xFFFFFFC0) returns block aligned length */
    blocksLen = len & ~(WC_SHA_BLOCK_SIZE-1);
    if (blocksLen > 0) {
        /* Byte reversal performed in function if required. */
        XTRANSFORM_LEN(sha, data, blocksLen);
        data += blocksLen;
        len  -= blocksLen;
    }
#else
    while (len >= WC_SHA_BLOCK_SIZE) {
        word32* local32 = sha->buffer;
        /* optimization to avoid memcpy if data pointer is properly aligned */
        /* Little Endian requires byte swap, so can't use data directly */
    #if defined(WC_HASH_DATA_ALIGNMENT) && !defined(LITTLE_ENDIAN_ORDER)
        if (((size_t)data % WC_HASH_DATA_ALIGNMENT) == 0) {
            local32 = (word32*)data;
        }
        else
    #endif
        {
            XMEMCPY(local32, data, WC_SHA_BLOCK_SIZE);
        }

        data += WC_SHA_BLOCK_SIZE;
        len  -= WC_SHA_BLOCK_SIZE;

    #if defined(LITTLE_ENDIAN_ORDER) && !defined(FREESCALE_MMCAU_SHA)
        ByteReverseWords(local32, local32, WC_SHA_BLOCK_SIZE);
    #endif

    #if defined(WOLFSSL_ESP32WROOM32_CRYPT) && \
        !defined(NO_WOLFSSL_ESP32WROOM32_CRYPT_HASH)
        if (sha->ctx.mode == ESP32_SHA_INIT){
            esp_sha_try_hw_lock(&sha->ctx);
        }
        if (sha->ctx.mode == ESP32_SHA_SW){
            ret = XTRANSFORM(sha, (const byte*)local32);
        } else {
            esp_sha_process(sha, (const byte*)local32);
        }
    #else
        ret = XTRANSFORM(sha, (const byte*)local32);
    #endif
    }
#endif /* XTRANSFORM_LEN */

    /* save remainder */
    if (len > 0) {
        XMEMCPY(local, data, len);
        sha->buffLen = len;
    }

    return ret;
}

int wc_ShaFinalRaw(wc_Sha* sha, byte* hash)
{
#ifdef LITTLE_ENDIAN_ORDER
    word32 digest[WC_SHA_DIGEST_SIZE / sizeof(word32)];
#endif

    if (sha == NULL || hash == NULL) {
        return BAD_FUNC_ARG;
    }

#ifdef LITTLE_ENDIAN_ORDER
    ByteReverseWords((word32*)digest, (word32*)sha->digest, WC_SHA_DIGEST_SIZE);
    XMEMCPY(hash, digest, WC_SHA_DIGEST_SIZE);
#else
    XMEMCPY(hash, sha->digest, WC_SHA_DIGEST_SIZE);
#endif

    return 0;
}

int wc_ShaFinal(wc_Sha* sha, byte* hash)
{
    int ret;
    byte* local;

    if (sha == NULL || hash == NULL) {
        return BAD_FUNC_ARG;
    }

    local = (byte*)sha->buffer;

#ifdef WOLF_CRYPTO_CB
    if (sha->devId != INVALID_DEVID) {
        ret = wc_CryptoCb_ShaHash(sha, NULL, 0, hash);
        if (ret != CRYPTOCB_UNAVAILABLE)
            return ret;
        ret = 0; /* reset ret */
        /* fall-through when unavailable */
    }
#endif
#if defined(WOLFSSL_ASYNC_CRYPT) && defined(WC_ASYNC_ENABLE_SHA)
    if (sha->asyncDev.marker == WOLFSSL_ASYNC_MARKER_SHA) {
    #if defined(HAVE_INTEL_QA)
        return IntelQaSymSha(&sha->asyncDev, hash, NULL, WC_SHA_DIGEST_SIZE);
    #endif
    }
#endif /* WOLFSSL_ASYNC_CRYPT */

    local[sha->buffLen++] = 0x80;  /* add 1 */

    /* pad with zeros */
    if (sha->buffLen > WC_SHA_PAD_SIZE) {
        XMEMSET(&local[sha->buffLen], 0, WC_SHA_BLOCK_SIZE - sha->buffLen);
        sha->buffLen += WC_SHA_BLOCK_SIZE - sha->buffLen;

    #if defined(LITTLE_ENDIAN_ORDER) && !defined(FREESCALE_MMCAU_SHA)
        ByteReverseWords(sha->buffer, sha->buffer, WC_SHA_BLOCK_SIZE);
    #endif

    #if defined(WOLFSSL_ESP32WROOM32_CRYPT) && \
        !defined(NO_WOLFSSL_ESP32WROOM32_CRYPT_HASH)
        if (sha->ctx.mode == ESP32_SHA_INIT) {
            esp_sha_try_hw_lock(&sha->ctx);
        }
        if (sha->ctx.mode == ESP32_SHA_SW) {
            ret = XTRANSFORM(sha, (const byte*)local);
        } else {
            ret = esp_sha_process(sha, (const byte*)local);
        }
    #else
        ret = XTRANSFORM(sha, (const byte*)local);
    #endif
        if (ret != 0)
            return ret;

        sha->buffLen = 0;
    }
    XMEMSET(&local[sha->buffLen], 0, WC_SHA_PAD_SIZE - sha->buffLen);

#if defined(LITTLE_ENDIAN_ORDER) && !defined(FREESCALE_MMCAU_SHA)
    ByteReverseWords(sha->buffer, sha->buffer, WC_SHA_BLOCK_SIZE);
#endif

    /* store lengths */
    /* put lengths in bits */
    sha->hiLen = (sha->loLen >> (8*sizeof(sha->loLen) - 3)) + (sha->hiLen << 3);
    sha->loLen = sha->loLen << 3;

    /* ! length ordering dependent on digest endian type ! */
    XMEMCPY(&local[WC_SHA_PAD_SIZE], &sha->hiLen, sizeof(word32));
    XMEMCPY(&local[WC_SHA_PAD_SIZE + sizeof(word32)], &sha->loLen, sizeof(word32));

#if defined(FREESCALE_MMCAU_SHA)
    /* Kinetis requires only these bytes reversed */
    ByteReverseWords(&sha->buffer[WC_SHA_PAD_SIZE/sizeof(word32)],
                     &sha->buffer[WC_SHA_PAD_SIZE/sizeof(word32)],
                     2 * sizeof(word32));
#endif

#if defined(WOLFSSL_ESP32WROOM32_CRYPT) && \
    !defined(NO_WOLFSSL_ESP32WROOM32_CRYPT_HASH)
    if (sha->ctx.mode == ESP32_SHA_INIT) {
        esp_sha_try_hw_lock(&sha->ctx);
    }
    if (sha->ctx.mode == ESP32_SHA_SW) {
        ret = XTRANSFORM(sha, (const byte*)local);
    } else {
        ret = esp_sha_digest_process(sha, 1);
    }
#else
    ret = XTRANSFORM(sha, (const byte*)local);
#endif

#ifdef LITTLE_ENDIAN_ORDER
    ByteReverseWords(sha->digest, sha->digest, WC_SHA_DIGEST_SIZE);
#endif

    XMEMCPY(hash, sha->digest, WC_SHA_DIGEST_SIZE);

    (void)InitSha(sha); /* reset state */

    return ret;
}

#endif /* USE_SHA_SOFTWARE_IMPL */


int wc_InitSha(wc_Sha* sha)
{
    return wc_InitSha_ex(sha, NULL, INVALID_DEVID);
}

void wc_ShaFree(wc_Sha* sha)
{
    if (sha == NULL)
        return;

#if defined(WOLFSSL_ASYNC_CRYPT) && defined(WC_ASYNC_ENABLE_SHA)
    wolfAsync_DevCtxFree(&sha->asyncDev, WOLFSSL_ASYNC_MARKER_SHA);
#endif /* WOLFSSL_ASYNC_CRYPT */

#ifdef WOLFSSL_PIC32MZ_HASH
    wc_ShaPic32Free(sha);
#endif
#if (defined(WOLFSSL_RENESAS_TSIP_CRYPT) && \
    !defined(NO_WOLFSSL_RENESAS_TSIP_CRYPT_HASH))
    if (sha->msg != NULL) {
        XFREE(sha->msg, sha->heap, DYNAMIC_TYPE_TMP_BUFFER);
        sha->msg = NULL;
    }
#endif
}

#endif /* !WOLFSSL_TI_HASH */
#endif /* HAVE_FIPS */

#ifndef WOLFSSL_TI_HASH
#if !defined(WOLFSSL_RENESAS_TSIP_CRYPT) || \
    defined(NO_WOLFSSL_RENESAS_TSIP_CRYPT_HASH)
int wc_ShaGetHash(wc_Sha* sha, byte* hash)
{
    int ret;
    wc_Sha tmpSha;

    if (sha == NULL || hash == NULL)
        return BAD_FUNC_ARG;

#if defined(WOLFSSL_ESP32WROOM32_CRYPT) && \
    !defined(NO_WOLFSSL_ESP32WROOM32_CRYPT_HASH)
    if(sha->ctx.mode == ESP32_SHA_INIT){
        esp_sha_try_hw_lock(&sha->ctx);
    }
    if(sha->ctx.mode != ESP32_SHA_SW)
        esp_sha_digest_process(sha, 0);
#endif

    ret = wc_ShaCopy(sha, &tmpSha);
    if (ret == 0) {
       ret = wc_ShaFinal(&tmpSha, hash);
#if defined(WOLFSSL_ESP32WROOM32_CRYPT) && \
    !defined(NO_WOLFSSL_ESP32WROOM32_CRYPT_HASH)
        sha->ctx.mode = ESP32_SHA_SW;
#endif


    }
    return ret;
}

int wc_ShaCopy(wc_Sha* src, wc_Sha* dst)
{
    int ret = 0;

    if (src == NULL || dst == NULL)
        return BAD_FUNC_ARG;

    XMEMCPY(dst, src, sizeof(wc_Sha));

#ifdef WOLFSSL_ASYNC_CRYPT
    ret = wolfAsync_DevCopy(&src->asyncDev, &dst->asyncDev);
#endif
#ifdef WOLFSSL_PIC32MZ_HASH
    ret = wc_Pic32HashCopy(&src->cache, &dst->cache);
#endif
#if defined(WOLFSSL_ESP32WROOM32_CRYPT) && \
    !defined(NO_WOLFSSL_ESP32WROOM32_CRYPT_HASH)
     dst->ctx.mode = src->ctx.mode;
     dst->ctx.isfirstblock = src->ctx.isfirstblock;
     dst->ctx.sha_type = src->ctx.sha_type;
#endif
#if defined(WOLFSSL_HASH_FLAGS) || defined(WOLF_CRYPTO_CB)
     dst->flags |= WC_HASH_FLAG_ISCOPY;
#endif
    return ret;
}
#endif /* defined(WOLFSSL_RENESAS_TSIP_CRYPT) ... */
#endif /* !WOLFSSL_TI_HASH */


#if defined(WOLFSSL_HASH_FLAGS) || defined(WOLF_CRYPTO_CB)
int wc_ShaSetFlags(wc_Sha* sha, word32 flags)
{
    if (sha) {
        sha->flags = flags;
    }
    return 0;
}
int wc_ShaGetFlags(wc_Sha* sha, word32* flags)
{
    if (sha && flags) {
        *flags = sha->flags;
    }
    return 0;
}
#endif

#endif /* !NO_SHA */
