/* armv8-aes.c
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
 * There are two versions one for 64 (Aarch64)  and one for 32 bit (Aarch32).
 * If changing one check the other.
 */


#ifdef HAVE_CONFIG_H
    #include <config.h>
#endif

#include <wolfssl/wolfcrypt/settings.h>

#if !defined(NO_AES) && defined(WOLFSSL_ARMASM)

#include <wolfssl/wolfcrypt/aes.h>
#include <wolfssl/wolfcrypt/error-crypt.h>
#include <wolfssl/wolfcrypt/logging.h>
#ifdef NO_INLINE
    #include <wolfssl/wolfcrypt/misc.h>
#else
    #define WOLFSSL_MISC_INCLUDED
    #include <wolfcrypt/src/misc.c>
#endif

#ifdef _MSC_VER
    /* 4127 warning constant while(1)  */
    #pragma warning(disable: 4127)
#endif


static const byte rcon[] = {
    0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40, 0x80,0x1B, 0x36
    /* for 128-bit blocks, Rijndael never uses more than 10 rcon values */
};

/* get table value from hardware */
#ifdef __aarch64__
    #define SBOX(x)                      \
        do {                             \
            __asm__ volatile (           \
                "DUP v1.4s, %w[in]  \n"  \
                "MOVI v0.16b, #0     \n" \
                "AESE v0.16b, v1.16b \n" \
                "UMOV %w[out], v0.s[0] \n" \
                : [out] "=r"((x))        \
                : [in] "r" ((x))         \
                : "cc", "memory", "v0", "v1"\
            ); \
        } while(0)

    #define IMIX(x) \
        do {        \
            __asm__ volatile (             \
                "LD1 {v0.16b}, [%[in]] \n" \
                "AESIMC v0.16b, v0.16b \n" \
                "ST1 {v0.16b}, [%[out]]\n" \
                : [out] "=r" ((x))         \
                : [in] "0" ((x))           \
                : "cc", "memory", "v0"     \
            );                             \
        } while(0)
#else /* if not defined __aarch64__ then use 32 bit version */
    #define SBOX(x)                      \
        do {                             \
            __asm__ volatile (           \
                "VDUP.32 q1, %[in]   \n" \
                "VMOV.i32 q0, #0     \n" \
                "AESE.8 q0, q1      \n" \
                "VMOV.32 %[out], d0[0] \n" \
                : [out] "=r"((x))        \
                : [in] "r" ((x))         \
                : "cc", "memory", "q0", "q1"\
            ); \
        } while(0)

    #define IMIX(x) \
        do {        \
            __asm__ volatile (           \
                "VLD1.32 {q0}, [%[in]] \n" \
                "AESIMC.8 q0, q0    \n" \
                "VST1.32 {q0}, [%[out]] \n" \
                : [out] "=r" ((x))       \
                : [in] "0" ((x))         \
                : "cc", "memory", "q0"   \
            );                           \
        } while(0)
#endif /* aarch64 */


#ifdef HAVE_AESGCM

static WC_INLINE void IncrementGcmCounter(byte* inOutCtr)
{
    int i;

    /* in network byte order so start at end and work back */
    for (i = AES_BLOCK_SIZE - 1; i >= AES_BLOCK_SIZE - CTR_SZ; i--) {
        if (++inOutCtr[i])  /* we're done unless we overflow */
            return;
    }
}


static WC_INLINE void FlattenSzInBits(byte* buf, word32 sz)
{
    /* Multiply the sz by 8 */
    word32 szHi = (sz >> (8*sizeof(sz) - 3));
    sz <<= 3;

    /* copy over the words of the sz into the destination buffer */
    buf[0] = (szHi >> 24) & 0xff;
    buf[1] = (szHi >> 16) & 0xff;
    buf[2] = (szHi >>  8) & 0xff;
    buf[3] = szHi & 0xff;
    buf[4] = (sz >> 24) & 0xff;
    buf[5] = (sz >> 16) & 0xff;
    buf[6] = (sz >>  8) & 0xff;
    buf[7] = sz & 0xff;
}

#endif /* HAVE_AESGCM */

/* Similar to wolfSSL software implementation of expanding the AES key.
 * Changed out the locations of where table look ups where made to
 * use hardware instruction. Also altered decryption key to match. */
int wc_AesSetKey(Aes* aes, const byte* userKey, word32 keylen,
            const byte* iv, int dir)
{
    word32 temp;
    word32 *rk;
    unsigned int i = 0;

#if defined(AES_MAX_KEY_SIZE)
    const word32 max_key_len = (AES_MAX_KEY_SIZE / 8);
#endif

    if (!((keylen == 16) || (keylen == 24) || (keylen == 32)) ||
           aes == NULL || userKey == NULL)
        return BAD_FUNC_ARG;

    rk = aes->key;
#if defined(AES_MAX_KEY_SIZE)
    /* Check key length */
    if (keylen > max_key_len) {
        return BAD_FUNC_ARG;
    }
#endif

    #ifdef WOLFSSL_AES_COUNTER
        aes->left = 0;
    #endif /* WOLFSSL_AES_COUNTER */

    aes->rounds = keylen/4 + 6;
    XMEMCPY(rk, userKey, keylen);

    switch(keylen)
    {
#if defined(AES_MAX_KEY_SIZE) && AES_MAX_KEY_SIZE >= 128 && \
        defined(WOLFSSL_AES_128)
    case 16:
        while (1)
        {
            temp  = rk[3];
            SBOX(temp);
            temp = rotrFixed(temp, 8);
            rk[4] = rk[0] ^ temp ^ rcon[i];
            rk[5] = rk[4] ^ rk[1];
            rk[6] = rk[5] ^ rk[2];
            rk[7] = rk[6] ^ rk[3];
            if (++i == 10)
                break;
            rk += 4;
        }
        break;
#endif /* 128 */

#if defined(AES_MAX_KEY_SIZE) && AES_MAX_KEY_SIZE >= 192 && \
        defined(WOLFSSL_AES_192)
    case 24:
        /* for (;;) here triggers a bug in VC60 SP4 w/ Pro Pack */
        while (1)
        {
            temp  = rk[5];
            SBOX(temp);
            temp = rotrFixed(temp, 8);
            rk[ 6] = rk[ 0] ^ temp ^ rcon[i];
            rk[ 7] = rk[ 1] ^ rk[ 6];
            rk[ 8] = rk[ 2] ^ rk[ 7];
            rk[ 9] = rk[ 3] ^ rk[ 8];
            if (++i == 8)
                break;
            rk[10] = rk[ 4] ^ rk[ 9];
            rk[11] = rk[ 5] ^ rk[10];
            rk += 6;
        }
        break;
#endif /* 192 */

#if defined(AES_MAX_KEY_SIZE) && AES_MAX_KEY_SIZE >= 256 && \
        defined(WOLFSSL_AES_256)
    case 32:
        while (1)
        {
            temp  = rk[7];
            SBOX(temp);
            temp = rotrFixed(temp, 8);
            rk[8] = rk[0] ^ temp ^ rcon[i];
            rk[ 9] = rk[ 1] ^ rk[ 8];
            rk[10] = rk[ 2] ^ rk[ 9];
            rk[11] = rk[ 3] ^ rk[10];
            if (++i == 7)
                break;
            temp  = rk[11];
            SBOX(temp);
            rk[12] = rk[ 4] ^ temp;
            rk[13] = rk[ 5] ^ rk[12];
            rk[14] = rk[ 6] ^ rk[13];
            rk[15] = rk[ 7] ^ rk[14];

            rk += 8;
        }
        break;
#endif /* 256 */

    default:
        return BAD_FUNC_ARG;
    }

    if (dir == AES_DECRYPTION)
    {
#ifdef HAVE_AES_DECRYPT
        unsigned int j;
        rk = aes->key;

        /* invert the order of the round keys: */
        for (i = 0, j = 4* aes->rounds; i < j; i += 4, j -= 4) {
            temp = rk[i    ]; rk[i    ] = rk[j    ]; rk[j    ] = temp;
            temp = rk[i + 1]; rk[i + 1] = rk[j + 1]; rk[j + 1] = temp;
            temp = rk[i + 2]; rk[i + 2] = rk[j + 2]; rk[j + 2] = temp;
            temp = rk[i + 3]; rk[i + 3] = rk[j + 3]; rk[j + 3] = temp;
        }
        /* apply the inverse MixColumn transform to all round keys but the
           first and the last: */
        for (i = 1; i < aes->rounds; i++) {
            rk += 4;
            IMIX(rk);
        }
#else
    WOLFSSL_MSG("AES Decryption not compiled in");
    return BAD_FUNC_ARG;
#endif /* HAVE_AES_DECRYPT */
    }

    return wc_AesSetIV(aes, iv);
}

#if defined(WOLFSSL_AES_DIRECT) || defined(WOLFSSL_AES_COUNTER)
    int wc_AesSetKeyDirect(Aes* aes, const byte* userKey, word32 keylen,
                        const byte* iv, int dir)
    {
        return wc_AesSetKey(aes, userKey, keylen, iv, dir);
    }
#endif

/* wc_AesSetIV is shared between software and hardware */
int wc_AesSetIV(Aes* aes, const byte* iv)
{
    if (aes == NULL)
        return BAD_FUNC_ARG;

    if (iv)
        XMEMCPY(aes->reg, iv, AES_BLOCK_SIZE);
    else
        XMEMSET(aes->reg,  0, AES_BLOCK_SIZE);

    return 0;
}


#ifdef __aarch64__
/* AES CCM/GCM use encrypt direct but not decrypt */
#if defined(HAVE_AESCCM) || defined(HAVE_AESGCM) || \
    defined(WOLFSSL_AES_DIRECT) || defined(WOLFSSL_AES_COUNTER)
    static int wc_AesEncrypt(Aes* aes, const byte* inBlock, byte* outBlock)
    {
            word32* keyPt = aes->key;

            /*
              AESE exor's input with round key
                   shift rows of exor'ed result
                   sub bytes for shifted rows
             */

            __asm__ __volatile__ (
                "LD1 {v0.16b}, [%[CtrIn]] \n"
                "LD1 {v1.2d-v4.2d}, [%[Key]], #64  \n"

                "AESE v0.16b, v1.16b  \n"
                "AESMC v0.16b, v0.16b \n"
                "AESE v0.16b, v2.16b  \n"
                "AESMC v0.16b, v0.16b \n"
                "AESE v0.16b, v3.16b  \n"
                "AESMC v0.16b, v0.16b \n"
                "AESE v0.16b, v4.16b  \n"
                "AESMC v0.16b, v0.16b \n"

                "LD1 {v1.2d-v4.2d}, [%[Key]], #64  \n"
                "AESE v0.16b, v1.16b  \n"
                "AESMC v0.16b, v0.16b \n"
                "AESE v0.16b, v2.16b  \n"
                "AESMC v0.16b, v0.16b \n"
                "AESE v0.16b, v3.16b  \n"
                "AESMC v0.16b, v0.16b \n"
                "AESE v0.16b, v4.16b  \n"
                "AESMC v0.16b, v0.16b \n"

                "LD1 {v1.2d-v2.2d}, [%[Key]], #32  \n"
                "AESE v0.16b, v1.16b  \n"
                "AESMC v0.16b, v0.16b \n"
                "AESE v0.16b, v2.16b  \n"

                "#subtract rounds done so far and see if should continue\n"
                "MOV w12, %w[R]    \n"
                "SUB w12, w12, #10 \n"
                "CBZ w12, 1f       \n"
                "LD1 {v1.2d-v2.2d}, [%[Key]], #32  \n"
                "AESMC v0.16b, v0.16b \n"
                "AESE v0.16b, v1.16b  \n"
                "AESMC v0.16b, v0.16b \n"
                "AESE v0.16b, v2.16b  \n"

                "SUB w12, w12, #2 \n"
                "CBZ w12, 1f      \n"
                "LD1 {v1.2d-v2.2d}, [%[Key]], #32  \n"
                "AESMC v0.16b, v0.16b \n"
                "AESE v0.16b, v1.16b  \n"
                "AESMC v0.16b, v0.16b \n"
                "AESE v0.16b, v2.16b  \n"

                "#Final AddRoundKey then store result \n"
                "1: \n"
                "LD1 {v1.2d}, [%[Key]], #16 \n"
                "EOR v0.16b, v0.16b, v1.16b  \n"
                "ST1 {v0.16b}, [%[CtrOut]]   \n"

                :[CtrOut] "=r" (outBlock), "=r" (keyPt), "=r" (aes->rounds),
                 "=r" (inBlock)
                :"0" (outBlock), [Key] "1" (keyPt), [R] "2" (aes->rounds),
                 [CtrIn] "3" (inBlock)
                : "cc", "memory", "w12", "v0", "v1", "v2", "v3", "v4"
            );

        return 0;
    }
#endif /* AES_GCM, AES_CCM, DIRECT or COUNTER */
#if defined(WOLFSSL_AES_DIRECT) || defined(WOLFSSL_AES_COUNTER)
    #ifdef HAVE_AES_DECRYPT
    static int wc_AesDecrypt(Aes* aes, const byte* inBlock, byte* outBlock)
    {
            word32* keyPt = aes->key;

            /*
              AESE exor's input with round key
                   shift rows of exor'ed result
                   sub bytes for shifted rows
             */

            __asm__ __volatile__ (
                "LD1 {v0.16b}, [%[CtrIn]] \n"
                "LD1 {v1.2d-v4.2d}, [%[Key]], #64  \n"

                "AESD v0.16b, v1.16b   \n"
                "AESIMC v0.16b, v0.16b \n"
                "AESD v0.16b, v2.16b   \n"
                "AESIMC v0.16b, v0.16b \n"
                "AESD v0.16b, v3.16b   \n"
                "AESIMC v0.16b, v0.16b \n"
                "AESD v0.16b, v4.16b   \n"
                "AESIMC v0.16b, v0.16b \n"

                "LD1 {v1.2d-v4.2d}, [%[Key]], #64  \n"
                "AESD v0.16b, v1.16b   \n"
                "AESIMC v0.16b, v0.16b \n"
                "AESD v0.16b, v2.16b   \n"
                "AESIMC v0.16b, v0.16b \n"
                "AESD v0.16b, v3.16b   \n"
                "AESIMC v0.16b, v0.16b \n"
                "AESD v0.16b, v4.16b   \n"
                "AESIMC v0.16b, v0.16b \n"

                "LD1 {v1.2d-v2.2d}, [%[Key]], #32  \n"
                "AESD v0.16b, v1.16b   \n"
                "AESIMC v0.16b, v0.16b \n"
                "AESD v0.16b, v2.16b   \n"

                "#subtract rounds done so far and see if should continue\n"
                "MOV w12, %w[R]    \n"
                "SUB w12, w12, #10 \n"
                "CBZ w12, 1f       \n"
                "LD1 {v1.2d-v2.2d}, [%[Key]], #32  \n"
                "AESIMC v0.16b, v0.16b \n"
                "AESD v0.16b, v1.16b   \n"
                "AESIMC v0.16b, v0.16b \n"
                "AESD v0.16b, v2.16b   \n"

                "SUB w12, w12, #2  \n"
                "CBZ w12, 1f       \n"
                "LD1 {v1.2d-v2.2d}, [%[Key]], #32  \n"
                "AESIMC v0.16b, v0.16b \n"
                "AESD v0.16b, v1.16b   \n"
                "AESIMC v0.16b, v0.16b \n"
                "AESD v0.16b, v2.16b   \n"

                "#Final AddRoundKey then store result \n"
                "1: \n"
                "LD1 {v1.2d}, [%[Key]], #16 \n"
                "EOR v0.16b, v0.16b, v1.16b  \n"
                "ST1 {v0.4s}, [%[CtrOut]]    \n"

                :[CtrOut] "=r" (outBlock), "=r" (keyPt), "=r" (aes->rounds),
                 "=r" (inBlock)
                :[Key] "1" (aes->key), "0" (outBlock), [R] "2" (aes->rounds),
                 [CtrIn] "3" (inBlock)
                : "cc", "memory", "w12", "v0", "v1", "v2", "v3", "v4"
            );

        return 0;
}
    #endif /* HAVE_AES_DECRYPT */
#endif /* DIRECT or COUNTER */

/* AES-CBC */
#ifdef HAVE_AES_CBC
    int wc_AesCbcEncrypt(Aes* aes, byte* out, const byte* in, word32 sz)
    {
        word32 numBlocks = sz / AES_BLOCK_SIZE;

        if (aes == NULL || out == NULL || (in == NULL && sz > 0)) {
            return BAD_FUNC_ARG;
        }

        /* do as many block size ops as possible */
        if (numBlocks > 0) {
            word32* key = aes->key;
            word32* reg = aes->reg;
            /*
            AESE exor's input with round key
            shift rows of exor'ed result
            sub bytes for shifted rows

            note: grouping AESE & AESMC together as pairs reduces latency
            */
            switch(aes->rounds) {
#ifdef WOLFSSL_AES_128
            case 10: /* AES 128 BLOCK */
                __asm__ __volatile__ (
                "MOV w11, %w[blocks] \n"
                "LD1 {v1.2d-v4.2d}, [%[Key]], #64  \n"
                "LD1 {v5.2d-v8.2d}, [%[Key]], #64  \n"
                "LD1 {v9.2d-v11.2d},[%[Key]], #48  \n"
                "LD1 {v0.2d}, [%[reg]] \n"

                "LD1 {v12.2d}, [%[input]], #16 \n"
                "1:\n"
                "#CBC operations, xorbuf in with current aes->reg \n"
                "EOR v0.16b, v0.16b, v12.16b \n"
                "AESE v0.16b, v1.16b  \n"
                "AESMC v0.16b, v0.16b \n"
                "AESE v0.16b, v2.16b  \n"
                "AESMC v0.16b, v0.16b \n"
                "AESE v0.16b, v3.16b  \n"
                "AESMC v0.16b, v0.16b \n"
                "AESE v0.16b, v4.16b  \n"
                "AESMC v0.16b, v0.16b \n"
                "AESE v0.16b, v5.16b  \n"
                "AESMC v0.16b, v0.16b \n"
                "AESE v0.16b, v6.16b  \n"
                "AESMC v0.16b, v0.16b \n"
                "AESE v0.16b, v7.16b  \n"
                "AESMC v0.16b, v0.16b \n"
                "AESE v0.16b, v8.16b  \n"
                "AESMC v0.16b, v0.16b \n"
                "AESE v0.16b, v9.16b  \n"
                "AESMC v0.16b, v0.16b \n"
                "AESE v0.16b, v10.16b  \n"
                "SUB w11, w11, #1 \n"
                "EOR v0.16b, v0.16b, v11.16b  \n"
                "ST1 {v0.2d}, [%[out]], #16   \n"

                "CBZ w11, 2f \n"
                "LD1 {v12.2d}, [%[input]], #16 \n"
                "B 1b \n"

                "2:\n"
                "#store current counter value at the end \n"
                "ST1 {v0.2d}, [%[regOut]] \n"

                :[out] "=r" (out), [regOut] "=r" (reg), "=r" (in)
                :"0" (out), [Key] "r" (key), [input] "2" (in),
                 [blocks] "r" (numBlocks), [reg] "1" (reg)
                : "cc", "memory", "w11", "v0", "v1", "v2", "v3", "v4", "v5",
                "v6", "v7", "v8", "v9", "v10", "v11", "v12", "v13"
                );
                break;
#endif /* WOLFSSL_AES_128 */
#ifdef WOLFSSL_AES_192
            case 12: /* AES 192 BLOCK */
                __asm__ __volatile__ (
                "MOV w11, %w[blocks] \n"
                "LD1 {v1.2d-v4.2d}, %[Key], #64  \n"
                "LD1 {v5.2d-v8.2d}, %[Key], #64  \n"
                "LD1 {v9.2d-v12.2d},%[Key], #64  \n"
                "LD1 {v13.2d}, %[Key], #16 \n"
                "LD1 {v0.2d}, %[reg] \n"

                "LD1 {v14.2d}, [%[input]], #16  \n"
                "1:\n"
                "#CBC operations, xorbuf in with current aes->reg \n"
                "EOR v0.16b, v0.16b, v14.16b \n"
                "AESE v0.16b, v1.16b  \n"
                "AESMC v0.16b, v0.16b \n"
                "AESE v0.16b, v2.16b  \n"
                "AESMC v0.16b, v0.16b \n"
                "AESE v0.16b, v3.16b  \n"
                "AESMC v0.16b, v0.16b \n"
                "AESE v0.16b, v4.16b  \n"
                "AESMC v0.16b, v0.16b \n"
                "AESE v0.16b, v5.16b  \n"
                "AESMC v0.16b, v0.16b \n"
                "AESE v0.16b, v6.16b  \n"
                "AESMC v0.16b, v0.16b \n"
                "AESE v0.16b, v7.16b  \n"
                "AESMC v0.16b, v0.16b \n"
                "AESE v0.16b, v8.16b  \n"
                "AESMC v0.16b, v0.16b \n"
                "AESE v0.16b, v9.16b  \n"
                "AESMC v0.16b, v0.16b \n"
                "AESE v0.16b, v10.16b \n"
                "AESMC v0.16b, v0.16b \n"
                "AESE v0.16b, v11.16b \n"
                "AESMC v0.16b, v0.16b \n"
                "AESE v0.16b, v12.16b \n"
                "EOR v0.16b, v0.16b, v13.16b  \n"
                "SUB w11, w11, #1 \n"
                "ST1 {v0.2d}, [%[out]], #16  \n"

                "CBZ w11, 2f \n"
                "LD1 {v14.2d}, [%[input]], #16\n"
                "B 1b \n"

                "2:\n"
                "#store current counter value at the end \n"
                "ST1 {v0.2d}, %[regOut]   \n"


                :[out] "=r" (out), [regOut] "=m" (aes->reg), "=r" (in)
                :"0" (out), [Key] "m" (aes->key), [input] "2" (in),
                 [blocks] "r" (numBlocks), [reg] "m" (aes->reg)
                : "cc", "memory", "w11", "v0", "v1", "v2", "v3", "v4", "v5",
                "v6", "v7", "v8", "v9", "v10", "v11", "v12", "v13", "v14"
                );
                break;
#endif /* WOLFSSL_AES_192*/
#ifdef WOLFSSL_AES_256
            case 14: /* AES 256 BLOCK */
                __asm__ __volatile__ (
                "MOV w11, %w[blocks] \n"
                "LD1 {v1.2d-v4.2d},   %[Key], #64 \n"

                "LD1 {v5.2d-v8.2d},   %[Key], #64 \n"
                "LD1 {v9.2d-v12.2d},  %[Key], #64 \n"
                "LD1 {v13.2d-v15.2d}, %[Key], #48 \n"
                "LD1 {v0.2d}, %[reg] \n"

                "LD1 {v16.2d}, [%[input]], #16  \n"
                "1: \n"
                "#CBC operations, xorbuf in with current aes->reg \n"
                "EOR v0.16b, v0.16b, v16.16b \n"
                "AESE v0.16b, v1.16b  \n"
                "AESMC v0.16b, v0.16b \n"
                "AESE v0.16b, v2.16b  \n"
                "AESMC v0.16b, v0.16b \n"
                "AESE v0.16b, v3.16b  \n"
                "AESMC v0.16b, v0.16b \n"
                "AESE v0.16b, v4.16b  \n"
                "AESMC v0.16b, v0.16b \n"
                "AESE v0.16b, v5.16b  \n"
                "AESMC v0.16b, v0.16b \n"
                "AESE v0.16b, v6.16b  \n"
                "AESMC v0.16b, v0.16b \n"
                "AESE v0.16b, v7.16b  \n"
                "AESMC v0.16b, v0.16b \n"
                "AESE v0.16b, v8.16b  \n"
                "AESMC v0.16b, v0.16b \n"
                "AESE v0.16b, v9.16b  \n"
                "AESMC v0.16b, v0.16b \n"
                "AESE v0.16b, v10.16b \n"
                "AESMC v0.16b, v0.16b \n"
                "AESE v0.16b, v11.16b \n"
                "AESMC v0.16b, v0.16b \n"
                "AESE v0.16b, v12.16b \n"
                "AESMC v0.16b, v0.16b \n"
                "AESE v0.16b, v13.16b \n"
                "AESMC v0.16b, v0.16b \n"
                "AESE v0.16b, v14.16b \n"
                "EOR v0.16b, v0.16b, v15.16b \n"
                "SUB w11, w11, #1     \n"
                "ST1 {v0.2d}, [%[out]], #16  \n"

                "CBZ w11, 2f \n"
                "LD1 {v16.2d}, [%[input]], #16 \n"
                "B 1b \n"

                "2: \n"
                "#store current counter value at the end \n"
                "ST1 {v0.2d}, %[regOut]   \n"


                :[out] "=r" (out), [regOut] "=m" (aes->reg), "=r" (in)
                :"0" (out), [Key] "m" (aes->key), [input] "2" (in),
                 [blocks] "r" (numBlocks), [reg] "m" (aes->reg)
                : "cc", "memory", "w11", "v0", "v1", "v2", "v3", "v4", "v5",
                "v6", "v7", "v8", "v9", "v10", "v11", "v12", "v13", "v14","v15",
                "v16"
                );
                break;
#endif /* WOLFSSL_AES_256 */
            default:
                WOLFSSL_MSG("Bad AES-CBC round value");
                return BAD_FUNC_ARG;
            }
        }

        return 0;
    }

    #ifdef HAVE_AES_DECRYPT
    int wc_AesCbcDecrypt(Aes* aes, byte* out, const byte* in, word32 sz)
    {
        word32 numBlocks = sz / AES_BLOCK_SIZE;

        if (aes == NULL || out == NULL || (in == NULL && sz > 0)
                || sz % AES_BLOCK_SIZE != 0) {
            return BAD_FUNC_ARG;
        }

        /* do as many block size ops as possible */
        if (numBlocks > 0) {
            word32* key = aes->key;
            word32* reg = aes->reg;

            switch(aes->rounds) {
#ifdef WOLFSSL_AES_128
            case 10: /* AES 128 BLOCK */
                __asm__ __volatile__ (
                "MOV w11, %w[blocks] \n"
                "LD1 {v1.2d-v4.2d}, [%[Key]], #64  \n"
                "LD1 {v5.2d-v8.2d}, [%[Key]], #64  \n"
                "LD1 {v9.2d-v11.2d},[%[Key]], #48  \n"
                "LD1 {v13.2d}, [%[reg]] \n"

                "1:\n"
                "LD1 {v0.2d}, [%[input]], #16  \n"
                "MOV v12.16b, v0.16b \n"
                "AESD v0.16b, v1.16b   \n"
                "AESIMC v0.16b, v0.16b \n"
                "AESD v0.16b, v2.16b   \n"
                "AESIMC v0.16b, v0.16b \n"
                "AESD v0.16b, v3.16b   \n"
                "AESIMC v0.16b, v0.16b \n"
                "AESD v0.16b, v4.16b   \n"
                "AESIMC v0.16b, v0.16b \n"
                "AESD v0.16b, v5.16b   \n"
                "AESIMC v0.16b, v0.16b \n"
                "AESD v0.16b, v6.16b   \n"
                "AESIMC v0.16b, v0.16b \n"
                "AESD v0.16b, v7.16b   \n"
                "AESIMC v0.16b, v0.16b \n"
                "AESD v0.16b, v8.16b   \n"
                "AESIMC v0.16b, v0.16b \n"
                "AESD v0.16b, v9.16b   \n"
                "AESIMC v0.16b, v0.16b \n"
                "AESD v0.16b, v10.16b  \n"
                "EOR v0.16b, v0.16b, v11.16b \n"

                "EOR v0.16b, v0.16b, v13.16b \n"
                "SUB w11, w11, #1            \n"
                "ST1 {v0.2d}, [%[out]], #16  \n"
                "MOV v13.16b, v12.16b        \n"

                "CBZ w11, 2f \n"
                "B 1b      \n"

                "2: \n"
                "#store current counter value at the end \n"
                "ST1 {v13.2d}, [%[regOut]] \n"

                :[out] "=r" (out), [regOut] "=r" (reg), "=r" (in)
                :"0" (out), [Key] "r" (key), [input] "2" (in),
                 [blocks] "r" (numBlocks), [reg] "1" (reg)
                : "cc", "memory", "w11", "v0", "v1", "v2", "v3", "v4", "v5",
                "v6", "v7", "v8", "v9", "v10", "v11", "v12", "v13"
                );
                break;
#endif /* WOLFSSL_AES_128 */
#ifdef WOLFSSL_AES_192
            case 12: /* AES 192 BLOCK */
                __asm__ __volatile__ (
                "MOV w11, %w[blocks] \n"
                "LD1 {v1.2d-v4.2d}, [%[Key]], #64  \n"
                "LD1 {v5.2d-v8.2d}, [%[Key]], #64  \n"
                "LD1 {v9.2d-v12.2d},[%[Key]], #64  \n"
                "LD1 {v13.16b}, [%[Key]], #16 \n"
                "LD1 {v15.2d}, [%[reg]]       \n"

                "LD1 {v0.2d}, [%[input]], #16  \n"
                "1:    \n"
                "MOV v14.16b, v0.16b   \n"
                "AESD v0.16b, v1.16b   \n"
                "AESIMC v0.16b, v0.16b \n"
                "AESD v0.16b, v2.16b   \n"
                "AESIMC v0.16b, v0.16b \n"
                "AESD v0.16b, v3.16b   \n"
                "AESIMC v0.16b, v0.16b \n"
                "AESD v0.16b, v4.16b   \n"
                "AESIMC v0.16b, v0.16b \n"
                "AESD v0.16b, v5.16b   \n"
                "AESIMC v0.16b, v0.16b \n"
                "AESD v0.16b, v6.16b   \n"
                "AESIMC v0.16b, v0.16b \n"
                "AESD v0.16b, v7.16b   \n"
                "AESIMC v0.16b, v0.16b \n"
                "AESD v0.16b, v8.16b   \n"
                "AESIMC v0.16b, v0.16b \n"
                "AESD v0.16b, v9.16b   \n"
                "AESIMC v0.16b, v0.16b \n"
                "AESD v0.16b, v10.16b  \n"
                "AESIMC v0.16b, v0.16b \n"
                "AESD v0.16b, v11.16b  \n"
                "AESIMC v0.16b, v0.16b \n"
                "AESD v0.16b, v12.16b  \n"
                "EOR v0.16b, v0.16b, v13.16b \n"

                "EOR v0.16b, v0.16b, v15.16b \n"
                "SUB w11, w11, #1            \n"
                "ST1 {v0.2d}, [%[out]], #16  \n"
                "MOV v15.16b, v14.16b        \n"

                "CBZ w11, 2f \n"
                "LD1 {v0.2d}, [%[input]], #16 \n"
                "B 1b \n"

                "2:\n"
                "#store current counter value at the end \n"
                "ST1 {v15.2d}, [%[regOut]] \n"

                :[out] "=r" (out), [regOut] "=r" (reg), "=r" (in)
                :"0" (out), [Key] "r" (key), [input] "2" (in),
                 [blocks] "r" (numBlocks), [reg] "1" (reg)
                : "cc", "memory", "w11", "v0", "v1", "v2", "v3", "v4", "v5",
                "v6", "v7", "v8", "v9", "v10", "v11", "v12", "v13", "v14", "v15"
                );
                break;
#endif /* WOLFSSL_AES_192 */
#ifdef WOLFSSL_AES_256
            case 14: /* AES 256 BLOCK */
                __asm__ __volatile__ (
                "MOV w11, %w[blocks] \n"
                "LD1 {v1.2d-v4.2d},   [%[Key]], #64  \n"
                "LD1 {v5.2d-v8.2d},   [%[Key]], #64  \n"
                "LD1 {v9.2d-v12.2d},  [%[Key]], #64  \n"
                "LD1 {v13.2d-v15.2d}, [%[Key]], #48  \n"
                "LD1 {v17.2d}, [%[reg]] \n"

                "LD1 {v0.2d}, [%[input]], #16  \n"
                "1:    \n"
                "MOV v16.16b, v0.16b   \n"
                "AESD v0.16b, v1.16b   \n"
                "AESIMC v0.16b, v0.16b \n"
                "AESD v0.16b, v2.16b   \n"
                "AESIMC v0.16b, v0.16b \n"
                "AESD v0.16b, v3.16b   \n"
                "AESIMC v0.16b, v0.16b \n"
                "AESD v0.16b, v4.16b   \n"
                "AESIMC v0.16b, v0.16b \n"
                "AESD v0.16b, v5.16b   \n"
                "AESIMC v0.16b, v0.16b \n"
                "AESD v0.16b, v6.16b   \n"
                "AESIMC v0.16b, v0.16b \n"
                "AESD v0.16b, v7.16b   \n"
                "AESIMC v0.16b, v0.16b \n"
                "AESD v0.16b, v8.16b   \n"
                "AESIMC v0.16b, v0.16b \n"
                "AESD v0.16b, v9.16b   \n"
                "AESIMC v0.16b, v0.16b \n"
                "AESD v0.16b, v10.16b  \n"
                "AESIMC v0.16b, v0.16b \n"
                "AESD v0.16b, v11.16b  \n"
                "AESIMC v0.16b, v0.16b \n"
                "AESD v0.16b, v12.16b  \n"
                "AESIMC v0.16b, v0.16b \n"
                "AESD v0.16b, v13.16b  \n"
                "AESIMC v0.16b, v0.16b \n"
                "AESD v0.16b, v14.16b  \n"
                "EOR v0.16b, v0.16b, v15.16b \n"

                "EOR v0.16b, v0.16b, v17.16b \n"
                "SUB w11, w11, #1            \n"
                "ST1 {v0.2d}, [%[out]], #16  \n"
                "MOV v17.16b, v16.16b        \n"

                "CBZ w11, 2f \n"
                "LD1 {v0.2d}, [%[input]], #16  \n"
                "B 1b \n"

                "2:\n"
                "#store current counter value at the end \n"
                "ST1 {v17.2d}, [%[regOut]]   \n"

                :[out] "=r" (out), [regOut] "=r" (reg), "=r" (in)
                :"0" (out), [Key] "r" (key), [input] "2" (in),
                 [blocks] "r" (numBlocks), [reg] "1" (reg)
                : "cc", "memory", "w11", "v0", "v1", "v2", "v3", "v4", "v5",
                "v6", "v7", "v8", "v9", "v10", "v11", "v12", "v13", "v14","v15",
                "v16", "v17"
                );
                break;
#endif /* WOLFSSL_AES_256 */
            default:
                WOLFSSL_MSG("Bad AES-CBC round value");
                return BAD_FUNC_ARG;
            }
        }

        return 0;
    }
    #endif

#endif /* HAVE_AES_CBC */

/* AES-CTR */
#ifdef WOLFSSL_AES_COUNTER

        /* Increment AES counter */
        static WC_INLINE void IncrementAesCounter(byte* inOutCtr)
        {
            int i;

            /* in network byte order so start at end and work back */
            for (i = AES_BLOCK_SIZE - 1; i >= 0; i--) {
                if (++inOutCtr[i])  /* we're done unless we overflow */
                    return;
            }
        }

        int wc_AesCtrEncrypt(Aes* aes, byte* out, const byte* in, word32 sz)
        {
            byte* tmp;
            word32 numBlocks;

            if (aes == NULL || out == NULL || in == NULL) {
                return BAD_FUNC_ARG;
            }

            tmp = (byte*)aes->tmp + AES_BLOCK_SIZE - aes->left;

            /* consume any unused bytes left in aes->tmp */
            while (aes->left && sz) {
               *(out++) = *(in++) ^ *(tmp++);
               aes->left--;
               sz--;
            }

            /* do as many block size ops as possible */
            numBlocks = sz/AES_BLOCK_SIZE;
            if (numBlocks > 0) {
                /* pointer needed because it is incremented when read, causing
                 * an issue with call to encrypt/decrypt leftovers */
                byte*  keyPt  = (byte*)aes->key;
                sz           -= numBlocks * AES_BLOCK_SIZE;
                switch(aes->rounds) {
#ifdef WOLFSSL_AES_128
                case 10: /* AES 128 BLOCK */
                    __asm__ __volatile__ (
                    "MOV w11, %w[blocks] \n"
                    "LD1 {v1.2d-v4.2d}, [%[Key]], #64 \n"

                    "#Create vector with the value 1  \n"
                    "MOVI v15.16b, #1                 \n"
                    "USHR v15.2d, v15.2d, #56         \n"
                    "LD1 {v5.2d-v8.2d}, [%[Key]], #64 \n"
                    "EOR v14.16b, v14.16b, v14.16b    \n"
                    "EXT v14.16b, v15.16b, v14.16b, #8\n"

                    "LD1 {v9.2d-v11.2d}, [%[Key]], #48\n"
                    "LD1 {v13.2d}, %[reg]             \n"

                    /* double block */
                    "1:      \n"
                    "CMP w11, #1 \n"
                    "BEQ 2f    \n"
                    "CMP w11, #0 \n"
                    "BEQ 3f    \n"

                    "MOV v0.16b, v13.16b  \n"
                    "AESE v0.16b, v1.16b  \n"
                    "AESMC v0.16b, v0.16b \n"
                    "REV64 v13.16b, v13.16b \n" /* network order */
                    "AESE v0.16b, v2.16b  \n"
                    "AESMC v0.16b, v0.16b \n"
                    "EXT v13.16b, v13.16b, v13.16b, #8 \n"
                    "SUB w11, w11, #2     \n"
                    "ADD v15.2d, v13.2d, v14.2d \n" /* add 1 to counter */
                    "ADD v13.2d, v15.2d, v14.2d \n" /* add 1 to counter */

                    "AESE v0.16b, v3.16b  \n"
                    "AESMC v0.16b, v0.16b \n"
                    "EXT v15.16b, v15.16b, v15.16b, #8 \n"
                    "EXT v13.16b, v13.16b, v13.16b, #8 \n"

                    "AESE v0.16b, v4.16b  \n"
                    "AESMC v0.16b, v0.16b \n"
                    "REV64 v15.16b, v15.16b \n" /* revert from network order */
                    "REV64 v13.16b, v13.16b \n" /* revert from network order */

                    "AESE v0.16b, v5.16b  \n"
                    "AESMC v0.16b, v0.16b \n"
                    "AESE v15.16b, v1.16b  \n"
                    "AESMC v15.16b, v15.16b \n"

                    "AESE v0.16b, v6.16b  \n"
                    "AESMC v0.16b, v0.16b \n"
                    "AESE v15.16b, v2.16b  \n"
                    "AESMC v15.16b, v15.16b \n"

                    "AESE v0.16b, v7.16b  \n"
                    "AESMC v0.16b, v0.16b \n"
                    "AESE v15.16b, v3.16b  \n"
                    "AESMC v15.16b, v15.16b \n"

                    "AESE v0.16b, v8.16b  \n"
                    "AESMC v0.16b, v0.16b \n"
                    "AESE v15.16b, v4.16b  \n"
                    "AESMC v15.16b, v15.16b \n"

                    "AESE v0.16b, v9.16b  \n"
                    "AESMC v0.16b, v0.16b \n"
                    "AESE v15.16b, v5.16b  \n"
                    "AESMC v15.16b, v15.16b \n"

                    "AESE v0.16b, v10.16b  \n"
                    "AESE v15.16b, v6.16b  \n"
                    "AESMC v15.16b, v15.16b \n"

                    "EOR v0.16b, v0.16b, v11.16b \n"
                    "AESE v15.16b, v7.16b  \n"
                    "AESMC v15.16b, v15.16b \n"

                    "LD1 {v12.2d}, [%[input]], #16  \n"
                    "AESE v15.16b, v8.16b  \n"
                    "AESMC v15.16b, v15.16b \n"

                    "EOR v0.16b, v0.16b, v12.16b \n"
                    "AESE v15.16b, v9.16b  \n"
                    "AESMC v15.16b, v15.16b \n"

                    "LD1 {v12.2d}, [%[input]], #16  \n"
                    "AESE v15.16b, v10.16b  \n"
                    "ST1 {v0.2d}, [%[out]], #16  \n"
                    "EOR v15.16b, v15.16b, v11.16b \n"
                    "EOR v15.16b, v15.16b, v12.16b \n"
                    "ST1 {v15.2d}, [%[out]], #16  \n"

                    "B 1b \n"

                    /* single block */
                    "2: \n"
                    "MOV v0.16b, v13.16b  \n"
                    "AESE v0.16b, v1.16b  \n"
                    "AESMC v0.16b, v0.16b \n"
                    "REV64 v13.16b, v13.16b \n" /* network order */
                    "AESE v0.16b, v2.16b  \n"
                    "AESMC v0.16b, v0.16b \n"
                    "EXT v13.16b, v13.16b, v13.16b, #8 \n"
                    "AESE v0.16b, v3.16b  \n"
                    "AESMC v0.16b, v0.16b \n"
                    "ADD v13.2d, v13.2d, v14.2d \n" /* add 1 to counter */
                    "AESE v0.16b, v4.16b  \n"
                    "AESMC v0.16b, v0.16b \n"
                    "SUB w11, w11, #1     \n"
                    "AESE v0.16b, v5.16b  \n"
                    "AESMC v0.16b, v0.16b \n"
                    "EXT v13.16b, v13.16b, v13.16b, #8 \n"
                    "AESE v0.16b, v6.16b  \n"
                    "AESMC v0.16b, v0.16b \n"
                    "REV64 v13.16b, v13.16b \n" /* revert from network order */
                    "AESE v0.16b, v7.16b  \n"
                    "AESMC v0.16b, v0.16b \n"
                    "AESE v0.16b, v8.16b  \n"
                    "AESMC v0.16b, v0.16b \n"
                    "AESE v0.16b, v9.16b  \n"
                    "AESMC v0.16b, v0.16b \n"
                    "AESE v0.16b, v10.16b \n"
                    "EOR v0.16b, v0.16b, v11.16b \n"
                    "#CTR operations, increment counter and xorbuf \n"
                    "LD1 {v12.2d}, [%[input]], #16  \n"
                    "EOR v0.16b, v0.16b, v12.16b \n"
                    "ST1 {v0.2d}, [%[out]], #16  \n"

                    "3: \n"
                    "#store current counter value at the end \n"
                    "ST1 {v13.2d}, %[regOut]   \n"

                    :[out] "=r" (out), "=r" (keyPt), [regOut] "=m" (aes->reg),
                     "=r" (in)
                    :"0" (out), [Key] "1" (keyPt), [input] "3" (in),
                     [blocks] "r" (numBlocks), [reg] "m" (aes->reg)
                    : "cc", "memory", "w11", "v0", "v1", "v2", "v3", "v4", "v5",
                    "v6", "v7", "v8", "v9", "v10","v11","v12","v13","v14","v15"
                    );
                    break;
#endif /* WOLFSSL_AES_128 */
#ifdef WOLFSSL_AES_192
                case 12: /* AES 192 BLOCK */
                    __asm__ __volatile__ (
                    "MOV w11, %w[blocks]              \n"
                    "LD1 {v1.2d-v4.2d}, [%[Key]], #64 \n"

                    "#Create vector with the value 1  \n"
                    "MOVI v16.16b, #1                 \n"
                    "USHR v16.2d, v16.2d, #56         \n"
                    "LD1 {v5.2d-v8.2d}, [%[Key]], #64 \n"
                    "EOR v14.16b, v14.16b, v14.16b    \n"
                    "EXT v16.16b, v16.16b, v14.16b, #8\n"

                    "LD1 {v9.2d-v12.2d}, [%[Key]], #64\n"
                    "LD1 {v15.2d}, %[reg]             \n"
                    "LD1 {v13.16b}, [%[Key]], #16     \n"

                    /* double block */
                    "1:      \n"
                    "CMP w11, #1 \n"
                    "BEQ 2f    \n"
                    "CMP w11, #0 \n"
                    "BEQ 3f    \n"

                    "MOV v0.16b, v15.16b  \n"
                    "AESE v0.16b, v1.16b  \n"
                    "AESMC v0.16b, v0.16b \n"
                    "REV64 v15.16b, v15.16b \n" /* network order */
                    "AESE v0.16b, v2.16b  \n"
                    "AESMC v0.16b, v0.16b \n"
                    "EXT v15.16b, v15.16b, v15.16b, #8 \n"
                    "SUB w11, w11, #2     \n"
                    "ADD v17.2d, v15.2d, v16.2d \n" /* add 1 to counter */
                    "ADD v15.2d, v17.2d, v16.2d \n" /* add 1 to counter */

                    "AESE v0.16b, v3.16b  \n"
                    "AESMC v0.16b, v0.16b \n"
                    "EXT v17.16b, v17.16b, v17.16b, #8 \n"
                    "EXT v15.16b, v15.16b, v15.16b, #8 \n"

                    "AESE v0.16b, v4.16b  \n"
                    "AESMC v0.16b, v0.16b \n"
                    "REV64 v17.16b, v17.16b \n" /* revert from network order */
                    "REV64 v15.16b, v15.16b \n" /* revert from network order */

                    "AESE v0.16b, v5.16b  \n"
                    "AESMC v0.16b, v0.16b \n"
                    "AESE v17.16b, v1.16b  \n"
                    "AESMC v17.16b, v17.16b \n"

                    "AESE v0.16b, v6.16b  \n"
                    "AESMC v0.16b, v0.16b \n"
                    "AESE v17.16b, v2.16b  \n"
                    "AESMC v17.16b, v17.16b \n"

                    "AESE v0.16b, v7.16b  \n"
                    "AESMC v0.16b, v0.16b \n"
                    "AESE v17.16b, v3.16b  \n"
                    "AESMC v17.16b, v17.16b \n"

                    "AESE v0.16b, v8.16b  \n"
                    "AESMC v0.16b, v0.16b \n"
                    "AESE v17.16b, v4.16b  \n"
                    "AESMC v17.16b, v17.16b \n"

                    "AESE v0.16b, v9.16b  \n"
                    "AESMC v0.16b, v0.16b \n"
                    "AESE v17.16b, v5.16b  \n"
                    "AESMC v17.16b, v17.16b \n"

                    "AESE v0.16b, v10.16b  \n"
                    "AESMC v0.16b, v0.16b \n"
                    "AESE v17.16b, v6.16b  \n"
                    "AESMC v17.16b, v17.16b \n"

                    "AESE v0.16b, v11.16b  \n"
                    "AESMC v0.16b, v0.16b \n"
                    "AESE v17.16b, v7.16b  \n"
                    "AESMC v17.16b, v17.16b \n"

                    "AESE v0.16b, v12.16b  \n"
                    "AESE v17.16b, v8.16b  \n"
                    "AESMC v17.16b, v17.16b \n"

                    "EOR v0.16b, v0.16b, v13.16b \n"
                    "AESE v17.16b, v9.16b  \n"
                    "AESMC v17.16b, v17.16b \n"

                    "LD1 {v14.2d}, [%[input]], #16  \n"
                    "AESE v17.16b, v10.16b  \n"
                    "AESMC v17.16b, v17.16b \n"

                    "EOR v0.16b, v0.16b, v14.16b \n"
                    "AESE v17.16b, v11.16b  \n"
                    "AESMC v17.16b, v17.16b \n"

                    "LD1 {v14.2d}, [%[input]], #16  \n"
                    "AESE v17.16b, v12.16b  \n"
                    "ST1 {v0.2d}, [%[out]], #16  \n"
                    "EOR v17.16b, v17.16b, v13.16b \n"
                    "EOR v17.16b, v17.16b, v14.16b \n"
                    "ST1 {v17.2d}, [%[out]], #16  \n"

                    "B 1b \n"

                    "2:      \n"
                    "LD1 {v14.2d}, [%[input]], #16    \n"
                    "MOV v0.16b, v15.16b  \n"

                    "AESE v0.16b, v1.16b  \n"
                    "AESMC v0.16b, v0.16b \n"
                    "REV64 v15.16b, v15.16b \n" /* network order */
                    "AESE v0.16b, v2.16b  \n"
                    "AESMC v0.16b, v0.16b \n"
                    "EXT v15.16b, v15.16b, v15.16b, #8 \n"
                    "AESE v0.16b, v3.16b  \n"
                    "AESMC v0.16b, v0.16b \n"
                    "ADD v15.2d, v15.2d, v16.2d \n" /* add 1 to counter */
                    "AESE v0.16b, v4.16b  \n"
                    "AESMC v0.16b, v0.16b \n"
                    "SUB w11, w11, #1     \n"
                    "AESE v0.16b, v5.16b  \n"
                    "AESMC v0.16b, v0.16b \n"
                    "EXT v15.16b, v15.16b, v15.16b, #8 \n"
                    "AESE v0.16b, v6.16b  \n"
                    "AESMC v0.16b, v0.16b \n"
                    "REV64 v15.16b, v15.16b \n" /* revert from network order */
                    "AESE v0.16b, v7.16b  \n"
                    "AESMC v0.16b, v0.16b \n"
                    "AESE v0.16b, v8.16b  \n"
                    "AESMC v0.16b, v0.16b \n"
                    "AESE v0.16b, v9.16b  \n"
                    "AESMC v0.16b, v0.16b \n"
                    "AESE v0.16b, v10.16b \n"
                    "AESMC v0.16b, v0.16b \n"
                    "AESE v0.16b, v11.16b \n"
                    "AESMC v0.16b, v0.16b \n"
                    "AESE v0.16b, v12.16b \n"
                    "EOR v0.16b, v0.16b, v13.16b \n"
                    "#CTR operations, increment counter and xorbuf \n"
                    "EOR v0.16b, v0.16b, v14.16b \n"
                    "ST1 {v0.2d}, [%[out]], #16  \n"

                    "3: \n"
                    "#store current counter value at the end \n"
                    "ST1 {v15.2d}, %[regOut] \n"

                    :[out] "=r" (out), "=r" (keyPt), [regOut] "=m" (aes->reg),
                     "=r" (in)
                    :"0" (out), [Key] "1" (keyPt), [input] "3" (in),
                     [blocks] "r" (numBlocks), [reg] "m" (aes->reg)
                    : "cc", "memory", "w11", "v0", "v1", "v2", "v3", "v4", "v5",
                    "v6", "v7", "v8", "v9", "v10","v11","v12","v13","v14","v15",
                    "v16", "v17"
                    );
                    break;
#endif /* WOLFSSL_AES_192 */
#ifdef WOLFSSL_AES_256
                case 14: /* AES 256 BLOCK */
                    __asm__ __volatile__ (
                    "MOV w11, %w[blocks] \n"
                    "LD1 {v1.2d-v4.2d}, [%[Key]], #64 \n"

                    "#Create vector with the value 1  \n"
                    "MOVI v18.16b, #1                 \n"
                    "USHR v18.2d, v18.2d, #56         \n"
                    "LD1 {v5.2d-v8.2d}, [%[Key]], #64 \n"
                    "EOR v19.16b, v19.16b, v19.16b    \n"
                    "EXT v18.16b, v18.16b, v19.16b, #8\n"

                    "LD1 {v9.2d-v12.2d}, [%[Key]], #64  \n"
                    "LD1 {v13.2d-v15.2d}, [%[Key]], #48 \n"
                    "LD1 {v17.2d}, %[reg]               \n"

                    /* double block */
                    "1:      \n"
                    "CMP w11, #1 \n"
                    "BEQ 2f    \n"
                    "CMP w11, #0 \n"
                    "BEQ 3f    \n"

                    "MOV v0.16b, v17.16b  \n"
                    "AESE v0.16b, v1.16b  \n"
                    "AESMC v0.16b, v0.16b \n"
                    "REV64 v17.16b, v17.16b \n" /* network order */
                    "AESE v0.16b, v2.16b  \n"
                    "AESMC v0.16b, v0.16b \n"
                    "EXT v17.16b, v17.16b, v17.16b, #8 \n"
                    "SUB w11, w11, #2     \n"
                    "ADD v19.2d, v17.2d, v18.2d \n" /* add 1 to counter */
                    "ADD v17.2d, v19.2d, v18.2d \n" /* add 1 to counter */

                    "AESE v0.16b, v3.16b  \n"
                    "AESMC v0.16b, v0.16b \n"
                    "EXT v19.16b, v19.16b, v19.16b, #8 \n"
                    "EXT v17.16b, v17.16b, v17.16b, #8 \n"

                    "AESE v0.16b, v4.16b  \n"
                    "AESMC v0.16b, v0.16b \n"
                    "REV64 v19.16b, v19.16b \n" /* revert from network order */
                    "REV64 v17.16b, v17.16b \n" /* revert from network order */

                    "AESE v0.16b, v5.16b  \n"
                    "AESMC v0.16b, v0.16b \n"
                    "AESE v19.16b, v1.16b  \n"
                    "AESMC v19.16b, v19.16b \n"

                    "AESE v0.16b, v6.16b  \n"
                    "AESMC v0.16b, v0.16b \n"
                    "AESE v19.16b, v2.16b  \n"
                    "AESMC v19.16b, v19.16b \n"

                    "AESE v0.16b, v7.16b  \n"
                    "AESMC v0.16b, v0.16b \n"
                    "AESE v19.16b, v3.16b  \n"
                    "AESMC v19.16b, v19.16b \n"

                    "AESE v0.16b, v8.16b  \n"
                    "AESMC v0.16b, v0.16b \n"
                    "AESE v19.16b, v4.16b  \n"
                    "AESMC v19.16b, v19.16b \n"

                    "AESE v0.16b, v9.16b  \n"
                    "AESMC v0.16b, v0.16b \n"
                    "AESE v19.16b, v5.16b  \n"
                    "AESMC v19.16b, v19.16b \n"

                    "AESE v0.16b, v10.16b  \n"
                    "AESMC v0.16b, v0.16b \n"
                    "AESE v19.16b, v6.16b  \n"
                    "AESMC v19.16b, v19.16b \n"

                    "AESE v0.16b, v11.16b  \n"
                    "AESMC v0.16b, v0.16b \n"
                    "AESE v19.16b, v7.16b  \n"
                    "AESMC v19.16b, v19.16b \n"

                    "AESE v0.16b, v12.16b  \n"
                    "AESMC v0.16b, v0.16b \n"
                    "AESE v19.16b, v8.16b  \n"
                    "AESMC v19.16b, v19.16b \n"

                    "AESE v0.16b, v13.16b  \n"
                    "AESMC v0.16b, v0.16b \n"
                    "AESE v19.16b, v9.16b  \n"
                    "AESMC v19.16b, v19.16b \n"

                    "AESE v0.16b, v14.16b  \n"
                    "AESE v19.16b, v10.16b  \n"
                    "AESMC v19.16b, v19.16b \n"

                    "EOR v0.16b, v0.16b, v15.16b \n"
                    "AESE v19.16b, v11.16b  \n"
                    "AESMC v19.16b, v19.16b \n"

                    "LD1 {v16.2d}, [%[input]], #16 \n"
                    "AESE v19.16b, v12.16b  \n"
                    "AESMC v19.16b, v19.16b \n"

                    "EOR v0.16b, v0.16b, v16.16b \n"
                    "AESE v19.16b, v13.16b  \n"
                    "AESMC v19.16b, v19.16b \n"

                    "LD1 {v16.2d}, [%[input]], #16 \n"
                    "AESE v19.16b, v14.16b  \n"
                    "ST1 {v0.2d}, [%[out]], #16  \n"
                    "EOR v19.16b, v19.16b, v15.16b \n"
                    "EOR v19.16b, v19.16b, v16.16b \n"
                    "ST1 {v19.2d}, [%[out]], #16  \n"

                    "B 1b \n"

                    "2:      \n"
                    "LD1 {v16.2d}, [%[input]], #16 \n"
                    "MOV v0.16b, v17.16b  \n"
                    "AESE v0.16b, v1.16b  \n"
                    "AESMC v0.16b, v0.16b \n"
                    "REV64 v17.16b, v17.16b \n" /* network order */
                    "AESE v0.16b, v2.16b  \n"
                    "AESMC v0.16b, v0.16b \n"
                    "EXT v17.16b, v17.16b, v17.16b, #8 \n"
                    "AESE v0.16b, v3.16b  \n"
                    "AESMC v0.16b, v0.16b \n"
                    "ADD v17.2d, v17.2d, v18.2d \n" /* add 1 to counter */
                    "AESE v0.16b, v4.16b  \n"
                    "AESMC v0.16b, v0.16b \n"
                    "AESE v0.16b, v5.16b  \n"
                    "AESMC v0.16b, v0.16b \n"
                    "EXT v17.16b, v17.16b, v17.16b, #8 \n"
                    "AESE v0.16b, v6.16b  \n"
                    "AESMC v0.16b, v0.16b \n"
                    "REV64 v17.16b, v17.16b \n" /* revert from network order */
                    "AESE v0.16b, v7.16b  \n"
                    "AESMC v0.16b, v0.16b \n"
                    "AESE v0.16b, v8.16b  \n"
                    "AESMC v0.16b, v0.16b \n"
                    "AESE v0.16b, v9.16b  \n"
                    "AESMC v0.16b, v0.16b \n"
                    "AESE v0.16b, v10.16b \n"
                    "AESMC v0.16b, v0.16b \n"
                    "AESE v0.16b, v11.16b \n"
                    "AESMC v0.16b, v0.16b \n"
                    "AESE v0.16b, v12.16b \n"
                    "AESMC v0.16b, v0.16b \n"
                    "AESE v0.16b, v13.16b \n"
                    "AESMC v0.16b, v0.16b \n"
                    "AESE v0.16b, v14.16b \n"
                    "EOR v0.16b, v0.16b, v15.16b \n"
                    "#CTR operations, increment counter and xorbuf \n"
                    "EOR v0.16b, v0.16b, v16.16b \n"
                    "ST1 {v0.2d}, [%[out]], #16 \n"

                    "3: \n"
                    "#store current counter value at the end \n"
                    "ST1 {v17.2d}, %[regOut] \n"


                    :[out] "=r" (out), "=r" (keyPt), [regOut] "=m" (aes->reg),
                     "=r" (in)
                    :"0" (out), [Key] "1" (keyPt), [input] "3" (in),
                     [blocks] "r" (numBlocks), [reg] "m" (aes->reg)
                    : "cc", "memory", "w11", "v0", "v1", "v2", "v3", "v4", "v5",
                    "v6", "v7", "v8", "v9", "v10","v11","v12","v13","v14","v15",
                    "v16", "v17", "v18", "v19"
                    );
                    break;
#endif /* WOLFSSL_AES_256 */
                default:
                    WOLFSSL_MSG("Bad AES-CTR round value");
                    return BAD_FUNC_ARG;
                }

                aes->left = 0;
            }

            /* handle non block size remaining */
            if (sz) {
                wc_AesEncrypt(aes, (byte*)aes->reg, (byte*)aes->tmp);
                IncrementAesCounter((byte*)aes->reg);

                aes->left = AES_BLOCK_SIZE;
                tmp = (byte*)aes->tmp;

                while (sz--) {
                    *(out++) = *(in++) ^ *(tmp++);
                    aes->left--;
                }
            }
            return 0;
        }

#endif /* WOLFSSL_AES_COUNTER */

#ifdef HAVE_AESGCM

/*
 * Based from GCM implementation in wolfcrypt/src/aes.c
 */

/* PMULL and RBIT only with AArch64 */
/* Use ARM hardware for polynomial multiply */
static void GMULT(byte* X, byte* Y)
{
    __asm__ volatile (
        "LD1 {v0.16b}, [%[inX]] \n"
        "LD1 {v1.16b}, [%[inY]] \n" /* v1 already reflected from set key */
        "RBIT v0.16b, v0.16b \n"


        /* Algorithm 1 from Intel GCM white paper.
           "Carry-Less Multiplication and Its Usage for Computing the GCM Mode"
         */
        "PMULL  v3.1q, v0.1d, v1.1d \n"     /* a0 * b0 = C */
        "PMULL2 v4.1q, v0.2d, v1.2d \n"     /* a1 * b1 = D */
        "EXT v5.16b, v1.16b, v1.16b, #8 \n" /* b0b1 -> b1b0 */
        "PMULL  v6.1q, v0.1d, v5.1d \n"     /* a0 * b1 = E */
        "PMULL2 v5.1q, v0.2d, v5.2d \n"     /* a1 * b0 = F */

        "#Set a register to all 0s using EOR \n"
        "EOR v7.16b, v7.16b, v7.16b \n"
        "EOR v5.16b, v5.16b, v6.16b \n"     /* F ^ E */
        "EXT v6.16b, v7.16b, v5.16b, #8 \n" /* get (F^E)[0] */
        "EOR v3.16b, v3.16b, v6.16b \n"     /* low 128 bits in v3 */
        "EXT v6.16b, v5.16b, v7.16b, #8 \n" /* get (F^E)[1] */
        "EOR v4.16b, v4.16b, v6.16b \n"     /* high 128 bits in v4 */


        /* Based from White Paper "Implementing GCM on ARMv8"
           by Conrado P.L. Gouvea and Julio Lopez
           reduction on 256bit value using Algorithm 5 */
        "MOVI v8.16b, #0x87 \n"
        "USHR v8.2d, v8.2d, #56 \n"
        /* v8 is now 0x00000000000000870000000000000087 reflected 0xe1....*/
        "PMULL2 v5.1q, v4.2d, v8.2d \n"
        "EXT v6.16b, v5.16b, v7.16b, #8 \n" /* v7 is all 0's */
        "EOR v4.16b, v4.16b, v6.16b \n"
        "EXT v6.16b, v7.16b, v5.16b, #8 \n"
        "EOR v3.16b, v3.16b, v6.16b \n"
        "PMULL v5.1q, v4.1d, v8.1d  \n"
        "EOR v4.16b, v3.16b, v5.16b \n"

        "RBIT v4.16b, v4.16b \n"
        "STR q4, [%[out]] \n"
        : [out] "=r" (X), "=r" (Y)
        : [inX] "0" (X), [inY] "1" (Y)
        : "cc", "memory", "v0", "v1", "v2", "v3", "v4", "v5", "v6", "v7", "v8"
    );
}


void GHASH(Aes* aes, const byte* a, word32 aSz,
                                const byte* c, word32 cSz, byte* s, word32 sSz)
{
    byte x[AES_BLOCK_SIZE];
    byte scratch[AES_BLOCK_SIZE];
    word32 blocks, partial;
    byte* h = aes->H;

    XMEMSET(x, 0, AES_BLOCK_SIZE);

    /* Hash in A, the Additional Authentication Data */
    if (aSz != 0 && a != NULL) {
        blocks = aSz / AES_BLOCK_SIZE;
        partial = aSz % AES_BLOCK_SIZE;
        /* do as many blocks as possible */
        while (blocks--) {
            xorbuf(x, a, AES_BLOCK_SIZE);
            GMULT(x, h);
            a += AES_BLOCK_SIZE;
        }
        if (partial != 0) {
            XMEMSET(scratch, 0, AES_BLOCK_SIZE);
            XMEMCPY(scratch, a, partial);
            xorbuf(x, scratch, AES_BLOCK_SIZE);
            GMULT(x, h);
        }
    }

    /* Hash in C, the Ciphertext */
    if (cSz != 0 && c != NULL) {
        blocks = cSz / AES_BLOCK_SIZE;
        partial = cSz % AES_BLOCK_SIZE;
        while (blocks--) {
            xorbuf(x, c, AES_BLOCK_SIZE);
            GMULT(x, h);
            c += AES_BLOCK_SIZE;
        }
        if (partial != 0) {
            XMEMSET(scratch, 0, AES_BLOCK_SIZE);
            XMEMCPY(scratch, c, partial);
            xorbuf(x, scratch, AES_BLOCK_SIZE);
            GMULT(x, h);
        }
    }

    /* Hash in the lengths of A and C in bits */
    FlattenSzInBits(&scratch[0], aSz);
    FlattenSzInBits(&scratch[8], cSz);
    xorbuf(x, scratch, AES_BLOCK_SIZE);

    /* Copy the result (minus last GMULT) into s. */
    XMEMCPY(s, x, sSz);
}


#ifdef WOLFSSL_AES_128
/* internal function : see wc_AesGcmEncrypt */
static int Aes128GcmEncrypt(Aes* aes, byte* out, const byte* in, word32 sz,
                   const byte* iv, word32 ivSz,
                   byte* authTag, word32 authTagSz,
                   const byte* authIn, word32 authInSz)
{
    word32 blocks;
    word32 partial;
    byte counter[AES_BLOCK_SIZE];
    byte initialCounter[AES_BLOCK_SIZE];
    byte x[AES_BLOCK_SIZE];
    byte scratch[AES_BLOCK_SIZE];

    /* Noticed different optimization levels treated head of array different.
       Some cases was stack pointer plus offset others was a regester containing
       address. To make uniform for passing in to inline assembly code am using
       pointers to the head of each local array.
     */
    byte* ctr  = counter;
    byte* iCtr = initialCounter;
    byte* xPt  = x;
    byte* sPt  = scratch;
    byte* keyPt; /* pointer to handle pointer advencment */

    XMEMSET(initialCounter, 0, AES_BLOCK_SIZE);
    if (ivSz == GCM_NONCE_MID_SZ) {
        XMEMCPY(initialCounter, iv, ivSz);
        initialCounter[AES_BLOCK_SIZE - 1] = 1;
    }
    else {
        GHASH(aes, NULL, 0, iv, ivSz, initialCounter, AES_BLOCK_SIZE);
        GMULT(initialCounter, aes->H);
    }
    XMEMCPY(counter, initialCounter, AES_BLOCK_SIZE);


    /* Hash in the Additional Authentication Data */
    XMEMSET(x, 0, AES_BLOCK_SIZE);
    if (authInSz != 0 && authIn != NULL) {
        blocks = authInSz / AES_BLOCK_SIZE;
        partial = authInSz % AES_BLOCK_SIZE;
        /* do as many blocks as possible */
        while (blocks--) {
            xorbuf(x, authIn, AES_BLOCK_SIZE);
            GMULT(x, aes->H);
            authIn += AES_BLOCK_SIZE;
        }
        if (partial != 0) {
            XMEMSET(scratch, 0, AES_BLOCK_SIZE);
            XMEMCPY(scratch, authIn, partial);
            xorbuf(x, scratch, AES_BLOCK_SIZE);
            GMULT(x, aes->H);
        }
    }

    /* do as many blocks as possible */
    blocks = sz / AES_BLOCK_SIZE;
    partial = sz % AES_BLOCK_SIZE;
    if (blocks > 0) {
        keyPt  = (byte*)aes->key;
        __asm__ __volatile__ (
            "MOV w11, %w[blocks] \n"
            "LD1 {v13.2d}, [%[ctr]] \n"

            "#Create vector with the value 1  \n"
            "MOVI v14.16b, #1                 \n"
            "USHR v14.2d, v14.2d, #56         \n"
            "EOR v22.16b, v22.16b, v22.16b    \n"
            "EXT v14.16b, v14.16b, v22.16b, #8\n"


            /***************************************************
               Get first out block for GHASH using AES encrypt
             ***************************************************/
            "REV64 v13.16b, v13.16b \n" /* network order */
            "LD1 {v1.2d-v4.2d}, [%[Key]], #64 \n"
            "EXT v13.16b, v13.16b, v13.16b, #8 \n"
            "ADD v13.2d, v13.2d, v14.2d \n" /* add 1 to counter */
            "EXT v13.16b, v13.16b, v13.16b, #8 \n"
            "REV64 v13.16b, v13.16b \n" /* revert from network order */
            "LD1 {v5.2d-v8.2d}, [%[Key]], #64 \n"
            "MOV v0.16b, v13.16b  \n"
            "AESE v0.16b, v1.16b  \n"
            "AESMC v0.16b, v0.16b \n"
            "AESE v0.16b, v2.16b  \n"
            "AESMC v0.16b, v0.16b \n"
            "AESE v0.16b, v3.16b  \n"
            "AESMC v0.16b, v0.16b \n"
            "LD1 {v16.2d}, %[inY] \n"
            "AESE v0.16b, v4.16b  \n"
            "AESMC v0.16b, v0.16b \n"
            "SUB w11, w11, #1     \n"
            "LD1 {v9.2d-v11.2d}, [%[Key]], #48\n"
            "AESE v0.16b, v5.16b  \n"
            "AESMC v0.16b, v0.16b \n"
            "MOVI v23.16b, #0x87 \n"
            "AESE v0.16b, v6.16b  \n"
            "AESMC v0.16b, v0.16b \n"
            "LD1 {v17.2d}, [%[inX]] \n" /* account for additional data */
            "AESE v0.16b, v7.16b  \n"
            "AESMC v0.16b, v0.16b \n"
            "USHR v23.2d, v23.2d, #56 \n"
            "AESE v0.16b, v8.16b  \n"
            "AESMC v0.16b, v0.16b \n"
            "LD1 {v12.2d}, [%[input]], #16 \n"
            "AESE v0.16b, v9.16b  \n"
            "AESMC v0.16b, v0.16b \n"
            "AESE v0.16b, v10.16b \n"
            "EOR v0.16b, v0.16b, v11.16b \n"

            "EOR v0.16b, v0.16b, v12.16b \n"
            "ST1 {v0.2d}, [%[out]], #16  \n"
            "MOV v15.16b, v0.16b \n"

            "CBZ w11, 1f \n" /* only one block jump to final GHASH */

            "LD1 {v12.2d}, [%[input]], #16 \n"

            /***************************************************
               Interweave GHASH and encrypt if more then 1 block
             ***************************************************/
            "2: \n"
            "REV64 v13.16b, v13.16b \n" /* network order */
            "EOR v15.16b, v17.16b, v15.16b \n"
            "EXT v13.16b, v13.16b, v13.16b, #8 \n"
            "ADD v13.2d, v13.2d, v14.2d \n" /* add 1 to counter */
            "RBIT v15.16b, v15.16b \n" /* v15 is encrypted out block (c) */
            "EXT v13.16b, v13.16b, v13.16b, #8 \n"
            "REV64 v13.16b, v13.16b \n" /* revert from network order */
            "PMULL  v18.1q, v15.1d, v16.1d \n"     /* a0 * b0 = C */
            "MOV v0.16b, v13.16b  \n"
            "PMULL2 v19.1q, v15.2d, v16.2d \n"     /* a1 * b1 = D */
            "AESE v0.16b, v1.16b  \n"
            "AESMC v0.16b, v0.16b \n"
            "EXT v20.16b, v16.16b, v16.16b, #8 \n" /* b0b1 -> b1b0 */
            "AESE v0.16b, v2.16b  \n"
            "AESMC v0.16b, v0.16b \n"
            "PMULL  v21.1q, v15.1d, v20.1d \n"     /* a0 * b1 = E */
            "PMULL2 v20.1q, v15.2d, v20.2d \n"     /* a1 * b0 = F */
            "AESE v0.16b, v3.16b  \n"
            "AESMC v0.16b, v0.16b \n"
            "EOR v20.16b, v20.16b, v21.16b \n"     /* F ^ E */
            "AESE v0.16b, v4.16b  \n"
            "AESMC v0.16b, v0.16b \n"
            "EXT v21.16b, v22.16b, v20.16b, #8 \n" /* get (F^E)[0] */
            "SUB w11, w11, #1     \n"
            "AESE v0.16b, v5.16b  \n"
            "AESMC v0.16b, v0.16b \n"
            "EOR v18.16b, v18.16b, v21.16b \n"     /* low 128 bits in v3 */
            "EXT v21.16b, v20.16b, v22.16b, #8 \n" /* get (F^E)[1] */
            "AESE v0.16b, v6.16b  \n"
            "AESMC v0.16b, v0.16b \n"
            "EOR v19.16b, v19.16b, v21.16b \n"     /* high 128 bits in v4 */
            "AESE v0.16b, v7.16b  \n"
            "AESMC v0.16b, v0.16b \n"
            "PMULL2 v20.1q, v19.2d, v23.2d \n"
            "AESE v0.16b, v8.16b  \n"
            "AESMC v0.16b, v0.16b \n"
            "EXT v21.16b, v20.16b, v22.16b, #8 \n" /* v22 is all 0's */
            "AESE v0.16b, v9.16b  \n"
            "AESMC v0.16b, v0.16b \n"
            "EOR v19.16b, v19.16b, v21.16b \n"
            "AESE v0.16b, v10.16b \n"
            "EXT v21.16b, v22.16b, v20.16b, #8 \n"
            "EOR v0.16b, v0.16b, v11.16b \n"
            "EOR v18.16b, v18.16b, v21.16b \n"

            "EOR v0.16b, v0.16b, v12.16b \n"
            "PMULL v20.1q, v19.1d, v23.1d  \n"
            "ST1 {v0.2d}, [%[out]], #16  \n"
            "EOR v19.16b, v18.16b, v20.16b \n"
            "MOV v15.16b, v0.16b \n"
            "RBIT v17.16b, v19.16b \n"

            "CBZ w11, 1f \n"
            "LD1 {v12.2d}, [%[input]], #16 \n"
            "B 2b \n"

            /***************************************************
               GHASH on last block
             ***************************************************/
            "1: \n"
            "EOR v15.16b, v17.16b, v15.16b \n"
            "RBIT v15.16b, v15.16b \n" /* v15 is encrypted out block */

            "#store current AES counter value \n"
            "ST1 {v13.2d}, [%[ctrOut]] \n"
            "PMULL  v18.1q, v15.1d, v16.1d \n"     /* a0 * b0 = C */
            "PMULL2 v19.1q, v15.2d, v16.2d \n"     /* a1 * b1 = D */
            "EXT v20.16b, v16.16b, v16.16b, #8 \n" /* b0b1 -> b1b0 */
            "PMULL  v21.1q, v15.1d, v20.1d \n"     /* a0 * b1 = E */
            "PMULL2 v20.1q, v15.2d, v20.2d \n"     /* a1 * b0 = F */
            "EOR v20.16b, v20.16b, v21.16b \n"     /* F ^ E */
            "EXT v21.16b, v22.16b, v20.16b, #8 \n" /* get (F^E)[0] */
            "EOR v18.16b, v18.16b, v21.16b \n"     /* low 128 bits in v3 */
            "EXT v21.16b, v20.16b, v22.16b, #8 \n" /* get (F^E)[1] */
            "EOR v19.16b, v19.16b, v21.16b \n"     /* high 128 bits in v4 */

            "#Reduce product from multiplication \n"
            "PMULL2 v20.1q, v19.2d, v23.2d \n"
            "EXT v21.16b, v20.16b, v22.16b, #8 \n" /* v22 is all 0's */
            "EOR v19.16b, v19.16b, v21.16b \n"
            "EXT v21.16b, v22.16b, v20.16b, #8 \n"
            "EOR v18.16b, v18.16b, v21.16b \n"
            "PMULL v20.1q, v19.1d, v23.1d  \n"
            "EOR v19.16b, v18.16b, v20.16b \n"
            "RBIT v17.16b, v19.16b \n"
            "STR q17, [%[xOut]] \n" /* GHASH x value for partial blocks */

            :[out] "=r" (out), "=r" (keyPt), [ctrOut] "=r" (ctr), "=r" (in)
            ,[xOut] "=r" (xPt),"=m" (aes->H)
            :"0" (out), [Key] "1" (keyPt), [ctr] "2" (ctr), [blocks] "r" (blocks),
             [input] "3" (in)
            ,[inX] "4" (xPt), [inY] "m" (aes->H)
            : "cc", "w11", "v0", "v1", "v2", "v3", "v4", "v5",
            "v6", "v7", "v8", "v9", "v10", "v11", "v12", "v13", "v14"
            ,"v15", "v16", "v17", "v18", "v19", "v20", "v21", "v22", "v23", "v24"
        );
    }

    /* take care of partial block sizes leftover */
    if (partial != 0) {
        IncrementGcmCounter(counter);
        wc_AesEncrypt(aes, counter, scratch);
        xorbuf(scratch, in, partial);
        XMEMCPY(out, scratch, partial);

        XMEMSET(scratch, 0, AES_BLOCK_SIZE);
        XMEMCPY(scratch, out, partial);
        xorbuf(x, scratch, AES_BLOCK_SIZE);
        GMULT(x, aes->H);
    }

    /* Hash in the lengths of A and C in bits */
    XMEMSET(scratch, 0, AES_BLOCK_SIZE);
    FlattenSzInBits(&scratch[0], authInSz);
    FlattenSzInBits(&scratch[8], sz);
    xorbuf(x, scratch, AES_BLOCK_SIZE);
    XMEMCPY(scratch, x, AES_BLOCK_SIZE);

    keyPt  = (byte*)aes->key;
    __asm__ __volatile__ (

        "LD1 {v16.16b}, [%[tag]] \n"
        "LD1 {v17.16b}, %[h] \n"
        "RBIT v16.16b, v16.16b \n"

        "LD1 {v1.2d-v4.2d}, [%[Key]], #64 \n"
        "PMULL  v18.1q, v16.1d, v17.1d \n"     /* a0 * b0 = C */
        "PMULL2 v19.1q, v16.2d, v17.2d \n"     /* a1 * b1 = D */
        "LD1 {v5.2d-v8.2d}, [%[Key]], #64 \n"
        "EXT v20.16b, v17.16b, v17.16b, #8 \n" /* b0b1 -> b1b0 */
        "LD1 {v9.2d-v11.2d}, [%[Key]], #48\n"
        "PMULL  v21.1q, v16.1d, v20.1d \n"     /* a0 * b1 = E */
        "PMULL2 v20.1q, v16.2d, v20.2d \n"     /* a1 * b0 = F */
        "LD1 {v0.2d}, [%[ctr]]             \n"

        "#Set a register to all 0s using EOR \n"
        "EOR v22.16b, v22.16b, v22.16b \n"
        "EOR v20.16b, v20.16b, v21.16b \n"     /* F ^ E */
        "AESE v0.16b, v1.16b  \n"
        "AESMC v0.16b, v0.16b \n"
        "EXT v21.16b, v22.16b, v20.16b, #8 \n" /* get (F^E)[0] */
        "AESE v0.16b, v2.16b  \n"
        "AESMC v0.16b, v0.16b \n"
        "EOR v18.16b, v18.16b, v21.16b \n"     /* low 128 bits in v3 */
        "EXT v21.16b, v20.16b, v22.16b, #8 \n" /* get (F^E)[1] */
        "AESE v0.16b, v3.16b  \n"
        "AESMC v0.16b, v0.16b \n"
        "EOR v19.16b, v19.16b, v21.16b \n"     /* high 128 bits in v4 */
        "MOVI v23.16b, #0x87 \n"
        "AESE v0.16b, v4.16b  \n"
        "AESMC v0.16b, v0.16b \n"
        "USHR v23.2d, v23.2d, #56 \n"
        "PMULL2 v20.1q, v19.2d, v23.2d \n"
        "AESE v0.16b, v5.16b  \n"
        "AESMC v0.16b, v0.16b \n"
        "EXT v21.16b, v20.16b, v22.16b, #8 \n"
        "AESE v0.16b, v6.16b  \n"
        "AESMC v0.16b, v0.16b \n"
        "EOR v19.16b, v19.16b, v21.16b \n"
        "AESE v0.16b, v7.16b  \n"
        "AESMC v0.16b, v0.16b \n"
        "EXT v21.16b, v22.16b, v20.16b, #8 \n"
        "AESE v0.16b, v8.16b  \n"
        "AESMC v0.16b, v0.16b \n"
        "EOR v18.16b, v18.16b, v21.16b \n"
        "AESE v0.16b, v9.16b  \n"
        "AESMC v0.16b, v0.16b \n"
        "PMULL v20.1q, v19.1d, v23.1d  \n"
        "EOR v19.16b, v18.16b, v20.16b \n"
        "AESE v0.16b, v10.16b \n"
        "RBIT v19.16b, v19.16b \n"
        "EOR v0.16b, v0.16b, v11.16b \n"
        "EOR v19.16b, v19.16b, v0.16b \n"
        "STR q19, [%[out]] \n"

        :[out] "=r" (sPt), "=r" (keyPt), "=r" (iCtr)
        :[tag] "0" (sPt), [Key] "1" (keyPt),
        [ctr] "2" (iCtr) , [h] "m" (aes->H)
        : "cc", "memory", "v0", "v1", "v2", "v3", "v4", "v5",
        "v6", "v7", "v8", "v9", "v10","v11","v12","v13","v14",
        "v15", "v16", "v17","v18", "v19", "v20","v21","v22","v23","v24"
    );


    if (authTagSz > AES_BLOCK_SIZE) {
        XMEMCPY(authTag, scratch, AES_BLOCK_SIZE);
    }
    else {
        /* authTagSz can be smaller than AES_BLOCK_SIZE */
        XMEMCPY(authTag, scratch, authTagSz);
    }
    return 0;
}
#endif /* WOLFSSL_AES_128 */

#ifdef WOLFSSL_AES_192
/* internal function : see wc_AesGcmEncrypt */
static int Aes192GcmEncrypt(Aes* aes, byte* out, const byte* in, word32 sz,
                   const byte* iv, word32 ivSz,
                   byte* authTag, word32 authTagSz,
                   const byte* authIn, word32 authInSz)
{
    word32 blocks;
    word32 partial;
    byte counter[AES_BLOCK_SIZE];
    byte initialCounter[AES_BLOCK_SIZE];
    byte x[AES_BLOCK_SIZE];
    byte scratch[AES_BLOCK_SIZE];

    /* Noticed different optimization levels treated head of array different.
       Some cases was stack pointer plus offset others was a regester containing
       address. To make uniform for passing in to inline assembly code am using
       pointers to the head of each local array.
     */
    byte* ctr  = counter;
    byte* iCtr = initialCounter;
    byte* xPt  = x;
    byte* sPt  = scratch;
    byte* keyPt; /* pointer to handle pointer advencment */

    XMEMSET(initialCounter, 0, AES_BLOCK_SIZE);
    if (ivSz == GCM_NONCE_MID_SZ) {
        XMEMCPY(initialCounter, iv, ivSz);
        initialCounter[AES_BLOCK_SIZE - 1] = 1;
    }
    else {
        GHASH(aes, NULL, 0, iv, ivSz, initialCounter, AES_BLOCK_SIZE);
        GMULT(initialCounter, aes->H);
    }
    XMEMCPY(counter, initialCounter, AES_BLOCK_SIZE);


    /* Hash in the Additional Authentication Data */
    XMEMSET(x, 0, AES_BLOCK_SIZE);
    if (authInSz != 0 && authIn != NULL) {
        blocks = authInSz / AES_BLOCK_SIZE;
        partial = authInSz % AES_BLOCK_SIZE;
        /* do as many blocks as possible */
        while (blocks--) {
            xorbuf(x, authIn, AES_BLOCK_SIZE);
            GMULT(x, aes->H);
            authIn += AES_BLOCK_SIZE;
        }
        if (partial != 0) {
            XMEMSET(scratch, 0, AES_BLOCK_SIZE);
            XMEMCPY(scratch, authIn, partial);
            xorbuf(x, scratch, AES_BLOCK_SIZE);
            GMULT(x, aes->H);
        }
    }

    /* do as many blocks as possible */
    blocks = sz / AES_BLOCK_SIZE;
    partial = sz % AES_BLOCK_SIZE;
    if (blocks > 0) {
        keyPt  = (byte*)aes->key;
        __asm__ __volatile__ (
            "MOV w11, %w[blocks] \n"
            "LD1 {v13.2d}, [%[ctr]] \n"

            "#Create vector with the value 1  \n"
            "MOVI v14.16b, #1                 \n"
            "USHR v14.2d, v14.2d, #56         \n"
            "EOR v22.16b, v22.16b, v22.16b    \n"
            "EXT v14.16b, v14.16b, v22.16b, #8\n"


            /***************************************************
               Get first out block for GHASH using AES encrypt
             ***************************************************/
            "REV64 v13.16b, v13.16b \n" /* network order */
            "LD1 {v1.2d-v4.2d}, [%[Key]], #64 \n"
            "EXT v13.16b, v13.16b, v13.16b, #8 \n"
            "ADD v13.2d, v13.2d, v14.2d \n" /* add 1 to counter */
            "EXT v13.16b, v13.16b, v13.16b, #8 \n"
            "REV64 v13.16b, v13.16b \n" /* revert from network order */
            "LD1 {v5.2d-v8.2d}, [%[Key]], #64 \n"
            "MOV v0.16b, v13.16b  \n"
            "AESE v0.16b, v1.16b  \n"
            "AESMC v0.16b, v0.16b \n"
            "AESE v0.16b, v2.16b  \n"
            "AESMC v0.16b, v0.16b \n"
            "AESE v0.16b, v3.16b  \n"
            "AESMC v0.16b, v0.16b \n"
            "LD1 {v16.2d}, %[inY] \n"
            "AESE v0.16b, v4.16b  \n"
            "AESMC v0.16b, v0.16b \n"
            "SUB w11, w11, #1     \n"
            "LD1 {v9.2d-v11.2d}, [%[Key]], #48\n"
            "LD1 {v30.2d-v31.2d}, [%[Key]], #32\n"
            "AESE v0.16b, v5.16b  \n"
            "AESMC v0.16b, v0.16b \n"
            "MOVI v23.16b, #0x87 \n"
            "AESE v0.16b, v6.16b  \n"
            "AESMC v0.16b, v0.16b \n"
            "LD1 {v17.2d}, [%[inX]] \n" /* account for additional data */
            "AESE v0.16b, v7.16b  \n"
            "AESMC v0.16b, v0.16b \n"
            "USHR v23.2d, v23.2d, #56 \n"
            "AESE v0.16b, v8.16b  \n"
            "AESMC v0.16b, v0.16b \n"
            "LD1 {v12.2d}, [%[input]], #16 \n"
            "AESE v0.16b, v9.16b  \n"
            "AESMC v0.16b, v0.16b \n"
            "AESE v0.16b, v10.16b  \n"
            "AESMC v0.16b, v0.16b \n"
            "AESE v0.16b, v11.16b  \n"
            "AESMC v0.16b, v0.16b \n"
            "AESE v0.16b, v30.16b \n"
            "EOR v0.16b, v0.16b, v31.16b \n"

            "EOR v0.16b, v0.16b, v12.16b \n"
            "ST1 {v0.2d}, [%[out]], #16  \n"
            "MOV v15.16b, v0.16b \n"

            "CBZ w11, 1f \n" /* only one block jump to final GHASH */
            "LD1 {v12.2d}, [%[input]], #16 \n"

            /***************************************************
               Interweave GHASH and encrypt if more then 1 block
             ***************************************************/
            "2: \n"
            "REV64 v13.16b, v13.16b \n" /* network order */
            "EOR v15.16b, v17.16b, v15.16b \n"
            "EXT v13.16b, v13.16b, v13.16b, #8 \n"
            "ADD v13.2d, v13.2d, v14.2d \n" /* add 1 to counter */
            "RBIT v15.16b, v15.16b \n" /* v15 is encrypted out block (c) */
            "EXT v13.16b, v13.16b, v13.16b, #8 \n"
            "REV64 v13.16b, v13.16b \n" /* revert from network order */
            "PMULL  v18.1q, v15.1d, v16.1d \n"     /* a0 * b0 = C */
            "MOV v0.16b, v13.16b  \n"
            "PMULL2 v19.1q, v15.2d, v16.2d \n"     /* a1 * b1 = D */
            "AESE v0.16b, v1.16b  \n"
            "AESMC v0.16b, v0.16b \n"
            "EXT v20.16b, v16.16b, v16.16b, #8 \n" /* b0b1 -> b1b0 */
            "AESE v0.16b, v2.16b  \n"
            "AESMC v0.16b, v0.16b \n"
            "PMULL  v21.1q, v15.1d, v20.1d \n"     /* a0 * b1 = E */
            "PMULL2 v20.1q, v15.2d, v20.2d \n"     /* a1 * b0 = F */
            "AESE v0.16b, v3.16b  \n"
            "AESMC v0.16b, v0.16b \n"
            "EOR v20.16b, v20.16b, v21.16b \n"     /* F ^ E */
            "AESE v0.16b, v4.16b  \n"
            "AESMC v0.16b, v0.16b \n"
            "EXT v21.16b, v22.16b, v20.16b, #8 \n" /* get (F^E)[0] */
            "SUB w11, w11, #1     \n"
            "AESE v0.16b, v5.16b  \n"
            "AESMC v0.16b, v0.16b \n"
            "EOR v18.16b, v18.16b, v21.16b \n"     /* low 128 bits in v3 */
            "EXT v21.16b, v20.16b, v22.16b, #8 \n" /* get (F^E)[1] */
            "AESE v0.16b, v6.16b  \n"
            "AESMC v0.16b, v0.16b \n"
            "EOR v19.16b, v19.16b, v21.16b \n"     /* high 128 bits in v4 */
            "AESE v0.16b, v7.16b  \n"
            "AESMC v0.16b, v0.16b \n"
            "PMULL2 v20.1q, v19.2d, v23.2d \n"
            "AESE v0.16b, v8.16b  \n"
            "AESMC v0.16b, v0.16b \n"
            "EXT v21.16b, v20.16b, v22.16b, #8 \n" /* v22 is all 0's */
            "AESE v0.16b, v9.16b  \n"
            "AESMC v0.16b, v0.16b \n"
            "AESE v0.16b, v10.16b  \n"
            "AESMC v0.16b, v0.16b \n"
            "AESE v0.16b, v11.16b  \n"
            "AESMC v0.16b, v0.16b \n"
            "EOR v19.16b, v19.16b, v21.16b \n"
            "AESE v0.16b, v30.16b \n"
            "EXT v21.16b, v22.16b, v20.16b, #8 \n"
            "EOR v0.16b, v0.16b, v31.16b \n"
            "EOR v18.16b, v18.16b, v21.16b \n"

            "EOR v0.16b, v0.16b, v12.16b \n"
            "PMULL v20.1q, v19.1d, v23.1d  \n"
            "ST1 {v0.2d}, [%[out]], #16  \n"
            "EOR v19.16b, v18.16b, v20.16b \n"
            "MOV v15.16b, v0.16b \n"
            "RBIT v17.16b, v19.16b \n"

            "CBZ w11, 1f \n"
            "LD1 {v12.2d}, [%[input]], #16 \n"
            "B 2b \n"

            /***************************************************
               GHASH on last block
             ***************************************************/
            "1: \n"
            "EOR v15.16b, v17.16b, v15.16b \n"
            "RBIT v15.16b, v15.16b \n" /* v15 is encrypted out block */

            "#store current AES counter value \n"
            "ST1 {v13.2d}, [%[ctrOut]] \n"
            "PMULL  v18.1q, v15.1d, v16.1d \n"     /* a0 * b0 = C */
            "PMULL2 v19.1q, v15.2d, v16.2d \n"     /* a1 * b1 = D */
            "EXT v20.16b, v16.16b, v16.16b, #8 \n" /* b0b1 -> b1b0 */
            "PMULL  v21.1q, v15.1d, v20.1d \n"     /* a0 * b1 = E */
            "PMULL2 v20.1q, v15.2d, v20.2d \n"     /* a1 * b0 = F */
            "EOR v20.16b, v20.16b, v21.16b \n"     /* F ^ E */
            "EXT v21.16b, v22.16b, v20.16b, #8 \n" /* get (F^E)[0] */
            "EOR v18.16b, v18.16b, v21.16b \n"     /* low 128 bits in v3 */
            "EXT v21.16b, v20.16b, v22.16b, #8 \n" /* get (F^E)[1] */
            "EOR v19.16b, v19.16b, v21.16b \n"     /* high 128 bits in v4 */

            "#Reduce product from multiplication \n"
            "PMULL2 v20.1q, v19.2d, v23.2d \n"
            "EXT v21.16b, v20.16b, v22.16b, #8 \n" /* v22 is all 0's */
            "EOR v19.16b, v19.16b, v21.16b \n"
            "EXT v21.16b, v22.16b, v20.16b, #8 \n"
            "EOR v18.16b, v18.16b, v21.16b \n"
            "PMULL v20.1q, v19.1d, v23.1d  \n"
            "EOR v19.16b, v18.16b, v20.16b \n"
            "RBIT v17.16b, v19.16b \n"
            "STR q17, [%[xOut]] \n" /* GHASH x value for partial blocks */

            :[out] "=r" (out), "=r" (keyPt), [ctrOut] "=r" (ctr), "=r" (in)
            ,[xOut] "=r" (xPt),"=m" (aes->H)
            :"0" (out), [Key] "1" (keyPt), [ctr] "2" (ctr), [blocks] "r" (blocks),
             [input] "3" (in)
            ,[inX] "4" (xPt), [inY] "m" (aes->H)
            : "cc", "w11", "v0", "v1", "v2", "v3", "v4", "v5",
            "v6", "v7", "v8", "v9", "v10", "v11", "v12", "v13", "v14"
            ,"v15", "v16", "v17", "v18", "v19", "v20", "v21", "v22", "v23",
            "v24","v25","v26","v27","v28","v29","v30","v31"
        );
    }

    /* take care of partial block sizes leftover */
    if (partial != 0) {
        IncrementGcmCounter(counter);
        wc_AesEncrypt(aes, counter, scratch);
        xorbuf(scratch, in, partial);
        XMEMCPY(out, scratch, partial);

        XMEMSET(scratch, 0, AES_BLOCK_SIZE);
        XMEMCPY(scratch, out, partial);
        xorbuf(x, scratch, AES_BLOCK_SIZE);
        GMULT(x, aes->H);
    }

    /* Hash in the lengths of A and C in bits */
    XMEMSET(scratch, 0, AES_BLOCK_SIZE);
    FlattenSzInBits(&scratch[0], authInSz);
    FlattenSzInBits(&scratch[8], sz);
    xorbuf(x, scratch, AES_BLOCK_SIZE);
    XMEMCPY(scratch, x, AES_BLOCK_SIZE);

    keyPt  = (byte*)aes->key;
    __asm__ __volatile__ (

        "LD1 {v16.16b}, [%[tag]] \n"
        "LD1 {v17.16b}, %[h] \n"
        "RBIT v16.16b, v16.16b \n"

        "LD1 {v1.2d-v4.2d}, [%[Key]], #64 \n"
        "PMULL  v18.1q, v16.1d, v17.1d \n"     /* a0 * b0 = C */
        "PMULL2 v19.1q, v16.2d, v17.2d \n"     /* a1 * b1 = D */
        "LD1 {v5.2d-v8.2d}, [%[Key]], #64 \n"
        "EXT v20.16b, v17.16b, v17.16b, #8 \n" /* b0b1 -> b1b0 */
        "LD1 {v9.2d-v11.2d}, [%[Key]], #48\n"
        "LD1 {v30.2d-v31.2d}, [%[Key]], #32\n"
        "PMULL  v21.1q, v16.1d, v20.1d \n"     /* a0 * b1 = E */
        "PMULL2 v20.1q, v16.2d, v20.2d \n"     /* a1 * b0 = F */
        "LD1 {v0.2d}, [%[ctr]]             \n"

        "#Set a register to all 0s using EOR \n"
        "EOR v22.16b, v22.16b, v22.16b \n"
        "EOR v20.16b, v20.16b, v21.16b \n"     /* F ^ E */
        "AESE v0.16b, v1.16b  \n"
        "AESMC v0.16b, v0.16b \n"
        "EXT v21.16b, v22.16b, v20.16b, #8 \n" /* get (F^E)[0] */
        "AESE v0.16b, v2.16b  \n"
        "AESMC v0.16b, v0.16b \n"
        "EOR v18.16b, v18.16b, v21.16b \n"     /* low 128 bits in v3 */
        "EXT v21.16b, v20.16b, v22.16b, #8 \n" /* get (F^E)[1] */
        "AESE v0.16b, v3.16b  \n"
        "AESMC v0.16b, v0.16b \n"
        "EOR v19.16b, v19.16b, v21.16b \n"     /* high 128 bits in v4 */
        "MOVI v23.16b, #0x87 \n"
        "AESE v0.16b, v4.16b  \n"
        "AESMC v0.16b, v0.16b \n"
        "USHR v23.2d, v23.2d, #56 \n"
        "PMULL2 v20.1q, v19.2d, v23.2d \n"
        "AESE v0.16b, v5.16b  \n"
        "AESMC v0.16b, v0.16b \n"
        "EXT v21.16b, v20.16b, v22.16b, #8 \n"
        "AESE v0.16b, v6.16b  \n"
        "AESMC v0.16b, v0.16b \n"
        "EOR v19.16b, v19.16b, v21.16b \n"
        "AESE v0.16b, v7.16b  \n"
        "AESMC v0.16b, v0.16b \n"
        "EXT v21.16b, v22.16b, v20.16b, #8 \n"
        "AESE v0.16b, v8.16b  \n"
        "AESMC v0.16b, v0.16b \n"
        "EOR v18.16b, v18.16b, v21.16b \n"
        "AESE v0.16b, v9.16b  \n"
        "AESMC v0.16b, v0.16b \n"
        "AESE v0.16b, v10.16b  \n"
        "AESMC v0.16b, v0.16b \n"
        "AESE v0.16b, v11.16b  \n"
        "AESMC v0.16b, v0.16b \n"
        "PMULL v20.1q, v19.1d, v23.1d  \n"
        "EOR v19.16b, v18.16b, v20.16b \n"
        "AESE v0.16b, v30.16b \n"
        "RBIT v19.16b, v19.16b \n"
        "EOR v0.16b, v0.16b, v31.16b \n"
        "EOR v19.16b, v19.16b, v0.16b \n"
        "STR q19, [%[out]] \n"

        :[out] "=r" (sPt), "=r" (keyPt), "=r" (iCtr)
        :[tag] "0" (sPt), [Key] "1" (keyPt),
        [ctr] "2" (iCtr) , [h] "m" (aes->H)
        : "cc", "memory", "v0", "v1", "v2", "v3", "v4", "v5",
        "v6", "v7", "v8", "v9", "v10","v11","v12","v13","v14",
        "v15", "v16", "v17","v18", "v19", "v20","v21","v22","v23","v24"
    );


    if (authTagSz > AES_BLOCK_SIZE) {
        XMEMCPY(authTag, scratch, AES_BLOCK_SIZE);
    }
    else {
        /* authTagSz can be smaller than AES_BLOCK_SIZE */
        XMEMCPY(authTag, scratch, authTagSz);
    }

    return 0;
}
#endif /* WOLFSSL_AES_192 */

#ifdef WOLFSSL_AES_256
/* internal function : see wc_AesGcmEncrypt */
static int Aes256GcmEncrypt(Aes* aes, byte* out, const byte* in, word32 sz,
                   const byte* iv, word32 ivSz,
                   byte* authTag, word32 authTagSz,
                   const byte* authIn, word32 authInSz)
{
    word32 blocks;
    word32 partial;
    byte counter[AES_BLOCK_SIZE];
    byte initialCounter[AES_BLOCK_SIZE];
    byte x[AES_BLOCK_SIZE];
    byte scratch[AES_BLOCK_SIZE];

    /* Noticed different optimization levels treated head of array different.
       Some cases was stack pointer plus offset others was a regester containing
       address. To make uniform for passing in to inline assembly code am using
       pointers to the head of each local array.
     */
    byte* ctr  = counter;
    byte* iCtr = initialCounter;
    byte* xPt  = x;
    byte* sPt  = scratch;
    byte* keyPt; /* pointer to handle pointer advencment */

    XMEMSET(initialCounter, 0, AES_BLOCK_SIZE);
    if (ivSz == GCM_NONCE_MID_SZ) {
        XMEMCPY(initialCounter, iv, ivSz);
        initialCounter[AES_BLOCK_SIZE - 1] = 1;
    }
    else {
        GHASH(aes, NULL, 0, iv, ivSz, initialCounter, AES_BLOCK_SIZE);
        GMULT(initialCounter, aes->H);
    }
    XMEMCPY(counter, initialCounter, AES_BLOCK_SIZE);


    /* Hash in the Additional Authentication Data */
    XMEMSET(x, 0, AES_BLOCK_SIZE);
    if (authInSz != 0 && authIn != NULL) {
        blocks = authInSz / AES_BLOCK_SIZE;
        partial = authInSz % AES_BLOCK_SIZE;
        /* do as many blocks as possible */
        while (blocks--) {
            xorbuf(x, authIn, AES_BLOCK_SIZE);
            GMULT(x, aes->H);
            authIn += AES_BLOCK_SIZE;
        }
        if (partial != 0) {
            XMEMSET(scratch, 0, AES_BLOCK_SIZE);
            XMEMCPY(scratch, authIn, partial);
            xorbuf(x, scratch, AES_BLOCK_SIZE);
            GMULT(x, aes->H);
        }
    }

    /* do as many blocks as possible */
    blocks = sz / AES_BLOCK_SIZE;
    partial = sz % AES_BLOCK_SIZE;
    if (blocks > 0) {
        keyPt  = (byte*)aes->key;
        __asm__ __volatile__ (
            "MOV w11, %w[blocks] \n"
            "LD1 {v13.2d}, [%[ctr]] \n"

            "#Create vector with the value 1  \n"
            "MOVI v14.16b, #1                 \n"
            "USHR v14.2d, v14.2d, #56         \n"
            "EOR v22.16b, v22.16b, v22.16b    \n"
            "EXT v14.16b, v14.16b, v22.16b, #8\n"


            /***************************************************
               Get first out block for GHASH using AES encrypt
             ***************************************************/
            "REV64 v13.16b, v13.16b \n" /* network order */
            "LD1 {v1.2d-v4.2d}, [%[Key]], #64 \n"
            "EXT v13.16b, v13.16b, v13.16b, #8 \n"
            "ADD v13.2d, v13.2d, v14.2d \n" /* add 1 to counter */
            "EXT v13.16b, v13.16b, v13.16b, #8 \n"
            "REV64 v13.16b, v13.16b \n" /* revert from network order */
            "LD1 {v5.2d-v8.2d}, [%[Key]], #64 \n"
            "MOV v0.16b, v13.16b  \n"
            "AESE v0.16b, v1.16b  \n"
            "AESMC v0.16b, v0.16b \n"
            "AESE v0.16b, v2.16b  \n"
            "AESMC v0.16b, v0.16b \n"
            "AESE v0.16b, v3.16b  \n"
            "AESMC v0.16b, v0.16b \n"
            "LD1 {v16.2d}, %[inY] \n"
            "AESE v0.16b, v4.16b  \n"
            "AESMC v0.16b, v0.16b \n"
            "SUB w11, w11, #1     \n"
            "LD1 {v9.2d-v11.2d}, [%[Key]], #48\n"
            "LD1 {v28.2d-v31.2d}, [%[Key]], #64\n"
            "AESE v0.16b, v5.16b  \n"
            "AESMC v0.16b, v0.16b \n"
            "MOVI v23.16b, #0x87 \n"
            "AESE v0.16b, v6.16b  \n"
            "AESMC v0.16b, v0.16b \n"
            "LD1 {v17.2d}, [%[inX]] \n" /* account for additional data */
            "AESE v0.16b, v7.16b  \n"
            "AESMC v0.16b, v0.16b \n"
            "USHR v23.2d, v23.2d, #56 \n"
            "AESE v0.16b, v8.16b  \n"
            "AESMC v0.16b, v0.16b \n"
            "LD1 {v12.2d}, [%[input]], #16 \n"
            "AESE v0.16b, v9.16b  \n"
            "AESMC v0.16b, v0.16b \n"
            "AESE v0.16b, v10.16b  \n"
            "AESMC v0.16b, v0.16b \n"
            "AESE v0.16b, v11.16b  \n"
            "AESMC v0.16b, v0.16b \n"
            "AESE v0.16b, v28.16b  \n"
            "AESMC v0.16b, v0.16b \n"
            "AESE v0.16b, v29.16b  \n"
            "AESMC v0.16b, v0.16b \n"
            "AESE v0.16b, v30.16b \n"
            "EOR v0.16b, v0.16b, v31.16b \n"

            "EOR v0.16b, v0.16b, v12.16b \n"
            "ST1 {v0.2d}, [%[out]], #16  \n"
            "MOV v15.16b, v0.16b \n"

            "CBZ w11, 1f \n" /* only one block jump to final GHASH */
            "LD1 {v12.2d}, [%[input]], #16 \n"

            /***************************************************
               Interweave GHASH and encrypt if more then 1 block
             ***************************************************/
            "2: \n"
            "REV64 v13.16b, v13.16b \n" /* network order */
            "EOR v15.16b, v17.16b, v15.16b \n"
            "EXT v13.16b, v13.16b, v13.16b, #8 \n"
            "ADD v13.2d, v13.2d, v14.2d \n" /* add 1 to counter */
            "RBIT v15.16b, v15.16b \n" /* v15 is encrypted out block (c) */
            "EXT v13.16b, v13.16b, v13.16b, #8 \n"
            "REV64 v13.16b, v13.16b \n" /* revert from network order */
            "PMULL  v18.1q, v15.1d, v16.1d \n"     /* a0 * b0 = C */
            "MOV v0.16b, v13.16b  \n"
            "PMULL2 v19.1q, v15.2d, v16.2d \n"     /* a1 * b1 = D */
            "AESE v0.16b, v1.16b  \n"
            "AESMC v0.16b, v0.16b \n"
            "EXT v20.16b, v16.16b, v16.16b, #8 \n" /* b0b1 -> b1b0 */
            "AESE v0.16b, v2.16b  \n"
            "AESMC v0.16b, v0.16b \n"
            "PMULL  v21.1q, v15.1d, v20.1d \n"     /* a0 * b1 = E */
            "PMULL2 v20.1q, v15.2d, v20.2d \n"     /* a1 * b0 = F */
            "AESE v0.16b, v3.16b  \n"
            "AESMC v0.16b, v0.16b \n"
            "EOR v20.16b, v20.16b, v21.16b \n"     /* F ^ E */
            "AESE v0.16b, v4.16b  \n"
            "AESMC v0.16b, v0.16b \n"
            "EXT v21.16b, v22.16b, v20.16b, #8 \n" /* get (F^E)[0] */
            "SUB w11, w11, #1     \n"
            "AESE v0.16b, v5.16b  \n"
            "AESMC v0.16b, v0.16b \n"
            "EOR v18.16b, v18.16b, v21.16b \n"     /* low 128 bits in v3 */
            "EXT v21.16b, v20.16b, v22.16b, #8 \n" /* get (F^E)[1] */
            "AESE v0.16b, v6.16b  \n"
            "AESMC v0.16b, v0.16b \n"
            "EOR v19.16b, v19.16b, v21.16b \n"     /* high 128 bits in v4 */
            "AESE v0.16b, v7.16b  \n"
            "AESMC v0.16b, v0.16b \n"
            "PMULL2 v20.1q, v19.2d, v23.2d \n"
            "AESE v0.16b, v8.16b  \n"
            "AESMC v0.16b, v0.16b \n"
            "EXT v21.16b, v20.16b, v22.16b, #8 \n" /* v22 is all 0's */
            "AESE v0.16b, v9.16b  \n"
            "AESMC v0.16b, v0.16b \n"
            "AESE v0.16b, v10.16b  \n"
            "AESMC v0.16b, v0.16b \n"
            "AESE v0.16b, v11.16b  \n"
            "AESMC v0.16b, v0.16b \n"
            "AESE v0.16b, v28.16b  \n"
            "AESMC v0.16b, v0.16b \n"
            "AESE v0.16b, v29.16b  \n"
            "AESMC v0.16b, v0.16b \n"
            "EOR v19.16b, v19.16b, v21.16b \n"
            "AESE v0.16b, v30.16b \n"
            "EXT v21.16b, v22.16b, v20.16b, #8 \n"
            "EOR v0.16b, v0.16b, v31.16b \n"
            "EOR v18.16b, v18.16b, v21.16b \n"

            "EOR v0.16b, v0.16b, v12.16b \n"
            "PMULL v20.1q, v19.1d, v23.1d  \n"
            "ST1 {v0.2d}, [%[out]], #16  \n"
            "EOR v19.16b, v18.16b, v20.16b \n"
            "MOV v15.16b, v0.16b \n"
            "RBIT v17.16b, v19.16b \n"

            "CBZ w11, 1f \n"
            "LD1 {v12.2d}, [%[input]], #16 \n"
            "B 2b \n"

            /***************************************************
               GHASH on last block
             ***************************************************/
            "1: \n"
            "EOR v15.16b, v17.16b, v15.16b \n"
            "RBIT v15.16b, v15.16b \n" /* v15 is encrypted out block */

            "#store current AES counter value \n"
            "ST1 {v13.2d}, [%[ctrOut]] \n"
            "PMULL  v18.1q, v15.1d, v16.1d \n"     /* a0 * b0 = C */
            "PMULL2 v19.1q, v15.2d, v16.2d \n"     /* a1 * b1 = D */
            "EXT v20.16b, v16.16b, v16.16b, #8 \n" /* b0b1 -> b1b0 */
            "PMULL  v21.1q, v15.1d, v20.1d \n"     /* a0 * b1 = E */
            "PMULL2 v20.1q, v15.2d, v20.2d \n"     /* a1 * b0 = F */
            "EOR v20.16b, v20.16b, v21.16b \n"     /* F ^ E */
            "EXT v21.16b, v22.16b, v20.16b, #8 \n" /* get (F^E)[0] */
            "EOR v18.16b, v18.16b, v21.16b \n"     /* low 128 bits in v3 */
            "EXT v21.16b, v20.16b, v22.16b, #8 \n" /* get (F^E)[1] */
            "EOR v19.16b, v19.16b, v21.16b \n"     /* high 128 bits in v4 */

            "#Reduce product from multiplication \n"
            "PMULL2 v20.1q, v19.2d, v23.2d \n"
            "EXT v21.16b, v20.16b, v22.16b, #8 \n" /* v22 is all 0's */
            "EOR v19.16b, v19.16b, v21.16b \n"
            "EXT v21.16b, v22.16b, v20.16b, #8 \n"
            "EOR v18.16b, v18.16b, v21.16b \n"
            "PMULL v20.1q, v19.1d, v23.1d  \n"
            "EOR v19.16b, v18.16b, v20.16b \n"
            "RBIT v17.16b, v19.16b \n"
            "STR q17, [%[xOut]] \n" /* GHASH x value for partial blocks */

            :[out] "=r" (out), "=r" (keyPt), [ctrOut] "=r" (ctr), "=r" (in)
            ,[xOut] "=r" (xPt),"=m" (aes->H)
            :"0" (out), [Key] "1" (keyPt), [ctr] "2" (ctr), [blocks] "r" (blocks),
             [input] "3" (in)
            ,[inX] "4" (xPt), [inY] "m" (aes->H)
            : "cc", "w11", "v0", "v1", "v2", "v3", "v4", "v5",
            "v6", "v7", "v8", "v9", "v10", "v11", "v12", "v13", "v14"
            ,"v15", "v16", "v17", "v18", "v19", "v20", "v21", "v22", "v23", "v24"
        );
    }

    /* take care of partial block sizes leftover */
    if (partial != 0) {
        IncrementGcmCounter(counter);
        wc_AesEncrypt(aes, counter, scratch);
        xorbuf(scratch, in, partial);
        XMEMCPY(out, scratch, partial);

        XMEMSET(scratch, 0, AES_BLOCK_SIZE);
        XMEMCPY(scratch, out, partial);
        xorbuf(x, scratch, AES_BLOCK_SIZE);
        GMULT(x, aes->H);
    }

    /* Hash in the lengths of A and C in bits */
    XMEMSET(scratch, 0, AES_BLOCK_SIZE);
    FlattenSzInBits(&scratch[0], authInSz);
    FlattenSzInBits(&scratch[8], sz);
    xorbuf(x, scratch, AES_BLOCK_SIZE);
    XMEMCPY(scratch, x, AES_BLOCK_SIZE);

    keyPt  = (byte*)aes->key;
    __asm__ __volatile__ (

        "LD1 {v16.16b}, [%[tag]] \n"
        "LD1 {v17.16b}, %[h] \n"
        "RBIT v16.16b, v16.16b \n"

        "LD1 {v1.2d-v4.2d}, [%[Key]], #64 \n"
        "PMULL  v18.1q, v16.1d, v17.1d \n"     /* a0 * b0 = C */
        "PMULL2 v19.1q, v16.2d, v17.2d \n"     /* a1 * b1 = D */
        "LD1 {v5.2d-v8.2d}, [%[Key]], #64 \n"
        "EXT v20.16b, v17.16b, v17.16b, #8 \n" /* b0b1 -> b1b0 */
        "LD1 {v9.2d-v11.2d}, [%[Key]], #48\n"
        "LD1 {v28.2d-v31.2d}, [%[Key]], #64\n"
        "PMULL  v21.1q, v16.1d, v20.1d \n"     /* a0 * b1 = E */
        "PMULL2 v20.1q, v16.2d, v20.2d \n"     /* a1 * b0 = F */
        "LD1 {v0.2d}, [%[ctr]]             \n"

        "#Set a register to all 0s using EOR \n"
        "EOR v22.16b, v22.16b, v22.16b \n"
        "EOR v20.16b, v20.16b, v21.16b \n"     /* F ^ E */
        "AESE v0.16b, v1.16b  \n"
        "AESMC v0.16b, v0.16b \n"
        "EXT v21.16b, v22.16b, v20.16b, #8 \n" /* get (F^E)[0] */
        "AESE v0.16b, v2.16b  \n"
        "AESMC v0.16b, v0.16b \n"
        "EOR v18.16b, v18.16b, v21.16b \n"     /* low 128 bits in v3 */
        "EXT v21.16b, v20.16b, v22.16b, #8 \n" /* get (F^E)[1] */
        "AESE v0.16b, v3.16b  \n"
        "AESMC v0.16b, v0.16b \n"
        "EOR v19.16b, v19.16b, v21.16b \n"     /* high 128 bits in v4 */
        "MOVI v23.16b, #0x87 \n"
        "AESE v0.16b, v4.16b  \n"
        "AESMC v0.16b, v0.16b \n"
        "USHR v23.2d, v23.2d, #56 \n"
        "PMULL2 v20.1q, v19.2d, v23.2d \n"
        "AESE v0.16b, v5.16b  \n"
        "AESMC v0.16b, v0.16b \n"
        "EXT v21.16b, v20.16b, v22.16b, #8 \n"
        "AESE v0.16b, v6.16b  \n"
        "AESMC v0.16b, v0.16b \n"
        "EOR v19.16b, v19.16b, v21.16b \n"
        "AESE v0.16b, v7.16b  \n"
        "AESMC v0.16b, v0.16b \n"
        "EXT v21.16b, v22.16b, v20.16b, #8 \n"
        "AESE v0.16b, v8.16b  \n"
        "AESMC v0.16b, v0.16b \n"
        "EOR v18.16b, v18.16b, v21.16b \n"
        "AESE v0.16b, v9.16b  \n"
        "AESMC v0.16b, v0.16b \n"
        "AESE v0.16b, v10.16b  \n"
        "AESMC v0.16b, v0.16b \n"
        "AESE v0.16b, v11.16b  \n"
        "AESMC v0.16b, v0.16b \n"
        "AESE v0.16b, v28.16b  \n"
        "AESMC v0.16b, v0.16b \n"
        "AESE v0.16b, v29.16b  \n"
        "AESMC v0.16b, v0.16b \n"
        "PMULL v20.1q, v19.1d, v23.1d  \n"
        "EOR v19.16b, v18.16b, v20.16b \n"
        "AESE v0.16b, v30.16b \n"
        "RBIT v19.16b, v19.16b \n"
        "EOR v0.16b, v0.16b, v31.16b \n"
        "EOR v19.16b, v19.16b, v0.16b \n"
        "STR q19, [%[out]] \n"

        :[out] "=r" (sPt), "=r" (keyPt), "=r" (iCtr)
        :[tag] "0" (sPt), [Key] "1" (keyPt),
        [ctr] "2" (iCtr) , [h] "m" (aes->H)
        : "cc", "memory", "v0", "v1", "v2", "v3", "v4", "v5",
        "v6", "v7", "v8", "v9", "v10","v11","v12","v13","v14",
        "v15", "v16", "v17","v18", "v19", "v20","v21","v22","v23",
        "v24","v25","v26","v27","v28","v29","v30","v31"
    );


    if (authTagSz > AES_BLOCK_SIZE) {
        XMEMCPY(authTag, scratch, AES_BLOCK_SIZE);
    }
    else {
        /* authTagSz can be smaller than AES_BLOCK_SIZE */
        XMEMCPY(authTag, scratch, authTagSz);
    }

    return 0;
}
#endif /* WOLFSSL_AES_256 */


/* aarch64 with PMULL and PMULL2
 * Encrypt and tag data using AES with GCM mode.
 * aes: Aes structure having already been set with set key function
 * out: encrypted data output buffer
 * in:  plain text input buffer
 * sz:  size of plain text and out buffer
 * iv:  initialization vector
 * ivSz:      size of iv buffer
 * authTag:   buffer to hold tag
 * authTagSz: size of tag buffer
 * authIn:    additional data buffer
 * authInSz:  size of additional data buffer
 *
 * Notes:
 * GHASH multiplication based from Algorithm 1 from Intel GCM white paper.
 * "Carry-Less Multiplication and Its Usage for Computing the GCM Mode"
 *
 * GHASH reduction Based from White Paper "Implementing GCM on ARMv8"
 * by Conrado P.L. Gouvea and Julio Lopez reduction on 256bit value using
 * Algorithm 5
 */
int wc_AesGcmEncrypt(Aes* aes, byte* out, const byte* in, word32 sz,
                   const byte* iv, word32 ivSz,
                   byte* authTag, word32 authTagSz,
                   const byte* authIn, word32 authInSz)
{
    /* sanity checks */
    if (aes == NULL || (iv == NULL && ivSz > 0) ||
                       (authTag == NULL) ||
                       (authIn == NULL && authInSz > 0) ||
                       (in == NULL && sz > 0) ||
                       (out == NULL && sz > 0)) {
        WOLFSSL_MSG("a NULL parameter passed in when size is larger than 0");
        return BAD_FUNC_ARG;
    }

    if (authTagSz < WOLFSSL_MIN_AUTH_TAG_SZ || authTagSz > AES_BLOCK_SIZE) {
        WOLFSSL_MSG("GcmEncrypt authTagSz error");
        return BAD_FUNC_ARG;
    }

    switch (aes->rounds) {
#ifdef WOLFSSL_AES_128
        case 10:
            return Aes128GcmEncrypt(aes, out, in, sz, iv, ivSz,
                                    authTag, authTagSz, authIn, authInSz);
#endif
#ifdef WOLFSSL_AES_192
        case 12:
            return Aes192GcmEncrypt(aes, out, in, sz, iv, ivSz,
                                    authTag, authTagSz, authIn, authInSz);
#endif
#ifdef WOLFSSL_AES_256
        case 14:
            return Aes256GcmEncrypt(aes, out, in, sz, iv, ivSz,
                                    authTag, authTagSz, authIn, authInSz);
#endif
        default:
            WOLFSSL_MSG("AES-GCM invalid round number");
            return BAD_FUNC_ARG;
    }
}


#ifdef HAVE_AES_DECRYPT
/*
 * Check tag and decrypt data using AES with GCM mode.
 * aes: Aes structure having already been set with set key function
 * out: decrypted data output buffer
 * in:  cipher text buffer
 * sz:  size of plain text and out buffer
 * iv:  initialization vector
 * ivSz:      size of iv buffer
 * authTag:   buffer holding tag
 * authTagSz: size of tag buffer
 * authIn:    additional data buffer
 * authInSz:  size of additional data buffer
 */
int  wc_AesGcmDecrypt(Aes* aes, byte* out, const byte* in, word32 sz,
                   const byte* iv, word32 ivSz,
                   const byte* authTag, word32 authTagSz,
                   const byte* authIn, word32 authInSz)
{
    word32 blocks = sz / AES_BLOCK_SIZE;
    word32 partial = sz % AES_BLOCK_SIZE;
    const byte* c = in;
    byte* p = out;
    byte counter[AES_BLOCK_SIZE];
    byte initialCounter[AES_BLOCK_SIZE];
    byte *ctr ;
    byte scratch[AES_BLOCK_SIZE];

    ctr = counter ;

    /* sanity checks */
    if (aes == NULL || (iv == NULL && ivSz > 0) ||
                       (authTag == NULL) ||
                       (authIn == NULL && authInSz > 0) ||
                       (in  == NULL && sz > 0) ||
                       (out == NULL && sz > 0)) {
        WOLFSSL_MSG("a NULL parameter passed in when size is larger than 0");
        return BAD_FUNC_ARG;
    }

    XMEMSET(initialCounter, 0, AES_BLOCK_SIZE);
    if (ivSz == GCM_NONCE_MID_SZ) {
        XMEMCPY(initialCounter, iv, ivSz);
        initialCounter[AES_BLOCK_SIZE - 1] = 1;
    }
    else {
        GHASH(aes, NULL, 0, iv, ivSz, initialCounter, AES_BLOCK_SIZE);
        GMULT(initialCounter, aes->H);
    }
    XMEMCPY(ctr, initialCounter, AES_BLOCK_SIZE);

    /* Calculate the authTag again using the received auth data and the
     * cipher text. */
    {
        byte Tprime[AES_BLOCK_SIZE];
        byte EKY0[AES_BLOCK_SIZE];

        GHASH(aes, authIn, authInSz, in, sz, Tprime, sizeof(Tprime));
        GMULT(Tprime, aes->H);
        wc_AesEncrypt(aes, ctr, EKY0);
        xorbuf(Tprime, EKY0, sizeof(Tprime));

        if (ConstantCompare(authTag, Tprime, authTagSz) != 0) {
            return AES_GCM_AUTH_E;
        }
    }

    /* do as many blocks as possible */
    if (blocks > 0) {
        /* pointer needed because it is incremented when read, causing
         * an issue with call to encrypt/decrypt leftovers */
        byte*  keyPt  = (byte*)aes->key;
        switch(aes->rounds) {
#ifdef WOLFSSL_AES_128
        case 10: /* AES 128 BLOCK */
            __asm__ __volatile__ (
            "MOV w11, %w[blocks] \n"
            "LD1 {v1.2d-v4.2d}, [%[Key]], #64  \n"

            "#Create vector with the value 1   \n"
            "MOVI v14.16b, #1                  \n"
            "USHR v14.2d, v14.2d, #56          \n"
            "LD1 {v5.2d-v8.2d}, [%[Key]], #64  \n"
            "EOR v13.16b, v13.16b, v13.16b     \n"
            "EXT v14.16b, v14.16b, v13.16b, #8 \n"

            "LD1 {v9.2d-v11.2d}, [%[Key]], #48 \n"
            "LD1 {v12.2d}, [%[ctr]]            \n"
            "LD1 {v13.2d}, [%[input]], #16     \n"

            "1: \n"
            "REV64 v12.16b, v12.16b \n" /* network order */
            "EXT v12.16b, v12.16b, v12.16b, #8 \n"
            "ADD v12.2d, v12.2d, v14.2d \n" /* add 1 to counter */
            "EXT v12.16b, v12.16b, v12.16b, #8 \n"
            "REV64 v12.16b, v12.16b \n" /* revert from network order */
            "MOV v0.16b, v12.16b  \n"
            "AESE v0.16b, v1.16b  \n"
            "AESMC v0.16b, v0.16b \n"
            "AESE v0.16b, v2.16b  \n"
            "AESMC v0.16b, v0.16b \n"
            "AESE v0.16b, v3.16b  \n"
            "AESMC v0.16b, v0.16b \n"
            "AESE v0.16b, v4.16b  \n"
            "AESMC v0.16b, v0.16b \n"
            "SUB w11, w11, #1     \n"
            "AESE v0.16b, v5.16b  \n"
            "AESMC v0.16b, v0.16b \n"
            "AESE v0.16b, v6.16b  \n"
            "AESMC v0.16b, v0.16b \n"
            "AESE v0.16b, v7.16b  \n"
            "AESMC v0.16b, v0.16b \n"
            "AESE v0.16b, v8.16b  \n"
            "AESMC v0.16b, v0.16b \n"
            "AESE v0.16b, v9.16b  \n"
            "AESMC v0.16b, v0.16b \n"
            "AESE v0.16b, v10.16b \n"
            "EOR v0.16b, v0.16b, v11.16b \n"

            "EOR v0.16b, v0.16b, v13.16b \n"
            "ST1 {v0.2d}, [%[out]], #16  \n"

            "CBZ w11, 2f \n"
            "LD1 {v13.2d}, [%[input]], #16 \n"
            "B 1b \n"

            "2: \n"
            "#store current counter value at the end \n"
            "ST1 {v12.16b}, [%[ctrOut]] \n"

            :[out] "=r" (p), "=r" (keyPt), [ctrOut] "=r" (ctr), "=r" (c)
            :"0" (p), [Key] "1" (keyPt), [ctr] "2" (ctr), [blocks] "r" (blocks),
             [input] "3" (c)
            : "cc", "memory", "w11", "v0", "v1", "v2", "v3", "v4", "v5",
            "v6", "v7", "v8", "v9", "v10", "v11", "v12", "v13", "v14"
            );
            break;
#endif
#ifdef WOLFSSL_AES_192
        case 12: /* AES 192 BLOCK */
            __asm__ __volatile__ (
            "MOV w11, %w[blocks] \n"
            "LD1 {v1.2d-v4.2d}, [%[Key]], #64  \n"

            "#Create vector with the value 1   \n"
            "MOVI v16.16b, #1                  \n"
            "USHR v16.2d, v16.2d, #56          \n"
            "LD1 {v5.2d-v8.2d}, [%[Key]], #64  \n"
            "EOR v14.16b, v14.16b, v14.16b     \n"
            "EXT v16.16b, v16.16b, v14.16b, #8 \n"

            "LD1 {v9.2d-v12.2d}, [%[Key]], #64 \n"
            "LD1 {v13.2d}, [%[Key]], #16       \n"
            "LD1 {v14.2d}, [%[ctr]]            \n"
            "LD1 {v15.2d}, [%[input]], #16     \n"

            "1: \n"
            "REV64 v14.16b, v14.16b \n" /* network order */
            "EXT v14.16b, v14.16b, v14.16b, #8 \n"
            "ADD v14.2d, v14.2d, v16.2d \n" /* add 1 to counter */
            "EXT v14.16b, v14.16b, v14.16b, #8 \n"
            "REV64 v14.16b, v14.16b \n" /* revert from network order */
            "MOV v0.16b, v14.16b  \n"
            "AESE v0.16b, v1.16b  \n"
            "AESMC v0.16b, v0.16b \n"
            "AESE v0.16b, v2.16b  \n"
            "AESMC v0.16b, v0.16b \n"
            "AESE v0.16b, v3.16b  \n"
            "AESMC v0.16b, v0.16b \n"
            "AESE v0.16b, v4.16b  \n"
            "AESMC v0.16b, v0.16b \n"
            "SUB w11, w11, #1     \n"
            "AESE v0.16b, v5.16b  \n"
            "AESMC v0.16b, v0.16b \n"
            "AESE v0.16b, v6.16b  \n"
            "AESMC v0.16b, v0.16b \n"
            "AESE v0.16b, v7.16b  \n"
            "AESMC v0.16b, v0.16b \n"
            "AESE v0.16b, v8.16b  \n"
            "AESMC v0.16b, v0.16b \n"
            "AESE v0.16b, v9.16b  \n"
            "AESMC v0.16b, v0.16b \n"
            "AESE v0.16b, v10.16b \n"
            "AESMC v0.16b, v0.16b \n"
            "AESE v0.16b, v11.16b \n"
            "AESMC v0.16b, v0.16b \n"
            "AESE v0.16b, v12.16b \n"
            "EOR v0.16b, v0.16b, v13.16b \n"

            "EOR v0.16b, v0.16b, v15.16b \n"
            "ST1 {v0.2d}, [%[out]], #16  \n"

            "CBZ w11, 2f \n"
            "LD1 {v15.2d}, [%[input]], #16 \n"
            "B 1b \n"

            "2: \n"
            "#store current counter value at the end \n"
            "ST1 {v14.2d}, [%[ctrOut]]   \n"

            :[out] "=r" (p), "=r" (keyPt), [ctrOut] "=r" (ctr), "=r" (c)
            :"0" (p), [Key] "1" (keyPt), [ctr] "2" (ctr), [blocks] "r" (blocks),
             [input] "3" (c)
            : "cc", "memory", "w11", "v0", "v1", "v2", "v3", "v4", "v5",
            "v6", "v7", "v8", "v9", "v10", "v11", "v12", "v13", "v14", "v15",
            "v16"
            );
            break;
#endif /* WOLFSSL_AES_192 */
#ifdef WOLFSSL_AES_256
        case 14: /* AES 256 BLOCK */
            __asm__ __volatile__ (
            "MOV w11, %w[blocks] \n"
            "LD1 {v1.2d-v4.2d}, [%[Key]], #64  \n"

            "#Create vector with the value 1   \n"
            "MOVI v18.16b, #1                  \n"
            "USHR v18.2d, v18.2d, #56          \n"
            "LD1 {v5.2d-v8.2d}, [%[Key]], #64  \n"
            "EOR v19.16b, v19.16b, v19.16b     \n"
            "EXT v18.16b, v18.16b, v19.16b, #8 \n"

            "LD1 {v9.2d-v12.2d},  [%[Key]], #64 \n"
            "LD1 {v13.2d-v15.2d}, [%[Key]], #48 \n"
            "LD1 {v17.2d}, [%[ctr]]             \n"
            "LD1 {v16.2d}, [%[input]], #16      \n"

            "1: \n"
            "REV64 v17.16b, v17.16b \n" /* network order */
            "EXT v17.16b, v17.16b, v17.16b, #8 \n"
            "ADD v17.2d, v17.2d, v18.2d \n" /* add 1 to counter */
            "EXT v17.16b, v17.16b, v17.16b, #8 \n"
            "REV64 v17.16b, v17.16b \n" /* revert from network order */
            "MOV v0.16b, v17.16b  \n"
            "AESE v0.16b, v1.16b  \n"
            "AESMC v0.16b, v0.16b \n"
            "AESE v0.16b, v2.16b  \n"
            "AESMC v0.16b, v0.16b \n"
            "AESE v0.16b, v3.16b  \n"
            "AESMC v0.16b, v0.16b \n"
            "AESE v0.16b, v4.16b  \n"
            "AESMC v0.16b, v0.16b \n"
            "SUB w11, w11, #1     \n"
            "AESE v0.16b, v5.16b  \n"
            "AESMC v0.16b, v0.16b \n"
            "AESE v0.16b, v6.16b  \n"
            "AESMC v0.16b, v0.16b \n"
            "AESE v0.16b, v7.16b  \n"
            "AESMC v0.16b, v0.16b \n"
            "AESE v0.16b, v8.16b  \n"
            "AESMC v0.16b, v0.16b \n"
            "AESE v0.16b, v9.16b  \n"
            "AESMC v0.16b, v0.16b \n"
            "AESE v0.16b, v10.16b \n"
            "AESMC v0.16b, v0.16b \n"
            "AESE v0.16b, v11.16b \n"
            "AESMC v0.16b, v0.16b \n"
            "AESE v0.16b, v12.16b \n"
            "AESMC v0.16b, v0.16b \n"
            "AESE v0.16b, v13.16b \n"
            "AESMC v0.16b, v0.16b \n"
            "AESE v0.16b, v14.16b \n"
            "EOR v0.16b, v0.16b, v15.16b \n"

            "EOR v0.16b, v0.16b, v16.16b \n"
            "ST1 {v0.2d}, [%[out]], #16  \n"

            "CBZ w11, 2f \n"
            "LD1 {v16.2d}, [%[input]], #16 \n"
            "B 1b \n"

            "2: \n"
            "#store current counter value at the end \n"
            "ST1 {v17.2d}, [%[ctrOut]] \n"

            :[out] "=r" (p), "=r" (keyPt), [ctrOut] "=r" (ctr), "=r" (c)
            :"0" (p), [Key] "1" (keyPt), [ctr] "2" (ctr), [blocks] "r" (blocks),
             [input] "3" (c)
            : "cc", "memory", "w11", "v0", "v1", "v2", "v3", "v4", "v5",
            "v6", "v7", "v8", "v9", "v10", "v11", "v12", "v13", "v14", "v15",
            "v16", "v17", "v18", "v19"
            );
            break;
#endif /* WOLFSSL_AES_256 */
        default:
            WOLFSSL_MSG("Bad AES-GCM round value");
            return BAD_FUNC_ARG;
        }
    }
    if (partial != 0) {
        IncrementGcmCounter(ctr);
        wc_AesEncrypt(aes, ctr, scratch);

        /* check if pointer is null after main AES-GCM blocks
         * helps static analysis */
        if (p == NULL || c == NULL) {
            return BAD_STATE_E;
        }
        xorbuf(scratch, c, partial);
        XMEMCPY(p, scratch, partial);
    }
    return 0;
}

#endif /* HAVE_AES_DECRYPT */
#endif /* HAVE_AESGCM */


/***************************************
 * not 64 bit so use 32 bit mode
****************************************/
#else

/* AES CCM/GCM use encrypt direct but not decrypt */
#if defined(HAVE_AESCCM) || defined(HAVE_AESGCM) || \
    defined(WOLFSSL_AES_DIRECT) || defined(WOLFSSL_AES_COUNTER)
    static int wc_AesEncrypt(Aes* aes, const byte* inBlock, byte* outBlock)
    {
            /*
              AESE exor's input with round key
                   shift rows of exor'ed result
                   sub bytes for shifted rows
             */

            word32* keyPt = aes->key;
            __asm__ __volatile__ (
                "VLD1.32 {q0}, [%[CtrIn]] \n"
                "VLDM %[Key]!, {q1-q4}    \n"

                "AESE.8 q0, q1\n"
                "AESMC.8 q0, q0\n"
                "AESE.8 q0, q2\n"
                "AESMC.8 q0, q0\n"
                "VLD1.32 {q1}, [%[Key]]!  \n"
                "AESE.8 q0, q3\n"
                "AESMC.8 q0, q0\n"
                "VLD1.32 {q2}, [%[Key]]!  \n"
                "AESE.8 q0, q4\n"
                "AESMC.8 q0, q0\n"
                "VLD1.32 {q3}, [%[Key]]!  \n"
                "AESE.8 q0, q1\n"
                "AESMC.8 q0, q0\n"
                "VLD1.32 {q4}, [%[Key]]!  \n"
                "AESE.8 q0, q2\n"
                "AESMC.8 q0, q0\n"
                "AESE.8 q0, q3\n"
                "AESMC.8 q0, q0\n"
                "VLD1.32 {q1}, [%[Key]]!  \n"
                "AESE.8 q0, q4\n"
                "AESMC.8 q0, q0\n"
                "VLD1.32 {q2}, [%[Key]]!  \n"
                "AESE.8 q0, q1\n"
                "AESMC.8 q0, q0\n"
                "AESE.8 q0, q2\n"

                "MOV r12, %[R]    \n"
                "CMP r12, #10 \n"
                "BEQ 1f    \n"
                "VLD1.32 {q1}, [%[Key]]!  \n"
                "AESMC.8 q0, q0\n"
                "VLD1.32 {q2}, [%[Key]]!  \n"
                "AESE.8 q0, q1\n"
                "AESMC.8 q0, q0\n"
                "AESE.8 q0, q2\n"

                "CMP r12, #12 \n"
                "BEQ 1f    \n"
                "VLD1.32 {q1}, [%[Key]]!  \n"
                "AESMC.8 q0, q0\n"
                "VLD1.32 {q2}, [%[Key]]!  \n"
                "AESE.8 q0, q1\n"
                "AESMC.8 q0, q0\n"
                "AESE.8 q0, q2\n"

                "#Final AddRoundKey then store result \n"
                "1: \n"
                "VLD1.32 {q1}, [%[Key]]!  \n"
                "VEOR.32 q0, q0, q1\n"
                "VST1.32 {q0}, [%[CtrOut]]   \n"

                :[CtrOut] "=r" (outBlock), "=r" (keyPt), "=r" (aes->rounds),
                 "=r" (inBlock)
                :"0" (outBlock), [Key] "1" (keyPt), [R] "2" (aes->rounds),
                 [CtrIn] "3" (inBlock)
                : "cc", "memory", "r12", "q0", "q1", "q2", "q3", "q4"
            );

        return 0;
    }
#endif /* AES_GCM, AES_CCM, DIRECT or COUNTER */
#if defined(WOLFSSL_AES_DIRECT) || defined(WOLFSSL_AES_COUNTER)
    #ifdef HAVE_AES_DECRYPT
    static int wc_AesDecrypt(Aes* aes, const byte* inBlock, byte* outBlock)
    {
            /*
              AESE exor's input with round key
                   shift rows of exor'ed result
                   sub bytes for shifted rows
             */

            word32* keyPt = aes->key;
            __asm__ __volatile__ (
                "VLD1.32 {q0}, [%[CtrIn]] \n"
                "VLDM %[Key]!, {q1-q4}    \n"

                "AESD.8 q0, q1\n"
                "AESIMC.8 q0, q0\n"
                "AESD.8 q0, q2\n"
                "AESIMC.8 q0, q0\n"
                "VLD1.32 {q1}, [%[Key]]!  \n"
                "AESD.8 q0, q3\n"
                "AESIMC.8 q0, q0\n"
                "VLD1.32 {q2}, [%[Key]]!  \n"
                "AESD.8 q0, q4\n"
                "AESIMC.8 q0, q0\n"
                "VLD1.32 {q3}, [%[Key]]!  \n"
                "AESD.8 q0, q1\n"
                "AESIMC.8 q0, q0\n"
                "VLD1.32 {q4}, [%[Key]]!  \n"
                "AESD.8 q0, q2\n"
                "AESIMC.8 q0, q0\n"
                "AESD.8 q0, q3\n"
                "AESIMC.8 q0, q0\n"
                "VLD1.32 {q1}, [%[Key]]!  \n"
                "AESD.8 q0, q4\n"
                "AESIMC.8 q0, q0\n"
                "VLD1.32 {q2}, [%[Key]]!  \n"
                "AESD.8 q0, q1\n"
                "AESIMC.8 q0, q0\n"
                "AESD.8 q0, q2\n"

                "MOV r12, %[R] \n"
                "CMP r12, #10  \n"
                "BEQ 1f \n"
                "VLD1.32 {q1}, [%[Key]]!  \n"
                "AESIMC.8 q0, q0\n"
                "VLD1.32 {q2}, [%[Key]]!  \n"
                "AESD.8 q0, q1\n"
                "AESIMC.8 q0, q0\n"
                "AESD.8 q0, q2\n"

                "CMP r12, #12  \n"
                "BEQ 1f \n"
                "VLD1.32 {q1}, [%[Key]]!  \n"
                "AESIMC.8 q0, q0\n"
                "VLD1.32 {q2}, [%[Key]]!  \n"
                "AESD.8 q0, q1\n"
                "AESIMC.8 q0, q0\n"
                "AESD.8 q0, q2\n"

                "#Final AddRoundKey then store result \n"
                "1: \n"
                "VLD1.32 {q1}, [%[Key]]! \n"
                "VEOR.32 q0, q0, q1\n"
                "VST1.32 {q0}, [%[CtrOut]]    \n"

                :[CtrOut] "=r" (outBlock), "=r" (keyPt), "=r" (aes->rounds),
                 "=r" (inBlock)
                :"0" (outBlock), [Key] "1" (keyPt), [R] "2" (aes->rounds),
                 [CtrIn] "3" (inBlock)
                : "cc", "memory", "r12", "q0", "q1", "q2", "q3", "q4"
            );

        return 0;
}
    #endif /* HAVE_AES_DECRYPT */
#endif /* DIRECT or COUNTER */

/* AES-CBC */
#ifdef HAVE_AES_CBC
    int wc_AesCbcEncrypt(Aes* aes, byte* out, const byte* in, word32 sz)
    {
        word32 numBlocks = sz / AES_BLOCK_SIZE;

        if (aes == NULL || out == NULL || (in == NULL && sz > 0)) {
            return BAD_FUNC_ARG;
        }

        /* do as many block size ops as possible */
        if (numBlocks > 0) {
            word32* keyPt = aes->key;
            word32* regPt = aes->reg;
            /*
            AESE exor's input with round key
            shift rows of exor'ed result
            sub bytes for shifted rows

            note: grouping AESE & AESMC together as pairs reduces latency
            */
            switch(aes->rounds) {
#ifdef WOLFSSL_AES_128
            case 10: /* AES 128 BLOCK */
                __asm__ __volatile__ (
                "MOV r11, %[blocks] \n"
                "VLD1.32 {q1}, [%[Key]]!  \n"
                "VLD1.32 {q2}, [%[Key]]!  \n"
                "VLD1.32 {q3}, [%[Key]]!  \n"
                "VLD1.32 {q4}, [%[Key]]!  \n"
                "VLD1.32 {q5}, [%[Key]]!  \n"
                "VLD1.32 {q6}, [%[Key]]!  \n"
                "VLD1.32 {q7}, [%[Key]]!  \n"
                "VLD1.32 {q8}, [%[Key]]!  \n"
                "VLD1.32 {q9}, [%[Key]]!  \n"
                "VLD1.32 {q10}, [%[Key]]! \n"
                "VLD1.32 {q11}, [%[Key]]! \n"
                "VLD1.32 {q0}, [%[reg]]   \n"
                "VLD1.32 {q12}, [%[input]]!\n"

                "1:\n"
                "#CBC operations, xorbuf in with current aes->reg \n"
                "VEOR.32 q0, q0, q12 \n"
                "AESE.8 q0, q1 \n"
                "AESMC.8 q0, q0\n"
                "AESE.8 q0, q2 \n"
                "AESMC.8 q0, q0\n"
                "AESE.8 q0, q3 \n"
                "AESMC.8 q0, q0\n"
                "AESE.8 q0, q4 \n"
                "AESMC.8 q0, q0\n"
                "AESE.8 q0, q5 \n"
                "AESMC.8 q0, q0\n"
                "AESE.8 q0, q6 \n"
                "AESMC.8 q0, q0\n"
                "AESE.8 q0, q7 \n"
                "AESMC.8 q0, q0\n"
                "AESE.8 q0, q8 \n"
                "AESMC.8 q0, q0\n"
                "AESE.8 q0, q9 \n"
                "AESMC.8 q0, q0\n"
                "AESE.8 q0, q10\n"
                "VEOR.32 q0, q0, q11 \n"
                "SUB r11, r11, #1    \n"
                "VST1.32 {q0}, [%[out]]!   \n"

                "CMP r11, #0   \n"
                "BEQ 2f \n"
                "VLD1.32 {q12}, [%[input]]! \n"
                "B 1b \n"

                "2:\n"
                "#store current counter value at the end \n"
                "VST1.32 {q0}, [%[regOut]] \n"

                :[out] "=r" (out), [regOut] "=r" (regPt)
                :"0" (out), [Key] "r" (keyPt), [input] "r" (in),
                 [blocks] "r" (numBlocks), [reg] "1" (regPt)
                : "cc", "memory", "r11", "q0", "q1", "q2", "q3", "q4", "q5",
                "q6", "q7", "q8", "q9", "q10", "q11", "q12"
                );
                break;
#endif /* WOLFSSL_AES_128 */
#ifdef WOLFSSL_AES_192
            case 12: /* AES 192 BLOCK */
                __asm__ __volatile__ (
                "MOV r11, %[blocks] \n"
                "VLD1.32 {q1}, [%[Key]]!  \n"
                "VLD1.32 {q2}, [%[Key]]!  \n"
                "VLD1.32 {q3}, [%[Key]]!  \n"
                "VLD1.32 {q4}, [%[Key]]!  \n"
                "VLD1.32 {q5}, [%[Key]]!  \n"
                "VLD1.32 {q6}, [%[Key]]!  \n"
                "VLD1.32 {q7}, [%[Key]]!  \n"
                "VLD1.32 {q8}, [%[Key]]!  \n"
                "VLD1.32 {q9}, [%[Key]]!  \n"
                "VLD1.32 {q10}, [%[Key]]! \n"
                "VLD1.32 {q11}, [%[Key]]! \n"
                "VLD1.32 {q0}, [%[reg]]   \n"
                "VLD1.32 {q12}, [%[input]]!\n"
                "VLD1.32 {q13}, [%[Key]]!  \n"
                "VLD1.32 {q14}, [%[Key]]!  \n"

                "1:\n"
                "#CBC operations, xorbuf in with current aes->reg \n"
                "VEOR.32 q0, q0, q12 \n"
                "AESE.8 q0, q1 \n"
                "AESMC.8 q0, q0\n"
                "AESE.8 q0, q2 \n"
                "AESMC.8 q0, q0\n"
                "AESE.8 q0, q3 \n"
                "AESMC.8 q0, q0\n"
                "AESE.8 q0, q4 \n"
                "AESMC.8 q0, q0\n"
                "AESE.8 q0, q5 \n"
                "AESMC.8 q0, q0\n"
                "AESE.8 q0, q6 \n"
                "AESMC.8 q0, q0\n"
                "AESE.8 q0, q7 \n"
                "AESMC.8 q0, q0\n"
                "AESE.8 q0, q8 \n"
                "AESMC.8 q0, q0\n"
                "AESE.8 q0, q9 \n"
                "AESMC.8 q0, q0\n"
                "AESE.8 q0, q10 \n"
                "AESMC.8 q0, q0\n"
                "AESE.8 q0, q11 \n"
                "AESMC.8 q0, q0\n"
                "AESE.8 q0, q13\n"
                "VEOR.32 q0, q0, q14 \n"
                "SUB r11, r11, #1    \n"
                "VST1.32 {q0}, [%[out]]!   \n"

                "CMP r11, #0   \n"
                "BEQ 2f \n"
                "VLD1.32 {q12}, [%[input]]! \n"
                "B 1b \n"

                "2:\n"
                "#store current counter qalue at the end \n"
                "VST1.32 {q0}, [%[regOut]] \n"

                :[out] "=r" (out), [regOut] "=r" (regPt)
                :"0" (out), [Key] "r" (keyPt), [input] "r" (in),
                 [blocks] "r" (numBlocks), [reg] "1" (regPt)
                : "cc", "memory", "r11", "q0", "q1", "q2", "q3", "q4", "q5",
                "q6", "q7", "q8", "q9", "q10", "q11", "q12", "q13", "q14"
                );
                break;
#endif /* WOLFSSL_AES_192 */
#ifdef WOLFSSL_AES_256
            case 14: /* AES 256 BLOCK */
                __asm__ __volatile__ (
                "MOV r11, %[blocks] \n"
                "VLD1.32 {q1}, [%[Key]]!  \n"
                "VLD1.32 {q2}, [%[Key]]!  \n"
                "VLD1.32 {q3}, [%[Key]]!  \n"
                "VLD1.32 {q4}, [%[Key]]!  \n"
                "VLD1.32 {q5}, [%[Key]]!  \n"
                "VLD1.32 {q6}, [%[Key]]!  \n"
                "VLD1.32 {q7}, [%[Key]]!  \n"
                "VLD1.32 {q8}, [%[Key]]!  \n"
                "VLD1.32 {q9}, [%[Key]]!  \n"
                "VLD1.32 {q10}, [%[Key]]! \n"
                "VLD1.32 {q11}, [%[Key]]! \n"
                "VLD1.32 {q0}, [%[reg]]   \n"
                "VLD1.32 {q12}, [%[input]]!\n"
                "VLD1.32 {q13}, [%[Key]]!  \n"
                "VLD1.32 {q14}, [%[Key]]!  \n"

                "1:\n"
                "#CBC operations, xorbuf in with current aes->reg \n"
                "VEOR.32 q0, q0, q12 \n"
                "AESE.8 q0, q1 \n"
                "AESMC.8 q0, q0\n"
                "AESE.8 q0, q2 \n"
                "AESMC.8 q0, q0\n"
                "AESE.8 q0, q3 \n"
                "AESMC.8 q0, q0\n"
                "AESE.8 q0, q4 \n"
                "AESMC.8 q0, q0\n"
                "AESE.8 q0, q5 \n"
                "AESMC.8 q0, q0\n"
                "AESE.8 q0, q6 \n"
                "AESMC.8 q0, q0\n"
                "AESE.8 q0, q7 \n"
                "AESMC.8 q0, q0\n"
                "AESE.8 q0, q8 \n"
                "AESMC.8 q0, q0\n"
                "AESE.8 q0, q9 \n"
                "AESMC.8 q0, q0\n"
                "AESE.8 q0, q10 \n"
                "AESMC.8 q0, q0\n"
                "AESE.8 q0, q11 \n"
                "AESMC.8 q0, q0\n"
                "AESE.8 q0, q13 \n"
                "AESMC.8 q0, q0\n"
                "VLD1.32 {q15}, [%[Key]]!  \n"
                "AESE.8 q0, q14 \n"
                "AESMC.8 q0, q0\n"
                "AESE.8 q0, q15\n"
                "VLD1.32 {q15}, [%[Key]]   \n"
                "VEOR.32 q0, q0, q15 \n"
                "SUB r11, r11, #1    \n"
                "VST1.32 {q0}, [%[out]]!   \n"
                "SUB %[Key], %[Key], #16   \n"

                "CMP r11, #0   \n"
                "BEQ 2f \n"
                "VLD1.32 {q12}, [%[input]]! \n"
                "B 1b \n"

                "2:\n"
                "#store current counter qalue at the end \n"
                "VST1.32 {q0}, [%[regOut]] \n"

                :[out] "=r" (out), [regOut] "=r" (regPt), "=r" (keyPt)
                :"0" (out), [Key] "2" (keyPt), [input] "r" (in),
                 [blocks] "r" (numBlocks), [reg] "1" (regPt)
                : "cc", "memory", "r11", "q0", "q1", "q2", "q3", "q4", "q5",
                "q6", "q7", "q8", "q9", "q10", "q11", "q12", "q13", "q14", "q15"
                );
                break;
#endif /* WOLFSSL_AES_256 */
            default:
                WOLFSSL_MSG("Bad AES-CBC round value");
                return BAD_FUNC_ARG;
            }
        }

        return 0;
    }

    #ifdef HAVE_AES_DECRYPT
    int wc_AesCbcDecrypt(Aes* aes, byte* out, const byte* in, word32 sz)
    {
        word32 numBlocks = sz / AES_BLOCK_SIZE;

        if (aes == NULL || out == NULL || (in == NULL && sz > 0)
                || sz % AES_BLOCK_SIZE != 0) {
            return BAD_FUNC_ARG;
        }

        /* do as many block size ops as possible */
        if (numBlocks > 0) {
            word32* keyPt = aes->key;
            word32* regPt = aes->reg;
            switch(aes->rounds) {
#ifdef WOLFSSL_AES_128
            case 10: /* AES 128 BLOCK */
                __asm__ __volatile__ (
                "MOV r11, %[blocks] \n"
                "VLD1.32 {q1}, [%[Key]]!  \n"
                "VLD1.32 {q2}, [%[Key]]!  \n"
                "VLD1.32 {q3}, [%[Key]]!  \n"
                "VLD1.32 {q4}, [%[Key]]!  \n"
                "VLD1.32 {q5}, [%[Key]]!  \n"
                "VLD1.32 {q6}, [%[Key]]!  \n"
                "VLD1.32 {q7}, [%[Key]]!  \n"
                "VLD1.32 {q8}, [%[Key]]!  \n"
                "VLD1.32 {q9}, [%[Key]]!  \n"
                "VLD1.32 {q10}, [%[Key]]! \n"
                "VLD1.32 {q11}, [%[Key]]! \n"
                "VLD1.32 {q13}, [%[reg]]  \n"
                "VLD1.32 {q0}, [%[input]]!\n"

                "1:\n"
                "VMOV.32 q12, q0 \n"
                "AESD.8 q0, q1\n"
                "AESIMC.8 q0, q0\n"
                "AESD.8 q0, q2\n"
                "AESIMC.8 q0, q0\n"
                "AESD.8 q0, q3\n"
                "AESIMC.8 q0, q0\n"
                "AESD.8 q0, q4\n"
                "AESIMC.8 q0, q0\n"
                "AESD.8 q0, q5\n"
                "AESIMC.8 q0, q0\n"
                "AESD.8 q0, q6\n"
                "AESIMC.8 q0, q0\n"
                "AESD.8 q0, q7\n"
                "AESIMC.8 q0, q0\n"
                "AESD.8 q0, q8\n"
                "AESIMC.8 q0, q0\n"
                "AESD.8 q0, q9\n"
                "AESIMC.8 q0, q0\n"
                "AESD.8 q0, q10\n"
                "VEOR.32 q0, q0, q11\n"

                "VEOR.32 q0, q0, q13\n"
                "SUB r11, r11, #1            \n"
                "VST1.32 {q0}, [%[out]]!  \n"
                "VMOV.32 q13, q12        \n"

                "CMP r11, #0 \n"
                "BEQ 2f \n"
                "VLD1.32 {q0}, [%[input]]!  \n"
                "B 1b      \n"

                "2: \n"
                "#store current counter qalue at the end \n"
                "VST1.32 {q13}, [%[regOut]] \n"

                :[out] "=r" (out), [regOut] "=r" (regPt)
                :"0" (out), [Key] "r" (keyPt), [input] "r" (in),
                 [blocks] "r" (numBlocks), [reg] "1" (regPt)
                : "cc", "memory", "r11", "q0", "q1", "q2", "q3", "q4", "q5",
                "q6", "q7", "q8", "q9", "q10", "q11", "q12", "q13"
                );
                break;
#endif /* WOLFSSL_AES_128 */
#ifdef WOLFSSL_AES_192
            case 12: /* AES 192 BLOCK */
                __asm__ __volatile__ (
                "MOV r11, %[blocks] \n"
                "VLD1.32 {q1}, [%[Key]]!  \n"
                "VLD1.32 {q2}, [%[Key]]!  \n"
                "VLD1.32 {q3}, [%[Key]]!  \n"
                "VLD1.32 {q4}, [%[Key]]!  \n"
                "VLD1.32 {q5}, [%[Key]]!  \n"
                "VLD1.32 {q6}, [%[Key]]!  \n"
                "VLD1.32 {q7}, [%[Key]]!  \n"
                "VLD1.32 {q8}, [%[Key]]!  \n"
                "VLD1.32 {q9}, [%[Key]]!  \n"
                "VLD1.32 {q10}, [%[Key]]! \n"
                "VLD1.32 {q11}, [%[Key]]! \n"
                "VLD1.32 {q12}, [%[Key]]! \n"
                "VLD1.32 {q13}, [%[Key]]! \n"
                "VLD1.32 {q14}, [%[reg]]  \n"
                "VLD1.32 {q0}, [%[input]]!\n"

                "1:    \n"
                "VMOV.32 q15, q0 \n"
                "AESD.8 q0, q1\n"
                "AESIMC.8 q0, q0\n"
                "AESD.8 q0, q2\n"
                "AESIMC.8 q0, q0\n"
                "AESD.8 q0, q3\n"
                "AESIMC.8 q0, q0\n"
                "AESD.8 q0, q4\n"
                "AESIMC.8 q0, q0\n"
                "AESD.8 q0, q5\n"
                "AESIMC.8 q0, q0\n"
                "AESD.8 q0, q6\n"
                "AESIMC.8 q0, q0\n"
                "AESD.8 q0, q7\n"
                "AESIMC.8 q0, q0\n"
                "AESD.8 q0, q8\n"
                "AESIMC.8 q0, q0\n"
                "AESD.8 q0, q9\n"
                "AESIMC.8 q0, q0\n"
                "AESD.8 q0, q10\n"
                "AESIMC.8 q0, q0\n"
                "AESD.8 q0, q11\n"
                "AESIMC.8 q0, q0\n"
                "AESD.8 q0, q12\n"
                "VEOR.32 q0, q0, q13\n"

                "VEOR.32 q0, q0, q14\n"
                "SUB r11, r11, #1        \n"
                "VST1.32 {q0}, [%[out]]! \n"
                "VMOV.32 q14, q15        \n"

                "CMP r11, #0 \n"
                "BEQ 2f \n"
                "VLD1.32 {q0}, [%[input]]!  \n"
                "B 1b \n"

                "2:\n"
                "#store current counter value at the end \n"
                "VST1.32 {q15}, [%[regOut]] \n"

                :[out] "=r" (out), [regOut] "=r" (regPt)
                :"0" (out), [Key] "r" (keyPt), [input] "r" (in),
                 [blocks] "r" (numBlocks), [reg] "1" (regPt)
                : "cc", "memory", "r11", "q0", "q1", "q2", "q3", "q4", "q5",
                "q6", "q7", "q8", "q9", "q10", "q11", "q12", "q13", "q14", "q15"
                );
                break;
#endif /* WOLFSSL_AES_192 */
#ifdef WOLFSSL_AES_256
            case 14: /* AES 256 BLOCK */
                __asm__ __volatile__ (
                "MOV r11, %[blocks] \n"
                "VLD1.32 {q1}, [%[Key]]!  \n"
                "VLD1.32 {q2}, [%[Key]]!  \n"
                "VLD1.32 {q3}, [%[Key]]!  \n"
                "VLD1.32 {q4}, [%[Key]]!  \n"
                "VLD1.32 {q5}, [%[Key]]!  \n"
                "VLD1.32 {q6}, [%[Key]]!  \n"
                "VLD1.32 {q7}, [%[Key]]!  \n"
                "VLD1.32 {q8}, [%[Key]]!  \n"
                "VLD1.32 {q9}, [%[Key]]!  \n"
                "VLD1.32 {q10}, [%[Key]]! \n"
                "VLD1.32 {q11}, [%[Key]]! \n"
                "VLD1.32 {q12}, [%[Key]]! \n"
                "VLD1.32 {q14}, [%[reg]]  \n"
                "VLD1.32 {q0}, [%[input]]!\n"

                "1:\n"
                "VMOV.32 q15, q0 \n"
                "AESD.8 q0, q1\n"
                "AESIMC.8 q0, q0\n"
                "AESD.8 q0, q2\n"
                "AESIMC.8 q0, q0\n"
                "AESD.8 q0, q3\n"
                "AESIMC.8 q0, q0\n"
                "AESD.8 q0, q4\n"
                "AESIMC.8 q0, q0\n"
                "AESD.8 q0, q5\n"
                "AESIMC.8 q0, q0\n"
                "AESD.8 q0, q6\n"
                "AESIMC.8 q0, q0\n"
                "AESD.8 q0, q7\n"
                "AESIMC.8 q0, q0\n"
                "AESD.8 q0, q8\n"
                "AESIMC.8 q0, q0\n"
                "AESD.8 q0, q9\n"
                "AESIMC.8 q0, q0\n"
                "AESD.8 q0, q10\n"
                "AESIMC.8 q0, q0\n"
                "AESD.8 q0, q11\n"
                "AESIMC.8 q0, q0\n"
                "VLD1.32 {q13}, [%[Key]]!  \n"
                "AESD.8 q0, q12\n"
                "AESIMC.8 q0, q0\n"
                "AESD.8 q0, q13\n"
                "AESIMC.8 q0, q0\n"
                "VLD1.32 {q13}, [%[Key]]!  \n"
                "AESD.8 q0, q13\n"
                "VLD1.32 {q13}, [%[Key]]  \n"
                "VEOR.32 q0, q0, q13\n"
                "SUB %[Key], %[Key], #32 \n"

                "VEOR.32 q0, q0, q14\n"
                "SUB r11, r11, #1            \n"
                "VST1.32 {q0}, [%[out]]!  \n"
                "VMOV.32 q14, q15        \n"

                "CMP r11, #0 \n"
                "BEQ 2f \n"
                "VLD1.32 {q0}, [%[input]]!  \n"
                "B 1b \n"

                "2:\n"
                "#store current counter value at the end \n"
                "VST1.32 {q15}, [%[regOut]] \n"

                :[out] "=r" (out), [regOut] "=r" (regPt)
                :"0" (out), [Key] "r" (keyPt), [input] "r" (in),
                 [blocks] "r" (numBlocks), [reg] "1" (regPt)
                : "cc", "memory", "r11", "q0", "q1", "q2", "q3", "q4", "q5",
                "q6", "q7", "q8", "q9", "q10", "q11", "q12", "q13", "q14", "q15"
                );
                break;
#endif /* WOLFSSL_AES_256 */
            default:
                WOLFSSL_MSG("Bad AES-CBC round value");
                return BAD_FUNC_ARG;
            }
        }

        return 0;
    }
    #endif

#endif /* HAVE_AES_CBC */

/* AES-CTR */
#ifdef WOLFSSL_AES_COUNTER

        /* Increment AES counter */
        static WC_INLINE void IncrementAesCounter(byte* inOutCtr)
        {
            int i;

            /* in network byte order so start at end and work back */
            for (i = AES_BLOCK_SIZE - 1; i >= 0; i--) {
                if (++inOutCtr[i])  /* we're done unless we overflow */
                    return;
            }
        }

        int wc_AesCtrEncrypt(Aes* aes, byte* out, const byte* in, word32 sz)
        {
            byte* tmp;
            word32 numBlocks;

            if (aes == NULL || out == NULL || in == NULL) {
                return BAD_FUNC_ARG;
            }

            tmp = (byte*)aes->tmp + AES_BLOCK_SIZE - aes->left;

            /* consume any unused bytes left in aes->tmp */
            while (aes->left && sz) {
               *(out++) = *(in++) ^ *(tmp++);
               aes->left--;
               sz--;
            }

            /* do as many block size ops as possible */
            numBlocks = sz/AES_BLOCK_SIZE;
            if (numBlocks > 0) {
                /* pointer needed because it is incremented when read, causing
                 * an issue with call to encrypt/decrypt leftovers */
                word32*  keyPt  = aes->key;
                word32*  regPt  = aes->reg;
                sz           -= numBlocks * AES_BLOCK_SIZE;
                switch(aes->rounds) {
#ifdef WOLFSSL_AES_128
                case 10: /* AES 128 BLOCK */
                    __asm__ __volatile__ (
                    "MOV r11, %[blocks] \n"
                    "VLDM %[Key]!, {q1-q4} \n"

                    "#Create vector with the value 1  \n"
                    "VMOV.u32 q15, #1                 \n"
                    "VSHR.u64 q15, q15, #32  \n"
                    "VLDM %[Key]!, {q5-q8} \n"
                    "VEOR.32 q14, q14, q14    \n"
                    "VLDM %[Key]!, {q9-q11} \n"
                    "VEXT.8 q14, q15, q14, #8\n"

                    "VLD1.32 {q13}, [%[reg]]\n"

                    /* double block */
                    "1:      \n"
                    "CMP r11, #1 \n"
                    "BEQ 2f    \n"
                    "CMP r11, #0 \n"
                    "BEQ 3f    \n"

                    "VMOV.32 q0, q13  \n"
                    "AESE.8 q0, q1\n"
                    "AESMC.8 q0, q0\n"
                    "VREV64.8 q13, q13 \n" /* network order */
                    "AESE.8 q0, q2\n"
                    "AESMC.8 q0, q0\n"
                    "VEXT.8 q13, q13, q13, #8 \n"
                    "SUB r11, r11, #2     \n"
                    "VADD.i32 q15, q13, q14 \n" /* add 1 to counter */
                    "VADD.i32 q13, q15, q14 \n" /* add 1 to counter */
                    "AESE.8 q0, q3\n"
                    "AESMC.8 q0, q0\n"
                    "VEXT.8 q15, q15, q15, #8 \n"
                    "VEXT.8 q13, q13, q13, #8 \n"
                    "AESE.8 q0, q4\n"
                    "AESMC.8 q0, q0\n"
                    "VREV64.8 q15, q15\n" /* revert from network order */
                    "VREV64.8 q13, q13\n" /* revert from network order */
                    "AESE.8 q0, q5\n"
                    "AESMC.8 q0, q0\n"
                    "AESE.8 q15, q1\n"
                    "AESMC.8 q15, q15\n"

                    "AESE.8 q0, q6\n"
                    "AESMC.8 q0, q0\n"
                    "AESE.8 q15, q2\n"
                    "AESMC.8 q15, q15\n"

                    "AESE.8 q0, q7\n"
                    "AESMC.8 q0, q0\n"
                    "AESE.8 q15, q3\n"
                    "AESMC.8 q15, q15\n"

                    "AESE.8 q0, q8\n"
                    "AESMC.8 q0, q0\n"
                    "AESE.8 q15, q4\n"
                    "AESMC.8 q15, q15\n"

                    "AESE.8 q0, q9\n"
                    "AESMC.8 q0, q0\n"
                    "AESE.8 q15, q5\n"
                    "AESMC.8 q15, q15\n"

                    "AESE.8 q0, q10\n"
                    "AESE.8 q15, q6\n"
                    "AESMC.8 q15, q15\n"
                    "VEOR.32 q0, q0, q11\n"

                    "AESE.8 q15, q7\n"
                    "AESMC.8 q15, q15\n"
                    "VLD1.32 {q12}, [%[input]]!  \n"
                    "AESE.8 q15, q8\n"
                    "AESMC.8 q15, q15\n"

                    "VEOR.32 q0, q0, q12\n"
                    "AESE.8 q15, q9\n"
                    "AESMC.8 q15, q15\n"

                    "VLD1.32 {q12}, [%[input]]!  \n"
                    "AESE.8 q15, q10\n"
                    "VST1.32 {q0}, [%[out]]!  \n"
                    "VEOR.32 q15, q15, q11\n"
                    "VEOR.32 q15, q15, q12\n"
                    "VST1.32 {q15}, [%[out]]!  \n"

                    "B 1b \n"

                    /* single block */
                    "2:      \n"
                    "VMOV.32 q0, q13  \n"
                    "AESE.8 q0, q1\n"
                    "AESMC.8 q0, q0\n"
                    "VREV64.8 q13, q13 \n" /* network order */
                    "AESE.8 q0, q2\n"
                    "AESMC.8 q0, q0\n"
                    "VEXT.8 q13, q13, q13, #8 \n"
                    "AESE.8 q0, q3\n"
                    "AESMC.8 q0, q0\n"
                    "VADD.i32 q13, q13, q14 \n" /* add 1 to counter */
                    "AESE.8 q0, q4\n"
                    "AESMC.8 q0, q0\n"
                    "SUB r11, r11, #1     \n"
                    "AESE.8 q0, q5\n"
                    "AESMC.8 q0, q0\n"
                    "VEXT.8 q13, q13, q13, #8 \n"
                    "AESE.8 q0, q6\n"
                    "AESMC.8 q0, q0\n"
                    "VREV64.8 q13, q13\n" /* revert from network order */
                    "AESE.8 q0, q7\n"
                    "AESMC.8 q0, q0\n"
                    "AESE.8 q0, q8\n"
                    "AESMC.8 q0, q0\n"
                    "AESE.8 q0, q9\n"
                    "AESMC.8 q0, q0\n"
                    "AESE.8 q0, q10\n"
                    "VLD1.32 {q12}, [%[input]]!  \n"
                    "VEOR.32 q0, q0, q11\n"
                    "#CTR operations, increment counter and xorbuf \n"
                    "VEOR.32 q0, q0, q12\n"
                    "VST1.32 {q0}, [%[out]]!  \n"

                    "3: \n"
                    "#store current counter qalue at the end \n"
                    "VST1.32 {q13}, [%[regOut]]   \n"

                    :[out] "=r" (out), "=r" (keyPt), [regOut] "=r" (regPt),
                     "=r" (in)
                    :"0" (out), [Key] "1" (keyPt), [input] "3" (in),
                     [blocks] "r" (numBlocks), [reg] "2" (regPt)
                    : "cc", "memory", "r11", "q0", "q1", "q2", "q3", "q4", "q5",
                    "q6", "q7", "q8", "q9", "q10","q11","q12","q13","q14", "q15"
                    );
                    break;
#endif /* WOLFSSL_AES_128 */
#ifdef WOLFSSL_AES_192
                case 12: /* AES 192 BLOCK */
                    __asm__ __volatile__ (
                    "MOV r11, %[blocks] \n"
                    "VLDM %[Key]!, {q1-q4} \n"

                    "#Create vector with the value 1  \n"
                    "VMOV.u32 q15, #1                 \n"
                    "VSHR.u64 q15, q15, #32  \n"
                    "VLDM %[Key]!, {q5-q8} \n"
                    "VEOR.32 q14, q14, q14    \n"
                    "VEXT.8 q14, q15, q14, #8\n"

                    "VLDM %[Key]!, {q9-q10} \n"
                    "VLD1.32 {q13}, [%[reg]]\n"

                    /* double block */
                    "1:   \n"
                    "CMP r11, #1 \n"
                    "BEQ 2f \n"
                    "CMP r11, #0 \n"
                    "BEQ 3f   \n"

                    "VMOV.32 q0, q13\n"
                    "AESE.8 q0, q1\n"
                    "AESMC.8 q0, q0\n"
                    "VREV64.8 q13, q13 \n" /* network order */
                    "AESE.8 q0, q2\n"
                    "AESMC.8 q0, q0\n"
                    "VEXT.8 q13, q13, q13, #8 \n"
                    "SUB r11, r11, #2     \n"
                    "VADD.i32 q15, q13, q14 \n" /* add 1 to counter */
                    "VADD.i32 q13, q15, q14 \n" /* add 1 to counter */
                    "AESE.8 q0, q3\n"
                    "AESMC.8 q0, q0\n"
                    "VEXT.8 q15, q15, q15, #8 \n"
                    "VEXT.8 q13, q13, q13, #8 \n"
                    "AESE.8 q0, q4\n"
                    "AESMC.8 q0, q0\n"
                    "VREV64.8 q15, q15\n" /* revert from network order */
                    "VREV64.8 q13, q13\n" /* revert from network order */
                    "AESE.8 q0, q5\n"
                    "AESMC.8 q0, q0\n"
                    "AESE.8 q15, q1\n"
                    "AESMC.8 q15, q15\n"

                    "AESE.8 q0, q6\n"
                    "AESMC.8 q0, q0\n"
                    "AESE.8 q15, q2\n"
                    "AESMC.8 q15, q15\n"

                    "AESE.8 q0, q7\n"
                    "AESMC.8 q0, q0\n"
                    "AESE.8 q15, q3\n"
                    "AESMC.8 q15, q15\n"

                    "AESE.8 q0, q8\n"
                    "AESMC.8 q0, q0\n"
                    "AESE.8 q15, q4\n"
                    "AESMC.8 q15, q15\n"

                    "AESE.8 q0, q9\n"
                    "AESMC.8 q0, q0\n"
                    "AESE.8 q15, q5\n"
                    "AESMC.8 q15, q15\n"

                    "AESE.8 q0, q10\n"
                    "AESMC.8 q0, q0\n"
                    "VLD1.32 {q11}, [%[Key]]! \n"
                    "AESE.8 q15, q6\n"
                    "AESMC.8 q15, q15\n"

                    "AESE.8 q0, q11\n"
                    "AESMC.8 q0, q0\n"
                    "AESE.8 q15, q7\n"
                    "AESMC.8 q15, q15\n"

                    "AESE.8 q15, q8\n"
                    "AESMC.8 q15, q15\n"

                    "VLD1.32 {q12}, [%[Key]]! \n"
                    "AESE.8 q15, q9\n"
                    "AESMC.8 q15, q15\n"
                    "AESE.8 q15, q10\n"
                    "AESMC.8 q15, q15\n"

                    "AESE.8 q15, q11\n"
                    "AESMC.8 q15, q15\n"
                    "VLD1.32 {q11}, [%[Key]] \n"
                    "AESE.8 q0, q12\n"
                    "AESE.8 q15, q12\n"

                    "VLD1.32 {q12}, [%[input]]!  \n"
                    "VEOR.32 q0, q0, q11\n"
                    "VEOR.32 q15, q15, q11\n"
                    "VEOR.32 q0, q0, q12\n"

                    "VLD1.32 {q12}, [%[input]]!  \n"
                    "VST1.32 {q0}, [%[out]]!  \n"
                    "VEOR.32 q15, q15, q12\n"
                    "VST1.32 {q15}, [%[out]]!  \n"
                    "SUB %[Key], %[Key], #32 \n"

                    "B 1b \n"


                    /* single block */
                    "2:      \n"
                    "VLD1.32 {q11}, [%[Key]]! \n"
                    "VMOV.32 q0, q13  \n"
                    "AESE.8 q0, q1\n"
                    "AESMC.8 q0, q0\n"
                    "VREV64.8 q13, q13 \n" /* network order */
                    "AESE.8 q0, q2\n"
                    "AESMC.8 q0, q0\n"
                    "VEXT.8 q13, q13, q13, #8 \n"
                    "AESE.8 q0, q3\n"
                    "AESMC.8 q0, q0\n"
                    "VADD.i32 q13, q13, q14 \n" /* add 1 to counter */
                    "AESE.8 q0, q4\n"
                    "AESMC.8 q0, q0\n"
                    "SUB r11, r11, #1     \n"
                    "AESE.8 q0, q5\n"
                    "AESMC.8 q0, q0\n"
                    "VEXT.8 q13, q13, q13, #8 \n"
                    "AESE.8 q0, q6\n"
                    "AESMC.8 q0, q0\n"
                    "VREV64.8 q13, q13\n" /* revert from network order */
                    "AESE.8 q0, q7\n"
                    "AESMC.8 q0, q0\n"
                    "AESE.8 q0, q8\n"
                    "AESMC.8 q0, q0\n"
                    "AESE.8 q0, q9\n"
                    "AESMC.8 q0, q0\n"
                    "AESE.8 q0, q10\n"
                    "AESMC.8 q0, q0\n"
                    "VLD1.32 {q12}, [%[Key]]! \n"
                    "AESE.8 q0, q11\n"
                    "AESMC.8 q0, q0\n"
                    "VLD1.32 {q11}, [%[Key]] \n"
                    "AESE.8 q0, q12\n"
                    "VLD1.32 {q12}, [%[input]]! \n"
                    "VEOR.32 q0, q0, q11\n"
                    "#CTR operations, increment counter and xorbuf \n"
                    "VEOR.32 q0, q0, q12\n"
                    "VST1.32 {q0}, [%[out]]!  \n"

                    "3: \n"
                    "#store current counter qalue at the end \n"
                    "VST1.32 {q13}, [%[regOut]]   \n"

                    :[out] "=r" (out), "=r" (keyPt), [regOut] "=r" (regPt),
                     "=r" (in)
                    :"0" (out), [Key] "1" (keyPt), [input] "3" (in),
                     [blocks] "r" (numBlocks), [reg] "2" (regPt)
                    : "cc", "memory", "r11", "q0", "q1", "q2", "q3", "q4", "q5",
                    "q6", "q7", "q8", "q9", "q10","q11","q12","q13","q14"
                    );
                    break;
#endif /* WOLFSSL_AES_192 */
#ifdef WOLFSSL_AES_256
                case 14: /* AES 256 BLOCK */
                    __asm__ __volatile__ (
                    "MOV r11, %[blocks] \n"
                    "VLDM %[Key]!, {q1-q4} \n"

                    "#Create vector with the value 1  \n"
                    "VMOV.u32 q15, #1                 \n"
                    "VSHR.u64 q15, q15, #32  \n"
                    "VLDM %[Key]!, {q5-q8} \n"
                    "VEOR.32 q14, q14, q14    \n"
                    "VEXT.8 q14, q15, q14, #8\n"

                    "VLDM %[Key]!, {q9-q10} \n"
                    "VLD1.32 {q13}, [%[reg]]\n"

                    /* double block */
                    "1:      \n"
                    "CMP r11, #1 \n"
                    "BEQ 2f    \n"
                    "CMP r11, #0 \n"
                    "BEQ 3f    \n"

                    "VMOV.32 q0, q13  \n"
                    "AESE.8 q0, q1\n"
                    "AESMC.8 q0, q0\n"
                    "VREV64.8 q13, q13 \n" /* network order */
                    "AESE.8 q0, q2\n"
                    "AESMC.8 q0, q0\n"
                    "VEXT.8 q13, q13, q13, #8 \n"
                    "SUB r11, r11, #2     \n"
                    "VADD.i32 q15, q13, q14 \n" /* add 1 to counter */
                    "VADD.i32 q13, q15, q14 \n" /* add 1 to counter */
                    "AESE.8 q0, q3\n"
                    "AESMC.8 q0, q0\n"
                    "VEXT.8 q15, q15, q15, #8 \n"
                    "VEXT.8 q13, q13, q13, #8 \n"
                    "AESE.8 q0, q4\n"
                    "AESMC.8 q0, q0\n"
                    "VREV64.8 q15, q15\n" /* revert from network order */
                    "AESE.8 q0, q5\n"
                    "AESMC.8 q0, q0\n"
                    "VREV64.8 q13, q13\n" /* revert from network order */
                    "AESE.8 q15, q1\n"
                    "AESMC.8 q15, q15\n"

                    "AESE.8 q0, q6\n"
                    "AESMC.8 q0, q0\n"
                    "AESE.8 q15, q2\n"
                    "AESMC.8 q15, q15\n"

                    "AESE.8 q0, q7\n"
                    "AESMC.8 q0, q0\n"
                    "AESE.8 q15, q3\n"
                    "AESMC.8 q15, q15\n"

                    "AESE.8 q0, q8\n"
                    "AESMC.8 q0, q0\n"
                    "AESE.8 q15, q4\n"
                    "AESMC.8 q15, q15\n"

                    "AESE.8 q0, q9\n"
                    "AESMC.8 q0, q0\n"
                    "AESE.8 q15, q5\n"
                    "AESMC.8 q15, q15\n"

                    "AESE.8 q0, q10\n"
                    "AESMC.8 q0, q0\n"
                    "VLD1.32 {q11}, [%[Key]]! \n"
                    "AESE.8 q15, q6\n"
                    "AESMC.8 q15, q15\n"

                    "AESE.8 q0, q11\n"
                    "AESMC.8 q0, q0\n"
                    "AESE.8 q15, q7\n"
                    "AESMC.8 q15, q15\n"

                    "AESE.8 q15, q8\n"
                    "AESMC.8 q15, q15\n"

                    "AESE.8 q15, q9\n"
                    "AESMC.8 q15, q15\n"
                    "VLD1.32 {q12}, [%[Key]]!  \n"
                    "AESE.8 q15, q10\n"
                    "AESMC.8 q15, q15\n"

                    "AESE.8 q15, q11\n"
                    "AESMC.8 q15, q15\n"

                    "VLD1.32 {q11}, [%[Key]]! \n"
                    "AESE.8 q0, q12\n" /* rnd 12*/
                    "AESMC.8 q0, q0\n"
                    "AESE.8 q15, q12\n" /* rnd 12 */
                    "AESMC.8 q15, q15\n"

                    "VLD1.32 {q12}, [%[Key]]!  \n"
                    "AESE.8 q0, q11\n" /* rnd 13 */
                    "AESMC.8 q0, q0\n"
                    "AESE.8 q15, q11\n" /* rnd 13 */
                    "AESMC.8 q15, q15\n"

                    "VLD1.32 {q11}, [%[Key]] \n"
                    "AESE.8 q0, q12\n" /* rnd 14 */
                    "AESE.8 q15, q12\n" /* rnd 14 */

                    "VLD1.32 {q12}, [%[input]]!  \n"
                    "VEOR.32 q0, q0, q11\n" /* rnd 15 */
                    "VEOR.32 q15, q15, q11\n" /* rnd 15 */
                    "VEOR.32 q0, q0, q12\n"

                    "VLD1.32 {q12}, [%[input]]!  \n"
                    "VST1.32 {q0}, [%[out]]!  \n"
                    "VEOR.32 q15, q15, q12\n"
                    "VST1.32 {q15}, [%[out]]!  \n"
                    "SUB %[Key], %[Key], #64 \n"

                    /* single block */
                    "B 1b \n"

                    "2:      \n"
                    "VLD1.32 {q11}, [%[Key]]! \n"
                    "VMOV.32 q0, q13  \n"
                    "AESE.8 q0, q1\n"
                    "AESMC.8 q0, q0\n"
                    "VREV64.8 q13, q13 \n" /* network order */
                    "AESE.8 q0, q2\n"
                    "AESMC.8 q0, q0\n"
                    "VEXT.8 q13, q13, q13, #8 \n"
                    "AESE.8 q0, q3\n"
                    "AESMC.8 q0, q0\n"
                    "VADD.i32 q13, q13, q14 \n" /* add 1 to counter */
                    "AESE.8 q0, q4\n"
                    "AESMC.8 q0, q0\n"
                    "AESE.8 q0, q5\n"
                    "AESMC.8 q0, q0\n"
                    "VEXT.8 q13, q13, q13, #8 \n"
                    "AESE.8 q0, q6\n"
                    "AESMC.8 q0, q0\n"
                    "VREV64.8 q13, q13\n" /* revert from network order */
                    "AESE.8 q0, q7\n"
                    "AESMC.8 q0, q0\n"
                    "AESE.8 q0, q8\n"
                    "AESMC.8 q0, q0\n"
                    "AESE.8 q0, q9\n"
                    "AESMC.8 q0, q0\n"
                    "AESE.8 q0, q10\n"
                    "AESMC.8 q0, q0\n"
                    "VLD1.32 {q12}, [%[Key]]! \n"
                    "AESE.8 q0, q11\n"
                    "AESMC.8 q0, q0\n"
                    "VLD1.32 {q11}, [%[Key]]! \n"
                    "AESE.8 q0, q12\n" /* rnd 12 */
                    "AESMC.8 q0, q0\n"
                    "VLD1.32 {q12}, [%[Key]]! \n"
                    "AESE.8 q0, q11\n" /* rnd 13 */
                    "AESMC.8 q0, q0\n"
                    "VLD1.32 {q11}, [%[Key]] \n"
                    "AESE.8 q0, q12\n" /* rnd 14 */
                    "VLD1.32 {q12}, [%[input]]! \n"
                    "VEOR.32 q0, q0, q11\n" /* rnd 15 */
                    "#CTR operations, increment counter and xorbuf \n"
                    "VEOR.32 q0, q0, q12\n"
                    "VST1.32 {q0}, [%[out]]!  \n"

                    "3: \n"
                    "#store current counter qalue at the end \n"
                    "VST1.32 {q13}, [%[regOut]]   \n"

                    :[out] "=r" (out), "=r" (keyPt), [regOut] "=r" (regPt),
                     "=r" (in)
                    :"0" (out), [Key] "1" (keyPt), [input] "3" (in),
                     [blocks] "r" (numBlocks), [reg] "2" (regPt)
                    : "cc", "memory", "r11", "q0", "q1", "q2", "q3", "q4", "q5",
                    "q6", "q7", "q8", "q9", "q10","q11","q12","q13","q14"
                    );
                    break;
#endif /* WOLFSSL_AES_256 */
                default:
                    WOLFSSL_MSG("Bad AES-CTR round qalue");
                    return BAD_FUNC_ARG;
                }

                aes->left = 0;
            }

            /* handle non block size remaining */
            if (sz) {
                wc_AesEncrypt(aes, (byte*)aes->reg, (byte*)aes->tmp);
                IncrementAesCounter((byte*)aes->reg);

                aes->left = AES_BLOCK_SIZE;
                tmp = (byte*)aes->tmp;

                while (sz--) {
                    *(out++) = *(in++) ^ *(tmp++);
                    aes->left--;
                }
            }

            return 0;
        }

#endif /* WOLFSSL_AES_COUNTER */

#ifdef HAVE_AESGCM
/*
 * Uses Karatsuba algorithm. Reduction algorithm is based on "Implementing GCM
 * on ARMv8". Shifting left to account for bit reflection is based on
 * "Carry-Less Multiplication and Its Usage for Computing the GCM mode"
 */
static void GMULT(byte* X, byte* Y)
{
    __asm__ __volatile__ (
        "VLD1.32 {q0}, [%[x]] \n"

        /* In GCM format bits are big endian, switch location of bytes to
         * allow for logical shifts and carries.
         */
        "VREV64.8 q0, q0 \n"
        "VLD1.32 {q1}, [%[y]] \n" /* converted on set key */
        "VSWP.8 d0, d1 \n"

        "VMULL.p64  q5, d0, d2 \n"
        "VMULL.p64  q6, d1, d3 \n"
        "VEOR d15, d2, d3 \n"
        "VEOR d14, d0, d1 \n"
        "VMULL.p64  q7, d15, d14 \n"
        "VEOR q7, q5 \n"
        "VEOR q7, q6 \n"
        "VEOR d11, d14 \n"
        "VEOR d12, d15\n"

        /* shift to left by 1 to account for reflection */
        "VMOV q7, q6 \n"
        "VSHL.u64 q6, q6, #1 \n"
        "VSHR.u64 q7, q7, #63 \n"
        "VEOR d13, d14 \n"
        "VMOV q8, q5 \n"
        "VSHL.u64 q5, q5, #1 \n"
        "VSHR.u64 q8, q8, #63 \n"
        "VEOR d12, d17 \n"
        "VEOR d11, d16 \n"

        /* create constant 0xc200000000000000 */
        "VMOV.i32 d16, 0xc2000000 \n"
        "VSHL.u64 d16, d16, #32 \n"

        /* reduce product of multiplication */
        "VMULL.p64 q9, d10, d16 \n"
        "VEOR d11, d18 \n"
        "VEOR d12, d19 \n"
        "VMULL.p64 q9, d11, d16 \n"
        "VEOR q6, q9 \n"
        "VEOR q10, q5, q6 \n"

        /* convert to GCM format */
        "VREV64.8 q10, q10 \n"
        "VSWP.8 d20, d21 \n"

        "VST1.32 {q10}, [%[xOut]] \n"

        : [xOut] "=r" (X), [yOut] "=r" (Y)
        : [x] "0" (X), [y] "1" (Y)
        : "cc", "memory", "q0", "q1", "q2", "q3", "q4", "q5", "q6" ,"q7", "q8",
        "q9", "q10", "q11" ,"q12", "q13", "q14", "q15"
    );
}


void GHASH(Aes* aes, const byte* a, word32 aSz,
                                const byte* c, word32 cSz, byte* s, word32 sSz)
{
    byte x[AES_BLOCK_SIZE];
    byte scratch[AES_BLOCK_SIZE];
    word32 blocks, partial;
    byte* h = aes->H;

    XMEMSET(x, 0, AES_BLOCK_SIZE);

    /* Hash in A, the Additional Authentication Data */
    if (aSz != 0 && a != NULL) {
        blocks = aSz / AES_BLOCK_SIZE;
        partial = aSz % AES_BLOCK_SIZE;
        while (blocks--) {
            xorbuf(x, a, AES_BLOCK_SIZE);
            GMULT(x, h);
            a += AES_BLOCK_SIZE;
        }
        if (partial != 0) {
            XMEMSET(scratch, 0, AES_BLOCK_SIZE);
            XMEMCPY(scratch, a, partial);
            xorbuf(x, scratch, AES_BLOCK_SIZE);
            GMULT(x, h);
        }
    }

    /* Hash in C, the Ciphertext */
    if (cSz != 0 && c != NULL) {
        blocks = cSz / AES_BLOCK_SIZE;
        partial = cSz % AES_BLOCK_SIZE;
        while (blocks--) {
            xorbuf(x, c, AES_BLOCK_SIZE);
            GMULT(x, h);
            c += AES_BLOCK_SIZE;
        }
        if (partial != 0) {
            XMEMSET(scratch, 0, AES_BLOCK_SIZE);
            XMEMCPY(scratch, c, partial);
            xorbuf(x, scratch, AES_BLOCK_SIZE);
            GMULT(x, h);
        }
    }

    /* Hash in the lengths of A and C in bits */
    FlattenSzInBits(&scratch[0], aSz);
    FlattenSzInBits(&scratch[8], cSz);
    xorbuf(x, scratch, AES_BLOCK_SIZE);
    GMULT(x, h);

    /* Copy the result into s. */
    XMEMCPY(s, x, sSz);
}


/* Aarch32
 * Encrypt and tag data using AES with GCM mode.
 * aes: Aes structure having already been set with set key function
 * out: encrypted data output buffer
 * in:  plain text input buffer
 * sz:  size of plain text and out buffer
 * iv:  initialization vector
 * ivSz:      size of iv buffer
 * authTag:   buffer to hold tag
 * authTagSz: size of tag buffer
 * authIn:    additional data buffer
 * authInSz:  size of additional data buffer
 */
int wc_AesGcmEncrypt(Aes* aes, byte* out, const byte* in, word32 sz,
                   const byte* iv, word32 ivSz,
                   byte* authTag, word32 authTagSz,
                   const byte* authIn, word32 authInSz)
{
    word32 blocks = sz / AES_BLOCK_SIZE;
    word32 partial = sz % AES_BLOCK_SIZE;
    const byte* p = in;
    byte* c = out;
    byte counter[AES_BLOCK_SIZE];
    byte initialCounter[AES_BLOCK_SIZE];
    byte *ctr ;
    byte scratch[AES_BLOCK_SIZE];
    ctr = counter ;

    /* sanity checks */
    if (aes == NULL || (iv == NULL && ivSz > 0) ||
                       (authTag == NULL) ||
                       (authIn == NULL && authInSz > 0) ||
                       (in == NULL && sz > 0) ||
                       (out == NULL && sz > 0)) {
        WOLFSSL_MSG("a NULL parameter passed in when size is larger than 0");
        return BAD_FUNC_ARG;
    }

    if (authTagSz < WOLFSSL_MIN_AUTH_TAG_SZ || authTagSz > AES_BLOCK_SIZE) {
        WOLFSSL_MSG("GcmEncrypt authTagSz error");
        return BAD_FUNC_ARG;
    }

    XMEMSET(initialCounter, 0, AES_BLOCK_SIZE);
    if (ivSz == GCM_NONCE_MID_SZ) {
        XMEMCPY(initialCounter, iv, ivSz);
        initialCounter[AES_BLOCK_SIZE - 1] = 1;
    }
    else {
        GHASH(aes, NULL, 0, iv, ivSz, initialCounter, AES_BLOCK_SIZE);
    }
    XMEMCPY(ctr, initialCounter, AES_BLOCK_SIZE);

    while (blocks--) {
        IncrementGcmCounter(ctr);
        wc_AesEncrypt(aes, ctr, scratch);
        xorbuf(scratch, p, AES_BLOCK_SIZE);
        XMEMCPY(c, scratch, AES_BLOCK_SIZE);
        p += AES_BLOCK_SIZE;
        c += AES_BLOCK_SIZE;
    }

    if (partial != 0) {
        IncrementGcmCounter(ctr);
        wc_AesEncrypt(aes, ctr, scratch);
        xorbuf(scratch, p, partial);
        XMEMCPY(c, scratch, partial);

    }

    GHASH(aes, authIn, authInSz, out, sz, authTag, authTagSz);
    wc_AesEncrypt(aes, initialCounter, scratch);
    if (authTagSz > AES_BLOCK_SIZE) {
        xorbuf(authTag, scratch, AES_BLOCK_SIZE);
    }
    else {
        xorbuf(authTag, scratch, authTagSz);
    }

    return 0;
}


#ifdef HAVE_AES_DECRYPT
/*
 * Check tag and decrypt data using AES with GCM mode.
 * aes: Aes structure having already been set with set key function
 * out: decrypted data output buffer
 * in:  cipher text buffer
 * sz:  size of plain text and out buffer
 * iv:  initialization vector
 * ivSz:      size of iv buffer
 * authTag:   buffer holding tag
 * authTagSz: size of tag buffer
 * authIn:    additional data buffer
 * authInSz:  size of additional data buffer
 */
int  wc_AesGcmDecrypt(Aes* aes, byte* out, const byte* in, word32 sz,
                   const byte* iv, word32 ivSz,
                   const byte* authTag, word32 authTagSz,
                   const byte* authIn, word32 authInSz)
{
    word32 blocks = sz / AES_BLOCK_SIZE;
    word32 partial = sz % AES_BLOCK_SIZE;
    const byte* c = in;
    byte* p = out;
    byte counter[AES_BLOCK_SIZE];
    byte initialCounter[AES_BLOCK_SIZE];
    byte *ctr ;
    byte scratch[AES_BLOCK_SIZE];
    ctr = counter ;

    /* sanity checks */
    if (aes == NULL || (iv == NULL && ivSz > 0) ||
                       (authTag == NULL) ||
                       (authIn == NULL && authInSz > 0) ||
                       (in  == NULL && sz > 0) ||
                       (out == NULL && sz > 0)) {
        WOLFSSL_MSG("a NULL parameter passed in when size is larger than 0");
        return BAD_FUNC_ARG;
    }

    XMEMSET(initialCounter, 0, AES_BLOCK_SIZE);
    if (ivSz == GCM_NONCE_MID_SZ) {
        XMEMCPY(initialCounter, iv, ivSz);
        initialCounter[AES_BLOCK_SIZE - 1] = 1;
    }
    else {
        GHASH(aes, NULL, 0, iv, ivSz, initialCounter, AES_BLOCK_SIZE);
    }
    XMEMCPY(ctr, initialCounter, AES_BLOCK_SIZE);

    /* Calculate the authTag again using the received auth data and the
     * cipher text. */
    {
        byte Tprime[AES_BLOCK_SIZE];
        byte EKY0[AES_BLOCK_SIZE];

        GHASH(aes, authIn, authInSz, in, sz, Tprime, sizeof(Tprime));
        wc_AesEncrypt(aes, ctr, EKY0);
        xorbuf(Tprime, EKY0, sizeof(Tprime));

        if (ConstantCompare(authTag, Tprime, authTagSz) != 0) {
            return AES_GCM_AUTH_E;
        }
    }

    while (blocks--) {
        IncrementGcmCounter(ctr);
        wc_AesEncrypt(aes, ctr, scratch);
        xorbuf(scratch, c, AES_BLOCK_SIZE);
        XMEMCPY(p, scratch, AES_BLOCK_SIZE);
        p += AES_BLOCK_SIZE;
        c += AES_BLOCK_SIZE;
    }
    if (partial != 0) {
        IncrementGcmCounter(ctr);
        wc_AesEncrypt(aes, ctr, scratch);

        /* check if pointer is null after main AES-GCM blocks
         * helps static analysis */
        if (p == NULL || c == NULL) {
            return BAD_STATE_E;
        }
        xorbuf(scratch, c, partial);
        XMEMCPY(p, scratch, partial);
    }
    return 0;
}
#endif /* HAVE_AES_DECRYPT */
#endif /* HAVE_AESGCM */

#endif /* aarch64 */


#ifdef HAVE_AESCCM
/* Software version of AES-CCM from wolfcrypt/src/aes.c
 * Gets some speed up from hardware acceleration of wc_AesEncrypt */

static void roll_x(Aes* aes, const byte* in, word32 inSz, byte* out)
{
    /* process the bulk of the data */
    while (inSz >= AES_BLOCK_SIZE) {
        xorbuf(out, in, AES_BLOCK_SIZE);
        in += AES_BLOCK_SIZE;
        inSz -= AES_BLOCK_SIZE;

        wc_AesEncrypt(aes, out, out);
    }

    /* process remainder of the data */
    if (inSz > 0) {
        xorbuf(out, in, inSz);
        wc_AesEncrypt(aes, out, out);
    }
}


static void roll_auth(Aes* aes, const byte* in, word32 inSz, byte* out)
{
    word32 authLenSz;
    word32 remainder;

    /* encode the length in */
    if (inSz <= 0xFEFF) {
        authLenSz = 2;
        out[0] ^= ((inSz & 0xFF00) >> 8);
        out[1] ^=  (inSz & 0x00FF);
    }
    else if (inSz <= 0xFFFFFFFF) {
        authLenSz = 6;
        out[0] ^= 0xFF; out[1] ^= 0xFE;
        out[2] ^= ((inSz & 0xFF000000) >> 24);
        out[3] ^= ((inSz & 0x00FF0000) >> 16);
        out[4] ^= ((inSz & 0x0000FF00) >>  8);
        out[5] ^=  (inSz & 0x000000FF);
    }
    /* Note, the protocol handles auth data up to 2^64, but we are
     * using 32-bit sizes right now, so the bigger data isn't handled
     * else if (inSz <= 0xFFFFFFFFFFFFFFFF) {} */
    else
        return;

    /* start fill out the rest of the first block */
    remainder = AES_BLOCK_SIZE - authLenSz;
    if (inSz >= remainder) {
        /* plenty of bulk data to fill the remainder of this block */
        xorbuf(out + authLenSz, in, remainder);
        inSz -= remainder;
        in += remainder;
    }
    else {
        /* not enough bulk data, copy what is available, and pad zero */
        xorbuf(out + authLenSz, in, inSz);
        inSz = 0;
    }
    wc_AesEncrypt(aes, out, out);

    if (inSz > 0)
        roll_x(aes, in, inSz, out);
}


static WC_INLINE void AesCcmCtrInc(byte* B, word32 lenSz)
{
    word32 i;

    for (i = 0; i < lenSz; i++) {
        if (++B[AES_BLOCK_SIZE - 1 - i] != 0) return;
    }
}


/* return 0 on success */
int wc_AesCcmEncrypt(Aes* aes, byte* out, const byte* in, word32 inSz,
                   const byte* nonce, word32 nonceSz,
                   byte* authTag, word32 authTagSz,
                   const byte* authIn, word32 authInSz)
{
    byte A[AES_BLOCK_SIZE];
    byte B[AES_BLOCK_SIZE];
    byte lenSz;
    word32 i;
    byte mask     = 0xFF;
    word32 wordSz = (word32)sizeof(word32);

    /* sanity check on arguments */
    if (aes == NULL || out == NULL || in == NULL || nonce == NULL
            || authTag == NULL || nonceSz < 7 || nonceSz > 13)
        return BAD_FUNC_ARG;

    XMEMCPY(B+1, nonce, nonceSz);
    lenSz = AES_BLOCK_SIZE - 1 - (byte)nonceSz;
    B[0] = (authInSz > 0 ? 64 : 0)
         + (8 * (((byte)authTagSz - 2) / 2))
         + (lenSz - 1);
    for (i = 0; i < lenSz; i++) {
        if (mask && i >= wordSz)
            mask = 0x00;
        B[AES_BLOCK_SIZE - 1 - i] = (inSz >> ((8 * i) & mask)) & mask;
    }

    wc_AesEncrypt(aes, B, A);

    if (authInSz > 0)
        roll_auth(aes, authIn, authInSz, A);
    if (inSz > 0)
        roll_x(aes, in, inSz, A);
    XMEMCPY(authTag, A, authTagSz);

    B[0] = lenSz - 1;
    for (i = 0; i < lenSz; i++)
        B[AES_BLOCK_SIZE - 1 - i] = 0;
    wc_AesEncrypt(aes, B, A);
    xorbuf(authTag, A, authTagSz);

    B[15] = 1;
    while (inSz >= AES_BLOCK_SIZE) {
        wc_AesEncrypt(aes, B, A);
        xorbuf(A, in, AES_BLOCK_SIZE);
        XMEMCPY(out, A, AES_BLOCK_SIZE);

        AesCcmCtrInc(B, lenSz);
        inSz -= AES_BLOCK_SIZE;
        in += AES_BLOCK_SIZE;
        out += AES_BLOCK_SIZE;
    }
    if (inSz > 0) {
        wc_AesEncrypt(aes, B, A);
        xorbuf(A, in, inSz);
        XMEMCPY(out, A, inSz);
    }

    ForceZero(A, AES_BLOCK_SIZE);
    ForceZero(B, AES_BLOCK_SIZE);

    return 0;
}

#ifdef HAVE_AES_DECRYPT
int  wc_AesCcmDecrypt(Aes* aes, byte* out, const byte* in, word32 inSz,
                   const byte* nonce, word32 nonceSz,
                   const byte* authTag, word32 authTagSz,
                   const byte* authIn, word32 authInSz)
{
    byte A[AES_BLOCK_SIZE];
    byte B[AES_BLOCK_SIZE];
    byte* o;
    byte lenSz;
    word32 i, oSz;
    int result = 0;
    byte mask     = 0xFF;
    word32 wordSz = (word32)sizeof(word32);

    /* sanity check on arguments */
    if (aes == NULL || out == NULL || in == NULL || nonce == NULL
            || authTag == NULL || nonceSz < 7 || nonceSz > 13)
        return BAD_FUNC_ARG;

    o = out;
    oSz = inSz;
    XMEMCPY(B+1, nonce, nonceSz);
    lenSz = AES_BLOCK_SIZE - 1 - (byte)nonceSz;

    B[0] = lenSz - 1;
    for (i = 0; i < lenSz; i++)
        B[AES_BLOCK_SIZE - 1 - i] = 0;
    B[15] = 1;

    while (oSz >= AES_BLOCK_SIZE) {
        wc_AesEncrypt(aes, B, A);
        xorbuf(A, in, AES_BLOCK_SIZE);
        XMEMCPY(o, A, AES_BLOCK_SIZE);

        AesCcmCtrInc(B, lenSz);
        oSz -= AES_BLOCK_SIZE;
        in += AES_BLOCK_SIZE;
        o += AES_BLOCK_SIZE;
    }
    if (inSz > 0) {
        wc_AesEncrypt(aes, B, A);
        xorbuf(A, in, oSz);
        XMEMCPY(o, A, oSz);
    }

    for (i = 0; i < lenSz; i++)
        B[AES_BLOCK_SIZE - 1 - i] = 0;
    wc_AesEncrypt(aes, B, A);

    o = out;
    oSz = inSz;

    B[0] = (authInSz > 0 ? 64 : 0)
         + (8 * (((byte)authTagSz - 2) / 2))
         + (lenSz - 1);
    for (i = 0; i < lenSz; i++) {
        if (mask && i >= wordSz)
            mask = 0x00;
        B[AES_BLOCK_SIZE - 1 - i] = (inSz >> ((8 * i) & mask)) & mask;
    }

    wc_AesEncrypt(aes, B, A);

    if (authInSz > 0)
        roll_auth(aes, authIn, authInSz, A);
    if (inSz > 0)
        roll_x(aes, o, oSz, A);

    B[0] = lenSz - 1;
    for (i = 0; i < lenSz; i++)
        B[AES_BLOCK_SIZE - 1 - i] = 0;
    wc_AesEncrypt(aes, B, B);
    xorbuf(A, B, authTagSz);

    if (ConstantCompare(A, authTag, authTagSz) != 0) {
        /* If the authTag check fails, don't keep the decrypted data.
         * Unfortunately, you need the decrypted data to calculate the
         * check value. */
        XMEMSET(out, 0, inSz);
        result = AES_CCM_AUTH_E;
    }

    ForceZero(A, AES_BLOCK_SIZE);
    ForceZero(B, AES_BLOCK_SIZE);
    o = NULL;

    return result;
}
#endif /* HAVE_AES_DECRYPT */
#endif /* HAVE_AESCCM */



#ifdef HAVE_AESGCM /* common GCM functions 32 and 64 bit */
int wc_AesGcmSetKey(Aes* aes, const byte* key, word32 len)
{
    int  ret;
    byte iv[AES_BLOCK_SIZE];

    if (!((len == 16) || (len == 24) || (len == 32)))
        return BAD_FUNC_ARG;

    XMEMSET(iv, 0, AES_BLOCK_SIZE);
    ret = wc_AesSetKey(aes, key, len, iv, AES_ENCRYPTION);

    if (ret == 0) {
        wc_AesEncrypt(aes, iv, aes->H);
    #if defined(__aarch64__)
        {
            word32* pt = (word32*)aes->H;
            __asm__ volatile (
                "LD1 {v0.16b}, [%[h]] \n"
                "RBIT v0.16b, v0.16b \n"
                "ST1 {v0.16b}, [%[out]] \n"
                : [out] "=r" (pt)
                : [h] "0" (pt)
                : "cc", "memory", "v0"
            );
        }
    #else
        {
            word32* pt = (word32*)aes->H;
            __asm__ volatile (
                "VLD1.32 {q0}, [%[h]] \n"
                "VREV64.8 q0, q0 \n"
                "VSWP.8 d0, d1 \n"
                "VST1.32 {q0}, [%[out]] \n"
                : [out] "=r" (pt)
                : [h] "0" (pt)
                : "cc", "memory", "q0"
            );
        }
    #endif
    }

    return ret;
}

#endif /* HAVE_AESGCM */

/* AES-DIRECT */
#if defined(WOLFSSL_AES_DIRECT)
        /* Allow direct access to one block encrypt */
        void wc_AesEncryptDirect(Aes* aes, byte* out, const byte* in)
        {
            if (aes == NULL || out == NULL || in == NULL) {
                WOLFSSL_MSG("Invalid input to wc_AesEncryptDirect");
                return;
            }
            wc_AesEncrypt(aes, in, out);
        }
    #ifdef HAVE_AES_DECRYPT
        /* Allow direct access to one block decrypt */
        void wc_AesDecryptDirect(Aes* aes, byte* out, const byte* in)
        {
            if (aes == NULL || out == NULL || in == NULL) {
                WOLFSSL_MSG("Invalid input to wc_AesDecryptDirect");
                return;
            }
            wc_AesDecrypt(aes, in, out);
        }
    #endif /* HAVE_AES_DECRYPT */
#endif /* WOLFSSL_AES_DIRECT */
#endif /* !NO_AES && WOLFSSL_ARMASM */
