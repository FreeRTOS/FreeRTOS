/* sha.c
 *
 * Copyright (C) 2006-2014 wolfSSL Inc.
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
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301, USA
 */


#ifdef HAVE_CONFIG_H
    #include <config.h>
#endif

#include <cyassl/ctaocrypt/settings.h>

#if !defined(NO_SHA)

#ifdef CYASSL_PIC32MZ_HASH
#define InitSha   InitSha_sw
#define ShaUpdate ShaUpdate_sw
#define ShaFinal  ShaFinal_sw
#endif

#ifdef HAVE_FIPS
    /* set NO_WRAPPERS before headers, use direct internal f()s not wrappers */
    #define FIPS_NO_WRAPPERS
#endif

#include <cyassl/ctaocrypt/sha.h>
#include <cyassl/ctaocrypt/logging.h>
#include <cyassl/ctaocrypt/error-crypt.h>

#ifdef NO_INLINE
    #include <cyassl/ctaocrypt/misc.h>
#else
    #include <ctaocrypt/src/misc.c>
#endif

#ifdef FREESCALE_MMCAU
    #include "cau_api.h"
    #define XTRANSFORM(S,B)  cau_sha1_hash_n((B), 1, ((S))->digest)
#else
    #define XTRANSFORM(S,B)  Transform((S))
#endif


#ifdef STM32F2_HASH
    /*
     * STM32F2 hardware SHA1 support through the STM32F2 standard peripheral
     * library. Documentation located in STM32F2xx Standard Peripheral Library
     * document (See note in README).
     */
    #include "stm32f2xx.h"
    #include "stm32f2xx_hash.h"

    int InitSha(Sha* sha)
    {
        /* STM32F2 struct notes:
         * sha->buffer  = first 4 bytes used to hold partial block if needed 
         * sha->buffLen = num bytes currently stored in sha->buffer
         * sha->loLen   = num bytes that have been written to STM32 FIFO
         */
        XMEMSET(sha->buffer, 0, SHA_REG_SIZE);
        sha->buffLen = 0;
        sha->loLen = 0;

        /* initialize HASH peripheral */
        HASH_DeInit();

        /* configure algo used, algo mode, datatype */
        HASH->CR &= ~ (HASH_CR_ALGO | HASH_CR_DATATYPE | HASH_CR_MODE);
        HASH->CR |= (HASH_AlgoSelection_SHA1 | HASH_AlgoMode_HASH 
                 | HASH_DataType_8b);

        /* reset HASH processor */
        HASH->CR |= HASH_CR_INIT;

        return 0;
    }

    int ShaUpdate(Sha* sha, const byte* data, word32 len)
    {
        word32 i = 0;
        word32 fill = 0;
        word32 diff = 0;

        /* if saved partial block is available */
        if (sha->buffLen) {
            fill = 4 - sha->buffLen;

            /* if enough data to fill, fill and push to FIFO */
            if (fill <= len) {
                XMEMCPY((byte*)sha->buffer + sha->buffLen, data, fill);
                HASH_DataIn(*(uint32_t*)sha->buffer);

                data += fill;
                len -= fill;
                sha->loLen += 4;
                sha->buffLen = 0;
            } else {
                /* append partial to existing stored block */
                XMEMCPY((byte*)sha->buffer + sha->buffLen, data, len);
                sha->buffLen += len;
                return;
            }
        }
       
        /* write input block in the IN FIFO */
        for(i = 0; i < len; i += 4)
        {
            diff = len - i;
            if ( diff < 4) {
                /* store incomplete last block, not yet in FIFO */
                XMEMSET(sha->buffer, 0, SHA_REG_SIZE);
                XMEMCPY((byte*)sha->buffer, data, diff);
                sha->buffLen = diff;
            } else {
                HASH_DataIn(*(uint32_t*)data);
                data+=4;
            }
        }

        /* keep track of total data length thus far */ 
        sha->loLen += (len - sha->buffLen);

        return 0;
    }

    int ShaFinal(Sha* sha, byte* hash)
    {
        __IO uint16_t nbvalidbitsdata = 0;
        
        /* finish reading any trailing bytes into FIFO */
        if (sha->buffLen) {
            HASH_DataIn(*(uint32_t*)sha->buffer);
            sha->loLen += sha->buffLen;
        }

        /* calculate number of valid bits in last word of input data */
        nbvalidbitsdata = 8 * (sha->loLen % SHA_REG_SIZE);

        /* configure number of valid bits in last word of the data */
        HASH_SetLastWordValidBitsNbr(nbvalidbitsdata);

        /* start HASH processor */
        HASH_StartDigest();

        /* wait until Busy flag == RESET */
        while (HASH_GetFlagStatus(HASH_FLAG_BUSY) != RESET) {}

        /* read message digest */
        sha->digest[0] = HASH->HR[0];
        sha->digest[1] = HASH->HR[1];
        sha->digest[2] = HASH->HR[2];
        sha->digest[3] = HASH->HR[3];
        sha->digest[4] = HASH->HR[4];
        
        ByteReverseWords(sha->digest, sha->digest, SHA_DIGEST_SIZE);

        XMEMCPY(hash, sha->digest, SHA_DIGEST_SIZE);

        return InitSha(sha);  /* reset state */
    }

#else /* CTaoCrypt software implementation */

#ifndef min

    static INLINE word32 min(word32 a, word32 b)
    {
        return a > b ? b : a;
    }

#endif /* min */


int InitSha(Sha* sha)
{
    #ifdef FREESCALE_MMCAU
        cau_sha1_initialize_output(sha->digest);
    #else
        sha->digest[0] = 0x67452301L;
        sha->digest[1] = 0xEFCDAB89L;
        sha->digest[2] = 0x98BADCFEL;
        sha->digest[3] = 0x10325476L;
        sha->digest[4] = 0xC3D2E1F0L;
    #endif

    sha->buffLen = 0;
    sha->loLen   = 0;
    sha->hiLen   = 0;

    return 0;
}

#ifndef FREESCALE_MMCAU

#define blk0(i) (W[i] = sha->buffer[i])
#define blk1(i) (W[i&15] = \
                   rotlFixed(W[(i+13)&15]^W[(i+8)&15]^W[(i+2)&15]^W[i&15],1))

#define f1(x,y,z) (z^(x &(y^z)))
#define f2(x,y,z) (x^y^z)
#define f3(x,y,z) ((x&y)|(z&(x|y)))
#define f4(x,y,z) (x^y^z)

/* (R0+R1), R2, R3, R4 are the different operations used in SHA1 */
#define R0(v,w,x,y,z,i) z+= f1(w,x,y) + blk0(i) + 0x5A827999+ \
                        rotlFixed(v,5); w = rotlFixed(w,30);
#define R1(v,w,x,y,z,i) z+= f1(w,x,y) + blk1(i) + 0x5A827999+ \
                        rotlFixed(v,5); w = rotlFixed(w,30);
#define R2(v,w,x,y,z,i) z+= f2(w,x,y) + blk1(i) + 0x6ED9EBA1+ \
                        rotlFixed(v,5); w = rotlFixed(w,30);
#define R3(v,w,x,y,z,i) z+= f3(w,x,y) + blk1(i) + 0x8F1BBCDC+ \
                        rotlFixed(v,5); w = rotlFixed(w,30);
#define R4(v,w,x,y,z,i) z+= f4(w,x,y) + blk1(i) + 0xCA62C1D6+ \
                        rotlFixed(v,5); w = rotlFixed(w,30);


static void Transform(Sha* sha)
{
    word32 W[SHA_BLOCK_SIZE / sizeof(word32)];

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
    /* nearly 1 K bigger in code size but 25% faster  */
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
}

#endif /* FREESCALE_MMCAU */


static INLINE void AddLength(Sha* sha, word32 len)
{
    word32 tmp = sha->loLen;
    if ( (sha->loLen += len) < tmp)
        sha->hiLen++;                       /* carry low to high */
}


int ShaUpdate(Sha* sha, const byte* data, word32 len)
{
    /* do block size increments */
    byte* local = (byte*)sha->buffer;

    while (len) {
        word32 add = min(len, SHA_BLOCK_SIZE - sha->buffLen);
        XMEMCPY(&local[sha->buffLen], data, add);

        sha->buffLen += add;
        data         += add;
        len          -= add;

        if (sha->buffLen == SHA_BLOCK_SIZE) {
            #if defined(LITTLE_ENDIAN_ORDER) && !defined(FREESCALE_MMCAU)
                ByteReverseWords(sha->buffer, sha->buffer, SHA_BLOCK_SIZE);
            #endif
            XTRANSFORM(sha, local);
            AddLength(sha, SHA_BLOCK_SIZE);
            sha->buffLen = 0;
        }
    }

    return 0;
}


int ShaFinal(Sha* sha, byte* hash)
{
    byte* local = (byte*)sha->buffer;

    AddLength(sha, sha->buffLen);  /* before adding pads */

    local[sha->buffLen++] = 0x80;  /* add 1 */

    /* pad with zeros */
    if (sha->buffLen > SHA_PAD_SIZE) {
        XMEMSET(&local[sha->buffLen], 0, SHA_BLOCK_SIZE - sha->buffLen);
        sha->buffLen += SHA_BLOCK_SIZE - sha->buffLen;

        #if defined(LITTLE_ENDIAN_ORDER) && !defined(FREESCALE_MMCAU)
            ByteReverseWords(sha->buffer, sha->buffer, SHA_BLOCK_SIZE);
        #endif
        XTRANSFORM(sha, local);
        sha->buffLen = 0;
    }
    XMEMSET(&local[sha->buffLen], 0, SHA_PAD_SIZE - sha->buffLen);
   
    /* put lengths in bits */
    sha->hiLen = (sha->loLen >> (8*sizeof(sha->loLen) - 3)) + 
                 (sha->hiLen << 3);
    sha->loLen = sha->loLen << 3;

    /* store lengths */
    #if defined(LITTLE_ENDIAN_ORDER) && !defined(FREESCALE_MMCAU)
        ByteReverseWords(sha->buffer, sha->buffer, SHA_BLOCK_SIZE);
    #endif
    /* ! length ordering dependent on digest endian type ! */
    XMEMCPY(&local[SHA_PAD_SIZE], &sha->hiLen, sizeof(word32));
    XMEMCPY(&local[SHA_PAD_SIZE + sizeof(word32)], &sha->loLen, sizeof(word32));

    #ifdef FREESCALE_MMCAU
        /* Kinetis requires only these bytes reversed */
        ByteReverseWords(&sha->buffer[SHA_PAD_SIZE/sizeof(word32)],
                         &sha->buffer[SHA_PAD_SIZE/sizeof(word32)],
                         2 * sizeof(word32));
    #endif

    XTRANSFORM(sha, local);
    #ifdef LITTLE_ENDIAN_ORDER
        ByteReverseWords(sha->digest, sha->digest, SHA_DIGEST_SIZE);
    #endif
    XMEMCPY(hash, sha->digest, SHA_DIGEST_SIZE);

    return InitSha(sha);  /* reset state */
}

#endif /* STM32F2_HASH */


int ShaHash(const byte* data, word32 len, byte* hash)
{
    int ret = 0;
#ifdef CYASSL_SMALL_STACK
    Sha* sha;
#else
    Sha sha[1];
#endif

#ifdef CYASSL_SMALL_STACK
    sha = (Sha*)XMALLOC(sizeof(Sha), NULL, DYNAMIC_TYPE_TMP_BUFFER);
    if (sha == NULL)
        return MEMORY_E;
#endif

    if ((ret = InitSha(sha)) != 0) {
        CYASSL_MSG("InitSha failed");
    }
    else {
        ShaUpdate(sha, data, len);
        ShaFinal(sha, hash);
    }

#ifdef CYASSL_SMALL_STACK
    XFREE(sha, NULL, DYNAMIC_TYPE_TMP_BUFFER);
#endif

    return ret;
}

#endif /* NO_SHA */
