/* stm32.c
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

/* Generic STM32 Hashing Function */
/* Supports CubeMX HAL or Standard Peripheral Library */

#ifdef HAVE_CONFIG_H
    #include <config.h>
#endif

#include <wolfssl/wolfcrypt/settings.h>

#include <wolfssl/wolfcrypt/port/st/stm32.h>
#include <wolfssl/wolfcrypt/types.h>
#include <wolfssl/wolfcrypt/error-crypt.h>

#ifdef NO_INLINE
    #include <wolfssl/wolfcrypt/misc.h>
#else
    #define WOLFSSL_MISC_INCLUDED
    #include <wolfcrypt/src/misc.c>
#endif

#ifndef NO_AES
    #include <wolfssl/wolfcrypt/aes.h>
#endif


#ifdef STM32_HASH

#ifdef WOLFSSL_STM32L4
    #define HASH_STR_NBW HASH_STR_NBLW
#endif

/* User can override STM32_HASH_CLOCK_ENABLE and STM32_HASH_CLOCK_DISABLE */
#ifndef STM32_HASH_CLOCK_ENABLE
    static WC_INLINE void wc_Stm32_Hash_Clock_Enable(STM32_HASH_Context* stmCtx)
    {
    #ifdef WOLFSSL_STM32_CUBEMX
        __HAL_RCC_HASH_CLK_ENABLE();
    #else
        RCC_AHB2PeriphClockCmd(RCC_AHB2Periph_HASH, ENABLE);
    #endif
        (void)stmCtx;
    }
    #define STM32_HASH_CLOCK_ENABLE(ctx) wc_Stm32_Hash_Clock_Enable(ctx)
#endif

#ifndef STM32_HASH_CLOCK_DISABLE
    static WC_INLINE void wc_Stm32_Hash_Clock_Disable(STM32_HASH_Context* stmCtx)
    {
    #ifdef WOLFSSL_STM32_CUBEMX
        __HAL_RCC_HASH_CLK_DISABLE();
    #else
        RCC_AHB2PeriphClockCmd(RCC_AHB2Periph_HASH, DISABLE);
    #endif
        (void)stmCtx;
    }
    #define STM32_HASH_CLOCK_DISABLE(ctx) wc_Stm32_Hash_Clock_Disable(ctx)
#endif

/* STM32 Port Internal Functions */
static WC_INLINE void wc_Stm32_Hash_SaveContext(STM32_HASH_Context* ctx)
{
    int i;

    /* save context registers */
    ctx->HASH_IMR = HASH->IMR;
    ctx->HASH_STR = HASH->STR;
    ctx->HASH_CR  = HASH->CR;
    for (i=0; i<HASH_CR_SIZE; i++) {
        ctx->HASH_CSR[i] = HASH->CSR[i];
    }
}

static WC_INLINE int wc_Stm32_Hash_RestoreContext(STM32_HASH_Context* ctx)
{
    int i;

    if (ctx->HASH_CR != 0) {
        /* restore context registers */
        HASH->IMR = ctx->HASH_IMR;
        HASH->STR = ctx->HASH_STR;
        HASH->CR = ctx->HASH_CR;

        /* Initialize the hash processor */
        HASH->CR |= HASH_CR_INIT;

        /* continue restoring context registers */
        for (i=0; i<HASH_CR_SIZE; i++) {
            HASH->CSR[i] = ctx->HASH_CSR[i];
        }
        return 1;
    }
    return 0;
}

static WC_INLINE void wc_Stm32_Hash_GetDigest(byte* hash, int digestSize)
{
    word32 digest[HASH_MAX_DIGEST/sizeof(word32)];

    /* get digest result */
    digest[0] = HASH->HR[0];
    digest[1] = HASH->HR[1];
    digest[2] = HASH->HR[2];
    digest[3] = HASH->HR[3];
    if (digestSize >= 20) {
        digest[4] = HASH->HR[4];
    #ifdef HASH_DIGEST
        if (digestSize >= 28) {
            digest[5] = HASH_DIGEST->HR[5];
            digest[6] = HASH_DIGEST->HR[6];
            if (digestSize == 32)
                digest[7] = HASH_DIGEST->HR[7];
        }
    #endif
    }

    ByteReverseWords(digest, digest, digestSize);

    XMEMCPY(hash, digest, digestSize);
}


/* STM32 Port Exposed Functions */
static WC_INLINE int wc_Stm32_Hash_WaitDone(void)
{
    /* wait until hash hardware is not busy */
    int timeout = 0;
    while ((HASH->SR & HASH_SR_BUSY) && ++timeout < STM32_HASH_TIMEOUT) {

    }
    /* verify timeout did not occur */
    if (timeout >= STM32_HASH_TIMEOUT) {
        return WC_TIMEOUT_E;
    }
    return 0;
}


void wc_Stm32_Hash_Init(STM32_HASH_Context* stmCtx)
{
    /* clear context */
    XMEMSET(stmCtx, 0, sizeof(STM32_HASH_Context));
}

int wc_Stm32_Hash_Update(STM32_HASH_Context* stmCtx, word32 algo,
    const byte* data, int len)
{
    int ret = 0;
    byte* local = (byte*)stmCtx->buffer;
    int wroteToFifo = 0;

    /* check that internal buffLen is valid */
    if (stmCtx->buffLen >= STM32_HASH_REG_SIZE) {
        return BUFFER_E;
    }

    /* turn on hash clock */
    STM32_HASH_CLOCK_ENABLE(stmCtx);

    /* restore hash context or init as new hash */
    if (wc_Stm32_Hash_RestoreContext(stmCtx) == 0) {
        /* reset the control register */
        HASH->CR &= ~(HASH_CR_ALGO | HASH_CR_DATATYPE | HASH_CR_MODE);

        /* configure algorithm, mode and data type */
        HASH->CR |= (algo | HASH_ALGOMODE_HASH | HASH_DATATYPE_8B);

        /* reset HASH processor */
        HASH->CR |= HASH_CR_INIT;
    }

    /* write 4-bytes at a time into FIFO */
    while (len) {
        word32 add = min(len, STM32_HASH_REG_SIZE - stmCtx->buffLen);
        XMEMCPY(&local[stmCtx->buffLen], data, add);

        stmCtx->buffLen += add;
        data            += add;
        len             -= add;

        if (stmCtx->buffLen == STM32_HASH_REG_SIZE) {
            wroteToFifo = 1;
            HASH->DIN = *(word32*)stmCtx->buffer;

            stmCtx->loLen += STM32_HASH_REG_SIZE;
            stmCtx->buffLen = 0;
        }
    }

    if (wroteToFifo) {
        /* save hash state for next operation */
        wc_Stm32_Hash_SaveContext(stmCtx);
    }

    /* turn off hash clock */
    STM32_HASH_CLOCK_DISABLE(stmCtx);

    return ret;
}

int wc_Stm32_Hash_Final(STM32_HASH_Context* stmCtx, word32 algo,
    byte* hash, int digestSize)
{
    int ret = 0;
    word32 nbvalidbitsdata = 0;

    /* turn on hash clock */
    STM32_HASH_CLOCK_ENABLE(stmCtx);

    /* restore hash state */
    wc_Stm32_Hash_RestoreContext(stmCtx);

    /* finish reading any trailing bytes into FIFO */
    if (stmCtx->buffLen > 0) {
        HASH->DIN = *(word32*)stmCtx->buffer;
        stmCtx->loLen += stmCtx->buffLen;
    }

    /* calculate number of valid bits in last word */
    nbvalidbitsdata = 8 * (stmCtx->loLen % STM32_HASH_REG_SIZE);
    HASH->STR &= ~HASH_STR_NBW;
    HASH->STR |= nbvalidbitsdata;

    /* start hash processor */
    HASH->STR |= HASH_STR_DCAL;

    /* wait for hash done */
    ret = wc_Stm32_Hash_WaitDone();
    if (ret == 0) {
        /* read message digest */
        wc_Stm32_Hash_GetDigest(hash, digestSize);
    }

    /* turn off hash clock */
    STM32_HASH_CLOCK_DISABLE(stmCtx);

    return ret;
}

#endif /* STM32_HASH */


#ifdef STM32_CRYPTO

#ifndef NO_AES
#ifdef WOLFSSL_STM32_CUBEMX
int wc_Stm32_Aes_Init(Aes* aes, CRYP_HandleTypeDef* hcryp)
{
    int ret;
    word32 keySize;

    ret = wc_AesGetKeySize(aes, &keySize);
    if (ret != 0)
        return ret;

    XMEMSET(hcryp, 0, sizeof(CRYP_HandleTypeDef));
    switch (keySize) {
        case 16: /* 128-bit key */
            hcryp->Init.KeySize = CRYP_KEYSIZE_128B;
            break;
    #ifdef CRYP_KEYSIZE_192B
        case 24: /* 192-bit key */
            hcryp->Init.KeySize = CRYP_KEYSIZE_192B;
            break;
    #endif
        case 32: /* 256-bit key */
            hcryp->Init.KeySize = CRYP_KEYSIZE_256B;
            break;
        default:
            break;
    }
    hcryp->Instance = CRYP;
    hcryp->Init.DataType = CRYP_DATATYPE_8B;
    hcryp->Init.pKey = (STM_CRYPT_TYPE*)aes->key;
#ifdef STM32_HAL_V2
    hcryp->Init.DataWidthUnit = CRYP_DATAWIDTHUNIT_BYTE;
#endif

    return 0;
}

#else /* STD_PERI_LIB */

int wc_Stm32_Aes_Init(Aes* aes, CRYP_InitTypeDef* cryptInit,
    CRYP_KeyInitTypeDef* keyInit)
{
    int ret;
    word32 keySize;
    word32* aes_key;

    ret = wc_AesGetKeySize(aes, &keySize);
    if (ret != 0)
        return ret;

    aes_key = aes->key;

    /* crypto structure initialization */
    CRYP_KeyStructInit(keyInit);
    CRYP_StructInit(cryptInit);

    /* load key into correct registers */
    switch (keySize) {
        case 16: /* 128-bit key */
            cryptInit->CRYP_KeySize = CRYP_KeySize_128b;
            keyInit->CRYP_Key2Left  = aes_key[0];
            keyInit->CRYP_Key2Right = aes_key[1];
            keyInit->CRYP_Key3Left  = aes_key[2];
            keyInit->CRYP_Key3Right = aes_key[3];
            break;

        case 24: /* 192-bit key */
            cryptInit->CRYP_KeySize = CRYP_KeySize_192b;
            keyInit->CRYP_Key1Left  = aes_key[0];
            keyInit->CRYP_Key1Right = aes_key[1];
            keyInit->CRYP_Key2Left  = aes_key[2];
            keyInit->CRYP_Key2Right = aes_key[3];
            keyInit->CRYP_Key3Left  = aes_key[4];
            keyInit->CRYP_Key3Right = aes_key[5];
            break;

        case 32: /* 256-bit key */
            cryptInit->CRYP_KeySize = CRYP_KeySize_256b;
            keyInit->CRYP_Key0Left  = aes_key[0];
            keyInit->CRYP_Key0Right = aes_key[1];
            keyInit->CRYP_Key1Left  = aes_key[2];
            keyInit->CRYP_Key1Right = aes_key[3];
            keyInit->CRYP_Key2Left  = aes_key[4];
            keyInit->CRYP_Key2Right = aes_key[5];
            keyInit->CRYP_Key3Left  = aes_key[6];
            keyInit->CRYP_Key3Right = aes_key[7];
            break;

        default:
            break;
    }
    cryptInit->CRYP_DataType = CRYP_DataType_8b;

    return 0;
}
#endif /* WOLFSSL_STM32_CUBEMX */
#endif /* !NO_AES */
#endif /* STM32_CRYPTO */

#ifdef WOLFSSL_STM32_PKA
#include <stdint.h>
#include <stm32wbxx_hal_conf.h>
#include <stm32wbxx_hal_pka.h>

extern PKA_HandleTypeDef hpka;

/* Reverse array in memory (in place) */
#ifdef HAVE_ECC
#include <wolfssl/wolfcrypt/ecc.h>

/* convert from mp_int to STM32 PKA HAL integer, as array of bytes of size sz.
 * if mp_int has less bytes than sz, add zero bytes at most significant byte positions.
 * This is when for example modulus is 32 bytes (P-256 curve)
 * and mp_int has only 31 bytes, we add leading zeros
 * so that result array has 32 bytes, same as modulus (sz).
 */
static int stm32_get_from_mp_int(uint8_t *dst, mp_int *a, int sz)
{
    int res;
    int szbin;
    int offset;

    if (!a || !dst || (sz < 0))
        return -1;

    /* check how many bytes are in the mp_int */
    szbin = mp_unsigned_bin_size(a);
    if ((szbin < 0) || (szbin > sz))
        return -1;

    /* compute offset from dst */
    offset = sz - szbin;
    if (offset < 0)
        offset = 0;
    if (offset > sz)
        offset = sz;

    /* add leading zeroes */
    if (offset)
        XMEMSET(dst, 0, offset);

    /* convert mp_int to array of bytes */
    res = mp_to_unsigned_bin(a, dst + offset);
    return res;
}

/* ECC specs in lsbyte at lowest address format for direct use by STM32_PKA PKHA driver functions */
#if defined(HAVE_ECC192) || defined(HAVE_ALL_CURVES)
#define ECC192
#endif
#if defined(HAVE_ECC224) || defined(HAVE_ALL_CURVES)
#define ECC224
#endif
#if !defined(NO_ECC256) || defined(HAVE_ALL_CURVES)
#define ECC256
#endif
#if defined(HAVE_ECC384) || defined(HAVE_ALL_CURVES)
#define ECC384
#endif

/* STM32 PKA supports up to 640bit numbers */
#define STM32_MAX_ECC_SIZE (80)


/* P-192 */
#ifdef ECC192
#define ECC192_KEYSIZE (24)
static const uint8_t stm32_ecc192_prime[ECC192_KEYSIZE] = {
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xfe,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff
};
static const uint32_t stm32_ecc192_coef_sign = 1U;

static const uint8_t stm32_ecc192_coef[ECC192_KEYSIZE] = {
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x03
};

static const uint8_t stm32_ecc192_pointX[ECC192_KEYSIZE] =  {
    0x18, 0x8D, 0xA8, 0x0E,  0xB0, 0x30, 0x90, 0xF6,
    0x7C, 0xBF, 0x20, 0xEB,  0x43, 0xA1, 0x88, 0x00,
    0xF4, 0xFF, 0x0A, 0xFD,  0x82, 0xFF, 0x10, 0x12
};

const uint8_t stm32_ecc192_pointY[ECC192_KEYSIZE] = {
    0x07, 0x19, 0x2B, 0x95,  0xFF, 0xC8, 0xDA, 0x78,
    0x63, 0x10, 0x11, 0xED,  0x6B, 0x24, 0xCD, 0xD5,
    0x73, 0xF9, 0x77, 0xA1,  0x1E, 0x79, 0x48, 0x11
};

const uint8_t stm32_ecc192_order[ECC192_KEYSIZE] = {
    0xFF, 0xFF, 0xFF, 0xFF,  0xFF, 0xFF, 0xFF, 0xFF,
    0xFF, 0xFF, 0xFF, 0xFF,  0x99, 0xDE, 0xF8, 0x36,
    0x14, 0x6B, 0xC9, 0xB1,  0xB4, 0xD2, 0x28, 0x31
};
const uint32_t stm32_ecc192_cofactor = 1U;

#endif /* ECC192 */

/* P-224 */
#ifdef ECC224
#define ECC224_KEYSIZE (28)
static const uint8_t stm32_ecc224_prime[ECC224_KEYSIZE] = {
    0xFF, 0xFF, 0xFF, 0xFF,  0xFF, 0xFF, 0xFF, 0xFF,
    0xFF, 0xFF, 0xFF, 0xFF,  0xFF, 0xFF, 0xFF, 0xFF,
    0x00, 0x00, 0x00, 0x00,  0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x01
};
static const uint32_t stm32_ecc224_coef_sign = 1U;

static const uint8_t stm32_ecc224_coef[ECC224_KEYSIZE] = {
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x03
};

static const uint8_t stm32_ecc224_pointX[ECC224_KEYSIZE] =  {
    0xB7, 0x0E, 0x0C, 0xBD, 0x6B, 0xB4, 0xBF, 0x7F,
    0x32, 0x13, 0x90, 0xB9, 0x4A, 0x03, 0xC1, 0xD3,
    0x56, 0xC2, 0x11, 0x22, 0x34, 0x32, 0x80, 0xD6,
    0x11, 0x5C, 0x1D, 0x21
};

const uint8_t stm32_ecc224_pointY[ECC224_KEYSIZE] = {
    0xBD, 0x37, 0x63, 0x88, 0xB5, 0xF7, 0x23, 0xFB,
    0x4C, 0x22, 0xDF, 0xE6, 0xCD, 0x43, 0x75, 0xA0,
    0x5A, 0x07, 0x47, 0x64, 0x44, 0xD5, 0x81, 0x99,
    0x85, 0x00, 0x7E, 0x34
};

const uint8_t stm32_ecc224_order[ECC224_KEYSIZE] = {
};
const uint32_t stm32_ecc224_cofactor = 1U;

#endif /* ECC224 */

/* P-256 */
#ifdef ECC256
#define ECC256_KEYSIZE (32)

static const uint8_t stm32_ecc256_prime[ECC256_KEYSIZE] = {
    0xff, 0xff, 0xff, 0xff, 0x00, 0x00, 0x00, 0x01,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff
};
static const uint32_t stm32_ecc256_coef_sign = 1U;

static const uint8_t stm32_ecc256_coef[ECC256_KEYSIZE] = {
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x03
};

static const uint8_t stm32_ecc256_pointX[ECC256_KEYSIZE] = {
    0x6b, 0x17, 0xd1, 0xf2, 0xe1, 0x2c, 0x42, 0x47,
    0xf8, 0xbc, 0xe6, 0xe5, 0x63, 0xa4, 0x40, 0xf2,
    0x77, 0x03, 0x7d, 0x81, 0x2d, 0xeb, 0x33, 0xa0,
    0xf4, 0xa1, 0x39, 0x45, 0xd8, 0x98, 0xc2, 0x96
};

const uint8_t stm32_ecc256_pointY[ECC256_KEYSIZE] = {
    0x4f, 0xe3, 0x42, 0xe2, 0xfe, 0x1a, 0x7f, 0x9b,
    0x8e, 0xe7, 0xeb, 0x4a, 0x7c, 0x0f, 0x9e, 0x16,
    0x2b, 0xce, 0x33, 0x57, 0x6b, 0x31, 0x5e, 0xce,
    0xcb, 0xb6, 0x40, 0x68, 0x37, 0xbf, 0x51, 0xf5
};

const uint8_t stm32_ecc256_order[ECC256_KEYSIZE] = {
    0xff, 0xff, 0xff, 0xff, 0x00, 0x00, 0x00, 0x00,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xbc, 0xe6, 0xfa, 0xad, 0xa7, 0x17, 0x9e, 0x84,
    0xf3, 0xb9, 0xca, 0xc2, 0xfc, 0x63, 0x25, 0x51
};
const uint32_t stm32_ecc256_cofactor = 1U;

#endif /* ECC256 */

/* P-384 */
#ifdef ECC384
#define ECC384_KEYSIZE (48)

static const uint8_t stm32_ecc384_prime[ECC384_KEYSIZE] = {
    0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
    0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
    0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
    0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFE,
    0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0xFF, 0xFF, 0xFF, 0xFF
};
static const uint32_t stm32_ecc384_coef_sign = 1U;

static const uint8_t stm32_ecc384_coef[ECC384_KEYSIZE] = {
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x03
};

static const uint8_t stm32_ecc384_pointX[ECC384_KEYSIZE] =  {
    0xAA, 0x87, 0xCA, 0x22, 0xBE, 0x8B, 0x05, 0x37,
    0x8E, 0xB1, 0xC7, 0x1E, 0xF3, 0x20, 0xAD, 0x74,
    0x6E, 0x1D, 0x3B, 0x62, 0x8B, 0xA7, 0x9B, 0x98,
    0x59, 0xF7, 0x41, 0xE0, 0x82, 0x54, 0x2A, 0x38,
    0x55, 0x02, 0xF2, 0x5D, 0xBF, 0x55, 0x29, 0x6C,
    0x3A, 0x54, 0x5E, 0x38, 0x72, 0x76, 0x0A, 0xB7,
};

const uint8_t stm32_ecc384_pointY[ECC384_KEYSIZE] = {
    0x36, 0x17, 0xDE, 0x4A, 0x96, 0x26, 0x2C, 0x6F,
    0x5D, 0x9E, 0x98, 0xBF, 0x92, 0x92, 0xDC, 0x29,
    0xF8, 0xF4, 0x1D, 0xBD, 0x28, 0x9A, 0x14, 0x7C,
    0xE9, 0xDA, 0x31, 0x13, 0xB5, 0xF0, 0xB8, 0xC0,
    0x0A, 0x60, 0xB1, 0xCE, 0x1D, 0x7E, 0x81, 0x9D,
    0x7A, 0x43, 0x1D, 0x7C, 0x90, 0xEA, 0x0E, 0x5F,
};

const uint8_t stm32_ecc384_order[ECC384_KEYSIZE] = {
};
const uint32_t stm32_ecc384_cofactor = 1U;

#endif /* ECC384 */
static int stm32_get_ecc_specs(const uint8_t **prime, const uint8_t **coef,
    const uint32_t **coef_sign, const uint8_t **GenPointX, const uint8_t **GenPointY,
    const uint8_t **order, int size)
{
    switch(size) {
    case 32:
        *prime = stm32_ecc256_prime;
        *coef = stm32_ecc256_coef;
        *GenPointX = stm32_ecc256_pointX;
        *GenPointY = stm32_ecc256_pointY;
        *coef_sign = &stm32_ecc256_coef_sign;
        *order = stm32_ecc256_order;
        break;
#ifdef ECC224
    case 28:
        *prime = stm32_ecc224_prime;
        *coef = stm32_ecc224_coef;
        *GenPointX = stm32_ecc224_pointX;
        *GenPointY = stm32_ecc224_pointY;
        *coef_sign = &stm32_ecc224_coef;
        break;
#endif
#ifdef ECC192
    case 24:
        *prime = stm32_ecc192_prime;
        *coef = stm32_ecc192_coef;
        *GenPointX = stm32_ecc192_pointX;
        *GenPointY = stm32_ecc192_pointY;
        *coef_sign = &stm32_ecc192_coef;
        break;
#endif
#ifdef ECC384
    case 48:
        *prime = stm32_ecc384_prime;
        *coef = stm32_ecc384_coef;
        *GenPointX = stm32_ecc384_pointX;
        *GenPointY = stm32_ecc384_pointY;
        *coef_sign = &stm32_ecc384_coef;
        break;
#endif
    default:
        return -1;
    }
    return 0;
}


/**
   Perform a point multiplication  (timing resistant)
   k    The scalar to multiply by
   G    The base point
   R    [out] Destination for kG
   modulus  The modulus of the field the ECC curve is in
   map      Boolean whether to map back to affine or not
            (1==map, 0 == leave in projective)
   return MP_OKAY on success
*/
int wc_ecc_mulmod_ex(mp_int *k, ecc_point *G, ecc_point *R, mp_int* a,
    mp_int *modulus, int map, void* heap)
{
    PKA_ECCMulInTypeDef pka_mul;
    PKA_ECCMulOutTypeDef pka_mul_res;
    uint8_t size;
    int szModulus;
    int szkbin;
    int status;
    int res;
    uint8_t Gxbin[STM32_MAX_ECC_SIZE];
    uint8_t Gybin[STM32_MAX_ECC_SIZE];
    uint8_t kbin[STM32_MAX_ECC_SIZE];
    uint8_t PtXbin[STM32_MAX_ECC_SIZE];
    uint8_t PtYbin[STM32_MAX_ECC_SIZE];
    const uint8_t *prime, *coef, *gen_x, *gen_y, *order;
    const uint32_t *coef_sign;
    (void)a;
    (void)heap;
    XMEMSET(&pka_mul, 0x00, sizeof(PKA_ECCMulInTypeDef));
    XMEMSET(&pka_mul_res, 0x00, sizeof(PKA_ECCMulOutTypeDef));
    pka_mul_res.ptX = PtXbin;
    pka_mul_res.ptY = PtYbin;

    if (k == NULL || G == NULL || R == NULL || modulus == NULL) {
        return ECC_BAD_ARG_E;
    }

    szModulus = mp_unsigned_bin_size(modulus);
    szkbin = mp_unsigned_bin_size(k);

    res = stm32_get_from_mp_int(kbin, k, szkbin);
    if (res == MP_OKAY)
        res = stm32_get_from_mp_int(Gxbin, G->x, szModulus);
    if (res == MP_OKAY)
        res = stm32_get_from_mp_int(Gybin, G->y, szModulus);

    if (res != MP_OKAY)
        return res;

    size = (uint8_t)szModulus;
    /* find STM32_PKA friendly parameters for the selected curve */
    if (0 != stm32_get_ecc_specs(&prime, &coef, &coef_sign, &gen_x, &gen_y, &order, size)) {
        return ECC_BAD_ARG_E;
    }
    (void)order;

    pka_mul.modulusSize = szModulus;
    pka_mul.coefSign = *coef_sign;
    pka_mul.coefA = coef;
    pka_mul.modulus = prime;
    pka_mul.pointX = Gxbin;
    pka_mul.pointY = Gybin;
    pka_mul.scalarMulSize = size;
    pka_mul.scalarMul = kbin;

    status = HAL_PKA_ECCMul(&hpka, &pka_mul, HAL_MAX_DELAY);
    if (status != HAL_OK) {
        return WC_HW_E;
    }
    pka_mul_res.ptX = Gxbin;
    pka_mul_res.ptY = Gybin;
    HAL_PKA_ECCMul_GetResult(&hpka, &pka_mul_res);
    res = mp_read_unsigned_bin(R->x, Gxbin, size);
    if (res == MP_OKAY) {
        res = mp_read_unsigned_bin(R->y, Gybin, size);
#ifndef WOLFSSL_SP_MATH
        /* if k is negative, we compute the multiplication with abs(-k)
         * with result (x, y) and modify the result to (x, -y)
         */
        R->y->sign = k->sign;
#endif
    }
    if (res == MP_OKAY)
        res = mp_set(R->z, 1);
    HAL_PKA_RAMReset(&hpka);
    return res;
}

int stm32_ecc_verify_hash_ex(mp_int *r, mp_int *s, const byte* hash,
                    word32 hashlen, int* res, ecc_key* key)
{
    PKA_ECDSAVerifInTypeDef pka_ecc;
    uint8_t size;
    int szModulus;
    int szrbin;
    int status;
    uint8_t Rbin[STM32_MAX_ECC_SIZE];
    uint8_t Sbin[STM32_MAX_ECC_SIZE];
    uint8_t Qxbin[STM32_MAX_ECC_SIZE];
    uint8_t Qybin[STM32_MAX_ECC_SIZE];
    uint8_t Hashbin[STM32_MAX_ECC_SIZE];
    uint8_t privKeybin[STM32_MAX_ECC_SIZE];
    const uint8_t *prime, *coef, *gen_x, *gen_y, *order;
    const uint32_t *coef_sign;
    XMEMSET(&pka_ecc, 0x00, sizeof(PKA_ECDSAVerifInTypeDef));

    if (r == NULL || s == NULL || hash == NULL || res == NULL || key == NULL) {
        return ECC_BAD_ARG_E;
    }
    *res = 0;

    szModulus = mp_unsigned_bin_size(key->pubkey.x);
    szrbin = mp_unsigned_bin_size(r);

    status = stm32_get_from_mp_int(Rbin, r, szrbin);
    if (status == MP_OKAY)
        status = stm32_get_from_mp_int(Sbin, s, szrbin);
    if (status == MP_OKAY)
        status = stm32_get_from_mp_int(Qxbin, key->pubkey.x, szModulus);
    if (status == MP_OKAY)
        status = stm32_get_from_mp_int(Qybin, key->pubkey.y, szModulus);
    if (status == MP_OKAY)
        status = stm32_get_from_mp_int(privKeybin, &key->k, szModulus);
    if (status != MP_OKAY)
        return status;

    size = (uint8_t)szModulus;
    /* find parameters for the selected curve */
    if (0 != stm32_get_ecc_specs(&prime, &coef, &coef_sign, &gen_x, &gen_y, &order, size)) {
        return ECC_BAD_ARG_E;
    }


    pka_ecc.primeOrderSize =  size;
    pka_ecc.modulusSize =     size;
    pka_ecc.coefSign =        *coef_sign;
    pka_ecc.coef =            coef;
    pka_ecc.modulus =         prime;
    pka_ecc.basePointX =      gen_x;
    pka_ecc.basePointY =      gen_y;
    pka_ecc.primeOrder =      order;

    pka_ecc.pPubKeyCurvePtX = Qxbin;
    pka_ecc.pPubKeyCurvePtY = Qybin;
    pka_ecc.RSign =           Rbin;
    pka_ecc.SSign =           Sbin;
    XMEMSET(Hashbin, 0, STM32_MAX_ECC_SIZE);
    XMEMCPY(Hashbin + (size - hashlen), hash, hashlen);
    pka_ecc.hash =            Hashbin;

    status = HAL_PKA_ECDSAVerif(&hpka, &pka_ecc, HAL_MAX_DELAY);
    if (status != HAL_OK) {
        HAL_PKA_RAMReset(&hpka);
        return WC_HW_E;
    }
    *res = HAL_PKA_ECDSAVerif_IsValidSignature(&hpka);
    HAL_PKA_RAMReset(&hpka);
    return status;
}

int stm32_ecc_sign_hash_ex(const byte* hash, word32 hashlen, WC_RNG* rng,
                     ecc_key* key, mp_int *r, mp_int *s)
{
    PKA_ECDSASignInTypeDef pka_ecc;
    PKA_ECDSASignOutTypeDef pka_ecc_out;
    int size;
    int status;
    mp_int gen_k;
    mp_int order_mp;
    uint8_t Keybin[STM32_MAX_ECC_SIZE];
    uint8_t Intbin[STM32_MAX_ECC_SIZE];
    uint8_t Rbin[STM32_MAX_ECC_SIZE];
    uint8_t Sbin[STM32_MAX_ECC_SIZE];
    uint8_t Hashbin[STM32_MAX_ECC_SIZE];
    const uint8_t *prime, *coef, *gen_x, *gen_y, *order;
    const uint32_t *coef_sign;
    XMEMSET(&pka_ecc, 0x00, sizeof(PKA_ECDSASignInTypeDef));
    XMEMSET(&pka_ecc, 0x00, sizeof(PKA_ECDSASignOutTypeDef));

    if (r == NULL || s == NULL || hash == NULL || key == NULL) {
        return ECC_BAD_ARG_E;
    }

    mp_init(&gen_k);
    mp_init(&order_mp);

    size = mp_unsigned_bin_size(key->pubkey.x);

    status = stm32_get_from_mp_int(Keybin, &key->k, size);
    if (status != MP_OKAY)
        return status;

    /* find parameters for the selected curve */
    if (0 != stm32_get_ecc_specs(&prime, &coef, &coef_sign, &gen_x, &gen_y, &order, size)) {
        return ECC_BAD_ARG_E;
    }

    status = mp_read_unsigned_bin(&order_mp, order, size);
    if (status == MP_OKAY)
        status = wc_ecc_gen_k(rng, size, &gen_k, &order_mp);
    if (status == MP_OKAY)
        status = stm32_get_from_mp_int(Intbin, &gen_k, size);
    if (status != MP_OKAY)
        return status;

    pka_ecc.primeOrderSize =  size;
    pka_ecc.modulusSize =     size;
    pka_ecc.coefSign =        *coef_sign;
    pka_ecc.coef =            coef;
    pka_ecc.modulus =         prime;
    pka_ecc.basePointX =      gen_x;
    pka_ecc.basePointY =      gen_y;
    pka_ecc.primeOrder =      order;

    XMEMSET(Hashbin, 0, STM32_MAX_ECC_SIZE);
    XMEMCPY(Hashbin + (size - hashlen), hash, hashlen);
    pka_ecc.hash =            Hashbin;
    pka_ecc.integer =         Intbin;
    pka_ecc.privateKey =      Keybin;

    /* Assign R, S static buffers */
    pka_ecc_out.RSign = Rbin;
    pka_ecc_out.SSign = Sbin;

    status = HAL_PKA_ECDSASign(&hpka, &pka_ecc, HAL_MAX_DELAY);
    if (status != HAL_OK) {
        HAL_PKA_RAMReset(&hpka);
        return WC_HW_E;
    }
    HAL_PKA_ECDSASign_GetResult(&hpka, &pka_ecc_out, NULL);
    status = mp_read_unsigned_bin(r, pka_ecc_out.RSign, size);
    if (status == MP_OKAY)
        status = mp_read_unsigned_bin(s, pka_ecc_out.SSign, size);
    HAL_PKA_RAMReset(&hpka);
    return status;
}

#endif /* HAVE_ECC */
#endif /* WOLFSSL_STM32_PKA */
