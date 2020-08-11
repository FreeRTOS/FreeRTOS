/* stm32.h
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

#ifndef _WOLFPORT_STM32_H_
#define _WOLFPORT_STM32_H_

/* Generic STM32 Hashing and Crypto Functions */
/* Supports CubeMX HAL or Standard Peripheral Library */

#include <wolfssl/wolfcrypt/settings.h>
#include <wolfssl/wolfcrypt/types.h>

#if defined(WOLFSSL_STM32_PKA) && defined(HAVE_ECC)
    #include <wolfssl/wolfcrypt/integer.h>
    #include <wolfssl/wolfcrypt/ecc.h>
#endif

#ifdef STM32_HASH

#define WOLFSSL_NO_HASH_RAW

#ifdef HASH_DIGEST
    /* The HASH_DIGEST register indicates SHA224/SHA256 support */
    #define STM32_HASH_SHA2
    #define HASH_CR_SIZE 54
    #define HASH_MAX_DIGEST 32
#else
    #define HASH_CR_SIZE 50
    #define HASH_MAX_DIGEST 20
#endif

/* Handle hash differences between CubeMX and StdPeriLib */
#if !defined(HASH_ALGOMODE_HASH) && defined(HASH_AlgoMode_HASH)
    #define HASH_ALGOMODE_HASH HASH_AlgoMode_HASH
#endif
#if !defined(HASH_DATATYPE_8B) && defined(HASH_DataType_8b)
    #define HASH_DATATYPE_8B HASH_DataType_8b
#endif

#ifndef STM32_HASH_TIMEOUT
    #define STM32_HASH_TIMEOUT 0xFFFF
#endif


/* STM32 register size in bytes */
#define STM32_HASH_REG_SIZE  4

/* STM32 Hash Context */
typedef struct {
    /* Context switching registers */
    uint32_t HASH_IMR;
    uint32_t HASH_STR;
    uint32_t HASH_CR;
    uint32_t HASH_CSR[HASH_CR_SIZE];

    /* Hash state / buffers */
    word32 buffer[STM32_HASH_REG_SIZE / sizeof(word32)]; /* partial word buffer */
    word32 buffLen; /* partial word remain */
    word32 loLen;   /* total update bytes
                 (only lsb 6-bits is used for nbr valid bytes in last word) */
} STM32_HASH_Context;


/* API's */
void wc_Stm32_Hash_Init(STM32_HASH_Context* stmCtx);
int  wc_Stm32_Hash_Update(STM32_HASH_Context* stmCtx, word32 algo,
    const byte* data, int len);
int  wc_Stm32_Hash_Final(STM32_HASH_Context* stmCtx, word32 algo,
    byte* hash, int digestSize);

#endif /* STM32_HASH */


#ifdef STM32_CRYPTO

#ifndef NO_AES
    #if !defined(STM32_CRYPTO_AES_GCM) && (defined(WOLFSSL_STM32F4) || \
            defined(WOLFSSL_STM32F7) || defined(WOLFSSL_STM32L4))
        /* Hardware supports AES GCM acceleration */
        #define STM32_CRYPTO_AES_GCM
    #endif

    #ifdef WOLFSSL_STM32L4
        #define STM32_CRYPTO_AES_ONLY /* crypto engine only supports AES */
        #define CRYP AES
    #endif

    /* Detect newer CubeMX crypto HAL (HAL_CRYP_Encrypt / HAL_CRYP_Decrypt) */
    #if !defined(STM32_HAL_V2) && \
        defined(WOLFSSL_STM32F7) && defined(CRYP_AES_GCM)
        #define STM32_HAL_V2
    #endif

    /* The datatype for STM32 CubeMX HAL Crypt calls */
    #ifdef STM32_HAL_V2
        #define STM_CRYPT_TYPE uint32_t
    #else
        #define STM_CRYPT_TYPE uint8_t
    #endif

    /* CRYPT_AES_GCM starts the IV with 2 */
    #define STM32_GCM_IV_START 2

    struct Aes;
    #ifdef WOLFSSL_STM32_CUBEMX
        int wc_Stm32_Aes_Init(struct Aes* aes, CRYP_HandleTypeDef* hcryp);
    #else /* STD_PERI_LIB */
        int wc_Stm32_Aes_Init(struct Aes* aes, CRYP_InitTypeDef* cryptInit,
            CRYP_KeyInitTypeDef* keyInit);
    #endif /* WOLFSSL_STM32_CUBEMX */
#endif /* !NO_AES */

#endif /* STM32_CRYPTO */

#if defined(WOLFSSL_STM32_PKA) && defined(HAVE_ECC)
int stm32_ecc_verify_hash_ex(mp_int *r, mp_int *s, const byte* hash,
                    word32 hashlen, int* res, ecc_key* key);

int stm32_ecc_sign_hash_ex(const byte* hash, word32 hashlen, WC_RNG* rng,
                     ecc_key* key, mp_int *r, mp_int *s);
#endif


#endif /* _WOLFPORT_STM32_H_ */
