/* aes.c
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

DESCRIPTION
This library provides the interfaces to the Advanced Encryption Standard (AES)
for encrypting and decrypting data. AES is the standard known for a symmetric
block cipher mechanism that uses n-bit binary string parameter key with 128-bits,
192-bits, and 256-bits of key sizes.

*/
#ifdef HAVE_CONFIG_H
    #include <config.h>
#endif

#include <wolfssl/wolfcrypt/settings.h>
#include <wolfssl/wolfcrypt/error-crypt.h>

#if !defined(NO_AES)

/* Tip: Locate the software cipher modes by searching for "Software AES" */

#if defined(HAVE_FIPS) && \
    defined(HAVE_FIPS_VERSION) && (HAVE_FIPS_VERSION >= 2)

    /* set NO_WRAPPERS before headers, use direct internal f()s not wrappers */
    #define FIPS_NO_WRAPPERS

    #ifdef USE_WINDOWS_API
        #pragma code_seg(".fipsA$g")
        #pragma const_seg(".fipsB$g")
    #endif
#endif

#include <wolfssl/wolfcrypt/aes.h>
#include <wolfssl/wolfcrypt/cpuid.h>

#ifdef WOLF_CRYPTO_CB
    #include <wolfssl/wolfcrypt/cryptocb.h>
#endif


/* fips wrapper calls, user can call direct */
#if defined(HAVE_FIPS) && \
    (!defined(HAVE_FIPS_VERSION) || (HAVE_FIPS_VERSION < 2))

    int wc_AesSetKey(Aes* aes, const byte* key, word32 len, const byte* iv,
                              int dir)
    {
        if (aes == NULL ||  !( (len == 16) || (len == 24) || (len == 32)) ) {
            return BAD_FUNC_ARG;
        }

        return AesSetKey_fips(aes, key, len, iv, dir);
    }
    int wc_AesSetIV(Aes* aes, const byte* iv)
    {
        if (aes == NULL) {
            return BAD_FUNC_ARG;
        }

        return AesSetIV_fips(aes, iv);
    }
    #ifdef HAVE_AES_CBC
        int wc_AesCbcEncrypt(Aes* aes, byte* out, const byte* in, word32 sz)
        {
            if (aes == NULL || out == NULL || in == NULL) {
                return BAD_FUNC_ARG;
            }

            return AesCbcEncrypt_fips(aes, out, in, sz);
        }
        #ifdef HAVE_AES_DECRYPT
            int wc_AesCbcDecrypt(Aes* aes, byte* out, const byte* in, word32 sz)
            {
                if (aes == NULL || out == NULL || in == NULL
                                            || sz % AES_BLOCK_SIZE != 0) {
                    return BAD_FUNC_ARG;
                }

                return AesCbcDecrypt_fips(aes, out, in, sz);
            }
        #endif /* HAVE_AES_DECRYPT */
    #endif /* HAVE_AES_CBC */

    /* AES-CTR */
    #ifdef WOLFSSL_AES_COUNTER
        int wc_AesCtrEncrypt(Aes* aes, byte* out, const byte* in, word32 sz)
        {
            if (aes == NULL || out == NULL || in == NULL) {
                return BAD_FUNC_ARG;
            }

            return AesCtrEncrypt(aes, out, in, sz);
        }
    #endif

    /* AES-DIRECT */
    #if defined(WOLFSSL_AES_DIRECT)
        void wc_AesEncryptDirect(Aes* aes, byte* out, const byte* in)
        {
            AesEncryptDirect(aes, out, in);
        }

        #ifdef HAVE_AES_DECRYPT
            void wc_AesDecryptDirect(Aes* aes, byte* out, const byte* in)
            {
                AesDecryptDirect(aes, out, in);
            }
        #endif /* HAVE_AES_DECRYPT */

        int wc_AesSetKeyDirect(Aes* aes, const byte* key, word32 len,
                                        const byte* iv, int dir)
        {
            return AesSetKeyDirect(aes, key, len, iv, dir);
        }
    #endif /* WOLFSSL_AES_DIRECT */

    /* AES-GCM */
    #ifdef HAVE_AESGCM
        int wc_AesGcmSetKey(Aes* aes, const byte* key, word32 len)
        {
            if (aes == NULL || !( (len == 16) || (len == 24) || (len == 32)) ) {
                return BAD_FUNC_ARG;
            }

            return AesGcmSetKey_fips(aes, key, len);
        }
        int wc_AesGcmEncrypt(Aes* aes, byte* out, const byte* in, word32 sz,
                                      const byte* iv, word32 ivSz,
                                      byte* authTag, word32 authTagSz,
                                      const byte* authIn, word32 authInSz)
        {
            if (aes == NULL || authTagSz > AES_BLOCK_SIZE ||
                        authTagSz < WOLFSSL_MIN_AUTH_TAG_SZ ||
                        ivSz == 0 || ivSz > AES_BLOCK_SIZE) {
                return BAD_FUNC_ARG;
            }

            return AesGcmEncrypt_fips(aes, out, in, sz, iv, ivSz, authTag,
                authTagSz, authIn, authInSz);
        }

        #ifdef HAVE_AES_DECRYPT
            int wc_AesGcmDecrypt(Aes* aes, byte* out, const byte* in, word32 sz,
                                          const byte* iv, word32 ivSz,
                                          const byte* authTag, word32 authTagSz,
                                          const byte* authIn, word32 authInSz)
            {
                if (aes == NULL || out == NULL || in == NULL || iv == NULL
                        || authTag == NULL || authTagSz > AES_BLOCK_SIZE ||
                        ivSz == 0 || ivSz > AES_BLOCK_SIZE) {
                    return BAD_FUNC_ARG;
                }

                return AesGcmDecrypt_fips(aes, out, in, sz, iv, ivSz, authTag,
                    authTagSz, authIn, authInSz);
            }
        #endif /* HAVE_AES_DECRYPT */

        int wc_GmacSetKey(Gmac* gmac, const byte* key, word32 len)
        {
            if (gmac == NULL || key == NULL || !((len == 16) ||
                                (len == 24) || (len == 32)) ) {
                return BAD_FUNC_ARG;
            }

            return GmacSetKey(gmac, key, len);
        }
        int wc_GmacUpdate(Gmac* gmac, const byte* iv, word32 ivSz,
                                      const byte* authIn, word32 authInSz,
                                      byte* authTag, word32 authTagSz)
        {
            if (gmac == NULL || authTagSz > AES_BLOCK_SIZE ||
                               authTagSz < WOLFSSL_MIN_AUTH_TAG_SZ) {
                return BAD_FUNC_ARG;
            }

            return GmacUpdate(gmac, iv, ivSz, authIn, authInSz,
                              authTag, authTagSz);
        }
    #endif /* HAVE_AESGCM */

    /* AES-CCM */
    #if defined(HAVE_AESCCM) && \
        defined(HAVE_FIPS_VERSION) && (HAVE_FIPS_VERSION >= 2)
        int wc_AesCcmSetKey(Aes* aes, const byte* key, word32 keySz)
        {
            return AesCcmSetKey(aes, key, keySz);
        }
        int wc_AesCcmEncrypt(Aes* aes, byte* out, const byte* in, word32 inSz,
                                      const byte* nonce, word32 nonceSz,
                                      byte* authTag, word32 authTagSz,
                                      const byte* authIn, word32 authInSz)
        {
            /* sanity check on arguments */
            if (aes == NULL || out == NULL || in == NULL || nonce == NULL
                    || authTag == NULL || nonceSz < 7 || nonceSz > 13)
                return BAD_FUNC_ARG;

            AesCcmEncrypt(aes, out, in, inSz, nonce, nonceSz, authTag,
                authTagSz, authIn, authInSz);
            return 0;
        }

        #ifdef HAVE_AES_DECRYPT
            int  wc_AesCcmDecrypt(Aes* aes, byte* out,
                const byte* in, word32 inSz,
                const byte* nonce, word32 nonceSz,
                const byte* authTag, word32 authTagSz,
                const byte* authIn, word32 authInSz)
            {

                if (aes == NULL || out == NULL || in == NULL || nonce == NULL
                    || authTag == NULL || nonceSz < 7 || nonceSz > 13) {
                        return BAD_FUNC_ARG;
                }

                return AesCcmDecrypt(aes, out, in, inSz, nonce, nonceSz,
                    authTag, authTagSz, authIn, authInSz);
            }
        #endif /* HAVE_AES_DECRYPT */
    #endif /* HAVE_AESCCM && HAVE_FIPS_VERSION 2 */

    int wc_AesInit(Aes* aes, void* h, int i)
    {
        if (aes == NULL)
            return BAD_FUNC_ARG;

        (void)h;
        (void)i;

        /* FIPS doesn't support:
            return AesInit(aes, h, i); */
        return 0;
    }
    void wc_AesFree(Aes* aes)
    {
        (void)aes;
        /* FIPS doesn't support:
            AesFree(aes); */
    }

#else /* else build without fips, or for FIPS v2 */


#if defined(WOLFSSL_TI_CRYPT)
    #include <wolfcrypt/src/port/ti/ti-aes.c>
#else

#include <wolfssl/wolfcrypt/logging.h>

#ifdef NO_INLINE
    #include <wolfssl/wolfcrypt/misc.h>
#else
    #define WOLFSSL_MISC_INCLUDED
    #include <wolfcrypt/src/misc.c>
#endif

#if !defined(WOLFSSL_ARMASM)

#ifdef WOLFSSL_IMX6_CAAM_BLOB
    /* case of possibly not using hardware acceleration for AES but using key
       blobs */
    #include <wolfssl/wolfcrypt/port/caam/wolfcaam.h>
#endif

#ifdef DEBUG_AESNI
    #include <stdio.h>
#endif

#ifdef _MSC_VER
    /* 4127 warning constant while(1)  */
    #pragma warning(disable: 4127)
#endif


/* Define AES implementation includes and functions */
#if defined(STM32_CRYPTO)
     /* STM32F2/F4/F7/L4/L5/H7/WB55 hardware AES support for ECB, CBC, CTR and GCM modes */

#if defined(WOLFSSL_AES_DIRECT) || defined(HAVE_AESGCM) || defined(HAVE_AESCCM)

    static int wc_AesEncrypt(Aes* aes, const byte* inBlock, byte* outBlock)
    {
        int ret = 0;
    #ifdef WOLFSSL_STM32_CUBEMX
        CRYP_HandleTypeDef hcryp;
    #else
        CRYP_InitTypeDef cryptInit;
        CRYP_KeyInitTypeDef keyInit;
    #endif

    #ifdef WOLFSSL_STM32_CUBEMX
        ret = wc_Stm32_Aes_Init(aes, &hcryp);
        if (ret != 0)
            return ret;

    #if defined(STM32_HAL_V2)
        hcryp.Init.Algorithm  = CRYP_AES_ECB;
    #elif defined(STM32_CRYPTO_AES_ONLY)
        hcryp.Init.OperatingMode = CRYP_ALGOMODE_ENCRYPT;
        hcryp.Init.ChainingMode  = CRYP_CHAINMODE_AES_ECB;
        hcryp.Init.KeyWriteFlag  = CRYP_KEY_WRITE_ENABLE;
    #endif
        HAL_CRYP_Init(&hcryp);

    #if defined(STM32_HAL_V2)
        ret = HAL_CRYP_Encrypt(&hcryp, (uint32_t*)inBlock, AES_BLOCK_SIZE,
            (uint32_t*)outBlock, STM32_HAL_TIMEOUT);
    #elif defined(STM32_CRYPTO_AES_ONLY)
        ret = HAL_CRYPEx_AES(&hcryp, (uint8_t*)inBlock, AES_BLOCK_SIZE,
            outBlock, STM32_HAL_TIMEOUT);
    #else
        ret = HAL_CRYP_AESECB_Encrypt(&hcryp, (uint8_t*)inBlock, AES_BLOCK_SIZE,
            outBlock, STM32_HAL_TIMEOUT);
    #endif
        if (ret != HAL_OK) {
            ret = WC_TIMEOUT_E;
        }
        HAL_CRYP_DeInit(&hcryp);

    #else /* Standard Peripheral Library */
        ret = wc_Stm32_Aes_Init(aes, &cryptInit, &keyInit);
        if (ret != 0)
            return ret;

        /* reset registers to their default values */
        CRYP_DeInit();

        /* setup key */
        CRYP_KeyInit(&keyInit);

        /* set direction and mode */
        cryptInit.CRYP_AlgoDir  = CRYP_AlgoDir_Encrypt;
        cryptInit.CRYP_AlgoMode = CRYP_AlgoMode_AES_ECB;
        CRYP_Init(&cryptInit);

        /* enable crypto processor */
        CRYP_Cmd(ENABLE);

        /* flush IN/OUT FIFOs */
        CRYP_FIFOFlush();

        CRYP_DataIn(*(uint32_t*)&inBlock[0]);
        CRYP_DataIn(*(uint32_t*)&inBlock[4]);
        CRYP_DataIn(*(uint32_t*)&inBlock[8]);
        CRYP_DataIn(*(uint32_t*)&inBlock[12]);

        /* wait until the complete message has been processed */
        while (CRYP_GetFlagStatus(CRYP_FLAG_BUSY) != RESET) {}

        *(uint32_t*)&outBlock[0]  = CRYP_DataOut();
        *(uint32_t*)&outBlock[4]  = CRYP_DataOut();
        *(uint32_t*)&outBlock[8]  = CRYP_DataOut();
        *(uint32_t*)&outBlock[12] = CRYP_DataOut();

        /* disable crypto processor */
        CRYP_Cmd(DISABLE);
    #endif /* WOLFSSL_STM32_CUBEMX */

        return ret;
    }
#endif /* WOLFSSL_AES_DIRECT || HAVE_AESGCM || HAVE_AESCCM */

#ifdef HAVE_AES_DECRYPT
    #if defined(WOLFSSL_AES_DIRECT) || defined(HAVE_AESCCM)
    static int wc_AesDecrypt(Aes* aes, const byte* inBlock, byte* outBlock)
    {
        int ret = 0;
    #ifdef WOLFSSL_STM32_CUBEMX
        CRYP_HandleTypeDef hcryp;
    #else
        CRYP_InitTypeDef cryptInit;
        CRYP_KeyInitTypeDef keyInit;
    #endif

    #ifdef WOLFSSL_STM32_CUBEMX
        ret = wc_Stm32_Aes_Init(aes, &hcryp);
        if (ret != 0)
            return ret;

    #if defined(STM32_HAL_V2)
        hcryp.Init.Algorithm  = CRYP_AES_ECB;
    #elif defined(STM32_CRYPTO_AES_ONLY)
        hcryp.Init.OperatingMode = CRYP_ALGOMODE_KEYDERIVATION_DECRYPT;
        hcryp.Init.ChainingMode  = CRYP_CHAINMODE_AES_ECB;
        hcryp.Init.KeyWriteFlag  = CRYP_KEY_WRITE_ENABLE;
    #endif
        HAL_CRYP_Init(&hcryp);

    #if defined(STM32_HAL_V2)
        ret = HAL_CRYP_Decrypt(&hcryp, (uint32_t*)inBlock, AES_BLOCK_SIZE,
            (uint32_t*)outBlock, STM32_HAL_TIMEOUT);
    #elif defined(STM32_CRYPTO_AES_ONLY)
        ret = HAL_CRYPEx_AES(&hcryp, (uint8_t*)inBlock, AES_BLOCK_SIZE,
            outBlock, STM32_HAL_TIMEOUT);
    #else
        ret = HAL_CRYP_AESECB_Decrypt(&hcryp, (uint8_t*)inBlock, AES_BLOCK_SIZE,
            outBlock, STM32_HAL_TIMEOUT);
    #endif
        if (ret != HAL_OK) {
            ret = WC_TIMEOUT_E;
        }
        HAL_CRYP_DeInit(&hcryp);

    #else /* Standard Peripheral Library */
        ret = wc_Stm32_Aes_Init(aes, &cryptInit, &keyInit);
        if (ret != 0)
            return ret;

        /* reset registers to their default values */
        CRYP_DeInit();

        /* set direction and key */
        CRYP_KeyInit(&keyInit);
        cryptInit.CRYP_AlgoDir  = CRYP_AlgoDir_Decrypt;
        cryptInit.CRYP_AlgoMode = CRYP_AlgoMode_AES_Key;
        CRYP_Init(&cryptInit);

        /* enable crypto processor */
        CRYP_Cmd(ENABLE);

        /* wait until decrypt key has been initialized */
        while (CRYP_GetFlagStatus(CRYP_FLAG_BUSY) != RESET) {}

        /* set direction and mode */
        cryptInit.CRYP_AlgoDir  = CRYP_AlgoDir_Decrypt;
        cryptInit.CRYP_AlgoMode = CRYP_AlgoMode_AES_ECB;
        CRYP_Init(&cryptInit);

        /* enable crypto processor */
        CRYP_Cmd(ENABLE);

        /* flush IN/OUT FIFOs */
        CRYP_FIFOFlush();

        CRYP_DataIn(*(uint32_t*)&inBlock[0]);
        CRYP_DataIn(*(uint32_t*)&inBlock[4]);
        CRYP_DataIn(*(uint32_t*)&inBlock[8]);
        CRYP_DataIn(*(uint32_t*)&inBlock[12]);

        /* wait until the complete message has been processed */
        while (CRYP_GetFlagStatus(CRYP_FLAG_BUSY) != RESET) {}

        *(uint32_t*)&outBlock[0]  = CRYP_DataOut();
        *(uint32_t*)&outBlock[4]  = CRYP_DataOut();
        *(uint32_t*)&outBlock[8]  = CRYP_DataOut();
        *(uint32_t*)&outBlock[12] = CRYP_DataOut();

        /* disable crypto processor */
        CRYP_Cmd(DISABLE);
    #endif /* WOLFSSL_STM32_CUBEMX */

        return ret;
    }
    #endif /* WOLFSSL_AES_DIRECT || HAVE_AESCCM */
#endif /* HAVE_AES_DECRYPT */

#elif defined(HAVE_COLDFIRE_SEC)
    /* Freescale Coldfire SEC support for CBC mode.
     * NOTE: no support for AES-CTR/GCM/CCM/Direct */
    #include <wolfssl/wolfcrypt/types.h>
    #include "sec.h"
    #include "mcf5475_sec.h"
    #include "mcf5475_siu.h"
#elif defined(FREESCALE_LTC)
    #include "fsl_ltc.h"
    #if defined(FREESCALE_LTC_AES_GCM)
        #undef NEED_AES_TABLES
        #undef GCM_TABLE
    #else
        /* if LTC doesn't have GCM, use software with LTC AES ECB mode */
        static int wc_AesEncrypt(Aes* aes, const byte* inBlock, byte* outBlock)
        {
            wc_AesEncryptDirect(aes, outBlock, inBlock);
            return 0;
        }
        static int wc_AesDecrypt(Aes* aes, const byte* inBlock, byte* outBlock)
        {
            wc_AesDecryptDirect(aes, outBlock, inBlock);
            return 0;
        }
    #endif
#elif defined(FREESCALE_MMCAU)
    /* Freescale mmCAU hardware AES support for Direct, CBC, CCM, GCM modes
     * through the CAU/mmCAU library. Documentation located in
     * ColdFire/ColdFire+ CAU and Kinetis mmCAU Software Library User
     * Guide (See note in README). */
    #ifdef FREESCALE_MMCAU_CLASSIC
        /* MMCAU 1.4 library used with non-KSDK / classic MQX builds */
        #include "cau_api.h"
    #else
        #include "fsl_mmcau.h"
    #endif

    static int wc_AesEncrypt(Aes* aes, const byte* inBlock, byte* outBlock)
    {
        int ret;

    #ifdef FREESCALE_MMCAU_CLASSIC
        if ((wolfssl_word)outBlock % WOLFSSL_MMCAU_ALIGNMENT) {
            WOLFSSL_MSG("Bad cau_aes_encrypt alignment");
            return BAD_ALIGN_E;
        }
    #endif

        ret = wolfSSL_CryptHwMutexLock();
        if(ret == 0) {
        #ifdef FREESCALE_MMCAU_CLASSIC
            cau_aes_encrypt(inBlock, (byte*)aes->key, aes->rounds, outBlock);
        #else
            MMCAU_AES_EncryptEcb(inBlock, (byte*)aes->key, aes->rounds,
                                 outBlock);
        #endif
            wolfSSL_CryptHwMutexUnLock();
        }
        return ret;
    }
    #ifdef HAVE_AES_DECRYPT
    static int wc_AesDecrypt(Aes* aes, const byte* inBlock, byte* outBlock)
    {
        int ret;

    #ifdef FREESCALE_MMCAU_CLASSIC
        if ((wolfssl_word)outBlock % WOLFSSL_MMCAU_ALIGNMENT) {
            WOLFSSL_MSG("Bad cau_aes_decrypt alignment");
            return BAD_ALIGN_E;
        }
    #endif

        ret = wolfSSL_CryptHwMutexLock();
        if(ret == 0) {
        #ifdef FREESCALE_MMCAU_CLASSIC
            cau_aes_decrypt(inBlock, (byte*)aes->key, aes->rounds, outBlock);
        #else
            MMCAU_AES_DecryptEcb(inBlock, (byte*)aes->key, aes->rounds,
                                 outBlock);
        #endif
            wolfSSL_CryptHwMutexUnLock();
        }
        return ret;
    }
    #endif /* HAVE_AES_DECRYPT */

#elif defined(WOLFSSL_PIC32MZ_CRYPT)

    #include <wolfssl/wolfcrypt/port/pic32/pic32mz-crypt.h>

    #if defined(HAVE_AESGCM) || defined(WOLFSSL_AES_DIRECT)
    static int wc_AesEncrypt(Aes* aes, const byte* inBlock, byte* outBlock)
    {
        return wc_Pic32AesCrypt(aes->key, aes->keylen, NULL, 0,
            outBlock, inBlock, AES_BLOCK_SIZE,
            PIC32_ENCRYPTION, PIC32_ALGO_AES, PIC32_CRYPTOALGO_RECB);
    }
    #endif

    #if defined(HAVE_AES_DECRYPT) && defined(WOLFSSL_AES_DIRECT)
    static int wc_AesDecrypt(Aes* aes, const byte* inBlock, byte* outBlock)
    {
        return wc_Pic32AesCrypt(aes->key, aes->keylen, NULL, 0,
            outBlock, inBlock, AES_BLOCK_SIZE,
            PIC32_DECRYPTION, PIC32_ALGO_AES, PIC32_CRYPTOALGO_RECB);
    }
    #endif

#elif defined(WOLFSSL_NRF51_AES)
    /* Use built-in AES hardware - AES 128 ECB Encrypt Only */
    #include "wolfssl/wolfcrypt/port/nrf51.h"

    static int wc_AesEncrypt(Aes* aes, const byte* inBlock, byte* outBlock)
    {
        return nrf51_aes_encrypt(inBlock, (byte*)aes->key, aes->rounds, outBlock);
    }

    #ifdef HAVE_AES_DECRYPT
        #error nRF51 AES Hardware does not support decrypt
    #endif /* HAVE_AES_DECRYPT */

#elif defined(WOLFSSL_ESP32WROOM32_CRYPT) && \
    !defined(NO_WOLFSSL_ESP32WROOM32_CRYPT_AES)

    #include "wolfssl/wolfcrypt/port/Espressif/esp32-crypt.h"

    #if defined(HAVE_AESGCM) || defined(WOLFSSL_AES_DIRECT)
    static int wc_AesEncrypt(Aes* aes, const byte* inBlock, byte* outBlock)
    {
        return wc_esp32AesEncrypt(aes, inBlock, outBlock);
    }
    #endif

    #if defined(HAVE_AES_DECRYPT) && defined(WOLFSSL_AES_DIRECT)
    static int wc_AesDecrypt(Aes* aes, const byte* inBlock, byte* outBlock)
    {
       return wc_esp32AesDecrypt(aes, inBlock, outBlock);
    }
    #endif

#elif defined(WOLFSSL_AESNI)

    #define NEED_AES_TABLES

    /* Each platform needs to query info type 1 from cpuid to see if aesni is
     * supported. Also, let's setup a macro for proper linkage w/o ABI conflicts
     */

    #ifndef AESNI_ALIGN
        #define AESNI_ALIGN 16
    #endif

    #ifdef _MSC_VER
        #define XASM_LINK(f)
    #elif defined(__APPLE__)
        #define XASM_LINK(f) asm("_" f)
    #else
        #define XASM_LINK(f) asm(f)
    #endif /* _MSC_VER */

    static int checkAESNI = 0;
    static int haveAESNI  = 0;
    static word32 intel_flags = 0;

    static int Check_CPU_support_AES(void)
    {
        intel_flags = cpuid_get_flags();

        return IS_INTEL_AESNI(intel_flags) != 0;
    }


    /* tell C compiler these are asm functions in case any mix up of ABI underscore
       prefix between clang/gcc/llvm etc */
    #ifdef HAVE_AES_CBC
        void AES_CBC_encrypt(const unsigned char* in, unsigned char* out,
                             unsigned char* ivec, unsigned long length,
                             const unsigned char* KS, int nr)
                             XASM_LINK("AES_CBC_encrypt");

        #ifdef HAVE_AES_DECRYPT
            #if defined(WOLFSSL_AESNI_BY4)
                void AES_CBC_decrypt_by4(const unsigned char* in, unsigned char* out,
                                         unsigned char* ivec, unsigned long length,
                                         const unsigned char* KS, int nr)
                                         XASM_LINK("AES_CBC_decrypt_by4");
            #elif defined(WOLFSSL_AESNI_BY6)
                void AES_CBC_decrypt_by6(const unsigned char* in, unsigned char* out,
                                         unsigned char* ivec, unsigned long length,
                                         const unsigned char* KS, int nr)
                                         XASM_LINK("AES_CBC_decrypt_by6");
            #else /* WOLFSSL_AESNI_BYx */
                void AES_CBC_decrypt_by8(const unsigned char* in, unsigned char* out,
                                         unsigned char* ivec, unsigned long length,
                                         const unsigned char* KS, int nr)
                                         XASM_LINK("AES_CBC_decrypt_by8");
            #endif /* WOLFSSL_AESNI_BYx */
        #endif /* HAVE_AES_DECRYPT */
    #endif /* HAVE_AES_CBC */

    void AES_ECB_encrypt(const unsigned char* in, unsigned char* out,
                         unsigned long length, const unsigned char* KS, int nr)
                         XASM_LINK("AES_ECB_encrypt");

    #ifdef HAVE_AES_DECRYPT
        void AES_ECB_decrypt(const unsigned char* in, unsigned char* out,
                             unsigned long length, const unsigned char* KS, int nr)
                             XASM_LINK("AES_ECB_decrypt");
    #endif

    void AES_128_Key_Expansion(const unsigned char* userkey,
                               unsigned char* key_schedule)
                               XASM_LINK("AES_128_Key_Expansion");

    void AES_192_Key_Expansion(const unsigned char* userkey,
                               unsigned char* key_schedule)
                               XASM_LINK("AES_192_Key_Expansion");

    void AES_256_Key_Expansion(const unsigned char* userkey,
                               unsigned char* key_schedule)
                               XASM_LINK("AES_256_Key_Expansion");


    static int AES_set_encrypt_key(const unsigned char *userKey, const int bits,
                                   Aes* aes)
    {
        int ret;

        if (!userKey || !aes)
            return BAD_FUNC_ARG;

        switch (bits) {
            case 128:
               AES_128_Key_Expansion (userKey,(byte*)aes->key); aes->rounds = 10;
               return 0;
            case 192:
               AES_192_Key_Expansion (userKey,(byte*)aes->key); aes->rounds = 12;
               return 0;
            case 256:
               AES_256_Key_Expansion (userKey,(byte*)aes->key); aes->rounds = 14;
               return 0;
            default:
                ret = BAD_FUNC_ARG;
        }

        return ret;
    }

    #ifdef HAVE_AES_DECRYPT
        static int AES_set_decrypt_key(const unsigned char* userKey,
                                                    const int bits, Aes* aes)
        {
            int nr;
            Aes temp_key;
            __m128i *Key_Schedule = (__m128i*)aes->key;
            __m128i *Temp_Key_Schedule = (__m128i*)temp_key.key;

            if (!userKey || !aes)
                return BAD_FUNC_ARG;

            if (AES_set_encrypt_key(userKey,bits,&temp_key) == BAD_FUNC_ARG)
                return BAD_FUNC_ARG;

            nr = temp_key.rounds;
            aes->rounds = nr;

            Key_Schedule[nr] = Temp_Key_Schedule[0];
            Key_Schedule[nr-1] = _mm_aesimc_si128(Temp_Key_Schedule[1]);
            Key_Schedule[nr-2] = _mm_aesimc_si128(Temp_Key_Schedule[2]);
            Key_Schedule[nr-3] = _mm_aesimc_si128(Temp_Key_Schedule[3]);
            Key_Schedule[nr-4] = _mm_aesimc_si128(Temp_Key_Schedule[4]);
            Key_Schedule[nr-5] = _mm_aesimc_si128(Temp_Key_Schedule[5]);
            Key_Schedule[nr-6] = _mm_aesimc_si128(Temp_Key_Schedule[6]);
            Key_Schedule[nr-7] = _mm_aesimc_si128(Temp_Key_Schedule[7]);
            Key_Schedule[nr-8] = _mm_aesimc_si128(Temp_Key_Schedule[8]);
            Key_Schedule[nr-9] = _mm_aesimc_si128(Temp_Key_Schedule[9]);

            if (nr>10) {
                Key_Schedule[nr-10] = _mm_aesimc_si128(Temp_Key_Schedule[10]);
                Key_Schedule[nr-11] = _mm_aesimc_si128(Temp_Key_Schedule[11]);
            }

            if (nr>12) {
                Key_Schedule[nr-12] = _mm_aesimc_si128(Temp_Key_Schedule[12]);
                Key_Schedule[nr-13] = _mm_aesimc_si128(Temp_Key_Schedule[13]);
            }

            Key_Schedule[0] = Temp_Key_Schedule[nr];

            return 0;
        }
    #endif /* HAVE_AES_DECRYPT */

#elif (defined(WOLFSSL_IMX6_CAAM) && !defined(NO_IMX6_CAAM_AES)) || \
      ((defined(WOLFSSL_AFALG) || defined(WOLFSSL_DEVCRYPTO_AES)) && \
        defined(HAVE_AESCCM))
        static int wc_AesEncrypt(Aes* aes, const byte* inBlock, byte* outBlock)
        {
            wc_AesEncryptDirect(aes, outBlock, inBlock);
            return 0;
        }

#elif defined(WOLFSSL_AFALG)
#elif defined(WOLFSSL_DEVCRYPTO_AES)

#elif defined(WOLFSSL_SCE) && !defined(WOLFSSL_SCE_NO_AES)
    #include "hal_data.h"

    #ifndef WOLFSSL_SCE_AES256_HANDLE
        #define WOLFSSL_SCE_AES256_HANDLE g_sce_aes_256
    #endif

    #ifndef WOLFSSL_SCE_AES192_HANDLE
        #define WOLFSSL_SCE_AES192_HANDLE g_sce_aes_192
    #endif

    #ifndef WOLFSSL_SCE_AES128_HANDLE
        #define WOLFSSL_SCE_AES128_HANDLE g_sce_aes_128
    #endif

    static int AES_ECB_encrypt(Aes* aes, const byte* inBlock, byte* outBlock,
            int sz)
    {
        uint32_t ret;

        if (WOLFSSL_SCE_GSCE_HANDLE.p_cfg->endian_flag ==
                CRYPTO_WORD_ENDIAN_BIG) {
            ByteReverseWords((word32*)inBlock, (word32*)inBlock, sz);
        }

        switch (aes->keylen) {
        #ifdef WOLFSSL_AES_128
            case AES_128_KEY_SIZE:
                ret = WOLFSSL_SCE_AES128_HANDLE.p_api->encrypt(
                        WOLFSSL_SCE_AES128_HANDLE.p_ctrl, aes->key,
                        NULL, (sz / sizeof(word32)), (word32*)inBlock,
                        (word32*)outBlock);
                break;
        #endif
        #ifdef WOLFSSL_AES_192
            case AES_192_KEY_SIZE:
                ret = WOLFSSL_SCE_AES192_HANDLE.p_api->encrypt(
                        WOLFSSL_SCE_AES192_HANDLE.p_ctrl, aes->key,
                        NULL, (sz / sizeof(word32)), (word32*)inBlock,
                        (word32*)outBlock);
                break;
        #endif
        #ifdef WOLFSSL_AES_256
            case AES_256_KEY_SIZE:
                ret = WOLFSSL_SCE_AES256_HANDLE.p_api->encrypt(
                        WOLFSSL_SCE_AES256_HANDLE.p_ctrl, aes->key,
                        NULL, (sz / sizeof(word32)), (word32*)inBlock,
                        (word32*)outBlock);
                break;
        #endif
            default:
                WOLFSSL_MSG("Unknown key size");
                return BAD_FUNC_ARG;
        }

        if (ret != SSP_SUCCESS) {
           /* revert input */
            ByteReverseWords((word32*)inBlock, (word32*)inBlock, sz);
            return WC_HW_E;
        }

        if (WOLFSSL_SCE_GSCE_HANDLE.p_cfg->endian_flag ==
                CRYPTO_WORD_ENDIAN_BIG) {
            ByteReverseWords((word32*)outBlock, (word32*)outBlock, sz);
            if (inBlock != outBlock) {
                /* revert input */
                ByteReverseWords((word32*)inBlock, (word32*)inBlock, sz);
            }
        }
        return 0;
    }

    #if defined(HAVE_AES_DECRYPT)
    static int AES_ECB_decrypt(Aes* aes, const byte* inBlock, byte* outBlock,
            int sz)
    {
        uint32_t ret;

        if (WOLFSSL_SCE_GSCE_HANDLE.p_cfg->endian_flag ==
                CRYPTO_WORD_ENDIAN_BIG) {
            ByteReverseWords((word32*)inBlock, (word32*)inBlock, sz);
        }

        switch (aes->keylen) {
        #ifdef WOLFSSL_AES_128
            case AES_128_KEY_SIZE:
                ret = WOLFSSL_SCE_AES128_HANDLE.p_api->decrypt(
                        WOLFSSL_SCE_AES128_HANDLE.p_ctrl, aes->key, aes->reg,
                        (sz / sizeof(word32)), (word32*)inBlock,
                        (word32*)outBlock);
                break;
        #endif
        #ifdef WOLFSSL_AES_192
            case AES_192_KEY_SIZE:
                ret = WOLFSSL_SCE_AES192_HANDLE.p_api->decrypt(
                        WOLFSSL_SCE_AES192_HANDLE.p_ctrl, aes->key, aes->reg,
                        (sz / sizeof(word32)), (word32*)inBlock,
                        (word32*)outBlock);
                break;
        #endif
        #ifdef WOLFSSL_AES_256
            case AES_256_KEY_SIZE:
                ret = WOLFSSL_SCE_AES256_HANDLE.p_api->decrypt(
                        WOLFSSL_SCE_AES256_HANDLE.p_ctrl, aes->key, aes->reg,
                        (sz / sizeof(word32)), (word32*)inBlock,
                        (word32*)outBlock);
                break;
        #endif
            default:
                WOLFSSL_MSG("Unknown key size");
                return BAD_FUNC_ARG;
        }
        if (ret != SSP_SUCCESS) {
            return WC_HW_E;
        }

        if (WOLFSSL_SCE_GSCE_HANDLE.p_cfg->endian_flag ==
                CRYPTO_WORD_ENDIAN_BIG) {
            ByteReverseWords((word32*)outBlock, (word32*)outBlock, sz);
            if (inBlock != outBlock) {
                /* revert input */
                ByteReverseWords((word32*)inBlock, (word32*)inBlock, sz);
            }
        }

        return 0;
    }

    #endif

    #if defined(HAVE_AESGCM) || defined(WOLFSSL_AES_DIRECT)
    static int wc_AesEncrypt(Aes* aes, const byte* inBlock, byte* outBlock)
    {
        return AES_ECB_encrypt(aes, inBlock, outBlock, AES_BLOCK_SIZE);
    }
    #endif

    #if defined(HAVE_AES_DECRYPT) && defined(WOLFSSL_AES_DIRECT)
    static int wc_AesDecrypt(Aes* aes, const byte* inBlock, byte* outBlock)
    {
        return AES_ECB_decrypt(aes, inBlock, outBlock, AES_BLOCK_SIZE);
    }
    #endif
#else

    /* using wolfCrypt software implementation */
    #define NEED_AES_TABLES
#endif



#ifdef NEED_AES_TABLES

static const FLASH_QUALIFIER word32 rcon[] = {
    0x01000000, 0x02000000, 0x04000000, 0x08000000,
    0x10000000, 0x20000000, 0x40000000, 0x80000000,
    0x1B000000, 0x36000000,
    /* for 128-bit blocks, Rijndael never uses more than 10 rcon values */
};

#ifndef WOLFSSL_AES_SMALL_TABLES
static const FLASH_QUALIFIER word32 Te[4][256] = {
{
    0xc66363a5U, 0xf87c7c84U, 0xee777799U, 0xf67b7b8dU,
    0xfff2f20dU, 0xd66b6bbdU, 0xde6f6fb1U, 0x91c5c554U,
    0x60303050U, 0x02010103U, 0xce6767a9U, 0x562b2b7dU,
    0xe7fefe19U, 0xb5d7d762U, 0x4dababe6U, 0xec76769aU,
    0x8fcaca45U, 0x1f82829dU, 0x89c9c940U, 0xfa7d7d87U,
    0xeffafa15U, 0xb25959ebU, 0x8e4747c9U, 0xfbf0f00bU,
    0x41adadecU, 0xb3d4d467U, 0x5fa2a2fdU, 0x45afafeaU,
    0x239c9cbfU, 0x53a4a4f7U, 0xe4727296U, 0x9bc0c05bU,
    0x75b7b7c2U, 0xe1fdfd1cU, 0x3d9393aeU, 0x4c26266aU,
    0x6c36365aU, 0x7e3f3f41U, 0xf5f7f702U, 0x83cccc4fU,
    0x6834345cU, 0x51a5a5f4U, 0xd1e5e534U, 0xf9f1f108U,
    0xe2717193U, 0xabd8d873U, 0x62313153U, 0x2a15153fU,
    0x0804040cU, 0x95c7c752U, 0x46232365U, 0x9dc3c35eU,
    0x30181828U, 0x379696a1U, 0x0a05050fU, 0x2f9a9ab5U,
    0x0e070709U, 0x24121236U, 0x1b80809bU, 0xdfe2e23dU,
    0xcdebeb26U, 0x4e272769U, 0x7fb2b2cdU, 0xea75759fU,
    0x1209091bU, 0x1d83839eU, 0x582c2c74U, 0x341a1a2eU,
    0x361b1b2dU, 0xdc6e6eb2U, 0xb45a5aeeU, 0x5ba0a0fbU,
    0xa45252f6U, 0x763b3b4dU, 0xb7d6d661U, 0x7db3b3ceU,
    0x5229297bU, 0xdde3e33eU, 0x5e2f2f71U, 0x13848497U,
    0xa65353f5U, 0xb9d1d168U, 0x00000000U, 0xc1eded2cU,
    0x40202060U, 0xe3fcfc1fU, 0x79b1b1c8U, 0xb65b5bedU,
    0xd46a6abeU, 0x8dcbcb46U, 0x67bebed9U, 0x7239394bU,
    0x944a4adeU, 0x984c4cd4U, 0xb05858e8U, 0x85cfcf4aU,
    0xbbd0d06bU, 0xc5efef2aU, 0x4faaaae5U, 0xedfbfb16U,
    0x864343c5U, 0x9a4d4dd7U, 0x66333355U, 0x11858594U,
    0x8a4545cfU, 0xe9f9f910U, 0x04020206U, 0xfe7f7f81U,
    0xa05050f0U, 0x783c3c44U, 0x259f9fbaU, 0x4ba8a8e3U,
    0xa25151f3U, 0x5da3a3feU, 0x804040c0U, 0x058f8f8aU,
    0x3f9292adU, 0x219d9dbcU, 0x70383848U, 0xf1f5f504U,
    0x63bcbcdfU, 0x77b6b6c1U, 0xafdada75U, 0x42212163U,
    0x20101030U, 0xe5ffff1aU, 0xfdf3f30eU, 0xbfd2d26dU,
    0x81cdcd4cU, 0x180c0c14U, 0x26131335U, 0xc3ecec2fU,
    0xbe5f5fe1U, 0x359797a2U, 0x884444ccU, 0x2e171739U,
    0x93c4c457U, 0x55a7a7f2U, 0xfc7e7e82U, 0x7a3d3d47U,
    0xc86464acU, 0xba5d5de7U, 0x3219192bU, 0xe6737395U,
    0xc06060a0U, 0x19818198U, 0x9e4f4fd1U, 0xa3dcdc7fU,
    0x44222266U, 0x542a2a7eU, 0x3b9090abU, 0x0b888883U,
    0x8c4646caU, 0xc7eeee29U, 0x6bb8b8d3U, 0x2814143cU,
    0xa7dede79U, 0xbc5e5ee2U, 0x160b0b1dU, 0xaddbdb76U,
    0xdbe0e03bU, 0x64323256U, 0x743a3a4eU, 0x140a0a1eU,
    0x924949dbU, 0x0c06060aU, 0x4824246cU, 0xb85c5ce4U,
    0x9fc2c25dU, 0xbdd3d36eU, 0x43acacefU, 0xc46262a6U,
    0x399191a8U, 0x319595a4U, 0xd3e4e437U, 0xf279798bU,
    0xd5e7e732U, 0x8bc8c843U, 0x6e373759U, 0xda6d6db7U,
    0x018d8d8cU, 0xb1d5d564U, 0x9c4e4ed2U, 0x49a9a9e0U,
    0xd86c6cb4U, 0xac5656faU, 0xf3f4f407U, 0xcfeaea25U,
    0xca6565afU, 0xf47a7a8eU, 0x47aeaee9U, 0x10080818U,
    0x6fbabad5U, 0xf0787888U, 0x4a25256fU, 0x5c2e2e72U,
    0x381c1c24U, 0x57a6a6f1U, 0x73b4b4c7U, 0x97c6c651U,
    0xcbe8e823U, 0xa1dddd7cU, 0xe874749cU, 0x3e1f1f21U,
    0x964b4bddU, 0x61bdbddcU, 0x0d8b8b86U, 0x0f8a8a85U,
    0xe0707090U, 0x7c3e3e42U, 0x71b5b5c4U, 0xcc6666aaU,
    0x904848d8U, 0x06030305U, 0xf7f6f601U, 0x1c0e0e12U,
    0xc26161a3U, 0x6a35355fU, 0xae5757f9U, 0x69b9b9d0U,
    0x17868691U, 0x99c1c158U, 0x3a1d1d27U, 0x279e9eb9U,
    0xd9e1e138U, 0xebf8f813U, 0x2b9898b3U, 0x22111133U,
    0xd26969bbU, 0xa9d9d970U, 0x078e8e89U, 0x339494a7U,
    0x2d9b9bb6U, 0x3c1e1e22U, 0x15878792U, 0xc9e9e920U,
    0x87cece49U, 0xaa5555ffU, 0x50282878U, 0xa5dfdf7aU,
    0x038c8c8fU, 0x59a1a1f8U, 0x09898980U, 0x1a0d0d17U,
    0x65bfbfdaU, 0xd7e6e631U, 0x844242c6U, 0xd06868b8U,
    0x824141c3U, 0x299999b0U, 0x5a2d2d77U, 0x1e0f0f11U,
    0x7bb0b0cbU, 0xa85454fcU, 0x6dbbbbd6U, 0x2c16163aU,
},
{
    0xa5c66363U, 0x84f87c7cU, 0x99ee7777U, 0x8df67b7bU,
    0x0dfff2f2U, 0xbdd66b6bU, 0xb1de6f6fU, 0x5491c5c5U,
    0x50603030U, 0x03020101U, 0xa9ce6767U, 0x7d562b2bU,
    0x19e7fefeU, 0x62b5d7d7U, 0xe64dababU, 0x9aec7676U,
    0x458fcacaU, 0x9d1f8282U, 0x4089c9c9U, 0x87fa7d7dU,
    0x15effafaU, 0xebb25959U, 0xc98e4747U, 0x0bfbf0f0U,
    0xec41adadU, 0x67b3d4d4U, 0xfd5fa2a2U, 0xea45afafU,
    0xbf239c9cU, 0xf753a4a4U, 0x96e47272U, 0x5b9bc0c0U,
    0xc275b7b7U, 0x1ce1fdfdU, 0xae3d9393U, 0x6a4c2626U,
    0x5a6c3636U, 0x417e3f3fU, 0x02f5f7f7U, 0x4f83ccccU,
    0x5c683434U, 0xf451a5a5U, 0x34d1e5e5U, 0x08f9f1f1U,
    0x93e27171U, 0x73abd8d8U, 0x53623131U, 0x3f2a1515U,
    0x0c080404U, 0x5295c7c7U, 0x65462323U, 0x5e9dc3c3U,
    0x28301818U, 0xa1379696U, 0x0f0a0505U, 0xb52f9a9aU,
    0x090e0707U, 0x36241212U, 0x9b1b8080U, 0x3ddfe2e2U,
    0x26cdebebU, 0x694e2727U, 0xcd7fb2b2U, 0x9fea7575U,
    0x1b120909U, 0x9e1d8383U, 0x74582c2cU, 0x2e341a1aU,
    0x2d361b1bU, 0xb2dc6e6eU, 0xeeb45a5aU, 0xfb5ba0a0U,
    0xf6a45252U, 0x4d763b3bU, 0x61b7d6d6U, 0xce7db3b3U,
    0x7b522929U, 0x3edde3e3U, 0x715e2f2fU, 0x97138484U,
    0xf5a65353U, 0x68b9d1d1U, 0x00000000U, 0x2cc1ededU,
    0x60402020U, 0x1fe3fcfcU, 0xc879b1b1U, 0xedb65b5bU,
    0xbed46a6aU, 0x468dcbcbU, 0xd967bebeU, 0x4b723939U,
    0xde944a4aU, 0xd4984c4cU, 0xe8b05858U, 0x4a85cfcfU,
    0x6bbbd0d0U, 0x2ac5efefU, 0xe54faaaaU, 0x16edfbfbU,
    0xc5864343U, 0xd79a4d4dU, 0x55663333U, 0x94118585U,
    0xcf8a4545U, 0x10e9f9f9U, 0x06040202U, 0x81fe7f7fU,
    0xf0a05050U, 0x44783c3cU, 0xba259f9fU, 0xe34ba8a8U,
    0xf3a25151U, 0xfe5da3a3U, 0xc0804040U, 0x8a058f8fU,
    0xad3f9292U, 0xbc219d9dU, 0x48703838U, 0x04f1f5f5U,
    0xdf63bcbcU, 0xc177b6b6U, 0x75afdadaU, 0x63422121U,
    0x30201010U, 0x1ae5ffffU, 0x0efdf3f3U, 0x6dbfd2d2U,
    0x4c81cdcdU, 0x14180c0cU, 0x35261313U, 0x2fc3ececU,
    0xe1be5f5fU, 0xa2359797U, 0xcc884444U, 0x392e1717U,
    0x5793c4c4U, 0xf255a7a7U, 0x82fc7e7eU, 0x477a3d3dU,
    0xacc86464U, 0xe7ba5d5dU, 0x2b321919U, 0x95e67373U,
    0xa0c06060U, 0x98198181U, 0xd19e4f4fU, 0x7fa3dcdcU,
    0x66442222U, 0x7e542a2aU, 0xab3b9090U, 0x830b8888U,
    0xca8c4646U, 0x29c7eeeeU, 0xd36bb8b8U, 0x3c281414U,
    0x79a7dedeU, 0xe2bc5e5eU, 0x1d160b0bU, 0x76addbdbU,
    0x3bdbe0e0U, 0x56643232U, 0x4e743a3aU, 0x1e140a0aU,
    0xdb924949U, 0x0a0c0606U, 0x6c482424U, 0xe4b85c5cU,
    0x5d9fc2c2U, 0x6ebdd3d3U, 0xef43acacU, 0xa6c46262U,
    0xa8399191U, 0xa4319595U, 0x37d3e4e4U, 0x8bf27979U,
    0x32d5e7e7U, 0x438bc8c8U, 0x596e3737U, 0xb7da6d6dU,
    0x8c018d8dU, 0x64b1d5d5U, 0xd29c4e4eU, 0xe049a9a9U,
    0xb4d86c6cU, 0xfaac5656U, 0x07f3f4f4U, 0x25cfeaeaU,
    0xafca6565U, 0x8ef47a7aU, 0xe947aeaeU, 0x18100808U,
    0xd56fbabaU, 0x88f07878U, 0x6f4a2525U, 0x725c2e2eU,
    0x24381c1cU, 0xf157a6a6U, 0xc773b4b4U, 0x5197c6c6U,
    0x23cbe8e8U, 0x7ca1ddddU, 0x9ce87474U, 0x213e1f1fU,
    0xdd964b4bU, 0xdc61bdbdU, 0x860d8b8bU, 0x850f8a8aU,
    0x90e07070U, 0x427c3e3eU, 0xc471b5b5U, 0xaacc6666U,
    0xd8904848U, 0x05060303U, 0x01f7f6f6U, 0x121c0e0eU,
    0xa3c26161U, 0x5f6a3535U, 0xf9ae5757U, 0xd069b9b9U,
    0x91178686U, 0x5899c1c1U, 0x273a1d1dU, 0xb9279e9eU,
    0x38d9e1e1U, 0x13ebf8f8U, 0xb32b9898U, 0x33221111U,
    0xbbd26969U, 0x70a9d9d9U, 0x89078e8eU, 0xa7339494U,
    0xb62d9b9bU, 0x223c1e1eU, 0x92158787U, 0x20c9e9e9U,
    0x4987ceceU, 0xffaa5555U, 0x78502828U, 0x7aa5dfdfU,
    0x8f038c8cU, 0xf859a1a1U, 0x80098989U, 0x171a0d0dU,
    0xda65bfbfU, 0x31d7e6e6U, 0xc6844242U, 0xb8d06868U,
    0xc3824141U, 0xb0299999U, 0x775a2d2dU, 0x111e0f0fU,
    0xcb7bb0b0U, 0xfca85454U, 0xd66dbbbbU, 0x3a2c1616U,
},
{
    0x63a5c663U, 0x7c84f87cU, 0x7799ee77U, 0x7b8df67bU,
    0xf20dfff2U, 0x6bbdd66bU, 0x6fb1de6fU, 0xc55491c5U,
    0x30506030U, 0x01030201U, 0x67a9ce67U, 0x2b7d562bU,
    0xfe19e7feU, 0xd762b5d7U, 0xabe64dabU, 0x769aec76U,
    0xca458fcaU, 0x829d1f82U, 0xc94089c9U, 0x7d87fa7dU,
    0xfa15effaU, 0x59ebb259U, 0x47c98e47U, 0xf00bfbf0U,
    0xadec41adU, 0xd467b3d4U, 0xa2fd5fa2U, 0xafea45afU,
    0x9cbf239cU, 0xa4f753a4U, 0x7296e472U, 0xc05b9bc0U,
    0xb7c275b7U, 0xfd1ce1fdU, 0x93ae3d93U, 0x266a4c26U,
    0x365a6c36U, 0x3f417e3fU, 0xf702f5f7U, 0xcc4f83ccU,
    0x345c6834U, 0xa5f451a5U, 0xe534d1e5U, 0xf108f9f1U,
    0x7193e271U, 0xd873abd8U, 0x31536231U, 0x153f2a15U,
    0x040c0804U, 0xc75295c7U, 0x23654623U, 0xc35e9dc3U,
    0x18283018U, 0x96a13796U, 0x050f0a05U, 0x9ab52f9aU,
    0x07090e07U, 0x12362412U, 0x809b1b80U, 0xe23ddfe2U,
    0xeb26cdebU, 0x27694e27U, 0xb2cd7fb2U, 0x759fea75U,
    0x091b1209U, 0x839e1d83U, 0x2c74582cU, 0x1a2e341aU,
    0x1b2d361bU, 0x6eb2dc6eU, 0x5aeeb45aU, 0xa0fb5ba0U,
    0x52f6a452U, 0x3b4d763bU, 0xd661b7d6U, 0xb3ce7db3U,
    0x297b5229U, 0xe33edde3U, 0x2f715e2fU, 0x84971384U,
    0x53f5a653U, 0xd168b9d1U, 0x00000000U, 0xed2cc1edU,
    0x20604020U, 0xfc1fe3fcU, 0xb1c879b1U, 0x5bedb65bU,
    0x6abed46aU, 0xcb468dcbU, 0xbed967beU, 0x394b7239U,
    0x4ade944aU, 0x4cd4984cU, 0x58e8b058U, 0xcf4a85cfU,
    0xd06bbbd0U, 0xef2ac5efU, 0xaae54faaU, 0xfb16edfbU,
    0x43c58643U, 0x4dd79a4dU, 0x33556633U, 0x85941185U,
    0x45cf8a45U, 0xf910e9f9U, 0x02060402U, 0x7f81fe7fU,
    0x50f0a050U, 0x3c44783cU, 0x9fba259fU, 0xa8e34ba8U,
    0x51f3a251U, 0xa3fe5da3U, 0x40c08040U, 0x8f8a058fU,
    0x92ad3f92U, 0x9dbc219dU, 0x38487038U, 0xf504f1f5U,
    0xbcdf63bcU, 0xb6c177b6U, 0xda75afdaU, 0x21634221U,
    0x10302010U, 0xff1ae5ffU, 0xf30efdf3U, 0xd26dbfd2U,
    0xcd4c81cdU, 0x0c14180cU, 0x13352613U, 0xec2fc3ecU,
    0x5fe1be5fU, 0x97a23597U, 0x44cc8844U, 0x17392e17U,
    0xc45793c4U, 0xa7f255a7U, 0x7e82fc7eU, 0x3d477a3dU,
    0x64acc864U, 0x5de7ba5dU, 0x192b3219U, 0x7395e673U,
    0x60a0c060U, 0x81981981U, 0x4fd19e4fU, 0xdc7fa3dcU,
    0x22664422U, 0x2a7e542aU, 0x90ab3b90U, 0x88830b88U,
    0x46ca8c46U, 0xee29c7eeU, 0xb8d36bb8U, 0x143c2814U,
    0xde79a7deU, 0x5ee2bc5eU, 0x0b1d160bU, 0xdb76addbU,
    0xe03bdbe0U, 0x32566432U, 0x3a4e743aU, 0x0a1e140aU,
    0x49db9249U, 0x060a0c06U, 0x246c4824U, 0x5ce4b85cU,
    0xc25d9fc2U, 0xd36ebdd3U, 0xacef43acU, 0x62a6c462U,
    0x91a83991U, 0x95a43195U, 0xe437d3e4U, 0x798bf279U,
    0xe732d5e7U, 0xc8438bc8U, 0x37596e37U, 0x6db7da6dU,
    0x8d8c018dU, 0xd564b1d5U, 0x4ed29c4eU, 0xa9e049a9U,
    0x6cb4d86cU, 0x56faac56U, 0xf407f3f4U, 0xea25cfeaU,
    0x65afca65U, 0x7a8ef47aU, 0xaee947aeU, 0x08181008U,
    0xbad56fbaU, 0x7888f078U, 0x256f4a25U, 0x2e725c2eU,
    0x1c24381cU, 0xa6f157a6U, 0xb4c773b4U, 0xc65197c6U,
    0xe823cbe8U, 0xdd7ca1ddU, 0x749ce874U, 0x1f213e1fU,
    0x4bdd964bU, 0xbddc61bdU, 0x8b860d8bU, 0x8a850f8aU,
    0x7090e070U, 0x3e427c3eU, 0xb5c471b5U, 0x66aacc66U,
    0x48d89048U, 0x03050603U, 0xf601f7f6U, 0x0e121c0eU,
    0x61a3c261U, 0x355f6a35U, 0x57f9ae57U, 0xb9d069b9U,
    0x86911786U, 0xc15899c1U, 0x1d273a1dU, 0x9eb9279eU,
    0xe138d9e1U, 0xf813ebf8U, 0x98b32b98U, 0x11332211U,
    0x69bbd269U, 0xd970a9d9U, 0x8e89078eU, 0x94a73394U,
    0x9bb62d9bU, 0x1e223c1eU, 0x87921587U, 0xe920c9e9U,
    0xce4987ceU, 0x55ffaa55U, 0x28785028U, 0xdf7aa5dfU,
    0x8c8f038cU, 0xa1f859a1U, 0x89800989U, 0x0d171a0dU,
    0xbfda65bfU, 0xe631d7e6U, 0x42c68442U, 0x68b8d068U,
    0x41c38241U, 0x99b02999U, 0x2d775a2dU, 0x0f111e0fU,
    0xb0cb7bb0U, 0x54fca854U, 0xbbd66dbbU, 0x163a2c16U,
},
{
    0x6363a5c6U, 0x7c7c84f8U, 0x777799eeU, 0x7b7b8df6U,
    0xf2f20dffU, 0x6b6bbdd6U, 0x6f6fb1deU, 0xc5c55491U,
    0x30305060U, 0x01010302U, 0x6767a9ceU, 0x2b2b7d56U,
    0xfefe19e7U, 0xd7d762b5U, 0xababe64dU, 0x76769aecU,
    0xcaca458fU, 0x82829d1fU, 0xc9c94089U, 0x7d7d87faU,
    0xfafa15efU, 0x5959ebb2U, 0x4747c98eU, 0xf0f00bfbU,
    0xadadec41U, 0xd4d467b3U, 0xa2a2fd5fU, 0xafafea45U,
    0x9c9cbf23U, 0xa4a4f753U, 0x727296e4U, 0xc0c05b9bU,
    0xb7b7c275U, 0xfdfd1ce1U, 0x9393ae3dU, 0x26266a4cU,
    0x36365a6cU, 0x3f3f417eU, 0xf7f702f5U, 0xcccc4f83U,
    0x34345c68U, 0xa5a5f451U, 0xe5e534d1U, 0xf1f108f9U,
    0x717193e2U, 0xd8d873abU, 0x31315362U, 0x15153f2aU,
    0x04040c08U, 0xc7c75295U, 0x23236546U, 0xc3c35e9dU,
    0x18182830U, 0x9696a137U, 0x05050f0aU, 0x9a9ab52fU,
    0x0707090eU, 0x12123624U, 0x80809b1bU, 0xe2e23ddfU,
    0xebeb26cdU, 0x2727694eU, 0xb2b2cd7fU, 0x75759feaU,
    0x09091b12U, 0x83839e1dU, 0x2c2c7458U, 0x1a1a2e34U,
    0x1b1b2d36U, 0x6e6eb2dcU, 0x5a5aeeb4U, 0xa0a0fb5bU,
    0x5252f6a4U, 0x3b3b4d76U, 0xd6d661b7U, 0xb3b3ce7dU,
    0x29297b52U, 0xe3e33eddU, 0x2f2f715eU, 0x84849713U,
    0x5353f5a6U, 0xd1d168b9U, 0x00000000U, 0xeded2cc1U,
    0x20206040U, 0xfcfc1fe3U, 0xb1b1c879U, 0x5b5bedb6U,
    0x6a6abed4U, 0xcbcb468dU, 0xbebed967U, 0x39394b72U,
    0x4a4ade94U, 0x4c4cd498U, 0x5858e8b0U, 0xcfcf4a85U,
    0xd0d06bbbU, 0xefef2ac5U, 0xaaaae54fU, 0xfbfb16edU,
    0x4343c586U, 0x4d4dd79aU, 0x33335566U, 0x85859411U,
    0x4545cf8aU, 0xf9f910e9U, 0x02020604U, 0x7f7f81feU,
    0x5050f0a0U, 0x3c3c4478U, 0x9f9fba25U, 0xa8a8e34bU,
    0x5151f3a2U, 0xa3a3fe5dU, 0x4040c080U, 0x8f8f8a05U,
    0x9292ad3fU, 0x9d9dbc21U, 0x38384870U, 0xf5f504f1U,
    0xbcbcdf63U, 0xb6b6c177U, 0xdada75afU, 0x21216342U,
    0x10103020U, 0xffff1ae5U, 0xf3f30efdU, 0xd2d26dbfU,
    0xcdcd4c81U, 0x0c0c1418U, 0x13133526U, 0xecec2fc3U,
    0x5f5fe1beU, 0x9797a235U, 0x4444cc88U, 0x1717392eU,
    0xc4c45793U, 0xa7a7f255U, 0x7e7e82fcU, 0x3d3d477aU,
    0x6464acc8U, 0x5d5de7baU, 0x19192b32U, 0x737395e6U,
    0x6060a0c0U, 0x81819819U, 0x4f4fd19eU, 0xdcdc7fa3U,
    0x22226644U, 0x2a2a7e54U, 0x9090ab3bU, 0x8888830bU,
    0x4646ca8cU, 0xeeee29c7U, 0xb8b8d36bU, 0x14143c28U,
    0xdede79a7U, 0x5e5ee2bcU, 0x0b0b1d16U, 0xdbdb76adU,
    0xe0e03bdbU, 0x32325664U, 0x3a3a4e74U, 0x0a0a1e14U,
    0x4949db92U, 0x06060a0cU, 0x24246c48U, 0x5c5ce4b8U,
    0xc2c25d9fU, 0xd3d36ebdU, 0xacacef43U, 0x6262a6c4U,
    0x9191a839U, 0x9595a431U, 0xe4e437d3U, 0x79798bf2U,
    0xe7e732d5U, 0xc8c8438bU, 0x3737596eU, 0x6d6db7daU,
    0x8d8d8c01U, 0xd5d564b1U, 0x4e4ed29cU, 0xa9a9e049U,
    0x6c6cb4d8U, 0x5656faacU, 0xf4f407f3U, 0xeaea25cfU,
    0x6565afcaU, 0x7a7a8ef4U, 0xaeaee947U, 0x08081810U,
    0xbabad56fU, 0x787888f0U, 0x25256f4aU, 0x2e2e725cU,
    0x1c1c2438U, 0xa6a6f157U, 0xb4b4c773U, 0xc6c65197U,
    0xe8e823cbU, 0xdddd7ca1U, 0x74749ce8U, 0x1f1f213eU,
    0x4b4bdd96U, 0xbdbddc61U, 0x8b8b860dU, 0x8a8a850fU,
    0x707090e0U, 0x3e3e427cU, 0xb5b5c471U, 0x6666aaccU,
    0x4848d890U, 0x03030506U, 0xf6f601f7U, 0x0e0e121cU,
    0x6161a3c2U, 0x35355f6aU, 0x5757f9aeU, 0xb9b9d069U,
    0x86869117U, 0xc1c15899U, 0x1d1d273aU, 0x9e9eb927U,
    0xe1e138d9U, 0xf8f813ebU, 0x9898b32bU, 0x11113322U,
    0x6969bbd2U, 0xd9d970a9U, 0x8e8e8907U, 0x9494a733U,
    0x9b9bb62dU, 0x1e1e223cU, 0x87879215U, 0xe9e920c9U,
    0xcece4987U, 0x5555ffaaU, 0x28287850U, 0xdfdf7aa5U,
    0x8c8c8f03U, 0xa1a1f859U, 0x89898009U, 0x0d0d171aU,
    0xbfbfda65U, 0xe6e631d7U, 0x4242c684U, 0x6868b8d0U,
    0x4141c382U, 0x9999b029U, 0x2d2d775aU, 0x0f0f111eU,
    0xb0b0cb7bU, 0x5454fca8U, 0xbbbbd66dU, 0x16163a2cU,
}
};

#ifdef HAVE_AES_DECRYPT
static const FLASH_QUALIFIER word32 Td[4][256] = {
{
    0x51f4a750U, 0x7e416553U, 0x1a17a4c3U, 0x3a275e96U,
    0x3bab6bcbU, 0x1f9d45f1U, 0xacfa58abU, 0x4be30393U,
    0x2030fa55U, 0xad766df6U, 0x88cc7691U, 0xf5024c25U,
    0x4fe5d7fcU, 0xc52acbd7U, 0x26354480U, 0xb562a38fU,
    0xdeb15a49U, 0x25ba1b67U, 0x45ea0e98U, 0x5dfec0e1U,
    0xc32f7502U, 0x814cf012U, 0x8d4697a3U, 0x6bd3f9c6U,
    0x038f5fe7U, 0x15929c95U, 0xbf6d7aebU, 0x955259daU,
    0xd4be832dU, 0x587421d3U, 0x49e06929U, 0x8ec9c844U,
    0x75c2896aU, 0xf48e7978U, 0x99583e6bU, 0x27b971ddU,
    0xbee14fb6U, 0xf088ad17U, 0xc920ac66U, 0x7dce3ab4U,
    0x63df4a18U, 0xe51a3182U, 0x97513360U, 0x62537f45U,
    0xb16477e0U, 0xbb6bae84U, 0xfe81a01cU, 0xf9082b94U,
    0x70486858U, 0x8f45fd19U, 0x94de6c87U, 0x527bf8b7U,
    0xab73d323U, 0x724b02e2U, 0xe31f8f57U, 0x6655ab2aU,
    0xb2eb2807U, 0x2fb5c203U, 0x86c57b9aU, 0xd33708a5U,
    0x302887f2U, 0x23bfa5b2U, 0x02036abaU, 0xed16825cU,
    0x8acf1c2bU, 0xa779b492U, 0xf307f2f0U, 0x4e69e2a1U,
    0x65daf4cdU, 0x0605bed5U, 0xd134621fU, 0xc4a6fe8aU,
    0x342e539dU, 0xa2f355a0U, 0x058ae132U, 0xa4f6eb75U,
    0x0b83ec39U, 0x4060efaaU, 0x5e719f06U, 0xbd6e1051U,
    0x3e218af9U, 0x96dd063dU, 0xdd3e05aeU, 0x4de6bd46U,
    0x91548db5U, 0x71c45d05U, 0x0406d46fU, 0x605015ffU,
    0x1998fb24U, 0xd6bde997U, 0x894043ccU, 0x67d99e77U,
    0xb0e842bdU, 0x07898b88U, 0xe7195b38U, 0x79c8eedbU,
    0xa17c0a47U, 0x7c420fe9U, 0xf8841ec9U, 0x00000000U,
    0x09808683U, 0x322bed48U, 0x1e1170acU, 0x6c5a724eU,
    0xfd0efffbU, 0x0f853856U, 0x3daed51eU, 0x362d3927U,
    0x0a0fd964U, 0x685ca621U, 0x9b5b54d1U, 0x24362e3aU,
    0x0c0a67b1U, 0x9357e70fU, 0xb4ee96d2U, 0x1b9b919eU,
    0x80c0c54fU, 0x61dc20a2U, 0x5a774b69U, 0x1c121a16U,
    0xe293ba0aU, 0xc0a02ae5U, 0x3c22e043U, 0x121b171dU,
    0x0e090d0bU, 0xf28bc7adU, 0x2db6a8b9U, 0x141ea9c8U,
    0x57f11985U, 0xaf75074cU, 0xee99ddbbU, 0xa37f60fdU,
    0xf701269fU, 0x5c72f5bcU, 0x44663bc5U, 0x5bfb7e34U,
    0x8b432976U, 0xcb23c6dcU, 0xb6edfc68U, 0xb8e4f163U,
    0xd731dccaU, 0x42638510U, 0x13972240U, 0x84c61120U,
    0x854a247dU, 0xd2bb3df8U, 0xaef93211U, 0xc729a16dU,
    0x1d9e2f4bU, 0xdcb230f3U, 0x0d8652ecU, 0x77c1e3d0U,
    0x2bb3166cU, 0xa970b999U, 0x119448faU, 0x47e96422U,
    0xa8fc8cc4U, 0xa0f03f1aU, 0x567d2cd8U, 0x223390efU,
    0x87494ec7U, 0xd938d1c1U, 0x8ccaa2feU, 0x98d40b36U,
    0xa6f581cfU, 0xa57ade28U, 0xdab78e26U, 0x3fadbfa4U,
    0x2c3a9de4U, 0x5078920dU, 0x6a5fcc9bU, 0x547e4662U,
    0xf68d13c2U, 0x90d8b8e8U, 0x2e39f75eU, 0x82c3aff5U,
    0x9f5d80beU, 0x69d0937cU, 0x6fd52da9U, 0xcf2512b3U,
    0xc8ac993bU, 0x10187da7U, 0xe89c636eU, 0xdb3bbb7bU,
    0xcd267809U, 0x6e5918f4U, 0xec9ab701U, 0x834f9aa8U,
    0xe6956e65U, 0xaaffe67eU, 0x21bccf08U, 0xef15e8e6U,
    0xbae79bd9U, 0x4a6f36ceU, 0xea9f09d4U, 0x29b07cd6U,
    0x31a4b2afU, 0x2a3f2331U, 0xc6a59430U, 0x35a266c0U,
    0x744ebc37U, 0xfc82caa6U, 0xe090d0b0U, 0x33a7d815U,
    0xf104984aU, 0x41ecdaf7U, 0x7fcd500eU, 0x1791f62fU,
    0x764dd68dU, 0x43efb04dU, 0xccaa4d54U, 0xe49604dfU,
    0x9ed1b5e3U, 0x4c6a881bU, 0xc12c1fb8U, 0x4665517fU,
    0x9d5eea04U, 0x018c355dU, 0xfa877473U, 0xfb0b412eU,
    0xb3671d5aU, 0x92dbd252U, 0xe9105633U, 0x6dd64713U,
    0x9ad7618cU, 0x37a10c7aU, 0x59f8148eU, 0xeb133c89U,
    0xcea927eeU, 0xb761c935U, 0xe11ce5edU, 0x7a47b13cU,
    0x9cd2df59U, 0x55f2733fU, 0x1814ce79U, 0x73c737bfU,
    0x53f7cdeaU, 0x5ffdaa5bU, 0xdf3d6f14U, 0x7844db86U,
    0xcaaff381U, 0xb968c43eU, 0x3824342cU, 0xc2a3405fU,
    0x161dc372U, 0xbce2250cU, 0x283c498bU, 0xff0d9541U,
    0x39a80171U, 0x080cb3deU, 0xd8b4e49cU, 0x6456c190U,
    0x7bcb8461U, 0xd532b670U, 0x486c5c74U, 0xd0b85742U,
},
{
    0x5051f4a7U, 0x537e4165U, 0xc31a17a4U, 0x963a275eU,
    0xcb3bab6bU, 0xf11f9d45U, 0xabacfa58U, 0x934be303U,
    0x552030faU, 0xf6ad766dU, 0x9188cc76U, 0x25f5024cU,
    0xfc4fe5d7U, 0xd7c52acbU, 0x80263544U, 0x8fb562a3U,
    0x49deb15aU, 0x6725ba1bU, 0x9845ea0eU, 0xe15dfec0U,
    0x02c32f75U, 0x12814cf0U, 0xa38d4697U, 0xc66bd3f9U,
    0xe7038f5fU, 0x9515929cU, 0xebbf6d7aU, 0xda955259U,
    0x2dd4be83U, 0xd3587421U, 0x2949e069U, 0x448ec9c8U,
    0x6a75c289U, 0x78f48e79U, 0x6b99583eU, 0xdd27b971U,
    0xb6bee14fU, 0x17f088adU, 0x66c920acU, 0xb47dce3aU,
    0x1863df4aU, 0x82e51a31U, 0x60975133U, 0x4562537fU,
    0xe0b16477U, 0x84bb6baeU, 0x1cfe81a0U, 0x94f9082bU,
    0x58704868U, 0x198f45fdU, 0x8794de6cU, 0xb7527bf8U,
    0x23ab73d3U, 0xe2724b02U, 0x57e31f8fU, 0x2a6655abU,
    0x07b2eb28U, 0x032fb5c2U, 0x9a86c57bU, 0xa5d33708U,
    0xf2302887U, 0xb223bfa5U, 0xba02036aU, 0x5ced1682U,
    0x2b8acf1cU, 0x92a779b4U, 0xf0f307f2U, 0xa14e69e2U,
    0xcd65daf4U, 0xd50605beU, 0x1fd13462U, 0x8ac4a6feU,
    0x9d342e53U, 0xa0a2f355U, 0x32058ae1U, 0x75a4f6ebU,
    0x390b83ecU, 0xaa4060efU, 0x065e719fU, 0x51bd6e10U,
    0xf93e218aU, 0x3d96dd06U, 0xaedd3e05U, 0x464de6bdU,
    0xb591548dU, 0x0571c45dU, 0x6f0406d4U, 0xff605015U,
    0x241998fbU, 0x97d6bde9U, 0xcc894043U, 0x7767d99eU,
    0xbdb0e842U, 0x8807898bU, 0x38e7195bU, 0xdb79c8eeU,
    0x47a17c0aU, 0xe97c420fU, 0xc9f8841eU, 0x00000000U,
    0x83098086U, 0x48322bedU, 0xac1e1170U, 0x4e6c5a72U,
    0xfbfd0effU, 0x560f8538U, 0x1e3daed5U, 0x27362d39U,
    0x640a0fd9U, 0x21685ca6U, 0xd19b5b54U, 0x3a24362eU,
    0xb10c0a67U, 0x0f9357e7U, 0xd2b4ee96U, 0x9e1b9b91U,
    0x4f80c0c5U, 0xa261dc20U, 0x695a774bU, 0x161c121aU,
    0x0ae293baU, 0xe5c0a02aU, 0x433c22e0U, 0x1d121b17U,
    0x0b0e090dU, 0xadf28bc7U, 0xb92db6a8U, 0xc8141ea9U,
    0x8557f119U, 0x4caf7507U, 0xbbee99ddU, 0xfda37f60U,
    0x9ff70126U, 0xbc5c72f5U, 0xc544663bU, 0x345bfb7eU,
    0x768b4329U, 0xdccb23c6U, 0x68b6edfcU, 0x63b8e4f1U,
    0xcad731dcU, 0x10426385U, 0x40139722U, 0x2084c611U,
    0x7d854a24U, 0xf8d2bb3dU, 0x11aef932U, 0x6dc729a1U,
    0x4b1d9e2fU, 0xf3dcb230U, 0xec0d8652U, 0xd077c1e3U,
    0x6c2bb316U, 0x99a970b9U, 0xfa119448U, 0x2247e964U,
    0xc4a8fc8cU, 0x1aa0f03fU, 0xd8567d2cU, 0xef223390U,
    0xc787494eU, 0xc1d938d1U, 0xfe8ccaa2U, 0x3698d40bU,
    0xcfa6f581U, 0x28a57adeU, 0x26dab78eU, 0xa43fadbfU,
    0xe42c3a9dU, 0x0d507892U, 0x9b6a5fccU, 0x62547e46U,
    0xc2f68d13U, 0xe890d8b8U, 0x5e2e39f7U, 0xf582c3afU,
    0xbe9f5d80U, 0x7c69d093U, 0xa96fd52dU, 0xb3cf2512U,
    0x3bc8ac99U, 0xa710187dU, 0x6ee89c63U, 0x7bdb3bbbU,
    0x09cd2678U, 0xf46e5918U, 0x01ec9ab7U, 0xa8834f9aU,
    0x65e6956eU, 0x7eaaffe6U, 0x0821bccfU, 0xe6ef15e8U,
    0xd9bae79bU, 0xce4a6f36U, 0xd4ea9f09U, 0xd629b07cU,
    0xaf31a4b2U, 0x312a3f23U, 0x30c6a594U, 0xc035a266U,
    0x37744ebcU, 0xa6fc82caU, 0xb0e090d0U, 0x1533a7d8U,
    0x4af10498U, 0xf741ecdaU, 0x0e7fcd50U, 0x2f1791f6U,
    0x8d764dd6U, 0x4d43efb0U, 0x54ccaa4dU, 0xdfe49604U,
    0xe39ed1b5U, 0x1b4c6a88U, 0xb8c12c1fU, 0x7f466551U,
    0x049d5eeaU, 0x5d018c35U, 0x73fa8774U, 0x2efb0b41U,
    0x5ab3671dU, 0x5292dbd2U, 0x33e91056U, 0x136dd647U,
    0x8c9ad761U, 0x7a37a10cU, 0x8e59f814U, 0x89eb133cU,
    0xeecea927U, 0x35b761c9U, 0xede11ce5U, 0x3c7a47b1U,
    0x599cd2dfU, 0x3f55f273U, 0x791814ceU, 0xbf73c737U,
    0xea53f7cdU, 0x5b5ffdaaU, 0x14df3d6fU, 0x867844dbU,
    0x81caaff3U, 0x3eb968c4U, 0x2c382434U, 0x5fc2a340U,
    0x72161dc3U, 0x0cbce225U, 0x8b283c49U, 0x41ff0d95U,
    0x7139a801U, 0xde080cb3U, 0x9cd8b4e4U, 0x906456c1U,
    0x617bcb84U, 0x70d532b6U, 0x74486c5cU, 0x42d0b857U,
},
{
    0xa75051f4U, 0x65537e41U, 0xa4c31a17U, 0x5e963a27U,
    0x6bcb3babU, 0x45f11f9dU, 0x58abacfaU, 0x03934be3U,
    0xfa552030U, 0x6df6ad76U, 0x769188ccU, 0x4c25f502U,
    0xd7fc4fe5U, 0xcbd7c52aU, 0x44802635U, 0xa38fb562U,
    0x5a49deb1U, 0x1b6725baU, 0x0e9845eaU, 0xc0e15dfeU,
    0x7502c32fU, 0xf012814cU, 0x97a38d46U, 0xf9c66bd3U,
    0x5fe7038fU, 0x9c951592U, 0x7aebbf6dU, 0x59da9552U,
    0x832dd4beU, 0x21d35874U, 0x692949e0U, 0xc8448ec9U,
    0x896a75c2U, 0x7978f48eU, 0x3e6b9958U, 0x71dd27b9U,
    0x4fb6bee1U, 0xad17f088U, 0xac66c920U, 0x3ab47dceU,
    0x4a1863dfU, 0x3182e51aU, 0x33609751U, 0x7f456253U,
    0x77e0b164U, 0xae84bb6bU, 0xa01cfe81U, 0x2b94f908U,
    0x68587048U, 0xfd198f45U, 0x6c8794deU, 0xf8b7527bU,
    0xd323ab73U, 0x02e2724bU, 0x8f57e31fU, 0xab2a6655U,
    0x2807b2ebU, 0xc2032fb5U, 0x7b9a86c5U, 0x08a5d337U,
    0x87f23028U, 0xa5b223bfU, 0x6aba0203U, 0x825ced16U,
    0x1c2b8acfU, 0xb492a779U, 0xf2f0f307U, 0xe2a14e69U,
    0xf4cd65daU, 0xbed50605U, 0x621fd134U, 0xfe8ac4a6U,
    0x539d342eU, 0x55a0a2f3U, 0xe132058aU, 0xeb75a4f6U,
    0xec390b83U, 0xefaa4060U, 0x9f065e71U, 0x1051bd6eU,

    0x8af93e21U, 0x063d96ddU, 0x05aedd3eU, 0xbd464de6U,
    0x8db59154U, 0x5d0571c4U, 0xd46f0406U, 0x15ff6050U,
    0xfb241998U, 0xe997d6bdU, 0x43cc8940U, 0x9e7767d9U,
    0x42bdb0e8U, 0x8b880789U, 0x5b38e719U, 0xeedb79c8U,
    0x0a47a17cU, 0x0fe97c42U, 0x1ec9f884U, 0x00000000U,
    0x86830980U, 0xed48322bU, 0x70ac1e11U, 0x724e6c5aU,
    0xfffbfd0eU, 0x38560f85U, 0xd51e3daeU, 0x3927362dU,
    0xd9640a0fU, 0xa621685cU, 0x54d19b5bU, 0x2e3a2436U,
    0x67b10c0aU, 0xe70f9357U, 0x96d2b4eeU, 0x919e1b9bU,
    0xc54f80c0U, 0x20a261dcU, 0x4b695a77U, 0x1a161c12U,
    0xba0ae293U, 0x2ae5c0a0U, 0xe0433c22U, 0x171d121bU,
    0x0d0b0e09U, 0xc7adf28bU, 0xa8b92db6U, 0xa9c8141eU,
    0x198557f1U, 0x074caf75U, 0xddbbee99U, 0x60fda37fU,
    0x269ff701U, 0xf5bc5c72U, 0x3bc54466U, 0x7e345bfbU,
    0x29768b43U, 0xc6dccb23U, 0xfc68b6edU, 0xf163b8e4U,
    0xdccad731U, 0x85104263U, 0x22401397U, 0x112084c6U,
    0x247d854aU, 0x3df8d2bbU, 0x3211aef9U, 0xa16dc729U,
    0x2f4b1d9eU, 0x30f3dcb2U, 0x52ec0d86U, 0xe3d077c1U,
    0x166c2bb3U, 0xb999a970U, 0x48fa1194U, 0x642247e9U,
    0x8cc4a8fcU, 0x3f1aa0f0U, 0x2cd8567dU, 0x90ef2233U,
    0x4ec78749U, 0xd1c1d938U, 0xa2fe8ccaU, 0x0b3698d4U,
    0x81cfa6f5U, 0xde28a57aU, 0x8e26dab7U, 0xbfa43fadU,
    0x9de42c3aU, 0x920d5078U, 0xcc9b6a5fU, 0x4662547eU,
    0x13c2f68dU, 0xb8e890d8U, 0xf75e2e39U, 0xaff582c3U,
    0x80be9f5dU, 0x937c69d0U, 0x2da96fd5U, 0x12b3cf25U,
    0x993bc8acU, 0x7da71018U, 0x636ee89cU, 0xbb7bdb3bU,
    0x7809cd26U, 0x18f46e59U, 0xb701ec9aU, 0x9aa8834fU,
    0x6e65e695U, 0xe67eaaffU, 0xcf0821bcU, 0xe8e6ef15U,
    0x9bd9bae7U, 0x36ce4a6fU, 0x09d4ea9fU, 0x7cd629b0U,
    0xb2af31a4U, 0x23312a3fU, 0x9430c6a5U, 0x66c035a2U,
    0xbc37744eU, 0xcaa6fc82U, 0xd0b0e090U, 0xd81533a7U,
    0x984af104U, 0xdaf741ecU, 0x500e7fcdU, 0xf62f1791U,
    0xd68d764dU, 0xb04d43efU, 0x4d54ccaaU, 0x04dfe496U,
    0xb5e39ed1U, 0x881b4c6aU, 0x1fb8c12cU, 0x517f4665U,
    0xea049d5eU, 0x355d018cU, 0x7473fa87U, 0x412efb0bU,
    0x1d5ab367U, 0xd25292dbU, 0x5633e910U, 0x47136dd6U,
    0x618c9ad7U, 0x0c7a37a1U, 0x148e59f8U, 0x3c89eb13U,
    0x27eecea9U, 0xc935b761U, 0xe5ede11cU, 0xb13c7a47U,
    0xdf599cd2U, 0x733f55f2U, 0xce791814U, 0x37bf73c7U,
    0xcdea53f7U, 0xaa5b5ffdU, 0x6f14df3dU, 0xdb867844U,
    0xf381caafU, 0xc43eb968U, 0x342c3824U, 0x405fc2a3U,
    0xc372161dU, 0x250cbce2U, 0x498b283cU, 0x9541ff0dU,
    0x017139a8U, 0xb3de080cU, 0xe49cd8b4U, 0xc1906456U,
    0x84617bcbU, 0xb670d532U, 0x5c74486cU, 0x5742d0b8U,
},
{
    0xf4a75051U, 0x4165537eU, 0x17a4c31aU, 0x275e963aU,
    0xab6bcb3bU, 0x9d45f11fU, 0xfa58abacU, 0xe303934bU,
    0x30fa5520U, 0x766df6adU, 0xcc769188U, 0x024c25f5U,
    0xe5d7fc4fU, 0x2acbd7c5U, 0x35448026U, 0x62a38fb5U,
    0xb15a49deU, 0xba1b6725U, 0xea0e9845U, 0xfec0e15dU,
    0x2f7502c3U, 0x4cf01281U, 0x4697a38dU, 0xd3f9c66bU,
    0x8f5fe703U, 0x929c9515U, 0x6d7aebbfU, 0x5259da95U,
    0xbe832dd4U, 0x7421d358U, 0xe0692949U, 0xc9c8448eU,
    0xc2896a75U, 0x8e7978f4U, 0x583e6b99U, 0xb971dd27U,
    0xe14fb6beU, 0x88ad17f0U, 0x20ac66c9U, 0xce3ab47dU,
    0xdf4a1863U, 0x1a3182e5U, 0x51336097U, 0x537f4562U,
    0x6477e0b1U, 0x6bae84bbU, 0x81a01cfeU, 0x082b94f9U,
    0x48685870U, 0x45fd198fU, 0xde6c8794U, 0x7bf8b752U,
    0x73d323abU, 0x4b02e272U, 0x1f8f57e3U, 0x55ab2a66U,
    0xeb2807b2U, 0xb5c2032fU, 0xc57b9a86U, 0x3708a5d3U,
    0x2887f230U, 0xbfa5b223U, 0x036aba02U, 0x16825cedU,
    0xcf1c2b8aU, 0x79b492a7U, 0x07f2f0f3U, 0x69e2a14eU,
    0xdaf4cd65U, 0x05bed506U, 0x34621fd1U, 0xa6fe8ac4U,
    0x2e539d34U, 0xf355a0a2U, 0x8ae13205U, 0xf6eb75a4U,
    0x83ec390bU, 0x60efaa40U, 0x719f065eU, 0x6e1051bdU,
    0x218af93eU, 0xdd063d96U, 0x3e05aeddU, 0xe6bd464dU,
    0x548db591U, 0xc45d0571U, 0x06d46f04U, 0x5015ff60U,
    0x98fb2419U, 0xbde997d6U, 0x4043cc89U, 0xd99e7767U,
    0xe842bdb0U, 0x898b8807U, 0x195b38e7U, 0xc8eedb79U,
    0x7c0a47a1U, 0x420fe97cU, 0x841ec9f8U, 0x00000000U,
    0x80868309U, 0x2bed4832U, 0x1170ac1eU, 0x5a724e6cU,
    0x0efffbfdU, 0x8538560fU, 0xaed51e3dU, 0x2d392736U,
    0x0fd9640aU, 0x5ca62168U, 0x5b54d19bU, 0x362e3a24U,
    0x0a67b10cU, 0x57e70f93U, 0xee96d2b4U, 0x9b919e1bU,
    0xc0c54f80U, 0xdc20a261U, 0x774b695aU, 0x121a161cU,
    0x93ba0ae2U, 0xa02ae5c0U, 0x22e0433cU, 0x1b171d12U,
    0x090d0b0eU, 0x8bc7adf2U, 0xb6a8b92dU, 0x1ea9c814U,
    0xf1198557U, 0x75074cafU, 0x99ddbbeeU, 0x7f60fda3U,
    0x01269ff7U, 0x72f5bc5cU, 0x663bc544U, 0xfb7e345bU,
    0x4329768bU, 0x23c6dccbU, 0xedfc68b6U, 0xe4f163b8U,
    0x31dccad7U, 0x63851042U, 0x97224013U, 0xc6112084U,
    0x4a247d85U, 0xbb3df8d2U, 0xf93211aeU, 0x29a16dc7U,
    0x9e2f4b1dU, 0xb230f3dcU, 0x8652ec0dU, 0xc1e3d077U,
    0xb3166c2bU, 0x70b999a9U, 0x9448fa11U, 0xe9642247U,
    0xfc8cc4a8U, 0xf03f1aa0U, 0x7d2cd856U, 0x3390ef22U,
    0x494ec787U, 0x38d1c1d9U, 0xcaa2fe8cU, 0xd40b3698U,
    0xf581cfa6U, 0x7ade28a5U, 0xb78e26daU, 0xadbfa43fU,
    0x3a9de42cU, 0x78920d50U, 0x5fcc9b6aU, 0x7e466254U,
    0x8d13c2f6U, 0xd8b8e890U, 0x39f75e2eU, 0xc3aff582U,
    0x5d80be9fU, 0xd0937c69U, 0xd52da96fU, 0x2512b3cfU,
    0xac993bc8U, 0x187da710U, 0x9c636ee8U, 0x3bbb7bdbU,
    0x267809cdU, 0x5918f46eU, 0x9ab701ecU, 0x4f9aa883U,
    0x956e65e6U, 0xffe67eaaU, 0xbccf0821U, 0x15e8e6efU,
    0xe79bd9baU, 0x6f36ce4aU, 0x9f09d4eaU, 0xb07cd629U,
    0xa4b2af31U, 0x3f23312aU, 0xa59430c6U, 0xa266c035U,
    0x4ebc3774U, 0x82caa6fcU, 0x90d0b0e0U, 0xa7d81533U,
    0x04984af1U, 0xecdaf741U, 0xcd500e7fU, 0x91f62f17U,
    0x4dd68d76U, 0xefb04d43U, 0xaa4d54ccU, 0x9604dfe4U,
    0xd1b5e39eU, 0x6a881b4cU, 0x2c1fb8c1U, 0x65517f46U,
    0x5eea049dU, 0x8c355d01U, 0x877473faU, 0x0b412efbU,
    0x671d5ab3U, 0xdbd25292U, 0x105633e9U, 0xd647136dU,
    0xd7618c9aU, 0xa10c7a37U, 0xf8148e59U, 0x133c89ebU,
    0xa927eeceU, 0x61c935b7U, 0x1ce5ede1U, 0x47b13c7aU,
    0xd2df599cU, 0xf2733f55U, 0x14ce7918U, 0xc737bf73U,
    0xf7cdea53U, 0xfdaa5b5fU, 0x3d6f14dfU, 0x44db8678U,
    0xaff381caU, 0x68c43eb9U, 0x24342c38U, 0xa3405fc2U,
    0x1dc37216U, 0xe2250cbcU, 0x3c498b28U, 0x0d9541ffU,
    0xa8017139U, 0x0cb3de08U, 0xb4e49cd8U, 0x56c19064U,
    0xcb84617bU, 0x32b670d5U, 0x6c5c7448U, 0xb85742d0U,
}
};
#endif /* HAVE_AES_DECRYPT */
#endif

#ifdef HAVE_AES_DECRYPT
#if (defined(HAVE_AES_CBC) && !defined(WOLFSSL_DEVCRYPTO_CBC)) \
            || defined(WOLFSSL_AES_DIRECT)
static const FLASH_QUALIFIER byte Td4[256] =
{
    0x52U, 0x09U, 0x6aU, 0xd5U, 0x30U, 0x36U, 0xa5U, 0x38U,
    0xbfU, 0x40U, 0xa3U, 0x9eU, 0x81U, 0xf3U, 0xd7U, 0xfbU,
    0x7cU, 0xe3U, 0x39U, 0x82U, 0x9bU, 0x2fU, 0xffU, 0x87U,
    0x34U, 0x8eU, 0x43U, 0x44U, 0xc4U, 0xdeU, 0xe9U, 0xcbU,
    0x54U, 0x7bU, 0x94U, 0x32U, 0xa6U, 0xc2U, 0x23U, 0x3dU,
    0xeeU, 0x4cU, 0x95U, 0x0bU, 0x42U, 0xfaU, 0xc3U, 0x4eU,
    0x08U, 0x2eU, 0xa1U, 0x66U, 0x28U, 0xd9U, 0x24U, 0xb2U,
    0x76U, 0x5bU, 0xa2U, 0x49U, 0x6dU, 0x8bU, 0xd1U, 0x25U,
    0x72U, 0xf8U, 0xf6U, 0x64U, 0x86U, 0x68U, 0x98U, 0x16U,
    0xd4U, 0xa4U, 0x5cU, 0xccU, 0x5dU, 0x65U, 0xb6U, 0x92U,
    0x6cU, 0x70U, 0x48U, 0x50U, 0xfdU, 0xedU, 0xb9U, 0xdaU,
    0x5eU, 0x15U, 0x46U, 0x57U, 0xa7U, 0x8dU, 0x9dU, 0x84U,
    0x90U, 0xd8U, 0xabU, 0x00U, 0x8cU, 0xbcU, 0xd3U, 0x0aU,
    0xf7U, 0xe4U, 0x58U, 0x05U, 0xb8U, 0xb3U, 0x45U, 0x06U,
    0xd0U, 0x2cU, 0x1eU, 0x8fU, 0xcaU, 0x3fU, 0x0fU, 0x02U,
    0xc1U, 0xafU, 0xbdU, 0x03U, 0x01U, 0x13U, 0x8aU, 0x6bU,
    0x3aU, 0x91U, 0x11U, 0x41U, 0x4fU, 0x67U, 0xdcU, 0xeaU,
    0x97U, 0xf2U, 0xcfU, 0xceU, 0xf0U, 0xb4U, 0xe6U, 0x73U,
    0x96U, 0xacU, 0x74U, 0x22U, 0xe7U, 0xadU, 0x35U, 0x85U,
    0xe2U, 0xf9U, 0x37U, 0xe8U, 0x1cU, 0x75U, 0xdfU, 0x6eU,
    0x47U, 0xf1U, 0x1aU, 0x71U, 0x1dU, 0x29U, 0xc5U, 0x89U,
    0x6fU, 0xb7U, 0x62U, 0x0eU, 0xaaU, 0x18U, 0xbeU, 0x1bU,
    0xfcU, 0x56U, 0x3eU, 0x4bU, 0xc6U, 0xd2U, 0x79U, 0x20U,
    0x9aU, 0xdbU, 0xc0U, 0xfeU, 0x78U, 0xcdU, 0x5aU, 0xf4U,
    0x1fU, 0xddU, 0xa8U, 0x33U, 0x88U, 0x07U, 0xc7U, 0x31U,
    0xb1U, 0x12U, 0x10U, 0x59U, 0x27U, 0x80U, 0xecU, 0x5fU,
    0x60U, 0x51U, 0x7fU, 0xa9U, 0x19U, 0xb5U, 0x4aU, 0x0dU,
    0x2dU, 0xe5U, 0x7aU, 0x9fU, 0x93U, 0xc9U, 0x9cU, 0xefU,
    0xa0U, 0xe0U, 0x3bU, 0x4dU, 0xaeU, 0x2aU, 0xf5U, 0xb0U,
    0xc8U, 0xebU, 0xbbU, 0x3cU, 0x83U, 0x53U, 0x99U, 0x61U,
    0x17U, 0x2bU, 0x04U, 0x7eU, 0xbaU, 0x77U, 0xd6U, 0x26U,
    0xe1U, 0x69U, 0x14U, 0x63U, 0x55U, 0x21U, 0x0cU, 0x7dU,
};
#endif /* HAVE_AES_CBC || WOLFSSL_AES_DIRECT */
#endif /* HAVE_AES_DECRYPT */

#define GETBYTE(x, y) (word32)((byte)((x) >> (8 * (y))))

#ifdef WOLFSSL_AES_SMALL_TABLES
static const byte Tsbox[256] = {
    0x63U, 0x7cU, 0x77U, 0x7bU, 0xf2U, 0x6bU, 0x6fU, 0xc5U,
    0x30U, 0x01U, 0x67U, 0x2bU, 0xfeU, 0xd7U, 0xabU, 0x76U,
    0xcaU, 0x82U, 0xc9U, 0x7dU, 0xfaU, 0x59U, 0x47U, 0xf0U,
    0xadU, 0xd4U, 0xa2U, 0xafU, 0x9cU, 0xa4U, 0x72U, 0xc0U,
    0xb7U, 0xfdU, 0x93U, 0x26U, 0x36U, 0x3fU, 0xf7U, 0xccU,
    0x34U, 0xa5U, 0xe5U, 0xf1U, 0x71U, 0xd8U, 0x31U, 0x15U,
    0x04U, 0xc7U, 0x23U, 0xc3U, 0x18U, 0x96U, 0x05U, 0x9aU,
    0x07U, 0x12U, 0x80U, 0xe2U, 0xebU, 0x27U, 0xb2U, 0x75U,
    0x09U, 0x83U, 0x2cU, 0x1aU, 0x1bU, 0x6eU, 0x5aU, 0xa0U,
    0x52U, 0x3bU, 0xd6U, 0xb3U, 0x29U, 0xe3U, 0x2fU, 0x84U,
    0x53U, 0xd1U, 0x00U, 0xedU, 0x20U, 0xfcU, 0xb1U, 0x5bU,
    0x6aU, 0xcbU, 0xbeU, 0x39U, 0x4aU, 0x4cU, 0x58U, 0xcfU,
    0xd0U, 0xefU, 0xaaU, 0xfbU, 0x43U, 0x4dU, 0x33U, 0x85U,
    0x45U, 0xf9U, 0x02U, 0x7fU, 0x50U, 0x3cU, 0x9fU, 0xa8U,
    0x51U, 0xa3U, 0x40U, 0x8fU, 0x92U, 0x9dU, 0x38U, 0xf5U,
    0xbcU, 0xb6U, 0xdaU, 0x21U, 0x10U, 0xffU, 0xf3U, 0xd2U,
    0xcdU, 0x0cU, 0x13U, 0xecU, 0x5fU, 0x97U, 0x44U, 0x17U,
    0xc4U, 0xa7U, 0x7eU, 0x3dU, 0x64U, 0x5dU, 0x19U, 0x73U,
    0x60U, 0x81U, 0x4fU, 0xdcU, 0x22U, 0x2aU, 0x90U, 0x88U,
    0x46U, 0xeeU, 0xb8U, 0x14U, 0xdeU, 0x5eU, 0x0bU, 0xdbU,
    0xe0U, 0x32U, 0x3aU, 0x0aU, 0x49U, 0x06U, 0x24U, 0x5cU,
    0xc2U, 0xd3U, 0xacU, 0x62U, 0x91U, 0x95U, 0xe4U, 0x79U,
    0xe7U, 0xc8U, 0x37U, 0x6dU, 0x8dU, 0xd5U, 0x4eU, 0xa9U,
    0x6cU, 0x56U, 0xf4U, 0xeaU, 0x65U, 0x7aU, 0xaeU, 0x08U,
    0xbaU, 0x78U, 0x25U, 0x2eU, 0x1cU, 0xa6U, 0xb4U, 0xc6U,
    0xe8U, 0xddU, 0x74U, 0x1fU, 0x4bU, 0xbdU, 0x8bU, 0x8aU,
    0x70U, 0x3eU, 0xb5U, 0x66U, 0x48U, 0x03U, 0xf6U, 0x0eU,
    0x61U, 0x35U, 0x57U, 0xb9U, 0x86U, 0xc1U, 0x1dU, 0x9eU,
    0xe1U, 0xf8U, 0x98U, 0x11U, 0x69U, 0xd9U, 0x8eU, 0x94U,
    0x9bU, 0x1eU, 0x87U, 0xe9U, 0xceU, 0x55U, 0x28U, 0xdfU,
    0x8cU, 0xa1U, 0x89U, 0x0dU, 0xbfU, 0xe6U, 0x42U, 0x68U,
    0x41U, 0x99U, 0x2dU, 0x0fU, 0xb0U, 0x54U, 0xbbU, 0x16U
};

#define AES_XTIME(x)    ((byte)((byte)((x) << 1) ^ ((0 - ((x) >> 7)) & 0x1b)))

static word32 col_mul(word32 t, int i2, int i3, int ia, int ib)
{
    byte t3 = GETBYTE(t, i3);
    byte tm = AES_XTIME(GETBYTE(t, i2) ^ t3);

    return GETBYTE(t, ia) ^ GETBYTE(t, ib) ^ t3 ^ tm;
}

#if defined(HAVE_AES_CBC) || defined(WOLFSSL_AES_DIRECT)
static word32 inv_col_mul(word32 t, int i9, int ib, int id, int ie)
{
    byte t9 = GETBYTE(t, i9);
    byte tb = GETBYTE(t, ib);
    byte td = GETBYTE(t, id);
    byte te = GETBYTE(t, ie);
    byte t0 = t9 ^ tb ^ td;
    return t0 ^ AES_XTIME(AES_XTIME(AES_XTIME(t0 ^ te) ^ td ^ te) ^ tb ^ te);
}
#endif
#endif

#if defined(HAVE_AES_CBC) || defined(WOLFSSL_AES_DIRECT) || \
                                    defined(HAVE_AESCCM) || defined(HAVE_AESGCM)

#ifndef WC_CACHE_LINE_SZ
    #if defined(__x86_64__) || defined(_M_X64) || \
       (defined(__ILP32__) && (__ILP32__ >= 1))
        #define WC_CACHE_LINE_SZ 64
    #else
        /* default cache line size */
        #define WC_CACHE_LINE_SZ 32
    #endif
#endif


#ifndef WOLFSSL_AES_SMALL_TABLES
/* load 4 Te Tables into cache by cache line stride */
static WC_INLINE word32 PreFetchTe(void)
{
    word32 x = 0;
    int i,j;

    for (i = 0; i < 4; i++) {
        /* 256 elements, each one is 4 bytes */
        for (j = 0; j < 256; j += WC_CACHE_LINE_SZ/4) {
            x &= Te[i][j];
        }
    }
    return x;
}
#else
/* load sbox into cache by cache line stride */
static WC_INLINE word32 PreFetchSBox(void)
{
    word32 x = 0;
    int i;

    for (i = 0; i < 256; i += WC_CACHE_LINE_SZ/4) {
        x &= Tsbox[i];
    }
    return x;
}
#endif

/* Software AES - ECB Encrypt */
static void wc_AesEncrypt(Aes* aes, const byte* inBlock, byte* outBlock)
{
    word32 s0, s1, s2, s3;
    word32 t0, t1, t2, t3;
    word32 r = aes->rounds >> 1;
    const word32* rk = aes->key;

    if (r > 7 || r == 0) {
        WOLFSSL_MSG("AesEncrypt encountered improper key, set it up");
        return;  /* stop instead of seg-faulting, set up your keys! */
    }

#ifdef WOLFSSL_AESNI
    if (haveAESNI && aes->use_aesni) {
        #ifdef DEBUG_AESNI
            printf("about to aes encrypt\n");
            printf("in  = %p\n", inBlock);
            printf("out = %p\n", outBlock);
            printf("aes->key = %p\n", aes->key);
            printf("aes->rounds = %d\n", aes->rounds);
            printf("sz = %d\n", AES_BLOCK_SIZE);
        #endif

        /* check alignment, decrypt doesn't need alignment */
        if ((wolfssl_word)inBlock % AESNI_ALIGN) {
        #ifndef NO_WOLFSSL_ALLOC_ALIGN
            byte* tmp = (byte*)XMALLOC(AES_BLOCK_SIZE + AESNI_ALIGN, aes->heap,
                                                      DYNAMIC_TYPE_TMP_BUFFER);
            byte* tmp_align;
            if (tmp == NULL) return;

            tmp_align = tmp + (AESNI_ALIGN - ((size_t)tmp % AESNI_ALIGN));

            XMEMCPY(tmp_align, inBlock, AES_BLOCK_SIZE);
            AES_ECB_encrypt(tmp_align, tmp_align, AES_BLOCK_SIZE,
                    (byte*)aes->key, aes->rounds);
            XMEMCPY(outBlock, tmp_align, AES_BLOCK_SIZE);
            XFREE(tmp, aes->heap, DYNAMIC_TYPE_TMP_BUFFER);
            return;
        #else
            WOLFSSL_MSG("AES-ECB encrypt with bad alignment");
            return;
        #endif
        }

        AES_ECB_encrypt(inBlock, outBlock, AES_BLOCK_SIZE, (byte*)aes->key,
                        aes->rounds);

        return;
    }
    else {
        #ifdef DEBUG_AESNI
            printf("Skipping AES-NI\n");
        #endif
    }
#endif
#if defined(WOLFSSL_SCE) && !defined(WOLFSSL_SCE_NO_AES)
    AES_ECB_encrypt(aes, inBlock, outBlock, AES_BLOCK_SIZE);
    return;
#endif

    /*
     * map byte array block to cipher state
     * and add initial round key:
     */
    XMEMCPY(&s0, inBlock,                  sizeof(s0));
    XMEMCPY(&s1, inBlock + sizeof(s0),     sizeof(s1));
    XMEMCPY(&s2, inBlock + 2 * sizeof(s0), sizeof(s2));
    XMEMCPY(&s3, inBlock + 3 * sizeof(s0), sizeof(s3));

#ifdef LITTLE_ENDIAN_ORDER
    s0 = ByteReverseWord32(s0);
    s1 = ByteReverseWord32(s1);
    s2 = ByteReverseWord32(s2);
    s3 = ByteReverseWord32(s3);
#endif

    /* AddRoundKey */
    s0 ^= rk[0];
    s1 ^= rk[1];
    s2 ^= rk[2];
    s3 ^= rk[3];

#ifndef WOLFSSL_AES_SMALL_TABLES
    s0 |= PreFetchTe();

    /*
     * Nr - 1 full rounds:
     */

    for (;;) {
        t0 =
            Te[0][GETBYTE(s0, 3)] ^
            Te[1][GETBYTE(s1, 2)] ^
            Te[2][GETBYTE(s2, 1)] ^
            Te[3][GETBYTE(s3, 0)] ^
            rk[4];
        t1 =
            Te[0][GETBYTE(s1, 3)] ^
            Te[1][GETBYTE(s2, 2)] ^
            Te[2][GETBYTE(s3, 1)] ^
            Te[3][GETBYTE(s0, 0)] ^
            rk[5];
        t2 =
            Te[0][GETBYTE(s2, 3)] ^
            Te[1][GETBYTE(s3, 2)] ^
            Te[2][GETBYTE(s0, 1)] ^
            Te[3][GETBYTE(s1, 0)] ^
            rk[6];
        t3 =
            Te[0][GETBYTE(s3, 3)] ^
            Te[1][GETBYTE(s0, 2)] ^
            Te[2][GETBYTE(s1, 1)] ^
            Te[3][GETBYTE(s2, 0)] ^
            rk[7];

        rk += 8;
        if (--r == 0) {
            break;
        }

        s0 =
            Te[0][GETBYTE(t0, 3)] ^
            Te[1][GETBYTE(t1, 2)] ^
            Te[2][GETBYTE(t2, 1)] ^
            Te[3][GETBYTE(t3, 0)] ^
            rk[0];
        s1 =
            Te[0][GETBYTE(t1, 3)] ^
            Te[1][GETBYTE(t2, 2)] ^
            Te[2][GETBYTE(t3, 1)] ^
            Te[3][GETBYTE(t0, 0)] ^
            rk[1];
        s2 =
            Te[0][GETBYTE(t2, 3)] ^
            Te[1][GETBYTE(t3, 2)] ^
            Te[2][GETBYTE(t0, 1)] ^
            Te[3][GETBYTE(t1, 0)] ^
            rk[2];
        s3 =
            Te[0][GETBYTE(t3, 3)] ^
            Te[1][GETBYTE(t0, 2)] ^
            Te[2][GETBYTE(t1, 1)] ^
            Te[3][GETBYTE(t2, 0)] ^
            rk[3];
    }

    /*
     * apply last round and
     * map cipher state to byte array block:
     */

    s0 =
        (Te[2][GETBYTE(t0, 3)] & 0xff000000) ^
        (Te[3][GETBYTE(t1, 2)] & 0x00ff0000) ^
        (Te[0][GETBYTE(t2, 1)] & 0x0000ff00) ^
        (Te[1][GETBYTE(t3, 0)] & 0x000000ff) ^
        rk[0];
    s1 =
        (Te[2][GETBYTE(t1, 3)] & 0xff000000) ^
        (Te[3][GETBYTE(t2, 2)] & 0x00ff0000) ^
        (Te[0][GETBYTE(t3, 1)] & 0x0000ff00) ^
        (Te[1][GETBYTE(t0, 0)] & 0x000000ff) ^
        rk[1];
    s2 =
        (Te[2][GETBYTE(t2, 3)] & 0xff000000) ^
        (Te[3][GETBYTE(t3, 2)] & 0x00ff0000) ^
        (Te[0][GETBYTE(t0, 1)] & 0x0000ff00) ^
        (Te[1][GETBYTE(t1, 0)] & 0x000000ff) ^
        rk[2];
    s3 =
        (Te[2][GETBYTE(t3, 3)] & 0xff000000) ^
        (Te[3][GETBYTE(t0, 2)] & 0x00ff0000) ^
        (Te[0][GETBYTE(t1, 1)] & 0x0000ff00) ^
        (Te[1][GETBYTE(t2, 0)] & 0x000000ff) ^
        rk[3];
#else
    s0 |= PreFetchSBox();

    r *= 2;
    /* Two rounds at a time */
    for (rk += 4; r > 1; r--, rk += 4) {
        t0 =
            ((word32)Tsbox[GETBYTE(s0, 3)] << 24) ^
            ((word32)Tsbox[GETBYTE(s1, 2)] << 16) ^
            ((word32)Tsbox[GETBYTE(s2, 1)] <<  8) ^
            ((word32)Tsbox[GETBYTE(s3, 0)]);
        t1 =
            ((word32)Tsbox[GETBYTE(s1, 3)] << 24) ^
            ((word32)Tsbox[GETBYTE(s2, 2)] << 16) ^
            ((word32)Tsbox[GETBYTE(s3, 1)] <<  8) ^
            ((word32)Tsbox[GETBYTE(s0, 0)]);
        t2 =
            ((word32)Tsbox[GETBYTE(s2, 3)] << 24) ^
            ((word32)Tsbox[GETBYTE(s3, 2)] << 16) ^
            ((word32)Tsbox[GETBYTE(s0, 1)] <<  8) ^
            ((word32)Tsbox[GETBYTE(s1, 0)]);
        t3 =
            ((word32)Tsbox[GETBYTE(s3, 3)] << 24) ^
            ((word32)Tsbox[GETBYTE(s0, 2)] << 16) ^
            ((word32)Tsbox[GETBYTE(s1, 1)] <<  8) ^
            ((word32)Tsbox[GETBYTE(s2, 0)]);

        s0 =
            (col_mul(t0, 3, 2, 0, 1) << 24) ^
            (col_mul(t0, 2, 1, 0, 3) << 16) ^
            (col_mul(t0, 1, 0, 2, 3) <<  8) ^
            (col_mul(t0, 0, 3, 2, 1)      ) ^
            rk[0];
        s1 =
            (col_mul(t1, 3, 2, 0, 1) << 24) ^
            (col_mul(t1, 2, 1, 0, 3) << 16) ^
            (col_mul(t1, 1, 0, 2, 3) <<  8) ^
            (col_mul(t1, 0, 3, 2, 1)      ) ^
            rk[1];
        s2 =
            (col_mul(t2, 3, 2, 0, 1) << 24) ^
            (col_mul(t2, 2, 1, 0, 3) << 16) ^
            (col_mul(t2, 1, 0, 2, 3) <<  8) ^
            (col_mul(t2, 0, 3, 2, 1)      ) ^
            rk[2];
        s3 =
            (col_mul(t3, 3, 2, 0, 1) << 24) ^
            (col_mul(t3, 2, 1, 0, 3) << 16) ^
            (col_mul(t3, 1, 0, 2, 3) <<  8) ^
            (col_mul(t3, 0, 3, 2, 1)      ) ^
            rk[3];
    }

    t0 =
        ((word32)Tsbox[GETBYTE(s0, 3)] << 24) ^
        ((word32)Tsbox[GETBYTE(s1, 2)] << 16) ^
        ((word32)Tsbox[GETBYTE(s2, 1)] <<  8) ^
        ((word32)Tsbox[GETBYTE(s3, 0)]);
    t1 =
        ((word32)Tsbox[GETBYTE(s1, 3)] << 24) ^
        ((word32)Tsbox[GETBYTE(s2, 2)] << 16) ^
        ((word32)Tsbox[GETBYTE(s3, 1)] <<  8) ^
        ((word32)Tsbox[GETBYTE(s0, 0)]);
    t2 =
        ((word32)Tsbox[GETBYTE(s2, 3)] << 24) ^
        ((word32)Tsbox[GETBYTE(s3, 2)] << 16) ^
        ((word32)Tsbox[GETBYTE(s0, 1)] <<  8) ^
        ((word32)Tsbox[GETBYTE(s1, 0)]);
    t3 =
        ((word32)Tsbox[GETBYTE(s3, 3)] << 24) ^
        ((word32)Tsbox[GETBYTE(s0, 2)] << 16) ^
        ((word32)Tsbox[GETBYTE(s1, 1)] <<  8) ^
        ((word32)Tsbox[GETBYTE(s2, 0)]);
    s0 = t0 ^ rk[0];
    s1 = t1 ^ rk[1];
    s2 = t2 ^ rk[2];
    s3 = t3 ^ rk[3];
#endif

    /* write out */
#ifdef LITTLE_ENDIAN_ORDER
    s0 = ByteReverseWord32(s0);
    s1 = ByteReverseWord32(s1);
    s2 = ByteReverseWord32(s2);
    s3 = ByteReverseWord32(s3);
#endif

    XMEMCPY(outBlock,                  &s0, sizeof(s0));
    XMEMCPY(outBlock + sizeof(s0),     &s1, sizeof(s1));
    XMEMCPY(outBlock + 2 * sizeof(s0), &s2, sizeof(s2));
    XMEMCPY(outBlock + 3 * sizeof(s0), &s3, sizeof(s3));

}
#endif /* HAVE_AES_CBC || WOLFSSL_AES_DIRECT || HAVE_AESGCM */

#if defined(HAVE_AES_DECRYPT)
#if (defined(HAVE_AES_CBC) && !defined(WOLFSSL_DEVCRYPTO_CBC)) || \
     defined(WOLFSSL_AES_DIRECT)

#ifndef WOLFSSL_AES_SMALL_TABLES
/* load 4 Td Tables into cache by cache line stride */
static WC_INLINE word32 PreFetchTd(void)
{
    word32 x = 0;
    int i,j;

    for (i = 0; i < 4; i++) {
        /* 256 elements, each one is 4 bytes */
        for (j = 0; j < 256; j += WC_CACHE_LINE_SZ/4) {
            x &= Td[i][j];
        }
    }
    return x;
}
#endif

/* load Td Table4 into cache by cache line stride */
static WC_INLINE word32 PreFetchTd4(void)
{
    word32 x = 0;
    int i;

    for (i = 0; i < 256; i += WC_CACHE_LINE_SZ) {
        x &= (word32)Td4[i];
    }
    return x;
}

/* Software AES - ECB Decrypt */
static void wc_AesDecrypt(Aes* aes, const byte* inBlock, byte* outBlock)
{
    word32 s0, s1, s2, s3;
    word32 t0, t1, t2, t3;
    word32 r = aes->rounds >> 1;

    const word32* rk = aes->key;
    if (r > 7 || r == 0) {
        WOLFSSL_MSG("AesDecrypt encountered improper key, set it up");
        return;  /* stop instead of seg-faulting, set up your keys! */
    }
#ifdef WOLFSSL_AESNI
    if (haveAESNI && aes->use_aesni) {
        #ifdef DEBUG_AESNI
            printf("about to aes decrypt\n");
            printf("in  = %p\n", inBlock);
            printf("out = %p\n", outBlock);
            printf("aes->key = %p\n", aes->key);
            printf("aes->rounds = %d\n", aes->rounds);
            printf("sz = %d\n", AES_BLOCK_SIZE);
        #endif

        /* if input and output same will overwrite input iv */
        if ((const byte*)aes->tmp != inBlock)
            XMEMCPY(aes->tmp, inBlock, AES_BLOCK_SIZE);
        AES_ECB_decrypt(inBlock, outBlock, AES_BLOCK_SIZE, (byte*)aes->key,
                        aes->rounds);
        return;
    }
    else {
        #ifdef DEBUG_AESNI
            printf("Skipping AES-NI\n");
        #endif
    }
#endif /* WOLFSSL_AESNI */
#if defined(WOLFSSL_SCE) && !defined(WOLFSSL_SCE_NO_AES)
    return AES_ECB_decrypt(aes, inBlock, outBlock, AES_BLOCK_SIZE);
#endif

    /*
     * map byte array block to cipher state
     * and add initial round key:
     */
    XMEMCPY(&s0, inBlock,                  sizeof(s0));
    XMEMCPY(&s1, inBlock + sizeof(s0),     sizeof(s1));
    XMEMCPY(&s2, inBlock + 2 * sizeof(s0), sizeof(s2));
    XMEMCPY(&s3, inBlock + 3 * sizeof(s0), sizeof(s3));

#ifdef LITTLE_ENDIAN_ORDER
    s0 = ByteReverseWord32(s0);
    s1 = ByteReverseWord32(s1);
    s2 = ByteReverseWord32(s2);
    s3 = ByteReverseWord32(s3);
#endif

    s0 ^= rk[0];
    s1 ^= rk[1];
    s2 ^= rk[2];
    s3 ^= rk[3];

#ifndef WOLFSSL_AES_SMALL_TABLES
    s0 |= PreFetchTd();

    /*
     * Nr - 1 full rounds:
     */

    for (;;) {
        t0 =
            Td[0][GETBYTE(s0, 3)] ^
            Td[1][GETBYTE(s3, 2)] ^
            Td[2][GETBYTE(s2, 1)] ^
            Td[3][GETBYTE(s1, 0)] ^
            rk[4];
        t1 =
            Td[0][GETBYTE(s1, 3)] ^
            Td[1][GETBYTE(s0, 2)] ^
            Td[2][GETBYTE(s3, 1)] ^
            Td[3][GETBYTE(s2, 0)] ^
            rk[5];
        t2 =
            Td[0][GETBYTE(s2, 3)] ^
            Td[1][GETBYTE(s1, 2)] ^
            Td[2][GETBYTE(s0, 1)] ^
            Td[3][GETBYTE(s3, 0)] ^
            rk[6];
        t3 =
            Td[0][GETBYTE(s3, 3)] ^
            Td[1][GETBYTE(s2, 2)] ^
            Td[2][GETBYTE(s1, 1)] ^
            Td[3][GETBYTE(s0, 0)] ^
            rk[7];

        rk += 8;
        if (--r == 0) {
            break;
        }

        s0 =
            Td[0][GETBYTE(t0, 3)] ^
            Td[1][GETBYTE(t3, 2)] ^
            Td[2][GETBYTE(t2, 1)] ^
            Td[3][GETBYTE(t1, 0)] ^
            rk[0];
        s1 =
            Td[0][GETBYTE(t1, 3)] ^
            Td[1][GETBYTE(t0, 2)] ^
            Td[2][GETBYTE(t3, 1)] ^
            Td[3][GETBYTE(t2, 0)] ^
            rk[1];
        s2 =
            Td[0][GETBYTE(t2, 3)] ^
            Td[1][GETBYTE(t1, 2)] ^
            Td[2][GETBYTE(t0, 1)] ^
            Td[3][GETBYTE(t3, 0)] ^
            rk[2];
        s3 =
            Td[0][GETBYTE(t3, 3)] ^
            Td[1][GETBYTE(t2, 2)] ^
            Td[2][GETBYTE(t1, 1)] ^
            Td[3][GETBYTE(t0, 0)] ^
            rk[3];
    }
    /*
     * apply last round and
     * map cipher state to byte array block:
     */

    t0 |= PreFetchTd4();

    s0 =
        ((word32)Td4[GETBYTE(t0, 3)] << 24) ^
        ((word32)Td4[GETBYTE(t3, 2)] << 16) ^
        ((word32)Td4[GETBYTE(t2, 1)] <<  8) ^
        ((word32)Td4[GETBYTE(t1, 0)]) ^
        rk[0];
    s1 =
        ((word32)Td4[GETBYTE(t1, 3)] << 24) ^
        ((word32)Td4[GETBYTE(t0, 2)] << 16) ^
        ((word32)Td4[GETBYTE(t3, 1)] <<  8) ^
        ((word32)Td4[GETBYTE(t2, 0)]) ^
        rk[1];
    s2 =
        ((word32)Td4[GETBYTE(t2, 3)] << 24) ^
        ((word32)Td4[GETBYTE(t1, 2)] << 16) ^
        ((word32)Td4[GETBYTE(t0, 1)] <<  8) ^
        ((word32)Td4[GETBYTE(t3, 0)]) ^
        rk[2];
    s3 =
        ((word32)Td4[GETBYTE(t3, 3)] << 24) ^
        ((word32)Td4[GETBYTE(t2, 2)] << 16) ^
        ((word32)Td4[GETBYTE(t1, 1)] <<  8) ^
        ((word32)Td4[GETBYTE(t0, 0)]) ^
        rk[3];
#else
    s0 |= PreFetchTd4();

    r *= 2;
    for (rk += 4; r > 1; r--, rk += 4) {
        t0 =
            ((word32)Td4[GETBYTE(s0, 3)] << 24) ^
            ((word32)Td4[GETBYTE(s3, 2)] << 16) ^
            ((word32)Td4[GETBYTE(s2, 1)] <<  8) ^
            ((word32)Td4[GETBYTE(s1, 0)]) ^
            rk[0];
        t1 =
            ((word32)Td4[GETBYTE(s1, 3)] << 24) ^
            ((word32)Td4[GETBYTE(s0, 2)] << 16) ^
            ((word32)Td4[GETBYTE(s3, 1)] <<  8) ^
            ((word32)Td4[GETBYTE(s2, 0)]) ^
            rk[1];
        t2 =
            ((word32)Td4[GETBYTE(s2, 3)] << 24) ^
            ((word32)Td4[GETBYTE(s1, 2)] << 16) ^
            ((word32)Td4[GETBYTE(s0, 1)] <<  8) ^
            ((word32)Td4[GETBYTE(s3, 0)]) ^
            rk[2];
        t3 =
            ((word32)Td4[GETBYTE(s3, 3)] << 24) ^
            ((word32)Td4[GETBYTE(s2, 2)] << 16) ^
            ((word32)Td4[GETBYTE(s1, 1)] <<  8) ^
            ((word32)Td4[GETBYTE(s0, 0)]) ^
            rk[3];

        s0 =
            (inv_col_mul(t0, 0, 2, 1, 3) << 24) ^
            (inv_col_mul(t0, 3, 1, 0, 2) << 16) ^
            (inv_col_mul(t0, 2, 0, 3, 1) <<  8) ^
            (inv_col_mul(t0, 1, 3, 2, 0)      );
        s1 =
            (inv_col_mul(t1, 0, 2, 1, 3) << 24) ^
            (inv_col_mul(t1, 3, 1, 0, 2) << 16) ^
            (inv_col_mul(t1, 2, 0, 3, 1) <<  8) ^
            (inv_col_mul(t1, 1, 3, 2, 0)      );
        s2 =
            (inv_col_mul(t2, 0, 2, 1, 3) << 24) ^
            (inv_col_mul(t2, 3, 1, 0, 2) << 16) ^
            (inv_col_mul(t2, 2, 0, 3, 1) <<  8) ^
            (inv_col_mul(t2, 1, 3, 2, 0)      );
        s3 =
            (inv_col_mul(t3, 0, 2, 1, 3) << 24) ^
            (inv_col_mul(t3, 3, 1, 0, 2) << 16) ^
            (inv_col_mul(t3, 2, 0, 3, 1) <<  8) ^
            (inv_col_mul(t3, 1, 3, 2, 0)      );
    }

    t0 =
        ((word32)Td4[GETBYTE(s0, 3)] << 24) ^
        ((word32)Td4[GETBYTE(s3, 2)] << 16) ^
        ((word32)Td4[GETBYTE(s2, 1)] <<  8) ^
        ((word32)Td4[GETBYTE(s1, 0)]);
    t1 =
        ((word32)Td4[GETBYTE(s1, 3)] << 24) ^
        ((word32)Td4[GETBYTE(s0, 2)] << 16) ^
        ((word32)Td4[GETBYTE(s3, 1)] <<  8) ^
        ((word32)Td4[GETBYTE(s2, 0)]);
    t2 =
        ((word32)Td4[GETBYTE(s2, 3)] << 24) ^
        ((word32)Td4[GETBYTE(s1, 2)] << 16) ^
        ((word32)Td4[GETBYTE(s0, 1)] <<  8) ^
        ((word32)Td4[GETBYTE(s3, 0)]);
    t3 =
        ((word32)Td4[GETBYTE(s3, 3)] << 24) ^
        ((word32)Td4[GETBYTE(s2, 2)] << 16) ^
        ((word32)Td4[GETBYTE(s1, 1)] <<  8) ^
        ((word32)Td4[GETBYTE(s0, 0)]);
    s0 = t0 ^ rk[0];
    s1 = t1 ^ rk[1];
    s2 = t2 ^ rk[2];
    s3 = t3 ^ rk[3];
#endif

    /* write out */
#ifdef LITTLE_ENDIAN_ORDER
    s0 = ByteReverseWord32(s0);
    s1 = ByteReverseWord32(s1);
    s2 = ByteReverseWord32(s2);
    s3 = ByteReverseWord32(s3);
#endif

    XMEMCPY(outBlock,                  &s0, sizeof(s0));
    XMEMCPY(outBlock + sizeof(s0),     &s1, sizeof(s1));
    XMEMCPY(outBlock + 2 * sizeof(s0), &s2, sizeof(s2));
    XMEMCPY(outBlock + 3 * sizeof(s0), &s3, sizeof(s3));
}
#endif /* HAVE_AES_CBC || WOLFSSL_AES_DIRECT */
#endif /* HAVE_AES_DECRYPT */

#endif /* NEED_AES_TABLES */



/* wc_AesSetKey */
#if defined(STM32_CRYPTO)

    int wc_AesSetKey(Aes* aes, const byte* userKey, word32 keylen,
            const byte* iv, int dir)
    {
        word32 *rk;

        (void)dir;

        if (aes == NULL || (keylen != 16 &&
        #ifdef WOLFSSL_AES_192
            keylen != 24 &&
        #endif
            keylen != 32)) {
            return BAD_FUNC_ARG;
        }

        rk = aes->key;
        aes->keylen = keylen;
        aes->rounds = keylen/4 + 6;
        XMEMCPY(rk, userKey, keylen);
    #if !defined(WOLFSSL_STM32_CUBEMX) || defined(STM32_HAL_V2)
        ByteReverseWords(rk, rk, keylen);
    #endif
    #if defined(WOLFSSL_AES_CFB) || defined(WOLFSSL_AES_COUNTER) || \
        defined(WOLFSSL_AES_OFB)
        aes->left = 0;
    #endif

        return wc_AesSetIV(aes, iv);
    }
    #if defined(WOLFSSL_AES_DIRECT)
        int wc_AesSetKeyDirect(Aes* aes, const byte* userKey, word32 keylen,
                            const byte* iv, int dir)
        {
            return wc_AesSetKey(aes, userKey, keylen, iv, dir);
        }
    #endif

#elif defined(HAVE_COLDFIRE_SEC)
    #if defined (HAVE_THREADX)
        #include "memory_pools.h"
        extern TX_BYTE_POOL mp_ncached;  /* Non Cached memory pool */
    #endif

    #define AES_BUFFER_SIZE (AES_BLOCK_SIZE * 64)
    static unsigned char *AESBuffIn = NULL;
    static unsigned char *AESBuffOut = NULL;
    static byte *secReg;
    static byte *secKey;
    static volatile SECdescriptorType *secDesc;

    static wolfSSL_Mutex Mutex_AesSEC;

    #define SEC_DESC_AES_CBC_ENCRYPT 0x60300010
    #define SEC_DESC_AES_CBC_DECRYPT 0x60200010

    extern volatile unsigned char __MBAR[];

    int wc_AesSetKey(Aes* aes, const byte* userKey, word32 keylen,
        const byte* iv, int dir)
    {
        if (AESBuffIn == NULL) {
        #if defined (HAVE_THREADX)
            int s1, s2, s3, s4, s5;
            s5 = tx_byte_allocate(&mp_ncached,(void *)&secDesc,
                                  sizeof(SECdescriptorType), TX_NO_WAIT);
            s1 = tx_byte_allocate(&mp_ncached, (void *)&AESBuffIn,
                                  AES_BUFFER_SIZE, TX_NO_WAIT);
            s2 = tx_byte_allocate(&mp_ncached, (void *)&AESBuffOut,
                                  AES_BUFFER_SIZE, TX_NO_WAIT);
            s3 = tx_byte_allocate(&mp_ncached, (void *)&secKey,
                                  AES_BLOCK_SIZE*2, TX_NO_WAIT);
            s4 = tx_byte_allocate(&mp_ncached, (void *)&secReg,
                                  AES_BLOCK_SIZE, TX_NO_WAIT);

            if (s1 || s2 || s3 || s4 || s5)
                return BAD_FUNC_ARG;
        #else
            #warning "Allocate non-Cache buffers"
        #endif

            wc_InitMutex(&Mutex_AesSEC);
        }

        if (!((keylen == 16) || (keylen == 24) || (keylen == 32)))
            return BAD_FUNC_ARG;

        if (aes == NULL)
            return BAD_FUNC_ARG;

        aes->keylen = keylen;
        aes->rounds = keylen/4 + 6;
        XMEMCPY(aes->key, userKey, keylen);

        if (iv)
            XMEMCPY(aes->reg, iv, AES_BLOCK_SIZE);

    #if defined(WOLFSSL_AES_CFB) || defined(WOLFSSL_AES_COUNTER) || \
        defined(WOLFSSL_AES_OFB)
        aes->left = 0;
    #endif

        return 0;
    }
#elif defined(FREESCALE_LTC)
    int wc_AesSetKey(Aes* aes, const byte* userKey, word32 keylen, const byte* iv,
                  int dir)
    {
        if (aes == NULL || !((keylen == 16) || (keylen == 24) || (keylen == 32)))
            return BAD_FUNC_ARG;

        aes->rounds = keylen/4 + 6;
        XMEMCPY(aes->key, userKey, keylen);

    #if defined(WOLFSSL_AES_CFB) || defined(WOLFSSL_AES_COUNTER) || \
        defined(WOLFSSL_AES_OFB)
        aes->left = 0;
    #endif

        return wc_AesSetIV(aes, iv);
    }

    int wc_AesSetKeyDirect(Aes* aes, const byte* userKey, word32 keylen,
                        const byte* iv, int dir)
    {
        return wc_AesSetKey(aes, userKey, keylen, iv, dir);
    }
#elif defined(FREESCALE_MMCAU)
    int wc_AesSetKey(Aes* aes, const byte* userKey, word32 keylen,
        const byte* iv, int dir)
    {
        int ret;
        byte* rk;
        byte* tmpKey = (byte*)userKey;
        int tmpKeyDynamic = 0;
        word32 alignOffset = 0;

        (void)dir;

        if (!((keylen == 16) || (keylen == 24) || (keylen == 32)))
            return BAD_FUNC_ARG;
        if (aes == NULL)
            return BAD_FUNC_ARG;

        rk = (byte*)aes->key;
        if (rk == NULL)
            return BAD_FUNC_ARG;

    #if defined(WOLFSSL_AES_CFB) || defined(WOLFSSL_AES_COUNTER) || \
        defined(WOLFSSL_AES_OFB)
        aes->left = 0;
    #endif

        aes->rounds = keylen/4 + 6;

    #ifdef FREESCALE_MMCAU_CLASSIC
        if ((wolfssl_word)userKey % WOLFSSL_MMCAU_ALIGNMENT) {
        #ifndef NO_WOLFSSL_ALLOC_ALIGN
            byte* tmp = (byte*)XMALLOC(keylen + WOLFSSL_MMCAU_ALIGNMENT,
                                       aes->heap, DYNAMIC_TYPE_TMP_BUFFER);
            if (tmp == NULL) {
                return MEMORY_E;
            }
            alignOffset = WOLFSSL_MMCAU_ALIGNMENT -
                          ((wolfssl_word)tmp % WOLFSSL_MMCAU_ALIGNMENT);
            tmpKey = tmp + alignOffset;
            XMEMCPY(tmpKey, userKey, keylen);
            tmpKeyDynamic = 1;
        #else
            WOLFSSL_MSG("Bad cau_aes_set_key alignment");
            return BAD_ALIGN_E;
        #endif
        }
    #endif

        ret = wolfSSL_CryptHwMutexLock();
        if(ret == 0) {
        #ifdef FREESCALE_MMCAU_CLASSIC
            cau_aes_set_key(tmpKey, keylen*8, rk);
        #else
            MMCAU_AES_SetKey(tmpKey, keylen, rk);
        #endif
            wolfSSL_CryptHwMutexUnLock();

            ret = wc_AesSetIV(aes, iv);
        }

        if (tmpKeyDynamic == 1) {
            XFREE(tmpKey - alignOffset, aes->heap, DYNAMIC_TYPE_TMP_BUFFER);
        }

        return ret;
    }

    int wc_AesSetKeyDirect(Aes* aes, const byte* userKey, word32 keylen,
                        const byte* iv, int dir)
    {
        return wc_AesSetKey(aes, userKey, keylen, iv, dir);
    }

#elif defined(WOLFSSL_NRF51_AES)
    int wc_AesSetKey(Aes* aes, const byte* userKey, word32 keylen,
        const byte* iv, int dir)
    {
        int ret;

        (void)dir;
        (void)iv;

        if (aes == NULL || keylen != 16)
            return BAD_FUNC_ARG;

        aes->keylen = keylen;
        aes->rounds = keylen/4 + 6;
        XMEMCPY(aes->key, userKey, keylen);
        ret = nrf51_aes_set_key(userKey);

    #if defined(WOLFSSL_AES_CFB) || defined(WOLFSSL_AES_COUNTER) || \
        defined(WOLFSSL_AES_OFB)
        aes->left = 0;
    #endif

        return ret;
    }

    int wc_AesSetKeyDirect(Aes* aes, const byte* userKey, word32 keylen,
                        const byte* iv, int dir)
    {
        return wc_AesSetKey(aes, userKey, keylen, iv, dir);
    }
#elif defined(WOLFSSL_ESP32WROOM32_CRYPT) && \
    !defined(NO_WOLFSSL_ESP32WROOM32_CRYPT_AES)

    int wc_AesSetKey(Aes* aes, const byte* userKey, word32 keylen,
        const byte* iv, int dir)
    {
        (void)dir;
        (void)iv;

        if (aes == NULL || (keylen != 16 && keylen != 24 && keylen != 32)) {
            return BAD_FUNC_ARG;
        }

        aes->keylen = keylen;
        aes->rounds = keylen/4 + 6;

        XMEMCPY(aes->key, userKey, keylen);
        #if defined(WOLFSSL_AES_COUNTER)
            aes->left = 0;
        #endif
        return wc_AesSetIV(aes, iv);
    }

    int wc_AesSetKeyDirect(Aes* aes, const byte* userKey, word32 keylen,
                        const byte* iv, int dir)
    {
        return wc_AesSetKey(aes, userKey, keylen, iv, dir);
    }
#elif defined(WOLFSSL_CRYPTOCELL) && defined(WOLFSSL_CRYPTOCELL_AES)

    int wc_AesSetKey(Aes* aes, const byte* userKey, word32 keylen, const byte* iv,
                    int dir)
    {
        SaSiError_t ret = SASI_OK;
        SaSiAesIv_t iv_aes;

        if (aes == NULL ||
           (keylen != AES_128_KEY_SIZE &&
            keylen != AES_192_KEY_SIZE &&
            keylen != AES_256_KEY_SIZE)) {
            return BAD_FUNC_ARG;
        }
    #if defined(AES_MAX_KEY_SIZE)
        if (keylen > (AES_MAX_KEY_SIZE/8)) {
            return BAD_FUNC_ARG;
        }
    #endif
        if (dir != AES_ENCRYPTION &&
            dir != AES_DECRYPTION) {
            return BAD_FUNC_ARG;
        }

        if (dir == AES_ENCRYPTION) {
            aes->ctx.mode = SASI_AES_ENCRYPT;
            SaSi_AesInit(&aes->ctx.user_ctx,
                         SASI_AES_ENCRYPT,
                         SASI_AES_MODE_CBC,
                         SASI_AES_PADDING_NONE);
        }
        else {
            aes->ctx.mode = SASI_AES_DECRYPT;
            SaSi_AesInit(&aes->ctx.user_ctx,
                         SASI_AES_DECRYPT,
                         SASI_AES_MODE_CBC,
                         SASI_AES_PADDING_NONE);
        }

        aes->keylen = keylen;
        aes->rounds = keylen/4 + 6;
        XMEMCPY(aes->key, userKey, keylen);

        aes->ctx.key.pKey = (uint8_t*)aes->key;
        aes->ctx.key.keySize= keylen;

        ret = SaSi_AesSetKey(&aes->ctx.user_ctx,
                             SASI_AES_USER_KEY,
                             &aes->ctx.key,
                             sizeof(aes->ctx.key));
        if (ret != SASI_OK) {
            return BAD_FUNC_ARG;
        }

        ret = wc_AesSetIV(aes, iv);

        if (iv)
            XMEMCPY(iv_aes, iv, AES_BLOCK_SIZE);
        else
            XMEMSET(iv_aes,  0, AES_BLOCK_SIZE);


        ret = SaSi_AesSetIv(&aes->ctx.user_ctx, iv_aes);
        if (ret != SASI_OK) {
            return ret;
        }
       return ret;
    }
    #if defined(WOLFSSL_AES_DIRECT)
        int wc_AesSetKeyDirect(Aes* aes, const byte* userKey, word32 keylen,
                            const byte* iv, int dir)
        {
            return wc_AesSetKey(aes, userKey, keylen, iv, dir);
        }
    #endif

#elif defined(WOLFSSL_IMX6_CAAM) && !defined(NO_IMX6_CAAM_AES)
      /* implemented in wolfcrypt/src/port/caam/caam_aes.c */

#elif defined(WOLFSSL_AFALG)
    /* implemented in wolfcrypt/src/port/af_alg/afalg_aes.c */

#elif defined(WOLFSSL_DEVCRYPTO_AES)
    /* implemented in wolfcrypt/src/port/devcrypto/devcrypto_aes.c */

#else

    /* Software AES - SetKey */
    static int wc_AesSetKeyLocal(Aes* aes, const byte* userKey, word32 keylen,
                const byte* iv, int dir)
    {
        word32 *rk = aes->key;
    #ifdef NEED_AES_TABLES
        word32 temp;
        unsigned int i = 0;
    #endif

        #ifdef WOLFSSL_AESNI
            aes->use_aesni = 0;
        #endif /* WOLFSSL_AESNI */
        #if defined(WOLFSSL_AES_CFB) || defined(WOLFSSL_AES_COUNTER) || \
            defined(WOLFSSL_AES_OFB)
            aes->left = 0;
        #endif

        aes->keylen = keylen;
        aes->rounds = (keylen/4) + 6;

        XMEMCPY(rk, userKey, keylen);
    #if defined(LITTLE_ENDIAN_ORDER) && !defined(WOLFSSL_PIC32MZ_CRYPT) && \
        (!defined(WOLFSSL_ESP32WROOM32_CRYPT) || \
          defined(NO_WOLFSSL_ESP32WROOM32_CRYPT_AES))
        ByteReverseWords(rk, rk, keylen);
    #endif

#ifdef NEED_AES_TABLES
        switch (keylen) {
    #if defined(AES_MAX_KEY_SIZE) && AES_MAX_KEY_SIZE >= 128 && \
            defined(WOLFSSL_AES_128)
        case 16:
            while (1)
            {
                temp  = rk[3];
                rk[4] = rk[0] ^
            #ifndef WOLFSSL_AES_SMALL_TABLES
                    (Te[2][GETBYTE(temp, 2)] & 0xff000000) ^
                    (Te[3][GETBYTE(temp, 1)] & 0x00ff0000) ^
                    (Te[0][GETBYTE(temp, 0)] & 0x0000ff00) ^
                    (Te[1][GETBYTE(temp, 3)] & 0x000000ff) ^
            #else
                    ((word32)Tsbox[GETBYTE(temp, 2)] << 24) ^
                    ((word32)Tsbox[GETBYTE(temp, 1)] << 16) ^
                    ((word32)Tsbox[GETBYTE(temp, 0)] <<  8) ^
                    ((word32)Tsbox[GETBYTE(temp, 3)]) ^
            #endif
                    rcon[i];
                rk[5] = rk[1] ^ rk[4];
                rk[6] = rk[2] ^ rk[5];
                rk[7] = rk[3] ^ rk[6];
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
                temp = rk[ 5];
                rk[ 6] = rk[ 0] ^
            #ifndef WOLFSSL_AES_SMALL_TABLES
                    (Te[2][GETBYTE(temp, 2)] & 0xff000000) ^
                    (Te[3][GETBYTE(temp, 1)] & 0x00ff0000) ^
                    (Te[0][GETBYTE(temp, 0)] & 0x0000ff00) ^
                    (Te[1][GETBYTE(temp, 3)] & 0x000000ff) ^
            #else
                    ((word32)Tsbox[GETBYTE(temp, 2)] << 24) ^
                    ((word32)Tsbox[GETBYTE(temp, 1)] << 16) ^
                    ((word32)Tsbox[GETBYTE(temp, 0)] <<  8) ^
                    ((word32)Tsbox[GETBYTE(temp, 3)]) ^
            #endif
                    rcon[i];
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
                temp = rk[ 7];
                rk[ 8] = rk[ 0] ^
            #ifndef WOLFSSL_AES_SMALL_TABLES
                    (Te[2][GETBYTE(temp, 2)] & 0xff000000) ^
                    (Te[3][GETBYTE(temp, 1)] & 0x00ff0000) ^
                    (Te[0][GETBYTE(temp, 0)] & 0x0000ff00) ^
                    (Te[1][GETBYTE(temp, 3)] & 0x000000ff) ^
            #else
                    ((word32)Tsbox[GETBYTE(temp, 2)] << 24) ^
                    ((word32)Tsbox[GETBYTE(temp, 1)] << 16) ^
                    ((word32)Tsbox[GETBYTE(temp, 0)] <<  8) ^
                    ((word32)Tsbox[GETBYTE(temp, 3)]) ^
            #endif
                    rcon[i];
                rk[ 9] = rk[ 1] ^ rk[ 8];
                rk[10] = rk[ 2] ^ rk[ 9];
                rk[11] = rk[ 3] ^ rk[10];
                if (++i == 7)
                    break;
                temp = rk[11];
                rk[12] = rk[ 4] ^
            #ifndef WOLFSSL_AES_SMALL_TABLES
                    (Te[2][GETBYTE(temp, 3)] & 0xff000000) ^
                    (Te[3][GETBYTE(temp, 2)] & 0x00ff0000) ^
                    (Te[0][GETBYTE(temp, 1)] & 0x0000ff00) ^
                    (Te[1][GETBYTE(temp, 0)] & 0x000000ff);
            #else
                    ((word32)Tsbox[GETBYTE(temp, 3)] << 24) ^
                    ((word32)Tsbox[GETBYTE(temp, 2)] << 16) ^
                    ((word32)Tsbox[GETBYTE(temp, 1)] <<  8) ^
                    ((word32)Tsbox[GETBYTE(temp, 0)]);
            #endif
                rk[13] = rk[ 5] ^ rk[12];
                rk[14] = rk[ 6] ^ rk[13];
                rk[15] = rk[ 7] ^ rk[14];

                rk += 8;
            }
            break;
    #endif /* 256 */

        default:
            return BAD_FUNC_ARG;
        } /* switch */

    #if defined(HAVE_AES_DECRYPT)
        if (dir == AES_DECRYPTION) {
            unsigned int j;
            rk = aes->key;

            /* invert the order of the round keys: */
            for (i = 0, j = 4* aes->rounds; i < j; i += 4, j -= 4) {
                temp = rk[i    ]; rk[i    ] = rk[j    ]; rk[j    ] = temp;
                temp = rk[i + 1]; rk[i + 1] = rk[j + 1]; rk[j + 1] = temp;
                temp = rk[i + 2]; rk[i + 2] = rk[j + 2]; rk[j + 2] = temp;
                temp = rk[i + 3]; rk[i + 3] = rk[j + 3]; rk[j + 3] = temp;
            }
        #if !defined(WOLFSSL_AES_SMALL_TABLES)
            /* apply the inverse MixColumn transform to all round keys but the
               first and the last: */
            for (i = 1; i < aes->rounds; i++) {
                rk += 4;
                rk[0] =
                    Td[0][Te[1][GETBYTE(rk[0], 3)] & 0xff] ^
                    Td[1][Te[1][GETBYTE(rk[0], 2)] & 0xff] ^
                    Td[2][Te[1][GETBYTE(rk[0], 1)] & 0xff] ^
                    Td[3][Te[1][GETBYTE(rk[0], 0)] & 0xff];
                rk[1] =
                    Td[0][Te[1][GETBYTE(rk[1], 3)] & 0xff] ^
                    Td[1][Te[1][GETBYTE(rk[1], 2)] & 0xff] ^
                    Td[2][Te[1][GETBYTE(rk[1], 1)] & 0xff] ^
                    Td[3][Te[1][GETBYTE(rk[1], 0)] & 0xff];
                rk[2] =
                    Td[0][Te[1][GETBYTE(rk[2], 3)] & 0xff] ^
                    Td[1][Te[1][GETBYTE(rk[2], 2)] & 0xff] ^
                    Td[2][Te[1][GETBYTE(rk[2], 1)] & 0xff] ^
                    Td[3][Te[1][GETBYTE(rk[2], 0)] & 0xff];
                rk[3] =
                    Td[0][Te[1][GETBYTE(rk[3], 3)] & 0xff] ^
                    Td[1][Te[1][GETBYTE(rk[3], 2)] & 0xff] ^
                    Td[2][Te[1][GETBYTE(rk[3], 1)] & 0xff] ^
                    Td[3][Te[1][GETBYTE(rk[3], 0)] & 0xff];
            }
        #endif
        }
    #else
        (void)dir;
    #endif /* HAVE_AES_DECRYPT */
        (void)temp;
#endif /* NEED_AES_TABLES */

#if defined(WOLFSSL_SCE) && !defined(WOLFSSL_SCE_NO_AES)
        XMEMCPY((byte*)aes->key, userKey, keylen);
        if (WOLFSSL_SCE_GSCE_HANDLE.p_cfg->endian_flag == CRYPTO_WORD_ENDIAN_BIG) {
            ByteReverseWords(aes->key, aes->key, 32);
        }
#endif

        return wc_AesSetIV(aes, iv);
    }

    int wc_AesSetKey(Aes* aes, const byte* userKey, word32 keylen,
        const byte* iv, int dir)
    {
        int ret;
    #if defined(AES_MAX_KEY_SIZE)
        const word32 max_key_len = (AES_MAX_KEY_SIZE / 8);
    #endif

    #ifdef WOLFSSL_IMX6_CAAM_BLOB
        byte   local[32];
        word32 localSz = 32;

        if (keylen == (16 + WC_CAAM_BLOB_SZ) ||
                keylen == (24 + WC_CAAM_BLOB_SZ) ||
                keylen == (32 + WC_CAAM_BLOB_SZ)) {
            if (wc_caamOpenBlob((byte*)userKey, keylen, local, &localSz) != 0) {
                return BAD_FUNC_ARG;
            }

            /* set local values */
            userKey = local;
            keylen = localSz;
        }
    #endif
        if (aes == NULL ||
                !((keylen == 16) || (keylen == 24) || (keylen == 32))) {
            return BAD_FUNC_ARG;
        }

    #if defined(AES_MAX_KEY_SIZE)
        /* Check key length */
        if (keylen > max_key_len) {
            return BAD_FUNC_ARG;
        }
    #endif
        aes->keylen = keylen;
        aes->rounds = keylen/4 + 6;

    #if defined(WOLF_CRYPTO_CB) || (defined(WOLFSSL_DEVCRYPTO) && \
        (defined(WOLFSSL_DEVCRYPTO_AES) || defined(WOLFSSL_DEVCRYPTO_CBC))) || \
        (defined(WOLFSSL_ASYNC_CRYPT) && defined(WC_ASYNC_ENABLE_AES))
        #ifdef WOLF_CRYPTO_CB
        if (aes->devId != INVALID_DEVID)
        #endif
        {
            XMEMCPY(aes->devKey, userKey, keylen);
        }
    #endif

    #ifdef WOLFSSL_AESNI
        if (checkAESNI == 0) {
            haveAESNI  = Check_CPU_support_AES();
            checkAESNI = 1;
        }
        if (haveAESNI) {
            #if defined(WOLFSSL_AES_COUNTER) || defined(WOLFSSL_AES_CFB) || \
                defined(WOLFSSL_AES_OFB)
                aes->left = 0;
            #endif /* WOLFSSL_AES_COUNTER */
            aes->use_aesni = 1;
            if (iv)
                XMEMCPY(aes->reg, iv, AES_BLOCK_SIZE);
            else
                XMEMSET(aes->reg, 0, AES_BLOCK_SIZE);
            if (dir == AES_ENCRYPTION)
                return AES_set_encrypt_key(userKey, keylen * 8, aes);
        #ifdef HAVE_AES_DECRYPT
            else
                return AES_set_decrypt_key(userKey, keylen * 8, aes);
        #endif
        }
    #endif /* WOLFSSL_AESNI */

        ret = wc_AesSetKeyLocal(aes, userKey, keylen, iv, dir);

    #if defined(WOLFSSL_DEVCRYPTO) && \
        (defined(WOLFSSL_DEVCRYPTO_AES) || defined(WOLFSSL_DEVCRYPTO_CBC))
        aes->ctx.cfd = -1;
    #endif
    #ifdef WOLFSSL_IMX6_CAAM_BLOB
        ForceZero(local, sizeof(local));
    #endif
        return ret;
    }

    #if defined(WOLFSSL_AES_DIRECT) || defined(WOLFSSL_AES_COUNTER)
        /* AES-CTR and AES-DIRECT need to use this for key setup, no aesni yet */
        int wc_AesSetKeyDirect(Aes* aes, const byte* userKey, word32 keylen,
                            const byte* iv, int dir)
        {
            int ret;

        #ifdef WOLFSSL_IMX6_CAAM_BLOB
            byte   local[32];
            word32 localSz = 32;

            if (keylen == (16 + WC_CAAM_BLOB_SZ) ||
             keylen == (24 + WC_CAAM_BLOB_SZ) ||
             keylen == (32 + WC_CAAM_BLOB_SZ)) {
                if (wc_caamOpenBlob((byte*)userKey, keylen, local, &localSz)
                        != 0) {
                    return BAD_FUNC_ARG;
                }

                /* set local values */
                userKey = local;
                keylen = localSz;
            }
        #endif
            ret = wc_AesSetKeyLocal(aes, userKey, keylen, iv, dir);

        #ifdef WOLFSSL_IMX6_CAAM_BLOB
            ForceZero(local, sizeof(local));
        #endif

            return ret;
        }
    #endif /* WOLFSSL_AES_DIRECT || WOLFSSL_AES_COUNTER */
#endif /* wc_AesSetKey block */


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

/* AES-DIRECT */
#if defined(WOLFSSL_AES_DIRECT)
    #if defined(HAVE_COLDFIRE_SEC)
        #error "Coldfire SEC doesn't yet support AES direct"

    #elif defined(FREESCALE_LTC)
        /* Allow direct access to one block encrypt */
        void wc_AesEncryptDirect(Aes* aes, byte* out, const byte* in)
        {
            byte *key;
            uint32_t keySize;

            key = (byte*)aes->key;
            wc_AesGetKeySize(aes, &keySize);

            LTC_AES_EncryptEcb(LTC_BASE, in, out, AES_BLOCK_SIZE,
                key, keySize);
        }

        /* Allow direct access to one block decrypt */
        void wc_AesDecryptDirect(Aes* aes, byte* out, const byte* in)
        {
            byte *key;
            uint32_t keySize;

            key = (byte*)aes->key;
            wc_AesGetKeySize(aes, &keySize);

            LTC_AES_DecryptEcb(LTC_BASE, in, out, AES_BLOCK_SIZE,
                key, keySize, kLTC_EncryptKey);
        }

    #elif defined(WOLFSSL_IMX6_CAAM) && !defined(NO_IMX6_CAAM_AES)
        /* implemented in wolfcrypt/src/port/caam/caam_aes.c */

    #elif defined(WOLFSSL_AFALG)
        /* implemented in wolfcrypt/src/port/af_alg/afalg_aes.c */

    #elif defined(WOLFSSL_DEVCRYPTO_AES)
        /* implemented in wolfcrypt/src/port/devcrypt/devcrypto_aes.c */

    #elif defined(STM32_CRYPTO)
        /* Allow direct access to one block encrypt */
        void wc_AesEncryptDirect(Aes* aes, byte* out, const byte* in)
        {
            if (wolfSSL_CryptHwMutexLock() == 0) {
                wc_AesEncrypt(aes, in, out);
                wolfSSL_CryptHwMutexUnLock();
            }
        }
        #ifdef HAVE_AES_DECRYPT
        /* Allow direct access to one block decrypt */
        void wc_AesDecryptDirect(Aes* aes, byte* out, const byte* in)
        {
            if (wolfSSL_CryptHwMutexLock() == 0) {
                wc_AesDecrypt(aes, in, out);
                wolfSSL_CryptHwMutexUnLock();
            }
        }
        #endif /* HAVE_AES_DECRYPT */

    #elif defined(WOLFSSL_ESP32WROOM32_CRYPT) && \
        !defined(NO_WOLFSSL_ESP32WROOM32_CRYPT_AES)
        
        /* Allow direct access to one block encrypt */
        void wc_AesEncryptDirect(Aes* aes, byte* out, const byte* in)
        {
            wc_AesEncrypt(aes, in, out);
        }
        #ifdef HAVE_AES_DECRYPT
        /* Allow direct access to one block decrypt */
        void wc_AesDecryptDirect(Aes* aes, byte* out, const byte* in)
        {
            wc_AesDecrypt(aes, in, out);
        }
        #endif /* HAVE_AES_DECRYPT */
    #else
        /* Allow direct access to one block encrypt */
        void wc_AesEncryptDirect(Aes* aes, byte* out, const byte* in)
        {
            wc_AesEncrypt(aes, in, out);
        }
        #ifdef HAVE_AES_DECRYPT
        /* Allow direct access to one block decrypt */
        void wc_AesDecryptDirect(Aes* aes, byte* out, const byte* in)
        {
            wc_AesDecrypt(aes, in, out);
        }
        #endif /* HAVE_AES_DECRYPT */
    #endif /* AES direct block */
#endif /* WOLFSSL_AES_DIRECT */


/* AES-CBC */
#ifdef HAVE_AES_CBC
#if defined(STM32_CRYPTO)

#ifdef WOLFSSL_STM32_CUBEMX
    int wc_AesCbcEncrypt(Aes* aes, byte* out, const byte* in, word32 sz)
    {
        int ret = 0;
        word32 blocks = (sz / AES_BLOCK_SIZE);
        CRYP_HandleTypeDef hcryp;

        ret = wc_Stm32_Aes_Init(aes, &hcryp);
        if (ret != 0)
            return ret;

        ret = wolfSSL_CryptHwMutexLock();
        if (ret != 0) {
            return ret;
        }

    #if defined(STM32_HAL_V2)
        hcryp.Init.Algorithm  = CRYP_AES_CBC;
        ByteReverseWords(aes->reg, aes->reg, AES_BLOCK_SIZE);
    #elif defined(STM32_CRYPTO_AES_ONLY)
        hcryp.Init.OperatingMode = CRYP_ALGOMODE_ENCRYPT;
        hcryp.Init.ChainingMode  = CRYP_CHAINMODE_AES_CBC;
        hcryp.Init.KeyWriteFlag  = CRYP_KEY_WRITE_ENABLE;
    #endif
        hcryp.Init.pInitVect = (STM_CRYPT_TYPE*)aes->reg;
        HAL_CRYP_Init(&hcryp);

    #if defined(STM32_HAL_V2)
        ret = HAL_CRYP_Encrypt(&hcryp, (uint32_t*)in, blocks * AES_BLOCK_SIZE,
            (uint32_t*)out, STM32_HAL_TIMEOUT);
    #elif defined(STM32_CRYPTO_AES_ONLY)
        ret = HAL_CRYPEx_AES(&hcryp, (uint8_t*)in, blocks * AES_BLOCK_SIZE,
            out, STM32_HAL_TIMEOUT);
    #else
        ret = HAL_CRYP_AESCBC_Encrypt(&hcryp, (uint8_t*)in, blocks * AES_BLOCK_SIZE,
            out, STM32_HAL_TIMEOUT);
    #endif
        if (ret != HAL_OK) {
            ret = WC_TIMEOUT_E;
        }

        /* store iv for next call */
        XMEMCPY(aes->reg, out + sz - AES_BLOCK_SIZE, AES_BLOCK_SIZE);

        HAL_CRYP_DeInit(&hcryp);

        wolfSSL_CryptHwMutexUnLock();

        return ret;
    }
    #ifdef HAVE_AES_DECRYPT
    int wc_AesCbcDecrypt(Aes* aes, byte* out, const byte* in, word32 sz)
    {
        int ret = 0;
        word32 blocks = (sz / AES_BLOCK_SIZE);
        CRYP_HandleTypeDef hcryp;

        ret = wc_Stm32_Aes_Init(aes, &hcryp);
        if (ret != 0)
            return ret;

        ret = wolfSSL_CryptHwMutexLock();
        if (ret != 0) {
            return ret;
        }

        /* if input and output same will overwrite input iv */
        XMEMCPY(aes->tmp, in + sz - AES_BLOCK_SIZE, AES_BLOCK_SIZE);

    #if defined(STM32_HAL_V2)
        hcryp.Init.Algorithm  = CRYP_AES_CBC;
        ByteReverseWords(aes->reg, aes->reg, AES_BLOCK_SIZE);
    #elif defined(STM32_CRYPTO_AES_ONLY)
        hcryp.Init.OperatingMode = CRYP_ALGOMODE_KEYDERIVATION_DECRYPT;
        hcryp.Init.ChainingMode  = CRYP_CHAINMODE_AES_CBC;
        hcryp.Init.KeyWriteFlag  = CRYP_KEY_WRITE_ENABLE;
    #endif

        hcryp.Init.pInitVect = (STM_CRYPT_TYPE*)aes->reg;
        HAL_CRYP_Init(&hcryp);

    #if defined(STM32_HAL_V2)
        ret = HAL_CRYP_Decrypt(&hcryp, (uint32_t*)in, blocks * AES_BLOCK_SIZE,
            (uint32_t*)out, STM32_HAL_TIMEOUT);
    #elif defined(STM32_CRYPTO_AES_ONLY)
        ret = HAL_CRYPEx_AES(&hcryp, (uint8_t*)in, blocks * AES_BLOCK_SIZE,
            out, STM32_HAL_TIMEOUT);
    #else
        ret = HAL_CRYP_AESCBC_Decrypt(&hcryp, (uint8_t*)in, blocks * AES_BLOCK_SIZE,
            out, STM32_HAL_TIMEOUT);
    #endif
        if (ret != HAL_OK) {
            ret = WC_TIMEOUT_E;
        }

        /* store iv for next call */
        XMEMCPY(aes->reg, aes->tmp, AES_BLOCK_SIZE);

        HAL_CRYP_DeInit(&hcryp);
        wolfSSL_CryptHwMutexUnLock();

        return ret;
    }
    #endif /* HAVE_AES_DECRYPT */

#else /* Standard Peripheral Library */
    int wc_AesCbcEncrypt(Aes* aes, byte* out, const byte* in, word32 sz)
    {
        int ret;
        word32 *iv;
        word32 blocks = (sz / AES_BLOCK_SIZE);
        CRYP_InitTypeDef cryptInit;
        CRYP_KeyInitTypeDef keyInit;
        CRYP_IVInitTypeDef ivInit;

        ret = wc_Stm32_Aes_Init(aes, &cryptInit, &keyInit);
        if (ret != 0)
            return ret;

        ret = wolfSSL_CryptHwMutexLock();
        if (ret != 0) {
            return ret;
        }

        /* reset registers to their default values */
        CRYP_DeInit();

        /* set key */
        CRYP_KeyInit(&keyInit);

        /* set iv */
        iv = aes->reg;
        CRYP_IVStructInit(&ivInit);
        ByteReverseWords(iv, iv, AES_BLOCK_SIZE);
        ivInit.CRYP_IV0Left  = iv[0];
        ivInit.CRYP_IV0Right = iv[1];
        ivInit.CRYP_IV1Left  = iv[2];
        ivInit.CRYP_IV1Right = iv[3];
        CRYP_IVInit(&ivInit);

        /* set direction and mode */
        cryptInit.CRYP_AlgoDir  = CRYP_AlgoDir_Encrypt;
        cryptInit.CRYP_AlgoMode = CRYP_AlgoMode_AES_CBC;
        CRYP_Init(&cryptInit);

        /* enable crypto processor */
        CRYP_Cmd(ENABLE);

        while (blocks--) {
            /* flush IN/OUT FIFOs */
            CRYP_FIFOFlush();

            CRYP_DataIn(*(uint32_t*)&in[0]);
            CRYP_DataIn(*(uint32_t*)&in[4]);
            CRYP_DataIn(*(uint32_t*)&in[8]);
            CRYP_DataIn(*(uint32_t*)&in[12]);

            /* wait until the complete message has been processed */
            while (CRYP_GetFlagStatus(CRYP_FLAG_BUSY) != RESET) {}

            *(uint32_t*)&out[0]  = CRYP_DataOut();
            *(uint32_t*)&out[4]  = CRYP_DataOut();
            *(uint32_t*)&out[8]  = CRYP_DataOut();
            *(uint32_t*)&out[12] = CRYP_DataOut();

            /* store iv for next call */
            XMEMCPY(aes->reg, out + sz - AES_BLOCK_SIZE, AES_BLOCK_SIZE);

            sz  -= AES_BLOCK_SIZE;
            in  += AES_BLOCK_SIZE;
            out += AES_BLOCK_SIZE;
        }

        /* disable crypto processor */
        CRYP_Cmd(DISABLE);
        wolfSSL_CryptHwMutexUnLock();

        return ret;
    }

    #ifdef HAVE_AES_DECRYPT
    int wc_AesCbcDecrypt(Aes* aes, byte* out, const byte* in, word32 sz)
    {
        int ret;
        word32 *iv;
        word32 blocks = (sz / AES_BLOCK_SIZE);
        CRYP_InitTypeDef cryptInit;
        CRYP_KeyInitTypeDef keyInit;
        CRYP_IVInitTypeDef ivInit;

        ret = wc_Stm32_Aes_Init(aes, &cryptInit, &keyInit);
        if (ret != 0)
            return ret;

        ret = wolfSSL_CryptHwMutexLock();
        if (ret != 0) {
            return ret;
        }

        /* if input and output same will overwrite input iv */
        XMEMCPY(aes->tmp, in + sz - AES_BLOCK_SIZE, AES_BLOCK_SIZE);

        /* reset registers to their default values */
        CRYP_DeInit();

        /* set direction and key */
        CRYP_KeyInit(&keyInit);
        cryptInit.CRYP_AlgoDir  = CRYP_AlgoDir_Decrypt;
        cryptInit.CRYP_AlgoMode = CRYP_AlgoMode_AES_Key;
        CRYP_Init(&cryptInit);

        /* enable crypto processor */
        CRYP_Cmd(ENABLE);

        /* wait until key has been prepared */
        while (CRYP_GetFlagStatus(CRYP_FLAG_BUSY) != RESET) {}

        /* set direction and mode */
        cryptInit.CRYP_AlgoDir  = CRYP_AlgoDir_Decrypt;
        cryptInit.CRYP_AlgoMode = CRYP_AlgoMode_AES_CBC;
        CRYP_Init(&cryptInit);

        /* set iv */
        iv = aes->reg;
        CRYP_IVStructInit(&ivInit);
        ByteReverseWords(iv, iv, AES_BLOCK_SIZE);
        ivInit.CRYP_IV0Left  = iv[0];
        ivInit.CRYP_IV0Right = iv[1];
        ivInit.CRYP_IV1Left  = iv[2];
        ivInit.CRYP_IV1Right = iv[3];
        CRYP_IVInit(&ivInit);

        /* enable crypto processor */
        CRYP_Cmd(ENABLE);

        while (blocks--) {
            /* flush IN/OUT FIFOs */
            CRYP_FIFOFlush();

            CRYP_DataIn(*(uint32_t*)&in[0]);
            CRYP_DataIn(*(uint32_t*)&in[4]);
            CRYP_DataIn(*(uint32_t*)&in[8]);
            CRYP_DataIn(*(uint32_t*)&in[12]);

            /* wait until the complete message has been processed */
            while (CRYP_GetFlagStatus(CRYP_FLAG_BUSY) != RESET) {}

            *(uint32_t*)&out[0]  = CRYP_DataOut();
            *(uint32_t*)&out[4]  = CRYP_DataOut();
            *(uint32_t*)&out[8]  = CRYP_DataOut();
            *(uint32_t*)&out[12] = CRYP_DataOut();

            /* store iv for next call */
            XMEMCPY(aes->reg, aes->tmp, AES_BLOCK_SIZE);

            in  += AES_BLOCK_SIZE;
            out += AES_BLOCK_SIZE;
        }

        /* disable crypto processor */
        CRYP_Cmd(DISABLE);
        wolfSSL_CryptHwMutexUnLock();

        return ret;
    }
    #endif /* HAVE_AES_DECRYPT */
#endif /* WOLFSSL_STM32_CUBEMX */

#elif defined(HAVE_COLDFIRE_SEC)
    static int wc_AesCbcCrypt(Aes* aes, byte* po, const byte* pi, word32 sz,
        word32 descHeader)
    {
        #ifdef DEBUG_WOLFSSL
            int i; int stat1, stat2; int ret;
        #endif

        int size;
        volatile int v;

        if ((pi == NULL) || (po == NULL))
            return BAD_FUNC_ARG;    /*wrong pointer*/

        wc_LockMutex(&Mutex_AesSEC);

        /* Set descriptor for SEC */
        secDesc->length1 = 0x0;
        secDesc->pointer1 = NULL;

        secDesc->length2 = AES_BLOCK_SIZE;
        secDesc->pointer2 = (byte *)secReg; /* Initial Vector */

        switch(aes->rounds) {
            case 10: secDesc->length3 = 16; break;
            case 12: secDesc->length3 = 24; break;
            case 14: secDesc->length3 = 32; break;
        }
        XMEMCPY(secKey, aes->key, secDesc->length3);

        secDesc->pointer3 = (byte *)secKey;
        secDesc->pointer4 = AESBuffIn;
        secDesc->pointer5 = AESBuffOut;
        secDesc->length6 = 0x0;
        secDesc->pointer6 = NULL;
        secDesc->length7 = 0x0;
        secDesc->pointer7 = NULL;
        secDesc->nextDescriptorPtr = NULL;

        while (sz) {
            secDesc->header = descHeader;
            XMEMCPY(secReg, aes->reg, AES_BLOCK_SIZE);
            if ((sz % AES_BUFFER_SIZE) == sz) {
                size = sz;
                sz = 0;
            } else {
                size = AES_BUFFER_SIZE;
                sz -= AES_BUFFER_SIZE;
            }
            secDesc->length4 = size;
            secDesc->length5 = size;

            XMEMCPY(AESBuffIn, pi, size);
            if(descHeader == SEC_DESC_AES_CBC_DECRYPT) {
                XMEMCPY((void*)aes->tmp, (void*)&(pi[size-AES_BLOCK_SIZE]),
                        AES_BLOCK_SIZE);
            }

            /* Point SEC to the location of the descriptor */
            MCF_SEC_FR0 = (uint32)secDesc;
            /* Initialize SEC and wait for encryption to complete */
            MCF_SEC_CCCR0 = 0x0000001a;
            /* poll SISR to determine when channel is complete */
            v=0;

            while ((secDesc->header>> 24) != 0xff) v++;

            #ifdef DEBUG_WOLFSSL
                ret = MCF_SEC_SISRH;
                stat1 = MCF_SEC_AESSR;
                stat2 = MCF_SEC_AESISR;
                if (ret & 0xe0000000) {
                    db_printf("Aes_Cbc(i=%d):ISRH=%08x, AESSR=%08x, "
                              "AESISR=%08x\n", i, ret, stat1, stat2);
                }
            #endif

            XMEMCPY(po, AESBuffOut, size);

            if (descHeader == SEC_DESC_AES_CBC_ENCRYPT) {
                XMEMCPY((void*)aes->reg, (void*)&(po[size-AES_BLOCK_SIZE]),
                        AES_BLOCK_SIZE);
            } else {
                XMEMCPY((void*)aes->reg, (void*)aes->tmp, AES_BLOCK_SIZE);
            }

            pi += size;
            po += size;
        }

        wc_UnLockMutex(&Mutex_AesSEC);
        return 0;
    }

    int wc_AesCbcEncrypt(Aes* aes, byte* po, const byte* pi, word32 sz)
    {
        return (wc_AesCbcCrypt(aes, po, pi, sz, SEC_DESC_AES_CBC_ENCRYPT));
    }

    #ifdef HAVE_AES_DECRYPT
    int wc_AesCbcDecrypt(Aes* aes, byte* po, const byte* pi, word32 sz)
    {
        return (wc_AesCbcCrypt(aes, po, pi, sz, SEC_DESC_AES_CBC_DECRYPT));
    }
    #endif /* HAVE_AES_DECRYPT */

#elif defined(FREESCALE_LTC)
    int wc_AesCbcEncrypt(Aes* aes, byte* out, const byte* in, word32 sz)
    {
        uint32_t keySize;
        status_t status;
        byte *iv, *enc_key;
        word32 blocks = (sz / AES_BLOCK_SIZE);

        iv      = (byte*)aes->reg;
        enc_key = (byte*)aes->key;

        status = wc_AesGetKeySize(aes, &keySize);
        if (status != 0) {
            return status;
        }

        status = LTC_AES_EncryptCbc(LTC_BASE, in, out, blocks * AES_BLOCK_SIZE,
            iv, enc_key, keySize);

        /* store iv for next call */
        if (status == kStatus_Success) {
            XMEMCPY(iv, out + sz - AES_BLOCK_SIZE, AES_BLOCK_SIZE);
        }

        return (status == kStatus_Success) ? 0 : -1;
    }

    #ifdef HAVE_AES_DECRYPT
    int wc_AesCbcDecrypt(Aes* aes, byte* out, const byte* in, word32 sz)
    {
        uint32_t keySize;
        status_t status;
        byte* iv, *dec_key;
        word32 blocks = (sz / AES_BLOCK_SIZE);
        byte temp_block[AES_BLOCK_SIZE];

        iv      = (byte*)aes->reg;
        dec_key = (byte*)aes->key;

        status = wc_AesGetKeySize(aes, &keySize);
        if (status != 0) {
            return status;
        }

        /* get IV for next call */
        XMEMCPY(temp_block, in + sz - AES_BLOCK_SIZE, AES_BLOCK_SIZE);

        status = LTC_AES_DecryptCbc(LTC_BASE, in, out, blocks * AES_BLOCK_SIZE,
            iv, dec_key, keySize, kLTC_EncryptKey);

        /* store IV for next call */
        if (status == kStatus_Success) {
            XMEMCPY(iv, temp_block, AES_BLOCK_SIZE);
        }

        return (status == kStatus_Success) ? 0 : -1;
    }
    #endif /* HAVE_AES_DECRYPT */

#elif defined(FREESCALE_MMCAU)
    int wc_AesCbcEncrypt(Aes* aes, byte* out, const byte* in, word32 sz)
    {
        int i;
        int offset = 0;
        word32 blocks = (sz / AES_BLOCK_SIZE);
        byte *iv;
        byte temp_block[AES_BLOCK_SIZE];

        iv      = (byte*)aes->reg;

        while (blocks--) {
            XMEMCPY(temp_block, in + offset, AES_BLOCK_SIZE);

            /* XOR block with IV for CBC */
            for (i = 0; i < AES_BLOCK_SIZE; i++)
                temp_block[i] ^= iv[i];

            wc_AesEncrypt(aes, temp_block, out + offset);

            offset += AES_BLOCK_SIZE;

            /* store IV for next block */
            XMEMCPY(iv, out + offset - AES_BLOCK_SIZE, AES_BLOCK_SIZE);
        }

        return 0;
    }
    #ifdef HAVE_AES_DECRYPT
    int wc_AesCbcDecrypt(Aes* aes, byte* out, const byte* in, word32 sz)
    {
        int i;
        int offset = 0;
        word32 blocks = (sz / AES_BLOCK_SIZE);
        byte* iv;
        byte temp_block[AES_BLOCK_SIZE];

        iv      = (byte*)aes->reg;

        while (blocks--) {
            XMEMCPY(temp_block, in + offset, AES_BLOCK_SIZE);

            wc_AesDecrypt(aes, in + offset, out + offset);

            /* XOR block with IV for CBC */
            for (i = 0; i < AES_BLOCK_SIZE; i++)
                (out + offset)[i] ^= iv[i];

            /* store IV for next block */
            XMEMCPY(iv, temp_block, AES_BLOCK_SIZE);

            offset += AES_BLOCK_SIZE;
        }

        return 0;
    }
    #endif /* HAVE_AES_DECRYPT */

#elif defined(WOLFSSL_PIC32MZ_CRYPT)

    int wc_AesCbcEncrypt(Aes* aes, byte* out, const byte* in, word32 sz)
    {
        int ret;

        /* hardware fails on input that is not a multiple of AES block size */
        if (sz % AES_BLOCK_SIZE != 0) {
            return BAD_FUNC_ARG;
        }

        ret = wc_Pic32AesCrypt(
            aes->key, aes->keylen, aes->reg, AES_BLOCK_SIZE,
            out, in, sz, PIC32_ENCRYPTION,
            PIC32_ALGO_AES, PIC32_CRYPTOALGO_RCBC);

        /* store iv for next call */
        if (ret == 0) {
            XMEMCPY(aes->reg, out + sz - AES_BLOCK_SIZE, AES_BLOCK_SIZE);
        }

        return ret;
    }
    #ifdef HAVE_AES_DECRYPT
    int wc_AesCbcDecrypt(Aes* aes, byte* out, const byte* in, word32 sz)
    {
        int ret;
        byte scratch[AES_BLOCK_SIZE];

        /* hardware fails on input that is not a multiple of AES block size */
        if (sz % AES_BLOCK_SIZE != 0) {
            return BAD_FUNC_ARG;
        }
        XMEMCPY(scratch, in + sz - AES_BLOCK_SIZE, AES_BLOCK_SIZE);

        ret = wc_Pic32AesCrypt(
            aes->key, aes->keylen, aes->reg, AES_BLOCK_SIZE,
            out, in, sz, PIC32_DECRYPTION,
            PIC32_ALGO_AES, PIC32_CRYPTOALGO_RCBC);

        /* store iv for next call */
        if (ret == 0) {
            XMEMCPY((byte*)aes->reg, scratch, AES_BLOCK_SIZE);
        }

        return ret;
    }
    #endif /* HAVE_AES_DECRYPT */
#elif defined(WOLFSSL_ESP32WROOM32_CRYPT) && \
    !defined(NO_WOLFSSL_ESP32WROOM32_CRYPT_AES)

    int wc_AesCbcEncrypt(Aes* aes, byte* out, const byte* in, word32 sz)
    {
        return wc_esp32AesCbcEncrypt(aes, out, in, sz);
    }
    int wc_AesCbcDecrypt(Aes* aes, byte* out, const byte* in, word32 sz)
    {
        return wc_esp32AesCbcDecrypt(aes, out, in, sz);
    }
#elif defined(WOLFSSL_CRYPTOCELL) && defined(WOLFSSL_CRYPTOCELL_AES)
    int wc_AesCbcEncrypt(Aes* aes, byte* out, const byte* in, word32 sz)
    {
        return SaSi_AesBlock(&aes->ctx.user_ctx, (uint8_t* )in, sz, out);
    }
    int wc_AesCbcDecrypt(Aes* aes, byte* out, const byte* in, word32 sz)
    {
        return SaSi_AesBlock(&aes->ctx.user_ctx, (uint8_t* )in, sz, out);
    }
#elif defined(WOLFSSL_IMX6_CAAM) && !defined(NO_IMX6_CAAM_AES)
      /* implemented in wolfcrypt/src/port/caam/caam_aes.c */

#elif defined(WOLFSSL_AFALG)
    /* implemented in wolfcrypt/src/port/af_alg/afalg_aes.c */

#elif defined(WOLFSSL_DEVCRYPTO_CBC)
    /* implemented in wolfcrypt/src/port/devcrypt/devcrypto_aes.c */

#else

    /* Software AES - CBC Encrypt */
    int wc_AesCbcEncrypt(Aes* aes, byte* out, const byte* in, word32 sz)
    {
        word32 blocks = (sz / AES_BLOCK_SIZE);

        if (aes == NULL || out == NULL || in == NULL) {
            return BAD_FUNC_ARG;
        }

    #ifdef WOLF_CRYPTO_CB
        if (aes->devId != INVALID_DEVID) {
            int ret = wc_CryptoCb_AesCbcEncrypt(aes, out, in, sz);
            if (ret != CRYPTOCB_UNAVAILABLE)
                return ret;
            /* fall-through when unavailable */
        }
    #endif
    #if defined(WOLFSSL_ASYNC_CRYPT) && defined(WC_ASYNC_ENABLE_AES)
        /* if async and byte count above threshold */
        if (aes->asyncDev.marker == WOLFSSL_ASYNC_MARKER_AES &&
                                                sz >= WC_ASYNC_THRESH_AES_CBC) {
        #if defined(HAVE_CAVIUM)
            return NitroxAesCbcEncrypt(aes, out, in, sz);
        #elif defined(HAVE_INTEL_QA)
            return IntelQaSymAesCbcEncrypt(&aes->asyncDev, out, in, sz,
                (const byte*)aes->devKey, aes->keylen,
                (byte*)aes->reg, AES_BLOCK_SIZE);
        #else /* WOLFSSL_ASYNC_CRYPT_TEST */
            if (wc_AsyncTestInit(&aes->asyncDev, ASYNC_TEST_AES_CBC_ENCRYPT)) {
                WC_ASYNC_TEST* testDev = &aes->asyncDev.test;
                testDev->aes.aes = aes;
                testDev->aes.out = out;
                testDev->aes.in = in;
                testDev->aes.sz = sz;
                return WC_PENDING_E;
            }
        #endif
        }
    #endif /* WOLFSSL_ASYNC_CRYPT */

    #ifdef WOLFSSL_AESNI
        if (haveAESNI) {
            #ifdef DEBUG_AESNI
                printf("about to aes cbc encrypt\n");
                printf("in  = %p\n", in);
                printf("out = %p\n", out);
                printf("aes->key = %p\n", aes->key);
                printf("aes->reg = %p\n", aes->reg);
                printf("aes->rounds = %d\n", aes->rounds);
                printf("sz = %d\n", sz);
            #endif

            /* check alignment, decrypt doesn't need alignment */
            if ((wolfssl_word)in % AESNI_ALIGN) {
            #ifndef NO_WOLFSSL_ALLOC_ALIGN
                byte* tmp = (byte*)XMALLOC(sz + AES_BLOCK_SIZE + AESNI_ALIGN,
                                            aes->heap, DYNAMIC_TYPE_TMP_BUFFER);
                byte* tmp_align;
                if (tmp == NULL) return MEMORY_E;

                tmp_align = tmp + (AESNI_ALIGN - ((size_t)tmp % AESNI_ALIGN));
                XMEMCPY(tmp_align, in, sz);
                AES_CBC_encrypt(tmp_align, tmp_align, (byte*)aes->reg, sz,
                                                  (byte*)aes->key, aes->rounds);
                /* store iv for next call */
                XMEMCPY(aes->reg, tmp_align + sz - AES_BLOCK_SIZE, AES_BLOCK_SIZE);

                XMEMCPY(out, tmp_align, sz);
                XFREE(tmp, aes->heap, DYNAMIC_TYPE_TMP_BUFFER);
                return 0;
            #else
                WOLFSSL_MSG("AES-CBC encrypt with bad alignment");
                return BAD_ALIGN_E;
            #endif
            }

            AES_CBC_encrypt(in, out, (byte*)aes->reg, sz, (byte*)aes->key,
                            aes->rounds);
            /* store iv for next call */
            XMEMCPY(aes->reg, out + sz - AES_BLOCK_SIZE, AES_BLOCK_SIZE);

            return 0;
        }
    #endif

        while (blocks--) {
            xorbuf((byte*)aes->reg, in, AES_BLOCK_SIZE);
            wc_AesEncrypt(aes, (byte*)aes->reg, (byte*)aes->reg);
            XMEMCPY(out, aes->reg, AES_BLOCK_SIZE);

            out += AES_BLOCK_SIZE;
            in  += AES_BLOCK_SIZE;
        }

        return 0;
    }

    #ifdef HAVE_AES_DECRYPT
    /* Software AES - CBC Decrypt */
    int wc_AesCbcDecrypt(Aes* aes, byte* out, const byte* in, word32 sz)
    {
        word32 blocks;

        if (aes == NULL || out == NULL || in == NULL
                                       || sz % AES_BLOCK_SIZE != 0) {
            return BAD_FUNC_ARG;
        }

    #ifdef WOLF_CRYPTO_CB
        if (aes->devId != INVALID_DEVID) {
            int ret = wc_CryptoCb_AesCbcDecrypt(aes, out, in, sz);
            if (ret != CRYPTOCB_UNAVAILABLE)
                return ret;
            /* fall-through when unavailable */
        }
    #endif
    #if defined(WOLFSSL_ASYNC_CRYPT) && defined(WC_ASYNC_ENABLE_AES)
        /* if async and byte count above threshold */
        if (aes->asyncDev.marker == WOLFSSL_ASYNC_MARKER_AES &&
                                                sz >= WC_ASYNC_THRESH_AES_CBC) {
        #if defined(HAVE_CAVIUM)
            return NitroxAesCbcDecrypt(aes, out, in, sz);
        #elif defined(HAVE_INTEL_QA)
            return IntelQaSymAesCbcDecrypt(&aes->asyncDev, out, in, sz,
                (const byte*)aes->devKey, aes->keylen,
                (byte*)aes->reg, AES_BLOCK_SIZE);
        #else /* WOLFSSL_ASYNC_CRYPT_TEST */
            if (wc_AsyncTestInit(&aes->asyncDev, ASYNC_TEST_AES_CBC_DECRYPT)) {
                WC_ASYNC_TEST* testDev = &aes->asyncDev.test;
                testDev->aes.aes = aes;
                testDev->aes.out = out;
                testDev->aes.in = in;
                testDev->aes.sz = sz;
                return WC_PENDING_E;
            }
        #endif
        }
    #endif

    #ifdef WOLFSSL_AESNI
        if (haveAESNI) {
            #ifdef DEBUG_AESNI
                printf("about to aes cbc decrypt\n");
                printf("in  = %p\n", in);
                printf("out = %p\n", out);
                printf("aes->key = %p\n", aes->key);
                printf("aes->reg = %p\n", aes->reg);
                printf("aes->rounds = %d\n", aes->rounds);
                printf("sz = %d\n", sz);
            #endif

            /* if input and output same will overwrite input iv */
            XMEMCPY(aes->tmp, in + sz - AES_BLOCK_SIZE, AES_BLOCK_SIZE);
            #if defined(WOLFSSL_AESNI_BY4)
            AES_CBC_decrypt_by4(in, out, (byte*)aes->reg, sz, (byte*)aes->key,
                            aes->rounds);
            #elif defined(WOLFSSL_AESNI_BY6)
            AES_CBC_decrypt_by6(in, out, (byte*)aes->reg, sz, (byte*)aes->key,
                            aes->rounds);
            #else /* WOLFSSL_AESNI_BYx */
            AES_CBC_decrypt_by8(in, out, (byte*)aes->reg, sz, (byte*)aes->key,
                            aes->rounds);
            #endif /* WOLFSSL_AESNI_BYx */
            /* store iv for next call */
            XMEMCPY(aes->reg, aes->tmp, AES_BLOCK_SIZE);
            return 0;
        }
    #endif

        blocks = sz / AES_BLOCK_SIZE;
        while (blocks--) {
            XMEMCPY(aes->tmp, in, AES_BLOCK_SIZE);
            wc_AesDecrypt(aes, (byte*)aes->tmp, out);
            xorbuf(out, (byte*)aes->reg, AES_BLOCK_SIZE);
            /* store iv for next call */
            XMEMCPY(aes->reg, aes->tmp, AES_BLOCK_SIZE);

            out += AES_BLOCK_SIZE;
            in  += AES_BLOCK_SIZE;
        }

        return 0;
    }
    #endif

#endif /* AES-CBC block */
#endif /* HAVE_AES_CBC */

/* AES-CTR */
#if defined(WOLFSSL_AES_COUNTER)

    #ifdef STM32_CRYPTO
        #define NEED_AES_CTR_SOFT
        #define XTRANSFORM_AESCTRBLOCK wc_AesCtrEncryptBlock

        int wc_AesCtrEncryptBlock(Aes* aes, byte* out, const byte* in)
        {
            int ret = 0;
        #ifdef WOLFSSL_STM32_CUBEMX
            CRYP_HandleTypeDef hcryp;
            #ifdef STM32_HAL_V2
            word32 iv[AES_BLOCK_SIZE/sizeof(word32)];
            #endif
        #else
            word32 *iv;
            CRYP_InitTypeDef cryptInit;
            CRYP_KeyInitTypeDef keyInit;
            CRYP_IVInitTypeDef ivInit;
        #endif

        #ifdef WOLFSSL_STM32_CUBEMX
            ret = wc_Stm32_Aes_Init(aes, &hcryp);
            if (ret != 0) {
                return ret;
            }

            ret = wolfSSL_CryptHwMutexLock();
            if (ret != 0) {
                return ret;
            }

        #if defined(STM32_HAL_V2)
            hcryp.Init.Algorithm  = CRYP_AES_CTR;
            ByteReverseWords(iv, aes->reg, AES_BLOCK_SIZE);
            hcryp.Init.pInitVect = (STM_CRYPT_TYPE*)iv;
        #elif defined(STM32_CRYPTO_AES_ONLY)
            hcryp.Init.OperatingMode = CRYP_ALGOMODE_ENCRYPT;
            hcryp.Init.ChainingMode  = CRYP_CHAINMODE_AES_CTR;
            hcryp.Init.KeyWriteFlag  = CRYP_KEY_WRITE_ENABLE;
            hcryp.Init.pInitVect = (STM_CRYPT_TYPE*)aes->reg;
        #else
            hcryp.Init.pInitVect = (STM_CRYPT_TYPE*)aes->reg;
        #endif
            HAL_CRYP_Init(&hcryp);

        #if defined(STM32_HAL_V2)
            ret = HAL_CRYP_Encrypt(&hcryp, (uint32_t*)in, AES_BLOCK_SIZE,
                (uint32_t*)out, STM32_HAL_TIMEOUT);
        #elif defined(STM32_CRYPTO_AES_ONLY)
            ret = HAL_CRYPEx_AES(&hcryp, (byte*)in, AES_BLOCK_SIZE,
                out, STM32_HAL_TIMEOUT);
        #else
            ret = HAL_CRYP_AESCTR_Encrypt(&hcryp, (byte*)in, AES_BLOCK_SIZE,
                out, STM32_HAL_TIMEOUT);
        #endif
            if (ret != HAL_OK) {
                ret = WC_TIMEOUT_E;
            }
            HAL_CRYP_DeInit(&hcryp);

        #else /* Standard Peripheral Library */
            ret = wc_Stm32_Aes_Init(aes, &cryptInit, &keyInit);
            if (ret != 0) {
                return ret;
            }

            ret = wolfSSL_CryptHwMutexLock();
            if (ret != 0) {
                return ret;
            }

            /* reset registers to their default values */
            CRYP_DeInit();

            /* set key */
            CRYP_KeyInit(&keyInit);

            /* set iv */
            iv = aes->reg;
            CRYP_IVStructInit(&ivInit);
            ivInit.CRYP_IV0Left  = ByteReverseWord32(iv[0]);
            ivInit.CRYP_IV0Right = ByteReverseWord32(iv[1]);
            ivInit.CRYP_IV1Left  = ByteReverseWord32(iv[2]);
            ivInit.CRYP_IV1Right = ByteReverseWord32(iv[3]);
            CRYP_IVInit(&ivInit);

            /* set direction and mode */
            cryptInit.CRYP_AlgoDir  = CRYP_AlgoDir_Encrypt;
            cryptInit.CRYP_AlgoMode = CRYP_AlgoMode_AES_CTR;
            CRYP_Init(&cryptInit);

            /* enable crypto processor */
            CRYP_Cmd(ENABLE);

            /* flush IN/OUT FIFOs */
            CRYP_FIFOFlush();

            CRYP_DataIn(*(uint32_t*)&in[0]);
            CRYP_DataIn(*(uint32_t*)&in[4]);
            CRYP_DataIn(*(uint32_t*)&in[8]);
            CRYP_DataIn(*(uint32_t*)&in[12]);

            /* wait until the complete message has been processed */
            while (CRYP_GetFlagStatus(CRYP_FLAG_BUSY) != RESET) {}

            *(uint32_t*)&out[0]  = CRYP_DataOut();
            *(uint32_t*)&out[4]  = CRYP_DataOut();
            *(uint32_t*)&out[8]  = CRYP_DataOut();
            *(uint32_t*)&out[12] = CRYP_DataOut();

            /* disable crypto processor */
            CRYP_Cmd(DISABLE);
        #endif /* WOLFSSL_STM32_CUBEMX */

            wolfSSL_CryptHwMutexUnLock();
            return ret;
        }


    #elif defined(WOLFSSL_PIC32MZ_CRYPT)

        #define NEED_AES_CTR_SOFT
        #define XTRANSFORM_AESCTRBLOCK wc_AesCtrEncryptBlock

        int wc_AesCtrEncryptBlock(Aes* aes, byte* out, const byte* in)
        {
            word32 tmpIv[AES_BLOCK_SIZE / sizeof(word32)];
            XMEMCPY(tmpIv, aes->reg, AES_BLOCK_SIZE);
            return wc_Pic32AesCrypt(
                aes->key, aes->keylen, tmpIv, AES_BLOCK_SIZE,
                out, in, AES_BLOCK_SIZE,
                PIC32_ENCRYPTION, PIC32_ALGO_AES, PIC32_CRYPTOALGO_RCTR);
        }

    #elif defined(HAVE_COLDFIRE_SEC)
        #error "Coldfire SEC doesn't currently support AES-CTR mode"

    #elif defined(FREESCALE_LTC)
        int wc_AesCtrEncrypt(Aes* aes, byte* out, const byte* in, word32 sz)
        {
            uint32_t keySize;
            byte *iv, *enc_key;
            byte* tmp;

            if (aes == NULL || out == NULL || in == NULL) {
                return BAD_FUNC_ARG;
            }

            /* consume any unused bytes left in aes->tmp */
            tmp = (byte*)aes->tmp + AES_BLOCK_SIZE - aes->left;
            while (aes->left && sz) {
                *(out++) = *(in++) ^ *(tmp++);
                aes->left--;
                sz--;
            }

            if (sz) {
                iv      = (byte*)aes->reg;
                enc_key = (byte*)aes->key;

                wc_AesGetKeySize(aes, &keySize);

                LTC_AES_CryptCtr(LTC_BASE, in, out, sz,
                    iv, enc_key, keySize, (byte*)aes->tmp,
                    (uint32_t*)&aes->left);
            }

            return 0;
        }

    #elif defined(WOLFSSL_IMX6_CAAM) && !defined(NO_IMX6_CAAM_AES)
        /* implemented in wolfcrypt/src/port/caam/caam_aes.c */

    #elif defined(WOLFSSL_AFALG)
        /* implemented in wolfcrypt/src/port/af_alg/afalg_aes.c */

    #elif defined(WOLFSSL_DEVCRYPTO_AES)
        /* implemented in wolfcrypt/src/port/devcrypt/devcrypto_aes.c */
   
    #elif defined(WOLFSSL_ESP32WROOM32_CRYPT) && \
        !defined(NO_WOLFSSL_ESP32WROOM32_CRYPT_AES)
        /* esp32 doesn't support CRT mode by hw.     */
        /* use aes ecnryption plus sw implementation */
        #define NEED_AES_CTR_SOFT

    #else

        /* Use software based AES counter */
        #define NEED_AES_CTR_SOFT
    #endif

    #ifdef NEED_AES_CTR_SOFT
        /* Increment AES counter */
        static WC_INLINE void IncrementAesCounter(byte* inOutCtr)
        {
            /* in network byte order so start at end and work back */
            int i;
            for (i = AES_BLOCK_SIZE - 1; i >= 0; i--) {
                if (++inOutCtr[i])  /* we're done unless we overflow */
                    return;
            }
        }

        /* Software AES - CTR Encrypt */
        int wc_AesCtrEncrypt(Aes* aes, byte* out, const byte* in, word32 sz)
        {
            byte* tmp;
            byte scratch[AES_BLOCK_SIZE];

            if (aes == NULL || out == NULL || in == NULL) {
                return BAD_FUNC_ARG;
            }

            /* consume any unused bytes left in aes->tmp */
            tmp = (byte*)aes->tmp + AES_BLOCK_SIZE - aes->left;
            while (aes->left && sz) {
               *(out++) = *(in++) ^ *(tmp++);
               aes->left--;
               sz--;
            }

            /* do as many block size ops as possible */
            while (sz >= AES_BLOCK_SIZE) {
            #ifdef XTRANSFORM_AESCTRBLOCK
                XTRANSFORM_AESCTRBLOCK(aes, out, in);
            #else
                wc_AesEncrypt(aes, (byte*)aes->reg, scratch);
                xorbuf(scratch, in, AES_BLOCK_SIZE);
                XMEMCPY(out, scratch, AES_BLOCK_SIZE);
            #endif
                IncrementAesCounter((byte*)aes->reg);

                out += AES_BLOCK_SIZE;
                in  += AES_BLOCK_SIZE;
                sz  -= AES_BLOCK_SIZE;
                aes->left = 0;
            }
            ForceZero(scratch, AES_BLOCK_SIZE);

            /* handle non block size remaining and store unused byte count in left */
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

    #endif /* NEED_AES_CTR_SOFT */

#endif /* WOLFSSL_AES_COUNTER */
#endif /* !WOLFSSL_ARMASM */


/*
 * The IV for AES GCM and CCM, stored in struct Aes's member reg, is comprised
 * of two parts in order:
 *   1. The fixed field which may be 0 or 4 bytes long. In TLS, this is set
 *      to the implicit IV.
 *   2. The explicit IV is generated by wolfCrypt. It needs to be managed
 *      by wolfCrypt to ensure the IV is unique for each call to encrypt.
 * The IV may be a 96-bit random value, or the 32-bit fixed value and a
 * 64-bit set of 0 or random data. The final 32-bits of reg is used as a
 * block counter during the encryption.
 */

#if (defined(HAVE_AESGCM) && !defined(WC_NO_RNG)) || defined(HAVE_AESCCM)
static WC_INLINE void IncCtr(byte* ctr, word32 ctrSz)
{
    int i;
    for (i = ctrSz-1; i >= 0; i--) {
        if (++ctr[i])
            break;
    }
}
#endif /* HAVE_AESGCM || HAVE_AESCCM */


#ifdef HAVE_AESGCM

#if defined(HAVE_COLDFIRE_SEC)
    #error "Coldfire SEC doesn't currently support AES-GCM mode"

#endif

#ifdef WOLFSSL_ARMASM
    /* implementation is located in wolfcrypt/src/port/arm/armv8-aes.c */

#elif defined(WOLFSSL_AFALG)
    /* implemented in wolfcrypt/src/port/afalg/afalg_aes.c */

#elif defined(WOLFSSL_DEVCRYPTO_AES)
    /* implemented in wolfcrypt/src/port/devcrypt/devcrypto_aes.c */

#else /* software + AESNI implementation */

#if !defined(FREESCALE_LTC_AES_GCM)
static WC_INLINE void IncrementGcmCounter(byte* inOutCtr)
{
    int i;

    /* in network byte order so start at end and work back */
    for (i = AES_BLOCK_SIZE - 1; i >= AES_BLOCK_SIZE - CTR_SZ; i--) {
        if (++inOutCtr[i])  /* we're done unless we overflow */
            return;
    }
}
#endif /* !FREESCALE_LTC_AES_GCM */

#if defined(GCM_SMALL) || defined(GCM_TABLE)

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


static WC_INLINE void RIGHTSHIFTX(byte* x)
{
    int i;
    int carryOut = 0;
    int carryIn = 0;
    int borrow = x[15] & 0x01;

    for (i = 0; i < AES_BLOCK_SIZE; i++) {
        carryOut = x[i] & 0x01;
        x[i] = (x[i] >> 1) | (carryIn ? 0x80 : 0);
        carryIn = carryOut;
    }
    if (borrow) x[0] ^= 0xE1;
}

#endif /* defined(GCM_SMALL) || defined(GCM_TABLE) */


#ifdef GCM_TABLE

static void GenerateM0(Aes* aes)
{
    int i, j;
    byte (*m)[AES_BLOCK_SIZE] = aes->M0;

    XMEMCPY(m[128], aes->H, AES_BLOCK_SIZE);

    for (i = 64; i > 0; i /= 2) {
        XMEMCPY(m[i], m[i*2], AES_BLOCK_SIZE);
        RIGHTSHIFTX(m[i]);
    }

    for (i = 2; i < 256; i *= 2) {
        for (j = 1; j < i; j++) {
            XMEMCPY(m[i+j], m[i], AES_BLOCK_SIZE);
            xorbuf(m[i+j], m[j], AES_BLOCK_SIZE);
        }
    }

    XMEMSET(m[0], 0, AES_BLOCK_SIZE);
}

#endif /* GCM_TABLE */

/* Software AES - GCM SetKey */
int wc_AesGcmSetKey(Aes* aes, const byte* key, word32 len)
{
    int  ret;
    byte iv[AES_BLOCK_SIZE];

    #ifdef WOLFSSL_IMX6_CAAM_BLOB
        byte   local[32];
        word32 localSz = 32;

        if (len == (16 + WC_CAAM_BLOB_SZ) ||
          len == (24 + WC_CAAM_BLOB_SZ) ||
          len == (32 + WC_CAAM_BLOB_SZ)) {
            if (wc_caamOpenBlob((byte*)key, len, local, &localSz) != 0) {
                 return BAD_FUNC_ARG;
            }

            /* set local values */
            key = local;
            len = localSz;
        }
    #endif

    if (!((len == 16) || (len == 24) || (len == 32)))
        return BAD_FUNC_ARG;

#ifdef OPENSSL_EXTRA
    if (aes != NULL) {
        XMEMSET(aes->aadH, 0, sizeof(aes->aadH));
        aes->aadLen = 0;
    }
#endif
    XMEMSET(iv, 0, AES_BLOCK_SIZE);
    ret = wc_AesSetKey(aes, key, len, iv, AES_ENCRYPTION);

    #ifdef WOLFSSL_AESNI
        /* AES-NI code generates its own H value. */
        if (haveAESNI)
            return ret;
    #endif /* WOLFSSL_AESNI */

#if !defined(FREESCALE_LTC_AES_GCM)
    if (ret == 0) {
        ret = wolfSSL_CryptHwMutexLock();
        if (ret == 0) {
            wc_AesEncrypt(aes, iv, aes->H);
            wolfSSL_CryptHwMutexUnLock();
        }
    #ifdef GCM_TABLE
        GenerateM0(aes);
    #endif /* GCM_TABLE */
    }
#endif /* FREESCALE_LTC_AES_GCM */

#if defined(WOLFSSL_XILINX_CRYPT)
    wc_AesGcmSetKey_ex(aes, key, len, XSECURE_CSU_AES_KEY_SRC_KUP);
#elif defined(WOLFSSL_AFALG_XILINX_AES)
    wc_AesGcmSetKey_ex(aes, key, len, 0);
#endif

#ifdef WOLF_CRYPTO_CB
    if (aes->devId != INVALID_DEVID) {
        XMEMCPY(aes->devKey, key, len);
    }
#endif

#ifdef WOLFSSL_IMX6_CAAM_BLOB
    ForceZero(local, sizeof(local));
#endif

    return ret;
}


#ifdef WOLFSSL_AESNI

#if defined(USE_INTEL_SPEEDUP)
    #define HAVE_INTEL_AVX1
    #define HAVE_INTEL_AVX2
#endif /* USE_INTEL_SPEEDUP */

#ifndef _MSC_VER

void AES_GCM_encrypt(const unsigned char *in, unsigned char *out,
                     const unsigned char* addt, const unsigned char* ivec,
                     unsigned char *tag, unsigned int nbytes,
                     unsigned int abytes, unsigned int ibytes,
                     unsigned int tbytes, const unsigned char* key, int nr)
                     XASM_LINK("AES_GCM_encrypt");
#ifdef HAVE_INTEL_AVX1
void AES_GCM_encrypt_avx1(const unsigned char *in, unsigned char *out,
                          const unsigned char* addt, const unsigned char* ivec,
                          unsigned char *tag, unsigned int nbytes,
                          unsigned int abytes, unsigned int ibytes,
                          unsigned int tbytes, const unsigned char* key,
                          int nr)
                          XASM_LINK("AES_GCM_encrypt_avx1");
#ifdef HAVE_INTEL_AVX2
void AES_GCM_encrypt_avx2(const unsigned char *in, unsigned char *out,
                          const unsigned char* addt, const unsigned char* ivec,
                          unsigned char *tag, unsigned int nbytes,
                          unsigned int abytes, unsigned int ibytes,
                          unsigned int tbytes, const unsigned char* key,
                          int nr)
                          XASM_LINK("AES_GCM_encrypt_avx2");
#endif /* HAVE_INTEL_AVX2 */
#endif /* HAVE_INTEL_AVX1 */

#ifdef HAVE_AES_DECRYPT
void AES_GCM_decrypt(const unsigned char *in, unsigned char *out,
                     const unsigned char* addt, const unsigned char* ivec,
                     const unsigned char *tag, int nbytes, int abytes,
                     int ibytes, int tbytes, const unsigned char* key, int nr,
                     int* res)
                     XASM_LINK("AES_GCM_decrypt");
#ifdef HAVE_INTEL_AVX1
void AES_GCM_decrypt_avx1(const unsigned char *in, unsigned char *out,
                          const unsigned char* addt, const unsigned char* ivec,
                          const unsigned char *tag, int nbytes, int abytes,
                          int ibytes, int tbytes, const unsigned char* key,
                          int nr, int* res)
                          XASM_LINK("AES_GCM_decrypt_avx1");
#ifdef HAVE_INTEL_AVX2
void AES_GCM_decrypt_avx2(const unsigned char *in, unsigned char *out,
                          const unsigned char* addt, const unsigned char* ivec,
                          const unsigned char *tag, int nbytes, int abytes,
                          int ibytes, int tbytes, const unsigned char* key,
                          int nr, int* res)
                          XASM_LINK("AES_GCM_decrypt_avx2");
#endif /* HAVE_INTEL_AVX2 */
#endif /* HAVE_INTEL_AVX1 */
#endif /* HAVE_AES_DECRYPT */

#else /* _MSC_VER */

#define S(w,z) ((char)((unsigned long long)(w) >> (8*(7-(z))) & 0xFF))
#define M128_INIT(x,y) { S((x),7), S((x),6), S((x),5), S((x),4), \
                         S((x),3), S((x),2), S((x),1), S((x),0), \
                         S((y),7), S((y),6), S((y),5), S((y),4), \
                         S((y),3), S((y),2), S((y),1), S((y),0) }

static const __m128i MOD2_128 =
        M128_INIT(0x1, (long long int)0xc200000000000000UL);


/* See Intel® Carry-Less Multiplication Instruction
 * and its Usage for Computing the GCM Mode White Paper
 * by Shay Gueron, Intel Mobility Group, Israel Development Center;
 * and Michael E. Kounavis, Intel Labs, Circuits and Systems Research */


/* Figure 9. AES-GCM – Encrypt With Single Block Ghash at a Time */

static const __m128i ONE   = M128_INIT(0x0, 0x1);
#ifndef AES_GCM_AESNI_NO_UNROLL
static const __m128i TWO   = M128_INIT(0x0, 0x2);
static const __m128i THREE = M128_INIT(0x0, 0x3);
static const __m128i FOUR  = M128_INIT(0x0, 0x4);
static const __m128i FIVE  = M128_INIT(0x0, 0x5);
static const __m128i SIX   = M128_INIT(0x0, 0x6);
static const __m128i SEVEN = M128_INIT(0x0, 0x7);
static const __m128i EIGHT = M128_INIT(0x0, 0x8);
#endif
static const __m128i BSWAP_EPI64 =
        M128_INIT(0x0001020304050607, 0x08090a0b0c0d0e0f);
static const __m128i BSWAP_MASK =
        M128_INIT(0x08090a0b0c0d0e0f, 0x0001020304050607);


/* The following are for MSC based builds which do not allow
 * inline assembly. Intrinsic functions are used instead. */

#define aes_gcm_calc_iv_12(KEY, ivec, nr, H, Y, T)         \
do                                                         \
{                                                          \
    word32 iv12[4];                                        \
    iv12[0] = *(word32*)&ivec[0];                          \
    iv12[1] = *(word32*)&ivec[4];                          \
    iv12[2] = *(word32*)&ivec[8];                          \
    iv12[3] = 0x01000000;                                  \
    Y = _mm_loadu_si128((__m128i*)iv12);                   \
                                                           \
    /* (Compute E[ZERO, KS] and E[Y0, KS] together */      \
    tmp1 = _mm_load_si128(&KEY[0]);                        \
    tmp2 = _mm_xor_si128(Y, KEY[0]);                       \
    tmp1 = _mm_aesenc_si128(tmp1, KEY[1]);                 \
    tmp2 = _mm_aesenc_si128(tmp2, KEY[1]);                 \
    tmp1 = _mm_aesenc_si128(tmp1, KEY[2]);                 \
    tmp2 = _mm_aesenc_si128(tmp2, KEY[2]);                 \
    tmp1 = _mm_aesenc_si128(tmp1, KEY[3]);                 \
    tmp2 = _mm_aesenc_si128(tmp2, KEY[3]);                 \
    tmp1 = _mm_aesenc_si128(tmp1, KEY[4]);                 \
    tmp2 = _mm_aesenc_si128(tmp2, KEY[4]);                 \
    tmp1 = _mm_aesenc_si128(tmp1, KEY[5]);                 \
    tmp2 = _mm_aesenc_si128(tmp2, KEY[5]);                 \
    tmp1 = _mm_aesenc_si128(tmp1, KEY[6]);                 \
    tmp2 = _mm_aesenc_si128(tmp2, KEY[6]);                 \
    tmp1 = _mm_aesenc_si128(tmp1, KEY[7]);                 \
    tmp2 = _mm_aesenc_si128(tmp2, KEY[7]);                 \
    tmp1 = _mm_aesenc_si128(tmp1, KEY[8]);                 \
    tmp2 = _mm_aesenc_si128(tmp2, KEY[8]);                 \
    tmp1 = _mm_aesenc_si128(tmp1, KEY[9]);                 \
    tmp2 = _mm_aesenc_si128(tmp2, KEY[9]);                 \
    lastKey = KEY[10];                                     \
    if (nr > 10) {                                         \
        tmp1 = _mm_aesenc_si128(tmp1, lastKey);            \
        tmp2 = _mm_aesenc_si128(tmp2, lastKey);            \
        tmp1 = _mm_aesenc_si128(tmp1, KEY[11]);            \
        tmp2 = _mm_aesenc_si128(tmp2, KEY[11]);            \
        lastKey = KEY[12];                                 \
        if (nr > 12) {                                     \
            tmp1 = _mm_aesenc_si128(tmp1, lastKey);        \
            tmp2 = _mm_aesenc_si128(tmp2, lastKey);        \
            tmp1 = _mm_aesenc_si128(tmp1, KEY[13]);        \
            tmp2 = _mm_aesenc_si128(tmp2, KEY[13]);        \
            lastKey = KEY[14];                             \
        }                                                  \
    }                                                      \
    H = _mm_aesenclast_si128(tmp1, lastKey);               \
    T = _mm_aesenclast_si128(tmp2, lastKey);               \
    H = _mm_shuffle_epi8(H, BSWAP_MASK);                   \
}                                                          \
while (0)

#define aes_gcm_calc_iv(KEY, ivec, ibytes, nr, H, Y, T)         \
do                                                              \
{                                                               \
    if (ibytes % 16) {                                          \
        i = ibytes / 16;                                        \
        for (j=0; j < (int)(ibytes%16); j++)                    \
            ((unsigned char*)&last_block)[j] = ivec[i*16+j];    \
    }                                                           \
    tmp1 = _mm_load_si128(&KEY[0]);                             \
    tmp1 = _mm_aesenc_si128(tmp1, KEY[1]);                      \
    tmp1 = _mm_aesenc_si128(tmp1, KEY[2]);                      \
    tmp1 = _mm_aesenc_si128(tmp1, KEY[3]);                      \
    tmp1 = _mm_aesenc_si128(tmp1, KEY[4]);                      \
    tmp1 = _mm_aesenc_si128(tmp1, KEY[5]);                      \
    tmp1 = _mm_aesenc_si128(tmp1, KEY[6]);                      \
    tmp1 = _mm_aesenc_si128(tmp1, KEY[7]);                      \
    tmp1 = _mm_aesenc_si128(tmp1, KEY[8]);                      \
    tmp1 = _mm_aesenc_si128(tmp1, KEY[9]);                      \
    lastKey = KEY[10];                                          \
    if (nr > 10) {                                              \
        tmp1 = _mm_aesenc_si128(tmp1, lastKey);                 \
        tmp1 = _mm_aesenc_si128(tmp1, KEY[11]);                 \
        lastKey = KEY[12];                                      \
        if (nr > 12) {                                          \
            tmp1 = _mm_aesenc_si128(tmp1, lastKey);             \
            tmp1 = _mm_aesenc_si128(tmp1, KEY[13]);             \
            lastKey = KEY[14];                                  \
        }                                                       \
    }                                                           \
    H = _mm_aesenclast_si128(tmp1, lastKey);                    \
    H = _mm_shuffle_epi8(H, BSWAP_MASK);                        \
    Y = _mm_setzero_si128();                                    \
    for (i=0; i < (int)(ibytes/16); i++) {                      \
        tmp1 = _mm_loadu_si128(&((__m128i*)ivec)[i]);           \
        tmp1 = _mm_shuffle_epi8(tmp1, BSWAP_MASK);              \
        Y = _mm_xor_si128(Y, tmp1);                             \
        Y = gfmul_sw(Y, H);                                     \
    }                                                           \
    if (ibytes % 16) {                                          \
        tmp1 = last_block;                                      \
        tmp1 = _mm_shuffle_epi8(tmp1, BSWAP_MASK);              \
        Y = _mm_xor_si128(Y, tmp1);                             \
        Y = gfmul_sw(Y, H);                                     \
    }                                                           \
    tmp1 = _mm_insert_epi64(tmp1, ibytes*8, 0);                 \
    tmp1 = _mm_insert_epi64(tmp1, 0, 1);                        \
    Y = _mm_xor_si128(Y, tmp1);                                 \
    Y = gfmul_sw(Y, H);                                         \
    Y = _mm_shuffle_epi8(Y, BSWAP_MASK); /* Compute E(K, Y0) */ \
    tmp1 = _mm_xor_si128(Y, KEY[0]);                            \
    tmp1 = _mm_aesenc_si128(tmp1, KEY[1]);                      \
    tmp1 = _mm_aesenc_si128(tmp1, KEY[2]);                      \
    tmp1 = _mm_aesenc_si128(tmp1, KEY[3]);                      \
    tmp1 = _mm_aesenc_si128(tmp1, KEY[4]);                      \
    tmp1 = _mm_aesenc_si128(tmp1, KEY[5]);                      \
    tmp1 = _mm_aesenc_si128(tmp1, KEY[6]);                      \
    tmp1 = _mm_aesenc_si128(tmp1, KEY[7]);                      \
    tmp1 = _mm_aesenc_si128(tmp1, KEY[8]);                      \
    tmp1 = _mm_aesenc_si128(tmp1, KEY[9]);                      \
    lastKey = KEY[10];                                          \
    if (nr > 10) {                                              \
        tmp1 = _mm_aesenc_si128(tmp1, lastKey);                 \
        tmp1 = _mm_aesenc_si128(tmp1, KEY[11]);                 \
        lastKey = KEY[12];                                      \
        if (nr > 12) {                                          \
            tmp1 = _mm_aesenc_si128(tmp1, lastKey);             \
            tmp1 = _mm_aesenc_si128(tmp1, KEY[13]);             \
            lastKey = KEY[14];                                  \
        }                                                       \
    }                                                           \
    T = _mm_aesenclast_si128(tmp1, lastKey);                    \
}                                                               \
while (0)

#define AES_ENC_8(j)                       \
    tmp1 = _mm_aesenc_si128(tmp1, KEY[j]); \
    tmp2 = _mm_aesenc_si128(tmp2, KEY[j]); \
    tmp3 = _mm_aesenc_si128(tmp3, KEY[j]); \
    tmp4 = _mm_aesenc_si128(tmp4, KEY[j]); \
    tmp5 = _mm_aesenc_si128(tmp5, KEY[j]); \
    tmp6 = _mm_aesenc_si128(tmp6, KEY[j]); \
    tmp7 = _mm_aesenc_si128(tmp7, KEY[j]); \
    tmp8 = _mm_aesenc_si128(tmp8, KEY[j]);

#define AES_ENC_LAST_8()                                                  \
    tmp1 =_mm_aesenclast_si128(tmp1, lastKey);                            \
    tmp2 =_mm_aesenclast_si128(tmp2, lastKey);                            \
    tmp1 = _mm_xor_si128(tmp1, _mm_loadu_si128(&((__m128i*)in)[i*8+0]));  \
    tmp2 = _mm_xor_si128(tmp2, _mm_loadu_si128(&((__m128i*)in)[i*8+1]));  \
    _mm_storeu_si128(&((__m128i*)out)[i*8+0], tmp1);                      \
    _mm_storeu_si128(&((__m128i*)out)[i*8+1], tmp2);                      \
    tmp3 =_mm_aesenclast_si128(tmp3, lastKey);                            \
    tmp4 =_mm_aesenclast_si128(tmp4, lastKey);                            \
    tmp3 = _mm_xor_si128(tmp3, _mm_loadu_si128(&((__m128i*)in)[i*8+2]));  \
    tmp4 = _mm_xor_si128(tmp4, _mm_loadu_si128(&((__m128i*)in)[i*8+3]));  \
    _mm_storeu_si128(&((__m128i*)out)[i*8+2], tmp3);                      \
    _mm_storeu_si128(&((__m128i*)out)[i*8+3], tmp4);                      \
    tmp5 =_mm_aesenclast_si128(tmp5, lastKey);                            \
    tmp6 =_mm_aesenclast_si128(tmp6, lastKey);                            \
    tmp5 = _mm_xor_si128(tmp5, _mm_loadu_si128(&((__m128i*)in)[i*8+4]));  \
    tmp6 = _mm_xor_si128(tmp6, _mm_loadu_si128(&((__m128i*)in)[i*8+5]));  \
    _mm_storeu_si128(&((__m128i*)out)[i*8+4], tmp5);                      \
    _mm_storeu_si128(&((__m128i*)out)[i*8+5], tmp6);                      \
    tmp7 =_mm_aesenclast_si128(tmp7, lastKey);                            \
    tmp8 =_mm_aesenclast_si128(tmp8, lastKey);                            \
    tmp7 = _mm_xor_si128(tmp7, _mm_loadu_si128(&((__m128i*)in)[i*8+6]));  \
    tmp8 = _mm_xor_si128(tmp8, _mm_loadu_si128(&((__m128i*)in)[i*8+7]));  \
    _mm_storeu_si128(&((__m128i*)out)[i*8+6], tmp7);                      \
    _mm_storeu_si128(&((__m128i*)out)[i*8+7], tmp8);


static __m128i gfmul_sw(__m128i a, __m128i b)
{
    __m128i r, t1, t2, t3, t4, t5, t6, t7;
    t2 = _mm_shuffle_epi32(b, 78);
    t3 = _mm_shuffle_epi32(a, 78);
    t2 = _mm_xor_si128(t2, b);
    t3 = _mm_xor_si128(t3, a);
    t4 = _mm_clmulepi64_si128(b, a, 0x11);
    t1 = _mm_clmulepi64_si128(b, a, 0x00);
    t2 = _mm_clmulepi64_si128(t2, t3, 0x00);
    t2 = _mm_xor_si128(t2, t1);
    t2 = _mm_xor_si128(t2, t4);
    t3 = _mm_slli_si128(t2, 8);
    t2 = _mm_srli_si128(t2, 8);
    t1 = _mm_xor_si128(t1, t3);
    t4 = _mm_xor_si128(t4, t2);

    t5 = _mm_srli_epi32(t1, 31);
    t6 = _mm_srli_epi32(t4, 31);
    t1 = _mm_slli_epi32(t1, 1);
    t4 = _mm_slli_epi32(t4, 1);
    t7 = _mm_srli_si128(t5, 12);
    t5 = _mm_slli_si128(t5, 4);
    t6 = _mm_slli_si128(t6, 4);
    t4 = _mm_or_si128(t4, t7);
    t1 = _mm_or_si128(t1, t5);
    t4 = _mm_or_si128(t4, t6);

    t5 = _mm_slli_epi32(t1, 31);
    t6 = _mm_slli_epi32(t1, 30);
    t7 = _mm_slli_epi32(t1, 25);
    t5 = _mm_xor_si128(t5, t6);
    t5 = _mm_xor_si128(t5, t7);

    t6 = _mm_srli_si128(t5, 4);
    t5 = _mm_slli_si128(t5, 12);
    t1 = _mm_xor_si128(t1, t5);
    t7 = _mm_srli_epi32(t1, 1);
    t3 = _mm_srli_epi32(t1, 2);
    t2 = _mm_srli_epi32(t1, 7);

    t7 = _mm_xor_si128(t7, t3);
    t7 = _mm_xor_si128(t7, t2);
    t7 = _mm_xor_si128(t7, t6);
    t7 = _mm_xor_si128(t7, t1);
    r = _mm_xor_si128(t4, t7);

    return r;
}

static void gfmul_only(__m128i a, __m128i b, __m128i* r0, __m128i* r1)
{
    __m128i t1, t2, t3, t4;

    /* 128 x 128 Carryless Multiply */
    t2 = _mm_shuffle_epi32(b, 78);
    t3 = _mm_shuffle_epi32(a, 78);
    t2 = _mm_xor_si128(t2, b);
    t3 = _mm_xor_si128(t3, a);
    t4 = _mm_clmulepi64_si128(b, a, 0x11);
    t1 = _mm_clmulepi64_si128(b, a, 0x00);
    t2 = _mm_clmulepi64_si128(t2, t3, 0x00);
    t2 = _mm_xor_si128(t2, t1);
    t2 = _mm_xor_si128(t2, t4);
    t3 = _mm_slli_si128(t2, 8);
    t2 = _mm_srli_si128(t2, 8);
    t1 = _mm_xor_si128(t1, t3);
    t4 = _mm_xor_si128(t4, t2);
    *r0 = _mm_xor_si128(t1, *r0);
    *r1 = _mm_xor_si128(t4, *r1);
}

static __m128i gfmul_shl1(__m128i a)
{
    __m128i t1 = a, t2;
    t2 = _mm_srli_epi64(t1, 63);
    t1 = _mm_slli_epi64(t1, 1);
    t2 = _mm_slli_si128(t2, 8);
    t1 = _mm_or_si128(t1, t2);
    /* if (a[1] >> 63) t1 = _mm_xor_si128(t1, MOD2_128); */
    a = _mm_shuffle_epi32(a, 0xff);
    a = _mm_srai_epi32(a, 31);
    a = _mm_and_si128(a, MOD2_128);
    t1 = _mm_xor_si128(t1, a);
    return t1;
}

static __m128i ghash_red(__m128i r0, __m128i r1)
{
    __m128i t2, t3;
    __m128i t5, t6, t7;

    t5 = _mm_slli_epi32(r0, 31);
    t6 = _mm_slli_epi32(r0, 30);
    t7 = _mm_slli_epi32(r0, 25);
    t5 = _mm_xor_si128(t5, t6);
    t5 = _mm_xor_si128(t5, t7);

    t6 = _mm_srli_si128(t5, 4);
    t5 = _mm_slli_si128(t5, 12);
    r0 = _mm_xor_si128(r0, t5);
    t7 = _mm_srli_epi32(r0, 1);
    t3 = _mm_srli_epi32(r0, 2);
    t2 = _mm_srli_epi32(r0, 7);

    t7 = _mm_xor_si128(t7, t3);
    t7 = _mm_xor_si128(t7, t2);
    t7 = _mm_xor_si128(t7, t6);
    t7 = _mm_xor_si128(t7, r0);
    return _mm_xor_si128(r1, t7);
}

static __m128i gfmul_shifted(__m128i a, __m128i b)
{
    __m128i t0 = _mm_setzero_si128(), t1 = _mm_setzero_si128();
    gfmul_only(a, b, &t0, &t1);
    return ghash_red(t0, t1);
}

#ifndef AES_GCM_AESNI_NO_UNROLL
static __m128i gfmul8(__m128i a1, __m128i a2, __m128i a3, __m128i a4,
                      __m128i a5, __m128i a6, __m128i a7, __m128i a8,
                      __m128i b1, __m128i b2, __m128i b3, __m128i b4,
                      __m128i b5, __m128i b6, __m128i b7, __m128i b8)
{
    __m128i t0 = _mm_setzero_si128(), t1 = _mm_setzero_si128();
    gfmul_only(a1, b8, &t0, &t1);
    gfmul_only(a2, b7, &t0, &t1);
    gfmul_only(a3, b6, &t0, &t1);
    gfmul_only(a4, b5, &t0, &t1);
    gfmul_only(a5, b4, &t0, &t1);
    gfmul_only(a6, b3, &t0, &t1);
    gfmul_only(a7, b2, &t0, &t1);
    gfmul_only(a8, b1, &t0, &t1);
    return ghash_red(t0, t1);
}
#endif


static void AES_GCM_encrypt(const unsigned char *in,
                              unsigned char *out,
                              const unsigned char* addt,
                              const unsigned char* ivec,
                              unsigned char *tag, unsigned int nbytes,
                              unsigned int abytes, unsigned int ibytes,
                              unsigned int tbytes,
                              const unsigned char* key, int nr)
{
    int i, j ,k;
    __m128i ctr1;
    __m128i H, Y, T;
    __m128i X = _mm_setzero_si128();
    __m128i *KEY = (__m128i*)key, lastKey;
    __m128i last_block = _mm_setzero_si128();
    __m128i tmp1, tmp2;
#ifndef AES_GCM_AESNI_NO_UNROLL
    __m128i HT[8];
    __m128i r0, r1;
    __m128i XV;
    __m128i tmp3, tmp4, tmp5, tmp6, tmp7, tmp8;
#endif

    if (ibytes == GCM_NONCE_MID_SZ)
        aes_gcm_calc_iv_12(KEY, ivec, nr, H, Y, T);
    else
        aes_gcm_calc_iv(KEY, ivec, ibytes, nr, H, Y, T);

    for (i=0; i < (int)(abytes/16); i++) {
        tmp1 = _mm_loadu_si128(&((__m128i*)addt)[i]);
        tmp1 = _mm_shuffle_epi8(tmp1, BSWAP_MASK);
        X = _mm_xor_si128(X, tmp1);
        X = gfmul_sw(X, H);
    }
    if (abytes%16) {
        last_block = _mm_setzero_si128();
        for (j=0; j < (int)(abytes%16); j++)
            ((unsigned char*)&last_block)[j] = addt[i*16+j];
        tmp1 = last_block;
        tmp1 = _mm_shuffle_epi8(tmp1, BSWAP_MASK);
        X = _mm_xor_si128(X, tmp1);
        X = gfmul_sw(X, H);
    }
    tmp1 = _mm_shuffle_epi8(Y, BSWAP_EPI64);
    ctr1 = _mm_add_epi32(tmp1, ONE);
    H = gfmul_shl1(H);

#ifndef AES_GCM_AESNI_NO_UNROLL
    i = 0;
    if (nbytes >= 16*8) {
        HT[0] = H;
        HT[1] = gfmul_shifted(H, H);
        HT[2] = gfmul_shifted(H, HT[1]);
        HT[3] = gfmul_shifted(HT[1], HT[1]);
        HT[4] = gfmul_shifted(HT[1], HT[2]);
        HT[5] = gfmul_shifted(HT[2], HT[2]);
        HT[6] = gfmul_shifted(HT[2], HT[3]);
        HT[7] = gfmul_shifted(HT[3], HT[3]);

        tmp1 = _mm_shuffle_epi8(ctr1, BSWAP_EPI64);
        tmp2 = _mm_add_epi32(ctr1, ONE);
        tmp2 = _mm_shuffle_epi8(tmp2, BSWAP_EPI64);
        tmp3 = _mm_add_epi32(ctr1, TWO);
        tmp3 = _mm_shuffle_epi8(tmp3, BSWAP_EPI64);
        tmp4 = _mm_add_epi32(ctr1, THREE);
        tmp4 = _mm_shuffle_epi8(tmp4, BSWAP_EPI64);
        tmp5 = _mm_add_epi32(ctr1, FOUR);
        tmp5 = _mm_shuffle_epi8(tmp5, BSWAP_EPI64);
        tmp6 = _mm_add_epi32(ctr1, FIVE);
        tmp6 = _mm_shuffle_epi8(tmp6, BSWAP_EPI64);
        tmp7 = _mm_add_epi32(ctr1, SIX);
        tmp7 = _mm_shuffle_epi8(tmp7, BSWAP_EPI64);
        tmp8 = _mm_add_epi32(ctr1, SEVEN);
        tmp8 = _mm_shuffle_epi8(tmp8, BSWAP_EPI64);
        ctr1 = _mm_add_epi32(ctr1, EIGHT);
        tmp1 =_mm_xor_si128(tmp1, KEY[0]);
        tmp2 =_mm_xor_si128(tmp2, KEY[0]);
        tmp3 =_mm_xor_si128(tmp3, KEY[0]);
        tmp4 =_mm_xor_si128(tmp4, KEY[0]);
        tmp5 =_mm_xor_si128(tmp5, KEY[0]);
        tmp6 =_mm_xor_si128(tmp6, KEY[0]);
        tmp7 =_mm_xor_si128(tmp7, KEY[0]);
        tmp8 =_mm_xor_si128(tmp8, KEY[0]);
        AES_ENC_8(1);
        AES_ENC_8(2);
        AES_ENC_8(3);
        AES_ENC_8(4);
        AES_ENC_8(5);
        AES_ENC_8(6);
        AES_ENC_8(7);
        AES_ENC_8(8);
        AES_ENC_8(9);
        lastKey = KEY[10];
        if (nr > 10) {
            AES_ENC_8(10);
            AES_ENC_8(11);
            lastKey = KEY[12];
            if (nr > 12) {
                AES_ENC_8(12);
                AES_ENC_8(13);
                lastKey = KEY[14];
            }
        }
        AES_ENC_LAST_8();

        for (i=1; i < (int)(nbytes/16/8); i++) {
                r0 = _mm_setzero_si128();
                r1 = _mm_setzero_si128();
            tmp1 = _mm_shuffle_epi8(ctr1, BSWAP_EPI64);
            tmp2 = _mm_add_epi32(ctr1, ONE);
            tmp2 = _mm_shuffle_epi8(tmp2, BSWAP_EPI64);
            tmp3 = _mm_add_epi32(ctr1, TWO);
            tmp3 = _mm_shuffle_epi8(tmp3, BSWAP_EPI64);
            tmp4 = _mm_add_epi32(ctr1, THREE);
            tmp4 = _mm_shuffle_epi8(tmp4, BSWAP_EPI64);
            tmp5 = _mm_add_epi32(ctr1, FOUR);
            tmp5 = _mm_shuffle_epi8(tmp5, BSWAP_EPI64);
            tmp6 = _mm_add_epi32(ctr1, FIVE);
            tmp6 = _mm_shuffle_epi8(tmp6, BSWAP_EPI64);
            tmp7 = _mm_add_epi32(ctr1, SIX);
            tmp7 = _mm_shuffle_epi8(tmp7, BSWAP_EPI64);
            tmp8 = _mm_add_epi32(ctr1, SEVEN);
            tmp8 = _mm_shuffle_epi8(tmp8, BSWAP_EPI64);
            ctr1 = _mm_add_epi32(ctr1, EIGHT);
            tmp1 =_mm_xor_si128(tmp1, KEY[0]);
            tmp2 =_mm_xor_si128(tmp2, KEY[0]);
            tmp3 =_mm_xor_si128(tmp3, KEY[0]);
            tmp4 =_mm_xor_si128(tmp4, KEY[0]);
            tmp5 =_mm_xor_si128(tmp5, KEY[0]);
            tmp6 =_mm_xor_si128(tmp6, KEY[0]);
            tmp7 =_mm_xor_si128(tmp7, KEY[0]);
            tmp8 =_mm_xor_si128(tmp8, KEY[0]);
                /* 128 x 128 Carryless Multiply */
                XV = _mm_loadu_si128(&((__m128i*)out)[(i-1)*8+0]);
                XV = _mm_shuffle_epi8(XV, BSWAP_MASK);
                XV = _mm_xor_si128(XV, X);
                gfmul_only(XV, HT[7], &r0, &r1);
            tmp1 = _mm_aesenc_si128(tmp1, KEY[1]);
            tmp2 = _mm_aesenc_si128(tmp2, KEY[1]);
            tmp3 = _mm_aesenc_si128(tmp3, KEY[1]);
            tmp4 = _mm_aesenc_si128(tmp4, KEY[1]);
            tmp5 = _mm_aesenc_si128(tmp5, KEY[1]);
            tmp6 = _mm_aesenc_si128(tmp6, KEY[1]);
            tmp7 = _mm_aesenc_si128(tmp7, KEY[1]);
            tmp8 = _mm_aesenc_si128(tmp8, KEY[1]);
                /* 128 x 128 Carryless Multiply */
                XV = _mm_loadu_si128(&((__m128i*)out)[(i-1)*8+1]);
                XV = _mm_shuffle_epi8(XV, BSWAP_MASK);
                gfmul_only(XV, HT[6], &r0, &r1);
            tmp1 = _mm_aesenc_si128(tmp1, KEY[2]);
            tmp2 = _mm_aesenc_si128(tmp2, KEY[2]);
            tmp3 = _mm_aesenc_si128(tmp3, KEY[2]);
            tmp4 = _mm_aesenc_si128(tmp4, KEY[2]);
            tmp5 = _mm_aesenc_si128(tmp5, KEY[2]);
            tmp6 = _mm_aesenc_si128(tmp6, KEY[2]);
            tmp7 = _mm_aesenc_si128(tmp7, KEY[2]);
            tmp8 = _mm_aesenc_si128(tmp8, KEY[2]);
                /* 128 x 128 Carryless Multiply */
                XV = _mm_loadu_si128(&((__m128i*)out)[(i-1)*8+2]);
                XV = _mm_shuffle_epi8(XV, BSWAP_MASK);
                gfmul_only(XV, HT[5], &r0, &r1);
            tmp1 = _mm_aesenc_si128(tmp1, KEY[3]);
            tmp2 = _mm_aesenc_si128(tmp2, KEY[3]);
            tmp3 = _mm_aesenc_si128(tmp3, KEY[3]);
            tmp4 = _mm_aesenc_si128(tmp4, KEY[3]);
            tmp5 = _mm_aesenc_si128(tmp5, KEY[3]);
            tmp6 = _mm_aesenc_si128(tmp6, KEY[3]);
            tmp7 = _mm_aesenc_si128(tmp7, KEY[3]);
            tmp8 = _mm_aesenc_si128(tmp8, KEY[3]);
                /* 128 x 128 Carryless Multiply */
                XV = _mm_loadu_si128(&((__m128i*)out)[(i-1)*8+3]);
                XV = _mm_shuffle_epi8(XV, BSWAP_MASK);
                gfmul_only(XV, HT[4], &r0, &r1);
            tmp1 = _mm_aesenc_si128(tmp1, KEY[4]);
            tmp2 = _mm_aesenc_si128(tmp2, KEY[4]);
            tmp3 = _mm_aesenc_si128(tmp3, KEY[4]);
            tmp4 = _mm_aesenc_si128(tmp4, KEY[4]);
            tmp5 = _mm_aesenc_si128(tmp5, KEY[4]);
            tmp6 = _mm_aesenc_si128(tmp6, KEY[4]);
            tmp7 = _mm_aesenc_si128(tmp7, KEY[4]);
            tmp8 = _mm_aesenc_si128(tmp8, KEY[4]);
                /* 128 x 128 Carryless Multiply */
                XV = _mm_loadu_si128(&((__m128i*)out)[(i-1)*8+4]);
                XV = _mm_shuffle_epi8(XV, BSWAP_MASK);
                gfmul_only(XV, HT[3], &r0, &r1);
            tmp1 = _mm_aesenc_si128(tmp1, KEY[5]);
            tmp2 = _mm_aesenc_si128(tmp2, KEY[5]);
            tmp3 = _mm_aesenc_si128(tmp3, KEY[5]);
            tmp4 = _mm_aesenc_si128(tmp4, KEY[5]);
            tmp5 = _mm_aesenc_si128(tmp5, KEY[5]);
            tmp6 = _mm_aesenc_si128(tmp6, KEY[5]);
            tmp7 = _mm_aesenc_si128(tmp7, KEY[5]);
            tmp8 = _mm_aesenc_si128(tmp8, KEY[5]);
                /* 128 x 128 Carryless Multiply */
                XV = _mm_loadu_si128(&((__m128i*)out)[(i-1)*8+5]);
                XV = _mm_shuffle_epi8(XV, BSWAP_MASK);
                gfmul_only(XV, HT[2], &r0, &r1);
            tmp1 = _mm_aesenc_si128(tmp1, KEY[6]);
            tmp2 = _mm_aesenc_si128(tmp2, KEY[6]);
            tmp3 = _mm_aesenc_si128(tmp3, KEY[6]);
            tmp4 = _mm_aesenc_si128(tmp4, KEY[6]);
            tmp5 = _mm_aesenc_si128(tmp5, KEY[6]);
            tmp6 = _mm_aesenc_si128(tmp6, KEY[6]);
            tmp7 = _mm_aesenc_si128(tmp7, KEY[6]);
            tmp8 = _mm_aesenc_si128(tmp8, KEY[6]);
                /* 128 x 128 Carryless Multiply */
                XV = _mm_loadu_si128(&((__m128i*)out)[(i-1)*8+6]);
                XV = _mm_shuffle_epi8(XV, BSWAP_MASK);
                gfmul_only(XV, HT[1], &r0, &r1);
            tmp1 = _mm_aesenc_si128(tmp1, KEY[7]);
            tmp2 = _mm_aesenc_si128(tmp2, KEY[7]);
            tmp3 = _mm_aesenc_si128(tmp3, KEY[7]);
            tmp4 = _mm_aesenc_si128(tmp4, KEY[7]);
            tmp5 = _mm_aesenc_si128(tmp5, KEY[7]);
            tmp6 = _mm_aesenc_si128(tmp6, KEY[7]);
            tmp7 = _mm_aesenc_si128(tmp7, KEY[7]);
            tmp8 = _mm_aesenc_si128(tmp8, KEY[7]);
                /* 128 x 128 Carryless Multiply */
                XV = _mm_loadu_si128(&((__m128i*)out)[(i-1)*8+7]);
                XV = _mm_shuffle_epi8(XV, BSWAP_MASK);
                gfmul_only(XV, HT[0], &r0, &r1);
            tmp1 = _mm_aesenc_si128(tmp1, KEY[8]);
            tmp2 = _mm_aesenc_si128(tmp2, KEY[8]);
            tmp3 = _mm_aesenc_si128(tmp3, KEY[8]);
            tmp4 = _mm_aesenc_si128(tmp4, KEY[8]);
            tmp5 = _mm_aesenc_si128(tmp5, KEY[8]);
            tmp6 = _mm_aesenc_si128(tmp6, KEY[8]);
            tmp7 = _mm_aesenc_si128(tmp7, KEY[8]);
            tmp8 = _mm_aesenc_si128(tmp8, KEY[8]);
                /* Reduction */
                X = ghash_red(r0, r1);
            tmp1 = _mm_aesenc_si128(tmp1, KEY[9]);
            tmp2 = _mm_aesenc_si128(tmp2, KEY[9]);
            tmp3 = _mm_aesenc_si128(tmp3, KEY[9]);
            tmp4 = _mm_aesenc_si128(tmp4, KEY[9]);
            tmp5 = _mm_aesenc_si128(tmp5, KEY[9]);
            tmp6 = _mm_aesenc_si128(tmp6, KEY[9]);
            tmp7 = _mm_aesenc_si128(tmp7, KEY[9]);
            tmp8 = _mm_aesenc_si128(tmp8, KEY[9]);
            lastKey = KEY[10];
            if (nr > 10) {
                tmp1 = _mm_aesenc_si128(tmp1, KEY[10]);
                tmp2 = _mm_aesenc_si128(tmp2, KEY[10]);
                tmp3 = _mm_aesenc_si128(tmp3, KEY[10]);
                tmp4 = _mm_aesenc_si128(tmp4, KEY[10]);
                tmp5 = _mm_aesenc_si128(tmp5, KEY[10]);
                tmp6 = _mm_aesenc_si128(tmp6, KEY[10]);
                tmp7 = _mm_aesenc_si128(tmp7, KEY[10]);
                tmp8 = _mm_aesenc_si128(tmp8, KEY[10]);
                tmp1 = _mm_aesenc_si128(tmp1, KEY[11]);
                tmp2 = _mm_aesenc_si128(tmp2, KEY[11]);
                tmp3 = _mm_aesenc_si128(tmp3, KEY[11]);
                tmp4 = _mm_aesenc_si128(tmp4, KEY[11]);
                tmp5 = _mm_aesenc_si128(tmp5, KEY[11]);
                tmp6 = _mm_aesenc_si128(tmp6, KEY[11]);
                tmp7 = _mm_aesenc_si128(tmp7, KEY[11]);
                tmp8 = _mm_aesenc_si128(tmp8, KEY[11]);
                lastKey = KEY[12];
                if (nr > 12) {
                    tmp1 = _mm_aesenc_si128(tmp1, KEY[12]);
                    tmp2 = _mm_aesenc_si128(tmp2, KEY[12]);
                    tmp3 = _mm_aesenc_si128(tmp3, KEY[12]);
                    tmp4 = _mm_aesenc_si128(tmp4, KEY[12]);
                    tmp5 = _mm_aesenc_si128(tmp5, KEY[12]);
                    tmp6 = _mm_aesenc_si128(tmp6, KEY[12]);
                    tmp7 = _mm_aesenc_si128(tmp7, KEY[12]);
                    tmp8 = _mm_aesenc_si128(tmp8, KEY[12]);
                    tmp1 = _mm_aesenc_si128(tmp1, KEY[13]);
                    tmp2 = _mm_aesenc_si128(tmp2, KEY[13]);
                    tmp3 = _mm_aesenc_si128(tmp3, KEY[13]);
                    tmp4 = _mm_aesenc_si128(tmp4, KEY[13]);
                    tmp5 = _mm_aesenc_si128(tmp5, KEY[13]);
                    tmp6 = _mm_aesenc_si128(tmp6, KEY[13]);
                    tmp7 = _mm_aesenc_si128(tmp7, KEY[13]);
                    tmp8 = _mm_aesenc_si128(tmp8, KEY[13]);
                    lastKey = KEY[14];
                }
            }
            AES_ENC_LAST_8();
        }

        tmp1 = _mm_shuffle_epi8(tmp1, BSWAP_MASK);
        tmp2 = _mm_shuffle_epi8(tmp2, BSWAP_MASK);
        tmp3 = _mm_shuffle_epi8(tmp3, BSWAP_MASK);
        tmp4 = _mm_shuffle_epi8(tmp4, BSWAP_MASK);
        tmp5 = _mm_shuffle_epi8(tmp5, BSWAP_MASK);
        tmp6 = _mm_shuffle_epi8(tmp6, BSWAP_MASK);
        tmp7 = _mm_shuffle_epi8(tmp7, BSWAP_MASK);
        tmp8 = _mm_shuffle_epi8(tmp8, BSWAP_MASK);
        tmp1 = _mm_xor_si128(X, tmp1);
        X = gfmul8(tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7, tmp8,
                   HT[0], HT[1], HT[2], HT[3], HT[4], HT[5], HT[6], HT[7]);
    }
    for (k = i*8; k < (int)(nbytes/16); k++) {
        tmp1 = _mm_shuffle_epi8(ctr1, BSWAP_EPI64);
        ctr1 = _mm_add_epi32(ctr1, ONE);
        tmp1 = _mm_xor_si128(tmp1, KEY[0]);
        tmp1 = _mm_aesenc_si128(tmp1, KEY[1]);
        tmp1 = _mm_aesenc_si128(tmp1, KEY[2]);
        tmp1 = _mm_aesenc_si128(tmp1, KEY[3]);
        tmp1 = _mm_aesenc_si128(tmp1, KEY[4]);
        tmp1 = _mm_aesenc_si128(tmp1, KEY[5]);
        tmp1 = _mm_aesenc_si128(tmp1, KEY[6]);
        tmp1 = _mm_aesenc_si128(tmp1, KEY[7]);
        tmp1 = _mm_aesenc_si128(tmp1, KEY[8]);
        tmp1 = _mm_aesenc_si128(tmp1, KEY[9]);
        lastKey = KEY[10];
        if (nr > 10) {
            tmp1 = _mm_aesenc_si128(tmp1, lastKey);
            tmp1 = _mm_aesenc_si128(tmp1, KEY[11]);
            lastKey = KEY[12];
            if (nr > 12) {
                tmp1 = _mm_aesenc_si128(tmp1, lastKey);
                tmp1 = _mm_aesenc_si128(tmp1, KEY[13]);
                lastKey = KEY[14];
            }
        }
        tmp1 = _mm_aesenclast_si128(tmp1, lastKey);
        tmp1 = _mm_xor_si128(tmp1, _mm_loadu_si128(&((__m128i*)in)[k]));
        _mm_storeu_si128(&((__m128i*)out)[k], tmp1);
        tmp1 = _mm_shuffle_epi8(tmp1, BSWAP_MASK);
        X =_mm_xor_si128(X, tmp1);
        X = gfmul_shifted(X, H);
    }
#else /* AES_GCM_AESNI_NO_UNROLL */
    for (k = 0; k < (int)(nbytes/16) && k < 1; k++) {
        tmp1 = _mm_shuffle_epi8(ctr1, BSWAP_EPI64);
        ctr1 = _mm_add_epi32(ctr1, ONE);
        tmp1 = _mm_xor_si128(tmp1, KEY[0]);
        tmp1 = _mm_aesenc_si128(tmp1, KEY[1]);
        tmp1 = _mm_aesenc_si128(tmp1, KEY[2]);
        tmp1 = _mm_aesenc_si128(tmp1, KEY[3]);
        tmp1 = _mm_aesenc_si128(tmp1, KEY[4]);
        tmp1 = _mm_aesenc_si128(tmp1, KEY[5]);
        tmp1 = _mm_aesenc_si128(tmp1, KEY[6]);
        tmp1 = _mm_aesenc_si128(tmp1, KEY[7]);
        tmp1 = _mm_aesenc_si128(tmp1, KEY[8]);
        tmp1 = _mm_aesenc_si128(tmp1, KEY[9]);
        lastKey = KEY[10];
        if (nr > 10) {
            tmp1 = _mm_aesenc_si128(tmp1, lastKey);
            tmp1 = _mm_aesenc_si128(tmp1, KEY[11]);
            lastKey = KEY[12];
            if (nr > 12) {
                tmp1 = _mm_aesenc_si128(tmp1, lastKey);
                tmp1 = _mm_aesenc_si128(tmp1, KEY[13]);
                lastKey = KEY[14];
            }
        }
        tmp1 = _mm_aesenclast_si128(tmp1, lastKey);
        tmp1 = _mm_xor_si128(tmp1, _mm_loadu_si128(&((__m128i*)in)[k]));
        _mm_storeu_si128(&((__m128i*)out)[k], tmp1);
        tmp1 = _mm_shuffle_epi8(tmp1, BSWAP_MASK);
        X =_mm_xor_si128(X, tmp1);
    }
    for (; k < (int)(nbytes/16); k++) {
        tmp1 = _mm_shuffle_epi8(ctr1, BSWAP_EPI64);
        ctr1 = _mm_add_epi32(ctr1, ONE);
        tmp1 = _mm_xor_si128(tmp1, KEY[0]);
        tmp1 = _mm_aesenc_si128(tmp1, KEY[1]);
        tmp1 = _mm_aesenc_si128(tmp1, KEY[2]);
        tmp1 = _mm_aesenc_si128(tmp1, KEY[3]);
        tmp1 = _mm_aesenc_si128(tmp1, KEY[4]);
        tmp1 = _mm_aesenc_si128(tmp1, KEY[5]);
        tmp1 = _mm_aesenc_si128(tmp1, KEY[6]);
        tmp1 = _mm_aesenc_si128(tmp1, KEY[7]);
        tmp1 = _mm_aesenc_si128(tmp1, KEY[8]);
        tmp1 = _mm_aesenc_si128(tmp1, KEY[9]);
        X = gfmul_shifted(X, H);
        lastKey = KEY[10];
        if (nr > 10) {
            tmp1 = _mm_aesenc_si128(tmp1, lastKey);
            tmp1 = _mm_aesenc_si128(tmp1, KEY[11]);
            lastKey = KEY[12];
            if (nr > 12) {
                tmp1 = _mm_aesenc_si128(tmp1, lastKey);
                tmp1 = _mm_aesenc_si128(tmp1, KEY[13]);
                lastKey = KEY[14];
            }
        }
        tmp1 = _mm_aesenclast_si128(tmp1, lastKey);
        tmp1 = _mm_xor_si128(tmp1, _mm_loadu_si128(&((__m128i*)in)[k]));
        _mm_storeu_si128(&((__m128i*)out)[k], tmp1);
        tmp1 = _mm_shuffle_epi8(tmp1, BSWAP_MASK);
        X =_mm_xor_si128(X, tmp1);
    }
    if (k > 0) {
        X = gfmul_shifted(X, H);
    }
#endif /* AES_GCM_AESNI_NO_UNROLL */

    /* If one partial block remains */
    if (nbytes % 16) {
        tmp1 = _mm_shuffle_epi8(ctr1, BSWAP_EPI64);
        tmp1 = _mm_xor_si128(tmp1, KEY[0]);
        tmp1 = _mm_aesenc_si128(tmp1, KEY[1]);
        tmp1 = _mm_aesenc_si128(tmp1, KEY[2]);
        tmp1 = _mm_aesenc_si128(tmp1, KEY[3]);
        tmp1 = _mm_aesenc_si128(tmp1, KEY[4]);
        tmp1 = _mm_aesenc_si128(tmp1, KEY[5]);
        tmp1 = _mm_aesenc_si128(tmp1, KEY[6]);
        tmp1 = _mm_aesenc_si128(tmp1, KEY[7]);
        tmp1 = _mm_aesenc_si128(tmp1, KEY[8]);
        tmp1 = _mm_aesenc_si128(tmp1, KEY[9]);
        lastKey = KEY[10];
        if (nr > 10) {
            tmp1 = _mm_aesenc_si128(tmp1, lastKey);
            tmp1 = _mm_aesenc_si128(tmp1, KEY[11]);
            lastKey = KEY[12];
            if (nr > 12) {
                tmp1 = _mm_aesenc_si128(tmp1, lastKey);
                tmp1 = _mm_aesenc_si128(tmp1, KEY[13]);
                lastKey = KEY[14];
            }
        }
        tmp1 = _mm_aesenclast_si128(tmp1, lastKey);
        last_block = tmp1;
        for (j=0; j < (int)(nbytes%16); j++)
            ((unsigned char*)&last_block)[j] = in[k*16+j];
        tmp1 = _mm_xor_si128(tmp1, last_block);
        last_block = tmp1;
        for (j=0; j < (int)(nbytes%16); j++)
            out[k*16+j] = ((unsigned char*)&last_block)[j];
        tmp1 = last_block;
        tmp1 = _mm_shuffle_epi8(tmp1, BSWAP_MASK);
        X =_mm_xor_si128(X, tmp1);
        X = gfmul_shifted(X, H);
    }
    tmp1 = _mm_insert_epi64(tmp1, nbytes*8, 0);
    tmp1 = _mm_insert_epi64(tmp1, abytes*8, 1);
    X = _mm_xor_si128(X, tmp1);
    X = gfmul_shifted(X, H);
    X = _mm_shuffle_epi8(X, BSWAP_MASK);
    T = _mm_xor_si128(X, T);
    /*_mm_storeu_si128((__m128i*)tag, T);*/
    XMEMCPY(tag, &T, tbytes);
}

#ifdef HAVE_AES_DECRYPT

static void AES_GCM_decrypt(const unsigned char *in,
                           unsigned char *out,
                           const unsigned char* addt,
                           const unsigned char* ivec,
                           const unsigned char *tag, int nbytes, int abytes,
                           int ibytes, word32 tbytes, const unsigned char* key,
                           int nr, int* res)
{
    int i, j ,k;
    __m128i H, Y, T;
    __m128i *KEY = (__m128i*)key, lastKey;
    __m128i ctr1;
    __m128i last_block = _mm_setzero_si128();
    __m128i X = _mm_setzero_si128();
    __m128i tmp1, tmp2, XV;
#ifndef AES_GCM_AESNI_NO_UNROLL
    __m128i HT[8];
    __m128i r0, r1;
    __m128i tmp3, tmp4, tmp5, tmp6, tmp7, tmp8;
#endif /* AES_GCM_AESNI_NO_UNROLL */

    if (ibytes == GCM_NONCE_MID_SZ)
        aes_gcm_calc_iv_12(KEY, ivec, nr, H, Y, T);
    else
        aes_gcm_calc_iv(KEY, ivec, ibytes, nr, H, Y, T);

    for (i=0; i<abytes/16; i++) {
        tmp1 = _mm_loadu_si128(&((__m128i*)addt)[i]);
        tmp1 = _mm_shuffle_epi8(tmp1, BSWAP_MASK);
        X = _mm_xor_si128(X, tmp1);
        X = gfmul_sw(X, H);
    }
    if (abytes%16) {
        last_block = _mm_setzero_si128();
        for (j=0; j<abytes%16; j++)
            ((unsigned char*)&last_block)[j] = addt[i*16+j];
        tmp1 = last_block;
        tmp1 = _mm_shuffle_epi8(tmp1, BSWAP_MASK);
        X = _mm_xor_si128(X, tmp1);
        X = gfmul_sw(X, H);
    }

    tmp1 = _mm_shuffle_epi8(Y, BSWAP_EPI64);
    ctr1 = _mm_add_epi32(tmp1, ONE);
    H = gfmul_shl1(H);
    i = 0;

#ifndef AES_GCM_AESNI_NO_UNROLL

    if (0 < nbytes/16/8) {
        HT[0] = H;
        HT[1] = gfmul_shifted(H, H);
        HT[2] = gfmul_shifted(H, HT[1]);
        HT[3] = gfmul_shifted(HT[1], HT[1]);
        HT[4] = gfmul_shifted(HT[1], HT[2]);
        HT[5] = gfmul_shifted(HT[2], HT[2]);
        HT[6] = gfmul_shifted(HT[2], HT[3]);
        HT[7] = gfmul_shifted(HT[3], HT[3]);

        for (; i < nbytes/16/8; i++) {
                r0 = _mm_setzero_si128();
                r1 = _mm_setzero_si128();

            tmp1 = _mm_shuffle_epi8(ctr1, BSWAP_EPI64);
            tmp2 = _mm_add_epi32(ctr1, ONE);
            tmp2 = _mm_shuffle_epi8(tmp2, BSWAP_EPI64);
            tmp3 = _mm_add_epi32(ctr1, TWO);
            tmp3 = _mm_shuffle_epi8(tmp3, BSWAP_EPI64);
            tmp4 = _mm_add_epi32(ctr1, THREE);
            tmp4 = _mm_shuffle_epi8(tmp4, BSWAP_EPI64);
            tmp5 = _mm_add_epi32(ctr1, FOUR);
            tmp5 = _mm_shuffle_epi8(tmp5, BSWAP_EPI64);
            tmp6 = _mm_add_epi32(ctr1, FIVE);
            tmp6 = _mm_shuffle_epi8(tmp6, BSWAP_EPI64);
            tmp7 = _mm_add_epi32(ctr1, SIX);
            tmp7 = _mm_shuffle_epi8(tmp7, BSWAP_EPI64);
            tmp8 = _mm_add_epi32(ctr1, SEVEN);
            tmp8 = _mm_shuffle_epi8(tmp8, BSWAP_EPI64);
            ctr1 = _mm_add_epi32(ctr1, EIGHT);
            tmp1 =_mm_xor_si128(tmp1, KEY[0]);
            tmp2 =_mm_xor_si128(tmp2, KEY[0]);
            tmp3 =_mm_xor_si128(tmp3, KEY[0]);
            tmp4 =_mm_xor_si128(tmp4, KEY[0]);
            tmp5 =_mm_xor_si128(tmp5, KEY[0]);
            tmp6 =_mm_xor_si128(tmp6, KEY[0]);
            tmp7 =_mm_xor_si128(tmp7, KEY[0]);
            tmp8 =_mm_xor_si128(tmp8, KEY[0]);
                /* 128 x 128 Carryless Multiply */
                XV = _mm_loadu_si128(&((__m128i*)in)[i*8+0]);
                XV = _mm_shuffle_epi8(XV, BSWAP_MASK);
                XV = _mm_xor_si128(XV, X);
                gfmul_only(XV, HT[7], &r0, &r1);
            tmp1 = _mm_aesenc_si128(tmp1, KEY[1]);
            tmp2 = _mm_aesenc_si128(tmp2, KEY[1]);
            tmp3 = _mm_aesenc_si128(tmp3, KEY[1]);
            tmp4 = _mm_aesenc_si128(tmp4, KEY[1]);
            tmp5 = _mm_aesenc_si128(tmp5, KEY[1]);
            tmp6 = _mm_aesenc_si128(tmp6, KEY[1]);
            tmp7 = _mm_aesenc_si128(tmp7, KEY[1]);
            tmp8 = _mm_aesenc_si128(tmp8, KEY[1]);
                /* 128 x 128 Carryless Multiply */
                XV = _mm_loadu_si128(&((__m128i*)in)[i*8+1]);
                XV = _mm_shuffle_epi8(XV, BSWAP_MASK);
                gfmul_only(XV, HT[6], &r0, &r1);
            tmp1 = _mm_aesenc_si128(tmp1, KEY[2]);
            tmp2 = _mm_aesenc_si128(tmp2, KEY[2]);
            tmp3 = _mm_aesenc_si128(tmp3, KEY[2]);
            tmp4 = _mm_aesenc_si128(tmp4, KEY[2]);
            tmp5 = _mm_aesenc_si128(tmp5, KEY[2]);
            tmp6 = _mm_aesenc_si128(tmp6, KEY[2]);
            tmp7 = _mm_aesenc_si128(tmp7, KEY[2]);
            tmp8 = _mm_aesenc_si128(tmp8, KEY[2]);
                /* 128 x 128 Carryless Multiply */
                XV = _mm_loadu_si128(&((__m128i*)in)[i*8+2]);
                XV = _mm_shuffle_epi8(XV, BSWAP_MASK);
                gfmul_only(XV, HT[5], &r0, &r1);
            tmp1 = _mm_aesenc_si128(tmp1, KEY[3]);
            tmp2 = _mm_aesenc_si128(tmp2, KEY[3]);
            tmp3 = _mm_aesenc_si128(tmp3, KEY[3]);
            tmp4 = _mm_aesenc_si128(tmp4, KEY[3]);
            tmp5 = _mm_aesenc_si128(tmp5, KEY[3]);
            tmp6 = _mm_aesenc_si128(tmp6, KEY[3]);
            tmp7 = _mm_aesenc_si128(tmp7, KEY[3]);
            tmp8 = _mm_aesenc_si128(tmp8, KEY[3]);
                /* 128 x 128 Carryless Multiply */
                XV = _mm_loadu_si128(&((__m128i*)in)[i*8+3]);
                XV = _mm_shuffle_epi8(XV, BSWAP_MASK);
                gfmul_only(XV, HT[4], &r0, &r1);
            tmp1 = _mm_aesenc_si128(tmp1, KEY[4]);
            tmp2 = _mm_aesenc_si128(tmp2, KEY[4]);
            tmp3 = _mm_aesenc_si128(tmp3, KEY[4]);
            tmp4 = _mm_aesenc_si128(tmp4, KEY[4]);
            tmp5 = _mm_aesenc_si128(tmp5, KEY[4]);
            tmp6 = _mm_aesenc_si128(tmp6, KEY[4]);
            tmp7 = _mm_aesenc_si128(tmp7, KEY[4]);
            tmp8 = _mm_aesenc_si128(tmp8, KEY[4]);
                /* 128 x 128 Carryless Multiply */
                XV = _mm_loadu_si128(&((__m128i*)in)[i*8+4]);
                XV = _mm_shuffle_epi8(XV, BSWAP_MASK);
                gfmul_only(XV, HT[3], &r0, &r1);
            tmp1 = _mm_aesenc_si128(tmp1, KEY[5]);
            tmp2 = _mm_aesenc_si128(tmp2, KEY[5]);
            tmp3 = _mm_aesenc_si128(tmp3, KEY[5]);
            tmp4 = _mm_aesenc_si128(tmp4, KEY[5]);
            tmp5 = _mm_aesenc_si128(tmp5, KEY[5]);
            tmp6 = _mm_aesenc_si128(tmp6, KEY[5]);
            tmp7 = _mm_aesenc_si128(tmp7, KEY[5]);
            tmp8 = _mm_aesenc_si128(tmp8, KEY[5]);
                /* 128 x 128 Carryless Multiply */
                XV = _mm_loadu_si128(&((__m128i*)in)[i*8+5]);
                XV = _mm_shuffle_epi8(XV, BSWAP_MASK);
                gfmul_only(XV, HT[2], &r0, &r1);
            tmp1 = _mm_aesenc_si128(tmp1, KEY[6]);
            tmp2 = _mm_aesenc_si128(tmp2, KEY[6]);
            tmp3 = _mm_aesenc_si128(tmp3, KEY[6]);
            tmp4 = _mm_aesenc_si128(tmp4, KEY[6]);
            tmp5 = _mm_aesenc_si128(tmp5, KEY[6]);
            tmp6 = _mm_aesenc_si128(tmp6, KEY[6]);
            tmp7 = _mm_aesenc_si128(tmp7, KEY[6]);
            tmp8 = _mm_aesenc_si128(tmp8, KEY[6]);
                /* 128 x 128 Carryless Multiply */
                XV = _mm_loadu_si128(&((__m128i*)in)[i*8+6]);
                XV = _mm_shuffle_epi8(XV, BSWAP_MASK);
                gfmul_only(XV, HT[1], &r0, &r1);
            tmp1 = _mm_aesenc_si128(tmp1, KEY[7]);
            tmp2 = _mm_aesenc_si128(tmp2, KEY[7]);
            tmp3 = _mm_aesenc_si128(tmp3, KEY[7]);
            tmp4 = _mm_aesenc_si128(tmp4, KEY[7]);
            tmp5 = _mm_aesenc_si128(tmp5, KEY[7]);
            tmp6 = _mm_aesenc_si128(tmp6, KEY[7]);
            tmp7 = _mm_aesenc_si128(tmp7, KEY[7]);
            tmp8 = _mm_aesenc_si128(tmp8, KEY[7]);
                /* 128 x 128 Carryless Multiply */
                XV = _mm_loadu_si128(&((__m128i*)in)[i*8+7]);
                XV = _mm_shuffle_epi8(XV, BSWAP_MASK);
                gfmul_only(XV, HT[0], &r0, &r1);
            tmp1 = _mm_aesenc_si128(tmp1, KEY[8]);
            tmp2 = _mm_aesenc_si128(tmp2, KEY[8]);
            tmp3 = _mm_aesenc_si128(tmp3, KEY[8]);
            tmp4 = _mm_aesenc_si128(tmp4, KEY[8]);
            tmp5 = _mm_aesenc_si128(tmp5, KEY[8]);
            tmp6 = _mm_aesenc_si128(tmp6, KEY[8]);
            tmp7 = _mm_aesenc_si128(tmp7, KEY[8]);
            tmp8 = _mm_aesenc_si128(tmp8, KEY[8]);
                /* Reduction */
                X = ghash_red(r0, r1);
            tmp1 = _mm_aesenc_si128(tmp1, KEY[9]);
            tmp2 = _mm_aesenc_si128(tmp2, KEY[9]);
            tmp3 = _mm_aesenc_si128(tmp3, KEY[9]);
            tmp4 = _mm_aesenc_si128(tmp4, KEY[9]);
            tmp5 = _mm_aesenc_si128(tmp5, KEY[9]);
            tmp6 = _mm_aesenc_si128(tmp6, KEY[9]);
            tmp7 = _mm_aesenc_si128(tmp7, KEY[9]);
            tmp8 = _mm_aesenc_si128(tmp8, KEY[9]);
            lastKey = KEY[10];
            if (nr > 10) {
                tmp1 = _mm_aesenc_si128(tmp1, KEY[10]);
                tmp2 = _mm_aesenc_si128(tmp2, KEY[10]);
                tmp3 = _mm_aesenc_si128(tmp3, KEY[10]);
                tmp4 = _mm_aesenc_si128(tmp4, KEY[10]);
                tmp5 = _mm_aesenc_si128(tmp5, KEY[10]);
                tmp6 = _mm_aesenc_si128(tmp6, KEY[10]);
                tmp7 = _mm_aesenc_si128(tmp7, KEY[10]);
                tmp8 = _mm_aesenc_si128(tmp8, KEY[10]);
                tmp1 = _mm_aesenc_si128(tmp1, KEY[11]);
                tmp2 = _mm_aesenc_si128(tmp2, KEY[11]);
                tmp3 = _mm_aesenc_si128(tmp3, KEY[11]);
                tmp4 = _mm_aesenc_si128(tmp4, KEY[11]);
                tmp5 = _mm_aesenc_si128(tmp5, KEY[11]);
                tmp6 = _mm_aesenc_si128(tmp6, KEY[11]);
                tmp7 = _mm_aesenc_si128(tmp7, KEY[11]);
                tmp8 = _mm_aesenc_si128(tmp8, KEY[11]);
                lastKey = KEY[12];
                if (nr > 12) {
                    tmp1 = _mm_aesenc_si128(tmp1, KEY[12]);
                    tmp2 = _mm_aesenc_si128(tmp2, KEY[12]);
                    tmp3 = _mm_aesenc_si128(tmp3, KEY[12]);
                    tmp4 = _mm_aesenc_si128(tmp4, KEY[12]);
                    tmp5 = _mm_aesenc_si128(tmp5, KEY[12]);
                    tmp6 = _mm_aesenc_si128(tmp6, KEY[12]);
                    tmp7 = _mm_aesenc_si128(tmp7, KEY[12]);
                    tmp8 = _mm_aesenc_si128(tmp8, KEY[12]);
                    tmp1 = _mm_aesenc_si128(tmp1, KEY[13]);
                    tmp2 = _mm_aesenc_si128(tmp2, KEY[13]);
                    tmp3 = _mm_aesenc_si128(tmp3, KEY[13]);
                    tmp4 = _mm_aesenc_si128(tmp4, KEY[13]);
                    tmp5 = _mm_aesenc_si128(tmp5, KEY[13]);
                    tmp6 = _mm_aesenc_si128(tmp6, KEY[13]);
                    tmp7 = _mm_aesenc_si128(tmp7, KEY[13]);
                    tmp8 = _mm_aesenc_si128(tmp8, KEY[13]);
                    lastKey = KEY[14];
                }
            }
            AES_ENC_LAST_8();
        }
    }

#endif /* AES_GCM_AESNI_NO_UNROLL */

    for (k = i*8; k < nbytes/16; k++) {
        tmp1 = _mm_shuffle_epi8(ctr1, BSWAP_EPI64);
        ctr1 = _mm_add_epi32(ctr1, ONE);
        tmp1 = _mm_xor_si128(tmp1, KEY[0]);
        tmp1 = _mm_aesenc_si128(tmp1, KEY[1]);
        tmp1 = _mm_aesenc_si128(tmp1, KEY[2]);
        tmp1 = _mm_aesenc_si128(tmp1, KEY[3]);
        tmp1 = _mm_aesenc_si128(tmp1, KEY[4]);
        tmp1 = _mm_aesenc_si128(tmp1, KEY[5]);
        tmp1 = _mm_aesenc_si128(tmp1, KEY[6]);
        tmp1 = _mm_aesenc_si128(tmp1, KEY[7]);
        tmp1 = _mm_aesenc_si128(tmp1, KEY[8]);
        tmp1 = _mm_aesenc_si128(tmp1, KEY[9]);
        /* 128 x 128 Carryless Multiply */
        XV = _mm_loadu_si128(&((__m128i*)in)[k]);
        XV = _mm_shuffle_epi8(XV, BSWAP_MASK);
        XV = _mm_xor_si128(XV, X);
        X = gfmul_shifted(XV, H);
        lastKey = KEY[10];
        if (nr > 10) {
            tmp1 = _mm_aesenc_si128(tmp1, lastKey);
            tmp1 = _mm_aesenc_si128(tmp1, KEY[11]);
            lastKey = KEY[12];
            if (nr > 12) {
                tmp1 = _mm_aesenc_si128(tmp1, lastKey);
                tmp1 = _mm_aesenc_si128(tmp1, KEY[13]);
                lastKey = KEY[14];
            }
        }
        tmp1 = _mm_aesenclast_si128(tmp1, lastKey);
        tmp2 = _mm_loadu_si128(&((__m128i*)in)[k]);
        tmp1 = _mm_xor_si128(tmp1, tmp2);
        _mm_storeu_si128(&((__m128i*)out)[k], tmp1);
    }

    /* If one partial block remains */
    if (nbytes % 16) {
        tmp1 = _mm_shuffle_epi8(ctr1, BSWAP_EPI64);
        tmp1 = _mm_xor_si128(tmp1, KEY[0]);
        tmp1 = _mm_aesenc_si128(tmp1, KEY[1]);
        tmp1 = _mm_aesenc_si128(tmp1, KEY[2]);
        tmp1 = _mm_aesenc_si128(tmp1, KEY[3]);
        tmp1 = _mm_aesenc_si128(tmp1, KEY[4]);
        tmp1 = _mm_aesenc_si128(tmp1, KEY[5]);
        tmp1 = _mm_aesenc_si128(tmp1, KEY[6]);
        tmp1 = _mm_aesenc_si128(tmp1, KEY[7]);
        tmp1 = _mm_aesenc_si128(tmp1, KEY[8]);
        tmp1 = _mm_aesenc_si128(tmp1, KEY[9]);
        lastKey = KEY[10];
        if (nr > 10) {
            tmp1 = _mm_aesenc_si128(tmp1, lastKey);
            tmp1 = _mm_aesenc_si128(tmp1, KEY[11]);
            lastKey = KEY[12];
            if (nr > 12) {
                tmp1 = _mm_aesenc_si128(tmp1, lastKey);
                tmp1 = _mm_aesenc_si128(tmp1, KEY[13]);
                lastKey = KEY[14];
            }
        }
        tmp1 = _mm_aesenclast_si128(tmp1, lastKey);
        last_block = _mm_setzero_si128();
        for (j=0; j < nbytes%16; j++)
            ((unsigned char*)&last_block)[j] = in[k*16+j];
        XV = last_block;
        tmp1 = _mm_xor_si128(tmp1, last_block);
        last_block = tmp1;
        for (j=0; j < nbytes%16; j++)
            out[k*16+j] = ((unsigned char*)&last_block)[j];
        XV = _mm_shuffle_epi8(XV, BSWAP_MASK);
        XV = _mm_xor_si128(XV, X);
        X = gfmul_shifted(XV, H);
    }

    tmp1 = _mm_insert_epi64(tmp1, nbytes*8, 0);
    tmp1 = _mm_insert_epi64(tmp1, abytes*8, 1);
    /* 128 x 128 Carryless Multiply */
    X = _mm_xor_si128(X, tmp1);
    X = gfmul_shifted(X, H);
    X = _mm_shuffle_epi8(X, BSWAP_MASK);
    T = _mm_xor_si128(X, T);

/*    if (0xffff !=
           _mm_movemask_epi8(_mm_cmpeq_epi8(T, _mm_loadu_si128((__m128i*)tag)))) */
    if (XMEMCMP(tag, &T, tbytes) != 0)
        *res = 0; /* in case the authentication failed */
    else
        *res = 1; /* when successful returns 1 */
}

#endif /* HAVE_AES_DECRYPT */
#endif /* _MSC_VER */
#endif /* WOLFSSL_AESNI */


#if defined(GCM_SMALL)
static void GMULT(byte* X, byte* Y)
{
    byte Z[AES_BLOCK_SIZE];
    byte V[AES_BLOCK_SIZE];
    int i, j;

    XMEMSET(Z, 0, AES_BLOCK_SIZE);
    XMEMCPY(V, X, AES_BLOCK_SIZE);
    for (i = 0; i < AES_BLOCK_SIZE; i++)
    {
        byte y = Y[i];
        for (j = 0; j < 8; j++)
        {
            if (y & 0x80) {
                xorbuf(Z, V, AES_BLOCK_SIZE);
            }

            RIGHTSHIFTX(V);
            y = y << 1;
        }
    }
    XMEMCPY(X, Z, AES_BLOCK_SIZE);
}


void GHASH(Aes* aes, const byte* a, word32 aSz, const byte* c,
    word32 cSz, byte* s, word32 sSz)
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

/* end GCM_SMALL */
#elif defined(GCM_TABLE)

static const byte R[256][2] = {
    {0x00, 0x00}, {0x01, 0xc2}, {0x03, 0x84}, {0x02, 0x46},
    {0x07, 0x08}, {0x06, 0xca}, {0x04, 0x8c}, {0x05, 0x4e},
    {0x0e, 0x10}, {0x0f, 0xd2}, {0x0d, 0x94}, {0x0c, 0x56},
    {0x09, 0x18}, {0x08, 0xda}, {0x0a, 0x9c}, {0x0b, 0x5e},
    {0x1c, 0x20}, {0x1d, 0xe2}, {0x1f, 0xa4}, {0x1e, 0x66},
    {0x1b, 0x28}, {0x1a, 0xea}, {0x18, 0xac}, {0x19, 0x6e},
    {0x12, 0x30}, {0x13, 0xf2}, {0x11, 0xb4}, {0x10, 0x76},
    {0x15, 0x38}, {0x14, 0xfa}, {0x16, 0xbc}, {0x17, 0x7e},
    {0x38, 0x40}, {0x39, 0x82}, {0x3b, 0xc4}, {0x3a, 0x06},
    {0x3f, 0x48}, {0x3e, 0x8a}, {0x3c, 0xcc}, {0x3d, 0x0e},
    {0x36, 0x50}, {0x37, 0x92}, {0x35, 0xd4}, {0x34, 0x16},
    {0x31, 0x58}, {0x30, 0x9a}, {0x32, 0xdc}, {0x33, 0x1e},
    {0x24, 0x60}, {0x25, 0xa2}, {0x27, 0xe4}, {0x26, 0x26},
    {0x23, 0x68}, {0x22, 0xaa}, {0x20, 0xec}, {0x21, 0x2e},
    {0x2a, 0x70}, {0x2b, 0xb2}, {0x29, 0xf4}, {0x28, 0x36},
    {0x2d, 0x78}, {0x2c, 0xba}, {0x2e, 0xfc}, {0x2f, 0x3e},
    {0x70, 0x80}, {0x71, 0x42}, {0x73, 0x04}, {0x72, 0xc6},
    {0x77, 0x88}, {0x76, 0x4a}, {0x74, 0x0c}, {0x75, 0xce},
    {0x7e, 0x90}, {0x7f, 0x52}, {0x7d, 0x14}, {0x7c, 0xd6},
    {0x79, 0x98}, {0x78, 0x5a}, {0x7a, 0x1c}, {0x7b, 0xde},
    {0x6c, 0xa0}, {0x6d, 0x62}, {0x6f, 0x24}, {0x6e, 0xe6},
    {0x6b, 0xa8}, {0x6a, 0x6a}, {0x68, 0x2c}, {0x69, 0xee},
    {0x62, 0xb0}, {0x63, 0x72}, {0x61, 0x34}, {0x60, 0xf6},
    {0x65, 0xb8}, {0x64, 0x7a}, {0x66, 0x3c}, {0x67, 0xfe},
    {0x48, 0xc0}, {0x49, 0x02}, {0x4b, 0x44}, {0x4a, 0x86},
    {0x4f, 0xc8}, {0x4e, 0x0a}, {0x4c, 0x4c}, {0x4d, 0x8e},
    {0x46, 0xd0}, {0x47, 0x12}, {0x45, 0x54}, {0x44, 0x96},
    {0x41, 0xd8}, {0x40, 0x1a}, {0x42, 0x5c}, {0x43, 0x9e},
    {0x54, 0xe0}, {0x55, 0x22}, {0x57, 0x64}, {0x56, 0xa6},
    {0x53, 0xe8}, {0x52, 0x2a}, {0x50, 0x6c}, {0x51, 0xae},
    {0x5a, 0xf0}, {0x5b, 0x32}, {0x59, 0x74}, {0x58, 0xb6},
    {0x5d, 0xf8}, {0x5c, 0x3a}, {0x5e, 0x7c}, {0x5f, 0xbe},
    {0xe1, 0x00}, {0xe0, 0xc2}, {0xe2, 0x84}, {0xe3, 0x46},
    {0xe6, 0x08}, {0xe7, 0xca}, {0xe5, 0x8c}, {0xe4, 0x4e},
    {0xef, 0x10}, {0xee, 0xd2}, {0xec, 0x94}, {0xed, 0x56},
    {0xe8, 0x18}, {0xe9, 0xda}, {0xeb, 0x9c}, {0xea, 0x5e},
    {0xfd, 0x20}, {0xfc, 0xe2}, {0xfe, 0xa4}, {0xff, 0x66},
    {0xfa, 0x28}, {0xfb, 0xea}, {0xf9, 0xac}, {0xf8, 0x6e},
    {0xf3, 0x30}, {0xf2, 0xf2}, {0xf0, 0xb4}, {0xf1, 0x76},
    {0xf4, 0x38}, {0xf5, 0xfa}, {0xf7, 0xbc}, {0xf6, 0x7e},
    {0xd9, 0x40}, {0xd8, 0x82}, {0xda, 0xc4}, {0xdb, 0x06},
    {0xde, 0x48}, {0xdf, 0x8a}, {0xdd, 0xcc}, {0xdc, 0x0e},
    {0xd7, 0x50}, {0xd6, 0x92}, {0xd4, 0xd4}, {0xd5, 0x16},
    {0xd0, 0x58}, {0xd1, 0x9a}, {0xd3, 0xdc}, {0xd2, 0x1e},
    {0xc5, 0x60}, {0xc4, 0xa2}, {0xc6, 0xe4}, {0xc7, 0x26},
    {0xc2, 0x68}, {0xc3, 0xaa}, {0xc1, 0xec}, {0xc0, 0x2e},
    {0xcb, 0x70}, {0xca, 0xb2}, {0xc8, 0xf4}, {0xc9, 0x36},
    {0xcc, 0x78}, {0xcd, 0xba}, {0xcf, 0xfc}, {0xce, 0x3e},
    {0x91, 0x80}, {0x90, 0x42}, {0x92, 0x04}, {0x93, 0xc6},
    {0x96, 0x88}, {0x97, 0x4a}, {0x95, 0x0c}, {0x94, 0xce},
    {0x9f, 0x90}, {0x9e, 0x52}, {0x9c, 0x14}, {0x9d, 0xd6},
    {0x98, 0x98}, {0x99, 0x5a}, {0x9b, 0x1c}, {0x9a, 0xde},
    {0x8d, 0xa0}, {0x8c, 0x62}, {0x8e, 0x24}, {0x8f, 0xe6},
    {0x8a, 0xa8}, {0x8b, 0x6a}, {0x89, 0x2c}, {0x88, 0xee},
    {0x83, 0xb0}, {0x82, 0x72}, {0x80, 0x34}, {0x81, 0xf6},
    {0x84, 0xb8}, {0x85, 0x7a}, {0x87, 0x3c}, {0x86, 0xfe},
    {0xa9, 0xc0}, {0xa8, 0x02}, {0xaa, 0x44}, {0xab, 0x86},
    {0xae, 0xc8}, {0xaf, 0x0a}, {0xad, 0x4c}, {0xac, 0x8e},
    {0xa7, 0xd0}, {0xa6, 0x12}, {0xa4, 0x54}, {0xa5, 0x96},
    {0xa0, 0xd8}, {0xa1, 0x1a}, {0xa3, 0x5c}, {0xa2, 0x9e},
    {0xb5, 0xe0}, {0xb4, 0x22}, {0xb6, 0x64}, {0xb7, 0xa6},
    {0xb2, 0xe8}, {0xb3, 0x2a}, {0xb1, 0x6c}, {0xb0, 0xae},
    {0xbb, 0xf0}, {0xba, 0x32}, {0xb8, 0x74}, {0xb9, 0xb6},
    {0xbc, 0xf8}, {0xbd, 0x3a}, {0xbf, 0x7c}, {0xbe, 0xbe} };


static void GMULT(byte *x, byte m[256][AES_BLOCK_SIZE])
{
    int i, j;
    byte Z[AES_BLOCK_SIZE];
    byte a;

    XMEMSET(Z, 0, sizeof(Z));

    for (i = 15; i > 0; i--) {
        xorbuf(Z, m[x[i]], AES_BLOCK_SIZE);
        a = Z[15];

        for (j = 15; j > 0; j--) {
            Z[j] = Z[j-1];
        }

        Z[0] = R[a][0];
        Z[1] ^= R[a][1];
    }
    xorbuf(Z, m[x[0]], AES_BLOCK_SIZE);

    XMEMCPY(x, Z, AES_BLOCK_SIZE);
}


void GHASH(Aes* aes, const byte* a, word32 aSz, const byte* c,
    word32 cSz, byte* s, word32 sSz)
{
    byte x[AES_BLOCK_SIZE];
    byte scratch[AES_BLOCK_SIZE];
    word32 blocks, partial;

    XMEMSET(x, 0, AES_BLOCK_SIZE);

    /* Hash in A, the Additional Authentication Data */
    if (aSz != 0 && a != NULL) {
        blocks = aSz / AES_BLOCK_SIZE;
        partial = aSz % AES_BLOCK_SIZE;
        while (blocks--) {
            xorbuf(x, a, AES_BLOCK_SIZE);
            GMULT(x, aes->M0);
            a += AES_BLOCK_SIZE;
        }
        if (partial != 0) {
            XMEMSET(scratch, 0, AES_BLOCK_SIZE);
            XMEMCPY(scratch, a, partial);
            xorbuf(x, scratch, AES_BLOCK_SIZE);
            GMULT(x, aes->M0);
        }
    }

    /* Hash in C, the Ciphertext */
    if (cSz != 0 && c != NULL) {
        blocks = cSz / AES_BLOCK_SIZE;
        partial = cSz % AES_BLOCK_SIZE;
        while (blocks--) {
            xorbuf(x, c, AES_BLOCK_SIZE);
            GMULT(x, aes->M0);
            c += AES_BLOCK_SIZE;
        }
        if (partial != 0) {
            XMEMSET(scratch, 0, AES_BLOCK_SIZE);
            XMEMCPY(scratch, c, partial);
            xorbuf(x, scratch, AES_BLOCK_SIZE);
            GMULT(x, aes->M0);
        }
    }

    /* Hash in the lengths of A and C in bits */
    FlattenSzInBits(&scratch[0], aSz);
    FlattenSzInBits(&scratch[8], cSz);
    xorbuf(x, scratch, AES_BLOCK_SIZE);
    GMULT(x, aes->M0);

    /* Copy the result into s. */
    XMEMCPY(s, x, sSz);
}

/* end GCM_TABLE */
#elif defined(WORD64_AVAILABLE) && !defined(GCM_WORD32)

#if !defined(FREESCALE_LTC_AES_GCM)
static void GMULT(word64* X, word64* Y)
{
    word64 Z[2] = {0,0};
    word64 V[2];
    int i, j;
    V[0] = X[0];  V[1] = X[1];

    for (i = 0; i < 2; i++)
    {
        word64 y = Y[i];
        for (j = 0; j < 64; j++)
        {
            if (y & 0x8000000000000000ULL) {
                Z[0] ^= V[0];
                Z[1] ^= V[1];
            }

            if (V[1] & 0x0000000000000001) {
                V[1] >>= 1;
                V[1] |= ((V[0] & 0x0000000000000001) ?
                    0x8000000000000000ULL : 0);
                V[0] >>= 1;
                V[0] ^= 0xE100000000000000ULL;
            }
            else {
                V[1] >>= 1;
                V[1] |= ((V[0] & 0x0000000000000001) ?
                    0x8000000000000000ULL : 0);
                V[0] >>= 1;
            }
            y <<= 1;
        }
    }
    X[0] = Z[0];
    X[1] = Z[1];
}


void GHASH(Aes* aes, const byte* a, word32 aSz, const byte* c,
    word32 cSz, byte* s, word32 sSz)
{
    word64 x[2] = {0,0};
    word32 blocks, partial;
    word64 bigH[2];

    XMEMCPY(bigH, aes->H, AES_BLOCK_SIZE);
    #ifdef LITTLE_ENDIAN_ORDER
        ByteReverseWords64(bigH, bigH, AES_BLOCK_SIZE);
    #endif

    /* Hash in A, the Additional Authentication Data */
    if (aSz != 0 && a != NULL) {
        word64 bigA[2];
        blocks = aSz / AES_BLOCK_SIZE;
        partial = aSz % AES_BLOCK_SIZE;
        while (blocks--) {
            XMEMCPY(bigA, a, AES_BLOCK_SIZE);
            #ifdef LITTLE_ENDIAN_ORDER
                ByteReverseWords64(bigA, bigA, AES_BLOCK_SIZE);
            #endif
            x[0] ^= bigA[0];
            x[1] ^= bigA[1];
            GMULT(x, bigH);
            a += AES_BLOCK_SIZE;
        }
        if (partial != 0) {
            XMEMSET(bigA, 0, AES_BLOCK_SIZE);
            XMEMCPY(bigA, a, partial);
            #ifdef LITTLE_ENDIAN_ORDER
                ByteReverseWords64(bigA, bigA, AES_BLOCK_SIZE);
            #endif
            x[0] ^= bigA[0];
            x[1] ^= bigA[1];
            GMULT(x, bigH);
        }
#ifdef OPENSSL_EXTRA
        /* store AAD partial tag for next call */
        aes->aadH[0] = (word32)((x[0] & 0xFFFFFFFF00000000) >> 32);
        aes->aadH[1] = (word32)(x[0] & 0xFFFFFFFF);
        aes->aadH[2] = (word32)((x[1] & 0xFFFFFFFF00000000) >> 32);
        aes->aadH[3] = (word32)(x[1] & 0xFFFFFFFF);
#endif
    }

    /* Hash in C, the Ciphertext */
    if (cSz != 0 && c != NULL) {
        word64 bigC[2];
        blocks = cSz / AES_BLOCK_SIZE;
        partial = cSz % AES_BLOCK_SIZE;
#ifdef OPENSSL_EXTRA
        /* Start from last AAD partial tag */
        if(aes->aadLen) {
            x[0] = ((word64)aes->aadH[0]) << 32 | aes->aadH[1];
            x[1] = ((word64)aes->aadH[2]) << 32 | aes->aadH[3];
         }
#endif
        while (blocks--) {
            XMEMCPY(bigC, c, AES_BLOCK_SIZE);
            #ifdef LITTLE_ENDIAN_ORDER
                ByteReverseWords64(bigC, bigC, AES_BLOCK_SIZE);
            #endif
            x[0] ^= bigC[0];
            x[1] ^= bigC[1];
            GMULT(x, bigH);
            c += AES_BLOCK_SIZE;
        }
        if (partial != 0) {
            XMEMSET(bigC, 0, AES_BLOCK_SIZE);
            XMEMCPY(bigC, c, partial);
            #ifdef LITTLE_ENDIAN_ORDER
                ByteReverseWords64(bigC, bigC, AES_BLOCK_SIZE);
            #endif
            x[0] ^= bigC[0];
            x[1] ^= bigC[1];
            GMULT(x, bigH);
        }
    }

    /* Hash in the lengths in bits of A and C */
    {
        word64 len[2];
        len[0] = aSz; len[1] = cSz;
#ifdef OPENSSL_EXTRA
        if (aes->aadLen)
            len[0] = (word64)aes->aadLen;
#endif
        /* Lengths are in bytes. Convert to bits. */
        len[0] *= 8;
        len[1] *= 8;

        x[0] ^= len[0];
        x[1] ^= len[1];
        GMULT(x, bigH);
    }
    #ifdef LITTLE_ENDIAN_ORDER
        ByteReverseWords64(x, x, AES_BLOCK_SIZE);
    #endif
    XMEMCPY(s, x, sSz);
}
#endif /* !FREESCALE_LTC_AES_GCM */

/* end defined(WORD64_AVAILABLE) && !defined(GCM_WORD32) */
#else /* GCM_WORD32 */

static void GMULT(word32* X, word32* Y)
{
    word32 Z[4] = {0,0,0,0};
    word32 V[4];
    int i, j;

    V[0] = X[0];  V[1] = X[1]; V[2] =  X[2]; V[3] =  X[3];

    for (i = 0; i < 4; i++)
    {
        word32 y = Y[i];
        for (j = 0; j < 32; j++)
        {
            if (y & 0x80000000) {
                Z[0] ^= V[0];
                Z[1] ^= V[1];
                Z[2] ^= V[2];
                Z[3] ^= V[3];
            }

            if (V[3] & 0x00000001) {
                V[3] >>= 1;
                V[3] |= ((V[2] & 0x00000001) ? 0x80000000 : 0);
                V[2] >>= 1;
                V[2] |= ((V[1] & 0x00000001) ? 0x80000000 : 0);
                V[1] >>= 1;
                V[1] |= ((V[0] & 0x00000001) ? 0x80000000 : 0);
                V[0] >>= 1;
                V[0] ^= 0xE1000000;
            } else {
                V[3] >>= 1;
                V[3] |= ((V[2] & 0x00000001) ? 0x80000000 : 0);
                V[2] >>= 1;
                V[2] |= ((V[1] & 0x00000001) ? 0x80000000 : 0);
                V[1] >>= 1;
                V[1] |= ((V[0] & 0x00000001) ? 0x80000000 : 0);
                V[0] >>= 1;
            }
            y <<= 1;
        }
    }
    X[0] = Z[0];
    X[1] = Z[1];
    X[2] = Z[2];
    X[3] = Z[3];
}


void GHASH(Aes* aes, const byte* a, word32 aSz, const byte* c,
    word32 cSz, byte* s, word32 sSz)
{
    word32 x[4] = {0,0,0,0};
    word32 blocks, partial;
    word32 bigH[4];

    XMEMCPY(bigH, aes->H, AES_BLOCK_SIZE);
    #ifdef LITTLE_ENDIAN_ORDER
        ByteReverseWords(bigH, bigH, AES_BLOCK_SIZE);
    #endif

    /* Hash in A, the Additional Authentication Data */
    if (aSz != 0 && a != NULL) {
        word32 bigA[4];
        blocks = aSz / AES_BLOCK_SIZE;
        partial = aSz % AES_BLOCK_SIZE;
        while (blocks--) {
            XMEMCPY(bigA, a, AES_BLOCK_SIZE);
            #ifdef LITTLE_ENDIAN_ORDER
                ByteReverseWords(bigA, bigA, AES_BLOCK_SIZE);
            #endif
            x[0] ^= bigA[0];
            x[1] ^= bigA[1];
            x[2] ^= bigA[2];
            x[3] ^= bigA[3];
            GMULT(x, bigH);
            a += AES_BLOCK_SIZE;
        }
        if (partial != 0) {
            XMEMSET(bigA, 0, AES_BLOCK_SIZE);
            XMEMCPY(bigA, a, partial);
            #ifdef LITTLE_ENDIAN_ORDER
                ByteReverseWords(bigA, bigA, AES_BLOCK_SIZE);
            #endif
            x[0] ^= bigA[0];
            x[1] ^= bigA[1];
            x[2] ^= bigA[2];
            x[3] ^= bigA[3];
            GMULT(x, bigH);
        }
    }

    /* Hash in C, the Ciphertext */
    if (cSz != 0 && c != NULL) {
        word32 bigC[4];
        blocks = cSz / AES_BLOCK_SIZE;
        partial = cSz % AES_BLOCK_SIZE;
        while (blocks--) {
            XMEMCPY(bigC, c, AES_BLOCK_SIZE);
            #ifdef LITTLE_ENDIAN_ORDER
                ByteReverseWords(bigC, bigC, AES_BLOCK_SIZE);
            #endif
            x[0] ^= bigC[0];
            x[1] ^= bigC[1];
            x[2] ^= bigC[2];
            x[3] ^= bigC[3];
            GMULT(x, bigH);
            c += AES_BLOCK_SIZE;
        }
        if (partial != 0) {
            XMEMSET(bigC, 0, AES_BLOCK_SIZE);
            XMEMCPY(bigC, c, partial);
            #ifdef LITTLE_ENDIAN_ORDER
                ByteReverseWords(bigC, bigC, AES_BLOCK_SIZE);
            #endif
            x[0] ^= bigC[0];
            x[1] ^= bigC[1];
            x[2] ^= bigC[2];
            x[3] ^= bigC[3];
            GMULT(x, bigH);
        }
    }

    /* Hash in the lengths in bits of A and C */
    {
        word32 len[4];

        /* Lengths are in bytes. Convert to bits. */
        len[0] = (aSz >> (8*sizeof(aSz) - 3));
        len[1] = aSz << 3;
        len[2] = (cSz >> (8*sizeof(cSz) - 3));
        len[3] = cSz << 3;

        x[0] ^= len[0];
        x[1] ^= len[1];
        x[2] ^= len[2];
        x[3] ^= len[3];
        GMULT(x, bigH);
    }
    #ifdef LITTLE_ENDIAN_ORDER
        ByteReverseWords(x, x, AES_BLOCK_SIZE);
    #endif
    XMEMCPY(s, x, sSz);
}

#endif /* end GCM_WORD32 */


#if !defined(WOLFSSL_XILINX_CRYPT) && !defined(WOLFSSL_AFALG_XILINX_AES)
#ifdef FREESCALE_LTC_AES_GCM
int wc_AesGcmEncrypt(Aes* aes, byte* out, const byte* in, word32 sz,
                   const byte* iv, word32 ivSz,
                   byte* authTag, word32 authTagSz,
                   const byte* authIn, word32 authInSz)
{
    status_t status;
    word32 keySize;

    /* argument checks */
    if (aes == NULL || authTagSz > AES_BLOCK_SIZE || ivSz == 0) {
        return BAD_FUNC_ARG;
    }

    if (authTagSz < WOLFSSL_MIN_AUTH_TAG_SZ) {
        WOLFSSL_MSG("GcmEncrypt authTagSz too small error");
        return BAD_FUNC_ARG;
    }

    status = wc_AesGetKeySize(aes, &keySize);
    if (status)
        return status;

    status = LTC_AES_EncryptTagGcm(LTC_BASE, in, out, sz, iv, ivSz,
        authIn, authInSz, (byte*)aes->key, keySize, authTag, authTagSz);

    return (status == kStatus_Success) ? 0 : AES_GCM_AUTH_E;
}

#else

#ifdef STM32_CRYPTO_AES_GCM

/* this function supports inline encrypt */
static int wc_AesGcmEncrypt_STM32(Aes* aes, byte* out, const byte* in, word32 sz,
                                  const byte* iv, word32 ivSz,
                                  byte* authTag, word32 authTagSz,
                                  const byte* authIn, word32 authInSz)
{
    int ret;
#ifdef WOLFSSL_STM32_CUBEMX
    CRYP_HandleTypeDef hcryp;
#else
    word32 keyCopy[AES_256_KEY_SIZE/sizeof(word32)];
#endif
    word32 keySize;
#ifdef WOLFSSL_STM32_CUBEMX
    int status = HAL_OK;
    word32 blocks = sz / AES_BLOCK_SIZE;
    word32 partialBlock[AES_BLOCK_SIZE/sizeof(word32)];
#else
    int status = SUCCESS;
#endif
    word32 partial = sz % AES_BLOCK_SIZE;
    word32 tag[AES_BLOCK_SIZE/sizeof(word32)];
    word32 ctrInit[AES_BLOCK_SIZE/sizeof(word32)];
    word32 ctr[AES_BLOCK_SIZE/sizeof(word32)];
    word32 authhdr[AES_BLOCK_SIZE/sizeof(word32)];
    byte* authInPadded = NULL;
    int authPadSz, wasAlloc = 0;

    ret = wc_AesGetKeySize(aes, &keySize);
    if (ret != 0)
        return ret;

#ifdef WOLFSSL_STM32_CUBEMX
    ret = wc_Stm32_Aes_Init(aes, &hcryp);
    if (ret != 0)
        return ret;
#endif

    ret = wolfSSL_CryptHwMutexLock();
    if (ret != 0) {
        return ret;
    }

    XMEMSET(ctr, 0, AES_BLOCK_SIZE);
    if (ivSz == GCM_NONCE_MID_SZ) {
        byte* pCtr = (byte*)ctr;
        XMEMCPY(ctr, iv, ivSz);
        pCtr[AES_BLOCK_SIZE - 1] = 1;
    }
    else {
        GHASH(aes, NULL, 0, iv, ivSz, (byte*)ctr, AES_BLOCK_SIZE);
    }
    XMEMCPY(ctrInit, ctr, sizeof(ctr)); /* save off initial counter for GMAC */

    /* Authentication buffer - must be 4-byte multiple zero padded */
    authPadSz = authInSz % sizeof(word32);
    if (authPadSz != 0) {
        authPadSz = authInSz + sizeof(word32) - authPadSz;
        if (authPadSz <= sizeof(authhdr)) {
            authInPadded = (byte*)authhdr;
        }
        else {
            authInPadded = (byte*)XMALLOC(authPadSz, aes->heap,
                DYNAMIC_TYPE_TMP_BUFFER);
            if (authInPadded == NULL) {
                wolfSSL_CryptHwMutexUnLock();
                return MEMORY_E;
            }
            wasAlloc = 1;
        }
        XMEMSET(authInPadded, 0, authPadSz);
        XMEMCPY(authInPadded, authIn, authInSz);
    } else {
        authPadSz = authInSz;
        authInPadded = (byte*)authIn;
    }

    /* Hardware requires counter + 1 */
    IncrementGcmCounter((byte*)ctr);

#ifdef WOLFSSL_STM32_CUBEMX
    hcryp.Init.pInitVect = (STM_CRYPT_TYPE*)ctr;
    hcryp.Init.Header = (STM_CRYPT_TYPE*)authInPadded;

#if defined(STM32_HAL_V2)
    hcryp.Init.Algorithm  = CRYP_AES_GCM;
    hcryp.Init.HeaderSize = authPadSz/sizeof(word32);
    ByteReverseWords(partialBlock, ctr, AES_BLOCK_SIZE);
    hcryp.Init.pInitVect = (STM_CRYPT_TYPE*)partialBlock;
    HAL_CRYP_Init(&hcryp);

    /* GCM payload phase - can handle partial blocks */
    status = HAL_CRYP_Encrypt(&hcryp, (uint32_t*)in,
        (blocks * AES_BLOCK_SIZE) + partial, (uint32_t*)out, STM32_HAL_TIMEOUT);
    if (status == HAL_OK) {
        /* Compute the authTag */
        status = HAL_CRYPEx_AESGCM_GenerateAuthTAG(&hcryp, (uint32_t*)tag,
            STM32_HAL_TIMEOUT);
    }
#elif defined(STM32_CRYPTO_AES_ONLY)
    /* Set the CRYP parameters */
    hcryp.Init.HeaderSize = authPadSz;
    if (authPadSz == 0)
        hcryp.Init.Header = NULL; /* cannot pass pointer here when authIn == 0 */
    hcryp.Init.ChainingMode  = CRYP_CHAINMODE_AES_GCM_GMAC;
    hcryp.Init.OperatingMode = CRYP_ALGOMODE_ENCRYPT;
    hcryp.Init.GCMCMACPhase  = CRYP_INIT_PHASE;
    HAL_CRYP_Init(&hcryp);

    /* GCM init phase */
    status = HAL_CRYPEx_AES_Auth(&hcryp, NULL, 0, NULL, STM32_HAL_TIMEOUT);
    if (status == HAL_OK) {
        /* GCM header phase */
        hcryp.Init.GCMCMACPhase = CRYP_HEADER_PHASE;
        status = HAL_CRYPEx_AES_Auth(&hcryp, NULL, 0, NULL, STM32_HAL_TIMEOUT);
    }
    if (status == HAL_OK) {
        /* GCM payload phase - blocks */
        hcryp.Init.GCMCMACPhase = CRYP_PAYLOAD_PHASE;
        if (blocks) {
            status = HAL_CRYPEx_AES_Auth(&hcryp, (byte*)in,
                (blocks * AES_BLOCK_SIZE), out, STM32_HAL_TIMEOUT);
        }
    }
    if (status == HAL_OK && (partial != 0 || (sz > 0 && blocks == 0))) {
        /* GCM payload phase - partial remainder */
        XMEMSET(partialBlock, 0, sizeof(partialBlock));
        XMEMCPY(partialBlock, in + (blocks * AES_BLOCK_SIZE), partial);
        status = HAL_CRYPEx_AES_Auth(&hcryp, (uint8_t*)partialBlock, partial,
                (uint8_t*)partialBlock, STM32_HAL_TIMEOUT);
        XMEMCPY(out + (blocks * AES_BLOCK_SIZE), partialBlock, partial);
    }
    if (status == HAL_OK) {
        /* GCM final phase */
        hcryp.Init.GCMCMACPhase  = CRYP_FINAL_PHASE;
        status = HAL_CRYPEx_AES_Auth(&hcryp, NULL, sz, (uint8_t*)tag, STM32_HAL_TIMEOUT);
    }
#else
    hcryp.Init.HeaderSize = authPadSz;
    HAL_CRYP_Init(&hcryp);
    if (blocks) {
        /* GCM payload phase - blocks */
        status = HAL_CRYPEx_AESGCM_Encrypt(&hcryp, (byte*)in,
            (blocks * AES_BLOCK_SIZE), out, STM32_HAL_TIMEOUT);
    }
    if (status == HAL_OK && (partial != 0 || blocks == 0)) {
        /* GCM payload phase - partial remainder */
        XMEMSET(partialBlock, 0, sizeof(partialBlock));
        XMEMCPY(partialBlock, in + (blocks * AES_BLOCK_SIZE), partial);
        status = HAL_CRYPEx_AESGCM_Encrypt(&hcryp, (uint8_t*)partialBlock, partial,
            (uint8_t*)partialBlock, STM32_HAL_TIMEOUT);
        XMEMCPY(out + (blocks * AES_BLOCK_SIZE), partialBlock, partial);
    }
    if (status == HAL_OK) {
        /* Compute the authTag */
        status = HAL_CRYPEx_AESGCM_Finish(&hcryp, sz, (uint8_t*)tag, STM32_HAL_TIMEOUT);
    }
#endif

    if (status != HAL_OK)
        ret = AES_GCM_AUTH_E;
    HAL_CRYP_DeInit(&hcryp);

#else /* Standard Peripheral Library */
    ByteReverseWords(keyCopy, (word32*)aes->key, keySize);
    status = CRYP_AES_GCM(MODE_ENCRYPT, (uint8_t*)ctr,
                         (uint8_t*)keyCopy,      keySize * 8,
                         (uint8_t*)in,           sz,
                         (uint8_t*)authInPadded, authInSz,
                         (uint8_t*)out,          (uint8_t*)tag);
    if (status != SUCCESS)
        ret = AES_GCM_AUTH_E;
#endif /* WOLFSSL_STM32_CUBEMX */

    if (ret == 0) {
        /* return authTag */
        if (authTag) {
            /* For STM32 GCM fallback to software if partial AES block or IV != 12 */
            if (sz == 0 || partial != 0 || ivSz != GCM_NONCE_MID_SZ) {
                GHASH(aes, authIn, authInSz, out, sz, authTag, authTagSz);
                wc_AesEncrypt(aes, (byte*)ctrInit, (byte*)tag);
                xorbuf(authTag, tag, authTagSz);
            }
            else {
                XMEMCPY(authTag, tag, authTagSz);
            }
        }
    }

    /* Free memory */
    if (wasAlloc) {
        XFREE(authInPadded, aes->heap, DYNAMIC_TYPE_TMP_BUFFER);
    }

    wolfSSL_CryptHwMutexUnLock();

    return ret;
}

#endif /* STM32_CRYPTO_AES_GCM */

#ifdef WOLFSSL_AESNI
int AES_GCM_encrypt_C(Aes* aes, byte* out, const byte* in, word32 sz,
                      const byte* iv, word32 ivSz,
                      byte* authTag, word32 authTagSz,
                      const byte* authIn, word32 authInSz);
#else
static
#endif
int AES_GCM_encrypt_C(Aes* aes, byte* out, const byte* in, word32 sz,
                      const byte* iv, word32 ivSz,
                      byte* authTag, word32 authTagSz,
                      const byte* authIn, word32 authInSz)
{
    int ret = 0;
    word32 blocks = sz / AES_BLOCK_SIZE;
    word32 partial = sz % AES_BLOCK_SIZE;
    const byte* p = in;
    byte* c = out;
    byte counter[AES_BLOCK_SIZE];
    byte initialCounter[AES_BLOCK_SIZE];
    byte *ctr;
    byte scratch[AES_BLOCK_SIZE];
#ifdef OPENSSL_EXTRA
    word32 aadTemp;
#endif
    ctr = counter;
    XMEMSET(initialCounter, 0, AES_BLOCK_SIZE);
    XMEMSET(scratch, 0, AES_BLOCK_SIZE);
    if (ivSz == GCM_NONCE_MID_SZ) {
        XMEMCPY(initialCounter, iv, ivSz);
        initialCounter[AES_BLOCK_SIZE - 1] = 1;
    }
    else {
#ifdef OPENSSL_EXTRA
        aadTemp = aes->aadLen;
        aes->aadLen = 0;
#endif
        GHASH(aes, NULL, 0, iv, ivSz, initialCounter, AES_BLOCK_SIZE);
#ifdef OPENSSL_EXTRA
        aes->aadLen = aadTemp;
#endif
    }
    XMEMCPY(ctr, initialCounter, AES_BLOCK_SIZE);

#ifdef WOLFSSL_PIC32MZ_CRYPT
    if (blocks) {
        /* use initial IV for HW, but don't use it below */
        XMEMCPY(aes->reg, ctr, AES_BLOCK_SIZE);

        ret = wc_Pic32AesCrypt(
            aes->key, aes->keylen, aes->reg, AES_BLOCK_SIZE,
            out, in, (blocks * AES_BLOCK_SIZE),
            PIC32_ENCRYPTION, PIC32_ALGO_AES, PIC32_CRYPTOALGO_AES_GCM);
        if (ret != 0)
            return ret;
    }
    /* process remainder using partial handling */
#endif

#if defined(HAVE_AES_ECB) && !defined(WOLFSSL_PIC32MZ_CRYPT)
    /* some hardware acceleration can gain performance from doing AES encryption
     * of the whole buffer at once */
    if (c != p && blocks > 0) { /* can not handle inline encryption */
        while (blocks--) {
            IncrementGcmCounter(ctr);
            XMEMCPY(c, ctr, AES_BLOCK_SIZE);
            c += AES_BLOCK_SIZE;
        }

        /* reset number of blocks and then do encryption */
        blocks = sz / AES_BLOCK_SIZE;
        wc_AesEcbEncrypt(aes, out, out, AES_BLOCK_SIZE * blocks);
        xorbuf(out, p, AES_BLOCK_SIZE * blocks);
        p += AES_BLOCK_SIZE * blocks;
    }
    else
#endif /* HAVE_AES_ECB && !WOLFSSL_PIC32MZ_CRYPT */

    while (blocks--) {
        IncrementGcmCounter(ctr);
    #if !defined(WOLFSSL_PIC32MZ_CRYPT)
        wc_AesEncrypt(aes, ctr, scratch);
        xorbuf(scratch, p, AES_BLOCK_SIZE);
        XMEMCPY(c, scratch, AES_BLOCK_SIZE);
    #endif
        p += AES_BLOCK_SIZE;
        c += AES_BLOCK_SIZE;
    }

    if (partial != 0) {
        IncrementGcmCounter(ctr);
        wc_AesEncrypt(aes, ctr, scratch);
        xorbuf(scratch, p, partial);
        XMEMCPY(c, scratch, partial);
    }
    if (authTag) {
        GHASH(aes, authIn, authInSz, out, sz, authTag, authTagSz);
        wc_AesEncrypt(aes, initialCounter, scratch);
        xorbuf(authTag, scratch, authTagSz);
#ifdef OPENSSL_EXTRA
        if (!in && !sz)
            /* store AAD size for next call */
            aes->aadLen = authInSz;
#endif
    }

    return ret;
}

/* Software AES - GCM Encrypt */
int wc_AesGcmEncrypt(Aes* aes, byte* out, const byte* in, word32 sz,
                   const byte* iv, word32 ivSz,
                   byte* authTag, word32 authTagSz,
                   const byte* authIn, word32 authInSz)
{
    /* argument checks */
    if (aes == NULL || authTagSz > AES_BLOCK_SIZE || ivSz == 0) {
        return BAD_FUNC_ARG;
    }

    if (authTagSz < WOLFSSL_MIN_AUTH_TAG_SZ) {
        WOLFSSL_MSG("GcmEncrypt authTagSz too small error");
        return BAD_FUNC_ARG;
    }

#ifdef WOLF_CRYPTO_CB
    if (aes->devId != INVALID_DEVID) {
        int ret = wc_CryptoCb_AesGcmEncrypt(aes, out, in, sz, iv, ivSz,
            authTag, authTagSz, authIn, authInSz);
        if (ret != CRYPTOCB_UNAVAILABLE)
            return ret;
        /* fall-through when unavailable */
    }
#endif

#if defined(WOLFSSL_ASYNC_CRYPT) && defined(WC_ASYNC_ENABLE_AES)
    /* if async and byte count above threshold */
    /* only 12-byte IV is supported in HW */
    if (aes->asyncDev.marker == WOLFSSL_ASYNC_MARKER_AES &&
                    sz >= WC_ASYNC_THRESH_AES_GCM && ivSz == GCM_NONCE_MID_SZ) {
    #if defined(HAVE_CAVIUM)
        #ifdef HAVE_CAVIUM_V
        if (authInSz == 20) { /* Nitrox V GCM is only working with 20 byte AAD */
            return NitroxAesGcmEncrypt(aes, out, in, sz,
                (const byte*)aes->devKey, aes->keylen, iv, ivSz,
                authTag, authTagSz, authIn, authInSz);
        }
        #endif
    #elif defined(HAVE_INTEL_QA)
        return IntelQaSymAesGcmEncrypt(&aes->asyncDev, out, in, sz,
            (const byte*)aes->devKey, aes->keylen, iv, ivSz,
            authTag, authTagSz, authIn, authInSz);
    #else /* WOLFSSL_ASYNC_CRYPT_TEST */
        if (wc_AsyncTestInit(&aes->asyncDev, ASYNC_TEST_AES_GCM_ENCRYPT)) {
            WC_ASYNC_TEST* testDev = &aes->asyncDev.test;
            testDev->aes.aes = aes;
            testDev->aes.out = out;
            testDev->aes.in = in;
            testDev->aes.sz = sz;
            testDev->aes.iv = iv;
            testDev->aes.ivSz = ivSz;
            testDev->aes.authTag = authTag;
            testDev->aes.authTagSz = authTagSz;
            testDev->aes.authIn = authIn;
            testDev->aes.authInSz = authInSz;
            return WC_PENDING_E;
        }
    #endif
    }
#endif /* WOLFSSL_ASYNC_CRYPT */

#ifdef STM32_CRYPTO_AES_GCM
    return wc_AesGcmEncrypt_STM32(
        aes, out, in, sz, iv, ivSz,
        authTag, authTagSz, authIn, authInSz);
#endif /* STM32_CRYPTO_AES_GCM */

#ifdef WOLFSSL_AESNI
    #ifdef HAVE_INTEL_AVX2
    if (IS_INTEL_AVX2(intel_flags)) {
        AES_GCM_encrypt_avx2(in, out, authIn, iv, authTag, sz, authInSz, ivSz,
                                 authTagSz, (const byte*)aes->key, aes->rounds);
        return 0;
    }
    else
    #endif
    #ifdef HAVE_INTEL_AVX1
    if (IS_INTEL_AVX1(intel_flags)) {
        AES_GCM_encrypt_avx1(in, out, authIn, iv, authTag, sz, authInSz, ivSz,
                                 authTagSz, (const byte*)aes->key, aes->rounds);
        return 0;
    }
    else
    #endif
    if (haveAESNI) {
        AES_GCM_encrypt(in, out, authIn, iv, authTag, sz, authInSz, ivSz,
                                 authTagSz, (const byte*)aes->key, aes->rounds);
        return 0;
    }
    else
#endif
    {
        return AES_GCM_encrypt_C(aes, out, in, sz, iv, ivSz, authTag, authTagSz,
                                                              authIn, authInSz);
    }
}
#endif



/* AES GCM Decrypt */
#if defined(HAVE_AES_DECRYPT) || defined(HAVE_AESGCM_DECRYPT)
#ifdef FREESCALE_LTC_AES_GCM
int  wc_AesGcmDecrypt(Aes* aes, byte* out, const byte* in, word32 sz,
                   const byte* iv, word32 ivSz,
                   const byte* authTag, word32 authTagSz,
                   const byte* authIn, word32 authInSz)
{
    int ret;
    word32 keySize;
    status_t status;

    /* argument checks */
    /* If the sz is non-zero, both in and out must be set. If sz is 0,
     * in and out are don't cares, as this is is the GMAC case. */
    if (aes == NULL || iv == NULL || (sz != 0 && (in == NULL || out == NULL)) ||
        authTag == NULL || authTagSz > AES_BLOCK_SIZE || authTagSz == 0 ||
        ivSz == 0) {

        return BAD_FUNC_ARG;
    }

    ret = wc_AesGetKeySize(aes, &keySize);
    if (ret != 0) {
        return ret;
    }

    status = LTC_AES_DecryptTagGcm(LTC_BASE, in, out, sz, iv, ivSz,
        authIn, authInSz, (byte*)aes->key, keySize, authTag, authTagSz);

    return (status == kStatus_Success) ? 0 : AES_GCM_AUTH_E;
}

#else

#ifdef STM32_CRYPTO_AES_GCM
/* this function supports inline decrypt */
static int wc_AesGcmDecrypt_STM32(Aes* aes, byte* out,
                                  const byte* in, word32 sz,
                                  const byte* iv, word32 ivSz,
                                  const byte* authTag, word32 authTagSz,
                                  const byte* authIn, word32 authInSz)
{
    int ret;
#ifdef WOLFSSL_STM32_CUBEMX
    int status = HAL_OK;
    CRYP_HandleTypeDef hcryp;
    word32 blocks = sz / AES_BLOCK_SIZE;
#else
    int status = SUCCESS;
    word32 keyCopy[AES_256_KEY_SIZE/sizeof(word32)];
#endif
    word32 keySize;
    word32 partial = sz % AES_BLOCK_SIZE;
    word32 tag[AES_BLOCK_SIZE/sizeof(word32)];
    word32 partialBlock[AES_BLOCK_SIZE/sizeof(word32)];
    word32 ctr[AES_BLOCK_SIZE/sizeof(word32)];
    word32 ctrInit[AES_BLOCK_SIZE/sizeof(word32)];
    word32 authhdr[AES_BLOCK_SIZE/sizeof(word32)];
    byte* authInPadded = NULL;
    int authPadSz, wasAlloc = 0;

    ret = wc_AesGetKeySize(aes, &keySize);
    if (ret != 0)
        return ret;

#ifdef WOLFSSL_STM32_CUBEMX
    ret = wc_Stm32_Aes_Init(aes, &hcryp);
    if (ret != 0)
        return ret;
#endif

    ret = wolfSSL_CryptHwMutexLock();
    if (ret != 0) {
        return ret;
    }

    XMEMSET(ctr, 0, AES_BLOCK_SIZE);
    if (ivSz == GCM_NONCE_MID_SZ) {
        byte* pCtr = (byte*)ctr;
        XMEMCPY(ctr, iv, ivSz);
        pCtr[AES_BLOCK_SIZE - 1] = 1;
    }
    else {
        GHASH(aes, NULL, 0, iv, ivSz, (byte*)ctr, AES_BLOCK_SIZE);
    }
    XMEMCPY(ctrInit, ctr, sizeof(ctr)); /* save off initial counter for GMAC */

    /* Authentication buffer - must be 4-byte multiple zero padded */
    authPadSz = authInSz % sizeof(word32);
    if (authPadSz != 0) {
        authPadSz = authInSz + sizeof(word32) - authPadSz;
        if (authPadSz <= sizeof(authhdr)) {
            authInPadded = (byte*)authhdr;
        }
        else {
            authInPadded = (byte*)XMALLOC(authPadSz, aes->heap,
                DYNAMIC_TYPE_TMP_BUFFER);
            if (authInPadded == NULL) {
                wolfSSL_CryptHwMutexUnLock();
                return MEMORY_E;
            }
            wasAlloc = 1;
        }
        XMEMSET(authInPadded, 0, authPadSz);
        XMEMCPY(authInPadded, authIn, authInSz);
    } else {
        authPadSz = authInSz;
        authInPadded = (byte*)authIn;
    }

    /* Hardware requires counter + 1 */
    IncrementGcmCounter((byte*)ctr);

#ifdef WOLFSSL_STM32_CUBEMX
    hcryp.Init.pInitVect = (STM_CRYPT_TYPE*)ctr;
    hcryp.Init.Header = (STM_CRYPT_TYPE*)authInPadded;

#if defined(STM32_HAL_V2)
    hcryp.Init.HeaderSize = authPadSz/sizeof(word32);
    hcryp.Init.Algorithm = CRYP_AES_GCM;
    ByteReverseWords(partialBlock, ctr, AES_BLOCK_SIZE);
    hcryp.Init.pInitVect = (STM_CRYPT_TYPE*)partialBlock;
    HAL_CRYP_Init(&hcryp);

    /* GCM payload phase - can handle partial blocks */
    status = HAL_CRYP_Decrypt(&hcryp, (uint32_t*)in,
        (blocks * AES_BLOCK_SIZE) + partial, (uint32_t*)out, STM32_HAL_TIMEOUT);
    if (status == HAL_OK) {
        /* Compute the authTag */
        status = HAL_CRYPEx_AESGCM_GenerateAuthTAG(&hcryp, (uint32_t*)tag,
            STM32_HAL_TIMEOUT);
    }
#elif defined(STM32_CRYPTO_AES_ONLY)
    /* Set the CRYP parameters */
    hcryp.Init.HeaderSize = authPadSz;
    if (authPadSz == 0)
        hcryp.Init.Header = NULL; /* cannot pass pointer when authIn == 0 */
    hcryp.Init.ChainingMode  = CRYP_CHAINMODE_AES_GCM_GMAC;
    hcryp.Init.OperatingMode = CRYP_ALGOMODE_DECRYPT;
    hcryp.Init.GCMCMACPhase  = CRYP_INIT_PHASE;
    HAL_CRYP_Init(&hcryp);

    /* GCM init phase */
    status = HAL_CRYPEx_AES_Auth(&hcryp, NULL, 0, NULL, STM32_HAL_TIMEOUT);
    if (status == HAL_OK) {
        /* GCM header phase */
        hcryp.Init.GCMCMACPhase = CRYP_HEADER_PHASE;
        status = HAL_CRYPEx_AES_Auth(&hcryp, NULL, 0, NULL, STM32_HAL_TIMEOUT);
    }
    if (status == HAL_OK) {
        /* GCM payload phase - blocks */
        hcryp.Init.GCMCMACPhase = CRYP_PAYLOAD_PHASE;
        if (blocks) {
            status = HAL_CRYPEx_AES_Auth(&hcryp, (byte*)in,
                (blocks * AES_BLOCK_SIZE), out, STM32_HAL_TIMEOUT);
        }
    }
    if (status == HAL_OK && (partial != 0 || (sz > 0 && blocks == 0))) {
        /* GCM payload phase - partial remainder */
        XMEMSET(partialBlock, 0, sizeof(partialBlock));
        XMEMCPY(partialBlock, in + (blocks * AES_BLOCK_SIZE), partial);
        status = HAL_CRYPEx_AES_Auth(&hcryp, (byte*)partialBlock, partial,
            (byte*)partialBlock, STM32_HAL_TIMEOUT);
        XMEMCPY(out + (blocks * AES_BLOCK_SIZE), partialBlock, partial);
    }
    if (status == HAL_OK) {
        /* GCM final phase */
        hcryp.Init.GCMCMACPhase = CRYP_FINAL_PHASE;
        status = HAL_CRYPEx_AES_Auth(&hcryp, NULL, sz, (byte*)tag, STM32_HAL_TIMEOUT);
    }
#else
    hcryp.Init.HeaderSize = authPadSz;
    HAL_CRYP_Init(&hcryp);
    if (blocks) {
        /* GCM payload phase - blocks */
        status = HAL_CRYPEx_AESGCM_Decrypt(&hcryp, (byte*)in,
            (blocks * AES_BLOCK_SIZE), out, STM32_HAL_TIMEOUT);
    }
    if (status == HAL_OK && (partial != 0 || blocks == 0)) {
        /* GCM payload phase - partial remainder */
        XMEMSET(partialBlock, 0, sizeof(partialBlock));
        XMEMCPY(partialBlock, in + (blocks * AES_BLOCK_SIZE), partial);
        status = HAL_CRYPEx_AESGCM_Decrypt(&hcryp, (byte*)partialBlock, partial,
            (byte*)partialBlock, STM32_HAL_TIMEOUT);
        XMEMCPY(out + (blocks * AES_BLOCK_SIZE), partialBlock, partial);
    }
    if (status == HAL_OK) {
        /* Compute the authTag */
        status = HAL_CRYPEx_AESGCM_Finish(&hcryp, sz, (byte*)tag, STM32_HAL_TIMEOUT);
    }
#endif

    if (status != HAL_OK)
        ret = AES_GCM_AUTH_E;

    HAL_CRYP_DeInit(&hcryp);

#else /* Standard Peripheral Library */
    ByteReverseWords(keyCopy, (word32*)aes->key, aes->keylen);

    /* Input size and auth size need to be the actual sizes, even though
     * they are not block aligned, because this length (in bits) is used
     * in the final GHASH. */
    status = CRYP_AES_GCM(MODE_DECRYPT, (uint8_t*)ctr,
                         (uint8_t*)keyCopy,      keySize * 8,
                         (uint8_t*)in,           sz,
                         (uint8_t*)authInPadded, authInSz,
                         (uint8_t*)out,          (uint8_t*)tag);
    if (status != SUCCESS)
        ret = AES_GCM_AUTH_E;
#endif /* WOLFSSL_STM32_CUBEMX */

    /* For STM32 GCM fallback to software if partial AES block or IV != 12 */
    if (sz == 0 || partial != 0 || ivSz != GCM_NONCE_MID_SZ) {
        GHASH(aes, authIn, authInSz, in, sz, (byte*)tag, sizeof(tag));
        wc_AesEncrypt(aes, (byte*)ctrInit, (byte*)partialBlock);
        xorbuf(tag, partialBlock, sizeof(tag));
    }

    /* Check authentication tag */
    if (ConstantCompare(authTag, (byte*)tag, authTagSz) != 0) {
        ret = AES_GCM_AUTH_E;
    }

    /* Free memory */
    if (wasAlloc) {
        XFREE(authInPadded, aes->heap, DYNAMIC_TYPE_TMP_BUFFER);
    }

    wolfSSL_CryptHwMutexUnLock();

    return ret;
}

#endif /* STM32_CRYPTO_AES_GCM */

#ifdef WOLFSSL_AESNI
int AES_GCM_decrypt_C(Aes* aes, byte* out, const byte* in, word32 sz,
                      const byte* iv, word32 ivSz,
                      const byte* authTag, word32 authTagSz,
                      const byte* authIn, word32 authInSz);
#else
static
#endif
int AES_GCM_decrypt_C(Aes* aes, byte* out, const byte* in, word32 sz,
                      const byte* iv, word32 ivSz,
                      const byte* authTag, word32 authTagSz,
                      const byte* authIn, word32 authInSz)
{
    int ret = 0;
    word32 blocks = sz / AES_BLOCK_SIZE;
    word32 partial = sz % AES_BLOCK_SIZE;
    const byte* c = in;
    byte* p = out;
    byte counter[AES_BLOCK_SIZE];
    byte initialCounter[AES_BLOCK_SIZE];
    byte *ctr;
    byte scratch[AES_BLOCK_SIZE];
    byte Tprime[AES_BLOCK_SIZE];
    byte EKY0[AES_BLOCK_SIZE];
#ifdef OPENSSL_EXTRA
    word32 aadTemp;
#endif
    ctr = counter;
    XMEMSET(initialCounter, 0, AES_BLOCK_SIZE);
    if (ivSz == GCM_NONCE_MID_SZ) {
        XMEMCPY(initialCounter, iv, ivSz);
        initialCounter[AES_BLOCK_SIZE - 1] = 1;
    }
    else {
#ifdef OPENSSL_EXTRA
        aadTemp = aes->aadLen;
        aes->aadLen = 0;
#endif
        GHASH(aes, NULL, 0, iv, ivSz, initialCounter, AES_BLOCK_SIZE);
#ifdef OPENSSL_EXTRA
        aes->aadLen = aadTemp;
#endif
    }
    XMEMCPY(ctr, initialCounter, AES_BLOCK_SIZE);

    /* Calc the authTag again using the received auth data and the cipher text */
    GHASH(aes, authIn, authInSz, in, sz, Tprime, sizeof(Tprime));
    wc_AesEncrypt(aes, ctr, EKY0);
    xorbuf(Tprime, EKY0, sizeof(Tprime));

#ifdef OPENSSL_EXTRA
    if (!out) {
        /* authenticated, non-confidential data */
        /* store AAD size for next call */
        aes->aadLen = authInSz;
    }
#endif
    if (ConstantCompare(authTag, Tprime, authTagSz) != 0) {
        return AES_GCM_AUTH_E;
    }

#if defined(WOLFSSL_PIC32MZ_CRYPT)
    if (blocks) {
        /* use initial IV for HW, but don't use it below */
        XMEMCPY(aes->reg, ctr, AES_BLOCK_SIZE);

        ret = wc_Pic32AesCrypt(
            aes->key, aes->keylen, aes->reg, AES_BLOCK_SIZE,
            out, in, (blocks * AES_BLOCK_SIZE),
            PIC32_DECRYPTION, PIC32_ALGO_AES, PIC32_CRYPTOALGO_AES_GCM);
        if (ret != 0)
            return ret;
    }
    /* process remainder using partial handling */
#endif

#if defined(HAVE_AES_ECB) && !defined(WOLFSSL_PIC32MZ_CRYPT)
    /* some hardware acceleration can gain performance from doing AES encryption
     * of the whole buffer at once */
    if (c != p && blocks > 0) { /* can not handle inline decryption */
        while (blocks--) {
            IncrementGcmCounter(ctr);
            XMEMCPY(p, ctr, AES_BLOCK_SIZE);
            p += AES_BLOCK_SIZE;
        }

        /* reset number of blocks and then do encryption */
        blocks = sz / AES_BLOCK_SIZE;

        wc_AesEcbEncrypt(aes, out, out, AES_BLOCK_SIZE * blocks);
        xorbuf(out, c, AES_BLOCK_SIZE * blocks);
        c += AES_BLOCK_SIZE * blocks;
    }
    else
#endif /* HAVE_AES_ECB && !PIC32MZ */
    while (blocks--) {
        IncrementGcmCounter(ctr);
    #if !defined(WOLFSSL_PIC32MZ_CRYPT)
        wc_AesEncrypt(aes, ctr, scratch);
        xorbuf(scratch, c, AES_BLOCK_SIZE);
        XMEMCPY(p, scratch, AES_BLOCK_SIZE);
    #endif
        p += AES_BLOCK_SIZE;
        c += AES_BLOCK_SIZE;
    }

    if (partial != 0) {
        IncrementGcmCounter(ctr);
        wc_AesEncrypt(aes, ctr, scratch);
        xorbuf(scratch, c, partial);
        XMEMCPY(p, scratch, partial);
    }

    return ret;
}

/* Software AES - GCM Decrypt */
int wc_AesGcmDecrypt(Aes* aes, byte* out, const byte* in, word32 sz,
                     const byte* iv, word32 ivSz,
                     const byte* authTag, word32 authTagSz,
                     const byte* authIn, word32 authInSz)
{
#ifdef WOLFSSL_AESNI
    int res = AES_GCM_AUTH_E;
#endif

    /* argument checks */
    /* If the sz is non-zero, both in and out must be set. If sz is 0,
     * in and out are don't cares, as this is is the GMAC case. */
    if (aes == NULL || iv == NULL || (sz != 0 && (in == NULL || out == NULL)) ||
        authTag == NULL || authTagSz > AES_BLOCK_SIZE || authTagSz == 0 ||
        ivSz == 0) {

        return BAD_FUNC_ARG;
    }

#ifdef WOLF_CRYPTO_CB
    if (aes->devId != INVALID_DEVID) {
        int ret = wc_CryptoCb_AesGcmDecrypt(aes, out, in, sz, iv, ivSz,
            authTag, authTagSz, authIn, authInSz);
        if (ret != CRYPTOCB_UNAVAILABLE)
            return ret;
        /* fall-through when unavailable */
    }
#endif

#if defined(WOLFSSL_ASYNC_CRYPT) && defined(WC_ASYNC_ENABLE_AES)
    /* if async and byte count above threshold */
    /* only 12-byte IV is supported in HW */
    if (aes->asyncDev.marker == WOLFSSL_ASYNC_MARKER_AES &&
                    sz >= WC_ASYNC_THRESH_AES_GCM && ivSz == GCM_NONCE_MID_SZ) {
    #if defined(HAVE_CAVIUM)
        #ifdef HAVE_CAVIUM_V
        if (authInSz == 20) { /* Nitrox V GCM is only working with 20 byte AAD */
            return NitroxAesGcmDecrypt(aes, out, in, sz,
                (const byte*)aes->devKey, aes->keylen, iv, ivSz,
                authTag, authTagSz, authIn, authInSz);
        }
        #endif
    #elif defined(HAVE_INTEL_QA)
        return IntelQaSymAesGcmDecrypt(&aes->asyncDev, out, in, sz,
            (const byte*)aes->devKey, aes->keylen, iv, ivSz,
            authTag, authTagSz, authIn, authInSz);
    #else /* WOLFSSL_ASYNC_CRYPT_TEST */
        if (wc_AsyncTestInit(&aes->asyncDev, ASYNC_TEST_AES_GCM_DECRYPT)) {
            WC_ASYNC_TEST* testDev = &aes->asyncDev.test;
            testDev->aes.aes = aes;
            testDev->aes.out = out;
            testDev->aes.in = in;
            testDev->aes.sz = sz;
            testDev->aes.iv = iv;
            testDev->aes.ivSz = ivSz;
            testDev->aes.authTag = (byte*)authTag;
            testDev->aes.authTagSz = authTagSz;
            testDev->aes.authIn = authIn;
            testDev->aes.authInSz = authInSz;
            return WC_PENDING_E;
        }
    #endif
    }
#endif /* WOLFSSL_ASYNC_CRYPT */

#ifdef STM32_CRYPTO_AES_GCM
    /* The STM standard peripheral library API's doesn't support partial blocks */
    return wc_AesGcmDecrypt_STM32(
        aes, out, in, sz, iv, ivSz,
        authTag, authTagSz, authIn, authInSz);
#endif /* STM32_CRYPTO_AES_GCM */

#ifdef WOLFSSL_AESNI
    #ifdef HAVE_INTEL_AVX2
    if (IS_INTEL_AVX2(intel_flags)) {
        AES_GCM_decrypt_avx2(in, out, authIn, iv, authTag, sz, authInSz, ivSz,
                                 authTagSz, (byte*)aes->key, aes->rounds, &res);
        if (res == 0)
            return AES_GCM_AUTH_E;
        return 0;
    }
    else
    #endif
    #ifdef HAVE_INTEL_AVX1
    if (IS_INTEL_AVX1(intel_flags)) {
        AES_GCM_decrypt_avx1(in, out, authIn, iv, authTag, sz, authInSz, ivSz,
                                 authTagSz, (byte*)aes->key, aes->rounds, &res);
        if (res == 0)
            return AES_GCM_AUTH_E;
        return 0;
    }
    else
    #endif
    if (haveAESNI) {
        AES_GCM_decrypt(in, out, authIn, iv, authTag, sz, authInSz, ivSz,
                                 authTagSz, (byte*)aes->key, aes->rounds, &res);
        if (res == 0)
            return AES_GCM_AUTH_E;
        return 0;
    }
    else
#endif
    {
        return AES_GCM_decrypt_C(aes, out, in, sz, iv, ivSz, authTag, authTagSz,
                                                              authIn, authInSz);
    }
}
#endif
#endif /* HAVE_AES_DECRYPT || HAVE_AESGCM_DECRYPT */
#endif /* WOLFSSL_XILINX_CRYPT */
#endif /* end of block for AESGCM implementation selection */


/* Common to all, abstract functions that build off of lower level AESGCM
 * functions */
#ifndef WC_NO_RNG

int wc_AesGcmSetExtIV(Aes* aes, const byte* iv, word32 ivSz)
{
    int ret = 0;

    if (aes == NULL || iv == NULL ||
        (ivSz != GCM_NONCE_MIN_SZ && ivSz != GCM_NONCE_MID_SZ &&
         ivSz != GCM_NONCE_MAX_SZ)) {

        ret = BAD_FUNC_ARG;
    }

    if (ret == 0) {
        XMEMCPY((byte*)aes->reg, iv, ivSz);

        /* If the IV is 96, allow for a 2^64 invocation counter.
         * For any other size for the nonce, limit the invocation
         * counter to 32-bits. (SP 800-38D 8.3) */
        aes->invokeCtr[0] = 0;
        aes->invokeCtr[1] = (ivSz == GCM_NONCE_MID_SZ) ? 0 : 0xFFFFFFFF;
        aes->nonceSz = ivSz;
    }

    return ret;
}


int wc_AesGcmSetIV(Aes* aes, word32 ivSz,
                   const byte* ivFixed, word32 ivFixedSz,
                   WC_RNG* rng)
{
    int ret = 0;

    if (aes == NULL || rng == NULL ||
        (ivSz != GCM_NONCE_MIN_SZ && ivSz != GCM_NONCE_MID_SZ &&
         ivSz != GCM_NONCE_MAX_SZ) ||
        (ivFixed == NULL && ivFixedSz != 0) ||
        (ivFixed != NULL && ivFixedSz != AES_IV_FIXED_SZ)) {

        ret = BAD_FUNC_ARG;
    }

    if (ret == 0) {
        byte* iv = (byte*)aes->reg;

        if (ivFixedSz)
            XMEMCPY(iv, ivFixed, ivFixedSz);

        ret = wc_RNG_GenerateBlock(rng, iv + ivFixedSz, ivSz - ivFixedSz);
    }

    if (ret == 0) {
        /* If the IV is 96, allow for a 2^64 invocation counter.
         * For any other size for the nonce, limit the invocation
         * counter to 32-bits. (SP 800-38D 8.3) */
        aes->invokeCtr[0] = 0;
        aes->invokeCtr[1] = (ivSz == GCM_NONCE_MID_SZ) ? 0 : 0xFFFFFFFF;
        aes->nonceSz = ivSz;
    }

    return ret;
}


int wc_AesGcmEncrypt_ex(Aes* aes, byte* out, const byte* in, word32 sz,
                        byte* ivOut, word32 ivOutSz,
                        byte* authTag, word32 authTagSz,
                        const byte* authIn, word32 authInSz)
{
    int ret = 0;

    if (aes == NULL || (sz != 0 && (in == NULL || out == NULL)) ||
        ivOut == NULL || ivOutSz != aes->nonceSz ||
        (authIn == NULL && authInSz != 0)) {

        ret = BAD_FUNC_ARG;
    }

    if (ret == 0) {
        aes->invokeCtr[0]++;
        if (aes->invokeCtr[0] == 0) {
            aes->invokeCtr[1]++;
            if (aes->invokeCtr[1] == 0)
                ret = AES_GCM_OVERFLOW_E;
        }
    }

    if (ret == 0) {
        XMEMCPY(ivOut, aes->reg, ivOutSz);
        ret = wc_AesGcmEncrypt(aes, out, in, sz,
                               (byte*)aes->reg, ivOutSz,
                               authTag, authTagSz,
                               authIn, authInSz);
        if (ret == 0)
            IncCtr((byte*)aes->reg, ivOutSz);
    }

    return ret;
}

int wc_Gmac(const byte* key, word32 keySz, byte* iv, word32 ivSz,
            const byte* authIn, word32 authInSz,
            byte* authTag, word32 authTagSz, WC_RNG* rng)
{
    Aes aes;
    int ret;

    if (key == NULL || iv == NULL || (authIn == NULL && authInSz != 0) ||
        authTag == NULL || authTagSz == 0 || rng == NULL) {

        return BAD_FUNC_ARG;
    }

    ret = wc_AesInit(&aes, NULL, INVALID_DEVID);
    if (ret == 0) {
        ret = wc_AesGcmSetKey(&aes, key, keySz);
        if (ret == 0)
            ret = wc_AesGcmSetIV(&aes, ivSz, NULL, 0, rng);
        if (ret == 0)
            ret = wc_AesGcmEncrypt_ex(&aes, NULL, NULL, 0, iv, ivSz,
                                  authTag, authTagSz, authIn, authInSz);
        wc_AesFree(&aes);
    }
    ForceZero(&aes, sizeof(aes));

    return ret;
}

int wc_GmacVerify(const byte* key, word32 keySz,
                  const byte* iv, word32 ivSz,
                  const byte* authIn, word32 authInSz,
                  const byte* authTag, word32 authTagSz)
{
    int ret;
#ifndef NO_AES_DECRYPT
    Aes aes;

    if (key == NULL || iv == NULL || (authIn == NULL && authInSz != 0) ||
        authTag == NULL || authTagSz == 0 || authTagSz > AES_BLOCK_SIZE) {

        return BAD_FUNC_ARG;
    }

    ret = wc_AesInit(&aes, NULL, INVALID_DEVID);
    if (ret == 0) {
        ret = wc_AesGcmSetKey(&aes, key, keySz);
        if (ret == 0)
            ret = wc_AesGcmDecrypt(&aes, NULL, NULL, 0, iv, ivSz,
                                  authTag, authTagSz, authIn, authInSz);
        wc_AesFree(&aes);
    }
    ForceZero(&aes, sizeof(aes));
#else
    (void)key;
    (void)keySz;
    (void)iv;
    (void)ivSz;
    (void)authIn;
    (void)authInSz;
    (void)authTag;
    (void)authTagSz;
    ret = NOT_COMPILED_IN;
#endif
    return ret;
}

#endif /* WC_NO_RNG */


WOLFSSL_API int wc_GmacSetKey(Gmac* gmac, const byte* key, word32 len)
{
    if (gmac == NULL || key == NULL) {
        return BAD_FUNC_ARG;
    }
    return wc_AesGcmSetKey(&gmac->aes, key, len);
}


WOLFSSL_API int wc_GmacUpdate(Gmac* gmac, const byte* iv, word32 ivSz,
                              const byte* authIn, word32 authInSz,
                              byte* authTag, word32 authTagSz)
{
    return wc_AesGcmEncrypt(&gmac->aes, NULL, NULL, 0, iv, ivSz,
                                         authTag, authTagSz, authIn, authInSz);
}

#endif /* HAVE_AESGCM */


#ifdef HAVE_AESCCM

int wc_AesCcmSetKey(Aes* aes, const byte* key, word32 keySz)
{
    if (!((keySz == 16) || (keySz == 24) || (keySz == 32)))
        return BAD_FUNC_ARG;

    return wc_AesSetKey(aes, key, keySz, NULL, AES_ENCRYPTION);
}


/* Checks if the tag size is an accepted value based on RFC 3610 section 2
 * returns 0 if tag size is ok
 */
int wc_AesCcmCheckTagSize(int sz)
{
    /* values here are from RFC 3610 section 2 */
    if (sz != 4 && sz != 6 && sz != 8 && sz != 10 && sz != 12 && sz != 14
            && sz != 16) {
        WOLFSSL_MSG("Bad auth tag size AES-CCM");
        return BAD_FUNC_ARG;
    }
    return 0;
}

#ifdef WOLFSSL_ARMASM
    /* implementation located in wolfcrypt/src/port/arm/armv8-aes.c */

#elif defined(HAVE_COLDFIRE_SEC)
    #error "Coldfire SEC doesn't currently support AES-CCM mode"

#elif defined(WOLFSSL_IMX6_CAAM) && !defined(NO_IMX6_CAAM_AES)
    /* implemented in wolfcrypt/src/port/caam_aes.c */

#elif defined(FREESCALE_LTC)

/* return 0 on success */
int wc_AesCcmEncrypt(Aes* aes, byte* out, const byte* in, word32 inSz,
                   const byte* nonce, word32 nonceSz,
                   byte* authTag, word32 authTagSz,
                   const byte* authIn, word32 authInSz)
{
    byte *key;
    uint32_t keySize;
    status_t status;

    /* sanity check on arguments */
    if (aes == NULL || out == NULL || in == NULL || nonce == NULL
            || authTag == NULL || nonceSz < 7 || nonceSz > 13)
        return BAD_FUNC_ARG;

    if (wc_AesCcmCheckTagSize(authTagSz) != 0) {
        return BAD_FUNC_ARG;
    }

    key = (byte*)aes->key;

    status = wc_AesGetKeySize(aes, &keySize);
    if (status != 0) {
        return status;
    }

    status = LTC_AES_EncryptTagCcm(LTC_BASE, in, out, inSz,
        nonce, nonceSz, authIn, authInSz, key, keySize, authTag, authTagSz);

    return (kStatus_Success == status) ? 0 : BAD_FUNC_ARG;
}

#ifdef HAVE_AES_DECRYPT
int  wc_AesCcmDecrypt(Aes* aes, byte* out, const byte* in, word32 inSz,
                   const byte* nonce, word32 nonceSz,
                   const byte* authTag, word32 authTagSz,
                   const byte* authIn, word32 authInSz)
{
    byte *key;
    uint32_t keySize;
    status_t status;

    /* sanity check on arguments */
    if (aes == NULL || out == NULL || in == NULL || nonce == NULL
            || authTag == NULL || nonceSz < 7 || nonceSz > 13)
        return BAD_FUNC_ARG;

    key = (byte*)aes->key;

    status = wc_AesGetKeySize(aes, &keySize);
    if (status != 0) {
        return status;
    }

    status = LTC_AES_DecryptTagCcm(LTC_BASE, in, out, inSz,
        nonce, nonceSz, authIn, authInSz, key, keySize, authTag, authTagSz);

    if (status == kStatus_Success) {
        return 0;
    }
    else {
        XMEMSET(out, 0, inSz);
        return AES_CCM_AUTH_E;
    }
}
#endif /* HAVE_AES_DECRYPT */

#else

/* Software CCM */
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

#ifdef WOLFSSL_AESNI
static WC_INLINE void AesCcmCtrIncSet4(byte* B, word32 lenSz)
{
    word32 i;

    /* B+1 = B */
    XMEMCPY(B + AES_BLOCK_SIZE * 1, B, AES_BLOCK_SIZE);
    /* B+2,B+3 = B,B+1 */
    XMEMCPY(B + AES_BLOCK_SIZE * 2, B, AES_BLOCK_SIZE * 2);

    for (i = 0; i < lenSz; i++) {
        if (++B[AES_BLOCK_SIZE * 2 - 1 - i] != 0) break;
    }
    B[AES_BLOCK_SIZE * 3 - 1] += 2;
    if (B[AES_BLOCK_SIZE * 3 - 1] < 2) {
        for (i = 1; i < lenSz; i++) {
            if (++B[AES_BLOCK_SIZE * 3 - 1 - i] != 0) break;
        }
    }
    B[AES_BLOCK_SIZE * 4 - 1] += 3;
    if (B[AES_BLOCK_SIZE * 4 - 1] < 3) {
        for (i = 1; i < lenSz; i++) {
            if (++B[AES_BLOCK_SIZE * 4 - 1 - i] != 0) break;
        }
    }
}

static WC_INLINE void AesCcmCtrInc4(byte* B, word32 lenSz)
{
    word32 i;

    B[AES_BLOCK_SIZE - 1] += 4;
    if (B[AES_BLOCK_SIZE - 1] < 4) {
        for (i = 1; i < lenSz; i++) {
            if (++B[AES_BLOCK_SIZE - 1 - i] != 0) break;
        }
    }
}
#endif

/* Software AES - CCM Encrypt */
/* return 0 on success */
int wc_AesCcmEncrypt(Aes* aes, byte* out, const byte* in, word32 inSz,
                   const byte* nonce, word32 nonceSz,
                   byte* authTag, word32 authTagSz,
                   const byte* authIn, word32 authInSz)
{
#ifndef WOLFSSL_AESNI
    byte A[AES_BLOCK_SIZE];
    byte B[AES_BLOCK_SIZE];
#else
    ALIGN128 byte A[AES_BLOCK_SIZE * 4];
    ALIGN128 byte B[AES_BLOCK_SIZE * 4];
#endif
    byte lenSz;
    word32 i;
    byte mask = 0xFF;
    const word32 wordSz = (word32)sizeof(word32);

    /* sanity check on arguments */
    if (aes == NULL || out == NULL || in == NULL || nonce == NULL
            || authTag == NULL || nonceSz < 7 || nonceSz > 13 ||
            authTagSz > AES_BLOCK_SIZE)
        return BAD_FUNC_ARG;

    /* sanity check on tag size */
    if (wc_AesCcmCheckTagSize(authTagSz) != 0) {
        return BAD_FUNC_ARG;
    }

    XMEMSET(A, 0, sizeof(A));
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
#ifdef WOLFSSL_AESNI
    if (haveAESNI && aes->use_aesni) {
        while (inSz >= AES_BLOCK_SIZE * 4) {
            AesCcmCtrIncSet4(B, lenSz);

            AES_ECB_encrypt(B, A, AES_BLOCK_SIZE * 4, (byte*)aes->key,
                            aes->rounds);
            xorbuf(A, in, AES_BLOCK_SIZE * 4);
            XMEMCPY(out, A, AES_BLOCK_SIZE * 4);

            inSz -= AES_BLOCK_SIZE * 4;
            in += AES_BLOCK_SIZE * 4;
            out += AES_BLOCK_SIZE * 4;

            AesCcmCtrInc4(B, lenSz);
        }
    }
#endif
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
/* Software AES - CCM Decrypt */
int  wc_AesCcmDecrypt(Aes* aes, byte* out, const byte* in, word32 inSz,
                   const byte* nonce, word32 nonceSz,
                   const byte* authTag, word32 authTagSz,
                   const byte* authIn, word32 authInSz)
{
#ifndef WOLFSSL_AESNI
    byte A[AES_BLOCK_SIZE];
    byte B[AES_BLOCK_SIZE];
#else
    ALIGN128 byte B[AES_BLOCK_SIZE * 4];
    ALIGN128 byte A[AES_BLOCK_SIZE * 4];
#endif
    byte* o;
    byte lenSz;
    word32 i, oSz;
    int result = 0;
    byte mask = 0xFF;
    const word32 wordSz = (word32)sizeof(word32);

    /* sanity check on arguments */
    if (aes == NULL || out == NULL || in == NULL || nonce == NULL
            || authTag == NULL || nonceSz < 7 || nonceSz > 13 ||
            authTagSz > AES_BLOCK_SIZE)
        return BAD_FUNC_ARG;

    /* sanity check on tag size */
    if (wc_AesCcmCheckTagSize(authTagSz) != 0) {
        return BAD_FUNC_ARG;
    }

    o = out;
    oSz = inSz;
    XMEMCPY(B+1, nonce, nonceSz);
    lenSz = AES_BLOCK_SIZE - 1 - (byte)nonceSz;

    B[0] = lenSz - 1;
    for (i = 0; i < lenSz; i++)
        B[AES_BLOCK_SIZE - 1 - i] = 0;
    B[15] = 1;

#ifdef WOLFSSL_AESNI
    if (haveAESNI && aes->use_aesni) {
        while (oSz >= AES_BLOCK_SIZE * 4) {
            AesCcmCtrIncSet4(B, lenSz);

            AES_ECB_encrypt(B, A, AES_BLOCK_SIZE * 4, (byte*)aes->key,
                            aes->rounds);
            xorbuf(A, in, AES_BLOCK_SIZE * 4);
            XMEMCPY(o, A, AES_BLOCK_SIZE * 4);

            oSz -= AES_BLOCK_SIZE * 4;
            in += AES_BLOCK_SIZE * 4;
            o += AES_BLOCK_SIZE * 4;

            AesCcmCtrInc4(B, lenSz);
        }
    }
#endif
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
#endif /* software CCM */

/* abstract functions that call lower level AESCCM functions */
#ifndef WC_NO_RNG

int wc_AesCcmSetNonce(Aes* aes, const byte* nonce, word32 nonceSz)
{
    int ret = 0;

    if (aes == NULL || nonce == NULL ||
        nonceSz < CCM_NONCE_MIN_SZ || nonceSz > CCM_NONCE_MAX_SZ) {

        ret = BAD_FUNC_ARG;
    }

    if (ret == 0) {
        XMEMCPY(aes->reg, nonce, nonceSz);
        aes->nonceSz = nonceSz;

        /* Invocation counter should be 2^61 */
        aes->invokeCtr[0] = 0;
        aes->invokeCtr[1] = 0xE0000000;
    }

    return ret;
}


int wc_AesCcmEncrypt_ex(Aes* aes, byte* out, const byte* in, word32 sz,
                        byte* ivOut, word32 ivOutSz,
                        byte* authTag, word32 authTagSz,
                        const byte* authIn, word32 authInSz)
{
    int ret = 0;

    if (aes == NULL || out == NULL ||
        (in == NULL && sz != 0) ||
        ivOut == NULL ||
        (authIn == NULL && authInSz != 0) ||
        (ivOutSz != aes->nonceSz)) {

        ret = BAD_FUNC_ARG;
    }

    if (ret == 0) {
        aes->invokeCtr[0]++;
        if (aes->invokeCtr[0] == 0) {
            aes->invokeCtr[1]++;
            if (aes->invokeCtr[1] == 0)
                ret = AES_CCM_OVERFLOW_E;
        }
    }

    if (ret == 0) {
        ret = wc_AesCcmEncrypt(aes, out, in, sz,
                               (byte*)aes->reg, aes->nonceSz,
                               authTag, authTagSz,
                               authIn, authInSz);
        if (ret == 0) {
            XMEMCPY(ivOut, aes->reg, aes->nonceSz);
            IncCtr((byte*)aes->reg, aes->nonceSz);
        }
    }

    return ret;
}

#endif /* WC_NO_RNG */

#endif /* HAVE_AESCCM */


/* Initialize Aes for use with async hardware */
int wc_AesInit(Aes* aes, void* heap, int devId)
{
    int ret = 0;

    if (aes == NULL)
        return BAD_FUNC_ARG;

    aes->heap = heap;

#ifdef WOLF_CRYPTO_CB
    aes->devId = devId;
    aes->devCtx = NULL;
#else
    (void)devId;
#endif
#if defined(WOLFSSL_ASYNC_CRYPT) && defined(WC_ASYNC_ENABLE_AES)
    ret = wolfAsync_DevCtxInit(&aes->asyncDev, WOLFSSL_ASYNC_MARKER_AES,
                                                        aes->heap, devId);
#endif /* WOLFSSL_ASYNC_CRYPT */

#ifdef WOLFSSL_AFALG
    aes->alFd = -1;
    aes->rdFd = -1;
#endif
#if defined(WOLFSSL_DEVCRYPTO) && \
   (defined(WOLFSSL_DEVCRYPTO_AES) || defined(WOLFSSL_DEVCRYPTO_CBC))
    aes->ctx.cfd = -1;
#endif
#if defined(WOLFSSL_CRYPTOCELL) && defined(WOLFSSL_CRYPTOCELL_AES)
    XMEMSET(&aes->ctx, 0, sizeof(aes->ctx));
#endif
#ifdef HAVE_AESGCM
#ifdef OPENSSL_EXTRA
    XMEMSET(aes->aadH, 0, sizeof(aes->aadH));
    aes->aadLen = 0;
#endif
#endif
    return ret;
}

#ifdef HAVE_PKCS11
int  wc_AesInit_Id(Aes* aes, unsigned char* id, int len, void* heap, int devId)
{
    int ret = 0;

    if (aes == NULL)
        ret = BAD_FUNC_ARG;
    if (ret == 0 && (len < 0 || len > AES_MAX_ID_LEN))
        ret = BUFFER_E;

    if (ret == 0)
        ret  = wc_AesInit(aes, heap, devId);
    if (ret == 0) {
        XMEMCPY(aes->id, id, len);
        aes->idLen = len;
    }

    return ret;
}
#endif

/* Free Aes from use with async hardware */
void wc_AesFree(Aes* aes)
{
    if (aes == NULL)
        return;

#if defined(WOLFSSL_ASYNC_CRYPT) && defined(WC_ASYNC_ENABLE_AES)
    wolfAsync_DevCtxFree(&aes->asyncDev, WOLFSSL_ASYNC_MARKER_AES);
#endif /* WOLFSSL_ASYNC_CRYPT */
#if defined(WOLFSSL_AFALG) || defined(WOLFSSL_AFALG_XILINX_AES)
    if (aes->rdFd > 0) { /* negative is error case */
        close(aes->rdFd);
    }
    if (aes->alFd > 0) {
        close(aes->alFd);
    }
#endif /* WOLFSSL_AFALG */
#if defined(WOLFSSL_DEVCRYPTO) && \
    (defined(WOLFSSL_DEVCRYPTO_AES) || defined(WOLFSSL_DEVCRYPTO_CBC))
    wc_DevCryptoFree(&aes->ctx);
#endif
#if defined(WOLF_CRYPTO_CB) || (defined(WOLFSSL_DEVCRYPTO) && \
    (defined(WOLFSSL_DEVCRYPTO_AES) || defined(WOLFSSL_DEVCRYPTO_CBC))) || \
    (defined(WOLFSSL_ASYNC_CRYPT) && defined(WC_ASYNC_ENABLE_AES))
    ForceZero((byte*)aes->devKey, AES_MAX_KEY_SIZE/WOLFSSL_BIT_SIZE);
#endif
}


int wc_AesGetKeySize(Aes* aes, word32* keySize)
{
    int ret = 0;

    if (aes == NULL || keySize == NULL) {
        return BAD_FUNC_ARG;
    }
#if defined(WOLFSSL_CRYPTOCELL) && defined(WOLFSSL_CRYPTOCELL_AES)
    *keySize = aes->ctx.key.keySize;
    return ret;
#endif
    switch (aes->rounds) {
#ifdef WOLFSSL_AES_128
    case 10:
        *keySize = 16;
        break;
#endif
#ifdef WOLFSSL_AES_192
    case 12:
        *keySize = 24;
        break;
#endif
#ifdef WOLFSSL_AES_256
    case 14:
        *keySize = 32;
        break;
#endif
    default:
        *keySize = 0;
        ret = BAD_FUNC_ARG;
    }

    return ret;
}

#endif /* !WOLFSSL_TI_CRYPT */

#ifdef HAVE_AES_ECB
#if defined(WOLFSSL_IMX6_CAAM) && !defined(NO_IMX6_CAAM_AES)
    /* implemented in wolfcrypt/src/port/caam/caam_aes.c */

#elif defined(WOLFSSL_AFALG)
    /* implemented in wolfcrypt/src/port/af_alg/afalg_aes.c */

#elif defined(WOLFSSL_DEVCRYPTO_AES)
    /* implemented in wolfcrypt/src/port/devcrypt/devcrypto_aes.c */

#elif defined(WOLFSSL_SCE) && !defined(WOLFSSL_SCE_NO_AES)

/* Software AES - ECB */
int wc_AesEcbEncrypt(Aes* aes, byte* out, const byte* in, word32 sz)
{
    if ((in == NULL) || (out == NULL) || (aes == NULL))
        return BAD_FUNC_ARG;

        return AES_ECB_encrypt(aes, in, out, sz);
}


int wc_AesEcbDecrypt(Aes* aes, byte* out, const byte* in, word32 sz)
{
    if ((in == NULL) || (out == NULL) || (aes == NULL))
        return BAD_FUNC_ARG;

        return AES_ECB_decrypt(aes, in, out, sz);
}

#else

/* Software AES - ECB */
int wc_AesEcbEncrypt(Aes* aes, byte* out, const byte* in, word32 sz)
{
    word32 blocks = sz / AES_BLOCK_SIZE;

    if ((in == NULL) || (out == NULL) || (aes == NULL))
      return BAD_FUNC_ARG;
    while (blocks>0) {
      wc_AesEncryptDirect(aes, out, in);
      out += AES_BLOCK_SIZE;
      in  += AES_BLOCK_SIZE;
      sz  -= AES_BLOCK_SIZE;
      blocks--;
    }
    return 0;
}


int wc_AesEcbDecrypt(Aes* aes, byte* out, const byte* in, word32 sz)
{
    word32 blocks = sz / AES_BLOCK_SIZE;

    if ((in == NULL) || (out == NULL) || (aes == NULL))
      return BAD_FUNC_ARG;
    while (blocks>0) {
      wc_AesDecryptDirect(aes, out, in);
      out += AES_BLOCK_SIZE;
      in  += AES_BLOCK_SIZE;
      sz  -= AES_BLOCK_SIZE;
      blocks--;
    }
    return 0;
}
#endif
#endif /* HAVE_AES_ECB */

#if defined(WOLFSSL_AES_CFB) || defined(WOLFSSL_AES_OFB)
/* Feedback AES mode
 *
 * aes structure holding key to use for encryption
 * out buffer to hold result of encryption (must be at least as large as input
 *     buffer)
 * in  buffer to encrypt
 * sz  size of input buffer
 * mode flag to specify AES mode
 *
 * returns 0 on success and negative error values on failure
 */
/* Software AES - CFB Encrypt */
static int wc_AesFeedbackEncrypt(Aes* aes, byte* out, const byte* in,
        word32 sz, byte mode)
{
    byte*  tmp = NULL;
#ifdef WOLFSSL_AES_CFB
    byte*  reg = NULL;
#endif

    if (aes == NULL || out == NULL || in == NULL) {
        return BAD_FUNC_ARG;
    }

#ifdef WOLFSSL_AES_CFB
    if (aes->left && sz) {
        reg = (byte*)aes->reg + AES_BLOCK_SIZE - aes->left;
    }
#endif

    /* consume any unused bytes left in aes->tmp */
    tmp = (byte*)aes->tmp + AES_BLOCK_SIZE - aes->left;
    while (aes->left && sz) {
        *(out) = *(in++) ^ *(tmp++);
    #ifdef WOLFSSL_AES_CFB
        if (mode == AES_CFB_MODE) {
            *(reg++) = *out;
        }
    #endif
        out++;
        aes->left--;
        sz--;
    }

    while (sz >= AES_BLOCK_SIZE) {
        /* Using aes->tmp here for inline case i.e. in=out */
        wc_AesEncryptDirect(aes, (byte*)aes->tmp, (byte*)aes->reg);
    #ifdef WOLFSSL_AES_OFB
        if (mode == AES_OFB_MODE) {
            XMEMCPY(aes->reg, aes->tmp, AES_BLOCK_SIZE);
        }
    #endif
        xorbuf((byte*)aes->tmp, in, AES_BLOCK_SIZE);
    #ifdef WOLFSSL_AES_CFB
        if (mode == AES_CFB_MODE) {
            XMEMCPY(aes->reg, aes->tmp, AES_BLOCK_SIZE);
        }
    #endif
        XMEMCPY(out, aes->tmp, AES_BLOCK_SIZE);
        out += AES_BLOCK_SIZE;
        in  += AES_BLOCK_SIZE;
        sz  -= AES_BLOCK_SIZE;
        aes->left = 0;
    }

    /* encrypt left over data */
    if (sz) {
        wc_AesEncryptDirect(aes, (byte*)aes->tmp, (byte*)aes->reg);
        aes->left = AES_BLOCK_SIZE;
        tmp = (byte*)aes->tmp;
    #ifdef WOLFSSL_AES_OFB
        if (mode == AES_OFB_MODE) {
            XMEMCPY(aes->reg, aes->tmp, AES_BLOCK_SIZE);
        }
    #endif
    #ifdef WOLFSSL_AES_CFB
        reg = (byte*)aes->reg;
    #endif

        while (sz--) {
            *(out) = *(in++) ^ *(tmp++);
        #ifdef WOLFSSL_AES_CFB
            if (mode == AES_CFB_MODE) {
                *(reg++) = *out;
            }
        #endif
            out++;
            aes->left--;
        }
    }

    return 0;
}


#ifdef HAVE_AES_DECRYPT
/* CFB 128
 *
 * aes structure holding key to use for decryption
 * out buffer to hold result of decryption (must be at least as large as input
 *     buffer)
 * in  buffer to decrypt
 * sz  size of input buffer
 *
 * returns 0 on success and negative error values on failure
 */
/* Software AES - CFB Decrypt */
static int wc_AesFeedbackDecrypt(Aes* aes, byte* out, const byte* in, word32 sz,
        byte mode)
{
    byte*  tmp;

    if (aes == NULL || out == NULL || in == NULL) {
        return BAD_FUNC_ARG;
    }

    #ifdef WOLFSSL_AES_CFB
    /* check if more input needs copied over to aes->reg */
    if (aes->left && sz && mode == AES_CFB_MODE) {
        int size = min(aes->left, sz);
        XMEMCPY((byte*)aes->reg + AES_BLOCK_SIZE - aes->left, in, size);
    }
    #endif

    /* consume any unused bytes left in aes->tmp */
    tmp = (byte*)aes->tmp + AES_BLOCK_SIZE - aes->left;
    while (aes->left && sz) {
        *(out++) = *(in++) ^ *(tmp++);
        aes->left--;
        sz--;
    }

    while (sz > AES_BLOCK_SIZE) {
        /* Using aes->tmp here for inline case i.e. in=out */
        wc_AesEncryptDirect(aes, (byte*)aes->tmp, (byte*)aes->reg);
    #ifdef WOLFSSL_AES_OFB
        if (mode == AES_OFB_MODE) {
            XMEMCPY((byte*)aes->reg, (byte*)aes->tmp, AES_BLOCK_SIZE);
        }
    #endif
        xorbuf((byte*)aes->tmp, in, AES_BLOCK_SIZE);
    #ifdef WOLFSSL_AES_CFB
        if (mode == AES_CFB_MODE) {
            XMEMCPY(aes->reg, in, AES_BLOCK_SIZE);
        }
    #endif
        XMEMCPY(out, (byte*)aes->tmp, AES_BLOCK_SIZE);
        out += AES_BLOCK_SIZE;
        in  += AES_BLOCK_SIZE;
        sz  -= AES_BLOCK_SIZE;
        aes->left = 0;
    }

    /* decrypt left over data */
    if (sz) {
        wc_AesEncryptDirect(aes, (byte*)aes->tmp, (byte*)aes->reg);
    #ifdef WOLFSSL_AES_CFB
        if (mode == AES_CFB_MODE) {
            XMEMCPY(aes->reg, in, sz);
        }
    #endif
    #ifdef WOLFSSL_AES_OFB
        if (mode == AES_OFB_MODE) {
            XMEMCPY(aes->reg, aes->tmp, AES_BLOCK_SIZE);
        }
    #endif

        aes->left = AES_BLOCK_SIZE;
        tmp = (byte*)aes->tmp;

        while (sz--) {
            *(out++) = *(in++) ^ *(tmp++);
            aes->left--;
        }
    }

    return 0;
}
#endif /* HAVE_AES_DECRYPT */
#endif /* WOLFSSL_AES_CFB */

#ifdef WOLFSSL_AES_CFB
/* CFB 128
 *
 * aes structure holding key to use for encryption
 * out buffer to hold result of encryption (must be at least as large as input
 *     buffer)
 * in  buffer to encrypt
 * sz  size of input buffer
 *
 * returns 0 on success and negative error values on failure
 */
/* Software AES - CFB Encrypt */
int wc_AesCfbEncrypt(Aes* aes, byte* out, const byte* in, word32 sz)
{
    return wc_AesFeedbackEncrypt(aes, out, in, sz, AES_CFB_MODE);
}


#ifdef HAVE_AES_DECRYPT
/* CFB 128
 *
 * aes structure holding key to use for decryption
 * out buffer to hold result of decryption (must be at least as large as input
 *     buffer)
 * in  buffer to decrypt
 * sz  size of input buffer
 *
 * returns 0 on success and negative error values on failure
 */
/* Software AES - CFB Decrypt */
int wc_AesCfbDecrypt(Aes* aes, byte* out, const byte* in, word32 sz)
{
    return wc_AesFeedbackDecrypt(aes, out, in, sz, AES_CFB_MODE);
}
#endif /* HAVE_AES_DECRYPT */


/* shift the whole AES_BLOCK_SIZE array left by 8 or 1 bits */
static void shiftLeftArray(byte* ary, byte shift)
{
    int i;

    if (shift == WOLFSSL_BIT_SIZE) {
        /* shifting over by 8 bits */
        for (i = 0; i < AES_BLOCK_SIZE - 1; i++) {
            ary[i] = ary[i+1];
        }
        ary[i] = 0;
    }
    else {
        byte carry = 0;

        /* shifting over by 7 or less bits */
        for (i = 0; i < AES_BLOCK_SIZE - 1; i++) {
            carry = ary[i+1] & (0XFF << (WOLFSSL_BIT_SIZE - shift));
            carry >>= (WOLFSSL_BIT_SIZE - shift);
            ary[i] = (ary[i] << shift) + carry;
        }
        ary[i] = ary[i] << shift;
    }
}


/* returns 0 on success and negative values on failure */
static int wc_AesFeedbackCFB8(Aes* aes, byte* out, const byte* in,
        word32 sz, byte dir)
{
    byte *pt;

    if (aes == NULL || out == NULL || in == NULL) {
        return BAD_FUNC_ARG;
    }

    if (sz == 0) {
        return 0;
    }

    while (sz > 0) {
        wc_AesEncryptDirect(aes, (byte*)aes->tmp, (byte*)aes->reg);
        if (dir == AES_DECRYPTION) {
            pt = (byte*)aes->reg;

            /* LSB + CAT */
            shiftLeftArray(pt, WOLFSSL_BIT_SIZE);
            pt[AES_BLOCK_SIZE - 1] = in[0];
        }

        /* MSB + XOR */
        out[0] = aes->tmp[0] ^ in[0];
        if (dir == AES_ENCRYPTION) {
            pt = (byte*)aes->reg;

            /* LSB + CAT */
            shiftLeftArray(pt, WOLFSSL_BIT_SIZE);
            pt[AES_BLOCK_SIZE - 1] = out[0];
        }

        out += 1;
        in  += 1;
        sz  -= 1;
    }

    return 0;
}


/* returns 0 on success and negative values on failure */
static int wc_AesFeedbackCFB1(Aes* aes, byte* out, const byte* in,
        word32 sz, byte dir)
{
    byte tmp;
    byte cur = 0; /* hold current work in order to handle inline in=out */
    byte* pt;
    int bit = 7;

    if (aes == NULL || out == NULL || in == NULL) {
        return BAD_FUNC_ARG;
    }

    if (sz == 0) {
        return 0;
    }

    while (sz > 0) {
        wc_AesEncryptDirect(aes, (byte*)aes->tmp, (byte*)aes->reg);
        if (dir == AES_DECRYPTION) {
            pt = (byte*)aes->reg;

            /* LSB + CAT */
            tmp = (0X01 << bit) & in[0];
            tmp = tmp >> bit;
            tmp &= 0x01;
            shiftLeftArray((byte*)aes->reg, 1);
            pt[AES_BLOCK_SIZE - 1] |= tmp;
        }

        /* MSB  + XOR */
        tmp = (0X01 << bit) & in[0];
        pt = (byte*)aes->tmp;
        tmp = (pt[0] >> 7) ^ (tmp >> bit);
        tmp &= 0x01;
        cur |= (tmp << bit);


        if (dir == AES_ENCRYPTION) {
            pt = (byte*)aes->reg;

            /* LSB + CAT */
            shiftLeftArray((byte*)aes->reg, 1);
            pt[AES_BLOCK_SIZE - 1] |= tmp;
        }

        bit--;
        if (bit < 0) {
            out[0] = cur;
            out += 1;
            in  += 1;
            sz  -= 1;
            bit = 7;
            cur = 0;
        }
        else {
            sz -= 1;
        }
    }

    if (bit > 0 && bit < 7) {
        out[0] = cur;
    }

    return 0;
}


/* CFB 1
 *
 * aes structure holding key to use for encryption
 * out buffer to hold result of encryption (must be at least as large as input
 *     buffer)
 * in  buffer to encrypt (packed to left, i.e. 101 is 0x90)
 * sz  size of input buffer in bits (0x1 would be size of 1 and 0xFF size of 8)
 *
 * returns 0 on success and negative values on failure
 */
int wc_AesCfb1Encrypt(Aes* aes, byte* out, const byte* in, word32 sz)
{
    return wc_AesFeedbackCFB1(aes, out, in, sz, AES_ENCRYPTION);
}


/* CFB 8
 *
 * aes structure holding key to use for encryption
 * out buffer to hold result of encryption (must be at least as large as input
 *     buffer)
 * in  buffer to encrypt
 * sz  size of input buffer
 *
 * returns 0 on success and negative values on failure
 */
int wc_AesCfb8Encrypt(Aes* aes, byte* out, const byte* in, word32 sz)
{
    return wc_AesFeedbackCFB8(aes, out, in, sz, AES_ENCRYPTION);
}
#ifdef HAVE_AES_DECRYPT

/* CFB 1
 *
 * aes structure holding key to use for encryption
 * out buffer to hold result of encryption (must be at least as large as input
 *     buffer)
 * in  buffer to encrypt
 * sz  size of input buffer in bits (0x1 would be size of 1 and 0xFF size of 8)
 *
 * returns 0 on success and negative values on failure
 */
int wc_AesCfb1Decrypt(Aes* aes, byte* out, const byte* in, word32 sz)
{
    return wc_AesFeedbackCFB1(aes, out, in, sz, AES_DECRYPTION);
}


/* CFB 8
 *
 * aes structure holding key to use for encryption
 * out buffer to hold result of encryption (must be at least as large as input
 *     buffer)
 * in  buffer to encrypt
 * sz  size of input buffer
 *
 * returns 0 on success and negative values on failure
 */
int wc_AesCfb8Decrypt(Aes* aes, byte* out, const byte* in, word32 sz)
{
    return wc_AesFeedbackCFB8(aes, out, in, sz, AES_DECRYPTION);
}
#endif /* HAVE_AES_DECRYPT */
#endif /* WOLFSSL_AES_CFB */

#ifdef WOLFSSL_AES_OFB
/* OFB
 *
 * aes structure holding key to use for encryption
 * out buffer to hold result of encryption (must be at least as large as input
 *     buffer)
 * in  buffer to encrypt
 * sz  size of input buffer
 *
 * returns 0 on success and negative error values on failure
 */
/* Software AES - CFB Encrypt */
int wc_AesOfbEncrypt(Aes* aes, byte* out, const byte* in, word32 sz)
{
    return wc_AesFeedbackEncrypt(aes, out, in, sz, AES_OFB_MODE);
}


#ifdef HAVE_AES_DECRYPT
/* OFB
 *
 * aes structure holding key to use for decryption
 * out buffer to hold result of decryption (must be at least as large as input
 *     buffer)
 * in  buffer to decrypt
 * sz  size of input buffer
 *
 * returns 0 on success and negative error values on failure
 */
/* Software AES - OFB Decrypt */
int wc_AesOfbDecrypt(Aes* aes, byte* out, const byte* in, word32 sz)
{
    return wc_AesFeedbackDecrypt(aes, out, in, sz, AES_OFB_MODE);
}
#endif /* HAVE_AES_DECRYPT */
#endif /* WOLFSSL_AES_OFB */


#ifdef HAVE_AES_KEYWRAP

/* Initialize key wrap counter with value */
static WC_INLINE void InitKeyWrapCounter(byte* inOutCtr, word32 value)
{
    int i;
    word32 bytes;

    bytes = sizeof(word32);
    for (i = 0; i < (int)sizeof(word32); i++) {
        inOutCtr[i+sizeof(word32)] = (value >> ((bytes - 1) * 8)) & 0xFF;
        bytes--;
    }
}

/* Increment key wrap counter */
static WC_INLINE void IncrementKeyWrapCounter(byte* inOutCtr)
{
    int i;

    /* in network byte order so start at end and work back */
    for (i = KEYWRAP_BLOCK_SIZE - 1; i >= 0; i--) {
        if (++inOutCtr[i])  /* we're done unless we overflow */
            return;
    }
}

/* Decrement key wrap counter */
static WC_INLINE void DecrementKeyWrapCounter(byte* inOutCtr)
{
    int i;

    for (i = KEYWRAP_BLOCK_SIZE - 1; i >= 0; i--) {
        if (--inOutCtr[i] != 0xFF)  /* we're done unless we underflow */
            return;
    }
}

/* perform AES key wrap (RFC3394), return out sz on success, negative on err */
int wc_AesKeyWrap(const byte* key, word32 keySz, const byte* in, word32 inSz,
                  byte* out, word32 outSz, const byte* iv)
{
    Aes aes;
    byte* r;
    word32 i;
    int ret, j;

    byte t[KEYWRAP_BLOCK_SIZE];
    byte tmp[AES_BLOCK_SIZE];

    /* n must be at least 2, output size is n + 8 bytes */
    if (key == NULL || in  == NULL || inSz < 2 ||
        out == NULL || outSz < (inSz + KEYWRAP_BLOCK_SIZE))
        return BAD_FUNC_ARG;

    /* input must be multiple of 64-bits */
    if (inSz % KEYWRAP_BLOCK_SIZE != 0)
        return BAD_FUNC_ARG;

    /* user IV is optional */
    if (iv == NULL) {
        XMEMSET(tmp, 0xA6, KEYWRAP_BLOCK_SIZE);
    } else {
        XMEMCPY(tmp, iv, KEYWRAP_BLOCK_SIZE);
    }

    r = out + 8;
    XMEMCPY(r, in, inSz);
    XMEMSET(t, 0, sizeof(t));

    ret = wc_AesInit(&aes, NULL, INVALID_DEVID);
    if (ret != 0)
        return ret;

    ret = wc_AesSetKey(&aes, key, keySz, NULL, AES_ENCRYPTION);
    if (ret != 0)
        return ret;

    for (j = 0; j <= 5; j++) {
        for (i = 1; i <= inSz / KEYWRAP_BLOCK_SIZE; i++) {

            /* load R[i] */
            XMEMCPY(tmp + KEYWRAP_BLOCK_SIZE, r, KEYWRAP_BLOCK_SIZE);

            wc_AesEncryptDirect(&aes, tmp, tmp);

            /* calculate new A */
            IncrementKeyWrapCounter(t);
            xorbuf(tmp, t, KEYWRAP_BLOCK_SIZE);

            /* save R[i] */
            XMEMCPY(r, tmp + KEYWRAP_BLOCK_SIZE, KEYWRAP_BLOCK_SIZE);
            r += KEYWRAP_BLOCK_SIZE;
        }
        r = out + KEYWRAP_BLOCK_SIZE;
    }

    /* C[0] = A */
    XMEMCPY(out, tmp, KEYWRAP_BLOCK_SIZE);

    wc_AesFree(&aes);

    return inSz + KEYWRAP_BLOCK_SIZE;
}

int wc_AesKeyUnWrap(const byte* key, word32 keySz, const byte* in, word32 inSz,
                    byte* out, word32 outSz, const byte* iv)
{
    Aes aes;
    byte* r;
    word32 i, n;
    int ret, j;

    byte t[KEYWRAP_BLOCK_SIZE];
    byte tmp[AES_BLOCK_SIZE];

    const byte* expIv;
    const byte defaultIV[] = {
        0xA6, 0xA6, 0xA6, 0xA6, 0xA6, 0xA6, 0xA6, 0xA6
    };

    (void)iv;

    if (key == NULL || in == NULL || inSz < 3 ||
        out == NULL || outSz < (inSz - KEYWRAP_BLOCK_SIZE))
        return BAD_FUNC_ARG;

    /* input must be multiple of 64-bits */
    if (inSz % KEYWRAP_BLOCK_SIZE != 0)
        return BAD_FUNC_ARG;

    /* user IV optional */
    if (iv != NULL) {
        expIv = iv;
    } else {
        expIv = defaultIV;
    }

    /* A = C[0], R[i] = C[i] */
    XMEMCPY(tmp, in, KEYWRAP_BLOCK_SIZE);
    XMEMCPY(out, in + KEYWRAP_BLOCK_SIZE, inSz - KEYWRAP_BLOCK_SIZE);
    XMEMSET(t, 0, sizeof(t));

    ret = wc_AesInit(&aes, NULL, INVALID_DEVID);
    if (ret != 0)
        return ret;

    ret = wc_AesSetKey(&aes, key, keySz, NULL, AES_DECRYPTION);
    if (ret != 0)
        return ret;

    /* initialize counter to 6n */
    n = (inSz - 1) / KEYWRAP_BLOCK_SIZE;
    InitKeyWrapCounter(t, 6 * n);

    for (j = 5; j >= 0; j--) {
        for (i = n; i >= 1; i--) {

            /* calculate A */
            xorbuf(tmp, t, KEYWRAP_BLOCK_SIZE);
            DecrementKeyWrapCounter(t);

            /* load R[i], starting at end of R */
            r = out + ((i - 1) * KEYWRAP_BLOCK_SIZE);
            XMEMCPY(tmp + KEYWRAP_BLOCK_SIZE, r, KEYWRAP_BLOCK_SIZE);
            wc_AesDecryptDirect(&aes, tmp, tmp);

            /* save R[i] */
            XMEMCPY(r, tmp + KEYWRAP_BLOCK_SIZE, KEYWRAP_BLOCK_SIZE);
        }
    }

    wc_AesFree(&aes);

    /* verify IV */
    if (XMEMCMP(tmp, expIv, KEYWRAP_BLOCK_SIZE) != 0)
        return BAD_KEYWRAP_IV_E;

    return inSz - KEYWRAP_BLOCK_SIZE;
}

#endif /* HAVE_AES_KEYWRAP */

#ifdef WOLFSSL_AES_XTS

/* Galios Field to use */
#define GF_XTS 0x87

/* This is to help with setting keys to correct encrypt or decrypt type.
 *
 * tweak AES key for tweak in XTS
 * aes   AES key for encrypt/decrypt process
 * key   buffer holding aes key | tweak key
 * len   length of key buffer in bytes. Should be twice that of key size. i.e.
 *       32 for a 16 byte key.
 * dir   direction, either AES_ENCRYPTION or AES_DECRYPTION
 * heap  heap hint to use for memory. Can be NULL
 * devId id to use with async crypto. Can be 0
 *
 * Note: is up to user to call wc_AesFree on tweak and aes key when done.
 *
 * return 0 on success
 */
int wc_AesXtsSetKey(XtsAes* aes, const byte* key, word32 len, int dir,
        void* heap, int devId)
{
    word32 keySz;
    int    ret = 0;

    if (aes == NULL || key == NULL) {
        return BAD_FUNC_ARG;
    }

    if ((ret = wc_AesInit(&aes->tweak, heap, devId)) != 0) {
        return ret;
    }
    if ((ret = wc_AesInit(&aes->aes, heap, devId)) != 0) {
        return ret;
    }

    keySz = len/2;
    if (keySz != 16 && keySz != 32) {
        WOLFSSL_MSG("Unsupported key size");
        return WC_KEY_SIZE_E;
    }

    if ((ret = wc_AesSetKey(&aes->aes, key, keySz, NULL, dir)) == 0) {
        ret = wc_AesSetKey(&aes->tweak, key + keySz, keySz, NULL,
                AES_ENCRYPTION);
        if (ret != 0) {
            wc_AesFree(&aes->aes);
        }
    }

    return ret;
}


/* This is used to free up resources used by Aes structs
 *
 * aes AES keys to free
 *
 * return 0 on success
 */
int wc_AesXtsFree(XtsAes* aes)
{
    if (aes != NULL) {
        wc_AesFree(&aes->aes);
        wc_AesFree(&aes->tweak);
    }

    return 0;
}


/* Same process as wc_AesXtsEncrypt but uses a word64 type as the tweak value
 * instead of a byte array. This just converts the word64 to a byte array and
 * calls wc_AesXtsEncrypt.
 *
 * aes    AES keys to use for block encrypt/decrypt
 * out    output buffer to hold cipher text
 * in     input plain text buffer to encrypt
 * sz     size of both out and in buffers
 * sector value to use for tweak
 *
 * returns 0 on success
 */
int wc_AesXtsEncryptSector(XtsAes* aes, byte* out, const byte* in,
        word32 sz, word64 sector)
{
    byte* pt;
    byte  i[AES_BLOCK_SIZE];

    XMEMSET(i, 0, AES_BLOCK_SIZE);
#ifdef BIG_ENDIAN_ORDER
    sector = ByteReverseWord64(sector);
#endif
    pt = (byte*)&sector;
    XMEMCPY(i, pt, sizeof(word64));

    return wc_AesXtsEncrypt(aes, out, in, sz, (const byte*)i, AES_BLOCK_SIZE);
}


/* Same process as wc_AesXtsDecrypt but uses a word64 type as the tweak value
 * instead of a byte array. This just converts the word64 to a byte array.
 *
 * aes    AES keys to use for block encrypt/decrypt
 * out    output buffer to hold plain text
 * in     input cipher text buffer to encrypt
 * sz     size of both out and in buffers
 * sector value to use for tweak
 *
 * returns 0 on success
 */
int wc_AesXtsDecryptSector(XtsAes* aes, byte* out, const byte* in, word32 sz,
        word64 sector)
{
    byte* pt;
    byte  i[AES_BLOCK_SIZE];

    XMEMSET(i, 0, AES_BLOCK_SIZE);
#ifdef BIG_ENDIAN_ORDER
    sector = ByteReverseWord64(sector);
#endif
    pt = (byte*)&sector;
    XMEMCPY(i, pt, sizeof(word64));

    return wc_AesXtsDecrypt(aes, out, in, sz, (const byte*)i, AES_BLOCK_SIZE);
}

#ifdef HAVE_AES_ECB
/* helper function for encrypting / decrypting full buffer at once */
static int _AesXtsHelper(Aes* aes, byte* out, const byte* in, word32 sz, int dir)
{
    word32 outSz   = sz;
    word32 totalSz = (sz / AES_BLOCK_SIZE) * AES_BLOCK_SIZE; /* total bytes */
    byte*  pt      = out;

    outSz -= AES_BLOCK_SIZE;

    while (outSz > 0) {
        word32 j;
        byte carry = 0;

        /* multiply by shift left and propagate carry */
        for (j = 0; j < AES_BLOCK_SIZE && outSz > 0; j++, outSz--) {
            byte tmpC;

            tmpC   = (pt[j] >> 7) & 0x01;
            pt[j+AES_BLOCK_SIZE] = ((pt[j] << 1) + carry) & 0xFF;
            carry  = tmpC;
        }
        if (carry) {
            pt[AES_BLOCK_SIZE] ^= GF_XTS;
        }

        pt += AES_BLOCK_SIZE;
    }

    xorbuf(out, in, totalSz);
    if (dir == AES_ENCRYPTION) {
        return wc_AesEcbEncrypt(aes, out, out, totalSz);
    }
    else {
        return wc_AesEcbDecrypt(aes, out, out, totalSz);
    }
}
#endif /* HAVE_AES_ECB */


/* AES with XTS mode. (XTS) XEX encryption with Tweak and cipher text Stealing.
 *
 * xaes  AES keys to use for block encrypt/decrypt
 * out   output buffer to hold cipher text
 * in    input plain text buffer to encrypt
 * sz    size of both out and in buffers
 * i     value to use for tweak
 * iSz   size of i buffer, should always be AES_BLOCK_SIZE but having this input
 *       adds a sanity check on how the user calls the function.
 *
 * returns 0 on success
 */
/* Software AES - XTS Encrypt  */
int wc_AesXtsEncrypt(XtsAes* xaes, byte* out, const byte* in, word32 sz,
        const byte* i, word32 iSz)
{
    int ret = 0;
    word32 blocks = (sz / AES_BLOCK_SIZE);
    Aes *aes, *tweak;

    if (xaes == NULL || out == NULL || in == NULL) {
        return BAD_FUNC_ARG;
    }

    aes   = &xaes->aes;
    tweak = &xaes->tweak;

    if (iSz < AES_BLOCK_SIZE) {
        return BAD_FUNC_ARG;
    }

    if (blocks > 0) {
        byte tmp[AES_BLOCK_SIZE];

        XMEMSET(tmp, 0, AES_BLOCK_SIZE); /* set to 0's in case of improper AES
                                          * key setup passed to encrypt direct*/

        wc_AesEncryptDirect(tweak, tmp, i);

    #ifdef HAVE_AES_ECB
        /* encrypt all of buffer at once when possible */
        if (in != out) { /* can not handle inline */
            XMEMCPY(out, tmp, AES_BLOCK_SIZE);
            if ((ret = _AesXtsHelper(aes, out, in, sz, AES_ENCRYPTION)) != 0) {
                return ret;
            }
        }
    #endif

        while (blocks > 0) {
            word32 j;
            byte carry = 0;
            byte buf[AES_BLOCK_SIZE];

    #ifdef HAVE_AES_ECB
            if (in == out) { /* check for if inline */
    #endif
            XMEMCPY(buf, in, AES_BLOCK_SIZE);
            xorbuf(buf, tmp, AES_BLOCK_SIZE);
            wc_AesEncryptDirect(aes, out, buf);
    #ifdef HAVE_AES_ECB
            }
    #endif
            xorbuf(out, tmp, AES_BLOCK_SIZE);

            /* multiply by shift left and propagate carry */
            for (j = 0; j < AES_BLOCK_SIZE; j++) {
                byte tmpC;

                tmpC   = (tmp[j] >> 7) & 0x01;
                tmp[j] = ((tmp[j] << 1) + carry) & 0xFF;
                carry  = tmpC;
            }
            if (carry) {
                tmp[0] ^= GF_XTS;
            }

            in  += AES_BLOCK_SIZE;
            out += AES_BLOCK_SIZE;
            sz  -= AES_BLOCK_SIZE;
            blocks--;
        }

        /* stealing operation of XTS to handle left overs */
        if (sz > 0) {
            byte buf[AES_BLOCK_SIZE];

            XMEMCPY(buf, out - AES_BLOCK_SIZE, AES_BLOCK_SIZE);
            if (sz >= AES_BLOCK_SIZE) { /* extra sanity check before copy */
                return BUFFER_E;
            }
            XMEMCPY(out, buf, sz);
            XMEMCPY(buf, in, sz);

            xorbuf(buf, tmp, AES_BLOCK_SIZE);
            wc_AesEncryptDirect(aes, out - AES_BLOCK_SIZE, buf);
            xorbuf(out - AES_BLOCK_SIZE, tmp, AES_BLOCK_SIZE);
        }
    }
    else {
        WOLFSSL_MSG("Plain text input too small for encryption");
        return BAD_FUNC_ARG;
    }

    return ret;
}


/* Same process as encryption but Aes key is AES_DECRYPTION type.
 *
 * xaes  AES keys to use for block encrypt/decrypt
 * out   output buffer to hold plain text
 * in    input cipher text buffer to decrypt
 * sz    size of both out and in buffers
 * i     value to use for tweak
 * iSz   size of i buffer, should always be AES_BLOCK_SIZE but having this input
 *       adds a sanity check on how the user calls the function.
 *
 * returns 0 on success
 */
/* Software AES - XTS Decrypt */
int wc_AesXtsDecrypt(XtsAes* xaes, byte* out, const byte* in, word32 sz,
        const byte* i, word32 iSz)
{
    int ret = 0;
    word32 blocks = (sz / AES_BLOCK_SIZE);
    Aes *aes, *tweak;

    if (xaes == NULL || out == NULL || in == NULL) {
        return BAD_FUNC_ARG;
    }

    aes   = &xaes->aes;
    tweak = &xaes->tweak;

    if (iSz < AES_BLOCK_SIZE) {
        return BAD_FUNC_ARG;
    }

    if (blocks > 0) {
        word32 j;
        byte carry = 0;
        byte tmp[AES_BLOCK_SIZE];
        byte stl = (sz % AES_BLOCK_SIZE);

        XMEMSET(tmp, 0, AES_BLOCK_SIZE); /* set to 0's in case of improper AES
                                          * key setup passed to decrypt direct*/

        wc_AesEncryptDirect(tweak, tmp, i);

        /* if Stealing then break out of loop one block early to handle special
         * case */
        if (stl > 0) {
            blocks--;
        }

    #ifdef HAVE_AES_ECB
        /* decrypt all of buffer at once when possible */
        if (in != out) { /* can not handle inline */
            XMEMCPY(out, tmp, AES_BLOCK_SIZE);
            if ((ret = _AesXtsHelper(aes, out, in, sz, AES_DECRYPTION)) != 0) {
                return ret;
            }
        }
    #endif

        while (blocks > 0) {
            byte buf[AES_BLOCK_SIZE];

    #ifdef HAVE_AES_ECB
            if (in == out) { /* check for if inline */
    #endif
            XMEMCPY(buf, in, AES_BLOCK_SIZE);
            xorbuf(buf, tmp, AES_BLOCK_SIZE);
            wc_AesDecryptDirect(aes, out, buf);
    #ifdef HAVE_AES_ECB
            }
    #endif
            xorbuf(out, tmp, AES_BLOCK_SIZE);

            /* multiply by shift left and propagate carry */
            for (j = 0; j < AES_BLOCK_SIZE; j++) {
                byte tmpC;

                tmpC   = (tmp[j] >> 7) & 0x01;
                tmp[j] = ((tmp[j] << 1) + carry) & 0xFF;
                carry  = tmpC;
            }
            if (carry) {
                tmp[0] ^= GF_XTS;
            }
            carry = 0;

            in  += AES_BLOCK_SIZE;
            out += AES_BLOCK_SIZE;
            sz  -= AES_BLOCK_SIZE;
            blocks--;
        }

        /* stealing operation of XTS to handle left overs */
        if (sz > 0) {
            byte buf[AES_BLOCK_SIZE];
            byte tmp2[AES_BLOCK_SIZE];

            /* multiply by shift left and propagate carry */
            for (j = 0; j < AES_BLOCK_SIZE; j++) {
                byte tmpC;

                tmpC   = (tmp[j] >> 7) & 0x01;
                tmp2[j] = ((tmp[j] << 1) + carry) & 0xFF;
                carry  = tmpC;
            }
            if (carry) {
                tmp2[0] ^= GF_XTS;
            }

            XMEMCPY(buf, in, AES_BLOCK_SIZE);
            xorbuf(buf, tmp2, AES_BLOCK_SIZE);
            wc_AesDecryptDirect(aes, out, buf);
            xorbuf(out, tmp2, AES_BLOCK_SIZE);

            /* tmp2 holds partial | last */
            XMEMCPY(tmp2, out, AES_BLOCK_SIZE);
            in  += AES_BLOCK_SIZE;
            out += AES_BLOCK_SIZE;
            sz  -= AES_BLOCK_SIZE;

            /* Make buffer with end of cipher text | last */
            XMEMCPY(buf, tmp2, AES_BLOCK_SIZE);
            if (sz >= AES_BLOCK_SIZE) { /* extra sanity check before copy */
                return BUFFER_E;
            }
            XMEMCPY(buf, in,   sz);
            XMEMCPY(out, tmp2, sz);

            xorbuf(buf, tmp, AES_BLOCK_SIZE);
            wc_AesDecryptDirect(aes, tmp2, buf);
            xorbuf(tmp2, tmp, AES_BLOCK_SIZE);
            XMEMCPY(out - AES_BLOCK_SIZE, tmp2, AES_BLOCK_SIZE);
        }
    }
    else {
        WOLFSSL_MSG("Plain text input too small for encryption");
        return BAD_FUNC_ARG;
    }

    return ret;
}

#endif /* WOLFSSL_AES_XTS */

#endif /* HAVE_FIPS */
#endif /* !NO_AES */
