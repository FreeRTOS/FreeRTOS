/* esp32_aes.c
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

#include <string.h>
#include <stdio.h>

#ifdef HAVE_CONFIG_H
    #include <config.h>
#endif
#include <wolfssl/wolfcrypt/settings.h>

#ifndef NO_AES

#if defined(WOLFSSL_ESP32WROOM32_CRYPT) && \
    !defined(NO_WOLFSSL_ESP32WROOM32_CRYPT_AES)

#include <wolfssl/wolfcrypt/aes.h>
#include "wolfssl/wolfcrypt/port/Espressif/esp32-crypt.h"

static const char* TAG = "wolf_hw_aes";
/* mutex */
static wolfSSL_Mutex aes_mutex;
static int espaes_CryptHwMutexInit = 0;

/*
* lock hw engine.
* this should be called before using engine.
*/
static int esp_aes_hw_InUse()
{
    int ret = 0;

    ESP_LOGV(TAG, "enter esp_aes_hw_InUse");

    if(espaes_CryptHwMutexInit == 0) {
        ret = esp_CryptHwMutexInit(&aes_mutex);
        if(ret == 0){
            espaes_CryptHwMutexInit = 1;
        } else {
            ESP_LOGE(TAG, "aes mutx initialization failed.");
            return -1;
        }
    }
    /* lock hardware */
    ret = esp_CryptHwMutexLock(&aes_mutex, portMAX_DELAY);
    if(ret != 0) {
        ESP_LOGE(TAG, "aes engine lock failed.");
        return -1;
    }
    /* Enable AES hardware */
    periph_module_enable(PERIPH_AES_MODULE);

    ESP_LOGV(TAG, "leave esp_aes_hw_InUse");
    return ret;
}

/*
*   release hw engine
*/
static void esp_aes_hw_Leave( void )
{
    ESP_LOGV(TAG, "enter esp_aes_hw_Leave");
    /* Disable AES hardware */
    periph_module_disable(PERIPH_AES_MODULE);

    /* unlock */
    esp_CryptHwMutexUnLock(&aes_mutex);

    ESP_LOGV(TAG, "leave esp_aes_hw_Leave");
}

/*
 * set key to hardware key registers.
 */
static void esp_aes_hw_Set_KeyMode(Aes *ctx, ESP32_AESPROCESS mode)
{
    int i;
    word32 mode_ = 0;

    ESP_LOGV(TAG, "enter esp_aes_hw_Set_KeyMode");

    /* check mode */
    if(mode == ESP32_AES_UPDATEKEY_ENCRYPT) {
        mode_ = 0;
    } else if(mode == ESP32_AES_UPDATEKEY_DECRYPT){
        mode_ = 4;
    } else {
        ESP_LOGE(TAG, "unexpected error.");
        return;
    }

    /* update key */
    for(i=0;i<(ctx->keylen)/sizeof(word32);i++){
        DPORT_REG_WRITE(AES_KEY_BASE + (i*4), *(((word32*)ctx->key) + i));
    }

    /* mode
    *   0       AES-128 Encryption
    *   1       AES-192 Encryption
    *   2       AES-256 Encryption
    *   4       AES-128 Decryption
    *   5       AES-192 Decryption
    *   6       AES-256 Decryption
    */
    switch(ctx->keylen){
        case 24: mode_ += 1; break;
        case 32: mode_ += 2; break;
        default: break;
    }

    DPORT_REG_WRITE(AES_MODE_REG, mode_);
    ESP_LOGV(TAG, "leave esp_aes_hw_Setkey");
}

/*
 * Process a one block of AES
 */
static void esp_aes_bk(const byte* in, byte* out)
{
    const word32 *inwords = (const word32 *)in;
    word32 *outwords      = (word32 *)out;

    ESP_LOGV(TAG, "enter esp_aes_bk");

    /* copy text for encrypting/decrypting blocks */
    DPORT_REG_WRITE(AES_TEXT_BASE, inwords[0]);
    DPORT_REG_WRITE(AES_TEXT_BASE + 4, inwords[1]);
    DPORT_REG_WRITE(AES_TEXT_BASE + 8, inwords[2]);
    DPORT_REG_WRITE(AES_TEXT_BASE + 12, inwords[3]);

    /* start engine */
    DPORT_REG_WRITE(AES_START_REG, 1);

    /* wait until finishing the process */
    while(1) {
        if(DPORT_REG_READ(AES_IDLE_REG) == 1)
            break;
    }

    /* read-out blocks */
    esp_dport_access_read_buffer(outwords, AES_TEXT_BASE, 4);
    ESP_LOGV(TAG, "leave esp_aes_bk");
}

/*
* wc_esp32AesEncrypt
* @brief: a one block encrypt of the input block, into the output block
* @param aes: a pointer of the AES object used to encrypt data
* @param in : a pointer of the input buffer containing plain text to be encrypted
* @param out: a pointer of the output buffer in which to store the cipher text of
*             the encrypted message
*/
int wc_esp32AesEncrypt(Aes *aes, const byte* in, byte* out)
{
    ESP_LOGV(TAG, "enter wc_esp32AesEncrypt");
    /* lock the hw engine */
    esp_aes_hw_InUse();
    /* load the key into the register */
    esp_aes_hw_Set_KeyMode(aes, ESP32_AES_UPDATEKEY_ENCRYPT);
    /* process a one block of AES */
    esp_aes_bk(in, out);
    /* release hw */
    esp_aes_hw_Leave();
    return 0;
}
/*
* wc_esp32AesDecrypt
* @brief: a one block decrypt of the input block, into the output block
* @param aes: a pointer of the AES object used to decrypt data
* @param in : a pointer of the input buffer containing plain text to be decrypted
* @param out: a pointer of the output buffer in which to store the cipher text of
*             the decrypted message
*/
int wc_esp32AesDecrypt(Aes *aes, const byte* in, byte* out)
{
    ESP_LOGV(TAG, "enter wc_esp32AesDecrypt");
    /* lock the hw engine */
    esp_aes_hw_InUse();
    /* load the key into the register */
    esp_aes_hw_Set_KeyMode(aes, ESP32_AES_UPDATEKEY_DECRYPT);
    /* process a one block of AES */
    esp_aes_bk(in, out);
    /* release hw engine */
    esp_aes_hw_Leave();
    return 0;
}
/*
* wc_esp32AesCbcEncrypt
* @brief: Encrypts a plain text message from the input buffer, and places the
*         resulting cipher text into the output buffer using cipher block chaining
*         with AES.
* @param aes: a pointer of the AES object used to encrypt data
* @param out: a pointer of the output buffer in which to store the cipher text of
*             the encrypted message
* @param in : a pointer of the input buffer containing plain text to be encrypted
* @param sz : size of input message
*/
int wc_esp32AesCbcEncrypt(Aes* aes, byte* out, const byte* in, word32 sz)
{
    int i;
    int offset = 0;
    word32 blocks = (sz / AES_BLOCK_SIZE);
    byte *iv;
    byte temp_block[AES_BLOCK_SIZE];

    ESP_LOGV(TAG, "enter wc_esp32AesCbcEncrypt");

    iv      = (byte*)aes->reg;

    esp_aes_hw_InUse();

    esp_aes_hw_Set_KeyMode(aes, ESP32_AES_UPDATEKEY_ENCRYPT);

    while (blocks--) {
          XMEMCPY(temp_block, in + offset, AES_BLOCK_SIZE);

         /* XOR block with IV for CBC */
         for (i = 0; i < AES_BLOCK_SIZE; i++)
             temp_block[i] ^= iv[i];

         esp_aes_bk(temp_block, (out + offset));

         offset += AES_BLOCK_SIZE;

         /* store IV for next block */
         XMEMCPY(iv, out + offset - AES_BLOCK_SIZE, AES_BLOCK_SIZE);
    }

    esp_aes_hw_Leave();
    ESP_LOGV(TAG, "leave wc_esp32AesCbcEncrypt");
    return 0;
}
/*
* wc_esp32AesCbcDecrypt
* @brief: Encrypts a plain text message from the input buffer, and places the
*         resulting cipher text into the output buffer using cipher block chaining
*         with AES.
* @param aes: a pointer of the AES object used to decrypt data
* @param out: a pointer of the output buffer in which to store the cipher text of
*             the decrypted message
* @param in : a pointer of the input buffer containing plain text to be decrypted
* @param sz : size of input message
*/
int wc_esp32AesCbcDecrypt(Aes* aes, byte* out, const byte* in, word32 sz)
{
    int i;
    int offset = 0;
    word32 blocks = (sz / AES_BLOCK_SIZE);
    byte* iv;
    byte temp_block[AES_BLOCK_SIZE];

    ESP_LOGV(TAG, "enter wc_esp32AesCbcDecrypt");

    iv      = (byte*)aes->reg;

    esp_aes_hw_InUse();

    esp_aes_hw_Set_KeyMode(aes, ESP32_AES_UPDATEKEY_DECRYPT);

    while (blocks--) {
        XMEMCPY(temp_block, in + offset, AES_BLOCK_SIZE);

        esp_aes_bk((in + offset), (out + offset));

        /* XOR block with IV for CBC */
        for (i = 0; i < AES_BLOCK_SIZE; i++)
            (out + offset)[i] ^= iv[i];

        /* store IV for next block */
        XMEMCPY(iv, temp_block, AES_BLOCK_SIZE);

        offset += AES_BLOCK_SIZE;
    }

    esp_aes_hw_Leave();
    ESP_LOGV(TAG, "leave wc_esp32AesCbcDecrypt");
    return 0;
}

#endif /* WOLFSSL_ESP32WROOM32_CRYPT */
#endif /* NO_AES */
