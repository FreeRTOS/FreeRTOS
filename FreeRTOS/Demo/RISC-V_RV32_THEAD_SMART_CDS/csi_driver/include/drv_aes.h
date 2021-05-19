/*
 * Copyright (C) 2017-2019 Alibaba Group Holding Limited. All rights reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *   http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */


/******************************************************************************
 * @file     drv_aes.h
 * @brief    Header File for AES Driver
 * @version  V1.0
 * @date     02. June 2017
 * @model    aes
 ******************************************************************************/
#ifndef _CSI_AES_H_
#define _CSI_AES_H_


#include <stdint.h>
#include <drv_common.h>
#include <drv_errno.h>

#ifdef __cplusplus
extern "C" {
#endif

/// definition for aes handle.
typedef void *aes_handle_t;

/****** AES specific error codes *****/
typedef enum {
    AES_ERROR_MODE  = (DRV_ERROR_SPECIFIC + 1),        ///< Specified Mode not supported
    AES_ERROR_DATA_BITS,                               ///< Specified number of Data bits not supported
    AES_ERROR_ENDIAN                                   ///< Specified endian not supported
} aes_error_e;

/*----- AES Control Codes: Mode -----*/
typedef enum {
    AES_MODE_ECB                  = 0,   ///< ECB Mode
    AES_MODE_CBC,                        ///< CBC Mode
    AES_MODE_CFB1,                       ///< CFB1 Mode
    AES_MODE_CFB8,                       ///< CFB8 Mode
    AES_MODE_CFB128,                     ///< CFB128 Mode
    AES_MODE_OFB,                        ///< OFB Mode
    AES_MODE_CTR                         ///< CTR Mode
} aes_mode_e;

/*----- AES Control Codes: Crypto Mode -----*/
typedef enum {
    AES_CRYPTO_MODE_ENCRYPT                  = 0,   ///< encrypt Mode
    AES_CRYPTO_MODE_DECRYPT,                        ///< decrypt Mode
} aes_crypto_mode_e;

/*----- AES Control Codes: Mode Parameters: Key length -----*/
typedef enum {
    AES_KEY_LEN_BITS_128        = 0,      ///< 128 Data bits
    AES_KEY_LEN_BITS_192,                 ///< 192 Data bits
    AES_KEY_LEN_BITS_256                  ///< 256 Data bits
} aes_key_len_bits_e;

/*----- AES Control Codes: Mode Parameters: Endian -----*/
typedef enum {
    AES_ENDIAN_LITTLE          = 0,       ///< Little Endian
    AES_ENDIAN_BIG                        ///< Big Endian
} aes_endian_mode_e;

/**
\brief AES Status
*/
typedef struct {
    uint32_t busy             : 1;        ///< busy flag
} aes_status_t;

/****** AES Event *****/
typedef enum {
    AES_EVENT_CRYPTO_COMPLETE    = 0   ///< Encrypt completed
} aes_event_e;
typedef void (*aes_event_cb_t)(int32_t idx, aes_event_e event);   ///< Pointer to \ref aes_event_cb_t : AES Event call back.


/**
\brief AES Device Driver Capabilities.
*/
typedef struct {
    uint32_t ecb_mode           : 1;      ///< supports ECB mode
    uint32_t cbc_mode           : 1;      ///< supports CBC mode
    uint32_t cfb1_mode          : 1;      ///< supports CFB1 mode
    uint32_t cfb8_mode          : 1;      ///< supports CFB8 mode
    uint32_t cfb128_mode        : 1;      ///< supports CFB128 mode
    uint32_t ofb_mode           : 1;      ///< supports OFB mode
    uint32_t ctr_mode           : 1;      ///< supports CTR mode
    uint32_t bits_128           : 1;      ///< supports 128bits key length
    uint32_t bits_192           : 1;      ///< supports 192bits key length
    uint32_t bits_256           : 1;      ///< supports 256bits key length
} aes_capabilities_t;


// Function documentation

/**
  \brief       Initialize AES Interface. 1. Initializes the resources needed for the AES interface 2.registers event callback function
  \param[in]   idx   device id
  \param[in]   cb_event  event callback function \ref aes_event_cb_t
  \return      if success return aes handle else return NULL
*/
aes_handle_t csi_aes_initialize(int32_t idx, aes_event_cb_t cb_event);

/**
  \brief       De-initialize AES Interface. stops operation and releases the software resources used by the interface
  \param[in]   handle  aes handle to operate.
  \return      error code
*/
int32_t csi_aes_uninitialize(aes_handle_t handle);

/**
  \brief       control aes power.
  \param[in]   handle  aes handle to operate.
  \param[in]   state   power state.\ref csi_power_stat_e.
  \return      error code
*/
int32_t csi_aes_power_control(aes_handle_t handle, csi_power_stat_e state);

/**
  \brief       Get driver capabilities.
  \param[in]   idx device id
  \return      \ref aes_capabilities_t
*/
aes_capabilities_t csi_aes_get_capabilities(int32_t idx);

/**
  \brief       config aes mode.
  \param[in]   handle  aes handle to operate.
  \param[in]   mode      \ref aes_mode_e
  \param[in]   keylen_bits \ref aes_key_len_bits_e
  \param[in]   endian    \ref aes_endian_mode_e
  \return      error code
*/
int32_t csi_aes_config(aes_handle_t handle,
                       aes_mode_e mode,
                       aes_key_len_bits_e keylen_bits,
                       aes_endian_mode_e endian
                      );

/**
  \brief       set crypto key.
  \param[in]   handle    aes handle to operate.
  \param[in]   context   aes information context
  \param[in]   key       Pointer to the key buf
  \param[in]   key_len   Pointer to \ref aes_key_len_bits_e
  \param[in]   enc       \ref aes_crypto_mode_e
  \return      error code
*/
int32_t csi_aes_set_key(aes_handle_t handle, void *context, void *key, aes_key_len_bits_e key_len, aes_crypto_mode_e enc);

/**
  \brief       aes ecb encrypt or decrypt
  \param[in]   handle  aes handle to operate.
  \param[in]   context aes information context
  \param[in]   in   Pointer to the Source data
  \param[out]  out  Pointer to the Result data.
  \param[in]   len  the Source data len.
  \return      error code
*/
int32_t csi_aes_ecb_crypto(aes_handle_t handle, void *context, void *in, void *out, uint32_t len);

/**
  \brief       aes cbc encrypt or decrypt
  \param[in]   handle  aes handle to operate.
  \param[in]   context aes information context
  \param[in]   in   Pointer to the Source data
  \param[out]  out  Pointer to the Result data.
  \param[in]   len  the Source data len.
  \param[in]   iv   Pointer to initialization vector
  \return      error code
*/
int32_t csi_aes_cbc_crypto(aes_handle_t handle, void *context, void *in, void *out, uint32_t len, uint8_t iv[16]);

/**
  \brief       aes cfb1 encrypt or decrypt
  \param[in]   handle  aes handle to operate.
  \param[in]   context aes information context
  \param[in]   in   Pointer to the Source data
  \param[out]  out  Pointer to the Result data.
  \param[in]   len  the Source data len.
  \param[in]   iv   Pointer to initialization vector
  \return      error code
*/
int32_t csi_aes_cfb1_crypto(aes_handle_t handle, void *context, void *in, void *out,  uint32_t len, uint8_t iv[16]);

/**
  \brief       aes cfb8 encrypt or decrypt
  \param[in]   handle  aes handle to operate.
  \param[in]   context aes information context
  \param[in]   in   Pointer to the Source data
  \param[out]  out  Pointer to the Result data.
  \param[in]   len  the Source data len.
  \param[in]   iv   Pointer to initialization vector
  \return      error code
*/
int32_t csi_aes_cfb8_crypto(aes_handle_t handle, void *context, void *in, void *out, uint32_t len, uint8_t iv[16]);

/**
  \brief       aes cfb128 encrypt or decrypt
  \param[in]   handle  aes handle to operate.
  \param[in]   context aes information context
  \param[in]   in   Pointer to the Source data
  \param[out]  out  Pointer to the Result data.
  \param[in]   len  the Source data len.
  \param[in]   iv   Pointer to initialization vector
  \param[in]   num  the number of the 128-bit block we have used
  \return      error code
*/
int32_t csi_aes_cfb128_crypto(aes_handle_t handle, void *context, void *in, void *out, uint32_t len, uint8_t iv[16], uint32_t *num);

/**
  \brief       aes ofb encrypt or decrypt
  \param[in]   handle  aes handle to operate.
  \param[in]   context aes information context
  \param[in]   in   Pointer to the Source data
  \param[out]  out  Pointer to the Result data.
  \param[in]   len  the Source data len.
  \param[in]   iv   Pointer to initialization vector
  \param[in]   num  the number of the 128-bit block we have used
  \return      error code
*/
int32_t csi_aes_ofb_crypto(aes_handle_t handle, void *context, void *in, void *out, uint32_t len, uint8_t iv[16], uint32_t *num);

/**
  \brief       aes ctr encrypt or decrypt
  \param[in]   handle  aes handle to operate.
  \param[in]   context aes information context
  \param[in]   in   Pointer to the Source data
  \param[out]  out  Pointer to the Result data.
  \param[in]   len  the Source data len.
  \param[in]   nonce_counter   Pointer to the 128-bit nonce and counter
  \param[in]   stream_block  Pointer to the saved stream-block for resuming
  \param[in]   num  the number of the 128-bit block we have used
  \return      error code
*/
int32_t csi_aes_ctr_crypto(aes_handle_t handle, void *context, void *in, void *out, uint32_t len, uint8_t nonce_counter[16], uint8_t stream_block[16], uint32_t *num);

/**
  \brief       Get AES status.
  \param[in]   handle  aes handle to operate.
  \return      AES status \ref aes_status_t
*/
aes_status_t csi_aes_get_status(aes_handle_t handle);

#ifdef __cplusplus
}
#endif

#endif /* _CSI_AES_H_ */
