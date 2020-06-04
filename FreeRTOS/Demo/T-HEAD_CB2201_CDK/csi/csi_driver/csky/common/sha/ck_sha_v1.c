/*
 * Copyright (C) 2017 C-SKY Microsystems Co., Ltd. All rights reserved.
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
 * @file     ck_sha.c
 * @brief    CSI Source File for SHA Driver
 * @version  V1.0
 * @date     02. June 2017
 ******************************************************************************/
#include <stdio.h>
#include <string.h>
#include <stdbool.h>
#include "csi_core.h"
#include "drv_sha.h"
#include "ck_sha_v1.h"

#ifndef CONFIG_SHA_SUPPORT_MUL_THREAD
#define CONFIG_SHA_SUPPORT_MUL_THREAD   1
#endif

typedef struct {
    uint32_t base;
    uint32_t irq;
    sha_event_cb_t cb;
    sha_status_t status;
    sha_mode_e mode;
    sha_endian_mode_e endian;
#ifdef CONFIG_SHA_SUPPORT_MUL_THREAD
    uint32_t  state[16];
    uint32_t sha_buffer[32];
    uint32_t total;
    uint8_t first_cal;
#endif
} ck_sha_priv_t;

#ifndef CONFIG_SHA_SUPPORT_MUL_THREAD
static ck_sha_priv_t sha_handle[CONFIG_SHA_NUM];
#endif
bool finish_flag = 0;

/* Driver Capabilities */
static const sha_capabilities_t driver_capabilities = {
    .sha1 = 1, /* sha1 mode */
    .sha224 = 1, /* sha224 mode */
    .sha256 = 1, /* sha256 mode */
    .sha384 = 1, /* sha384 mode */
    .sha512 = 1, /* sha512 mode */
    .sha512_224 = 1, /* sha512_224 mode */
    .sha512_256 = 1, /* sha512_256 mode */
    .endianmode = 1, /* endian mode */
    .interruptmode = 1  /* interrupt mode */
};

#define ERR_SHA(errno) (CSI_DRV_ERRNO_SHA_BASE | errno)
#define SHA_NULL_PARAM_CHK(para)                         \
        do {                                        \
            if (para == NULL) {                     \
                return ERR_SHA(EDRV_PARAMETER);   \
            }                                       \
        } while (0)

extern int32_t target_get_sha(int32_t idx, uint32_t *base, uint32_t *irq);
extern int32_t target_get_sha_count(void);
//
// Functions
//

ck_sha_reg_t *sha_reg = NULL;

#ifndef CONFIG_SHA_SUPPORT_MUL_THREAD
static uint32_t sha_buffer[32];
static uint32_t total[2] = {0x0};
static uint8_t first_cal = 1;
#endif
static uint8_t sha_result[64] = {0x0};

static int32_t sha_set_mode(sha_mode_e mode)
{
    sha_reg->SHA_MODE &= ~0x7;
    sha_reg->SHA_MODE |= mode;
    return 0;
}

static void sha_set_source_message(uint32_t baseaddr)
{
    sha_reg->SHA_BASEADDR = baseaddr;
}

static void sha_set_dest_message(uint32_t destaddr)
{
    sha_reg->SHA_DESTADDR = destaddr;
}

static void sha_enable_without_count(void)
{
    sha_reg->SHA_MODE |= 1<<25;
}

static void sha_disable_without_count(void)
{
    sha_reg->SHA_MODE &= ~(1<<25);
}

static void sha_set_message_count(uint32_t count)
{
    sha_reg->SHA_COUNTER0 = count;
    sha_reg->SHA_COUNTER1 = 0;
}

static int32_t sha_enable_initial(void)
{
    sha_reg->SHA_MODE |= 1 << SHA_INIT_OFFSET;
    return 0;
}

static int32_t sha_disable_initial(void)
{
    sha_reg->SHA_MODE &= ~(1 << SHA_INIT_OFFSET);
    return 0;
}

static int32_t sha_enable_calculate(void)
{
    sha_reg->SHA_CON |= 1;
    return 0;
}

static int32_t sha_message_done(void)
{
    while(sha_reg->SHA_CON & 0x1);
    return 0;
}

static void sha_new_encode(void)
{
    sha_reg->SHA_INTSTATE = 0;
    sha_reg->SHA_MODE = 0;
}

#ifdef CONFIG_SHA_SUPPORT_MUL_THREAD
static int32_t sha_restore_context(sha_handle_t handle, uint32_t *data)
{
    uint32_t *result = (uint32_t *)&sha_reg->SHA_H0L;

    uint8_t i;
    for (i = 0; i < 16; i++) {
        result[i] = data[i];
    }
    return 0;
}

static int32_t sha_save_context(sha_handle_t handle, uint32_t *data)
{
    uint32_t *result = (uint32_t *)&sha_reg->SHA_H0L;

    uint8_t i;
    for (i = 0; i < 16; i++) {
        data[i] = result[i];
    }
    return 0;
}
#endif

static inline void sha_reverse_order(uint8_t *pdata, int32_t length)
{
    uint8_t input_data[length];
    uint8_t result[length];
    uint32_t tmp = 0;
    int32_t i = 0;
    memcpy((void *)input_data, (void *)pdata, length);

    for (i = 0; i < length; i++) {
        tmp = i >> 2;
        tmp = tmp << 3;
        result[i] = input_data[tmp + 3 - i];
    }

    memcpy((void *)pdata, (void *)result, length);
}

/**
  \brief       get sha handle count.
  \return      sha handle count
*/
int32_t csi_sha_get_instance_count(void)
{
    return target_get_sha_count();
}

/**
  \brief       Initialize SHA Interface. 1. Initializes the resources needed for the SHA interface 2.registers event callback function
  \param[in]   idx must not exceed return value of csi_sha_get_instance_count()
  \param[in]   cb_event  Pointer to \ref sha_event_cb_t
  \return      return sha handle if success
*/
sha_handle_t csi_sha_initialize(sha_handle_t handle, sha_event_cb_t cb_event)
{
#ifdef CONFIG_SHA_SUPPORT_MUL_THREAD
    uint32_t base = 0u;
    uint32_t irq;
    /* obtain the sha information */
    target_get_sha(0, &base, &irq);
    ck_sha_priv_t *sha_priv = handle;
    memset(sha_priv->state, 0, sizeof(sha_priv->state));
    sha_priv->total = 0;
    sha_priv->first_cal = 1;

#else
    if (idx < 0 || idx >= CONFIG_SHA_NUM) {
        return NULL;
    }

    uint32_t base = 0u;
    uint32_t irq;
    /* obtain the sha information */
    int32_t real_idx = target_get_sha(idx, &base, &irq);

    if (real_idx != idx) {
        return NULL;
    }
    ck_sha_priv_t *sha_priv = &sha_handle[idx];
#endif
    sha_priv->base = base;
    sha_priv->irq  = irq;

    /* initialize the sha context */
    sha_priv->cb = cb_event;
    sha_priv->status.busy = 0;

    return (sha_handle_t)sha_priv;
}

/**
  \brief       De-initialize SHA Interface. stops operation and releases the software resources used by the interface
  \param[in]   handle  sha handle to operate.
  \return      error code
*/
int32_t csi_sha_uninitialize(sha_handle_t handle)
{
    SHA_NULL_PARAM_CHK(handle);

    ck_sha_priv_t *sha_priv = handle;
    sha_priv->cb = NULL;

    return 0;
}

/**
  \brief       Get driver capabilities.
  \param[in]   handle sha handle to operate.
  \return      \ref sha_capabilities_t
*/
sha_capabilities_t csi_sha_get_capabilities(sha_handle_t handle)
{
    return driver_capabilities;
}

/**
  \brief       config sha mode.
  \param[in]   handle  sha handle to operate.
  \param[in]   mode      \ref sha_mode_e
  \param[in]   endian    \ref sha_endian_mode_e
  \return      error code
*/
int32_t csi_sha_config(sha_handle_t handle, sha_mode_e mode, sha_endian_mode_e endian_mode)
{
    SHA_NULL_PARAM_CHK(handle);

    ck_sha_priv_t *sha_priv = handle;
    sha_reg = (ck_sha_reg_t *)(sha_priv->base);

    /* config the sha mode */
    switch (mode) {
        case SHA_MODE_512_256:
        case SHA_MODE_512_224:
            return ERR_SHA(EDRV_UNSUPPORTED);

        case SHA_MODE_1:
        case SHA_MODE_224:
        case SHA_MODE_256:
        case SHA_MODE_384:
        case SHA_MODE_512:
            sha_priv->mode = mode;
            break;

        default:
            return ERR_SHA(EDRV_PARAMETER);
    }

    return 0;
}

/**
  \brief       start the engine
  \param[in]   handle  sha handle to operate.
  \param[in]   context  Pointer to the sha context.
  \return      error code
*/
int32_t csi_sha_starts(sha_handle_t handle, void *context)
{
    SHA_NULL_PARAM_CHK(handle);

    ck_sha_priv_t *sha_priv = handle;
    sha_priv->status.busy = 1;

    sha_new_encode();
    sha_set_mode(sha_priv->mode);

#ifdef CONFIG_SHA_SUPPORT_MUL_THREAD
    memset(sha_priv->sha_buffer, 0, sizeof(sha_priv->sha_buffer));
    memset(sha_priv->state, 0, sizeof(sha_priv->state));
    sha_priv->first_cal = 1;
    sha_priv->total = 0;
#endif

    return 0;
}

/**
  \brief       updata the engine
  \param[in]   handle  sha handle to operate.
  \param[in]   context  Pointer to the sha context.
  \param[in]   input   Pointer to the Source data
  \param[in]   len    the data len
  \return      error code
*/
int32_t csi_sha_update(sha_handle_t handle, void *context, const void *input, uint32_t len)
{
    SHA_NULL_PARAM_CHK(handle);
    SHA_NULL_PARAM_CHK(input);
    if (len <= 0) {
        return ERR_SHA(EDRV_PARAMETER);
    }

    ck_sha_priv_t *sha_priv = handle;
    sha_reg = (ck_sha_reg_t *)(sha_priv->base);

    uint8_t total_len_num;
    uint32_t block_size;
    if (sha_priv->mode < 4) {
        block_size = 64;
        total_len_num = 2;
    } else {
        block_size = 128;
        total_len_num = 4;
    }

#ifdef CONFIG_SHA_SUPPORT_MUL_THREAD
    uint32_t *sha_buffer = sha_priv->sha_buffer;
    uint8_t first_cal = sha_priv->first_cal;
    sha_set_mode(sha_priv->mode);
    uint32_t left = sha_priv->total & (block_size - 1);
    uint32_t fill = block_size - left;
    uint32_t total_length = sha_priv->total << 3;
    uint32_t index = left >> 2;

    if (left & 0x3) {
        index++;
    }
    sha_priv->total += len;
    sha_priv->total &= 0xffffffff;
#else
    uint32_t left = total[0] & (block_size - 1);
    uint32_t fill = block_size - left;
    uint32_t total_length = total[0] << 3;
    uint32_t index = left >> 2;

    if (left & 0x3) {
        index++;
    }
    total[0] += len;
    total[0] &= 0xffffffff;
#endif
    uint8_t *p = (uint8_t *)input;
    /* when the text is not aligned by block and len > fill */
    if (left && len >= fill) {
        if (finish_flag) {
#ifdef CONFIG_SHA_SUPPORT_MUL_THREAD
            memset(((uint8_t *)sha_buffer + left), 0x0, sizeof(sha_priv->sha_buffer) - left);
#else
            memset(((uint8_t *)sha_buffer + left), 0x0, sizeof(sha_buffer) - left);
#endif
            sha_buffer[index + total_len_num - 1] = total_length;

            sha_disable_without_count();
            sha_set_message_count(left << 3);
        } else {
            memcpy((void *)(((uint8_t *)sha_buffer) + left), p, fill);
            p += fill;

            sha_enable_without_count();
            sha_set_message_count(block_size << 3);
        }

        sha_set_source_message((uint32_t)sha_buffer);
        sha_set_dest_message((uint32_t)sha_result);
        if (first_cal == 0) {
            sha_enable_initial();
        } else {
            sha_disable_initial();
        }

#ifdef CONFIG_SHA_SUPPORT_MUL_THREAD
        sha_restore_context(handle, (uint32_t *)sha_priv->state);
#endif

        sha_enable_calculate();
        sha_message_done();

#ifdef CONFIG_SHA_SUPPORT_MUL_THREAD
        sha_save_context(handle, (uint32_t *)sha_priv->state);
#endif
        len -= fill;
        left = 0;
#ifdef CONFIG_SHA_SUPPORT_MUL_THREAD
        sha_priv->first_cal = 0;
        first_cal = 0;
#else
        first_cal = 0;
#endif
    }

    /* calculate the hash by block */
    while (len >= block_size) {
        if (finish_flag) {
#ifdef CONFIG_SHA_SUPPORT_MUL_THREAD
            memset(sha_buffer, 0, sizeof(sha_priv->sha_buffer));
#else
            memset(sha_buffer, 0, sizeof(sha_buffer));
#endif
            sha_buffer[total_len_num - 1] = total_length;

            sha_set_source_message((uint32_t)sha_buffer);
            sha_disable_without_count();
            sha_set_message_count(0);
        } else {
            memcpy(sha_buffer, p, block_size);
            sha_set_source_message((uint32_t)sha_buffer);
            sha_enable_without_count();
            sha_set_message_count(block_size << 3);
            p += block_size;
        }
        sha_set_dest_message((uint32_t)sha_result);
        if (first_cal == 0) {
            sha_enable_initial();
        } else {
            sha_disable_initial();
        }
#ifdef CONFIG_SHA_SUPPORT_MUL_THREAD
        sha_restore_context(handle, (uint32_t *)sha_priv->state);
#endif

        sha_enable_calculate();
        sha_message_done();
#ifdef CONFIG_SHA_SUPPORT_MUL_THREAD
        sha_save_context(handle, (uint32_t *)sha_priv->state);
#endif
#ifdef CONFIG_SHA_SUPPORT_MUL_THREAD
        sha_priv->first_cal = 0;
        first_cal = 0;
#else
        first_cal = 0;
#endif
        len -= block_size;
    }

    /* when the text is not aligned by block and len < fill */
    if (len > 0) {
        memcpy((void *)(((uint8_t *)sha_buffer) + left), p, len);
    }

    sha_priv->status.busy = 0;

    return 0;
}

/**
  \brief       finish the engine
  \param[in]   handle  sha handle to operate.
  \param[in]   context  Pointer to the sha context.
  \param[out]  output   Pointer to the dest data
  \return      error code
*/
int32_t csi_sha_finish(sha_handle_t handle, void *context, void *output)
{
    SHA_NULL_PARAM_CHK(handle);
    SHA_NULL_PARAM_CHK(output);

    ck_sha_priv_t *sha_priv = handle;
    uint32_t block_size;
    if (sha_priv->mode < 4) {
        block_size = 64;
    } else {
        block_size = 128;
    }

#ifdef CONFIG_SHA_SUPPORT_MUL_THREAD
    uint32_t last = sha_priv->total & (block_size - 1);
#else
    uint32_t last = total[0] & (block_size - 1);
#endif
    uint32_t padn = block_size - last;

    finish_flag = 1;

    csi_sha_update(handle, NULL, output, padn);

    uint8_t result_len = 20;
    /* convert the data endian according the sha mode */
    if (sha_priv->mode == SHA_MODE_1) {
        result_len = 20;
    } else if (sha_priv->mode == SHA_MODE_224) {
        result_len = 28;
    } else if (sha_priv->mode == SHA_MODE_256) {
        result_len = 32;
    } else if (sha_priv->mode == SHA_MODE_512) {
        result_len = 64;
    } else if (sha_priv->mode == SHA_MODE_384) {
        result_len = 48;
    }
    sha_reverse_order(sha_result, result_len);
    memcpy((uint8_t*)output, sha_result, result_len);

    finish_flag = 0;
#ifdef CONFIG_SHA_SUPPORT_MUL_THREAD
    memset(sha_priv->sha_buffer, 0, sizeof(sha_priv->sha_buffer));
    sha_priv->first_cal = 1;
    sha_priv->total = 0;
#else
    memset(sha_buffer, 0, sizeof(sha_buffer));
    first_cal = 1;
    total[0] = 0;
#endif
    return 0;
}

/**
  \brief       Get SHA status.
  \param[in]   handle  sha handle to operate.
  \return      SHA status \ref sha_status_t
*/
sha_status_t csi_sha_get_status(sha_handle_t handle)
{
    ck_sha_priv_t *sha_priv = handle;
    return sha_priv->status;
}
