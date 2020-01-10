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
 * @file     osr_trng.c
 * @brief    CSI Source File for TRNG Driver
 * @version  V1.0
 * @date     02. June 2017
 ******************************************************************************/

#include <stdbool.h>
#include <stdio.h>
#include <string.h>
#include "drv_trng.h"
#include "osr_trng.h"


#define ERR_TRNG(errno) (CSI_DRV_ERRNO_TRNG_BASE | errno)
#define TRNG_NULL_PARAM_CHK(para)                         \
        do {                                        \
            if (para == NULL) {                     \
                return ERR_TRNG(EDRV_PARAMETER);   \
            }                                       \
        } while (0)

typedef struct {
    uint32_t base;
    uint32_t irq;
    trng_event_cb_t cb;
    trng_status_t status;
} osr_trng_priv_t;

extern int32_t target_get_trng(int32_t idx, uint32_t *base, uint32_t *irq);

static osr_trng_priv_t trng_handle[CONFIG_TRNG_NUM];

/* Driver Capabilities */
static const trng_capabilities_t driver_capabilities = {
    .lowper_mode = 0 /* low power mode */
};

//
// Functions
//

osr_trng_reg_t *trng_reg = NULL;

static int32_t trng_disable_irq(void)
{
    trng_reg->RBG_CR &= ~TRNG_IRQ_BIT;
    return 0;
}

static int32_t trng_enable(void)
{
    trng_reg->RBG_CR |= TRNG_EN;
    return 0;
}

static int32_t trng_get_data(void)
{
    int data = trng_reg->RBG_DR;
    return data;
}

static int32_t trng_data_is_ready(void)
{
    int flag = (trng_reg->RBG_FIFO_SR & TRNG_DATA_READY);
    return flag;
}

/**
  \brief       Initialize TRNG Interface. 1. Initializes the resources needed for the TRNG interface 2.registers event callback function
  \param[in]   idx device id
  \param[in]   cb_event  Pointer to \ref trng_event_cb_t
  \return      pointer to trng handle
*/
trng_handle_t csi_trng_initialize(int32_t idx, trng_event_cb_t cb_event)
{

    if (idx < 0 || idx >= CONFIG_TRNG_NUM) {
        return NULL;
    }

    /* obtain the trng information */
    uint32_t base = 0u;
    uint32_t irq = 0u;
    int32_t real_idx = target_get_trng(idx, &base, &irq);

    if (real_idx != idx) {
        return NULL;
    }

    osr_trng_priv_t *trng_priv = &trng_handle[idx];
    trng_priv->base = base;
    trng_priv->irq = irq;

    /* initialize the trng context */
    trng_reg = (osr_trng_reg_t *)(trng_priv->base);
    trng_priv->cb = cb_event;
    trng_priv->status.busy = 0;
    trng_priv->status.data_valid = 0;

    trng_disable_irq();

    return (trng_handle_t)trng_priv;
}

/**
  \brief       De-initialize TRNG Interface. stops operation and releases the software resources used by the interface
  \param[in]   handle  trng handle to operate.
  \return      error code
*/
int32_t csi_trng_uninitialize(trng_handle_t handle)
{
    TRNG_NULL_PARAM_CHK(handle);

    osr_trng_priv_t *trng_priv = handle;
    trng_priv->cb = NULL;

    return 0;
}

/**
  \brief       Get driver capabilities.
  \param[in]   idx device id.
  \return      \ref trng_capabilities_t
*/
//trng_capabilities_t csi_trng_get_capabilities(int32_t idx)
trng_capabilities_t csi_trng_get_capabilities(trng_handle_t handle)
{
    /*
    if (idx < 0 || idx >= CONFIG_TRNG_NUM) {
        trng_capabilities_t ret;
        memset(&ret, 0, sizeof(trng_capabilities_t));
        return ret;
    }*/
    return driver_capabilities;
}

/**
  \brief       Get data from the TRNG.
  \param[in]   handle  trng handle to operate.
  \param[out]  data  Pointer to buffer with data get from TRNG
  \param[in]   num   Number of data items to obtain
  \return      error code
*/
int32_t csi_trng_get_data(trng_handle_t handle, void *data, uint32_t num)
{
    TRNG_NULL_PARAM_CHK(handle);
    TRNG_NULL_PARAM_CHK(data);
    TRNG_NULL_PARAM_CHK(num);

    osr_trng_priv_t *trng_priv = handle;

    trng_priv->status.busy = 1U;
    trng_priv->status.data_valid = 0U;

    uint8_t left_len = (uint32_t)data & 0x3;
    uint32_t result = 0;

    trng_enable();
    /* if the data addr is not aligned by word */
    if (left_len) {
        while (!trng_data_is_ready());
        result = trng_get_data();

        if (num > (4 - left_len)) {
            memcpy(data, &result, 4 - left_len);
        } else {
            memcpy(data, &result, num);
            trng_priv->status.busy = 0U;
            trng_priv->status.data_valid = 1U;

            if (trng_priv->cb) {
                //trng_priv->cb(0, TRNG_EVENT_DATA_GENERATE_COMPLETE);
                trng_priv->cb(TRNG_EVENT_DATA_GENERATE_COMPLETE);
            }
            return 0;
        }
        num -= (4 - left_len);
        data += (4 - left_len);
    }

    uint32_t word_len = num >> 2;
    left_len = num & 0x3;

    /* obtain the data by word */
    while (word_len--) {
        while (!trng_data_is_ready());
        result = trng_get_data();
        *(uint32_t *)data = result;
        data = (void *)((uint32_t)data + 4);
    }

    /* if the num is not aligned by word */
    if (left_len) {
        while (!trng_data_is_ready());
        result = trng_get_data();
        memcpy(data, &result, left_len);
    }

    trng_priv->status.busy = 0U;
    trng_priv->status.data_valid = 1U;

    if (trng_priv->cb) {
        //trng_priv->cb(0, TRNG_EVENT_DATA_GENERATE_COMPLETE);
        trng_priv->cb(TRNG_EVENT_DATA_GENERATE_COMPLETE);
    }

    return 0;
}

/**
  \brief       Get TRNG status.
  \param[in]   handle  trng handle to operate.
  \return      TRNG status \ref trng_status_t
*/
trng_status_t csi_trng_get_status(trng_handle_t handle)
{
    if (handle == NULL) {
        trng_status_t ret;
        memset(&ret, 0, sizeof(trng_status_t));
        return ret;
    }
    osr_trng_priv_t *trng_priv = handle;
    return trng_priv->status;
}
