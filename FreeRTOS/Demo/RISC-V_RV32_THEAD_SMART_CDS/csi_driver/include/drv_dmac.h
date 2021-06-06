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
 * @file     drv_dmac.h
 * @brief    header file for dmac driver
 * @version  V1.0
 * @date     02. June 2017
 * @model    dmac
 ******************************************************************************/
#ifndef _CSI_DMA_H_
#define _CSI_DMA_H_

#include <stdint.h>
#include <drv_common.h>

#ifdef __cplusplus
extern "C" {
#endif
/**
\brief DMA Driver Capabilities.
*/
typedef struct {
    uint32_t unalign_addr : 1;          ///< support for unalign address transfer when memory is source
} dma_capabilities_t;

typedef enum {
    DMA_STATE_FREE = 0,       ///< DMA channel not yet initialized or disabled
    DMA_STATE_READY,          ///< DMA channel process success and ready for use, but not start yet
    DMA_STATE_BUSY,           ///< DMA channel process is ongoing
    DMA_STATE_DONE,           ///< DMA channel transfer done
    DMA_STATE_ERROR,          ///< DMA channel transfer error
} dma_status_e;

/****** DMA specific error codes *****/
typedef enum {
    EDRV_DMA_MODE  = (DRV_ERROR_SPECIFIC + 1),     ///< Specified Mode not supported
} dma_error_e;

/****** DMA Event *****/
typedef enum {
    DMA_EVENT_TRANSFER_DONE        = 0,  ///< transfer complete
    DMA_EVENT_TRANSFER_HALF_DONE   = 1,  ///< transfer half done
    DMA_EVENT_TRANSFER_MODE_DONE   = 2,  ///< transfer complete in a certain dma trigger mode.
    DMA_EVENT_CAHNNEL_PEND         = 3,  ///< it happens when there is a low priority channel was preempted by a high priority channel
    DMA_EVENT_TRANSFER_ERROR       = 4,  ///< transfer error
} dma_event_e;

typedef enum {
    DMA_ADDR_INC    = 0,
    DMA_ADDR_DEC,
    DMA_ADDR_CONSTANT
} dma_addr_inc_e;

typedef enum {
    DMA_MEM2MEM     = 0,
    DMA_MEM2PERH,
    DMA_PERH2MEM,
    DMA_PERH2PERH,
} dma_trans_type_e;

typedef enum {
    DMA_SINGLE_TRIGGER     = 0,
    DMA_GROUP_TRIGGER,
    DMA_BLOCK_TRIGGER
} dma_trig_trans_mode_e;

typedef enum {
    DMA_DIR_DEST = 0,
    DMA_DIR_SOURCE
} dma_single_dir_e;

typedef enum {
    DMA_ADDR_LITTLE = 0,
    DMA_ADDR_BIG
} dma_addr_endian_e;

typedef enum {
    DMA_MODE_HARDWARE = 0,
    DMA_MODE_SOFTWARE
} dma_channel_req_mode_e;

typedef struct {
    dma_addr_inc_e         src_inc;        ///< source address increment
    dma_addr_inc_e         dst_inc;        ///< destination address increment
    dma_addr_endian_e      src_endian;     ///< source read data little-big endian change control.
    dma_addr_endian_e      dst_endian;     ///< destination write data little-big endian change control.
    uint8_t                src_tw;         ///< source transfer width in byte
    uint8_t                dst_tw;         ///< destination transfer width in byte
    uint8_t                hs_if;          ///< a hardware handshaking interface (optional).
    uint8_t                preemption;     ///< determine whether if a channel can be preempted by a higher priority channel, 0 -- not allow preempt, 1 -- allow preempt.
    dma_trans_type_e       type;           ///< transfer type
    dma_trig_trans_mode_e  mode;           ///< channel trigger mode
    dma_channel_req_mode_e ch_mode;        ///< software or hardware to tigger dma channel work.
    dma_single_dir_e       single_dir;     ///< after select single mode control for source(read) or destination(write) transfer.
    uint32_t               group_len;      ///< group transaction length (unit: bytes) when use DMA_GROUP_TRIGGER mode.
    uint32_t               src_reload_en;  ///< 1:dma enable src addr auto reload, 0:disable
    uint32_t               dest_reload_en; ///< 1:dma enable dst addr auto reload, 0:disable
} dma_config_t;

typedef void (*dma_event_cb_t)(int32_t ch, dma_event_e event, void *arg);   ///< Pointer to \ref dma_event_cb_t : dmac event call back.

/**
  \brief     get one free dma channel
  \param[in] ch channel num. if -1 then allocate a free channal in this dma
                             else allocate a fix channal
  \return    dma channel num. if -1 alloc channle error
 */
int32_t csi_dma_alloc_channel_ex(int32_t ch);

/**
  \brief     get one free dma channel
  \return    dma channel num. if -1 alloc channle error
 */
int32_t csi_dma_alloc_channel(void);

/**
  \brief       control dma power.
  \param[in]   ch      dma channel num
  \param[in]   state   power state.\ref csi_power_stat_e.
  \return      error code
*/
int32_t csi_dma_power_control(int32_t ch, csi_power_stat_e state);

/**
  \brief       Get driver capabilities.
  \param[in]   ch      dma channel num
  \return      \ref dma_capabilities_t
*/
dma_capabilities_t csi_dma_get_capabilities(int32_t ch);

/**
  \brief        release dma channel and related resources
  \param[in]    ch dma channel num
  \return       error code
 */
void csi_dma_release_channel(int32_t ch);

/**
  \brief        config dma channel
  \param[in]    ch          dma channel num
  \param[in]    config      dma channel transfer configure
  \param[in]    cb_event    Pointer to \ref dma_event_cb_t
  \return       error code
 */
int32_t csi_dma_config_channel(int32_t ch, dma_config_t *config, dma_event_cb_t cb_event, void *cb_arg);

/**
  \brief       start generate dma channel signal.
  \param[in]   ch          dma channel num
  \param[in]   psrcaddr    dma transfer source address
  \param[in]   pdstaddr    dma transfer destination address
  \param[in]   length      dma transfer length (unit: bytes).
*/
void csi_dma_start(int32_t ch, void *psrcaddr, void *pdstaddr, uint32_t length);

/**
  \brief       Stop generate dma channel signal.
  \param[in]   ch     dma channel num
*/
void csi_dma_stop(int32_t ch);

/**
  \brief       start generate dma channel cyclic transfer.
  \param[in]   ch          dma channel num
  \param[in]   psrcaddr    dma transfer source address
  \param[in]   pdstaddr    dma transfer destination address
  \param[in]   cycle_len   The length of a cycle
  \param[in]   cycle_num   the number of a cycle
  \return       error code
*/
int32_t csi_dma_cyclic_prep(int32_t ch, void *psrcaddr, void *pdstaddr, uint32_t cycle_len, uint32_t cycle_num);
/**
  \brief       start generate dma channel cyclic transfer.
  \param[in]   ch   dma channel num
*/

void csi_dma_cyclic_start(int32_t ch);

/**
  \brief       Stop generate dma channel cyclic transfer.
  \param[in]   ch   dma channel num
*/
void csi_dma_cyclic_stop(int32_t ch);

/**
  \brief       Get DMA channel status.
  \param[in]   ch  dma channel num
  \return      DMA status \ref dma_status_e
*/
dma_status_e csi_dma_get_status(int32_t ch);

#ifdef __cplusplus
}
#endif

#endif /* _CSI_DMA_H_ */

