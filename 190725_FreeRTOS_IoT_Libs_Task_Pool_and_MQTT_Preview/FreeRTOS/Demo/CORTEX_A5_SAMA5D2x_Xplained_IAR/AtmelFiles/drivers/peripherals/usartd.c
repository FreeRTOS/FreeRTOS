/* ----------------------------------------------------------------------------
 *         SAM Software Package License
 * ----------------------------------------------------------------------------
 * Copyright (c) 2015, Atmel Corporation
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * - Redistributions of source code must retain the above copyright notice,
 * this list of conditions and the disclaimer below.
 *
 * Atmel's name may not be used to endorse or promote products derived from
 * this software without specific prior written permission.
 *
 * DISCLAIMER: THIS SOFTWARE IS PROVIDED BY ATMEL "AS IS" AND ANY EXPRESS OR
 * IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NON-INFRINGEMENT ARE
 * DISCLAIMED. IN NO EVENT SHALL ATMEL BE LIABLE FOR ANY DIRECT, INDIRECT,
 * INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA,
 * OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE,
 * EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 * ----------------------------------------------------------------------------
 */

#include "chip.h"

#ifdef CONFIG_HAVE_FLEXCOM
#include "peripherals/flexcom.h"
#endif
#include "peripherals/pmc.h"
#include "peripherals/usartd.h"
#include "peripherals/usart.h"
#include "peripherals/xdmac.h"
#include "peripherals/xdmad.h"
#include "peripherals/l2cc.h"

#include "cortex-a/cp15.h"

#include "trace.h"
#include "mutex.h"

#include <assert.h>
#include <string.h>
#include <stdint.h>

#define USARTD_ATTRIBUTE_MASK     (0)
#define USARTD_DMA_THRESHOLD      16

static void _usartd_xdmad_callback_wrapper(struct _xdmad_channel* channel,
					   void* args)
{
	trace_debug("USARTD DMA Transfert Finished\r\n");
	struct _usart_desc* usartd = (struct _usart_desc*) args;

	xdmad_free_channel(channel);

	if (usartd->region_start && usartd->region_end) {
		l2cc_invalidate_region(usartd->region_start,
				       usartd->region_end);
	}

	if (usartd && usartd->callback)
		usartd->callback(usartd, usartd->cb_args);
}

static void _usartd_init_dma_read_channel(const struct _usart_desc* desc,
					  struct _xdmad_channel** channel,
					  struct _xdmad_cfg* cfg)
{
	assert(cfg);
	assert(channel);

	uint32_t id = get_usart_id_from_addr(desc->addr);

	memset(cfg, 0x0, sizeof(*cfg));

	*channel =
		xdmad_allocate_channel(id, XDMAD_PERIPH_MEMORY);
	assert(*channel);

	xdmad_prepare_channel(*channel);
	cfg->cfg.uint32_value = XDMAC_CC_TYPE_PER_TRAN
		| XDMAC_CC_DSYNC_PER2MEM
		| XDMAC_CC_MEMSET_NORMAL_MODE
		| XDMAC_CC_CSIZE_CHK_1
		| XDMAC_CC_DWIDTH_BYTE
		| XDMAC_CC_DIF_AHB_IF0
		| XDMAC_CC_SIF_AHB_IF1
		| XDMAC_CC_SAM_FIXED_AM;

	cfg->src_addr = (void*)&desc->addr->US_RHR;
}

static void _usartd_dma_read(const struct _usart_desc* desc,
			   struct _buffer* buffer)
{
	struct _xdmad_channel* channel = NULL;
	struct _xdmad_cfg cfg;

	_usartd_init_dma_read_channel(desc, &channel, &cfg);

	cfg.cfg.bitfield.dam = XDMAC_CC_DAM_INCREMENTED_AM
		>> XDMAC_CC_DAM_Pos;
	cfg.dest_addr = buffer->data;
	cfg.ublock_size = buffer->size;
	cfg.block_size = 0;
	xdmad_configure_transfer(channel, &cfg, 0, 0);
	xdmad_set_callback(channel, _usartd_xdmad_callback_wrapper,
			   (void*)desc);

	l2cc_clean_region(desc->region_start, desc->region_end);

	xdmad_start_transfer(channel);
}

static void _usartd_init_dma_write_channel(const struct _usart_desc* desc,
					  struct _xdmad_channel** channel,
					  struct _xdmad_cfg* cfg)
{
	assert(cfg);
	assert(channel);

	uint32_t id = get_usart_id_from_addr(desc->addr);

	memset(cfg, 0x0, sizeof(*cfg));

	*channel =
		xdmad_allocate_channel(XDMAD_PERIPH_MEMORY, id);
	assert(*channel);

	xdmad_prepare_channel(*channel);
	cfg->cfg.uint32_value = XDMAC_CC_TYPE_PER_TRAN
		| XDMAC_CC_DSYNC_MEM2PER
		| XDMAC_CC_MEMSET_NORMAL_MODE
		| XDMAC_CC_CSIZE_CHK_1
		| XDMAC_CC_DWIDTH_BYTE
		| XDMAC_CC_DIF_AHB_IF1
		| XDMAC_CC_SIF_AHB_IF0
		| XDMAC_CC_DAM_FIXED_AM;

	cfg->dest_addr = (void*)&desc->addr->US_THR;
}

static void _usartd_dma_write(const struct _usart_desc* desc,
			   struct _buffer* buffer)
{
	struct _xdmad_channel* channel = NULL;
	struct _xdmad_cfg cfg;

	_usartd_init_dma_write_channel(desc, &channel, &cfg);

	cfg.cfg.bitfield.sam = XDMAC_CC_SAM_INCREMENTED_AM
		>> XDMAC_CC_SAM_Pos;
	cfg.src_addr = buffer->data;
	cfg.ublock_size = buffer->size;
	cfg.block_size = 0;
	xdmad_configure_transfer(channel, &cfg, 0, 0);
	xdmad_set_callback(channel, _usartd_xdmad_callback_wrapper,
			   (void*)desc);

	l2cc_clean_region(desc->region_start, desc->region_end);

	xdmad_start_transfer(channel);
}

void usartd_configure(struct _usart_desc* desc)
{
	uint32_t id = get_usart_id_from_addr(desc->addr);
	assert(id < ID_PERIPH_COUNT);

#ifdef CONFIG_HAVE_FLEXCOM
	Flexcom* flexcom = get_flexcom_addr_from_id(id);
	if (flexcom) {
		flexcom_select(flexcom, FLEX_MR_OPMODE_USART);
	}
#endif
	pmc_enable_peripheral(id);
	usart_configure(desc->addr, desc->mode, desc->baudrate);

#ifdef CONFIG_HAVE_USART_FIFO
	if (desc->transfert_mode == USARTD_MODE_FIFO) {
		uint32_t fifo_size = get_peripheral_fifo_depth(desc->addr);
		uint32_t tx_thres = fifo_size >> 1;
		uint32_t rx_thres1 = (fifo_size >> 1) + (fifo_size >> 2);
		uint32_t rx_thres2 = (fifo_size >> 1) - (fifo_size >> 2);
		usart_fifo_configure(desc->addr, tx_thres, rx_thres1, rx_thres2,
				     US_FMR_RXRDYM_ONE_DATA | US_FMR_TXRDYM_FOUR_DATA);
	}
#endif
}

uint32_t usartd_transfert(struct _usart_desc* desc, struct _buffer* rx,
			  struct _buffer* tx, usartd_callback_t cb,
			  void* user_args)
{
	uint32_t i = 0;

	desc->callback = cb;
	desc->cb_args = user_args;

	if (mutex_try_lock(&desc->mutex)) {
		return USARTD_ERROR_LOCK;
	}

	switch (desc->transfert_mode) {
	case USARTD_MODE_POLLING:
		if (tx) {
			for (i = 0; i < tx->size; ++i) {
				usart_put_char(desc->addr, tx->data[i]);
			}
		}
		if (rx) {
			for (i = 0; i < rx->size; ++i) {
				rx->data[i] = usart_get_char(desc->addr);
			}
		}
		mutex_free(&desc->mutex);
		if (cb)
			cb(desc, user_args);
		break;
	case USARTD_MODE_DMA:
		if (!(rx || tx)) {
			return USARTD_ERROR_DUPLEX;
		}

		if (tx) {
			if (tx->size < USARTD_DMA_THRESHOLD) {
				for (i = 0; i < tx->size; ++i) {
					usart_put_char(desc->addr, tx->data[i]);
				}
				if (cb)
					cb(desc, user_args);
				mutex_free(&desc->mutex);
			} else {
				desc->region_start = (uint32_t)tx->data;
				desc->region_end = desc->region_start
					+ tx->size;
				_usartd_dma_write(desc, tx);
			}
		} else if (rx) {
			if (rx->size < USARTD_DMA_THRESHOLD) {
				for (i = 0; i < rx->size; ++i) {
					rx->data[i] = usart_get_char(desc->addr);
				}
				if (cb)
					cb(desc, user_args);
				mutex_free(&desc->mutex);
			} else {
				desc->region_start = (uint32_t)rx->data;
				desc->region_end = desc->region_start
					+ rx->size;
				_usartd_dma_read(desc, rx);
			}
		} else {
			mutex_free(&desc->mutex);
		}
		break;
#ifdef CONFIG_HAVE_USART_FIFO
	case USARTD_MODE_FIFO:
		if (tx) {
			usart_write_stream(desc->addr, tx->data, tx->size);
		}
		if (rx) {
			usart_read_stream(desc->addr, rx->data, rx->size);
		}
		mutex_free(&desc->mutex);
		if (cb)
			cb(desc, user_args);
		break;
#endif
	default:
		trace_debug("Unkown mode");
	}

	return USARTD_SUCCESS;
}

void usartd_finish_transfert_callback(struct _usart_desc* desc,
				      void* user_args)
{
	(void)user_args;
	usartd_finish_transfert(desc);
}

void usartd_finish_transfert(struct _usart_desc* desc)
{
	mutex_free(&desc->mutex);
}

uint32_t usartd_is_busy(const struct _usart_desc* desc)
{
	return mutex_is_locked(&desc->mutex);
}

void usartd_wait_transfert(const struct _usart_desc* desc)
{
	while (mutex_is_locked(&desc->mutex));
}
