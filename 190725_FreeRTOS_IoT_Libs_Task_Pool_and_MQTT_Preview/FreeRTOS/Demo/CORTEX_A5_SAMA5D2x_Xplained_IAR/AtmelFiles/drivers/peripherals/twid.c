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


#ifdef CONFIG_HAVE_FLEXCOM
#include "peripherals/flexcom.h"
#endif
#include "peripherals/pmc.h"
#include "peripherals/twid.h"
#include "peripherals/twi.h"
#include "peripherals/xdmad.h"
#include "peripherals/l2cc.h"

#include "cortex-a/cp15.h"

#include "trace.h"
#include "io.h"
#include "timer.h"

#include <assert.h>
#include <string.h>

#define TWID_DMA_THRESHOLD      16
#define TWID_TIMEOUT            100

static uint32_t _twid_wait_twi_transfer(struct _twi_desc* desc)
{
	struct _timeout timeout;
	timer_start_timeout(&timeout, TWID_TIMEOUT);
	while(!twi_is_transfer_complete(desc->addr)){
		if (timer_timeout_reached(&timeout)) {
			trace_error("twid: Unable to complete transfert!\r\n");
			twid_configure(desc);
			return TWID_ERROR_TRANSFER;
		}
	}
	return TWID_SUCCESS;
}

static void _twid_xdmad_callback_wrapper(struct _xdmad_channel* channel,
					   void* args)
{
	trace_debug("TWID DMA Transfert Finished\r\n");
	struct _twi_desc* twid = (struct _twi_desc*) args;

	xdmad_free_channel(channel);

	if (twid->region_start && twid->region_end) {
		l2cc_invalidate_region(twid->region_start, twid->region_end);
	}

	if (twid && twid->callback)
		twid->callback(twid, twid->cb_args);

}

static void _twid_init_dma_read_channel(const struct _twi_desc* desc,
					  struct _xdmad_channel** channel,
					  struct _xdmad_cfg* cfg)
{
	assert(cfg);
	assert(channel);

	uint32_t id = get_twi_id_from_addr(desc->addr);
	assert(id < ID_PERIPH_COUNT);

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

	cfg->src_addr = (void*)&desc->addr->TWI_RHR;
}

static void _twid_dma_read(const struct _twi_desc* desc,
			   struct _buffer* buffer)
{
	struct _xdmad_channel* channel = NULL;
	struct _xdmad_cfg cfg;

	_twid_init_dma_read_channel(desc, &channel, &cfg);

	cfg.cfg.bitfield.dam = XDMAC_CC_DAM_INCREMENTED_AM
		>> XDMAC_CC_DAM_Pos;
	cfg.dest_addr = buffer->data;
	cfg.ublock_size = buffer->size;
	cfg.block_size = 0;
	xdmad_configure_transfer(channel, &cfg, 0, 0);
	xdmad_set_callback(channel, _twid_xdmad_callback_wrapper,
			   (void*)desc);

	l2cc_clean_region(desc->region_start, desc->region_end);

	xdmad_start_transfer(channel);
}

static void _twid_init_dma_write_channel(struct _twi_desc* desc,
					 struct _xdmad_channel** channel,
					 struct _xdmad_cfg* cfg)
{
	assert(cfg);
	assert(channel);

	uint32_t id = get_twi_id_from_addr(desc->addr);
	assert(id < ID_PERIPH_COUNT);
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

	cfg->dest_addr = (void*)&desc->addr->TWI_THR;
}

static void _twid_dma_write(struct _twi_desc* desc,
			    struct _buffer* buffer)
{
	struct _xdmad_channel* channel = NULL;
	struct _xdmad_cfg cfg;

	_twid_init_dma_write_channel(desc, &channel, &cfg);

	cfg.cfg.bitfield.sam = XDMAC_CC_SAM_INCREMENTED_AM
		>> XDMAC_CC_SAM_Pos;
	cfg.src_addr = buffer->data;
	cfg.ublock_size = buffer->size;
	cfg.block_size = 0;
	xdmad_configure_transfer(channel, &cfg, 0, 0);
	xdmad_set_callback(channel, _twid_xdmad_callback_wrapper,
			   (void*)desc);

	l2cc_clean_region(desc->region_start, desc->region_end);

	xdmad_start_transfer(channel);
}

void twid_configure(struct _twi_desc* desc)
{
	uint32_t id = get_twi_id_from_addr(desc->addr);
	assert(id < ID_PERIPH_COUNT);

#ifdef CONFIG_HAVE_FLEXCOM
	Flexcom* flexcom = get_flexcom_addr_from_id(get_twi_id_from_addr(desc->addr));
	if (flexcom) {
		flexcom_select(flexcom, FLEX_MR_OPMODE_TWI);
	}
#endif

	pmc_enable_peripheral(id);
	twi_configure_master(desc->addr, desc->freq);

#ifdef CONFIG_HAVE_TWI_FIFO
	if (desc->transfert_mode == TWID_MODE_FIFO) {
		uint32_t fifo_depth = get_peripheral_fifo_depth(desc->addr);
		twi_fifo_configure(desc->addr, fifo_depth/2, fifo_depth/2,
				   TWI_FMR_RXRDYM_ONE_DATA | TWI_FMR_TXRDYM_ONE_DATA);
	}
#endif
}

static uint32_t _twid_poll_write(struct _twi_desc* desc, struct _buffer* buffer)
{
	int i = 0;
	struct _timeout timeout;
	twi_init_write_transfert(desc->addr,
				 desc->slave_addr,
				 desc->iaddr,
				 desc->isize,
				 buffer->size);
	if (twi_get_status(desc->addr) & TWI_SR_NACK) {
		trace_error("twid: command NACK!\r\n");
		return TWID_ERROR_ACK;
	}
	for (i = 0; i < buffer->size; ++i) {
		timer_start_timeout(&timeout, TWID_TIMEOUT);
		while(!twi_byte_sent(desc->addr)) {
			if (timer_timeout_reached(&timeout)) {
				trace_error("twid: Device doesn't answer, "
					    "(TX TIMEOUT)\r\n");
				break;
			}
		}
		twi_write_byte(desc->addr, buffer->data[i]);
		if(twi_get_status(desc->addr) & TWI_SR_NACK) {
			trace_error("twid: command NACK!\r\n");
			return TWID_ERROR_ACK;
		}
	}
	/* wait transfert to be finished */
	return _twid_wait_twi_transfer(desc);
}

static uint32_t _twid_poll_read(struct _twi_desc* desc, struct _buffer* buffer)
{
	int i = 0;
	struct _timeout timeout;
	twi_init_read_transfert(desc->addr,
				desc->slave_addr,
				desc->iaddr,
				desc->isize,
				buffer->size);
	if (twi_get_status(desc->addr) & TWI_SR_NACK) {
		trace_error("twid: command NACK!\r\n");
		return TWID_ERROR_ACK;
	}
	for (i = 0; i < buffer->size; ++i) {
		timer_start_timeout(&timeout, TWID_TIMEOUT);
		while(!twi_is_byte_received(desc->addr)) {
			if (timer_timeout_reached(&timeout)) {
				trace_error("twid: Device doesn't answer, "
					    "(RX TIMEOUT)\r\n");
				break;
			}
		}
		buffer->data[i] = twi_read_byte(desc->addr);
		if(twi_get_status(desc->addr) & TWI_SR_NACK) {
			trace_error("twid: command NACK\r\n");
		return TWID_ERROR_ACK;
		}
	}
	/* wait transfert to be finished */
	return _twid_wait_twi_transfer(desc);
}

uint32_t twid_transfert(struct _twi_desc* desc, struct _buffer* rx,
			struct _buffer* tx, twid_callback_t cb,
			void* user_args)
{
	uint32_t status = TWID_SUCCESS;

	desc->callback = cb;
	desc->cb_args = user_args;

	if (mutex_try_lock(&desc->mutex)) {
		return TWID_ERROR_LOCK;
	}

	switch (desc->transfert_mode) {
	case TWID_MODE_POLLING:
		if (tx) {
			status = _twid_poll_write(desc, tx);
			if (status) break;
		}
		if (rx) {
			status = _twid_poll_read(desc, rx);
			if (status) break;
		}
		if (cb)
			cb(desc, user_args);
		mutex_free(&desc->mutex);
		break;

	case TWID_MODE_DMA:
		if (!(rx || tx)) {
			status = TWID_ERROR_DUPLEX;
			break;
		}
		if (tx) {
			if (tx->size < TWID_DMA_THRESHOLD) {
				status = _twid_poll_write(desc, tx);
				if (status) break;
				if (cb)
					cb(desc, user_args);
				mutex_free(&desc->mutex);
			} else {
				twi_init_write_transfert(desc->addr,
							 desc->slave_addr,
							 desc->iaddr,
							 desc->isize,
							 tx->size);
				desc->region_start = (uint32_t)tx->data;
				desc->region_end = desc->region_start
					+ tx->size;
				_twid_dma_write(desc, tx);
			}
		}
		if (rx) {
			if (rx->size < TWID_DMA_THRESHOLD) {
				status = _twid_poll_read(desc, rx);
				if (status) break;
				if (cb)
					cb(desc, user_args);
				mutex_free(&desc->mutex);
			} else {
				twi_init_read_transfert(desc->addr,
							desc->slave_addr,
							desc->iaddr,
							desc->isize,
							rx->size);
				desc->region_start = (uint32_t)rx->data;
				desc->region_end = desc->region_start
					+ rx->size;
				if(twi_get_status(desc->addr) & TWI_SR_NACK) {
					trace_error("twid: Acknolegment "
						    "Error\r\n");
					status = TWID_ERROR_ACK;
					break;
				}
				_twid_dma_read(desc, rx);
			}
		}
		break;

#ifdef CONFIG_HAVE_TWI_FIFO
	case TWID_MODE_FIFO:
		if (tx) {
			status = twi_write_stream(desc->addr, desc->slave_addr,
						  desc->iaddr, desc->isize,
						  tx->data, tx->size);
			status = status ? TWID_SUCCESS : TWID_ERROR_ACK;
			if (status)
				break;
			status = _twid_wait_twi_transfer(desc);
			if (status)
				break;
		}
		if (rx) {
			status = twi_read_stream(desc->addr, desc->slave_addr,
						 desc->iaddr, desc->isize,
						 rx->data, rx->size);
			status = status ? TWID_SUCCESS : TWID_ERROR_ACK;
			if (status)
				break;
			status = _twid_wait_twi_transfer(desc);
			if (status)
				break;
		}
		if (cb)
			cb(desc, user_args);
		mutex_free(&desc->mutex);
		break;
#endif
	default:
		trace_debug("Unkown mode");
	}

	if (status)
		mutex_free(&desc->mutex);

	return status;
}

void twid_finish_transfert_callback(struct _twi_desc* desc, void* user_args)
{
	(void)user_args;
	twid_finish_transfert(desc);
}

void twid_finish_transfert(struct _twi_desc* desc)
{
	mutex_free(&desc->mutex);
}

uint32_t twid_is_busy(const struct _twi_desc* desc)
{
	return mutex_is_locked(&desc->mutex);
}

void twid_wait_transfert(const struct _twi_desc* desc)
{
	while (mutex_is_locked(&desc->mutex));
}
