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


#include "peripherals/aic.h"
#ifdef CONFIG_HAVE_FLEXCOM
#include "peripherals/flexcom.h"
#endif
#include "peripherals/pmc.h"
#include "peripherals/spid.h"
#include "peripherals/spi.h"
#include "peripherals/xdmac.h"
#include "peripherals/xdmad.h"
#include "peripherals/l2cc.h"

#include "cortex-a/cp15.h"

#include "trace.h"

#include <stddef.h>
#include <stdint.h>
#include <assert.h>
#include <string.h>

#define SPID_ATTRIBUTE_MASK     (SPI_MR_PS | SPI_MR_MODFDIS | SPI_MR_MSTR | SPI_MR_WDRBT)
#define SPID_DMA_THRESHOLD      16

static uint32_t _garbage = 0;

static void _spid_xdmad_callback_wrapper(struct _xdmad_channel *channel,
					 void *arg)
{
	trace_debug("SPID DMA Transfert Finished\r\n");
	struct _spi_desc* spid = (struct _spi_desc*) arg;

	xdmad_free_channel(channel);

	if (spid->region_start && spid->region_end) {
		l2cc_invalidate_region(spid->region_start, spid->region_end);
	}

	if (spid && spid->callback)
		spid->callback(spid, spid->cb_args);
}

static void _spid_xdmad_cleanup_callback(struct _xdmad_channel *channel,
					 void *arg)
{
	xdmad_free_channel(channel);
}

#ifdef CONFIG_HAVE_SPI_FIFO
static void spid_fifo_error(void)
{
	trace_error("Fifo pointer error encountered !!\r\n");
}
#endif

void spid_configure(struct _spi_desc* desc)
{
	uint32_t id = get_spi_id_from_addr(desc->addr);

#ifdef CONFIG_HAVE_FLEXCOM
	Flexcom* flexcom = get_flexcom_addr_from_id(id);
	if (flexcom) {
		flexcom_select(flexcom, FLEX_MR_OPMODE_SPI);
	}
#endif
	/* Enable SPI early otherwise FIFO configuration won't be applied */
	pmc_enable_peripheral(id);
	if (desc->transfert_mode == SPID_MODE_FIFO) {
		desc->attributes &= ~SPI_MR_WDRBT;
	}
	spi_configure(desc->addr, (desc->attributes & SPID_ATTRIBUTE_MASK) | SPI_MR_MSTR);
	spi_chip_select(desc->addr, desc->chip_select);
	spi_configure_cs(desc->addr, desc->chip_select, desc->bitrate,
			 desc->dlybs, desc->dlybct, desc->spi_mode, 0);
#ifdef CONFIG_HAVE_SPI_FIFO
	if (desc->transfert_mode == SPID_MODE_FIFO) {
		spi_fifo_configure(desc->addr, SPI_FIFO_DEPTH, SPI_FIFO_DEPTH,
				   SPI_FMR_TXRDYM_ONE_DATA | SPI_FMR_RXRDYM_ONE_DATA);
		spi_enable_it(desc->addr, SPI_IER_TXFPTEF | SPI_IER_RXFPTEF);
		aic_set_source_vector(id, spid_fifo_error);
		aic_enable(id);
	}
#endif
	(void)spi_get_status(desc->addr);

	spi_enable(desc->addr);
}

void spid_begin_transfert(struct _spi_desc* desc)
{
	spi_chip_select(desc->addr, desc->chip_select);
	spi_configure_cs_mode(desc->addr, desc->chip_select, SPI_KEEP_CS_OW);
}

static void _spid_init_dma_write_channel(const struct _spi_desc* desc,
					 struct _xdmad_channel** channel,
					 struct _xdmad_cfg* cfg)
{
	assert(cfg);
	assert(channel);

	uint32_t id = get_spi_id_from_addr(desc->addr);

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

	cfg->dest_addr = (void*)&desc->addr->SPI_TDR;
}

static void _spid_init_dma_read_channel(const struct _spi_desc* desc,
					 struct _xdmad_channel** channel,
					 struct _xdmad_cfg* cfg)
{
	assert(cfg);
	assert(channel);

	uint32_t id = get_spi_id_from_addr(desc->addr);

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

	cfg->src_addr = (void*)&desc->addr->SPI_RDR;
}

static void _spid_dma_write(const struct _spi_desc* desc,
			   const struct _buffer* buffer)
{
	struct _xdmad_channel* w_channel = NULL;
	struct _xdmad_channel* r_channel = NULL;
	struct _xdmad_cfg w_cfg;
	struct _xdmad_cfg r_cfg;

	_spid_init_dma_write_channel(desc, &w_channel, &w_cfg);
	_spid_init_dma_read_channel(desc, &r_channel, &r_cfg);

	w_cfg.cfg.bitfield.sam = XDMAC_CC_SAM_INCREMENTED_AM
		>> XDMAC_CC_SAM_Pos;
	w_cfg.src_addr = buffer->data;
	w_cfg.ublock_size = buffer->size;
	xdmad_configure_transfer(w_channel, &w_cfg, 0, 0);
	xdmad_set_callback(w_channel, _spid_xdmad_cleanup_callback,
			   NULL);

	r_cfg.cfg.bitfield.dam = XDMAC_CC_DAM_FIXED_AM
		>> XDMAC_CC_DAM_Pos;
	r_cfg.dest_addr = &_garbage;
	r_cfg.ublock_size = buffer->size;
	xdmad_configure_transfer(r_channel, &r_cfg, 0, 0);
	xdmad_set_callback(r_channel, _spid_xdmad_callback_wrapper,
			   (void*)desc);

	l2cc_clean_region(desc->region_start, desc->region_end);

	xdmad_start_transfer(w_channel);
	xdmad_start_transfer(r_channel);
}

static void _spid_dma_read(const struct _spi_desc* desc,
			   struct _buffer* buffer)
{
	struct _xdmad_channel* w_channel = NULL;
	struct _xdmad_channel* r_channel = NULL;
	struct _xdmad_cfg w_cfg;
	struct _xdmad_cfg r_cfg;

	_spid_init_dma_write_channel(desc, &w_channel, &w_cfg);
	_spid_init_dma_read_channel(desc, &r_channel, &r_cfg);

	w_cfg.cfg.bitfield.sam = XDMAC_CC_SAM_FIXED_AM
		>> XDMAC_CC_SAM_Pos;
	w_cfg.src_addr = buffer->data;
	w_cfg.ublock_size = buffer->size;
	w_cfg.block_size = 0;
	xdmad_configure_transfer(w_channel, &w_cfg, 0, 0);
	xdmad_set_callback(w_channel, _spid_xdmad_cleanup_callback, NULL);

	r_cfg.cfg.bitfield.dam = XDMAC_CC_DAM_INCREMENTED_AM
		>> XDMAC_CC_DAM_Pos;
	r_cfg.dest_addr = buffer->data;
	r_cfg.ublock_size = buffer->size;
	xdmad_configure_transfer(r_channel, &r_cfg, 0, 0);
	xdmad_set_callback(r_channel, _spid_xdmad_callback_wrapper,
			   (void*)desc);

	l2cc_clean_region(desc->region_start, desc->region_end);

	xdmad_start_transfer(w_channel);
	xdmad_start_transfer(r_channel);
}

uint32_t spid_transfert(struct _spi_desc* desc, struct _buffer* rx,
			struct _buffer* tx, spid_callback_t cb,
			void* user_args)
{
	Spi* spi = desc->addr;
	uint32_t i = 0;

	desc->callback = cb;
	desc->cb_args = user_args;

	if (mutex_try_lock(&desc->mutex)) {
		return SPID_ERROR_LOCK;
	}

	switch (desc->transfert_mode) {
	case SPID_MODE_POLLING:
		if (tx) {
			for (i = 0; i < tx->size; ++i) {
				spi_write(spi, desc->chip_select, tx->data[i]);
			}
		}
		if (rx) {
			for (i = 0; i < rx->size; ++i) {
				rx->data[i] = spi_read(spi, desc->chip_select);
			}
		}
		mutex_free(&desc->mutex);
		if (cb)
			cb(desc, user_args);
		break;
	case SPID_MODE_DMA:
		if (tx) {
			if (tx->size < SPID_DMA_THRESHOLD) {
				for (i = 0; i < tx->size; ++i) {
					spi_write(spi, desc->chip_select, tx->data[i]);
				}
				if (!rx) {
					if (cb)
						cb(desc, user_args);
					mutex_free(&desc->mutex);
				}
			} else {
				desc->region_start = (uint32_t)tx->data;
				desc->region_end = desc->region_start
					+ tx->size;
				_spid_dma_write(desc, tx);
				if (rx) {
					spid_wait_transfert(desc);
					mutex_lock(&desc->mutex);
				}
			}
		}
		if (rx) {
			if (rx->size < SPID_DMA_THRESHOLD) {
				for (i = 0; i < rx->size; ++i) {
					rx->data[i] = spi_read(spi, desc->chip_select);
				}
				if (cb)
					cb(desc, user_args);
				mutex_free(&desc->mutex);
			} else {
				desc->region_start = (uint32_t)rx->data;
				desc->region_end = desc->region_start
					+ rx->size;
				_spid_dma_read(desc, rx);
			}
		}
		break;
#ifdef CONFIG_HAVE_SPI_FIFO
	case SPID_MODE_FIFO:
		if (tx) {
			spi_write_stream(spi, desc->chip_select,
					 tx->data, tx->size);
		}
		if (rx) {
			spi_read_stream(spi, desc->chip_select,
					rx->data, rx->size);
		}
		mutex_free(&desc->mutex);
		if (cb)
			cb(desc, user_args);
		break;
#endif
	default:
		trace_debug("Unkown mode");
	}

	return SPID_SUCCESS;
}

void spid_finish_transfert_callback(struct _spi_desc* desc, void* user_args)
{
	(void)user_args;
	spid_finish_transfert(desc);
}

void spid_finish_transfert(struct _spi_desc* desc)
{
	spi_release_cs(desc->addr);
	mutex_free(&desc->mutex);
}

void spid_close(const struct _spi_desc* desc)
{
	uint32_t id = get_spi_id_from_addr(desc->addr);
#ifdef CONFIG_HAVE_SPI_FIFO
	spi_fifo_disable(desc->addr);
	spi_disable_it(desc->addr, SPI_IER_TXFPTEF | SPI_IER_RXFPTEF);
	aic_disable(id);
#endif
	spi_disable(desc->addr);
	pmc_disable_peripheral(id);
}

uint32_t spid_is_busy(const struct _spi_desc* desc)
{
	return mutex_is_locked(&desc->mutex);
}

void spid_wait_transfert(const struct _spi_desc* desc)
{
	while (mutex_is_locked(&desc->mutex));
}
