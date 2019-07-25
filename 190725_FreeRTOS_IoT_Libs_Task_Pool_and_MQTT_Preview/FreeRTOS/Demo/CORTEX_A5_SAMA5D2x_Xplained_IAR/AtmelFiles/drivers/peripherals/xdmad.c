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

/** \addtogroup xdmad_module
 *
 * \section Xdma xDma Configuration Usage
 *
 * To configure a XDMA channel, the user has to follow these few steps :
 * <ul>
 * <li> Initialize a XDMA driver instance by XDMAD_Initialize().</li>
 * <li> choose an available (disabled) channel using XDMAD_AllocateChannel().</li>
 * <li> After the XDMAC selected channel has been programmed, XDMAD_PrepareChannel() is to enable
 * clock and dma peripheral of the DMA, and set Configuration register to set up the transfer type
 * (memory or non-memory peripheral for source and destination) and flow control device.</li>
 * <li> Invoke XDMAD_StartTransfer() to start DMA transfer  or XDMAD_StopTransfer() to force stop DMA transfer.</li>
  * <li> Once the buffer of data is transferred, XDMAD_IsTransferDone() checks if DMA transfer is finished.</li>
 * <li> XDMAD_Handler() handles XDMA interrupt, and invoking XDMAD_SetCallback() if provided.</li>
 * </ul>
 *
 * Related files:\n
 * \ref xdmad.h\n
 * \ref xdmad.c\n
 */

/** \file */

/** \addtogroup dmad_functions
  @{*/

/*----------------------------------------------------------------------------
 *        Includes
 *----------------------------------------------------------------------------*/

#include "peripherals/aic.h"
#include "peripherals/pmc.h"
#include "peripherals/xdmad.h"

#include <assert.h>
#include "compiler.h"

/*----------------------------------------------------------------------------
 *        Local definitions
 *----------------------------------------------------------------------------*/

#define XDMAD_CHANNELS (XDMAC_CONTROLLERS * XDMAC_CHANNELS)

/** DMA state for channel */
enum {
	XDMAD_STATE_FREE = 0,  /**< Free channel */
	XDMAD_STATE_ALLOCATED, /**< Allocated to some peripheral */
	XDMAD_STATE_STARTED,   /**< DMA started */
	XDMAD_STATE_DONE,      /**< DMA transfer done */
};

/** DMA driver channel */
struct _xdmad_channel
{
	Xdmac           *xdmac;     /**< XDMAC instance */
	uint32_t         id;        /**< Channel ID */
	xdmad_callback_t callback;  /**< Callback */
	void            *user_arg;  /**< Callback argument */
	uint8_t          src_txif;  /**< Source TX Interface ID */
	uint8_t          src_rxif;  /**< Source RX Interface ID */
	uint8_t          dest_txif; /**< Destination TX Interface ID */
	uint8_t          dest_rxif; /**< Destination RX Interface ID */
	volatile uint8_t state;     /**< Channel State */
};

/** DMA driver instance */
struct _xdmad {
	struct _xdmad_channel channels[XDMAD_CHANNELS];
	bool                  polling;
	uint8_t               polling_timeout;
};

static struct _xdmad _xdmad;

/*----------------------------------------------------------------------------
 *        Local functions
 *----------------------------------------------------------------------------*/

static inline struct _xdmad_channel *_xdmad_channel(uint32_t controller, uint32_t channel)
{
	return &_xdmad.channels[controller * XDMAC_CHANNELS + channel];
}

/**
 * \brief xDMA interrupt handler
 * \param pXdmad Pointer to DMA driver instance.
 */
static void xdmad_handler(void)
{
	uint32_t cont;

	for (cont= 0; cont< XDMAC_CONTROLLERS; cont++) {
		uint32_t chan, gis, gcs;

		Xdmac *xdmac = xdmac_get_instance(cont);

		gis = xdmac_get_global_isr(xdmac);
		if ((gis & 0xFFFF) == 0)
			continue;

		gcs = xdmac_get_global_channel_status(xdmac);
		for (chan = 0; chan < XDMAC_CHANNELS; chan++) {
			struct _xdmad_channel *channel;
			bool exec = false;

			if (!(gis & (1 << chan)))
				continue;

			channel = _xdmad_channel(cont, chan);
			if (channel->state == XDMAD_STATE_FREE)
				continue;

			if (!(gcs & (1 << chan))) {
				uint32_t cis = xdmac_get_channel_isr(xdmac, chan);

				if (cis & XDMAC_CIS_BIS) {
					if (!(xdmac_get_channel_it_mask(xdmac, chan) & XDMAC_CIM_LIM)) {
						channel->state = XDMAD_STATE_DONE;
						exec = 1;
					}
				}

				if (cis & XDMAC_CIS_LIS) {
					channel->state = XDMAD_STATE_DONE;
					exec = 1;
				}

				if (cis & XDMAC_CIS_DIS) {
					channel->state = XDMAD_STATE_DONE;
					exec = 1;
				}
			}

			/* Execute callback */
			if (exec && channel->callback) {
				channel->callback(channel, channel->user_arg);
			}
		}
	}
}


/*----------------------------------------------------------------------------
 *        Exported functions
 *----------------------------------------------------------------------------*/

void xdmad_initialize(bool polling)
{
	uint32_t cont, chan;

	_xdmad.polling = polling;

	for (cont = 0; cont < XDMAC_CONTROLLERS; cont++) {
		Xdmac* xdmac = xdmac_get_instance(cont);
		for (chan = 0; chan < XDMAC_CHANNELS; chan++) {
			xdmac_get_channel_isr(xdmac, chan);
			struct _xdmad_channel *channel = _xdmad_channel(cont, chan);
			channel->xdmac = xdmac;
			channel->id = chan;
			channel->callback = 0;
			channel->user_arg = 0;
			channel->src_txif = 0;
			channel->src_rxif = 0;
			channel->dest_txif = 0;
			channel->dest_rxif = 0;
			channel->state = XDMAD_STATE_FREE;
		}

		if (!polling) {
			uint32_t pid = xdmac_get_periph_id(xdmac);
			/* enable interrupts */
			aic_set_source_vector(pid, xdmad_handler);
			aic_enable(pid);
		}
	}
}

void xdmad_poll(void)
{
	if (_xdmad.polling)
		xdmad_handler();
}

struct _xdmad_channel *xdmad_allocate_channel(uint8_t src, uint8_t dest)
{
	uint32_t i;

	/* Reject peripheral to peripheral transfers */
	if (src != XDMAD_PERIPH_MEMORY && dest != XDMAD_PERIPH_MEMORY) {
		return NULL;
	}

	for (i = 0; i < XDMAD_CHANNELS; i++) {
		struct _xdmad_channel *channel = &_xdmad.channels[i];
		Xdmac *xdmac = channel->xdmac;

		if (channel->state == XDMAD_STATE_FREE) {
			/* Check if source peripheral matches this channel controller */
			if (src != XDMAD_PERIPH_MEMORY)
				if (!is_peripheral_on_xdma_controller(src, xdmac))
					continue;

			/* Check if destination peripheral matches this channel controller */
			if (dest != XDMAD_PERIPH_MEMORY)
				if (!is_peripheral_on_xdma_controller(dest, xdmac))
					continue;

			/* Allocate the channel */
			channel->state = XDMAD_STATE_ALLOCATED;
			channel->src_txif = get_peripheral_xdma_channel(src, xdmac, true);
			channel->src_rxif = get_peripheral_xdma_channel(src, xdmac, false);
			channel->dest_txif = get_peripheral_xdma_channel(dest, xdmac, true);
			channel->dest_rxif = get_peripheral_xdma_channel(dest, xdmac, false);

			return channel;
		}
	}
	return NULL;
}

uint32_t xdmad_free_channel(struct _xdmad_channel *channel)
{
	switch (channel->state) {
	case XDMAD_STATE_STARTED:
		return XDMAD_BUSY;
	case XDMAD_STATE_ALLOCATED:
	case XDMAD_STATE_DONE:
		channel->state = XDMAD_STATE_FREE;
		break;
	}
	return XDMAD_OK;
}

uint32_t xdmad_set_callback(struct _xdmad_channel *channel,
		xdmad_callback_t callback, void *user_arg)
{
	if (channel->state == XDMAD_STATE_FREE)
		return XDMAD_ERROR;
	else if (channel->state == XDMAD_STATE_STARTED)
		return XDMAD_BUSY;

	channel->callback = callback;
	channel->user_arg = user_arg;

	return XDMAD_OK;
}

uint32_t xdmad_prepare_channel(struct _xdmad_channel *channel)
{
	Xdmac *xdmac = channel->xdmac;

	if (channel->state == XDMAD_STATE_FREE)
		return XDMAD_ERROR;
	else if (channel->state == XDMAD_STATE_STARTED)
		return XDMAD_BUSY;

	/* Clear status */
	xdmac_get_global_channel_status(xdmac);
	xdmac_get_global_isr(xdmac);

	/* Enable clock of the DMA peripheral */
	pmc_enable_peripheral(xdmac_get_periph_id(xdmac));

	/* Clear status */
	xdmac_get_channel_isr(xdmac, channel->id);

	/* Disables XDMAC interrupt for the given channel */
	xdmac_disable_global_it(xdmac, -1);
	xdmac_disable_channel_it(xdmac, channel->id, -1);

	/* Disable the given dma channel */
	xdmac_disable_channel(xdmac, channel->id);
	xdmac_set_src_addr(xdmac, channel->id, 0);
	xdmac_set_dest_addr(xdmac, channel->id, 0);
	xdmac_set_block_control(xdmac, channel->id, 0);
	xdmac_set_channel_config(xdmac, channel->id, XDMAC_CC_PROT_UNSEC);
	xdmac_set_descriptor_addr(xdmac, channel->id, 0, 0);
	xdmac_set_descriptor_control(xdmac, channel->id, 0);

	return XDMAD_OK;
}

bool xdmad_is_transfer_done(struct _xdmad_channel *channel)
{
	return channel->state != XDMAD_STATE_STARTED;
}

uint32_t xdmad_configure_transfer(struct _xdmad_channel *channel,
				  struct _xdmad_cfg *cfg,
				  uint32_t desc_cntrl,
				  void *desc_addr)
{
	if (channel->state == XDMAD_STATE_FREE)
		return XDMAD_ERROR;
	else if (channel->state == XDMAD_STATE_STARTED)
		return XDMAD_BUSY;

	Xdmac *xdmac = channel->xdmac;

	if (cfg->cfg.bitfield.dsync == XDMAC_CC_DSYNC_PER2MEM) {
		cfg->cfg.bitfield.perid = channel->src_rxif;
	} else {
		cfg->cfg.bitfield.perid = channel->dest_txif;
	}

	/* Clear status */
	xdmac_get_global_isr(xdmac);
	xdmac_get_channel_isr(xdmac, channel->id);

	if ((desc_cntrl & XDMAC_CNDC_NDE) == XDMAC_CNDC_NDE_DSCR_FETCH_EN) {
		/* Linked List is enabled */
		if ((desc_cntrl & XDMAC_CNDC_NDVIEW_Msk)
		    == XDMAC_CNDC_NDVIEW_NDV0) {
			xdmac_set_channel_config(xdmac, channel->id,
						 cfg->cfg.uint32_value);
			xdmac_set_src_addr(xdmac, channel->id, cfg->src_addr);
			xdmac_set_dest_addr(xdmac, channel->id, cfg->dest_addr);
		}
		else if ((desc_cntrl & XDMAC_CNDC_NDVIEW_Msk)
			 == XDMAC_CNDC_NDVIEW_NDV1) {
			xdmac_set_channel_config(xdmac, channel->id,
						 cfg->cfg.uint32_value);
		}
		xdmac_set_descriptor_addr(xdmac, channel->id, desc_addr, 0);
		xdmac_set_descriptor_control(xdmac, channel->id, desc_cntrl);
		xdmac_disable_channel_it(xdmac, channel->id, -1);
		xdmac_enable_channel_it(xdmac, channel->id, XDMAC_CIE_LIE);
	} else {
		/* Linked List is disabled. */
		xdmac_set_src_addr(xdmac, channel->id, cfg->src_addr);
		xdmac_set_dest_addr(xdmac, channel->id, cfg->dest_addr);
		xdmac_set_microblock_control(xdmac, channel->id, cfg->ublock_size);
		xdmac_set_block_control(xdmac, channel->id,
					cfg->block_size > 1 ? cfg->block_size : 0);
		xdmac_set_data_stride_mem_pattern(xdmac, channel->id,
						  cfg->data_stride);
		xdmac_set_src_microblock_stride(xdmac, channel->id,
						cfg->src_ublock_stride);
		xdmac_set_dest_microblock_stride(xdmac, channel->id,
						 cfg->dest_ublock_stride);
		xdmac_set_channel_config(xdmac, channel->id, cfg->cfg.uint32_value);
		xdmac_set_descriptor_addr(xdmac, channel->id, 0, 0);
		xdmac_set_descriptor_control(xdmac, channel->id, 0);
		xdmac_enable_channel_it(xdmac, channel->id,
					XDMAC_CIE_BIE | XDMAC_CIE_DIE |
					XDMAC_CIE_FIE | XDMAC_CIE_RBIE |
					XDMAC_CIE_WBIE | XDMAC_CIE_ROIE);
	}
	return XDMAD_OK;
}

uint32_t xdmad_start_transfer(struct _xdmad_channel *channel)
{
	if (channel->state == XDMAD_STATE_FREE)
		return XDMAD_ERROR;
	else if (channel->state == XDMAD_STATE_STARTED)
		return XDMAD_BUSY;

	/* Change state to 'started' */
	channel->state = XDMAD_STATE_STARTED;

	/* Start DMA transfer */
	xdmac_enable_channel(channel->xdmac, channel->id);
	if (!_xdmad.polling) {
		xdmac_enable_global_it(channel->xdmac, 1 << channel->id);
	}

	return XDMAD_OK;
}

uint32_t xdmad_stop_transfer(struct _xdmad_channel *channel)
{
	Xdmac *xdmac = channel->xdmac;

	/* Disable channel */
	xdmac_disable_channel(xdmac, channel->id);

	/* Disable interrupts */
	xdmac_disable_channel_it(xdmac, channel->id, -1);

	/* Clear pending status */
	xdmac_get_channel_isr(xdmac, channel->id);
	xdmac_get_global_channel_status(xdmac);

	/* Change state to 'allocated' */
	channel->state = XDMAD_STATE_ALLOCATED;

	return XDMAD_OK;
}

/**@}*/
