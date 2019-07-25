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

#ifndef _XDMAD_H_
#define _XDMAD_H_

/*----------------------------------------------------------------------------
 *        Includes
 *----------------------------------------------------------------------------*/

#include "chip.h"
#include "peripherals/xdmac.h"

#include <stdbool.h>

/*----------------------------------------------------------------------------
 *        Consts
 *----------------------------------------------------------------------------*/

/** \addtogroup dmad_defines DMA Driver Defines
        @{*/

/** Pseudo Peripheral ID for memory transfers */
#define XDMAD_PERIPH_MEMORY 0xFF

/* XDMA_MBR_UBC */

#define XDMA_UBC_NDE (0x1u << 24)
#define   XDMA_UBC_NDE_FETCH_DIS (0x0u << 24)
#define   XDMA_UBC_NDE_FETCH_EN  (0x1u << 24)

#define XDMA_UBC_NSEN (0x1u << 25)
#define   XDMA_UBC_NSEN_UNCHANGED (0x0u << 25)
#define   XDMA_UBC_NSEN_UPDATED (0x1u << 25)

#define XDMA_UBC_NDEN (0x1u << 26)
#define   XDMA_UBC_NDEN_UNCHANGED (0x0u << 26)
#define   XDMA_UBC_NDEN_UPDATED (0x1u << 26)

#define XDMA_UBC_NVIEW_Pos 27
#define    XDMA_UBC_NVIEW_Msk (0x3u << XDMA_UBC_NVIEW_Pos)
#define    XDMA_UBC_NVIEW_NDV0 (0x0u << XDMA_UBC_NVIEW_Pos)
#define    XDMA_UBC_NVIEW_NDV1 (0x1u << XDMA_UBC_NVIEW_Pos)
#define    XDMA_UBC_NVIEW_NDV2 (0x2u << XDMA_UBC_NVIEW_Pos)
#define    XDMA_UBC_NVIEW_NDV3 (0x3u << XDMA_UBC_NVIEW_Pos)

/**     @}*/

/*----------------------------------------------------------------------------
 *        Types
 *----------------------------------------------------------------------------*/

/** \addtogroup dmad_structs DMA Driver Structs
        @{*/

/** DMA status or return code */
enum {
	XDMAD_OK = 0,	     /**< Operation is sucessful */
	XDMAD_PARTIAL_DONE,
	XDMAD_DONE,
	XDMAD_BUSY,	     /**< Channel occupied or transfer not finished */
	XDMAD_ERROR,	     /**< Operation failed */
	XDMAD_CANCELED	     /**< Operation canceled */
};

/** DMA channel */
struct _xdmad_channel;

/** DMA transfer callback */
typedef void (*xdmad_callback_t)(struct _xdmad_channel *channel, void *arg);

union _xdmac_cfg_reg {
	uint32_t uint32_value;
	struct {
		uint32_t type:  1,
			mbsize: 2,
			dummy1: 1,
			dsync:  1,
			prot:   1,
			sweq:   1,
			memset: 1,
			csize:  3,
			dwidth: 2,
			sif:    1,
			dif:    1,
			dummy2: 1,
			sam:    2,
			dam:    2,
			dummy3: 1,
			initd:  1,
			rdip:   1,
			wrip:   1,
			perid:  7;
	} bitfield;
};

struct _xdmad_cfg {
	uint32_t ublock_size;        /**< Microblock Size */
	uint32_t block_size;         /**< Block Size (number of Microblock) */
	uint32_t data_stride;        /**< Data Stride */
	uint32_t src_ublock_stride;  /**< Source Microblock Stride */
	uint32_t dest_ublock_stride; /**< Destination Microblock Stride */
	void    *src_addr;           /**< Source Address */
	void    *dest_addr;          /**< Destination Address */
	union _xdmac_cfg_reg cfg;    /**< Configuration Register */
};

/** Structure for storing parameters for DMA view0 that can be performed by the
 * DMA Master transfer.*/
struct _xdmad_desc_view0 {
	void    *next_desc;   /**< Next Descriptor Address */
	uint32_t ublock_size; /**< Microblock Control */
	uint32_t mbr_ta;      /**< Transfer Address */
};

/** Structure for storing parameters for DMA view1 that can be performed by the
 * DMA Master transfer.*/
struct _xdmad_desc_view1 {
	void    *next_desc;   /**< Next Descriptor Address */
	uint32_t ublock_size; /**< Microblock Control */
	void    *src_addr;    /**< Source Address */
	void    *dest_addr;   /**< Destination Address */
};

/** Structure for storing parameters for DMA view2 that can be performed by the
 * DMA Master transfer.*/
struct _xdmad_desc_view2 {
	void    *next_desc;   /**< Next Descriptor Address */
	uint32_t ublock_size; /**< Microblock Control */
	void    *src_addr;    /**< Source Address */
	void    *dest_addr;   /**< Destination Address */
	union _xdmac_cfg_reg cfg; /**< Configuration Register */
};

/** Structure for storing parameters for DMA view3 that can be performed by the
 * DMA Master transfer.*/
struct _xdmad_desc_view3 {
	void    *next_desc;   /**< Next Descriptor Address */
	uint32_t ublock_size; /**< Microblock Control */
	void    *src_addr;    /**< Source Address */
	void    *dest_addr;   /**< Destination Address */
	union _xdmac_cfg_reg cfg;
	uint32_t block_size;   /**< Block Control */
	uint32_t data_stride;  /**< Data Stride */
	uint32_t src_ublock_stride;  /**< Source Microblock Stride */
	uint32_t dest_ublock_stride; /**< Destination Microblock Stride */
};

/**     @}*/

/*----------------------------------------------------------------------------
 *        Exported functions
 *----------------------------------------------------------------------------*/
/** \addtogroup dmad_functions DMA Driver Functionos
        @{*/

/**
 * \brief Initialize DMA driver instance.
 * \param polling if true, interrupts will not be configured and xdmad_poll
 * must be called to poll for transfer completion
 */
extern void xdmad_initialize(bool polling);

/**
 * \brief Poll for transfers completion.
 * If polling mode is enabled, this function will call callbacks for completed
 * transfers.  If interrupt mode is enabled, this function will do nothing.
 */
extern void xdmad_poll(void);

/**
 * \brief Allocate an DMA channel
 * \param src Source peripheral ID, XDMAD_PERIPH_MEMORY for memory.
 * \param dest Destination peripheral ID, XDMAD_PERIPH_MEMORY for memory.
 * \return Channel pointer if allocation successful, or NULL if channel
 * allocation failed.
 */
extern struct _xdmad_channel *xdmad_allocate_channel(uint8_t src, uint8_t dest);

/**
 * \brief Free the specified DMA channel.
 * \param channel Channel pointer
 */
extern uint32_t xdmad_free_channel(struct _xdmad_channel *channel);

/**
 * \brief Set the callback function for an DMA channel transfer.
 * \param channel Channel pointer
 * \param callback Pointer to callback function.
 * \param user_arg Pointer to user argument for callback.
 */
extern uint32_t xdmad_set_callback(struct _xdmad_channel *channel,
		xdmad_callback_t callback, void *user_arg);

/**
 * \brief Enable clock of the DMA peripheral, Enable the peripheral,
 * setup configuration register for transfer.
 * \param channel Channel pointer
 */
extern uint32_t xdmad_prepare_channel(struct _xdmad_channel *channel);

/**
 * \brief Configure DMA for a single transfer.
 * \param channel Channel pointer
 * \param cfg DMA transfer configuration
 * \param desc_cntrl optional descriptor control
 * \param desc_addr optional descriptor address
 */
extern uint32_t xdmad_configure_transfer(struct _xdmad_channel *channel,
		struct _xdmad_cfg *cfg, uint32_t desc_cntrl, void *desc_addr);

/**
 * \brief Start DMA transfer.
 * \param channel Channel pointer
 */
extern uint32_t xdmad_start_transfer(struct _xdmad_channel *channel);

/**
 * \brief Check if DMA transfer is finished.
 * \param channel Channel pointer
 */
extern bool xdmad_is_transfer_done(struct _xdmad_channel *channel);

/**
 * \brief Stop DMA transfer.
 * \param channel Channel pointer
 */
extern uint32_t xdmad_stop_transfer(struct _xdmad_channel *channel);

/**     @}*/

/**@}*/

#endif /* _XDMAD_H_ */
