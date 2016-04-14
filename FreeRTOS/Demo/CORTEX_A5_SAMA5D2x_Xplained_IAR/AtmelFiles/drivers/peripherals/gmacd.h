/* ----------------------------------------------------------------------------
 *         SAM Software Package License
 * ----------------------------------------------------------------------------
 * Copyright (c) 2012, Atmel Corporation
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

/** \file */

/** \addtogroup gmacd_module
 * @{
 * Implement GMAC data transfer and PHY management functions.
 *
 * \section Usage
 * -# Implement GMAC interrupt handler, which must invoke GMACD_Handler()
 *    to handle GMAC interrupt events.
 * -# Implement struct _gmacd instance in application.
 * -# Initialize the instance with GMACD_Init() and GMACD_InitTransfer(),
 *    so that GMAC data can be transmitted/received.
 * -# Some management callbacks can be set by GMACD_SetRxCallback()
 *    and GMACD_SetTxWakeupCallback().
 * -# Send ethernet packets using GMACD_Send(), GMACD_TxLoad() is used
 *    to check the free space in TX queue.
 * -# Check and obtain received ethernet packets via GMACD_Poll().
 *
 * \sa \ref gmacb_module, \ref gmac_module
 *
 * Related files:\n
 * \ref gmacd.c\n
 * \ref gmacd.h.\n
 *
 *  \defgroup gmacd_defines GMAC Driver Defines
 *  \defgroup gmacd_types GMAC Driver Types
 *  \defgroup gmacd_functions GMAC Driver Functions
 */
/**@}*/

#ifndef _GMACD_H_
#define _GMACD_H_

/*---------------------------------------------------------------------------
 *         Headers
 *---------------------------------------------------------------------------*/

#include "peripherals/gmac.h"
#include <stdint.h>

/*---------------------------------------------------------------------------
 *         Definitions
 *---------------------------------------------------------------------------*/
/** \addtogroup gmacd_defines
    @{*/

/** \addtogroup gmacd_buf_size GMACD Default Buffer Size
        @{*/
#define GMAC_RX_UNITSIZE            128  /**< RX buffer size, must be 128 */
#define GMAC_TX_UNITSIZE            1536 /**< TX buffer size, must be multiple
					   of 32 (cache line) */
/**     @}*/

/** \addtogroup gmacd_rc GMACD Return Codes
        @{*/
#define GMACD_OK                0   /**< Operation OK */
#define GMACD_TX_BUSY           1   /**< TX in progress */
#define GMACD_RX_NULL           1   /**< No data received */
/** Buffer size not enough */
#define GMACD_SIZE_TOO_SMALL    2
/** Parameter error, TX packet invalid or RX size too small */
#define GMACD_PARAM             3
/** Transter is not initialized */
#define GMACD_NOT_INITIALIZED   4
/**     @}*/

/** @}*/

/*---------------------------------------------------------------------------
 *         Types
 *---------------------------------------------------------------------------*/
/** \addtogroup gmacd_types
    @{*/

/** RX/TX callback */
typedef void (*gmacd_callback_t)(uint8_t queue, uint32_t status);

/** TX Wakeup callback */
typedef void (*gmacd_wakeup_cb_t)(uint8_t queue);

/** GMAC scatter-gather entry */
struct _gmac_sg {
	uint32_t         size;
	void            *buffer;
	struct _gmac_sg *next;
};

/** GMAC scatter-gather list */
struct _gmac_sg_list {
	uint32_t         size;
	struct _gmac_sg *entries;
};

struct _gmacd_queue {
	uint8_t           *rx_buffer;
	struct _gmac_desc *rx_desc;
	uint16_t           rx_size;
	uint16_t           rx_head;
	gmacd_callback_t   rx_callback;

	uint8_t           *tx_buffer;
	struct _gmac_desc *tx_desc;
	uint16_t           tx_size;
	uint16_t           tx_head;
	uint16_t           tx_tail;
	gmacd_callback_t  *tx_callbacks;

	gmacd_wakeup_cb_t  tx_wakeup_callback;
	uint16_t           tx_wakeup_threshold;
};

/**
 * GMAC driver struct.
 */
struct _gmacd {
	Gmac* gmac; /**< GMAC instance */
	struct _gmacd_queue queues[GMAC_NUM_QUEUES];
};

/** @}*/

/** \addtogroup gmacd_functions
    @{*/

/*---------------------------------------------------------------------------
 *         GMAC Exported functions
 *---------------------------------------------------------------------------*/

extern void gmacd_configure(struct _gmacd* gmacd, Gmac *pHw, uint8_t enableCAF, uint8_t enableNBC);

extern uint8_t gmacd_setup_queue(struct _gmacd* gmacd, uint8_t queue,
		uint16_t rx_size, uint8_t* rx_buffer, struct _gmac_desc* rx_desc,
		uint16_t tx_size, uint8_t* tx_buffer, struct _gmac_desc* tx_desc,
		gmacd_callback_t *tx_callbacks);

extern void gmacd_start(struct _gmacd* gmacd);

extern void gmacd_reset(struct _gmacd* gmacd);

extern uint8_t gmacd_send_sg(struct _gmacd* gmacd, uint8_t queue,
		const struct _gmac_sg_list* sgl, gmacd_callback_t callback);

extern uint8_t gmacd_send(struct _gmacd* gmacd, uint8_t queue, void *buffer,
		uint32_t size, gmacd_callback_t callback);

extern uint32_t gmacd_get_tx_load(struct _gmacd* gmacd, uint8_t queue);

extern uint8_t gmacd_poll(struct _gmacd* gmacd, uint8_t queue,
		uint8_t* buffer, uint32_t buffer_size, uint32_t* recv_size);

extern void gmacd_set_rx_callback(struct _gmacd *gmacd, uint8_t queue,
		gmacd_callback_t callback);

extern uint8_t gmacd_set_tx_wakeup_callback(struct _gmacd *gmacd,
		uint8_t queue, gmacd_wakeup_cb_t wakeup_callback,
		uint16_t threshold);

/** @}*/

#endif /* _GMACD_H_ */
