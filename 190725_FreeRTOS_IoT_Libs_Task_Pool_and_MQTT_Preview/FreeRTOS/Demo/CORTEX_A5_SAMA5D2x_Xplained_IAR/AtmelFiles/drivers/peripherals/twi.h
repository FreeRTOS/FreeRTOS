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

/**
 * \file
 *
 * Interface for configuration the Two Wire Interface (TWI) peripheral.
 *
 */

#ifndef _TWI_H_
#define _TWI_H_

/*------------------------------------------------------------------------------
 *         Headers
 *------------------------------------------------------------------------------*/

#include "chip.h"

#include <stdint.h>

/*----------------------------------------------------------------------------
 *        Macros
 *----------------------------------------------------------------------------*/
/* Returns 1 if the TXRDY bit (ready to transmit data) is set in the given status register value.*/
#define TWI_STATUS_TXRDY(status) ((status & TWI_SR_TXRDY) == TWI_SR_TXRDY)

/* Returns 1 if the RXRDY bit (ready to receive data) is set in the given status register value.*/
#define TWI_STATUS_RXRDY(status) ((status & TWI_SR_RXRDY) == TWI_SR_RXRDY)

/* Returns 1 if the TXCOMP bit (transfer complete) is set in the given status register value.*/
#define TWI_STATUS_TXCOMP(status) ((status & TWI_SR_TXCOMP) == TWI_SR_TXCOMP)

#ifdef __cplusplus
extern "C" {
#endif

/*----------------------------------------------------------------------------
 *        External function
 *----------------------------------------------------------------------------*/

extern void twi_configure_master(Twi * pTwi, uint32_t twck);
extern void twi_configure_slave(Twi * pTwi, uint8_t slaveAddress);
extern void twi_stop(Twi * pTwi);
extern void twi_start_read(Twi * pTwi, uint8_t address,
						   uint32_t iaddress, uint8_t isize);
extern uint8_t twi_read_byte(Twi * pTwi);
extern void twi_write_byte(Twi * pTwi, uint8_t byte);
extern void twi_start_write(Twi * pTwi, uint8_t address, uint32_t iaddress,
							uint8_t isize, uint8_t byte);
extern uint8_t twi_is_byte_received(Twi * pTwi);
extern uint8_t twi_byte_sent(Twi * pTwi);
extern uint8_t twi_is_transfer_complete(Twi * pTwi);
extern void twi_enable_it(Twi * pTwi, uint32_t sources);
extern void twi_disable_it(Twi * pTwi, uint32_t sources);
extern uint32_t twi_get_status(Twi * pTwi);
extern uint32_t twi_get_masked_status(Twi * pTwi);
extern void twi_send_stop_condition(Twi * pTwi);

#ifdef CONFIG_HAVE_TWI_ALTERNATE_CMD
extern void twi_init_write_transfert(Twi * twi, uint8_t addr, uint32_t iaddress,
				     uint8_t isize, uint8_t len);
extern void twi_init_read_transfert(Twi * twi, uint8_t addr, uint32_t iaddress,
				    uint8_t isize, uint8_t len);
#endif

#ifdef CONFIG_HAVE_TWI_FIFO
extern void twi_fifo_configure(Twi* twi, uint8_t tx_thres,
			uint8_t rx_thres,
			uint32_t ready_modes);
extern void twi_fifo_disable(Twi* twi);

extern uint32_t twi_fifo_rx_size(Twi *twi);
extern uint32_t twi_fifo_tx_size(Twi *twi);

extern uint32_t twi_read_stream(Twi *twi, uint32_t addr, uint32_t iaddr,
				 uint32_t isize, const void *stream, uint8_t len);
extern uint32_t twi_write_stream(Twi *twi, uint32_t addr, uint32_t iaddr,
				 uint32_t isize, const void *stream, uint8_t len);
#endif

#ifdef __cplusplus
}
#endif
#endif /* #ifndef _TWI_H_ */
