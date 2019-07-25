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

/*------------------------------------------------------------------------------
 *         Headers
 *------------------------------------------------------------------------------*/

#include "chip.h"
#include "peripherals/flexcom.h"

#include "peripherals/usart.h"
#include "peripherals/spi.h"
#include "peripherals/twi.h"

#include <assert.h>

/*------------------------------------------------------------------------------
 *         Exported functions
 *------------------------------------------------------------------------------*/

/**
 * \brief Select a protocol for a FLEXCOM device
 *
 *
 *  \param flexcom  Pointer to FLEXCOM peripheral to configure.
 *  \param protocol  Protocol to use.
 */
void flexcom_select(Flexcom * flexcom, uint32_t protocol)
{
	assert(flexcom);
	uint32_t current_protocol = flexcom->FLEX_MR;

	usart_set_receiver_enabled(&flexcom->usart, 0u);

	/* Shutdown previous protocol */
	switch (current_protocol) {
	case FLEX_MR_OPMODE_USART:
		usart_set_receiver_enabled(&flexcom->usart, 0u);
		usart_set_transmitter_enabled(&flexcom->usart, 0u);
		break;
	case FLEX_MR_OPMODE_SPI:
		spi_disable(&flexcom->spi);
		break;
	case FLEX_MR_OPMODE_TWI:
		twi_stop(&flexcom->twi);
	default:
		break;
	}

	assert(protocol & FLEX_MR_OPMODE_NO_COM ||
	       protocol & FLEX_MR_OPMODE_USART ||
	       FLEX_MR_OPMODE_SPI || FLEX_MR_OPMODE_TWI);

	/* Activate the new mode () */
	flexcom->FLEX_MR = protocol;
}
