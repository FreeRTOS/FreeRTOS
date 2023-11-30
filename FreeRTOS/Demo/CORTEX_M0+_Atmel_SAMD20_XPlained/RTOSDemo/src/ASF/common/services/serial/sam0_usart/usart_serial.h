/**
 * \file
 *
 * \brief USART Serial wrapper service for the SAM D20 devices.
 *
 * Copyright (c) 2009-2013 Atmel Corporation. All rights reserved.
 *
 * \asf_license_start
 *
 * \page License
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * 1. Redistributions of source code must retain the above copyright notice,
 *    this list of conditions and the following disclaimer.
 *
 * 2. Redistributions in binary form must reproduce the above copyright notice,
 *    this list of conditions and the following disclaimer in the documentation
 *    and/or other materials provided with the distribution.
 *
 * 3. The name of Atmel may not be used to endorse or promote products derived
 *    from this software without specific prior written permission.
 *
 * 4. This software may only be redistributed and used in connection with an
 *    Atmel microcontroller product.
 *
 * THIS SOFTWARE IS PROVIDED BY ATMEL "AS IS" AND ANY EXPRESS OR IMPLIED
 * WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NON-INFRINGEMENT ARE
 * EXPRESSLY AND SPECIFICALLY DISCLAIMED. IN NO EVENT SHALL ATMEL BE LIABLE FOR
 * ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT,
 * STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN
 * ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
 * POSSIBILITY OF SUCH DAMAGE.
 *
 * \asf_license_stop
 *
 */
#ifndef _USART_SERIAL_H_
#define _USART_SERIAL_H_

#include "compiler.h"
#ifndef SAMD20
# include "sysclk.h"
#endif
#include "status_codes.h"
#include "usart.h"

/*! \name Serial Management Configuration
 */
//! @{
//#include "conf_usart_serial.h"
//! @}

typedef Sercom * usart_inst_t;

struct usart_module usart;

/*! \brief Initializes the Usart in master mode.
 *
 * \param usart       Base address of the USART instance.
 * \param options     Options needed to set up RS232 communication (see \ref usart_serial_options_t).
 *
 * \retval true if the initialization was successful
 * \retval false if initialization failed (error in baud rate calculation)
 */
static inline bool usart_serial_init(struct usart_module *const module,
		usart_inst_t const hw, const struct usart_config *const config)
{
	if (usart_init(module, hw, config) == STATUS_OK) {
		return true;
	}
	else {
		return false;
	}
}

/*! \brief Sends a character with the USART.
 *
 * \param usart   Base address of the USART instance.
 * \param c       Character to write.
 *
 * \return Status code
 */
static inline enum status_code usart_serial_putchar(struct usart_module *const module,
		uint8_t c)
{
	return usart_write_wait(module, c);
}
/*! \brief Waits until a character is received, and returns it.
 *
 * \param usart   Base address of the USART instance.
 * \param data   Data to read
 *
 */
static inline void usart_serial_getchar(struct usart_module *const module,
		uint8_t *c)
{
	uint16_t temp;

	usart_read_wait(module, &temp);

	*c = temp;
}

/**
 * \brief Send a sequence of bytes to USART device
 *
 * \param usart  Base address of the USART instance.
 * \param data   Data buffer to read
 * \param len    Length of data
 *
 */
static inline enum status_code usart_serial_write_packet(struct usart_module *const module,
		const uint8_t *tx_data, uint16_t length)
{
	return usart_write_buffer_wait(module, tx_data, length);
}

/**
 * \brief Receive a sequence of bytes from USART device
 *
 * \param usart  Base address of the USART instance.
 * \param data   Data buffer to write
 * \param len    Length of data
 *
 */
static inline enum status_code usart_serial_read_packet(struct usart_module *const module,
		uint8_t *rx_data, uint16_t length)
{
	return usart_read_buffer_wait(module, rx_data, length);
}

#endif  // _USART_SERIAL_H_
