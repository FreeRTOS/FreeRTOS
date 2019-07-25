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
#include "peripherals/uart.h"
#include "peripherals/pmc.h"

#include <stdint.h>

/*------------------------------------------------------------------------------
 *         Exported functions
 *------------------------------------------------------------------------------*/

/*
 * Initializes the UART with the given parameters, and enables both the
 * transmitter and the receiver. The mode parameter contains the value of the
 * UART_MR register.
 * Value UART_STANDARD can be used for mode to get the most common configuration
 * (i.e. aysnchronous, 8bits, no parity, 1 stop bit, no flow control).
 * \param mode  Operating mode to configure.
 * \param baudrate  Desired baudrate (e.g. 115200).
 * \param mck  Frequency of the system master clock in Hz.
 */
void uart_configure(Uart* pUart, uint32_t mode, uint32_t baudrate)
{
	uint32_t uart_id = get_uart_id_from_addr(pUart);
	// Reset & disable receiver and transmitter, disable interrupts
	pUart->UART_CR = UART_CR_RSTRX | UART_CR_RSTTX | UART_CR_RXDIS | UART_CR_TXDIS
		| UART_CR_RSTSTA;
	pUart->UART_IDR = 0xFFFFFFFF;
	// Configure baud rate
	pUart->UART_BRGR = pmc_get_peripheral_clock(uart_id) / (baudrate * 16);
	// Configure mode register
	pUart->UART_MR = mode;
	// Enable receiver and transmitter
	pUart->UART_CR = UART_CR_RXEN | UART_CR_TXEN;
}

/* Enable transmitter
 *
 */
void uart_set_transmitter_enabled (Uart* pUart, uint8_t enabled)
{
	if (enabled) pUart->UART_CR = UART_CR_TXEN;
	else pUart->UART_CR = UART_CR_TXDIS;
}

/* Enable receiver
 *
 */
void uart_set_receiver_enabled (Uart* pUart, uint8_t enabled)
{
	if (enabled)
		pUart->UART_CR = UART_CR_RXEN;
	else
		pUart->UART_CR = UART_CR_RXDIS;
}

/* Set interrupt register
 *
 */
void uart_set_int (Uart* pUart, uint32_t int_mask)
{
	pUart->UART_IER |= int_mask;
}

/**
 * Outputs a character on the UART line.
 * \note This function is synchronous (i.e. uses polling).
 * \param c  Character to send.
 */
void uart_put_char(Uart* pUart, uint8_t c)
{
	// Wait for the transmitter to be ready
	while ((pUart->UART_SR & UART_SR_TXEMPTY) == 0);
	// Send character
	pUart->UART_THR = c;
}

/**
 * Return 1 if a character can be read in UART
 */
uint32_t uart_is_rx_ready(Uart* pUart)
{
	return (pUart->UART_SR & UART_SR_RXRDY);
}

/**
 * Return 1 if a character can be write in UART
 */
uint32_t uart_is_tx_ready(Uart* pUart)
{
	return (pUart->UART_SR & UART_SR_TXRDY);
}

/**
 * \brief Reads and returns a character from the UART.
 * \note This function is synchronous (i.e. uses polling).
 * \return Character received.
 */
uint8_t uart_get_char(Uart* pUart)
{
	while ((pUart->UART_SR & UART_SR_RXRDY) == 0);
	return pUart->UART_RHR;
}
