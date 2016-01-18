/**
 * \file
 *
 * \brief Universal Asynchronous Receiver Transceiver (UART) driver for SAM.
 *
 * Copyright (c) 2011-2015 Atmel Corporation. All rights reserved.
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
/*
 * Support and FAQ: visit <a href="http://www.atmel.com/design-support/">Atmel Support</a>
 */

#include "uart.h"

/// @cond 0
/**INDENT-OFF**/
#ifdef __cplusplus
extern "C" {
#endif
/**INDENT-ON**/
/// @endcond

/**
 * \defgroup sam_drivers_uart_group Universal Asynchronous Receiver Transceiver (UART)
 *
 * The Universal Asynchronous Receiver Transmitter features a two-pin UART that
 * can be used for communication and trace purposes and offers an ideal medium
 * for in-situ programming solutions. Moreover, the association with two
 * peripheral DMA controller (PDC) channels permits packet handling for these
 * tasks with processor time reduced to a minimum.
 *
 * \par Usage
 *
 * -# Enable the UART peripheral clock in the PMC.
 * -# Enable the required UART PIOs (see pio.h).
 * -# Configure the UART by calling uart_init.
 * -# Send data through the UART using the uart_write.
 * -# Receive data from the UART using the uart_read; the availability of data
 *    can be polled with uart_is_rx_ready.
 * -# Disable the transmitter and/or the receiver of the UART with
 *    uart_disable_tx and uart_disable_rx.
 *
 * @{
 */

/**
 * \brief Configure UART with the specified parameters.
 *
 * \note The PMC and PIOs must be configured first.
 *
 * \param p_uart Pointer to a UART instance.
 * \param p_uart_opt Pointer to sam_uart_opt_t instance.
 *
 * \retval 0 Success.
 * \retval 1 Bad baud rate generator value.
 */
uint32_t uart_init(Uart *p_uart, const sam_uart_opt_t *p_uart_opt)
{
	uint32_t cd = 0;

	/* Reset and disable receiver & transmitter */
	p_uart->UART_CR = UART_CR_RSTRX | UART_CR_RSTTX
			| UART_CR_RXDIS | UART_CR_TXDIS;

	/* Check and configure baudrate */
	/* Asynchronous, no oversampling */
	cd = (p_uart_opt->ul_mck / p_uart_opt->ul_baudrate) / UART_MCK_DIV;
	if (cd < UART_MCK_DIV_MIN_FACTOR || cd > UART_MCK_DIV_MAX_FACTOR)
		return 1;

	p_uart->UART_BRGR = cd;
	/* Configure mode */
	p_uart->UART_MR = p_uart_opt->ul_mode;

#if (!SAMV71 && !SAMV70 && !SAME70 && !SAMS70)
	/* Disable PDC channel */
	p_uart->UART_PTCR = UART_PTCR_RXTDIS | UART_PTCR_TXTDIS;
#endif

	/* Enable receiver and transmitter */
	p_uart->UART_CR = UART_CR_RXEN | UART_CR_TXEN;

	return 0;
}

/**
 * \brief Enable UART transmitter.
 *
 * \param p_uart Pointer to a UART instance.
 */
void uart_enable_tx(Uart *p_uart)
{
	/* Enable transmitter */
	p_uart->UART_CR = UART_CR_TXEN;
}

/**
 * \brief Disable UART transmitter.
 *
 * \param p_uart Pointer to a UART instance.
 */
void uart_disable_tx(Uart *p_uart)
{
	/* Disable transmitter */
	p_uart->UART_CR = UART_CR_TXDIS;
}

/**
 * \brief Reset UART transmitter.
 *
 * \param p_uart Pointer to a UART instance.
 */
void uart_reset_tx(Uart *p_uart)
{
	/* Reset transmitter */
	p_uart->UART_CR = UART_CR_RSTTX | UART_CR_TXDIS;
}

/**
 * \brief Enable UART receiver.
 *
 * \param p_uart Pointer to a UART instance.
 */
void uart_enable_rx(Uart *p_uart)
{
	/* Enable receiver */
	p_uart->UART_CR = UART_CR_RXEN;
}

/**
 * \brief Disable UART receiver.
 *
 * \param p_uart Pointer to a UART instance.
 */
void uart_disable_rx(Uart *p_uart)
{
	/* Disable receiver */
	p_uart->UART_CR = UART_CR_RXDIS;
}

/**
 * \brief Reset UART receiver.
 *
 * \param p_uart Pointer to a UART instance.
 */
void uart_reset_rx(Uart *p_uart)
{
	/* Reset receiver */
	p_uart->UART_CR = UART_CR_RSTRX | UART_CR_RXDIS;
}

/**
 * \brief Enable UART receiver and transmitter.
 *
 * \param p_uart Pointer to a UART instance.
 */
void uart_enable(Uart *p_uart)
{
	/* Enable receiver and transmitter */
	p_uart->UART_CR = UART_CR_RXEN | UART_CR_TXEN;
}

/**
 * \brief Disable UART receiver and transmitter.
 *
 * \param p_uart Pointer to a UART instance.
 */
void uart_disable(Uart *p_uart)
{
	/* Disable receiver and transmitter */
	p_uart->UART_CR = UART_CR_RXDIS | UART_CR_TXDIS;
}

/**
 * \brief Reset UART receiver and transmitter.
 *
 * \param p_uart Pointer to a UART instance.
 */
void uart_reset(Uart *p_uart)
{
	/* Reset and disable receiver & transmitter */
	p_uart->UART_CR = UART_CR_RSTRX | UART_CR_RSTTX
			| UART_CR_RXDIS | UART_CR_TXDIS;
}

/** \brief Enable UART interrupts.
 *
 * \param p_uart Pointer to a UART instance.
 *  \param ul_sources Interrupts to be enabled.
 */
void uart_enable_interrupt(Uart *p_uart, uint32_t ul_sources)
{
	p_uart->UART_IER = ul_sources;
}

/** \brief Disable UART interrupts.
 *
 * \param p_uart Pointer to a UART instance.
 *  \param ul_sources Interrupts to be disabled.
 */
void uart_disable_interrupt(Uart *p_uart, uint32_t ul_sources)
{
	p_uart->UART_IDR = ul_sources;
}

/** \brief Read UART interrupt mask.
 *
 * \param p_uart Pointer to a UART instance.
 *
 *  \return The interrupt mask value.
 */
uint32_t uart_get_interrupt_mask(Uart *p_uart)
{
	return p_uart->UART_IMR;
}

/**
 * \brief Get current status.
 *
 * \param p_uart Pointer to a UART instance.
 *
 * \return The current UART status.
 */
uint32_t uart_get_status(Uart *p_uart)
{
	return p_uart->UART_SR;
}

/**
 * \brief Reset status bits.
 *
 * \param p_uart Pointer to a UART instance.
 */
void uart_reset_status(Uart *p_uart)
{
	p_uart->UART_CR = UART_CR_RSTSTA;
}

/**
 * \brief Check if Transmit is Ready.
 * Check if data has been loaded in UART_THR and is waiting to be loaded in the
 * Transmit Shift Register (TSR).
 *
 * \param p_uart Pointer to a UART instance.
 *
 * \retval 1 Data has been transmitted.
 * \retval 0 Transmit is not ready, data pending.
 */
uint32_t uart_is_tx_ready(Uart *p_uart)
{
	return (p_uart->UART_SR & UART_SR_TXRDY) > 0;
}

/**
 * \brief Check if Transmit Hold Register is empty.
 * Check if the last data written in UART_THR has been loaded in TSR and the
 * last data loaded in TSR has been transmitted.
 *
 * \param p_uart Pointer to a UART instance.
 *
 * \retval 1 Transmitter is empty.
 * \retval 0 Transmitter is not empty.
 */
uint32_t uart_is_tx_empty(Uart *p_uart)
{
	return (p_uart->UART_SR & UART_SR_TXEMPTY) > 0;
}

/**
 * \brief Check if Received data is ready.
 * Check if data has been received and loaded in UART_RHR.
 *
 * \param p_uart Pointer to a UART instance.
 *
 * \retval 1 One data has been received.
 * \retval 0 No data has been received.
 */
uint32_t uart_is_rx_ready(Uart *p_uart)
{
	return (p_uart->UART_SR & UART_SR_RXRDY) > 0;
}

/**
 * \brief Check if both transmit buffers are sent out.
 *
 * \param p_uart Pointer to a UART instance.
 *
 * \retval 1 Transmit buffer is empty.
 * \retval 0 Transmit buffer is not empty.
 */
uint32_t uart_is_tx_buf_empty(Uart *p_uart)
{
	return (p_uart->UART_SR & UART_SR_TXEMPTY) > 0;
}

/**
 * \brief Set UART clock divisor value
 *
 * \param p_uart Pointer to a UART instance.
 * \param us_divisor Value to be set.
 *
 */
void uart_set_clock_divisor(Uart *p_uart, uint16_t us_divisor)
{
	p_uart->UART_BRGR = us_divisor;
}

/**
 * \brief Write to UART Transmit Holding Register
 * Before writing user should check if tx is ready (or empty).
 *
 * \param p_uart Pointer to a UART instance.
 * \param data Data to be sent.
 *
 * \retval 0 Success.
 * \retval 1 I/O Failure, UART is not ready.
 */
uint32_t uart_write(Uart *p_uart, const uint8_t uc_data)
{
	/* Check if the transmitter is ready */
	if (!(p_uart->UART_SR & UART_SR_TXRDY))
		return 1;

	/* Send character */
	p_uart->UART_THR = uc_data;
	return 0;
}

/**
 * \brief Read from UART Receive Holding Register.
 * Before reading user should check if rx is ready.
 *
 * \param p_uart Pointer to a UART instance.
 *
 * \retval 0 Success.
 * \retval 1 I/O Failure, UART is not ready.
 */
uint32_t uart_read(Uart *p_uart, uint8_t *puc_data)
{
	/* Check if the receiver is ready */
	if ((p_uart->UART_SR & UART_SR_RXRDY) == 0)
		return 1;

	/* Read character */
	*puc_data = (uint8_t) p_uart->UART_RHR;
	return 0;
}

#if (!SAMV71 && !SAMV70 && !SAME70 && !SAMS70)
/**
 * \brief Check if one receive buffer is filled.
 *
 * \param p_uart Pointer to a UART instance.
 *
 * \retval 1 Receive is completed.
 * \retval 0 Receive is still pending.
 */
uint32_t uart_is_rx_buf_end(Uart *p_uart)
{
	return (p_uart->UART_SR & UART_SR_ENDRX) > 0;
}

/**
 * \brief Check if one transmit buffer is sent out.
 *
 * \param p_uart Pointer to a UART instance.
 *
 * \retval 1 Transmit is completed.
 * \retval 0 Transmit is still pending.
 */
uint32_t uart_is_tx_buf_end(Uart *p_uart)
{
	return (p_uart->UART_SR & UART_SR_ENDTX) > 0;
}

/**
 * \brief Check if both receive buffers are full.
 *
 * \param p_uart Pointer to a UART instance.
 *
 * \retval 1 Receive buffers are full.
 * \retval 0 Receive buffers are not full.
 */
uint32_t uart_is_rx_buf_full(Uart *p_uart)
{
	return (p_uart->UART_SR & UART_SR_RXBUFF) > 0;
}

/**
 * \brief Get UART PDC base address.
 *
 * \param p_uart Pointer to a UART instance.
 *
 * \return UART PDC registers base for PDC driver to access.
 */
Pdc *uart_get_pdc_base(Uart *p_uart)
{
	Pdc *p_pdc_base;

#if (SAM3S || SAM3N || SAM4S || SAM4E || SAM4N || SAM4C || SAMG || SAM4CP || SAM4CM)
	if (p_uart == UART0)
		p_pdc_base = PDC_UART0;
#elif (SAM3XA || SAM3U)
	if (p_uart == UART)
		p_pdc_base = PDC_UART;
#else
#error "Unsupported device"
#endif

#if (SAM3S || SAM4S || SAM4E || SAM4N || SAM4C || SAMG || SAM4CP || SAM4CM)
	if (p_uart == UART1)
		p_pdc_base = PDC_UART1;
#endif

#if (SAM4N)
	if (p_uart == UART2)
		p_pdc_base = PDC_UART2;
#endif

	return p_pdc_base;
}
#endif

#if (SAM4C || SAM4CP || SAM4CM)
/**
 * \brief Enable UART optical interface.
 *
 * \param p_uart Pointer to a UART instance.
 */
void uart_enable_optical_interface(Uart *p_uart)
{
	Assert(p_uart == UART1);
	p_uart->UART_MR |= UART_MR_OPT_EN;
}

/**
 * \brief Disable UART optical interface.
 *
 * \param p_uart Pointer to a UART instance.
 */
void uart_disable_optical_interface(Uart *p_uart)
{
	Assert(p_uart == UART1);
	p_uart->UART_MR &= ~UART_MR_OPT_EN;
}

/**
 * \brief Enable UART optical interface.
 *
 * \param p_uart Pointer to a UART instance.
 * \param cfg Pointer to a UART optical interface configuration.
 */
void uart_config_optical_interface(Uart *p_uart,
		struct uart_config_optical *cfg)
{
	Assert(p_uart == UART1);
	uint32_t reg = p_uart->UART_MR;

	reg &= ~(UART_MR_OPT_RXINV | UART_MR_OPT_MDINV | UART_MR_FILTER
			| UART_MR_OPT_CLKDIV_Msk | UART_MR_OPT_DUTY_Msk
			| UART_MR_OPT_CMPTH_Msk);
	reg |= (cfg->rx_inverted ? UART_MR_OPT_RXINV : 0)
			| (cfg->tx_inverted ? UART_MR_OPT_MDINV : 0)
			| (cfg->rx_filter ? UART_MR_FILTER : 0)
			| UART_MR_OPT_CLKDIV(cfg->clk_div)
			| cfg->duty | cfg->threshold;

	p_uart->UART_MR = reg;
}
#endif

#if (SAMG53 || SAMG54 || SAMV71 || SAMV70 || SAME70 || SAMS70)
/**
 * \brief Set sleepwalking match mode.
 *
 * \param p_uart Pointer to a UART instance.
 * \param ul_low_value First comparison value for received character.
 * \param ul_high_value Second comparison value for received character.
 * \param cmpmode ture for start condition, false for flag only.
 * \param cmppar ture for parity check, false for no.
 */
void uart_set_sleepwalking(Uart *p_uart, uint8_t ul_low_value,
		bool cmpmode, bool cmppar, uint8_t ul_high_value)
{
	Assert(ul_low_value <= ul_high_value);

	uint32_t temp = 0;

	if (cmpmode) {
		temp |= UART_CMPR_CMPMODE_START_CONDITION;
	}

	if (cmppar) {
		temp |= UART_CMPR_CMPPAR;
	}

	temp |= UART_CMPR_VAL1(ul_low_value);

	temp |= UART_CMPR_VAL2(ul_high_value);

	p_uart->UART_CMPR= temp;
}

/**
 * \brief Enables/Disables write protection mode.
 *
 * \param p_uart Pointer to a UART instance.
 * \param flag ture for enable, false for disable.
 */
void uart_set_write_protection(Uart *p_uart, bool flag)
{
	if (flag) {
		p_uart->UART_WPMR = UART_WPMR_WPKEY_PASSWD | UART_WPMR_WPEN;
	} else {
		p_uart->UART_WPMR = UART_WPMR_WPKEY_PASSWD;
	}
}
#endif

//@}

/// @cond 0
/**INDENT-OFF**/
#ifdef __cplusplus
}
#endif
/**INDENT-ON**/
/// @endcond
