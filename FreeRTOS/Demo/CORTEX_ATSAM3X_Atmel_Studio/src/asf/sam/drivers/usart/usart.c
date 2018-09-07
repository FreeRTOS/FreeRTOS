/**
 * \file
 *
 * \brief Universal Synchronous Asynchronous Receiver Transmitter (USART) driver for SAM.
 *
 * Copyright (c) 2011-2012 Atmel Corporation. All rights reserved.
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
 
#include "usart.h"

/// @cond 0
/**INDENT-OFF**/
#ifdef __cplusplus
extern "C" {
#endif
/**INDENT-ON**/
/// @endcond

/**
 * \defgroup sam_drivers_usart_group Universal Synchronous Asynchronous Receiver Transmitter (USART)
 *
 * The Universal Synchronous Asynchronous Receiver Transceiver (USART) provides one full duplex 
 * universal synchronous asynchronous serial link. Data frame format is widely programmable
 * (data length, parity, number of stop bits) to support a maximum of standards. The receiver
 * implements parity error, framing error and overrun error detection. The receiver time-out enables
 * handling variable-length frames and the transmitter timeguard facilitates communications with
 * slow remote devices. Multidrop communications are also supported through address bit handling
 * in reception and transmission.
 * The driver supports the following modes: RS232, RS485, SPI, IrDA, ISO7816, MODEM,
 * Hardware handshaking and LIN.
 *
 * @{
 */

/* The write protect key value. */
#define US_WPKEY_VALUE                0x555341

/* The CD value scope programmed in MR register. */
#define MIN_CD_VALUE                  0x01
#define MIN_CD_VALUE_SPI              0x04
#define MAX_CD_VALUE                  US_BRGR_CD_Msk

/* Define the default time-out value for USART. */
#define USART_DEFAULT_TIMEOUT         1000

/* The receiver sampling divide of baudrate clock. */
#define HIGH_FRQ_SAMPLE_DIV           16
#define LOW_FRQ_SAMPLE_DIV            8

/* Max transmitter timeguard. */
#define MAX_TRAN_GUARD_TIME           US_TTGR_TG_Msk

/* The non-existent parity error number. */
#define USART_PARITY_ERROR            5

/* ISO7816 protocol type. */
#define ISO7816_T_0                   0
#define ISO7816_T_1                   1

/**
 * \brief Calculate a clock divider(CD) and a fractional part (FP) for the 
 * USART asynchronous modes to generate a baudrate as close as possible to 
 * the baudrate set point.
 *
 * \note Baud rate calculation: Baudrate = ul_mck/(Over * (CD + FP/8))
 * (Over being 16 or 8). The maximal oversampling is selected if it allows to 
 * generate a baudrate close to the set point.
 *
 * \param p_usart Pointer to a USART instance.
 * \param baudrate Baud rate set point.
 * \param ul_mck USART module input clock frequency.
 *
 * \retval 0 Baud rate is successfully initialized.
 * \retval 1 Baud rate set point is out of range for the given input clock 
 * frequency.
 */
static uint32_t usart_set_async_baudrate(Usart *p_usart,
		uint32_t baudrate, uint32_t ul_mck)
{
	uint32_t over;
	uint32_t cd_fp;
	uint32_t cd;
	uint32_t fp;

	/* Calculate the receiver sampling divide of baudrate clock. */
	if (ul_mck >= HIGH_FRQ_SAMPLE_DIV * baudrate) {
		over = HIGH_FRQ_SAMPLE_DIV;
	} else {
		over = LOW_FRQ_SAMPLE_DIV;
	}

	/* Calculate the clock divider according to the fraction calculated formula. */
	cd_fp = (8 * ul_mck + (over * baudrate) / 2) / (over * baudrate);
	cd = cd_fp >> 3;
	fp = cd_fp & 0x07;
	if (cd < MIN_CD_VALUE || cd > MAX_CD_VALUE) {
		return 1;
	}

	/* Configure the OVER bit in MR register. */
	if (over == 8) {
		p_usart->US_MR |= US_MR_OVER;
	}

	/* Configure the baudrate generate register. */
	p_usart->US_BRGR = (cd << US_BRGR_CD_Pos) | (fp << US_BRGR_FP_Pos);

	return 0;
}

/**
 * \brief Calculate a clock divider for the USART synchronous master modes
 * to generate a baudrate as close as possible to the baudrate set point.
 *
 * \note Synchronous baudrate calculation: baudrate = ul_mck / cd
 *
 * \param p_usart Pointer to a USART instance.
 * \param baudrate Baud rate set point.
 * \param ul_mck USART module input clock frequency.
 *
 * \retval 0 Baud rate is successfully initialized.
 * \retval 1 Baud rate set point is out of range for the given input clock 
 * frequency.
 */
static uint32_t usart_set_sync_master_baudrate(Usart *p_usart,
		uint32_t baudrate, uint32_t ul_mck)
{
	uint32_t cd;

	/* Calculate the clock divider according to the formula in synchronous mode. */
	cd = (ul_mck + baudrate / 2) / baudrate;

	if (cd < MIN_CD_VALUE || cd > MAX_CD_VALUE) {
		return 1;
	}

	/* Configure the baudrate generate register. */
	p_usart->US_BRGR = cd << US_BRGR_CD_Pos;

	p_usart->US_MR = (p_usart->US_MR & ~US_MR_USCLKS_Msk) |
			US_MR_USCLKS_MCK | US_MR_SYNC;
	return 0;
}

/**
 * \brief Select the SCK pin as the source of baud rate for the USART
 * synchronous slave modes.
 *
 * \param p_usart Pointer to a USART instance.
 */
static void usart_set_sync_slave_baudrate(Usart *p_usart)
{
	p_usart->US_MR = (p_usart->US_MR & ~US_MR_USCLKS_Msk) |
			US_MR_USCLKS_SCK | US_MR_SYNC;
}


/**
 * \brief Calculate a clock divider (\e CD) for the USART ISO7816 mode to 
 * generate an ISO7816 clock as close as possible to the clock set point.
 *
 * \note ISO7816 clock calculation: Clock = ul_mck / cd
 *
 * \param p_usart Pointer to a USART instance.
 * \param clock ISO7816 clock set point.
 * \param ul_mck USART module input clock frequency.
 *
 * \retval 0 ISO7816 clock is successfully initialized.
 * \retval 1 ISO7816 clock set point is out of range for the given input clock 
 * frequency.
 */
static uint32_t usart_set_iso7816_clock(Usart *p_usart,
		uint32_t clock, uint32_t ul_mck)
{
	uint32_t cd;

	/* Calculate the clock divider according to the formula in ISO7816 mode. */
	cd = (ul_mck + clock / 2) / clock;

	if (cd < MIN_CD_VALUE || cd > MAX_CD_VALUE) {
		return 1;
	}

	p_usart->US_MR = (p_usart->US_MR & ~(US_MR_USCLKS_Msk | US_MR_SYNC |
					US_MR_OVER)) | US_MR_USCLKS_MCK | US_MR_CLKO;

	/* Configure the baudrate generate register. */
	p_usart->US_BRGR = cd << US_BRGR_CD_Pos;

	return 0;
}

/**
 * \brief Calculate a clock divider (\e CD) for the USART SPI master mode to
 * generate a baud rate as close as possible to the baud rate set point.
 *
 * \note Baud rate calculation:
 * \f$ Baudrate = \frac{SelectedClock}{CD} \f$.
 *
 * \param p_usart Pointer to a USART instance.
 * \param baudrate Baud rate set point.
 * \param ul_mck USART module input clock frequency.
 *
 * \retval 0 Baud rate is successfully initialized.
 * \retval 1 Baud rate set point is out of range for the given input clock 
 * frequency.
 */
static uint32_t usart_set_spi_master_baudrate(Usart *p_usart,
		uint32_t baudrate, uint32_t ul_mck)
{
	uint32_t cd;

	/* Calculate the clock divider according to the formula in SPI mode. */
	cd = (ul_mck + baudrate / 2) / baudrate;

	if (cd < MIN_CD_VALUE_SPI || cd > MAX_CD_VALUE) {
		return 1;
	}

	p_usart->US_BRGR = cd << US_BRGR_CD_Pos;

	return 0;
}

/**
 * \brief Select the SCK pin as the source of baudrate for the USART SPI slave 
 * mode.
 *
 * \param p_usart Pointer to a USART instance.
 */
static void usart_set_spi_slave_baudrate(Usart *p_usart)
{
	p_usart->US_MR &= ~US_MR_USCLKS_Msk;
	p_usart->US_MR |= US_MR_USCLKS_SCK;
}

/**
 * \brief Reset the USART and disable TX and RX.
 *
 * \param p_usart Pointer to a USART instance.
 */
void usart_reset(Usart *p_usart)
{
	/* Disable the Write Protect. Some register can't be written if the write protect is enabled. */
	usart_disable_writeprotect(p_usart);

	/* Reset mode and other registers that could cause unpredictable behavior after reset. */
	p_usart->US_MR = 0;
	p_usart->US_RTOR = 0;
	p_usart->US_TTGR = 0;

	/* Disable TX and RX, reset status bits and turn off RTS and DTR if exist. */
	usart_reset_tx(p_usart);
	usart_reset_rx(p_usart);
	usart_reset_status(p_usart);
	usart_drive_RTS_pin_high(p_usart);
#if (SAM3S || SAM4S || SAM3U)
	usart_drive_DTR_pin_high(p_usart);
#endif
}

/**
 * \brief Configure USART to work in RS232 mode.
 *
 * \note By default, the transmitter and receiver aren't enabled.
 *
 * \param p_usart Pointer to a USART instance.
 * \param p_usart_opt Pointer to sam_usart_opt_t instance.
 * \param ul_mck USART module input clock frequency.
 *
 * \retval 0 on success.
 * \retval 1 on failure.
 */
uint32_t usart_init_rs232(Usart *p_usart,
		const sam_usart_opt_t *p_usart_opt, uint32_t ul_mck)
{
	static uint32_t ul_reg_val;

	/* Reset the USART and shut down TX and RX. */
	usart_reset(p_usart);

	ul_reg_val = 0;
	/* Check whether the input values are legal. */
	if (!p_usart_opt ||
		usart_set_async_baudrate(p_usart, p_usart_opt->baudrate, ul_mck)) {
		return 1;
	}

	/* Configure the character length, parity type, channel mode and stop bit length. */
	ul_reg_val |= p_usart_opt->char_length | p_usart_opt->parity_type |
				p_usart_opt->channel_mode | p_usart_opt->stop_bits;
	
	/* Configure the USART mode as normal mode. */
	ul_reg_val |= US_MR_USART_MODE_NORMAL;
	
	p_usart->US_MR |= ul_reg_val;
	
	return 0;
}

/**
 * \brief Configure USART to work in hardware handshaking mode.
 *
 * \note By default, the transmitter and receiver aren't enabled.
 *
 * \param p_usart Pointer to a USART instance.
 * \param p_usart_opt Pointer to sam_usart_opt_t instance.
 * \param ul_mck USART module input clock frequency.
 *
 * \retval 0 on success.
 * \retval 1 on failure.
 */
uint32_t usart_init_hw_handshaking(Usart *p_usart,
		const sam_usart_opt_t *p_usart_opt, uint32_t ul_mck)
{
	/* Initialize the USART as standard RS232. */
	if (usart_init_rs232(p_usart, p_usart_opt, ul_mck)) {
		return 1;
	}

	/* Set hardware handshaking mode. */
	p_usart->US_MR = (p_usart->US_MR & ~US_MR_USART_MODE_Msk) |
			US_MR_USART_MODE_HW_HANDSHAKING;

	return 0;
}

#if (SAM3S || SAM4S || SAM3U)
/**
 * \brief Configure USART to work in modem mode.
 *
 * \note By default, the transmitter and receiver aren't enabled.
 *
 * \param p_usart Pointer to a USART instance.
 * \param p_usart_opt Pointer to sam_usart_opt_t instance.
 * \param ul_mck USART module input clock frequency.
 *
 * \retval 0 on success.
 * \retval 1 on failure.
 */
uint32_t usart_init_modem(Usart *p_usart,
		const sam_usart_opt_t *p_usart_opt, uint32_t ul_mck)
{
	/* SAM3S || SAM4S series support MODEM mode only on USART1, and 
	   SAM3U series support MODEM mode only on USART0. */
#if (SAM3S || SAM4S)
	if (p_usart != USART1) {
		return 1;
	}
#elif (SAM3U)
	if (p_usart != USART0) {
		return 1;
	}
#endif

	/* Initialize the USART as standard RS232. */
	if (usart_init_rs232(p_usart, p_usart_opt, ul_mck)) {
		return 1;
	}
	
	/* Set MODEM mode. */
	p_usart->US_MR = (p_usart->US_MR & ~US_MR_USART_MODE_Msk) |
			US_MR_USART_MODE_MODEM;

	return 0;
}
#endif

/**
 * \brief Configure USART to work in SYNC mode and act as a master.
 *
 * \note By default, the transmitter and receiver aren't enabled.
 *
 * \param p_usart Pointer to a USART instance.
 * \param p_usart_opt Pointer to sam_usart_opt_t instance.
 * \param ul_mck USART module input clock frequency.
 *
 * \retval 0 on success.
 * \retval 1 on failure.
 */
uint32_t usart_init_sync_master(Usart *p_usart,
		const sam_usart_opt_t *p_usart_opt, uint32_t ul_mck)
{
	static uint32_t ul_reg_val;

	/* Reset the USART and shut down TX and RX. */
	usart_reset(p_usart);

	ul_reg_val = 0;
	/* Check whether the input values are legal. */
	if (!p_usart_opt ||
		usart_set_sync_master_baudrate(p_usart, p_usart_opt->baudrate, ul_mck)) {
		return 1;
	}

	/* Configure the character length, parity type, channel mode and stop bit length. */
	ul_reg_val |= p_usart_opt->char_length | p_usart_opt->parity_type |
				p_usart_opt->channel_mode | p_usart_opt->stop_bits;
	
	/* Set normal mode and output clock on the SCK pin as synchronous master. */
	ul_reg_val |= US_MR_USART_MODE_NORMAL | US_MR_CLKO;
	p_usart->US_MR |= ul_reg_val;

	return 0;
}

/**
 * \brief Configure USART to work in SYNC mode and act as a slave.
 *
 * \note By default, the transmitter and receiver aren't enabled.
 *
 * \param p_usart Pointer to a USART instance.
 * \param p_usart_opt Pointer to sam_usart_opt_t instance.
 *
 * \retval 0 on success.
 * \retval 1 on failure.
 */
uint32_t usart_init_sync_slave(Usart *p_usart,
		const sam_usart_opt_t *p_usart_opt)
{
	static uint32_t ul_reg_val;
	
	/* Reset the USART and shut down TX and RX. */
	usart_reset(p_usart);
	
	ul_reg_val = 0;
	usart_set_sync_slave_baudrate(p_usart);
	
	/* Check whether the input values are legal. */
	if (!p_usart_opt) {
		return 1;
	}

	/* Configure the character length, parity type, channel mode and stop bit length. */
	ul_reg_val |= p_usart_opt->char_length | p_usart_opt->parity_type |
			p_usart_opt->channel_mode | p_usart_opt->stop_bits;

	/* Set normal mode. */
	ul_reg_val |= US_MR_USART_MODE_NORMAL;
	p_usart->US_MR |= ul_reg_val;	

	return 0;
}

/**
 * \brief Configure USART to work in RS485 mode.
 *
 * \note By default, the transmitter and receiver aren't enabled.
 *
 * \param p_usart Pointer to a USART instance.
 * \param p_usart_opt Pointer to sam_usart_opt_t instance.
 * \param ul_mck USART module input clock frequency.
 *
 * \retval 0 on success.
 * \retval 1 on failure.
 */
uint32_t usart_init_rs485(Usart *p_usart,
		const sam_usart_opt_t *p_usart_opt, uint32_t ul_mck)
{
	/* Initialize the USART as standard RS232. */
	if (usart_init_rs232(p_usart, p_usart_opt, ul_mck)) {
		return 1;
	}

	/* Set RS485 mode. */
	p_usart->US_MR = (p_usart->US_MR & ~US_MR_USART_MODE_Msk) |
			US_MR_USART_MODE_RS485;

	return 0;
}

/**
 * \brief Configure USART to work in IrDA mode.
 *
 * \note By default, the transmitter and receiver aren't enabled.
 *
 * \param p_usart Pointer to a USART instance.
 * \param p_usart_opt Pointer to sam_usart_opt_t instance.
 * \param ul_mck USART module input clock frequency.
 *
 * \retval 0 on success.
 * \retval 1 on failure.
 */
uint32_t usart_init_irda(Usart *p_usart,
		const sam_usart_opt_t *p_usart_opt, uint32_t ul_mck)
{
	/* Initialize the USART as standard RS232. */
	if (usart_init_rs232(p_usart, p_usart_opt, ul_mck)) {
		return 1;
	}

	/* Set IrDA filter. */
	p_usart->US_IF = p_usart_opt->irda_filter;

	/* Set IrDA mode. */
	p_usart->US_MR = (p_usart->US_MR & ~US_MR_USART_MODE_Msk) |
			US_MR_USART_MODE_IRDA;

	return 0;
}

/**
 * \brief Configure USART to work in ISO7816 mode.
 *
 * \note By default, the transmitter and receiver aren't enabled.
 *
 * \param p_usart Pointer to a USART instance.
 * \param p_usart_opt Pointer to sam_usart_opt_t instance.
 * \param ul_mck USART module input clock frequency.
 *
 * \retval 0 on success.
 * \retval 1 on failure.
 */
uint32_t usart_init_iso7816(Usart *p_usart,
		const usart_iso7816_opt_t *p_usart_opt, uint32_t ul_mck)
{
	static uint32_t ul_reg_val;
	
	/* Reset the USART and shut down TX and RX. */
	usart_reset(p_usart);
	
	ul_reg_val = 0;
	
	/* Check whether the input values are legal. */
	if (!p_usart_opt || ((p_usart_opt->parity_type != US_MR_PAR_EVEN) &&
		(p_usart_opt->parity_type != US_MR_PAR_ODD))) {
		return 1;
	}
	
	if (p_usart_opt->protocol_type == ISO7816_T_0) {
		ul_reg_val |= US_MR_USART_MODE_IS07816_T_0 | US_MR_NBSTOP_2_BIT |
				(p_usart_opt->max_iterations << US_MR_MAX_ITERATION_Pos);

		if (p_usart_opt->bit_order) {
			ul_reg_val |= US_MR_MSBF;
		}
	} else if (p_usart_opt->protocol_type == ISO7816_T_1) {
		/* Only LSBF is used in the T=1 protocol, and max_iterations field is only used in T=0 mode.*/
		if (p_usart_opt->bit_order || p_usart_opt->max_iterations) {
			return 1;
		}
		
		/* Set USART mode to ISO7816, T=1, and always uses 1 stop bit. */
		ul_reg_val |= US_MR_USART_MODE_IS07816_T_1 | US_MR_NBSTOP_1_BIT;
	} else {
		return 1;
	}

	/* Set up the baudrate. */
	if (usart_set_iso7816_clock(p_usart, p_usart_opt->iso7816_hz, ul_mck)) {
		return 1;
	}

	/* Set FIDI register: bit rate = iso7816_hz / fidi_ratio. */
	p_usart->US_FIDI = p_usart_opt->fidi_ratio;

	/* Set ISO7816 parity type in the MODE register. */
	ul_reg_val |= p_usart_opt->parity_type;
	
	if (p_usart_opt->inhibit_nack) {
		ul_reg_val |= US_MR_INACK;
	}
	if (p_usart_opt->dis_suc_nack) {
		ul_reg_val |= US_MR_DSNACK;
	}
	
	p_usart->US_MR |= ul_reg_val;

	return 0;
}

/**
 * \brief Configure USART to work in SPI mode and act as a master.
 *
 * \note By default, the transmitter and receiver aren't enabled.
 *
 * \param p_usart Pointer to a USART instance.
 * \param p_usart_opt Pointer to sam_usart_opt_t instance.
 * \param ul_mck USART module input clock frequency.
 *
 * \retval 0 on success.
 * \retval 1 on failure.
 */
uint32_t usart_init_spi_master(Usart *p_usart,
		const usart_spi_opt_t *p_usart_opt, uint32_t ul_mck)
{
	static uint32_t ul_reg_val;
	
	/* Reset the USART and shut down TX and RX. */
	usart_reset(p_usart);
	
	ul_reg_val = 0;
	/* Check whether the input values are legal. */
	if (!p_usart_opt ||
		(p_usart_opt->spi_mode > SPI_MODE_3) ||
		usart_set_spi_master_baudrate(p_usart, p_usart_opt->baudrate, ul_mck)) {
		return 1;
	}

	/* Configure the character length bit in MR register. */
	ul_reg_val |= p_usart_opt->char_length;
	
	/* Set SPI master mode and channel mode. */
	ul_reg_val |= US_MR_USART_MODE_SPI_MASTER | US_MR_CLKO |
				p_usart_opt->channel_mode;
					
	switch (p_usart_opt->spi_mode) {
	case SPI_MODE_0:
		ul_reg_val |= US_MR_CPHA;
		ul_reg_val &= ~US_MR_CPOL;
		break;
	case SPI_MODE_1:
		ul_reg_val &= ~US_MR_CPHA;
		ul_reg_val &= ~US_MR_CPOL;
		break;
	case SPI_MODE_2:
		ul_reg_val |= US_MR_CPHA;
		ul_reg_val |= US_MR_CPOL;
		break;
	case SPI_MODE_3:
		ul_reg_val |= US_MR_CPOL;
		ul_reg_val &= ~US_MR_CPHA;
		break;
	default:
		break;
	}
	
	p_usart->US_MR |= ul_reg_val;

	return 0;
}

/**
 * \brief Configure USART to work in SPI mode and act as a slave.
 *
 * \note By default, the transmitter and receiver aren't enabled.
 *
 * \param p_usart Pointer to a USART instance.
 * \param p_usart_opt Pointer to sam_usart_opt_t instance.
 *
 * \retval 0 on success.
 * \retval 1 on failure.
 */
uint32_t usart_init_spi_slave(Usart *p_usart,
		const usart_spi_opt_t *p_usart_opt)
{
	static uint32_t ul_reg_val;

	/* Reset the USART and shut down TX and RX. */
	usart_reset(p_usart);
	
	ul_reg_val = 0;
	usart_set_spi_slave_baudrate(p_usart);
	
	/* Check whether the input values are legal. */
	if (!p_usart_opt ||
		p_usart_opt->spi_mode > SPI_MODE_3) {
		return 1;
	}

	/* Configure the character length bit in MR register. */
	ul_reg_val |= p_usart_opt->char_length;
	
	/* Set SPI slave mode and channel mode. */
	ul_reg_val |= US_MR_USART_MODE_SPI_SLAVE | p_usart_opt->channel_mode;
					
	switch (p_usart_opt->spi_mode) {
	case SPI_MODE_0:
		ul_reg_val |= US_MR_CPHA;
		ul_reg_val &= ~US_MR_CPOL;
		break;
	case SPI_MODE_1:
		ul_reg_val &= ~US_MR_CPHA;
		ul_reg_val &= ~US_MR_CPOL;
		break;
	case SPI_MODE_2:
		ul_reg_val |= US_MR_CPHA;
		ul_reg_val |= US_MR_CPOL;
		break;
	case SPI_MODE_3:
		ul_reg_val |= US_MR_CPOL;
		ul_reg_val &= ~US_MR_CPHA;
		break;
	default:
		break;
	}

	p_usart->US_MR |= ul_reg_val;

	return 0;
}

#if SAM3XA
/**
 * \brief Configure USART to work in LIN mode and act as a LIN master.
 *
 * \note By default, the transmitter and receiver aren't enabled.
 *
 * \param p_usart Pointer to a USART instance.
 * \param p_usart_opt Pointer to sam_usart_opt_t instance.
 * \param ul_mck USART module input clock frequency.
 *
 * \retval 0 on success.
 * \retval 1 on failure.
 */
uint32_t usart_init_lin_master(Usart *p_usart,
		const sam_usart_opt_t *p_usart_opt, uint32_t ul_mck)
{
	/* Reset the USART and shut down TX and RX. */
	usart_reset(p_usart);

	/* Set up the baudrate. */
	if (usart_set_async_baudrate(p_usart, p_usart_opt->baudrate, ul_mck)) {
		return 1;
	}
	
	/* Set LIN master mode. */
	p_usart->US_MR = (p_usart->US_MR & ~US_MR_USART_MODE_Msk) |
					US_MR_USART_MODE_LIN_MASTER;	

	return 0;
}

/**
 * \brief Configure USART to work in LIN mode and act as a LIN slave.
 *
 * \note By default, the transmitter and receiver aren't enabled.
 *
 * \param p_usart Pointer to a USART instance.
 * \param p_usart_opt Pointer to sam_usart_opt_t instance.
 * \param ul_mck USART module input clock frequency.
 *
 * \retval 0 on success.
 * \retval 1 on failure.
 */
uint32_t usart_init_lin_slave(Usart *p_usart,
		const sam_usart_opt_t *p_usart_opt, uint32_t ul_mck)
{
	/* Reset the USART and shut down TX and RX. */
	usart_reset(p_usart);

	/* Set up the baudrate. */
	if (usart_set_async_baudrate(p_usart, p_usart_opt->baudrate, ul_mck)) {
		return 1;
	}
	
	/* Set LIN slave mode. */
	p_usart->US_MR = (p_usart->US_MR & ~US_MR_USART_MODE_Msk) |
					US_MR_USART_MODE_LIN_SLAVE;

	return 0;
}

/**
 * \brief Abort the current LIN transmission.
 *
 * \param p_usart Pointer to a USART instance.
 */
void usart_lin_abort_tx(Usart *p_usart)
{
	p_usart->US_CR = US_CR_LINABT;
}

/**
 * \brief Send a wakeup signal on the LIN bus.
 *
 * \param p_usart Pointer to a USART instance.
 */
void usart_lin_send_wakeup_signal(Usart *p_usart)
{
	p_usart->US_CR = US_CR_LINWKUP;
}

/**
 * \brief Configure the LIN node action, which should be one of PUBLISH,
 * SUBSCRIBE or IGNORE.
 *
 * \param p_usart Pointer to a USART instance.
 * \param uc_action 0 for PUBLISH, 1 for SUBSCRIBE, 2 for IGNORE.
 */
void usart_lin_set_node_action(Usart *p_usart, uint8_t uc_action)
{
	p_usart->US_LINMR = (p_usart->US_LINMR & ~US_LINMR_NACT_Msk) |
					(uc_action << US_LINMR_NACT_Pos);
}

/**
 * \brief Disable the parity check during the LIN communication.
 *
 * \param p_usart Pointer to a USART instance.
 */
void usart_lin_disable_parity(Usart *p_usart)
{
	p_usart->US_LINMR |= US_LINMR_PARDIS;
}

/**
 * \brief Enable the parity check during the LIN communication.
 *
 * \param p_usart Pointer to a USART instance.
 */
void usart_lin_enable_parity(Usart *p_usart)
{
	p_usart->US_LINMR &= ~US_LINMR_PARDIS;
}

/**
 * \brief Disable the checksum during the LIN communication.
 *
 * \param p_usart Pointer to a USART instance.
 */
void usart_lin_disable_checksum(Usart *p_usart)
{
	p_usart->US_LINMR |= US_LINMR_CHKDIS;
}

/**
 * \brief Enable the checksum during the LIN communication.
 *
 * \param p_usart Pointer to a USART instance.
 */
void usart_lin_enable_checksum(Usart *p_usart)
{
	p_usart->US_LINMR &= ~US_LINMR_CHKDIS;
}

/**
 * \brief Configure the checksum type during the LIN communication.
 *
 * \param p_usart Pointer to a USART instance.
 * \param uc_type 0 for LIN 2.0 Enhanced checksum or 1 for LIN 1.3 Classic checksum.
 */
void usart_lin_set_checksum_type(Usart *p_usart, uint8_t uc_type)
{
	p_usart->US_LINMR = (p_usart->US_LINMR & ~US_LINMR_CHKTYP) |
			(uc_type << 4);
}

/**
 * \brief Configure the data length mode during the LIN communication.
 *
 * \param p_usart Pointer to a USART instance.
 * \param uc_mode Indicate the checksum type: 0 if the data length is defined by the 
 * DLC of LIN mode register or 1 if the data length is defined by the bit 5 and 6 of 
 * the identifier.
 */
void usart_lin_set_data_len_mode(Usart *p_usart, uint8_t uc_mode)
{
	p_usart->US_LINMR = (p_usart->US_LINMR & ~US_LINMR_DLM) |
			(uc_mode << 5);
}

/**
 * \brief Disable the frame slot mode during the LIN communication.
 *
 * \param p_usart Pointer to a USART instance.
 */
void usart_lin_disable_frame_slot(Usart *p_usart)
{
	p_usart->US_LINMR |= US_LINMR_FSDIS;
}

/**
 * \brief Enable the frame slot mode during the LIN communication.
 *
 * \param p_usart Pointer to a USART instance.
 */
void usart_lin_enable_frame_slot(Usart *p_usart)
{
	p_usart->US_LINMR &= ~US_LINMR_FSDIS;
}

/**
 * \brief Configure the wakeup signal type during the LIN communication.
 *
 * \param p_usart Pointer to a USART instance.
 * \param uc_type Indicate the checksum type: 0 if the wakeup signal is a LIN 2.0 
 * wakeup signal; 1 if the wakeup signal is a LIN 1.3 wakeup signal.
 */
void usart_lin_set_wakeup_signal_type(Usart *p_usart, uint8_t uc_type)
{
	p_usart->US_LINMR = (p_usart->US_LINMR & ~US_LINMR_WKUPTYP) |
					(uc_type << 7);
}

/**
 * \brief Configure the response data length if the data length is defined by
 * the DLC field during the LIN communication.
 *
 * \param p_usart Pointer to a USART instance.
 * \param uc_len Indicate the response data length.
 */
void usart_lin_set_response_data_len(Usart *p_usart, uint8_t uc_len)
{
	p_usart->US_LINMR = (p_usart->US_LINMR & ~US_LINMR_DLC_Msk) |
			(uc_len << US_LINMR_DLC_Pos);
}

/**
 * \brief The LIN mode register is not written by the PDC.
 *
 * \param p_usart Pointer to a USART instance.
 */
void usart_lin_disable_pdc_mode(Usart *p_usart)
{
	p_usart->US_LINMR &= ~US_LINMR_PDCM;
}

/**
 * \brief The LIN mode register (except this flag) is written by the PDC.
 *
 * \param p_usart Pointer to a USART instance.
 */
void usart_lin_enable_pdc_mode(Usart *p_usart)
{
	p_usart->US_LINMR |= US_LINMR_PDCM;
}

/**
 * \brief Configure the LIN identifier when USART works in LIN master mode.
 *
 * \param p_usart Pointer to a USART instance.
 * \param uc_id The identifier to be transmitted.
 */
void usart_lin_set_tx_identifier(Usart *p_usart, uint8_t uc_id)
{
	p_usart->US_LINIR = (p_usart->US_LINIR & ~US_LINIR_IDCHR_Msk) |
			US_LINIR_IDCHR(uc_id);
}

/**
 * \brief Read the identifier when USART works in LIN mode.
 *
 * \param p_usart Pointer to a USART instance.
 *
 * \return The last identifier received in LIN slave mode or the last identifier 
 * transmitted in LIN master mode. 
 */
uint8_t usart_lin_read_identifier(Usart *p_usart)
{
	return (p_usart->US_LINMR & US_LINIR_IDCHR_Msk);
}
#endif

/**
 * \brief Enable USART transmitter.
 *
 * \param p_usart Pointer to a USART instance.
 */
void usart_enable_tx(Usart *p_usart)
{
	p_usart->US_CR = US_CR_TXEN;
}

/**
 * \brief Disable USART transmitter.
 *
 * \param p_usart Pointer to a USART instance.
 */
void usart_disable_tx(Usart *p_usart)
{
	p_usart->US_CR = US_CR_TXDIS;
}

/**
 * \brief Immediately stop and disable USART transmitter.
 *
 * \param p_usart Pointer to a USART instance.
 */
void usart_reset_tx(Usart *p_usart)
{
	/* Reset transmitter */
	p_usart->US_CR = US_CR_RSTTX | US_CR_TXDIS;
}

/**
 * \brief Configure the transmit timeguard register.
 *
 * \param p_usart Pointer to a USART instance.
 * \param timeguard The value of transmit timeguard.
 */
void usart_set_tx_timeguard(Usart *p_usart, uint32_t timeguard)
{
	p_usart->US_TTGR = timeguard;
}

/**
 * \brief Enable USART receiver.
 *
 * \param p_usart Pointer to a USART instance.
 */
void usart_enable_rx(Usart *p_usart)
{
	p_usart->US_CR = US_CR_RXEN;
}

/**
 * \brief Disable USART receiver.
 *
 * \param p_usart Pointer to a USART instance.
 */
void usart_disable_rx(Usart *p_usart)
{
	p_usart->US_CR = US_CR_RXDIS;
}

/**
 * \brief Immediately stop and disable USART receiver.
 *
 * \param p_usart Pointer to a USART instance.
 */
void usart_reset_rx(Usart *p_usart)
{
	/* Reset Receiver */
	p_usart->US_CR = US_CR_RSTRX | US_CR_RXDIS;
}

/**
 * \brief Configure the receive timeout register.
 *
 * \param p_usart Pointer to a USART instance.
 * \param timeout The value of receive timeout.
 */
void usart_set_rx_timeout(Usart *p_usart, uint32_t timeout)
{
	p_usart->US_RTOR = timeout;
}

/**
 * \brief Enable USART interrupts.
 *
 * \param p_usart Pointer to a USART peripheral.
 * \param ul_sources Interrupt sources bit map.
 */
void usart_enable_interrupt(Usart *p_usart, uint32_t ul_sources)
{
	p_usart->US_IER = ul_sources;
}

/**
 * \brief Disable USART interrupts.
 *
 * \param p_usart Pointer to a USART peripheral.
 * \param ul_sources Interrupt sources bit map.
 */
void usart_disable_interrupt(Usart *p_usart, uint32_t ul_sources)
{
	p_usart->US_IDR = ul_sources;
}

/**
 * \brief Read USART interrupt mask.
 *
 * \param p_usart Pointer to a USART peripheral.
 *
 * \return The interrupt mask value.
 */
uint32_t usart_get_interrupt_mask(Usart *p_usart)
{
	return p_usart->US_IMR;
}

/**
 * \brief Get current status.
 *
 * \param p_usart Pointer to a USART instance.
 *
 * \return The current USART status.
 */
uint32_t usart_get_status(Usart *p_usart)
{
	return p_usart->US_CSR;
}

/**
 * \brief Reset status bits (PARE, OVER, MANERR, UNRE and PXBRK in US_CSR).
 *
 * \param p_usart Pointer to a USART instance.
 */
void usart_reset_status(Usart *p_usart)
{
	p_usart->US_CR = US_CR_RSTSTA;
}

/**
 * \brief Start transmission of a break.
 *
 * \param p_usart Pointer to a USART instance.
 */
void usart_start_tx_break(Usart *p_usart)
{
	p_usart->US_CR = US_CR_STTBRK;
}

/**
 * \brief Stop transmission of a break.
 *
 * \param p_usart Pointer to a USART instance.
 */
void usart_stop_tx_break(Usart *p_usart)
{
	p_usart->US_CR = US_CR_STPBRK;
}

/**
 * \brief Start waiting for a character before clocking the timeout count.
 * Reset the status bit TIMEOUT in US_CSR. 
 *
 * \param p_usart Pointer to a USART instance.
 */
void usart_start_rx_timeout(Usart *p_usart)
{
	p_usart->US_CR = US_CR_STTTO;
}

/**
 * \brief In Multidrop mode only, the next character written to the US_THR
 * is sent with the address bit set. 
 *
 * \param p_usart Pointer to a USART instance.
 * \param ul_addr The address to be sent out.
 *
 * \retval 0 on success.
 * \retval 1 on failure.
 */
uint32_t usart_send_address(Usart *p_usart, uint32_t ul_addr)
{
	if ((p_usart->US_MR & US_MR_PAR_MULTIDROP) != US_MR_PAR_MULTIDROP) {
		return 1;
	}
	
	p_usart->US_CR = US_CR_SENDA;
	
	if (usart_write(p_usart, ul_addr)) {
		return 1;
	} else {
		return 0;
	}
}

/**
 * \brief Reset the ITERATION in US_CSR when the ISO7816 mode is enabled.
 *
 * \param p_usart Pointer to a USART instance.
 */
void usart_reset_iterations(Usart *p_usart)
{
	p_usart->US_CR = US_CR_RSTIT;
}

/**
 * \brief Reset NACK in US_CSR.
 *
 * \param p_usart Pointer to a USART instance.
 */
void usart_reset_nack(Usart *p_usart)
{
	p_usart->US_CR = US_CR_RSTNACK;
}

/**
 * \brief Restart the receive timeout.
 *
 * \param p_usart Pointer to a USART instance.
 */
void usart_restart_rx_timeout(Usart *p_usart)
{
	p_usart->US_CR = US_CR_RETTO;
}

#if (SAM3S || SAM4S || SAM3U)
/**
 * \brief Drive the pin DTR to 0.
 *
 * \param p_usart Pointer to a USART instance.
 */
void usart_drive_DTR_pin_low(Usart *p_usart)
{
	p_usart->US_CR = US_CR_DTREN;
}

/**
 * \brief Drive the pin DTR to 1.
 *
 * \param p_usart Pointer to a USART instance.
 */
void usart_drive_DTR_pin_high(Usart *p_usart)
{
	p_usart->US_CR = US_CR_DTRDIS;
}
#endif

/**
 * \brief Drive the pin RTS to 0.
 *
 * \param p_usart Pointer to a USART instance.
 */
void usart_drive_RTS_pin_low(Usart *p_usart)
{
	p_usart->US_CR = US_CR_RTSEN;
}

/**
 * \brief Drive the pin RTS to 1.
 *
 * \param p_usart Pointer to a USART instance.
 */
void usart_drive_RTS_pin_high(Usart *p_usart)
{
	p_usart->US_CR = US_CR_RTSDIS;
}

/**
 * \brief Drive the slave select line NSS (RTS pin) to 0 in SPI master mode.
 *
 * \param p_usart Pointer to a USART instance.
 */
void usart_spi_force_chip_select(Usart *p_usart)
{
	p_usart->US_CR = US_CR_FCS;
}

/**
 * \brief Drive the slave select line NSS (RTS pin) to 1 in SPI master mode.
 *
 * \param p_usart Pointer to a USART instance.
 */
void usart_spi_release_chip_select(Usart *p_usart)
{
	p_usart->US_CR = US_CR_RCS;
}

/**
 * \brief Check if Transmit is Ready.
 * Check if data have been loaded in USART_THR and are waiting to be loaded 
 * into the Transmit Shift Register (TSR).
 *
 * \param p_usart Pointer to a USART instance.
 *
 * \retval 1 No data is in the Transmit Holding Register.
 * \retval 0 There is data in the Transmit Holding Register.
 */
uint32_t usart_is_tx_ready(Usart *p_usart)
{
	return (p_usart->US_CSR & US_CSR_TXRDY) > 0;
}

/**
 * \brief Check if Transmit Holding Register is empty.
 * Check if the last data written in USART_THR have been loaded in TSR and the last
 * data loaded in TSR have been transmitted.
 *
 * \param p_usart Pointer to a USART instance.
 *
 * \retval 1 Transmitter is empty.
 * \retval 0 Transmitter is not empty.
 */
uint32_t usart_is_tx_empty(Usart *p_usart)
{
	return (p_usart->US_CSR & US_CSR_TXEMPTY) > 0;
}

/**
 * \brief Check if the received data are ready.
 * Check if Data have been received and loaded into USART_RHR.
 *
 * \param p_usart Pointer to a USART instance.
 *
 * \retval 1 Some data has been received.
 * \retval 0 No data has been received.
 */
uint32_t usart_is_rx_ready(Usart *p_usart)
{
	return (p_usart->US_CSR & US_CSR_RXRDY) > 0;
}

/**
 * \brief Check if one receive buffer is filled.
 *
 * \param p_usart Pointer to a USART instance.
 *
 * \retval 1 Receive is complete.
 * \retval 0 Receive is still pending.
 */
uint32_t usart_is_rx_buf_end(Usart *p_usart)
{
	return (p_usart->US_CSR & US_CSR_ENDRX) > 0;
}

/**
 * \brief Check if one transmit buffer is empty.
 *
 * \param p_usart Pointer to a USART instance.
 *
 * \retval 1 Transmit is complete.
 * \retval 0 Transmit is still pending.
 */
uint32_t usart_is_tx_buf_end(Usart *p_usart)
{
	return (p_usart->US_CSR & US_CSR_ENDTX) > 0;
}

/**
 * \brief Check if both receive buffers are full.
 *
 * \param p_usart Pointer to a USART instance.
 *
 * \retval 1 Receive buffers are full.
 * \retval 0 Receive buffers are not full.
 */
uint32_t usart_is_rx_buf_full(Usart *p_usart)
{
	return (p_usart->US_CSR & US_CSR_RXBUFF) > 0;
}

/**
 * \brief Check if both transmit buffers are empty.
 *
 * \param p_usart Pointer to a USART instance.
 *
 * \retval 1 Transmit buffers are empty.
 * \retval 0 Transmit buffers are not empty.
 */
uint32_t usart_is_tx_buf_empty(Usart *p_usart)
{
	return (p_usart->US_CSR & US_CSR_TXBUFE) > 0;
}

/**
 * \brief Write to USART Transmit Holding Register.
 *
 * \note Before writing user should check if tx is ready (or empty).
 *
 * \param p_usart Pointer to a USART instance.
 * \param c Data to be sent.
 *
 * \retval 0 on success.
 * \retval 1 on failure.
 */
uint32_t usart_write(Usart *p_usart, uint32_t c)
{
	if (!(p_usart->US_CSR & US_CSR_TXRDY)) {
		return 1;
	}

	p_usart->US_THR = US_THR_TXCHR(c);
	return 0;
}

/**
 * \brief Write to USART Transmit Holding Register.
 *
 * \note Before writing user should check if tx is ready (or empty).
 *
 * \param p_usart Pointer to a USART instance.
 * \param c Data to be sent.
 *
 * \retval 0 on success.
 * \retval 1 on failure.
 */
uint32_t usart_putchar(Usart *p_usart, uint32_t c)
{
	uint32_t timeout = USART_DEFAULT_TIMEOUT;

	while (!(p_usart->US_CSR & US_CSR_TXRDY)) {
		if (!timeout--) {
			return 1;
		}
	}

	p_usart->US_THR = US_THR_TXCHR(c);

	return 0;
}

/**
 * \brief Write one-line string through USART.
 *
 * \param p_usart Pointer to a USART instance.
 * \param string Pointer to one-line string to be sent.
 */
void usart_write_line(Usart *p_usart, const char *string)
{
	while (*string != '\0') {
		usart_putchar(p_usart, *string++);
	}
}

/**
 * \brief Read from USART Receive Holding Register.
 *
 * \note Before reading user should check if rx is ready.
 *
 * \param p_usart Pointer to a USART instance.
 * \param c Pointer where the one-byte received data will be stored.
 *
 * \retval 0 on success.
 * \retval 1 if no data is available or errors.
 */
uint32_t usart_read(Usart *p_usart, uint32_t *c)
{
	if (!(p_usart->US_CSR & US_CSR_RXRDY)) {
		return 1;
	}
	
	/* Read character */
	*c = p_usart->US_RHR & US_RHR_RXCHR_Msk;
	
	return 0;
}

/**
 * \brief Read from USART Receive Holding Register.
 * Before reading user should check if rx is ready.
 *
 * \param p_usart Pointer to a USART instance.
 * \param c Pointer where the one-byte received data will be stored.
 *
 * \retval 0 Data has been received.
 * \retval 1 on failure.
 */
uint32_t usart_getchar(Usart *p_usart, uint32_t *c)
{
	uint32_t timeout = USART_DEFAULT_TIMEOUT;

	/* If the receiver is empty, wait until it's not empty or timeout has reached. */
	while (!(p_usart->US_CSR & US_CSR_RXRDY)) {
		if (!timeout--) {
			return 1;
		}
	}

	/* Read character */
	*c = p_usart->US_RHR & US_RHR_RXCHR_Msk;

	return 0;
}

#if (SAM3XA || SAM3U)
/**
 * \brief Get Transmit address for DMA operation.
 *
 * \param p_usart Pointer to a USART instance.
 *
 * \return Transmit address for DMA access.
 */
uint32_t *usart_get_tx_access(Usart *p_usart)
{
	return (uint32_t *)&(p_usart->US_THR);
}

/**
 * \brief Get Receive address for DMA operation.
 *
 * \param p_usart Pointer to a USART instance.
 *
 * \return Receive address for DMA access.
 */
uint32_t *usart_get_rx_access(Usart *p_usart)
{
	return (uint32_t *)&(p_usart->US_RHR);
}
#endif

/**
 * \brief Get USART PDC base address.
 *
 * \param p_usart Pointer to a UART instance.
 *
 * \return USART PDC registers base for PDC driver to access.
 */
Pdc *usart_get_pdc_base(Usart *p_usart)
{
	Pdc *p_pdc_base;

	p_pdc_base = (Pdc *) NULL;

	if (p_usart == USART0) {
		p_pdc_base = PDC_USART0;
		return p_pdc_base;
	}
#if (SAM3S || SAM4S || SAM3XA || SAM3U)
	else if (p_usart == USART1) {
		p_pdc_base = PDC_USART1;
		return p_pdc_base;
	}
#endif
#if (SAM3SD8 || SAM3XA || SAM3U)
	else if (p_usart == USART2) {
		p_pdc_base = PDC_USART2;
		return p_pdc_base;
	}
#endif
#if (SAM3XA || SAM3U)
	else if (p_usart == USART3) {
		p_pdc_base = PDC_USART3;
		return p_pdc_base;
	}
#endif

	return p_pdc_base;
}

/**
 * \brief Enable write protect of USART registers.
 *
 * \param p_usart Pointer to a USART instance.
 */
void usart_enable_writeprotect(Usart *p_usart)
{
	p_usart->US_WPMR = US_WPMR_WPEN | US_WPMR_WPKEY(US_WPKEY_VALUE);
}

/**
 * \brief Disable write protect of USART registers.
 *
 * \param p_usart Pointer to a USART instance.
 */
void usart_disable_writeprotect(Usart *p_usart)
{
	p_usart->US_WPMR = US_WPMR_WPKEY(US_WPKEY_VALUE);
}

/**
 * \brief Get write protect status.
 *
 * \param p_usart Pointer to a USART instance.
 *
 * \return 0 if the peripheral is not protected. 
 * \return 16-bit Write Protect Violation Status otherwise.
 */
uint32_t usart_get_writeprotect_status(Usart *p_usart)
{
	uint32_t reg_value;

	reg_value = p_usart->US_WPSR;
	if (reg_value & US_WPSR_WPVS) {
		return (reg_value & US_WPSR_WPVSRC_Msk) >> US_WPSR_WPVSRC_Pos;
	} else {
		return 0;
	}
}

/**
 * \brief Get the total number of errors that occur during an ISO7816 transfer.
 *
 * \param p_usart Pointer to a USART instance.
 *
 * \return The number of errors that occurred.
 */
uint8_t usart_get_error_number(Usart *p_usart)
{
	return (p_usart->US_NER & US_NER_NB_ERRORS_Msk);
}

#if (SAM3S || SAM4S || SAM3U || SAM3XA)
/**
 * \brief Configure the transmitter preamble length when the Manchester 
 * encode/decode is enabled.
 *
 * \param p_usart Pointer to a USART instance.
 * \param uc_len The transmitter preamble length, which should be 0 ~ 15.
 */
void usart_man_set_tx_pre_len(Usart *p_usart, uint8_t uc_len)
{
	p_usart->US_MAN = (p_usart->US_MAN & ~US_MAN_TX_PL_Msk) |
			US_MAN_TX_PL(uc_len);
}

/**
 * \brief Configure the transmitter preamble pattern when the Manchester 
 * encode/decode is enabled, which should be 0 ~ 3.
 *
 * \param p_usart Pointer to a USART instance.
 * \param uc_pattern 0 if the preamble is composed of '1's;
 * 1 if the preamble is composed of '0's;
 * 2 if the preamble is composed of '01's;
 * 3 if the preamble is composed of '10's.
 */
void usart_man_set_tx_pre_pattern(Usart *p_usart, uint8_t uc_pattern)
{
	p_usart->US_MAN = (p_usart->US_MAN & ~US_MAN_TX_PP_Msk) |
					(uc_pattern << US_MAN_TX_PP_Pos);
}

/**
 * \brief Configure the transmitter Manchester polarity when the Manchester 
 * encode/decode is enabled.
 *
 * \param p_usart Pointer to a USART instance.
 * \param uc_polarity Indicate the transmitter Manchester polarity, which 
 * should be 0 or 1.
 */
void usart_man_set_tx_polarity(Usart *p_usart, uint8_t uc_polarity)
{
	p_usart->US_MAN = (p_usart->US_MAN & ~US_MAN_TX_MPOL) |
				(uc_polarity << 12);
}

/**
 * \brief Configure the detected receiver preamble length when the Manchester 
 * encode/decode is enabled.
 *
 * \param p_usart Pointer to a USART instance.
 * \param uc_len The detected receiver preamble length, which should be 0 ~ 15.
 */
void usart_man_set_rx_pre_len(Usart *p_usart, uint8_t uc_len)
{
	p_usart->US_MAN = (p_usart->US_MAN & ~US_MAN_RX_PL_Msk) |
				US_MAN_RX_PL(uc_len);
}

/**
 * \brief Configure the detected receiver preamble pattern when the Manchester 
 *  encode/decode is enabled, which should be 0 ~ 3.
 *
 * \param p_usart Pointer to a USART instance.
 * \param uc_pattern 0 if the preamble is composed of '1's;
 * 1 if the preamble is composed of '0's;
 * 2 if the preamble is composed of '01's;
 * 3 if the preamble is composed of '10's.
 */
void usart_man_set_rx_pre_pattern(Usart *p_usart, uint8_t uc_pattern)
{
	p_usart->US_MAN = (p_usart->US_MAN & ~US_MAN_RX_PP_Msk) |
					(uc_pattern << US_MAN_RX_PP_Pos);
}

/**
 * \brief Configure the receiver Manchester polarity when the Manchester 
 * encode/decode is enabled.
 *
 * \param p_usart Pointer to a USART instance.
 * \param uc_polarity Indicate the receiver Manchester polarity, which should 
 * be 0 or 1.
 */
void usart_man_set_rx_polarity(Usart *p_usart, uint8_t uc_polarity)
{
	p_usart->US_MAN = (p_usart->US_MAN & ~US_MAN_RX_MPOL) |
				(uc_polarity << 28);
}

/**
 * \brief Enable drift compensation.
 *
 * \note The 16X clock mode must be enabled.
 *
 * \param p_usart Pointer to a USART instance.
 */
void usart_man_enable_drift_compensation(Usart *p_usart)
{
	p_usart->US_MAN |= US_MAN_DRIFT;
}

/**
 * \brief Disable drift compensation.
 *
 * \param p_usart Pointer to a USART instance.
 */
void usart_man_disable_drift_compensation(Usart *p_usart)
{
	p_usart->US_MAN &= ~US_MAN_DRIFT;
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
