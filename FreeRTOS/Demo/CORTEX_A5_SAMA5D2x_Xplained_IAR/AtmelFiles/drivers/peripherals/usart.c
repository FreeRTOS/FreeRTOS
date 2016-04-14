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

/** \addtogroup usart_module Working with USART
 * \section Purpose
 * The USART driver provides the interface to configure and use the USART peripheral.\n
 *
 * The USART supports several kinds of communication modes such as full-duplex asynchronous/
 * synchronous serial communication,RS485 with driver control signal,ISO7816,SPI and Test modes.
 *
 * To start a USART transfer with \ref dmad_module "DMA" support, the user could follow these steps:
 * <ul>
 * <li> Configure USART with expected mode and baudrate(see \ref usart_configure), which could be done by:
 * -# Resetting and disabling transmitter and receiver by setting US_CR(Control Register). </li>
 * -# Configuring the USART in a specific mode by setting USART_MODE bits in US_MR(Mode Register) </li>
 * -# Setting baudrate which is different from mode to mode.
   </li>
 * <li> Enable transmitter or receiver respectively by set US_CR_TXEN or US_CR_RXEN in US_CR.</li>
 * <li> Read from or write to the peripheral with  \ref dmad_module </li>
 * </ul>
 *
 * \section Usage
 * <ul>
 * <li>  Enable or disable USART transmitter or receiver using
 * usart_set_transmitter_enabled() and usart_set_receiver_enabled().
 * <li>  Enable or disable USART interrupt using usart_enable_it() or usart_disable_it().
 * </li>
 * </ul>
 *
 * For more accurate information, please look at the USART section of the
 * Datasheet.
 *
 * Related files :\n
 * \ref usart.c\n
 * \ref usart.h\n
*/

/**
 * \file
 *
 * Implementation of USART (Universal Synchronous Asynchronous Receiver Transmitter)
 * controller.
 *
 */
/*-----------------------------------------------------------------------------
*         Headers
 *---------------------------------------------------------------------------*/

#include "chip.h"
#include "compiler.h"
#include "peripherals/usart.h"
#include "peripherals/pmc.h"

#include "trace.h"
#include "io.h"

#include <assert.h>
#include <string.h>

/*-----------------------------------------------------------------------------
*
 *---------------------------------------------------------------------------*/

#ifdef CONFIG_HAVE_USART_FIFO
/* Clear FIFO related register if present. Dummy function otherwise. */
static inline void _clear_fifo_control_flags(uint32_t* control_reg)
{
	*control_reg |= US_CR_FIFODIS | US_CR_TXFCLR | US_CR_RXFCLR | US_CR_TXFLCLR;
}
#else
#define _clear_fifo_control_flags(dummy) do {} while(0)
#endif

/* The CD value scope programmed in MR register. */
#define MIN_CD_VALUE                  0x01
#define MIN_CD_VALUE_SPI              0x04
#define MAX_CD_VALUE                  US_BRGR_CD_Msk

/* The receiver sampling divide of baudrate clock. */
#define HIGH_FRQ_SAMPLE_DIV           16
#define LOW_FRQ_SAMPLE_DIV            8

/*----------------------------------------------------------------------------
 *         Exported functions
 *----------------------------------------------------------------------------*/

/**
 * \brief Reset status bits (PARE, OVER, MANERR, UNRE and PXBRK in US_CSR).
 *
 * \param usart Pointer to a USART instance.
 */
void usart_reset_status(Usart *usart)
{
	usart->US_CR = US_CR_RSTSTA;
}


/**
 * \brief Configures an USART peripheral with the specified parameters.
 *  \param usart  Pointer to the USART peripheral to configure.
 *  \param mode  Desired value for the USART mode register (see the datasheet).
 *  \param baudrate  Baudrate at which the USART should operate (in Hz).
 *  \param clock  Frequency of the system master clock (in Hz).
 */
void usart_configure(Usart *usart, uint32_t mode, uint32_t baudrate)
{
	uint32_t clock = pmc_get_peripheral_clock(get_usart_id_from_addr(usart));
	/* Reset and disable receiver & transmitter */
	uint32_t control = US_CR_RSTRX | US_CR_RSTTX | US_CR_RXDIS | US_CR_TXDIS;
	/* Reset and disable FIFO if present */
	_clear_fifo_control_flags(&control);
	/* apply */
	usart->US_CR = control;
	/* Configure mode */
	usart->US_MR = mode;

	/* Configure baudrate */
	/* Asynchronous, no oversampling */
	if (((mode & US_MR_SYNC) == 0) && ((mode & US_MR_OVER) == 0)) {
		usart->US_BRGR = (clock / baudrate) / 16;
	}
#ifdef CONFIG_HAVE_USART_SPI_MODE
	if (((mode & US_MR_USART_MODE_SPI_MASTER) ==
	     US_MR_USART_MODE_SPI_MASTER) || ((mode & US_MR_SYNC) == US_MR_SYNC)) {
		if ((mode & US_MR_USCLKS_Msk) == US_MR_USCLKS_MCK) {
			usart->US_BRGR = clock / baudrate;
		} else {
			if ((mode & US_MR_USCLKS_DIV) == US_MR_USCLKS_DIV) {
				usart->US_BRGR = clock / baudrate / 8;
			}
		}
	}
#endif /* CONFIG_HAVE_USART_SPI_MODE */

	/* TODO other modes */

	/* Disable all interrupts */
	usart->US_IDR = 0xFFFFFFFF;
	/* Enable receiver and transmitter */
	usart->US_CR = US_CR_RXEN | US_CR_TXEN;
}

/**
 * \brief   Get present status
 * \param usart  Pointer to an USART peripheral.
 */
uint32_t usart_get_status(Usart *usart)
{
	return usart->US_CSR;
}

/**
 * \brief   Enable interrupt
 * \param usart  Pointer to an USART peripheral.
 * \param mode  Interrupt mode.
 */
void usart_enable_it(Usart *usart, uint32_t mode)
{
	usart->US_IER = mode;
}

/**
 * \brief   Disable interrupt
 * \param usart  Pointer to an USART peripheral.
 * \param mode  Interrupt mode.
 */
void usart_disable_it(Usart *usart, uint32_t mode)
{
	usart->US_IDR = mode;
}

/**
 * \brief   Return interrupt mask
 * \param usart  Pointer to an USART peripheral.
 */
uint32_t usart_get_it_mask(Usart *usart)
{
	return usart->US_IMR;
}

/**
 * \brief Enables or disables the transmitter of an USART peripheral.
 * \param usart  Pointer to an USART peripheral
 * \param enabled  If true, the transmitter is enabled; otherwise it is
 *                disabled.
 */
void usart_set_transmitter_enabled(Usart *usart, uint8_t enabled)
{
	if (enabled) {
		usart->US_CR = US_CR_TXEN;
	} else {
		usart->US_CR = US_CR_TXDIS;
	}
}

/**
 * \brief Enables or disables the receiver of an USART peripheral
 * \param usart  Pointer to an USART peripheral
 * \param enabled  If true, the receiver is enabled; otherwise it is disabled.
 */
void usart_set_receiver_enabled(Usart *usart, uint8_t enabled)
{
	if (enabled) {
		usart->US_CR = US_CR_RXEN;
	} else {
		usart->US_CR = US_CR_RXDIS;
	}
}

/**
 * \brief Enables or disables the Request To Send (RTS) of an USART peripheral
 * \param usart  Pointer to an USART peripheral
 * \param enabled  If true, the RTS is enabled (0); otherwise it is disabled.
 */
void usart_set_rts_enabled(Usart *usart, uint8_t enabled)
{
	if (enabled) {
		usart->US_CR = US_CR_RTSEN;
	} else {
		usart->US_CR = US_CR_RTSDIS;
	}
}

/**
 * \brief Immediately stop and disable USART transmitter.
 *
 * \param usart Pointer to a USART instance.
 */
void usart_reset_tx(Usart *usart)
{
	/* Reset transmitter */
	usart->US_CR = US_CR_RSTTX | US_CR_TXDIS;
}

/**
 * \brief Configure the transmit timeguard register.
 *
 * \param usart Pointer to a USART instance.
 * \param timeguard The value of transmit timeguard.
 */
void usart_set_tx_timeguard(Usart *usart, uint32_t timeguard)
{
	usart->US_TTGR = timeguard;
}

/**
 * \brief Immediately stop and disable USART receiver.
 *
 * \param usart Pointer to a USART instance.
 */
void usart_reset_rx(Usart *usart)
{
	/* Reset Receiver */
	usart->US_CR = US_CR_RSTRX | US_CR_RXDIS;
}

/**
 * \brief Configure the receive timeout register.
 *
 * \param usart Pointer to a USART instance.
 * \param timeout The value of receive timeout.
 */
void usart_set_rx_timeout(Usart *usart, uint32_t timeout)
{
	usart->US_RTOR = timeout;
}


/**
 * \brief Start transmission of a break.
 *
 * \param usart Pointer to a USART instance.
 */
void usart_start_tx_break(Usart *usart)
{
	usart->US_CR = US_CR_STTBRK;
}

/**
 * \brief Stop transmission of a break.
 *
 * \param usart Pointer to a USART instance.
 */
void usart_stop_tx_break(Usart *usart)
{
	usart->US_CR = US_CR_STPBRK;
}

/**
 * \brief Start waiting for a character before clocking the timeout count.
 * Reset the status bit TIMEOUT in US_CSR.
 *
 * \param usart Pointer to a USART instance.
 */
void usart_start_rx_timeout(Usart *usart)
{
	usart->US_CR = US_CR_STTTO;
}

/**
 * \brief Reset the ITERATION in US_CSR when the ISO7816 mode is enabled.
 *
 * \param usart Pointer to a USART instance.
 */
void usart_reset_iterations(Usart *usart)
{
	usart->US_CR = US_CR_RSTIT;
}

/**
 * \brief Reset NACK in US_CSR.
 *
 * \param usart Pointer to a USART instance.
 */
void usart_reset_nack(Usart *usart)
{
	usart->US_CR = US_CR_RSTNACK;
}

/**
 * \brief Restart the receive timeout.
 *
 * \param usart Pointer to a USART instance.
 */
void usart_restart_rx_timeout(Usart *usart)
{
	usart->US_CR = US_CR_RETTO;
}

/**
 * \brief Sends one packet of data through the specified USART peripheral. This
 * function operates synchronously, so it only returns when the data has been
 * actually sent.
 * \param usart  Pointer to an USART peripheral.
 * \param data  Data to send including 9nth bit and sync field if necessary (in
 *        the same format as the US_THR register in the datasheet).
 * \param timeout  Time out value (0 = no timeout).
 */
void usart_write(Usart *usart, uint16_t data, volatile uint32_t timeout)
{
	if (timeout == 0) {
		while ((usart->US_CSR & US_CSR_TXRDY) == 0) ;
	} else {
		while ((usart->US_CSR & US_CSR_TXRDY) == 0) {
			if (timeout == 0) {
				trace_error("usart_write: Timed out.\n\r");
				return;
			}
			timeout--;
		}
	}
	usart->US_THR = data;
}

/**
 * \brief  Reads and return a packet of data on the specified USART peripheral. This
 * function operates asynchronously, so it waits until some data has been
 * received.
 * \param usart  Pointer to an USART peripheral.
 * \param timeout  Time out value (0 -> no timeout).
 */
uint16_t usart_read(Usart *usart, volatile uint32_t timeout)
{
	if (timeout == 0) {
		while ((usart->US_CSR & US_CSR_RXRDY) == 0) ;
	} else {
		while ((usart->US_CSR & US_CSR_RXRDY) == 0) {
			if (timeout == 0) {
				trace_error("usart_read: Timed out.\n\r");
				return 0;
			}
			timeout--;
		}
	}
	return usart->US_RHR;
}

/**
 * \brief  Returns 1 if some data has been received and can be read from an USART;
 * otherwise returns 0.
 * \param usart  Pointer to an USART instance.
 */
uint8_t usart_is_data_available(Usart *usart)
{
	if ((usart->US_CSR & US_CSR_RXRDY) != 0) {
		return 1;
	} else {
		return 0;
	}
}

/**
 * \brief   Return 1 if a character can be read in USART
 * \param usart  Pointer to an USART peripheral.
 */
uint32_t usart_is_rx_ready(Usart *usart)
{
	return (usart->US_CSR & US_CSR_RXRDY);
}

/**
 * \brief   Return 1 if a character send in USART
 * \param usart  Pointer to an USART peripheral.
 */
uint32_t usart_is_tx_ready(Usart *usart)
{
	return (usart->US_CSR & US_CSR_TXRDY);
}

/**
 * \brief  Sends one packet of data through the specified USART peripheral. This
 * function operates synchronously, so it only returns when the data has been
 * actually sent.
 * \param usart  Pointer to an USART peripheral.
 * \param c  Character to send
 */
void usart_put_char(Usart *usart, uint8_t c)
{
	/* Wait for the transmitter to be ready */
	while ((usart->US_CSR & US_CSR_TXEMPTY) == 0) ;
	/* Send character */
	/* Force an octet write to avoid race conditions with FIFO mode */
	writeb(&usart->US_THR, c);
}

/**
 * \brief  Reads and returns a character from the USART.
 * \note This function is synchronous (i.e. uses polling).
 * \param usart  Pointer to an USART peripheral.
 * \return Character received.
 */
uint8_t usart_get_char(Usart *usart)
{
	while ((usart->US_CSR & US_CSR_RXRDY) == 0) ;
	/* Force an octet read to avoid race conditions with FIFO mode */
	uint8_t v;
	readb(&usart->US_RHR, &v);
	return v;
}

/**
 * \brief  Sets the filter value for the IRDA demodulator.
 * \param usart  Pointer to an USART instance.
 * \param filter  Filter value.
 */
void usart_set_irda_filter(Usart *usart, uint8_t filter)
{
	assert(usart != NULL);

	usart->US_IF = filter;
	/* Set IrDA mode. */
	usart->US_MR = (usart->US_MR & ~US_MR_USART_MODE_Msk) | US_MR_USART_MODE_IRDA;
}

/**
 * \brief Select the SCK pin as the source of baud rate for the USART
 * synchronous slave modes.
 *
 * \param usart Pointer to a USART instance.
 */
void usart_set_sync_slave_baudrate(Usart *usart)
{
	usart->US_MR = (usart->US_MR & ~US_MR_USCLKS_Msk) | US_MR_USCLKS_SCK | US_MR_SYNC;
}

/**
 * \brief Calculate a clock divider (\e CD) for the USART SPI master mode to
 * generate a baud rate as close as possible to the baud rate set point.
 *
 * \note Baud rate calculation:
 * \f$ Baudrate = \frac{SelectedClock}{CD} \f$.
 *
 * \param usart Pointer to a USART instance.
 * \param baudrate Baud rate set point.
 *
 * \retval 0 Baud rate is successfully initialized.
 * \retval 1 Baud rate set point is out of range for the given input clock
 * frequency.
 */
uint32_t usart_set_spi_master_baudrate(Usart *usart, uint32_t baudrate)
{
	uint32_t cd;
	uint32_t clock = pmc_get_peripheral_clock(get_usart_id_from_addr(usart));

	/* Calculate the clock divider according to the formula in SPI mode. */
	cd = (clock + baudrate / 2) / baudrate;
	if (cd < MIN_CD_VALUE_SPI || cd > MAX_CD_VALUE) {
		return 1;
	}
	usart->US_BRGR = cd << US_BRGR_CD_Pos;
	return 0;
}

/**
 * \brief Select the SCK pin as the source of baudrate for the USART SPI slave
 * mode.
 *
 * \param usart Pointer to a USART instance.
 */
void usart_set_spi_slave_baudrate(Usart *usart)
{
	usart->US_MR &= ~US_MR_USCLKS_Msk;
	usart->US_MR |= US_MR_USCLKS_SCK;
}

/**
 * \brief Configure USART to work in hardware handshaking mode.
 *
 * \note By default, the transmitter and receiver aren't enabled.
 *
 * \param usart Pointer to a USART instance.
 *
 * \retval 0 on success.
 * \retval 1 on failure.
 */
uint32_t usart_init_hw_handshaking(Usart *usart)
{
	/* The USART should be initialized first as standard RS232. */
	/* Set hardware handshaking mode. */
	usart->US_MR = (usart->US_MR & ~US_MR_USART_MODE_Msk) | US_MR_USART_MODE_HW_HANDSHAKING;
	return 0;
}

/**
 * \brief Calculate a clock divider(CD) and a fractional part (FP) for the
 * USART asynchronous modes to generate a baudrate as close as possible to
 * the baudrate set point.
 *
 * \note Baud rate calculation: Baudrate = mck/(Over * (CD + FP/8))
 * (Over being 16 or 8). The maximal oversampling is selected if it allows to
 * generate a baudrate close to the set point.
 *
 * \param usart Pointer to a USART instance.
 * \param baudrate Baud rate set point.
 *
 * \retval 0 Baud rate is successfully initialized.
 * \retval 1 Baud rate set point is out of range for the given input clock
 * frequency.
 */
uint32_t usart_set_async_baudrate(Usart *usart, uint32_t baudrate)
{
	uint32_t over, cd_fp, cd, fp;
	uint32_t mck;

	/* get peripheral clock */
	mck = pmc_get_peripheral_clock(get_usart_id_from_addr(usart));

	/* Calculate the receiver sampling divide of baudrate clock. */
	if (mck >= HIGH_FRQ_SAMPLE_DIV * baudrate) {
		over = HIGH_FRQ_SAMPLE_DIV;
	} else {
		over = LOW_FRQ_SAMPLE_DIV;
	}

	/* Calculate clock divider according to the fraction calculated formula. */
	cd_fp = (8 * mck + (over * baudrate) / 2) / (over * baudrate);
	cd = cd_fp >> 0x03;
	fp = cd_fp & 0x07;
	if (cd < MIN_CD_VALUE || cd > MAX_CD_VALUE) {
		return 1;
	}

	/* Configure the OVER bit in MR register. */
	if (over == 8) {
		usart->US_MR |= US_MR_OVER;
	}

	/* Configure the baudrate generate register. */
	usart->US_BRGR = (cd << US_BRGR_CD_Pos) | (fp << US_BRGR_FP_Pos);

	return 0;
}

/*-----------------------------------------------------------------------------
*        Functions if FIFO are used
 *---------------------------------------------------------------------------*/

#ifdef CONFIG_HAVE_USART_FIFO
/**
 * \brief Configure the FIFO of USART device
 *
 * \param usart Pointer to an USART instance.
 * \param tx_thres
 * \param rx_down_thres
 * \param rx_up_thres
 * \param ready_modes
 */
void usart_fifo_configure(Usart *usart, uint8_t tx_thres,
			  uint8_t rx_down_thres, uint8_t rx_up_thres,
			  uint32_t ready_modes)
{
	/* Disable transmitter & receiver */
	usart->US_CR = US_CR_RXDIS | US_CR_TXDIS;
	/* Enable FIFO */
	usart->US_CR = US_CR_FIFOEN;
	/* Configure FIFO */
	usart->US_FMR = US_FMR_TXFTHRES(tx_thres) | US_FMR_RXFTHRES(rx_down_thres)
		| US_FMR_RXFTHRES2(rx_up_thres) | ready_modes;

	/* Disable all fifo related interrupts */
	usart->US_FIDR = 0xFFFFFFFF;

	/* Reenable receiver & transmitter */
	usart->US_CR = US_CR_RXEN | US_CR_TXEN;
}

/**
 * \brief Disable the FIFO mode from the USART device
 *
 * \param usart Pointer to an USART instance.
 * \note receiver and transmitter are reenabled.
 */
void usart_fifo_disable(Usart *usart)
{
	/* Reset and disable receiver & transmitter */
	uint32_t control = US_CR_RSTRX | US_CR_RSTTX | US_CR_RXDIS | US_CR_TXDIS;
	/* clear and disable FIFO */
	_clear_fifo_control_flags(&control);
	/* apply */
	usart->US_CR = control;

	/* Reenable receiver & transmitter */
	usart->US_CR = US_CR_RXEN | US_CR_TXEN;
}

/**
 * \brief Enable FIFO related interrupts according to the given mask
 *
 * \param usart Pointer to an USART instance.
 * \param interrupt_mask The mask to apply
 */
void usart_fifo_enable_it(Usart *usart, uint32_t interrupt_mask)
{
	usart->US_FIER = interrupt_mask;
}

/**
 * \brief Disable FIFO related interrupts according to the given mask
 *
 * \param usart Pointer to an USART instance.
 * \param interrupt_mask The mask to apply
 */
void usart_fifo_disable_it(Usart *usart, uint32_t interrupt_mask)
{
	usart->US_FIDR = interrupt_mask;
}

/**
 * \brief Retrive FIFO related interrupt mask.
 *
 * \param usart Pointer to an USART instance.
 * \return current FIFO interrupt mask.
 */
uint32_t usart_fifo_get_interrupts(Usart *usart)
{
	return usart->US_FIMR;
}


/**
 * \brief Get the size occupied in the input FIFO of USART device.
 *
 * \param usart Pointer to an USART instance.
 * \return Size occupied in the input FIFO (not read yet) in octet
 */
uint32_t usart_fifo_rx_size(Usart *usart)
{
	return (usart->US_FLR & US_FLR_RXFL_Msk) >> US_FLR_RXFL_Pos;
}

/**
 * \brief Get the size occupied in the ouput FIFO of USART device.
 *
 * \param usart Pointer to an USART instance.
 * \return Size occupied in the output FIFO (not sent yet) in octet
 */
uint32_t usart_fifo_tx_size(Usart *usart)
{
	return (usart->US_FLR & US_FLR_TXFL_Msk) >> US_FLR_TXFL_Pos;
}

/**
 * \brief Reads from USART device input channel until the specified length is
 * reached.
 *
 * \param usart Pointer to an USART instance.
 * \param stream Pointer to the receive buffer.
 * \param len Size of the receive buffer, in octets.
 *
 * \return Number of read octets
 *
 * \warning WORKS ONLY IN LITTLE ENDIAN MODE!
 *
 * \note The FIFO must be configured before using this function.
 * \note In case of a TIMEOUT or a BREAK, a null character is appended to the
 * buffer and the returned value should be inferior to \ref len.
 */
uint32_t usart_read_stream(Usart *usart, void *stream, uint32_t len)
{
	uint8_t* buffer = stream;
	uint32_t left = len;
	while (left > 0) {
		/* Stop reception if a timeout or break occur */
		if ((usart->US_CSR & (US_CSR_TIMEOUT | US_CSR_RXBRK)) != 0) {
			*buffer = '\0';
			break;
		}

		if ((usart->US_CSR & US_CSR_RXRDY) == 0) continue;

		/* Get FIFO size (in octets) and clamp it */
		uint32_t buf_size = usart_fifo_rx_size(usart);
		buf_size = buf_size > left ? left : buf_size;

		/* Fill the buffer as must as possible with four data reads */
		while (buf_size >= sizeof(uint32_t)) {
			*(uint32_t*)buffer = usart->US_RHR;
			buffer += sizeof(uint32_t);
			left -= sizeof(uint32_t);
			buf_size -= sizeof(uint32_t);
		}
		/* Add tail data if stream is not 4 octet aligned */
		if (buf_size >= sizeof(uint16_t)) {
			/* two data read */
			readhw(&usart->US_RHR, (uint16_t*)buffer);
			left -= sizeof(uint16_t);
			buffer += sizeof(uint16_t);
			buf_size -= sizeof(uint16_t);
		}
		if (buf_size >= sizeof(uint8_t)) {
			/* one data read */
			readb(&usart->US_RHR, buffer);
			buffer += sizeof(uint8_t);
			left -= sizeof(uint8_t);
			buf_size -= sizeof(uint8_t);
		}
	}
	return len - left;
}

/**
 * \brief Writes given data to USART device output channel until the specified
 * length is reached.
 *
 * \param usart Pointer to an USART instance.
 * \param stream Pointer to the data to send.
 * \param len Size of the data to send, in octets.
 *
 * \return Number of written octets
 *
 * \warning WORKS ONLY IN LITTLE ENDIAN MODE!
 *
 * \note The FIFO must be configured before using this function.
 * \note This function do not wait for the FIFO to be empty.
 * \note In case of a TIMEOUT the transmission is aborted and the returned value
 * should be inferior to \ref len.
 */
uint32_t usart_write_stream(Usart *usart, const void *stream, uint32_t len)
{
	const uint8_t* buffer = stream;
	uint32_t left = len;
	int32_t fifo_size = get_peripheral_fifo_depth(usart);
	if (fifo_size < 0)
		return 0;

	while (left > 0) {
		if ((usart->US_CSR & US_CSR_TXRDY) == 0) continue;

		/* Get FIFO free size (int octet) and clamp it */
		uint32_t buf_size = fifo_size - usart_fifo_tx_size(usart);
		buf_size = buf_size > left ? left : buf_size;

		/* Fill the FIFO as must as possible with four data writes */
		while (buf_size >= sizeof(uint32_t)) {
			usart->US_THR = *(uint32_t*)buffer;
			buffer += sizeof(uint32_t);
			left -= sizeof(uint32_t);
			buf_size -= sizeof(uint32_t);
		}
		/* Add tail data if stream is not 4 octet aligned */
		if (buf_size >= sizeof(uint16_t)) {
			/* two data write */
			writehw(&usart->US_THR, *(uint16_t*)buffer);
			buffer += sizeof(uint16_t);
			left -= sizeof(uint16_t);
			buf_size -= sizeof(uint16_t);
		}
		if (buf_size >= sizeof(uint8_t)) {
			/* one data write */
			writeb(&usart->US_THR, *buffer);
			buffer += sizeof(uint8_t);
			left -= sizeof(uint8_t);
			buf_size -= sizeof(uint8_t);
		}
	}
	return len - left;
}

#endif
