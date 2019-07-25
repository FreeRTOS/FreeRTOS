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

/** \addtogroup usart_module Working with USART_LIN
 * \section Purpose
 * The USART_LIN driver provides the interface to configure and use the USART peripheral in LIN mode.\n
 *
 *
 * For more accurate information, please look at the USART LIN section of the
 * Datasheet.
 *
 * Related files :\n
 * \ref usart_lin.c\n
 * \ref usart_lin.h\n
*/

/**
 * \file
 *
 * Implementation of USART in LIN mode (Universal Synchronous Asynchronous Receiver Transmitter)
 * controller.
 *
 */
/*-----------------------------------------------------------------------------
*         Headers
 *---------------------------------------------------------------------------*/

#include "chip.h"
#include "compiler.h"

#include "peripherals/pmc.h"
#include "peripherals/usart.h"
#include "peripherals/usart_lin.h"

#include "trace.h"
#include "io.h"

#include <assert.h>
#include <string.h>

/*-----------------------------------------------------------------------------
*
 *---------------------------------------------------------------------------*/

/*----------------------------------------------------------------------------
 *         Exported functions
 *----------------------------------------------------------------------------*/

void usart_lin_reset_status_bits(Usart *usart)
{
	 usart->US_CR = US_CR_RSTSTA;
}


uint32_t usart_lin_get_status_register(Usart *usart)
{
	return usart->US_CSR;
}

void usart_lin_set_mode_master_or_slave (Usart* usart, uint32_t mode_master_or_slave)
{
	/* Set LIN master or slave mode. */
	usart->US_MR = (usart->US_MR & ~US_MR_USART_MODE_Msk) | US_MR_USART_MODE(mode_master_or_slave);
}

/**
 * \brief Abort the current LIN transmission.
 *
 * \param usart Pointer to a USART instance.
 */
void usart_lin_abort_tx(Usart *usart)
{
	usart->US_CR = US_CR_LINABT;
}

/**
 * \brief Send a wakeup signal on the LIN bus.
 *
 * \param usart Pointer to a USART instance.
 */
void usart_lin_send_wakeup_signal(Usart *usart)
{
	usart->US_CR = US_CR_LINWKUP;
}

/**
 * \brief Configure the LIN node action, which should be one of PUBLISH,
 * SUBSCRIBE or IGNORE.
 *
 * \param usart Pointer to a USART instance.
 * \param action 0 for PUBLISH, 1 for SUBSCRIBE, 2 for IGNORE.
 */
void usart_lin_set_node_action(Usart *usart, uint8_t action)
{
	usart->US_LINMR = (usart->US_LINMR & ~US_LINMR_NACT_Msk) | (action << US_LINMR_NACT_Pos);
}

/**
 * \brief Disable the parity check during the LIN communication.
 *
 * \param usart Pointer to a USART instance.
 */
void usart_lin_disable_parity(Usart *usart)
{
	usart->US_LINMR |= US_LINMR_PARDIS;
}

/**
 * \brief Enable the parity check during the LIN communication.
 *
 * \param usart Pointer to a USART instance.
 */
void usart_lin_enable_parity(Usart *usart)
{
	usart->US_LINMR &= ~US_LINMR_PARDIS;
}

/**
 * \brief Disable the checksum during the LIN communication.
 *
 * \param usart Pointer to a USART instance.
 */
void usart_lin_disable_checksum(Usart *usart)
{
	usart->US_LINMR |= US_LINMR_CHKDIS;
}

/**
 * \brief Enable the checksum during the LIN communication.
 *
 * \param usart Pointer to a USART instance.
 */
void usart_lin_enable_checksum(Usart *usart)
{
	usart->US_LINMR &= ~US_LINMR_CHKDIS;
}

/**
 * \brief Configure the checksum type during the LIN communication.
 *
 * \param usart Pointer to a USART instance.
 * \param type 0 for LIN 2.0 Enhanced checksum or 1 for LIN 1.3 Classic
 *  checksum.
 */
void usart_lin_set_checksum_type(Usart *usart, uint8_t type)
{
	usart->US_LINMR = (usart->US_LINMR & ~US_LINMR_CHKTYP) | (type << 4);
}

/**
 * \brief Configure the data length mode during the LIN communication.
 *
 * \param usart Pointer to a USART instance.
 * \param mode Indicate the data length type: 0 if the data length is
 * defined by the DLC of LIN mode register or 1 if the data length is defined
 * by the bit 5 and 6 of the identifier.
 */
void usart_lin_set_data_len_mode(Usart *usart, uint8_t mode)
{
	usart->US_LINMR = (usart->US_LINMR & ~US_LINMR_DLM) | (mode << 5);
}

/**
 * \brief Disable the frame slot mode during the LIN communication.
 *
 * \param usart Pointer to a USART instance.
 */
void usart_lin_disable_frame_slot(Usart *usart)
{
	usart->US_LINMR |= US_LINMR_FSDIS;
}

/**
 * \brief Enable the frame slot mode during the LIN communication.
 *
 * \param usart Pointer to a USART instance.
 */
void usart_lin_enable_frame_slot(Usart *usart)
{
	usart->US_LINMR &= ~US_LINMR_FSDIS;
}

/**
 * \brief Configure the wakeup signal type during the LIN communication.
 *
 * \param usart Pointer to a USART instance.
 * \param type Indicate the checksum type: 0 if the wakeup signal is a
 * LIN 2.0 wakeup signal; 1 if the wakeup signal is a LIN 1.3 wakeup signal.
 */
void usart_lin_set_wakeup_signal_type(Usart *usart, uint8_t type)
{
	usart->US_LINMR = (usart->US_LINMR & ~US_LINMR_WKUPTYP) | (type << 7);
}

/**
 * \brief Configure the response data length if the data length is defined by
 * the DLC field during the LIN communication.
 *
 * \param usart Pointer to a USART instance.
 * \param len Indicate the response data length.
 */
void usart_lin_set_frame_data_len(Usart *usart, uint8_t len)
{
	usart->US_LINMR = (usart->US_LINMR & ~US_LINMR_DLC_Msk) | ((len-1) << US_LINMR_DLC_Pos);
}

/**
 * \brief The LIN mode register is not written by the DMAC.
 *
 * \param usart Pointer to a USART instance.
 */
void usart_lin_disable_dmac_mode(Usart *usart)
{
	usart->US_LINMR &= ~US_LINMR_PDCM;
}

/**
 * \brief The LIN mode register (except this flag) is written by the DMAC.
 *
 * \param usart Pointer to a USART instance.
 */
void usart_lin_enable_dmac_mode(Usart *usart)
{
	usart->US_LINMR |= US_LINMR_PDCM;
}

/**
 * \brief Configure the LIN identifier when USART works in LIN master mode.
 *
 * \param usart Pointer to a USART instance.
 * \param id The identifier to be transmitted.
 */
void usart_lin_set_tx_identifier(Usart *usart, uint8_t id)
{
	usart->US_LINIR = (usart->US_LINIR & ~US_LINIR_IDCHR_Msk) | US_LINIR_IDCHR(id);
}

/**
 * \brief Read the identifier when USART works in LIN mode.
 *
 * \param usart Pointer to a USART instance.
 *
 * \return The last identifier received in LIN slave mode or the last
 * identifier transmitted in LIN master mode.
 */
uint8_t usart_lin_read_identifier(Usart *usart)
{
	return (usart->US_LINIR & US_LINIR_IDCHR_Msk);
}

/**
 * \brief Get data length.
 *
 * \param usart Pointer to a USART instance.
 *
 * \return Data length.
 */
uint8_t usart_lin_get_data_length(Usart *usart)
{
	if (usart->US_LINMR & US_LINMR_DLM) {
		uint8_t data_length = 1 << ((usart->US_LINIR >> (US_LINIR_IDCHR_Pos + 4)) & 0x03);
		return data_length;
	} else {
		return ((usart->US_LINMR & US_LINMR_DLC_Msk) >> US_LINMR_DLC_Pos) + 1;
	}
}

/*-----------------------------------------------------------------------------
*        Functions if FIFO are used
 *---------------------------------------------------------------------------*/

#ifdef CONFIG_HAVE_USART_FIFO

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
uint32_t usart_lin_read_stream(Usart *usart, uint8_t *stream, uint32_t len)
{
	uint8_t* buffer = stream;
	uint32_t left = len;
	while (left > 0) {
		/* Stop reception if a timeout or break occur */
		if ((usart->US_CSR & (US_CSR_TIMEOUT | US_CSR_RXBRK)) != 0) {
			*buffer = '\0';
			break;
		}
		if ((usart->US_CSR & (US_CSR_RXRDY | US_CSR_LINTC)) == 0) continue;

		/* Get FIFO size (in octets) and clamp it */
		uint32_t buf_size = usart_fifo_rx_size(usart);
		buf_size = buf_size > left ? left : buf_size;

		/* Fill the buffer with data received */
		while (buf_size) {
			readb(&usart->US_RHR, buffer);
			buffer ++;
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
uint32_t usart_lin_write_stream(Usart *usart, uint8_t *stream, uint32_t len)
{
	uint8_t* buffer = stream;
	uint32_t left = len;
	int32_t fifo_size = get_peripheral_fifo_depth(usart);
	if (fifo_size < 0)
		return 0;

	while (left > 0) {
		if ((usart->US_CSR & US_CSR_TXRDY) == 0) continue;

		/* Get FIFO free size (int octet) and clamp it */
		uint32_t buf_size = fifo_size - usart_fifo_tx_size(usart);
		buf_size = buf_size > left ? left : buf_size;

		/* Fill the FIFO with data to send */
		while (buf_size) {
			writeb(&usart->US_THR, *buffer);
			buffer ++ ;
			left -= sizeof(uint8_t);
			buf_size -= sizeof(uint8_t);
		}
	}
	return len - left;
}

#endif

