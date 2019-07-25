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
 * Interface for Quad Serial Peripheral Interface (QSPI) controller.
 *
 */

#ifndef _QSPI_H_
#define _QSPI_H_

/*----------------------------------------------------------------------------
 *        Types
 *----------------------------------------------------------------------------*/

/** QSPI Command structure */
struct _qspi_cmd {
	/** Data Transfer Type (QSPI_IFR_TFRTYP_TRSFR_xxx) */
	uint32_t ifr_type;

	/** Width of Instruction Code, Address, Option Code and Data
	 * (QSPI_IFR_WIDTH_xxx) */
	uint32_t ifr_width;

	/** Flags to select which information is included in the command */
	struct {
		/** 0: don't send instruction code, 1: send instuction code */
		uint32_t instruction:1;
		/** 0: don't send address, 3: send 3-byte address, 4: send
		 * 4-byte address */
		uint32_t address:3;
		/** 0: don't send mode bits, 1: send mode bits */
		uint32_t mode:1;
		/** 0: don't send dummy bits, 1: send dummy bits */
		uint32_t dummy:1;
		/** 0: don't send/recieve data, 1: send/recieve data */
		uint32_t data:1;
		/** reserved, not used */
		uint32_t reserved:25;
	} enable;

	/** Instruction code */
	uint8_t instruction;

	/** Mode bits */
	uint8_t mode;

	/** Number of mode cycles */
	uint8_t num_mode_cycles;

	/** Number of dummy cycles */
	uint8_t num_dummy_cycles;

	/** QSPI address */
	uint32_t address;

	/** Address of the TX buffer */
	const void *tx_buffer;

	/** Address of the RX buffer */
	void *rx_buffer;

	/** Size of the RX/TX buffer */
	uint32_t buffer_len;

	/** Timeout for the command execution, in timer ticks */
	uint32_t timeout;
};

/*----------------------------------------------------------------------------
 *        Exported functions
 *----------------------------------------------------------------------------*/

#ifdef __cplusplus
 extern "C" {
#endif

/**
 * \brief Reset and initialize a QSPI instance.
 *
 * \param qspi the QSPI instance
 */
void qspi_initialize(Qspi *qspi);

/**
 * \brief Configure the baudrate for a QSPI instance.
 *
 * \param qspi the QSPI instance
 * \param baudrate the requested baudrate
 * \return the actual baudrate configured (can be lower than requested)
 */
uint32_t qspi_set_baudrate(Qspi *qspi, uint32_t baudrate);

/**
 * \brief Perform a QSPI command.
 *
 * Note that if enable.data is set in the command, data will be sent/recieved:
 * - if tx_buffer is not NULL, data will be sent
 * - if rx_buffer is not NULL, data will be recieved
 * - if both tx_buffer and rx_buffer are NULL, QSPI will be configured in
 * "Continuous Read" mode and random read access can be done at the address
 * returned by get_qspi_mem_from_addr
 *
 * \param qspi the QSPI instance
 * \param cmd the QSPI command to perform
 * \return true if the command was succesfully issued, false otherwise
 */
bool qspi_perform_command(Qspi *qspi, const struct _qspi_cmd *cmd);

#ifdef __cplusplus
}
#endif

#endif /* _QSPI_H_ */
