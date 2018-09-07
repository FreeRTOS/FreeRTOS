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
 * \section Purpose
 *
 * ISO 7816 driver
 *
 * \section Usage
 *
 * Explanation on the usage of the code made available through the header file.
 */

/*------------------------------------------------------------------------------
 *         Headers
 *------------------------------------------------------------------------------*/

#include "board.h"
#include "chip.h"

#ifdef CONFIG_HAVE_FLEXCOM
#include "peripherals/flexcom.h"
#endif
#include "peripherals/pmc.h"
#include "peripherals/usart_iso7816_4.h"
#include "peripherals/usart.h"

#include "trace.h"

/*------------------------------------------------------------------------------
 *         Definitions
 *------------------------------------------------------------------------------*/
/** Case for APDU commands*/
#define CASE1  1
#define CASE2  2
#define CASE3  3

/** Flip flop for send and receive char */
#define USART_SEND 0
#define USART_RCV  1

/*-----------------------------------------------------------------------------
 *          Internal variables
 *-----------------------------------------------------------------------------*/
/** Variable for state of send and receive froom USART */
static uint8_t state_usart_global = USART_RCV;

/*----------------------------------------------------------------------------
 *          Internal functions
 *----------------------------------------------------------------------------*/

/**
 * Get a character from iso7816
 * \param pchar_to_receive Pointer for store the received char
 * \return 0: if timeout else status of US_CSR
 */
static uint32_t iso7816_get_char(Usart* usart, uint8_t * pchar_to_receive)
{
	uint32_t status;
	uint32_t timeout = 0;

	if (state_usart_global == USART_SEND) {
		while ((usart->US_CSR & US_CSR_TXEMPTY) == 0) {
		}
		usart->US_CR = US_CR_RSTSTA | US_CR_RSTIT | US_CR_RSTNACK;
		state_usart_global = USART_RCV;
	}

	/* Wait USART ready for reception */
	while (((usart->US_CSR & US_CSR_RXRDY) == 0)) {
		if (timeout++ > 12000 * (pmc_get_master_clock() / 1000000)) {
			trace_debug("TimeOut\n\r");
			return (0);
		}
	}
	trace_debug("T: %u\n\r", (unsigned)timeout);

	/* At least one complete character has been received and US_RHR has not yet been read. */
	/* Get a char */
	*pchar_to_receive = ((usart->US_RHR) & 0xFF);

	status = (usart-> US_CSR & (US_CSR_OVRE | US_CSR_FRAME | US_CSR_PARE | US_CSR_TIMEOUT | US_CSR_NACK | (1 << 10)));

	if (status != 0) {
		/* trace_debug("R:0x%X\n\r", status); */
		trace_debug("R:0x%X\n\r", (unsigned)usart->US_CSR);
		trace_debug("Nb:0x%X\n\r", (unsigned)usart->US_NER);
		usart->US_CR = US_CR_RSTSTA;
	}
	/* Return status */
	return (status);
}

/**
 * Send a char to iso7816
 * \param char_to_send char to be send
 * \return status of US_CSR
 */
static uint32_t iso7816_send_char(Usart* usart, uint8_t char_to_send)
{
	uint32_t status;

	if (state_usart_global == USART_RCV) {
		usart->US_CR = US_CR_RSTSTA | US_CR_RSTIT | US_CR_RSTNACK;
		state_usart_global = USART_SEND;
	}

	/* Wait USART ready for transmit */
	while ((usart->US_CSR & US_CSR_TXRDY) == 0) {
	}
	/* There is no character in the US_THR */
	/* Transmit a char */
	usart->US_THR = char_to_send;

	status = (usart-> US_CSR & (US_CSR_OVRE | US_CSR_FRAME | US_CSR_PARE | US_CSR_TIMEOUT | US_CSR_NACK | (1 << 10)));

	if (status != 0) {
		trace_debug("E:0x%X\n\r", (unsigned)usart->US_CSR);
		trace_debug("Nb:0x%X\n\r", (unsigned)usart->US_NER);
		usart->US_CR = US_CR_RSTSTA;
	}
	/* Return status */
	return (status);
}



/*----------------------------------------------------------------------------
 *          Exported functions
 *----------------------------------------------------------------------------*/

/**
 *  Iso 7816 ICC power off
 */
void iso7816_icc_power_off(const struct _pin* pinrst)
{
	/* Clear RESET Master Card */
	pio_clear(pinrst);
}

/**
 *  Iso 7816 ICC power on
 */
static void iso7816_icc_power_on(const struct _pin* pinrst)
{
	/* Set RESET Master Card */
	pio_set(pinrst);
}


/**
 * Transfert Block TPDU T=0
 * \param pAPDU    APDU buffer
 * \param pMessage Message buffer
 * \param length  Block length
 * \return         Message index
 */
uint16_t iso7816_xfr_block_TPDU_T0(const struct _iso7816_desc* iso7816, const uint8_t * pAPDU,
								   uint8_t * pMessage, uint16_t length)
{
	uint16_t NeNc, indexApdu = 4, indexMessage = 0;
	uint8_t SW1 = 0, procByte, cmdCase, ins;
	Usart* usart = iso7816->addr;

	trace_debug("pAPDU[0]=0x%X\n\r", pAPDU[0]);
	trace_debug("pAPDU[1]=0x%X\n\r", pAPDU[1]);
	trace_debug("pAPDU[2]=0x%X\n\r", pAPDU[2]);
	trace_debug("pAPDU[3]=0x%X\n\r", pAPDU[3]);
	trace_debug("pAPDU[4]=0x%X\n\r", pAPDU[4]);
	trace_debug("pAPDU[5]=0x%X\n\r", pAPDU[5]);
	trace_debug("wlength=%d\n\r", length);

	iso7816_send_char(usart, pAPDU[0]);	/* CLA */
	iso7816_send_char(usart, pAPDU[1]);	/* INS */
	iso7816_send_char(usart, pAPDU[2]);	/* P1 */
	iso7816_send_char(usart, pAPDU[3]);	/* P2 */
	iso7816_send_char(usart, pAPDU[4]);	/* P3 */

	/* Handle the four structures of command APDU */
	indexApdu = 4;

	if (length == 4) {
		cmdCase = CASE1;
		NeNc = 0;
	} else if (length == 5) {
		cmdCase = CASE2;
		NeNc = pAPDU[4];	/* C5 */
		if (NeNc == 0) {
			NeNc = 256;
		}
	} else if (length == 6) {
		NeNc = pAPDU[4];	/* C5 */
		cmdCase = CASE3;
	} else if (length == 7) {
		NeNc = pAPDU[4];	/* C5 */
		if (NeNc == 0) {
			cmdCase = CASE2;
			NeNc = (pAPDU[5] << 8) + pAPDU[6];
		} else {
			cmdCase = CASE3;
		}
	} else {
		NeNc = pAPDU[4];	/* C5 */
		if (NeNc == 0) {
			cmdCase = CASE3;
			NeNc = (pAPDU[5] << 8) + pAPDU[6];
		} else {
			cmdCase = CASE3;
		}
	}

	trace_debug("CASE=0x%X NeNc=0x%X\n\r", cmdCase, NeNc);

	/* Handle Procedure Bytes */
	do {
		iso7816_get_char(usart, &procByte);
		ins = procByte ^ 0xff;
		/* Handle NULL */
		if (procByte == ISO_NULL_VAL) {
			trace_debug("INS\n\r");
			continue;
		}
		/* Handle SW1 */
		else if (((procByte & 0xF0) == 0x60) || ((procByte & 0xF0) == 0x90)) {
			trace_debug("SW1\n\r");
			SW1 = 1;
		}
		/* Handle INS */
		else if (pAPDU[1] == procByte) {
			trace_debug("HdlINS\n\r");
			if (cmdCase == CASE2) {
				/* receive data from card */
				do {
					iso7816_get_char(usart, &pMessage[indexMessage++]);
				} while (0 != --NeNc);
			} else {
				/* Send data */
				do {
					iso7816_send_char(usart, pAPDU[indexApdu++]);
				} while (0 != --NeNc);
			}
		}
		/* Handle INS ^ 0xff */
		else if (pAPDU[1] == ins) {
			trace_debug("HdlINS+\n\r");
			if (cmdCase == CASE2) {
				/* receive data from card */
				iso7816_get_char(usart, &pMessage[indexMessage++]);
			} else {
				iso7816_send_char(usart, pAPDU[indexApdu++]);
			}
			NeNc--;
		} else {
			/* ?? */
			trace_debug("procByte=0x%X\n\r", procByte);
			break;
		}
	} while (NeNc != 0);

	/* Status Bytes */
	if (SW1 == 0) {
		iso7816_get_char(usart, &pMessage[indexMessage++]);	/* SW1 */
	} else {
		pMessage[indexMessage++] = procByte;
	}
	iso7816_get_char(usart, &pMessage[indexMessage++]);	/* SW2 */

	return (indexMessage);
}

/**
 *  Escape iso7816
 */
void iso7816_escape(void)
{
	trace_debug("For user, if needed\n\r");
}

/**
 *  Restart clock iso7816
 */
void iso7816_restart_clock(struct _iso7816_desc* iso7816)
{
	Usart* usart = iso7816->addr;
	trace_debug("iso7816_restart_clock\n\r");
	usart->US_BRGR = 13;
}

/**
 *  Stop clock iso7816
 */
void iso7816_stop_clock(struct _iso7816_desc* iso7816)
{
	Usart* usart = iso7816->addr;
	trace_debug("iso7816_stop_clock\n\r");
	usart->US_BRGR = 0;
}

/**
 *  T0 APDU
 */
void iso7816_to_APDU(void)
{
	trace_debug("iso7816_toAPDU\n\r");
	trace_debug("Not supported at this time\n\r");
}

/**
 * Answer To Reset (ATR)
 * \param pAtr    ATR buffer
 * \param plength Pointer for store the ATR length
 */
void iso7816_get_data_block_ATR(struct _iso7816_desc* iso7816, uint8_t * pAtr, uint8_t * plength)
{
	uint32_t i, j, y;
	Usart* usart = iso7816->addr;

	*plength = 0;

	/* Read ATR TS */
	iso7816_get_char(usart, &pAtr[0]);
	/* Read ATR T0 */
	iso7816_get_char(usart, &pAtr[1]);
	y = pAtr[1] & 0xF0;
	i = 2;

	/* Read ATR Ti */
	while (y) {
		if (y & 0x10) {	/* TA[i] */
			iso7816_get_char(usart, &pAtr[i++]);
		}
		if (y & 0x20) {	/* TB[i] */
			iso7816_get_char(usart, &pAtr[i++]);
		}
		if (y & 0x40) {	/* TC[i] */
			iso7816_get_char(usart, &pAtr[i++]);
		}
		if (y & 0x80) {	/* TD[i] */
			iso7816_get_char(usart, &pAtr[i]);
			y = pAtr[i++] & 0xF0;
		} else {
			y = 0;
		}
	}
	/* Historical Bytes */
	y = pAtr[1] & 0x0F;
	for (j = 0; j < y; j++) {
		iso7816_get_char(usart, &pAtr[i++]);
	}
	*plength = i;
}

/**
 * Set data rate and clock frequency
 * \param clock_frequency ICC clock frequency in KHz.
 * \param data_rate       ICC data rate in bpd
 */
void iso7816_set_data_rate_and_clock_frequency(struct _iso7816_desc* iso7816, uint32_t clock_frequency, uint32_t data_rate)
{
	uint8_t clk_frequency;
	uint32_t per_mck;
	Usart* usart = iso7816->addr;

	/* Define the baud rate divisor register */
	per_mck = pmc_get_peripheral_clock(iso7816->id);
	usart->US_BRGR = per_mck / (clock_frequency * 1000);
	clk_frequency = per_mck / usart->US_BRGR;
	usart->US_FIDI = (clk_frequency) / data_rate;
}

/**
 * Pin status for iso7816 RESET
 * \return 1 if the Pin RstMC is high; otherwise 0.
 */
uint8_t iso7816_get_status_pin_reset(const struct _pin* pinrst)
{
	return pio_get(pinrst);
}

/**
 *  cold reset
 */
void iso7816_cold_reset(struct _iso7816_desc* iso7816)
{
	volatile uint32_t i;
	Usart* usart = iso7816->addr;

	/* tb: wait 400 cycles */
	for (i = 0; i < (120 * (pmc_get_master_clock() / 1000000)); i++) {
	}
	usart->US_RHR;
	usart->US_CR = US_CR_RSTSTA | US_CR_RSTIT | US_CR_RSTNACK;
	iso7816_icc_power_on(&iso7816->pin_rst);
}

/**
 *  Warm reset
 */
void iso7816_warm_reset(struct _iso7816_desc* iso7816)
{
	volatile uint32_t i;
	Usart* usart = iso7816->addr;

	iso7816_icc_power_off(&iso7816->pin_rst);
	/* tb: wait 400 cycles, 40000cycles/t(277ns)=11ms  */
	for (i = 0; i < (30 * (pmc_get_master_clock() / 1000000)); i++) {
	}
	usart->US_RHR;
	usart->US_CR = US_CR_RSTSTA | US_CR_RSTIT | US_CR_RSTNACK;
	iso7816_icc_power_on(&iso7816->pin_rst);
}

/**
 * Decode ATR trace
 * \param pAtr pointer on ATR buffer
 */
void iso7816_decode_ATR(uint8_t * pAtr)
{
	uint32_t i, j, y;
	uint8_t offset;

	printf("\n\r");
	printf("ATR: Answer To Reset:\n\r");
	printf("TS = 0x%X Initial character ", pAtr[0]);

	switch (pAtr[0])
	{
		case 0x3B:
			printf("Direct Convention\n\r");
			break;
		case 0x3F:
			printf("Inverse Convention\n\r");
			break;
		default:
			printf("BAD Convention\n\r");
			break;
	}
	printf("T0 = 0x%X Format caracter\n\r", pAtr[1]);
	printf("    Number of historical bytes: K = %d\n\r", pAtr[1] & 0x0F);
	printf("    Presence further interface byte:\n\r");
	if (pAtr[1] & 0x80) {
		printf("TA ");
	}
	if (pAtr[1] & 0x40) {
		printf("TB ");
	}
	if (pAtr[1] & 0x20) {
		printf("TC ");
	}
	if (pAtr[1] & 0x10) {
		printf("TD ");
	}
	if (pAtr[1] != 0) {
		printf(" present\n\r");
	}

	i = 2;
	y = pAtr[1] & 0xF0;

	/* Read ATR Ti */
	offset = 1;
	while (y) {

		if (y & 0x10) {	/* TA[i] */
			printf("TA[%d] = 0x%X ", offset, pAtr[i]);
			if (offset == 1) {
				printf("FI = %d ", (pAtr[i] >> 8));
				printf("DI = %d", (pAtr[i] & 0x0F));
			}
			printf("\n\r");
			i++;
		}
		if (y & 0x20) {	/* TB[i] */
			printf("TB[%d] = 0x%X\n\r", offset, pAtr[i]);
			i++;
		}
		if (y & 0x40) {	/* TC[i] */
			printf("TC[%d] = 0x%X ", offset, pAtr[i]);
			if (offset == 1) {
				printf("Extra Guard Time: N = %d", pAtr[i]);
			}
			printf("\n\r");
			i++;
		}
		if (y & 0x80) {	/* TD[i] */
			printf("TD[%d] = 0x%X\n\r", offset, pAtr[i]);
			y = pAtr[i++] & 0xF0;
		} else {
			y = 0;
		}
		offset++;
	}

	/* Historical Bytes */
	printf("Historical bytes:\n\r");
	y = pAtr[1] & 0x0F;
	for (j = 0; j < y; j++) {

		printf(" 0x%X", pAtr[i]);
		if ((pAtr[i] > 0x21) && (pAtr[i] < 0x7D)) {	/* ASCII */
			printf("(%c) ", pAtr[i]);
		}
		i++;
	}
	printf("\n\r\n\r");

}

/** Initializes a usart ISO7816
 *  \param
 */
static void _usart_iso7816_configure(Usart* usart, const struct _iso7816_opt* opt, uint32_t mode)
{
	/* Reset and disable receiver & transmitter */
	usart->US_CR = US_CR_RSTRX | US_CR_RSTTX | US_CR_RXDIS | US_CR_TXDIS;
	/* Configure mode */
	usart->US_MR = mode;

	/* Disable all interrupts */
	usart->US_IDR = 0xFFFFFFFF;
	usart->US_FIDI = opt->fidi_ratio;
	/* Define the baud rate divisor register  */
	/* CD = MCK /(FIDI x BAUD) = periph_mck / (372x9600) */
	uint32_t per_mck = pmc_get_peripheral_clock(get_usart_id_from_addr(usart));
	usart->US_BRGR = per_mck / opt->iso7816_hz;
	/* Write the Timeguard Register */
	usart->US_TTGR = opt->time_guard;
	/* Enable receiver and transmitter */
	usart->US_CR = US_CR_RXEN | US_CR_TXEN;
}

/** Initializes a ISO driver
 *  \param
 */
uint8_t iso7816_init(struct _iso7816_desc* iso7816, const struct _iso7816_opt* opt)
{
	uint32_t mode = 0;
	Usart* usart = iso7816->addr;

	trace_debug("ISO_Init\n\r");

	/* Configure control Pios */
	pio_configure(&iso7816->pin_stop, 1);
	pio_configure(&iso7816->pin_mod_vcc, 1);
	pio_configure(&iso7816->pin_rst, 1);

	/* STOP = 1, normal operation */
	pio_set(&iso7816->pin_stop);
	/* MOD = 1, 3V3 */
	pio_set(&iso7816->pin_mod_vcc);

	pmc_enable_peripheral(iso7816->id);

#ifdef CONFIG_HAVE_FLEXCOM
	/* switch Flexcom to Usart mode */
	Flexcom* flexcom = get_flexcom_addr_from_id(iso7816->id);
	if (flexcom) {
		flexcom_select(flexcom, FLEX_MR_OPMODE_USART);
	}
#endif

	/* Initialize driver to use */
	mode  = opt->clock_sel | opt->char_length | opt->sync | opt->parity_type ;
	mode |= opt->inhibit_nack | opt->dis_suc_nack ;
	mode |= US_MR_CLKO ; /* The USART drives the SCK pin */

	/* Check whether the input values are legal. */
	if ( (opt->parity_type != US_MR_PAR_EVEN) && (opt->parity_type != US_MR_PAR_ODD) ) {
		return 1;
	}
	if (opt->protocol_type == US_MR_USART_MODE_IS07816_T_0) {
		mode |= US_MR_USART_MODE_IS07816_T_0 | US_MR_NBSTOP_2_BIT | US_MR_MAX_ITERATION(opt->max_iterations);
		if (opt->bit_order) {
			mode |= US_MR_MSBF;
		}
	} else if (opt->protocol_type == US_MR_USART_MODE_IS07816_T_1) {
		/*
		 * Only LSBF is used in the T=1 protocol, and max_iterations field
		 * is only used in T=0 mode.
		 */
		if (opt->bit_order || opt->max_iterations) {
			return 1;
		}
		/* Set USART mode to ISO7816, T=1, and always uses 1 stop bit. */
		mode |= US_MR_USART_MODE_IS07816_T_1 | US_MR_NBSTOP_1_BIT;
	} else {
		return 1;
	}

	_usart_iso7816_configure (usart, opt, mode);
	return 0;
}
