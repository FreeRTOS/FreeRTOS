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

//------------------------------------------------------------------------------
/** \addtogroup iso7816_4 ISO7816-4 Driver
 *  \section Purpose
 *
 *  Definition of methods for ISO7816 driver.
 *
 *  \section Usage
 *
 *  -# ISO7816_Init()
 *  -# ISO7816_IccPowerOff()
 *  -# ISO7816_XfrBlockTPDU_T0()
 *  -# ISO7816_Escape()
 *  -# ISO7816_RestartClock()
 *  -# ISO7816_StopClock()
 *  -# ISO7816_toAPDU()
 *  -# ISO7816_Datablock_ATR()
 *  -# ISO7816_SetDataRateandClockFrequency()
 *  -# ISO7816_StatusReset()
 *  -# ISO7816_cold_reset()
 *  -# ISO7816_warm_reset()
 *  -# ISO7816_Decode_ATR()
 */

#ifndef ISO7816_4_H
#define ISO7816_4_H

/*------------------------------------------------------------------------------
 * Include headers
 *----------------------------------------------------------------------------*/

#include "peripherals/pio.h"
#include "peripherals/usart.h"

/*------------------------------------------------------------------------------
 * Constants Definition
 *----------------------------------------------------------------------------*/

/** Size max of Answer To Reset */
#define ATR_SIZE_MAX            55

/** NULL byte to restart byte procedure */
#define ISO_NULL_VAL            0x60

/* MOD_VCC The signal present on this pin programs the SIM_VCC value */
#define MOD_VCC_1V8		0
#define MOD_VCC_3V3		1

/* STOP pin, Power Down Mode pin */
#define STOP_SHUTDOWN	0
#define	STOP_NORMAL		1

struct _iso7816_opt {
	uint32_t protocol_type; /* Which protocol is used 0: T = 0, 1: T = 1*/
	uint32_t clock_sel;		/* Clock Selection */
	uint32_t char_length;	/* Character Length*/
	uint32_t sync;			/* Synchronous Mode Select */
	uint32_t parity_type;	/* Parity Type*/
	uint32_t num_stop_bits;	/* Number of Stop Bits*/
	uint32_t bit_order; 	/* Bit order in transmitted characters 0: LSB first 1: MSB first.*/
	uint32_t inhibit_nack;	/* Inhibit Non Acknowledge*/
	uint32_t dis_suc_nack;	/* Disable Successive NACK*/

	uint32_t max_iterations;/* */
	uint32_t iso7816_hz;	/* Set the frequency of the ISO7816 clock. */
	uint32_t fidi_ratio;	/* */
	uint32_t time_guard;	/* */
};


struct _iso7816_desc {
	const struct _pin pin_stop;
	const struct _pin pin_mod_vcc;
	const struct _pin pin_rst;

	Usart* addr;
	uint8_t id;
};

/*------------------------------------------------------------------------------
 *         Exported functions
 *----------------------------------------------------------------------------*/

extern void iso7816_icc_power_off(const struct _pin* pinrst);
extern uint16_t iso7816_xfr_block_TPDU_T0(const struct _iso7816_desc* iso7816, const uint8_t* pAPDU, uint8_t* pMessage, uint16_t length);
extern void iso7816_escape(void);
extern void iso7816_restart_clock(struct _iso7816_desc* iso7816);
extern void iso7816_stop_clock(struct _iso7816_desc* iso7816);
extern void iso7816_to_APDU(void);
extern void iso7816_get_data_block_ATR(struct _iso7816_desc* iso7816, uint8_t * pAtr, uint8_t * plength);
extern void iso7816_set_data_rate_and_clock_frequency(struct _iso7816_desc* iso7816, uint32_t clock_frequency, uint32_t data_rate);

extern uint8_t iso7816_get_status_pin_reset(const struct _pin* pinrst);
extern void iso7816_cold_reset(struct _iso7816_desc* iso7816);
extern void iso7816_warm_reset(struct _iso7816_desc* iso7816);
extern void iso7816_decode_ATR(uint8_t * pAtr);

extern uint8_t iso7816_init(struct _iso7816_desc* iso7816, const struct _iso7816_opt* opt);




#endif				/* ISO7816_4_H */
