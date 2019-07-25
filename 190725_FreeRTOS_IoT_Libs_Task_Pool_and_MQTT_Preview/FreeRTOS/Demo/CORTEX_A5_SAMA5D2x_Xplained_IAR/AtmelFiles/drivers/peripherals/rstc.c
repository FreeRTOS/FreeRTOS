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

/** \file */
/*---------------------------------------------------------------------------
 *         Headers
 *---------------------------------------------------------------------------*/

#include "chip.h"
#include "peripherals/rstc.h"

/*---------------------------------------------------------------------------
 *         Exported functions
 *---------------------------------------------------------------------------*/

/**
 * Configure the mode of the RSTC peripheral.
 * The configuration is computed by the lib (RSTC_RMR_*).
 * \param mr Desired mode configuration.
 */
void rstc_configure_mode(uint32_t mr)
{
	RSTC->RSTC_MR = (mr & ~RSTC_MR_KEY_Msk) | RSTC_MR_KEY_PASSWD;
}

/**
 * Enable/Disable the detection of a low level on the pin NRST as User Reset
 * \param enable 1 to enable & 0 to disable.
 */
void rstc_set_user_reset_enable(uint8_t enable)
{
	uint32_t mr = RSTC->RSTC_MR;
	if (enable) {
		mr |= RSTC_MR_URSTEN;
	} else {
		mr &= ~RSTC_MR_URSTEN;
	}
	RSTC->RSTC_MR = mr | RSTC_MR_KEY_PASSWD;
}

/**
 * Enable/Disable the interrupt of a User Reset (USRTS bit in RSTC_RST).
 * \param enable 1 to enable & 0 to disable.
 */
void rstc_set_user_reset_interrupt_enable(uint8_t enable)
{
	uint32_t mr = RSTC->RSTC_MR;
	if (enable) {
		mr |= RSTC_MR_URSTIEN;
	} else {

		mr &= ~RSTC_MR_URSTIEN;
	}
	RSTC->RSTC_MR = mr | RSTC_MR_KEY_PASSWD;
}

/**
 * Resets the processor.
 */
void rstc_processor_reset(void)
{
	RSTC->RSTC_CR = RSTC_CR_PROCRST | RSTC_MR_KEY_PASSWD;
}

/**
 * Resets the peripherals.
 */
void rstc_peripheral_reset(void)
{
	RSTC->RSTC_CR = RSTC_CR_PERRST | RSTC_MR_KEY_PASSWD;
}

/**
 * Return NRST pin level ( 1 or 0 ).
 */
uint8_t rstc_get_nrst_level(void)
{
	return (RSTC->RSTC_SR & RSTC_SR_NRSTL) != 0;
}

/**
 * Returns 1 if at least one high-to-low transition of NRST (User Reset) has
 * been detected since the last read of RSTC_RSR.
 */
uint8_t rstc_is_user_reset_detected(void)
{
	return (RSTC->RSTC_SR & RSTC_SR_URSTS) != 0;
}

/**
 * Return 1 if a software reset command is being performed by the reset
 * controller. The reset controller is busy.
 */
uint8_t rstc_is_busy(void)
{
	return (RSTC->RSTC_SR & RSTC_SR_SRCMP) != 0;
}

/**
 * Get the status
 */
uint32_t rstc_get_status(void)
{
	return RSTC->RSTC_SR;
}
