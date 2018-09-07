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

/** \addtogroup rtng_module Working with RTNG
 * \ingroup peripherals_module
 * The TRNG driver provides the interface to configure and use the TRNG
 * peripheral.
 * \n
 *
 * The True Random Number Generator (TRNG) passes the American NIST Special
 * Publication 800-22 and Diehard Random Tests Suites. As soon as the TRNG is
 * enabled (trng_enable()), the generator provides one 32-bit value every 84
 * clock cycles.  TRNG Interrupt can be enabled through trng_enable_it()
 * (respectively disabled with trng_disable_it()).  When new random data is
 * ready, the interrupt will fire and the configured callback will be called.
 * Alternatively, the TRNG can also be used in polling mode using
 * trng_get_random_data().
 *
 * For more accurate information, please look at the TRNG section of the
 * datasheet.
 *
 * Related files :\n
 * \ref trng.c\n
 * \ref trng.h\n
 */
/*@{*/
/*@}*/

/**
 * \file
 *
 * Implementation of True Random Number Generator (TRNG)
 *
 */

/*----------------------------------------------------------------------------
 *        Headers
 *----------------------------------------------------------------------------*/

#include "chip.h"
#include "peripherals/aic.h"
#include "peripherals/pmc.h"
#include "peripherals/trng.h"

/*----------------------------------------------------------------------------
 *        Local Data
 *----------------------------------------------------------------------------*/

static trng_callback_t _trng_callback;
static void*           _trng_callback_arg;

/*------------------------------------------------------------------------------
 *         Local functions
 *------------------------------------------------------------------------------*/

static void _trng_handler(void)
{
	if (TRNG->TRNG_ISR & TRNG_ISR_DATRDY) {
		if (_trng_callback) {
			_trng_callback(TRNG->TRNG_ODATA, _trng_callback_arg);
		}
	}
}

/*------------------------------------------------------------------------------
 *         Exported functions
 *------------------------------------------------------------------------------*/

void trng_enable()
{
	pmc_enable_peripheral(ID_TRNG);
	TRNG->TRNG_CR = TRNG_CR_ENABLE | TRNG_CR_KEY_PASSWD;
}

void trng_disable()
{
	TRNG->TRNG_CR = TRNG_CR_KEY_PASSWD;
	pmc_disable_peripheral(ID_TRNG);
}

void trng_enable_it(trng_callback_t cb, void* user_arg)
{
	_trng_callback = cb;
	_trng_callback_arg = user_arg;
	aic_set_source_vector(ID_TRNG, _trng_handler);
	aic_enable(ID_TRNG);
	TRNG->TRNG_IER = TRNG_IER_DATRDY;
}

void trng_disable_it(void)
{
	TRNG->TRNG_IDR = TRNG_IDR_DATRDY;
	aic_disable(ID_TRNG);
	_trng_callback = NULL;
	_trng_callback_arg = NULL;
}

uint32_t trng_get_random_data(void)
{
	while (!(TRNG->TRNG_ISR & TRNG_ISR_DATRDY));
	return TRNG->TRNG_ODATA;
}
