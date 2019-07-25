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

/** \addtogroup tc_module
 * \section Purpose
 * The TC driver provides the Interface to configure the Timer Counter (TC).
 *
 * \section Usage
 * <ul>
 *  <li> Optionally, use tc_find_mck_divisor() to let the program find the best
 *     TCCLKS field value automatically.</li>
 *  <li> Configure a Timer Counter in the desired mode using tc_configure().</li>
 *  <li> Start or stop the timer clock using tc_start() and tc_stop().</li>
 *  </li>
 * </ul>
 * For more accurate information, please look at the TC section of the Datasheet.
 *
 * Related files :\n
 * \ref tc.c\n
 * \ref tc.h.\n
*/

/**
*  \file
*
*  \section Purpose
*
*  Interface for configuring and using Timer Counter (TC) peripherals.
*
*  \section Usage
*  -# Optionally, use tc_find_mck_divisor() to let the program find the best
*     TCCLKS field value automatically.
*  -# Configure a Timer Counter in the desired mode using tc_configure().
*  -# Start or stop the timer clock using tc_start() and tc_stop().
*/

/**
 * \file
 *
 * Implementation of Timer Counter (TC).
 *
 */

/*------------------------------------------------------------------------------
 *         Headers
 *------------------------------------------------------------------------------*/

#include "chip.h"
#include "peripherals/tc.h"
#include "peripherals/pmc.h"

#include <assert.h>

/*------------------------------------------------------------------------------
 *         Global functions
 *------------------------------------------------------------------------------*/

/**
 * \brief Configures a Timer Counter Channel
 *
 * Configures a Timer Counter to operate in the given mode. Timer is stopped
 * after configuration and must be restarted with tc_start(). All the
 * interrupts of the timer are also disabled.
 *
 * \param pTc  Pointer to a Tc instance.
 * \param channel Channel number.
 * \param mode  Operating mode (TC_CMR value).
 */
void tc_configure(Tc * pTc, uint32_t channel, uint32_t mode)
{
	volatile TcChannel *pTcCh;

	assert(channel <
	       (sizeof (pTc->TC_CHANNEL) / sizeof (pTc->TC_CHANNEL[0])));
	pTcCh = pTc->TC_CHANNEL + channel;

	/*  Disable TC clock */
	pTcCh->TC_CCR = TC_CCR_CLKDIS;

	/*  Disable interrupts */
	pTcCh->TC_IDR = 0xFFFFFFFF;

	/*  Clear status register */
	pTcCh->TC_SR;

	/*  Set mode */
	pTcCh->TC_CMR = mode;
}

/**
 * \brief Reset and Start the TC Channel
 *
 * Enables the timer clock and performs a software reset to start the counting.
 *
 * \param pTc  Pointer to a Tc instance.
 * \param channel Channel number.
 */
void tc_start(Tc * pTc, uint32_t channel)
{
	volatile TcChannel *pTcCh;

	assert(channel <
	       (sizeof (pTc->TC_CHANNEL) / sizeof (pTc->TC_CHANNEL[0])));

	pTcCh = pTc->TC_CHANNEL + channel;
	pTcCh->TC_CCR = TC_CCR_CLKEN | TC_CCR_SWTRG;
	pTcCh->TC_IER = TC_IER_COVFS;
}

/**
 * \brief Stop TC Channel
 *
 * Disables the timer clock, stopping the counting.
 *
 * \param pTc     Pointer to a Tc instance.
 * \param channel Channel number.
 */
void tc_stop(Tc * pTc, uint32_t channel)
{
	volatile TcChannel *pTcCh;

	assert(channel <
	       (sizeof (pTc->TC_CHANNEL) / sizeof (pTc->TC_CHANNEL[0])));

	pTcCh = pTc->TC_CHANNEL + channel;
	pTcCh->TC_CCR = TC_CCR_CLKDIS;
	pTcCh->TC_IDR = TC_IER_COVFS;
}

/**
 * \brief Enables TC channel interrupts
 *
 * \param tc Pointer to Tc instance
 * \param channel Channel number
 * \param mask mask of interrupts to enable
 */
void tc_enable_it(Tc* tc, uint32_t channel, uint32_t mask)
{
	assert(channel < (sizeof (tc->TC_CHANNEL) / sizeof (tc->TC_CHANNEL[0])));
	tc->TC_CHANNEL[channel].TC_IER = mask;
}

/**
 * \brief Find best MCK divisor
 *
 * Finds the best MCK divisor given the timer frequency and MCK. The result
 * is guaranteed to satisfy the following equation:
 * \code
 *   (MCK / (DIV * 65536)) <= freq <= (MCK / DIV)
 * \endcode
 * with DIV being the highest possible value.
 *
 * \param freq  Desired timer freq.
 * \param div  Divisor value.
 * \param tc_clks  TCCLKS field value for divisor.
 *
 * \return 1 if a proper divisor has been found, otherwise 0.
 */
uint32_t tc_find_mck_divisor (uint32_t freq, uint32_t * div,
				  uint32_t * tc_clks)
{
	const uint32_t periph_clock = pmc_get_peripheral_clock(ID_TC0);
	const uint32_t available_freqs[5] = {periph_clock >> 1, periph_clock >> 3, periph_clock >> 5, periph_clock >> 7, 32768};

	int i = 0;
	for (i = 0; i < 5; ++i)
	{
		uint32_t tmp = freq << 1;
		if (tmp > available_freqs[i])
			break;
	}

	i = (i == 5 ? i-1 : i);

	/*  Store results */
	if (div) {
		*div = periph_clock / available_freqs[i];
	}
	if (tc_clks) {
		*tc_clks = i;
	}

	return 1;
}

uint32_t tc_get_status(Tc* tc, uint32_t channel_num)
{
	return tc->TC_CHANNEL[channel_num].TC_SR;
}


void tc_trigger_on_freq(Tc* tc, uint32_t channel_num, uint32_t freq)
{
	uint32_t div = 0;
	uint32_t tcclks = 0;
	uint32_t tc_id = get_tc_id_from_addr(tc);
	TcChannel* channel = &tc->TC_CHANNEL[channel_num];

	tc_find_mck_divisor(freq, &div, &tcclks);
	tc_configure(tc, channel_num, tcclks | TC_CMR_CPCTRG);
	channel->TC_RC = (pmc_get_peripheral_clock(tc_id) / div) / freq;
}
