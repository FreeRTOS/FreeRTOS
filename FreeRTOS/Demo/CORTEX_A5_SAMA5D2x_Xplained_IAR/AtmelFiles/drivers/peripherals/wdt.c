/* ----------------------------------------------------------------------------
 *        SAM Software Package License
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
 * Implementation of Watchdog Timer (WDT) controller.
 *
 */

/** \addtogroup wdt_module Working with WDT
 * \section Purpose
 * The WDT driver provides the interface to configure and use the WDT
 * peripheral.
 *
 * The WDT can be used to prevent system lock-up if the software becomes
 * trapped in a deadlock. It can generate a general reset or a processor
 * reset only. It is clocked by slow clock divided by 128.
 *
 * The WDT is running at reset with 16 seconds watchdog period (slow clock at 32.768 kHz)
 * and external reset generation enabled. The user must either disable it or
 * reprogram it to meet the application requires.
 *
 * \section Usage
 * To use the WDT, the user could follow these few steps:
 * <ul>
 * <li>Enable watchdog with given mode using \ref wdt_enable().
 * <li>Restart the watchdog using \ref wdt_restart() within the watchdog period.
 * </ul>
 *
 * For more accurate information, please look at the WDT section of the
 * Datasheet.
 *
 * \note
 * The Watchdog Mode Register (WDT_MR) can be written only once.\n
 *
 * Related files :\n
 * \ref wdt.c\n
 * \ref wdt.h.\n
 */
/*@{*/
/*@}*/

/*---------------------------------------------------------------------------
 *        Headers
 *---------------------------------------------------------------------------*/

#include "chip.h"
#include "peripherals/pmc.h"
#include "peripherals/wdt.h"
#include <stdio.h>

/*----------------------------------------------------------------------------
 *        Local functions
 *----------------------------------------------------------------------------*/

static uint32_t _wdt_compute_period(uint32_t period)
{
	uint32_t value = period * (pmc_get_slow_clock() >> 7) / 1000;
	if (value > 0xfff)
		value = 0xfff;
	return value;
}

/*----------------------------------------------------------------------------
 *        Exported functions
 *----------------------------------------------------------------------------*/

void wdt_enable(uint32_t mode, uint32_t delta, uint32_t counter)
{
	WDT->WDT_MR = (mode & ~(WDT_MR_WDDIS | WDT_MR_WDD_Msk | WDT_MR_WDV_Msk)) |
	              WDT_MR_WDD(_wdt_compute_period(delta)) |
	              WDT_MR_WDV(_wdt_compute_period(counter));
}

void wdt_disable(void)
{
	WDT->WDT_MR = WDT_MR_WDDIS;
}

void wdt_restart()
{
	WDT->WDT_CR = WDT_CR_KEY_PASSWD | WDT_CR_WDRSTT;
}

uint32_t wdt_get_status(void)
{
	return WDT->WDT_SR & (WDT_SR_WDUNF | WDT_SR_WDERR);
}

uint32_t wdt_get_counter_value(void)
{
	return (WDT->WDT_MR & WDT_MR_WDV_Msk) >> WDT_MR_WDV_Pos;
}

