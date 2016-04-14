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

/** \addtogroup pit_module Working with PIT
 * \section Purpose
 * The PIT driver provides the Interface for configuration the Periodic
 *  Interval Timer (PIT) peripheral.
 *
 * \section Usage
 * <ul>
 * <li>  Initialize the PIT with the desired period using pit_init().
 *    Alternatively, the Periodic Interval Value (PIV) can be configured
 *    manually using pit_set_piv(). </li>
 * <li>  Start the PIT counting using pit_enable().
 * <li>  Enable & disable the PIT interrupt using pit_enable_it() and
 *    pit_disable_it(). </li>
 * <li>  Retrieve the current status of the PIT using pit_get_status(). </li>
 * <li>  To get the current value of the internal counter and the number of ticks
 *    that have occurred, use either pit_get_pivr() or pit_get_piir() depending
 *    on whether you want the values to be cleared or not. </li>
 *
 * </ul>
 * For more accurate information, please look at the PIT section of the
 * Datasheet.
 *
 * Related files :\n
 * \ref pit.c\n
 * \ref pit.h.\n
*/
/*@{*/
/*@}*/

/**
 * \file
 *
 * Implementation of PIT (Periodic Interval Timer) controller.
 *
 */
/*------------------------------------------------------------------------------
 *         Headers
 *------------------------------------------------------------------------------*/

#include "chip.h"
#include "peripherals/pit.h"
#include "peripherals/pmc.h"

/*------------------------------------------------------------------------------
 *         Exported functions
 *------------------------------------------------------------------------------*/

void pit_init(uint32_t period)
{
	uint32_t pit_frequency = pmc_get_peripheral_clock(ID_PIT) / 1000000;
	PIT->PIT_MR = period ? (period * pit_frequency + 8) >> 4 : 0;
	PIT->PIT_MR |= PIT_MR_PITEN;
}

void pit_set_piv(uint32_t piv)
{
	uint32_t dwMr = PIT->PIT_MR & (~PIT_MR_PIV_Msk);
	PIT->PIT_MR = dwMr | PIT_MR_PIV(piv);
}

void pit_enable(void)
{
	PIT->PIT_MR |= PIT_MR_PITEN;
}

void pit_disable(void)
{
	PIT->PIT_MR &= ~PIT_MR_PITEN;
}

void pit_enable_it(void)
{
	PIT->PIT_MR |= PIT_MR_PITIEN;
}

void pit_disable_it(void)
{
	PIT->PIT_MR &= ~PIT_MR_PITIEN;
}

uint32_t pit_get_mode(void)
{
	return PIT->PIT_MR;
}

uint32_t pit_get_status(void)
{
	return PIT->PIT_SR;
}

uint32_t pit_get_piir(void)
{
	return PIT->PIT_PIIR;
}

uint32_t pit_get_pivr(void)
{
	return PIT->PIT_PIVR;
}
