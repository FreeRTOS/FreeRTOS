/* ----------------------------------------------------------------------------
 *         SAM Software Package License 
 * ----------------------------------------------------------------------------
 * Copyright (c) 2011, Atmel Corporation
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
 * The PIT driver provides the Interface for configuration the Periodic 
 *  Interval Timer (PIT) peripheral.
 *
 * <ul>
 * <li>  Initialize the PIT with the desired period using PIT_Init().
 *    Alternatively, the Periodic Interval Value (PIV) can be configured
 *    manually using PIT_SetPIV(). </li> 
 * <li>  Start the PIT counting using PIT_Enable().
 * <li>  Enable & disable the PIT interrupt using PIT_EnableIT() and
 *    PIT_DisableIT(). </li> 
 * <li>  Retrieve the current status of the PIT using PIT_GetStatus(). </li> 
 * <li>  To get the current value of the internal counter and the number of ticks
 *    that have occurred, use either PIT_GetPIVR() or PIT_GetPIIR() depending
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

/*------------------------------------------------------------------------------
 *         Exported functions
 *------------------------------------------------------------------------------*/

 /**
 * \brief Initialize the Periodic Interval Timer to generate a tick at the 
 * specified period, given the current master clock frequency.
 *
 *  \param uperiod  Period in uSecond.
 *  \param pit_frequency  Master clock frequency in MHz.
 */

void PIT_Init(uint32_t period, uint32_t pit_frequency)
{
    PIT->PIT_MR = period? (period * pit_frequency + 8) >> 4 : 0;
    PIT->PIT_MR |= PIT_MR_PITEN;
}

/**
 * \brief Set the Periodic Interval Value of the PIT.
 *
 *  \param piv  PIV value to set.
 */
void PIT_SetPIV(uint32_t piv)
{
    uint32_t dwMr = PIT->PIT_MR & (~PIT_MR_PIV_Msk);
    PIT->PIT_MR = dwMr | PIT_MR_PIV(piv);
}

/**
 * \brief Enables the PIT if this is not already the case.
 *
 */
void PIT_Enable(void)
{
    PIT->PIT_MR |= PIT_MR_PITEN;
}

/**
 * \brief Disnables the PIT when PIV value is reached.
 *
 */
void PIT_Disable(void)
{
    PIT->PIT_MR &= ~PIT_MR_PITEN;
}

/**
 * \brief Enable the PIT periodic interrupt.
 *
 */
void PIT_EnableIT(void) 
{
    PIT->PIT_MR |= PIT_MR_PITIEN;
}

/**
 * \brief Disables the PIT periodic interrupt.
 *
 */
void PIT_DisableIT(void)
{
    PIT->PIT_MR &= ~PIT_MR_PITIEN;
}

/**
 * \brief Returns the value of the PIT mode register.
 *
 * \return PIT_MR value.
 */
uint32_t PIT_GetMode(void)
{
    return PIT->PIT_MR;
}

/**
 * \brief Returns the value of the PIT status register, clearing it as a side effect.
 *
 * \return PIT_SR value.
 */
uint32_t PIT_GetStatus(void)
{
    return PIT->PIT_SR;
}

/**
 * \brief Returns the value of the PIT Image Register, to read PICNT and CPIV without
 *  clearing the current values.
 * 
 * \return PIT_PIIR value.
 */
uint32_t PIT_GetPIIR(void)
{
    return PIT->PIT_PIIR;
}

/**
 * \brief Returns the value of the PIT Value Register, clearing it as a side effect.
 * 
 * \return PITC_PIVR value.
 */
uint32_t PIT_GetPIVR(void)
{
    return PIT->PIT_PIVR;
}

