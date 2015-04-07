/* ----------------------------------------------------------------------------
 *         ATMEL Microcontroller Software Support 
 * ----------------------------------------------------------------------------
 * Copyright (c) 2008, Atmel Corporation
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
//         Headers
//------------------------------------------------------------------------------

#include "pit.h"
#include <board.h>

//------------------------------------------------------------------------------
//         Global functions
//------------------------------------------------------------------------------

//------------------------------------------------------------------------------
/// Initialize the Periodic Interval Timer to generate a tick at the specified
/// period, given the current master clock frequency.
/// \param period  Period in µsecond.
/// \param pit_frequency  Master clock frequency in MHz.
//------------------------------------------------------------------------------
void PIT_Init(unsigned int period, unsigned int pit_frequency)
{
    AT91C_BASE_PITC->PITC_PIMR = period? (period * pit_frequency + 8) >> 4 : 0;
    AT91C_BASE_PITC->PITC_PIMR |= AT91C_PITC_PITEN;
}

//------------------------------------------------------------------------------
/// Set the Periodic Interval Value of the PIT.
/// \param piv  PIV value to set.
//------------------------------------------------------------------------------
void PIT_SetPIV(unsigned int piv)
{
    AT91C_BASE_PITC->PITC_PIMR = (AT91C_BASE_PITC->PITC_PIMR & AT91C_PITC_PIV)
                                 | piv;
}

//------------------------------------------------------------------------------
/// Enables the PIT if this is not already the case.
//------------------------------------------------------------------------------
void PIT_Enable(void)
{
    AT91C_BASE_PITC->PITC_PIMR |= AT91C_PITC_PITEN;
}

//----------------------------------------------------------------------------
/// Enable the PIT periodic interrupt.
//----------------------------------------------------------------------------
void PIT_EnableIT(void)
{
    AT91C_BASE_PITC->PITC_PIMR |= AT91C_PITC_PITIEN;
}

//------------------------------------------------------------------------------
/// Disables the PIT periodic interrupt.
//------------------------------------------------------------------------------
void PIT_DisableIT(void)
{
    AT91C_BASE_PITC->PITC_PIMR &= ~AT91C_PITC_PITIEN;
}

//------------------------------------------------------------------------------
/// Returns the value of the PIT mode register.
/// \return PIT_MR value.
//------------------------------------------------------------------------------
unsigned int PIT_GetMode(void)
{
    return AT91C_BASE_PITC->PITC_PIMR;
}

//------------------------------------------------------------------------------
/// Returns the value of the PIT status register, clearing it as a side effect.
/// \return PIT_SR value.
//------------------------------------------------------------------------------
unsigned int PIT_GetStatus(void)
{
    return AT91C_BASE_PITC->PITC_PISR;
}

//------------------------------------------------------------------------------
/// Returns the value of the PIT Image Register, to read PICNT and CPIV without
/// clearing the current values.
/// \return PIT_PIIR value.
//------------------------------------------------------------------------------
unsigned int PIT_GetPIIR(void)
{
    return AT91C_BASE_PITC->PITC_PIIR;
}

//------------------------------------------------------------------------------
/// Returns the value of the PIT Value Register, clearing it as a side effect.
/// \return PIT_PIVR value.
//------------------------------------------------------------------------------
unsigned int PIT_GetPIVR(void)
{
    return AT91C_BASE_PITC->PITC_PIVR;
}
