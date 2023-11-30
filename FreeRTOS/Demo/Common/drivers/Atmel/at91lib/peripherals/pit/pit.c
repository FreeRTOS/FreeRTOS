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
//         Exported functions
//------------------------------------------------------------------------------
//------------------------------------------------------------------------------
/// Initialize the System timer for a period in µsecond with a system clock
/// freq in MHz
/// \param period  Period in µsecond.
/// \param pit_frequency  System clock frequency in MHz.
//------------------------------------------------------------------------------
void PIT_Init(unsigned int period,
                     unsigned int pit_frequency)
{
    AT91C_BASE_PITC->PITC_PIMR = period? (period * pit_frequency + 8) >> 4 : 0; // +8 to avoid %10 and /10
    AT91C_BASE_PITC->PITC_PIMR |= AT91C_PITC_PITEN;
}

//------------------------------------------------------------------------------
/// Set the PIT Periodic Interval Value
//------------------------------------------------------------------------------
void PIT_SetPIV(unsigned int piv)
{
    AT91C_BASE_PITC->PITC_PIMR = piv | (AT91C_BASE_PITC->PITC_PIMR & (AT91C_PITC_PITEN | AT91C_PITC_PITIEN));
}

//------------------------------------------------------------------------------
/// Enable the PIT
//------------------------------------------------------------------------------
void PIT_Enable(void)
{
    AT91C_BASE_PITC->PITC_PIMR |= AT91C_PITC_PITEN;
}

//----------------------------------------------------------------------------
/// Enable PIT periodic interrupt
//----------------------------------------------------------------------------
void PIT_EnableIT(void)
{
    AT91C_BASE_PITC->PITC_PIMR |= AT91C_PITC_PITIEN;
}

//------------------------------------------------------------------------------
/// Disable PIT periodic interrupt
//------------------------------------------------------------------------------
void PIT_DisableIT(void)
{
    AT91C_BASE_PITC->PITC_PIMR &= ~AT91C_PITC_PITIEN;
}

//------------------------------------------------------------------------------
/// Read PIT mode register
//------------------------------------------------------------------------------
unsigned int PIT_GetMode(void)
{
    return(AT91C_BASE_PITC->PITC_PIMR);
}

//------------------------------------------------------------------------------
/// Read PIT status register
//------------------------------------------------------------------------------
unsigned int PIT_GetStatus(void)
{
    return(AT91C_BASE_PITC->PITC_PISR);
}

//------------------------------------------------------------------------------
/// Read PIT CPIV and PICNT without ressetting the counters
//------------------------------------------------------------------------------
unsigned int PIT_GetPIIR(void)
{
    return(AT91C_BASE_PITC->PITC_PIIR);
}

//------------------------------------------------------------------------------
/// Read System timer CPIV and PICNT without ressetting the counters
//------------------------------------------------------------------------------
unsigned int PIT_GetPIVR(void)
{
    return(AT91C_BASE_PITC->PITC_PIVR);
}
