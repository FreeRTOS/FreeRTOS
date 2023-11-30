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

#include "rtt.h"
#include <utility/assert.h>

//------------------------------------------------------------------------------
//         Exported functions
//------------------------------------------------------------------------------

//------------------------------------------------------------------------------
/// Changes the prescaler value of the given RTT and restarts it. This function
/// disables RTT interrupt sources.
/// \param rtt  Pointer to a AT91S_RTTC instance.
/// \param prescaler  Prescaler value for the RTT.
//------------------------------------------------------------------------------
void RTT_SetPrescaler(AT91S_RTTC *rtt, unsigned short prescaler)
{
    rtt->RTTC_RTMR = (prescaler | AT91C_RTTC_RTTRST);
}

//------------------------------------------------------------------------------
/// Returns the current value of the RTT timer value.
/// \param rtt  Pointer to a AT91S_RTTC instance.
//------------------------------------------------------------------------------
unsigned int RTT_GetTime(AT91S_RTTC *rtt)
{
    return rtt->RTTC_RTVR;
}

//------------------------------------------------------------------------------
/// Enables the specified RTT interrupt sources.
/// \param rtt  Pointer to a AT91S_RTTC instance.
/// \param sources  Bitmask of interrupts to enable.
//------------------------------------------------------------------------------
void RTT_EnableIT(AT91S_RTTC *rtt, unsigned int sources)
{
    ASSERT((sources & 0x0004FFFF) == 0,
           "RTT_EnableIT: Wrong sources value.\n\r");
    rtt->RTTC_RTMR |= sources;
}

//------------------------------------------------------------------------------
/// Returns the status register value of the given RTT.
/// \param rtt  Pointer to an AT91S_RTTC instance.
//------------------------------------------------------------------------------
unsigned int RTT_GetStatus(AT91S_RTTC *rtt)
{
    return rtt->RTTC_RTSR;
}

//------------------------------------------------------------------------------
/// Configures the RTT to generate an alarm at the given time.
/// \param pRtt  Pointer to an AT91S_RTTC instance.
/// \param time  Alarm time.
//------------------------------------------------------------------------------
void RTT_SetAlarm(AT91S_RTTC *pRtt, unsigned int time)
{
    SANITY_CHECK(time > 0);

    pRtt->RTTC_RTAR = time - 1;
}

