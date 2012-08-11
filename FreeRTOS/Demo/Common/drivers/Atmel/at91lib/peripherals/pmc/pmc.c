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

#include "pmc.h"
#include <board.h>
#include <utility/assert.h>
#include <utility/trace.h>

//------------------------------------------------------------------------------
//         Global functions
//------------------------------------------------------------------------------

#if defined(at91sam7l64) || defined(at91sam7l128)
//------------------------------------------------------------------------------
/// Sets the fast wake-up inputs that can get the device out of Wait mode.
/// \param inputs  Fast wake-up inputs to enable.
//------------------------------------------------------------------------------
void PMC_SetFastWakeUpInputs(unsigned int inputs)
{
    SANITY_CHECK((inputs & ~0xFF) == 0);
    AT91C_BASE_PMC->PMC_FSMR = inputs;
}

#if !defined(__ICCARM__)
__attribute__ ((section (".ramfunc"))) // GCC
#endif
//------------------------------------------------------------------------------
/// Disables the main oscillator, making the device enter Wait mode.
//------------------------------------------------------------------------------
void PMC_DisableMainOscillatorForWaitMode(void)
{
    AT91C_BASE_PMC->PMC_MOR = 0x37 << 16;
    while ((AT91C_BASE_PMC->PMC_MOR & AT91C_PMC_MAINSELS) != AT91C_PMC_MAINSELS);
}

#endif

#if defined(at91sam7l)
//------------------------------------------------------------------------------
/// Disables the main oscillator when NOT running on it.
//------------------------------------------------------------------------------
void PMC_DisableMainOscillator(void)
{
    AT91C_BASE_PMC->PMC_MOR = 0x37 << 16;
    while ((AT91C_BASE_PMC->PMC_SR & AT91C_PMC_MAINSELS) == AT91C_PMC_MAINSELS);
}
#endif

//------------------------------------------------------------------------------
/// Disables the processor clock, making the device enter Idle mode.
//------------------------------------------------------------------------------
void PMC_DisableProcessorClock(void)
{
    AT91C_BASE_PMC->PMC_SCDR = AT91C_PMC_PCK;
    while ((AT91C_BASE_PMC->PMC_SCSR & AT91C_PMC_PCK) != AT91C_PMC_PCK);
}

//------------------------------------------------------------------------------
/// Enables the clock of a peripheral. The peripheral ID (AT91C_ID_xxx) is used
/// to identify which peripheral is targetted.
/// Note that the ID must NOT be shifted (i.e. 1 << AT91C_ID_xxx).
/// \param id  Peripheral ID (AT91C_ID_xxx).
//------------------------------------------------------------------------------
void PMC_EnablePeripheral(unsigned int id)
{
    SANITY_CHECK(id < 32);

    if ((AT91C_BASE_PMC->PMC_PCSR & (1 << id)) == (1 << id)) {

        trace_LOG(trace_INFO,
                  "-I- PMC_EnablePeripheral: clock of peripheral"
                  " %u is already enabled\n\r",
                  id);
    }
    else {

        AT91C_BASE_PMC->PMC_PCER = 1 << id;
    }
}

//------------------------------------------------------------------------------
/// Disables the clock of a peripheral. The peripheral ID (AT91C_ID_xxx) is used
/// to identify which peripheral is targetted.
/// Note that the ID must NOT be shifted (i.e. 1 << AT91C_ID_xxx).
/// \param id  Peripheral ID (AT91C_ID_xxx).
//------------------------------------------------------------------------------
void PMC_DisablePeripheral(unsigned int id)
{
    SANITY_CHECK(id < 32);

    if ((AT91C_BASE_PMC->PMC_PCSR & (1 << id)) != (1 << id)) {

        trace_LOG(trace_INFO,
                  "-I- PMC_DisablePeripheral: clock of peripheral"
                  " %u is not enabled\n\r",
                  id);
    }
    else {

        AT91C_BASE_PMC->PMC_PCDR = 1 << id;
    }
}

