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

#include "pwmc.h"
#include <board.h>
#include <utility/assert.h>
#include <utility/trace.h>

//------------------------------------------------------------------------------
//         Local functions
//------------------------------------------------------------------------------

//------------------------------------------------------------------------------
/// Finds a prescaler/divisor couple to generate the desired frequency from
/// MCK.
/// Returns the value to enter in PWMC_MR or 0 if the configuration cannot be
/// met.
/// \param frequency  Desired frequency in Hz.
/// \param mck  Master clock frequency in Hz.
//------------------------------------------------------------------------------
static unsigned short FindClockConfiguration(
    unsigned int frequency,
    unsigned int mck)
{
    unsigned int divisors[11] = {1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024};
    unsigned char divisor = 0;
    unsigned int prescaler;

    SANITY_CHECK(frequency < mck);

    // Find prescaler and divisor values
    prescaler = (mck / divisors[divisor]) / frequency;
    while ((prescaler > 255) && (divisor < 11)) {

        divisor++;
        prescaler = (mck / divisors[divisor]) / frequency;
    }

    // Return result
    if (divisor < 11) {

        TRACE_DEBUG("Found divisor=%u and prescaler=%u for freq=%uHz\n\r",
                  divisors[divisor], prescaler, frequency);
        return prescaler | (divisor << 8);
    }
    else {

        return 0;
    }
}

//------------------------------------------------------------------------------
//         Global functions
//------------------------------------------------------------------------------

//------------------------------------------------------------------------------
/// Configures PWM a channel with the given parameters.
/// The PWM controller must have been clocked in the PMC prior to calling this
/// function. 
/// Beware: this function disables the channel. It waits until disable is effective.
/// \param channel  Channel number.
/// \param prescaler  Channel prescaler.
/// \param alignment  Channel alignment.
/// \param polarity  Channel polarity.
//------------------------------------------------------------------------------
void PWMC_ConfigureChannel(
    unsigned char channel,
    unsigned int prescaler,
    unsigned int alignment,
    unsigned int polarity)
{
    SANITY_CHECK(prescaler < AT91C_PWMC_CPRE_MCKB);
    SANITY_CHECK((alignment & ~AT91C_PWMC_CALG) == 0);
    SANITY_CHECK((polarity & ~AT91C_PWMC_CPOL) == 0);

    // Disable channel (effective at the end of the current period)
    if ((AT91C_BASE_PWMC->PWMC_SR & (1 << channel)) != 0) {
        AT91C_BASE_PWMC->PWMC_DIS = 1 << channel;
        while ((AT91C_BASE_PWMC->PWMC_SR & (1 << channel)) != 0);
    }

    // Configure channel
    AT91C_BASE_PWMC->PWMC_CH[channel].PWMC_CMR = prescaler | alignment | polarity;
}

//------------------------------------------------------------------------------
/// Configures PWM clocks A & B to run at the given frequencies. This function
/// finds the best MCK divisor and prescaler values automatically.
/// \param clka  Desired clock A frequency (0 if not used).
/// \param clkb  Desired clock B frequency (0 if not used).
/// \param mck  Master clock frequency.
//------------------------------------------------------------------------------
void PWMC_ConfigureClocks(unsigned int clka, unsigned int clkb, unsigned int mck)
{
    unsigned int mode = 0;
    unsigned int result;

    // Clock A
    if (clka != 0) {

        result = FindClockConfiguration(clka, mck);
        ASSERT(result != 0, "-F- Could not generate the desired PWM frequency (%uHz)\n\r", clka);
        mode |= result;
    }

    // Clock B
    if (clkb != 0) {

        result = FindClockConfiguration(clkb, mck);
        ASSERT(result != 0, "-F- Could not generate the desired PWM frequency (%uHz)\n\r", clkb);
        mode |= (result << 16);
    }

    // Configure clocks
    TRACE_DEBUG("Setting PWMC_MR = 0x%08X\n\r", mode);
    AT91C_BASE_PWMC->PWMC_MR = mode;
}

//------------------------------------------------------------------------------
/// Sets the period value used by a PWM channel. This function writes directly
/// to the CPRD register if the channel is disabled; otherwise, it uses the
/// update register CUPD.
/// \param channel  Channel number.
/// \param period  Period value.
//------------------------------------------------------------------------------
void PWMC_SetPeriod(unsigned char channel, unsigned short period)
{
    // If channel is disabled, write to CPRD
    if ((AT91C_BASE_PWMC->PWMC_SR & (1 << channel)) == 0) {

        AT91C_BASE_PWMC->PWMC_CH[channel].PWMC_CPRDR = period;
    }
    // Otherwise use update register
    else {

        AT91C_BASE_PWMC->PWMC_CH[channel].PWMC_CMR |= AT91C_PWMC_CPD;
        AT91C_BASE_PWMC->PWMC_CH[channel].PWMC_CUPDR = period;
    }
}

//------------------------------------------------------------------------------
/// Sets the duty cycle used by a PWM channel. This function writes directly to
/// the CDTY register if the channel is disabled; otherwise it uses the
/// update register CUPD.
/// Note that the duty cycle must always be inferior or equal to the channel
/// period.
/// \param channel  Channel number.
/// \param duty  Duty cycle value.
//------------------------------------------------------------------------------
void PWMC_SetDutyCycle(unsigned char channel, unsigned short duty)
{
    SANITY_CHECK(duty <= AT91C_BASE_PWMC->PWMC_CH[channel].PWMC_CPRDR);

    // SAM7S errata
#if defined(at91sam7s16) || defined(at91sam7s161) || defined(at91sam7s32) \
    || defined(at91sam7s321) || defined(at91sam7s64) || defined(at91sam7s128) \
    || defined(at91sam7s256) || defined(at91sam7s512)
    ASSERT(duty > 0, "-F- Duty cycle value 0 is not permitted on SAM7S chips.\n\r");
    ASSERT((duty > 1) || (AT91C_BASE_PWMC->PWMC_CH[channel].PWMC_CMR & AT91C_PWMC_CALG),
           "-F- Duty cycle value 1 is not permitted in left-aligned mode on SAM7S chips.\n\r");
#endif

    // If channel is disabled, write to CDTY
    if ((AT91C_BASE_PWMC->PWMC_SR & (1 << channel)) == 0) {

        AT91C_BASE_PWMC->PWMC_CH[channel].PWMC_CDTYR = duty;
    }
    // Otherwise use update register
    else {

        AT91C_BASE_PWMC->PWMC_CH[channel].PWMC_CMR &= ~AT91C_PWMC_CPD;
        AT91C_BASE_PWMC->PWMC_CH[channel].PWMC_CUPDR = duty;
    }
}

//------------------------------------------------------------------------------
/// Enables the given PWM channel. This does NOT enable the corresponding pin;
/// this must be done in the user code.
/// \param channel  Channel number.
//------------------------------------------------------------------------------
void PWMC_EnableChannel(unsigned char channel)
{
    AT91C_BASE_PWMC->PWMC_ENA = 1 << channel;
}

//------------------------------------------------------------------------------
/// Disables the given PWM channel.
/// Beware, channel will be effectively disabled at the end of the current period.
/// Application can check channel is disabled using the following wait loop:
/// while ((AT91C_BASE_PWMC->PWMC_SR & (1 << channel)) != 0);
/// \param channel  Channel number.
//------------------------------------------------------------------------------
void PWMC_DisableChannel(unsigned char channel)
{
    AT91C_BASE_PWMC->PWMC_DIS = 1 << channel;
}

//------------------------------------------------------------------------------
/// Enables the period interrupt for the given PWM channel.
/// \param channel  Channel number.
//------------------------------------------------------------------------------
void PWMC_EnableChannelIt(unsigned char channel)
{
    AT91C_BASE_PWMC->PWMC_IER = 1 << channel;
}

//------------------------------------------------------------------------------
/// Disables the period interrupt for the given PWM channel.
/// \param channel  Channel number.
//------------------------------------------------------------------------------
void PWMC_DisableChannelIt(unsigned char channel)
{
    AT91C_BASE_PWMC->PWMC_IDR = 1 << channel;
}

