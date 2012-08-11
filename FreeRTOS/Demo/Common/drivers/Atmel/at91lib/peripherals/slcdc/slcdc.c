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

#include "slcdc.h"
#include <board.h>
#include <utility/assert.h>

#include <string.h>

//------------------------------------------------------------------------------
//         Local definitions
//------------------------------------------------------------------------------

/// Size of SLCDC buffer in bytes.
#define BUFFER_SIZE     320

//------------------------------------------------------------------------------
//         Global functions
//------------------------------------------------------------------------------

//------------------------------------------------------------------------------
/// Initializes the Segment LCD controller.
/// \param commons  Number of commons used by the display.
/// \param segments  Number of segments used by the display.
/// \param bias  Bias value.
/// \param timeSetting  Buffer timing value.
//------------------------------------------------------------------------------
void SLCDC_Configure(
    unsigned int commons,
    unsigned int segments,
    unsigned int bias,
    unsigned int timeSetting)
{
    SANITY_CHECK((commons > 0) && (commons <= 10));
    SANITY_CHECK((segments > 0) && (segments <= 40));
    SANITY_CHECK((bias & ~AT91C_SLCDC_BIAS) == 0);
	SANITY_CHECK((timeSetting & ~(0xF << 16)) == 0);  
    SANITY_CHECK((timeSetting >> 16) < 0x0A);

    // Enable peripheral clock
    AT91C_BASE_PMC->PMC_PCER = 1 << AT91C_ID_SLCD;
    AT91C_BASE_SLCDC->SLCDC_MR = (commons - 1) | ((segments - 1) << 8) | bias | timeSetting;
}

//------------------------------------------------------------------------------
/// Clears the SLCD display buffer.
//------------------------------------------------------------------------------
void SLCDC_Clear(void)
{
    memset((void *) AT91C_BASE_SLCDC->SLCDC_MEM, 0, BUFFER_SIZE);
}

//------------------------------------------------------------------------------
/// Enables the SLCD controller.
//------------------------------------------------------------------------------
void SLCDC_Enable(void)
{
    AT91C_BASE_SLCDC->SLCDC_CR = AT91C_SLCDC_LCDEN;
    while (AT91C_BASE_SLCDC -> SLCDC_SR != AT91C_SLCDC_ENA);
}

//------------------------------------------------------------------------------
/// Disables the SLCD controller.
//------------------------------------------------------------------------------
void SLCDC_Disable(void)
{
    AT91C_BASE_SLCDC->SLCDC_CR = AT91C_SLCDC_LCDDIS;
}

//------------------------------------------------------------------------------
/// Enables the SLCD low power mode.
//------------------------------------------------------------------------------
void SLCDC_EnableLowPowerMode(void)
{
    unsigned int value;

    value = AT91C_BASE_SLCDC->SLCDC_MR;
    value &= ~AT91C_SLCDC_LPMODE;
    value |=AT91C_SLCDC_LPMODE;
    AT91C_BASE_SLCDC->SLCDC_MR = value;
}
 
//------------------------------------------------------------------------------
/// Disables the SLCD low power mode
//------------------------------------------------------------------------------
void SLCDC_DisableLowPowerMode(void)
{
    unsigned int value;

    value = AT91C_BASE_SLCDC->SLCDC_MR;
    value &= ~AT91C_SLCDC_LPMODE;
    AT91C_BASE_SLCDC->SLCDC_MR = value;
}

//------------------------------------------------------------------------------
/// Adjusts the frame frequency. Frequency = FsCLK / (prescaler * divider . NCOM)
/// \param prescalerValue  Prescaler value
/// \param dividerValue  Divider value
//------------------------------------------------------------------------------
void SLCDC_SetFrameFreq(unsigned int prescalerValue, unsigned int dividerValue)
{
    SANITY_CHECK((prescalerValue & ~AT91C_SLCDC_PRESC) == 0);
    SANITY_CHECK((dividerValue & (~(0x07 << 8))) == 0);

    AT91C_BASE_SLCDC->SLCDC_FRR = prescalerValue | dividerValue;
}

//------------------------------------------------------------------------------
/// Sets the display mode (normal/force off/force on/blinking).
/// \param mode  Display mode to be set
//------------------------------------------------------------------------------
void SLCDC_SetDisplayMode(unsigned int mode)
{
    unsigned int value;

    SANITY_CHECK(mode < 8);
           
    value = AT91C_BASE_SLCDC->SLCDC_DR;
    value &= ~AT91C_SLCDC_DISPMODE;
    value |= mode;
    AT91C_BASE_SLCDC->SLCDC_DR = value;
}

//------------------------------------------------------------------------------
/// Adjusts the display blinking frequency.
/// Blinking frequency = Frame Frequency / LCDBLKFREQ.
/// \param frequency  Frequency value.
//------------------------------------------------------------------------------
void SLCDC_SetBlinkFreq(unsigned int frequency)
{
    unsigned int value;

    SANITY_CHECK((frequency & ~(0xFF << 8)) == 0);

    value = AT91C_BASE_SLCDC->SLCDC_DR;
    value &= ~AT91C_SLCDC_BLKFREQ;
    value |= frequency;           
    AT91C_BASE_SLCDC->SLCDC_DR = frequency;
}

//------------------------------------------------------------------------------
/// Enables the selected SLCDC interrupt sources.
/// \param sources  Interrupt sources to enable.
//------------------------------------------------------------------------------
void SLCDC_EnableInterrupts(unsigned int sources)
{
    SANITY_CHECK((sources & 0xFFFFFFFA) == 0);

    AT91C_BASE_SLCDC->SLCDC_IER = sources;
}

//------------------------------------------------------------------------------
/// Disables the selected SLCDC interrupt sources.
/// \param sources  Interrupt sources to disable.
//------------------------------------------------------------------------------
void SLCDC_DisableInterrupts(unsigned int sources)
{
    SANITY_CHECK((sources & 0xFFFFFFFA) == 0);

    AT91C_BASE_SLCDC->SLCDC_IDR = sources;
}

