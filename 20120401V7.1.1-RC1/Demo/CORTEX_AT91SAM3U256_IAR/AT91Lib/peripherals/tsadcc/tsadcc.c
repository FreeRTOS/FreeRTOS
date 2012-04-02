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

#include <board.h>

#ifdef AT91C_BASE_TSADC

#include <utility/trace.h>
#include <utility/assert.h>

//------------------------------------------------------------------------------
//         Local variables
//------------------------------------------------------------------------------

/// TSADC clock frequency in Hz.
static unsigned int lAdcclk = 0;

//------------------------------------------------------------------------------
//         Global functions
//------------------------------------------------------------------------------

//------------------------------------------------------------------------------
/// Sets the operating mode of the TSADCC peripheral. The mode value can be
/// one of the following:
/// - AT91C_TSADC_TSAMOD_ADC_ONLY_MODE
/// - AT91C_TSADC_TSAMOD_TS_ONLY_MODE
/// \param mode  Desired mode for the TSADCC.
//------------------------------------------------------------------------------
void TSADCC_SetOperatingMode(unsigned int mode)
{
    SANITY_CHECK(  (mode == AT91C_TSADC_TSAMOD_ADC_ONLY_MODE)
                 | (mode == AT91C_TSADC_TSAMOD_TS_ONLY_MODE));
                 
    AT91C_BASE_TSADC->TSADC_MR = (AT91C_BASE_TSADC->TSADC_MR
                                  & ~AT91C_TSADC_TSAMOD)
                                 | mode;
}

//------------------------------------------------------------------------------
/// Enables or disables the low resolution precision on the TSADC.
/// \param enable  If true, low resolution (8 bit) is used; otherwise the TSADC
///                will use a 10-bit resolution.
//------------------------------------------------------------------------------
void TSADCC_SetLowResolution(unsigned char enable)
{
    if (enable) {
    
        AT91C_BASE_TSADC->TSADC_MR |= AT91C_TSADC_LOWRES;
    }
    else {
    
        AT91C_BASE_TSADC->TSADC_MR &= ~AT91C_TSADC_LOWRES;
    }
}

//------------------------------------------------------------------------------
/// Enables or disable SLEEP mode on the TSADC.
/// \param enable  If true, the TSADC is put into sleep mode; in normal mode
///                otherwise.
//------------------------------------------------------------------------------
void TSADCC_SetSleepMode(unsigned char enable)
{
    if (enable) {
    
        AT91C_BASE_TSADC->TSADC_MR |= AT91C_TSADC_SLEEP;
    }
    else {
    
        AT91C_BASE_TSADC->TSADC_MR &= ~AT91C_TSADC_SLEEP;
    }
}

//------------------------------------------------------------------------------
/// Enables or disables pen detection on the TSADC.
/// \param enable  If true, pen detection is enabled; otherwise it is disabled.
//------------------------------------------------------------------------------
void TSADCC_SetPenDetect(unsigned char enable)
{
    if (enable) {
    
        AT91C_BASE_TSADC->TSADC_MR |= AT91C_TSADC_PENDET;
    }
    else {
        
        AT91C_BASE_TSADC->TSADC_MR &= ~AT91C_TSADC_PENDET;
    }
}

//------------------------------------------------------------------------------
/// Sets the TSADC clock to the desired frequency. The prescaler is calculated
/// by this function so the resulting frequency is equal or inferior to the
/// desired one.
/// \param adcclk  Desired ADC clock frequency in Hz.
/// \param mck  Master clock frequency in Hz.
//------------------------------------------------------------------------------
void TSADCC_SetAdcFrequency(unsigned int adcclk, unsigned int mck)
{
    unsigned int prescal;
    
    // Formula for PRESCAL is:
    // PRESCAL = (MCK / (2 * ADCCLK)) + 1
    // First, we do the division, multiplied by 10 to get higher precision
    // If the last digit is not zero, we round up to avoid generating a higher
    // than required frequency.
    prescal = (mck * 5) / adcclk;
    if ((prescal % 10) > 0) {
    
        prescal = (prescal / 10);
    }
    else {
    
        SANITY_CHECK((prescal / 10) != 0);
        prescal = (prescal / 10) - 1;
    }
    SANITY_CHECK((prescal & ~0x3F) == 0);
    
    AT91C_BASE_TSADC->TSADC_MR = (  AT91C_BASE_TSADC->TSADC_MR
                                  & ~AT91C_TSADC_PRESCAL)
                                 | (prescal << 8);
                                 
    // Save clock frequency for further timing calculations
    lAdcclk = adcclk;
}

//------------------------------------------------------------------------------
/// Sets the TSADC startup time. This function relies on the ADCCLK frequency
/// that has been set using TSADCC_SetAdcFrequency(), so it must have been
/// called first.
/// \param time  Startup time in µseconds.
//------------------------------------------------------------------------------
void TSADCC_SetStartupTime(unsigned int time)
{
    unsigned int startup;
    
    SANITY_CHECK(lAdcclk != 0);
        
    // Formula for STARTUP is:
    // STARTUP = (time x ADCCLK) / (1000000 x 8) - 1
    // Division multiplied by 10 for higher precision
    startup = (time * lAdcclk) / (800000);
    if ((startup % 10) > 0) {
    
        startup /= 10;
    }
    else {
    
        startup /= 10;
        if (startup > 0) {
        
            startup--;
        }
    }
    
    SANITY_CHECK((startup & ~0x7F) == 0);
    AT91C_BASE_TSADC->TSADC_MR = (  AT91C_BASE_TSADC->TSADC_MR
                                  & ~AT91C_TSADC_STARTUP)
                                 | (startup << 16);
}

//------------------------------------------------------------------------------
/// Sets the TSADC track and hold time. This function relies on the ADCCLK
/// frequency that has been set with TSADCC_SetAdcFrequency(), to it must be
/// called first.
/// This function also sets the track and hold time in the TSADC_TSR register.
/// \param time  Track and hold time in nanoseconds.
//------------------------------------------------------------------------------
void TSADCC_SetTrackAndHoldTime(unsigned int time)
{
    unsigned int shtim;
    
    SANITY_CHECK(lAdcclk != 0);
    
    // Formula for SHTIM:
    // SHTIM = (time x ADCCLK) / 1000000000 - 1
    // Since 1 billion is close to the maximum value for an integer, we first
    // divide ADCCLK by 1000 to avoid an overflow
    shtim = (time * (lAdcclk / 1000)) / 100000;
    if ((shtim % 10) > 0) {
    
        shtim /= 10;
    }
    else {
    
        shtim /= 10;
        if (shtim > 0) shtim--;
    }
    
    SANITY_CHECK((shtim & ~0xF) == 0);
    AT91C_BASE_TSADC->TSADC_MR = (  AT91C_BASE_TSADC->TSADC_MR
                                  & ~AT91C_TSADC_SHTIM)
                                 | (shtim << 24);
    AT91C_BASE_TSADC->TSADC_TSR = shtim << 24;
}

//------------------------------------------------------------------------------
/// Sets the TSADC debounce time. This function relies on the ADCCLK
/// frequency that has been set with TSADCC_SetAdcFrequency(), to it must be
/// called first.
/// \param time  Debounce time in nanoseconds (cannot be 0).
//------------------------------------------------------------------------------
void TSADCC_SetDebounceTime(unsigned int time)
{
    unsigned int divisor = 1000000000;
    unsigned int clock = lAdcclk;
    unsigned int pendbc = 0;
    unsigned int targetValue;
    unsigned int currentValue;
    
    SANITY_CHECK(lAdcclk != 0);
    SANITY_CHECK(time != 0);
    
    // Divide time & ADCCLK first to avoid overflows
    while ((divisor > 1) && ((time % 10) == 0)) {
    
        time /= 10;
        divisor /= 10;
    }
    while ((divisor > 1) && ((clock % 10) == 0)) {
    
        clock /= 10;
        divisor /= 10;
    }
    
    // Compute PENDBC value
    targetValue = time * clock / divisor;
    currentValue = 1;
    while (currentValue < targetValue) {
    
        pendbc++;
        currentValue *= 2;
    }
    
    SANITY_CHECK((pendbc & ~0xF) == 0);
    AT91C_BASE_TSADC->TSADC_MR = (  AT91C_BASE_TSADC->TSADC_MR
                                  & ~AT91C_TSADC_PENDBC)
                                 | (pendbc << 28);
}

//------------------------------------------------------------------------------
/// Sets the trigger mode of the TSADCC to one of the following values:
/// - AT91C_TSADC_TRGMOD_NO_TRIGGER
/// - AT91C_TSADC_TRGMOD_EXTERNAL_TRIGGER_RE
/// - AT91C_TSADC_TRGMOD_EXTERNAL_TRIGGER_FE
/// - AT91C_TSADC_TRGMOD_EXTERNAL_TRIGGER_AE
/// - AT91C_TSADC_TRGMOD_PENDET_TRIGGER
/// - AT91C_TSADC_TRGMOD_PERIODIC_TRIGGER
/// - AT91C_TSADC_TRGMOD_CONT_TRIGGER
/// \param mode  Trigger mode.
//------------------------------------------------------------------------------
void TSADCC_SetTriggerMode(unsigned int mode)
{
    SANITY_CHECK(((mode & ~AT91C_TSADC_TRGMOD) == 0)
                 | ((mode & AT91C_TSADC_TRGMOD) != 0x7));
    
    AT91C_BASE_TSADC->TSADC_TRGR = (AT91C_BASE_TSADC->TSADC_TRGR
                                    & ~AT91C_TSADC_TRGMOD)
                                   | mode;
}

//------------------------------------------------------------------------------
/// Sets the trigger period when using the TSADCC in periodic trigger mode.
/// As usual, this function requires TSADCC_SetAdcFrequency() to be called
/// before it.
/// \param period  Trigger period in nanoseconds.
//------------------------------------------------------------------------------
void TSADCC_SetTriggerPeriod(unsigned int period)
{
    unsigned int trgper;
    unsigned int divisor = 100000000;
    
    while ((period >= 10) && (divisor >= 10)) {
    
        period /= 10;
        divisor /= 10;
    }
    
    trgper = (period * lAdcclk) / divisor;
    if ((trgper % 10) > 0) {
    
        trgper /= 10;
    }
    else {
    
        trgper /= 10;
        if (trgper > 0) trgper--;
    }
    
    SANITY_CHECK((trgper & ~0xFFFF) == 0);
    AT91C_BASE_TSADC->TSADC_TRGR = (AT91C_BASE_TSADC->TSADC_TRGR
                                    & ~AT91C_TSADC_TRGPER)
                                   | (trgper << 16);
}

#endif //#ifdef AT91C_BASE_TSADC
