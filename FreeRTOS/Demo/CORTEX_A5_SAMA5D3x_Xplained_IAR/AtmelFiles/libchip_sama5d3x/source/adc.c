/* ----------------------------------------------------------------------------
 *         SAM Software Package License
 * ----------------------------------------------------------------------------
 * Copyright (c) 2012, Atmel Corporation
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

/** \addtogroup adc_module Working with ADC
 * \ingroup peripherals_module
 * The ADC driver provides the interface to configure and use the ADC peripheral.
 * \n
 *
 * It converts the analog input to digital format. The converted result could be
 * 12bit or 10bit. The ADC supports up to 16 analog lines.
 *
 * To Enable a ADC conversion,the user has to follow these few steps:
 * <ul>
 * <li> Select an appropriate reference voltage on ADVREF   </li>
 * <li> Configure the ADC according to its requirements and special needs,which
 * could be  broken down into several parts:
 * -#   Select the resolution by setting or clearing ADC_MR_LOWRES bit in
 *      ADC_MR (Mode Register)
 * -#   Set ADC clock by setting ADC_MR_PRESCAL bits in ADC_MR, the clock is
 *      calculated with ADCClock = MCK / ( (PRESCAL+1) * 2 )
 * -#   Set Startup Time,Tracking Clock cycles and Transfer Clock respectively
 *      in ADC_MR.
 </li>
 * <li> Start conversion by setting ADC_CR_START in ADC_CR. </li>
 * </ul>
 *
 * For more accurate information, please look at the ADC section of the
 * Datasheet.
 *
 * Related files :\n
 * \ref adc.c\n
 * \ref adc.h\n
 */
/*@{*/
/*@}*/
/**
 * \file
 *
 * Implementation of Analog-to-Digital Converter (ADC).
 *
 */
/*----------------------------------------------------------------------------
 *        Headers
 *----------------------------------------------------------------------------*/

#include "chip.h"


/*----------------------------------------------------------------------------
 *        Local variables
 *----------------------------------------------------------------------------*/

/** Current working clock */
static uint32_t dwAdcClock = 0;

/*----------------------------------------------------------------------------
 *        Exported functions
 *----------------------------------------------------------------------------*/

/**
 * \brief Initialize the ADC controller
 *
 * \param pAdc Pointer to an Adc instance.
 * \param dwID ADC Index
 */
extern void ADC_Initialize( Adc* pAdc, uint32_t dwID )
{
    /* Enable peripheral clock*/
    PMC_EnablePeripheral(dwID);

    /*  Reset the controller */
    pAdc->ADC_CR = ADC_CR_SWRST;

    /* Reset Mode Register */
    pAdc->ADC_MR = 0;

}

/**
 * \brief Set ADC clock.
 *
 * \param pAdc Pointer to an Adc instance.
 * \param dwPres prescal value
 * \param dwMck Board MCK (Hz)
 *
 * \return ADC clock
 */

extern uint32_t ADC_SetClock( Adc* pAdc, uint32_t dwClk, uint32_t dwMck )
{ 
    uint32_t dwPres, dwMr;
    /* Formula for PRESCAL is:
       PRESCAL = (MCK / (2 * ADCCLK)) + 1
       First, we do the division, multiplied by 10 to get higher precision
       If the last digit is not zero, we round up to avoid generating a higher
       than required frequency. */
    dwPres = (dwMck * 5) / dwClk;
    if (dwPres % 10) dwPres = dwPres / 10;
    else
    {
        if (dwPres == 0) return 0;
        dwPres = dwPres / 10 - 1;
    }

    dwMr = ADC_MR_PRESCAL(dwPres);
    if (dwMr == 0) return 0;

    dwMr |= (pAdc->ADC_MR & ~ADC_MR_PRESCAL_Msk);
    pAdc->ADC_MR = dwMr;

    dwAdcClock = dwMck / (dwPres + 1) / 2;
    //dwAdcClock = dwAdcClock / 1000 * 1000;
    return dwAdcClock;
}

/**
 * \brief Set ADC timing.
 *
 * \param pAdc Pointer to an Adc instance.
 * \param dwStartup startup value
 * \param dwTracking tracking value
 * \param dwSettling settling value
 */
extern void ADC_SetTiming( Adc* pAdc, uint32_t dwStartup, uint32_t dwTracking, uint32_t dwSettling )
{
    uint32_t dwMr;

    dwMr = pAdc->ADC_MR;
    dwMr &= (~ADC_MR_STARTUP_Msk) & (~ADC_MR_TRACKTIM_Msk) & (~ADC_MR_SETTLING_Msk);

    /* Formula:
     *     Startup  Time = startup value / ADCClock
     *     Transfer Time = (TRANSFER * 2 + 3) / ADCClock
     *     Tracking Time = (TRACKTIM + 1) / ADCClock
     *     Settling Time = settling value / ADCClock
     */
    dwMr |= dwStartup | dwTracking | dwSettling;
    pAdc->ADC_MR |= dwMr;
}

/**
 * \brief Set ADC trigger.
 *
 * \param pAdc Pointer to an Adc instance.
 * \param dwTrgSel Trigger selection
 */
extern void ADC_SetTrigger( Adc* pAdc, uint32_t dwTrgSel )
{
    uint32_t dwMr;

    dwMr = pAdc->ADC_MR;
    dwMr &= ~ADC_MR_TRGSEL_Msk;
    dwMr |= dwTrgSel;
    pAdc->ADC_MR |= dwMr;
}

/**
 * Sets the trigger mode to following:
 * - \ref ADC_TRGR_TRGMOD_NO_TRIGGER
 * - \ref ADC_TRGR_TRGMOD_EX_TRIG_RISE
 * - \ref ADC_TRGR_TRGMOD_EX_TRIG_FALL
 * - \ref ADC_TRGR_TRGMOD_EX_TRIG_ANY
 * - \ref ADC_TRGR_TRGMOD_PEN_TIRG
 * - \ref ADC_TRGR_TRGMOD_PERID_TRIG
 * - \ref ADC_TRGR_TRGMOD_CONTINUOUS
 * \param pAdc   Pointer to an Adc instance.
 * \param dwMode Trigger mode.
 */
void ADC_SetTriggerMode(Adc *pAdc, uint32_t dwMode)
{
    uint32_t dwTrgr = pAdc->ADC_TRGR & ~ADC_TRGR_TRGMOD_Msk;
    pAdc->ADC_TRGR = dwTrgr | dwMode;
}

/**
 * \brief Enable/Disable low resolution.
 *
 * \param pAdc Pointer to an Adc instance.
 * \param bEnDis Enable/Disable low resolution.
 */
extern void ADC_SetLowResolution( Adc* pAdc, uint32_t bEnDis )
{
    if ( bEnDis )
    {
        pAdc->ADC_MR |= ADC_MR_LOWRES;
    }
    else
    {
        pAdc->ADC_MR &= ~ADC_MR_LOWRES;
    }
}

/**
 * \brief Enable/Disable sleep mode.
 *
 * \param pAdc Pointer to an Adc instance.
 * \param bEnDis Enable/Disable sleep mode.
 */
extern void ADC_SetSleepMode( Adc *pAdc, uint8_t bEnDis )
{
    if ( bEnDis )
    {
        pAdc->ADC_MR |=  ADC_MR_SLEEP;
    }
    else
    {
        pAdc->ADC_MR &= ~ADC_MR_SLEEP;
    }
}

/**
 * \brief Enable/Disable fast wake up.
 *
 * \param pAdc Pointer to an Adc instance.
 * \param bEnDis Enable/Disable fast wake up in sleep mode.
 */
extern void ADC_SetFastWakeup( Adc *pAdc, uint8_t bEnDis )
{
    if ( bEnDis )
    {
        pAdc->ADC_MR |=  ADC_MR_FWUP;
    }
    else
    {
        pAdc->ADC_MR &= ~ADC_MR_FWUP;
    }
}

/**
 * \brief Enable/Disable seqnence mode.
 *
 * \param pAdc  Pointer to an Adc instance.
 * \param bEnDis Enable/Disable seqnence mode.
 */
extern void ADC_SetSequenceMode( Adc *pAdc, uint8_t bEnDis )
{
    if ( bEnDis )
    {
        /* User Sequence Mode: The sequence respects what is defined in
        ADC_SEQR1 and ADC_SEQR2 */
        pAdc->ADC_MR |=  ADC_MR_USEQ;
    }
    else
    {
        /* Normal Mode: The controller converts channels in a simple numeric order. */
        pAdc->ADC_MR &= ~ADC_MR_USEQ;
    }
}

/**
 * \brief Set channel sequence.
 *
 * \param pAdc   Pointer to an Adc instance.
 * \param dwSEQ1 Sequence 1 ~ 8  channel number.
 * \param dwSEQ2 Sequence 9 ~ 16 channel number.
 */
extern void ADC_SetSequence( Adc *pAdc, uint32_t dwSEQ1, uint32_t dwSEQ2 )
{
    pAdc->ADC_SEQR1 = dwSEQ1;
    pAdc->ADC_SEQR2 = dwSEQ2;
}

/**
 * \brief Set channel sequence by given channel list.
 *
 * \param pAdc    Pointer to an Adc instance.
 * \param ucChList Channel list.
 * \param ucNumCh  Number of channels in list.
 */
extern void ADC_SetSequenceByList( Adc *pAdc, uint8_t ucChList[], uint8_t ucNumCh )
{
    uint8_t i;
    uint8_t ucShift;

    pAdc->ADC_SEQR1 = 0;
    for (i = 0, ucShift = 0; i < 8; i ++, ucShift += 4)
    {
        if (i >= ucNumCh) return;
        pAdc->ADC_SEQR1 |= ucChList[i] << ucShift;

    }
    pAdc->ADC_SEQR2 = 0;
    for (ucShift = 0; i < 16; i ++, ucShift += 4)
    {
        if (i >= ucNumCh) return;
        pAdc->ADC_SEQR2 |= ucChList[i] << ucShift;
    }
}

/**
 * \brief Set analog change.
 * IF enabled, it allows different analog settings for each channel,
 * otherwise, DIFF0, GAIN0 and OFF0 are used for all channels.
 *
 * \param pAdc   Pointer to an Adc instance.
 * \param bEnDis Enable/Disable.
 */
extern void ADC_SetAnalogChange( Adc *pAdc, uint8_t bEnDis )
{
    if ( bEnDis )
    {
        pAdc->ADC_MR |=  ADC_MR_ANACH;
    }
    else
    {
        pAdc->ADC_MR &= ~ADC_MR_ANACH;
    }
}

/**
 * \brief Set "TAG" mode, show channel number in last data or not.
 *
 * \param pAdc   Pointer to an Adc instance.
 * \param bEnDis Enable/Disable TAG value.
 */
extern void ADC_SetTagEnable( Adc *pAdc, uint8_t bEnDis )
{
    if ( bEnDis )
    {
        pAdc->ADC_EMR |=  ADC_EMR_TAG;
    }
    else
    {
        pAdc->ADC_EMR &= ~ADC_EMR_TAG;
    }
}

/**
 * \brief Set compare channel.
 *
 * \param pAdc Pointer to an Adc instance.
 * \param dwChannel channel number to be set,16 for all channels
 */
extern void ADC_SetCompareChannel( Adc* pAdc, uint32_t dwChannel )
{
    assert( dwChannel <= 16 ) ;

    if ( dwChannel < 16 )
    {
        pAdc->ADC_EMR &= ~(ADC_EMR_CMPALL);
        pAdc->ADC_EMR &= ~(ADC_EMR_CMPSEL_Msk);
        pAdc->ADC_EMR |= (dwChannel << ADC_EMR_CMPSEL_Pos);
    }
    else
    {
        pAdc->ADC_EMR |= ADC_EMR_CMPALL;
    }
}

/**
 * \brief Set compare mode.
 *
 * \param pAdc Pointer to an Adc instance.
 * \param dwMode compare mode
 */
extern void ADC_SetCompareMode( Adc* pAdc, uint32_t dwMode )
{
    pAdc->ADC_EMR &= ~(ADC_EMR_CMPMODE_Msk);
    pAdc->ADC_EMR |= (dwMode & ADC_EMR_CMPMODE_Msk);
}

/**
 * \brief Set comparsion window.
 *
 * \param pAdc Pointer to an Adc instance.
 * \param dwHi_Lo Comparison Window
 */
extern void ADC_SetComparisonWindow( Adc* pAdc, uint32_t dwHi_Lo )
{
    pAdc->ADC_CWR = dwHi_Lo ;
}

/**
 * \brief Get startup value.
 */
static uint32_t GetStartupValue( uint32_t dwStartup )
{
    uint32_t dwStartupValue = 0;

    if( dwStartup == 0 )
        dwStartupValue = 0;
    else if( dwStartup == 1 )
        dwStartupValue = 8;
    else if( dwStartup == 2 )
        dwStartupValue = 16;
    else if( dwStartup == 3 )
        dwStartupValue = 24;
    else if( dwStartup == 4 )
        dwStartupValue = 64;
    else if( dwStartup == 5 )
        dwStartupValue = 80;
    else if( dwStartup == 6 )
        dwStartupValue = 96;
    else if( dwStartup == 7 )
        dwStartupValue = 112;
    else if( dwStartup == 8 )
        dwStartupValue = 512;
    else if( dwStartup == 9 )
        dwStartupValue = 576;
    else if( dwStartup == 10 )
        dwStartupValue = 640;
    else if( dwStartup == 11 )
        dwStartupValue = 704;
    else if( dwStartup == 12 )
        dwStartupValue = 768;
    else if( dwStartup == 13 )
        dwStartupValue = 832;
    else if( dwStartup == 14 )
        dwStartupValue = 896;
    else if( dwStartup == 15 )
        dwStartupValue = 960;

    return dwStartupValue;
}

/**
 * \brief Check if ADC configuration is right.
 *
 * \param pAdc Pointer to an Adc instance.
 * \param dwMck Board MCK (Hz)
 *
 * \return 0 if check ok, others if not ok.
 */
extern uint8_t ADC_CheckConfiguration( Adc* pAdc, uint32_t dwMck )
{
    uint8_t  bOk = 0;
    uint32_t dwMr;
    uint32_t dwPres;
    uint32_t dwStartup;
    uint32_t dwClock;
    uint32_t dwTemp;

    dwMr = pAdc->ADC_MR;

    dwPres = (dwMr & ADC_MR_PRESCAL_Msk) >> ADC_MR_PRESCAL_Pos;
    /* Formula: ADCClock = MCK / ( (PRESCAL+1) * 2 ) */
    dwClock = dwMck / ( (dwPres + 1) * 2 );
    if (dwClock > ADC_CLOCK_MAX)
    {
        printf("ADC clock is too high (out of specification: %d Hz)\r\n", (int)ADC_CLOCK_MAX);
        bOk = 1;
    }

    dwStartup = (dwMr & ADC_MR_STARTUP_Msk) >> ADC_MR_STARTUP_Pos;
    if (dwMr & ADC_MR_SLEEP_SLEEP)
    {
        if( pAdc->ADC_MR & ADC_MR_FWUP_ON )
        {
            /* Fast Wake Up Sleep Mode: 12µs */
            dwTemp = ADC_STARTUP_FAST_MAX * dwClock / 1000000;
            if( dwTemp > GetStartupValue(dwStartup) )
            {
                printf("Startup time too small: %d, programmed: %d\r\n", (int)dwTemp, (int)(GetStartupValue(dwStartup)));
                bOk = 1;
            }
        }
    }

    return bOk;
}

/**
 * \brief Return the Channel Converted Data
 *
 * \param pAdc Pointer to an Adc instance.
 * \param dwChannel channel to get converted value
 */
extern uint32_t ADC_GetConvertedData( Adc* pAdc, uint32_t dwChannel )
{
    uint32_t dwData = 0;

    assert( dwChannel < 16 ) ;

    dwData = pAdc->ADC_CDR[dwChannel];

    return dwData ;
}


/**
 * Sets the ADC startup time.
 * \param pAdc  Pointer to an Adc instance.
 * \param dwUs  Startup time in uS.
 */
void ADC_SetStartupTime( Adc *pAdc, uint32_t dwUs )
{
    uint32_t dwStart;
    uint32_t dwMr;

    if (dwAdcClock == 0) return;
    /* Formula for STARTUP is:
       STARTUP = (time x ADCCLK) / (1000000) - 1
       Division multiplied by 10 for higher precision */
    
    dwStart = (dwUs * dwAdcClock) / (100000);
    if (dwStart % 10) dwStart /= 10;
    else
    {
        dwStart /= 10;
        if (dwStart) dwStart --;
    }
    if      (dwStart >  896) dwMr = ADC_MR_STARTUP_SUT960;
    else if (dwStart >  832) dwMr = ADC_MR_STARTUP_SUT896;
    else if (dwStart >  768) dwMr = ADC_MR_STARTUP_SUT832;
    else if (dwStart >  704) dwMr = ADC_MR_STARTUP_SUT768;
    else if (dwStart >  640) dwMr = ADC_MR_STARTUP_SUT704;
    else if (dwStart >  576) dwMr = ADC_MR_STARTUP_SUT640;
    else if (dwStart >  512) dwMr = ADC_MR_STARTUP_SUT576;
    else if (dwStart >  112) dwMr = ADC_MR_STARTUP_SUT512;
    else if (dwStart >   96) dwMr = ADC_MR_STARTUP_SUT112;
    else if (dwStart >   80) dwMr = ADC_MR_STARTUP_SUT96;
    else if (dwStart >   64) dwMr = ADC_MR_STARTUP_SUT80;
    else if (dwStart >   24) dwMr = ADC_MR_STARTUP_SUT64;
    else if (dwStart >   16) dwMr = ADC_MR_STARTUP_SUT24;
    else if (dwStart >    8) dwMr = ADC_MR_STARTUP_SUT16;
    else if (dwStart >    0) dwMr = ADC_MR_STARTUP_SUT8;
    else                     dwMr = ADC_MR_STARTUP_SUT0;

    dwMr |= pAdc->ADC_MR & ~ADC_MR_STARTUP_Msk;
    pAdc->ADC_MR = dwMr;
}


/**
 * Set ADC tracking time
 * \param pAdc  Pointer to an Adc instance.
 * \param dwNs  Tracking time in nS.
 */
void ADC_SetTrackingTime( Adc *pAdc, uint32_t dwNs )
{
    uint32_t dwShtim;
    uint32_t dwMr;

    if (dwAdcClock == 0) return;
    /* Formula for SHTIM is:
       SHTIM = (time x ADCCLK) / (1000000000) - 1
       Since 1 billion is close to the maximum value for an integer, we first
       divide ADCCLK by 1000 to avoid an overflow */
    dwShtim = (dwNs * (dwAdcClock / 1000)) / 100000;
    if (dwShtim % 10) dwShtim /= 10;
    else
    {
        dwShtim /= 10;
        if (dwShtim) dwShtim --;
    }
    dwMr  = ADC_MR_TRACKTIM(dwShtim);
    dwMr |= pAdc->ADC_MR & ~ADC_MR_TRACKTIM_Msk;
    pAdc->ADC_MR = dwMr;
}


/**
 * Sets the trigger period.
 * \param pAdc   Pointer to an Adc instance.
 * \param dwPeriod Trigger period in nS.
 */
void ADC_SetTriggerPeriod(Adc *pAdc, uint32_t dwPeriod)
{
    uint32_t dwTrgper;
    uint32_t dwDiv = 100000000;
    uint32_t dwTrgr;
    if (dwAdcClock == 0) return;
    while (dwPeriod >= 10 && dwDiv >= 10)
    {
        dwPeriod /= 10; dwDiv /= 10;
    }
    dwTrgper = (dwPeriod * dwAdcClock) / dwDiv;
    if (dwTrgper % 10) dwTrgper /= 10;
    else
    {
        dwTrgper /= 10;
        if (dwTrgper) dwTrgper --;
    }
    dwTrgr = ADC_TRGR_TRGPER(dwTrgper);
    dwTrgr |= pAdc->ADC_TRGR & ~ADC_TRGR_TRGPER_Msk;
    pAdc->ADC_TRGR = dwTrgr;
}


/**
 * Start screen calibration (VDD/GND measurement)
 * \param pAdc Pointer to an Adc instance.
 */
void ADC_TsCalibration( Adc *pAdc )
{
    pAdc->ADC_CR = ADC_CR_TSCALIB;
}

/**
 * Sets the operation mode of the touch screen ADC. The mode can be:
 * - \ref ADC_TSMR_TSMODE_NONE (TSADC off)
 * - \ref ADC_TSMR_TSMODE_4_WIRE_NO_PM
 * - \ref ADC_TSMR_TSMODE_4_WIRE (CH 0~3 used)
 * - \ref ADC_TSMR_TSMODE_5_WIRE (CH 0~4 used)
 * \param pADC   Pointer to an Adc instance.
 * \param dwMode Desired mode
 */
void ADC_SetTsMode(Adc* pADC, uint32_t dwMode)
{
    pADC->ADC_TSMR = (pADC->ADC_TSMR & ~ADC_TSMR_TSMODE_Msk) | dwMode;
}

/**
 * Sets the touchscreen pan debounce time.
 * \param pADC   Pointer to an Adc instance.
 * \param dwTime Debounce time in nS.
 */
void ADC_SetTsDebounce(Adc *pADC, uint32_t dwTime)
{
    uint32_t dwDiv = 1000000000;
    uint32_t dwClk = dwAdcClock;
    uint32_t dwPenbc = 0;
    uint32_t dwTarget, dwCurrent;
    uint32_t dwTsmr;
    if (dwTime == 0 || dwAdcClock == 0) return;
    /* Divide time & ADCCLK to avoid overflows */
    while ((dwDiv > 1) && ((dwTime % 10) == 0))
    {
        dwTime /= 10; dwDiv /= 10;
    }
    while ((dwDiv > 1) && ((dwClk & 10) == 0))
    {
        dwClk /= 10; dwDiv /= 10;
    }
    /* Compute PENDBC */
    dwTarget = dwTime * dwClk / dwDiv;
    dwCurrent = 1;
    while (dwCurrent < dwTarget)
    {
        dwPenbc ++; dwCurrent *= 2;
    }
    dwTsmr = ADC_TSMR_PENDBC(dwPenbc);
    if (dwTsmr == 0) return;
    dwTsmr |= pADC->ADC_TSMR & ~ADC_TSMR_PENDBC_Msk;
    pADC->ADC_TSMR = dwTsmr;
}

/**
 * Enable/Disable touch screen pen detection.
 * \param pADC   Pointer to an Adc instance.
 * \param bEnDis If true, pen detection is enabled;
 *               in normal mode otherwise.
 */
void ADC_SetTsPenDetect(Adc* pADC, uint8_t bEnDis)
{
    if (bEnDis)
        pADC->ADC_TSMR |=  ADC_TSMR_PENDET;
    else
        pADC->ADC_TSMR &= ~ADC_TSMR_PENDET;
}


/**
 * Sets the average of the touch screen ADC. The mode can be:
 * - \ref ADC_TSMR_TSAV_NO_FILTER (No filtering)
 * - \ref ADC_TSMR_TSAV_AVG2CONV (Average 2 conversions)
 * - \ref ADC_TSMR_TSAV_AVG4CONV (Average 4 conversions)
 * - \ref ADC_TSMR_TSAV_AVG8CONV (Average 8 conversions)
 * \param pADC   Pointer to an Adc instance.
 * \param dwMode Desired mode
 */
void ADC_SetTsAverage(Adc* pADC, uint32_t dwAvg2Conv)
{
    uint32_t dwMr = pADC->ADC_TSMR & ~ADC_TSMR_TSAV_Msk;
    uint32_t dwTSAV = dwAvg2Conv >> ADC_TSMR_TSAV_Pos;
    uint32_t dwTSFREQ = (dwMr & ADC_TSMR_TSFREQ_Msk) >> ADC_TSMR_TSFREQ_Pos;
    if (dwTSAV)
    {
        if (dwTSAV > dwTSFREQ)
        {
            dwMr &= ~ADC_TSMR_TSFREQ_Msk;
            dwMr |=  ADC_TSMR_TSFREQ(dwTSAV);
        }
    }
    pADC->ADC_TSMR = dwMr | dwAvg2Conv;
}

/**
 * Return X measurement position value.
 * \param pADC   Pointer to an Adc instance.
 */
uint32_t ADC_GetTsXPosition(Adc *pADC)
{
    return pADC->ADC_XPOSR;
}

/**
 * Return Y measurement position value.
 * \param pADC   Pointer to an Adc instance.
 */
uint32_t ADC_GetTsYPosition(Adc *pADC)
{
    return pADC->ADC_YPOSR;
}

/**
 * Return Z measurement position value.
 * \param pADC   Pointer to an Adc instance.
 */
uint32_t ADC_GetTsPressure(Adc *pADC)
{
    return pADC->ADC_PRESSR;
}
