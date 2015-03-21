/* ----------------------------------------------------------------------------
 *         SAM Software Package License
 * ----------------------------------------------------------------------------
 * Copyright (c) 2014, Atmel Corporation
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

/** \addtogroup AFEC_module Working with AFE
 * \ingroup peripherals_module
 * The AFE driver provides the interface to configure and use the AFE peripheral.
 * \n
 *
 * It converts the analog input to digital format. The converted result could be
 * 12bit or 10bit. The AFE supports up to 16 analog lines.
 *
 * To Enable a AFE conversion,the user has to follow these few steps:
 * <ul>
 * <li> Select an appropriate reference voltage on ADVREF   </li>
 * <li> Configure the AFE according to its requirements and special needs,which
 * could be  broken down into several parts:
 * -#   Select the resolution by setting or clearing AFEC_MR_LOWRES bit in
 *      AFEC_MR (Mode Register)
 * -#   Set AFE clock by setting AFEC_MR_PRESCAL bits in AFEC_MR, the clock is
 *      calculated with AFEClock = MCK / ( (PRESCAL+1) * 2 )
 * -#   Set Startup Time,Tracking Clock cycles and Transfer Clock respectively
 *      in AFEC_MR.
 </li>
 * <li> Start conversion by setting AFEC_CR_START in AFEC_CR. </li>
 * </ul>
 *
 * For more accurate information, please look at the AFE section of the
 * Datasheet.
 *
 * Related files :\n
 * \ref AFE.c\n
 * \ref AFE.h\n
 */
/*@{*/
/*@}*/
/**
 * \file
 *
 * Implementation of Analog-to-Digital Converter (AFE).
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
static uint32_t dwAFEClock = 0;

/*----------------------------------------------------------------------------
 *        Exported functions
 *----------------------------------------------------------------------------*/

/**
 * \brief Initialize the AFE controller
 *
 * \param pAFE Pointer to an AFE instance.
 * \param dwID AFE Index
 */
extern void AFEC_Initialize( Afec* pAFE, uint32_t dwID )
{
    /* Enable peripheral clock*/
    PMC_EnablePeripheral(dwID);

    /*  Reset the controller */
    pAFE->AFEC_CR = AFEC_CR_SWRST;

    /* Reset Mode Register */
    pAFE->AFEC_MR = 0;
}

/**
 * \brief Set AFE clock.
 *
 * \param pAFE Pointer to an AFE instance.
 * \param dwPres prescal value
 * \param dwMck Board MCK (Hz)
 *
 * \return AFE clock
 */

extern uint32_t AFEC_SetClock( Afec* pAFE, uint32_t dwClk, uint32_t dwMck )
{ 
    uint32_t dwPres, dwMr;
    /* Formula for PRESCAL is:
       PRESCAL = peripheral clock/ fAFE Clock - 1 */

    dwPres = (dwMck) / (dwClk ) - 1;
    dwMr = AFEC_MR_PRESCAL(dwPres);
    if (dwMr == 0) return 0;

    dwMr |= (pAFE->AFEC_MR & ~AFEC_MR_PRESCAL_Msk);
    pAFE->AFEC_MR = dwMr;
    dwAFEClock = dwMck / (dwPres + 1);
    return dwAFEClock;
}

/**
 * \brief Set AFE timing.
 *
 * \param pAFE Pointer to an AFE instance.
 * \param dwStartup startup value
 * \param dwTracking tracking value
 * \param dwSettling settling value
 */
extern void AFEC_SetTiming( Afec* pAFE, uint32_t dwStartup, uint32_t dwTracking, uint32_t dwSettling )
{
    uint32_t dwMr;

    dwMr = pAFE->AFEC_MR;
    dwMr &= (~AFEC_MR_STARTUP_Msk) & (~AFEC_MR_TRACKTIM_Msk) & (~AFEC_MR_SETTLING_Msk);

    /* Formula:
     *     Startup  Time = startup value / AFEClock
     *     Transfer Time = (TRANSFER * 2 + 3) / AFEClock
     *     Tracking Time = (TRACKTIM + 1) / AFEClock
     *     Settling Time = settling value / AFEClock
     */
    dwMr |= dwStartup | dwTracking | dwSettling;
    pAFE->AFEC_MR |= dwMr;
}

/**
 * \brief Set AFE trigger.
 *
 * \param pAFE Pointer to an AFE instance.
 * \param dwTrgSel Trigger selection
 */
extern void AFEC_SetTrigger( Afec* pAFE, uint32_t dwTrgSel )
{
    uint32_t dwMr;

    dwMr = pAFE->AFEC_MR;
    dwMr &= ~AFEC_MR_TRGSEL_Msk;
    dwMr |= dwTrgSel;
    pAFE->AFEC_MR |= dwMr;
}


/**
 * \brief Enable/Disable sleep mode.
 *
 * \param pAFE Pointer to an AFE instance.
 * \param bEnDis Enable/Disable sleep mode.
 */
extern void AFEC_SetSleepMode( Afec *pAFE, uint8_t bEnDis )
{
    if ( bEnDis )
    {
        pAFE->AFEC_MR |=  AFEC_MR_SLEEP;
    }
    else
    {
        pAFE->AFEC_MR &= ~AFEC_MR_SLEEP;
    }
}

/**
 * \brief Enable/Disable fast wake up.
 *
 * \param pAFE Pointer to an AFE instance.
 * \param bEnDis Enable/Disable fast wake up in sleep mode.
 */
extern void AFEC_SetFastWakeup( Afec *pAFE, uint8_t bEnDis )
{
    if ( bEnDis )
    {
        pAFE->AFEC_MR |=  AFEC_MR_FWUP;
    }
    else
    {
        pAFE->AFEC_MR &= ~AFEC_MR_FWUP;
    }
}

/**
 * \brief Enable/Disable seqnence mode.
 *
 * \param pAFE  Pointer to an AFE instance.
 * \param bEnDis Enable/Disable seqnence mode.
 */
extern void AFEC_SetSequenceMode( Afec *pAFE, uint8_t bEnDis )
{
    if ( bEnDis )
    {
        /* User Sequence Mode: The sequence respects what is defined in
           AFEC_SEQR1 and AFEC_SEQR2 */
        pAFE->AFEC_MR |=  AFEC_MR_USEQ;
    }
    else
    {
        /* Normal Mode: The controller converts channels in a simple numeric order. */
        pAFE->AFEC_MR &= ~AFEC_MR_USEQ;
    }
}

/**
 * \brief Set channel sequence.
 *
 * \param pAFE   Pointer to an AFE instance.
 * \param dwSEQ1 Sequence 1 ~ 8  channel number.
 * \param dwSEQ2 Sequence 9 ~ 16 channel number.
 */
extern void AFEC_SetSequence( Afec *pAFE, uint32_t dwSEQ1, uint32_t dwSEQ2 )
{
    pAFE->AFEC_SEQ1R = dwSEQ1;
    pAFE->AFEC_SEQ2R = dwSEQ2;
}

/**
 * \brief Set channel sequence by given channel list.
 *
 * \param pAFE    Pointer to an AFE instance.
 * \param ucChList Channel list.
 * \param ucNumCh  Number of channels in list.
 */
extern void AFEC_SetSequenceByList( Afec *pAFE, uint8_t ucChList[], uint8_t ucNumCh )
{
    uint8_t i;
    uint8_t ucShift;

    pAFE->AFEC_SEQ1R = 0;
    for (i = 0, ucShift = 0; i < 8; i ++, ucShift += 4)
    {
        if (i >= ucNumCh) return;
        pAFE->AFEC_SEQ1R |= ucChList[i] << ucShift;

    }
    pAFE->AFEC_SEQ2R = 0;
    for (ucShift = 0; i < 16; i ++, ucShift += 4)
    {
        if (i >= ucNumCh) return;
        pAFE->AFEC_SEQ2R |= ucChList[i] << ucShift;
    }
}

/**
 * \brief Set analog change.
 * IF enabled, it allows different analog settings for each channel,
 * otherwise, DIFF0, GAIN0 and OFF0 are used for all channels.
 *
 * \param pAFE   Pointer to an AFE instance.
 * \param bEnDis Enable/Disable.
 */
extern void AFEC_SetAnalogChange( Afec* pAFE, uint8_t bEnDis )
{
    if ( bEnDis )
    {
        pAFE->AFEC_MR |=  AFEC_MR_ANACH;
    }
    else
    {
        pAFE->AFEC_MR &= ~AFEC_MR_ANACH;
    }
}

/**
 * \brief Set "TAG" mode, show channel number in last data or not.
 *
 * \param pAFE   Pointer to an AFE instance.
 * \param bEnDis Enable/Disable TAG value.
 */
extern void AFEC_SetTagEnable( Afec *pAFE, uint8_t bEnDis )
{
    if ( bEnDis )
    {
        pAFE->AFEC_EMR |=  AFEC_EMR_TAG;
    }
    else
    {
        pAFE->AFEC_EMR &= ~AFEC_EMR_TAG;
    }
}

/**
 * \brief Set compare channel.
 *
 * \param pAFE Pointer to an AFE instance.
 * \param dwChannel channel number to be set,16 for all channels
 */
extern void AFEC_SetCompareChannel( Afec* pAFE, uint32_t dwChannel )
{
    assert( dwChannel <= 16 ) ;

    if ( dwChannel < 16 )
    {
        pAFE->AFEC_EMR &= ~(AFEC_EMR_CMPALL);
        pAFE->AFEC_EMR &= ~(AFEC_EMR_CMPSEL_Msk);
        pAFE->AFEC_EMR |= (dwChannel << AFEC_EMR_CMPSEL_Pos);
    }
    else
    {
        pAFE->AFEC_EMR |= AFEC_EMR_CMPALL;
    }
}

/**
 * \brief Set compare mode.
 *
 * \param pAFE Pointer to an AFE instance.
 * \param dwMode compare mode
 */
extern void AFEC_SetCompareMode( Afec* pAFE, uint32_t dwMode )
{
    pAFE->AFEC_EMR &= ~(AFEC_EMR_CMPMODE_Msk);
    pAFE->AFEC_EMR |= (dwMode & AFEC_EMR_CMPMODE_Msk);
}

/**
 * \brief Set comparsion window.
 *
 * \param pAFE Pointer to an AFE instance.
 * \param dwHi_Lo Comparison Window
 */
extern void AFEC_SetComparisonWindow( Afec* pAFE, uint32_t dwHi_Lo )
{
    pAFE->AFEC_CWR = dwHi_Lo ;
}


/**
 * \brief Return the Channel Converted Data
 *
 * \param pAFE Pointer to an AFE instance.
 * \param dwChannel channel to get converted value
 */
extern uint32_t AFEC_GetConvertedData( Afec* pAFE, uint32_t dwChannel )
{
    uint32_t dwData = 0;
    assert( dwChannel < 12 ) ;
    pAFE->AFEC_CSELR = dwChannel;
    dwData = pAFE->AFEC_CDR;

    return dwData ;
}


/**
 * Sets the AFE startup time.
 * \param pAFE  Pointer to an AFE instance.
 * \param dwUs  Startup time in uS.
 */
void AFEC_SetStartupTime( Afec *pAFE, uint32_t dwUs )
{
    uint32_t dwStart;
    uint32_t dwMr;

    if (dwAFEClock == 0) return;
    /* Formula for STARTUP is:
       STARTUP = (time x AFECLK) / (1000000) - 1
       Division multiplied by 10 for higher precision */

    dwStart = (dwUs * dwAFEClock) / (100000);
    if (dwStart % 10) dwStart /= 10;
    else
    {
        dwStart /= 10;
        if (dwStart) dwStart --;
    }
    if      (dwStart >  896) dwMr = AFEC_MR_STARTUP_SUT960;
    else if (dwStart >  832) dwMr = AFEC_MR_STARTUP_SUT896;
    else if (dwStart >  768) dwMr = AFEC_MR_STARTUP_SUT832;
    else if (dwStart >  704) dwMr = AFEC_MR_STARTUP_SUT768;
    else if (dwStart >  640) dwMr = AFEC_MR_STARTUP_SUT704;
    else if (dwStart >  576) dwMr = AFEC_MR_STARTUP_SUT640;
    else if (dwStart >  512) dwMr = AFEC_MR_STARTUP_SUT576;
    else if (dwStart >  112) dwMr = AFEC_MR_STARTUP_SUT512;
    else if (dwStart >   96) dwMr = AFEC_MR_STARTUP_SUT112;
    else if (dwStart >   80) dwMr = AFEC_MR_STARTUP_SUT96;
    else if (dwStart >   64) dwMr = AFEC_MR_STARTUP_SUT80;
    else if (dwStart >   24) dwMr = AFEC_MR_STARTUP_SUT64;
    else if (dwStart >   16) dwMr = AFEC_MR_STARTUP_SUT24;
    else if (dwStart >    8) dwMr = AFEC_MR_STARTUP_SUT16;
    else if (dwStart >    0) dwMr = AFEC_MR_STARTUP_SUT8;
    else                     dwMr = AFEC_MR_STARTUP_SUT0;

    dwMr |= pAFE->AFEC_MR & ~AFEC_MR_STARTUP_Msk;
    pAFE->AFEC_MR = dwMr;
}


/**
 * Set AFE tracking time
 * \param pAFE  Pointer to an AFE instance.
 * \param dwNs  Tracking time in nS.
 */
void AFEC_SetTrackingTime( Afec *pAFE, uint32_t dwNs )
{
    uint32_t dwShtim;
    uint32_t dwMr;

    if (dwAFEClock == 0) return;
    /* Formula for SHTIM is:
       SHTIM = (time x AFECLK) / (1000000000) - 1
       Since 1 billion is close to the maximum value for an integer, we first
       divide AFECLK by 1000 to avoid an overflow */
    dwShtim = (dwNs * (dwAFEClock / 1000)) / 100000;
    if (dwShtim % 10) dwShtim /= 10;
    else
    {
        dwShtim /= 10;
        if (dwShtim) dwShtim --;
    }
    dwMr  = AFEC_MR_TRACKTIM(dwShtim);
    dwMr |= pAFE->AFEC_MR & ~AFEC_MR_TRACKTIM_Msk;
    pAFE->AFEC_MR = dwMr;
}

/**
 * \brief Set analog offset to be used for channel CSEL.
 *
 * \param afec  Base address of the AFEC.
 * \param dwChannel AFEC channel number.
 * \param aoffset  Analog offset value.
 */
void AFEC_SetAnalogOffset( Afec *pAFE, uint32_t dwChannel,uint32_t aoffset )
{
    assert( dwChannel < 12 ) ;
    pAFE->AFEC_CSELR = dwChannel;
    pAFE->AFEC_COCR = (aoffset & AFEC_COCR_AOFF_Msk);;
}

/**
 * \brief Set analog offset to be used for channel CSEL.
 *
 * \param afec  Base address of the AFEC.
 * \param control  Analog control value.
 */
void AFEC_SetAnalogControl( Afec *pAFE, uint32_t control)
{
    pAFE->AFEC_ACR = control;
}


