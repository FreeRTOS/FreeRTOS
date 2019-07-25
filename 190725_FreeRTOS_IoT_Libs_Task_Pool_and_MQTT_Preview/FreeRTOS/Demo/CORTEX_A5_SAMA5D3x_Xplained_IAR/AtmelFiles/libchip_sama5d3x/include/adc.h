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

/**
 *  \file
 *
 *  \section Purpose
 *
 *  Interface for configuration the Analog-to-Digital Converter (ADC) peripheral.
 *
 *  \section Usage
 *
 *  -# Configurate the pins for ADC.
 *  -# Initialize the ADC with ADC_Initialize().
 *  -# Set ADC clock and timing with ADC_SetClock() and ADC_SetTiming().
 *  -# Select the active channel using ADC_EnableChannel().
 *  -# Start the conversion with ADC_StartConversion().
 *  -# Wait the end of the conversion by polling status with ADC_GetStatus().
 *  -# Finally, get the converted data using ADC_GetConvertedData() or ADC_GetLastConvertedData().
 *
*/
#ifndef _ADC_
#define _ADC_

/*----------------------------------------------------------------------------
 *        Headers
 *----------------------------------------------------------------------------*/
#include <assert.h>
#include <stdint.h>

/*------------------------------------------------------------------------------
 *         Definitions
 *------------------------------------------------------------------------------*/

/* Max. ADC Clock Frequency (Hz) */
#define ADC_CLOCK_MAX   20000000

/* Max. normal ADC startup time (us) */
#define ADC_STARTUP_NORMAL_MAX     40
/* Max. fast ADC startup time (us) */
#define ADC_STARTUP_FAST_MAX       12

/* Definitions for ADC channels */
#define ADC_CHANNEL_0  0
#define ADC_CHANNEL_1  1
#define ADC_CHANNEL_2  2
#define ADC_CHANNEL_3  3
#define ADC_CHANNEL_4  4
#define ADC_CHANNEL_5  5
#define ADC_CHANNEL_6  6
#define ADC_CHANNEL_7  7
#define ADC_CHANNEL_8  8
#define ADC_CHANNEL_9  9
#define ADC_CHANNEL_10 10
#define ADC_CHANNEL_11 11
#define ADC_CHANNEL_12 12
#define ADC_CHANNEL_13 13
#define ADC_CHANNEL_14 14
#define ADC_CHANNEL_15 15

#ifdef __cplusplus
 extern "C" {
#endif

/*------------------------------------------------------------------------------
 *         Macros function of register access
 *------------------------------------------------------------------------------*/

#define ADC_GetModeReg( pAdc )                ((pAdc)->ADC_MR)

#define ADC_StartConversion( pAdc )           ((pAdc)->ADC_CR = ADC_CR_START)

#define ADC_SetCalibMode(pAdc)                  ((pAdc)->ADC_CR |= ADC_CR_AUTOCAL)

#define ADC_EnableChannel( pAdc, dwChannel )    {\
            (pAdc)->ADC_CHER = (1 << (dwChannel));\
        }

#define ADC_DisableChannel(pAdc, dwChannel)  {\
            (pAdc)->ADC_CHDR = (1 << (dwChannel));\
        }

#define ADC_EnableIt(pAdc, dwMode)            {\
            (pAdc)->ADC_IER = (dwMode);\
        }

#define ADC_DisableIt(pAdc, dwMode)           {\
            (pAdc)->ADC_IDR = (dwMode);\
        }

#define ADC_SetChannelGain(pAdc,dwMode)       {\
            (pAdc)->ADC_CGR = dwMode;\
        }

#define ADC_SetChannelOffset(pAdc,dwMode)     {\
            (pAdc)->ADC_COR = dwMode;\
        }

#define ADC_EnableDataReadyIt(pAdc)         ((pAdc)->ADC_IER = ADC_IER_DRDY)

#define ADC_GetStatus(pAdc)                 ((pAdc)->ADC_ISR)

#define ADC_GetCompareMode(pAdc)            (((pAdc)->ADC_EMR)& (ADC_EMR_CMPMODE_Msk))

#define ADC_GetChannelStatus(pAdc)          ((pAdc)->ADC_CHSR)

#define ADC_GetInterruptMaskStatus(pAdc)    ((pAdc)->ADC_IMR)

#define ADC_GetLastConvertedData(pAdc)      ((pAdc)->ADC_LCDR)

/*------------------------------------------------------------------------------
 *         Exported functions
 *------------------------------------------------------------------------------*/
extern void ADC_Initialize( Adc* pAdc, uint32_t dwId );
extern uint32_t ADC_SetClock( Adc* pAdc, uint32_t dwPres, uint32_t dwMck );
extern void ADC_SetTiming( Adc* pAdc, uint32_t dwStartup, uint32_t dwTracking, uint32_t dwSettling );
extern void ADC_SetTrigger( Adc* pAdc, uint32_t dwTrgSel );
extern void ADC_SetTriggerMode(Adc *pAdc, uint32_t dwMode);
extern void ADC_SetLowResolution( Adc* pAdc, uint32_t bEnDis );
extern void ADC_SetSleepMode( Adc *pAdc, uint8_t bEnDis );
extern void ADC_SetFastWakeup( Adc *pAdc, uint8_t bEnDis );
extern void ADC_SetSequenceMode( Adc *pAdc, uint8_t bEnDis );
extern void ADC_SetSequence( Adc *pAdc, uint32_t dwSEQ1, uint32_t dwSEQ2 );
extern void ADC_SetSequenceByList( Adc *pAdc, uint8_t ucChList[], uint8_t ucNumCh );
extern void ADC_SetAnalogChange( Adc *pAdc, uint8_t bEnDis );
extern void ADC_SetTagEnable( Adc *pAdc, uint8_t bEnDis );
extern void ADC_SetCompareChannel( Adc* pAdc, uint32_t dwChannel ) ;
extern void ADC_SetCompareMode( Adc* pAdc, uint32_t dwMode ) ;
extern void ADC_SetComparisonWindow( Adc* pAdc, uint32_t dwHi_Lo ) ;
extern uint8_t ADC_CheckConfiguration( Adc* pAdc, uint32_t dwMcK ) ;
extern uint32_t ADC_GetConvertedData( Adc* pAdc, uint32_t dwChannel ) ;
extern void ADC_SetTsAverage(Adc* pADC, uint32_t dwAvg2Conv);
extern uint32_t ADC_GetTsXPosition(Adc *pADC);
extern uint32_t ADC_GetTsYPosition(Adc *pADC);
extern uint32_t ADC_GetTsPressure(Adc *pADC);
extern void ADC_SetTsDebounce(Adc *pADC, uint32_t dwTime);
extern void ADC_SetTsPenDetect(Adc* pADC, uint8_t bEnDis);
extern void ADC_SetStartupTime( Adc *pAdc, uint32_t dwUs );
extern void ADC_SetTrackingTime( Adc *pAdc, uint32_t dwNs );
extern void ADC_SetTriggerPeriod(Adc *pAdc, uint32_t dwPeriod);
extern void ADC_SetTsMode(Adc* pADC, uint32_t dwMode);
extern void ADC_TsCalibration( Adc *pAdc );


#ifdef __cplusplus
}
#endif

#endif /* #ifndef _ADC_ */

