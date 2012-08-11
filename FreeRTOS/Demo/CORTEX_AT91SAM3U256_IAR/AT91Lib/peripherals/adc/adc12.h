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
/// \unit
///
/// !Purpose
///
/// Interface for configuration the Analog-to-Digital Converter (ADC) peripheral.
///
/// !Usage
///
/// -# Configurate the pins for ADC
/// -# Initialize the ADC with ADC_Initialize().
/// -# Select the active channel using ADC_EnableChannel()
/// -# Start the conversion with ADC_StartConversion()
//  -# Wait the end of the conversion by polling status with ADC_GetStatus()
//  -# Finally, get the converted data using ADC_GetConvertedData()
///
//------------------------------------------------------------------------------
#ifndef ADC12_H
#define ADC12_H

//------------------------------------------------------------------------------
//         Headers
//------------------------------------------------------------------------------
#include <utility/assert.h>

//------------------------------------------------------------------------------
//         Definitions
//------------------------------------------------------------------------------
#define ADC_CHANNEL_0 0
#define ADC_CHANNEL_1 1
#define ADC_CHANNEL_2 2
#define ADC_CHANNEL_3 3
#define ADC_CHANNEL_4 4
#define ADC_CHANNEL_5 5
#define ADC_CHANNEL_6 6
#define ADC_CHANNEL_7 7

//------------------------------------------------------------------------------
//         Macros function of register access
//------------------------------------------------------------------------------
#define ADC12_CfgModeReg(pAdc, mode)  { \
            ASSERT(((mode)&0xF00000C0)== 0, "ADC Bad configuration ADC MR");\
            (pAdc)->ADC_MR = (mode);\
        }

#define ADC12_GetModeReg(pAdc)                ((pAdc)->ADC_MR)

#define ADC12_StartConversion(pAdc)           ((pAdc)->ADC_CR = AT91C_ADC_START)

#define ADC12_SoftReset(pAdc)                 ((pAdc)->ADC_CR = AT91C_ADC_SWRST)

#define ADC12_EnableChannel(pAdc, channel)    {\
            ASSERT(channel < 8, "ADC Channel not exist");\
            (pAdc)->ADC_CHER = (1 << (channel));\
        }

#define ADC12_DisableChannel (pAdc, channel)  {\
            ASSERT((channel) < 8, "ADC Channel not exist");\
            (pAdc)->ADC_CHDR = (1 << (channel));\
        }

#define ADC12_EnableIt(pAdc, mode)            {\
            ASSERT(((mode)&0xFFF00000)== 0, "ADC bad interrupt IER");\
            (pAdc)->ADC_IER = (mode);\
        }

#define ADC12_DisableIt(pAdc, mode)           {\
            ASSERT(((mode)&0xFFF00000)== 0, "ADC bad interrupt IDR");\
            (pAdc)->ADC_IDR = (mode);\
        }

#define ADC12_EnableDataReadyIt(pAdc)         ((pAdc)->ADC_IER = AT91C_ADC_DRDY)

#define ADC12_GetStatus(pAdc)                 ((pAdc)->ADC_SR)

#define ADC12_GetChannelStatus(pAdc)          ((pAdc)->ADC_CHSR)

#define ADC12_GetInterruptMaskStatus(pAdc)    ((pAdc)->ADC_IMR)

#define ADC12_GetLastConvertedData(pAdc)      ((pAdc)->ADC_LCDR)

#define ADC12_CfgAnalogCtrlReg(pAdc,mode)     {\
            ASSERT(((mode) & 0xFFFCFF3C)==0, "ADC bad analog control config");\
            (pAdc)->ADC_ACR = (mode);\
        }

#define ADC12_CfgExtModeReg(pAdc, extmode)    {\
            ASSERT(((extmode) & 0xFF00FFFE)==0, "ADC bad extended mode config");\
            (pAdc)->ADC_EMR = (extmode);\
        }

#define ADC12_GetAnalogCtrlReg(pAdc)          ((pAdc)->ADC_ACR)

//------------------------------------------------------------------------------
//         Exported functions
//------------------------------------------------------------------------------
extern void ADC12_Initialize (AT91S_ADC *pAdc,
                     unsigned char idAdc,
                     unsigned char trgEn,
                     unsigned char trgSel,
                     unsigned char sleepMode,
                     unsigned char resolution,        
                     unsigned int mckClock,
                     unsigned int adcClock,
                     unsigned int startupTime,
                     unsigned int sampleAndHoldTime);
extern unsigned int ADC12_GetConvertedData(AT91S_ADC *pAdc, unsigned int channel);
extern unsigned int ADC12_IsInterruptMasked(AT91S_ADC *pAdc, unsigned int flag);
extern unsigned int ADC12_IsStatusSet(AT91S_ADC *pAdc, unsigned int flag);
extern unsigned char ADC12_IsChannelInterruptStatusSet(unsigned int adc_sr, 
                                              unsigned int channel);

#endif //#ifndef ADC12_H
