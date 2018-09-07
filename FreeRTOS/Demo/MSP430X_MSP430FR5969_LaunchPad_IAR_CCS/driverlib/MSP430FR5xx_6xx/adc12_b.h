/* --COPYRIGHT--,BSD
 * Copyright (c) 2014, Texas Instruments Incorporated
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 *
 * *  Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 *
 * *  Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 *
 * *  Neither the name of Texas Instruments Incorporated nor the names of
 *    its contributors may be used to endorse or promote products derived
 *    from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO,
 * THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR
 * PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR
 * CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
 * PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS;
 * OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY,
 * WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR
 * OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE,
 * EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 * --/COPYRIGHT--*/
//*****************************************************************************
//
// adc12_b.h - Driver for the ADC12_B Module.
//
//*****************************************************************************

#ifndef __MSP430WARE_ADC12_B_H__
#define __MSP430WARE_ADC12_B_H__

#include "inc/hw_memmap.h"

#ifdef __MSP430_HAS_ADC12_B__

//*****************************************************************************
//
// If building with a C++ compiler, make all of the definitions in this header
// have a C binding.
//
//*****************************************************************************
#ifdef __cplusplus
extern "C"
{
#endif

#include "inc/hw_regaccess.h"
//*****************************************************************************
//
//! \brief Used in the ADC12_B_init() function as the param parameter.
//
//*****************************************************************************
typedef struct ADC12_B_initParam
{
    //! Is the signal that will trigger a sample-and-hold for an input signal
    //! to be converted.
    //! \n Valid values are:
    //! - \b ADC12_B_SAMPLEHOLDSOURCE_SC [Default]
    //! - \b ADC12_B_SAMPLEHOLDSOURCE_1
    //! - \b ADC12_B_SAMPLEHOLDSOURCE_2
    //! - \b ADC12_B_SAMPLEHOLDSOURCE_3
    //! - \b ADC12_B_SAMPLEHOLDSOURCE_4
    //! - \b ADC12_B_SAMPLEHOLDSOURCE_5
    //! - \b ADC12_B_SAMPLEHOLDSOURCE_6
    //! - \b ADC12_B_SAMPLEHOLDSOURCE_7
    uint16_t sampleHoldSignalSourceSelect;
    //! Selects the clock that will be used by the ADC12B core, and the
    //! sampling timer if a sampling pulse mode is enabled.
    //! \n Valid values are:
    //! - \b ADC12_B_CLOCKSOURCE_ADC12OSC [Default]
    //! - \b ADC12_B_CLOCKSOURCE_ACLK
    //! - \b ADC12_B_CLOCKSOURCE_MCLK
    //! - \b ADC12_B_CLOCKSOURCE_SMCLK
    uint8_t clockSourceSelect;
    //! Selects the amount that the clock will be divided.
    //! \n Valid values are:
    //! - \b ADC12_B_CLOCKDIVIDER_1 [Default]
    //! - \b ADC12_B_CLOCKDIVIDER_2
    //! - \b ADC12_B_CLOCKDIVIDER_3
    //! - \b ADC12_B_CLOCKDIVIDER_4
    //! - \b ADC12_B_CLOCKDIVIDER_5
    //! - \b ADC12_B_CLOCKDIVIDER_6
    //! - \b ADC12_B_CLOCKDIVIDER_7
    //! - \b ADC12_B_CLOCKDIVIDER_8
    uint16_t clockSourceDivider;
    //! Selects the amount that the clock will be predivided.
    //! \n Valid values are:
    //! - \b ADC12_B_CLOCKPREDIVIDER__1 [Default]
    //! - \b ADC12_B_CLOCKPREDIVIDER__4
    //! - \b ADC12_B_CLOCKPREDIVIDER__32
    //! - \b ADC12_B_CLOCKPREDIVIDER__64
    uint16_t clockSourcePredivider;
    //! Selects what internal channel to map for ADC input channels
    //! \n Valid values are:
    //! - \b ADC12_B_MAPINTCH3
    //! - \b ADC12_B_MAPINTCH2
    //! - \b ADC12_B_MAPINTCH1
    //! - \b ADC12_B_MAPINTCH0
    //! - \b ADC12_B_TEMPSENSEMAP
    //! - \b ADC12_B_BATTMAP
    //! - \b ADC12_B_NOINTCH
    uint16_t internalChannelMap;
} ADC12_B_initParam;

//*****************************************************************************
//
//! \brief Used in the ADC12_B_configureMemory() function as the param
//! parameter.
//
//*****************************************************************************
typedef struct ADC12_B_configureMemoryParam
{
    //! Is the selected memory buffer to set the configuration for.
    //! \n Valid values are:
    //! - \b ADC12_B_MEMORY_0
    //! - \b ADC12_B_MEMORY_1
    //! - \b ADC12_B_MEMORY_2
    //! - \b ADC12_B_MEMORY_3
    //! - \b ADC12_B_MEMORY_4
    //! - \b ADC12_B_MEMORY_5
    //! - \b ADC12_B_MEMORY_6
    //! - \b ADC12_B_MEMORY_7
    //! - \b ADC12_B_MEMORY_8
    //! - \b ADC12_B_MEMORY_9
    //! - \b ADC12_B_MEMORY_10
    //! - \b ADC12_B_MEMORY_11
    //! - \b ADC12_B_MEMORY_12
    //! - \b ADC12_B_MEMORY_13
    //! - \b ADC12_B_MEMORY_14
    //! - \b ADC12_B_MEMORY_15
    //! - \b ADC12_B_MEMORY_16
    //! - \b ADC12_B_MEMORY_17
    //! - \b ADC12_B_MEMORY_18
    //! - \b ADC12_B_MEMORY_19
    //! - \b ADC12_B_MEMORY_20
    //! - \b ADC12_B_MEMORY_21
    //! - \b ADC12_B_MEMORY_22
    //! - \b ADC12_B_MEMORY_23
    //! - \b ADC12_B_MEMORY_24
    //! - \b ADC12_B_MEMORY_25
    //! - \b ADC12_B_MEMORY_26
    //! - \b ADC12_B_MEMORY_27
    //! - \b ADC12_B_MEMORY_28
    //! - \b ADC12_B_MEMORY_29
    //! - \b ADC12_B_MEMORY_30
    //! - \b ADC12_B_MEMORY_31
    uint8_t memoryBufferControlIndex;
    //! Is the input that will store the converted data into the specified
    //! memory buffer.
    //! \n Valid values are:
    //! - \b ADC12_B_INPUT_A0 [Default]
    //! - \b ADC12_B_INPUT_A1
    //! - \b ADC12_B_INPUT_A2
    //! - \b ADC12_B_INPUT_A3
    //! - \b ADC12_B_INPUT_A4
    //! - \b ADC12_B_INPUT_A5
    //! - \b ADC12_B_INPUT_A6
    //! - \b ADC12_B_INPUT_A7
    //! - \b ADC12_B_INPUT_A8
    //! - \b ADC12_B_INPUT_A9
    //! - \b ADC12_B_INPUT_A10
    //! - \b ADC12_B_INPUT_A11
    //! - \b ADC12_B_INPUT_A12
    //! - \b ADC12_B_INPUT_A13
    //! - \b ADC12_B_INPUT_A14
    //! - \b ADC12_B_INPUT_A15
    //! - \b ADC12_B_INPUT_A16
    //! - \b ADC12_B_INPUT_A17
    //! - \b ADC12_B_INPUT_A18
    //! - \b ADC12_B_INPUT_A19
    //! - \b ADC12_B_INPUT_A20
    //! - \b ADC12_B_INPUT_A21
    //! - \b ADC12_B_INPUT_A22
    //! - \b ADC12_B_INPUT_A23
    //! - \b ADC12_B_INPUT_A24
    //! - \b ADC12_B_INPUT_A25
    //! - \b ADC12_B_INPUT_A26
    //! - \b ADC12_B_INPUT_A27
    //! - \b ADC12_B_INPUT_A28
    //! - \b ADC12_B_INPUT_A29
    //! - \b ADC12_B_INPUT_TCMAP
    //! - \b ADC12_B_INPUT_BATMAP
    uint8_t inputSourceSelect;
    //! Is the reference voltage source to set as the upper/lower limits for
    //! the conversion stored in the specified memory.
    //! \n Valid values are:
    //! - \b ADC12_B_VREFPOS_AVCC_VREFNEG_VSS [Default]
    //! - \b ADC12_B_VREFPOS_INTBUF_VREFNEG_VSS
    //! - \b ADC12_B_VREFPOS_EXTNEG_VREFNEG_VSS
    //! - \b ADC12_B_VREFPOS_EXTBUF_VREFNEG_VSS
    //! - \b ADC12_B_VREFPOS_EXTPOS_VREFNEG_VSS
    //! - \b ADC12_B_VREFPOS_AVCC_VREFNEG_EXTBUF
    //! - \b ADC12_B_VREFPOS_AVCC_VREFNEG_EXTPOS
    //! - \b ADC12_B_VREFPOS_INTBUF_VREFNEG_EXTPOS
    //! - \b ADC12_B_VREFPOS_AVCC_VREFNEG_INTBUF
    //! - \b ADC12_B_VREFPOS_EXTPOS_VREFNEG_INTBUF
    //! - \b ADC12_B_VREFPOS_AVCC_VREFNEG_EXTNEG
    //! - \b ADC12_B_VREFPOS_INTBUF_VREFNEG_EXTNEG
    //! - \b ADC12_B_VREFPOS_EXTPOS_VREFNEG_EXTNEG
    //! - \b ADC12_B_VREFPOS_EXTBUF_VREFNEG_EXTNEG
    uint16_t refVoltageSourceSelect;
    //! Indicates that the specified memory buffer will be the end of the
    //! sequence if a sequenced conversion mode is selected
    //! \n Valid values are:
    //! - \b ADC12_B_NOTENDOFSEQUENCE [Default]
    //! - \b ADC12_B_ENDOFSEQUENCE
    uint16_t endOfSequence;
    //! Sets the window comparator mode
    //! \n Valid values are:
    //! - \b ADC12_B_WINDOW_COMPARATOR_DISABLE [Default]
    //! - \b ADC12_B_WINDOW_COMPARATOR_ENABLE
    uint16_t windowComparatorSelect;
    //! Sets the differential mode
    //! \n Valid values are:
    //! - \b ADC12_B_DIFFERENTIAL_MODE_DISABLE [Default]
    //! - \b ADC12_B_DIFFERENTIAL_MODE_ENABLE
    uint16_t differentialModeSelect;
} ADC12_B_configureMemoryParam;

//*****************************************************************************
//
// The following are values that can be passed to the clockSourceDivider
// parameter for functions: ADC12_B_init(); the param parameter for functions:
// ADC12_B_init().
//
//*****************************************************************************
#define ADC12_B_CLOCKDIVIDER_1                                     (ADC12DIV_0)
#define ADC12_B_CLOCKDIVIDER_2                                     (ADC12DIV_1)
#define ADC12_B_CLOCKDIVIDER_3                                     (ADC12DIV_2)
#define ADC12_B_CLOCKDIVIDER_4                                     (ADC12DIV_3)
#define ADC12_B_CLOCKDIVIDER_5                                     (ADC12DIV_4)
#define ADC12_B_CLOCKDIVIDER_6                                     (ADC12DIV_5)
#define ADC12_B_CLOCKDIVIDER_7                                     (ADC12DIV_6)
#define ADC12_B_CLOCKDIVIDER_8                                     (ADC12DIV_7)

//*****************************************************************************
//
// The following are values that can be passed to the clockSourceSelect
// parameter for functions: ADC12_B_init(); the param parameter for functions:
// ADC12_B_init().
//
//*****************************************************************************
#define ADC12_B_CLOCKSOURCE_ADC12OSC                              (ADC12SSEL_0)
#define ADC12_B_CLOCKSOURCE_ACLK                                  (ADC12SSEL_1)
#define ADC12_B_CLOCKSOURCE_MCLK                                  (ADC12SSEL_2)
#define ADC12_B_CLOCKSOURCE_SMCLK                                 (ADC12SSEL_3)

//*****************************************************************************
//
// The following are values that can be passed to the clockSourcePredivider
// parameter for functions: ADC12_B_init(); the param parameter for functions:
// ADC12_B_init().
//
//*****************************************************************************
#define ADC12_B_CLOCKPREDIVIDER__1                               (ADC12PDIV__1)
#define ADC12_B_CLOCKPREDIVIDER__4                               (ADC12PDIV__4)
#define ADC12_B_CLOCKPREDIVIDER__32                             (ADC12PDIV__32)
#define ADC12_B_CLOCKPREDIVIDER__64                             (ADC12PDIV__64)

//*****************************************************************************
//
// The following are values that can be passed to the param parameter for
// functions: ADC12_B_init(); the sampleHoldSignalSourceSelect parameter for
// functions: ADC12_B_init().
//
//*****************************************************************************
#define ADC12_B_SAMPLEHOLDSOURCE_SC                                (ADC12SHS_0)
#define ADC12_B_SAMPLEHOLDSOURCE_1                                 (ADC12SHS_1)
#define ADC12_B_SAMPLEHOLDSOURCE_2                                 (ADC12SHS_2)
#define ADC12_B_SAMPLEHOLDSOURCE_3                                 (ADC12SHS_3)
#define ADC12_B_SAMPLEHOLDSOURCE_4                                 (ADC12SHS_4)
#define ADC12_B_SAMPLEHOLDSOURCE_5                                 (ADC12SHS_5)
#define ADC12_B_SAMPLEHOLDSOURCE_6                                 (ADC12SHS_6)
#define ADC12_B_SAMPLEHOLDSOURCE_7                                 (ADC12SHS_7)

//*****************************************************************************
//
// The following are values that can be passed to the internalChannelMap
// parameter for functions: ADC12_B_init(); the param parameter for functions:
// ADC12_B_init().
//
//*****************************************************************************
#define ADC12_B_MAPINTCH3                                        (ADC12ICH3MAP)
#define ADC12_B_MAPINTCH2                                        (ADC12ICH2MAP)
#define ADC12_B_MAPINTCH1                                        (ADC12ICH1MAP)
#define ADC12_B_MAPINTCH0                                        (ADC12ICH0MAP)
#define ADC12_B_TEMPSENSEMAP                                       (ADC12TCMAP)
#define ADC12_B_BATTMAP                                           (ADC12BATMAP)
#define ADC12_B_NOINTCH                                                  (0x00)

//*****************************************************************************
//
// The following are values that can be passed to the clockCycleHoldCountLowMem
// parameter for functions: ADC12_B_setupSamplingTimer(); the
// clockCycleHoldCountHighMem parameter for functions:
// ADC12_B_setupSamplingTimer().
//
//*****************************************************************************
#define ADC12_B_CYCLEHOLD_4_CYCLES                                (ADC12SHT0_0)
#define ADC12_B_CYCLEHOLD_8_CYCLES                                (ADC12SHT0_1)
#define ADC12_B_CYCLEHOLD_16_CYCLES                               (ADC12SHT0_2)
#define ADC12_B_CYCLEHOLD_32_CYCLES                               (ADC12SHT0_3)
#define ADC12_B_CYCLEHOLD_64_CYCLES                               (ADC12SHT0_4)
#define ADC12_B_CYCLEHOLD_96_CYCLES                               (ADC12SHT0_5)
#define ADC12_B_CYCLEHOLD_128_CYCLES                              (ADC12SHT0_6)
#define ADC12_B_CYCLEHOLD_192_CYCLES                              (ADC12SHT0_7)
#define ADC12_B_CYCLEHOLD_256_CYCLES                              (ADC12SHT0_8)
#define ADC12_B_CYCLEHOLD_384_CYCLES                              (ADC12SHT0_9)
#define ADC12_B_CYCLEHOLD_512_CYCLES                             (ADC12SHT0_10)
#define ADC12_B_CYCLEHOLD_768_CYCLES                             (ADC12SHT0_11)
#define ADC12_B_CYCLEHOLD_1024_CYCLES                            (ADC12SHT0_12)

//*****************************************************************************
//
// The following are values that can be passed to the multipleSamplesEnabled
// parameter for functions: ADC12_B_setupSamplingTimer().
//
//*****************************************************************************
#define ADC12_B_MULTIPLESAMPLESDISABLE                            (!(ADC12MSC))
#define ADC12_B_MULTIPLESAMPLESENABLE                                (ADC12MSC)

//*****************************************************************************
//
// The following are values that can be passed to the param parameter for
// functions: ADC12_B_configureMemory().
//
//*****************************************************************************
#define ADC12_B_DIFFERENTIAL_MODE_DISABLE                                (0x00)
#define ADC12_B_DIFFERENTIAL_MODE_ENABLE                             (ADC12DIF)

//*****************************************************************************
//
// The following are values that can be passed to the param parameter for
// functions: ADC12_B_configureMemory().
//
//*****************************************************************************
#define ADC12_B_NOTENDOFSEQUENCE                                  (!(ADC12EOS))
#define ADC12_B_ENDOFSEQUENCE                                        (ADC12EOS)

//*****************************************************************************
//
// The following are values that can be passed to the param parameter for
// functions: ADC12_B_configureMemory().
//
//*****************************************************************************
#define ADC12_B_VREFPOS_AVCC_VREFNEG_VSS                         (ADC12VRSEL_0)
#define ADC12_B_VREFPOS_INTBUF_VREFNEG_VSS                       (ADC12VRSEL_1)
#define ADC12_B_VREFPOS_EXTNEG_VREFNEG_VSS                       (ADC12VRSEL_2)
#define ADC12_B_VREFPOS_EXTBUF_VREFNEG_VSS                       (ADC12VRSEL_3)
#define ADC12_B_VREFPOS_EXTPOS_VREFNEG_VSS                       (ADC12VRSEL_4)
#define ADC12_B_VREFPOS_AVCC_VREFNEG_EXTBUF                      (ADC12VRSEL_5)
#define ADC12_B_VREFPOS_AVCC_VREFNEG_EXTPOS                      (ADC12VRSEL_6)
#define ADC12_B_VREFPOS_INTBUF_VREFNEG_EXTPOS                    (ADC12VRSEL_7)
#define ADC12_B_VREFPOS_AVCC_VREFNEG_INTBUF                      (ADC12VRSEL_9)
#define ADC12_B_VREFPOS_EXTPOS_VREFNEG_INTBUF                   (ADC12VRSEL_11)
#define ADC12_B_VREFPOS_AVCC_VREFNEG_EXTNEG                     (ADC12VRSEL_12)
#define ADC12_B_VREFPOS_INTBUF_VREFNEG_EXTNEG                   (ADC12VRSEL_13)
#define ADC12_B_VREFPOS_EXTPOS_VREFNEG_EXTNEG                   (ADC12VRSEL_14)
#define ADC12_B_VREFPOS_EXTBUF_VREFNEG_EXTNEG                   (ADC12VRSEL_15)

//*****************************************************************************
//
// The following are values that can be passed to the param parameter for
// functions: ADC12_B_configureMemory().
//
//*****************************************************************************
#define ADC12_B_INPUT_A0                                          (ADC12INCH_0)
#define ADC12_B_INPUT_A1                                          (ADC12INCH_1)
#define ADC12_B_INPUT_A2                                          (ADC12INCH_2)
#define ADC12_B_INPUT_A3                                          (ADC12INCH_3)
#define ADC12_B_INPUT_A4                                          (ADC12INCH_4)
#define ADC12_B_INPUT_A5                                          (ADC12INCH_5)
#define ADC12_B_INPUT_A6                                          (ADC12INCH_6)
#define ADC12_B_INPUT_A7                                          (ADC12INCH_7)
#define ADC12_B_INPUT_A8                                          (ADC12INCH_8)
#define ADC12_B_INPUT_A9                                          (ADC12INCH_9)
#define ADC12_B_INPUT_A10                                        (ADC12INCH_10)
#define ADC12_B_INPUT_A11                                        (ADC12INCH_11)
#define ADC12_B_INPUT_A12                                        (ADC12INCH_12)
#define ADC12_B_INPUT_A13                                        (ADC12INCH_13)
#define ADC12_B_INPUT_A14                                        (ADC12INCH_14)
#define ADC12_B_INPUT_A15                                        (ADC12INCH_15)
#define ADC12_B_INPUT_A16                                        (ADC12INCH_16)
#define ADC12_B_INPUT_A17                                        (ADC12INCH_17)
#define ADC12_B_INPUT_A18                                        (ADC12INCH_18)
#define ADC12_B_INPUT_A19                                        (ADC12INCH_19)
#define ADC12_B_INPUT_A20                                        (ADC12INCH_20)
#define ADC12_B_INPUT_A21                                        (ADC12INCH_21)
#define ADC12_B_INPUT_A22                                        (ADC12INCH_22)
#define ADC12_B_INPUT_A23                                        (ADC12INCH_23)
#define ADC12_B_INPUT_A24                                        (ADC12INCH_24)
#define ADC12_B_INPUT_A25                                        (ADC12INCH_25)
#define ADC12_B_INPUT_A26                                        (ADC12INCH_26)
#define ADC12_B_INPUT_A27                                        (ADC12INCH_27)
#define ADC12_B_INPUT_A28                                        (ADC12INCH_28)
#define ADC12_B_INPUT_A29                                        (ADC12INCH_29)
#define ADC12_B_INPUT_TCMAP                                      (ADC12INCH_30)
#define ADC12_B_INPUT_BATMAP                                     (ADC12INCH_31)

//*****************************************************************************
//
// The following are values that can be passed to the param parameter for
// functions: ADC12_B_configureMemory().
//
//*****************************************************************************
#define ADC12_B_WINDOW_COMPARATOR_DISABLE                                (0x00)
#define ADC12_B_WINDOW_COMPARATOR_ENABLE                            (ADC12WINC)

//*****************************************************************************
//
// The following are values that can be passed to the memoryIndex parameter for
// functions: ADC12_B_getMemoryAddressForDMA(); the memoryBufferIndex parameter
// for functions: ADC12_B_getResults(); the param parameter for functions:
// ADC12_B_configureMemory().
//
//*****************************************************************************
#define ADC12_B_MEMORY_0                                                 (0x00)
#define ADC12_B_MEMORY_1                                                 (0x02)
#define ADC12_B_MEMORY_2                                                 (0x04)
#define ADC12_B_MEMORY_3                                                 (0x06)
#define ADC12_B_MEMORY_4                                                 (0x08)
#define ADC12_B_MEMORY_5                                                 (0x0A)
#define ADC12_B_MEMORY_6                                                 (0x0C)
#define ADC12_B_MEMORY_7                                                 (0x0E)
#define ADC12_B_MEMORY_8                                                 (0x10)
#define ADC12_B_MEMORY_9                                                 (0x12)
#define ADC12_B_MEMORY_10                                                (0x14)
#define ADC12_B_MEMORY_11                                                (0x16)
#define ADC12_B_MEMORY_12                                                (0x18)
#define ADC12_B_MEMORY_13                                                (0x1A)
#define ADC12_B_MEMORY_14                                                (0x1C)
#define ADC12_B_MEMORY_15                                                (0x1E)
#define ADC12_B_MEMORY_16                                                (0x20)
#define ADC12_B_MEMORY_17                                                (0x22)
#define ADC12_B_MEMORY_18                                                (0x24)
#define ADC12_B_MEMORY_19                                                (0x26)
#define ADC12_B_MEMORY_20                                                (0x28)
#define ADC12_B_MEMORY_21                                                (0x2A)
#define ADC12_B_MEMORY_22                                                (0x2C)
#define ADC12_B_MEMORY_23                                                (0x2E)
#define ADC12_B_MEMORY_24                                                (0x30)
#define ADC12_B_MEMORY_25                                                (0x32)
#define ADC12_B_MEMORY_26                                                (0x34)
#define ADC12_B_MEMORY_27                                                (0x36)
#define ADC12_B_MEMORY_28                                                (0x38)
#define ADC12_B_MEMORY_29                                                (0x3A)
#define ADC12_B_MEMORY_30                                                (0x3C)
#define ADC12_B_MEMORY_31                                                (0x3E)

//*****************************************************************************
//
// The following are values that can be passed to the interruptMask0 parameter
// for functions: ADC12_B_enableInterrupt(), and ADC12_B_disableInterrupt().
//
//*****************************************************************************
#define ADC12_B_IE0                                                  (ADC12IE0)
#define ADC12_B_IE1                                                  (ADC12IE1)
#define ADC12_B_IE2                                                  (ADC12IE2)
#define ADC12_B_IE3                                                  (ADC12IE3)
#define ADC12_B_IE4                                                  (ADC12IE4)
#define ADC12_B_IE5                                                  (ADC12IE5)
#define ADC12_B_IE6                                                  (ADC12IE6)
#define ADC12_B_IE7                                                  (ADC12IE7)
#define ADC12_B_IE8                                                  (ADC12IE8)
#define ADC12_B_IE9                                                  (ADC12IE9)
#define ADC12_B_IE10                                                (ADC12IE10)
#define ADC12_B_IE11                                                (ADC12IE11)
#define ADC12_B_IE12                                                (ADC12IE12)
#define ADC12_B_IE13                                                (ADC12IE13)
#define ADC12_B_IE14                                                (ADC12IE14)
#define ADC12_B_IE15                                                (ADC12IE15)

//*****************************************************************************
//
// The following are values that can be passed to the interruptMask1 parameter
// for functions: ADC12_B_enableInterrupt(), and ADC12_B_disableInterrupt().
//
//*****************************************************************************
#define ADC12_B_IE16                                                (ADC12IE16)
#define ADC12_B_IE17                                                (ADC12IE17)
#define ADC12_B_IE18                                                (ADC12IE18)
#define ADC12_B_IE19                                                (ADC12IE19)
#define ADC12_B_IE20                                                (ADC12IE20)
#define ADC12_B_IE21                                                (ADC12IE21)
#define ADC12_B_IE22                                                (ADC12IE22)
#define ADC12_B_IE23                                                (ADC12IE23)
#define ADC12_B_IE24                                                (ADC12IE24)
#define ADC12_B_IE25                                                (ADC12IE25)
#define ADC12_B_IE26                                                (ADC12IE26)
#define ADC12_B_IE27                                                (ADC12IE27)
#define ADC12_B_IE28                                                (ADC12IE28)
#define ADC12_B_IE29                                                (ADC12IE29)
#define ADC12_B_IE30                                                (ADC12IE30)
#define ADC12_B_IE31                                                (ADC12IE31)

//*****************************************************************************
//
// The following are values that can be passed to the interruptMask2 parameter
// for functions: ADC12_B_enableInterrupt(), and ADC12_B_disableInterrupt().
//
//*****************************************************************************
#define ADC12_B_INIE                                                (ADC12INIE)
#define ADC12_B_LOIE                                                (ADC12LOIE)
#define ADC12_B_HIIE                                                (ADC12HIIE)
#define ADC12_B_OVIE                                                (ADC12OVIE)
#define ADC12_B_TOVIE                                              (ADC12TOVIE)
#define ADC12_B_RDYIE                                              (ADC12RDYIE)

//*****************************************************************************
//
// The following are values that can be passed to the memoryInterruptFlagMask
// parameter for functions: ADC12_B_clearInterrupt(), and
// ADC12_B_getInterruptStatus().
//
//*****************************************************************************
#define ADC12_B_IFG0                                                (ADC12IFG0)
#define ADC12_B_IFG1                                                (ADC12IFG1)
#define ADC12_B_IFG2                                                (ADC12IFG2)
#define ADC12_B_IFG3                                                (ADC12IFG3)
#define ADC12_B_IFG4                                                (ADC12IFG4)
#define ADC12_B_IFG5                                                (ADC12IFG5)
#define ADC12_B_IFG6                                                (ADC12IFG6)
#define ADC12_B_IFG7                                                (ADC12IFG7)
#define ADC12_B_IFG8                                                (ADC12IFG8)
#define ADC12_B_IFG9                                                (ADC12IFG9)
#define ADC12_B_IFG10                                              (ADC12IFG10)
#define ADC12_B_IFG11                                              (ADC12IFG11)
#define ADC12_B_IFG12                                              (ADC12IFG12)
#define ADC12_B_IFG13                                              (ADC12IFG13)
#define ADC12_B_IFG14                                              (ADC12IFG14)
#define ADC12_B_IFG15                                              (ADC12IFG15)
#define ADC12_B_IFG16                                              (ADC12IFG16)
#define ADC12_B_IFG17                                              (ADC12IFG17)
#define ADC12_B_IFG18                                              (ADC12IFG18)
#define ADC12_B_IFG19                                              (ADC12IFG19)
#define ADC12_B_IFG20                                              (ADC12IFG20)
#define ADC12_B_IFG21                                              (ADC12IFG21)
#define ADC12_B_IFG22                                              (ADC12IFG22)
#define ADC12_B_IFG23                                              (ADC12IFG23)
#define ADC12_B_IFG24                                              (ADC12IFG24)
#define ADC12_B_IFG25                                              (ADC12IFG25)
#define ADC12_B_IFG26                                              (ADC12IFG26)
#define ADC12_B_IFG27                                              (ADC12IFG27)
#define ADC12_B_IFG28                                              (ADC12IFG28)
#define ADC12_B_IFG29                                              (ADC12IFG29)
#define ADC12_B_IFG30                                              (ADC12IFG30)
#define ADC12_B_IFG31                                              (ADC12IFG31)
#define ADC12_B_INIFG                                              (ADC12INIFG)
#define ADC12_B_LOIFG                                              (ADC12LOIFG)
#define ADC12_B_HIIFG                                              (ADC12HIIFG)
#define ADC12_B_OVIFG                                              (ADC12OVIFG)
#define ADC12_B_TOVIFG                                            (ADC12TOVIFG)
#define ADC12_B_RDYIFG                                            (ADC12RDYIFG)

//*****************************************************************************
//
// The following are values that can be passed to the startingMemoryBufferIndex
// parameter for functions: ADC12_B_startConversion().
//
//*****************************************************************************
#define ADC12_B_START_AT_ADC12MEM0                           (ADC12CSTARTADD_0)
#define ADC12_B_START_AT_ADC12MEM1                           (ADC12CSTARTADD_1)
#define ADC12_B_START_AT_ADC12MEM2                           (ADC12CSTARTADD_2)
#define ADC12_B_START_AT_ADC12MEM3                           (ADC12CSTARTADD_3)
#define ADC12_B_START_AT_ADC12MEM4                           (ADC12CSTARTADD_4)
#define ADC12_B_START_AT_ADC12MEM5                           (ADC12CSTARTADD_5)
#define ADC12_B_START_AT_ADC12MEM6                           (ADC12CSTARTADD_6)
#define ADC12_B_START_AT_ADC12MEM7                           (ADC12CSTARTADD_7)
#define ADC12_B_START_AT_ADC12MEM8                           (ADC12CSTARTADD_8)
#define ADC12_B_START_AT_ADC12MEM9                           (ADC12CSTARTADD_9)
#define ADC12_B_START_AT_ADC12MEM10                         (ADC12CSTARTADD_10)
#define ADC12_B_START_AT_ADC12MEM11                         (ADC12CSTARTADD_11)
#define ADC12_B_START_AT_ADC12MEM12                         (ADC12CSTARTADD_12)
#define ADC12_B_START_AT_ADC12MEM13                         (ADC12CSTARTADD_13)
#define ADC12_B_START_AT_ADC12MEM14                         (ADC12CSTARTADD_14)
#define ADC12_B_START_AT_ADC12MEM15                         (ADC12CSTARTADD_15)
#define ADC12_B_START_AT_ADC12MEM16                         (ADC12CSTARTADD_16)
#define ADC12_B_START_AT_ADC12MEM17                         (ADC12CSTARTADD_17)
#define ADC12_B_START_AT_ADC12MEM18                         (ADC12CSTARTADD_18)
#define ADC12_B_START_AT_ADC12MEM19                         (ADC12CSTARTADD_19)
#define ADC12_B_START_AT_ADC12MEM20                         (ADC12CSTARTADD_20)
#define ADC12_B_START_AT_ADC12MEM21                         (ADC12CSTARTADD_21)
#define ADC12_B_START_AT_ADC12MEM22                         (ADC12CSTARTADD_22)
#define ADC12_B_START_AT_ADC12MEM23                         (ADC12CSTARTADD_23)
#define ADC12_B_START_AT_ADC12MEM24                         (ADC12CSTARTADD_24)
#define ADC12_B_START_AT_ADC12MEM25                         (ADC12CSTARTADD_25)
#define ADC12_B_START_AT_ADC12MEM26                         (ADC12CSTARTADD_26)
#define ADC12_B_START_AT_ADC12MEM27                         (ADC12CSTARTADD_27)
#define ADC12_B_START_AT_ADC12MEM28                         (ADC12CSTARTADD_28)
#define ADC12_B_START_AT_ADC12MEM29                         (ADC12CSTARTADD_29)
#define ADC12_B_START_AT_ADC12MEM30                         (ADC12CSTARTADD_30)
#define ADC12_B_START_AT_ADC12MEM31                         (ADC12CSTARTADD_31)

//*****************************************************************************
//
// The following are values that can be passed to the
// conversionSequenceModeSelect parameter for functions:
// ADC12_B_startConversion().
//
//*****************************************************************************
#define ADC12_B_SINGLECHANNEL                                   (ADC12CONSEQ_0)
#define ADC12_B_SEQOFCHANNELS                                   (ADC12CONSEQ_1)
#define ADC12_B_REPEATED_SINGLECHANNEL                          (ADC12CONSEQ_2)
#define ADC12_B_REPEATED_SEQOFCHANNELS                          (ADC12CONSEQ_3)

//*****************************************************************************
//
// The following are values that can be passed to the preempt parameter for
// functions: ADC12_B_disableConversions().
//
//*****************************************************************************
#define ADC12_B_COMPLETECONVERSION                                        false
#define ADC12_B_PREEMPTCONVERSION                                          true

//*****************************************************************************
//
// The following are values that can be passed to the resolutionSelect
// parameter for functions: ADC12_B_setResolution().
//
//*****************************************************************************
#define ADC12_B_RESOLUTION_8BIT                                (ADC12RES__8BIT)
#define ADC12_B_RESOLUTION_10BIT                              (ADC12RES__10BIT)
#define ADC12_B_RESOLUTION_12BIT                              (ADC12RES__12BIT)

//*****************************************************************************
//
// The following are values that can be passed to the invertedSignal parameter
// for functions: ADC12_B_setSampleHoldSignalInversion().
//
//*****************************************************************************
#define ADC12_B_NONINVERTEDSIGNAL                                (!(ADC12ISSH))
#define ADC12_B_INVERTEDSIGNAL                                      (ADC12ISSH)

//*****************************************************************************
//
// The following are values that can be passed to the readBackFormat parameter
// for functions: ADC12_B_setDataReadBackFormat().
//
//*****************************************************************************
#define ADC12_B_UNSIGNED_BINARY                                    (!(ADC12DF))
#define ADC12_B_SIGNED_2SCOMPLEMENT                                   (ADC12DF)

//*****************************************************************************
//
// The following are values that can be passed to the powerMode parameter for
// functions: ADC12_B_setAdcPowerMode().
//
//*****************************************************************************
#define ADC12_B_REGULARPOWERMODE                                (!(ADC12PWRMD))
#define ADC12_B_LOWPOWERMODE                                       (ADC12PWRMD)

//*****************************************************************************
//
// The following are values that can be passed toThe following are values that
// can be returned by the ADC12_B_isBusy() function.
//
//*****************************************************************************
#define ADC12_B_NOTBUSY                                                    0x00
#define ADC12_B_BUSY                                                  ADC12BUSY

//*****************************************************************************
//
// Prototypes for the APIs.
//
//*****************************************************************************

//*****************************************************************************
//
//! \brief Initializes the ADC12B Module.
//!
//! This function initializes the ADC module to allow for analog-to-digital
//! conversions. Specifically this function sets up the sample-and-hold signal
//! and clock sources for the ADC core to use for conversions. Upon successful
//! completion of the initialization all of the ADC control registers will be
//! reset, excluding the memory controls and reference module bits, the given
//! parameters will be set, and the ADC core will be turned on (Note, that the
//! ADC core only draws power during conversions and remains off when not
//! converting).Note that sample/hold signal sources are device dependent. Note
//! that if re-initializing the ADC after starting a conversion with the
//! startConversion() function, the disableConversion() must be called BEFORE
//! this function can be called.
//!
//! \param baseAddress is the base address of the ADC12B module.
//! \param param is the pointer to struct for initialization.
//!
//! \return STATUS_SUCCESS or STATUS_FAILURE of the initialization process.
//
//*****************************************************************************
extern bool ADC12_B_init(uint16_t baseAddress,
                         ADC12_B_initParam *param);

//*****************************************************************************
//
//! \brief Enables the ADC12B block.
//!
//! This will enable operation of the ADC12B block.
//!
//! \param baseAddress is the base address of the ADC12B module.
//!
//! Modified bits are \b ADC12ON of \b ADC12CTL0 register.
//!
//! \return None
//
//*****************************************************************************
extern void ADC12_B_enable(uint16_t baseAddress);

//*****************************************************************************
//
//! \brief Disables the ADC12B block.
//!
//! This will disable operation of the ADC12B block.
//!
//! \param baseAddress is the base address of the ADC12B module.
//!
//! Modified bits are \b ADC12ON of \b ADC12CTL0 register.
//!
//! \return None
//
//*****************************************************************************
extern void ADC12_B_disable(uint16_t baseAddress);

//*****************************************************************************
//
//! \brief Sets up and enables the Sampling Timer Pulse Mode.
//!
//! This function sets up the sampling timer pulse mode which allows the
//! sample/hold signal to trigger a sampling timer to sample-and-hold an input
//! signal for a specified number of clock cycles without having to hold the
//! sample/hold signal for the entire period of sampling. Note that if a
//! conversion has been started with the startConversion() function, then a
//! call to disableConversions() is required before this function may be
//! called.
//!
//! \param baseAddress is the base address of the ADC12B module.
//! \param clockCycleHoldCountLowMem sets the amount of clock cycles to sample-
//!        and-hold for the higher memory buffers 0-7.
//!        Valid values are:
//!        - \b ADC12_B_CYCLEHOLD_4_CYCLES [Default]
//!        - \b ADC12_B_CYCLEHOLD_8_CYCLES
//!        - \b ADC12_B_CYCLEHOLD_16_CYCLES
//!        - \b ADC12_B_CYCLEHOLD_32_CYCLES
//!        - \b ADC12_B_CYCLEHOLD_64_CYCLES
//!        - \b ADC12_B_CYCLEHOLD_96_CYCLES
//!        - \b ADC12_B_CYCLEHOLD_128_CYCLES
//!        - \b ADC12_B_CYCLEHOLD_192_CYCLES
//!        - \b ADC12_B_CYCLEHOLD_256_CYCLES
//!        - \b ADC12_B_CYCLEHOLD_384_CYCLES
//!        - \b ADC12_B_CYCLEHOLD_512_CYCLES
//!        - \b ADC12_B_CYCLEHOLD_768_CYCLES
//!        - \b ADC12_B_CYCLEHOLD_1024_CYCLES
//!        \n Modified bits are \b ADC12SHT0x of \b ADC12CTL0 register.
//! \param clockCycleHoldCountHighMem sets the amount of clock cycles to
//!        sample-and-hold for the higher memory buffers 8-15.
//!        Valid values are:
//!        - \b ADC12_B_CYCLEHOLD_4_CYCLES [Default]
//!        - \b ADC12_B_CYCLEHOLD_8_CYCLES
//!        - \b ADC12_B_CYCLEHOLD_16_CYCLES
//!        - \b ADC12_B_CYCLEHOLD_32_CYCLES
//!        - \b ADC12_B_CYCLEHOLD_64_CYCLES
//!        - \b ADC12_B_CYCLEHOLD_96_CYCLES
//!        - \b ADC12_B_CYCLEHOLD_128_CYCLES
//!        - \b ADC12_B_CYCLEHOLD_192_CYCLES
//!        - \b ADC12_B_CYCLEHOLD_256_CYCLES
//!        - \b ADC12_B_CYCLEHOLD_384_CYCLES
//!        - \b ADC12_B_CYCLEHOLD_512_CYCLES
//!        - \b ADC12_B_CYCLEHOLD_768_CYCLES
//!        - \b ADC12_B_CYCLEHOLD_1024_CYCLES
//!        \n Modified bits are \b ADC12SHT1x of \b ADC12CTL0 register.
//! \param multipleSamplesEnabled allows multiple conversions to start without
//!        a trigger signal from the sample/hold signal
//!        Valid values are:
//!        - \b ADC12_B_MULTIPLESAMPLESDISABLE [Default] - a timer trigger will
//!           be needed to start every ADC conversion.
//!        - \b ADC12_B_MULTIPLESAMPLESENABLE - during a sequenced and/or
//!           repeated conversion mode, after the first conversion, no
//!           sample/hold signal is necessary to start subsequent sample/hold
//!           and convert processes.
//!        \n Modified bits are \b ADC12MSC of \b ADC12CTL0 register.
//!
//! \return None
//
//*****************************************************************************
extern void ADC12_B_setupSamplingTimer(uint16_t baseAddress,
                                       uint16_t clockCycleHoldCountLowMem,
                                       uint16_t clockCycleHoldCountHighMem,
                                       uint16_t multipleSamplesEnabled);

//*****************************************************************************
//
//! \brief Disables Sampling Timer Pulse Mode.
//!
//! Disables the Sampling Timer Pulse Mode. Note that if a conversion has been
//! started with the startConversion() function, then a call to
//! disableConversions() is required before this function may be called.
//!
//! \param baseAddress is the base address of the ADC12B module.
//!
//! \return None
//
//*****************************************************************************
extern void ADC12_B_disableSamplingTimer(uint16_t baseAddress);

//*****************************************************************************
//
//! \brief Configures the controls of the selected memory buffer.
//!
//! Maps an input signal conversion into the selected memory buffer, as well as
//! the positive and negative reference voltages for each conversion being
//! stored into this memory buffer. If the internal reference is used for the
//! positive reference voltage, the internal REF module must be used to control
//! the voltage level. Note that if a conversion has been started with the
//! startConversion() function, then a call to disableConversions() is required
//! before this function may be called.
//!
//! \param baseAddress is the base address of the ADC12B module.
//! \param param is the pointer to struct for ADC12B memory configuration.
//!
//! \return None
//
//*****************************************************************************
extern void ADC12_B_configureMemory(uint16_t baseAddress,
                                    ADC12_B_configureMemoryParam *param);

//*****************************************************************************
//
//! \brief Sets the high and low threshold for the window comparator feature.
//!
//! Sets the high and low threshold for the window comparator feature. Use the
//! ADC12HIIE, ADC12INIE, ADC12LOIE interrupts to utilize this feature.
//!
//! \param baseAddress is the base address of the ADC12B module.
//! \param highThreshold is the upper bound that could trip an interrupt for
//!        the window comparator.
//! \param lowThreshold is the lower bound that could trip on interrupt for the
//!        window comparator.
//!
//! \return None
//
//*****************************************************************************
extern void ADC12_B_setWindowCompAdvanced(uint16_t baseAddress,
                                          uint16_t highThreshold,
                                          uint16_t lowThreshold);

//*****************************************************************************
//
//! \brief Enables selected ADC12B interrupt sources.
//!
//! Enables the indicated ADC12B interrupt sources.  Only the sources that are
//! enabled can be reflected to the processor interrupt; disabled sources have
//! no effect on the processor. <b>Does not clear interrupt flags.
//!
//! \param baseAddress is the base address of the ADC12B module.
//! \param interruptMask0 is the bit mask of the memory buffer and overflow
//!        interrupt sources to be enabled. If the desired interrupt is not
//!        available in the selection for interruptMask0, then simply pass in a
//!        '0' for this value.
//!        Valid values are:
//!        - \b ADC12_B_IE0
//!        - \b ADC12_B_IE1
//!        - \b ADC12_B_IE2
//!        - \b ADC12_B_IE3
//!        - \b ADC12_B_IE4
//!        - \b ADC12_B_IE5
//!        - \b ADC12_B_IE6
//!        - \b ADC12_B_IE7
//!        - \b ADC12_B_IE8
//!        - \b ADC12_B_IE9
//!        - \b ADC12_B_IE10
//!        - \b ADC12_B_IE11
//!        - \b ADC12_B_IE12
//!        - \b ADC12_B_IE13
//!        - \b ADC12_B_IE14
//!        - \b ADC12_B_IE15
//! \param interruptMask1 is the bit mask of the memory buffer and overflow
//!        interrupt sources to be enabled. If the desired interrupt is not
//!        available in the selection for interruptMask1, then simply pass in a
//!        '0' for this value.
//!        Valid values are:
//!        - \b ADC12_B_IE16
//!        - \b ADC12_B_IE17
//!        - \b ADC12_B_IE18
//!        - \b ADC12_B_IE19
//!        - \b ADC12_B_IE20
//!        - \b ADC12_B_IE21
//!        - \b ADC12_B_IE22
//!        - \b ADC12_B_IE23
//!        - \b ADC12_B_IE24
//!        - \b ADC12_B_IE25
//!        - \b ADC12_B_IE26
//!        - \b ADC12_B_IE27
//!        - \b ADC12_B_IE28
//!        - \b ADC12_B_IE29
//!        - \b ADC12_B_IE30
//!        - \b ADC12_B_IE31
//! \param interruptMask2 is the bit mask of the memory buffer and overflow
//!        interrupt sources to be enabled. If the desired interrupt is not
//!        available in the selection for interruptMask2, then simply pass in a
//!        '0' for this value.
//!        Valid values are:
//!        - \b ADC12_B_INIE - Interrupt enable for a conversion in the result
//!           register is either greater than the ADC12LO or lower than the
//!           ADC12HI threshold. GIE bit must be set to enable the interrupt.
//!        - \b ADC12_B_LOIE - Interrupt enable for the falling short of the
//!           lower limit interrupt of the window comparator for the result
//!           register. GIE bit must be set to enable the interrupt.
//!        - \b ADC12_B_HIIE - Interrupt enable for the exceeding the upper
//!           limit of the window comparator for the result register. GIE bit
//!           must be set to enable the interrupt.
//!        - \b ADC12_B_OVIE - Interrupt enable for a conversion that is about
//!           to save to a memory buffer that has not been read out yet. GIE
//!           bit must be set to enable the interrupt.
//!        - \b ADC12_B_TOVIE - enable for a conversion that is about to start
//!           before the previous conversion has been completed. GIE bit must
//!           be set to enable the interrupt.
//!        - \b ADC12_B_RDYIE - enable for the local buffered reference ready
//!           signal. GIE bit must be set to enable the interrupt.
//!
//! Modified bits of \b ADC12IERx register.
//!
//! \return None
//
//*****************************************************************************
extern void ADC12_B_enableInterrupt(uint16_t baseAddress,
                                    uint16_t interruptMask0,
                                    uint16_t interruptMask1,
                                    uint16_t interruptMask2);

//*****************************************************************************
//
//! \brief Disables selected ADC12B interrupt sources.
//!
//! Disables the indicated ADC12B interrupt sources. Only the sources that are
//! enabled can be reflected to the processor interrupt; disabled sources have
//! no effect on the processor.
//!
//! \param baseAddress is the base address of the ADC12B module.
//! \param interruptMask0 is the bit mask of the memory buffer and overflow
//!        interrupt sources to be disabled. If the desired interrupt is not
//!        available in the selection for interruptMask0, then simply pass in a
//!        '0' for this value.
//!        Valid values are:
//!        - \b ADC12_B_IE0
//!        - \b ADC12_B_IE1
//!        - \b ADC12_B_IE2
//!        - \b ADC12_B_IE3
//!        - \b ADC12_B_IE4
//!        - \b ADC12_B_IE5
//!        - \b ADC12_B_IE6
//!        - \b ADC12_B_IE7
//!        - \b ADC12_B_IE8
//!        - \b ADC12_B_IE9
//!        - \b ADC12_B_IE10
//!        - \b ADC12_B_IE11
//!        - \b ADC12_B_IE12
//!        - \b ADC12_B_IE13
//!        - \b ADC12_B_IE14
//!        - \b ADC12_B_IE15
//! \param interruptMask1 is the bit mask of the memory buffer and overflow
//!        interrupt sources to be disabled. If the desired interrupt is not
//!        available in the selection for interruptMask1, then simply pass in a
//!        '0' for this value.
//!        Valid values are:
//!        - \b ADC12_B_IE16
//!        - \b ADC12_B_IE17
//!        - \b ADC12_B_IE18
//!        - \b ADC12_B_IE19
//!        - \b ADC12_B_IE20
//!        - \b ADC12_B_IE21
//!        - \b ADC12_B_IE22
//!        - \b ADC12_B_IE23
//!        - \b ADC12_B_IE24
//!        - \b ADC12_B_IE25
//!        - \b ADC12_B_IE26
//!        - \b ADC12_B_IE27
//!        - \b ADC12_B_IE28
//!        - \b ADC12_B_IE29
//!        - \b ADC12_B_IE30
//!        - \b ADC12_B_IE31
//! \param interruptMask2 is the bit mask of the memory buffer and overflow
//!        interrupt sources to be disabled. If the desired interrupt is not
//!        available in the selection for interruptMask2, then simply pass in a
//!        '0' for this value.
//!        Valid values are:
//!        - \b ADC12_B_INIE - Interrupt enable for a conversion in the result
//!           register is either greater than the ADC12LO or lower than the
//!           ADC12HI threshold. GIE bit must be set to enable the interrupt.
//!        - \b ADC12_B_LOIE - Interrupt enable for the falling short of the
//!           lower limit interrupt of the window comparator for the result
//!           register. GIE bit must be set to enable the interrupt.
//!        - \b ADC12_B_HIIE - Interrupt enable for the exceeding the upper
//!           limit of the window comparator for the result register. GIE bit
//!           must be set to enable the interrupt.
//!        - \b ADC12_B_OVIE - Interrupt enable for a conversion that is about
//!           to save to a memory buffer that has not been read out yet. GIE
//!           bit must be set to enable the interrupt.
//!        - \b ADC12_B_TOVIE - enable for a conversion that is about to start
//!           before the previous conversion has been completed. GIE bit must
//!           be set to enable the interrupt.
//!        - \b ADC12_B_RDYIE - enable for the local buffered reference ready
//!           signal. GIE bit must be set to enable the interrupt.
//!
//! Modified bits of \b ADC12IERx register.
//!
//! \return None
//
//*****************************************************************************
extern void ADC12_B_disableInterrupt(uint16_t baseAddress,
                                     uint16_t interruptMask0,
                                     uint16_t interruptMask1,
                                     uint16_t interruptMask2);

//*****************************************************************************
//
//! \brief Clears ADC12B selected interrupt flags.
//!
//! Modified registers are ADC12IFG .
//!
//! \param baseAddress is the base address of the ADC12B module.
//! \param interruptRegisterChoice is either 0, 1, or 2, to choose the correct
//!        interrupt register to update
//! \param memoryInterruptFlagMask is the bit mask of the memory buffer and
//!        overflow interrupt flags to be cleared.
//!        Valid values are:
//!        - \b ADC12_B_IFG0 - interruptRegisterChoice = 0
//!        - \b ADC12_B_IFG1
//!        - \b ADC12_B_IFG2
//!        - \b ADC12_B_IFG3
//!        - \b ADC12_B_IFG4
//!        - \b ADC12_B_IFG5
//!        - \b ADC12_B_IFG6
//!        - \b ADC12_B_IFG7
//!        - \b ADC12_B_IFG8
//!        - \b ADC12_B_IFG9
//!        - \b ADC12_B_IFG10
//!        - \b ADC12_B_IFG11
//!        - \b ADC12_B_IFG12
//!        - \b ADC12_B_IFG13
//!        - \b ADC12_B_IFG14
//!        - \b ADC12_B_IFG15
//!        - \b ADC12_B_IFG16 - interruptRegisterChoice = 1
//!        - \b ADC12_B_IFG17
//!        - \b ADC12_B_IFG18
//!        - \b ADC12_B_IFG19
//!        - \b ADC12_B_IFG20
//!        - \b ADC12_B_IFG21
//!        - \b ADC12_B_IFG22
//!        - \b ADC12_B_IFG23
//!        - \b ADC12_B_IFG24
//!        - \b ADC12_B_IFG25
//!        - \b ADC12_B_IFG26
//!        - \b ADC12_B_IFG27
//!        - \b ADC12_B_IFG28
//!        - \b ADC12_B_IFG29
//!        - \b ADC12_B_IFG30
//!        - \b ADC12_B_IFG31
//!        - \b ADC12_B_INIFG - interruptRegisterChoice = 2
//!        - \b ADC12_B_LOIFG
//!        - \b ADC12_B_HIIFG
//!        - \b ADC12_B_OVIFG
//!        - \b ADC12_B_TOVIFG
//!        - \b ADC12_B_RDYIFG - The selected ADC12B interrupt flags are
//!           cleared, so that it no longer asserts. The memory buffer
//!           interrupt flags are only cleared when the memory buffer is
//!           accessed. Note that the overflow interrupts do not have an
//!           interrupt flag to clear; they must be accessed directly from the
//!           interrupt vector.
//!
//! \return None
//
//*****************************************************************************
extern void ADC12_B_clearInterrupt(uint16_t baseAddress,
                                   uint8_t interruptRegisterChoice,
                                   uint16_t memoryInterruptFlagMask);

//*****************************************************************************
//
//! \brief Returns the status of the selected memory interrupt flags.
//!
//! Returns the status of the selected memory interrupt flags. Note that the
//! overflow interrupts do not have an interrupt flag to clear; they must be
//! accessed directly from the interrupt vector.
//!
//! \param baseAddress is the base address of the ADC12B module.
//! \param interruptRegisterChoice is either 0, 1, or 2, to choose the correct
//!        interrupt register to update
//! \param memoryInterruptFlagMask is the bit mask of the memory buffer and
//!        overflow interrupt flags to be cleared.
//!        Valid values are:
//!        - \b ADC12_B_IFG0 - interruptRegisterChoice = 0
//!        - \b ADC12_B_IFG1
//!        - \b ADC12_B_IFG2
//!        - \b ADC12_B_IFG3
//!        - \b ADC12_B_IFG4
//!        - \b ADC12_B_IFG5
//!        - \b ADC12_B_IFG6
//!        - \b ADC12_B_IFG7
//!        - \b ADC12_B_IFG8
//!        - \b ADC12_B_IFG9
//!        - \b ADC12_B_IFG10
//!        - \b ADC12_B_IFG11
//!        - \b ADC12_B_IFG12
//!        - \b ADC12_B_IFG13
//!        - \b ADC12_B_IFG14
//!        - \b ADC12_B_IFG15
//!        - \b ADC12_B_IFG16 - interruptRegisterChoice = 1
//!        - \b ADC12_B_IFG17
//!        - \b ADC12_B_IFG18
//!        - \b ADC12_B_IFG19
//!        - \b ADC12_B_IFG20
//!        - \b ADC12_B_IFG21
//!        - \b ADC12_B_IFG22
//!        - \b ADC12_B_IFG23
//!        - \b ADC12_B_IFG24
//!        - \b ADC12_B_IFG25
//!        - \b ADC12_B_IFG26
//!        - \b ADC12_B_IFG27
//!        - \b ADC12_B_IFG28
//!        - \b ADC12_B_IFG29
//!        - \b ADC12_B_IFG30
//!        - \b ADC12_B_IFG31
//!        - \b ADC12_B_INIFG - interruptRegisterChoice = 2
//!        - \b ADC12_B_LOIFG
//!        - \b ADC12_B_HIIFG
//!        - \b ADC12_B_OVIFG
//!        - \b ADC12_B_TOVIFG
//!        - \b ADC12_B_RDYIFG - The selected ADC12B interrupt flags are
//!           cleared, so that it no longer asserts. The memory buffer
//!           interrupt flags are only cleared when the memory buffer is
//!           accessed. Note that the overflow interrupts do not have an
//!           interrupt flag to clear; they must be accessed directly from the
//!           interrupt vector.
//!
//! \return The current interrupt flag status for the corresponding mask.
//
//*****************************************************************************
extern uint16_t ADC12_B_getInterruptStatus(uint16_t baseAddress,
                                           uint8_t interruptRegisterChoice,
                                           uint16_t memoryInterruptFlagMask);

//*****************************************************************************
//
//! \brief Enables/Starts an Analog-to-Digital Conversion.
//!
//! Enables/starts the conversion process of the ADC. If the sample/hold signal
//! source chosen during initialization was ADC12OSC, then the conversion is
//! started immediately, otherwise the chosen sample/hold signal source starts
//! the conversion by a rising edge of the signal. Keep in mind when selecting
//! conversion modes, that for sequenced and/or repeated modes, to keep the
//! sample/hold-and-convert process continuing without a trigger from the
//! sample/hold signal source, the multiple samples must be enabled using the
//! ADC12_B_setupSamplingTimer() function. Note that after this function is
//! called, the ADC12_B_stopConversions() has to be called to re-initialize the
//! ADC, reconfigure a memory buffer control, enable/disable the sampling
//! timer, or to change the internal reference voltage.
//!
//! \param baseAddress is the base address of the ADC12B module.
//! \param startingMemoryBufferIndex is the memory buffer that will hold the
//!        first or only conversion.
//!        Valid values are:
//!        - \b ADC12_B_START_AT_ADC12MEM0 [Default]
//!        - \b ADC12_B_START_AT_ADC12MEM1
//!        - \b ADC12_B_START_AT_ADC12MEM2
//!        - \b ADC12_B_START_AT_ADC12MEM3
//!        - \b ADC12_B_START_AT_ADC12MEM4
//!        - \b ADC12_B_START_AT_ADC12MEM5
//!        - \b ADC12_B_START_AT_ADC12MEM6
//!        - \b ADC12_B_START_AT_ADC12MEM7
//!        - \b ADC12_B_START_AT_ADC12MEM8
//!        - \b ADC12_B_START_AT_ADC12MEM9
//!        - \b ADC12_B_START_AT_ADC12MEM10
//!        - \b ADC12_B_START_AT_ADC12MEM11
//!        - \b ADC12_B_START_AT_ADC12MEM12
//!        - \b ADC12_B_START_AT_ADC12MEM13
//!        - \b ADC12_B_START_AT_ADC12MEM14
//!        - \b ADC12_B_START_AT_ADC12MEM15
//!        - \b ADC12_B_START_AT_ADC12MEM16
//!        - \b ADC12_B_START_AT_ADC12MEM17
//!        - \b ADC12_B_START_AT_ADC12MEM18
//!        - \b ADC12_B_START_AT_ADC12MEM19
//!        - \b ADC12_B_START_AT_ADC12MEM20
//!        - \b ADC12_B_START_AT_ADC12MEM21
//!        - \b ADC12_B_START_AT_ADC12MEM22
//!        - \b ADC12_B_START_AT_ADC12MEM23
//!        - \b ADC12_B_START_AT_ADC12MEM24
//!        - \b ADC12_B_START_AT_ADC12MEM25
//!        - \b ADC12_B_START_AT_ADC12MEM26
//!        - \b ADC12_B_START_AT_ADC12MEM27
//!        - \b ADC12_B_START_AT_ADC12MEM28
//!        - \b ADC12_B_START_AT_ADC12MEM29
//!        - \b ADC12_B_START_AT_ADC12MEM30
//!        - \b ADC12_B_START_AT_ADC12MEM31
//!        \n Modified bits are \b ADC12CSTARTADDx of \b ADC12CTL1 register.
//! \param conversionSequenceModeSelect determines the ADC operating mode.
//!        Valid values are:
//!        - \b ADC12_B_SINGLECHANNEL [Default] - one-time conversion of a
//!           single channel into a single memory buffer.
//!        - \b ADC12_B_SEQOFCHANNELS - one time conversion of multiple
//!           channels into the specified starting memory buffer and each
//!           subsequent memory buffer up until the conversion is stored in a
//!           memory buffer dedicated as the end-of-sequence by the memory's
//!           control register.
//!        - \b ADC12_B_REPEATED_SINGLECHANNEL - repeated conversions of one
//!           channel into a single memory buffer.
//!        - \b ADC12_B_REPEATED_SEQOFCHANNELS - repeated conversions of
//!           multiple channels into the specified starting memory buffer and
//!           each subsequent memory buffer up until the conversion is stored
//!           in a memory buffer dedicated as the end-of-sequence by the
//!           memory's control register.
//!        \n Modified bits are \b ADC12CONSEQx of \b ADC12CTL1 register.
//!
//! Modified bits of \b ADC12CTL1 register and bits of \b ADC12CTL0 register.
//!
//! \return None
//
//*****************************************************************************
extern void ADC12_B_startConversion(uint16_t baseAddress,
                                    uint16_t startingMemoryBufferIndex,
                                    uint8_t conversionSequenceModeSelect);

//*****************************************************************************
//
//! \brief Disables the ADC from converting any more signals.
//!
//! Disables the ADC from converting any more signals. If there is a conversion
//! in progress, this function can stop it immediately if the preempt parameter
//! is set as ADC12_B_PREEMPTCONVERSION, by changing the conversion mode to
//! single-channel, single-conversion and disabling conversions. If the
//! conversion mode is set as single-channel, single-conversion and this
//! function is called without preemption, then the ADC core conversion status
//! is polled until the conversion is complete before disabling conversions to
//! prevent unpredictable data. If the ADC12_B_startConversion() has been
//! called, then this function has to be called to re-initialize the ADC,
//! reconfigure a memory buffer control, enable/disable the sampling pulse
//! mode, or change the internal reference voltage.
//!
//! \param baseAddress is the base address of the ADC12B module.
//! \param preempt specifies if the current conversion should be preemptively
//!        stopped before the end of the conversion.
//!        Valid values are:
//!        - \b ADC12_B_COMPLETECONVERSION - Allows the ADC12B to end the
//!           current conversion before disabling conversions.
//!        - \b ADC12_B_PREEMPTCONVERSION - Stops the ADC12B immediately, with
//!           unpredictable results of the current conversion.
//!
//! Modified bits of \b ADC12CTL1 register and bits of \b ADC12CTL0 register.
//!
//! \return None
//
//*****************************************************************************
extern void ADC12_B_disableConversions(uint16_t baseAddress,
                                       bool preempt);

//*****************************************************************************
//
//! \brief Returns the raw contents of the specified memory buffer.
//!
//! Returns the raw contents of the specified memory buffer. The format of the
//! content depends on the read-back format of the data: if the data is in
//! signed 2's complement format then the contents in the memory buffer will be
//! left-justified with the least-significant bits as 0's, whereas if the data
//! is in unsigned format then the contents in the memory buffer will be right-
//! justified with the most-significant bits as 0's.
//!
//! \param baseAddress is the base address of the ADC12B module.
//! \param memoryBufferIndex is the specified memory buffer to read.
//!        Valid values are:
//!        - \b ADC12_B_MEMORY_0
//!        - \b ADC12_B_MEMORY_1
//!        - \b ADC12_B_MEMORY_2
//!        - \b ADC12_B_MEMORY_3
//!        - \b ADC12_B_MEMORY_4
//!        - \b ADC12_B_MEMORY_5
//!        - \b ADC12_B_MEMORY_6
//!        - \b ADC12_B_MEMORY_7
//!        - \b ADC12_B_MEMORY_8
//!        - \b ADC12_B_MEMORY_9
//!        - \b ADC12_B_MEMORY_10
//!        - \b ADC12_B_MEMORY_11
//!        - \b ADC12_B_MEMORY_12
//!        - \b ADC12_B_MEMORY_13
//!        - \b ADC12_B_MEMORY_14
//!        - \b ADC12_B_MEMORY_15
//!        - \b ADC12_B_MEMORY_16
//!        - \b ADC12_B_MEMORY_17
//!        - \b ADC12_B_MEMORY_18
//!        - \b ADC12_B_MEMORY_19
//!        - \b ADC12_B_MEMORY_20
//!        - \b ADC12_B_MEMORY_21
//!        - \b ADC12_B_MEMORY_22
//!        - \b ADC12_B_MEMORY_23
//!        - \b ADC12_B_MEMORY_24
//!        - \b ADC12_B_MEMORY_25
//!        - \b ADC12_B_MEMORY_26
//!        - \b ADC12_B_MEMORY_27
//!        - \b ADC12_B_MEMORY_28
//!        - \b ADC12_B_MEMORY_29
//!        - \b ADC12_B_MEMORY_30
//!        - \b ADC12_B_MEMORY_31
//!
//! \return A signed integer of the contents of the specified memory buffer.
//
//*****************************************************************************
extern uint16_t ADC12_B_getResults(uint16_t baseAddress,
                                   uint8_t memoryBufferIndex);

//*****************************************************************************
//
//! \brief Use to change the resolution of the converted data.
//!
//! This function can be used to change the resolution of the converted data
//! from the default of 12-bits.
//!
//! \param baseAddress is the base address of the ADC12B module.
//! \param resolutionSelect determines the resolution of the converted data.
//!        Valid values are:
//!        - \b ADC12_B_RESOLUTION_8BIT
//!        - \b ADC12_B_RESOLUTION_10BIT
//!        - \b ADC12_B_RESOLUTION_12BIT [Default]
//!        \n Modified bits are \b ADC12RESx of \b ADC12CTL2 register.
//!
//! \return None
//
//*****************************************************************************
extern void ADC12_B_setResolution(uint16_t baseAddress,
                                  uint8_t resolutionSelect);

//*****************************************************************************
//
//! \brief Use to invert or un-invert the sample/hold signal.
//!
//! This function can be used to invert or un-invert the sample/hold signal.
//! Note that if a conversion has been started with the startConversion()
//! function, then a call to disableConversions() is required before this
//! function may be called.
//!
//! \param baseAddress is the base address of the ADC12B module.
//! \param invertedSignal set if the sample/hold signal should be inverted
//!        Valid values are:
//!        - \b ADC12_B_NONINVERTEDSIGNAL [Default] - a sample-and-hold of an
//!           input signal for conversion will be started on a rising edge of
//!           the sample/hold signal.
//!        - \b ADC12_B_INVERTEDSIGNAL - a sample-and-hold of an input signal
//!           for conversion will be started on a falling edge of the
//!           sample/hold signal.
//!        \n Modified bits are \b ADC12ISSH of \b ADC12CTL1 register.
//!
//! \return None
//
//*****************************************************************************
extern void ADC12_B_setSampleHoldSignalInversion(uint16_t baseAddress,
                                                 uint16_t invertedSignal);

//*****************************************************************************
//
//! \brief Use to set the read-back format of the converted data.
//!
//! Sets the format of the converted data: how it will be stored into the
//! memory buffer, and how it should be read back. The format can be set as
//! right-justified (default), which indicates that the number will be
//! unsigned, or left-justified, which indicates that the number will be signed
//! in 2's complement format. This change affects all memory buffers for
//! subsequent conversions.
//!
//! \param baseAddress is the base address of the ADC12B module.
//! \param readBackFormat is the specified format to store the conversions in
//!        the memory buffer.
//!        Valid values are:
//!        - \b ADC12_B_UNSIGNED_BINARY [Default]
//!        - \b ADC12_B_SIGNED_2SCOMPLEMENT
//!        \n Modified bits are \b ADC12DF of \b ADC12CTL2 register.
//!
//! \return None
//
//*****************************************************************************
extern void ADC12_B_setDataReadBackFormat(uint16_t baseAddress,
                                          uint8_t readBackFormat);

//*****************************************************************************
//
//! \brief Use to set the ADC's power conservation mode if the sampling rate is
//! at 50-ksps or less.
//!
//! Sets ADC's power mode. If the user has a sampling rate greater than
//! 50-ksps, then he/she can only enable ADC12_B_REGULARPOWERMODE. If the
//! sampling rate is 50-ksps or less, the user can enable ADC12_B_LOWPOWERMODE
//! granting additional power savings.
//!
//! \param baseAddress is the base address of the ADC12B module.
//! \param powerMode is the specified maximum sampling rate.
//!        Valid values are:
//!        - \b ADC12_B_REGULARPOWERMODE [Default] - If sampling rate is
//!           greater than 50-ksps, there is no power saving feature available.
//!        - \b ADC12_B_LOWPOWERMODE - If sampling rate is less than or equal
//!           to 50-ksps, select this value to save power
//!        \n Modified bits are \b ADC12SR of \b ADC12CTL2 register.
//!
//! \return None
//
//*****************************************************************************
extern void ADC12_B_setAdcPowerMode(uint16_t baseAddress,
                                    uint8_t powerMode);

//*****************************************************************************
//
//! \brief Returns the address of the specified memory buffer for the DMA
//! module.
//!
//! Returns the address of the specified memory buffer. This can be used in
//! conjunction with the DMA to store the converted data directly to memory.
//!
//! \param baseAddress is the base address of the ADC12B module.
//! \param memoryIndex is the memory buffer to return the address of.
//!        Valid values are:
//!        - \b ADC12_B_MEMORY_0
//!        - \b ADC12_B_MEMORY_1
//!        - \b ADC12_B_MEMORY_2
//!        - \b ADC12_B_MEMORY_3
//!        - \b ADC12_B_MEMORY_4
//!        - \b ADC12_B_MEMORY_5
//!        - \b ADC12_B_MEMORY_6
//!        - \b ADC12_B_MEMORY_7
//!        - \b ADC12_B_MEMORY_8
//!        - \b ADC12_B_MEMORY_9
//!        - \b ADC12_B_MEMORY_10
//!        - \b ADC12_B_MEMORY_11
//!        - \b ADC12_B_MEMORY_12
//!        - \b ADC12_B_MEMORY_13
//!        - \b ADC12_B_MEMORY_14
//!        - \b ADC12_B_MEMORY_15
//!        - \b ADC12_B_MEMORY_16
//!        - \b ADC12_B_MEMORY_17
//!        - \b ADC12_B_MEMORY_18
//!        - \b ADC12_B_MEMORY_19
//!        - \b ADC12_B_MEMORY_20
//!        - \b ADC12_B_MEMORY_21
//!        - \b ADC12_B_MEMORY_22
//!        - \b ADC12_B_MEMORY_23
//!        - \b ADC12_B_MEMORY_24
//!        - \b ADC12_B_MEMORY_25
//!        - \b ADC12_B_MEMORY_26
//!        - \b ADC12_B_MEMORY_27
//!        - \b ADC12_B_MEMORY_28
//!        - \b ADC12_B_MEMORY_29
//!        - \b ADC12_B_MEMORY_30
//!        - \b ADC12_B_MEMORY_31
//!
//! \return address of the specified memory buffer
//
//*****************************************************************************
extern uint32_t ADC12_B_getMemoryAddressForDMA(uint16_t baseAddress,
                                               uint8_t memoryIndex);

//*****************************************************************************
//
//! \brief Returns the busy status of the ADC12B core.
//!
//! Returns the status of the ADC core if there is a conversion currently
//! taking place.
//!
//! \param baseAddress is the base address of the ADC12B module.
//!
//! \return ADC12_B_BUSY or ADC12_B_NOTBUSY dependent if there is a conversion
//!         currently taking place.
//!         Return one of the following:
//!         - \b ADC12_B_NOTBUSY
//!         - \b ADC12_B_BUSY
//!         \n indicating if a conversion is taking place
//
//*****************************************************************************
extern uint8_t ADC12_B_isBusy(uint16_t baseAddress);

//*****************************************************************************
//
// Mark the end of the C bindings section for C++ compilers.
//
//*****************************************************************************
#ifdef __cplusplus
}
#endif

#endif
#endif // __MSP430WARE_ADC12_B_H__
