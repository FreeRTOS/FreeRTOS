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
// timer_a.h - Driver for the TIMER_A Module.
//
//*****************************************************************************

#ifndef __MSP430WARE_TIMER_A_H__
#define __MSP430WARE_TIMER_A_H__

#include "inc/hw_memmap.h"

#ifdef __MSP430_HAS_TxA7__

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
// The following is a parameter used for Timer_A_getCounterValue that
// determines the maximum difference in counts of the TAxR register for a
// majority vote.
//
//*****************************************************************************
#define TIMER_A_THRESHOLD                                                    50

//*****************************************************************************
//
//! \brief Used in the Timer_A_initContinuousMode() function as the param
//! parameter.
//
//*****************************************************************************
typedef struct Timer_A_initContinuousModeParam
{
    //! Selects Clock source.
    //! \n Valid values are:
    //! - \b TIMER_A_CLOCKSOURCE_EXTERNAL_TXCLK [Default]
    //! - \b TIMER_A_CLOCKSOURCE_ACLK
    //! - \b TIMER_A_CLOCKSOURCE_SMCLK
    //! - \b TIMER_A_CLOCKSOURCE_INVERTED_EXTERNAL_TXCLK
    uint16_t clockSource;
    //! Is the desired divider for the clock source
    //! \n Valid values are:
    //! - \b TIMER_A_CLOCKSOURCE_DIVIDER_1 [Default]
    //! - \b TIMER_A_CLOCKSOURCE_DIVIDER_2
    //! - \b TIMER_A_CLOCKSOURCE_DIVIDER_3
    //! - \b TIMER_A_CLOCKSOURCE_DIVIDER_4
    //! - \b TIMER_A_CLOCKSOURCE_DIVIDER_5
    //! - \b TIMER_A_CLOCKSOURCE_DIVIDER_6
    //! - \b TIMER_A_CLOCKSOURCE_DIVIDER_7
    //! - \b TIMER_A_CLOCKSOURCE_DIVIDER_8
    //! - \b TIMER_A_CLOCKSOURCE_DIVIDER_10
    //! - \b TIMER_A_CLOCKSOURCE_DIVIDER_12
    //! - \b TIMER_A_CLOCKSOURCE_DIVIDER_14
    //! - \b TIMER_A_CLOCKSOURCE_DIVIDER_16
    //! - \b TIMER_A_CLOCKSOURCE_DIVIDER_20
    //! - \b TIMER_A_CLOCKSOURCE_DIVIDER_24
    //! - \b TIMER_A_CLOCKSOURCE_DIVIDER_28
    //! - \b TIMER_A_CLOCKSOURCE_DIVIDER_32
    //! - \b TIMER_A_CLOCKSOURCE_DIVIDER_40
    //! - \b TIMER_A_CLOCKSOURCE_DIVIDER_48
    //! - \b TIMER_A_CLOCKSOURCE_DIVIDER_56
    //! - \b TIMER_A_CLOCKSOURCE_DIVIDER_64
    uint16_t clockSourceDivider;
    //! Is to enable or disable Timer_A interrupt
    //! \n Valid values are:
    //! - \b TIMER_A_TAIE_INTERRUPT_ENABLE
    //! - \b TIMER_A_TAIE_INTERRUPT_DISABLE [Default]
    uint16_t timerInterruptEnable_TAIE;
    //! Decides if Timer_A clock divider, count direction, count need to be
    //! reset.
    //! \n Valid values are:
    //! - \b TIMER_A_DO_CLEAR
    //! - \b TIMER_A_SKIP_CLEAR [Default]
    uint16_t timerClear;
    //! Whether to start the timer immediately
    bool startTimer;
} Timer_A_initContinuousModeParam;

//*****************************************************************************
//
//! \brief Used in the Timer_A_initCaptureMode() function as the param
//! parameter.
//
//*****************************************************************************
typedef struct Timer_A_initCaptureModeParam
{
    //! Selects the Capture register being used. Refer to datasheet to ensure
    //! the device has the capture compare register being used.
    //! \n Valid values are:
    //! - \b TIMER_A_CAPTURECOMPARE_REGISTER_0
    //! - \b TIMER_A_CAPTURECOMPARE_REGISTER_1
    //! - \b TIMER_A_CAPTURECOMPARE_REGISTER_2
    //! - \b TIMER_A_CAPTURECOMPARE_REGISTER_3
    //! - \b TIMER_A_CAPTURECOMPARE_REGISTER_4
    //! - \b TIMER_A_CAPTURECOMPARE_REGISTER_5
    //! - \b TIMER_A_CAPTURECOMPARE_REGISTER_6
    uint16_t captureRegister;
    //! Is the capture mode selected.
    //! \n Valid values are:
    //! - \b TIMER_A_CAPTUREMODE_NO_CAPTURE [Default]
    //! - \b TIMER_A_CAPTUREMODE_RISING_EDGE
    //! - \b TIMER_A_CAPTUREMODE_FALLING_EDGE
    //! - \b TIMER_A_CAPTUREMODE_RISING_AND_FALLING_EDGE
    uint16_t captureMode;
    //! Decides the Input Select
    //! \n Valid values are:
    //! - \b TIMER_A_CAPTURE_INPUTSELECT_CCIxA
    //! - \b TIMER_A_CAPTURE_INPUTSELECT_CCIxB
    //! - \b TIMER_A_CAPTURE_INPUTSELECT_GND
    //! - \b TIMER_A_CAPTURE_INPUTSELECT_Vcc
    uint16_t captureInputSelect;
    //! Decides if capture source should be synchronized with timer clock
    //! \n Valid values are:
    //! - \b TIMER_A_CAPTURE_ASYNCHRONOUS [Default]
    //! - \b TIMER_A_CAPTURE_SYNCHRONOUS
    uint16_t synchronizeCaptureSource;
    //! Is to enable or disable timer captureComapre interrupt.
    //! \n Valid values are:
    //! - \b TIMER_A_CAPTURECOMPARE_INTERRUPT_DISABLE [Default]
    //! - \b TIMER_A_CAPTURECOMPARE_INTERRUPT_ENABLE
    uint16_t captureInterruptEnable;
    //! Specifies the output mode.
    //! \n Valid values are:
    //! - \b TIMER_A_OUTPUTMODE_OUTBITVALUE [Default]
    //! - \b TIMER_A_OUTPUTMODE_SET
    //! - \b TIMER_A_OUTPUTMODE_TOGGLE_RESET
    //! - \b TIMER_A_OUTPUTMODE_SET_RESET
    //! - \b TIMER_A_OUTPUTMODE_TOGGLE
    //! - \b TIMER_A_OUTPUTMODE_RESET
    //! - \b TIMER_A_OUTPUTMODE_TOGGLE_SET
    //! - \b TIMER_A_OUTPUTMODE_RESET_SET
    uint16_t captureOutputMode;
} Timer_A_initCaptureModeParam;

//*****************************************************************************
//
//! \brief Used in the Timer_A_initUpDownMode() function as the param
//! parameter.
//
//*****************************************************************************
typedef struct Timer_A_initUpDownModeParam
{
    //! Selects Clock source.
    //! \n Valid values are:
    //! - \b TIMER_A_CLOCKSOURCE_EXTERNAL_TXCLK [Default]
    //! - \b TIMER_A_CLOCKSOURCE_ACLK
    //! - \b TIMER_A_CLOCKSOURCE_SMCLK
    //! - \b TIMER_A_CLOCKSOURCE_INVERTED_EXTERNAL_TXCLK
    uint16_t clockSource;
    //! Is the desired divider for the clock source
    //! \n Valid values are:
    //! - \b TIMER_A_CLOCKSOURCE_DIVIDER_1 [Default]
    //! - \b TIMER_A_CLOCKSOURCE_DIVIDER_2
    //! - \b TIMER_A_CLOCKSOURCE_DIVIDER_3
    //! - \b TIMER_A_CLOCKSOURCE_DIVIDER_4
    //! - \b TIMER_A_CLOCKSOURCE_DIVIDER_5
    //! - \b TIMER_A_CLOCKSOURCE_DIVIDER_6
    //! - \b TIMER_A_CLOCKSOURCE_DIVIDER_7
    //! - \b TIMER_A_CLOCKSOURCE_DIVIDER_8
    //! - \b TIMER_A_CLOCKSOURCE_DIVIDER_10
    //! - \b TIMER_A_CLOCKSOURCE_DIVIDER_12
    //! - \b TIMER_A_CLOCKSOURCE_DIVIDER_14
    //! - \b TIMER_A_CLOCKSOURCE_DIVIDER_16
    //! - \b TIMER_A_CLOCKSOURCE_DIVIDER_20
    //! - \b TIMER_A_CLOCKSOURCE_DIVIDER_24
    //! - \b TIMER_A_CLOCKSOURCE_DIVIDER_28
    //! - \b TIMER_A_CLOCKSOURCE_DIVIDER_32
    //! - \b TIMER_A_CLOCKSOURCE_DIVIDER_40
    //! - \b TIMER_A_CLOCKSOURCE_DIVIDER_48
    //! - \b TIMER_A_CLOCKSOURCE_DIVIDER_56
    //! - \b TIMER_A_CLOCKSOURCE_DIVIDER_64
    uint16_t clockSourceDivider;
    //! Is the specified Timer_A period
    uint16_t timerPeriod;
    //! Is to enable or disable Timer_A interrupt
    //! \n Valid values are:
    //! - \b TIMER_A_TAIE_INTERRUPT_ENABLE
    //! - \b TIMER_A_TAIE_INTERRUPT_DISABLE [Default]
    uint16_t timerInterruptEnable_TAIE;
    //! Is to enable or disable Timer_A CCR0 captureComapre interrupt.
    //! \n Valid values are:
    //! - \b TIMER_A_CCIE_CCR0_INTERRUPT_ENABLE
    //! - \b TIMER_A_CCIE_CCR0_INTERRUPT_DISABLE [Default]
    uint16_t captureCompareInterruptEnable_CCR0_CCIE;
    //! Decides if Timer_A clock divider, count direction, count need to be
    //! reset.
    //! \n Valid values are:
    //! - \b TIMER_A_DO_CLEAR
    //! - \b TIMER_A_SKIP_CLEAR [Default]
    uint16_t timerClear;
    //! Whether to start the timer immediately
    bool startTimer;
} Timer_A_initUpDownModeParam;

//*****************************************************************************
//
//! \brief Used in the Timer_A_outputPWM() function as the param parameter.
//
//*****************************************************************************
typedef struct Timer_A_outputPWMParam
{
    //! Selects Clock source.
    //! \n Valid values are:
    //! - \b TIMER_A_CLOCKSOURCE_EXTERNAL_TXCLK [Default]
    //! - \b TIMER_A_CLOCKSOURCE_ACLK
    //! - \b TIMER_A_CLOCKSOURCE_SMCLK
    //! - \b TIMER_A_CLOCKSOURCE_INVERTED_EXTERNAL_TXCLK
    uint16_t clockSource;
    //! Is the desired divider for the clock source
    //! \n Valid values are:
    //! - \b TIMER_A_CLOCKSOURCE_DIVIDER_1 [Default]
    //! - \b TIMER_A_CLOCKSOURCE_DIVIDER_2
    //! - \b TIMER_A_CLOCKSOURCE_DIVIDER_3
    //! - \b TIMER_A_CLOCKSOURCE_DIVIDER_4
    //! - \b TIMER_A_CLOCKSOURCE_DIVIDER_5
    //! - \b TIMER_A_CLOCKSOURCE_DIVIDER_6
    //! - \b TIMER_A_CLOCKSOURCE_DIVIDER_7
    //! - \b TIMER_A_CLOCKSOURCE_DIVIDER_8
    //! - \b TIMER_A_CLOCKSOURCE_DIVIDER_10
    //! - \b TIMER_A_CLOCKSOURCE_DIVIDER_12
    //! - \b TIMER_A_CLOCKSOURCE_DIVIDER_14
    //! - \b TIMER_A_CLOCKSOURCE_DIVIDER_16
    //! - \b TIMER_A_CLOCKSOURCE_DIVIDER_20
    //! - \b TIMER_A_CLOCKSOURCE_DIVIDER_24
    //! - \b TIMER_A_CLOCKSOURCE_DIVIDER_28
    //! - \b TIMER_A_CLOCKSOURCE_DIVIDER_32
    //! - \b TIMER_A_CLOCKSOURCE_DIVIDER_40
    //! - \b TIMER_A_CLOCKSOURCE_DIVIDER_48
    //! - \b TIMER_A_CLOCKSOURCE_DIVIDER_56
    //! - \b TIMER_A_CLOCKSOURCE_DIVIDER_64
    uint16_t clockSourceDivider;
    //! Selects the desired timer period
    uint16_t timerPeriod;
    //! Selects the compare register being used. Refer to datasheet to ensure
    //! the device has the capture compare register being used.
    //! \n Valid values are:
    //! - \b TIMER_A_CAPTURECOMPARE_REGISTER_0
    //! - \b TIMER_A_CAPTURECOMPARE_REGISTER_1
    //! - \b TIMER_A_CAPTURECOMPARE_REGISTER_2
    //! - \b TIMER_A_CAPTURECOMPARE_REGISTER_3
    //! - \b TIMER_A_CAPTURECOMPARE_REGISTER_4
    //! - \b TIMER_A_CAPTURECOMPARE_REGISTER_5
    //! - \b TIMER_A_CAPTURECOMPARE_REGISTER_6
    uint16_t compareRegister;
    //! Specifies the output mode.
    //! \n Valid values are:
    //! - \b TIMER_A_OUTPUTMODE_OUTBITVALUE [Default]
    //! - \b TIMER_A_OUTPUTMODE_SET
    //! - \b TIMER_A_OUTPUTMODE_TOGGLE_RESET
    //! - \b TIMER_A_OUTPUTMODE_SET_RESET
    //! - \b TIMER_A_OUTPUTMODE_TOGGLE
    //! - \b TIMER_A_OUTPUTMODE_RESET
    //! - \b TIMER_A_OUTPUTMODE_TOGGLE_SET
    //! - \b TIMER_A_OUTPUTMODE_RESET_SET
    uint16_t compareOutputMode;
    //! Specifies the dutycycle for the generated waveform
    uint16_t dutyCycle;
} Timer_A_outputPWMParam;

//*****************************************************************************
//
//! \brief Used in the Timer_A_initUpMode() function as the param parameter.
//
//*****************************************************************************
typedef struct Timer_A_initUpModeParam
{
    //! Selects Clock source.
    //! \n Valid values are:
    //! - \b TIMER_A_CLOCKSOURCE_EXTERNAL_TXCLK [Default]
    //! - \b TIMER_A_CLOCKSOURCE_ACLK
    //! - \b TIMER_A_CLOCKSOURCE_SMCLK
    //! - \b TIMER_A_CLOCKSOURCE_INVERTED_EXTERNAL_TXCLK
    uint16_t clockSource;
    //! Is the desired divider for the clock source
    //! \n Valid values are:
    //! - \b TIMER_A_CLOCKSOURCE_DIVIDER_1 [Default]
    //! - \b TIMER_A_CLOCKSOURCE_DIVIDER_2
    //! - \b TIMER_A_CLOCKSOURCE_DIVIDER_3
    //! - \b TIMER_A_CLOCKSOURCE_DIVIDER_4
    //! - \b TIMER_A_CLOCKSOURCE_DIVIDER_5
    //! - \b TIMER_A_CLOCKSOURCE_DIVIDER_6
    //! - \b TIMER_A_CLOCKSOURCE_DIVIDER_7
    //! - \b TIMER_A_CLOCKSOURCE_DIVIDER_8
    //! - \b TIMER_A_CLOCKSOURCE_DIVIDER_10
    //! - \b TIMER_A_CLOCKSOURCE_DIVIDER_12
    //! - \b TIMER_A_CLOCKSOURCE_DIVIDER_14
    //! - \b TIMER_A_CLOCKSOURCE_DIVIDER_16
    //! - \b TIMER_A_CLOCKSOURCE_DIVIDER_20
    //! - \b TIMER_A_CLOCKSOURCE_DIVIDER_24
    //! - \b TIMER_A_CLOCKSOURCE_DIVIDER_28
    //! - \b TIMER_A_CLOCKSOURCE_DIVIDER_32
    //! - \b TIMER_A_CLOCKSOURCE_DIVIDER_40
    //! - \b TIMER_A_CLOCKSOURCE_DIVIDER_48
    //! - \b TIMER_A_CLOCKSOURCE_DIVIDER_56
    //! - \b TIMER_A_CLOCKSOURCE_DIVIDER_64
    uint16_t clockSourceDivider;
    //! Is the specified Timer_A period. This is the value that gets written
    //! into the CCR0. Limited to 16 bits[uint16_t]
    uint16_t timerPeriod;
    //! Is to enable or disable Timer_A interrupt
    //! \n Valid values are:
    //! - \b TIMER_A_TAIE_INTERRUPT_ENABLE
    //! - \b TIMER_A_TAIE_INTERRUPT_DISABLE [Default]
    uint16_t timerInterruptEnable_TAIE;
    //! Is to enable or disable Timer_A CCR0 captureComapre interrupt.
    //! \n Valid values are:
    //! - \b TIMER_A_CCIE_CCR0_INTERRUPT_ENABLE
    //! - \b TIMER_A_CCIE_CCR0_INTERRUPT_DISABLE [Default]
    uint16_t captureCompareInterruptEnable_CCR0_CCIE;
    //! Decides if Timer_A clock divider, count direction, count need to be
    //! reset.
    //! \n Valid values are:
    //! - \b TIMER_A_DO_CLEAR
    //! - \b TIMER_A_SKIP_CLEAR [Default]
    uint16_t timerClear;
    //! Whether to start the timer immediately
    bool startTimer;
} Timer_A_initUpModeParam;

//*****************************************************************************
//
//! \brief Used in the Timer_A_initCompareMode() function as the param
//! parameter.
//
//*****************************************************************************
typedef struct Timer_A_initCompareModeParam
{
    //! Selects the Capture register being used. Refer to datasheet to ensure
    //! the device has the capture compare register being used.
    //! \n Valid values are:
    //! - \b TIMER_A_CAPTURECOMPARE_REGISTER_0
    //! - \b TIMER_A_CAPTURECOMPARE_REGISTER_1
    //! - \b TIMER_A_CAPTURECOMPARE_REGISTER_2
    //! - \b TIMER_A_CAPTURECOMPARE_REGISTER_3
    //! - \b TIMER_A_CAPTURECOMPARE_REGISTER_4
    //! - \b TIMER_A_CAPTURECOMPARE_REGISTER_5
    //! - \b TIMER_A_CAPTURECOMPARE_REGISTER_6
    uint16_t compareRegister;
    //! Is to enable or disable timer captureComapre interrupt.
    //! \n Valid values are:
    //! - \b TIMER_A_CAPTURECOMPARE_INTERRUPT_DISABLE [Default]
    //! - \b TIMER_A_CAPTURECOMPARE_INTERRUPT_ENABLE
    uint16_t compareInterruptEnable;
    //! Specifies the output mode.
    //! \n Valid values are:
    //! - \b TIMER_A_OUTPUTMODE_OUTBITVALUE [Default]
    //! - \b TIMER_A_OUTPUTMODE_SET
    //! - \b TIMER_A_OUTPUTMODE_TOGGLE_RESET
    //! - \b TIMER_A_OUTPUTMODE_SET_RESET
    //! - \b TIMER_A_OUTPUTMODE_TOGGLE
    //! - \b TIMER_A_OUTPUTMODE_RESET
    //! - \b TIMER_A_OUTPUTMODE_TOGGLE_SET
    //! - \b TIMER_A_OUTPUTMODE_RESET_SET
    uint16_t compareOutputMode;
    //! Is the count to be compared with in compare mode
    uint16_t compareValue;
} Timer_A_initCompareModeParam;

//*****************************************************************************
//
// The following are values that can be passed to the param parameter for
// functions: Timer_A_initContinuousMode(), Timer_A_initUpMode(),
// Timer_A_initUpDownMode(), and Timer_A_outputPWM().
//
//*****************************************************************************
#define TIMER_A_CLOCKSOURCE_DIVIDER_1                                      0x00
#define TIMER_A_CLOCKSOURCE_DIVIDER_2                                      0x08
#define TIMER_A_CLOCKSOURCE_DIVIDER_3                                      0x02
#define TIMER_A_CLOCKSOURCE_DIVIDER_4                                      0x10
#define TIMER_A_CLOCKSOURCE_DIVIDER_5                                      0x04
#define TIMER_A_CLOCKSOURCE_DIVIDER_6                                      0x05
#define TIMER_A_CLOCKSOURCE_DIVIDER_7                                      0x06
#define TIMER_A_CLOCKSOURCE_DIVIDER_8                                      0x18
#define TIMER_A_CLOCKSOURCE_DIVIDER_10                                     0x0C
#define TIMER_A_CLOCKSOURCE_DIVIDER_12                                     0x0D
#define TIMER_A_CLOCKSOURCE_DIVIDER_14                                     0x0E
#define TIMER_A_CLOCKSOURCE_DIVIDER_16                                     0x0F
#define TIMER_A_CLOCKSOURCE_DIVIDER_20                                     0x14
#define TIMER_A_CLOCKSOURCE_DIVIDER_24                                     0x15
#define TIMER_A_CLOCKSOURCE_DIVIDER_28                                     0x16
#define TIMER_A_CLOCKSOURCE_DIVIDER_32                                     0x17
#define TIMER_A_CLOCKSOURCE_DIVIDER_40                                     0x1C
#define TIMER_A_CLOCKSOURCE_DIVIDER_48                                     0x1D
#define TIMER_A_CLOCKSOURCE_DIVIDER_56                                     0x1E
#define TIMER_A_CLOCKSOURCE_DIVIDER_64                                     0x1F

//*****************************************************************************
//
// The following are values that can be passed to the timerMode parameter for
// functions: Timer_A_startCounter().
//
//*****************************************************************************
#define TIMER_A_STOP_MODE                                                  MC_0
#define TIMER_A_UP_MODE                                                    MC_1
#define TIMER_A_CONTINUOUS_MODE                                            MC_2
#define TIMER_A_UPDOWN_MODE                                                MC_3

//*****************************************************************************
//
// The following are values that can be passed to the param parameter for
// functions: Timer_A_initContinuousMode(), Timer_A_initUpMode(), and
// Timer_A_initUpDownMode().
//
//*****************************************************************************
#define TIMER_A_DO_CLEAR                                                  TACLR
#define TIMER_A_SKIP_CLEAR                                                 0x00

//*****************************************************************************
//
// The following are values that can be passed to the param parameter for
// functions: Timer_A_initContinuousMode(), Timer_A_initUpMode(),
// Timer_A_initUpDownMode(), and Timer_A_outputPWM().
//
//*****************************************************************************
#define TIMER_A_CLOCKSOURCE_EXTERNAL_TXCLK                        TASSEL__TACLK
#define TIMER_A_CLOCKSOURCE_ACLK                                   TASSEL__ACLK
#define TIMER_A_CLOCKSOURCE_SMCLK                                 TASSEL__SMCLK
#define TIMER_A_CLOCKSOURCE_INVERTED_EXTERNAL_TXCLK               TASSEL__INCLK

//*****************************************************************************
//
// The following are values that can be passed to the param parameter for
// functions: Timer_A_initContinuousMode(), Timer_A_initUpMode(), and
// Timer_A_initUpDownMode().
//
//*****************************************************************************
#define TIMER_A_TAIE_INTERRUPT_ENABLE                                      TAIE
#define TIMER_A_TAIE_INTERRUPT_DISABLE                                     0x00

//*****************************************************************************
//
// The following are values that can be passed to the param parameter for
// functions: Timer_A_initUpMode(), and Timer_A_initUpDownMode().
//
//*****************************************************************************
#define TIMER_A_CCIE_CCR0_INTERRUPT_ENABLE                                 CCIE
#define TIMER_A_CCIE_CCR0_INTERRUPT_DISABLE                                0x00

//*****************************************************************************
//
// The following are values that can be passed to the param parameter for
// functions: Timer_A_initCaptureMode(), and Timer_A_initCompareMode().
//
//*****************************************************************************
#define TIMER_A_CAPTURECOMPARE_INTERRUPT_DISABLE                           0x00
#define TIMER_A_CAPTURECOMPARE_INTERRUPT_ENABLE                            CCIE

//*****************************************************************************
//
// The following are values that can be passed to the param parameter for
// functions: Timer_A_initCaptureMode().
//
//*****************************************************************************
#define TIMER_A_CAPTURE_INPUTSELECT_CCIxA                                CCIS_0
#define TIMER_A_CAPTURE_INPUTSELECT_CCIxB                                CCIS_1
#define TIMER_A_CAPTURE_INPUTSELECT_GND                                  CCIS_2
#define TIMER_A_CAPTURE_INPUTSELECT_Vcc                                  CCIS_3

//*****************************************************************************
//
// The following are values that can be passed to the param parameter for
// functions: Timer_A_initCaptureMode(), Timer_A_initCompareMode(), and
// Timer_A_outputPWM().
//
//*****************************************************************************
#define TIMER_A_OUTPUTMODE_OUTBITVALUE                                 OUTMOD_0
#define TIMER_A_OUTPUTMODE_SET                                         OUTMOD_1
#define TIMER_A_OUTPUTMODE_TOGGLE_RESET                                OUTMOD_2
#define TIMER_A_OUTPUTMODE_SET_RESET                                   OUTMOD_3
#define TIMER_A_OUTPUTMODE_TOGGLE                                      OUTMOD_4
#define TIMER_A_OUTPUTMODE_RESET                                       OUTMOD_5
#define TIMER_A_OUTPUTMODE_TOGGLE_SET                                  OUTMOD_6
#define TIMER_A_OUTPUTMODE_RESET_SET                                   OUTMOD_7

//*****************************************************************************
//
// The following are values that can be passed to the compareRegister parameter
// for functions: Timer_A_setCompareValue(); the captureCompareRegister
// parameter for functions: Timer_A_enableCaptureCompareInterrupt(),
// Timer_A_disableCaptureCompareInterrupt(),
// Timer_A_getCaptureCompareInterruptStatus(),
// Timer_A_getSynchronizedCaptureCompareInput(),
// Timer_A_getOutputForOutputModeOutBitValue(),
// Timer_A_getCaptureCompareCount(),
// Timer_A_setOutputForOutputModeOutBitValue(), and
// Timer_A_clearCaptureCompareInterrupt(); the param parameter for functions:
// Timer_A_initCaptureMode(), Timer_A_initCompareMode(), and
// Timer_A_outputPWM().
//
//*****************************************************************************
#define TIMER_A_CAPTURECOMPARE_REGISTER_0                                  0x02
#define TIMER_A_CAPTURECOMPARE_REGISTER_1                                  0x04
#define TIMER_A_CAPTURECOMPARE_REGISTER_2                                  0x06
#define TIMER_A_CAPTURECOMPARE_REGISTER_3                                  0x08
#define TIMER_A_CAPTURECOMPARE_REGISTER_4                                  0x0A
#define TIMER_A_CAPTURECOMPARE_REGISTER_5                                  0x0C
#define TIMER_A_CAPTURECOMPARE_REGISTER_6                                  0x0E

//*****************************************************************************
//
// The following are values that can be passed to the param parameter for
// functions: Timer_A_initCaptureMode().
//
//*****************************************************************************
#define TIMER_A_CAPTUREMODE_NO_CAPTURE                                     CM_0
#define TIMER_A_CAPTUREMODE_RISING_EDGE                                    CM_1
#define TIMER_A_CAPTUREMODE_FALLING_EDGE                                   CM_2
#define TIMER_A_CAPTUREMODE_RISING_AND_FALLING_EDGE                        CM_3

//*****************************************************************************
//
// The following are values that can be passed to the param parameter for
// functions: Timer_A_initCaptureMode().
//
//*****************************************************************************
#define TIMER_A_CAPTURE_ASYNCHRONOUS                                       0x00
#define TIMER_A_CAPTURE_SYNCHRONOUS                                         SCS

//*****************************************************************************
//
// The following are values that can be passed to the mask parameter for
// functions: Timer_A_getCaptureCompareInterruptStatus() as well as returned by
// the Timer_A_getCaptureCompareInterruptStatus() function.
//
//*****************************************************************************
#define TIMER_A_CAPTURE_OVERFLOW                                            COV
#define TIMER_A_CAPTURECOMPARE_INTERRUPT_FLAG                             CCIFG

//*****************************************************************************
//
// The following are values that can be passed to the synchronized parameter
// for functions: Timer_A_getSynchronizedCaptureCompareInput().
//
//*****************************************************************************
#define TIMER_A_READ_SYNCHRONIZED_CAPTURECOMPAREINPUT                      SCCI
#define TIMER_A_READ_CAPTURE_COMPARE_INPUT                                  CCI

//*****************************************************************************
//
// The following are values that can be passed toThe following are values that
// can be returned by the Timer_A_getSynchronizedCaptureCompareInput()
// function.
//
//*****************************************************************************
#define TIMER_A_CAPTURECOMPARE_INPUT_HIGH                                  0x01
#define TIMER_A_CAPTURECOMPARE_INPUT_LOW                                   0x00

//*****************************************************************************
//
// The following are values that can be passed to the outputModeOutBitValue
// parameter for functions: Timer_A_setOutputForOutputModeOutBitValue() as well
// as returned by the Timer_A_getOutputForOutputModeOutBitValue() function.
//
//*****************************************************************************
#define TIMER_A_OUTPUTMODE_OUTBITVALUE_HIGH                                 OUT
#define TIMER_A_OUTPUTMODE_OUTBITVALUE_LOW                                 0x00

//*****************************************************************************
//
// The following are values that can be passed toThe following are values that
// can be returned by the Timer_A_getInterruptStatus() function.
//
//*****************************************************************************
#define TIMER_A_INTERRUPT_NOT_PENDING                                      0x00
#define TIMER_A_INTERRUPT_PENDING                                          0x01

//*****************************************************************************
//
// Prototypes for the APIs.
//
//*****************************************************************************

//*****************************************************************************
//
//! \brief Starts Timer_A counter
//!
//! This function assumes that the timer has been previously configured using
//! Timer_A_configureContinuousMode, Timer_A_configureUpMode or
//! Timer_A_configureUpDownMode.
//!
//! \param baseAddress is the base address of the TIMER_A module.
//! \param timerMode mode to put the timer in
//!        Valid values are:
//!        - \b TIMER_A_STOP_MODE
//!        - \b TIMER_A_UP_MODE
//!        - \b TIMER_A_CONTINUOUS_MODE [Default]
//!        - \b TIMER_A_UPDOWN_MODE
//!
//! Modified bits of \b TAxCTL register.
//!
//! \return None
//
//*****************************************************************************
extern void Timer_A_startCounter(uint16_t baseAddress,
                                 uint16_t timerMode);

//*****************************************************************************
//
//! \brief Configures Timer_A in continuous mode.
//!
//! \param baseAddress is the base address of the TIMER_A module.
//! \param param is the pointer to struct for continuous mode initialization.
//!
//! Modified bits of \b TAxCTL register.
//!
//! \return None
//
//*****************************************************************************
extern void Timer_A_initContinuousMode(uint16_t baseAddress,
                                       Timer_A_initContinuousModeParam *param);

//*****************************************************************************
//
//! \brief Configures Timer_A in up mode.
//!
//! \param baseAddress is the base address of the TIMER_A module.
//! \param param is the pointer to struct for up mode initialization.
//!
//! Modified bits of \b TAxCTL register, bits of \b TAxCCTL0 register and bits
//! of \b TAxCCR0 register.
//!
//! \return None
//
//*****************************************************************************
extern void Timer_A_initUpMode(uint16_t baseAddress,
                               Timer_A_initUpModeParam *param);

//*****************************************************************************
//
//! \brief Configures Timer_A in up down mode.
//!
//! \param baseAddress is the base address of the TIMER_A module.
//! \param param is the pointer to struct for up-down mode initialization.
//!
//! Modified bits of \b TAxCTL register, bits of \b TAxCCTL0 register and bits
//! of \b TAxCCR0 register.
//!
//! \return None
//
//*****************************************************************************
extern void Timer_A_initUpDownMode(uint16_t baseAddress,
                                   Timer_A_initUpDownModeParam *param);

//*****************************************************************************
//
//! \brief Initializes Capture Mode
//!
//! \param baseAddress is the base address of the TIMER_A module.
//! \param param is the pointer to struct for capture mode initialization.
//!
//! Modified bits of \b TAxCCTLn register.
//!
//! \return None
//
//*****************************************************************************
extern void Timer_A_initCaptureMode(uint16_t baseAddress,
                                    Timer_A_initCaptureModeParam *param);

//*****************************************************************************
//
//! \brief Initializes Compare Mode
//!
//! \param baseAddress is the base address of the TIMER_A module.
//! \param param is the pointer to struct for compare mode initialization.
//!
//! Modified bits of \b TAxCCRn register and bits of \b TAxCCTLn register.
//!
//! \return None
//
//*****************************************************************************
extern void Timer_A_initCompareMode(uint16_t baseAddress,
                                    Timer_A_initCompareModeParam *param);

//*****************************************************************************
//
//! \brief Enable timer interrupt
//!
//! Does not clear interrupt flags
//!
//! \param baseAddress is the base address of the TIMER_A module.
//!
//! Modified bits of \b TAxCTL register.
//!
//! \return None
//
//*****************************************************************************
extern void Timer_A_enableInterrupt(uint16_t baseAddress);

//*****************************************************************************
//
//! \brief Disable timer interrupt
//!
//! \param baseAddress is the base address of the TIMER_A module.
//!
//! Modified bits of \b TAxCTL register.
//!
//! \return None
//
//*****************************************************************************
extern void Timer_A_disableInterrupt(uint16_t baseAddress);

//*****************************************************************************
//
//! \brief Get timer interrupt status
//!
//! \param baseAddress is the base address of the TIMER_A module.
//!
//! \return One of the following:
//!         - \b Timer_A_INTERRUPT_NOT_PENDING
//!         - \b Timer_A_INTERRUPT_PENDING
//!         \n indicating the Timer_A interrupt status
//
//*****************************************************************************
extern uint32_t Timer_A_getInterruptStatus(uint16_t baseAddress);

//*****************************************************************************
//
//! \brief Enable capture compare interrupt
//!
//! Does not clear interrupt flags
//!
//! \param baseAddress is the base address of the TIMER_A module.
//! \param captureCompareRegister is the selected capture compare register
//!        Valid values are:
//!        - \b TIMER_A_CAPTURECOMPARE_REGISTER_0
//!        - \b TIMER_A_CAPTURECOMPARE_REGISTER_1
//!        - \b TIMER_A_CAPTURECOMPARE_REGISTER_2
//!        - \b TIMER_A_CAPTURECOMPARE_REGISTER_3
//!        - \b TIMER_A_CAPTURECOMPARE_REGISTER_4
//!        - \b TIMER_A_CAPTURECOMPARE_REGISTER_5
//!        - \b TIMER_A_CAPTURECOMPARE_REGISTER_6
//!
//! Modified bits of \b TAxCCTLn register.
//!
//! \return None
//
//*****************************************************************************
extern void Timer_A_enableCaptureCompareInterrupt(uint16_t baseAddress,
                                                  uint16_t captureCompareRegister);

//*****************************************************************************
//
//! \brief Disable capture compare interrupt
//!
//! \param baseAddress is the base address of the TIMER_A module.
//! \param captureCompareRegister is the selected capture compare register
//!        Valid values are:
//!        - \b TIMER_A_CAPTURECOMPARE_REGISTER_0
//!        - \b TIMER_A_CAPTURECOMPARE_REGISTER_1
//!        - \b TIMER_A_CAPTURECOMPARE_REGISTER_2
//!        - \b TIMER_A_CAPTURECOMPARE_REGISTER_3
//!        - \b TIMER_A_CAPTURECOMPARE_REGISTER_4
//!        - \b TIMER_A_CAPTURECOMPARE_REGISTER_5
//!        - \b TIMER_A_CAPTURECOMPARE_REGISTER_6
//!
//! Modified bits of \b TAxCCTLn register.
//!
//! \return None
//
//*****************************************************************************
extern void Timer_A_disableCaptureCompareInterrupt(uint16_t baseAddress,
                                                   uint16_t captureCompareRegister);

//*****************************************************************************
//
//! \brief Return capture compare interrupt status
//!
//! \param baseAddress is the base address of the TIMER_A module.
//! \param captureCompareRegister is the selected capture compare register
//!        Valid values are:
//!        - \b TIMER_A_CAPTURECOMPARE_REGISTER_0
//!        - \b TIMER_A_CAPTURECOMPARE_REGISTER_1
//!        - \b TIMER_A_CAPTURECOMPARE_REGISTER_2
//!        - \b TIMER_A_CAPTURECOMPARE_REGISTER_3
//!        - \b TIMER_A_CAPTURECOMPARE_REGISTER_4
//!        - \b TIMER_A_CAPTURECOMPARE_REGISTER_5
//!        - \b TIMER_A_CAPTURECOMPARE_REGISTER_6
//! \param mask is the mask for the interrupt status
//!        Mask value is the logical OR of any of the following:
//!        - \b TIMER_A_CAPTURE_OVERFLOW
//!        - \b TIMER_A_CAPTURECOMPARE_INTERRUPT_FLAG
//!
//! \return Logical OR of any of the following:
//!         - \b Timer_A_CAPTURE_OVERFLOW
//!         - \b Timer_A_CAPTURECOMPARE_INTERRUPT_FLAG
//!         \n indicating the status of the masked interrupts
//
//*****************************************************************************
extern uint32_t Timer_A_getCaptureCompareInterruptStatus(uint16_t baseAddress,
                                                         uint16_t captureCompareRegister,
                                                         uint16_t mask);

//*****************************************************************************
//
//! \brief Reset/Clear the timer clock divider, count direction, count
//!
//! \param baseAddress is the base address of the TIMER_A module.
//!
//! Modified bits of \b TAxCTL register.
//!
//! \return None
//
//*****************************************************************************
extern void Timer_A_clear(uint16_t baseAddress);

//*****************************************************************************
//
//! \brief Get synchronized capturecompare input
//!
//! \param baseAddress is the base address of the TIMER_A module.
//! \param captureCompareRegister
//!        Valid values are:
//!        - \b TIMER_A_CAPTURECOMPARE_REGISTER_0
//!        - \b TIMER_A_CAPTURECOMPARE_REGISTER_1
//!        - \b TIMER_A_CAPTURECOMPARE_REGISTER_2
//!        - \b TIMER_A_CAPTURECOMPARE_REGISTER_3
//!        - \b TIMER_A_CAPTURECOMPARE_REGISTER_4
//!        - \b TIMER_A_CAPTURECOMPARE_REGISTER_5
//!        - \b TIMER_A_CAPTURECOMPARE_REGISTER_6
//! \param synchronized
//!        Valid values are:
//!        - \b TIMER_A_READ_SYNCHRONIZED_CAPTURECOMPAREINPUT
//!        - \b TIMER_A_READ_CAPTURE_COMPARE_INPUT
//!
//! \return One of the following:
//!         - \b Timer_A_CAPTURECOMPARE_INPUT_HIGH
//!         - \b Timer_A_CAPTURECOMPARE_INPUT_LOW
//
//*****************************************************************************
extern uint8_t Timer_A_getSynchronizedCaptureCompareInput(uint16_t baseAddress,
                                                          uint16_t captureCompareRegister,
                                                          uint16_t synchronized);

//*****************************************************************************
//
//! \brief Get output bit for output mode
//!
//! \param baseAddress is the base address of the TIMER_A module.
//! \param captureCompareRegister
//!        Valid values are:
//!        - \b TIMER_A_CAPTURECOMPARE_REGISTER_0
//!        - \b TIMER_A_CAPTURECOMPARE_REGISTER_1
//!        - \b TIMER_A_CAPTURECOMPARE_REGISTER_2
//!        - \b TIMER_A_CAPTURECOMPARE_REGISTER_3
//!        - \b TIMER_A_CAPTURECOMPARE_REGISTER_4
//!        - \b TIMER_A_CAPTURECOMPARE_REGISTER_5
//!        - \b TIMER_A_CAPTURECOMPARE_REGISTER_6
//!
//! \return One of the following:
//!         - \b Timer_A_OUTPUTMODE_OUTBITVALUE_HIGH
//!         - \b Timer_A_OUTPUTMODE_OUTBITVALUE_LOW
//
//*****************************************************************************
extern uint8_t Timer_A_getOutputForOutputModeOutBitValue(uint16_t baseAddress,
                                                         uint16_t captureCompareRegister);

//*****************************************************************************
//
//! \brief Get current capturecompare count
//!
//! \param baseAddress is the base address of the TIMER_A module.
//! \param captureCompareRegister
//!        Valid values are:
//!        - \b TIMER_A_CAPTURECOMPARE_REGISTER_0
//!        - \b TIMER_A_CAPTURECOMPARE_REGISTER_1
//!        - \b TIMER_A_CAPTURECOMPARE_REGISTER_2
//!        - \b TIMER_A_CAPTURECOMPARE_REGISTER_3
//!        - \b TIMER_A_CAPTURECOMPARE_REGISTER_4
//!        - \b TIMER_A_CAPTURECOMPARE_REGISTER_5
//!        - \b TIMER_A_CAPTURECOMPARE_REGISTER_6
//!
//! \return Current count as an uint16_t
//
//*****************************************************************************
extern uint16_t Timer_A_getCaptureCompareCount(uint16_t baseAddress,
                                               uint16_t captureCompareRegister);

//*****************************************************************************
//
//! \brief Set output bit for output mode
//!
//! \param baseAddress is the base address of the TIMER_A module.
//! \param captureCompareRegister
//!        Valid values are:
//!        - \b TIMER_A_CAPTURECOMPARE_REGISTER_0
//!        - \b TIMER_A_CAPTURECOMPARE_REGISTER_1
//!        - \b TIMER_A_CAPTURECOMPARE_REGISTER_2
//!        - \b TIMER_A_CAPTURECOMPARE_REGISTER_3
//!        - \b TIMER_A_CAPTURECOMPARE_REGISTER_4
//!        - \b TIMER_A_CAPTURECOMPARE_REGISTER_5
//!        - \b TIMER_A_CAPTURECOMPARE_REGISTER_6
//! \param outputModeOutBitValue is the value to be set for out bit
//!        Valid values are:
//!        - \b TIMER_A_OUTPUTMODE_OUTBITVALUE_HIGH
//!        - \b TIMER_A_OUTPUTMODE_OUTBITVALUE_LOW
//!
//! Modified bits of \b TAxCCTLn register.
//!
//! \return None
//
//*****************************************************************************
extern void Timer_A_setOutputForOutputModeOutBitValue(uint16_t baseAddress,
                                                      uint16_t captureCompareRegister,
                                                      uint8_t outputModeOutBitValue);

//*****************************************************************************
//
//! \brief Generate a PWM with timer running in up mode
//!
//! \param baseAddress is the base address of the TIMER_A module.
//! \param param is the pointer to struct for PWM configuration.
//!
//! Modified bits of \b TAxCTL register, bits of \b TAxCCTL0 register, bits of
//! \b TAxCCR0 register and bits of \b TAxCCTLn register.
//!
//! \return None
//
//*****************************************************************************
extern void Timer_A_outputPWM(uint16_t baseAddress,
                              Timer_A_outputPWMParam *param);

//*****************************************************************************
//
//! \brief Stops the timer
//!
//! \param baseAddress is the base address of the TIMER_A module.
//!
//! Modified bits of \b TAxCTL register.
//!
//! \return None
//
//*****************************************************************************
extern void Timer_A_stop(uint16_t baseAddress);

//*****************************************************************************
//
//! \brief Sets the value of the capture-compare register
//!
//! \param baseAddress is the base address of the TIMER_A module.
//! \param compareRegister selects the Capture register being used. Refer to
//!        datasheet to ensure the device has the capture compare register
//!        being used.
//!        Valid values are:
//!        - \b TIMER_A_CAPTURECOMPARE_REGISTER_0
//!        - \b TIMER_A_CAPTURECOMPARE_REGISTER_1
//!        - \b TIMER_A_CAPTURECOMPARE_REGISTER_2
//!        - \b TIMER_A_CAPTURECOMPARE_REGISTER_3
//!        - \b TIMER_A_CAPTURECOMPARE_REGISTER_4
//!        - \b TIMER_A_CAPTURECOMPARE_REGISTER_5
//!        - \b TIMER_A_CAPTURECOMPARE_REGISTER_6
//! \param compareValue is the count to be compared with in compare mode
//!
//! Modified bits of \b TAxCCRn register.
//!
//! \return None
//
//*****************************************************************************
extern void Timer_A_setCompareValue(uint16_t baseAddress,
                                    uint16_t compareRegister,
                                    uint16_t compareValue);

//*****************************************************************************
//
//! \brief Clears the Timer TAIFG interrupt flag
//!
//! \param baseAddress is the base address of the TIMER_A module.
//!
//! Modified bits are \b TAIFG of \b TAxCTL register.
//!
//! \return None
//
//*****************************************************************************
extern void Timer_A_clearTimerInterrupt(uint16_t baseAddress);

//*****************************************************************************
//
//! \brief Clears the capture-compare interrupt flag
//!
//! \param baseAddress is the base address of the TIMER_A module.
//! \param captureCompareRegister selects the Capture-compare register being
//!        used.
//!        Valid values are:
//!        - \b TIMER_A_CAPTURECOMPARE_REGISTER_0
//!        - \b TIMER_A_CAPTURECOMPARE_REGISTER_1
//!        - \b TIMER_A_CAPTURECOMPARE_REGISTER_2
//!        - \b TIMER_A_CAPTURECOMPARE_REGISTER_3
//!        - \b TIMER_A_CAPTURECOMPARE_REGISTER_4
//!        - \b TIMER_A_CAPTURECOMPARE_REGISTER_5
//!        - \b TIMER_A_CAPTURECOMPARE_REGISTER_6
//!
//! Modified bits are \b CCIFG of \b TAxCCTLn register.
//!
//! \return None
//
//*****************************************************************************
extern void Timer_A_clearCaptureCompareInterrupt(uint16_t baseAddress,
                                                 uint16_t captureCompareRegister);

//*****************************************************************************
//
//! \brief Reads the current timer count value
//!
//! Reads the current count value of the timer. There is a majority vote system
//! in place to confirm an accurate value is returned. The TIMER_A_THRESHOLD
//! #define in the corresponding header file can be modified so that the votes
//! must be closer together for a consensus to occur.
//!
//! \param baseAddress is the base address of the TIMER_A module.
//!
//! \return Majority vote of timer count value
//
//*****************************************************************************
extern uint16_t Timer_A_getCounterValue(uint16_t baseAddress);

//*****************************************************************************
//
// Mark the end of the C bindings section for C++ compilers.
//
//*****************************************************************************
#ifdef __cplusplus
}
#endif

#endif
#endif // __MSP430WARE_TIMER_A_H__
