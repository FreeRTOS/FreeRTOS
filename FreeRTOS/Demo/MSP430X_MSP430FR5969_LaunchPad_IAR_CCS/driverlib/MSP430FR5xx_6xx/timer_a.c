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
// timer_a.c - Driver for the timer_a Module.
//
//*****************************************************************************

//*****************************************************************************
//
//! \addtogroup timer_a_api timer_a
//! @{
//
//*****************************************************************************

#include "inc/hw_regaccess.h"
#include "inc/hw_memmap.h"

#ifdef __MSP430_HAS_TxA7__
#include "timer_a.h"

#include <assert.h>

void Timer_A_startCounter(uint16_t baseAddress,
                          uint16_t timerMode)
{
    HWREG16(baseAddress + OFS_TAxCTL) |= timerMode;
}

void Timer_A_initContinuousMode(uint16_t baseAddress,
                                Timer_A_initContinuousModeParam *param)
{
    HWREG16(baseAddress +
            OFS_TAxCTL) &= ~(TIMER_A_CLOCKSOURCE_INVERTED_EXTERNAL_TXCLK +
                             TIMER_A_UPDOWN_MODE +
                             TIMER_A_DO_CLEAR +
                             TIMER_A_TAIE_INTERRUPT_ENABLE +
                             ID__8
                             );
    HWREG16(baseAddress + OFS_TAxEX0) &= ~TAIDEX_7;

    HWREG16(baseAddress + OFS_TAxEX0) |= param->clockSourceDivider & 0x7;
    HWREG16(baseAddress + OFS_TAxCTL) |= (param->clockSource +
                                          param->timerClear +
                                          param->timerInterruptEnable_TAIE +
                                          ((param->clockSourceDivider >>
                                            3) << 6));

    if(param->startTimer)
    {
        HWREG16(baseAddress + OFS_TAxCTL) |= TIMER_A_CONTINUOUS_MODE;
    }
}

void Timer_A_initUpMode(uint16_t baseAddress,
                        Timer_A_initUpModeParam *param)
{
    HWREG16(baseAddress + OFS_TAxCTL) &=
        ~(TIMER_A_CLOCKSOURCE_INVERTED_EXTERNAL_TXCLK +
          TIMER_A_UPDOWN_MODE +
          TIMER_A_DO_CLEAR +
          TIMER_A_TAIE_INTERRUPT_ENABLE +
          ID__8
          );
    HWREG16(baseAddress + OFS_TAxEX0) &= ~TAIDEX_7;

    HWREG16(baseAddress + OFS_TAxEX0) |= param->clockSourceDivider & 0x7;
    HWREG16(baseAddress + OFS_TAxCTL) |= (param->clockSource +
                                          param->timerClear +
                                          param->timerInterruptEnable_TAIE +
                                          ((param->clockSourceDivider >>
                                            3) << 6));

    if(param->startTimer)
    {
        HWREG16(baseAddress + OFS_TAxCTL) |= TIMER_A_UP_MODE;
    }

    if(TIMER_A_CCIE_CCR0_INTERRUPT_ENABLE ==
       param->captureCompareInterruptEnable_CCR0_CCIE)
    {
        HWREG16(baseAddress +
                OFS_TAxCCTL0) |= TIMER_A_CCIE_CCR0_INTERRUPT_ENABLE;
    }
    else
    {
        HWREG16(baseAddress +
                OFS_TAxCCTL0) &= ~TIMER_A_CCIE_CCR0_INTERRUPT_ENABLE;
    }

    HWREG16(baseAddress + OFS_TAxCCR0) = param->timerPeriod;
}

void Timer_A_initUpDownMode(uint16_t baseAddress,
                            Timer_A_initUpDownModeParam *param)
{
    HWREG16(baseAddress + OFS_TAxCTL) &=
        ~(TIMER_A_CLOCKSOURCE_INVERTED_EXTERNAL_TXCLK +
          TIMER_A_UPDOWN_MODE +
          TIMER_A_DO_CLEAR +
          TIMER_A_TAIE_INTERRUPT_ENABLE +
          ID__8
          );
    HWREG16(baseAddress + OFS_TAxEX0) &= ~TAIDEX_7;

    HWREG16(baseAddress + OFS_TAxEX0) |= param->clockSourceDivider & 0x7;
    HWREG16(baseAddress + OFS_TAxCTL) |= (param->clockSource +
                                          param->timerClear +
                                          param->timerInterruptEnable_TAIE +
                                          ((param->clockSourceDivider >>
                                            3) << 6));

    if(param->startTimer)
    {
        HWREG16(baseAddress + OFS_TAxCTL) |= TIMER_A_UPDOWN_MODE;
    }

    if(TIMER_A_CCIE_CCR0_INTERRUPT_ENABLE ==
       param->captureCompareInterruptEnable_CCR0_CCIE)
    {
        HWREG16(baseAddress +
                OFS_TAxCCTL0) |= TIMER_A_CCIE_CCR0_INTERRUPT_ENABLE;
    }
    else
    {
        HWREG16(baseAddress +
                OFS_TAxCCTL0) &= ~TIMER_A_CCIE_CCR0_INTERRUPT_ENABLE;
    }

    HWREG16(baseAddress + OFS_TAxCCR0) = param->timerPeriod;
}

void Timer_A_initCaptureMode(uint16_t baseAddress,
                             Timer_A_initCaptureModeParam *param)
{
    HWREG16(baseAddress + param->captureRegister) |= CAP;

    HWREG16(baseAddress + param->captureRegister) &=
        ~(TIMER_A_CAPTUREMODE_RISING_AND_FALLING_EDGE +
          TIMER_A_CAPTURE_INPUTSELECT_Vcc +
          TIMER_A_CAPTURE_SYNCHRONOUS +
          TIMER_A_DO_CLEAR +
          TIMER_A_TAIE_INTERRUPT_ENABLE +
          CM_3
          );

    HWREG16(baseAddress + param->captureRegister) |= (param->captureMode +
                                                      param->captureInputSelect
                                                      +
                                                      param->
                                                      synchronizeCaptureSource +
                                                      param->
                                                      captureInterruptEnable +
                                                      param->captureOutputMode
                                                      );
}

void Timer_A_initCompareMode(uint16_t baseAddress,
                             Timer_A_initCompareModeParam *param)
{
    HWREG16(baseAddress + param->compareRegister) &= ~CAP;

    HWREG16(baseAddress + param->compareRegister) &=
        ~(TIMER_A_CAPTURECOMPARE_INTERRUPT_ENABLE +
          TIMER_A_OUTPUTMODE_RESET_SET
          );

    HWREG16(baseAddress +
            param->compareRegister) |= (param->compareInterruptEnable +
                                        param->compareOutputMode
                                        );

    HWREG16(baseAddress + param->compareRegister +
            OFS_TAxR) = param->compareValue;
}

void Timer_A_enableInterrupt(uint16_t baseAddress)
{
    HWREG16(baseAddress + OFS_TAxCTL) |= TAIE;
}

void Timer_A_disableInterrupt(uint16_t baseAddress)
{
    HWREG16(baseAddress + OFS_TAxCTL) &= ~TAIE;
}

uint32_t Timer_A_getInterruptStatus(uint16_t baseAddress)
{
    return (HWREG16(baseAddress + OFS_TAxCTL) & TAIFG);
}

void Timer_A_enableCaptureCompareInterrupt(uint16_t baseAddress,
                                           uint16_t captureCompareRegister)
{
    HWREG16(baseAddress + captureCompareRegister) |= CCIE;
}

void Timer_A_disableCaptureCompareInterrupt(uint16_t baseAddress,
                                            uint16_t captureCompareRegister)
{
    HWREG16(baseAddress + captureCompareRegister) &= ~CCIE;
}

uint32_t Timer_A_getCaptureCompareInterruptStatus(uint16_t baseAddress,
                                                  uint16_t captureCompareRegister,
                                                  uint16_t mask)
{
    return (HWREG16(baseAddress + captureCompareRegister) & mask);
}

void Timer_A_clear(uint16_t baseAddress)
{
    HWREG16(baseAddress + OFS_TAxCTL) |= TACLR;
}

uint8_t Timer_A_getSynchronizedCaptureCompareInput(uint16_t baseAddress,
                                                   uint16_t captureCompareRegister,
                                                   uint16_t synchronized)
{
    if(HWREG16(baseAddress + captureCompareRegister) & synchronized)
    {
        return (TIMER_A_CAPTURECOMPARE_INPUT_HIGH);
    }
    else
    {
        return (TIMER_A_CAPTURECOMPARE_INPUT_LOW);
    }
}

uint8_t Timer_A_getOutputForOutputModeOutBitValue(uint16_t baseAddress,
                                                  uint16_t captureCompareRegister)
{
    if(HWREG16(baseAddress + captureCompareRegister) & OUT)
    {
        return (TIMER_A_OUTPUTMODE_OUTBITVALUE_HIGH);
    }
    else
    {
        return (TIMER_A_OUTPUTMODE_OUTBITVALUE_LOW);
    }
}

uint16_t Timer_A_getCaptureCompareCount(uint16_t baseAddress,
                                        uint16_t captureCompareRegister)
{
    return  (HWREG16(baseAddress + OFS_TAxR + captureCompareRegister));
}

void Timer_A_setOutputForOutputModeOutBitValue(uint16_t baseAddress,
                                               uint16_t captureCompareRegister,
                                               uint8_t outputModeOutBitValue)
{
    HWREG16(baseAddress + captureCompareRegister) &= ~OUT;
    HWREG16(baseAddress + captureCompareRegister) |= outputModeOutBitValue;
}

void Timer_A_outputPWM(uint16_t baseAddress,
                       Timer_A_outputPWMParam *param)
{
    HWREG16(baseAddress + OFS_TAxCTL) &=
        ~(TIMER_A_CLOCKSOURCE_INVERTED_EXTERNAL_TXCLK +
          TIMER_A_UPDOWN_MODE + TIMER_A_DO_CLEAR +
          TIMER_A_TAIE_INTERRUPT_ENABLE +
          ID__8
          );
    HWREG16(baseAddress + OFS_TAxEX0) &= ~TAIDEX_7;

    HWREG16(baseAddress + OFS_TAxEX0) |= param->clockSourceDivider & 0x7;
    HWREG16(baseAddress + OFS_TAxCTL) |= (param->clockSource +
                                          TIMER_A_UP_MODE +
                                          TIMER_A_DO_CLEAR +
                                          ((param->clockSourceDivider >>
                                            3) << 6));

    HWREG16(baseAddress + OFS_TAxCCR0) = param->timerPeriod;

    HWREG16(baseAddress + OFS_TAxCCTL0) &=
        ~(TIMER_A_CAPTURECOMPARE_INTERRUPT_ENABLE +
          TIMER_A_OUTPUTMODE_RESET_SET);

    HWREG16(baseAddress + param->compareRegister) |= param->compareOutputMode;

    HWREG16(baseAddress + param->compareRegister + OFS_TAxR) = param->dutyCycle;
}

void Timer_A_stop(uint16_t baseAddress)
{
    HWREG16(baseAddress + OFS_TAxCTL) &= ~MC_3;
}

void Timer_A_setCompareValue(uint16_t baseAddress,
                             uint16_t compareRegister,
                             uint16_t compareValue)
{
    HWREG16(baseAddress + compareRegister + OFS_TAxR) = compareValue;
}

void Timer_A_clearTimerInterrupt(uint16_t baseAddress)
{
    HWREG16(baseAddress + OFS_TAxCTL) &= ~TAIFG;
}

void Timer_A_clearCaptureCompareInterrupt(uint16_t baseAddress,
                                          uint16_t captureCompareRegister)
{
    HWREG16(baseAddress + captureCompareRegister) &= ~CCIFG;
}

uint16_t Timer_A_getCounterValue(uint16_t baseAddress)
{
    uint16_t voteOne, voteTwo, res;

    voteTwo = HWREG16(baseAddress + OFS_TAxR);

    do
    {
        voteOne = voteTwo;
        voteTwo = HWREG16(baseAddress + OFS_TAxR);

        if(voteTwo > voteOne)
        {
            res = voteTwo - voteOne;
        }
        else if(voteOne > voteTwo)
        {
            res = voteOne - voteTwo;
        }
        else
        {
            res = 0;
        }
    }
    while(res > TIMER_A_THRESHOLD);

    return(voteTwo);
}

#endif
//*****************************************************************************
//
//! Close the doxygen group for timer_a_api
//! @}
//
//*****************************************************************************
