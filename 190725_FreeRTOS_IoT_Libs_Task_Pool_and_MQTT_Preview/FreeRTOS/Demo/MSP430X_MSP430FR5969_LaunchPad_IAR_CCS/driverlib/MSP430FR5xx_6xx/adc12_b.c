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
// adc12_b.c - Driver for the adc12_b Module.
//
//*****************************************************************************

//*****************************************************************************
//
//! \addtogroup adc12_b_api adc12_b
//! @{
//
//*****************************************************************************

#include "inc/hw_regaccess.h"
#include "inc/hw_memmap.h"

#ifdef __MSP430_HAS_ADC12_B__
#include "adc12_b.h"

#include <assert.h>

bool ADC12_B_init(uint16_t baseAddress,
                  ADC12_B_initParam *param)
{
    //Make sure the ENC bit is cleared before initializing the ADC12
    HWREG8(baseAddress + OFS_ADC12CTL0_L) &= ~ADC12ENC;

    bool retVal = STATUS_SUCCESS;

    //Turn OFF ADC12B Module & Clear Interrupt Registers
    HWREG16(baseAddress + OFS_ADC12CTL0) &= ~(ADC12ON + ADC12ENC + ADC12SC);
    HWREG16(baseAddress + OFS_ADC12IER0) &= 0x0000;  //Reset ALL interrupt enables
    HWREG16(baseAddress + OFS_ADC12IER1) &= 0x0000;
    HWREG16(baseAddress + OFS_ADC12IER2) &= 0x0000;
    HWREG16(baseAddress + OFS_ADC12IFGR0) &= 0x0000;  //Reset ALL interrupt flags
    HWREG16(baseAddress + OFS_ADC12IFGR1) &= 0x0000;
    HWREG16(baseAddress + OFS_ADC12IFGR2) &= 0x0000;

    //Set ADC12B Control 1
    HWREG16(baseAddress + OFS_ADC12CTL1) =
        param->sampleHoldSignalSourceSelect //Setup the Sample-and-Hold Source
        + (param->clockSourceDivider & ADC12DIV_7) //Set Clock Divider
        + (param->clockSourcePredivider & ADC12PDIV__64)
        + param->clockSourceSelect; //Setup Clock Source

    //Set ADC12B Control 2
    HWREG16(baseAddress + OFS_ADC12CTL2) =
        ADC12RES_2; //Default resolution to 12-bits

    //Set ADC12B Control 3
    HWREG16(baseAddress + OFS_ADC12CTL3) =
        param->internalChannelMap; // Map internal channels

    return (retVal);
}

void ADC12_B_enable(uint16_t baseAddress)
{
    // Clear ENC bit
    HWREG8(baseAddress + OFS_ADC12CTL0_L) &= ~ADC12ENC;

    //Enable the ADC12B Module
    HWREG8(baseAddress + OFS_ADC12CTL0_L) |= ADC12ON;
}

void ADC12_B_disable(uint16_t baseAddress)
{
    // Clear ENC bit
    HWREG8(baseAddress + OFS_ADC12CTL0_L) &= ~ADC12ENC;

    //Disable ADC12B module
    HWREG8(baseAddress + OFS_ADC12CTL0_L) &= ~ADC12ON;
}

void ADC12_B_setupSamplingTimer(uint16_t baseAddress,
                                uint16_t clockCycleHoldCountLowMem,
                                uint16_t clockCycleHoldCountHighMem,
                                uint16_t multipleSamplesEnabled)
{
    HWREG16(baseAddress + OFS_ADC12CTL1) |= ADC12SHP;

    //Reset clock cycle hold counts and msc bit before setting them
    HWREG16(baseAddress + OFS_ADC12CTL0) &=
        ~(ADC12SHT0_15 + ADC12SHT1_15 + ADC12MSC);

    //Set clock cycle hold counts and msc bit
    HWREG16(baseAddress + OFS_ADC12CTL0) |= clockCycleHoldCountLowMem
                                            + (clockCycleHoldCountHighMem << 4)
                                            + multipleSamplesEnabled;
}

void ADC12_B_disableSamplingTimer(uint16_t baseAddress)
{
    HWREG16(baseAddress + OFS_ADC12CTL1) &= ~(ADC12SHP);
}

void ADC12_B_configureMemory(uint16_t baseAddress,
                             ADC12_B_configureMemoryParam *param)
{
    //Set the offset in respect to ADC12MCTL0
    uint16_t memoryBufferControlOffset =
        (OFS_ADC12MCTL0 + param->memoryBufferControlIndex);

    //Reset the memory buffer control and Set the input source
    HWREG16(baseAddress + memoryBufferControlOffset) =
        param->inputSourceSelect //Set Input Source
        + param->refVoltageSourceSelect //Set Vref+/-
        + param->endOfSequence; //Set End of Sequence

    HWREG16(baseAddress + memoryBufferControlOffset)
        &= ~(ADC12WINC);

    HWREG16(baseAddress + memoryBufferControlOffset)
        |= param->windowComparatorSelect;
    //(OFS_ADC12MCTL0_H + memoryIndex) == offset of OFS_ADC12MCTLX_H

    HWREG16(baseAddress + memoryBufferControlOffset)
        &= ~(ADC12DIF);

    HWREG16(baseAddress + memoryBufferControlOffset)
        |= param->differentialModeSelect;
    //(OFS_ADC12MCTL0_H + memoryIndex) == offset of OFS_ADC12MCTLX_H
}

void ADC12_B_setWindowCompAdvanced(uint16_t baseAddress,
                                   uint16_t highThreshold,
                                   uint16_t lowThreshold)
{
    HWREG16(baseAddress + OFS_ADC12HI) = highThreshold;
    HWREG16(baseAddress + OFS_ADC12LO) = lowThreshold;
}

void ADC12_B_enableInterrupt(uint16_t baseAddress,
                             uint16_t interruptMask0,
                             uint16_t interruptMask1,
                             uint16_t interruptMask2)
{
    HWREG16(baseAddress + OFS_ADC12IER0) |= interruptMask0;
    HWREG16(baseAddress + OFS_ADC12IER1) |= interruptMask1;
    HWREG16(baseAddress + OFS_ADC12IER2) |= interruptMask2;
}

void ADC12_B_disableInterrupt(uint16_t baseAddress,
                              uint16_t interruptMask0,
                              uint16_t interruptMask1,
                              uint16_t interruptMask2)
{
    HWREG16(baseAddress + OFS_ADC12IER0) &= ~(interruptMask0);
    HWREG16(baseAddress + OFS_ADC12IER1) &= ~(interruptMask1);
    HWREG16(baseAddress + OFS_ADC12IER2) &= ~(interruptMask2);
}

void ADC12_B_clearInterrupt(uint16_t baseAddress,
                            uint8_t interruptRegisterChoice,
                            uint16_t memoryInterruptFlagMask)
{
    HWREG16(baseAddress + OFS_ADC12IFGR0 + 2 * interruptRegisterChoice) &=
        ~(memoryInterruptFlagMask);
}

uint16_t ADC12_B_getInterruptStatus(uint16_t baseAddress,
                                    uint8_t interruptRegisterChoice,
                                    uint16_t memoryInterruptFlagMask)
{
    return (HWREG16(baseAddress + OFS_ADC12IFGR0 + 2 * interruptRegisterChoice)
            & memoryInterruptFlagMask);
}

void ADC12_B_startConversion(uint16_t baseAddress,
                             uint16_t startingMemoryBufferIndex,
                             uint8_t conversionSequenceModeSelect)
{
    //Reset the ENC bit to set the starting memory address and conversion mode
    //sequence
    HWREG8(baseAddress + OFS_ADC12CTL0_L) &= ~(ADC12ENC);
    //Reset the bits about to be set
    HWREG16(baseAddress + OFS_ADC12CTL3) &= ~(ADC12CSTARTADD_31);
    HWREG16(baseAddress + OFS_ADC12CTL1) &= ~(ADC12CONSEQ_3);

    HWREG16(baseAddress + OFS_ADC12CTL3) |= startingMemoryBufferIndex;
    HWREG16(baseAddress + OFS_ADC12CTL1) |= conversionSequenceModeSelect;
    HWREG8(baseAddress + OFS_ADC12CTL0_L) |= ADC12ENC + ADC12SC;
}

void ADC12_B_disableConversions(uint16_t baseAddress,
                                bool preempt)
{
    if(ADC12_B_PREEMPTCONVERSION == preempt)
    {
        HWREG8(baseAddress + OFS_ADC12CTL1_L) &= ~(ADC12CONSEQ_3);
        //Reset conversion sequence mode to single-channel, single-conversion
    }
    else if(~(HWREG8(baseAddress + OFS_ADC12CTL1_L) & ADC12CONSEQ_3))
    {
        //To prevent preemption of a single-channel, single-conversion we must
        //wait for the ADC core to finish the conversion.
        while(ADC12_B_isBusy(baseAddress))
        {
            ;
        }
    }

    HWREG8(baseAddress + OFS_ADC12CTL0_L) &= ~(ADC12ENC);
}

uint16_t ADC12_B_getResults(uint16_t baseAddress,
                            uint8_t memoryBufferIndex)
{
    return (HWREG16(baseAddress + (OFS_ADC12MEM0 + memoryBufferIndex)));
    //(0x60 + memoryBufferIndex) == offset of ADC12MEMx
}

void ADC12_B_setResolution(uint16_t baseAddress,
                           uint8_t resolutionSelect)
{
    HWREG8(baseAddress + OFS_ADC12CTL2_L) &= ~(ADC12RES_3);
    HWREG8(baseAddress + OFS_ADC12CTL2_L) |= resolutionSelect;
}

void ADC12_B_setSampleHoldSignalInversion(uint16_t baseAddress,
                                          uint16_t invertedSignal)
{
    HWREG16(baseAddress + OFS_ADC12CTL1) &= ~(ADC12ISSH);
    HWREG16(baseAddress + OFS_ADC12CTL1) |= invertedSignal;
}

void ADC12_B_setDataReadBackFormat(uint16_t baseAddress,
                                   uint8_t readBackFormat)
{
    HWREG8(baseAddress + OFS_ADC12CTL2_L) &= ~(ADC12DF);
    HWREG8(baseAddress + OFS_ADC12CTL2_L) |= readBackFormat;
}

void ADC12_B_setAdcPowerMode(uint16_t baseAddress,
                             uint8_t powerMode)
{
    HWREG8(baseAddress + OFS_ADC12CTL2_L) &= ~(ADC12PWRMD);
    HWREG8(baseAddress + OFS_ADC12CTL2_L) |= powerMode;
}

uint32_t ADC12_B_getMemoryAddressForDMA(uint16_t baseAddress,
                                        uint8_t memoryIndex)
{
    return (baseAddress + (OFS_ADC12MEM0 + memoryIndex));
    //(0x60 + memoryIndex) == offset of ADC12MEMx
}

uint8_t ADC12_B_isBusy(uint16_t baseAddress)
{
    return (HWREG8(baseAddress + OFS_ADC12CTL1_L) & ADC12BUSY);
}

#endif
//*****************************************************************************
//
//! Close the doxygen group for adc12_b_api
//! @}
//
//*****************************************************************************
