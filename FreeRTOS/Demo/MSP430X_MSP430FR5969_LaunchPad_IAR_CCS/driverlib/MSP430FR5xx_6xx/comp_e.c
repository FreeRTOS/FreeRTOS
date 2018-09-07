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
// comp_e.c - Driver for the comp_e Module.
//
//*****************************************************************************

//*****************************************************************************
//
//! \addtogroup comp_e_api comp_e
//! @{
//
//*****************************************************************************

#include "inc/hw_regaccess.h"
#include "inc/hw_memmap.h"

#ifdef __MSP430_HAS_COMP_E__
#include "comp_e.h"

#include <assert.h>

static uint16_t __getRegisterSettingForInput(uint32_t input)
{
    switch(input)
    {
    case COMP_E_INPUT0:
        return(CEIPSEL_0);
    case COMP_E_INPUT1:
        return(CEIPSEL_1);
    case COMP_E_INPUT2:
        return(CEIPSEL_2);
    case COMP_E_INPUT3:
        return(CEIPSEL_3);
    case COMP_E_INPUT4:
        return(CEIPSEL_4);
    case COMP_E_INPUT5:
        return(CEIPSEL_5);
    case COMP_E_INPUT6:
        return(CEIPSEL_6);
    case COMP_E_INPUT7:
        return(CEIPSEL_7);
    case COMP_E_INPUT8:
        return(CEIPSEL_8);
    case COMP_E_INPUT9:
        return(CEIPSEL_9);
    case COMP_E_INPUT10:
        return(CEIPSEL_10);
    case COMP_E_INPUT11:
        return(CEIPSEL_11);
    case COMP_E_INPUT12:
        return(CEIPSEL_12);
    case COMP_E_INPUT13:
        return(CEIPSEL_13);
    case COMP_E_INPUT14:
        return(CEIPSEL_14);
    case COMP_E_INPUT15:
        return(CEIPSEL_15);
    case COMP_E_VREF:
        return(COMP_E_VREF);
    default:
        return(0x11);
    }
}

bool Comp_E_init(uint16_t baseAddress,
                 Comp_E_initParam *param)
{
    uint8_t positiveTerminalInput = __getRegisterSettingForInput(
        param->posTerminalInput);
    uint8_t negativeTerminalInput = __getRegisterSettingForInput(
        param->negTerminalInput);
    bool retVal = STATUS_SUCCESS;

    //Reset COMPE Control 1 & Interrupt Registers for initialization (OFS_CECTL3
    //is not reset because it controls the input buffers of the analog signals
    //and may cause parasitic effects if an analog signal is still attached and
    //the buffer is re-enabled
    HWREG16(baseAddress + OFS_CECTL0) &= 0x0000;
    HWREG16(baseAddress + OFS_CEINT) &= 0x0000;

    //Set the Positive Terminal
    if(COMP_E_VREF != positiveTerminalInput)
    {
        //Enable Positive Terminal Input Mux and Set it to the appropriate input
        HWREG16(baseAddress + OFS_CECTL0) |= CEIPEN + positiveTerminalInput;

        //Disable the input buffer
        HWREG16(baseAddress + OFS_CECTL3) |= (1 << positiveTerminalInput);
    }
    else
    {
        //Reset and Set COMPE Control 2 Register
        HWREG16(baseAddress + OFS_CECTL2) &= ~(CERSEL); //Set Vref to go to (+)terminal
    }

    //Set the Negative Terminal
    if(COMP_E_VREF != negativeTerminalInput)
    {
        //Enable Negative Terminal Input Mux and Set it to the appropriate input
        HWREG16(baseAddress +
                OFS_CECTL0) |= CEIMEN + (negativeTerminalInput << 8);

        //Disable the input buffer
        HWREG16(baseAddress + OFS_CECTL3) |= (1 << negativeTerminalInput);
    }
    else
    {
        //Reset and Set COMPE Control 2 Register
        HWREG16(baseAddress + OFS_CECTL2) |= CERSEL; //Set Vref to go to (-) terminal
    }

    //Reset and Set COMPE Control 1 Register
    HWREG16(baseAddress + OFS_CECTL1) =
        +param->outputFilterEnableAndDelayLevel  //Set the filter enable bit and delay
        + param->invertedOutputPolarity; //Set the polarity of the output

    return (retVal);
}

void Comp_E_setReferenceVoltage(uint16_t baseAddress,
                                uint16_t supplyVoltageReferenceBase,
                                uint16_t lowerLimitSupplyVoltageFractionOf32,
                                uint16_t upperLimitSupplyVoltageFractionOf32)
{
    HWREG16(baseAddress + OFS_CECTL1) &= ~(CEMRVS); //Set to VREF0

    //Reset COMPE Control 2 Bits (Except for CERSEL which is set in Comp_Init() )
    HWREG16(baseAddress + OFS_CECTL2) &= CERSEL;

    //Set Voltage Source (Vcc | Vref, resistor ladder or not)
    if(COMP_E_REFERENCE_AMPLIFIER_DISABLED == supplyVoltageReferenceBase)
    {
        HWREG16(baseAddress + OFS_CECTL2) |= CERS_1; //Vcc with resistor ladder
    }
    else if(lowerLimitSupplyVoltageFractionOf32 == 32)
    {
        //If the lower limit is 32, then the upper limit has to be 32 due to the
        //assertion that upper must be >= to the lower limit. If the numerator is
        //equal to 32, then the equation would be 32/32 == 1, therefore no resistor
        //ladder is needed
        HWREG16(baseAddress + OFS_CECTL2) |= CERS_3; //Vref, no resistor ladder
    }
    else
    {
        HWREG16(baseAddress + OFS_CECTL2) |= CERS_2; //Vref with resistor ladder
    }

    //Set COMPE Control 2 Register
    HWREG16(baseAddress + OFS_CECTL2) |=
        supplyVoltageReferenceBase //Set Supply Voltage Base
        + ((upperLimitSupplyVoltageFractionOf32 - 1) << 8) //Set Supply Voltage Num.
        + (lowerLimitSupplyVoltageFractionOf32 - 1);
}

void Comp_E_setReferenceAccuracy(uint16_t baseAddress,
                                 uint16_t referenceAccuracy)
{
    HWREG16(baseAddress + OFS_CECTL2) &= ~(CEREFACC);
    HWREG16(baseAddress + OFS_CECTL2) |= referenceAccuracy;
}

void Comp_E_setPowerMode(uint16_t baseAddress,
                         uint16_t powerMode)
{
    HWREG16(baseAddress +
            OFS_CECTL1) &= ~(COMP_E_NORMAL_MODE | COMP_E_ULTRA_LOW_POWER_MODE);
    HWREG16(baseAddress + OFS_CECTL1) |= powerMode;
}

void Comp_E_enableInterrupt(uint16_t baseAddress,
                            uint16_t interruptMask)
{
    //Set the Interrupt enable bit
    HWREG16(baseAddress + OFS_CEINT) |= interruptMask;
}

void Comp_E_disableInterrupt(uint16_t baseAddress,
                             uint16_t interruptMask)
{
    HWREG16(baseAddress + OFS_CEINT) &= ~(interruptMask);
}

void Comp_E_clearInterrupt(uint16_t baseAddress,
                           uint16_t interruptFlagMask)
{
    HWREG16(baseAddress + OFS_CEINT) &= ~(interruptFlagMask);
}

uint8_t Comp_E_getInterruptStatus(uint16_t baseAddress,
                                  uint16_t interruptFlagMask)
{
    return (HWREG16(baseAddress + OFS_CEINT) & interruptFlagMask);
}

void Comp_E_setInterruptEdgeDirection(uint16_t baseAddress,
                                      uint16_t edgeDirection)
{
    //Set the edge direction that will trigger an interrupt
    if(COMP_E_RISINGEDGE == edgeDirection)
    {
        HWREG16(baseAddress + OFS_CECTL1) |= CEIES;
    }
    else if(COMP_E_FALLINGEDGE == edgeDirection)
    {
        HWREG16(baseAddress + OFS_CECTL1) &= ~(CEIES);
    }
}

void Comp_E_toggleInterruptEdgeDirection(uint16_t baseAddress)
{
    HWREG16(baseAddress + OFS_CECTL1) ^= CEIES;
}

void Comp_E_enable(uint16_t baseAddress)
{
    HWREG16(baseAddress + OFS_CECTL1) |= CEON;
}

void Comp_E_disable(uint16_t baseAddress)
{
    HWREG16(baseAddress + OFS_CECTL1) &= ~(CEON);
}

void Comp_E_shortInputs(uint16_t baseAddress)
{
    HWREG16(baseAddress + OFS_CECTL1) |= CESHORT;
}

void Comp_E_unshortInputs(uint16_t baseAddress)
{
    HWREG16(baseAddress + OFS_CECTL1) &= ~(CESHORT);
}

void Comp_E_disableInputBuffer(uint16_t baseAddress,
                               uint16_t inputPort)
{
    HWREG16(baseAddress + OFS_CECTL3) |= (inputPort);
}

void Comp_E_enableInputBuffer(uint16_t baseAddress,
                              uint16_t inputPort)
{
    HWREG16(baseAddress + OFS_CECTL3) &= ~(inputPort);
}

void Comp_E_swapIO(uint16_t baseAddress)
{
    HWREG16(baseAddress + OFS_CECTL1) ^= CEEX; //Toggle CEEX bit
}

uint16_t Comp_E_outputValue(uint16_t baseAddress)
{
    return (HWREG16(baseAddress + OFS_CECTL1) & CEOUT);
}

#endif
//*****************************************************************************
//
//! Close the doxygen group for comp_e_api
//! @}
//
//*****************************************************************************
