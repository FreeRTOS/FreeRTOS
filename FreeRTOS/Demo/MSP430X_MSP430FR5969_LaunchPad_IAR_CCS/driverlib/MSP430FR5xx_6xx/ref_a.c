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
// ref_a.c - Driver for the ref_a Module.
//
//*****************************************************************************

//*****************************************************************************
//
//! \addtogroup ref_a_api ref_a
//! @{
//
//*****************************************************************************

#include "inc/hw_regaccess.h"
#include "inc/hw_memmap.h"

#ifdef __MSP430_HAS_REF_A__
#include "ref_a.h"

#include <assert.h>

void Ref_A_setReferenceVoltage(uint16_t baseAddress,
                               uint8_t referenceVoltageSelect)
{
    HWREG8(baseAddress + OFS_REFCTL0_L) &= ~(REFVSEL_3);
    HWREG8(baseAddress + OFS_REFCTL0_L) |= referenceVoltageSelect;
}

void Ref_A_disableTempSensor(uint16_t baseAddress)
{
    HWREG8(baseAddress + OFS_REFCTL0_L) |= REFTCOFF;
}

void Ref_A_enableTempSensor(uint16_t baseAddress)
{
    HWREG8(baseAddress + OFS_REFCTL0_L) &= ~(REFTCOFF);
}

void Ref_A_enableReferenceVoltageOutput(uint16_t baseAddress)
{
    HWREG8(baseAddress + OFS_REFCTL0_L) |= REFOUT;
}

void Ref_A_disableReferenceVoltageOutput(uint16_t baseAddress)
{
    HWREG8(baseAddress + OFS_REFCTL0_L) &= ~(REFOUT);
}

void Ref_A_enableReferenceVoltage(uint16_t baseAddress)
{
    HWREG8(baseAddress + OFS_REFCTL0_L) |= REFON;
}

void Ref_A_disableReferenceVoltage(uint16_t baseAddress)
{
    HWREG8(baseAddress + OFS_REFCTL0_L) &= ~(REFON);
}

uint16_t Ref_A_getBandgapMode(uint16_t baseAddress)
{
    return (HWREG16((baseAddress) + OFS_REFCTL0) & BGMODE);
}

bool Ref_A_isBandgapActive(uint16_t baseAddress)
{
    if(HWREG16((baseAddress) + OFS_REFCTL0) & REFBGACT)
    {
        return (REF_A_ACTIVE);
    }
    else
    {
        return (REF_A_INACTIVE);
    }
}

uint16_t Ref_A_isRefGenBusy(uint16_t baseAddress)
{
    return (HWREG16((baseAddress) + OFS_REFCTL0) & REFGENBUSY);
}

bool Ref_A_isRefGenActive(uint16_t baseAddress)
{
    if(HWREG16((baseAddress) + OFS_REFCTL0) & REFGENACT)
    {
        return (REF_A_ACTIVE);
    }
    else
    {
        return (REF_A_INACTIVE);
    }
}

bool Ref_A_isBufferedBandgapVoltageReady(uint16_t baseAddress)
{
    if(HWREG16((baseAddress) + OFS_REFCTL0) & REFBGRDY)
    {
        return (REF_A_READY);
    }
    else
    {
        return (REF_A_NOTREADY);
    }
}

bool Ref_A_isVariableReferenceVoltageOutputReady(uint16_t baseAddress)
{
    if(HWREG16((baseAddress) + OFS_REFCTL0) & REFGENRDY)
    {
        return (REF_A_READY);
    }
    else
    {
        return (REF_A_NOTREADY);
    }
}

void Ref_A_setReferenceVoltageOneTimeTrigger(uint16_t baseAddress)
{
    HWREG8(baseAddress + OFS_REFCTL0_L) |= REFGENOT;
}

void Ref_A_setBufferedBandgapVoltageOneTimeTrigger(uint16_t baseAddress)
{
    HWREG8(baseAddress + OFS_REFCTL0_L) |= REFBGOT;
}

#endif
//*****************************************************************************
//
//! Close the doxygen group for ref_a_api
//! @}
//
//*****************************************************************************
