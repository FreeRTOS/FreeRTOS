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
// sfr.c - Driver for the sfr Module.
//
//*****************************************************************************

//*****************************************************************************
//
//! \addtogroup sfr_api sfr
//! @{
//
//*****************************************************************************

#include "inc/hw_regaccess.h"
#include "inc/hw_memmap.h"

#ifdef __MSP430_HAS_SFR__
#include "sfr.h"

#include <assert.h>

void SFR_enableInterrupt(uint8_t interruptMask)
{
    HWREG8(SFR_BASE + OFS_SFRIE1_L) |= interruptMask;
}

void SFR_disableInterrupt(uint8_t interruptMask)
{
    HWREG8(SFR_BASE + OFS_SFRIE1_L) &= ~(interruptMask);
}

uint8_t SFR_getInterruptStatus(uint8_t interruptFlagMask)
{
    return (HWREG8(SFR_BASE + OFS_SFRIFG1_L) & interruptFlagMask);
}

void SFR_clearInterrupt(uint8_t interruptFlagMask)
{
    HWREG8(SFR_BASE + OFS_SFRIFG1_L) &= ~(interruptFlagMask);
}

void SFR_setResetPinPullResistor(uint16_t pullResistorSetup)
{
    HWREG8(SFR_BASE + OFS_SFRRPCR_L) &= ~(SYSRSTRE + SYSRSTUP);
    HWREG8(SFR_BASE + OFS_SFRRPCR_L) |= pullResistorSetup;
}

void SFR_setNMIEdge(uint16_t edgeDirection)
{
    HWREG8(SFR_BASE + OFS_SFRRPCR_L) &= ~(SYSNMIIES);
    HWREG8(SFR_BASE + OFS_SFRRPCR_L) |= edgeDirection;
}

void SFR_setResetNMIPinFunction(uint8_t resetPinFunction)
{
    HWREG8(SFR_BASE + OFS_SFRRPCR_L) &= ~(SYSNMI);
    HWREG8(SFR_BASE + OFS_SFRRPCR_L) |= resetPinFunction;
}

#endif
//*****************************************************************************
//
//! Close the doxygen group for sfr_api
//! @}
//
//*****************************************************************************
