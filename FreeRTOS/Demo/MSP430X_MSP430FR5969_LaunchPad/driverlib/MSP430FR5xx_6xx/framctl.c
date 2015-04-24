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
// framctl.c - Driver for the framctl Module.
//
//*****************************************************************************

//*****************************************************************************
//
//! \addtogroup framctl_api framctl
//! @{
//
//*****************************************************************************

#include "inc/hw_regaccess.h"
#include "inc/hw_memmap.h"

#ifdef __MSP430_HAS_FRAM__
#include "framctl.h"

#include <assert.h>

void FRAMCtl_write8(uint8_t *dataPtr,
                    uint8_t *framPtr,
                    uint16_t numberOfBytes)
{
    while(numberOfBytes > 0)
    {
        //Write to Fram
        *framPtr++ = *dataPtr++;
        numberOfBytes--;
    }
}

void FRAMCtl_write16(uint16_t *dataPtr,
                     uint16_t *framPtr,
                     uint16_t numberOfWords)
{
    while(numberOfWords > 0)
    {
        //Write to Fram
        *framPtr++ = *dataPtr++;
        numberOfWords--;
    }
}

void FRAMCtl_write32(uint32_t *dataPtr,
                     uint32_t *framPtr,
                     uint16_t count)
{
    while(count > 0)
    {
        //Write to Fram
        *framPtr++ = *dataPtr++;
        count--;
    }
}

void FRAMCtl_fillMemory32(uint32_t value,
                          uint32_t *framPtr,
                          uint16_t count)
{
    while(count > 0)
    {
        //Write to Fram
        *framPtr++ = value;
        count--;
    }
}

void FRAMCtl_enableInterrupt(uint8_t interruptMask)
{
    uint8_t waitSelection;

    waitSelection = (HWREG8(FRAM_BASE + OFS_FRCTL0) & 0xFF);
    // Clear lock in FRAM control registers
    HWREG16(FRAM_BASE + OFS_FRCTL0) = FWPW | waitSelection;

    // Enable user selected interrupt sources
    HWREG16(FRAM_BASE + OFS_GCCTL0) |= interruptMask;
}

uint8_t FRAMCtl_getInterruptStatus(uint16_t interruptFlagMask)
{
    return (HWREG16(FRAM_BASE + OFS_GCCTL1) & interruptFlagMask);
}

void FRAMCtl_disableInterrupt(uint16_t interruptMask)
{
    uint8_t waitSelection;

    waitSelection = (HWREG8(FRAM_BASE + OFS_FRCTL0) & 0xFF);
    //Clear lock in FRAM control registers
    HWREG16(FRAM_BASE + OFS_FRCTL0) = FWPW | waitSelection;

    HWREG16(FRAM_BASE + OFS_GCCTL0) &= ~(interruptMask);
}

void FRAMCtl_configureWaitStateControl(uint8_t waitState)
{
    // Clear lock in FRAM control registers
    HWREG16(FRAM_BASE + OFS_FRCTL0) = FWPW;

    HWREG8(FRAM_BASE + OFS_FRCTL0_L) &= ~NWAITS_7;
    HWREG8(FRAM_BASE + OFS_FRCTL0_L) |= (waitState);
}

void FRAMCtl_delayPowerUpFromLPM(uint8_t delayStatus)
{
    uint8_t waitSelection;

    waitSelection = (HWREG8(FRAM_BASE + OFS_FRCTL0) & 0xFF);

    // Clear lock in FRAM control registers
    HWREG16(FRAM_BASE + OFS_FRCTL0) = FWPW | waitSelection;

    HWREG8(FRAM_BASE + OFS_GCCTL0_L) &= ~0x02;
    HWREG8(FRAM_BASE + OFS_GCCTL0_L) |= delayStatus;
}

#endif
//*****************************************************************************
//
//! Close the doxygen group for framctl_api
//! @}
//
//*****************************************************************************
