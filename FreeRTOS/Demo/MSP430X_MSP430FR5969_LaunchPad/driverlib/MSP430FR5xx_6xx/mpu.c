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
// mpu.c - Driver for the mpu Module.
//
//*****************************************************************************

//*****************************************************************************
//
//! \addtogroup mpu_api mpu
//! @{
//
//*****************************************************************************

#include "inc/hw_regaccess.h"
#include "inc/hw_memmap.h"

#ifdef __MSP430_HAS_MPU__
#include "mpu.h"

#include <assert.h>

//*****************************************************************************
//
// The following value is used by createTwoSegments, createThreeSegments to
// check the user has passed a valid segmentation value. This value was
// obtained from the User's Guide.
//
//*****************************************************************************
#define MPU_MAX_SEG_VALUE                                                0x13C1

void MPU_initTwoSegments(uint16_t baseAddress,
                         uint16_t seg1boundary,
                         uint8_t seg1accmask,
                         uint8_t seg2accmask)
{
    // Write MPU password to allow MPU register configuration
    HWREG16(baseAddress + OFS_MPUCTL0) = MPUPW | HWREG8(
        baseAddress + OFS_MPUCTL0);

    // Create two memory segmentations
    HWREG16(baseAddress + OFS_MPUSEGB1) = seg1boundary;
    HWREG16(baseAddress + OFS_MPUSEGB2) = seg1boundary;

    // Set access rights based on user's selection for segment1
    switch(seg1accmask)
    {
    case MPU_EXEC | MPU_READ:
        HWREG16(baseAddress + OFS_MPUSAM) &= ~MPUSEG1WE;
        HWREG16(baseAddress + OFS_MPUSAM) |= MPUSEG1XE + MPUSEG1RE;
        break;
    case MPU_READ | MPU_WRITE:
        HWREG16(baseAddress + OFS_MPUSAM) &= ~MPUSEG1XE;
        HWREG16(baseAddress + OFS_MPUSAM) |= MPUSEG1RE + MPUSEG1WE;
        break;
    case MPU_READ:
        HWREG16(baseAddress + OFS_MPUSAM) &= ~(MPUSEG1XE + MPUSEG1WE);
        HWREG16(baseAddress + OFS_MPUSAM) |= MPUSEG1RE;
        break;
    case MPU_EXEC | MPU_READ | MPU_WRITE:
        HWREG16(baseAddress +
                OFS_MPUSAM) |= (MPUSEG1XE + MPUSEG1WE + MPUSEG1RE);
        break;
    case MPU_NO_READ_WRITE_EXEC:
        HWREG16(baseAddress +
                OFS_MPUSAM) &= ~(MPUSEG1XE + MPUSEG1WE + MPUSEG1RE);
        break;
    default:
        break;
    }

    // Set access rights based on user's selection for segment2
    switch(seg2accmask)
    {
    case MPU_EXEC | MPU_READ:
        HWREG16(baseAddress + OFS_MPUSAM) &= ~(MPUSEG3WE + MPUSEG2WE);
        HWREG16(baseAddress + OFS_MPUSAM) |= MPUSEG3XE + MPUSEG3RE +
                                             MPUSEG2XE + MPUSEG2RE;
        break;
    case MPU_READ | MPU_WRITE:
        HWREG16(baseAddress + OFS_MPUSAM) &= ~(MPUSEG3XE + MPUSEG2XE);
        HWREG16(baseAddress + OFS_MPUSAM) |= MPUSEG3RE + MPUSEG3WE +
                                             MPUSEG2RE + MPUSEG2WE;
        break;
    case MPU_READ:
        HWREG16(baseAddress + OFS_MPUSAM) &= ~(MPUSEG3XE + MPUSEG3WE +
                                               MPUSEG2XE + MPUSEG2WE);
        HWREG16(baseAddress + OFS_MPUSAM) |= MPUSEG3RE + MPUSEG2RE;
        break;
    case MPU_EXEC | MPU_READ | MPU_WRITE:
        HWREG16(baseAddress + OFS_MPUSAM) |= (MPUSEG3XE + MPUSEG3WE +
                                              MPUSEG3RE + MPUSEG2XE +
                                              MPUSEG2WE + MPUSEG2RE);
        break;
    case MPU_NO_READ_WRITE_EXEC:
        HWREG16(baseAddress + OFS_MPUSAM) &= ~(MPUSEG3XE + MPUSEG3WE +
                                               MPUSEG3RE + MPUSEG2XE +
                                               MPUSEG2WE + MPUSEG2RE);
        break;
    default:
        break;
    }

    //Lock MPU to disable writing to all registers
    HWREG8(baseAddress + OFS_MPUCTL0_H) = 0x00;
}

void MPU_initThreeSegments(uint16_t baseAddress,
                           MPU_initThreeSegmentsParam *param)
{
    // Write MPU password to allow MPU register configuration
    HWREG16(baseAddress + OFS_MPUCTL0) = MPUPW | HWREG8(
        baseAddress + OFS_MPUCTL0);

    // Create two memory segmentations
    HWREG16(baseAddress + OFS_MPUSEGB1) = param->seg1boundary;
    HWREG16(baseAddress + OFS_MPUSEGB2) = param->seg2boundary;

    // Set access rights based on user's selection for segment1
    switch(param->seg1accmask)
    {
    case MPU_EXEC | MPU_READ:
        HWREG16(baseAddress + OFS_MPUSAM) &= ~MPUSEG1WE;
        HWREG16(baseAddress + OFS_MPUSAM) |= MPUSEG1XE + MPUSEG1RE;
        break;
    case MPU_READ | MPU_WRITE:
        HWREG16(baseAddress + OFS_MPUSAM) &= ~MPUSEG1XE;
        HWREG16(baseAddress + OFS_MPUSAM) |= MPUSEG1RE + MPUSEG1WE;
        break;
    case MPU_READ:
        HWREG16(baseAddress + OFS_MPUSAM) &= ~(MPUSEG1XE + MPUSEG1WE);
        HWREG16(baseAddress + OFS_MPUSAM) |= MPUSEG1RE;
        break;
    case MPU_EXEC | MPU_READ | MPU_WRITE:
        HWREG16(baseAddress +
                OFS_MPUSAM) |= (MPUSEG1XE + MPUSEG1WE + MPUSEG1RE);
        break;
    case MPU_NO_READ_WRITE_EXEC:
        HWREG16(baseAddress +
                OFS_MPUSAM) &= ~(MPUSEG1XE + MPUSEG1WE + MPUSEG1RE);
        break;
    default:
        break;
    }

    // Set access rights based on user's selection for segment2
    switch(param->seg2accmask)
    {
    case MPU_EXEC | MPU_READ:
        HWREG16(baseAddress + OFS_MPUSAM) &= ~MPUSEG2WE;
        HWREG16(baseAddress + OFS_MPUSAM) |= MPUSEG2XE + MPUSEG2RE;
        break;
    case MPU_READ | MPU_WRITE:
        HWREG16(baseAddress + OFS_MPUSAM) &= ~MPUSEG2XE;
        HWREG16(baseAddress + OFS_MPUSAM) |= MPUSEG2RE + MPUSEG2WE;
        break;
    case MPU_READ:
        HWREG16(baseAddress + OFS_MPUSAM) &= ~(MPUSEG2XE + MPUSEG2WE);
        HWREG16(baseAddress + OFS_MPUSAM) |= MPUSEG2RE;
        break;
    case MPU_EXEC | MPU_READ | MPU_WRITE:
        HWREG16(baseAddress +
                OFS_MPUSAM) |= (MPUSEG2XE + MPUSEG2WE + MPUSEG2RE);
        break;
    case MPU_NO_READ_WRITE_EXEC:
        HWREG16(baseAddress +
                OFS_MPUSAM) &= ~(MPUSEG2XE + MPUSEG2WE + MPUSEG2RE);
        break;
    default:
        break;
    }

    // Set access rights based on user's selection for segment3
    switch(param->seg3accmask)
    {
    case MPU_EXEC | MPU_READ:
        HWREG16(baseAddress + OFS_MPUSAM) &= ~MPUSEG3WE;
        HWREG16(baseAddress + OFS_MPUSAM) |= MPUSEG3XE + MPUSEG3RE;
        break;
    case MPU_READ | MPU_WRITE:
        HWREG16(baseAddress + OFS_MPUSAM) &= ~MPUSEG3XE;
        HWREG16(baseAddress + OFS_MPUSAM) |= MPUSEG3RE + MPUSEG3WE;
        break;
    case MPU_READ:
        HWREG16(baseAddress + OFS_MPUSAM) &= ~(MPUSEG3XE + MPUSEG3WE);
        HWREG16(baseAddress + OFS_MPUSAM) |= MPUSEG3RE;
        break;
    case MPU_EXEC | MPU_READ | MPU_WRITE:
        HWREG16(baseAddress +
                OFS_MPUSAM) |= (MPUSEG3XE + MPUSEG3WE + MPUSEG3WE);
        break;
    case MPU_NO_READ_WRITE_EXEC:
        HWREG16(baseAddress +
                OFS_MPUSAM) &= ~(MPUSEG3XE + MPUSEG3WE + MPUSEG3WE);
        break;
    default:
        break;
    }

    //Lock MPU to disable writing to all registers
    HWREG8(baseAddress + OFS_MPUCTL0_H) = 0x00;
}

void MPU_initInfoSegment(uint16_t baseAddress,
                         uint8_t accmask)
{
    // Write MPU password to allow MPU register configuration
    HWREG16(baseAddress + OFS_MPUCTL0) = MPUPW | HWREG8(
        baseAddress + OFS_MPUCTL0);

    // Set access rights based on user's selection for segment1
    switch(accmask)
    {
    case MPU_EXEC | MPU_READ:
        HWREG16(baseAddress + OFS_MPUSAM) &= ~MPUSEGIWE;
        HWREG16(baseAddress + OFS_MPUSAM) |= MPUSEGIXE + MPUSEGIRE;
        break;
    case MPU_READ | MPU_WRITE:
        HWREG16(baseAddress + OFS_MPUSAM) &= ~MPUSEGIXE;
        HWREG16(baseAddress + OFS_MPUSAM) |= MPUSEGIRE + MPUSEGIWE;
        break;
    case MPU_READ:
        HWREG16(baseAddress + OFS_MPUSAM) &= ~(MPUSEGIXE + MPUSEGIWE);
        HWREG16(baseAddress + OFS_MPUSAM) |= MPUSEGIRE;
        break;
    case MPU_EXEC | MPU_READ | MPU_WRITE:
        HWREG16(baseAddress +
                OFS_MPUSAM) |= (MPUSEGIXE + MPUSEGIWE + MPUSEGIRE);
        break;
    case MPU_NO_READ_WRITE_EXEC:
        HWREG16(baseAddress +
                OFS_MPUSAM) &= ~(MPUSEGIXE + MPUSEGIWE + MPUSEGIRE);
        break;
    default:
        break;
    }

    //Lock MPU to disable writing to all registers
    HWREG8(baseAddress + OFS_MPUCTL0_H) = 0x00;
}

void MPU_enableNMIevent(uint16_t baseAddress)
{
    HWREG16(baseAddress + OFS_MPUCTL0) = MPUPW | MPUSEGIE |
                                         HWREG8(baseAddress + OFS_MPUCTL0);

    //Lock MPU to disable writing to all registers
    HWREG8(baseAddress + OFS_MPUCTL0_H) = 0x00;
}

void MPU_start(uint16_t baseAddress)
{
    HWREG16(baseAddress + OFS_MPUCTL0) = MPUPW | MPUENA | HWREG8(
        baseAddress + OFS_MPUCTL0);

    //Lock MPU to disable writing to all registers
    HWREG8(baseAddress + OFS_MPUCTL0_H) = 0x00;
}

void MPU_enablePUCOnViolation(uint16_t baseAddress,
                              uint16_t segment)
{
    HWREG16(baseAddress + OFS_MPUCTL0) = MPUPW | HWREG8(
        baseAddress + OFS_MPUCTL0);
    HWREG16(baseAddress + OFS_MPUSAM) |= segment;

    //Lock MPU to disable writing to all registers
    HWREG8(baseAddress + OFS_MPUCTL0_H) = 0x00;
}

void MPU_disablePUCOnViolation(uint16_t baseAddress,
                               uint16_t segment)
{
    HWREG16(baseAddress + OFS_MPUCTL0) = MPUPW | HWREG8(
        baseAddress + OFS_MPUCTL0);
    HWREG16(baseAddress + OFS_MPUSAM) &= ~segment;

    //Lock MPU to disable writing to all registers
    HWREG8(baseAddress + OFS_MPUCTL0_H) = 0x00;
}

uint16_t MPU_getInterruptStatus(uint16_t baseAddress,
                                uint16_t memAccFlag)
{
    return (HWREG16(baseAddress + OFS_MPUCTL1) & memAccFlag);
}

uint16_t MPU_clearInterrupt(uint16_t baseAddress,
                            uint16_t memAccFlag)
{
    HWREG16(baseAddress + OFS_MPUCTL0) = MPUPW | HWREG8(
        baseAddress + OFS_MPUCTL0);
    HWREG16(baseAddress + OFS_MPUCTL1) &= ~memAccFlag;

    //Lock MPU to disable writing to all registers
    HWREG8(baseAddress + OFS_MPUCTL0_H) = 0x00;

    return (HWREG16(baseAddress + OFS_MPUCTL1) & memAccFlag);
}

uint16_t MPU_clearAllInterrupts(uint16_t baseAddress)
{
    HWREG16(baseAddress + OFS_MPUCTL0) = MPUPW | HWREG8(
        baseAddress + OFS_MPUCTL0);
    HWREG16(baseAddress +
            OFS_MPUCTL1) &= ~(MPUSEG1IFG + MPUSEG2IFG + MPUSEG3IFG);

    //Lock MPU to disable writing to all registers
    HWREG8(baseAddress + OFS_MPUCTL0_H) = 0x00;

    return (HWREG16(baseAddress +
                    OFS_MPUCTL1) & (MPUSEG1IFG + MPUSEG2IFG + MPUSEG3IFG));
}

void MPU_lockMPU(uint16_t baseAddress)
{
    HWREG16(baseAddress + OFS_MPUCTL0) = MPUPW | MPULOCK |
                                         HWREG8(baseAddress + OFS_MPUCTL0);

    //Lock MPU to disable writing to all registers
    HWREG8(baseAddress + OFS_MPUCTL0_H) = 0x00;
}

#endif
//*****************************************************************************
//
//! Close the doxygen group for mpu_api
//! @}
//
//*****************************************************************************
