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
// mpy32.c - Driver for the mpy32 Module.
//
//*****************************************************************************

//*****************************************************************************
//
//! \addtogroup mpy32_api mpy32
//! @{
//
//*****************************************************************************

#include "inc/hw_regaccess.h"
#include "inc/hw_memmap.h"

#ifdef __MSP430_HAS_MPY32__
#include "mpy32.h"

#include <assert.h>

void MPY32_setWriteDelay(uint16_t writeDelaySelect)
{
    HWREG16(MPY32_BASE + OFS_MPY32CTL0) &= ~(MPYDLY32 + MPYDLYWRTEN);
    HWREG16(MPY32_BASE + OFS_MPY32CTL0) |= writeDelaySelect;
}

void MPY32_enableSaturationMode(void)
{
    HWREG8(MPY32_BASE + OFS_MPY32CTL0_L) |= MPYSAT;
}

void MPY32_disableSaturationMode(void)
{
    HWREG8(MPY32_BASE + OFS_MPY32CTL0_L) &= ~(MPYSAT);
}

uint8_t MPY32_getSaturationMode(void)
{
    return (HWREG8(MPY32_BASE + OFS_MPY32CTL0_L) & (MPYSAT));
}

void MPY32_enableFractionalMode(void)
{
    HWREG8(MPY32_BASE + OFS_MPY32CTL0_L) |= MPYFRAC;
}

void MPY32_disableFractionalMode(void)
{
    HWREG8(MPY32_BASE + OFS_MPY32CTL0_L) &= ~(MPYFRAC);
}

uint8_t MPY32_getFractionalMode(void)
{
    return (HWREG8(MPY32_BASE + OFS_MPY32CTL0_L) & (MPYFRAC));
}

void MPY32_setOperandOne8Bit(uint8_t multiplicationType,
                             uint8_t operand)
{
    HWREG8(MPY32_BASE + OFS_MPY + multiplicationType) = operand;
}

void MPY32_setOperandOne16Bit(uint8_t multiplicationType,
                              uint16_t operand)
{
    HWREG16(MPY32_BASE + OFS_MPY + multiplicationType) = operand;
}

void MPY32_setOperandOne24Bit(uint8_t multiplicationType,
                              uint32_t operand)
{
    multiplicationType <<= 1;
    HWREG16(MPY32_BASE + OFS_MPY32L + multiplicationType) = operand;
    HWREG8(MPY32_BASE + OFS_MPY32H + multiplicationType) = (operand >> 16);
}

void MPY32_setOperandOne32Bit(uint8_t multiplicationType,
                              uint32_t operand)
{
    multiplicationType <<= 1;
    HWREG16(MPY32_BASE + OFS_MPY32L + multiplicationType) = operand;
    HWREG16(MPY32_BASE + OFS_MPY32H + multiplicationType) = (operand >> 16);
}

void MPY32_setOperandTwo8Bit(uint8_t operand)
{
    HWREG8(MPY32_BASE + OFS_OP2) = operand;
}

void MPY32_setOperandTwo16Bit(uint16_t operand)
{
    HWREG16(MPY32_BASE + OFS_OP2) = operand;
}

void MPY32_setOperandTwo24Bit(uint32_t operand)
{
    HWREG16(MPY32_BASE + OFS_OP2L) = operand;
    HWREG8(MPY32_BASE + OFS_OP2H) = (operand >> 16);
}

void MPY32_setOperandTwo32Bit(uint32_t operand)
{
    HWREG16(MPY32_BASE + OFS_OP2L) = operand;
    HWREG16(MPY32_BASE + OFS_OP2H) = (operand >> 16);
}

uint64_t MPY32_getResult(void)
{
    uint64_t result;

    result = HWREG16(MPY32_BASE + OFS_RES0);
    result += ((uint64_t)HWREG16(MPY32_BASE + OFS_RES1) << 16);
    result += ((uint64_t)HWREG16(MPY32_BASE + OFS_RES2) << 32);
    result += ((uint64_t)HWREG16(MPY32_BASE + OFS_RES3) << 48);
    return (result);
}

uint16_t MPY32_getSumExtension(void)
{
    return (HWREG16(MPY32_BASE + OFS_SUMEXT));
}

uint16_t MPY32_getCarryBitValue(void)
{
    return (HWREG16(MPY32_BASE + OFS_MPY32CTL0) | MPYC);
}

void MPY32_clearCarryBitValue(void)
{
    HWREG16(MPY32_BASE + OFS_MPY32CTL0) &= ~MPYC;
}

void MPY32_preloadResult(uint64_t result)
{
    HWREG16(MPY32_BASE + OFS_RES0) = (result & 0xFFFF);
    HWREG16(MPY32_BASE + OFS_RES1) = ((result >> 16) & 0xFFFF);
    HWREG16(MPY32_BASE + OFS_RES2) = ((result >> 32) & 0xFFFF);
    HWREG16(MPY32_BASE + OFS_RES3) = ((result >> 48) & 0xFFFF);
}

#endif
//*****************************************************************************
//
//! Close the doxygen group for mpy32_api
//! @}
//
//*****************************************************************************
