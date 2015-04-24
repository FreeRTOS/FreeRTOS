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
// crc32.c - Driver for the crc32 Module.
//
//*****************************************************************************

//*****************************************************************************
//
//! \addtogroup crc32_api crc32
//! @{
//
//*****************************************************************************

#include "inc/hw_regaccess.h"
#include "inc/hw_memmap.h"

#ifdef __MSP430_HAS_CRC32__
#include "crc32.h"

#include <assert.h>

void CRC32_setSeed(uint32_t seed,
                   uint8_t crcMode)
{
    if(CRC16_MODE == crcMode)
    {
        HWREG16(CRC32_BASE + OFS_CRC16INIRESW0) = seed;
    }
    else
    {
        HWREG16(CRC32_BASE + OFS_CRC32INIRESW1) = ((seed & 0xFFFF0000)
                                                   >> 16);
        HWREG16(CRC32_BASE + OFS_CRC32INIRESW0) = (seed & 0xFFFF);
    }
}

void CRC32_set8BitData(uint8_t dataIn,
                       uint8_t crcMode)
{
    if(CRC16_MODE == crcMode)
    {
        HWREG8(CRC32_BASE + OFS_CRC16DIW0_L) = dataIn;
    }
    else
    {
        HWREG8(CRC32_BASE + OFS_CRC32DIW0_L) = dataIn;
    }
}

void CRC32_set16BitData(uint16_t dataIn,
                        uint8_t crcMode)
{
    if(CRC16_MODE == crcMode)
    {
        HWREG16(CRC32_BASE + OFS_CRC16DIW0) = dataIn;
    }
    else
    {
        HWREG16(CRC32_BASE + OFS_CRC32DIW0) = dataIn;
    }
}

void CRC32_set32BitData(uint32_t dataIn)
{
    HWREG16(CRC32_BASE + OFS_CRC32DIW0) = dataIn & 0xFFFF;
    HWREG16(CRC32_BASE + OFS_CRC32DIW1) = (uint16_t) ((dataIn & 0xFFFF0000)
                                                      >> 16);
}

void CRC32_set8BitDataReversed(uint8_t dataIn,
                               uint8_t crcMode)
{
    if(CRC16_MODE == crcMode)
    {
        HWREG8(CRC32_BASE + OFS_CRC16DIRBW1_L) = dataIn;
    }
    else
    {
        HWREG8(CRC32_BASE + OFS_CRC32DIRBW1_L) = dataIn;
    }
}

void CRC32_set16BitDataReversed(uint16_t dataIn,
                                uint8_t crcMode)
{
    if(CRC16_MODE == crcMode)
    {
        HWREG16(CRC32_BASE + OFS_CRC16DIRBW1) = dataIn;
    }
    else
    {
        HWREG16(CRC32_BASE + OFS_CRC32DIRBW1) = dataIn;
    }
}

void CRC32_set32BitDataReversed(uint32_t dataIn)
{
    HWREG16(CRC32_BASE + OFS_CRC32DIRBW1) = dataIn & 0xFFFF;
    HWREG16(CRC32_BASE + OFS_CRC32DIRBW0) = (uint16_t) ((dataIn & 0xFFFF0000)
                                                        >> 16);
}

uint32_t CRC32_getResult(uint8_t crcMode)
{
    if(CRC16_MODE == crcMode)
    {
        return (HWREG16(CRC32_BASE + OFS_CRC16INIRESW0));
    }
    else
    {
        uint32_t result = 0;
        result = HWREG16(CRC32_BASE + OFS_CRC32INIRESW1);
        result = (result << 16);
        result |= HWREG16(CRC32_BASE + OFS_CRC32INIRESW0);
        return (result);
    }
}

uint32_t CRC32_getResultReversed(uint8_t crcMode)
{
    if(CRC16_MODE == crcMode)
    {
        return (HWREG16(CRC32_BASE + OFS_CRC16RESRW0));
    }
    else
    {
        uint32_t result = 0;
        result = HWREG16(CRC32_BASE + OFS_CRC32RESRW0);
        result = (result << 16);
        result |= HWREG16(CRC32_BASE + OFS_CRC32RESRW1);
        return (result);
    }
}

#endif
//*****************************************************************************
//
//! Close the doxygen group for crc32_api
//! @}
//
//*****************************************************************************
