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
// crc.c - Driver for the crc Module.
//
//*****************************************************************************

//*****************************************************************************
//
//! \addtogroup crc_api crc
//! @{
//
//*****************************************************************************

#include "inc/hw_regaccess.h"
#include "inc/hw_memmap.h"

#ifdef __MSP430_HAS_CRC__
#include "crc.h"

#include <assert.h>

void CRC_setSeed(uint16_t baseAddress,
                 uint16_t seed)
{
    HWREG16(baseAddress + OFS_CRCINIRES) = seed;
}

void CRC_set16BitData(uint16_t baseAddress,
                      uint16_t dataIn)
{
    HWREG16(baseAddress + OFS_CRCDI) = dataIn;
}

void CRC_set8BitData(uint16_t baseAddress,
                     uint8_t dataIn)
{
    HWREG8(baseAddress + OFS_CRCDI_L) = dataIn;
}

void CRC_set16BitDataReversed(uint16_t baseAddress,
                              uint16_t dataIn)
{
    HWREG16(baseAddress + OFS_CRCDIRB) = dataIn;
}

void CRC_set8BitDataReversed(uint16_t baseAddress,
                             uint8_t dataIn)
{
    HWREG8(baseAddress + OFS_CRCDIRB_L) = dataIn;
}

uint16_t CRC_getData(uint16_t baseAddress)
{
    return (HWREG16(baseAddress + OFS_CRCDI));
}

uint16_t CRC_getResult(uint16_t baseAddress)
{
    return (HWREG16(baseAddress + OFS_CRCINIRES));
}

uint16_t CRC_getResultBitsReversed(uint16_t baseAddress)
{
    return (HWREG16(baseAddress + OFS_CRCRESR));
}

#endif
//*****************************************************************************
//
//! Close the doxygen group for crc_api
//! @}
//
//*****************************************************************************
