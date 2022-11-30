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
// crc.h - Driver for the CRC Module.
//
//*****************************************************************************

#ifndef __MSP430WARE_CRC_H__
#define __MSP430WARE_CRC_H__

#include "inc/hw_memmap.h"

#ifdef __MSP430_HAS_CRC__

//*****************************************************************************
//
// If building with a C++ compiler, make all of the definitions in this header
// have a C binding.
//
//*****************************************************************************
#ifdef __cplusplus
extern "C"
{
#endif

//*****************************************************************************
//
// Prototypes for the APIs.
//
//*****************************************************************************

//*****************************************************************************
//
//! \brief Sets the seed for the CRC.
//!
//! This function sets the seed for the CRC to begin generating a signature
//! with the given seed and all passed data. Using this function resets the CRC
//! signature.
//!
//! \param baseAddress is the base address of the CRC module.
//! \param seed is the seed for the CRC to start generating a signature from.
//!        \n Modified bits are \b CRCINIRES of \b CRCINIRES register.
//!
//! \return None
//
//*****************************************************************************
extern void CRC_setSeed(uint16_t baseAddress,
                        uint16_t seed);

//*****************************************************************************
//
//! \brief Sets the 16 bit data to add into the CRC module to generate a new
//! signature.
//!
//! This function sets the given data into the CRC module to generate the new
//! signature from the current signature and new data.
//!
//! \param baseAddress is the base address of the CRC module.
//! \param dataIn is the data to be added, through the CRC module, to the
//!        signature.
//!        \n Modified bits are \b CRCDI of \b CRCDI register.
//!
//! \return None
//
//*****************************************************************************
extern void CRC_set16BitData(uint16_t baseAddress,
                             uint16_t dataIn);

//*****************************************************************************
//
//! \brief Sets the 8 bit data to add into the CRC module to generate a new
//! signature.
//!
//! This function sets the given data into the CRC module to generate the new
//! signature from the current signature and new data.
//!
//! \param baseAddress is the base address of the CRC module.
//! \param dataIn is the data to be added, through the CRC module, to the
//!        signature.
//!        \n Modified bits are \b CRCDI of \b CRCDI register.
//!
//! \return None
//
//*****************************************************************************
extern void CRC_set8BitData(uint16_t baseAddress,
                            uint8_t dataIn);

//*****************************************************************************
//
//! \brief Translates the 16 bit data by reversing the bits in each byte and
//! then sets this data to add into the CRC module to generate a new signature.
//!
//! This function first reverses the bits in each byte of the data and then
//! generates the new signature from the current signature and new translated
//! data.
//!
//! \param baseAddress is the base address of the CRC module.
//! \param dataIn is the data to be added, through the CRC module, to the
//!        signature.
//!        \n Modified bits are \b CRCDIRB of \b CRCDIRB register.
//!
//! \return None
//
//*****************************************************************************
extern void CRC_set16BitDataReversed(uint16_t baseAddress,
                                     uint16_t dataIn);

//*****************************************************************************
//
//! \brief Translates the 8 bit data by reversing the bits in each byte and
//! then sets this data to add into the CRC module to generate a new signature.
//!
//! This function first reverses the bits in each byte of the data and then
//! generates the new signature from the current signature and new translated
//! data.
//!
//! \param baseAddress is the base address of the CRC module.
//! \param dataIn is the data to be added, through the CRC module, to the
//!        signature.
//!        \n Modified bits are \b CRCDIRB of \b CRCDIRB register.
//!
//! \return None
//
//*****************************************************************************
extern void CRC_set8BitDataReversed(uint16_t baseAddress,
                                    uint8_t dataIn);

//*****************************************************************************
//
//! \brief Returns the value currently in the Data register.
//!
//! This function returns the value currently in the data register. If set in
//! byte bits reversed format, then the translated data would be returned.
//!
//! \param baseAddress is the base address of the CRC module.
//!
//! \return The value currently in the data register
//
//*****************************************************************************
extern uint16_t CRC_getData(uint16_t baseAddress);

//*****************************************************************************
//
//! \brief Returns the value pf the Signature Result.
//!
//! This function returns the value of the signature result generated by the
//! CRC.
//!
//! \param baseAddress is the base address of the CRC module.
//!
//! \return The value currently in the data register
//
//*****************************************************************************
extern uint16_t CRC_getResult(uint16_t baseAddress);

//*****************************************************************************
//
//! \brief Returns the bit-wise reversed format of the Signature Result.
//!
//! This function returns the bit-wise reversed format of the Signature Result.
//!
//! \param baseAddress is the base address of the CRC module.
//!
//! \return The bit-wise reversed format of the Signature Result
//
//*****************************************************************************
extern uint16_t CRC_getResultBitsReversed(uint16_t baseAddress);

//*****************************************************************************
//
// Mark the end of the C bindings section for C++ compilers.
//
//*****************************************************************************
#ifdef __cplusplus
}
#endif

#endif
#endif // __MSP430WARE_CRC_H__
