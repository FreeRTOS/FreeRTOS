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
// crc32.h - Driver for the CRC32 Module.
//
//*****************************************************************************

#ifndef __MSP430WARE_CRC32_H__
#define __MSP430WARE_CRC32_H__

#include "inc/hw_memmap.h"

#ifdef __MSP430_HAS_CRC32__

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
// The following are values that can be passed to the crcMode parameter for
// functions: CRC32_setSeed(), CRC32_getResult(), CRC32_getResultReversed(),
// CRC32_set8BitDataReversed(), CRC32_set16BitDataReversed(),
// CRC32_set8BitData(), and CRC32_set16BitData().
//
//*****************************************************************************
#define CRC32_MODE                                                       (0x01)
#define CRC16_MODE                                                       (0x00)

//*****************************************************************************
//
// Prototypes for the APIs.
//
//*****************************************************************************

//*****************************************************************************
//
//! \brief Sets the seed for the CRC32.
//!
//! This function sets the seed for the CRC32 to begin generating a signature
//! with the given seed and all passed data. Using this function resets the
//! CRC32 signature.
//!
//! \param seed is the seed for the CRC32 to start generating a signature from.
//!        \n Modified bits are \b CRC32INIRESL0 of \b CRC32INIRESL0 register.
//! \param crcMode selects the mode of operation for the CRC32
//!        Valid values are:
//!        - \b CRC32_MODE - 32 Bit Mode
//!        - \b CRC16_MODE - 16 Bit Mode
//!
//! \return None
//
//*****************************************************************************
extern void CRC32_setSeed(uint32_t seed,
                          uint8_t crcMode);

//*****************************************************************************
//
//! \brief Sets the 8 bit data to add into the CRC32 module to generate a new
//! signature.
//!
//! This function sets the given data into the CRC32 module to generate the new
//! signature from the current signature and new data. Bit 0 is treated as the
//! LSB.
//!
//! \param dataIn is the data to be added, through the CRC32 module, to the
//!        signature.
//! \param crcMode selects the mode of operation for the CRC32
//!        Valid values are:
//!        - \b CRC32_MODE - 32 Bit Mode
//!        - \b CRC16_MODE - 16 Bit Mode
//!
//! \return None
//
//*****************************************************************************
extern void CRC32_set8BitData(uint8_t dataIn,
                              uint8_t crcMode);

//*****************************************************************************
//
//! \brief Sets the 16 bit data to add into the CRC32 module to generate a new
//! signature.
//!
//! This function sets the given data into the CRC32 module to generate the new
//! signature from the current signature and new data. Bit 0 is treated as the
//! LSB.
//!
//! \param dataIn is the data to be added, through the CRC32 module, to the
//!        signature.
//! \param crcMode selects the mode of operation for the CRC32
//!        Valid values are:
//!        - \b CRC32_MODE - 32 Bit Mode
//!        - \b CRC16_MODE - 16 Bit Mode
//!
//! \return None
//
//*****************************************************************************
extern void CRC32_set16BitData(uint16_t dataIn,
                               uint8_t crcMode);

//*****************************************************************************
//
//! \brief Sets the 32 bit data to add into the CRC32 module to generate a new
//! signature.
//!
//! This function sets the given data into the CRC32 module to generate the new
//! signature from the current signature and new data. Bit 0 is treated as the
//! LSB.
//!
//! \param dataIn is the data to be added, through the CRC32 module, to the
//!        signature.
//!
//! \return None
//
//*****************************************************************************
extern void CRC32_set32BitData(uint32_t dataIn);

//*****************************************************************************
//
//! \brief Translates the data by reversing the bits in each 8 bit data and
//! then sets this data to add into the CRC32 module to generate a new
//! signature.
//!
//! This function first reverses the bits in each byte of the data and then
//! generates the new signature from the current signature and new translated
//! data. Bit 0 is treated as the MSB.
//!
//! \param dataIn is the data to be added, through the CRC32 module, to the
//!        signature.
//! \param crcMode selects the mode of operation for the CRC32
//!        Valid values are:
//!        - \b CRC32_MODE - 32 Bit Mode
//!        - \b CRC16_MODE - 16 Bit Mode
//!
//! \return None
//
//*****************************************************************************
extern void CRC32_set8BitDataReversed(uint8_t dataIn,
                                      uint8_t crcMode);

//*****************************************************************************
//
//! \brief Translates the data by reversing the bits in each 16 bit data and
//! then sets this data to add into the CRC32 module to generate a new
//! signature.
//!
//! This function first reverses the bits in each byte of the data and then
//! generates the new signature from the current signature and new translated
//! data. Bit 0 is treated as the MSB.
//!
//! \param dataIn is the data to be added, through the CRC32 module, to the
//!        signature.
//! \param crcMode selects the mode of operation for the CRC32
//!        Valid values are:
//!        - \b CRC32_MODE - 32 Bit Mode
//!        - \b CRC16_MODE - 16 Bit Mode
//!
//! \return None
//
//*****************************************************************************
extern void CRC32_set16BitDataReversed(uint16_t dataIn,
                                       uint8_t crcMode);

//*****************************************************************************
//
//! \brief Translates the data by reversing the bits in each 32 bit data and
//! then sets this data to add into the CRC32 module to generate a new
//! signature.
//!
//! This function first reverses the bits in each byte of the data and then
//! generates the new signature from the current signature and new translated
//! data. Bit 0 is treated as the MSB.
//!
//! \param dataIn is the data to be added, through the CRC32 module, to the
//!        signature.
//!
//! \return None
//
//*****************************************************************************
extern void CRC32_set32BitDataReversed(uint32_t dataIn);

//*****************************************************************************
//
//! \brief Returns the value of the signature result.
//!
//! This function returns the value of the signature result generated by the
//! CRC32. Bit 0 is treated as LSB.
//!
//! \param crcMode selects the mode of operation for the CRC32
//!        Valid values are:
//!        - \b CRC32_MODE - 32 Bit Mode
//!        - \b CRC16_MODE - 16 Bit Mode
//!
//! \return The signature result
//
//*****************************************************************************
extern uint32_t CRC32_getResult(uint8_t crcMode);

//*****************************************************************************
//
//! \brief Returns the bit-wise reversed format of the 32 bit signature result.
//!
//! This function returns the bit-wise reversed format of the signature result.
//! Bit 0 is treated as MSB.
//!
//! \param crcMode selects the mode of operation for the CRC32
//!        Valid values are:
//!        - \b CRC32_MODE - 32 Bit Mode
//!        - \b CRC16_MODE - 16 Bit Mode
//!
//! \return The bit-wise reversed format of the signature result
//
//*****************************************************************************
extern uint32_t CRC32_getResultReversed(uint8_t crcMode);

//*****************************************************************************
//
// Mark the end of the C bindings section for C++ compilers.
//
//*****************************************************************************
#ifdef __cplusplus
}
#endif

#endif
#endif // __MSP430WARE_CRC32_H__
