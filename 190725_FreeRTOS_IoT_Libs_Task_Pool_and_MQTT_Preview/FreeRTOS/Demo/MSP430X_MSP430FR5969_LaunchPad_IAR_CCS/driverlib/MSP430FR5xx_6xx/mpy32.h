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
// mpy32.h - Driver for the MPY32 Module.
//
//*****************************************************************************

#ifndef __MSP430WARE_MPY32_H__
#define __MSP430WARE_MPY32_H__

#include "inc/hw_memmap.h"

#ifdef __MSP430_HAS_MPY32__

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

#include "inc/hw_regaccess.h"

//*****************************************************************************
//
// The following are values that can be passed to the writeDelaySelect
// parameter for functions: MPY32_setWriteDelay().
//
//*****************************************************************************
#define MPY32_WRITEDELAY_OFF                        (!(MPYDLY32 + MPYDLYWRTEN))
#define MPY32_WRITEDELAY_32BIT                                    (MPYDLYWRTEN)
#define MPY32_WRITEDELAY_64BIT                         (MPYDLY32 + MPYDLYWRTEN)

//*****************************************************************************
//
// The following are values that can be passed to the multiplicationType
// parameter for functions: MPY32_setOperandOne8Bit(),
// MPY32_setOperandOne16Bit(), MPY32_setOperandOne24Bit(), and
// MPY32_setOperandOne32Bit().
//
//*****************************************************************************
#define MPY32_MULTIPLY_UNSIGNED                                          (0x00)
#define MPY32_MULTIPLY_SIGNED                                            (0x02)
#define MPY32_MULTIPLYACCUMULATE_UNSIGNED                                (0x04)
#define MPY32_MULTIPLYACCUMULATE_SIGNED                                  (0x06)

//*****************************************************************************
//
// The following are values that can be passed toThe following are values that
// can be returned by the MPY32_getSaturationMode() function.
//
//*****************************************************************************
#define MPY32_SATURATION_MODE_DISABLED                                     0x00
#define MPY32_SATURATION_MODE_ENABLED                                    MPYSAT

//*****************************************************************************
//
// The following are values that can be passed toThe following are values that
// can be returned by the MPY32_getFractionalMode() function.
//
//*****************************************************************************
#define MPY32_FRACTIONAL_MODE_DISABLED                                     0x00
#define MPY32_FRACTIONAL_MODE_ENABLED                                   MPYFRAC

//*****************************************************************************
//
// Prototypes for the APIs.
//
//*****************************************************************************

//*****************************************************************************
//
//! \brief Sets the write delay setting for the MPY32 module.
//!
//! This function sets up a write delay to the MPY module's registers, which
//! holds any writes to the registers until all calculations are complete.
//! There are two different settings, one which waits for 32-bit results to be
//! ready, and one which waits for 64-bit results to be ready. This prevents
//! unpredicatble results if registers are changed before the results are
//! ready.
//!
//! \param writeDelaySelect delays the write to any MPY32 register until the
//!        selected bit size of result has been written.
//!        Valid values are:
//!        - \b MPY32_WRITEDELAY_OFF [Default] - writes are not delayed
//!        - \b MPY32_WRITEDELAY_32BIT - writes are delayed until a 32-bit
//!           result is available in the result registers
//!        - \b MPY32_WRITEDELAY_64BIT - writes are delayed until a 64-bit
//!           result is available in the result registers
//!        \n Modified bits are \b MPYDLY32 and \b MPYDLYWRTEN of \b MPY32CTL0
//!        register.
//!
//! \return None
//
//*****************************************************************************
extern void MPY32_setWriteDelay(uint16_t writeDelaySelect);

//*****************************************************************************
//
//! \brief Enables Saturation Mode.
//!
//! This function enables saturation mode. When this is enabled, the result
//! read out from the MPY result registers is converted to the most-positive
//! number in the case of an overflow, or the most-negative number in the case
//! of an underflow. Please note, that the raw value in the registers does not
//! reflect the result returned, and if the saturation mode is disabled, then
//! the raw value of the registers will be returned instead.
//!
//!
//! \return None
//
//*****************************************************************************
extern void MPY32_enableSaturationMode(void);

//*****************************************************************************
//
//! \brief Disables Saturation Mode.
//!
//! This function disables saturation mode, which allows the raw result of the
//! MPY result registers to be returned.
//!
//!
//! \return None
//
//*****************************************************************************
extern void MPY32_disableSaturationMode(void);

//*****************************************************************************
//
//! \brief Gets the Saturation Mode.
//!
//! This function gets the current saturation mode.
//!
//!
//! \return Gets the Saturation Mode
//!         Return one of the following:
//!         - \b MPY32_SATURATION_MODE_DISABLED
//!         - \b MPY32_SATURATION_MODE_ENABLED
//!         \n Gets the Saturation Mode
//
//*****************************************************************************
extern uint8_t MPY32_getSaturationMode(void);

//*****************************************************************************
//
//! \brief Enables Fraction Mode.
//!
//! This function enables fraction mode.
//!
//!
//! \return None
//
//*****************************************************************************
extern void MPY32_enableFractionalMode(void);

//*****************************************************************************
//
//! \brief Disables Fraction Mode.
//!
//! This function disables fraction mode.
//!
//!
//! \return None
//
//*****************************************************************************
extern void MPY32_disableFractionalMode(void);

//*****************************************************************************
//
//! \brief Gets the Fractional Mode.
//!
//! This function gets the current fractional mode.
//!
//!
//! \return Gets the fractional mode
//!         Return one of the following:
//!         - \b MPY32_FRACTIONAL_MODE_DISABLED
//!         - \b MPY32_FRACTIONAL_MODE_ENABLED
//!         \n Gets the Fractional Mode
//
//*****************************************************************************
extern uint8_t MPY32_getFractionalMode(void);

//*****************************************************************************
//
//! \brief Sets an 8-bit value into operand 1.
//!
//! This function sets the first operand for multiplication and determines what
//! type of operation should be performed. Once the second operand is set, then
//! the operation will begin.
//!
//! \param multiplicationType is the type of multiplication to perform once the
//!        second operand is set.
//!        Valid values are:
//!        - \b MPY32_MULTIPLY_UNSIGNED
//!        - \b MPY32_MULTIPLY_SIGNED
//!        - \b MPY32_MULTIPLYACCUMULATE_UNSIGNED
//!        - \b MPY32_MULTIPLYACCUMULATE_SIGNED
//! \param operand is the 8-bit value to load into the 1st operand.
//!
//! \return None
//
//*****************************************************************************
extern void MPY32_setOperandOne8Bit(uint8_t multiplicationType,
                                    uint8_t operand);

//*****************************************************************************
//
//! \brief Sets an 16-bit value into operand 1.
//!
//! This function sets the first operand for multiplication and determines what
//! type of operation should be performed. Once the second operand is set, then
//! the operation will begin.
//!
//! \param multiplicationType is the type of multiplication to perform once the
//!        second operand is set.
//!        Valid values are:
//!        - \b MPY32_MULTIPLY_UNSIGNED
//!        - \b MPY32_MULTIPLY_SIGNED
//!        - \b MPY32_MULTIPLYACCUMULATE_UNSIGNED
//!        - \b MPY32_MULTIPLYACCUMULATE_SIGNED
//! \param operand is the 16-bit value to load into the 1st operand.
//!
//! \return None
//
//*****************************************************************************
extern void MPY32_setOperandOne16Bit(uint8_t multiplicationType,
                                     uint16_t operand);

//*****************************************************************************
//
//! \brief Sets an 24-bit value into operand 1.
//!
//! This function sets the first operand for multiplication and determines what
//! type of operation should be performed. Once the second operand is set, then
//! the operation will begin.
//!
//! \param multiplicationType is the type of multiplication to perform once the
//!        second operand is set.
//!        Valid values are:
//!        - \b MPY32_MULTIPLY_UNSIGNED
//!        - \b MPY32_MULTIPLY_SIGNED
//!        - \b MPY32_MULTIPLYACCUMULATE_UNSIGNED
//!        - \b MPY32_MULTIPLYACCUMULATE_SIGNED
//! \param operand is the 24-bit value to load into the 1st operand.
//!
//! \return None
//
//*****************************************************************************
extern void MPY32_setOperandOne24Bit(uint8_t multiplicationType,
                                     uint32_t operand);

//*****************************************************************************
//
//! \brief Sets an 32-bit value into operand 1.
//!
//! This function sets the first operand for multiplication and determines what
//! type of operation should be performed. Once the second operand is set, then
//! the operation will begin.
//!
//! \param multiplicationType is the type of multiplication to perform once the
//!        second operand is set.
//!        Valid values are:
//!        - \b MPY32_MULTIPLY_UNSIGNED
//!        - \b MPY32_MULTIPLY_SIGNED
//!        - \b MPY32_MULTIPLYACCUMULATE_UNSIGNED
//!        - \b MPY32_MULTIPLYACCUMULATE_SIGNED
//! \param operand is the 32-bit value to load into the 1st operand.
//!
//! \return None
//
//*****************************************************************************
extern void MPY32_setOperandOne32Bit(uint8_t multiplicationType,
                                     uint32_t operand);

//*****************************************************************************
//
//! \brief Sets an 8-bit value into operand 2, which starts the multiplication.
//!
//! This function sets the second operand of the multiplication operation and
//! starts the operation.
//!
//! \param operand is the 8-bit value to load into the 2nd operand.
//!
//! \return None
//
//*****************************************************************************
extern void MPY32_setOperandTwo8Bit(uint8_t operand);

//*****************************************************************************
//
//! \brief Sets an 16-bit value into operand 2, which starts the
//! multiplication.
//!
//! This function sets the second operand of the multiplication operation and
//! starts the operation.
//!
//! \param operand is the 16-bit value to load into the 2nd operand.
//!
//! \return None
//
//*****************************************************************************
extern void MPY32_setOperandTwo16Bit(uint16_t operand);

//*****************************************************************************
//
//! \brief Sets an 24-bit value into operand 2, which starts the
//! multiplication.
//!
//! This function sets the second operand of the multiplication operation and
//! starts the operation.
//!
//! \param operand is the 24-bit value to load into the 2nd operand.
//!
//! \return None
//
//*****************************************************************************
extern void MPY32_setOperandTwo24Bit(uint32_t operand);

//*****************************************************************************
//
//! \brief Sets an 32-bit value into operand 2, which starts the
//! multiplication.
//!
//! This function sets the second operand of the multiplication operation and
//! starts the operation.
//!
//! \param operand is the 32-bit value to load into the 2nd operand.
//!
//! \return None
//
//*****************************************************************************
extern void MPY32_setOperandTwo32Bit(uint32_t operand);

//*****************************************************************************
//
//! \brief Returns an 64-bit result of the last multiplication operation.
//!
//! This function returns all 64 bits of the result registers
//!
//!
//! \return The 64-bit result is returned as a uint64_t type
//
//*****************************************************************************
extern uint64_t MPY32_getResult(void);

//*****************************************************************************
//
//! \brief Returns the Sum Extension of the last multiplication operation.
//!
//! This function returns the Sum Extension of the MPY module, which either
//! gives the sign after a signed operation or shows a carry after a multiply-
//! and-accumulate operation. The Sum Extension acts as a check for overflows
//! or underflows.
//!
//!
//! \return The value of the MPY32 module Sum Extension.
//
//*****************************************************************************
extern uint16_t MPY32_getSumExtension(void);

//*****************************************************************************
//
//! \brief Returns the Carry Bit of the last multiplication operation.
//!
//! This function returns the Carry Bit of the MPY module, which either gives
//! the sign after a signed operation or shows a carry after a multiply- and-
//! accumulate operation.
//!
//!
//! \return The value of the MPY32 module Carry Bit 0x0 or 0x1.
//
//*****************************************************************************
extern uint16_t MPY32_getCarryBitValue(void);

//*****************************************************************************
//
//! \brief Clears the Carry Bit of the last multiplication operation.
//!
//! This function clears the Carry Bit of the MPY module
//!
//!
//! \return The value of the MPY32 module Carry Bit 0x0 or 0x1.
//
//*****************************************************************************
extern void MPY32_clearCarryBitValue(void);

//*****************************************************************************
//
//! \brief Preloads the result register
//!
//! This function Preloads the result register
//!
//! \param result value to preload the result register to
//!
//! \return None
//
//*****************************************************************************
extern void MPY32_preloadResult(uint64_t result);

//*****************************************************************************
//
// Mark the end of the C bindings section for C++ compilers.
//
//*****************************************************************************
#ifdef __cplusplus
}
#endif

#endif
#endif // __MSP430WARE_MPY32_H__
