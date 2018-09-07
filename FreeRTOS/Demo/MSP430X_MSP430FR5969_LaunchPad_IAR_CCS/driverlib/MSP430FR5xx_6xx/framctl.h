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
// framctl.h - Driver for the FRAMCTL Module.
//
//*****************************************************************************

#ifndef __MSP430WARE_FRAMCTL_H__
#define __MSP430WARE_FRAMCTL_H__

#include "inc/hw_memmap.h"

#ifdef __MSP430_HAS_FRAM__

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
// The following are values that can be passed to the interruptMask parameter
// for functions: FRAMCtl_enableInterrupt(), and FRAMCtl_disableInterrupt().
//
//*****************************************************************************
#define FRAMCTL_PUC_ON_UNCORRECTABLE_BIT                               UBDRSTEN
#define FRAMCTL_UNCORRECTABLE_BIT_INTERRUPT                               UBDIE
#define FRAMCTL_CORRECTABLE_BIT_INTERRUPT                                 CBDIE

//*****************************************************************************
//
// The following are values that can be passed to the interruptFlagMask
// parameter for functions: FRAMCtl_getInterruptStatus() as well as returned by
// the FRAMCtl_getInterruptStatus() function.
//
//*****************************************************************************
#define FRAMCTL_ACCESS_TIME_ERROR_FLAG                                 ACCTEIFG
#define FRAMCTL_UNCORRECTABLE_BIT_FLAG                                   UBDIFG
#define FRAMCTL_CORRECTABLE_BIT_FLAG                                     CBDIFG

//*****************************************************************************
//
// The following are values that can be passed to the waitState parameter for
// functions: FRAMCtl_configureWaitStateControl().
//
//*****************************************************************************
#define FRAMCTL_ACCESS_TIME_CYCLES_0                                   NWAITS_0
#define FRAMCTL_ACCESS_TIME_CYCLES_1                                   NWAITS_1
#define FRAMCTL_ACCESS_TIME_CYCLES_2                                   NWAITS_2
#define FRAMCTL_ACCESS_TIME_CYCLES_3                                   NWAITS_3
#define FRAMCTL_ACCESS_TIME_CYCLES_4                                   NWAITS_4
#define FRAMCTL_ACCESS_TIME_CYCLES_5                                   NWAITS_5
#define FRAMCTL_ACCESS_TIME_CYCLES_6                                   NWAITS_6
#define FRAMCTL_ACCESS_TIME_CYCLES_7                                   NWAITS_7

//*****************************************************************************
//
// The following are values that can be passed to the delayStatus parameter for
// functions: FRAMCtl_delayPowerUpFromLPM().
//
//*****************************************************************************
#define FRAMCTL_DELAY_FROM_LPM_ENABLE                                      0x00
#define FRAMCTL_DELAY_FROM_LPM_DISABLE                                     0x02

//*****************************************************************************
//
// Prototypes for the APIs.
//
//*****************************************************************************

//*****************************************************************************
//
//! \brief Write data into the fram memory in byte format.
//!
//! \param dataPtr is the pointer to the data to be written
//! \param framPtr is the pointer into which to write the data
//! \param numberOfBytes is the number of bytes to be written
//!
//! \return None
//
//*****************************************************************************
extern void FRAMCtl_write8(uint8_t *dataPtr,
                           uint8_t *framPtr,
                           uint16_t numberOfBytes);

//*****************************************************************************
//
//! \brief Write data into the fram memory in word format.
//!
//! \param dataPtr is the pointer to the data to be written
//! \param framPtr is the pointer into which to write the data
//! \param numberOfWords is the number of words to be written
//!
//! \return None
//
//*****************************************************************************
extern void FRAMCtl_write16(uint16_t *dataPtr,
                            uint16_t *framPtr,
                            uint16_t numberOfWords);

//*****************************************************************************
//
//! \brief Write data into the fram memory in long format, pass by reference
//!
//! \param dataPtr is the pointer to the data to be written
//! \param framPtr is the pointer into which to write the data
//! \param count is the number of 32 bit words to be written
//!
//! \return None
//
//*****************************************************************************
extern void FRAMCtl_write32(uint32_t *dataPtr,
                            uint32_t *framPtr,
                            uint16_t count);

//*****************************************************************************
//
//! \brief Write data into the fram memory in long format, pass by value
//!
//! \param value is the value to written to FRAMCTL memory
//! \param framPtr is the pointer into which to write the data
//! \param count is the number of 32 bit addresses to fill
//!
//! \return None
//
//*****************************************************************************
extern void FRAMCtl_fillMemory32(uint32_t value,
                                 uint32_t *framPtr,
                                 uint16_t count);

//*****************************************************************************
//
//! \brief Enables selected FRAMCtl interrupt sources.
//!
//! Enables the indicated FRAMCtl interrupt sources.  Only the sources that are
//! enabled can be reflected to the processor interrupt; disabled sources have
//! no effect on the processor. Does not clear interrupt flags.
//!
//! \param interruptMask is the bit mask of the memory buffer interrupt sources
//!        to be disabled.
//!        Mask value is the logical OR of any of the following:
//!        - \b FRAMCTL_PUC_ON_UNCORRECTABLE_BIT - Enable PUC reset if FRAMCtl
//!           uncorrectable bit error detected.
//!        - \b FRAMCTL_UNCORRECTABLE_BIT_INTERRUPT - Interrupts when an
//!           uncorrectable bit error is detected.
//!        - \b FRAMCTL_CORRECTABLE_BIT_INTERRUPT - Interrupts when a
//!           correctable bit error is detected.
//!
//! Modified bits of \b GCCTL0 register and bits of \b FRCTL0 register.
//!
//! \return None
//
//*****************************************************************************
extern void FRAMCtl_enableInterrupt(uint8_t interruptMask);

//*****************************************************************************
//
//! \brief Returns the status of the selected FRAMCtl interrupt flags.
//!
//! \param interruptFlagMask is a bit mask of the interrupt flags status to be
//!        returned.
//!        Mask value is the logical OR of any of the following:
//!        - \b FRAMCTL_ACCESS_TIME_ERROR_FLAG - Interrupt flag is set if a
//!           wrong setting for NPRECHG and NACCESS is set and FRAMCtl access
//!           time is not hold.
//!        - \b FRAMCTL_UNCORRECTABLE_BIT_FLAG - Interrupt flag is set if an
//!           uncorrectable bit error has been detected in the FRAMCtl memory
//!           error detection logic.
//!        - \b FRAMCTL_CORRECTABLE_BIT_FLAG - Interrupt flag is set if a
//!           correctable bit error has been detected and corrected in the
//!           FRAMCtl memory error detection logic.
//!
//! \return Logical OR of any of the following:
//!         - \b FRAMCtl_ACCESS_TIME_ERROR_FLAG Interrupt flag is set if a
//!         wrong setting for NPRECHG and NACCESS is set and FRAMCtl access
//!         time is not hold.
//!         - \b FRAMCtl_UNCORRECTABLE_BIT_FLAG Interrupt flag is set if an
//!         uncorrectable bit error has been detected in the FRAMCtl memory
//!         error detection logic.
//!         - \b FRAMCtl_CORRECTABLE_BIT_FLAG Interrupt flag is set if a
//!         correctable bit error has been detected and corrected in the
//!         FRAMCtl memory error detection logic.
//!         \n indicating the status of the masked flags
//
//*****************************************************************************
extern uint8_t FRAMCtl_getInterruptStatus(uint16_t interruptFlagMask);

//*****************************************************************************
//
//! \brief Disables selected FRAMCtl interrupt sources.
//!
//! Disables the indicated FRAMCtl interrupt sources.  Only the sources that
//! are enabled can be reflected to the processor interrupt; disabled sources
//! have no effect on the processor.
//!
//! \param interruptMask is the bit mask of the memory buffer interrupt sources
//!        to be disabled.
//!        Mask value is the logical OR of any of the following:
//!        - \b FRAMCTL_PUC_ON_UNCORRECTABLE_BIT - Enable PUC reset if FRAMCtl
//!           uncorrectable bit error detected.
//!        - \b FRAMCTL_UNCORRECTABLE_BIT_INTERRUPT - Interrupts when an
//!           uncorrectable bit error is detected.
//!        - \b FRAMCTL_CORRECTABLE_BIT_INTERRUPT - Interrupts when a
//!           correctable bit error is detected.
//!
//! \return None
//
//*****************************************************************************
extern void FRAMCtl_disableInterrupt(uint16_t interruptMask);

//*****************************************************************************
//
//! \brief Configures the access time of the FRAMCtl module
//!
//! Configures the access time of the FRAMCtl module.
//!
//! \param waitState defines the number of CPU cycles required for access time
//!        defined in the datasheet
//!        Valid values are:
//!        - \b FRAMCTL_ACCESS_TIME_CYCLES_0
//!        - \b FRAMCTL_ACCESS_TIME_CYCLES_1
//!        - \b FRAMCTL_ACCESS_TIME_CYCLES_2
//!        - \b FRAMCTL_ACCESS_TIME_CYCLES_3
//!        - \b FRAMCTL_ACCESS_TIME_CYCLES_4
//!        - \b FRAMCTL_ACCESS_TIME_CYCLES_5
//!        - \b FRAMCTL_ACCESS_TIME_CYCLES_6
//!        - \b FRAMCTL_ACCESS_TIME_CYCLES_7
//!
//! Modified bits are \b NWAITS of \b GCCTL0 register.
//!
//! \return None
//
//*****************************************************************************
extern void FRAMCtl_configureWaitStateControl(uint8_t waitState);

//*****************************************************************************
//
//! \brief Configures when the FRAMCtl module will power up after LPM exit
//!
//! Configures when the FRAMCtl module will power up after LPM exit. The module
//! can either wait until the first FRAMCtl access to power up or power up
//! immediately after leaving LPM. If FRAMCtl power is disabled, a memory
//! access will automatically insert wait states to ensure sufficient timing
//! for the FRAMCtl power-up and access.
//!
//! \param delayStatus chooses if FRAMCTL should power up instantly with LPM
//!        exit or to wait until first FRAMCTL access after LPM exit
//!        Valid values are:
//!        - \b FRAMCTL_DELAY_FROM_LPM_ENABLE
//!        - \b FRAMCTL_DELAY_FROM_LPM_DISABLE
//!
//! \return None
//
//*****************************************************************************
extern void FRAMCtl_delayPowerUpFromLPM(uint8_t delayStatus);

//*****************************************************************************
//
// Mark the end of the C bindings section for C++ compilers.
//
//*****************************************************************************
#ifdef __cplusplus
}
#endif

#endif
#endif // __MSP430WARE_FRAMCTL_H__
