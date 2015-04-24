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
// mpu.h - Driver for the MPU Module.
//
//*****************************************************************************

#ifndef __MSP430WARE_MPU_H__
#define __MSP430WARE_MPU_H__

#include "inc/hw_memmap.h"

#ifdef __MSP430_HAS_MPU__

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
//! \brief Used in the MPU_initThreeSegments() function as the param parameter.
//
//*****************************************************************************
typedef struct MPU_initThreeSegmentsParam
{
    //! Valid values can be found in the Family User's Guide
    uint16_t seg1boundary;
    //! Valid values can be found in the Family User's Guide
    uint16_t seg2boundary;
    //! Is the bit mask of access right for memory segment 1.
    //! \n Logical OR of any of the following:
    //! - \b MPU_READ
    //! - \b MPU_WRITE
    //! - \b MPU_EXEC
    //! - \b MPU_NO_READ_WRITE_EXEC
    uint8_t seg1accmask;
    //! Is the bit mask of access right for memory segment 2.
    //! \n Logical OR of any of the following:
    //! - \b MPU_READ
    //! - \b MPU_WRITE
    //! - \b MPU_EXEC
    //! - \b MPU_NO_READ_WRITE_EXEC
    uint8_t seg2accmask;
    //! Is the bit mask of access right for memory segment 3.
    //! \n Logical OR of any of the following:
    //! - \b MPU_READ
    //! - \b MPU_WRITE
    //! - \b MPU_EXEC
    //! - \b MPU_NO_READ_WRITE_EXEC
    uint8_t seg3accmask;
} MPU_initThreeSegmentsParam;

//*****************************************************************************
//
// The following are values that can be passed to the accmask parameter for
// functions: MPU_initInfoSegment(); the seg2accmask parameter for functions:
// MPU_initTwoSegments(); the seg1accmask parameter for functions:
// MPU_initTwoSegments(); the param parameter for functions:
// MPU_initThreeSegments(), MPU_initThreeSegments(), and
// MPU_initThreeSegments().
//
//*****************************************************************************
#define MPU_READ                                                      MPUSEG1RE
#define MPU_WRITE                                                     MPUSEG1WE
#define MPU_EXEC                                                      MPUSEG1XE
#define MPU_NO_READ_WRITE_EXEC                                         (0x0000)

//*****************************************************************************
//
// The following are values that can be passed to the segment parameter for
// functions: MPU_enablePUCOnViolation(), and MPU_disablePUCOnViolation().
//
//*****************************************************************************
#define MPU_FIRST_SEG                                                 MPUSEG1VS
#define MPU_SECOND_SEG                                                MPUSEG2VS
#define MPU_THIRD_SEG                                                 MPUSEG3VS
#define MPU_INFO_SEG                                                  MPUSEGIVS

//*****************************************************************************
//
// The following are values that can be passed to the memAccFlag parameter for
// functions: MPU_getInterruptStatus(), and MPU_clearInterrupt() as well as
// returned by the MPU_getInterruptStatus() function, the
// MPU_clearAllInterrupts() function and the MPU_clearInterrupt() function.
//
//*****************************************************************************
#define MPU_SEG_1_ACCESS_VIOLATION                                   MPUSEG1IFG
#define MPU_SEG_2_ACCESS_VIOLATION                                   MPUSEG2IFG
#define MPU_SEG_3_ACCESS_VIOLATION                                   MPUSEG3IFG
#define MPU_SEG_INFO_ACCESS_VIOLATION                                MPUSEGIIFG

//*****************************************************************************
//
// Prototypes for the APIs.
//
//*****************************************************************************

//*****************************************************************************
//
//! \brief Initializes MPU with two memory segments
//!
//! This function creates two memory segments in FRAM allowing the user to set
//! access right to each segment. To set the correct value for seg1boundary,
//! the user must consult the Device Family User's Guide and provide the MPUSBx
//! value corresponding to the memory address where the user wants to create
//! the partition. Consult the "Segment Border Setting" section in the User's
//! Guide to find the options available for MPUSBx.
//!
//! \param baseAddress is the base address of the MPU module.
//! \param seg1boundary Valid values can be found in the Family User's Guide
//! \param seg1accmask is the bit mask of access right for memory segment 1.
//!        Mask value is the logical OR of any of the following:
//!        - \b MPU_READ - Read rights
//!        - \b MPU_WRITE - Write rights
//!        - \b MPU_EXEC - Execute rights
//!        - \b MPU_NO_READ_WRITE_EXEC - no read/write/execute rights
//! \param seg2accmask is the bit mask of access right for memory segment 2
//!        Mask value is the logical OR of any of the following:
//!        - \b MPU_READ - Read rights
//!        - \b MPU_WRITE - Write rights
//!        - \b MPU_EXEC - Execute rights
//!        - \b MPU_NO_READ_WRITE_EXEC - no read/write/execute rights
//!
//! Modified bits of \b MPUSAM register, bits of \b MPUSEG register and bits of
//! \b MPUCTL0 register.
//!
//! \return None
//
//*****************************************************************************
extern void MPU_initTwoSegments(uint16_t baseAddress,
                                uint16_t seg1boundary,
                                uint8_t seg1accmask,
                                uint8_t seg2accmask);

//*****************************************************************************
//
//! \brief Initializes MPU with three memory segments
//!
//! This function creates three memory segments in FRAM allowing the user to
//! set access right to each segment. To set the correct value for
//! seg1boundary, the user must consult the Device Family User's Guide and
//! provide the MPUSBx value corresponding to the memory address where the user
//! wants to create the partition. Consult the "Segment Border Setting" section
//! in the User's Guide to find the options available for MPUSBx.
//!
//! \param baseAddress is the base address of the MPU module.
//! \param param is the pointer to struct for initializing three segments.
//!
//! Modified bits of \b MPUSAM register, bits of \b MPUSEG register and bits of
//! \b MPUCTL0 register.
//!
//! \return None
//
//*****************************************************************************
extern void MPU_initThreeSegments(uint16_t baseAddress,
                                  MPU_initThreeSegmentsParam *param);

//*****************************************************************************
//
//! \brief Initializes user information memory segment
//!
//! This function initializes user information memory segment with specified
//! access rights.
//!
//! \param baseAddress is the base address of the MPU module.
//! \param accmask is the bit mask of access right for user information memory
//!        segment.
//!        Mask value is the logical OR of any of the following:
//!        - \b MPU_READ - Read rights
//!        - \b MPU_WRITE - Write rights
//!        - \b MPU_EXEC - Execute rights
//!        - \b MPU_NO_READ_WRITE_EXEC - no read/write/execute rights
//!
//! Modified bits of \b MPUSAM register and bits of \b MPUCTL0 register.
//!
//! \return None
//
//*****************************************************************************
extern void MPU_initInfoSegment(uint16_t baseAddress,
                                uint8_t accmask);

//*****************************************************************************
//
//! \brief The following function enables the NMI Event if a Segment violation
//! has occurred.
//!
//! \param baseAddress is the base address of the MPU module.
//!
//! Modified bits of \b MPUCTL0 register.
//!
//! \return None
//
//*****************************************************************************
extern void MPU_enableNMIevent(uint16_t baseAddress);

//*****************************************************************************
//
//! \brief The following function enables the MPU module in the device.
//!
//! This function needs to be called once all memory segmentation has been
//! done. If this function is not called the MPU module will not be activated.
//!
//! \param baseAddress is the base address of the MPU module.
//!
//! Modified bits of \b MPUCTL0 register.
//!
//! \return None
//
//*****************************************************************************
extern void MPU_start(uint16_t baseAddress);

//*****************************************************************************
//
//! \brief The following function enables PUC generation when an access
//! violation has occurred on the memory segment selected by the user.
//!
//! Note that only specified segments for PUC generation are enabled. Other
//! segments for PUC generation are left untouched. Users may call
//! MPU_enablePUCOnViolation() and MPU_disablePUCOnViolation() to assure that
//! all the bits will be set and/or cleared.
//!
//! \param baseAddress is the base address of the MPU module.
//! \param segment is the bit mask of memory segment that will generate a PUC
//!        when an access violation occurs.
//!        Mask value is the logical OR of any of the following:
//!        - \b MPU_FIRST_SEG - PUC generation on first memory segment
//!        - \b MPU_SECOND_SEG - PUC generation on second memory segment
//!        - \b MPU_THIRD_SEG - PUC generation on third memory segment
//!        - \b MPU_INFO_SEG - PUC generation on user information memory
//!           segment
//!
//! Modified bits of \b MPUSAM register and bits of \b MPUCTL0 register.
//!
//! \return None
//
//*****************************************************************************
extern void MPU_enablePUCOnViolation(uint16_t baseAddress,
                                     uint16_t segment);

//*****************************************************************************
//
//! \brief The following function disables PUC generation when an access
//! violation has occurred on the memory segment selected by the user.
//!
//! Note that only specified segments for PUC generation are disabled. Other
//! segments for PUC generation are left untouched. Users may call
//! MPU_enablePUCOnViolation() and MPU_disablePUCOnViolation() to assure that
//! all the bits will be set and/or cleared.
//!
//! \param baseAddress is the base address of the MPU module.
//! \param segment is the bit mask of memory segment that will NOT generate a
//!        PUC when an access violation occurs.
//!        Mask value is the logical OR of any of the following:
//!        - \b MPU_FIRST_SEG - PUC generation on first memory segment
//!        - \b MPU_SECOND_SEG - PUC generation on second memory segment
//!        - \b MPU_THIRD_SEG - PUC generation on third memory segment
//!        - \b MPU_INFO_SEG - PUC generation on user information memory
//!           segment
//!
//! Modified bits of \b MPUSAM register and bits of \b MPUCTL0 register.
//!
//! \return None
//
//*****************************************************************************
extern void MPU_disablePUCOnViolation(uint16_t baseAddress,
                                      uint16_t segment);

//*****************************************************************************
//
//! \brief Returns the memory segment violation flag status requested by the
//! user.
//!
//! \param baseAddress is the base address of the MPU module.
//! \param memAccFlag is the is the memory access violation flag.
//!        Mask value is the logical OR of any of the following:
//!        - \b MPU_SEG_1_ACCESS_VIOLATION - is set if an access violation in
//!           Main Memory Segment 1 is detected
//!        - \b MPU_SEG_2_ACCESS_VIOLATION - is set if an access violation in
//!           Main Memory Segment 2 is detected
//!        - \b MPU_SEG_3_ACCESS_VIOLATION - is set if an access violation in
//!           Main Memory Segment 3 is detected
//!        - \b MPU_SEG_INFO_ACCESS_VIOLATION - is set if an access violation
//!           in User Information Memory Segment is detected
//!
//! \return Logical OR of any of the following:
//!         - \b MPU_SEG_1_ACCESS_VIOLATION is set if an access violation in
//!         Main Memory Segment 1 is detected
//!         - \b MPU_SEG_2_ACCESS_VIOLATION is set if an access violation in
//!         Main Memory Segment 2 is detected
//!         - \b MPU_SEG_3_ACCESS_VIOLATION is set if an access violation in
//!         Main Memory Segment 3 is detected
//!         - \b MPU_SEG_INFO_ACCESS_VIOLATION is set if an access violation in
//!         User Information Memory Segment is detected
//!         \n indicating the status of the masked flags.
//
//*****************************************************************************
extern uint16_t MPU_getInterruptStatus(uint16_t baseAddress,
                                       uint16_t memAccFlag);

//*****************************************************************************
//
//! \brief Clears the masked interrupt flags
//!
//! Returns the memory segment violation flag status requested by the user or
//! if user is providing a bit mask value, the function will return a value
//! indicating if all flags were cleared.
//!
//! \param baseAddress is the base address of the MPU module.
//! \param memAccFlag is the is the memory access violation flag.
//!        Mask value is the logical OR of any of the following:
//!        - \b MPU_SEG_1_ACCESS_VIOLATION - is set if an access violation in
//!           Main Memory Segment 1 is detected
//!        - \b MPU_SEG_2_ACCESS_VIOLATION - is set if an access violation in
//!           Main Memory Segment 2 is detected
//!        - \b MPU_SEG_3_ACCESS_VIOLATION - is set if an access violation in
//!           Main Memory Segment 3 is detected
//!        - \b MPU_SEG_INFO_ACCESS_VIOLATION - is set if an access violation
//!           in User Information Memory Segment is detected
//!
//! \return Logical OR of any of the following:
//!         - \b MPU_SEG_1_ACCESS_VIOLATION is set if an access violation in
//!         Main Memory Segment 1 is detected
//!         - \b MPU_SEG_2_ACCESS_VIOLATION is set if an access violation in
//!         Main Memory Segment 2 is detected
//!         - \b MPU_SEG_3_ACCESS_VIOLATION is set if an access violation in
//!         Main Memory Segment 3 is detected
//!         - \b MPU_SEG_INFO_ACCESS_VIOLATION is set if an access violation in
//!         User Information Memory Segment is detected
//!         \n indicating the status of the masked flags.
//
//*****************************************************************************
extern uint16_t MPU_clearInterrupt(uint16_t baseAddress,
                                   uint16_t memAccFlag);

//*****************************************************************************
//
//! \brief Clears all Memory Segment Access Violation Interrupt Flags.
//!
//! \param baseAddress is the base address of the MPU module.
//!
//! Modified bits of \b MPUCTL1 register.
//!
//! \return Logical OR of any of the following:
//!         - \b MPU_SEG_1_ACCESS_VIOLATION is set if an access violation in
//!         Main Memory Segment 1 is detected
//!         - \b MPU_SEG_2_ACCESS_VIOLATION is set if an access violation in
//!         Main Memory Segment 2 is detected
//!         - \b MPU_SEG_3_ACCESS_VIOLATION is set if an access violation in
//!         Main Memory Segment 3 is detected
//!         - \b MPU_SEG_INFO_ACCESS_VIOLATION is set if an access violation in
//!         User Information Memory Segment is detected
//!         \n indicating the status of the interrupt flags.
//
//*****************************************************************************
extern uint16_t MPU_clearAllInterrupts(uint16_t baseAddress);

//*****************************************************************************
//
//! \brief Lock MPU to protect from write access.
//!
//! Sets MPULOCK to protect MPU from write access on all MPU registers except
//! MPUCTL1, MPUIPC0 and MPUIPSEGBx until a BOR occurs. MPULOCK bit cannot be
//! cleared manually. MPU_clearInterrupt() and MPU_clearAllInterrupts() still
//! can be used after this API is called.
//!
//! \param baseAddress is the base address of the MPU module.
//!
//! Modified bits are \b MPULOCK of \b MPUCTL1 register.
//!
//! \return None
//
//*****************************************************************************
extern void MPU_lockMPU(uint16_t baseAddress);

//*****************************************************************************
//
// Mark the end of the C bindings section for C++ compilers.
//
//*****************************************************************************
#ifdef __cplusplus
}
#endif

#endif
#endif // __MSP430WARE_MPU_H__
