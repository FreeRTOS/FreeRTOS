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
// ram.h - Driver for the RAM Module.
//
//*****************************************************************************

#ifndef __MSP430WARE_RAM_H__
#define __MSP430WARE_RAM_H__

#include "inc/hw_memmap.h"

#ifdef __MSP430_HAS_RC_FRAM__

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
// The following are values that can be passed to the sector parameter for
// functions: RAM_setSectorOff(), and RAM_getSectorState().
//
//*****************************************************************************
#define RAM_SECTOR0                                                      (0x00)
#define RAM_SECTOR1                                                      (0x01)
#define RAM_SECTOR2                                                      (0x02)
#define RAM_SECTOR3                                                      (0x03)

//*****************************************************************************
//
// The following are values that can be passed to the mode parameter for
// functions: RAM_setSectorOff() as well as returned by the
// RAM_getSectorState() function.
//
//*****************************************************************************
#define RAM_RETENTION_MODE                                               (0x00)
#define RAM_OFF_WAKEUP_MODE                                         (RCRS0OFF0)
#define RAM_OFF_NON_WAKEUP_MODE                                     (RCRS0OFF1)

//*****************************************************************************
//
// Prototypes for the APIs.
//
//*****************************************************************************

//*****************************************************************************
//
//! \brief Set specified RAM sector off
//!
//! \param sector is specified sector to be set off.
//!        Valid values are:
//!        - \b RAM_SECTOR0
//!        - \b RAM_SECTOR1
//!        - \b RAM_SECTOR2
//!        - \b RAM_SECTOR3
//! \param mode is sector off mode
//!        Valid values are:
//!        - \b RAM_RETENTION_MODE
//!        - \b RAM_OFF_WAKEUP_MODE
//!        - \b RAM_OFF_NON_WAKEUP_MODE
//!
//! Modified bits of \b RCCTL0 register.
//!
//! \return None
//
//*****************************************************************************
extern void RAM_setSectorOff(uint8_t sector,
                             uint8_t mode);

//*****************************************************************************
//
//! \brief Get RAM sector ON/OFF status
//!
//! \param sector is specified sector
//!        Valid values are:
//!        - \b RAM_SECTOR0
//!        - \b RAM_SECTOR1
//!        - \b RAM_SECTOR2
//!        - \b RAM_SECTOR3
//!
//! \return One of the following:
//!         - \b RAM_RETENTION_MODE
//!         - \b RAM_OFF_WAKEUP_MODE
//!         - \b RAM_OFF_NON_WAKEUP_MODE
//!         \n indicating the status of the masked sectors
//
//*****************************************************************************
extern uint8_t RAM_getSectorState(uint8_t sector);

//*****************************************************************************
//
// Mark the end of the C bindings section for C++ compilers.
//
//*****************************************************************************
#ifdef __cplusplus
}
#endif

#endif
#endif // __MSP430WARE_RAM_H__
