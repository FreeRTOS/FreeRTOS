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
// wdt_a.c - Driver for the wdt_a Module.
//
//*****************************************************************************

//*****************************************************************************
//
//! \addtogroup wdt_a_api wdt_a
//! @{
//
//*****************************************************************************

#include "inc/hw_regaccess.h"
#include "inc/hw_memmap.h"

#ifdef __MSP430_HAS_WDT_A__
#include "wdt_a.h"

#include <assert.h>

void WDT_A_hold(uint16_t baseAddress)
{
    // Set Hold bit
    uint8_t newWDTStatus =
        ((HWREG16(baseAddress + OFS_WDTCTL) & 0x00FF) | WDTHOLD);

    HWREG16(baseAddress + OFS_WDTCTL) = WDTPW + newWDTStatus;
}

void WDT_A_start(uint16_t baseAddress)
{
    // Reset Hold bit
    uint8_t newWDTStatus =
        ((HWREG16(baseAddress + OFS_WDTCTL) & 0x00FF) & ~(WDTHOLD));

    HWREG16(baseAddress + OFS_WDTCTL) = WDTPW + newWDTStatus;
}

void WDT_A_resetTimer(uint16_t baseAddress)
{
    // Set Counter Clear bit
    uint8_t newWDTStatus =
        ((HWREG16(baseAddress + OFS_WDTCTL) & 0x00FF) | WDTCNTCL);

    HWREG16(baseAddress + OFS_WDTCTL) = WDTPW + newWDTStatus;
}

void WDT_A_initWatchdogTimer(uint16_t baseAddress,
                             uint8_t clockSelect,
                             uint8_t clockDivider)
{
    HWREG16(baseAddress + OFS_WDTCTL) =
        WDTPW + WDTCNTCL + WDTHOLD + clockSelect + clockDivider;
}

void WDT_A_initIntervalTimer(uint16_t baseAddress,
                             uint8_t clockSelect,
                             uint8_t clockDivider)
{
    HWREG16(baseAddress + OFS_WDTCTL) =
        WDTPW + WDTCNTCL + WDTHOLD + WDTTMSEL + clockSelect + clockDivider;
}

#endif
//*****************************************************************************
//
//! Close the doxygen group for wdt_a_api
//! @}
//
//*****************************************************************************
