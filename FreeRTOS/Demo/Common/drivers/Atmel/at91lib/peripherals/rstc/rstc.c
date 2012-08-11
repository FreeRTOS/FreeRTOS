/* ----------------------------------------------------------------------------
 *         ATMEL Microcontroller Software Support
 * ----------------------------------------------------------------------------
 * Copyright (c) 2008, Atmel Corporation
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * - Redistributions of source code must retain the above copyright notice,
 * this list of conditions and the disclaimer below.
 *
 * Atmel's name may not be used to endorse or promote products derived from
 * this software without specific prior written permission.
 *
 * DISCLAIMER: THIS SOFTWARE IS PROVIDED BY ATMEL "AS IS" AND ANY EXPRESS OR
 * IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NON-INFRINGEMENT ARE
 * DISCLAIMED. IN NO EVENT SHALL ATMEL BE LIABLE FOR ANY DIRECT, INDIRECT,
 * INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA,
 * OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE,
 * EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 * ----------------------------------------------------------------------------
 */

//-----------------------------------------------------------------------------
//         Headers
//-----------------------------------------------------------------------------

#include <board.h>

//-----------------------------------------------------------------------------
//         Macros
//-----------------------------------------------------------------------------

/// WRITE_RSTC: Write RSTC register
#define WRITE_RSTC(pRstc, regName, value) pRstc->regName = (value)

/// READ_RSTC: Read RSTC registers
#define READ_RSTC(pRstc, regName) (pRstc->regName)

//-----------------------------------------------------------------------------
//         Defines
//-----------------------------------------------------------------------------

/// Keywords to write to the reset registers
#define RSTC_KEY_PASSWORD       (0xA5UL << 24)

//-----------------------------------------------------------------------------
//         Exported functions
//-----------------------------------------------------------------------------

//-----------------------------------------------------------------------------
/// Configure the mode of the RSTC peripheral.
/// The configuration is computed by the lib (AT91C_RSTC_*).
/// \param rstc  Pointer to an RSTC peripheral.
/// \param rmr Desired mode configuration.
//-----------------------------------------------------------------------------
void RSTC_ConfigureMode(AT91PS_RSTC rstc, unsigned int rmr)
{
    rmr &= ~AT91C_RSTC_KEY;
    WRITE_RSTC(rstc, RSTC_RMR, rmr | RSTC_KEY_PASSWORD);
}

//-----------------------------------------------------------------------------
/// Enable/Disable the detection of a low level on the pin NRST as User Reset
/// \param rstc   Pointer to an RSTC peripheral.
/// \param enable 1 to enable & 0 to disable.
//-----------------------------------------------------------------------------
void RSTC_SetUserResetEnable(AT91PS_RSTC rstc, unsigned char enable)
{
    unsigned int rmr = READ_RSTC(rstc, RSTC_RMR) & (~AT91C_RSTC_KEY);
    if (enable) {

        rmr |=  AT91C_RSTC_URSTEN;
    }
    else {

        rmr &= ~AT91C_RSTC_URSTEN;
    }
    WRITE_RSTC(rstc, RSTC_RMR, rmr | RSTC_KEY_PASSWORD);
}

//-----------------------------------------------------------------------------
/// Enable/Disable the interrupt of a User Reset (USRTS bit in RSTC_RST).
/// \param rstc   Pointer to an RSTC peripheral.
/// \param enable 1 to enable & 0 to disable.
//-----------------------------------------------------------------------------
void RSTC_SetUserResetInterruptEnable(AT91PS_RSTC rstc, unsigned char enable)
{
    unsigned int rmr = READ_RSTC(rstc, RSTC_RMR) & (~AT91C_RSTC_KEY);
    if (enable) {

        rmr |=  AT91C_RSTC_URSTIEN;
    }
    else {

        rmr &= ~AT91C_RSTC_URSTIEN;
    }
    WRITE_RSTC(rstc, RSTC_RMR, rmr | RSTC_KEY_PASSWORD);
}

//-----------------------------------------------------------------------------
/// Setup the external reset length. The length is asserted during a time of
/// pow(2, powl+1) Slow Clock(32KHz). The duration is between 60us and 2s.
/// \param rstc   Pointer to an RSTC peripheral.
/// \param powl   Power length defined.
//-----------------------------------------------------------------------------
void RSTC_SetExtResetLength(AT91PS_RSTC rstc, unsigned char powl)
{
    unsigned int rmr = READ_RSTC(rstc, RSTC_RMR);
    rmr &= ~(AT91C_RSTC_KEY | AT91C_RSTC_ERSTL);
    rmr |=  (powl << 8) & AT91C_RSTC_ERSTL;
    WRITE_RSTC(rstc, RSTC_RMR, rmr | RSTC_KEY_PASSWORD);
}


//-----------------------------------------------------------------------------
/// Resets the processor.
/// \param rstc  Pointer to an RSTC peripheral.
//-----------------------------------------------------------------------------
void RSTC_ProcessorReset(AT91PS_RSTC rstc)
{
    WRITE_RSTC(rstc, RSTC_RCR, AT91C_RSTC_PROCRST | RSTC_KEY_PASSWORD);
}

//-----------------------------------------------------------------------------
/// Resets the peripherals.
/// \param rstc  Pointer to an RSTC peripheral.
//-----------------------------------------------------------------------------
void RSTC_PeripheralReset(AT91PS_RSTC rstc)
{
    WRITE_RSTC(rstc, RSTC_RCR, AT91C_RSTC_PERRST | RSTC_KEY_PASSWORD);
}

//-----------------------------------------------------------------------------
/// Asserts the NRST pin for external resets.
/// \param rstc  Pointer to an RSTC peripheral.
//-----------------------------------------------------------------------------
void RSTC_ExtReset(AT91PS_RSTC rstc)
{
    WRITE_RSTC(rstc, RSTC_RCR, AT91C_RSTC_EXTRST | RSTC_KEY_PASSWORD);
}

//-----------------------------------------------------------------------------
/// Return NRST pin level ( 1 or 0 ).
/// \param rstc  Pointer to an RSTC peripheral.
//-----------------------------------------------------------------------------
unsigned char RSTC_GetNrstLevel(AT91PS_RSTC rstc)
{
    if (READ_RSTC(rstc, RSTC_RSR) & AT91C_RSTC_NRSTL) {

        return 1;
    }
    return 0;
}

//-----------------------------------------------------------------------------
/// Returns 1 if at least one high-to-low transition of NRST (User Reset) has
/// been detected since the last read of RSTC_RSR.
/// \param rstc  Pointer to an RSTC peripheral.
//-----------------------------------------------------------------------------
unsigned char RSTC_IsUserReseetDetected(AT91PS_RSTC rstc)
{
    if (READ_RSTC(rstc, RSTC_RSR) & AT91C_RSTC_URSTS) {

        return 1;
    }
    return 0;
}

//-----------------------------------------------------------------------------
/// Return 1 if a software reset command is being performed by the reset
/// controller. The reset controller is busy.
/// \param rstc  Pointer to an RSTC peripheral.
//-----------------------------------------------------------------------------
unsigned char RSTC_IsBusy(AT91PS_RSTC rstc)
{
    if (READ_RSTC(rstc, RSTC_RSR) & AT91C_RSTC_SRCMP) {

        return 1;
    }
    return 0;
}
