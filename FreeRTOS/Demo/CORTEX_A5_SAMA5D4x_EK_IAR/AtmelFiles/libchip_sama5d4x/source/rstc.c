/* ----------------------------------------------------------------------------
 *         SAM Software Package License 
 * ----------------------------------------------------------------------------
 * Copyright (c) 2013, Atmel Corporation
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

/** \file */
/*---------------------------------------------------------------------------
 *         Headers
 *---------------------------------------------------------------------------*/

#include <chip.h>

/*---------------------------------------------------------------------------
 *         Defines
 *---------------------------------------------------------------------------*/

/** Keywords to write to the reset registers */
#define RSTC_KEY_PASSWORD           RSTC_MR_KEY(0xA5U)

/*---------------------------------------------------------------------------
 *         Exported functions
 *---------------------------------------------------------------------------*/

/**
 * Configure the mode of the RSTC peripheral.
 * The configuration is computed by the lib (RSTC_RMR_*).
 * \param mr Desired mode configuration.
 */
void RSTC_ConfigureMode(uint32_t mr)
{
    Rstc *pHw = RSTC;
    mr &= ~RSTC_MR_KEY_Msk;
    pHw->RSTC_MR = mr | RSTC_KEY_PASSWORD;
}

/**
 * Enable/Disable the detection of a low level on the pin NRST as User Reset
 * \param enable 1 to enable & 0 to disable.
 */
void RSTC_SetUserResetEnable(uint8_t enable)
{
    Rstc *pHw = RSTC;
    uint32_t mr = pHw->RSTC_MR & (~RSTC_MR_KEY_Msk);
    if (enable)
    {
        mr |=  RSTC_MR_URSTEN;
    }
    else
    {
        mr &= ~RSTC_MR_URSTEN;
    }
    pHw->RSTC_MR = mr | RSTC_KEY_PASSWORD;
}

/**
 * Enable/Disable the interrupt of a User Reset (USRTS bit in RSTC_RST).
 * \param enable 1 to enable & 0 to disable.
 */
void RSTC_SetUserResetInterruptEnable(uint8_t enable)
{
    Rstc *pHw = RSTC;
    uint32_t mr = pHw->RSTC_MR & (~RSTC_MR_KEY_Msk);
    if (enable)
    {
        mr |=  RSTC_MR_URSTIEN;
    }
    else {

        mr &= ~RSTC_MR_URSTIEN;
    }
    pHw->RSTC_MR = mr | RSTC_KEY_PASSWORD;
}

/**
 * Setup the external reset length. The length is asserted during a time of
 * pow(2, powl+1) Slow Clock(32KHz). The duration is between 60us and 2s.
 * \param powl   Power length defined.
 */
void RSTC_SetExtResetLength(uint8_t powl)
{
    Rstc *pHw = RSTC;
    uint32_t mr = pHw->RSTC_MR;
    mr &= ~(RSTC_MR_KEY_Msk | RSTC_MR_ERSTL_Msk);
    mr |=  RSTC_MR_ERSTL(powl);
    pHw->RSTC_MR = mr | RSTC_KEY_PASSWORD;
}


/**
 * Resets the processor.
 */
void RSTC_ProcessorReset(void)
{
    Rstc *pHw = RSTC;
    pHw->RSTC_CR = RSTC_CR_PROCRST | RSTC_KEY_PASSWORD;
}

/**
 * Resets the peripherals.
 */
void RSTC_PeripheralReset(void)
{
    Rstc *pHw = RSTC;
    pHw->RSTC_CR = RSTC_CR_PERRST | RSTC_KEY_PASSWORD;
}

/**
 * Asserts the NRST pin for external resets.
 */
void RSTC_ExtReset(void)
{
    Rstc *pHw = RSTC;
    pHw->RSTC_CR = RSTC_CR_EXTRST | RSTC_KEY_PASSWORD;
}

/**
 * Return NRST pin level ( 1 or 0 ).
 */
uint8_t RSTC_GetNrstLevel(void)
{
    Rstc *pHw = RSTC;
    return ((pHw->RSTC_SR & RSTC_SR_NRSTL) > 0);
}

/**
 * Returns 1 if at least one high-to-low transition of NRST (User Reset) has
 * been detected since the last read of RSTC_RSR.
 */
uint8_t RSTC_IsUserResetDetected(void)
{
    Rstc *pHw = RSTC;
    if (pHw->RSTC_SR & RSTC_SR_URSTS)
    {
        return 1;
    }
    return 0;
}

/**
 * Return 1 if a software reset command is being performed by the reset
 * controller. The reset controller is busy.
 */
uint8_t RSTC_IsBusy(void)
{
    Rstc *pHw = RSTC;
    if (pHw->RSTC_SR & RSTC_SR_SRCMP)
    {
        return 1;
    }
    return 0;
}

/**
 * Get the status
 */
uint32_t RSTC_GetStatus(void)
{
    Rstc *pHw = RSTC;
    return (pHw->RSTC_SR);
}

