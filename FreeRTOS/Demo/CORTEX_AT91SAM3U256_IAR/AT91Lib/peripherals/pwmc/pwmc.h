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

//------------------------------------------------------------------------------
/// \unit
///
/// !Purpose
///
/// Interface for configuration the Pulse Width Modulation Controller (PWM) peripheral.
///
/// !Usage
///
///    -# Configures PWM clocks A & B to run at the given frequencies using
///       PWMC_ConfigureClocks().
///    -# Configure PWMC channel using PWMC_ConfigureChannel(), PWMC_SetPeriod()
///       and PWMC_SetDutyCycle().
///    -# Enable & disable channel using PWMC_EnableChannel() and 
///       PWMC_DisableChannel().
///    -# Enable & disable the period interrupt for the given PWM channel using 
///       PWMC_EnableChannelIt() and PWMC_DisableChannelIt().
///
/// Please refer to the list of functions in the #Overview# tab of this unit
/// for more detailed information.
//------------------------------------------------------------------------------

#ifndef PWMC_H
#define PWMC_H

//------------------------------------------------------------------------------
//         Global functions
//------------------------------------------------------------------------------

extern void PWMC_ConfigureChannel(
    unsigned char channel,
    unsigned int prescaler,
    unsigned int alignment,
    unsigned int polarity);

extern void PWMC_ConfigureClocks
    (unsigned int clka,
     unsigned int clkb,
     unsigned int mck);

extern void PWMC_SetPeriod(unsigned char channel, unsigned short period);

extern void PWMC_SetDutyCycle(unsigned char channel, unsigned short duty);

extern void PWMC_EnableChannel(unsigned char channel);

extern void PWMC_DisableChannel(unsigned char channel);

extern void PWMC_EnableChannelIt(unsigned char channel);

extern void PWMC_DisableChannelIt(unsigned char channel);

#endif //#ifndef PWMC_H

