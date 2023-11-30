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
/// Interface for configuration the Periodic Interval Timer (PIT) peripheral.
///
/// !Usage
///
/// -# Initialize the PIT with the desired period using PIT_Init().
///    Alternatively, the Periodic Interval Value (PIV) can be configured
///    manually using PIT_SetPIV().
/// -# Start the PIT counting using PIT_Enable().
/// -# Enable & disable the PIT interrupt using PIT_EnableIT() and
///    PIT_DisableIT().
/// -# Retrieve the current status of the PIT using PIT_GetStatus().
/// -# To get the current value of the internal counter and the number of ticks
///    that have occurred, use either PIT_GetPIVR() or PIT_GetPIIR() depending
///    on whether you want the values to be cleared or not.
//------------------------------------------------------------------------------

#ifndef PIT_H
#define PIT_H

//------------------------------------------------------------------------------
//         Global Functions
//------------------------------------------------------------------------------

extern void PIT_Init(unsigned int period, unsigned int pit_frequency);

extern void PIT_SetPIV(unsigned int piv);

extern void PIT_Enable(void);

extern void PIT_EnableIT(void);

extern void PIT_DisableIT(void);

extern unsigned int PIT_GetMode(void);

extern unsigned int PIT_GetStatus(void);

extern unsigned int PIT_GetPIIR(void);

extern unsigned int PIT_GetPIVR(void);

#endif //#ifndef PIT_H

