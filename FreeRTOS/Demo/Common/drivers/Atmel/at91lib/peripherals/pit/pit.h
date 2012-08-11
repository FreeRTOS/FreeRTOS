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
/// !Purpose
///
/// Configuration and handling of PIT.
///
/// !Usage
///
/// -# Initialize System timer for a period in µsecond with
///    PIT_Init
/// -# Set the PIT Periodic Interval Value with PIT_SetPIV
/// -# Enable the PIT with PIT_Enable
/// -# Enable & disable PIT interrupts using PIT_EnableInt and
///    PIT_DisableInt
/// -# Read PIT mode register
///    PIT_GetMode
/// -# Read PIT status register
///    PIT_GetStatus
/// -# Read PIT CPIV and PICNT without ressetting the counters
///    PIT_GetPIIR
/// -# Read System timer CPIV and PICNT without ressetting the counters
///    PIT_GetPIVR
//------------------------------------------------------------------------------

#ifndef PIT_H
#define PIT_H

//------------------------------------------------------------------------------
//         Headers
//------------------------------------------------------------------------------

//------------------------------------------------------------------------------
//         Exported functions
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
