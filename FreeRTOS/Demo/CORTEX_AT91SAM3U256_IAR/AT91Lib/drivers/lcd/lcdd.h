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
/// !!!Purpose
/// 
/// Simple driver for the LCD, which takes care of the initialization.
/// 
/// !!!Usage
/// 
/// -# Call LCDD_Initialize to configure the LCD controller.
/// -# Set the buffer displayed by the LCD with LCDD_DisplayBuffer if using
///    peripheral LCDC, or start displaying with LCDD_Start if using HX8347.
//------------------------------------------------------------------------------
 
#ifndef LCDD_H
#define LCDD_H
 
//------------------------------------------------------------------------------
//         Global functions
//------------------------------------------------------------------------------

extern void LCDD_Initialize(void);                 // For peripheral LCDC & HX8347

extern void * LCDD_DisplayBuffer(void *pBuffer);   // For peripheral LCDC only

extern void LCDD_Start(void);                      // For HX8347 only

extern void LCDD_Stop(void);                       // For peripheral LCDC & HX8347

extern void LCDD_SetBacklight (unsigned int step); // For peripheral LCDC only

#endif //#ifndef LCDD_H
