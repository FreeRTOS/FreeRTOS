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

#ifndef SLCDC_H
#define SLCDC_H

//------------------------------------------------------------------------------
//         Global definitions
//------------------------------------------------------------------------------

/// Number of segments in SLCD.
#define S7LEKLCD_NUM_SEGMENTS       40
/// Number of commons in SLCD.
#define S7LEKLCD_NUM_COMMONS        10

//------------------------------------------------------------------------------
//         Global functions
//------------------------------------------------------------------------------

extern void SLCDC_Configure(
    unsigned int commons,
    unsigned int segments,
    unsigned int bias,
    unsigned int timeSetting);

extern void SLCDC_Clear(void);

extern void SLCDC_Enable(void);

extern void SLCDC_Disable(void);

extern void SLCDC_SetFrameFreq(
    unsigned int prescalerValue,
    unsigned int dividerValue);

extern void SLCDC_SetDisplayMode(unsigned int mode);

extern void SLCDC_SetBlinkFreq(unsigned int frequency);

extern void SLCDC_EnableInterrupts(unsigned int sources);

extern void SLCDC_DisableInterrupts(unsigned int sources);

#endif //#ifndef SLCDC_H

