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
/// Provides simple drawing function to use with the LCD.
///
/// !!!Usage
///
/// -# Use LCDD_Fill to fill the LCD buffer with a specific color.
/// -# Draw a pixel on the screen at the specified coordinates using
///    LCDD_DrawPixel.
/// -# Draw a rectangle with LCDD_DrawRectangle.
/// -# Draw a string on the LCD with LCDD_DrawString.
//------------------------------------------------------------------------------

#ifndef DRAW_H
#define DRAW_H

//------------------------------------------------------------------------------
//         Global functions
//------------------------------------------------------------------------------

extern void LCDD_Fill(void *pBuffer, unsigned int color);

extern void LCDD_DrawPixel(
    void *pBuffer,
    unsigned int x,
    unsigned int y,
    unsigned int c);

extern void LCDD_DrawRectangle(
    void *pBuffer,
    unsigned int x,
    unsigned int y,
    unsigned int width,
    unsigned int height,
    unsigned int color);

extern void LCDD_DrawString(
    void *pBuffer,
    unsigned int x,
    unsigned int y,
    const char *pString,
    unsigned int color);

extern void LCDD_GetStringSize(
    const char *pString,
    unsigned int *pWidth,
    unsigned int *pHeight);

#endif //#ifndef DRAW_H
