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

#ifndef LCD_H
#define LCD_H

//------------------------------------------------------------------------------
//         Exported functions
//------------------------------------------------------------------------------

extern void LCD_Enable(unsigned int frames);

extern void LCD_Disable(unsigned int frames);

extern void LCD_EnableDma();

extern void LCD_DisableDma();

extern void LCD_SetPixelClock(unsigned int masterClock, unsigned int pixelClock);

extern void LCD_SetDisplayType(unsigned int displayType);

extern void LCD_SetScanMode(unsigned int scanMode);

extern void LCD_SetBitsPerPixel(unsigned int bitsPerPixel);

extern void LCD_SetPolarities(
    unsigned int lcdd,
    unsigned int lcdvsync,
    unsigned int lcdhsync,
    unsigned int lcddotclk,
    unsigned int lcdden);

extern void LCD_SetClockMode(unsigned int clockMode);

extern void LCD_SetMemoryFormat(unsigned int format);

extern void LCD_SetSize(unsigned int width, unsigned int height);

extern void LCD_SetVerticalTimings(
    unsigned int vfp,
    unsigned int vbp,
    unsigned int vpw,
    unsigned int vhdly);

extern void LCD_SetHorizontalTimings(
    unsigned int hbp,
    unsigned int hpw,
    unsigned int hfp);

extern void LCD_SetFrameBufferAddress(void *address);

extern void LCD_SetFrameSize(unsigned int frameSize);

extern void LCD_SetBurstLength(unsigned int burstLength);

extern void LCD_SetContrastPrescaler(unsigned int prescaler);

extern void LCD_SetContrastPolarity(unsigned int polarity);

extern void LCD_SetContrastValue(unsigned int value);

extern void LCD_EnableContrast();

#endif //#ifndef LCD_H

