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
/// Definition of methods for HX8347 driver.
///
/// !!!Usage
///
/// -# LCD_WriteReg
/// -# LCD_ReadReg
/// -# LCD_ReadStatus
/// -# LCD_DumpReg
/// -# LCD_WriteRAM_Prepare
/// -# LCD_WriteRAM
/// -# LCD_ReadRAM
/// -# LCD_Initialize
/// -# LCD_SetCursor
/// -# LCD_On
/// -# LCD_Off
//------------------------------------------------------------------------------

#ifndef HX8347_H
#define HX8347_H

//------------------------------------------------------------------------------
//         Headers
//------------------------------------------------------------------------------
#include <board.h>

#ifdef BOARD_LCD_HX8347

//------------------------------------------------------------------------------
//         Definitions
//------------------------------------------------------------------------------
/// Convert 24-bits color to 16-bits color
#define RGB24ToRGB16(color) (((color >> 8) & 0xF800) | \
    ((color >> 5) & 0x7E0) | \
    ((color >> 3) & 0x1F))

//------------------------------------------------------------------------------
//         Global functions
//------------------------------------------------------------------------------

void LCD_WriteReg(void *pLcdBase, unsigned char reg, unsigned short data);
unsigned short LCD_ReadReg(void *pLcdBase, unsigned char reg);
unsigned short LCD_ReadStatus(void *pLcdBase);
void LCD_DumpReg(void *pLcdBase, unsigned char startAddr, unsigned char endAddr);
void LCD_WriteRAM_Prepare(void *pLcdBase);
void LCD_WriteRAM(void *pLcdBase, unsigned short color);
unsigned short LCD_ReadRAM(void *pLcdBase);
void LCD_Initialize(void *pLcdBase);
void LCD_SetCursor(void *pLcdBase, unsigned short x, unsigned short y);
void LCD_On(void *pLcdBase);
void LCD_Off(void *pLcdBase);

#endif //#ifdef BOARD_LCD_HX8347
#endif //#ifndef HX8347_H
