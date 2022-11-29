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
//         Headers
//------------------------------------------------------------------------------

#include "draw.h"
#include "font.h"
#include <board.h>
#include <utility/assert.h>
#include <hx8347/hx8347.h>

#include <string.h>

//------------------------------------------------------------------------------
//         Global functions
//------------------------------------------------------------------------------

//------------------------------------------------------------------------------
/// Fills the given LCD buffer with a particular color.
/// Only works in 24-bits packed mode for now.
/// \param pBuffer  LCD buffer to fill.
/// \param color  Fill color.
//------------------------------------------------------------------------------
void LCDD_Fill(void *pBuffer, unsigned int color)
{
    unsigned int i;
    unsigned short color16 = RGB24ToRGB16(color);


    LCD_SetCursor((void *)BOARD_LCD_BASE, 0, 0);
    LCD_WriteRAM_Prepare((void *)BOARD_LCD_BASE);
    for (i = 0; i < (BOARD_LCD_WIDTH * BOARD_LCD_HEIGHT); i++) {

        LCD_WriteRAM((void *)BOARD_LCD_BASE, color16);
    }
}

//------------------------------------------------------------------------------
/// Sets the specified pixel to the given color.
/// !!! Only works in 24-bits packed mode for now. !!!
/// \param pBuffer  LCD buffer to draw on.
/// \param x  X-coordinate of pixel.
/// \param y  Y-coordinate of pixel.
/// \param color  Pixel color.
//------------------------------------------------------------------------------
void LCDD_DrawPixel(
    void *pBuffer,
    unsigned int x,
    unsigned int y,
    unsigned int color)
{
    unsigned short color16 = RGB24ToRGB16(color);

    LCD_SetCursor(pBuffer, x, y);
    LCD_WriteRAM_Prepare(pBuffer);
    LCD_WriteRAM(pBuffer, color16);
}

//------------------------------------------------------------------------------
/// Draws a rectangle inside a LCD buffer, at the given coordinates.
/// \param pBuffer  LCD buffer to draw on.
/// \param x  X-coordinate of upper-left rectangle corner.
/// \param y  Y-coordinate of upper-left rectangle corner.
/// \param width  Rectangle width in pixels.
/// \param height  Rectangle height in pixels.
/// \param color  Rectangle color.
//------------------------------------------------------------------------------
void LCDD_DrawRectangle(
    void *pBuffer,
    unsigned int x,
    unsigned int y,
    unsigned int width,
    unsigned int height,
    unsigned int color)
{
    unsigned int rx, ry;

    for (ry=0; ry < height; ry++) {

        for (rx=0; rx < width; rx++) {

            LCDD_DrawPixel(pBuffer, x+rx, y+ry, color);
        }
    }
}

//------------------------------------------------------------------------------
/// Draws a string inside a LCD buffer, at the given coordinates. Line breaks
/// will be honored.
/// \param pBuffer  Buffer to draw on.
/// \param x  X-coordinate of string top-left corner.
/// \param y  Y-coordinate of string top-left corner.
/// \param pString  String to display.
/// \param color  String color.
//------------------------------------------------------------------------------
void LCDD_DrawString(
    void *pBuffer,
    unsigned int x,
    unsigned int y,
    const char *pString,
    unsigned int color)
{
    unsigned xorg = x;

    while (*pString != 0) {
        if (*pString == '\n') {

            y += gFont.height + 2;
            x = xorg;
        }
        else {

            LCDD_DrawChar(pBuffer, x, y, *pString, color);
            x += gFont.width + 2;
        }
        pString++;
    }
}

//------------------------------------------------------------------------------
/// Returns the width & height in pixels that a string will occupy on the screen
/// if drawn using LCDD_DrawString.
/// \param pString  String.
/// \param pWidth  Pointer for storing the string width (optional).
/// \param pHeight  Pointer for storing the string height (optional).
/// \return String width in pixels.
//------------------------------------------------------------------------------
void LCDD_GetStringSize(
    const char *pString,
    unsigned int *pWidth,
    unsigned int *pHeight)
{
    unsigned int width = 0;
    unsigned int height = gFont.height;

    while (*pString != 0) {

        if (*pString == '\n') {

            height += gFont.height + 2;
        }
        else {

            width += gFont.width + 2;
        }
        pString++;
    }

    if (width > 0) width -= 2;

    if (pWidth) *pWidth = width;
    if (pHeight) *pHeight = height;
}
