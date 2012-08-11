/* ----------------------------------------------------------------------------
 *     ATMEL Microcontroller Software Support
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
//     Headers
//------------------------------------------------------------------------------

#include "font.h"
#include "draw.h"
#include "font10x14.h"
#include <utility/assert.h>

//------------------------------------------------------------------------------
//     Local variables
//------------------------------------------------------------------------------

/// Global variable describing the font being instancied.
const Font gFont = {10, 14};

//------------------------------------------------------------------------------
//     Global functions
//------------------------------------------------------------------------------

//------------------------------------------------------------------------------
/// Draws an ASCII character on the given LCD buffer.
/// \param pBuffer  Buffer to write on.
/// \param x  X-coordinate of character upper-left corner.
/// \param y  Y-coordinate of character upper-left corner.
/// \param c  Character to output.
/// \param color  Character color.
//------------------------------------------------------------------------------
void LCDD_DrawChar(
    void *pBuffer,
    unsigned int x,
    unsigned int y,
    char c,
    unsigned int color)
{
    unsigned int row, col;

    SANITY_CHECK((c >= 0x20) && (c <= 0x7F));

    for (col = 0; col < 10; col++) {

        for (row = 0; row < 8; row++) {

            if ((pCharset10x14[((c - 0x20) * 20) + col * 2] >> (7 - row)) & 0x1) {

                LCDD_DrawPixel(pBuffer, x+col, y+row, color);
            }
        }
        for (row = 0; row < 6; row++) {

            if ((pCharset10x14[((c - 0x20) * 20) + col * 2 + 1] >> (7 - row)) & 0x1) {

                LCDD_DrawPixel(pBuffer, x+col, y+row+8, color);
            }
        }
    }
}
