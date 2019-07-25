/* ----------------------------------------------------------------------------
 *     SAM Software Package License
 * ----------------------------------------------------------------------------
 * Copyright (c) 2011, Atmel Corporation
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

/**
 * \file
 *
 * Implementation of draw font on LCD.
 *
 */

/*----------------------------------------------------------------------------
 *        Headers
 *----------------------------------------------------------------------------*/

#include "board.h"

#include <stdint.h>
#include <assert.h>

/*----------------------------------------------------------------------------
 *        Local variables
 *----------------------------------------------------------------------------*/

/** Global variable describing the font being instantiated. */
const Font gFont = {10, 14};

/*----------------------------------------------------------------------------
 *        Exported functions
 *----------------------------------------------------------------------------*/

/**
 * \brief Draws an ASCII character on LCD.
 *
 * \param pCanvasBuffer Pointer to dedicate canvas buffer.
 * \param x  X-coordinate of character upper-left corner.
 * \param y  Y-coordinate of character upper-left corner.
 * \param c  Character to output.
 * \param color  Character color.
 */
extern void LCDD_DrawChar(uint16_t* pCanvasBuffer, uint32_t x, uint32_t y, 
						uint8_t c, uint32_t color )
{
	uint32_t row, col;

	assert( (c >= 0x20) && (c <= 0x7F) );

	for ( col = 0; col < 10; col++ ) {
		for ( row = 0; row < 8; row++ ) {
			if ( (pCharset10x14[((c - 0x20) * 20) + col * 2] >> (7 - row)) & 0x1){
				LCDD_DrawPixel(pCanvasBuffer, x+col, y+row, color );
			}
		}
		for (row = 0; row < 6; row++ ) {
			if((pCharset10x14[((c - 0x20) * 20) + col * 2 + 1] 
							>> (7 - row)) & 0x1) {
				LCDD_DrawPixel(pCanvasBuffer, x+col, y+row+8, color );
			}
		}
	}
}

/**
 * \brief Draws a string inside a LCD buffer, at the given coordinates.
 * Line breaks will be honoured.
 *
 * \param pCanvasBuffer Pointer to dedicate canvas buffer.
 * \param dwX      X-coordinate of string top-left corner.
 * \param dwY      Y-coordinate of string top-left corner.
 * \param pString  String to display.
 */
extern void LCD_DrawString(uint16_t* pCanvasBuffer, uint32_t dwX, uint32_t dwY, 
						const uint8_t *pString, uint32_t color )
{
	uint32_t dwXorg = dwX;

	while ( *pString != 0 ) {
		if ( *pString == '\n' ) {
			dwY += gFont.height + 2;
			dwX = dwXorg;
		} else {
			LCDD_DrawChar(pCanvasBuffer, dwX, dwY, *pString, color );
			dwX += gFont.width + 2;
		}
		pString++;
	}
}


