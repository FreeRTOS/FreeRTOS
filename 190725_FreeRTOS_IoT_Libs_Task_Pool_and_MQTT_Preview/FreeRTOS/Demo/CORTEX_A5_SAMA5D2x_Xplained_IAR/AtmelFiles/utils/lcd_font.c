/* ----------------------------------------------------------------------------
 *         SAM Software Package License
 * ----------------------------------------------------------------------------
 * Copyright (c) 2015, Atmel Corporation
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

/** \file
 *
 * Implementation of draw font on LCD.
 *
 */

/*----------------------------------------------------------------------------
 *        Headers
 *----------------------------------------------------------------------------*/

#include "lcd_font.h"
#include "lcd_draw.h"

#include "font.h"

#include <assert.h>

/*----------------------------------------------------------------------------
 *        Local variables
 *----------------------------------------------------------------------------*/

/** Global variable describing the font being instanced. */
//const Font gFont = { 10, 14 };

static uint8_t font_sel = FONT10x14;

/*----------------------------------------------------------------------------
 *        Exported functions
 *----------------------------------------------------------------------------*/

struct _font_parameters* lcdd_select_font (_FONT_enum font)
{
	font_sel = font;
	return &font_param[font];
}

uint8_t lcdd_get_selected_font (void)
{
	return font_sel;
}

void lcdd_draw_char(uint32_t x, uint32_t y, uint8_t c, uint32_t color)
{
	uint32_t row, col;
	uint8_t Ch;
	uint8_t width = font_param[font_sel].width ;
    uint8_t height = font_param[font_sel].height;
	const uint8_t* pfont = font_param[font_sel].pfont;

	assert((c >= 0x20) && (c <= 0x7F));

    switch (font_sel)
    {
      case FONT10x14:
        for (col=0 ; col < width ; col++ ) {
          for (row=0 ; row<8 ; row++ ) {
            Ch = (pfont[((c - 0x20) * 20) + col * 2] >> (7 - row)) & 0x1;
            if (Ch) lcdd_draw_pixel( x+col, y+row, color) ;
          }
          for (row=0; row<6; row++ ) {
            Ch = (pfont[((c - 0x20) * 20) + col * 2 + 1] >> (7 - row)) & 0x1;
            if (Ch) lcdd_draw_pixel( x+col, y+row+8, color) ;
          }
        }
        break;

       case FONT10x8:
        for (col=0 ; col < width ; col++ ) {
          Ch = pfont[((c-0x20)*width)+ col];
		  if (Ch) {
            for (row=0 ; row < height; row++ ) {
              if ((Ch>>row)&0x1) {
                  lcdd_draw_pixel( x+(height-row), y+col, color) ;
              }
            }
          }
        }
        break;

      case FONT8x8:
      case FONT6x8:
        for (col=0 ; col < width ; col++ ) {
          Ch = pfont[((c-0x20)*width)+ col];
          if (Ch) {
            for (row=0 ; row < height; row++ ) {
              if ((Ch>>row)&0x1)  {
                if (font_sel == FONT8x8)
                  lcdd_draw_pixel( x+row, y+col, color) ;
                else
                  lcdd_draw_pixel( x+col, y+row, color) ;
              }
            }
          }
        }
        break;
    }
}

/**
 * \brief Draws an ASCII character on LCD with given background color.
 *
 * \param x          X-coordinate of character upper-left corner.
 * \param y          Y-coordinate of character upper-left corner.
 * \param c          Character to output.
 * \param fontColor  Character color.
 * \param bgColor    Background color.
 */
void lcdd_draw_char_with_bgcolor(uint32_t x, uint32_t y, uint8_t c, uint32_t fontColor,
			 uint32_t bgColor)
{
	uint32_t row, col;
	uint8_t Ch;
	uint8_t width = font_param[font_sel].width ;
    uint8_t height = font_param[font_sel].height;
	const uint8_t* pfont = font_param[font_sel].pfont;

	assert((c >= 0x20) && (c <= 0x7F));

    switch (font_sel)
    {
      case FONT10x14:
        for (col=0 ; col < width ; col++ ) {
          for (row=0 ; row<8 ; row++ ) {
            Ch = (pfont[((c - 0x20) * 20) + col * 2] >> (7 - row)) & 0x1;
            if (Ch) lcdd_draw_pixel( x+col, y+row, fontColor) ;
			else lcdd_draw_pixel( x+col, y+row, bgColor) ;
          }
          for (row=0; row<6; row++ ) {
            Ch = (pfont[((c - 0x20) * 20) + col * 2 + 1] >> (7 - row)) & 0x1;
            if (Ch) lcdd_draw_pixel( x+col, y+row+8, fontColor) ;
			else lcdd_draw_pixel( x+col, y+row+8, bgColor) ;
          }
        }
        break;

       case FONT10x8:
        for (col=0 ; col < width ; col++ ) {
          Ch = pfont[((c-0x20)*width)+ col];
		  if (Ch) {
            for (row=0 ; row < height; row++ ) {
              if ((Ch>>row)&0x1) {
                  lcdd_draw_pixel( x+(height-row), y+col, fontColor) ;
			  }
			  else {
				  lcdd_draw_pixel( x+(height-row), y+col, bgColor) ;
			  }
            }
          }
        }
        break;

      case FONT8x8:
      case FONT6x8:
        for (col=0 ; col < width ; col++ ) {
          Ch = pfont[((c-0x20)*width)+ col];
          if (Ch) {
            for (row=0 ; row < height; row++ ) {
              if ((Ch>>row)&0x1)  {
                if (font_sel == FONT8x8)
                  lcdd_draw_pixel( x+row, y+col, fontColor) ;
                else
                  lcdd_draw_pixel( x+col, y+row, fontColor) ;
              }
			  else {
				  if (font_sel == FONT8x8)
                  lcdd_draw_pixel( x+row, y+col, bgColor) ;
                else
                  lcdd_draw_pixel( x+col, y+row, bgColor) ;
			  }
            }
          }
        }
        break;
    }
}
