/* ----------------------------------------------------------------------------
 *         SAM Software Package License
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

/** \file */

/** \addtogroup lcdd_draw Drawing On LCD
 *
 * Interface for drawing function on LCD.
 *
 * \note Before drawing, <b>canvas</b> should be selected via
 *       lcdd_select_canvas(), or created by lcdd_create_canvas().
 *
 * Following functions can use:
 * - Simple drawing:
 *   - lcdd_fill()
 *   - lcdd_draw_pixel()
 *   - lcdd_read_pixel()
 *   - lcdd_draw_line()
 *   - lcdd_draw_rectangle(), lcdd_draw_filled_rectangle()
 *   - lcdd_draw_circle(), lcdd_draw_filled_circle()
 *   - lcdd_draw_image()
 * - String related:
 *   - lcdd_draw_string()
 *   - lcdd_get_string_size()
 *
 * \sa \ref lcdd_module, \ref lcdd_font
 */

#ifndef DRAW_H
#define DRAW_H
/** \addtogroup lcdd_draw
 *@{
 */

/*----------------------------------------------------------------------------
 *        Headers
 *----------------------------------------------------------------------------*/

#include <stdint.h>

/*----------------------------------------------------------------------------
 *        Definitions
 *----------------------------------------------------------------------------*/

/*----------------------------------------------------------------------------
 *        Exported functions
 *----------------------------------------------------------------------------*/

	 /** \addtogroup lcdd_draw_func LCD Drawing Functions */
/** @{*/
extern void lcdd_fill_white(void);

extern void lcdd_fill(uint32_t color);

extern void lcdd_draw_pixel(uint32_t x, uint32_t y, uint32_t c);

extern uint32_t lcdd_read_pixel(uint32_t x, uint32_t y);

extern void lcdd_draw_line(uint32_t x1, uint32_t y1, uint32_t x2, uint32_t y2,
			  uint32_t color);

extern void lcdd_draw_rectangle(uint32_t dwX, uint32_t dwY, uint32_t dwWidth,
								uint32_t dwHeight, uint32_t dwColor);

extern void lcdd_draw_filled_rectangle(uint32_t dwX1, uint32_t dwY1,
										uint32_t dwX2, uint32_t dwY2, uint32_t dwColor);

extern void lcdd_draw_circle(uint32_t x, uint32_t y, uint32_t r, uint32_t color);
extern void lcdd_draw_filled_circle(uint32_t dwX, uint32_t dwY, uint32_t dwR,
									uint32_t dwColor);

extern void lcdd_draw_string(uint32_t x, uint32_t y, const char *pString,
			    uint32_t color);

extern void lcdd_draw_string_with_bgcolor(uint32_t x, uint32_t y,
				       const char *pString, uint32_t fontColor,
				       uint32_t bgColor);

extern void lcdd_get_string_size(const char *pString, uint32_t * pWidth,
			       uint32_t * pHeight);

extern void lcdd_draw_image(uint32_t x, uint32_t y, const uint8_t * pImage,
			   uint32_t width, uint32_t height);

extern void lcdd_clear_window(uint32_t dwX, uint32_t dwY, uint32_t dwWidth,
								uint32_t dwHeight, uint32_t dwColor);


extern void lcdd_draw_rounded_rect (uint32_t x, uint32_t y, uint32_t w, uint32_t h, uint32_t r, uint32_t color);

extern void lcdd_fill_rounded_rect(uint32_t x, uint32_t y, uint32_t w, uint32_t h, uint32_t r, uint32_t color);


extern void lcdd_draw_fast_vline (uint32_t x, uint32_t y, uint32_t h, uint32_t color);
extern void lcdd_draw_fast_hline (uint32_t x, uint32_t y, uint32_t w, uint32_t color);

/** @}*/
/**@}*/
#endif /* #ifndef DRAW_H */
