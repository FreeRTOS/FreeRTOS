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

 /**
 * \file
 *
 * Interface for draw function on LCD.
 *
 */

#ifndef DRAW_H
#define DRAW_H

/*----------------------------------------------------------------------------
 *        Headers
 *----------------------------------------------------------------------------*/
#include "board.h"
#include <stdint.h>
#include "lcd_gimp_image.h"

/*----------------------------------------------------------------------------
 *        Definitions
 *----------------------------------------------------------------------------*/

/** Horizontal direction line definition */
#define DIRECTION_HLINE   0
/** Vertical direction line definition */
#define DIRECTION_VLINE   1

typedef struct _rect{
	uint32_t x;
	uint32_t y;
	uint32_t width;
	uint32_t height;
}rect;

COMPILER_PACK_SET(1)
typedef struct _rgb{
	uint8_t b;
	uint8_t g;
	uint8_t r;
}sBGR;
COMPILER_PACK_RESET()

/*----------------------------------------------------------------------------
 *        Exported functions
 *----------------------------------------------------------------------------*/
extern void LCDD_SetUpdateWindowSize(rect rc);

extern void LCDD_UpdateWindow(void);

extern void LCDD_UpdatePartialWindow( uint8_t* pbuf, uint32_t size);
	
extern void LCDD_DrawRectangleWithFill(
				uint16_t* pbuf,
				uint32_t dwX,
				uint32_t dwY,
				uint32_t dwWidth,
				uint32_t dwHeight,
				uint32_t dwColor);

extern uint32_t LCDD_DrawCircle( 
				uint16_t* pbuf,
				uint32_t x,
				uint32_t y, 
				uint32_t r,
				uint32_t color);

extern uint32_t LCD_DrawFilledCircle( 
				uint16_t* pbuf,
				uint32_t dwX,
				uint32_t dwY,
				uint32_t dwRadius,
				uint32_t color);

extern void LCDD_DrawString( 
				uint16_t* pbuf,
				uint32_t x,
				uint32_t y,
				const uint8_t *pString,
				uint32_t color );

extern void LCDD_GetStringSize(
				const uint8_t *pString,
				uint32_t *pWidth,
				uint32_t *pHeight );

extern void LCDD_BitBlt(
				uint16_t* pbuf,
				uint32_t dst_x,
				uint32_t dst_y,
				uint32_t dst_w,
				uint32_t dst_h,
				const LcdColor_t *src,
				uint32_t src_x,
				uint32_t src_y,
				uint32_t src_w,
				uint32_t src_h);
			
extern void LCDD_BitBltAlphaBlend(uint16_t* pbuf,
								uint32_t dst_x,
								uint32_t dst_y,
								uint32_t dst_w,
								uint32_t dst_h,
								const LcdColor_t *src,
								uint32_t src_x,
								uint32_t src_y,
								uint32_t src_w,
								uint32_t src_h,
								uint32_t alpha);
extern void LCDD_DrawImage(
				uint16_t* pbuf,
				uint32_t dwX,
				uint32_t dwY,
				const LcdColor_t *pImage,
				uint32_t dwWidth,
				uint32_t dwHeight );

extern void LCDD_DrawPixel(
				uint16_t* pbuf,
				uint32_t x,
				uint32_t y,
				uint32_t color );

extern void LCDD_DrawLine(
				uint16_t* pbuf,
				uint32_t dwX1,
				uint32_t dwY1,
				uint32_t dwX2,
				uint32_t dwY2,
				uint32_t color);

extern uint32_t LCDD_DrawLineBresenham(
				uint16_t* pbuf,
				uint32_t dwX1,
				uint32_t dwY1,
				uint32_t dwX2,
				uint32_t dwY2,
				uint32_t color);

extern void LCDD_DrawRectangle(
				uint16_t* pbuf,
				uint32_t x,
				uint32_t y,
				uint32_t width,
				uint32_t height,
				uint32_t color);

extern void LCDD_SetCavasBuffer(
				void* pBuffer,
				uint32_t wBufferSize);
			
extern void LCDD_DrawStraightLine(
				uint16_t* pbuf,
				uint32_t dwX1, 
				uint32_t dwY1, 
				uint32_t dwX2, 
				uint32_t dwY2 , 
				uint32_t color );
#endif /* #ifndef DRAW_H */
