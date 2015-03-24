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

#include <stdint.h>
#include "lcd_gimp_image.h"

/*----------------------------------------------------------------------------
 *        Definitions
 *----------------------------------------------------------------------------*/

/** Horizontal direction line definition */
#define DIRECTION_HLINE   0
/** Vertical direction line definition */
#define DIRECTION_VLINE   1

/*----------------------------------------------------------------------------
 *        Exported functions
 *----------------------------------------------------------------------------*/
extern void LCDD_Fill( uint32_t color ) ;

extern void LCDD_DrawPixel( uint32_t x, uint32_t y, uint32_t c ) ;

extern uint32_t LCDD_ReadPixel( uint32_t x, uint32_t y ) ;

extern void LCDD_DrawLine( uint32_t dwX1, uint32_t dwY1, uint32_t dwX2, uint32_t dwY2 , uint32_t color ) ;

extern uint32_t LCDD_DrawLineBresenham( uint32_t dwX1, uint32_t dwY1, uint32_t dwX2, uint32_t dwY2 , uint32_t color);

extern void LCDD_DrawRectangle( uint32_t dwX, uint32_t dwY, uint32_t dwWidth, uint32_t dwHeight, uint32_t dwColor ) ;

extern void LCDD_DrawRectangleWithFill( uint32_t dwX, uint32_t dwY, uint32_t dwWidth, uint32_t dwHeight, uint32_t dwColor ) ;

extern uint32_t LCDD_DrawCircle( uint32_t x, uint32_t y, uint32_t r, uint32_t color ) ;

extern uint32_t LCD_DrawFilledCircle( uint32_t dwX, uint32_t dwY, uint32_t dwRadius, uint32_t color);

extern void LCDD_DrawString( uint32_t x, uint32_t y, const uint8_t *pString, uint32_t color ) ;

extern void LCDD_DrawStringWithBGColor( uint32_t x, uint32_t y, const char *pString, uint32_t fontColor, uint32_t bgColor ) ;

extern void LCDD_GetStringSize( const uint8_t *pString, uint32_t *pWidth, uint32_t *pHeight ) ;

extern void LCDD_DrawImage( uint32_t x, uint32_t y, const LcdColor_t *pImage, uint32_t width, uint32_t height ) ;

extern void LCDD_DrawGIMPImage( uint32_t dwX, uint32_t dwY, const SGIMPImage* pGIMPImage );

extern void LCDD_ClearWindow( uint32_t dwX, uint32_t dwY, uint32_t dwWidth, uint32_t dwHeight, uint32_t dwColor ) ;

#endif /* #ifndef DRAW_H */
