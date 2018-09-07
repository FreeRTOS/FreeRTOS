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
 * Implementation of draw function on LCD, Include draw text, image
 * and basic shapes (line, rectangle, circle).
 *
 */

/*----------------------------------------------------------------------------
 *        Headers
 *----------------------------------------------------------------------------*/

#include "board.h"

#include <stdint.h>
#include <string.h>
#include <assert.h>

/*----------------------------------------------------------------------------
 *        Local variables
 *----------------------------------------------------------------------------*/
static void* gpCanvasBuffer;
static uint32_t gwCanvasBufferSize;
static uint32_t gwCanvasMaxWidth, gwCanvasMaxHeight;
extern uint8_t ili9488_lcdMode;
/*----------------------------------------------------------------------------
 *        Local functions
 *----------------------------------------------------------------------------*/

/*
 * \brief Fill rectangle with given color
 * \param pCanvasBuffer Pointer to dedicate canvas buffer.
 * \param rc  rectangle defines X and Y coordinate, width and height of windows.
 * \param dwColor color to be filled.
 */
static void LCDD_FillSolidRect(uint16_t *pCanvasBuffer, rect rc, uint32_t dwColor )
{
	uint32_t row, col;
	uint32_t w,h;
	
	//assert(gpCanvasBuffer!=NULL);
	w = rc.x + rc.width;
	w = w > gwCanvasMaxWidth ? gwCanvasMaxWidth : w;
	h = rc.y + rc.height;
	h = h > gwCanvasMaxHeight ? gwCanvasMaxHeight : h;

	if (ili9488_lcdMode == ILI9488_SPIMODE) {
		sBGR *p_buf = gpCanvasBuffer; 
		if(pCanvasBuffer != NULL) p_buf = (sBGR *)((uint8_t*)pCanvasBuffer);
		//it'd better change to a DMA transfer
		for(row = rc.y; row < h; row++) {
			for(col = rc.x; col < w; col++) {
				//*p_buf++ = dwColor;
				p_buf[row * gwCanvasMaxWidth + col].b = dwColor&0xFF;
				p_buf[row * gwCanvasMaxWidth + col].g = dwColor>>8;
				p_buf[row * gwCanvasMaxWidth + col].r = dwColor>>16;
			}
		}
	} else {
		uint16_t *p_buf = gpCanvasBuffer;
		if(pCanvasBuffer != NULL) p_buf = pCanvasBuffer;
		//it'd better change to a DMA transfer
		for(row = rc.y; row < h; row++) {
			for(col = rc.x; col < w; col++) {
				p_buf[row * gwCanvasMaxWidth + col] = (uint16_t)dwColor;
			}
		}
	}
}

/*----------------------------------------------------------------------------
 *        Exported functions
 *----------------------------------------------------------------------------*/
/*
 * \brief Update windows size.
 * \param rc  rectangle defines X and Y coordinate, width and height of windows.
 */
void LCDD_SetUpdateWindowSize(rect rc)
{
	gwCanvasMaxWidth = rc.width + 1;
	gwCanvasMaxHeight = rc.height + 1;
	if (ili9488_lcdMode == ILI9488_SPIMODE) {
		ILI9488_SpiSetWindow( rc.x, rc.y, rc.width, rc.height);
	} else {
		ILI9488_EbiSetWindow( rc.x, rc.y, rc.width, rc.height);
	}
}

/*
 * \brief Update windows in current canvas.
 */
void LCDD_UpdateWindow(void)
{
	uint32_t size = 0;
	if (ili9488_lcdMode == ILI9488_SPIMODE) {
		size = gwCanvasBufferSize / (sizeof(sBGR)) *3 ;
		ILI9488_SpiSendCommand(ILI9488_CMD_MEMORY_WRITE, 
						(uint8_t*)gpCanvasBuffer, 0, AccessWrite, size);
	} else {
		 size = gwCanvasBufferSize / sizeof(uint16_t);
		 ILI9488_EbiSendCommand(ILI9488_CMD_MEMORY_WRITE, 
						(uint16_t*)gpCanvasBuffer, 0, AccessWrite, size);
	}
 }

/*
 * \brief Update windows in partial canvas.
 * \param pCanvasBuffer Pointer to dedicate canvas buffer.
 * \param size Size of canvas buffer.
 */
void LCDD_UpdatePartialWindow(uint8_t* pCanvasBuffer,uint32_t size)
{
	uint32_t cnt = 0;
	if (ili9488_lcdMode == ILI9488_SPIMODE) {
		cnt = size/sizeof(sBGR) * 3;
		ILI9488_SpiSendCommand(ILI9488_CMD_MEMORY_WRITE, 
						(uint8_t*)pCanvasBuffer, 0, AccessWrite, cnt);
	} else {
		 cnt = size/sizeof(uint16_t);
		 ILI9488_EbiSendCommand(ILI9488_CMD_MEMORY_WRITE, 
						(uint16_t*)pCanvasBuffer, 0, AccessWrite, cnt);
	}
}
/*
 * \brief Draws a rectangle with fill inside on LCD, at the given coordinates.
 *
 * \param pCanvasBuffer Pointer to dedicate canvas buffer.
 * \param x      X-coordinate of upper-left rectangle corner.
 * \param y      Y-coordinate of upper-left rectangle corner.
 * \param width  Rectangle width in pixels.
 * \param height  Rectangle height in pixels.
 * \param color  Rectangle color.
 */
void LCDD_DrawRectangleWithFill(uint16_t *pCanvasBuffer, uint32_t dwX, uint32_t dwY, uint32_t dwWidth, 
				uint32_t dwHeight, uint32_t dwColor)
{
	rect rc;
	rc.x = dwX;
	rc.y = dwY;
	rc.width = dwWidth + 1;
	rc.height = dwHeight + 1;
	LCDD_FillSolidRect(pCanvasBuffer, rc , dwColor);
}

/**
 * \brief Draws a circle on LCD, at the given coordinates.
 *
 * \param pCanvasBuffer Pointer to dedicate canvas buffer.
 * \param x      X-coordinate of circle centre.
 * \param y      Y-coordinate of circle centre.
 * \param r      circle radius.
 * \param color  circle color.
 */
uint32_t LCDD_DrawCircle(uint16_t *pCanvasBuffer, uint32_t x, uint32_t y, uint32_t r, uint32_t color )
{
	signed int d; /* Decision Variable */
	uint32_t  curX; /* Current X Value */
	uint32_t  curY; /* Current Y Value */

	d = 3 - (r << 1);
	curX = 0;
	curY = r;

	while (curX <= curY) {
		LCDD_DrawPixel(pCanvasBuffer, x + curX, y + curY, color);
		LCDD_DrawPixel(pCanvasBuffer, x + curX, y - curY, color);
		LCDD_DrawPixel(pCanvasBuffer, x - curX, y + curY, color);
		LCDD_DrawPixel(pCanvasBuffer, x - curX, y - curY, color);
		LCDD_DrawPixel(pCanvasBuffer, x + curY, y + curX, color);
		LCDD_DrawPixel(pCanvasBuffer, x + curY, y - curX, color);
		LCDD_DrawPixel(pCanvasBuffer, x - curY, y + curX, color);
		LCDD_DrawPixel(pCanvasBuffer, x - curY, y - curX, color);

		if (d < 0) {
			d += (curX << 2) + 6;
		} else {
			d += ((curX - curY) << 2) + 10;
			curY--;
		}
		curX++;
	}
	return 0;
}

/*
 * \brief Draws a circle with fill inside on LCD, at the given coordinates.
 *
 * \param pCanvasBuffer Pointer to dedicate canvas buffer.
 * \param dwX      X-coordinate of upper-left rectangle corner.
 * \param dwY      Y-coordinate of upper-left rectangle corner.
 * \param dwRadius  Radius.
 * \param color  Rectangle color.
 */
uint32_t LCD_DrawFilledCircle(uint16_t *pCanvasBuffer, uint32_t dwX, uint32_t dwY, 
						uint32_t dwRadius, uint32_t color)
{
	signed int d; /* Decision Variable */
	uint32_t dwCurX; /* Current X Value */
	uint32_t dwCurY; /* Current Y Value */
	uint32_t dwXmin, dwYmin;

	if (dwRadius == 0) {
		return 0;
	}
	d = 3 - (dwRadius << 1);
	dwCurX = 0;
	dwCurY = dwRadius;

	while ( dwCurX <= dwCurY ) {
		dwXmin = (dwCurX > dwX) ? 0 : dwX-dwCurX;
		dwYmin = (dwCurY > dwY) ? 0 : dwY-dwCurY;
		LCDD_DrawRectangleWithFill(pCanvasBuffer, dwXmin, dwYmin, 
									dwX + dwCurX - dwXmin, 1 ,color);
		LCDD_DrawRectangleWithFill(pCanvasBuffer, dwXmin, 
								dwY+dwCurY, dwX + dwCurX - dwXmin, 1,
						color );
		dwXmin = (dwCurY > dwX) ? 0 : dwX-dwCurY;
		dwYmin = (dwCurX > dwY) ? 0 : dwY-dwCurX;
		LCDD_DrawRectangleWithFill(pCanvasBuffer, dwXmin, dwYmin, 
								dwX + dwCurY -dwXmin , 1, color );
		LCDD_DrawRectangleWithFill(pCanvasBuffer, dwXmin, 
								dwY + dwCurX, dwX+dwCurY - dwXmin, 1,
						color  );
		if ( d < 0 ) {
			d += (dwCurX << 2) + 6;
		} else {
			d += ((dwCurX - dwCurY) << 2) + 10;
			dwCurY--;
		}
		dwCurX++;
	}

	return 0;
}

/**
 * \brief Draws a string inside a LCD buffer, at the given coordinates.
 *
 * \param pCanvasBuffer Pointer to dedicate canvas buffer.
 * \param x        X-coordinate of string top-left corner.
 * \param y        Y-coordinate of string top-left corner.
 * \param pString  String to display.
 * \param color    String color.
 */
void LCDD_DrawString( uint16_t* pCanvasBuffer, uint32_t x, uint32_t y, 
                     const uint8_t *pString, uint32_t color )
{
	uint32_t xorg = x;

	while ( *pString != 0 ) {
		if ( *pString == '\n' ) {
			y += gFont.height + 2;
			x = xorg;
		} else {
			LCDD_DrawChar(pCanvasBuffer, x, y, *pString, color );
			x += gFont.width + 2;
		}
		pString++;
	}
}

/**
 * \brief Returns the width & height in pixels that a string will occupy on the 
 * screen if drawn using LCDD_DrawString.
 *
 * \param pString  String.
 * \param pWidth   Pointer for storing the string width (optional).
 * \param pHeight  Pointer for storing the string height (optional).
 *
 * \return String width in pixels.
 */
void LCDD_GetStringSize( const uint8_t *pString, uint32_t *pWidth,
				uint32_t *pHeight )
{
	uint32_t width = 0;
	uint32_t height = gFont.height;

	while ( *pString != 0 ) {
		if ( *pString == '\n' ) {
			height += gFont.height + 2;
		} else {
			width += gFont.width + 2;
		}
		pString++;
	}

	if ( width > 0 ) {
		width -= 2;
	}

	if ( pWidth != NULL ) {
		*pWidth = width;
	}

	if ( pHeight != NULL ) {
		*pHeight = height;
	}
}


/*
 * \brief Performs a bit-block transfer of the color data corresponding to a 
 * rectangle of pixels from the given source context into destination context.
 *
 * \param pCanvasBuffer Pointer to dedicate canvas buffer.
 * \param dst_x   X-coordinate of source rectangle.
 * \param dst_y   Y-coordinate of source rectangle.
 * \param dst_w   Rectangle width in pixels of source rectangle.
 * \param dst_h   Rectangle height in pixels of source rectangle.
 * \param src     Pointer to the source device context.
 * \param src_x   X-coordinate of destination rectangle.
 * \param src_y   Y-coordinate of destination rectangle.
 * \param src_w   Rectangle width in pixels of destination rectangle.
 * \param src_h   Rectangle height in pixels of destination rectangle.
 */
void LCDD_BitBlt( uint16_t* pCanvasBuffer, uint32_t dst_x,uint32_t dst_y,uint32_t dst_w,uint32_t dst_h,
				 const LcdColor_t *src,
				 uint32_t src_x,uint32_t src_y,uint32_t src_w,uint32_t src_h)
{
	uint32_t row,col;
	uint32_t src_row,src_col;
	//assert(gpCanvasBuffer!=NULL);
	
	src_h = src_h;
	if (ili9488_lcdMode == ILI9488_SPIMODE) {
		sBGR *p_buf = gpCanvasBuffer;
		if(pCanvasBuffer != NULL) p_buf = (sBGR *)((uint8_t*)pCanvasBuffer);
		//it'd better change to a DMA transfer
		SCB_CleanInvalidateDCache();
		for(src_row = src_y,row = dst_y; row < dst_h; row++,src_row++) {
			for(src_col = src_x,col = dst_x; col < dst_w; col++,src_col++) {
				p_buf[row * gwCanvasMaxWidth+col].r = src[src_row*src_w + src_col]&0xFF;
				p_buf[row * gwCanvasMaxWidth+col].g = src[src_row*src_w + src_col]>>8;
				p_buf[row * gwCanvasMaxWidth+col].b = src[src_row*src_w + src_col]>>16;
			}
			memory_barrier()
		}
		memory_barrier()
	} else {
		uint16_t *p_buf = gpCanvasBuffer;
		if(pCanvasBuffer != NULL) p_buf = pCanvasBuffer;
		//it'd better change to a DMA transfer
		SCB_CleanInvalidateDCache();
		for(src_row = src_y,row = dst_y; row < dst_h; row++,src_row++) {
			for(src_col = src_x, col = dst_x; col < dst_w; col++,src_col++) {
				p_buf[row * gwCanvasMaxWidth+col] = src[src_row*src_w + src_col];
			}
		}
		memory_barrier()
	}
}


/*
 * \brief Performs a bit-block transfer of the color data corresponding to a 
 * rectangle of pixels from the given source context into destination context.
 *
 * \param pCanvasBuffer Pointer to dedicate canvas buffer.
 * \param dst_x   X-coordinate of source rectangle.
 * \param dst_y   Y-coordinate of source rectangle.
 * \param dst_w   Rectangle width in pixels of source rectangle.
 * \param dst_h   Rectangle height in pixels of source rectangle.
 * \param src     Pointer to the source device context.
 * \param src_x   X-coordinate of destination rectangle.
 * \param src_y   Y-coordinate of destination rectangle.
 * \param src_w   Rectangle width in pixels of destination rectangle.
 * \param src_h   Rectangle height in pixels of destination rectangle.
 * \param alpha   alpha value.
 */
void LCDD_BitBltAlphaBlend(uint16_t* pCanvasBuffer,
						uint32_t dst_x,
						uint32_t dst_y,
						uint32_t dst_w,
						uint32_t dst_h,
						const LcdColor_t *src,
						uint32_t src_x,
						uint32_t src_y,
						uint32_t src_w,
						uint32_t src_h,
						uint32_t alpha)
{
	uint32_t row,col;
	uint32_t src_row,src_col;
	uint32_t w,h;
	uint32_t dst_row;
	uint32_t r,g,b;
	
	if (ili9488_lcdMode == ILI9488_SPIMODE) {
		sBGR *p_buf = gpCanvasBuffer;
		if(pCanvasBuffer != NULL) p_buf = (sBGR *)((uint8_t*)pCanvasBuffer);

		//it'd better change to a DMA transfer
		SCB_CleanInvalidateDCache();
		for(src_row = src_y,row = dst_y; row < dst_h; row++,src_row++) {
			for(src_col = src_x,col = dst_x; col < dst_w; col++,src_col++) {
				p_buf[row *dst_w +col].r = src[src_row*src_w + src_col]&0xFF;
				p_buf[row *dst_w +col].g = src[src_row*src_w + src_col]>>8;
				p_buf[row *dst_w +col].b = src[src_row*src_w + src_col]>>16;
			}
		}
		memory_barrier()
	} else {
		uint16_t *p_buf = gpCanvasBuffer;
		if(pCanvasBuffer != NULL) p_buf = pCanvasBuffer;
		w = src_x + src_w;
		h = src_y + src_h;
		dst_row = dst_y;
		p_buf += (dst_row*dst_w + dst_x);
		src += src_y*w + src_x;
		SCB_CleanInvalidateDCache();
		for(src_row = src_y; src_row < h; src_row++,dst_row++) {
			for(src_col = src_x; src_col < w; src_col++){
				r = (p_buf[src_col] >> 11) * (255 - alpha) / 255 + 
						(src[src_col] >> 11) * alpha / 255;
				if(r > 0x1F) r = 0x1F;
				g = ((p_buf[src_col] >> 5) & 0x3F) * (255 - alpha) / 255 + 
						((src[src_col] >> 5) & 0x3f) * alpha / 255;
				if(g > 0x3F) g = 0x3F;
				b = ((p_buf[src_col]) & 0x1F) * (255 - alpha) / 255 
						+ ((src[src_col]) & 0x1f) * alpha / 255;
				if(b > 0x1F) b = 0x1F;   
				p_buf[src_col] = ((r & 0x1F) << 11)|((g & 0x3F) << 5)|( b & 0x1F);
			}
			p_buf += dst_w;
			src += w;
		}
		memory_barrier()
	}
}

/*
 * \brief Draw a raw image at given position on LCD.
 *
 * \param pCanvasBuffer Pointer to dedicate canvas buffer.
 * \param dwX       X-coordinate of image start.
 * \param dwY       Y-coordinate of image start.
 * \param pImage    Image buffer.
 * \param width     Image width.
 * \param height    Image height.
 */
 void LCDD_DrawImage(uint16_t* pCanvasBuffer, uint32_t dwX, uint32_t dwY, 
					const LcdColor_t *pImage, uint32_t dwWidth, uint32_t dwHeight )
{
	/* Determine the refresh window area */
	/* Horizontal and Vertical RAM Address Position (R50h, R51h, R52h, R53h) */
	//CheckBoxCoordinates(&dwX, &dwY, &dwWidth, &dwHeight);

	LCDD_BitBlt(pCanvasBuffer, dwX, dwY, dwWidth, dwHeight,
				pImage, 0, 0, dwWidth - dwX, dwHeight - dwY);
}

/**
 * \brief Draw a pixel on LCD of given color.
 *
 * \param pCanvasBuffer Pointer to dedicate canvas buffer.
 * \param x  X-coordinate of pixel.
 * \param y  Y-coordinate of pixel.
 * \param color  Pixel color.
 */
void LCDD_DrawPixel(uint16_t* pCanvasBuffer, uint32_t x, uint32_t y, uint32_t color )
{
	//assert(gpCanvasBuffer!=NULL);
	if (ili9488_lcdMode == ILI9488_SPIMODE) {
		sBGR *p_buf = gpCanvasBuffer;
		if(pCanvasBuffer != NULL) p_buf = (sBGR *)((uint8_t*)pCanvasBuffer);
		p_buf += y * gwCanvasMaxWidth;
		p_buf += x;
		p_buf->b = color&0xFF;
		p_buf->g = color>>8;
		p_buf->r = color>>16;
		p_buf++;
		memory_barrier()
	} else {
		uint16_t *p_buf = gpCanvasBuffer;
		if(pCanvasBuffer != NULL) p_buf = pCanvasBuffer;
		p_buf += y * gwCanvasMaxWidth;
		p_buf += x;
		*p_buf = (uint16_t)color;
	}
}

/*
 * \brief Draw a line on LCD, horizontal and vertical line are supported.
 *
 * \param pCanvasBuffer Pointer to dedicate canvas buffer.
 * \param dwX1   X-coordinate of line start.
 * \param dwY1   Y-coordinate of line start.
 * \param dwX2   X-coordinate of line end.
 * \param dwY2   Y-coordinate of line end.
 * \param color  Pixel color.
 */
void LCDD_DrawLine(uint16_t* pCanvasBuffer, uint32_t dwX1, uint32_t dwY1, 
				uint32_t dwX2, uint32_t dwY2 , uint32_t color )
{
	if (( dwY1 == dwY2 ) || (dwX1 == dwX2)) {
		//LCDD_DrawRectangleWithFill( dwX1, dwY1, dwX2, dwY2, color );
		LCDD_DrawStraightLine(pCanvasBuffer, dwX1, dwY1, dwX2, dwY2, color );
	} else {
		LCDD_DrawLineBresenham(pCanvasBuffer, dwX1, dwY1, dwX2, dwY2 , color);
	}
}

void LCDD_DrawStraightLine(uint16_t* pCanvasBuffer, uint32_t dwX1, uint32_t dwY1, 
						uint32_t dwX2, uint32_t dwY2 , uint32_t color )
{
	uint32_t x,y;
	uint32_t tmp;

	if(dwY1 > dwY2)
	{
		tmp = dwY1;
		dwY1 = dwY2;
		dwY2 = tmp;
	}
	if(dwX1 > dwX2)
	{
		tmp = dwX1;
		dwX1 = dwX2;
		dwX2 = tmp;
	}
	for(y = dwY1; y<=dwY2; y++)
	{
		for(x=dwX1;x<=dwX2;x++)
		{
			LCDD_DrawPixel(pCanvasBuffer,  x , y , color);
		}
	}
}

/*
 * \brief Draw a line on LCD, which is not horizontal or vertical.
 *
 * \param pCanvasBuffer Pointer to dedicate canvas buffer.
 * \param dwX1    X-coordinate of line start.
 * \param dwY1    Y-coordinate of line start.
 * \param dwX2    X-coordinate of line end.
 * \param dwY2    Y-coordinate of line end.
 * \param color   pixel color.
 */
uint32_t LCDD_DrawLineBresenham(uint16_t* pCanvasBuffer, uint32_t dwX1, 
				uint32_t dwY1, uint32_t dwX2, uint32_t dwY2 , uint32_t color)
{
	int dx, dy;
	int i;
	int xinc, yinc, cumul;
	int x, y;

	x = dwX1;
	y = dwY1;
	dx = dwX2 - dwX1;
	dy = dwY2 - dwY1;

	xinc = ( dx > 0 ) ? 1 : -1;
	yinc = ( dy > 0 ) ? 1 : -1;
	dx = ( dx > 0 ) ? dx : -dx;
	dy = ( dy > 0 ) ? dy : -dy;

	LCDD_DrawPixel(pCanvasBuffer, x , y , color);

	if ( dx > dy ) {
		cumul = dx / 2;
		for ( i = 1; i <= dx; i++ ) {
			x += xinc;
			cumul += dy;

			if ( cumul >= dx ) {
				cumul -= dx;
				y += yinc;
			}
			LCDD_DrawPixel(pCanvasBuffer, x , y , color);
		}
	} else {
		cumul = dy / 2;
		for ( i = 1; i <= dy; i++ ) {
			y += yinc;
			cumul += dx;

			if ( cumul >= dy ) {
				cumul -= dy;
				x += xinc;
			}
			LCDD_DrawPixel(pCanvasBuffer, x , y , color);
		}
	}

	return 0;
}

/*
 * \brief Draws a rectangle on LCD, at the given coordinates.
 *
 * \param pCanvasBuffer Pointer to dedicate canvas buffer.
 * \param x      X-coordinate of upper-left rectangle corner.
 * \param y      Y-coordinate of upper-left rectangle corner.
 * \param width  Rectangle width in pixels.
 * \param height Rectangle height in pixels.
 * \param color  Rectangle color.
 */
void LCDD_DrawRectangle(uint16_t* pCanvasBuffer, uint32_t x, uint32_t y, 
					uint32_t width, uint32_t height, uint32_t color )
{
	LCDD_DrawRectangleWithFill(pCanvasBuffer, x, y, width, 1, color);
	LCDD_DrawRectangleWithFill(pCanvasBuffer, x, y, 1, height, color);

	LCDD_DrawRectangleWithFill(pCanvasBuffer, x + width , y, 1, height, color);
	LCDD_DrawRectangleWithFill(pCanvasBuffer, x, y + height, width, 1, color);
}

/*
 * \brief Set buffer for pCanvas.
 *
 * \param pCanvasBuffer  Pointer of external buffer.
 * \param wBufferSize   Size of buffer.
 */
void LCDD_SetCavasBuffer( void* pCanvasBuffer, uint32_t wBufferSize)
{
	if (ili9488_lcdMode == ILI9488_SPIMODE) {
		gpCanvasBuffer = (sBGR*)pCanvasBuffer;
		gwCanvasBufferSize = wBufferSize;
	} else {
		gpCanvasBuffer = (uint16_t*)pCanvasBuffer;
		gwCanvasBufferSize = wBufferSize;
	}
}


