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

/** \addtogroup lcdd_draw
 *
 * Implementation of draw function on LCD, Include draw text, image
 * and basic shapes (line, rectangle, circle).
 *
 */

/** \file */

/*----------------------------------------------------------------------------
 *        Headers
 *----------------------------------------------------------------------------*/

#include "board.h"

#include "video/lcdd.h"

#include "lcd_draw.h"
#include "lcd_font.h"
#include "font.h"

#include <string.h>
#include <stdlib.h>
#include <assert.h>

/*----------------------------------------------------------------------------
 *        Local variable
 *----------------------------------------------------------------------------*/

/** Front color cache */
static uint32_t front_color;

/*----------------------------------------------------------------------------
 *        Local functions
 *----------------------------------------------------------------------------*/

/**
 * Hide canvas layer
 */
static void _hide_canvas(void)
{
	//lcdd_enable_layer(lcdd_get_canvas()->layer_id, false);
}

/**
 * Update canvas
 */
static void _show_canvas(void)
{
	//lcdd_enable_layer(lcdd_get_canvas()->layer_id, true);
}

/**
 * Set front color
 * \param color Pixel color.
 */
static void _set_front_color(uint32_t color)
{
	front_color = color;
}

/**
 * \brief Draw a pixel on LCD of front color.
 *
 * \param dwX       X-coordinate of pixel.
 * \param dwY       Y-coordinate of pixel.
 */
static void _draw_pixel(uint32_t dwX, uint32_t dwY)
{
	struct _lcdd_layer *pDisp = lcdd_get_canvas();
	uint8_t *buffer = pDisp->buffer;
	uint16_t w = pDisp->width;
	//uint16_t h = pDisp->height;
	uint16_t cw = pDisp->bpp / 8;	/* color width */
	uint32_t rw = w * cw;	/* row width in bytes */
	//uint8_t  r, g, b;
	uint8_t *pPix;

	if (buffer == NULL)
		return;

	if (rw & 0x3)
		rw = (rw | 0x3) + 1;	/* 4-byte aligned rows */
	pPix = &buffer[dwY * rw + cw * dwX];

	switch (pDisp->bpp) {
	case 16:		/* TRGB 1555 */
		pPix[0] = (front_color) & 0xFF;
		pPix[1] = (front_color >> 8) & 0xFF;
		break;
	case 24:		/*  RGB  888 */
		pPix[0] = (front_color) & 0xFF;
		pPix[1] = (front_color >> 8) & 0xFF;
		pPix[2] = (front_color >> 16) & 0xFF;
		break;
	case 32:		/* ARGB 8888 */
		pPix[0] = (front_color) & 0xFF;
		pPix[1] = (front_color >> 8) & 0xFF;
		pPix[2] = (front_color >> 16) & 0xFF;
		pPix[3] = (front_color >> 24) & 0xFF;
		break;
	}
}

/**
 * \brief Fill rectangle with front color.
 * \param dwX1  X-coordinate of top left.
 * \param dwY1  Y-coordinate of top left.
 * \param dwX2  X-coordinate of bottom right.
 * \param dwY1  Y-coordinate of bottom right.
 */
static void _fill_rect(uint32_t dwX1, uint32_t dwY1, uint32_t dwX2, uint32_t dwY2)
{
	struct _lcdd_layer *pDisp = lcdd_get_canvas();
	uint16_t w = pDisp->width;
	uint16_t cw = pDisp->bpp / 8;	/* color width */
	uint32_t rw = w * cw;	/* row width in bytes */
	uint8_t *base = pDisp->buffer;
	uint8_t *buffer = pDisp->buffer;
	uint32_t fillStart, fillEnd;
	uint32_t i;
	if (buffer == NULL)
		return;

	/* 4-byte aligned rows */
	if (rw & 0x3)
		rw = (rw | 0x3) + 1;
	/* Buffer address for the starting row */
	base = &buffer[dwY1 * rw];

	fillStart = dwX1 * cw;
	fillEnd = dwX2 * cw;

#if 1				/* Memcopy pixel */
	buffer = base;
	for (; dwY1 <= dwY2; dwY1++) {
		for (i = fillStart; i <= fillEnd; i += cw) {
			memcpy(&buffer[i], &front_color, cw);
		}
		buffer = &buffer[rw];
	}
#endif

#if 0				/* Pixel by pixel */
	for (; dwY1 <= dwY2; dwY1++) {
		for (i = dwX1; i <= dwX2; i++) {
			_draw_pixel(i, dwY1);
		}
	}
#endif

#if 0				/* Optimized */
	/* First row */
	for (i = fillStart; i <= fillEnd; i += cw) {
		memcpy(&base[i], &front_color, cw);
	}
	/* Next rows, copy first */
	buffer = &base[rw + fillStart];
	for (i = dwY1 + 1; i <= dwY2; i++) {
		memcpy(buffer, &base[fillStart], fillEnd - fillStart + cw);
		buffer = &buffer[rw];
	}
#endif
}

/**
 * \brief Draw a line on LCD, which is not horizontal or vertical.
 *
 * \param dwX1       X-coordinate of line start.
 * \param dwY1       Y-coordinate of line start.
 * \param dwX2       X-coordinate of line end.
 * \param dwY2       Y-coordinate of line end.
 */

/*
static uint32_t _draw_line_bresenham (uint32_t dwX1, uint32_t dwY1, uint32_t dwX2, uint32_t dwY2)
{
	int dx, dy;
	int i;
	int xinc, yinc, cumul;
	int x, y;

	x = dwX1;
	y = dwY1;
	dx = dwX2 - dwX1;
	dy = dwY2 - dwY1;

	xinc = (dx > 0) ? 1 : -1;
	yinc = (dy > 0) ? 1 : -1;
	dx = (dx > 0) ? dx : -dx;
	dy = (dy > 0) ? dy : -dy;

	_draw_pixel(x, y);

	if (dx > dy) {
		cumul = dx / 2;
		for (i = 1; i <= dx; i++) {
			x += xinc;
			cumul += dy;

			if (cumul >= dx) {
				cumul -= dx;
				y += yinc;
			}
			_draw_pixel(x, y);
		}
	} else {
		cumul = dy / 2;
		for (i = 1; i <= dy; i++) {
			y += yinc;
			cumul += dx;

			if (cumul >= dy) {
				cumul -= dy;
				x += xinc;
			}

			_draw_pixel(x, y);
		}
	}

	return 0;
}
*/

static uint32_t _draw_line_bresenham (uint32_t dwX1, uint32_t dwY1, uint32_t dwX2, uint32_t dwY2)
{
    int dx = abs(dwX2 - dwX1);
    int dy = abs(dwY2 - dwY1);
    int sx = (dwX1 < dwX2) ? 1 : -1;
    int sy = (dwY1 < dwY2) ? 1 : -1;
    int err = dx - dy;
    int e2 ;

    while (1) {
      _draw_pixel(dwX1, dwY1);
      if ((dwX1 == dwX2) && (dwY1 == dwY2))
        break;
      e2 = 2 * err;
	  if (e2 > -dy) {
		  err -= dy; dwX1 += sx;
	  }
      if (e2 < dx) {
		  err += dx; dwY1 += sy;
	  }
    }
	return 0;
}

/*----------------------------------------------------------------------------
 *        Exported functions
 *----------------------------------------------------------------------------*/

/**
 * \brief Fills the given LCD buffer with a particular color.
 *
 * \param color  Fill color.
 */
void lcdd_fill(uint32_t color)
{
	struct _lcdd_layer *pDisp = lcdd_get_canvas();
	_set_front_color(color);
	_hide_canvas();
	_fill_rect(0, 0, pDisp->width, pDisp->height);
	_show_canvas();
}

void lcdd_fill_white(void)
{
	struct _lcdd_layer *pDisp = lcdd_get_canvas();
	_hide_canvas();
	_set_front_color(0x0000FF);
	_fill_rect(0, 0, pDisp->width / 3, pDisp->height);
	_set_front_color(0xFFFFFF);
	_fill_rect(pDisp->width/3, 0, pDisp->width/3+pDisp->width/3, pDisp->height);
	_set_front_color(0xFF0000);
	_fill_rect(pDisp->width/3+pDisp->width/3, 0, pDisp->width-1, pDisp->height);
	_show_canvas();
}

/**
 * \brief Draw a pixel on LCD of given color.
 *
 * \param x  X-coordinate of pixel.
 * \param y  Y-coordinate of pixel.
 * \param color  Pixel color.
 */
void lcdd_draw_pixel(uint32_t x, uint32_t y, uint32_t color)
{
	_set_front_color(color);
	_hide_canvas();
	_draw_pixel(x, y);
	_show_canvas();
}

/**
 * \brief Read a pixel from LCD.
 *
 * \param x  X-coordinate of pixel.
 * \param y  Y-coordinate of pixel.
 *
 * \return color  Readed pixel color.
 */
extern uint32_t lcdd_read_pixel(uint32_t x, uint32_t y)
{
	struct _lcdd_layer *pDisp = lcdd_get_canvas();
	uint8_t *buffer = pDisp->buffer;
	uint16_t w = pDisp->width;
	//uint16_t h = pDisp->height;
	uint16_t cw = pDisp->bpp / 8;	/* color width */
	uint32_t rw = w * cw;	/* row width in bytes */
	uint8_t *pPix;
	uint32_t color = 0;

	if (buffer == NULL)
		return 0;

	if (rw & 0x3)
		rw = (rw | 0x3) + 1;	/* 4-byte aligned rows */
	pPix = &buffer[x * rw + cw * y];

	switch (pDisp->bpp) {
	case 16:		/* TRGB 1555 */
		color = pPix[0] | (pPix[1] << 8);
		break;
	case 24:		/*  RGB  888 */
		color = pPix[0] | (pPix[1] << 8) | (pPix[2] << 16);
		break;
	case 32:		/* ARGB 8888 */
		color =
			pPix[0] | (pPix[1] << 8) | (pPix[2] << 16) | (pPix[3] <<
								      24);
		break;
	}
	return color;
}

/**
 * \brief Draw a line on LCD, horizontal and vertical line are supported.
 *
 * \param x1        X-coordinate of line start.
 * \param y1        Y-coordinate of line start.
 * \param x2        X-coordinate of line end.
 * \param y2        Y-coordinate of line end.
 * \param color     Pixel color.
 */
void lcdd_draw_line(uint32_t x1, uint32_t y1, uint32_t x2, uint32_t y2,
		    uint32_t color)
{
	_set_front_color(color);

	if ((x1 == x2) && (y1 > y2)) {
		SWAP(y1, y2);
	}
	if ((x1 > x2) & (y1 == y2)) {
		SWAP(x1, x2);
	}

	if ((x1 == x2) || (y1 == y2)) {
		lcdd_draw_filled_rectangle(x1, y1, x2, y2, color);
	} else {
		_hide_canvas();
		_draw_line_bresenham(x1, y1, x2, y2);
		_show_canvas();
	}
}

/**
 * \brief Draws a rectangle on LCD, at the given coordinates.
 *
 * \param x      X-coordinate of upper-left rectangle corner.
 * \param y      Y-coordinate of upper-left rectangle corner.
 * \param width  Rectangle width in pixels.
 * \param height  Rectangle height in pixels.
 * \param color  Rectangle color.
 */
void lcdd_draw_rectangle(uint32_t x, uint32_t y, uint32_t width, uint32_t height,
			 uint32_t color)
{
	uint32_t x1 = x + width - 1;
	uint32_t y1 = y + height - 1;

	_set_front_color(color);
	_hide_canvas();
	_fill_rect(x, y, x1, y);
	_fill_rect(x1, y, x1, y1);
	_fill_rect(x, y, x, y1);
	_fill_rect(x, y1, x1, y1);
	_show_canvas();
}

/**
 * \brief Draws a rectangle with fill inside on LCD, at the given coordinates.
 *
 * \param dwX1   X-coordinate of upper-left rectangle corner.
 * \param dwY1   Y-coordinate of upper-left rectangle corner.
 * \param dwX2   X-coordinate of down-right rectangle corner.
 * \param dwY2   Y-coordinate of down-right rectangle corner.
 * \param color Rectangle color.
 */
void lcdd_draw_filled_rectangle(uint32_t dwX1, uint32_t dwY1,
				uint32_t dwX2, uint32_t dwY2, uint32_t color)
{
	_set_front_color(color);
	_hide_canvas();
	_fill_rect(dwX1, dwY1, dwX2, dwY2);
	_show_canvas();
}

/**
 * \brief Draws a circle on LCD, at the given coordinates.
 *
 * \param dwX     X-coordinate of circle center.
 * \param dwY     Y-coordinate of circle center.
 * \param dwR     circle radius.
 * \param color circle color.
 */
void lcdd_draw_circle(uint32_t dwX, uint32_t dwY, uint32_t dwR, uint32_t color)
{
	int32_t d;		/* Decision Variable */
	uint32_t curX;		/* Current X Value */
	uint32_t curY;		/* Current Y Value */

	if (dwR == 0)
		return;
	_set_front_color(color);

	d = 3 - (dwR << 1);
	curX = 0;
	curY = dwR;

	_hide_canvas();
	while (curX <= curY) {
		_draw_pixel(dwX + curX, dwY + curY);
		_draw_pixel(dwX + curX, dwY - curY);
		_draw_pixel(dwX - curX, dwY + curY);
		_draw_pixel(dwX - curX, dwY - curY);
		_draw_pixel(dwX + curY, dwY + curX);
		_draw_pixel(dwX + curY, dwY - curX);
		_draw_pixel(dwX - curY, dwY + curX);
		_draw_pixel(dwX - curY, dwY - curX);

		if (d < 0) {
			d += (curX << 2) + 6;
		} else {
			d += ((curX - curY) << 2) + 10;
			curY--;
		}
		curX++;
	}
	_show_canvas();
}

/**
 * \brief Draws a filled circle on LCD, at the given coordinates.
 *
 * \param dwX     X-coordinate of circle center.
 * \param dwY     Y-coordinate of circle center.
 * \param dwR     circle radius.
 * \param color circle color.
 */
void lcdd_draw_filled_circle(uint32_t dwX, uint32_t dwY, uint32_t dwR,
			     uint32_t color)
{
	signed int d;		// Decision Variable
	uint32_t dwCurX;	// Current X Value
	uint32_t dwCurY;	// Current Y Value
	uint32_t dwXmin, dwYmin;

	if (dwR == 0)
		return;
	_set_front_color(color);

	d = 3 - (dwR << 1);
	dwCurX = 0;
	dwCurY = dwR;

	_hide_canvas();
	while (dwCurX <= dwCurY) {
		dwXmin = (dwCurX > dwX) ? 0 : dwX - dwCurX;
		dwYmin = (dwCurY > dwY) ? 0 : dwY - dwCurY;
		_fill_rect(dwXmin, dwYmin, dwX + dwCurX, dwYmin);
		_fill_rect(dwXmin, dwY + dwCurY, dwX + dwCurX, dwY + dwCurY);
		dwXmin = (dwCurY > dwX) ? 0 : dwX - dwCurY;
		dwYmin = (dwCurX > dwY) ? 0 : dwY - dwCurX;
		_fill_rect(dwXmin, dwYmin, dwX + dwCurY, dwYmin);
		_fill_rect(dwXmin, dwY + dwCurX, dwX + dwCurY, dwY + dwCurX);

		if (d < 0) {
			d += (dwCurX << 2) + 6;
		} else {
			d += ((dwCurX - dwCurY) << 2) + 10;
			dwCurY--;
		}

		dwCurX++;
	}
	_show_canvas();
}

/**
 * \brief Draws a string inside a LCD buffer, at the given coordinates. Line breaks
 * will be honored.
 *
 * \param x        X-coordinate of string top-left corner.
 * \param y        Y-coordinate of string top-left corner.
 * \param p_string  String to display.
 * \param color    String color.
 */
void lcdd_draw_string(uint32_t x, uint32_t y, const char *p_string, uint32_t color)
{
	uint32_t xorg = x;
	uint8_t font_sel = lcdd_get_selected_font();
	uint8_t width = font_param[font_sel].width ;
	uint8_t height = font_param[font_sel].height;
	uint8_t char_space = font_param[font_sel].char_space;

	/* Font 10*8 reverse height and width */
	if (font_sel == FONT10x8) {
		width = font_param[font_sel].height ;
		height = font_param[font_sel].width;
	}

	while (*p_string) {
		if (*p_string == '\n') {
			y += height + char_space;
			x = xorg;
		} else {
			lcdd_draw_char(x, y, *p_string, color);
			x += width + char_space;
		}
		p_string++;
	}
}

/**
 * \brief Draws a string inside a LCD buffer, at the given coordinates
 * with given background color. Line breaks will be honored.
 *
 * \param x         X-coordinate of string top-left corner.
 * \param y         Y-coordinate of string top-left corner.
 * \param p_string  String to display.
 * \param fontColor String color.
 * \param bgColor   Background color.
 */
void lcdd_draw_string_with_bgcolor(uint32_t x, uint32_t y,
								   const char *p_string,
								   uint32_t fontColor,
								   uint32_t bgColor)
{
	uint32_t xorg = x;
	uint8_t font_sel = lcdd_get_selected_font();
	uint8_t width = font_param[font_sel].width ;
	uint8_t height = font_param[font_sel].height;
	uint8_t char_space = font_param[font_sel].char_space;

	/* Font 10*8 reverse height and width */
	if (font_sel == FONT10x8) {
		width = font_param[font_sel].height ;
		height = font_param[font_sel].width;
	}

	while (*p_string) {
		if (*p_string == '\n') {
			y += height + char_space;;
			x = xorg;
		} else {
			lcdd_draw_char_with_bgcolor(x, y, *p_string, fontColor, bgColor);
			x += width + char_space;;
		}
		p_string++;
	}
}

/**
 * \brief Returns the width & height in pixels that a string will occupy on the screen
 * if drawn using lcdd_draw_string.
 *
 * \param p_string  String.
 * \param p_width   Pointer for storing the string width (optional).
 * \param p_height  Pointer for storing the string height (optional).
 *
 * \return String width in pixels.
 */
void lcdd_get_string_size(const char *p_string, uint32_t * p_width, uint32_t * p_height)
{
	uint8_t font_sel = lcdd_get_selected_font();
	uint8_t width = font_param[font_sel].width;
	uint8_t height = font_param[font_sel].height;
	uint8_t char_space = font_param[font_sel].char_space;
	uint32_t str_width = 0;

	/* Font 10*8 reverse height and width */
	if (font_sel == FONT10x8) {
		width = font_param[font_sel].height ;
		height = font_param[font_sel].width;
	}

	while (*p_string) {
		if (*p_string == '\n')
			height += height + char_space;
		else
			str_width += width + char_space;
		p_string++;
	}
	if (width > 0)
		str_width -= char_space;

	if (p_width != NULL)
		*p_width = str_width;
	if (p_height != NULL)
		*p_height = height;
}

/**
 * \brief Draw a raw image at given position on LCD.
 *
 * \param dwX       X-coordinate of image start.
 * \param dwY       Y-coordinate of image start.
 * \param pImage    Image buffer.
 * \param width     Image width.
 * \param height    Image height.
 */
void lcdd_draw_image(uint32_t dwX, uint32_t dwY, const uint8_t * pImage,
		     uint32_t width, uint32_t height)
{
	struct _lcdd_layer *pDisp = lcdd_get_canvas();
	uint16_t cw = pDisp->bpp / 8;	/* color width */
	uint32_t rw = pDisp->width * cw;	/* Row width in bytes */
	uint32_t rws = width * cw;	/* Source Row Width */
	uint32_t rl = (rw & 0x3) ? ((rw | 0x3) + 1) : rw;	/* Aligned length */
	uint32_t rls = (rws & 0x3) ? ((rws | 0x3) + 1) : rws;	/* Aligned length */
	uint8_t *pSrc, *pDst;
	uint32_t i;

	pSrc = (uint8_t *) pImage;
	pDst = pDisp->buffer;
	pDst = &pDst[dwX * cw + dwY * rl];

	for (i = 0; i < height; i++) {
		memcpy(pDst, pSrc, rws);
		pSrc = &pSrc[rls];
		pDst = &pDst[rl];
	}
}

/**
 * \brief Clear a window with an color.
 *
 * \param dwX         X-coordinate of the window.
 * \param dwY         Y-coordinate of the window.
 * \param width     window width.
 * \param height    window height.
 * \param color     background color
 */
void lcdd_clear_window(uint32_t dwX, uint32_t dwY, uint32_t width,
		       uint32_t height, uint32_t color)
{
	_set_front_color(color);
	_hide_canvas();
	_fill_rect(0, 0, dwX + width - 1, dwY + height - 1);
	_show_canvas();
}

/*----------------------------------------------------------------------------
 *        Local functions
 *----------------------------------------------------------------------------*/

/**
 * Draw fast vertical line
 */
void lcdd_draw_fast_vline (uint32_t x, uint32_t y, uint32_t h, uint32_t color)
{
	lcdd_draw_line(x, y, x, y+h-1, color);
}
/**
 * Draw fast horizontal line
 */
void lcdd_draw_fast_hline (uint32_t x, uint32_t y, uint32_t w, uint32_t color)
{
	lcdd_draw_line(x, y, x+w-1, y, color);
}
/**
 * Fill rectangle with color
 */
static void _lcdd_fill_rectangle (uint32_t x, uint32_t y, uint32_t w, uint32_t h, uint32_t color)
{
	uint32_t i;
	for (i=x; i<x+w; i++) lcdd_draw_fast_vline(i, y, h, color);
}
/**
 * Draw a circle
 */
static void _lcdd_draw_circle (uint32_t x0, uint32_t y0, uint32_t r, uint8_t corner, uint32_t color)
{
	int32_t f = 1 - r;
	int32_t ddF_x = 1;
	int32_t ddF_y = -2 * (int32_t)r;
	int32_t x = 0;
	int32_t y = r;

	while (x<y) {
		if (f >= 0)
		{
			y--;
			ddF_y += 2;
			f     += ddF_y;
		}
		x++;
		ddF_x += 2;
		f     += ddF_x;
		if (corner & 0x4) {
			_draw_pixel(x0 + x, y0 + y);
			_draw_pixel(x0 + y, y0 + x);
		}
		if (corner & 0x2) {
			_draw_pixel(x0 + x, y0 - y);
			_draw_pixel(x0 + y, y0 - x);
		}
		if (corner & 0x8) {
			_draw_pixel(x0 - y, y0 + x);
			_draw_pixel(x0 - x, y0 + y);
		}
		if (corner & 0x1) {
			_draw_pixel(x0 - y, y0 - x);
			_draw_pixel(x0 - x, y0 - y);
		}
	}
}
/**
 * Fill a circle
 */
static void _lcdd_fill_circle (uint32_t x0, uint32_t y0, uint32_t r, uint8_t corner, uint32_t delta, uint32_t color)
{
	int32_t f = 1 - r;
	int32_t ddF_x = 1;
	int32_t ddF_y = -2 * (int32_t)r;
	int32_t x = 0;
	int32_t y = r;

	while (x<y) {
		if (f >= 0) {
			y--;
			ddF_y += 2;
			f += ddF_y;
		}
		x++;
		ddF_x += 2;
		f += ddF_x;

		if (corner & 0x1) {
			lcdd_draw_fast_vline(x0+x, y0-y, 2*y+1+delta, color);
			lcdd_draw_fast_vline(x0+y, y0-x, 2*x+1+delta, color);
		}
		if (corner & 0x2) {
			lcdd_draw_fast_vline(x0-x, y0-y, 2*y+1+delta, color);
			lcdd_draw_fast_vline(x0-y, y0-x, 2*x+1+delta, color);
		}
	}
}

/*----------------------------------------------------------------------------
 *        Global functions
 *----------------------------------------------------------------------------*/

/**
 * Draw a rectangle with rounded corners
 */
void lcdd_draw_rounded_rect (uint32_t x, uint32_t y, uint32_t w, uint32_t h, uint32_t r, uint32_t color)
{
	_set_front_color(color);
	_hide_canvas();
	// smarter version
	lcdd_draw_fast_hline(x+r, y, w-2*r, color); // Top
	lcdd_draw_fast_hline(x+r, y+h-1, w-2*r, color); // Bottom
	lcdd_draw_fast_vline(x, y+r, h-2*r, color); // Left
	lcdd_draw_fast_vline(x+w-1, y+r, h-2*r, color); // Right
	// draw four corners
	_lcdd_draw_circle(x+r, y+r, r, 1, color);
	_lcdd_draw_circle(x+w-r-1, y+r, r, 2, color);
	_lcdd_draw_circle(x+w-r-1, y+h-r-1, r, 4, color);
	_lcdd_draw_circle(x+r, y+h-r-1, r, 8, color);
	_show_canvas();
}
/**
 * Fill a rectangle with rounded corners
 */
void lcdd_fill_rounded_rect(uint32_t x, uint32_t y, uint32_t w, uint32_t h, uint32_t r, uint32_t color)
{
	_set_front_color(color);
	_hide_canvas();
	if (w>(2*r)) {
		_lcdd_fill_rectangle(x+r, y, w-(2*r), h, color);
		// draw four corners
		_lcdd_fill_circle(x+w-r-1, y+r, r, 1, h-2*r-1, color);
		_lcdd_fill_circle(x+r, y+r, r, 2, h-2*r-1, color);
	}
	_show_canvas();
}
