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

#include <stdint.h>
#include <string.h>
#include <assert.h>

/*----------------------------------------------------------------------------
 *        Local variable
 *----------------------------------------------------------------------------*/

/** Front color cache */
static uint32_t dwFrontColor;

/*----------------------------------------------------------------------------
 *        Local functions
 *----------------------------------------------------------------------------*/

/**
 * Hide canvas layer
 */
static void _HideCanvas(void)
{
    //LCDD_EnableLayer(LCDD_GetCanvas()->bLayer, 0);
}

/**
 * Update canvas
 */
static void _ShowCanvas(void)
{
    //LCDD_EnableLayer(LCDD_GetCanvas()->bLayer, 1);
}

/**
 * Set front color
 * \param dwColor Pixel color.
 */
static void _SetFrontColor(uint32_t dwColor)
{
    dwFrontColor = dwColor;
}

/**
 * \brief Draw a pixel on LCD of front color.
 *
 * \param dwX       X-coordinate of pixel.
 * \param dwY       Y-coordinate of pixel.
 */
static void _DrawPixel( uint32_t dwX, uint32_t dwY )
{
    sLCDDLayer *pDisp = LCDD_GetCanvas();
    uint8_t* buffer = pDisp->pBuffer;
    uint16_t w = pDisp->wImgW;
    //uint16_t h = pDisp->wImgH;
    uint16_t cw = pDisp->bMode/8; /* color width */
    uint32_t rw = w * cw;         /* row width in bytes */
    //uint8_t  r, g, b;
    uint8_t  *pPix;

    if (buffer == NULL)
        return;

    if (rw & 0x3) rw = (rw | 0x3) + 1; /* 4-byte aligned rows */
    pPix = &buffer[dwY * rw + cw * dwX];

    switch (pDisp->bMode)
    {
        case 16: /* TRGB 1555 */
            pPix[0] = (dwFrontColor      ) & 0xFF;
            pPix[1] = (dwFrontColor >>  8) & 0xFF;
            break;
        case 24: /*  RGB  888 */
            pPix[0] = (dwFrontColor      ) & 0xFF;
            pPix[1] = (dwFrontColor >>  8) & 0xFF;
            pPix[2] = (dwFrontColor >> 16) & 0xFF;
            break;
        case 32: /* ARGB 8888 */
            pPix[0] = (dwFrontColor      ) & 0xFF;
            pPix[1] = (dwFrontColor >>  8) & 0xFF;
            pPix[2] = (dwFrontColor >> 16) & 0xFF;
            pPix[3] = (dwFrontColor >> 24) & 0xFF;
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
static void _FillRect( uint32_t dwX1, uint32_t dwY1, uint32_t dwX2, uint32_t dwY2 )
{
    sLCDDLayer *pDisp = LCDD_GetCanvas();
    uint16_t w = pDisp->wImgW;
    uint16_t cw = pDisp->bMode/8; /* color width */
    uint32_t rw = w * cw;         /* row width in bytes */
    uint8_t *base = pDisp->pBuffer;
    uint8_t *buffer = pDisp->pBuffer;
    uint32_t fillStart, fillEnd;
    uint32_t i;
    if (buffer == NULL) return;

    /* 4-byte aligned rows */
    if (rw & 0x3) rw = (rw | 0x3) + 1;
    /* Buffer address for the starting row */
    base = &buffer[dwY1*rw];

    fillStart = dwX1 * cw;
    fillEnd   = dwX2 * cw;

    #if 1 /* Memcopy pixel */
    buffer = base;
    for (; dwY1 <= dwY2; dwY1 ++)
    {
        for (i = fillStart; i <= fillEnd; i += cw)
        {
            memcpy(&buffer[i], &dwFrontColor, cw);
        }
        buffer = &buffer[rw]; 
    }
    #endif

    #if 0 /* Pixel by pixel */
    for (; dwY1 <= dwY2; dwY1 ++)
    {
        for (i = dwX1; i <= dwX2; i ++)
        {
            _DrawPixel(i, dwY1);
        }
    }
    #endif

    #if 0 /* Optimized */
    /* First row */
    for (i = fillStart; i <= fillEnd; i += cw)
    {
        memcpy(&base[i], &dwFrontColor, cw);
    }
    /* Next rows, copy first */
    buffer = &base[rw + fillStart];
    for (i = dwY1 + 1; i <= dwY2; i ++)
    {
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
static uint32_t _DrawLineBresenham( uint32_t dwX1, uint32_t dwY1,
                                    uint32_t dwX2, uint32_t dwY2 )
{
    int dx, dy ;
    int i ;
    int xinc, yinc, cumul ;
    int x, y ;

    x = dwX1 ;
    y = dwY1 ;
    dx = dwX2 - dwX1 ;
    dy = dwY2 - dwY1 ;

    xinc = ( dx > 0 ) ? 1 : -1 ;
    yinc = ( dy > 0 ) ? 1 : -1 ;
    dx = ( dx > 0 ) ? dx : -dx ;
    dy = ( dy > 0 ) ? dy : -dy ;

    _DrawPixel( x, y ) ;

    if ( dx > dy )
    {
      cumul = dx / 2 ;
      for ( i = 1 ; i <= dx ; i++ )
      {
        x += xinc ;
        cumul += dy ;

        if ( cumul >= dx )
        {
          cumul -= dx ;
          y += yinc ;
        }
        _DrawPixel( x, y ) ;
      }
    }
    else
    {
        cumul = dy / 2 ;
        for ( i = 1 ; i <= dy ; i++ )
        {
            y += yinc ;
            cumul += dx ;

            if ( cumul >= dy )
            {
                cumul -= dy ;
                x += xinc ;
            }

            _DrawPixel( x, y ) ;
        }
    }

    return 0 ;
}



/*----------------------------------------------------------------------------
 *        Exported functions
 *----------------------------------------------------------------------------*/

/**
 * \brief Fills the given LCD buffer with a particular color.
 *
 * \param color  Fill color.
 */
void LCDD_Fill( uint32_t dwColor )
{
    sLCDDLayer *pDisp = LCDD_GetCanvas();
    _SetFrontColor(dwColor);
    _HideCanvas();
    _FillRect( 0, 0, pDisp->wImgW, pDisp->wImgH );
    _ShowCanvas();
}

void LCDD_Fill0(void)
{
    sLCDDLayer *pDisp = LCDD_GetCanvas();    
    _HideCanvas();
    _SetFrontColor(0xFF0000);
    _FillRect( 0, 0, pDisp->wImgW/3, pDisp->wImgH );
    _SetFrontColor(0x00FF00);
    _FillRect( pDisp->wImgW/3, 0, pDisp->wImgW/3+pDisp->wImgW/3, pDisp->wImgH );
    _SetFrontColor(0x0000FF);
    _FillRect( pDisp->wImgW/3+pDisp->wImgW/3, 0, pDisp->wImgW, pDisp->wImgH );
    _ShowCanvas();
}
/**
 * \brief Draw a pixel on LCD of given color.
 *
 * \param x  X-coordinate of pixel.
 * \param y  Y-coordinate of pixel.
 * \param color  Pixel color.
 */
extern void LCDD_DrawPixel( uint32_t x, uint32_t y, uint32_t color )
{
    _SetFrontColor(color);
    _HideCanvas();
    _DrawPixel(x, y);
    _ShowCanvas();
}

/**
 * \brief Read a pixel from LCD.
 *
 * \param x  X-coordinate of pixel.
 * \param y  Y-coordinate of pixel.
 *
 * \return color  Readed pixel color.
 */
extern uint32_t LCDD_ReadPixel( uint32_t x, uint32_t y )
{
    sLCDDLayer *pDisp = LCDD_GetCanvas();
    uint8_t* buffer = pDisp->pBuffer;
    uint16_t w = pDisp->wImgW;
    //uint16_t h = pDisp->wImgH;
    uint16_t cw = pDisp->bMode/8; /* color width */
    uint32_t rw = w * cw;         /* row width in bytes */
    uint8_t  *pPix;
    uint32_t color = 0;

    if (buffer == NULL) return 0;

    if (rw & 0x3) rw = (rw | 0x3) + 1; /* 4-byte aligned rows */
    pPix = &buffer[x * rw + cw * y];

    switch (pDisp->bMode)
    {
        case 16: /* TRGB 1555 */
            color = pPix[0] | (pPix[1] << 8);
            break;
        case 24: /*  RGB  888 */
            color = pPix[0] | (pPix[1] << 8) | (pPix[2] << 16);
            break;
        case 32: /* ARGB 8888 */
            color = pPix[0] | (pPix[1] << 8) | (pPix[2] << 16) | (pPix[3] << 24);
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
extern void LCDD_DrawLine( uint32_t x1, uint32_t y1, uint32_t x2, uint32_t y2, uint32_t color )
{
    _SetFrontColor(color);
    if ( (x1 == x2) || (y1 == y2) )
    {
        LCDD_DrawFilledRectangle(x1, y1, x2, y2, color);
    }
    else
    {
        _HideCanvas();
        _DrawLineBresenham(x1, y1, x2, y2);
        _ShowCanvas();
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
extern void LCDD_DrawRectangle( uint32_t x, uint32_t y, uint32_t width, uint32_t height, uint32_t color )
{
    uint32_t x1 = x + width - 1;
    uint32_t y1 = y + height - 1;

    _SetFrontColor(color);
    _HideCanvas();
    _FillRect(x , y , x1, y );
    _FillRect(x1, y , x1, y1);
    _FillRect(x , y , x , y1);
    _FillRect(x , y1, x1, y1);
    _ShowCanvas();
}

/**
 * \brief Draws a rectangle with fill inside on LCD, at the given coordinates.
 *
 * \param dwX1   X-coordinate of upper-left rectangle corner.
 * \param dwY1   Y-coordinate of upper-left rectangle corner.
 * \param dwX2   X-coordinate of down-right rectangle corner.
 * \param dwY2   Y-coordinate of down-right rectangle corner.
 * \param color  Rectangle color.
 */
extern void LCDD_DrawFilledRectangle( uint32_t dwX1, uint32_t dwY1,
                                      uint32_t dwX2, uint32_t dwY2,
                                      uint32_t dwColor )
{
    _SetFrontColor(dwColor);
    _HideCanvas();
    _FillRect(dwX1, dwY1, dwX2, dwY2);
    _ShowCanvas();
}

/**
 * \brief Draws a circle on LCD, at the given coordinates.
 *
 * \param dwX     X-coordinate of circle center.
 * \param dwY     Y-coordinate of circle center.
 * \param dwR     circle radius.
 * \param dwColor circle color.
 */
extern void LCDD_DrawCircle( uint32_t dwX, uint32_t dwY, uint32_t dwR, uint32_t dwColor )
{
    int32_t   d;    /* Decision Variable */
    uint32_t  curX; /* Current X Value */
    uint32_t  curY; /* Current Y Value */

   if (dwR == 0) return;
   _SetFrontColor(dwColor);

   d = 3 - (dwR << 1);
   curX = 0;
   curY = dwR;

   _HideCanvas();
   while (curX <= curY)
   {
       _DrawPixel(dwX + curX, dwY + curY);
       _DrawPixel(dwX + curX, dwY - curY);
       _DrawPixel(dwX - curX, dwY + curY);
       _DrawPixel(dwX - curX, dwY - curY);
       _DrawPixel(dwX + curY, dwY + curX);
       _DrawPixel(dwX + curY, dwY - curX);
       _DrawPixel(dwX - curY, dwY + curX);
       _DrawPixel(dwX - curY, dwY - curX);
   
       if (d < 0) {
           d += (curX << 2) + 6;
       }
       else {
           d += ((curX - curY) << 2) + 10;
           curY--;
       }
       curX++;
   }
   _ShowCanvas();
}


/**
 * \brief Draws a filled circle on LCD, at the given coordinates.
 *
 * \param dwX     X-coordinate of circle center.
 * \param dwY     Y-coordinate of circle center.
 * \param dwR     circle radius.
 * \param dwColor circle color.
 */
void LCDD_DrawFilledCircle( uint32_t dwX, uint32_t dwY, uint32_t dwR, uint32_t dwColor )
{
    signed int d ; // Decision Variable
    uint32_t dwCurX ; // Current X Value
    uint32_t dwCurY ; // Current Y Value
    uint32_t dwXmin, dwYmin;

    if (dwR == 0)        return;
    _SetFrontColor(dwColor);

    d = 3 - (dwR << 1) ;
    dwCurX = 0 ;
    dwCurY = dwR ;

    _HideCanvas();
    while ( dwCurX <= dwCurY )
    {
        dwXmin = (dwCurX > dwX) ? 0 : dwX-dwCurX;
        dwYmin = (dwCurY > dwY) ? 0 : dwY-dwCurY;
        _FillRect( dwXmin, dwYmin, dwX+dwCurX, dwYmin ) ;
        _FillRect( dwXmin, dwY+dwCurY, dwX+dwCurX, dwY+dwCurY ) ;
        dwXmin = (dwCurY > dwX) ? 0 : dwX-dwCurY;
        dwYmin = (dwCurX > dwY) ? 0 : dwY-dwCurX;
        _FillRect( dwXmin, dwYmin, dwX+dwCurY, dwYmin ) ;
        _FillRect( dwXmin, dwY+dwCurX, dwX+dwCurY, dwY+dwCurX ) ;

        if ( d < 0 )
        {
            d += (dwCurX << 2) + 6 ;
        }
        else
        {
            d += ((dwCurX - dwCurY) << 2) + 10;
            dwCurY-- ;
        }

        dwCurX++ ;
    }
    _ShowCanvas();
}

/**
 * \brief Draws a string inside a LCD buffer, at the given coordinates. Line breaks
 * will be honored.
 *
 * \param x        X-coordinate of string top-left corner.
 * \param y        Y-coordinate of string top-left corner.
 * \param pString  String to display.
 * \param color    String color.
 */
extern void LCDD_DrawString( uint32_t x, uint32_t y, const char *pString, uint32_t color )
{
    uint32_t xorg = x;
    while (*pString)
    {
        if (*pString == '\n')
        {
            y += gFont.height + 2; x = xorg;
        }
        else
        {
            LCDD_DrawChar(x, y, *pString, color);
            x += gFont.width + 2;
        }
        pString ++;
    }
}

/**
 * \brief Draws a string inside a LCD buffer, at the given coordinates
 * with given background color. Line breaks will be honored.
 *
 * \param x         X-coordinate of string top-left corner.
 * \param y         Y-coordinate of string top-left corner.
 * \param pString   String to display.
 * \param fontColor String color.
 * \param bgColor   Background color.
 */
extern void LCDD_DrawStringWithBGColor( uint32_t x, uint32_t y, const char *pString, uint32_t fontColor, uint32_t bgColor )
{
    uint32_t xorg = x;
    while (*pString)
    {
        if (*pString == '\n')
        {
            y += gFont.height + 2; x = xorg;
        }
        else
        {
            LCDD_DrawCharWithBGColor(x, y, *pString, fontColor, bgColor);
            x += gFont.width + 2;
        }
        pString ++;
    }
}

/**
 * \brief Returns the width & height in pixels that a string will occupy on the screen
 * if drawn using LCDD_DrawString.
 *
 * \param pString  String.
 * \param pWidth   Pointer for storing the string width (optional).
 * \param pHeight  Pointer for storing the string height (optional).
 *
 * \return String width in pixels.
 */
extern void LCDD_GetStringSize( const char *pString, uint32_t *pWidth, uint32_t *pHeight )
{
    uint32_t width = 0;
    uint32_t height = gFont.height;
    while (*pString)
    {
        if (*pString == '\n') height += gFont.height + 2;
        else                  width  += gFont.height + 2;
        pString ++;
    }
    if (width > 0) width -= 2;

    if (pWidth) *pWidth  = width;
    if (pHeight)*pHeight = height;
}

/**
 * \brief Draw a raw image at given position on LCD.
 *
 * \param x         X-coordinate of image start.
 * \param y         Y-coordinate of image start.
 * \param pImage    Image buffer.
 * \param width     Image width.
 * \param height    Image height.
 */
void LCDD_DrawImage( uint32_t dwX, uint32_t dwY, const uint8_t *pImage, uint32_t dwWidth, uint32_t dwHeight )
{
    sLCDDLayer *pDisp = LCDD_GetCanvas();
    uint16_t cw  = pDisp->bMode/8;      /* color width */
    uint32_t rw  = pDisp->wImgW * cw;   /* Row width in bytes */
    uint32_t rws = dwWidth * cw;        /* Source Row Width */
    uint32_t rl  = (rw  & 0x3) ? ((rw  | 0x3) + 1) :  rw; /* Aligned length*/
    uint32_t rls = (rws & 0x3) ? ((rws | 0x3) + 1) : rws; /* Aligned length */
    uint8_t *pSrc, *pDst;
    uint32_t i;

    pSrc = (uint8_t*)pImage;
    pDst = pDisp->pBuffer;
    pDst = &pDst[dwX*cw + dwY*rl];

    for (i = 0; i < dwHeight; i ++)
    {
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
 * \param dwWidth     window width.
 * \param dwHeight    window height.
 * \param dwColor     background color
 */
extern void LCDD_ClearWindow( uint32_t dwX, uint32_t dwY, uint32_t dwWidth, uint32_t dwHeight, uint32_t dwColor )
{
    _SetFrontColor(dwColor);
    _HideCanvas();
    _FillRect(0, 0, dwX + dwWidth - 1, dwY + dwHeight - 1);
    _ShowCanvas();
}

