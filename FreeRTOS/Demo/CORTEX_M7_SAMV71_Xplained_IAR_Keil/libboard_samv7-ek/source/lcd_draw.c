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


static LcdColor_t gLcdPixelCache[LCD_DATA_CACHE_SIZE];
/*----------------------------------------------------------------------------
 *        Exported functions
 *----------------------------------------------------------------------------*/


/**
 * \brief Convert 24 bit RGB color into 5-6-5 rgb color space.
 *
 * Initialize the LcdColor_t cache with the color pattern.
 * \param x  24-bits RGB color.
 * \return 0 for successfull operation.
 */
static uint32_t LCD_SetColor( uint32_t dwRgb24Bits )
{
    uint32_t i ;

    /* Fill the cache with selected color */
    for ( i = 0 ; i < LCD_DATA_CACHE_SIZE ; ++i )
    {
        gLcdPixelCache[i] = dwRgb24Bits ;
    }

    return 0;
} 

/**
 * \brief Check Box coordinates. Return upper left and bottom right coordinates.
 *
 * \param pX1      X-coordinate of upper-left corner on LCD.
 * \param pY1      Y-coordinate of upper-left corner on LCD.
 * \param pX2      X-coordinate of lower-right corner on LCD.
 * \param pY2      Y-coordinate of lower-right corner on LCD.
 */
static void CheckBoxCoordinates( uint32_t *pX1, uint32_t *pY1, uint32_t *pX2, uint32_t *pY2 )
{
    uint32_t dw;

    if ( *pX1 >= BOARD_LCD_WIDTH )
    {
        *pX1 = BOARD_LCD_WIDTH-1 ;
    }
    if ( *pX2 >= BOARD_LCD_WIDTH )
    {
        *pX2 = BOARD_LCD_WIDTH-1 ;
    }
    if ( *pY1 >= BOARD_LCD_HEIGHT )
    {
        *pY1 = BOARD_LCD_HEIGHT-1 ;
    }
    if ( *pY2 >= BOARD_LCD_HEIGHT )
    {
        *pY2 = BOARD_LCD_HEIGHT-1 ;
    }
    if (*pX1 > *pX2)
    {
        dw = *pX1;
        *pX1 = *pX2;
        *pX2 = dw;
    }
    if (*pY1 > *pY2)
    {
        dw = *pY1;
        *pY1 = *pY2;
        *pY2 = dw;
    }
}
/**
 * \brief Fills the given LCD buffer with a particular color.
 *
 * \param color  Fill color.
 */
void LCDD_Fill( uint32_t dwColor )
{
    uint32_t dw ;

    //    LCD_SetCursor( 0, 0 ) ;
    ILI9488_WriteRAM_Prepare() ;

    for ( dw = BOARD_LCD_WIDTH * BOARD_LCD_HEIGHT; dw > 0; dw-- )
    {
        ILI9488_WriteRAM( dwColor ) ;
    }
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
    ILI9488_SetCursor( x, y ) ;
    ILI9488_WriteRAM_Prepare() ;
    ILI9488_WriteRAM( color ) ;
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
    uint32_t color;

    ILI9488_SetCursor(x, y);
    ILI9488_ReadRAM_Prepare();
    color = ILI9488_ReadRAM();

    return color;
}

/*
 * \brief Draw a line on LCD, horizontal and vertical line are supported.
 *
 * \param x         X-coordinate of line start.
 * \param y         Y-coordinate of line start.
 * \param length    line length.
 * \param direction line direction: 0 - horizontal, 1 - vertical.
 * \param color     Pixel color.
 */
extern void LCDD_DrawLine( uint32_t dwX1, uint32_t dwY1, uint32_t dwX2, uint32_t dwY2 , uint32_t color )
{
    if (( dwY1 == dwY2 ) || (dwX1 == dwX2))
    {
        LCDD_DrawRectangleWithFill( dwX1, dwY1, dwX2, dwY2, color );
    }
    else
    {
        LCDD_DrawLineBresenham( dwX1, dwY1, dwX2, dwY2 , color) ;
    }

}



/*
 * \brief Draw a line on LCD, which is not horizontal or vertical.
 *
 * \param x         X-coordinate of line start.
 * \param y         Y-coordinate of line start.
 * \param length    line length.
 * \param direction line direction: 0 - horizontal, 1 - vertical.
 * \param color     LcdColor_t color.
 */
extern uint32_t LCDD_DrawLineBresenham( uint32_t dwX1, uint32_t dwY1, uint32_t dwX2, uint32_t dwY2 , uint32_t color)
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

    LCDD_DrawPixel(x , y , color);

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
            LCDD_DrawPixel(x , y , color);
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

            LCDD_DrawPixel(x , y , color);
        }
    }

    return 0 ;
}

/*
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

    LCDD_DrawRectangleWithFill(x, y, width, y, color);
    LCDD_DrawRectangleWithFill(x, height, width, height, color);

    LCDD_DrawRectangleWithFill(x, y, x, height, color);
    LCDD_DrawRectangleWithFill(width, y, width, height, color);
}

/*
 * \brief Draws a rectangle with fill inside on LCD, at the given coordinates.
 *
 * \param x      X-coordinate of upper-left rectangle corner.
 * \param y      Y-coordinate of upper-left rectangle corner.
 * \param width  Rectangle width in pixels.
 * \param height  Rectangle height in pixels.
 * \param color  Rectangle color.
 */
extern void LCDD_DrawRectangleWithFill( uint32_t dwX, uint32_t dwY, uint32_t dwWidth, uint32_t dwHeight, uint32_t dwColor )
{
    uint32_t size, blocks;

    CheckBoxCoordinates(&dwX, &dwY, &dwWidth, &dwHeight);
    LCD_SetColor(dwColor);
    ILI9488_SetWindow( dwX, dwY, dwWidth, dwHeight ) ;

    size = (dwWidth - dwX + 1) * (dwHeight - dwY + 1);

    /* Send pixels blocks => one LCD IT / block */
    blocks = size / LCD_DATA_CACHE_SIZE;

    ILI9488_WriteRAM_Prepare() ;

    while (blocks--)
    {
        ILI9488_WriteRAMBuffer(gLcdPixelCache, LCD_DATA_CACHE_SIZE);
    }
    /* Send remaining pixels */
    ILI9488_WriteRAMBuffer(gLcdPixelCache, size % LCD_DATA_CACHE_SIZE);
    ILI9488_SetWindow( 0, 0, BOARD_LCD_WIDTH, BOARD_LCD_HEIGHT ) ;
    //    LCD_SetCursor( 0, 0 ) ;
}

/**
 * \brief Draws a circle on LCD, at the given coordinates.
 *
 * \param x      X-coordinate of circle center.
 * \param y      Y-coordinate of circle center.
 * \param r      circle radius.
 * \param color  circle color.
 */
extern uint32_t LCDD_DrawCircle( uint32_t x, uint32_t y, uint32_t r, uint32_t color )
{
    signed int    d;    /* Decision Variable */
    uint32_t  curX; /* Current X Value */
    uint32_t  curY; /* Current Y Value */

    d = 3 - (r << 1);
    curX = 0;
    curY = r;

    while (curX <= curY)
    {
        LCDD_DrawPixel(x + curX, y + curY, color);
        LCDD_DrawPixel(x + curX, y - curY, color);
        LCDD_DrawPixel(x - curX, y + curY, color);
        LCDD_DrawPixel(x - curX, y - curY, color);
        LCDD_DrawPixel(x + curY, y + curX, color);
        LCDD_DrawPixel(x + curY, y - curX, color);
        LCDD_DrawPixel(x - curY, y + curX, color);
        LCDD_DrawPixel(x - curY, y - curX, color);

        if (d < 0) {
            d += (curX << 2) + 6;
        }
        else {
            d += ((curX - curY) << 2) + 10;
            curY--;
        }
        curX++;
    }
    return 0;
}


extern uint32_t LCD_DrawFilledCircle( uint32_t dwX, uint32_t dwY, uint32_t dwRadius, uint32_t color)
{
    signed int d ; /* Decision Variable */
    uint32_t dwCurX ; /* Current X Value */
    uint32_t dwCurY ; /* Current Y Value */
    uint32_t dwXmin, dwYmin;

    if (dwRadius == 0)
    {
        return 0;
    }
    d = 3 - (dwRadius << 1) ;
    dwCurX = 0 ;
    dwCurY = dwRadius ;

    while ( dwCurX <= dwCurY )
    {
        dwXmin = (dwCurX > dwX) ? 0 : dwX-dwCurX;
        dwYmin = (dwCurY > dwY) ? 0 : dwY-dwCurY;
        LCDD_DrawRectangleWithFill( dwXmin, dwYmin, dwX+dwCurX, dwYmin ,color) ;
        LCDD_DrawRectangleWithFill( dwXmin, dwY+dwCurY, dwX+dwCurX, dwY+dwCurY, color ) ;
        dwXmin = (dwCurY > dwX) ? 0 : dwX-dwCurY;
        dwYmin = (dwCurX > dwY) ? 0 : dwY-dwCurX;
        LCDD_DrawRectangleWithFill( dwXmin, dwYmin, dwX+dwCurY, dwYmin, color  ) ;
        LCDD_DrawRectangleWithFill( dwXmin, dwY+dwCurX, dwX+dwCurY, dwY+dwCurX, color  ) ;

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

    return 0 ;
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
extern void LCDD_DrawString( uint32_t x, uint32_t y, const uint8_t *pString, uint32_t color )
{
    uint32_t xorg = x ;

    while ( *pString != 0 )
    {
        if ( *pString == '\n' )
        {
            y += gFont.height + 2 ;
            x = xorg ;
        }
        else
        {
            LCDD_DrawChar( x, y, *pString, color ) ;
            x += gFont.width + 2 ;
        }

        pString++ ;
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
    unsigned xorg = x;

    while ( *pString != 0 )
    {
        if ( *pString == '\n' )
        {
            y += gFont.height + 2 ;
            x = xorg ;
        }
        else
        {
            LCDD_DrawCharWithBGColor( x, y, *pString, fontColor, bgColor ) ;
            x += gFont.width + 2;
        }

        pString++;
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
extern void LCDD_GetStringSize( const uint8_t *pString, uint32_t *pWidth, uint32_t *pHeight )
{
    uint32_t width = 0;
    uint32_t height = gFont.height;

    while ( *pString != 0 )
    {
        if ( *pString == '\n' )
        {
            height += gFont.height + 2 ;
        }
        else
        {
            width += gFont.width + 2 ;
        }

        pString++ ;
    }

    if ( width > 0 )
    {
        width -= 2;
    }

    if ( pWidth != NULL )
    {
        *pWidth = width;
    }

    if ( pHeight != NULL )
    {
        *pHeight = height ;
    }
}

/*
 * \brief Draw a raw image at given position on LCD.
 *
 * \param x         X-coordinate of image start.
 * \param y         Y-coordinate of image start.
 * \param pImage    Image buffer.
 * \param width     Image width.
 * \param height    Image height.
 */
extern void LCDD_DrawImage( uint32_t dwX, uint32_t dwY, const LcdColor_t *pImage, uint32_t dwWidth, uint32_t dwHeight )
{
    uint32_t size;


    /* Determine the refresh window area */
    /* Horizontal and Vertical RAM Address Position (R50h, R51h, R52h, R53h) */
    CheckBoxCoordinates(&dwX, &dwY, &dwWidth, &dwHeight);
    ILI9488_SetWindow(dwX, dwY, dwWidth, dwHeight);

    /* Prepare to write in GRAM */
    ILI9488_WriteRAM_Prepare();

    size = (dwWidth - dwX + 1) * (dwHeight - dwY + 1);

    ILI9488_WriteRAMBuffer(pImage, size);

    ILI9488_SetWindow( 0, 0, BOARD_LCD_WIDTH, BOARD_LCD_HEIGHT ) ;
}

/*
 * \brief Draw a raw image at given position on LCD.
 *
 * \param dwX         X-coordinate of image start.
 * \param dwY         Y-coordinate of image start.
 * \param pGIMPImage  Image data.
 */
void LCDD_DrawGIMPImage( uint32_t dwX, uint32_t dwY, const SGIMPImage* pGIMPImage )
{
    uint32_t dw ;
    register uint32_t dwLength ;
    uint8_t* pucData ;
    LcdColor_t *pData;

    // Draw raw RGB bitmap
    //    CheckBoxCoordinates(&dwX, &dwY, &dwWidth, &dwHeight);
    ILI9488_SetWindow( dwX, dwY, pGIMPImage->dwWidth, pGIMPImage->dwHeight ) ;
    //    LCD_SetCursor( dwX, dwY ) ;

    ILI9488_WriteRAM_Prepare() ;

    dwLength = pGIMPImage->dwWidth*pGIMPImage->dwHeight ;
    pucData = pGIMPImage->pucPixel_data ;
    for ( dw=0; dw < dwLength; dw++ )
    {
        *pData  = ((*pucData++)<<16) ;
        *pData |= ((*pucData++)<<8) ;
        *pData |= (*pucData++) ;
        ILI9488_WriteRAM(*pData);
    }

    ILI9488_SetWindow( 0, 0, BOARD_LCD_WIDTH, BOARD_LCD_HEIGHT ) ;
}

/*
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
    uint32_t dw ;


    ILI9488_SetWindow( dwX, dwY, dwWidth, dwHeight ) ;
    ILI9488_WriteRAM_Prepare() ;

    for ( dw = dwWidth * dwHeight; dw > 0; dw-- )
    {
        ILI9488_WriteRAM( dwColor ) ;
    }
}
