//*****************************************************************************
//
// grlib.h - Prototypes for the low level primitives provided by the graphics
//           library.
//
// Copyright (c) 2007-2008 Luminary Micro, Inc.  All rights reserved.
// 
// Software License Agreement
// 
// Luminary Micro, Inc. (LMI) is supplying this software for use solely and
// exclusively on LMI's microcontroller products.
// 
// The software is owned by LMI and/or its suppliers, and is protected under
// applicable copyright laws.  All rights are reserved.  You may not combine
// this software with "viral" open-source software in order to form a larger
// program.  Any use in violation of the foregoing restrictions may subject
// the user to criminal sanctions under applicable laws, as well as to civil
// liability for the breach of the terms and conditions of this license.
// 
// THIS SOFTWARE IS PROVIDED "AS IS".  NO WARRANTIES, WHETHER EXPRESS, IMPLIED
// OR STATUTORY, INCLUDING, BUT NOT LIMITED TO, IMPLIED WARRANTIES OF
// MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE APPLY TO THIS SOFTWARE.
// LMI SHALL NOT, IN ANY CIRCUMSTANCES, BE LIABLE FOR SPECIAL, INCIDENTAL, OR
// CONSEQUENTIAL DAMAGES, FOR ANY REASON WHATSOEVER.
// 
// This is part of revision 2523 of the Stellaris Graphics Library.
//
//*****************************************************************************

#ifndef __GRLIB_H__
#define __GRLIB_H__

//*****************************************************************************
//
//! \addtogroup primitives_api
//! @{
//
//*****************************************************************************

//*****************************************************************************
//
// If building with a C++ compiler, make all of the definitions in this header
// have a C binding.
//
//*****************************************************************************
#ifdef __cplusplus
extern "C"
{
#endif

//*****************************************************************************
//
//! This structure defines the extents of a rectangle.  All points greater than
//! or equal to the minimum and less than or equal to the maximum are part of
//! the rectangle.
//
//*****************************************************************************
typedef struct
{
    //
    //! The minimum X coordinate of the rectangle.
    //
    short sXMin;

    //
    //! The minimum Y coordinate of the rectangle.
    //
    short sYMin;

    //
    //! The maximum X coordinate of the rectangle.
    //
    short sXMax;

    //
    //! The maximum Y coordinate of the rectangle.
    //
    short sYMax;
}
tRectangle;

//*****************************************************************************
//
//! This structure defines the characteristics of a display driver.
//
//*****************************************************************************
typedef struct
{
    //
    //! The size of this structure.
    //
    long lSize;

    //
    //! A pointer to display driver-specific data.
    //
    void *pvDisplayData;

    //
    //! The width of this display.
    //
    unsigned short usWidth;

    //
    //! The height of this display.
    //
    unsigned short usHeight;

    //
    //! A pointer to the function to draw a pixel on this display.
    //
    void (*pfnPixelDraw)(void *pvDisplayData, long lX, long lY,
                         unsigned long ulValue);

    //
    //! A pointer to the function to draw multiple pixels on this display.
    //
    void (*pfnPixelDrawMultiple)(void *pvDisplayData, long lX, long lY,
                                 long lX0, long lCount, long lBPP,
                                 const unsigned char *pucData,
                                 const unsigned char *pucPalette);

    //
    //! A pointer to the function to draw a horizontal line on this display.
    //
    void (*pfnLineDrawH)(void *pvDisplayData, long lX1, long lX2, long lY,
                         unsigned long ulValue);

    //
    //! A pointer to the function to draw a vertical line on this display.
    //
    void (*pfnLineDrawV)(void *pvDisplayData, long lX, long lY1, long lY2,
                         unsigned long ulValue);

    //
    //! A pointer to the function to draw a filled rectangle on this display.
    //
    void (*pfnRectFill)(void *pvDisplayData, const tRectangle *pRect,
                        unsigned long ulValue);

    //
    //! A pointer to the function to translate 24-bit RGB colors to
    //! display-specific colors.
    //
    unsigned long (*pfnColorTranslate)(void *pvDisplayData,
                                       unsigned long ulValue);

    //
    //! A pointer to the function to flush any cached drawing operations on
    //! this display.
    //
    void (*pfnFlush)(void *pvDisplayData);
}
tDisplay;

//*****************************************************************************
//
//! This structure describes a font used for drawing text onto the screen.
//
//*****************************************************************************
typedef struct
{
    //
    //! The format of the font.  Can be one of FONT_FMT_UNCOMPRESSED or
    //! FONT_FMT_PIXEL_RLE.
    //
    unsigned char ucFormat;

    //
    //! The maximum width of a character; this is the width of the widest
    //! character in the font, though any individual character may be narrower
    //! than this width.
    //
    unsigned char ucMaxWidth;

    //
    //! The height of the character cell; this may be taller than the font data
    //! for the characters (to provide inter-line spacing).
    //
    unsigned char ucHeight;

    //
    //! The offset between the top of the character cell and the baseline of
    //! the glyph.  The baseline is the bottom row of a capital letter, below
    //! which only the descenders of the lower case letters occur.
    //
    unsigned char ucBaseline;

    //
    //! The offset within pucData to the data for each character in the font.
    //
    unsigned short pusOffset[96];

    //
    //! A pointer to the data for the font.
    //
    const unsigned char *pucData;
}
tFont;

//*****************************************************************************
//
//! Indicates that the font data is stored in an uncompressed format.
//
//*****************************************************************************
#define FONT_FMT_UNCOMPRESSED   0x00

//*****************************************************************************
//
//! Indicates that the font data is stored using a pixel-based RLE format.
//
//*****************************************************************************
#define FONT_FMT_PIXEL_RLE      0x01

//*****************************************************************************
//
//! Indicates that the image data is not compressed and represents each pixel
//! with a single bit.
//
//*****************************************************************************
#define IMAGE_FMT_1BPP_UNCOMP   0x01

//*****************************************************************************
//
//! Indicates that the image data is not compressed and represents each pixel
//! with four bits.
//
//*****************************************************************************
#define IMAGE_FMT_4BPP_UNCOMP   0x04

//*****************************************************************************
//
//! Indicates that the image data is not compressed and represents each pixel
//! with eight bits.
//
//*****************************************************************************
#define IMAGE_FMT_8BPP_UNCOMP   0x08

//*****************************************************************************
//
//! Indicates that the image data is compressed and represents each pixel with
//! a single bit.
//
//*****************************************************************************
#define IMAGE_FMT_1BPP_COMP     0x81

//*****************************************************************************
//
//! Indicates that the image data is compressed and represents each pixel with
//! four bits.
//
//*****************************************************************************
#define IMAGE_FMT_4BPP_COMP     0x84

//*****************************************************************************
//
//! Indicates that the image data is compressed and represents each pixel with
//! eight bits.
//
//*****************************************************************************
#define IMAGE_FMT_8BPP_COMP     0x88

//*****************************************************************************
//
//! This structure defines a drawing context to be used to draw onto the
//! screen.  Multiple drawing contexts may exist at any time.
//
//*****************************************************************************
typedef struct
{
    //
    //! The size of this structure.
    //
    long lSize;

    //
    //! The screen onto which drawing operations are performed.
    //
    const tDisplay *pDisplay;

    //
    //! The clipping region to be used when drawing onto the screen.
    //
    tRectangle sClipRegion;

    //
    //! The color used to draw primitives onto the screen.
    //
    unsigned long ulForeground;

    //
    //! The background color used to draw primitives onto the screen.
    //
    unsigned long ulBackground;

    //
    //! The font used to render text onto the screen.
    //
    const tFont *pFont;
}
tContext;

//*****************************************************************************
//
//! Sets the background color to be used.
//!
//! \param pContext is a pointer to the drawing context to modify.
//! \param ulValue is the 24-bit RGB color to be used.
//!
//! This function sets the background color to be used for drawing operations
//! in the specified drawing context.
//!
//! \return None.
//
//*****************************************************************************
#define GrContextBackgroundSet(pContext, ulValue)                        \
        do                                                               \
        {                                                                \
            tContext *pC = pContext;                                     \
            pC->ulBackground = DpyColorTranslate(pC->pDisplay, ulValue); \
        }                                                                \
        while(0)

//*****************************************************************************
//
//! Sets the background color to be used.
//!
//! \param pContext is a pointer to the drawing context to modify.
//! \param ulValue is the display driver-specific color to be used.
//!
//! This function sets the background color to be used for drawing operations
//! in the specified drawing context, using a color that has been previously
//! translated to a driver-specific color (for example, via
//! DpyColorTranslate()).
//!
//! \return None.
//
//*****************************************************************************
#define GrContextBackgroundSetTranslated(pContext, ulValue) \
        do                                                  \
        {                                                   \
            tContext *pC = pContext;                        \
            pC->ulBackground = ulValue;                     \
        }                                                   \
        while(0)

//*****************************************************************************
//
//! Gets the width of the display being used by this drawing context.
//!
//! \param pContext is a pointer to the drawing context to query.
//!
//! This function returns the width of the display that is being used by this
//! drawing context.
//!
//! \return Returns the width of the display in pixels.
//
//*****************************************************************************
#define GrContextDpyWidthGet(pContext)      \
        (DpyWidthGet((pContext)->pDisplay))

//*****************************************************************************
//
//! Gets the height of the display being used by this drawing context.
//!
//! \param pContext is a pointer to the drawing context to query.
//!
//! This function returns the height of the display that is being used by this
//! drawing context.
//!
//! \return Returns the height of the display in pixels.
//
//*****************************************************************************
#define GrContextDpyHeightGet(pContext)      \
        (DpyHeightGet((pContext)->pDisplay))

//*****************************************************************************
//
//! Sets the font to be used.
//!
//! \param pContext is a pointer to the drawing context to modify.
//! \param pFnt is a pointer to the font to be used.
//!
//! This function sets the font to be used for string drawing operations in the
//! specified drawing context.
//!
//! \return None.
//
//*****************************************************************************
#define GrContextFontSet(pContext, pFnt) \
        do                               \
        {                                \
            tContext *pC = pContext;     \
            const tFont *pF = pFnt;      \
            pC->pFont = pF;              \
        }                                \
        while(0)

//*****************************************************************************
//
//! Sets the foreground color to be used.
//!
//! \param pContext is a pointer to the drawing context to modify.
//! \param ulValue is the 24-bit RGB color to be used.
//!
//! This function sets the color to be used for drawing operations in the
//! specified drawing context.
//!
//! \return None.
//
//*****************************************************************************
#define GrContextForegroundSet(pContext, ulValue)                        \
        do                                                               \
        {                                                                \
            tContext *pC = pContext;                                     \
            pC->ulForeground = DpyColorTranslate(pC->pDisplay, ulValue); \
        }                                                                \
        while(0)

//*****************************************************************************
//
//! Sets the foreground color to be used.
//!
//! \param pContext is a pointer to the drawing context to modify.
//! \param ulValue is the display driver-specific color to be used.
//!
//! This function sets the foreground color to be used for drawing operations
//! in the specified drawing context, using a color that has been previously
//! translated to a driver-specific color (for example, via
//! DpyColorTranslate()).
//!
//! \return None.
//
//*****************************************************************************
#define GrContextForegroundSetTranslated(pContext, ulValue) \
        do                                                  \
        {                                                   \
            tContext *pC = pContext;                        \
            pC->ulForeground = ulValue;                     \
        }                                                   \
        while(0)

//*****************************************************************************
//
//! Flushes any cached drawing operations.
//!
//! \param pContext is a pointer to the drawing context to use.
//!
//! This function flushes any cached drawing operations.  For display drivers
//! that draw into a local frame buffer before writing to the actual display,
//! calling this function will cause the display to be updated to match the
//! contents of the local frame buffer.
//!
//! \return None.
//
//*****************************************************************************
#define GrFlush(pContext)                  \
        do                                 \
        {                                  \
            const tContext *pC = pContext; \
            DpyFlush(pC->pDisplay);        \
        }                                  \
        while(0)

//*****************************************************************************
//
//! Gets the baseline of a font.
//!
//! \param pFont is a pointer to the font to query.
//!
//! This function determines the baseline position of a font.  The baseline is
//! the offset between the top of the font and the bottom of the capital
//! letters.  The only font data that exists below the baseline are the
//! descenders on some lower-case letters (such as ``y'').
//!
//! \return Returns the baseline of the font, in pixels.
//
//*****************************************************************************
#define GrFontBaselineGet(pFont) \
        ((pFont)->ucBaseline)

//*****************************************************************************
//
//! Gets the height of a font.
//!
//! \param pFont is a pointer to the font to query.
//!
//! This function determines the height of a font.  The height is the offset
//! between the top of the font and the bottom of the font, including any
//! ascenders and descenders.
//!
//! \return Returns the height of the font, in pixels.
//
//*****************************************************************************
#define GrFontHeightGet(pFont) \
        ((pFont)->ucHeight)

//*****************************************************************************
//
//! Gets the maximum width of a font.
//!
//! \param pFont is a pointer to the font to query.
//!
//! This function determines the maximum width of a font.  The maximum width is
//! the width of the widest individual character in the font.
//!
//! \return Returns the maximum width of the font, in pixels.
//
//*****************************************************************************
#define GrFontMaxWidthGet(pFont) \
        ((pFont)->ucMaxWidth)

//*****************************************************************************
//
//! Gets the number of colors in an image.
//!
//! \param pucImage is a pointer to the image to query.
//!
//! This function determines the number of colors in the palette of an image.
//! This is only valid for 4bpp and 8bpp images; 1bpp images do not contain a
//! palette.
//!
//! \return Returns the number of colors in the image.
//
//*****************************************************************************
#define GrImageColorsGet(pucImage)           \
        (((unsigned char *)pucImage)[5] + 1)

//*****************************************************************************
//
//! Gets the height of an image.
//!
//! \param pucImage is a pointer to the image to query.
//!
//! This function determines the height of an image in pixels.
//!
//! \return Returns the height of the image in pixels.
//
//*****************************************************************************
#define GrImageHeightGet(pucImage)          \
        (*(unsigned short *)(pucImage + 3))

//*****************************************************************************
//
//! Gets the width of an image.
//!
//! \param pucImage is a pointer to the image to query.
//!
//! This function determines the width of an image in pixels.
//!
//! \return Returns the width of the image in pixels.
//
//*****************************************************************************
#define GrImageWidthGet(pucImage)           \
        (*(unsigned short *)(pucImage + 1))

//*****************************************************************************
//
//! Determines the size of the buffer for a 1 BPP off-screen image.
//!
//! \param lWidth is the width of the image in pixels.
//! \param lHeight is the height of the image in pixels.
//!
//! This function determines the size of the memory buffer required to hold a
//! 1 BPP off-screen image of the specified geometry.
//!
//! \return Returns the number of bytes required by the image.
//
//*****************************************************************************
#define GrOffScreen1BPPSize(lWidth, lHeight) \
        (5 + (((lWidth + 7) / 8) * lHeight))

//*****************************************************************************
//
//! Determines the size of the buffer for a 4 BPP off-screen image.
//!
//! \param lWidth is the width of the image in pixels.
//! \param lHeight is the height of the image in pixels.
//!
//! This function determines the size of the memory buffer required to hold a
//! 4 BPP off-screen image of the specified geometry.
//!
//! \return Returns the number of bytes required by the image.
//
//*****************************************************************************
#define GrOffScreen4BPPSize(lWidth, lHeight)            \
        (6 + (16 * 3) + (((lWidth + 1) / 2) * lHeight))

//*****************************************************************************
//
//! Determines the size of the buffer for an 8 BPP off-screen image.
//!
//! \param lWidth is the width of the image in pixels.
//! \param lHeight is the height of the image in pixels.
//!
//! This function determines the size of the memory buffer required to hold an
//! 8 BPP off-screen image of the specified geometry.
//!
//! \return Returns the number of bytes required by the image.
//
//*****************************************************************************
#define GrOffScreen8BPPSize(lWidth, lHeight) \
        (6 + (256 * 3) + (lWidth * lHeight))

//*****************************************************************************
//
//! Draws a pixel.
//!
//! \param pContext is a pointer to the drawing context to use.
//! \param lX is the X coordinate of the pixel.
//! \param lY is the Y coordinate of the pixel.
//!
//! This function draws a pixel if it resides within the clipping region.
//!
//! \return None.
//
//*****************************************************************************
#define GrPixelDraw(pContext, lX, lY)                                 \
        do                                                            \
        {                                                             \
            const tContext *pC = pContext;                            \
            if((lX >= pC->sClipRegion.sXMin) &&                       \
               (lX <= pC->sClipRegion.sXMax) &&                       \
               (lY >= pC->sClipRegion.sYMin) &&                       \
               (lY <= pC->sClipRegion.sYMax))                         \
            {                                                         \
                DpyPixelDraw(pC->pDisplay, lX, lY, pC->ulForeground); \
            }                                                         \
        }                                                             \
        while(0)

//*****************************************************************************
//
//! Gets the baseline of a string.
//!
//! \param pContext is a pointer to the drawing context to query.
//!
//! This function determines the baseline position of a string.  The baseline
//! is the offset between the top of the string and the bottom of the capital
//! letters.  The only string data that exists below the baseline are the
//! descenders on some lower-case letters (such as ``y'').
//!
//! \return Returns the baseline of the string, in pixels.
//
//*****************************************************************************
#define GrStringBaselineGet(pContext)   \
        ((pContext)->pFont->ucBaseline)

//*****************************************************************************
//
//! Draws a centered string.
//!
//! \param pContext is a pointer to the drawing context to use.
//! \param pcString is a pointer to the string to be drawn.
//! \param lLength is the number of characters from the string that should be
//! drawn on the screen.
//! \param lX is the X coordinate of the center of the string position on the
//! screen.
//! \param lY is the Y coordinate of the center of the string position on the
//! screen.
//! \param bOpaque is \b true if the background of each character should be
//! drawn and \b false if it should not (leaving the background as is).
//!
//! This function draws a string of test on the screen centered upon the
//! provided position.  The \e lLength parameter allows a portion of the
//! string to be examined without having to insert a NULL character at the
//! stopping point (which would not be possible if the string was located in
//! flash); specifying a length of -1 will cause the entire string to be
//! rendered (subject to clipping).
//!
//! \return None.
//
//*****************************************************************************
#define GrStringDrawCentered(pContext, pcString, lLength, lX, lY, bOpaque)  \
        do                                                                  \
        {                                                                   \
            const tContext *pC = pContext;                                  \
            const char *pcStr = pcString;                                   \
                                                                            \
            GrStringDraw(pC, pcStr, lLength,                                \
                         (lX) - (GrStringWidthGet(pC, pcStr, lLength) / 2), \
                         (lY) - (pC->pFont->ucBaseline / 2), bOpaque);      \
        }                                                                   \
        while(0)

//*****************************************************************************
//
//! Gets the height of a string.
//!
//! \param pContext is a pointer to the drawing context to query.
//!
//! This function determines the height of a string.  The height is the offset
//! between the top of the string and the bottom of the string, including any
//! ascenders and descenders.  Note that this will not account for the case
//! where the string in question does not have any characters that use
//! descenders but the font in the drawing context does contain characters with
//! descenders.
//!
//! \return Returns the height of the string, in pixels.
//
//*****************************************************************************
#define GrStringHeightGet(pContext)   \
        ((pContext)->pFont->ucHeight)

//*****************************************************************************
//
//! Gets the maximum width of a character in a string.
//!
//! \param pContext is a pointer to the drawing context to query.
//!
//! This function determines the maximum width of a character in a string.  The
//! maximum width is the width of the widest individual character in the font
//! used to render the string, which may be wider than the widest character
//! that is used to render a particular string.
//!
//! \return Returns the maximum width of a character in a string, in pixels.
//
//*****************************************************************************
#define GrStringMaxWidthGet(pContext)   \
        ((pContext)->pFont->ucMaxWidth)

//*****************************************************************************
//
// A set of color definitions.  This set is the subset of the X11 colors (from
// rgb.txt) that are supported by typical web browsers.
//
//*****************************************************************************
#define ClrAliceBlue            0x00F0F8FF
#define ClrAntiqueWhite         0x00FAEBD7
#define ClrAqua                 0x0000FFFF
#define ClrAquamarine           0x007FFFD4
#define ClrAzure                0x00F0FFFF
#define ClrBeige                0x00F5F5DC
#define ClrBisque               0x00FFE4C4
#define ClrBlack                0x00000000
#define ClrBlanchedAlmond       0x00FFEBCD
#define ClrBlue                 0x000000FF
#define ClrBlueViolet           0x008A2BE2
#define ClrBrown                0x00A52A2A
#define ClrBurlyWood            0x00DEB887
#define ClrCadetBlue            0x005F9EA0
#define ClrChartreuse           0x007FFF00
#define ClrChocolate            0x00D2691E
#define ClrCoral                0x00FF7F50
#define ClrCornflowerBlue       0x006495ED
#define ClrCornsilk             0x00FFF8DC
#define ClrCrimson              0x00DC143C
#define ClrCyan                 0x0000FFFF
#define ClrDarkBlue             0x0000008B
#define ClrDarkCyan             0x00008B8B
#define ClrDarkGoldenrod        0x00B8860B
#define ClrDarkGray             0x00A9A9A9
#define ClrDarkGreen            0x00006400
#define ClrDarkKhaki            0x00BDB76B
#define ClrDarkMagenta          0x008B008B
#define ClrDarkOliveGreen       0x00556B2F
#define ClrDarkOrange           0x00FF8C00
#define ClrDarkOrchid           0x009932CC
#define ClrDarkRed              0x008B0000
#define ClrDarkSalmon           0x00E9967A
#define ClrDarkSeaGreen         0x008FBC8F
#define ClrDarkSlateBlue        0x00483D8B
#define ClrDarkSlateGray        0x002F4F4F
#define ClrDarkTurquoise        0x0000CED1
#define ClrDarkViolet           0x009400D3
#define ClrDeepPink             0x00FF1493
#define ClrDeepSkyBlue          0x0000BFFF
#define ClrDimGray              0x00696969
#define ClrDodgerBlue           0x001E90FF
#define ClrFireBrick            0x00B22222
#define ClrFloralWhite          0x00FFFAF0
#define ClrForestGreen          0x00228B22
#define ClrFuchsia              0x00FF00FF
#define ClrGainsboro            0x00DCDCDC
#define ClrGhostWhite           0x00F8F8FF
#define ClrGold                 0x00FFD700
#define ClrGoldenrod            0x00DAA520
#define ClrGray                 0x00808080
#define ClrGreen                0x00008000
#define ClrGreenYellow          0x00ADFF2F
#define ClrHoneydew             0x00F0FFF0
#define ClrHotPink              0x00FF69B4
#define ClrIndianRed            0x00CD5C5C
#define ClrIndigo               0x004B0082
#define ClrIvory                0x00FFFFF0
#define ClrKhaki                0x00F0E68C
#define ClrLavender             0x00E6E6FA
#define ClrLavenderBlush        0x00FFF0F5
#define ClrLawnGreen            0x007CFC00
#define ClrLemonChiffon         0x00FFFACD
#define ClrLightBlue            0x00ADD8E6
#define ClrLightCoral           0x00F08080
#define ClrLightCyan            0x00E0FFFF
#define ClrLightGoldenrodYellow 0x00FAFAD2
#define ClrLightGreen           0x0090EE90
#define ClrLightGrey            0x00D3D3D3
#define ClrLightPink            0x00FFB6C1
#define ClrLightSalmon          0x00FFA07A
#define ClrLightSeaGreen        0x0020B2AA
#define ClrLightSkyBlue         0x0087CEFA
#define ClrLightSlateGray       0x00778899
#define ClrLightSteelBlue       0x00B0C4DE
#define ClrLightYellow          0x00FFFFE0
#define ClrLime                 0x0000FF00
#define ClrLimeGreen            0x0032CD32
#define ClrLinen                0x00FAF0E6
#define ClrMagenta              0x00FF00FF
#define ClrMaroon               0x00800000
#define ClrMediumAquamarine     0x0066CDAA
#define ClrMediumBlue           0x000000CD
#define ClrMediumOrchid         0x00BA55D3
#define ClrMediumPurple         0x009370DB
#define ClrMediumSeaGreen       0x003CB371
#define ClrMediumSlateBlue      0x007B68EE
#define ClrMediumSpringGreen    0x0000FA9A
#define ClrMediumTurquoise      0x0048D1CC
#define ClrMediumVioletRed      0x00C71585
#define ClrMidnightBlue         0x00191970
#define ClrMintCream            0x00F5FFFA
#define ClrMistyRose            0x00FFE4E1
#define ClrMoccasin             0x00FFE4B5
#define ClrNavajoWhite          0x00FFDEAD
#define ClrNavy                 0x00000080
#define ClrOldLace              0x00FDF5E6
#define ClrOlive                0x00808000
#define ClrOliveDrab            0x006B8E23
#define ClrOrange               0x00FFA500
#define ClrOrangeRed            0x00FF4500
#define ClrOrchid               0x00DA70D6
#define ClrPaleGoldenrod        0x00EEE8AA
#define ClrPaleGreen            0x0098FB98
#define ClrPaleTurquoise        0x00AFEEEE
#define ClrPaleVioletRed        0x00DB7093
#define ClrPapayaWhip           0x00FFEFD5
#define ClrPeachPuff            0x00FFDAB9
#define ClrPeru                 0x00CD853F
#define ClrPink                 0x00FFC0CB
#define ClrPlum                 0x00DDA0DD
#define ClrPowderBlue           0x00B0E0E6
#define ClrPurple               0x00800080
#define ClrRed                  0x00FF0000
#define ClrRosyBrown            0x00BC8F8F
#define ClrRoyalBlue            0x004169E1
#define ClrSaddleBrown          0x008B4513
#define ClrSalmon               0x00FA8072
#define ClrSandyBrown           0x00F4A460
#define ClrSeaGreen             0x002E8B57
#define ClrSeashell             0x00FFF5EE
#define ClrSienna               0x00A0522D
#define ClrSilver               0x00C0C0C0
#define ClrSkyBlue              0x0087CEEB
#define ClrSlateBlue            0x006A5ACD
#define ClrSlateGray            0x00708090
#define ClrSnow                 0x00FFFAFA
#define ClrSpringGreen          0x0000FF7F
#define ClrSteelBlue            0x004682B4
#define ClrTan                  0x00D2B48C
#define ClrTeal                 0x00008080
#define ClrThistle              0x00D8BFD8
#define ClrTomato               0x00FF6347
#define ClrTurquoise            0x0040E0D0
#define ClrViolet               0x00EE82EE
#define ClrWheat                0x00F5DEB3
#define ClrWhite                0x00FFFFFF
#define ClrWhiteSmoke           0x00F5F5F5
#define ClrYellow               0x00FFFF00
#define ClrYellowGreen          0x009ACD32

//*****************************************************************************
//
// Masks and shifts to aid in color format translation by drivers.
//
//*****************************************************************************
#define ClrRedMask              0x00FF0000
#define ClrRedShift             16
#define ClrGreenMask            0x0000FF00
#define ClrGreenShift           8
#define ClrBlueMask             0x000000FF
#define ClrBlueShift            0

//*****************************************************************************
//
// Prototypes for the predefined fonts in the graphics library.  ..Cm.. is the
// computer modern font, which is a serif font.  ..Cmsc.. is the computer
// modern small-caps font, which is also a serif font.  ..Cmss.. is the
// computer modern sans-serif font.
//
//*****************************************************************************
extern const tFont g_sFontCm12;
extern const tFont g_sFontCm12b;
extern const tFont g_sFontCm12i;
extern const tFont g_sFontCm14;
extern const tFont g_sFontCm14b;
extern const tFont g_sFontCm14i;
extern const tFont g_sFontCm16;
extern const tFont g_sFontCm16b;
extern const tFont g_sFontCm16i;
extern const tFont g_sFontCm18;
extern const tFont g_sFontCm18b;
extern const tFont g_sFontCm18i;
extern const tFont g_sFontCm20;
extern const tFont g_sFontCm20b;
extern const tFont g_sFontCm20i;
extern const tFont g_sFontCm22;
extern const tFont g_sFontCm22b;
extern const tFont g_sFontCm22i;
extern const tFont g_sFontCm24;
extern const tFont g_sFontCm24b;
extern const tFont g_sFontCm24i;
extern const tFont g_sFontCm26;
extern const tFont g_sFontCm26b;
extern const tFont g_sFontCm26i;
extern const tFont g_sFontCm28;
extern const tFont g_sFontCm28b;
extern const tFont g_sFontCm28i;
extern const tFont g_sFontCm30;
extern const tFont g_sFontCm30b;
extern const tFont g_sFontCm30i;
extern const tFont g_sFontCm32;
extern const tFont g_sFontCm32b;
extern const tFont g_sFontCm32i;
extern const tFont g_sFontCm34;
extern const tFont g_sFontCm34b;
extern const tFont g_sFontCm34i;
extern const tFont g_sFontCm36;
extern const tFont g_sFontCm36b;
extern const tFont g_sFontCm36i;
extern const tFont g_sFontCm38;
extern const tFont g_sFontCm38b;
extern const tFont g_sFontCm38i;
extern const tFont g_sFontCm40;
extern const tFont g_sFontCm40b;
extern const tFont g_sFontCm40i;
extern const tFont g_sFontCm42;
extern const tFont g_sFontCm42b;
extern const tFont g_sFontCm42i;
extern const tFont g_sFontCm44;
extern const tFont g_sFontCm44b;
extern const tFont g_sFontCm44i;
extern const tFont g_sFontCm46;
extern const tFont g_sFontCm46b;
extern const tFont g_sFontCm46i;
extern const tFont g_sFontCm48;
extern const tFont g_sFontCm48b;
extern const tFont g_sFontCm48i;
extern const tFont g_sFontCmsc12;
extern const tFont g_sFontCmsc14;
extern const tFont g_sFontCmsc16;
extern const tFont g_sFontCmsc18;
extern const tFont g_sFontCmsc20;
extern const tFont g_sFontCmsc22;
extern const tFont g_sFontCmsc24;
extern const tFont g_sFontCmsc26;
extern const tFont g_sFontCmsc28;
extern const tFont g_sFontCmsc30;
extern const tFont g_sFontCmsc32;
extern const tFont g_sFontCmsc34;
extern const tFont g_sFontCmsc36;
extern const tFont g_sFontCmsc38;
extern const tFont g_sFontCmsc40;
extern const tFont g_sFontCmsc42;
extern const tFont g_sFontCmsc44;
extern const tFont g_sFontCmsc46;
extern const tFont g_sFontCmsc48;
extern const tFont g_sFontCmss12;
extern const tFont g_sFontCmss12b;
extern const tFont g_sFontCmss12i;
extern const tFont g_sFontCmss14;
extern const tFont g_sFontCmss14b;
extern const tFont g_sFontCmss14i;
extern const tFont g_sFontCmss16;
extern const tFont g_sFontCmss16b;
extern const tFont g_sFontCmss16i;
extern const tFont g_sFontCmss18;
extern const tFont g_sFontCmss18b;
extern const tFont g_sFontCmss18i;
extern const tFont g_sFontCmss20;
extern const tFont g_sFontCmss20b;
extern const tFont g_sFontCmss20i;
extern const tFont g_sFontCmss22;
extern const tFont g_sFontCmss22b;
extern const tFont g_sFontCmss22i;
extern const tFont g_sFontCmss24;
extern const tFont g_sFontCmss24b;
extern const tFont g_sFontCmss24i;
extern const tFont g_sFontCmss26;
extern const tFont g_sFontCmss26b;
extern const tFont g_sFontCmss26i;
extern const tFont g_sFontCmss28;
extern const tFont g_sFontCmss28b;
extern const tFont g_sFontCmss28i;
extern const tFont g_sFontCmss30;
extern const tFont g_sFontCmss30b;
extern const tFont g_sFontCmss30i;
extern const tFont g_sFontCmss32;
extern const tFont g_sFontCmss32b;
extern const tFont g_sFontCmss32i;
extern const tFont g_sFontCmss34;
extern const tFont g_sFontCmss34b;
extern const tFont g_sFontCmss34i;
extern const tFont g_sFontCmss36;
extern const tFont g_sFontCmss36b;
extern const tFont g_sFontCmss36i;
extern const tFont g_sFontCmss38;
extern const tFont g_sFontCmss38b;
extern const tFont g_sFontCmss38i;
extern const tFont g_sFontCmss40;
extern const tFont g_sFontCmss40b;
extern const tFont g_sFontCmss40i;
extern const tFont g_sFontCmss42;
extern const tFont g_sFontCmss42b;
extern const tFont g_sFontCmss42i;
extern const tFont g_sFontCmss44;
extern const tFont g_sFontCmss44b;
extern const tFont g_sFontCmss44i;
extern const tFont g_sFontCmss46;
extern const tFont g_sFontCmss46b;
extern const tFont g_sFontCmss46i;
extern const tFont g_sFontCmss48;
extern const tFont g_sFontCmss48b;
extern const tFont g_sFontCmss48i;
extern const tFont g_sFontFixed6x8;

//*****************************************************************************
//
//! Translates a 24-bit RGB color to a display driver-specific color.
//!
//! \param pDisplay is the pointer to the display driver structure for the
//! display to operate upon.
//! \param ulValue is the 24-bit RGB color.  The least-significant byte is the
//! blue channel, the next byte is the green channel, and the third byte is the
//! red channel.
//!
//! This function translates a 24-bit RGB color into a value that can be
//! written into the display's frame buffer in order to reproduce that color,
//! or the closest possible approximation of that color.
//!
//! \return Returns the display-driver specific color.
//
//*****************************************************************************
#define DpyColorTranslate(pDisplay, ulValue)                                \
        ((pDisplay)->pfnColorTranslate((pDisplay)->pvDisplayData, ulValue))

//*****************************************************************************
//
//! Flushes cached drawing operations.
//!
//! \param pDisplay is the pointer to the display driver structure for the
//! display to operate upon.
//!
//! This function flushes any cached drawing operations on a display.
//!
//! \return None.
//
//*****************************************************************************
#define DpyFlush(pDisplay)                   \
        do                                   \
        {                                    \
            const tDisplay *pD = pDisplay;   \
            pD->pfnFlush(pD->pvDisplayData); \
        }                                    \
        while(0)

//*****************************************************************************
//
//! Gets the height of the display.
//!
//! \param pDisplay is a pointer to the display driver structure for the
//! display to query.
//!
//! This function determines the height of the display.
//!
//! \return Returns the height of the display in pixels.
//
//*****************************************************************************
#define DpyHeightGet(pDisplay) \
        ((pDisplay)->usHeight)

//*****************************************************************************
//
//! Draws a horizontal line on a display.
//!
//! \param pDisplay is the pointer to the display driver structure for the
//! display to operate upon.
//! \param lX1 is the starting X coordinate of the line.
//! \param lX2 is the ending X coordinate of the line.
//! \param lY is the Y coordinate of the line.
//! \param ulValue is the color to draw the line.
//!
//! This function draws a horizontal line on a display.  This assumes that
//! clipping has already been performed, and that both end points of the line
//! are within the extents of the display.
//!
//! \return None.
//
//*****************************************************************************
#define DpyLineDrawH(pDisplay, lX1, lX2, lY, ulValue)                   \
        do                                                              \
        {                                                               \
            const tDisplay *pD = pDisplay;                              \
            pD->pfnLineDrawH(pD->pvDisplayData, lX1, lX2, lY, ulValue); \
        }                                                               \
        while(0)

//*****************************************************************************
//
//! Draws a vertical line on a display.
//!
//! \param pDisplay is the pointer to the display driver structure for the
//! display to operate upon.
//! \param lX is the X coordinate of the line.
//! \param lY1 is the starting Y coordinate of the line.
//! \param lY2 is the ending Y coordinate of the line.
//! \param ulValue is the color to draw the line.
//!
//! This function draws a vertical line on a display.  This assumes that
//! clipping has already been performed, and that both end points of the line
//! are within the extents of the display.
//!
//! \return None.
//
//*****************************************************************************
#define DpyLineDrawV(pDisplay, lX, lY1, lY2, ulValue)                   \
        do                                                              \
        {                                                               \
            const tDisplay *pD = pDisplay;                              \
            pD->pfnLineDrawV(pD->pvDisplayData, lX, lY1, lY2, ulValue); \
        }                                                               \
        while(0)

//*****************************************************************************
//
//! Draws a pixel on a display.
//!
//! \param pDisplay is the pointer to the display driver structure for the
//! display to operate upon.
//! \param lX is the X coordinate of the pixel.
//! \param lY is the Y coordinate of the pixel.
//! \param ulValue is the color to draw the pixel.
//!
//! This function draws a pixel on a display.  This assumes that clipping has
//! already been performed.
//!
//! \return None.
//
//*****************************************************************************
#define DpyPixelDraw(pDisplay, lX, lY, ulValue)                   \
        do                                                        \
        {                                                         \
            const tDisplay *pD = pDisplay;                        \
            pD->pfnPixelDraw(pD->pvDisplayData, lX, lY, ulValue); \
        }                                                         \
        while(0)

//*****************************************************************************
//
//! Draws a horizontal sequence of pixels on a display.
//!
//! \param pDisplay is the pointer to the display driver structure for the
//! display to operate upon.
//! \param lX is the X coordinate of the first pixel.
//! \param lY is the Y coordinate of the first pixel.
//! \param lX0 is sub-pixel offset within the pixel data, which is valid for 1
//! or 4 bit per pixel formats.
//! \param lCount is the number of pixels to draw.
//! \param lBPP is the number of bits per pixel; must be 1, 4, or 8.
//! \param pucData is a pointer to the pixel data.  For 1 and 4 bit per pixel
//! formats, the most significant bit(s) represent the left-most pixel.
//! \param pucPalette is a pointer to the palette used to draw the pixels.
//!
//! This function draws a horizontal sequence of pixels on a display, using the
//! supplied palette.  For 1 bit per pixel format, the palette contains
//! pre-translated colors; for 4 and 8 bit per pixel formats, the palette
//! contains 24-bit RGB values that must be translated before being written to
//! the display.
//!
//! \return None.
//
//*****************************************************************************
#define DpyPixelDrawMultiple(pDisplay, lX, lY, lX0, lCount, lBPP, pucData,   \
                             pucPalette)                                     \
        do                                                                   \
        {                                                                    \
            const tDisplay *pD = pDisplay;                                   \
            pD->pfnPixelDrawMultiple(pD->pvDisplayData, lX, lY, lX0, lCount, \
                                     lBPP, pucData, pucPalette);             \
        }                                                                    \
        while(0)

//*****************************************************************************
//
//! Fills a rectangle on a display.
//!
//! \param pDisplay is the pointer to the display driver structure for the
//! display to operate upon.
//! \param pRect is a pointer to the structure describing the rectangle to
//! fill.
//! \param ulValue is the color to fill the rectangle.
//!
//! This function fills a rectangle on the display.  This assumes that clipping
//! has already been performed, and that all sides of the rectangle are within
//! the extents of the display.
//!
//! \return None.
//
//*****************************************************************************
#define DpyRectFill(pDisplay, pRect, ulValue)                   \
        do                                                      \
        {                                                       \
            const tDisplay *pD = pDisplay;                      \
            pD->pfnRectFill(pD->pvDisplayData, pRect, ulValue); \
        }                                                       \
        while(0)

//*****************************************************************************
//
//! Gets the width of the display.
//!
//! \param pDisplay is a pointer to the display driver structure for the
//! display to query.
//!
//! This function determines the width of the display.
//!
//! \return Returns the width of the display in pixels.
//
//*****************************************************************************
#define DpyWidthGet(pDisplay) \
        ((pDisplay)->usWidth)

//*****************************************************************************
//
// Prototypes for the graphics library functions.
//
//*****************************************************************************
extern void GrCircleDraw(const tContext *pContext, long lX, long lY,
                         long lRadius);
extern void GrCircleFill(const tContext *pContext, long lX, long lY,
                         long lRadius);
extern void GrContextClipRegionSet(tContext *pContext, tRectangle *pRect);
extern void GrContextInit(tContext *pContext, const tDisplay *pDisplay);
extern void GrImageDraw(const tContext *pContext,
                        const unsigned char *pucImage, long lX, long lY);
extern void GrLineDraw(const tContext *pContext, long lX1, long lY1, long lX2,
                       long lY2);
extern void GrLineDrawH(const tContext *pContext, long lX1, long lX2, long lY);
extern void GrLineDrawV(const tContext *pContext, long lX, long lY1, long lY2);
extern void GrOffScreen1BPPInit(tDisplay *pDisplay, unsigned char *pucImage,
                                long lWidth, long lHeight);
extern void GrOffScreen4BPPInit(tDisplay *pDisplay, unsigned char *pucImage,
                                long lWidth, long lHeight);
extern void GrOffScreen4BPPPaletteSet(tDisplay *pDisplay,
                                      unsigned long *pulPalette,
                                      unsigned long ulOffset,
                                      unsigned long ulCount);
extern void GrOffScreen8BPPInit(tDisplay *pDisplay, unsigned char *pucImage,
                                long lWidth, long lHeight);
extern void GrOffScreen8BPPPaletteSet(tDisplay *pDisplay,
                                      unsigned long *pulPalette,
                                      unsigned long ulOffset,
                                      unsigned long ulCount);
extern void GrRectDraw(const tContext *pContext, const tRectangle *pRect);
extern void GrRectFill(const tContext *pContext, const tRectangle *pRect);
extern void GrStringDraw(const tContext *pContext, const char *pcString,
                         long lLength, long lX, long lY,
                         unsigned long bOpaque);
extern long GrStringWidthGet(const tContext *pContext, const char *pcString,
                             long lLength);

//*****************************************************************************
//
// Mark the end of the C bindings section for C++ compilers.
//
//*****************************************************************************
#ifdef __cplusplus
}
#endif

//*****************************************************************************
//
// Close the Doxygen group.
//! @}
//
//*****************************************************************************

#endif // __GRLIB_H__
