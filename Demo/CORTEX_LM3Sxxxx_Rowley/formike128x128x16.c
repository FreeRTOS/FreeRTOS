//*****************************************************************************
//
// formike128x128x16.c - Display driver for the Formike Electronic
//                       KWH015C04-F01 CSTN panel with an ST7637 controller.
//
// Copyright (c) 2008 Luminary Micro, Inc.  All rights reserved.
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
// This is part of revision 2523 of the Stellaris Peripheral Driver Library.
//
//*****************************************************************************

//*****************************************************************************
//
//! \addtogroup ek_lm3s3748_api
//! @{
//
//*****************************************************************************

#include "hw_gpio.h"
#include "hw_memmap.h"
#include "hw_types.h"
#include "gpio.h"
#include "sysctl.h"
#include "rom.h"
#include "grlib.h"
#include "formike128x128x16.h"
#include <string.h>

//*****************************************************************************
//
// Defines for the pins that are used to communicate with the ST7637.
//
//*****************************************************************************
#define LCD_A0_BASE            GPIO_PORTB_BASE
#define LCD_A0_PIN             GPIO_PIN_2
#define LCD_WR_BASE            GPIO_PORTC_BASE
#define LCD_WR_PIN             GPIO_PIN_4
#define LCD_RD_BASE            GPIO_PORTC_BASE
#define LCD_RD_PIN             GPIO_PIN_5
#define LCD_BL_BASE            GPIO_PORTF_BASE
#define LCD_BL_PIN             GPIO_PIN_1
#define LCD_DATA_BASE          GPIO_PORTG_BASE

//*****************************************************************************
//
// Translates a 24-bit RGB color to a display driver-specific color.
//
// \param c is the 24-bit RGB color.  The least-significant byte is the blue
// channel, the next byte is the green channel, and the third byte is the red
// channel.
//
// This macro translates a 24-bit RGB color into a value that can be written
// into the display's frame buffer in order to reproduce that color, or the
// closest possible approximation of that color.
//
// \return Returns the display-driver specific color.
//
//*****************************************************************************
#define DPYCOLORTRANSLATE(c)    ((((c) & 0x00ff0000) >> 19) |               \
                                 ((((c) & 0x0000ff00) >> 5) & 0x000007e0) | \
                                 ((((c) & 0x000000ff) << 8) & 0x0000f800))

//*****************************************************************************
//
// Writes a data word to the ST7637.
//
//*****************************************************************************
static void
WriteData(unsigned char ucData)
{
    //
    // Write the data to the data bus.
    //
    HWREG(LCD_DATA_BASE + GPIO_O_DATA + (0xff << 2)) = ucData;

    //
    // Assert the write enable signal.
    //
    HWREG(LCD_WR_BASE + GPIO_O_DATA + (LCD_WR_PIN << 2)) = 0;

    //
    // Deassert the write enable signal.
    //
    HWREG(LCD_WR_BASE + GPIO_O_DATA + (LCD_WR_PIN << 2)) = LCD_WR_PIN;
}

//*****************************************************************************
//
// Writes a command to the ST7637.
//
//*****************************************************************************
static void
WriteCommand(unsigned char ucData)
{
    //
    // Write the command to the data bus.
    //
    HWREG(LCD_DATA_BASE + GPIO_O_DATA + (0xff << 2)) = ucData;

    //
    // Set the A0 signal low, indicating a command.
    //
    HWREG(LCD_A0_BASE + GPIO_O_DATA + (LCD_A0_PIN << 2)) = 0;

    //
    // Assert the write enable signal.
    //
    HWREG(LCD_WR_BASE + GPIO_O_DATA + (LCD_WR_PIN << 2)) = 0;

    //
    // Deassert the write enable signal.
    //
    HWREG(LCD_WR_BASE + GPIO_O_DATA + (LCD_WR_PIN << 2)) = LCD_WR_PIN;

    //
    // Set the A0 signal high, indicating that following writes are data.
    //
    HWREG(LCD_A0_BASE + GPIO_O_DATA + (LCD_A0_PIN << 2)) = LCD_A0_PIN;
}

//*****************************************************************************
//
//! Initializes the display driver.
//!
//! This function initializes the ST7637 display controller on the panel,
//! preparing it to display data.
//!
//! \return None.
//
//*****************************************************************************
void
Formike128x128x16Init(void)
{
    unsigned long ulClockMS, ulCount;

    //
    // Get the value to pass to SysCtlDelay() in order to delay for 1 ms.
    //
    ulClockMS = SysCtlClockGet() / (3 * 1000);

    //
    // Enable the GPIO peripherals used to interface to the ST7637.
    //
    SysCtlPeripheralEnable(SYSCTL_PERIPH_GPIOB);
    SysCtlPeripheralEnable(SYSCTL_PERIPH_GPIOC);
    SysCtlPeripheralEnable(SYSCTL_PERIPH_GPIOF);
    SysCtlPeripheralEnable(SYSCTL_PERIPH_GPIOG);

    //
    // Configure the pins that connect to the LCD as GPIO outputs.
    //
    GPIOPinTypeGPIOOutput(LCD_A0_BASE, LCD_A0_PIN);
    GPIOPinTypeGPIOOutput(LCD_WR_BASE, LCD_WR_PIN);
    GPIOPinTypeGPIOOutput(LCD_RD_BASE, LCD_RD_PIN);
    GPIOPinTypeGPIOOutput(LCD_BL_BASE, LCD_BL_PIN);
    GPIOPinTypeGPIOOutput(LCD_DATA_BASE, 0xff);

    //
    // Set the LCD control pins to their default values.
    //
    GPIOPinWrite(LCD_A0_BASE, LCD_A0_PIN, LCD_A0_PIN);
    GPIOPinWrite(LCD_WR_BASE, LCD_WR_PIN | LCD_RD_PIN,
                     LCD_WR_PIN | LCD_RD_PIN);
    GPIOPinWrite(LCD_BL_BASE, LCD_BL_PIN, 0);
    GPIOPinWrite(LCD_DATA_BASE, 0xff, 0x00);

    //
    // Perform a software reset of the ST7637.
    //
    WriteCommand(0x01);

    //
    // Delay for 120ms.
    //
    SysCtlDelay(ulClockMS * 120);

    //
    // Disable auto-load of mask rom data.
    //
    WriteCommand(0xD7);
    WriteData(0xBF);

    //
    // Set the OTP control mode to read.
    //
    WriteCommand(0xE0);
    WriteData(0x00);

    //
    // Delay for 10ms.
    //
    SysCtlDelay(ulClockMS * 10);

    //
    // Start the OTP read.
    //
    WriteCommand(0xE3);

    //
    // Delay for 20ms.
    //
    SysCtlDelay(ulClockMS * 20);

    //
    // Cancel the OTP read (it should have finished by now).
    //
    WriteCommand(0xE1);

    //
    // Turn off the display.
    //
    WriteCommand(0x28);

    //
    // Exit sleep mode.
    //
    WriteCommand(0x11);

    //
    // Delay for 50ms.
    //
    SysCtlDelay(ulClockMS * 50);

    //
    // Program the LCD supply voltage V0 to 14V.
    //
    WriteCommand(0xC0);
    WriteData(0x04);
    WriteData(0x01);

    //
    // Select an LCD bias voltage ratio of 1/12.
    //
    WriteCommand(0xC3);
    WriteData(0x00);

    //
    // Enable the x8 booster circuit.
    //
    WriteCommand(0xC4);
    WriteData(0x07);

    //
    // Invert the column scan direction for the panel.
    //
    WriteCommand(0xB7);
    WriteData(0xC0);

    //
    // Select 16bpp, 5-6-5 data input mode.
    //
    WriteCommand(0x3A);
    WriteData(0x05);

    //
    // Select the memory scanning direction.  The scanning mode does not matter
    // for this driver since the row/column selects will constrain the writes
    // to the desired area of the display.
    //
    WriteCommand(0x36);
    WriteData(0x00);

    //
    // Turn on the display.
    //
    WriteCommand(0x29);

    //
    // Clear the contents of the display buffer.
    //
    WriteCommand(0x2A);
    WriteData(0x00);
    WriteData(0x7F);
    WriteCommand(0x2B);
    WriteData(0x01);
    WriteData(0x80);
    WriteCommand(0x2c);
    for(ulCount = 0; ulCount < (128 * 128); ulCount++)
    {
        WriteData(0x00);
        WriteData(0x00);
    }

    //
    // Enable normal operation of the LCD.
    //
    WriteCommand(0x13);
}

//*****************************************************************************
//
//! Turns on the backlight.
//!
//! This function turns on the backlight on the display.
//!
//! \return None.
//
//*****************************************************************************
void
Formike128x128x16BacklightOn(void)
{
    //
    // Assert the signal that turns on the backlight.
    //
    HWREG(LCD_BL_BASE + GPIO_O_DATA + (LCD_BL_PIN << 2)) = LCD_BL_PIN;
}

//*****************************************************************************
//
//! Turns off the backlight.
//!
//! This function turns off the backlight on the display.
//!
//! \return None.
//
//*****************************************************************************
void
Formike128x128x16BacklightOff(void)
{
    //
    // Deassert the signal that turns on the backlight.
    //
    HWREG(LCD_BL_BASE + GPIO_O_DATA + (LCD_BL_PIN << 2)) = 0;
}

//*****************************************************************************
//
//! Draws a pixel on the screen.
//!
//! \param pvDisplayData is a pointer to the driver-specific data for this
//! display driver.
//! \param lX is the X coordinate of the pixel.
//! \param lY is the Y coordinate of the pixel.
//! \param ulValue is the color of the pixel.
//!
//! This function sets the given pixel to a particular color.  The coordinates
//! of the pixel are assumed to be within the extents of the display.
//!
//! \return None.
//
//*****************************************************************************
static void
Formike128x128x16PixelDraw(void *pvDisplayData, long lX, long lY,
                           unsigned long ulValue)
{
    //
    // Set the X address of the display cursor.
    //
    WriteCommand(0x2a);
    WriteData(lX);
    WriteData(lX);

    //
    // Set the Y address of the display cursor.
    //
    WriteCommand(0x2b);
    WriteData(lY + 1);
    WriteData(lY + 1);

    //
    // Write the pixel value.
    //
    WriteCommand(0x2c);
    WriteData(ulValue >> 8);
    WriteData(ulValue);
}

//*****************************************************************************
//
//! Draws a horizontal sequence of pixels on the screen.
//!
//! \param pvDisplayData is a pointer to the driver-specific data for this
//! display driver.
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
//! This function draws a horizontal sequence of pixels on the screen, using
//! the supplied palette.  For 1 bit per pixel format, the palette contains
//! pre-translated colors; for 4 and 8 bit per pixel formats, the palette
//! contains 24-bit RGB values that must be translated before being written to
//! the display.
//!
//! \return None.
//
//*****************************************************************************
static void
Formike128x128x16PixelDrawMultiple(void *pvDisplayData, long lX, long lY,
                                   long lX0, long lCount, long lBPP,
                                   const unsigned char *pucData,
                                   const unsigned char *pucPalette)
{
    unsigned long ulByte;

    //
    // Set the extent of the line along the X axis.
    //
    WriteCommand(0x2a);
    WriteData(lX);
    WriteData(lX + lCount - 1);

    //
    // Set the Y address of the display cursor.
    //
    WriteCommand(0x2b);
    WriteData(lY + 1);
    WriteData(lY + 1);

    //
    // Write the data RAM write command.
    //
    WriteCommand(0x2c);

    //
    // Determine how to interpret the pixel data based on the number of bits
    // per pixel.
    //
    switch(lBPP)
    {
        //
        // The pixel data is in 1 bit per pixel format.
        //
        case 1:
        {
            //
            // Loop while there are more pixels to draw.
            //
            while(lCount)
            {
                //
                // Get the next byte of image data.
                //
                ulByte = *pucData++;

                //
                // Loop through the pixels in this byte of image data.
                //
                for(; (lX0 < 8) && lCount; lX0++, lCount--)
                {
                    //
                    // Draw this pixel in the appropriate color.
                    //
                    lBPP = ((unsigned long *)pucPalette)[(ulByte >>
                                                          (7 - lX0)) & 1];
                    WriteData(lBPP >> 8);
                    WriteData(lBPP);
                }

                //
                // Start at the beginning of the next byte of image data.
                //
                lX0 = 0;
            }

            //
            // The image data has been drawn.
            //
            break;
        }

        //
        // The pixel data is in 4 bit per pixel format.
        //
        case 4:
        {
            //
            // Loop while there are more pixels to draw.  "Duff's device" is
            // used to jump into the middle of the loop if the first nibble of
            // the pixel data should not be used.  Duff's device makes use of
            // the fact that a case statement is legal anywhere within a
            // sub-block of a switch statement.  See
            // http://en.wikipedia.org/wiki/Duff's_device for detailed
            // information about Duff's device.
            //
            switch(lX0 & 1)
            {
                case 0:
                    while(lCount)
                    {
                        //
                        // Get the upper nibble of the next byte of pixel data
                        // and extract the corresponding entry from the
                        // palette.
                        //
                        ulByte = (*pucData >> 4) * 3;
                        ulByte = (*(unsigned long *)(pucPalette + ulByte) &
                                  0x00ffffff);

                        //
                        // Translate this palette entry and write it to the
                        // screen.
                        //
                        ulByte = DPYCOLORTRANSLATE(ulByte);
                        WriteData(ulByte >> 8);
                        WriteData(ulByte);

                        //
                        // Decrement the count of pixels to draw.
                        //
                        lCount--;

                        //
                        // See if there is another pixel to draw.
                        //
                        if(lCount)
                        {
                case 1:
                            //
                            // Get the lower nibble of the next byte of pixel
                            // data and extract the corresponding entry from
                            // the palette.
                            //
                            ulByte = (*pucData++ & 15) * 3;
                            ulByte = (*(unsigned long *)(pucPalette + ulByte) &
                                      0x00ffffff);

                            //
                            // Translate this palette entry and write it to the
                            // screen.
                            //
                            ulByte = DPYCOLORTRANSLATE(ulByte);
                            WriteData(ulByte >> 8);
                            WriteData(ulByte);

                            //
                            // Decrement the count of pixels to draw.
                            //
                            lCount--;
                        }
                    }
            }

            //
            // The image data has been drawn.
            //
            break;
        }

        //
        // The pixel data is in 8 bit per pixel format.
        //
        case 8:
        {
            //
            // Loop while there are more pixels to draw.
            //
            while(lCount--)
            {
                //
                // Get the next byte of pixel data and extract the
                // corresponding entry from the palette.
                //
                ulByte = *pucData++ * 3;
                ulByte = *(unsigned long *)(pucPalette + ulByte) & 0x00ffffff;

                //
                // Translate this palette entry and write it to the screen.
                //
                ulByte = DPYCOLORTRANSLATE(ulByte);
                WriteData(ulByte >> 8);
                WriteData(ulByte);
            }

            //
            // The image data has been drawn.
            //
            break;
        }
    }
}

//*****************************************************************************
//
//! Flushes any cached drawing operations.
//!
//! \param pvDisplayData is a pointer to the driver-specific data for this
//! display driver.
//!
//! This functions flushes any cached drawing operations to the display.  This
//! is useful when a local frame buffer is used for drawing operations, and the
//! flush would copy the local frame buffer to the display.  For the ST7637
//! driver, the flush is a no operation.
//!
//! \return None.
//
//*****************************************************************************
static void
Formike128x128x16Flush(void *pvDisplayData)
{
    //
    // There is nothing to be done.
    //
}

//*****************************************************************************
//
//! Draws a horizontal line.
//!
//! \param pvDisplayData is a pointer to the driver-specific data for this
//! display driver.
//! \param lX1 is the X coordinate of the start of the line.
//! \param lX2 is the X coordinate of the end of the line.
//! \param lY is the Y coordinate of the line.
//! \param ulValue is the color of the line.
//!
//! This function draws a horizontal line on the display.  The coordinates of
//! the line are assumed to be within the extents of the display.
//!
//! \return None.
//
//*****************************************************************************
static void
Formike128x128x16LineDrawH(void *pvDisplayData, long lX1, long lX2, long lY,
                           unsigned long ulValue)
{
    //
    // Set the extent of the line along the X axis.
    //
    WriteCommand(0x2a);
    WriteData(lX1);
    WriteData(lX2);

    //
    // Set the Y address of the display cursor.
    //
    WriteCommand(0x2b);
    WriteData(lY + 1);
    WriteData(lY + 1);

    //
    // Write the data RAM write command.
    //
    WriteCommand(0x2c);

    //
    // Loop through the pixels of this horizontal line.
    //
    while(lX1++ <= lX2)
    {
        //
        // Write the pixel value.
        //
        WriteData(ulValue >> 8);
        WriteData(ulValue);
    }
}

//*****************************************************************************
//
//! Draws a vertical line.
//!
//! \param pvDisplayData is a pointer to the driver-specific data for this
//! display driver.
//! \param lX is the X coordinate of the line.
//! \param lY1 is the Y coordinate of the start of the line.
//! \param lY2 is the Y coordinate of the end of the line.
//! \param ulValue is the color of the line.
//!
//! This function draws a vertical line on the display.  The coordinates of the
//! line are assumed to be within the extents of the display.
//!
//! \return None.
//
//*****************************************************************************
static void
Formike128x128x16LineDrawV(void *pvDisplayData, long lX, long lY1, long lY2,
                           unsigned long ulValue)
{
    //
    // Set the X address of the display cursor.
    //
    WriteCommand(0x2a);
    WriteData(lX);
    WriteData(lX);

    //
    // Set the extent of the line along the Y axis.
    //
    WriteCommand(0x2b);
    WriteData(lY1 + 1);
    WriteData(lY2 + 1);

    //
    // Write the data RAM write command.
    //
    WriteCommand(0x2c);

    //
    // Loop through the pixels of this vertical line.
    //
    while(lY1++ <= lY2)
    {
        //
        // Write the pixel value.
        //
        WriteData(ulValue >> 8);
        WriteData(ulValue);
    }
}

//*****************************************************************************
//
//! Fills a rectangle.
//!
//! \param pvDisplayData is a pointer to the driver-specific data for this
//! display driver.
//! \param pRect is a pointer to the structure describing the rectangle.
//! \param ulValue is the color of the rectangle.
//!
//! This function fills a rectangle on the display.  The coordinates of the
//! rectangle are assumed to be within the extents of the display, and the
//! rectangle specification is fully inclusive (i.e. both sXMin and sXMax are
//! drawn, along with sYMin and sYMax).
//!
//! \return None.
//
//*****************************************************************************
static void
Formike128x128x16RectFill(void *pvDisplayData, const tRectangle *pRect,
                          unsigned long ulValue)
{
    long lCount;

    //
    // Set the extent of the rectangle along the X axis.
    //
    WriteCommand(0x2a);
    WriteData(pRect->sXMin);
    WriteData(pRect->sXMax);

    //
    // Set the extent of the rectangle along the Y axis.
    //
    WriteCommand(0x2b);
    WriteData(pRect->sYMin + 1);
    WriteData(pRect->sYMax + 1);

    //
    // Write the data RAM write command.
    //
    WriteCommand(0x2c);

    //
    // Loop through the pixels in this rectangle.
    //
    for(lCount = ((pRect->sXMax - pRect->sXMin + 1) *
                  (pRect->sYMax - pRect->sYMin + 1)); lCount > 0; lCount--)
    {
        //
        // Write the pixel value.
        //
        WriteData(ulValue >> 8);
        WriteData(ulValue);
    }
}

//*****************************************************************************
//
//! Translates a 24-bit RGB color to a display driver-specific color.
//!
//! \param pvDisplayData is a pointer to the driver-specific data for this
//! display driver.
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
static unsigned long
Formike128x128x16ColorTranslate(void *pvDisplayData, unsigned long ulValue)
{
    //
    // Translate from a 24-bit RGB color to a 5-6-5 RGB color.
    //
    return(DPYCOLORTRANSLATE(ulValue));
}

//*****************************************************************************
//
//! The display structure that describes the driver for the Formike Electronic
//! KWH015C04-F01 CSTN panel with an ST7637 controller.
//
//*****************************************************************************
const tDisplay g_sFormike128x128x16 =
{
    sizeof(tDisplay),
    0,
    128,
    128,
    Formike128x128x16PixelDraw,
    Formike128x128x16PixelDrawMultiple,
    Formike128x128x16LineDrawH,
    Formike128x128x16LineDrawV,
    Formike128x128x16RectFill,
    Formike128x128x16ColorTranslate,
    Formike128x128x16Flush
};

//*****************************************************************************
//
// Close the Doxygen group.
//! @}
//
//*****************************************************************************
















/* FreeRTOS.org demo wrappers.  These are required so the prototypes for the
functions are the same as for the display drivers used by other evaluation
kits. */

static tContext sContext;

void vFormike128x128x16Clear( void )
{
const tRectangle xRectangle = { 0, 0, 127, 127 };

    GrContextForegroundSet( &sContext, ClrBlack );
    GrRectFill( &sContext, &xRectangle );
	GrContextForegroundSet(&sContext, ClrWhite);
}
/*-----------------------------------------------------------*/

void vFormike128x128x16StringDraw( const char *pcString, unsigned long lX, unsigned long lY, unsigned char ucColor )
{
	GrContextForegroundSet(&sContext, ClrWhite);
	GrStringDraw( &sContext, pcString, strlen( pcString ), lX, lY, false );
}
/*-----------------------------------------------------------*/

void vFormike128x128x16Init( unsigned long ul )
{
tRectangle rectScreen;
const unsigned char *pcAppName = "www.FreeRTOS.org";

	( void ) ul;
	
    Formike128x128x16Init();
    Formike128x128x16BacklightOn();
    GrContextInit(&sContext, &g_sFormike128x128x16);
    GrContextFontSet(&sContext, &g_sFontCmss12);
    rectScreen.sXMin = 0;

	/* Fill the screen with a black rectangle. */
    rectScreen.sYMin = 0;
    rectScreen.sXMax = g_sFormike128x128x16.usWidth - 1;
    rectScreen.sYMax = g_sFormike128x128x16.usHeight - 1;
    GrContextForegroundSet(&sContext, ClrBlack);
    GrRectFill(&sContext, &rectScreen);
}
/*-----------------------------------------------------------*/

void vFormike128x128x16ImageDraw( const unsigned char *pucImage, unsigned long ulX, unsigned long ulY, unsigned long ulWidth, unsigned long ulHeight )
{
	GrImageDraw( &sContext, pucImage, ( long ) ulX, ( long ) ulY);
}




