//*****************************************************************************
//
// osram96x16.c - Driver for the OSRAM 96x16 graphical OLED display.
//
// Copyright (c) 2006-2007 Luminary Micro, Inc.  All rights reserved.
//
// Software License Agreement
//
// Luminary Micro, Inc. (LMI) is supplying this software for use solely and
// exclusively on LMI's microcontroller products.
//
// The software is owned by LMI and/or its suppliers, and is protected under
// applicable copyright laws.  All rights are reserved.  Any use in violation
// of the foregoing restrictions may subject the user to criminal sanctions
// under applicable laws, as well as to civil liability for the breach of the
// terms and conditions of this license.
//
// THIS SOFTWARE IS PROVIDED "AS IS".  NO WARRANTIES, WHETHER EXPRESS, IMPLIED
// OR STATUTORY, INCLUDING, BUT NOT LIMITED TO, IMPLIED WARRANTIES OF
// MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE APPLY TO THIS SOFTWARE.
// LMI SHALL NOT, IN ANY CIRCUMSTANCES, BE LIABLE FOR SPECIAL, INCIDENTAL, OR
// CONSEQUENTIAL DAMAGES, FOR ANY REASON WHATSOEVER.
//
// This is part of revision 1049 of the Stellaris Driver Library.
//
//*****************************************************************************

//*****************************************************************************
//
//! \addtogroup ev_lm3s811_api
//! @{
//
//*****************************************************************************

#include "hw_i2c.h"
#include "hw_memmap.h"
#include "hw_sysctl.h"
#include "hw_types.h"
#include "debug.h"
#include "gpio.h"
#include "i2c.h"
#include "sysctl.h"
#include "osram96x16.h"

//*****************************************************************************
//
// The I2C slave address of the SSD0303 controller on the OLED display.
//
//*****************************************************************************
#define SSD0303_ADDR            0x3d

//*****************************************************************************
//
// A 5x7 font (in a 6x8 cell, where the sixth column is omitted from this
// table) for displaying text on the OLED display.  The data is organized as
// bytes from the left column to the right column, with each byte containing
// the top row in the LSB and the bottom row in the MSB.
//
//*****************************************************************************
static const unsigned char g_pucFont[95][5] =
{
    { 0x00, 0x00, 0x00, 0x00, 0x00 }, // " "
    { 0x00, 0x00, 0x4f, 0x00, 0x00 }, // !
    { 0x00, 0x07, 0x00, 0x07, 0x00 }, // "
    { 0x14, 0x7f, 0x14, 0x7f, 0x14 }, // #
    { 0x24, 0x2a, 0x7f, 0x2a, 0x12 }, // $
    { 0x23, 0x13, 0x08, 0x64, 0x62 }, // %
    { 0x36, 0x49, 0x55, 0x22, 0x50 }, // &
    { 0x00, 0x05, 0x03, 0x00, 0x00 }, // '
    { 0x00, 0x1c, 0x22, 0x41, 0x00 }, // (
    { 0x00, 0x41, 0x22, 0x1c, 0x00 }, // )
    { 0x14, 0x08, 0x3e, 0x08, 0x14 }, // *
    { 0x08, 0x08, 0x3e, 0x08, 0x08 }, // +
    { 0x00, 0x50, 0x30, 0x00, 0x00 }, // ,
    { 0x08, 0x08, 0x08, 0x08, 0x08 }, // -
    { 0x00, 0x60, 0x60, 0x00, 0x00 }, // .
    { 0x20, 0x10, 0x08, 0x04, 0x02 }, // /
    { 0x3e, 0x51, 0x49, 0x45, 0x3e }, // 0
    { 0x00, 0x42, 0x7f, 0x40, 0x00 }, // 1
    { 0x42, 0x61, 0x51, 0x49, 0x46 }, // 2
    { 0x21, 0x41, 0x45, 0x4b, 0x31 }, // 3
    { 0x18, 0x14, 0x12, 0x7f, 0x10 }, // 4
    { 0x27, 0x45, 0x45, 0x45, 0x39 }, // 5
    { 0x3c, 0x4a, 0x49, 0x49, 0x30 }, // 6
    { 0x01, 0x71, 0x09, 0x05, 0x03 }, // 7
    { 0x36, 0x49, 0x49, 0x49, 0x36 }, // 8
    { 0x06, 0x49, 0x49, 0x29, 0x1e }, // 9
    { 0x00, 0x36, 0x36, 0x00, 0x00 }, // :
    { 0x00, 0x56, 0x36, 0x00, 0x00 }, // ;
    { 0x08, 0x14, 0x22, 0x41, 0x00 }, // <
    { 0x14, 0x14, 0x14, 0x14, 0x14 }, // =
    { 0x00, 0x41, 0x22, 0x14, 0x08 }, // >
    { 0x02, 0x01, 0x51, 0x09, 0x06 }, // ?
    { 0x32, 0x49, 0x79, 0x41, 0x3e }, // @
    { 0x7e, 0x11, 0x11, 0x11, 0x7e }, // A
    { 0x7f, 0x49, 0x49, 0x49, 0x36 }, // B
    { 0x3e, 0x41, 0x41, 0x41, 0x22 }, // C
    { 0x7f, 0x41, 0x41, 0x22, 0x1c }, // D
    { 0x7f, 0x49, 0x49, 0x49, 0x41 }, // E
    { 0x7f, 0x09, 0x09, 0x09, 0x01 }, // F
    { 0x3e, 0x41, 0x49, 0x49, 0x7a }, // G
    { 0x7f, 0x08, 0x08, 0x08, 0x7f }, // H
    { 0x00, 0x41, 0x7f, 0x41, 0x00 }, // I
    { 0x20, 0x40, 0x41, 0x3f, 0x01 }, // J
    { 0x7f, 0x08, 0x14, 0x22, 0x41 }, // K
    { 0x7f, 0x40, 0x40, 0x40, 0x40 }, // L
    { 0x7f, 0x02, 0x0c, 0x02, 0x7f }, // M
    { 0x7f, 0x04, 0x08, 0x10, 0x7f }, // N
    { 0x3e, 0x41, 0x41, 0x41, 0x3e }, // O
    { 0x7f, 0x09, 0x09, 0x09, 0x06 }, // P
    { 0x3e, 0x41, 0x51, 0x21, 0x5e }, // Q
    { 0x7f, 0x09, 0x19, 0x29, 0x46 }, // R
    { 0x46, 0x49, 0x49, 0x49, 0x31 }, // S
    { 0x01, 0x01, 0x7f, 0x01, 0x01 }, // T
    { 0x3f, 0x40, 0x40, 0x40, 0x3f }, // U
    { 0x1f, 0x20, 0x40, 0x20, 0x1f }, // V
    { 0x3f, 0x40, 0x38, 0x40, 0x3f }, // W
    { 0x63, 0x14, 0x08, 0x14, 0x63 }, // X
    { 0x07, 0x08, 0x70, 0x08, 0x07 }, // Y
    { 0x61, 0x51, 0x49, 0x45, 0x43 }, // Z
    { 0x00, 0x7f, 0x41, 0x41, 0x00 }, // [
    { 0x02, 0x04, 0x08, 0x10, 0x20 }, // "\"
    { 0x00, 0x41, 0x41, 0x7f, 0x00 }, // ]
    { 0x04, 0x02, 0x01, 0x02, 0x04 }, // ^
    { 0x40, 0x40, 0x40, 0x40, 0x40 }, // _
    { 0x00, 0x01, 0x02, 0x04, 0x00 }, // `
    { 0x20, 0x54, 0x54, 0x54, 0x78 }, // a
    { 0x7f, 0x48, 0x44, 0x44, 0x38 }, // b
    { 0x38, 0x44, 0x44, 0x44, 0x20 }, // c
    { 0x38, 0x44, 0x44, 0x48, 0x7f }, // d
    { 0x38, 0x54, 0x54, 0x54, 0x18 }, // e
    { 0x08, 0x7e, 0x09, 0x01, 0x02 }, // f
    { 0x0c, 0x52, 0x52, 0x52, 0x3e }, // g
    { 0x7f, 0x08, 0x04, 0x04, 0x78 }, // h
    { 0x00, 0x44, 0x7d, 0x40, 0x00 }, // i
    { 0x20, 0x40, 0x44, 0x3d, 0x00 }, // j
    { 0x7f, 0x10, 0x28, 0x44, 0x00 }, // k
    { 0x00, 0x41, 0x7f, 0x40, 0x00 }, // l
    { 0x7c, 0x04, 0x18, 0x04, 0x78 }, // m
    { 0x7c, 0x08, 0x04, 0x04, 0x78 }, // n
    { 0x38, 0x44, 0x44, 0x44, 0x38 }, // o
    { 0x7c, 0x14, 0x14, 0x14, 0x08 }, // p
    { 0x08, 0x14, 0x14, 0x18, 0x7c }, // q
    { 0x7c, 0x08, 0x04, 0x04, 0x08 }, // r
    { 0x48, 0x54, 0x54, 0x54, 0x20 }, // s
    { 0x04, 0x3f, 0x44, 0x40, 0x20 }, // t
    { 0x3c, 0x40, 0x40, 0x20, 0x7c }, // u
    { 0x1c, 0x20, 0x40, 0x20, 0x1c }, // v
    { 0x3c, 0x40, 0x30, 0x40, 0x3c }, // w
    { 0x44, 0x28, 0x10, 0x28, 0x44 }, // x
    { 0x0c, 0x50, 0x50, 0x50, 0x3c }, // y
    { 0x44, 0x64, 0x54, 0x4c, 0x44 }, // z
    { 0x00, 0x08, 0x36, 0x41, 0x00 }, // {
    { 0x00, 0x00, 0x7f, 0x00, 0x00 }, // |
    { 0x00, 0x41, 0x36, 0x08, 0x00 }, // }
    { 0x02, 0x01, 0x02, 0x04, 0x02 }, // ~
};

//*****************************************************************************
//
// The sequence of commands used to initialize the SSD0303 controller.  Each
// command is described as follows:  there is a byte specifying the number of
// bytes in the I2C transfer, followed by that many bytes of command data.
//
//*****************************************************************************
static const unsigned char g_pucOSRAMInit[] =
{
    //
    // Turn off the panel
    //
    0x04, 0x80, 0xae, 0x80, 0xe3,

    //
    // Set lower column address
    //
    0x04, 0x80, 0x04, 0x80, 0xe3,

    //
    // Set higher column address
    //
    0x04, 0x80, 0x12, 0x80, 0xe3,

    //
    // Set contrast control register
    //
    0x06, 0x80, 0x81, 0x80, 0x2b, 0x80, 0xe3,

    //
    // Set segment re-map
    //
    0x04, 0x80, 0xa1, 0x80, 0xe3,

    //
    // Set display start line
    //
    0x04, 0x80, 0x40, 0x80, 0xe3,

    //
    // Set display offset
    //
    0x06, 0x80, 0xd3, 0x80, 0x00, 0x80, 0xe3,

    //
    // Set multiplex ratio
    //
    0x06, 0x80, 0xa8, 0x80, 0x0f, 0x80, 0xe3,

    //
    // Set the display to normal mode
    //
    0x04, 0x80, 0xa4, 0x80, 0xe3,

    //
    // Non-inverted display
    //
    0x04, 0x80, 0xa6, 0x80, 0xe3,

    //
    // Set the page address
    //
    0x04, 0x80, 0xb0, 0x80, 0xe3,

    //
    // Set COM output scan direction
    //
    0x04, 0x80, 0xc8, 0x80, 0xe3,

    //
    // Set display clock divide ratio/oscillator frequency
    //
    0x06, 0x80, 0xd5, 0x80, 0x72, 0x80, 0xe3,

    //
    // Enable mono mode
    //
    0x06, 0x80, 0xd8, 0x80, 0x00, 0x80, 0xe3,

    //
    // Set pre-charge period
    //
    0x06, 0x80, 0xd9, 0x80, 0x22, 0x80, 0xe3,

    //
    // Set COM pins hardware configuration
    //
    0x06, 0x80, 0xda, 0x80, 0x12, 0x80, 0xe3,

    //
    // Set VCOM deslect level
    //
    0x06, 0x80, 0xdb, 0x80, 0x0f, 0x80, 0xe3,

    //
    // Set DC-DC on
    //
    0x06, 0x80, 0xad, 0x80, 0x8b, 0x80, 0xe3,

    //
    // Turn on the panel
    //
    0x04, 0x80, 0xaf, 0x80, 0xe3,
};

//*****************************************************************************
//
// The inter-byte delay required by the SSD0303 OLED controller.
//
//*****************************************************************************
static unsigned long g_ulDelay;

//*****************************************************************************
//
//! \internal
//!
//! Provide a small delay.
//!
//! \param ulCount is the number of delay loop iterations to perform.
//!
//! Since the SSD0303 controller needs a delay between bytes written to it over
//! the I2C bus, this function provides a means of generating that delay.  It
//! is written in assembly to keep the delay consistent across tool chains,
//! avoiding the need to tune the delay based on the tool chain in use.
//!
//! \return None.
//
//*****************************************************************************
#if defined(ewarm)
static void
OSRAMDelay(unsigned long ulCount)
{
    __asm("    subs    r0, #1\n"
          "    bne     OSRAMDelay\n"
          "    bx      lr");
}
#endif
#if defined(gcc)
static void __attribute__((naked))
OSRAMDelay(unsigned long ulCount)
{
    __asm("    subs    r0, #1\n"
          "    bne     OSRAMDelay\n"
          "    bx      lr");
}
#endif
#if defined(rvmdk) || defined(__ARMCC_VERSION)
__asm void
OSRAMDelay(unsigned long ulCount)
{
    subs    r0, #1;
    bne     OSRAMDelay;
    bx      lr;
}
#endif

//*****************************************************************************
//
//! \internal
//!
//! Start a transfer to the SSD0303 controller.
//!
//! \param ucChar is the first byte to be written to the controller.
//!
//! This function will start a transfer to the SSD0303 controller via the I2C
//! bus.
//!
//! The data is written in a polled fashion; this function will not return
//! until the byte has been written to the controller.
//!
//! \return None.
//
//*****************************************************************************
static void
OSRAMWriteFirst(unsigned char ucChar)
{
    //
    // Set the slave address.
    //
    I2CMasterSlaveAddrSet(I2C_MASTER_BASE, SSD0303_ADDR, false);

    //
    // Write the first byte to the controller.
    //
    I2CMasterDataPut(I2C_MASTER_BASE, ucChar);

    //
    // Start the transfer.
    //
    I2CMasterControl(I2C_MASTER_BASE, I2C_MASTER_CMD_BURST_SEND_START);
}

//*****************************************************************************
//
//! \internal
//!
//! Write a byte to the SSD0303 controller.
//!
//! \param ucChar is the byte to be transmitted to the controller.
//!
//! This function continues a transfer to the SSD0303 controller by writing
//! another byte over the I2C bus.  This must only be called after calling
//! OSRAMWriteFirst(), but before calling OSRAMWriteFinal().
//!
//! The data is written in a polled faashion; this function will not return
//! until the byte has been written to the controller.
//!
//! \return None.
//
//*****************************************************************************
static void
OSRAMWriteByte(unsigned char ucChar)
{
    //
    // Wait until the current byte has been transferred.
    //
    while(I2CMasterIntStatus(I2C_MASTER_BASE, false) == 0)
    {
    }

    //
    // Provide the required inter-byte delay.
    //
    OSRAMDelay(g_ulDelay);

    //
    // Write the next byte to the controller.
    //
    I2CMasterDataPut(I2C_MASTER_BASE, ucChar);

    //
    // Continue the transfer.
    //
    I2CMasterControl(I2C_MASTER_BASE, I2C_MASTER_CMD_BURST_SEND_CONT);
}

//*****************************************************************************
//
//! \internal
//!
//! Write a sequence of bytes to the SSD0303 controller.
//!
//! This function continues a transfer to the SSD0303 controller by writing a
//! sequence of bytes over the I2C bus.  This must only be called after calling
//! OSRAMWriteFirst(), but before calling OSRAMWriteFinal().
//!
//! The data is written in a polled fashion; this function will not return
//! until the entire byte sequence has been written to the controller.
//!
//! \return None.
//
//*****************************************************************************
static void
OSRAMWriteArray(const unsigned char *pucBuffer, unsigned long ulCount)
{
    //
    // Loop while there are more bytes left to be transferred.
    //
    while(ulCount != 0)
    {
        //
        // Wait until the current byte has been transferred.
        //
        while(I2CMasterIntStatus(I2C_MASTER_BASE, false) == 0)
        {
        }

        //
        // Provide the required inter-byte delay.
        //
        OSRAMDelay(g_ulDelay);

        //
        // Write the next byte to the controller.
        //
        I2CMasterDataPut(I2C_MASTER_BASE, *pucBuffer++);
        ulCount--;

        //
        // Continue the transfer.
        //
        I2CMasterControl(I2C_MASTER_BASE, I2C_MASTER_CMD_BURST_SEND_CONT);
    }
}

//*****************************************************************************
//
//! \internal
//!
//! Finish a transfer to the SSD0303 controller.
//!
//! \param ucChar is the final byte to be written to the controller.
//!
//! This function will finish a transfer to the SSD0303 controller via the I2C
//! bus.  This must only be called after calling OSRAMWriteFirst().
//!
//! The data is written in a polled fashion; this function will not return
//! until the byte has been written to the controller.
//!
//! \return None.
//
//*****************************************************************************
static void
OSRAMWriteFinal(unsigned char ucChar)
{
    //
    // Wait until the current byte has been transferred.
    //
    while(I2CMasterIntStatus(I2C_MASTER_BASE, false) == 0)
    {
    }

    //
    // Provide the required inter-byte delay.
    //
    OSRAMDelay(g_ulDelay);

    //
    // Write the final byte to the controller.
    //
    I2CMasterDataPut(I2C_MASTER_BASE, ucChar);

    //
    // Finish the transfer.
    //
    I2CMasterControl(I2C_MASTER_BASE, I2C_MASTER_CMD_BURST_SEND_FINISH);

    //
    // Wait until the final byte has been transferred.
    //
    while(I2CMasterIntStatus(I2C_MASTER_BASE, false) == 0)
    {
    }

    //
    // Provide the required inter-byte delay.
    //
    OSRAMDelay(g_ulDelay);
}

//*****************************************************************************
//
//! Clears the OLED display.
//!
//! This function will clear the display.  All pixels in the display will be
//! turned off.
//!
//! This function is contained in <tt>osram96x16.c</tt>, with
//! <tt>osram96x16.h</tt> containing the API definition for use by
//! applications.
//!
//! \return None.
//
//*****************************************************************************
void
OSRAMClear(void)
{
    static const unsigned char pucRow1[] =
    {
        0xb0, 0x80, 0x04, 0x80, 0x12, 0x40
    };
    static const unsigned char pucRow2[] =
    {
        0xb1, 0x80, 0x04, 0x80, 0x12, 0x40
    };
    unsigned long ulIdx;

    //
    // Move the display cursor to the first column of the first row.
    //
    OSRAMWriteFirst(0x80);
    OSRAMWriteArray(pucRow1, sizeof(pucRow1));

    //
    // Fill this row with zeros.
    //
    for(ulIdx = 0; ulIdx < 95; ulIdx++)
    {
        OSRAMWriteByte(0x00);
    }
    OSRAMWriteFinal(0x00);

    //
    // Move the display cursor to the first column of the second row.
    //
    OSRAMWriteFirst(0x80);
    OSRAMWriteArray(pucRow2, sizeof(pucRow2));

    //
    // Fill this row with zeros.
    //
    for(ulIdx = 0; ulIdx < 95; ulIdx++)
    {
        OSRAMWriteByte(0x00);
    }
    OSRAMWriteFinal(0x00);
}

//*****************************************************************************
//
//! Displays a string on the OLED display.
//!
//! \param pcStr is a pointer to the string to display.
//! \param ulX is the horizontal position to display the string, specified in
//! columns from the left edge of the display.
//! \param ulY is the vertical position to display the string, specified in
//! eight scan line blocks from the top of the display (i.e. only 0 and 1 are
//! valid).
//!
//! This function will draw a string on the display.  Only the ASCII characters
//! between 32 (space) and 126 (tilde) are supported; other characters will
//! result in random data being draw on the display (based on whatever appears
//! before/after the font in memory).  The font is mono-spaced, so characters
//! such as "i" and "l" have more white space around them than characters such
//! as "m" or "w".
//!
//! If the drawing of the string reaches the right edge of the display, no more
//! characters will be drawn.  Therefore, special care is not required to avoid
//! supplying a string that is "too long" to display.
//!
//! This function is contained in <tt>osram96x16.c</tt>, with
//! <tt>osram96x16.h</tt> containing the API definition for use by
//! applications.
//!
//! \return None.
//
//*****************************************************************************
void
OSRAMStringDraw(const char *pcStr, unsigned long ulX, unsigned long ulY)
{
    //
    // Check the arguments.
    //
    ASSERT(ulX < 96);
    ASSERT(ulY < 2);

    //
    // Move the display cursor to the requested position on the display.
    //
    OSRAMWriteFirst(0x80);
    OSRAMWriteByte((ulY == 0) ? 0xb0 : 0xb1);
    OSRAMWriteByte(0x80);
    OSRAMWriteByte((ulX + 36) & 0x0f);
    OSRAMWriteByte(0x80);
    OSRAMWriteByte(0x10 | (((ulX + 36) >> 4) & 0x0f));
    OSRAMWriteByte(0x40);

    //
    // Loop while there are more characters in the string.
    //
    while(*pcStr != 0)
    {
        //
        // See if there is enough space on the display for this entire
        // character.
        //
        if(ulX <= 90)
        {
            //
            // Write the contents of this character to the display.
            //
            OSRAMWriteArray(g_pucFont[*pcStr - ' '], 5);

            //
            // See if this is the last character to display (either because the
            // right edge has been reached or because there are no more
            // characters).
            //
            if((ulX == 90) || (pcStr[1] == 0))
            {
                //
                // Write the final column of the display.
                //
                OSRAMWriteFinal(0x00);

                //
                // The string has been displayed.
                //
                return;
            }

            //
            // Write the inter-character padding column.
            //
            OSRAMWriteByte(0x00);
        }
        else
        {
            //
            // Write the portion of the character that will fit onto the
            // display.
            //
            OSRAMWriteArray(g_pucFont[*pcStr - ' '], 95 - ulX);
            OSRAMWriteFinal(g_pucFont[*pcStr - ' '][95 - ulX]);

            //
            // The string has been displayed.
            //
            return;
        }

        //
        // Advance to the next character.
        //
        pcStr++;

        //
        // Increment the X coordinate by the six columns that were just
        // written.
        //
        ulX += 6;
    }
}

//*****************************************************************************
//
//! Displays an image on the OLED display.
//!
//! \param pucImage is a pointer to the image data.
//! \param ulX is the horizontal position to display this image, specified in
//! columns from the left edge of the display.
//! \param ulY is the vertical position to display this image, specified in
//! eight scan line blocks from the top of the display (i.e. only 0 and 1 are
//! valid).
//! \param ulWidth is the width of the image, specified in columns.
//! \param ulHeight is the height of the image, specified in eight row blocks
//! (i.e. only 1 and 2 are valid).
//!
//! This function will display a bitmap graphic on the display.  The image to
//! be displayed must be a multiple of eight scan lines high (i.e. one row) and
//! will be drawn at a vertical position that is a multiple of eight scan lines
//! (i.e. scan line zero or scan line eight, corresponding to row zero or row
//! one).
//!
//! The image data is organized with the first row of image data appearing left
//! to right, followed immediately by the second row of image data.  Each byte
//! contains the data for the eight scan lines of the column, with the top scan
//! line being in the least significant bit of the byte and the bottom scan
//! line being in the most significant bit of the byte.
//!
//! For example, an image four columns wide and sixteen scan lines tall would
//! be arranged as follows (showing how the eight bytes of the image would
//! appear on the display):
//!
//! \verbatim
//!     +-------+  +-------+  +-------+  +-------+
//!     |   | 0 |  |   | 0 |  |   | 0 |  |   | 0 |
//!     | B | 1 |  | B | 1 |  | B | 1 |  | B | 1 |
//!     | y | 2 |  | y | 2 |  | y | 2 |  | y | 2 |
//!     | t | 3 |  | t | 3 |  | t | 3 |  | t | 3 |
//!     | e | 4 |  | e | 4 |  | e | 4 |  | e | 4 |
//!     |   | 5 |  |   | 5 |  |   | 5 |  |   | 5 |
//!     | 0 | 6 |  | 1 | 6 |  | 2 | 6 |  | 3 | 6 |
//!     |   | 7 |  |   | 7 |  |   | 7 |  |   | 7 |
//!     +-------+  +-------+  +-------+  +-------+
//!
//!     +-------+  +-------+  +-------+  +-------+
//!     |   | 0 |  |   | 0 |  |   | 0 |  |   | 0 |
//!     | B | 1 |  | B | 1 |  | B | 1 |  | B | 1 |
//!     | y | 2 |  | y | 2 |  | y | 2 |  | y | 2 |
//!     | t | 3 |  | t | 3 |  | t | 3 |  | t | 3 |
//!     | e | 4 |  | e | 4 |  | e | 4 |  | e | 4 |
//!     |   | 5 |  |   | 5 |  |   | 5 |  |   | 5 |
//!     | 4 | 6 |  | 5 | 6 |  | 6 | 6 |  | 7 | 6 |
//!     |   | 7 |  |   | 7 |  |   | 7 |  |   | 7 |
//!     +-------+  +-------+  +-------+  +-------+
//! \endverbatim
//!
//! This function is contained in <tt>osram96x16.c</tt>, with
//! <tt>osram96x16.h</tt> containing the API definition for use by
//! applications.
//!
//! \return None.
//
//*****************************************************************************
void
OSRAMImageDraw(const unsigned char *pucImage, unsigned long ulX,
               unsigned long ulY, unsigned long ulWidth,
               unsigned long ulHeight)
{
    //
    // Check the arguments.
    //
    ASSERT(ulX < 96);
    ASSERT(ulY < 2);
    ASSERT((ulX + ulWidth) <= 96);
    ASSERT((ulY + ulHeight) <= 2);

    //
    // The first 36 columns of the LCD buffer are not displayed, so increment
    // the X coorddinate by 36 to account for the non-displayed frame buffer
    // memory.
    //
    ulX += 36;

    //
    // Loop while there are more rows to display.
    //
    while(ulHeight--)
    {
        //
        // Write the starting address within this row.
        //
        OSRAMWriteFirst(0x80);
        OSRAMWriteByte((ulY == 0) ? 0xb0 : 0xb1);
        OSRAMWriteByte(0x80);
        OSRAMWriteByte(ulX & 0x0f);
        OSRAMWriteByte(0x80);
        OSRAMWriteByte(0x10 | ((ulX >> 4) & 0x0f));
        OSRAMWriteByte(0x40);

        //
        // Write this row of image data.
        //
        OSRAMWriteArray(pucImage, ulWidth - 1);
        OSRAMWriteFinal(pucImage[ulWidth - 1]);

        //
        // Advance to the next row of the image.
        //
        pucImage += ulWidth;
        ulY++;
    }
}

//*****************************************************************************
//
//! Initialize the OLED display.
//!
//! \param bFast is a boolean that is \e true if the I2C interface should be
//! run at 400 kbps and \e false if it should be run at 100 kbps.
//!
//! This function initializes the I2C interface to the OLED display and
//! configures the SSD0303 controller on the panel.
//!
//! This function is contained in <tt>osram96x16.c</tt>, with
//! <tt>osram96x16.h</tt> containing the API definition for use by
//! applications.
//!
//! \return None.
//
//*****************************************************************************
void
OSRAMInit(tBoolean bFast)
{
    unsigned long ulIdx;

    //
    // Enable the I2C and GPIO port B blocks as they are needed by this driver.
    //
    SysCtlPeripheralEnable(SYSCTL_PERIPH_I2C);
    SysCtlPeripheralEnable(SYSCTL_PERIPH_GPIOB);

    //
    // Configure the I2C SCL and SDA pins for I2C operation.
    //
    GPIOPinTypeI2C(GPIO_PORTB_BASE, GPIO_PIN_2 | GPIO_PIN_3);

    //
    // Initialize the I2C master.
    //
    I2CMasterInit(I2C_MASTER_BASE, bFast);

    //
    // Compute the inter-byte delay for the SSD0303 controller.  This delay is
    // dependent upon the I2C bus clock rate; the slower the clock the longer
    // the delay required.
    //
    // The derivation of this formula is based on a measured delay of
    // OSRAMDelay(1700) for a 100 kHz I2C bus with the CPU running at 50 MHz
    // (referred to as C).  To scale this to the delay for a different CPU
    // speed (since this is just a CPU-based delay loop) is:
    //
    //           f(CPU)
    //     C * ----------
    //         50,000,000
    //
    // To then scale this to the actual I2C rate (since it won't always be
    // precisely 100 kHz):
    //
    //           f(CPU)     100,000
    //     C * ---------- * -------
    //         50,000,000    f(I2C)
    //
    // This equation will give the inter-byte delay required for any
    // configuration of the I2C master.  But, as arranged it is impossible to
    // directly compute in 32-bit arithmetic (without loosing a lot of
    // accuracy).  So, the equation is simplified.
    //
    // Since f(I2C) is generated by dividing down from f(CPU), replace it with
    // the equivalent (where TPR is the value programmed into the Master Timer
    // Period Register of the I2C master, with the 1 added back):
    //
    //                        100,000
    //           f(CPU)       -------
    //     C * ---------- *    f(CPU)
    //         50,000,000   ------------
    //                      2 * 10 * TPR
    //
    // Inverting the dividend in the last term:
    //
    //           f(CPU)     100,000 * 2 * 10 * TPR
    //     C * ---------- * ----------------------
    //         50,000,000          f(CPU)
    //
    // The f(CPU) now cancels out.
    //
    //         100,000 * 2 * 10 * TPR
    //     C * ----------------------
    //               50,000,000
    //
    // Since there are no clock frequencies left in the equation, this equation
    // also works for 400 kHz bus operation as well, since the 100,000 in the
    // numerator becomes 400,000 but C is 1/4, which cancel out each other.
    // Reducing the constants gives:
    //
    //         TPR              TPR             TPR
    //     C * ---   =   1700 * ---   =   340 * ---   = 68 * TPR
    //         25               25               5
    //
    // Note that the constant C is actually a bit larger than it needs to be in
    // order to provide some safety margin.
    //
    g_ulDelay = 68 * (HWREG(I2C_MASTER_BASE + I2C_MASTER_O_TPR) + 1);

    //
    // Initialize the SSD0303 controller.  Loop through the initialization
    // sequence doing a single I2C transfer for each command.
    //
    for(ulIdx = 0; ulIdx < sizeof(g_pucOSRAMInit);
        ulIdx += g_pucOSRAMInit[ulIdx] + 1)
    {
        //
        // Send this command.
        //
        OSRAMWriteFirst(g_pucOSRAMInit[ulIdx + 1]);
        OSRAMWriteArray(g_pucOSRAMInit + ulIdx + 2, g_pucOSRAMInit[ulIdx] - 2);
        OSRAMWriteFinal(g_pucOSRAMInit[ulIdx + g_pucOSRAMInit[ulIdx]]);
    }

    //
    // Clear the frame buffer.
    //
    OSRAMClear();
}

//*****************************************************************************
//
//! Turns on the OLED display.
//!
//! This function will turn on the OLED display, causing it to display the
//! contents of its internal frame buffer.
//!
//! This function is contained in <tt>osram96x16.c</tt>, with
//! <tt>osram96x16.h</tt> containing the API definition for use by
//! applications.
//!
//! \return None.
//
//*****************************************************************************
void
OSRAMDisplayOn(void)
{
    unsigned long ulIdx;

    //
    // Re-initialize the SSD0303 controller.  Loop through the initialization
    // sequence doing a single I2C transfer for each command.
    //
    for(ulIdx = 0; ulIdx < sizeof(g_pucOSRAMInit);
        ulIdx += g_pucOSRAMInit[ulIdx] + 1)
    {
        //
        // Send this command.
        //
        OSRAMWriteFirst(g_pucOSRAMInit[ulIdx + 1]);
        OSRAMWriteArray(g_pucOSRAMInit + ulIdx + 2, g_pucOSRAMInit[ulIdx] - 2);
        OSRAMWriteFinal(g_pucOSRAMInit[ulIdx + g_pucOSRAMInit[ulIdx]]);
    }
}

//*****************************************************************************
//
//! Turns off the OLED display.
//!
//! This function will turn off the OLED display.  This will stop the scanning
//! of the panel and turn off the on-chip DC-DC converter, preventing damage to
//! the panel due to burn-in (it has similar characters to a CRT in this
//! respect).
//!
//! This function is contained in <tt>osram96x16.c</tt>, with
//! <tt>osram96x16.h</tt> containing the API definition for use by
//! applications.
//!
//! \return None.
//
//*****************************************************************************
void
OSRAMDisplayOff(void)
{
    //
    // Turn off the DC-DC converter and the display.
    //
    OSRAMWriteFirst(0x80);
    OSRAMWriteByte(0xae);
    OSRAMWriteByte(0x80);
    OSRAMWriteByte(0xad);
    OSRAMWriteByte(0x80);
    OSRAMWriteFinal(0x8a);
}

//*****************************************************************************
//
// Close the Doxygen group.
//! @}
//
//*****************************************************************************
