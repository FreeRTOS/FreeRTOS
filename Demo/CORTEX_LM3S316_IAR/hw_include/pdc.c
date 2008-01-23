//*****************************************************************************
//
// pdc.c - Driver for the Peripheral Device Controller (PDC) on the Stellaris
//         development board.
//
// Copyright (c) 2005,2006 Luminary Micro, Inc.  All rights reserved.
//
// Software License Agreement
//
// Luminary Micro, Inc. (LMI) is supplying this software for use solely and
// exclusively on LMI's Stellaris Family of microcontroller products.
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
// This is part of revision 635 of the Stellaris Driver Library.
//
//*****************************************************************************

//*****************************************************************************
//
//! \addtogroup utilities_api
//! @{
//
//*****************************************************************************

#include "hw_memmap.h"
#include "hw_types.h"
#include "debug.h"
#include "gpio.h"
#include "ssi.h"
#include "sysctl.h"
#include "pdc.h"

//*****************************************************************************
//
//! Initializes the connection to the PDC.
//!
//! This function will enable clocking to the SSI and GPIO A modules, configure
//! the GPIO pins to be used for an SSI interface, and it will configure the
//! SSI as a 1 Mbps master device, operating in MOTO mode.  It will also enable
//! the SSI module, and will enable the chip select for the PDC on the
//! Stellaris development board.
//!
//! This function is contained in <tt>utils/pdc.c</tt>, with
//! <tt>utils/pdc.h</tt> containing the API definition for use by applications.
//!
//! \return None.
//
//*****************************************************************************
void
PDCInit(void)
{
    //
    // Enable the peripherals used to drive the PDC.
    //
    SysCtlPeripheralEnable(SYSCTL_PERIPH_SSI);
    SysCtlPeripheralEnable(SYSCTL_PERIPH_GPIOA);

    //
    // Configure the appropriate pins to be SSI instead of GPIO.
    //
    GPIODirModeSet(GPIO_PORTA_BASE, SSI_CLK | SSI_TX | SSI_RX,
                   GPIO_DIR_MODE_HW);
    GPIODirModeSet(GPIO_PORTA_BASE, SSI_CS, GPIO_DIR_MODE_OUT);
    GPIOPadConfigSet(GPIO_PORTA_BASE, SSI_CLK, GPIO_STRENGTH_4MA,
                     GPIO_PIN_TYPE_STD_WPU);

    //
    // Configure the SSI port.
    //
    SSIConfigSetExpClk(SSI_BASE, SysCtlClockGet(), SSI_FRF_MOTO_MODE_0,
                       SSI_MODE_MASTER, 1000000, 8);
    SSIEnable(SSI_BASE);

    //
    // Reset the PDC SSI state machine.  The chip select needs to be held low
    // for 100ns; the procedure call overhead more than accounts for this time.
    //
    GPIOPinWrite(GPIO_PORTA_BASE, PDC_CS, 0);
    GPIOPinWrite(GPIO_PORTA_BASE, PDC_CS, PDC_CS);
}

//*****************************************************************************
//
//! Read a PDC register.
//!
//! \param ucAddr specifies the PDC register to read.
//!
//! This function will perform the SSI transfers required to read a register in
//! the PDC on the Stellaris development board.
//!
//! This function is contained in <tt>utils/pdc.c</tt>, with
//! <tt>utils/pdc.h</tt> containing the API definition for use by applications.
//!
//! \return Returns the value read from the PDC.
//
//*****************************************************************************
unsigned char
PDCRead(unsigned char ucAddr)
{
    unsigned long ulTemp;

    //
    // Send address and read command.
    //
    SSIDataPut(SSI_BASE, (ucAddr & 0x0F) | PDC_RD);

    //
    // Dummy write to force read.
    //
    SSIDataPut(SSI_BASE, 0x00);

    //
    // Flush data read during address write.
    //
    SSIDataGet(SSI_BASE, &ulTemp);

    //
    // If the LCD control register or RAM is being read, then an additional
    // byte needs to be transferred.
    //
    if((ucAddr == PDC_LCD_CSR) || (ucAddr == PDC_LCD_RAM))
    {
        //
        // Dummy write to force read.
        //
        SSIDataPut(SSI_BASE, 0x00);

        //
        // Flush read data.
        //
        SSIDataGet(SSI_BASE, &ulTemp);
    }

    //
    // Read valid data.
    //
    SSIDataGet(SSI_BASE, &ulTemp);

    //
    // Return the data read.
    //
    return(ulTemp & 0xFF);
}

//*****************************************************************************
//
//! Write a PDC register.
//!
//! \param ucAddr specifies the PDC register to write.
//! \param ucData specifies the data to write.
//!
//! This function will perform the SSI transfers required to write a register
//! in the PDC on the Stellaris development board.
//!
//! This function is contained in <tt>utils/pdc.c</tt>, with
//! <tt>utils/pdc.h</tt> containing the API definition for use by applications.
//!
//! \return None.
//
//*****************************************************************************
void
PDCWrite(unsigned char ucAddr, unsigned char ucData)
{
    unsigned long ulTemp;

    //
    // Send address and write command.
    //
    SSIDataPut(SSI_BASE, (ucAddr & 0x0F) | PDC_WR);

    //
    // Write the data.
    //
    SSIDataPut(SSI_BASE, ucData);

    //
    // Flush data read during address write.
    //
    SSIDataGet(SSI_BASE, &ulTemp);

    //
    // Flush data read during data write.
    //
    SSIDataGet(SSI_BASE, &ulTemp);
}

//*****************************************************************************
//
//! Read the current value of the PDC DIP switches.
//!
//! This function will read the current value of the DIP switches attached to
//! the PDC on the Stellaris development board.
//!
//! This function is contained in <tt>utils/pdc.c</tt>, with
//! <tt>utils/pdc.h</tt> containing the API definition for use by applications.
//!
//! \return The current state of the DIP switches.
//
//*****************************************************************************
unsigned char
PDCDIPRead(void)
{
    return(PDCRead(PDC_DSW));
}

//*****************************************************************************
//
//! Write to the PDC LEDs.
//!
//! \param ucLED value to write to the LEDs.
//!
//! This function set the state of the LEDs connected to the PDC on the
//! Stellaris development board.
//!
//! This function is contained in <tt>utils/pdc.c</tt>, with
//! <tt>utils/pdc.h</tt> containing the API definition for use by applications.
//!
//! \return None.
//
//*****************************************************************************
void
PDCLEDWrite(unsigned char ucLED)
{
    PDCWrite(PDC_LED, ucLED);
}

//*****************************************************************************
//
//! Read the current status of the PDC LEDs.
//!
//! This function will read the state of the LEDs connected to the PDC on the
//! Stellaris development board.
//!
//! This function is contained in <tt>utils/pdc.c</tt>, with
//! <tt>utils/pdc.h</tt> containing the API definition for use by applications.
//!
//! \return The value currently displayed by the LEDs.
//
//*****************************************************************************
unsigned char
PDCLEDRead(void)
{
    return(PDCRead(PDC_LED));
}

//*****************************************************************************
//
//! Initializes the LCD display.
//!
//! This function will set up the LCD display for writing. It will set the
//! data bus to 8 bits, set the number of lines to 2, and the font size to
//! 5x10. It will also turn the display off, clear the display, turn the
//! display back on, and enable the backlight.
//!
//! This function is contained in <tt>utils/pdc.c</tt>, with
//! <tt>utils/pdc.h</tt> containing the API definition for use by applications.
//!
//! \note The PDC must be initialized via the PDCInit() function before this
//! function can be called.  Also, it may be necessary to adjust the contrast
//! potentiometer in order to discern any output on the LCD display.
//!
//! \return None.
//
//*****************************************************************************
void
PDCLCDInit(void)
{
    unsigned char pucCfg[] =
    {
        0x3C,   // Number of lines = 2 / font = 5x10
        0x08,   // Display off
        0x01,   // Display clear
        0x06,   // Entry mode [cursor dir][shift]
        0x0C,   // Display on [display on][curson on][blinking on]
    };
    unsigned long ulIdx;

    //
    // Set the data bus width to eight bits.
    //
    PDCWrite(PDC_LCD_CSR, 0x30);

    //
    // Wait for 4.1ms by reading the PDC version register enough times to
    // guarantee that amount of time has passed.
    //
    for(ulIdx = 0; ulIdx < 257; ulIdx++)
    {
        PDCRead(PDC_VER);
    }

    //
    // Set the data bus width to eight bits.
    //
    PDCWrite(PDC_LCD_CSR, 0x30);

    //
    // Wait for 100us by reading the PDC version register enough times to
    // guarantee that amount of time has passed.  This works out to 112us plus
    // overhead.
    //
    for(ulIdx = 0; ulIdx < 7; ulIdx++)
    {
        PDCRead(PDC_VER);
    }

    //
    // Set the data bus width to eight bits.
    //
    PDCWrite(PDC_LCD_CSR, 0x30);

    //
    // Configure the LCD.
    //
    for(ulIdx = 0; ulIdx < (sizeof(pucCfg) / sizeof(pucCfg[0])); ulIdx++)
    {
        //
        // Wait until the LCD has finished executing any previous command.
        //
        while((PDCRead(PDC_LCD_CSR) & LCD_B_BUSY))
        {
        }

        //
        // Write the next configuration byte.
        //
        PDCWrite(PDC_LCD_CSR, pucCfg[ulIdx]);
    }
}

//*****************************************************************************
//
//! Turns on the backlight.
//!
//! This function turns on the backlight on the LCD.
//!
//! This function is contained in <tt>utils/pdc.c</tt>, with
//! <tt>utils/pdc.h</tt> containing the API definition for use by applications.
//!
//! \return None.
//
//*****************************************************************************
void
PDCLCDBacklightOn(void)
{
    PDCWrite(PDC_CSR, 0x01);
}

//*****************************************************************************
//
//! Turn off the backlight.
//!
//! This function turns off the backlight on the LCD.
//!
//! This function is contained in <tt>utils/pdc.c</tt>, with
//! <tt>utils/pdc.h</tt> containing the API definition for use by applications.
//!
//! \return None.
//
//*****************************************************************************
void
PDCLCDBacklightOff(void)
{
    PDCWrite(PDC_CSR, 0x00);
}

//*****************************************************************************
//
//! Clear the screen.
//!
//! This function clears the contents of the LCD screen.  The cursor will be
//! returned to the upper left corner.
//!
//! This function is contained in <tt>utils/pdc.c</tt>, with
//! <tt>utils/pdc.h</tt> containing the API definition for use by applications.
//!
//! \return None.
//
//*****************************************************************************
void
PDCLCDClear(void)
{
    //
    // Wait until the LCD has finished executing any previous command.
    //
    while((PDCRead(PDC_LCD_CSR) & LCD_B_BUSY))
    {
    }

    //
    // Write the clear display command.
    //
    PDCWrite(PDC_LCD_CSR, LCD_CLEAR);
}

//*****************************************************************************
//
//! Write a character pattern to the LCD.
//!
//! \param ucChar is the character index to create.  Valid values are zero
//! through seven.
//! \param pucData is the data for the character pattern.  It contains eight
//! bytes, with the first byte being the top row of the pattern.  In each byte,
//! the LSB is the right pixel of the pattern.
//!
//! This function will write a character pattern into the LCD for use as a
//! character to be displayed.  After writing the pattern, it can be used on
//! the LCD by writing the corresponding character index to the display.
//!
//! This function is contained in <tt>utils/pdc.c</tt>, with
//! <tt>utils/pdc.h</tt> containing the API definition for use by applications.
//!
//! \return None.
//
//*****************************************************************************
void
PDCLCDCreateChar(unsigned char ucChar, unsigned char *pucData)
{
    //
    // Check the arguments.
    //
    ASSERT(ucChar < 8);

    //
    // Wait until the LCD has finished executing any previous command.
    //
    while((PDCRead(PDC_LCD_CSR) & LCD_B_BUSY))
    {
    }

    //
    // Write the character pattern memory address.
    //
    PDCWrite(PDC_LCD_CSR, LCD_CGADDR + (ucChar * 8));

    //
    // Write the pattern to chacter pattern memory.
    //
    for(ucChar = 0; ucChar < 8; ucChar++)
    {
        //
        // Wait until the LCD has finished executing any previous command.
        //
        while((PDCRead(PDC_LCD_CSR) & LCD_B_BUSY))
        {
        }

        //
        // Write this row of the pattern.
        //
        PDCWrite(PDC_LCD_RAM, *pucData++);
    }
}

//*****************************************************************************
//
//! Set the position of the cursor.
//!
//! \param ucX is the horizontal position.  Valid values are zero through
//! fifteen.
//! \param ucY is the vertical position.. Valid values are zero and one.
//!
//! This function will move the cursor to the specified position.  All
//! characters written to the LCD are placed at the current cursor position,
//! which is automatically advanced.
//!
//! This function is contained in <tt>utils/pdc.c</tt>, with
//! <tt>utils/pdc.h</tt> containing the API definition for use by applications.
//!
//! \return None.
//
//*****************************************************************************
void
PDCLCDSetPos(unsigned char ucX, unsigned char ucY)
{
    //
    // Check the arguments.
    //
    ASSERT(ucX < 16);
    ASSERT(ucY < 2);

    //
    // Wait until the LCD has finished executing any previous command.
    //
    while((PDCRead(PDC_LCD_CSR) & LCD_B_BUSY))
    {
    }

    //
    // Set the cursor position.
    //
    PDCWrite(PDC_LCD_CSR, LCD_DDADDR | (0x40 * ucY) + ucX);
}

//*****************************************************************************
//
//! Writes a string to the LCD display.
//!
//! \param pcStr pointer to the string to be displayed.
//! \param ulCount is the number of characters to be displayed.
//!
//! This function will display a string on the LCD at the current cursor
//! position.  It is the caller's responsibility to position the cursor to the
//! place where the string should be displayed (either explicitly via
//! PDCLCDSetPos() or implicitly from where the cursor was left after a
//! previous call to PDCLCDWrite()), and to properly account for the LCD
//! boundary (line wrapping is not automatically performed).  Null characters
//! are not treated special and are written to the LCD, which interprets it as
//! a special programmable character glyph (see PDCLCDCreateChar()).
//!
//! This function is contained in <tt>utils/pdc.c</tt>, with
//! <tt>utils/pdc.h</tt> containing the API definition for use by applications.
//!
//! \return None.
//
//*****************************************************************************
void
PDCLCDWrite(const char *pcStr, unsigned long ulCount)
{
    //
    // Write the string to the LCD.
    //
    while(ulCount--)
    {
        //
        // Wait until the LCD has finished executing any previous command.
        //
        while((PDCRead(PDC_LCD_CSR) & LCD_B_BUSY))
        {
        }

        //
        // Write this character to the LCD.
        //
        PDCWrite(PDC_LCD_RAM, *pcStr++);
    }
}

//*****************************************************************************
//
//! Reads a GPIO direction register.
//!
//! \param ucIdx is the index of the GPIO direction register to read; valid
//! values are 0, 1, and 2.
//!
//! This function reads one of the GPIO direction registers in the PDC.  The
//! direction bit is set for pins that are outputs and clear for pins that are
//! inputs.
//!
//! This function is contained in <tt>utils/pdc.c</tt>, with
//! <tt>utils/pdc.h</tt> containing the API definition for use by applications.
//!
//! \return The contents of the direction register.
//
//*****************************************************************************
unsigned char
PDCGPIODirRead(unsigned char ucIdx)
{
    //
    // Check the argument.
    //
    ASSERT((ucIdx == 0) || (ucIdx == 1) || (ucIdx == 2));

    //
    // Read the requested direction register.
    //
    if(ucIdx == 0)
    {
        return(PDCRead(PDC_GPXDIR));
    }
    else if(ucIdx == 1)
    {
        return(PDCRead(PDC_GPYDIR));
    }
    else
    {
        return(PDCRead(PDC_GPZDIR));
    }
}

//*****************************************************************************
//
//! Write a GPIO direction register.
//!
//! \param ucIdx is the index of the GPIO direction register to write; valid
//! values are 0, 1, and 2.
//! \param ucValue is the value to write to the GPIO direction register.
//!
//! This function writes ones of the GPIO direction registers in the PDC.  The
//! direction bit should be set for pins that are to be outputs and clear for
//! pins that are to be inputs.
//!
//! This function is contained in <tt>utils/pdc.c</tt>, with
//! <tt>utils/pdc.h</tt> containing the API definition for use by applications.
//!
//! \return None.
//
//*****************************************************************************
void
PDCGPIODirWrite(unsigned char ucIdx, unsigned char ucValue)
{
    //
    // Check the arguments.
    //
    ASSERT((ucIdx == 0) || (ucIdx == 1) || (ucIdx == 2));

    //
    // Write the requested direction register.
    //
    if(ucIdx == 0)
    {
        PDCWrite(PDC_GPXDIR, ucValue);
    }
    else if(ucIdx == 1)
    {
        PDCWrite(PDC_GPYDIR, ucValue);
    }
    else
    {
        PDCWrite(PDC_GPZDIR, ucValue);
    }
}

//*****************************************************************************
//
//! Reads a GPIO data register.
//!
//! \param ucIdx is the index of the GPIO direction register to read; valid
//! values are 0, 1, and 2.
//!
//! This function reads one of the GPIO data registers in the PDC.  The value
//! returned for a pin is the value being driven out for outputs or the value
//! being read for inputs.
//!
//! This function is contained in <tt>utils/pdc.c</tt>, with
//! <tt>utils/pdc.h</tt> containing the API definition for use by applications.
//!
//! \return The contents of the data register.
//
//*****************************************************************************
unsigned char
PDCGPIORead(unsigned char ucIdx)
{
    //
    // Check the argument.
    //
    ASSERT((ucIdx == 0) || (ucIdx == 1) || (ucIdx == 2));

    //
    // Read the requested data register.
    //
    if(ucIdx == 0)
    {
        return(PDCRead(PDC_GPXDAT));
    }
    else if(ucIdx == 1)
    {
        return(PDCRead(PDC_GPYDAT));
    }
    else
    {
        return(PDCRead(PDC_GPZDAT));
    }
}

//*****************************************************************************
//
//! Write a GPIO data register.
//!
//! \param ucIdx is the index of the GPIO data register to write; valid values
//! are 0, 1, and 2.
//! \param ucValue is the value to write to the GPIO data register.
//!
//! This function writes one of the GPIO direction registers in the PDC.  The
//! written to a pin is driven out for output pins and ignored for input pins.
//!
//! This function is contained in <tt>utils/pdc.c</tt>, with
//! <tt>utils/pdc.h</tt> containing the API definition for use by applications.
//!
//! \return None.
//
//*****************************************************************************
void
PDCGPIOWrite(unsigned char ucIdx, unsigned char ucValue)
{
    //
    // Check the arguments.
    //
    ASSERT((ucIdx == 0) || (ucIdx == 1) || (ucIdx == 2));

    //
    // Write the requested data register.
    //
    if(ucIdx == 0)
    {
        PDCWrite(PDC_GPXDAT, ucValue);
    }
    else if(ucIdx == 1)
    {
        PDCWrite(PDC_GPYDAT, ucValue);
    }
    else
    {
        PDCWrite(PDC_GPZDAT, ucValue);
    }
}

//*****************************************************************************
//
// Close the Doxygen group.
//! @}
//
//*****************************************************************************
