//*****************************************************************************
//
// pdc.h - Stellaris development board Peripheral Device Controller definitions
//         and prototypes.
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
// This is part of revision 523 of the Stellaris Driver Library.
//
//*****************************************************************************

#ifndef __PDC_H__
#define __PDC_H__

#ifdef __cplusplus
extern "C"
{
#endif

//*****************************************************************************
//
// The registers within the peripheral device controller.
//
//*****************************************************************************
#define PDC_VER                 0x0         // Version register
#define PDC_CSR                 0x1         // Command/Status register
#define PDC_DSW                 0x4         // DIP Switch register
#define PDC_LED                 0x5         // LED register
#define PDC_LCD_CSR             0x6         // LCD Command/Status register
#define PDC_LCD_RAM             0x7         // LCD RAM register
#define PDC_GPXDAT              0x8         // GPIO X Data register
#define PDC_GPXDIR              0x9         // GPIO X Direction register
#define PDC_GPYDAT              0xA         // GPIO Y Data register
#define PDC_GPYDIR              0xB         // GPIO Y Direction register
#define PDC_GPZDAT              0xC         // GPIO Z Data register
#define PDC_GPZDIR              0xD         // GPIO Z Direction register

//*****************************************************************************
//
// Flags indicating a read or write to the peripheral device controller.
//
//*****************************************************************************
#define PDC_RD                  0x80        // PDC read command
#define PDC_WR                  0x00        // PDC write command

//*****************************************************************************
//
// LCD panel (Crystalfontz CFAH1602B) commands, RS = 0
//
//*****************************************************************************
#define LCD_CLEAR               0x01        // Clear display (0 fill DDRAM).
#define LCD_HOME                0x02        // Cursor home.
#define LCD_MODE                0x04        // Set entry mode (cursor dir)
#define LCD_ON                  0x08        // Set display, cursor, blinking
                                            // on/off
#define LCD_CUR                 0x10        // Cursor, display shift
#define LCD_IF                  0x20        // Set interface data length,
                                            // lines, font
#define LCD_CGADDR              0x40        // Set CGRAM AC address
#define LCD_DDADDR              0x80        // Set DDRAM AC address

//*****************************************************************************
//
// LCD Status bit
//
//*****************************************************************************
#define LCD_B_BUSY              0x80        // Busy flag.

//*****************************************************************************
//
// The GPIO port A pin numbers for the various SSI signals.
//
//*****************************************************************************
#define SSI_CS                  GPIO_PIN_3
#define PDC_CS                  GPIO_PIN_3
#define SSI_CLK                 GPIO_PIN_2
#define SSI_TX                  GPIO_PIN_5
#define SSI_RX                  GPIO_PIN_4

//*****************************************************************************
//
// Function Prototypes
//
//*****************************************************************************
extern void PDCInit(void);
extern unsigned char PDCRead(unsigned char ucAddr);
extern void PDCWrite(unsigned char ucAddr, unsigned char ucData);
extern unsigned char PDCDIPRead(void);
extern void PDCLEDWrite(unsigned char ucLED);
extern unsigned char PDCLEDRead(void);
extern void PDCLCDInit(void);
extern void PDCLCDBacklightOn(void);
extern void PDCLCDBacklightOff(void);
extern void PDCLCDClear(void);
extern void PDCLCDCreateChar(unsigned char ucChar, unsigned char *pucData);
extern void PDCLCDSetPos(unsigned char ucX, unsigned char ucY);
extern void PDCLCDWrite(const char *pcStr, unsigned long ulCount);
extern unsigned char PDCGPIODirRead(unsigned char ucIdx);
extern void PDCGPIODirWrite(unsigned char ucIdx, unsigned char ucValue);
extern unsigned char PDCGPIORead(unsigned char ucIdx);
extern void PDCGPIOWrite(unsigned char ucIdx, unsigned char ucValue);

#ifdef __cplusplus
}
#endif

#endif // __PDC_H__
