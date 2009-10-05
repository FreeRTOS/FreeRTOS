//*****************************************************************************
//   +--+       
//   | ++----+   
//   +-++    |  
//     |     |  
//   +-+--+  |   
//   | +--+--+  
//   +----+    Copyright (c) 2009 Code Red Technologies Ltd. 
//
// lcd_commands.h contains defines mapping onto the commands accepted by the
// Sitronix ST7637 LCD Controller/driver used on the RDB1768 development board.//
//
// Software License Agreement
// 
// The software is owned by Code Red Technologies and/or its suppliers, and is 
// protected under applicable copyright laws.  All rights are reserved.  Any 
// use in violation of the foregoing restrictions may subject the user to criminal 
// sanctions under applicable laws, as well as to civil liability for the breach 
// of the terms and conditions of this license.
// 
// THIS SOFTWARE IS PROVIDED "AS IS".  NO WARRANTIES, WHETHER EXPRESS, IMPLIED
// OR STATUTORY, INCLUDING, BUT NOT LIMITED TO, IMPLIED WARRANTIES OF
// MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE APPLY TO THIS SOFTWARE.
// USE OF THIS SOFTWARE FOR COMMERCIAL DEVELOPMENT AND/OR EDUCATION IS SUBJECT
// TO A CURRENT END USER LICENSE AGREEMENT (COMMERCIAL OR EDUCATIONAL) WITH
// CODE RED TECHNOLOGIES LTD. 

#ifndef LCD_COMMANDS_H_
#define LCD_COMMANDS_H_

#define DD_NOP 			0x00
#define DD_SWRESET 		0x01	//SW reset the display
#define DD_SLPIN		0x10	//Sleep in and booster off
#define DD_SLPOUT		0x11	//Sleep out and booster on
#define DD_NORON		0x13	//Partial mode off (Normal mode on)
#define DD_DISPOFF		0x28	//Display Off
#define DD_DISPON		0x29	//Display On
#define DD_CASET		0x2a	//Column address set
#define DD_RASET		0x2b	//Row address set
#define DD_RAMWR		0x2c	//Memory write
#define DD_MADCTR		0x36	//Memory Data Access Control
#define DD_COLORMOD		0x3a	//Set the color mode for the display 
#define DD_ColScanDir	0xb7	//Set the column scanning direction
#define DD_VopSet		0xc0	//LCD supply voltage set
#define DD_BiasSel		0xc3	//Bias selection
#define DD_BstMbpXSel	0xc4	//Booster setting
#define DD_AUTOLOADSET	0xd7	//Control auto load of ROM data
#define DD_EPCTIN 		0xe0	//OTP control RD/WR
#define DD_EPREAD		0xe3	//OTP read
#define DD_EPCTOUT		0xe1	//OTP control cancel


#endif /*LCD_COMMANDS_H_*/
