//*****************************************************************************
//
// formike128x128x16.h - Prototypes for the Formike Electronic KWH015C04-F01
//                       display driver.
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

#ifndef __FORMIKE128X128X16_H__
#define __FORMIKE128X128X16_H__

//*****************************************************************************
//
// Prototypes for the globals exported by this driver.
//
//*****************************************************************************
extern void Formike128x128x16Init(void);
extern void Formike128x128x16BacklightOn(void);
extern void Formike128x128x16BacklightOff(void);
extern const tDisplay g_sFormike128x128x16;

/* FreeRTOS.org demo wrappers.  These are required so the prototypes for the
functions are the same as for the display drivers used by other evaluation
kits. */
void vFormike128x128x16Clear( void );
void vFormike128x128x16StringDraw( const char *pcString, unsigned long lX, unsigned long lY, unsigned char ucColor );
void vFormike128x128x16Init( unsigned long ul );
void vFormike128x128x16ImageDraw( const unsigned char *pucImage, unsigned long ulX, unsigned long ulY, unsigned long ulWidth, unsigned long ulHeight );

#endif // __FORMIKE128X128X16_H__
