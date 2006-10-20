//*****************************************************************************
//
// osram96x16.h - Prototypes for the driver for the OSRAM 96x16 graphical OLED
//                display.
//
// Copyright (c) 2006 Luminary Micro, Inc.  All rights reserved.
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
// This is part of revision 852 of the Stellaris Driver Library.
//
//*****************************************************************************

#ifndef __OSRAM96X16_H__
#define __OSRAM96X16_H__

//*****************************************************************************
//
// Prototypes for the driver APIs.
//
//*****************************************************************************
extern void OSRAMClear(void);
extern void OSRAMStringDraw(const char *pcStr, unsigned long ulX,
                            unsigned long ulY);
extern void OSRAMImageDraw(const unsigned char *pucImage, unsigned long ulX,
                           unsigned long ulY, unsigned long ulWidth,
                           unsigned long ulHeight);
extern void OSRAMInit(tBoolean bFast);
extern void OSRAMDisplayOn(void);
extern void OSRAMDisplayOff(void);

#endif // __OSRAM96X16_H__
