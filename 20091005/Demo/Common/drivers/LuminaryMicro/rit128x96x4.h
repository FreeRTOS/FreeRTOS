//*****************************************************************************
//
// rit128x96x4.h - Prototypes for the driver for the RITEK 128x96x4 graphical
//                   OLED display.
//
// Copyright (c) 2007 Luminary Micro, Inc.  All rights reserved.
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
// This is part of revision 1582 of the Stellaris Peripheral Driver Library.
//
//*****************************************************************************

#ifndef __RIT128X96X4_H__
#define __RIT128X96X4_H__

//*****************************************************************************
//
// Prototypes for the driver APIs.
//
//*****************************************************************************
extern void RIT128x96x4Clear(void);
extern void RIT128x96x4StringDraw(const char *pcStr,
                                    unsigned long ulX,
                                    unsigned long ulY,
                                    unsigned char ucLevel);
extern void RIT128x96x4ImageDraw(const unsigned char *pucImage,
                                   unsigned long ulX,
                                   unsigned long ulY,
                                   unsigned long ulWidth,
                                   unsigned long ulHeight);
extern void RIT128x96x4Init(unsigned long ulFrequency);
extern void RIT128x96x4Enable(unsigned long ulFrequency);
extern void RIT128x96x4Disable(void);
extern void RIT128x96x4DisplayOn(void);
extern void RIT128x96x4DisplayOff(void);

#endif // __RIT128X96X4_H__
