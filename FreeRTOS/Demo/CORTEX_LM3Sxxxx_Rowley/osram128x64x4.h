//*****************************************************************************
//
// osram128x64x4.h - Prototypes for the driver for the OSRAM 128x64x4 graphical
//                   OLED display.
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
// This is part of revision 1408 of the Stellaris Peripheral Driver Library.
//
//*****************************************************************************

#ifndef __OSRAM128X64X4_H__
#define __OSRAM128X64X4_H__

//*****************************************************************************
//
// Prototypes for the driver APIs.
//
//*****************************************************************************
extern void OSRAM128x64x4Clear(void);
extern void OSRAM128x64x4StringDraw(const char *pcStr,
                                    unsigned long ulX,
                                    unsigned long ulY,
                                    unsigned char ucLevel);
extern void OSRAM128x64x4ImageDraw(const unsigned char *pucImage,
                                   unsigned long ulX,
                                   unsigned long ulY,
                                   unsigned long ulWidth,
                                   unsigned long ulHeight);
extern void OSRAM128x64x4Init(unsigned long ulFrequency);
extern void OSRAM128x64x4Enable(unsigned long ulFrequency);
extern void OSRAM128x64x4Disable(void);
extern void OSRAM128x64x4DisplayOn(void);
extern void OSRAM128x64x4DisplayOff(void);

//*****************************************************************************
//
// The following macro(s) map old names for the OSRAM functions to the new
// names.  In new code, the new names should be used in favor of the old names.
//
//*****************************************************************************
#ifndef DEPRECATED
#define OSRAM128x64x1InitSSI    OSRAM128x64x4Enable
#endif

#endif // __OSRAM128X64X4_H__
