//*****************************************************************************
//
// diag.h - Prototypes for the diagnostic functions.
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

#ifndef __DIAG_H__
#define __DIAG_H__

#ifdef __cplusplus
extern "C"
{
#endif

//*****************************************************************************
//
// Values that can be passed as the iMode parater to DiagOpen, DiagRead, and
// DiagWrite.
//
//*****************************************************************************
#define OPEN_R                  0           // read access
#define OPEN_W                  4           // write access
#define OPEN_A                  8           // append to file
#define OPEN_B                  1           // binary access
#define OPEN_PLUS               2           // read and write access

//*****************************************************************************
//
// Prototypes for the APIs.
//
//*****************************************************************************
extern int DiagOpenStdio(void);
extern int DiagOpen(const char *pcName, int iMode);
extern int DiagClose(int iHandle);
extern int DiagWrite(int iHandle, const char *pcBuf, unsigned long ulLen,
                     int iMode);
extern int DiagRead(int iHandle, char *pcBuf, unsigned long ulLen, int iMode);
extern long DiagFlen(int iHandle);
extern void DiagExit(int iRet);
extern char *DiagCommandString(char *pcBuf, unsigned long ulLen);

#ifdef __cplusplus
}
#endif

#endif // __DIAG_H__
