//*****************************************************************************
//
// cspy.c - Routines for simply ignoring the debugger communciation APIs in
//          C-Spy for now.
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

#include "diag.h"

//*****************************************************************************
//
// Open a handle for stdio functions (both stdin and stdout).
//
//*****************************************************************************
int
DiagOpenStdio(void)
{
    return(-1);
}

//*****************************************************************************
//
// Open a host file system file.
//
//*****************************************************************************
int
DiagOpen(const char *pcName, int iMode)
{
    return(-1);
}

//*****************************************************************************
//
// Close a host file system file.
//
//*****************************************************************************
int
DiagClose(int iHandle)
{
    return(-1);
}

//*****************************************************************************
//
// Write data to a host file system file.
//
//*****************************************************************************
int
DiagWrite(int iHandle, const char *pcBuf, unsigned long ulLen, int iMode)
{
    return(-1);
}

//*****************************************************************************
//
// Read data from a host file system file.
//
//*****************************************************************************
int
DiagRead(int iHandle, char *pcBuf, unsigned long ulLen, int iMode)
{
    return(-1);
}

//*****************************************************************************
//
// Get the length of a host file system file.
//
//*****************************************************************************
long
DiagFlen(int iHandle)
{
    return(-1);
}

//*****************************************************************************
//
// Terminate the application.
//
//*****************************************************************************
void
DiagExit(int iRet)
{
    while(1)
    {
    }
}

//*****************************************************************************
//
// Get the command line arguments from the debugger.
//
//*****************************************************************************
char *
DiagCommandString(char *pcBuf, unsigned long ulLen)
{
    return(0);
}
