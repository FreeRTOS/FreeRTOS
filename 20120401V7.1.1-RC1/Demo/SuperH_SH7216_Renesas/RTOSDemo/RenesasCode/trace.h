/******************************************************************************
* File Name    : trace.h
* Version      : 1.0
* Device(s)    : Renesas
* Tool-Chain   : Renesas SH2A V9+
* OS           : None
* H/W Platform : SH2A
* Description  : Debug formatted output routine
*                TRACE print function enabled with define _TRACE_ON_
*******************************************************************************
* History      : DD.MM.YYYY Ver. Description
*              : 01.08.2009 1.00 MAB First Release
******************************************************************************/

/******************************************************************************
* DISCLAIMER
* This software is supplied by Renesas Technology Corp. and is only
* intended for use with Renesas products. No other uses are authorized.
* This software is owned by Renesas Technology Corp. and is protected under
* all applicable laws, including copyright laws.
* THIS SOFTWARE IS PROVIDED "AS IS" AND RENESAS MAKES NO WARRANTIES
* REGARDING THIS SOFTWARE, WHETHER EXPRESS, IMPLIED OR STATUTORY,
* INCLUDING BUT NOT LIMITED TO WARRANTIES OF MERCHANTABILITY, FITNESS FOR A
* PARTICULAR PURPOSE AND NON-INFRINGEMENT. ALL SUCH WARRANTIES ARE EXPRESSLY
* DISCLAIMED.
* TO THE MAXIMUM EXTENT PERMITTED NOT PROHIBITED BY LAW, NEITHER RENESAS
* TECHNOLOGY CORP. NOR ANY OF ITS AFFILIATED COMPANIES SHALL BE LIABLE
* FOR ANY DIRECT, INDIRECT, SPECIAL, INCIDENTAL OR CONSEQUENTIAL DAMAGES
* FOR ANY REASON RELATED TO THE THIS SOFTWARE, EVEN IF RENESAS OR ITS
* AFFILIATES HAVE BEEN ADVISED OF THE POSSIBILITY OF SUCH DAMAGES.
* Renesas reserves the right, without notice, to make changes to this
* software and to discontinue the availability of this software.
* By using this software, you agree to the additional terms and
* conditions found by accessing the following link:
* http://www.renesas.com/disclaimer
******************************************************************************/
/* Copyright (C) 2008. Renesas Technology Corp.,       All Rights Reserved.  */
/* Copyright (C) 2009. Renesas Technology Europe Ltd., All Rights Reserved.  */
/*****************************************************************************/

#ifndef TRACE_H_INCLUDED
#define TRACE_H_INCLUDED

/******************************************************************************
User Includes
******************************************************************************/

#include "types.h"

/******************************************************************************
Function Macros
******************************************************************************/

/* Some function macros for TRACE output
   NOTE: debugging TRACE statements require double braces
   so the debug strings can be removed from the output load module:
   TRACE(("My Variable = %u\r\n", uiMyVariable));
   See ANSI C formatted output for more detail on the format specifiers */

#ifdef _TRACE_ON_                   /* Trace ON */
#define TRACE(_x_)                  Trace _x_
#else                               /* _NO_TRACE_ON_ */
#define TRACE(_x_)                  /* TRACE REMOVED */
#endif                              /* _TRACE_ON_ */

/******************************************************************************
Public Functions
******************************************************************************/

#ifdef __cplusplus
extern "C" {
#endif

/******************************************************************************
Function Name: Trace
Description:   Function to perform a formatted print output for debugging
Parameters:    IN  pszFormat - Pointer to a null terminated format string
               I/O ... - The parameters
Return value:  The number of chars output
******************************************************************************/
#ifdef _TRACE_ON_                   /* Trace ON */
extern  int Trace(const char *pszFormat, ...);
#endif

/******************************************************************************
Function Name: dbgPrintBuffer
Description:   Function to print a data buffer in hex format
Parameters:    IN  pbyBuffer - Pointer to the buffer
               IN  stLength - The length of the buffer
Return value:  none
******************************************************************************/
#ifdef _TRACE_ON_                   /* Trace ON */
extern  void dbgPrintBuffer(PBYTE pbyBuffer, size_t stLength);
#endif

#ifdef __cplusplus
}
#endif

#endif /* TRACE_H_INCLUDED */

/******************************************************************************
End  Of File
******************************************************************************/