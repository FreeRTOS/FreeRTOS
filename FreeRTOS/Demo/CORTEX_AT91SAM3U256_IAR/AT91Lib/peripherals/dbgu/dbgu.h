/* ----------------------------------------------------------------------------
 *         ATMEL Microcontroller Software Support 
 * ----------------------------------------------------------------------------
 * Copyright (c) 2008, Atmel Corporation
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * - Redistributions of source code must retain the above copyright notice,
 * this list of conditions and the disclaimer below.
 *
 * Atmel's name may not be used to endorse or promote products derived from
 * this software without specific prior written permission.
 *
 * DISCLAIMER: THIS SOFTWARE IS PROVIDED BY ATMEL "AS IS" AND ANY EXPRESS OR
 * IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NON-INFRINGEMENT ARE
 * DISCLAIMED. IN NO EVENT SHALL ATMEL BE LIABLE FOR ANY DIRECT, INDIRECT,
 * INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA,
 * OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE,
 * EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 * ----------------------------------------------------------------------------
 */

//------------------------------------------------------------------------------
/// \unit
///
/// !Purpose
/// 
/// This module provides definitions and functions for using the Debug Unit
/// (DBGU).
///
/// It also overloads the fputc(), fputs() & putchar() functions so the printf()
/// method outputs its data on the DBGU. This behavior can be suppressed by
/// defining NOFPUT during compilation.
///
/// !Usage
/// 
/// -# Enable the DBGU pins (see pio & board.h).
/// -# Configure the DBGU using DBGU_Configure with the desired operating mode.
/// -# Send characters using DBGU_PutChar() or the printf() method.
/// -# Receive characters using DBGU_GetChar().
///
/// \note Unless specified, all the functions defined here operate synchronously;
/// i.e. they all wait the data is sent/received before returning.
//------------------------------------------------------------------------------

#ifndef DBGU_H
#define DBGU_H

//------------------------------------------------------------------------------
//         Definitions
//------------------------------------------------------------------------------
 
/// Standard operating mode (asynchronous, 8bit, no parity, 1 stop bit)
#define DBGU_STANDARD           AT91C_US_PAR_NONE

//------------------------------------------------------------------------------
//         Global functions
//------------------------------------------------------------------------------

extern void DBGU_Configure(
    unsigned int mode,
    unsigned int baudrate,
    unsigned int mck);

extern unsigned char DBGU_GetChar(void);

extern void DBGU_PutChar(unsigned char c);

extern unsigned int DBGU_IsRxReady(void);

#endif //#ifndef DBGU_H

