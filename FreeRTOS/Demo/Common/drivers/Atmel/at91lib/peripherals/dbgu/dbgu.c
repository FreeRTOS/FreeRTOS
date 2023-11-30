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
//      Headers
//------------------------------------------------------------------------------

#include "dbgu.h"
#include <stdarg.h>
#include <board.h>
            
//------------------------------------------------------------------------------
//      Exported functions
//------------------------------------------------------------------------------
//------------------------------------------------------------------------------
/// Initializes the DBGU with the given parameters, and enables both the
/// transmitter and the receiver.
/// \param mode  Operating mode to configure (see <Modes>).
/// \param baudrate  Desired baudrate.
/// \param mck  Frequency of the system master clock.
//------------------------------------------------------------------------------
void DBGU_Configure(unsigned int mode,
                           unsigned int baudrate,
                           unsigned int mck)
{   
    // Reset & disable receiver and transmitter, disable interrupts
    AT91C_BASE_DBGU->DBGU_CR = AT91C_US_RSTRX | AT91C_US_RSTTX;
    AT91C_BASE_DBGU->DBGU_IDR = 0xFFFFFFFF;
    
    // Configure baud rate
    AT91C_BASE_DBGU->DBGU_BRGR = mck / (baudrate * 16);
    
    // Configure mode register
    AT91C_BASE_DBGU->DBGU_MR = mode;
    
    // Disable DMA channel
    AT91C_BASE_DBGU->DBGU_PTCR = AT91C_PDC_RXTDIS | AT91C_PDC_TXTDIS;

    // Enable receiver and transmitter
    AT91C_BASE_DBGU->DBGU_CR = AT91C_US_RXEN | AT91C_US_TXEN;
}

//------------------------------------------------------------------------------
/// Outputs a character on the DBGU line.
/// \param c  Character to send.
//------------------------------------------------------------------------------
static void DBGU_PutChar(unsigned char c)
{
    // Wait for the transmitter to be ready
    while ((AT91C_BASE_DBGU->DBGU_CSR & AT91C_US_TXEMPTY) == 0);
    
    // Send character
    AT91C_BASE_DBGU->DBGU_THR = c;
    
    // Wait for the transfer to complete
    while ((AT91C_BASE_DBGU->DBGU_CSR & AT91C_US_TXEMPTY) == 0);
}

//------------------------------------------------------------------------------
/// Reads and returns a character from the DBGU.
//------------------------------------------------------------------------------
unsigned char DBGU_GetChar()
{
    while ((AT91C_BASE_DBGU->DBGU_CSR & AT91C_US_RXRDY) == 0);
    return AT91C_BASE_DBGU->DBGU_RHR;
}

#ifndef NOFPUT

#include <stdio.h>

//------------------------------------------------------------------------------
/// Implementation of fputc using the DBGU as the standard output. Required
/// for printf().
/// Returns the character written if successful, or -1 if the output stream is
/// not stdout or stderr.
/// \param c  Character to write.
/// \param pStream  Output stream.
//------------------------------------------------------------------------------
signed int fputc(signed int c, FILE *pStream)
{
    if ((pStream == stdout) || (pStream == stderr)) {
    
        DBGU_PutChar(c);
        return c;
    }
    else {

        return EOF;
    }
}

//------------------------------------------------------------------------------
/// Implementation of fputs using the DBGU as the standard output. Required
/// for printf(). Does NOT currently use the PDC.
/// Returns the number of characters written if successful, or -1 if the output
/// stream is not stdout or stderr.
/// \param pStr  String to write.
/// \param pStream  Output stream.
//------------------------------------------------------------------------------
signed int fputs(const char *pStr, FILE *pStream)
{
    signed int num = 0;

    while (*pStr != 0) {

        if (fputc(*pStr, pStream) == -1) {

            return -1;
        }
        num++;
        pStr++;
    }

    return num;
}

#undef putchar

//------------------------------------------------------------------------------
/// Outputs a character on the DBGU. Returns the character itself.
/// \param c  Character to output.
//------------------------------------------------------------------------------
signed int putchar(signed int c)
{
    return fputc(c, stdout);
}

#endif //#ifndef NOFPUT

