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

#ifndef TWI_H
#define TWI_H

//------------------------------------------------------------------------------
//         Headers
//------------------------------------------------------------------------------

#include <board.h>

//------------------------------------------------------------------------------
//         Global definitions
//------------------------------------------------------------------------------

// Missing AT91C_TWI_TXRDY definition.
#ifndef AT91C_TWI_TXRDY
    #define AT91C_TWI_TXRDY   AT91C_TWI_TXRDY_MASTER
#endif

// Missing AT91C_TWI_TXCOMP definition.
#ifndef AT91C_TWI_TXCOMP
    #define AT91C_TWI_TXCOMP  AT91C_TWI_TXCOMP_MASTER
#endif

//------------------------------------------------------------------------------
//         Global macros
//------------------------------------------------------------------------------

/// Returns 1 if the TXRDY bit (ready to transmit data) is set in the given
/// status register value.
#define TWI_STATUS_TXRDY(status) ((status & AT91C_TWI_TXRDY) == AT91C_TWI_TXRDY)

/// Returns 1 if the RXRDY bit (ready to receive data) is set in the given
/// status register value.
#define TWI_STATUS_RXRDY(status) ((status & AT91C_TWI_RXRDY) == AT91C_TWI_RXRDY)

/// Returns 1 if the TXCOMP bit (transfer complete) is set in the given
/// status register value.
#define TWI_STATUS_TXCOMP(status) ((status & AT91C_TWI_TXCOMP) == AT91C_TWI_TXCOMP)

//------------------------------------------------------------------------------
//         Global functions
//------------------------------------------------------------------------------

extern void TWI_Configure(AT91S_TWI *pTwi, unsigned int twck, unsigned int mck);

extern void TWI_Stop(AT91S_TWI *pTwi);

extern void TWI_StartRead(
    AT91S_TWI *pTwi,
    unsigned char address,
    unsigned int iaddress,
    unsigned char isize);

extern unsigned char TWI_ReadByte(AT91S_TWI *pTwi);

extern void TWI_WriteByte(AT91S_TWI *pTwi, unsigned char byte);

extern void TWI_StartWrite(
    AT91S_TWI *pTwi,
    unsigned char address,
    unsigned int iaddress,
    unsigned char isize,
    unsigned char byte);

extern unsigned char TWI_ByteReceived(AT91S_TWI *pTwi);

extern unsigned char TWI_ByteSent(AT91S_TWI *pTwi);

extern unsigned char TWI_TransferComplete(AT91S_TWI *pTwi);

extern void TWI_EnableIt(AT91S_TWI *pTwi, unsigned int sources);

extern void TWI_DisableIt(AT91S_TWI *pTwi, unsigned int sources);

extern unsigned int TWI_GetStatus(AT91S_TWI *pTwi);

extern unsigned int TWI_GetMaskedStatus(AT91S_TWI *pTwi);

#endif //#ifndef TWI_H
