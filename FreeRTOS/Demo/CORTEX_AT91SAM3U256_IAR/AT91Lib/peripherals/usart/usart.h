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
/// \dir
/// !Purpose
/// 
/// This module provides several definitions and methods for using an USART
/// peripheral.
///
/// !Usage
/// -# Enable the USART peripheral clock in the PMC.
/// -# Enable the required USART PIOs (see pio.h).
/// -# Configure the UART by calling USART_Configure.
/// -# Enable the transmitter and/or the receiver of the USART using
///    USART_SetTransmitterEnabled and USART_SetReceiverEnabled.
/// -# Send data through the USART using the USART_Write and
///    USART_WriteBuffer methods.
/// -# Receive data from the USART using the USART_Read and
///    USART_ReadBuffer functions; the availability of data can be polled
///    with USART_IsDataAvailable.
/// -# Disable the transmitter and/or the receiver of the USART with
///    USART_SetTransmitterEnabled and USART_SetReceiverEnabled.
//------------------------------------------------------------------------------

#ifndef USART_H
#define USART_H

//------------------------------------------------------------------------------
//         Headers
//------------------------------------------------------------------------------

#include <board.h>

//------------------------------------------------------------------------------
//         Definitions
//------------------------------------------------------------------------------

//------------------------------------------------------------------------------
/// \page "USART modes"
/// This page lists several common operating modes for an USART peripheral.
/// 
/// !Modes
/// - USART_MODE_ASYNCHRONOUS
/// - USART_MODE_IRDA

/// Basic asynchronous mode, i.e. 8 bits no parity.
#define USART_MODE_ASYNCHRONOUS (AT91C_US_CHRL_8_BITS | AT91C_US_PAR_NONE)

/// IRDA mode
#define USART_MODE_IRDA         (AT91C_US_USMODE_IRDA | AT91C_US_CHRL_8_BITS | AT91C_US_PAR_NONE | AT91C_US_FILTER)
//------------------------------------------------------------------------------

//------------------------------------------------------------------------------
//         Exported functions
//------------------------------------------------------------------------------

extern void USART_Configure(
    AT91S_USART *usart,
    unsigned int mode,
    unsigned int baudrate,
    unsigned int masterClock);

extern void USART_SetTransmitterEnabled(AT91S_USART *usart, unsigned char enabled);

extern void USART_SetReceiverEnabled(AT91S_USART *usart, unsigned char enabled);

extern void USART_Write(
    AT91S_USART *usart, 
    unsigned short data, 
    volatile unsigned int timeOut);

extern unsigned char USART_WriteBuffer(
    AT91S_USART *usart,
    void *buffer,
    unsigned int size);

extern unsigned short USART_Read(
    AT91S_USART *usart, 
    volatile unsigned int timeOut);

extern unsigned char USART_ReadBuffer(
    AT91S_USART *usart,
    void *buffer,
    unsigned int size);

extern unsigned char USART_IsDataAvailable(AT91S_USART *usart);

extern void USART_SetIrdaFilter(AT91S_USART *pUsart, unsigned char filter);

#endif //#ifndef USART_H

