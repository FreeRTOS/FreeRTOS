/* ----------------------------------------------------------------------------
 *         ATMEL Microcontroller Software Support 
 * ----------------------------------------------------------------------------
 * Copyright (c) 2014, Atmel Corporation
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


#ifndef UART_H
#define UART_H


//------------------------------------------------------------------------------
//         Global functions
//------------------------------------------------------------------------------

void UART_Configure(Uart *uart, uint32_t mode, uint32_t baudrate, uint32_t masterClock);

void UART_SetTransmitterEnabled(Uart *uart, uint8_t enabled);

void UART_SetReceiverEnabled(Uart *uart, uint8_t enabled);

void UART_PutChar( Uart *uart, uint8_t c);

uint32_t UART_IsRxReady(Uart *uart);

uint8_t UART_GetChar(Uart *uart);

uint32_t UART_GetStatus(Uart *uart);

void UART_EnableIt(Uart *uart,uint32_t mode);

void UART_DisableIt(Uart *uart,uint32_t mode);

uint32_t UART_GetItMask(Uart *uart);

void UART_SendBuffer(Uart *uart, uint8_t *pBuffer, uint32_t BuffLen);

void UART_ReceiveBuffer(Uart *uart, uint8_t *pBuffer, uint32_t BuffLen);

void UART_CompareConfig(Uart *uart, uint8_t Val1, uint8_t Val2);

uint32_t UART_IsTxReady(Uart *uart);
#endif //#ifndef UART_H

