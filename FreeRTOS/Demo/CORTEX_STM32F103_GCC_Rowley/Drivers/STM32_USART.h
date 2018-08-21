/*
 * FreeRTOS Kernel V10.1.0
 * Copyright (C) 2017 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 * http://www.FreeRTOS.org
 * http://aws.amazon.com/freertos
 *
 * 1 tab == 4 spaces!
 */

#ifndef STM_32_SERIAL_COMMS_H
#define STM_32_SERIAL_COMMS_H

/*
 * Initialise a COM port.  As supplied 2 COM ports are supported, so ulPort can
 * be either 0 or 1.  Note that COM 0 is in effect USART1 in ST library 
 * terminology.  The baud rate can be any standard baud rate and has been tested
 * up to 115200 baud.
 */
long lCOMPortInit( unsigned long ulPort, unsigned long ulWantedBaud );

/*
 * Output a single char to a COM port.  As supplied 2 COM ports are supported,
 * so ulPort can be 0 or 1.  Note that COM 0 is in effect USART1 in ST library
 * terminology.  cOutChar is the character to be transmit, and xBlockTime is
 * the time the task should be held in the Blocked state (in ticks) for space 
 * to become available in the queue of characters waiting transmission.  pdPASS 
 * will be returned if the character is successfully queued (possible after 
 * waiting in the Blocked state for up to xBlockTime ticks), otherwise pdFAIL 
 * will be returned.
 */
signed long xSerialPutChar( long lPort, signed char cOutChar, TickType_t xBlockTime );

/*
 * Retrieve a character from the queue of received characters.  As supplied 2 
 * COM ports are supported, so ulPort can be 0 or 1.  Note that COM 0 is in 
 * effect USART1 in ST library terminology.  pcRxedChar is the address into
 * which the received character will be copied, and xBlockTime is the time the 
 * task should be held in the Blocked state (in ticks) for a character to be
 * available if one is not available immediately.  pdPASS will be returned if a
 * character is successfully returned (possible after waiting in the Blocked 
 * state for up to xBlockTime ticks), otherwise pdFAIL will be returned.
 */
signed long xSerialGetChar( long lPort, signed char *pcRxedChar, TickType_t xBlockTime );

/*
 * Send a string of characters to a COM port.  As supplied 2 COM ports are 
 * supported, so ulPort can be 0 or 1.  Note that COM 0 is in effect USART1 in 
 * ST library terminology.  pcString contains the address of the first 
 * character to be transmit, and ulStringLength the total number of characters
 * from and including *pcString.  pdPASS will be returned if the entire string
 * is queued for transmission successfully, otherwise pdFAIL will be returned.
 * Note that serPUT_STRING_CHAR_DELAY within STM32_USART.c can be adjusted in
 * accordance with the applications requirements.  Comments are included where
 * serPUT_STRING_CHAR_DELAY is defined.
 */
long lSerialPutString( long lPort, const char * const pcString, unsigned long ulStringLength );

#endif


