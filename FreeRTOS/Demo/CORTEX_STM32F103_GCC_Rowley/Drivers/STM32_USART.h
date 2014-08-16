/*
    FreeRTOS V8.1.0 - Copyright (C) 2014 Real Time Engineers Ltd. 
    All rights reserved

    VISIT http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

    ***************************************************************************
     *                                                                       *
     *    FreeRTOS provides completely free yet professionally developed,    *
     *    robust, strictly quality controlled, supported, and cross          *
     *    platform software that has become a de facto standard.             *
     *                                                                       *
     *    Help yourself get started quickly and support the FreeRTOS         *
     *    project by purchasing a FreeRTOS tutorial book, reference          *
     *    manual, or both from: http://www.FreeRTOS.org/Documentation        *
     *                                                                       *
     *    Thank you!                                                         *
     *                                                                       *
    ***************************************************************************

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation >>!AND MODIFIED BY!<< the FreeRTOS exception.

    >>!   NOTE: The modification to the GPL is included to allow you to     !<<
    >>!   distribute a combined work that includes FreeRTOS without being   !<<
    >>!   obliged to provide the source code for proprietary components     !<<
    >>!   outside of the FreeRTOS kernel.                                   !<<

    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT ANY
    WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
    FOR A PARTICULAR PURPOSE.  Full license text is available from the following
    link: http://www.freertos.org/a00114.html

    1 tab == 4 spaces!

    ***************************************************************************
     *                                                                       *
     *    Having a problem?  Start by reading the FAQ "My application does   *
     *    not run, what could be wrong?"                                     *
     *                                                                       *
     *    http://www.FreeRTOS.org/FAQHelp.html                               *
     *                                                                       *
    ***************************************************************************

    http://www.FreeRTOS.org - Documentation, books, training, latest versions,
    license and Real Time Engineers Ltd. contact details.

    http://www.FreeRTOS.org/plus - A selection of FreeRTOS ecosystem products,
    including FreeRTOS+Trace - an indispensable productivity tool, a DOS
    compatible FAT file system, and our tiny thread aware UDP/IP stack.

    http://www.OpenRTOS.com - Real Time Engineers ltd license FreeRTOS to High
    Integrity Systems to sell under the OpenRTOS brand.  Low cost OpenRTOS
    licenses offer ticketed support, indemnification and middleware.

    http://www.SafeRTOS.com - High Integrity Systems also provide a safety
    engineered and independently SIL3 certified version for use in safety and
    mission critical applications that require provable dependability.

    1 tab == 4 spaces!
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


