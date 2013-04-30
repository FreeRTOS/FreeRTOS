/*
    FreeRTOS V7.4.2 - Copyright (C) 2013 Real Time Engineers Ltd.

    FEATURES AND PORTS ARE ADDED TO FREERTOS ALL THE TIME.  PLEASE VISIT
    http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

    ***************************************************************************
     *                                                                       *
     *    FreeRTOS tutorial books are available in pdf and paperback.        *
     *    Complete, revised, and edited pdf reference manuals are also       *
     *    available.                                                         *
     *                                                                       *
     *    Purchasing FreeRTOS documentation will not only help you, by       *
     *    ensuring you get running as quickly as possible and with an        *
     *    in-depth knowledge of how to use FreeRTOS, it will also help       *
     *    the FreeRTOS project to continue with its mission of providing     *
     *    professional grade, cross platform, de facto standard solutions    *
     *    for microcontrollers - completely free of charge!                  *
     *                                                                       *
     *    >>> See http://www.FreeRTOS.org/Documentation for details. <<<     *
     *                                                                       *
     *    Thank you for using FreeRTOS, and thank you for your support!      *
     *                                                                       *
    ***************************************************************************


    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation AND MODIFIED BY the FreeRTOS exception.

    >>>>>>NOTE<<<<<< The modification to the GPL is included to allow you to
    distribute a combined work that includes FreeRTOS without being obliged to
    provide the source code for proprietary components outside of the FreeRTOS
    kernel.

    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT ANY
    WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
    FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more
    details. You should have received a copy of the GNU General Public License
    and the FreeRTOS license exception along with FreeRTOS; if not it can be
    viewed here: http://www.freertos.org/a00114.html and also obtained by
    writing to Real Time Engineers Ltd., contact details for whom are available
    on the FreeRTOS WEB site.

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
    including FreeRTOS+Trace - an indispensable productivity tool, and our new
    fully thread aware and reentrant UDP/IP stack.

    http://www.OpenRTOS.com - Real Time Engineers ltd license FreeRTOS to High 
    Integrity Systems, who sell the code with commercial support, 
    indemnification and middleware, under the OpenRTOS brand.
    
    http://www.SafeRTOS.com - High Integrity Systems also provide a safety 
    engineered and independently SIL3 certified version for use in safety and 
    mission critical applications that require provable dependability.
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
signed long xSerialPutChar( long lPort, signed char cOutChar, portTickType xBlockTime );

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
signed long xSerialGetChar( long lPort, signed char *pcRxedChar, portTickType xBlockTime );

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


