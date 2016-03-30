/*
    FreeRTOS V9.0.0rc2 - Copyright (C) 2016 Real Time Engineers Ltd.
    All rights reserved

    VISIT http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation >>>> AND MODIFIED BY <<<< the FreeRTOS exception.

    ***************************************************************************
    >>!   NOTE: The modification to the GPL is included to allow you to     !<<
    >>!   distribute a combined work that includes FreeRTOS without being   !<<
    >>!   obliged to provide the source code for proprietary components     !<<
    >>!   outside of the FreeRTOS kernel.                                   !<<
    ***************************************************************************

    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT ANY
    WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
    FOR A PARTICULAR PURPOSE.  Full license text is available on the following
    link: http://www.freertos.org/a00114.html

    ***************************************************************************
     *                                                                       *
     *    FreeRTOS provides completely free yet professionally developed,    *
     *    robust, strictly quality controlled, supported, and cross          *
     *    platform software that is more than just the market leader, it     *
     *    is the industry's de facto standard.                               *
     *                                                                       *
     *    Help yourself get started quickly while simultaneously helping     *
     *    to support the FreeRTOS project by purchasing a FreeRTOS           *
     *    tutorial book, reference manual, or both:                          *
     *    http://www.FreeRTOS.org/Documentation                              *
     *                                                                       *
    ***************************************************************************

    http://www.FreeRTOS.org/FAQHelp.html - Having a problem?  Start by reading
    the FAQ page "My application does not run, what could be wrong?".  Have you
    defined configASSERT()?

    http://www.FreeRTOS.org/support - In return for receiving this top quality
    embedded software for free we request you assist our global community by
    participating in the support forum.

    http://www.FreeRTOS.org/training - Investing in training allows your team to
    be as productive as possible as early as possible.  Now you can receive
    FreeRTOS training directly from Richard Barry, CEO of Real Time Engineers
    Ltd, and the world's leading authority on the world's leading RTOS.

    http://www.FreeRTOS.org/plus - A selection of FreeRTOS ecosystem products,
    including FreeRTOS+Trace - an indispensable productivity tool, a DOS
    compatible FAT file system, and our tiny thread aware UDP/IP stack.

    http://www.FreeRTOS.org/labs - Where new FreeRTOS products go to incubate.
    Come and try FreeRTOS+TCP, our new open source TCP/IP stack for FreeRTOS.

    http://www.OpenRTOS.com - Real Time Engineers ltd. license FreeRTOS to High
    Integrity Systems ltd. to sell under the OpenRTOS brand.  Low cost OpenRTOS
    licenses offer ticketed support, indemnification and commercial middleware.

    http://www.SafeRTOS.com - High Integrity Systems also provide a safety
    engineered and independently SIL3 certified version for use in safety and
    mission critical applications that require provable dependability.

    1 tab == 4 spaces!
*/

/*
	BASIC SERIAL PORT DRIVER.

	This file just maps generic functions used by FreeRTOS example code to the
	simple UART drivers provided by Altera.
*/

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"
#include "semphr.h"

/* Demo application includes. */
#include "serial.h"

/* Altera library includes. */
#include "uart0_support.h"

/*-----------------------------------------------------------*/

/*
 * See the serial2.h header file.
 */
xComPortHandle xSerialPortInitMinimal( uint32_t ulWantedBaud, UBaseType_t uxQueueLength )
{
	/* Just call into the Altera support function, which has its own parameters,
	so the parameters passed in here are not used. */
	( void ) ulWantedBaud;
	( void ) uxQueueLength;
	uart0_init();

	return ( xComPortHandle ) 0;
}
/*-----------------------------------------------------------*/

BaseType_t xSerialGetChar( xComPortHandle pxPort, signed char *pcRxedChar, TickType_t xBlockTime )
{
BaseType_t xReturn;

	/* Just call into the Altera support function, which has its own parameters,
	so the parameters passed in here are not used. */
	( void ) pxPort;
	( void ) xBlockTime;

	*pcRxedChar = uart0_getc();

	if( *pcRxedChar != -1 )
	{
		xReturn = pdPASS;
	}
	else
	{
		xReturn = pdFAIL;
	}

	return xReturn;
}
/*-----------------------------------------------------------*/

void vSerialPutString( xComPortHandle pxPort, const signed char * const pcString, unsigned short usStringLength )
{
	/* Just call into the Altera support function, which has its own parameters,
	so the parameters passed in here are not used. */
	( void ) pxPort;

	uart0_print( ( char * ) pcString );
}
/*-----------------------------------------------------------*/

signed portBASE_TYPE xSerialPutChar( xComPortHandle pxPort, signed char cOutChar, TickType_t xBlockTime )
{
char cOutBytes[ 2 ];

	/* Just call into the Altera support function, which has its own parameters,
	so the parameters passed in here are not used. */
	( void ) pxPort;

	cOutBytes[ 0 ] = cOutChar;
	cOutBytes[ 1 ] = 0x00;
	uart0_print( cOutBytes );

	return pdPASS;
}
/*-----------------------------------------------------------*/

void vSerialClose(xComPortHandle xPort)
{
	/* Not supported as not required by the demo application. */
	( void ) xPort;
}
/*-----------------------------------------------------------*/

