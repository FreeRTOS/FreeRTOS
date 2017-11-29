/*
 * FreeRTOS Kernel V10.0.0
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
 * copies or substantial portions of the Software. If you wish to use our Amazon
 * FreeRTOS name, please do so in a fair use way that does not cause confusion.
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

