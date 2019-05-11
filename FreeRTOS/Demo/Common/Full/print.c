/*
 * FreeRTOS Kernel V10.2.1
 * Copyright (C) 2019 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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

/**
 * Manages a queue of strings that are waiting to be displayed.  This is used to 
 * ensure mutual exclusion of console output.
 *
 * A task wishing to display a message will call vPrintDisplayMessage (), with a 
 * pointer to the string as the parameter. The pointer is posted onto the 
 * xPrintQueue queue.
 *
 * The task spawned in main. c blocks on xPrintQueue.  When a message becomes 
 * available it calls pcPrintGetNextMessage () to obtain a pointer to the next 
 * string, then uses the functions defined in the portable layer FileIO. c to 
 * display the message.
 *
 * <b>NOTE:</b>
 * Using console IO can disrupt real time performance - depending on the port.  
 * Standard C IO routines are not designed for real time applications.  While 
 * standard IO is useful for demonstration and debugging an alternative method 
 * should be used if you actually require console IO as part of your application.
 *
 * \page PrintC print.c
 * \ingroup DemoFiles
 * <HR>
 */

/*
Changes from V2.0.0

	+ Delay periods are now specified using variables and constants of
	  TickType_t rather than unsigned long.
*/

#include <stdlib.h>

/* Scheduler include files. */
#include "FreeRTOS.h"
#include "queue.h"

/* Demo program include files. */
#include "print.h"

static QueueHandle_t xPrintQueue;

/*-----------------------------------------------------------*/

void vPrintInitialise( void )
{
const unsigned portBASE_TYPE uxQueueSize = 20;

	/* Create the queue on which errors will be reported. */
	xPrintQueue = xQueueCreate( uxQueueSize, ( unsigned portBASE_TYPE ) sizeof( char * ) );
}
/*-----------------------------------------------------------*/

void vPrintDisplayMessage( const char * const * ppcMessageToSend )
{
	#ifdef USE_STDIO
		xQueueSend( xPrintQueue, ( void * ) ppcMessageToSend, ( TickType_t ) 0 );
	#else
    	/* Stop warnings. */
		( void ) ppcMessageToSend;
	#endif
}
/*-----------------------------------------------------------*/

const char *pcPrintGetNextMessage( TickType_t xPrintRate )
{
char *pcMessage;

	if( xQueueReceive( xPrintQueue, &pcMessage, xPrintRate ) == pdPASS )
	{
		return pcMessage;
	}
	else
	{
		return NULL;
	}
}


