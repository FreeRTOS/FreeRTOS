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


