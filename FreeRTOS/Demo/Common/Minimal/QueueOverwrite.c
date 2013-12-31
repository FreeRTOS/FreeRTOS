/*
    FreeRTOS V8.0.0:rc1 - Copyright (C) 2014 Real Time Engineers Ltd.
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

    >>! NOTE: The modification to the GPL is included to allow you to distribute
    >>! a combined work that includes FreeRTOS without being obliged to provide
    >>! the source code for proprietary components outside of the FreeRTOS
    >>! kernel.

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

/*
 * Basic task to demonstrate the xQueueOverwrite() function.  See the comments
 * in the function itself.
 */

/* Scheduler include files. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"

/* Demo program include files. */
#include "QueueOverwrite.h"

/* A block time of 0 just means "don't block". */
#define qoDONT_BLOCK		0

/* Number of times to overwrite the value in the queue. */
#define qoLOOPS			5

/* The task that uses the queue. */
static void prvQueueOverwriteTask( void *pvParameters );

/* Variable that is incremented on each loop of prvQueueOverwriteTask() provided
prvQueueOverwriteTask() has not found any errors. */
static unsigned long ulLoopCounter = 0;

/* Set to pdFALSE if an error is discovered by the
vQueueOverwritePeriodicISRDemo() function. */
static portBASE_TYPE xISRTestStatus = pdPASS;

/* The queue that is accessed from the ISR.  The queue accessed by the task is
created inside the task itself. */
static xQueueHandle xISRQueue = NULL;

/*-----------------------------------------------------------*/

void vStartQueueOverwriteTask( unsigned portBASE_TYPE uxPriority )
{
const unsigned portBASE_TYPE uxQueueLength = 1;

	/* Create the queue used by the ISR.  xQueueOverwriteFromISR() should only
	be used on queues that have a length of 1. */
	xISRQueue = xQueueCreate( uxQueueLength, ( unsigned portBASE_TYPE ) sizeof( unsigned long ) );

	/* Create the test task.  The queue used by the test task is created inside
	the task itself. */
	xTaskCreate( prvQueueOverwriteTask, "QOver", configMINIMAL_STACK_SIZE, NULL, uxPriority, ( xTaskHandle * ) NULL );
}
/*-----------------------------------------------------------*/

static void prvQueueOverwriteTask( void *pvParameters )
{
xQueueHandle xTaskQueue;
const unsigned portBASE_TYPE uxQueueLength = 1;
unsigned long ulValue, ulStatus = pdPASS, x;

	/* The parameter is not used. */
	( void ) pvParameters;

	/* Create the queue.  xQueueOverwrite() should only be used on queues that
	have a length of 1. */
	xTaskQueue = xQueueCreate( uxQueueLength, ( unsigned portBASE_TYPE ) sizeof( unsigned long ) );
	configASSERT( xTaskQueue );

	for( ;; )
	{
		/* The queue is empty.  Writing to the queue then reading from the queue
		should return the item written. */
		ulValue = 10;
		xQueueOverwrite( xTaskQueue, &ulValue );

		ulValue = 0;
		xQueueReceive( xTaskQueue, &ulValue, qoDONT_BLOCK );

		if( ulValue != 10 )
		{
			ulStatus = pdFAIL;
		}

		/* Now try writing to the queue several times.  Each time the value
		in the queue should get overwritten. */
		for( x = 0; x < qoLOOPS; x++ )
		{
			/* Write to the queue. */
			xQueueOverwrite( xTaskQueue, &x );

			/* Check the value in the queue is that written, even though the
			queue was not necessarily empty. */
			xQueuePeek( xTaskQueue, &ulValue, qoDONT_BLOCK );
			if( ulValue != x )
			{
				ulStatus = pdFAIL;
			}

			/* There should always be one item in the queue. */
			if( uxQueueMessagesWaiting( xTaskQueue ) != uxQueueLength )
			{
				ulStatus = pdFAIL;
			}
		}

		/* Empty the queue again. */
		xQueueReceive( xTaskQueue, &ulValue, qoDONT_BLOCK );

		if( uxQueueMessagesWaiting( xTaskQueue ) != 0 )
		{
			ulStatus = pdFAIL;
		}

		if( ulStatus != pdFAIL )
		{
			/* Increment a counter to show this task is still running without
			error. */
			ulLoopCounter++;
		}

		#if( configUSE_PREEMPTION == 0 )
			taskYIELD();
		#endif
	}
}
/*-----------------------------------------------------------*/

portBASE_TYPE xIsQueueOverwriteTaskStillRunning( void )
{
portBASE_TYPE xReturn;

	if( xISRTestStatus != pdPASS )
	{
		xReturn = pdFAIL;
	}
	else if( ulLoopCounter > 0 )
	{
		xReturn = pdPASS;
	}
	else
	{
		/* The task has either stalled of discovered an error. */
		xReturn = pdFAIL;
	}

	ulLoopCounter = 0;

	return xReturn;
}
/*-----------------------------------------------------------*/

void vQueueOverwritePeriodicISRDemo( void )
{
static unsigned long ulCallCount = 0;
const unsigned long ulTx1 = 10UL, ulTx2 = 20UL, ulNumberOfSwitchCases = 3UL;
unsigned long ulRx;

	/* This function should be called from an interrupt, such as the tick hook
	function vApplicationTickHook(). */

	configASSERT( xISRQueue );

	switch( ulCallCount )
	{
		case 0:
			/* The queue is empty.  Write ulTx1 to the queue.  In this demo the
			last parameter is not used because there are no tasks blocked on
			this queue. */
			xQueueOverwriteFromISR( xISRQueue, &ulTx1, NULL );

			/* Peek the queue to check it holds the expected value. */
			xQueuePeekFromISR( xISRQueue, &ulRx );
			if( ulRx != ulTx1 )
			{
				xISRTestStatus = pdFAIL;
			}
			break;

		case 1:
			/* The queue already holds ulTx1.  Overwrite the value in the queue
			with ulTx2. */
			xQueueOverwriteFromISR( xISRQueue, &ulTx2, NULL );
			break;

		case 2:
			/* Read from the queue to empty the queue again.  The value read
			should be ulTx2. */
			xQueueReceiveFromISR( xISRQueue, &ulRx, NULL );

			if( ulRx != ulTx2 )
			{
				xISRTestStatus = pdFAIL;
			}
			break;
	}

	/* Run the next case in the switch statement above next time this function
	is called. */
	ulCallCount++;

	if( ulCallCount >= ulNumberOfSwitchCases )
	{
		/* Go back to the start. */
		ulCallCount = 0;
	}
}

