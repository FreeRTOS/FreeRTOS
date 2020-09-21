/*
 * FreeRTOS Kernel V10.3.0
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
static uint32_t ulLoopCounter = 0;

/* Set to pdFALSE if an error is discovered by the
vQueueOverwritePeriodicISRDemo() function. */
static BaseType_t xISRTestStatus = pdPASS;

/* The queue that is accessed from the ISR.  The queue accessed by the task is
created inside the task itself. */
static QueueHandle_t xISRQueue = NULL;

/*-----------------------------------------------------------*/

void vStartQueueOverwriteTask( UBaseType_t uxPriority )
{
const UBaseType_t uxQueueLength = 1;

	/* Create the queue used by the ISR.  xQueueOverwriteFromISR() should only
	be used on queues that have a length of 1. */
	xISRQueue = xQueueCreate( uxQueueLength, ( UBaseType_t ) sizeof( uint32_t ) );

	/* Create the test task.  The queue used by the test task is created inside
	the task itself. */
	xTaskCreate( prvQueueOverwriteTask, "QOver", configMINIMAL_STACK_SIZE, NULL, uxPriority, ( TaskHandle_t * ) NULL );
}
/*-----------------------------------------------------------*/

static void prvQueueOverwriteTask( void *pvParameters )
{
QueueHandle_t xTaskQueue;
const UBaseType_t uxQueueLength = 1;
uint32_t ulValue, ulStatus = pdPASS, x;

	/* The parameter is not used. */
	( void ) pvParameters;

	/* Create the queue.  xQueueOverwrite() should only be used on queues that
	have a length of 1. */
	xTaskQueue = xQueueCreate( uxQueueLength, ( UBaseType_t ) sizeof( uint32_t ) );
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

BaseType_t xIsQueueOverwriteTaskStillRunning( void )
{
BaseType_t xReturn;

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
static uint32_t ulCallCount = 0;
const uint32_t ulTx1 = 10UL, ulTx2 = 20UL, ulNumberOfSwitchCases = 3UL;
uint32_t ulRx;

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

