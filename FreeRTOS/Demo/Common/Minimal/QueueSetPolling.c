/*
 * FreeRTOS V202012.00
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
 * Tests the use of queue sets.
 *
 * A receive task creates a number of queues and adds them to a queue set before
 * blocking on the queue set receive.  A transmit task and (optionally) an
 * interrupt repeatedly unblocks the receive task by sending messages to the
 * queues in a pseudo random order.  The receive task removes the messages from
 * the queues and flags an error if the received message does not match that
 * expected.  The task sends values in the range 0 to
 * queuesetINITIAL_ISR_TX_VALUE, and the ISR sends value in the range
 * queuesetINITIAL_ISR_TX_VALUE to ULONG_MAX.
 */


/* Standard includes. */
#include <stdlib.h>
#include <limits.h>

/* Kernel includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"

/* Demo includes. */
#include "QueueSetPolling.h"

#if( configUSE_QUEUE_SETS == 1 )  /* Remove tests if queue sets are not defined. */

/* The length of each created queue. */
#define setpollQUEUE_LENGTH	10

/* Block times used in this demo.  A block time or 0 means "don't block". */
#define setpollDONT_BLOCK 0

/* The ISR sends to the queue every setpollISR_TX_PERIOD ticks. */
#define queuesetISR_TX_PERIOD	( 50UL )

/*
 * The task that reads from the queue set.
 */
static void prvQueueSetReceivingTask( void *pvParameters );

/*-----------------------------------------------------------*/

/* The queue that is added to the set. */
static QueueHandle_t xQueue = NULL;

/* The handle of the queue set to which the queue is added. */
static QueueSetHandle_t xQueueSet = NULL;

/* Set to pdFAIL if an error is detected by any queue set task.
ulCycleCounter will only be incremented if xQueueSetTasksSatus equals pdPASS. */
static volatile BaseType_t xQueueSetPollStatus = pdPASS;

/* Counter used to ensure the task is still running. */
static uint32_t ulCycleCounter = 0;

/*-----------------------------------------------------------*/

void vStartQueueSetPollingTask( void )
{
	/* Create the queue that is added to the set, the set, and add the queue to
	the set. */
	xQueue = xQueueCreate( setpollQUEUE_LENGTH, sizeof( uint32_t ) );
	xQueueSet = xQueueCreateSet( setpollQUEUE_LENGTH );

	if( ( xQueue != NULL ) && ( xQueueSet != NULL ) )
	{
		xQueueAddToSet( xQueue, xQueueSet );

		/* Create the task. */
		xTaskCreate( prvQueueSetReceivingTask, "SetPoll", configMINIMAL_STACK_SIZE, NULL, tskIDLE_PRIORITY, NULL );
	}
}
/*-----------------------------------------------------------*/

static void prvQueueSetReceivingTask( void *pvParameters )
{
uint32_t ulReceived, ulExpected = 0;
QueueHandle_t xActivatedQueue;

	/* Remove compiler warnings. */
	( void ) pvParameters;

	for( ;; )
	{
		/* Is a message waiting?  A block time is not used to ensure the queue
		set is polled while it is being written to from an interrupt. */
		xActivatedQueue = xQueueSelectFromSet( xQueueSet, setpollDONT_BLOCK );

		if( xActivatedQueue != NULL )
		{
			/* Reading from the queue should pass with a zero block time as
			this task will only run when something has been posted to a task
			in the queue set. */
			if( xQueueReceive( xActivatedQueue, &ulReceived, setpollDONT_BLOCK ) != pdPASS )
			{
				xQueueSetPollStatus = pdFAIL;
			}

			if( ulReceived == ulExpected )
			{
				ulExpected++;
			}
			else
			{
				xQueueSetPollStatus = pdFAIL;
			}

			if( xQueueSetPollStatus == pdPASS )
			{
				ulCycleCounter++;
			}
		}
	}
}
/*-----------------------------------------------------------*/

void vQueueSetPollingInterruptAccess( void )
{
static uint32_t ulCallCount = 0, ulValueToSend = 0;

	/* It is intended that this function is called from the tick hook
	function, so each call is one tick period apart. */
	ulCallCount++;
	if( ulCallCount > queuesetISR_TX_PERIOD )
	{
		ulCallCount = 0;

		if( xQueueSendFromISR( xQueue, ( void * ) &ulValueToSend, NULL ) == pdPASS )
		{
			/* Send the next value next time. */
			ulValueToSend++;
		}
	}
}
/*-----------------------------------------------------------*/

BaseType_t xAreQueueSetPollTasksStillRunning( void )
{
static uint32_t ulLastCycleCounter = 0;

	if( ulLastCycleCounter == ulCycleCounter )
	{
		xQueueSetPollStatus = pdFAIL;
	}

	ulLastCycleCounter = ulCycleCounter;

	return xQueueSetPollStatus;
}
/*-----------------------------------------------------------*/


#endif /* ( configUSE_QUEUE_SETS == 1 ) */
