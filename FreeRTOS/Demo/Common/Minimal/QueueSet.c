/*
    FreeRTOS V7.3.0 - Copyright (C) 2012 Real Time Engineers Ltd.

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
    >>>NOTE<<< The modification to the GPL is included to allow you to
    distribute a combined work that includes FreeRTOS without being obliged to
    provide the source code for proprietary components outside of the FreeRTOS
    kernel.  FreeRTOS is distributed in the hope that it will be useful, but
    WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
    or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
    more details. You should have received a copy of the GNU General Public
    License and the FreeRTOS license exception along with FreeRTOS; if not it
    can be viewed here: http://www.freertos.org/a00114.html and also obtained
    by writing to Richard Barry, contact details for whom are available on the
    FreeRTOS WEB site.

    1 tab == 4 spaces!

    ***************************************************************************
     *                                                                       *
     *    Having a problem?  Start by reading the FAQ "My application does   *
     *    not run, what could be wrong?"                                     *
     *                                                                       *
     *    http://www.FreeRTOS.org/FAQHelp.html                               *
     *                                                                       *
    ***************************************************************************


    http://www.FreeRTOS.org - Documentation, training, latest versions, license
    and contact details.

    http://www.FreeRTOS.org/plus - A selection of FreeRTOS ecosystem products,
    including FreeRTOS+Trace - an indispensable productivity tool.

    Real Time Engineers ltd license FreeRTOS to High Integrity Systems, who sell
    the code with commercial support, indemnification, and middleware, under
    the OpenRTOS brand: http://www.OpenRTOS.com.  High Integrity Systems also
    provide a safety engineered and independently SIL3 certified version under
    the SafeRTOS brand: http://www.SafeRTOS.com.
*/

/*
 * Demonstrates the creation an use of queue sets.
 *
 * A receive task creates a number of queues and adds them to a queue set before
 * blocking on a queue set receive.  A transmit task repeatedly unblocks the
 * receive task by sending messages to the queues in a pseudo random order.
 * The receive task removes the messages from the queues and flags an error if
 * the received message does not match that expected.
 */

/* Kernel includes. */
#include <FreeRTOS.h>
#include "task.h"
#include "queue.h"

/* Demo includes. */
#include "QueueSet.h"

/* The number of queues that are created and added to the queue set. */
#define queuesetNUM_QUEUES_IN_SET 3

/* The length of each created queue. */
#define queuesetQUEUE_LENGTH	3

/* Block times used in this demo.  A block time or 0 means "don't block". */
#define queuesetSHORT_DELAY	200
#define queuesetDONT_BLOCK 0

/*
 * The task that periodically sends to the queue set.
 */
static void prvQueueSetSendingTask( void *pvParameters );

/*
 * The task that reads from the queue set.
 */
static void prvQueueSetReceivingTask( void *pvParameters );

/* The queues that are added to the set. */
static xQueueHandle xQueues[ queuesetNUM_QUEUES_IN_SET ] = { 0 };

/* The handle of the queue set to which the queues are added. */
static xQueueSetHandle xQueueSet;

/* If the prvQueueSetReceivingTask() task has not detected any errors then
it increments ulCycleCounter on each iteration.
xAreQueueSetTasksStillRunning() returns pdPASS if the value of
ulCycleCounter has changed between consecutive calls, and pdFALSE if
ulCycleCounter has stopped incrementing (indicating an error condition). */
volatile unsigned long ulCycleCounter = 0UL;

/* Set to pdFAIL if an error is detected by any queue set task.
ulCycleCounter will only be incremented if xQueueSetTasksSatus equals pdPASS. */
volatile portBASE_TYPE xQueueSetTasksStatus = pdPASS;


/*-----------------------------------------------------------*/

void vStartQueueSetTasks( unsigned portBASE_TYPE uxPriority )
{
xTaskHandle xQueueSetSendingTask;

	/* Create the two queues.  The handle of the sending task is passed into
	the receiving task using the task parameter.  The receiving task uses the
	handle to resume the sending task after it has created the queues. */
	xTaskCreate( prvQueueSetSendingTask, ( signed char * ) "Check", configMINIMAL_STACK_SIZE, NULL, uxPriority, &xQueueSetSendingTask );
	xTaskCreate( prvQueueSetReceivingTask, ( signed char * ) "Check", configMINIMAL_STACK_SIZE, ( void * ) xQueueSetSendingTask, uxPriority, NULL );

	/* It is important that the sending task does not attempt to write to a
	queue before the queue has been created.  It is therefore placed into the
	suspended state before the scheduler has started.  It is resumed by the
	receiving task after the receiving task has created the queues and added the
	queues to the queue set. */
	vTaskSuspend( xQueueSetSendingTask );
}
/*-----------------------------------------------------------*/

portBASE_TYPE xAreQueueSetTasksStillRunning( void )
{
static unsigned long ulLastCycleCounter;
portBASE_TYPE xReturn;

	if( ulLastCycleCounter == ulCycleCounter )
	{
		/* The cycle counter is no longer being incremented.  Either one of the
		tasks is stalled or an error has been detected. */
		xReturn = pdFAIL;
	}
	else
	{
		xReturn = pdPASS;
	}

	return xReturn;
}
/*-----------------------------------------------------------*/

static void prvQueueSetSendingTask( void *pvParameters )
{
unsigned long ulTxValue = 0;
portBASE_TYPE xQueueToWriteTo;

	/* Remove compiler warning about the unused parameter. */
	( void ) pvParameters;

	srand( ( unsigned int ) &ulTxValue );

	for( ;; )
	{
		/* Generate the index for the queue to which a value is to be sent. */
		xQueueToWriteTo = rand() % queuesetNUM_QUEUES_IN_SET;
		if( xQueueSendToBack( xQueues[ xQueueToWriteTo ], &ulTxValue, portMAX_DELAY ) != pdPASS )
		{
			/* The send should always pass as an infinite block time was
			used. */
			xQueueSetTasksStatus = pdFAIL;
		}

		ulTxValue++;
	}
}
/*-----------------------------------------------------------*/

static void prvQueueSetReceivingTask( void *pvParameters )
{
unsigned long ulReceived, ulLastReceived = ~0UL;
xQueueHandle xActivatedQueue;
portBASE_TYPE x;
xTaskHandle xQueueSetSendingTask;

	/* The handle to the sending task is passed in using the task parameter. */
	xQueueSetSendingTask = ( xTaskHandle ) pvParameters;

	/* Ensure the queues are created and the queue set configured before the
	sending task is unsuspended.

	First Create the queue set such that it will be able to hold a message for
	every space in every queue in the set. */
	xQueueSet = xQueueSetCreate( queuesetNUM_QUEUES_IN_SET * queuesetQUEUE_LENGTH );

	for( x = 0; x < queuesetNUM_QUEUES_IN_SET; x++ )
	{
		/* Create the queue and add it to the set. */
		xQueues[ x ] = xQueueCreate( queuesetQUEUE_LENGTH, sizeof( unsigned long ) );
		configASSERT( xQueues[ x ] );
		if( xQueueAddToQueueSet( xQueues[ x ], xQueueSet ) != pdPASS )
		{
			xQueueSetTasksStatus = pdFAIL;
		}

		/* The queue has now been added to the queue set and cannot be added to
		another. */
		if( xQueueAddToQueueSet( xQueues[ x ], xQueueSet ) != pdFAIL )
		{
			xQueueSetTasksStatus = pdFAIL;
		}
	}

	/* The task that sends to the queues is not running yet, so attempting to
	read from the queue set should fail, resulting in xActivatedQueue being set
	to NULL. */
	xActivatedQueue = xQueueReadMultiple( xQueueSet, queuesetSHORT_DELAY );
	configASSERT( xActivatedQueue == NULL );

	/* Resume the task that writes to the queues. */
	vTaskResume( xQueueSetSendingTask );

	for( ;; )
	{
		/* Wait for a message to arrive on one of the queues in the set. */
		xActivatedQueue = xQueueReadMultiple( xQueueSet, portMAX_DELAY );
		configASSERT( xActivatedQueue );

		if( xActivatedQueue == NULL )
		{
			/* This should not happen as an infinite delay was used. */
			xQueueSetTasksStatus = pdFAIL;
		}
		else
		{
			/* Reading from the queue should pass with a zero block time as
			this task will only run when something has been posted to a task
			in the queue set. */
			if( xQueueReceive( xActivatedQueue, &ulReceived, queuesetDONT_BLOCK ) != pdPASS )
			{
				xQueueSetTasksStatus = pdFAIL;
			}

			/* It is always expected that the received value will be one
			greater than the previously received value. */
			configASSERT( ulReceived == ( ulLastReceived + 1 ) );
			if( ulReceived != ( ulLastReceived + 1 ) )
			{
				xQueueSetTasksStatus = pdFAIL;
			}
			else
			{
				ulLastReceived = ulReceived;
			}
		}

		if( xQueueSetTasksStatus == pdPASS )
		{
			ulCycleCounter++;
		}
	}
}

