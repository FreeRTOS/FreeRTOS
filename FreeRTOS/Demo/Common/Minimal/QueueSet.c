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
 * blocking on the queue set receive.  A transmit task and (optionally) an
 * interrupt repeatedly unblocks the receive task by sending messages to the
 * queues in a pseudo random order.  The receive task removes the messages from
 * the queues and flags an error if the received message does not match that
 * expected.  The task sends values in the range 0 to
 * queuesetINITIAL_ISR_TX_VALUE, and the ISR sends value in the range
 * queuesetINITIAL_ISR_TX_VALUE to 0xffffffffUL;
 */

/* Standard includes. */
#include <stdlib.h>

/* Kernel includes. */
#include "FreeRTOS.h"
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

/* Messages are sent in incrementing order from both a task and an interrupt.
The task sends values in the range 0 to 0xfffe, and the interrupt sends values
in the range of 0xffff to 0xffffffff; */
#define queuesetINITIAL_ISR_TX_VALUE 0xffffUL

/* The priorities used in this demo. */
#define queuesetLOW_PRIORITY	( tskIDLE_PRIORITY )
#define queuesetMEDIUM_PRIORITY ( queuesetLOW_PRIORITY + 1 )
#define queuesetHIGH_PRIORITY	( queuesetMEDIUM_PRIORITY + 1 )

/* For test purposes the priority of the sending task is changed after every
queuesetPRIORITY_CHANGE_LOOPS number of values are sent to a queue. */
#define queuesetPRIORITY_CHANGE_LOOPS	100UL

/* The ISR sends to the queue every queuesetISR_TX_PERIOD ticks. */
#define queuesetISR_TX_PERIOD	( 100UL )

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

/* Counts how many times each queue in the set is used to ensure all the
queues are used. */
static unsigned long ulQueueUsedCounter[ queuesetNUM_QUEUES_IN_SET ] = { 0 };

/* The handle of the queue set to which the queues are added. */
static xQueueSetHandle xQueueSet;

/* If the prvQueueSetReceivingTask() task has not detected any errors then
it increments ulCycleCounter on each iteration.
xAreQueueSetTasksStillRunning() returns pdPASS if the value of
ulCycleCounter has changed between consecutive calls, and pdFALSE if
ulCycleCounter has stopped incrementing (indicating an error condition). */
static volatile unsigned long ulCycleCounter = 0UL;

/* Set to pdFAIL if an error is detected by any queue set task.
ulCycleCounter will only be incremented if xQueueSetTasksSatus equals pdPASS. */
static volatile portBASE_TYPE xQueueSetTasksStatus = pdPASS;

/* Just a flag to let the function that writes to a queue from an ISR know that
the queues are setup and can be used. */
static volatile portBASE_TYPE xSetupComplete = pdFALSE;

/* The value sent to the queue from the ISR is file scope so the
xAreQueeuSetTasksStillRunning() function can check it is incrementing as
expected. */
static volatile unsigned long ulISRTxValue = queuesetINITIAL_ISR_TX_VALUE;

/*-----------------------------------------------------------*/

void vStartQueueSetTasks( void )
{
xTaskHandle xQueueSetSendingTask;

	/* Create the two queues.  The handle of the sending task is passed into
	the receiving task using the task parameter.  The receiving task uses the
	handle to resume the sending task after it has created the queues. */
	xTaskCreate( prvQueueSetSendingTask, ( signed char * ) "Check", configMINIMAL_STACK_SIZE, NULL, queuesetMEDIUM_PRIORITY, &xQueueSetSendingTask );
	xTaskCreate( prvQueueSetReceivingTask, ( signed char * ) "Check", configMINIMAL_STACK_SIZE, ( void * ) xQueueSetSendingTask, queuesetMEDIUM_PRIORITY, NULL );

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
static unsigned long ulLastCycleCounter, ulLastISRTxValue = 0;
static unsigned long ulLastQueueUsedCounter[ queuesetNUM_QUEUES_IN_SET ] = { 0 };
portBASE_TYPE xReturn = pdPASS, x;

	if( ulLastCycleCounter == ulCycleCounter )
	{
		/* The cycle counter is no longer being incremented.  Either one of the
		tasks is stalled or an error has been detected. */
		xReturn = pdFAIL;
	}

	ulLastCycleCounter = ulCycleCounter;

	/* Ensure that all the queues in the set have been used.  This ensures the
	test is working as intended and guards against the rand() in the Tx task
	missing some values. */
	for( x = 0; x < queuesetNUM_QUEUES_IN_SET; x++ )
	{
		if( ulLastQueueUsedCounter[ x ] == ulQueueUsedCounter[ x ] )
		{
			xReturn = pdFAIL;
		}

		ulLastQueueUsedCounter[ x ] = ulQueueUsedCounter[ x ];
	}

	/* Check the global status flag. */
	if( xQueueSetTasksStatus != pdPASS )
	{
		xReturn = pdFAIL;
	}

	/* Check that the ISR is still sending values to the queues too. */
	if( ulISRTxValue == ulLastISRTxValue )
	{
		xReturn = pdFAIL;
	}
	else
	{
		ulLastISRTxValue = ulISRTxValue;
	}

	return xReturn;
}
/*-----------------------------------------------------------*/

void vQueueSetWriteToQueueFromISR( void )
{
portBASE_TYPE x = 0;
static unsigned long ulCallCount = 0;

	/* xSetupComplete is set to pdTRUE when the queues have been created and
	are available for use. */
	if( xSetupComplete == pdTRUE )
	{
		/* It is intended that this function is called from the tick hook
		function, so each call is one tick period apart. */
		ulCallCount++;
		if( ulCallCount > queuesetISR_TX_PERIOD )
		{
			ulCallCount = 0;

			/* Look for a queue that can be written to. */
			for( x = 0; x < queuesetNUM_QUEUES_IN_SET; x++ )
			{
				if( xQueues[ x ] != NULL )
				{
					/* xQueues[ x ] can be written to.  Send the next value. */
					if( xQueueSendFromISR( xQueues[ x ], ( void * ) &ulISRTxValue, NULL ) == pdPASS )
					{
						ulISRTxValue++;

						/* If the Tx value has wrapped then set it back to its
						initial	value. */
						if( ulISRTxValue == 0UL )
						{
							ulISRTxValue = queuesetINITIAL_ISR_TX_VALUE;
						}
					}

					break;
				}
			}
		}
	}
}
/*-----------------------------------------------------------*/

static void prvQueueSetSendingTask( void *pvParameters )
{
unsigned long ulTaskTxValue = 0;
portBASE_TYPE xQueueToWriteTo;
xQueueHandle xQueueInUse;
unsigned portBASE_TYPE uxPriority = queuesetMEDIUM_PRIORITY, ulLoops = 0;

	/* Remove compiler warning about the unused parameter. */
	( void ) pvParameters;

	srand( ( unsigned int ) &ulTaskTxValue );

	for( ;; )
	{
		/* Generate the index for the queue to which a value is to be sent. */
		xQueueToWriteTo = rand() % queuesetNUM_QUEUES_IN_SET;
		xQueueInUse = xQueues[ xQueueToWriteTo ];

		/* Note which index is being written to to ensure all the queues are
		used. */
		( ulQueueUsedCounter[ xQueueToWriteTo ] )++;

		/* Send to the queue to unblock the task that is waiting for data to
		arrive on a queue within the queue set to which this queue belongs. */
		if( xQueueSendToBack( xQueueInUse, &ulTaskTxValue, portMAX_DELAY ) != pdPASS )
		{
			/* The send should always pass as an infinite block time was
			used. */
			xQueueSetTasksStatus = pdFAIL;
		}

		/* Attempt to remove the queue from a queue set it does not belong
		to (NULL being passed as the queue set in this case). */
		if( xQueueRemoveFromQueueSet( xQueueInUse, NULL ) != pdFAIL )
		{
			/* It is not possible to successfully remove a queue from a queue
			set it does not belong to. */
			xQueueSetTasksStatus = pdFAIL;
		}

		/* Mark the space in the array of queues as being empty before actually
		removing the queue from the queue set.  This is to prevent the code
		that accesses the queue set from an interrupt from attempting to access
		a queue that is no longer in the set. */
		xQueues[ xQueueToWriteTo ] = 0;

		/* Attempt to remove the queue from the queue set it does belong to. */
		if( xQueueRemoveFromQueueSet( xQueueInUse, xQueueSet ) != pdPASS )
		{
			/* It should be possible to remove the queue from the queue set it
			does belong to. */
			xQueueSetTasksStatus = pdFAIL;
		}

		/* Add the queue back before cycling back to run again. */
		if( xQueueAddToQueueSet( xQueueInUse, xQueueSet ) != pdPASS )
		{
			/* If the queue was successfully removed from the queue set then it
			should be possible to add it back in again. */
			xQueueSetTasksStatus = pdFAIL;
		}

		/* Now the queue is back in the set it is ok for the interrupt that
		writes to the queues to access it again. */
		xQueues[ xQueueToWriteTo ] = xQueueInUse;

		ulTaskTxValue++;

		/* If the Tx value has reached the range used by the ISR then set it
		back to 0. */
		if( ulTaskTxValue == queuesetINITIAL_ISR_TX_VALUE )
		{
			ulTaskTxValue = 0;
		}

		/* Occasionally change the task priority relative to the priority of
		the receiving task. */
		ulLoops++;
		if( ulLoops >= queuesetPRIORITY_CHANGE_LOOPS )
		{
			ulLoops = 0;
			uxPriority++;
			if( uxPriority > queuesetHIGH_PRIORITY )
			{
				uxPriority = queuesetLOW_PRIORITY;
			}

			vTaskPrioritySet( NULL, uxPriority );
		}
	}
}
/*-----------------------------------------------------------*/

static void prvQueueSetReceivingTask( void *pvParameters )
{
unsigned long ulReceived, ulExpectedReceivedFromTask = 0, ulExpectedReceivedFromISR = queuesetINITIAL_ISR_TX_VALUE;
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
		/* Create the queue and add it to the set.  The queue is just holding
		unsigned long value. */
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
	xActivatedQueue = xQueueBlockMultiple( xQueueSet, queuesetSHORT_DELAY );
	configASSERT( xActivatedQueue == NULL );

	/* Resume the task that writes to the queues. */
	vTaskResume( xQueueSetSendingTask );

	/* Let the ISR access the queues also. */
	xSetupComplete = pdTRUE;

	for( ;; )
	{
		/* Wait for a message to arrive on one of the queues in the set. */
		xActivatedQueue = xQueueBlockMultiple( xQueueSet, portMAX_DELAY );
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

			/* If the received value is equal to or greater than
			queuesetINITIAL_ISR_TX_VALUE then it was sent by an ISR. */
			if( ulReceived >= queuesetINITIAL_ISR_TX_VALUE )
			{
				/* The value was sent from the ISR.  Check it against its
				expected value. */
				configASSERT( ulReceived == ulExpectedReceivedFromISR );
				if( ulReceived != ulExpectedReceivedFromISR )
				{
					xQueueSetTasksStatus = pdFAIL;
				}
				else
				{
					/* It is expected to receive an incrementing value. */
					ulExpectedReceivedFromISR++;

					/* If the expected value has wrapped then set it back to
					its initial value. */
					if( ulExpectedReceivedFromISR == 0 )
					{
						ulExpectedReceivedFromISR = queuesetINITIAL_ISR_TX_VALUE;
					}
				}
			}
			else
			{
				/* The value was sent from the Tx task.  Check it against its
				expected value. */
				configASSERT( ulReceived == ulExpectedReceivedFromTask );
				if( ulReceived != ulExpectedReceivedFromTask )
				{
					xQueueSetTasksStatus = pdFAIL;
				}
				else
				{
					/* It is expected to receive an incrementing value. */
					ulExpectedReceivedFromTask++;

					/* If the expected value has reached the range of values
					used by the ISR then set it back to 0. */
					if( ulExpectedReceivedFromTask >= queuesetINITIAL_ISR_TX_VALUE )
					{
						ulExpectedReceivedFromTask = 0;
					}
				}
			}
		}

		if( xQueueSetTasksStatus == pdPASS )
		{
			ulCycleCounter++;
		}
	}
}

