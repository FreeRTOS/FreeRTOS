/*
    FreeRTOS V9.0.0 - Copyright (C) 2016 Real Time Engineers Ltd.
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


