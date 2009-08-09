/*
	FreeRTOS V5.4.2 - Copyright (C) 2009 Real Time Engineers Ltd.

	This file is part of the FreeRTOS distribution.

	FreeRTOS is free software; you can redistribute it and/or modify it	under 
	the terms of the GNU General Public License (version 2) as published by the 
	Free Software Foundation and modified by the FreeRTOS exception.
	**NOTE** The exception to the GPL is included to allow you to distribute a
	combined work that includes FreeRTOS without being obliged to provide the 
	source code for proprietary components outside of the FreeRTOS kernel.  
	Alternative commercial license and support terms are also available upon 
	request.  See the licensing section of http://www.FreeRTOS.org for full 
	license details.

	FreeRTOS is distributed in the hope that it will be useful,	but WITHOUT
	ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
	FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
	more details.

	You should have received a copy of the GNU General Public License along
	with FreeRTOS; if not, write to the Free Software Foundation, Inc., 59
	Temple Place, Suite 330, Boston, MA  02111-1307  USA.


	***************************************************************************
	*                                                                         *
	* Looking for a quick start?  Then check out the FreeRTOS eBook!          *
	* See http://www.FreeRTOS.org/Documentation for details                   *
	*                                                                         *
	***************************************************************************

	1 tab == 4 spaces!

	Please ensure to read the configuration and relevant port sections of the
	online documentation.

	http://www.FreeRTOS.org - Documentation, latest information, license and
	contact details.

	http://www.SafeRTOS.com - A version that is certified for use in safety
	critical systems.

	http://www.OpenRTOS.com - Commercial support, development, porting,
	licensing and training services.
*/

/*
 * This file contains some test scenarios that ensure tasks do not exit queue
 * send or receive functions prematurely.  A description of the tests is
 * included within the code.
 */

/* Kernel includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"

/* Demo includes. */
#include "blocktim.h"

/* Task priorities.  Allow these to be overridden. */
#ifndef bktPRIMARY_PRIORITY
	#define bktPRIMARY_PRIORITY			( 3 )
#endif

#ifndef bktSECONDARY_PRIORITY
	#define bktSECONDARY_PRIORITY		( 2 )
#endif

/* Task behaviour. */
#define bktQUEUE_LENGTH				( 5 )
#define bktSHORT_WAIT				( ( ( portTickType ) 20 ) / portTICK_RATE_MS )
#define bktPRIMARY_BLOCK_TIME		( 10 )
#define bktALLOWABLE_MARGIN			( 15 )
#define bktTIME_TO_BLOCK			( 175 )
#define bktDONT_BLOCK				( ( portTickType ) 0 )
#define bktRUN_INDICATOR			( ( unsigned portBASE_TYPE ) 0x55 )

/* The queue on which the tasks block. */
static xQueueHandle xTestQueue;

/* Handle to the secondary task is required by the primary task for calls
to vTaskSuspend/Resume(). */
static xTaskHandle xSecondary;

/* Used to ensure that tasks are still executing without error. */
static volatile portBASE_TYPE xPrimaryCycles = 0, xSecondaryCycles = 0;
static volatile portBASE_TYPE xErrorOccurred = pdFALSE;

/* Provides a simple mechanism for the primary task to know when the
secondary task has executed. */
static volatile unsigned portBASE_TYPE xRunIndicator;

/* The two test tasks.  Their behaviour is commented within the files. */
static void vPrimaryBlockTimeTestTask( void *pvParameters );
static void vSecondaryBlockTimeTestTask( void *pvParameters );

/*-----------------------------------------------------------*/

void vCreateBlockTimeTasks( void )
{
	/* Create the queue on which the two tasks block. */
    xTestQueue = xQueueCreate( bktQUEUE_LENGTH, sizeof( portBASE_TYPE ) );

	/* vQueueAddToRegistry() adds the queue to the queue registry, if one is
	in use.  The queue registry is provided as a means for kernel aware
	debuggers to locate queues and has no purpose if a kernel aware debugger
	is not being used.  The call to vQueueAddToRegistry() will be removed
	by the pre-processor if configQUEUE_REGISTRY_SIZE is not defined or is
	defined to be less than 1. */
	vQueueAddToRegistry( xTestQueue, ( signed portCHAR * ) "Block_Time_Queue" );

	/* Create the two test tasks. */
	xTaskCreate( vPrimaryBlockTimeTestTask, ( signed portCHAR * )"BTest1", configMINIMAL_STACK_SIZE, NULL, bktPRIMARY_PRIORITY, NULL );
	xTaskCreate( vSecondaryBlockTimeTestTask, ( signed portCHAR * )"BTest2", configMINIMAL_STACK_SIZE, NULL, bktSECONDARY_PRIORITY, &xSecondary );
}
/*-----------------------------------------------------------*/

static void vPrimaryBlockTimeTestTask( void *pvParameters )
{
portBASE_TYPE xItem, xData;
portTickType xTimeWhenBlocking;
portTickType xTimeToBlock, xBlockedTime;

	( void ) pvParameters;

	for( ;; )
	{
		/*********************************************************************
        Test 1

        Simple block time wakeup test on queue receives. */
		for( xItem = 0; xItem < bktQUEUE_LENGTH; xItem++ )
		{
			/* The queue is empty. Attempt to read from the queue using a block
			time.  When we wake, ensure the delta in time is as expected. */
			xTimeToBlock = bktPRIMARY_BLOCK_TIME << xItem;

			xTimeWhenBlocking = xTaskGetTickCount();

			/* We should unblock after xTimeToBlock having not received
			anything on the queue. */
			if( xQueueReceive( xTestQueue, &xData, xTimeToBlock ) != errQUEUE_EMPTY )
			{
				xErrorOccurred = pdTRUE;
			}

			/* How long were we blocked for? */
			xBlockedTime = xTaskGetTickCount() - xTimeWhenBlocking;

			if( xBlockedTime < xTimeToBlock )
			{
				/* Should not have blocked for less than we requested. */
				xErrorOccurred = pdTRUE;
			}

			if( xBlockedTime > ( xTimeToBlock + bktALLOWABLE_MARGIN ) )
			{
				/* Should not have blocked for longer than we requested,
				although we would not necessarily run as soon as we were
				unblocked so a margin is allowed. */
				xErrorOccurred = pdTRUE;
			}
		}

		/*********************************************************************
        Test 2

        Simple block time wakeup test on queue sends.

		First fill the queue.  It should be empty so all sends should pass. */
		for( xItem = 0; xItem < bktQUEUE_LENGTH; xItem++ )
		{
			if( xQueueSend( xTestQueue, &xItem, bktDONT_BLOCK ) != pdPASS )
			{
				xErrorOccurred = pdTRUE;
			}

			#if configUSE_PREEMPTION == 0
				taskYIELD();
			#endif
		}

		for( xItem = 0; xItem < bktQUEUE_LENGTH; xItem++ )
		{
			/* The queue is full. Attempt to write to the queue using a block
			time.  When we wake, ensure the delta in time is as expected. */
			xTimeToBlock = bktPRIMARY_BLOCK_TIME << xItem;

			xTimeWhenBlocking = xTaskGetTickCount();

			/* We should unblock after xTimeToBlock having not received
			anything on the queue. */
			if( xQueueSend( xTestQueue, &xItem, xTimeToBlock ) != errQUEUE_FULL )
			{
				xErrorOccurred = pdTRUE;
			}

			/* How long were we blocked for? */
			xBlockedTime = xTaskGetTickCount() - xTimeWhenBlocking;

			if( xBlockedTime < xTimeToBlock )
			{
				/* Should not have blocked for less than we requested. */
				xErrorOccurred = pdTRUE;
			}

			if( xBlockedTime > ( xTimeToBlock + bktALLOWABLE_MARGIN ) )
			{
				/* Should not have blocked for longer than we requested,
				although we would not necessarily run as soon as we were
				unblocked so a margin is allowed. */
				xErrorOccurred = pdTRUE;
			}
		}

		/*********************************************************************
        Test 3

		Wake the other task, it will block attempting to post to the queue.
		When we read from the queue the other task will wake, but before it
		can run we will post to the queue again.  When the other task runs it
		will find the queue still full, even though it was woken.  It should
		recognise that its block time has not expired and return to block for
		the remains of its block time.

		Wake the other task so it blocks attempting to post to the already
		full queue. */
		xRunIndicator = 0;
		vTaskResume( xSecondary );

		/* We need to wait a little to ensure the other task executes. */
		while( xRunIndicator != bktRUN_INDICATOR )
		{
			/* The other task has not yet executed. */
			vTaskDelay( bktSHORT_WAIT );
		}
		/* Make sure the other task is blocked on the queue. */
		vTaskDelay( bktSHORT_WAIT );
		xRunIndicator = 0;

		for( xItem = 0; xItem < bktQUEUE_LENGTH; xItem++ )
		{
			/* Now when we make space on the queue the other task should wake
			but not execute as this task has higher priority. */
			if( xQueueReceive( xTestQueue, &xData, bktDONT_BLOCK ) != pdPASS )
			{
				xErrorOccurred = pdTRUE;
			}

			/* Now fill the queue again before the other task gets a chance to
			execute.  If the other task had executed we would find the queue
			full ourselves, and the other task have set xRunIndicator. */
			if( xQueueSend( xTestQueue, &xItem, bktDONT_BLOCK ) != pdPASS )
			{
				xErrorOccurred = pdTRUE;
			}

			if( xRunIndicator == bktRUN_INDICATOR )
			{
				/* The other task should not have executed. */
				xErrorOccurred = pdTRUE;
			}

			/* Raise the priority of the other task so it executes and blocks
			on the queue again. */
			vTaskPrioritySet( xSecondary, bktPRIMARY_PRIORITY + 2 );

			/* The other task should now have re-blocked without exiting the
			queue function. */
			if( xRunIndicator == bktRUN_INDICATOR )
			{
				/* The other task should not have executed outside of the
				queue function. */
				xErrorOccurred = pdTRUE;
			}

			/* Set the priority back down. */
			vTaskPrioritySet( xSecondary, bktSECONDARY_PRIORITY );
		}

		/* Let the other task timeout.  When it unblockes it will check that it
		unblocked at the correct time, then suspend itself. */
		while( xRunIndicator != bktRUN_INDICATOR )
		{
			vTaskDelay( bktSHORT_WAIT );
		}
		vTaskDelay( bktSHORT_WAIT );
		xRunIndicator = 0;


		/*********************************************************************
        Test 4

		As per test 3 - but with the send and receive the other way around.
		The other task blocks attempting to read from the queue.

		Empty the queue.  We should find that it is full. */
		for( xItem = 0; xItem < bktQUEUE_LENGTH; xItem++ )
		{
			if( xQueueReceive( xTestQueue, &xData, bktDONT_BLOCK ) != pdPASS )
			{
				xErrorOccurred = pdTRUE;
			}
		}

		/* Wake the other task so it blocks attempting to read from  the
		already	empty queue. */
		vTaskResume( xSecondary );

		/* We need to wait a little to ensure the other task executes. */
		while( xRunIndicator != bktRUN_INDICATOR )
		{
			vTaskDelay( bktSHORT_WAIT );
		}
		vTaskDelay( bktSHORT_WAIT );
		xRunIndicator = 0;

		for( xItem = 0; xItem < bktQUEUE_LENGTH; xItem++ )
		{
			/* Now when we place an item on the queue the other task should
			wake but not execute as this task has higher priority. */
			if( xQueueSend( xTestQueue, &xItem, bktDONT_BLOCK ) != pdPASS )
			{
				xErrorOccurred = pdTRUE;
			}

			/* Now empty the queue again before the other task gets a chance to
			execute.  If the other task had executed we would find the queue
			empty ourselves, and the other task would be suspended. */
			if( xQueueReceive( xTestQueue, &xData, bktDONT_BLOCK ) != pdPASS )
			{
				xErrorOccurred = pdTRUE;
			}

			if( xRunIndicator == bktRUN_INDICATOR )
			{
				/* The other task should not have executed. */
				xErrorOccurred = pdTRUE;
			}

			/* Raise the priority of the other task so it executes and blocks
			on the queue again. */
			vTaskPrioritySet( xSecondary, bktPRIMARY_PRIORITY + 2 );

			/* The other task should now have re-blocked without exiting the
			queue function. */
			if( xRunIndicator == bktRUN_INDICATOR )
			{
				/* The other task should not have executed outside of the
				queue function. */
				xErrorOccurred = pdTRUE;
			}
			vTaskPrioritySet( xSecondary, bktSECONDARY_PRIORITY );
		}

		/* Let the other task timeout.  When it unblockes it will check that it
		unblocked at the correct time, then suspend itself. */
		while( xRunIndicator != bktRUN_INDICATOR )
		{
			vTaskDelay( bktSHORT_WAIT );
		}
		vTaskDelay( bktSHORT_WAIT );

		xPrimaryCycles++;
	}
}
/*-----------------------------------------------------------*/

static void vSecondaryBlockTimeTestTask( void *pvParameters )
{
portTickType xTimeWhenBlocking, xBlockedTime;
portBASE_TYPE xData;

	( void ) pvParameters;

	for( ;; )
	{
		/*********************************************************************
        Test 1 and 2

		This task does does not participate in these tests. */
		vTaskSuspend( NULL );

		/*********************************************************************
        Test 3

		The first thing we do is attempt to read from the queue.  It should be
		full so we block.  Note the time before we block so we can check the
		wake time is as per that expected. */
		xTimeWhenBlocking = xTaskGetTickCount();

		/* We should unblock after bktTIME_TO_BLOCK having not sent
		anything to the queue. */
		xData = 0;
		xRunIndicator = bktRUN_INDICATOR;
		if( xQueueSend( xTestQueue, &xData, bktTIME_TO_BLOCK ) != errQUEUE_FULL )
		{
			xErrorOccurred = pdTRUE;
		}

		/* How long were we inside the send function? */
		xBlockedTime = xTaskGetTickCount() - xTimeWhenBlocking;

		/* We should not have blocked for less time than bktTIME_TO_BLOCK. */
		if( xBlockedTime < bktTIME_TO_BLOCK )
		{
			xErrorOccurred = pdTRUE;
		}

		/* We should of not blocked for much longer than bktALLOWABLE_MARGIN
		either.  A margin is permitted as we would not necessarily run as
		soon as we unblocked. */
		if( xBlockedTime > ( bktTIME_TO_BLOCK + bktALLOWABLE_MARGIN ) )
		{
			xErrorOccurred = pdTRUE;
		}

		/* Suspend ready for test 3. */
		xRunIndicator = bktRUN_INDICATOR;
		vTaskSuspend( NULL );

		/*********************************************************************
        Test 4

		As per test three, but with the send and receive reversed. */
		xTimeWhenBlocking = xTaskGetTickCount();

		/* We should unblock after bktTIME_TO_BLOCK having not received
		anything on the queue. */
		xRunIndicator = bktRUN_INDICATOR;
		if( xQueueReceive( xTestQueue, &xData, bktTIME_TO_BLOCK ) != errQUEUE_EMPTY )
		{
			xErrorOccurred = pdTRUE;
		}

		xBlockedTime = xTaskGetTickCount() - xTimeWhenBlocking;

		/* We should not have blocked for less time than bktTIME_TO_BLOCK. */
		if( xBlockedTime < bktTIME_TO_BLOCK )
		{
			xErrorOccurred = pdTRUE;
		}

		/* We should of not blocked for much longer than bktALLOWABLE_MARGIN
		either.  A margin is permitted as we would not necessarily run as soon
		as we unblocked. */
		if( xBlockedTime > ( bktTIME_TO_BLOCK + bktALLOWABLE_MARGIN ) )
		{
			xErrorOccurred = pdTRUE;
		}

		xRunIndicator = bktRUN_INDICATOR;

		xSecondaryCycles++;
	}
}
/*-----------------------------------------------------------*/

portBASE_TYPE xAreBlockTimeTestTasksStillRunning( void )
{
static portBASE_TYPE xLastPrimaryCycleCount = 0, xLastSecondaryCycleCount = 0;
portBASE_TYPE xReturn = pdPASS;

	/* Have both tasks performed at least one cycle since this function was
	last called? */
	if( xPrimaryCycles == xLastPrimaryCycleCount )
	{
		xReturn = pdFAIL;
	}

	if( xSecondaryCycles == xLastSecondaryCycleCount )
	{
		xReturn = pdFAIL;
	}

	if( xErrorOccurred == pdTRUE )
	{
		xReturn = pdFAIL;
	}

	xLastSecondaryCycleCount = xSecondaryCycles;
	xLastPrimaryCycleCount = xPrimaryCycles;

	return xReturn;
}
