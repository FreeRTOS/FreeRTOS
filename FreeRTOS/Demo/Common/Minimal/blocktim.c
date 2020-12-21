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

/* Task priorities and stack sizes.  Allow these to be overridden. */
#ifndef bktPRIMARY_PRIORITY
	#define bktPRIMARY_PRIORITY		( configMAX_PRIORITIES - 3 )
#endif

#ifndef bktSECONDARY_PRIORITY
	#define bktSECONDARY_PRIORITY	( configMAX_PRIORITIES - 4 )
#endif

#ifndef bktBLOCK_TIME_TASK_STACK_SIZE
	#define bktBLOCK_TIME_TASK_STACK_SIZE configMINIMAL_STACK_SIZE
#endif

/* Task behaviour. */
#define bktQUEUE_LENGTH				( 5 )
#define bktSHORT_WAIT				pdMS_TO_TICKS( ( TickType_t ) 20 )
#define bktPRIMARY_BLOCK_TIME		( 10 )
#define bktALLOWABLE_MARGIN			( 15 )
#define bktTIME_TO_BLOCK			( 175 )
#define bktDONT_BLOCK				( ( TickType_t ) 0 )
#define bktRUN_INDICATOR			( ( UBaseType_t ) 0x55 )

/* In case the demo does not have software timers enabled, as this file uses
the configTIMER_TASK_PRIORITY setting. */
#ifndef configTIMER_TASK_PRIORITY
	#define configTIMER_TASK_PRIORITY ( configMAX_PRIORITIES - 1 )
#endif

/*-----------------------------------------------------------*/

/*
 * The two test tasks.  Their behaviour is commented within the functions.
 */
static void vPrimaryBlockTimeTestTask( void *pvParameters );
static void vSecondaryBlockTimeTestTask( void *pvParameters );

/*
 * Very basic tests to verify the block times are as expected.
 */
static void prvBasicDelayTests( void );

/*-----------------------------------------------------------*/

/* The queue on which the tasks block. */
static QueueHandle_t xTestQueue;

/* Handle to the secondary task is required by the primary task for calls
to vTaskSuspend/Resume(). */
static TaskHandle_t xSecondary;

/* Used to ensure that tasks are still executing without error. */
static volatile BaseType_t xPrimaryCycles = 0, xSecondaryCycles = 0;
static volatile BaseType_t xErrorOccurred = pdFALSE;

/* Provides a simple mechanism for the primary task to know when the
secondary task has executed. */
static volatile UBaseType_t xRunIndicator;

/*-----------------------------------------------------------*/

void vCreateBlockTimeTasks( void )
{
	/* Create the queue on which the two tasks block. */
	xTestQueue = xQueueCreate( bktQUEUE_LENGTH, sizeof( BaseType_t ) );

	if( xTestQueue != NULL )
	{
		/* vQueueAddToRegistry() adds the queue to the queue registry, if one
		is in use.  The queue registry is provided as a means for kernel aware
		debuggers to locate queues and has no purpose if a kernel aware
		debugger is not being used.  The call to vQueueAddToRegistry() will be
		removed by the pre-processor if configQUEUE_REGISTRY_SIZE is not
		defined or is defined to be less than 1. */
		vQueueAddToRegistry( xTestQueue, "Block_Time_Queue" );

		/* Create the two test tasks. */
		xTaskCreate( vPrimaryBlockTimeTestTask, "BTest1", bktBLOCK_TIME_TASK_STACK_SIZE, NULL, bktPRIMARY_PRIORITY, NULL );
		xTaskCreate( vSecondaryBlockTimeTestTask, "BTest2", bktBLOCK_TIME_TASK_STACK_SIZE, NULL, bktSECONDARY_PRIORITY, &xSecondary );
	}
}
/*-----------------------------------------------------------*/

static void vPrimaryBlockTimeTestTask( void *pvParameters )
{
BaseType_t xItem, xData;
TickType_t xTimeWhenBlocking;
TickType_t xTimeToBlock, xBlockedTime;

	( void ) pvParameters;

	for( ;; )
	{
		/*********************************************************************
		Test 0

		Basic vTaskDelay() and vTaskDelayUntil() tests. */
		prvBasicDelayTests();


		/*********************************************************************
		Test 1

		Simple block time wakeup test on queue receives. */
		for( xItem = 0; xItem < bktQUEUE_LENGTH; xItem++ )
		{
			/* The queue is empty. Attempt to read from the queue using a block
			time.  When we wake, ensure the delta in time is as expected. */
			xTimeToBlock = ( TickType_t ) ( bktPRIMARY_BLOCK_TIME << xItem );

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
			xTimeToBlock = ( TickType_t ) ( bktPRIMARY_BLOCK_TIME << xItem );

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
TickType_t xTimeWhenBlocking, xBlockedTime;
BaseType_t xData;

	( void ) pvParameters;

	for( ;; )
	{
		/*********************************************************************
		Test 0, 1 and 2

		This task does not participate in these tests. */
		vTaskSuspend( NULL );

		/*********************************************************************
		Test 3

		The first thing we do is attempt to read from the queue.  It should be
		full so we block.  Note the time before we block so we can check the
		wake time is as per that expected. */
		xTimeWhenBlocking = xTaskGetTickCount();

		/* We should unblock after bktTIME_TO_BLOCK having not sent anything to
		the queue. */
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

static void prvBasicDelayTests( void )
{
TickType_t xPreTime, xPostTime, x, xLastUnblockTime, xExpectedUnblockTime;
const TickType_t xPeriod = 75, xCycles = 5, xAllowableMargin = ( bktALLOWABLE_MARGIN >> 1 ), xHalfPeriod = xPeriod / ( TickType_t ) 2;
BaseType_t xDidBlock;

	/* Temporarily increase priority so the timing is more accurate, but not so
	high as to disrupt the timer tests. */
	vTaskPrioritySet( NULL, configTIMER_TASK_PRIORITY - 1 );

	/* Crude check to too see that vTaskDelay() blocks for the expected
	period. */
	xPreTime = xTaskGetTickCount();
	vTaskDelay( bktTIME_TO_BLOCK );
	xPostTime = xTaskGetTickCount();

	/* The priority is higher, so the allowable margin is halved when compared
	to the other tests in this file. */
	if( ( xPostTime - xPreTime ) > ( bktTIME_TO_BLOCK + xAllowableMargin ) )
	{
		xErrorOccurred = pdTRUE;
	}

	/* Now crude tests to check the vTaskDelayUntil() functionality. */
	xPostTime = xTaskGetTickCount();
	xLastUnblockTime = xPostTime;

	for( x = 0; x < xCycles; x++ )
	{
		/* Calculate the next expected unblock time from the time taken before
		this loop was entered. */
		xExpectedUnblockTime = xPostTime + ( x * xPeriod );

		vTaskDelayUntil( &xLastUnblockTime, xPeriod );

		if( ( xTaskGetTickCount() - xExpectedUnblockTime ) > ( bktTIME_TO_BLOCK + xAllowableMargin ) )
		{
			xErrorOccurred = pdTRUE;
		}

		xPrimaryCycles++;
	}

	/* Crude tests for return value of xTaskDelayUntil().  First a standard block
	should return that the task does block. */
	xDidBlock = xTaskDelayUntil( &xLastUnblockTime, xPeriod );
	if( xDidBlock != pdTRUE )
	{
		xErrorOccurred = pdTRUE;
	}

	/* Now delay a few ticks so repeating the above block period will not block for
	the full amount of time, but will still block. */
	vTaskDelay( xHalfPeriod );
	xDidBlock = xTaskDelayUntil( &xLastUnblockTime, xPeriod );
	if( xDidBlock != pdTRUE )
	{
		xErrorOccurred = pdTRUE;
	}

	/* This time block for longer than xPeriod before calling xTaskDelayUntil() so
	the call to xTaskDelayUntil() should not block. */
	vTaskDelay( xPeriod );
	xDidBlock = xTaskDelayUntil( &xLastUnblockTime, xPeriod );
	if( xDidBlock != pdFALSE )
	{
		xErrorOccurred = pdTRUE;
	}

	/* Catch up. */
	xDidBlock = xTaskDelayUntil( &xLastUnblockTime, xPeriod );
	if( xDidBlock != pdTRUE )
	{
		xErrorOccurred = pdTRUE;
	}

	/* Again block for slightly longer than a period so ensure the time is in the
	past next time xTaskDelayUntil() gets called. */
	vTaskDelay( xPeriod + xAllowableMargin );
	xDidBlock = xTaskDelayUntil( &xLastUnblockTime, xPeriod );
	if( xDidBlock != pdFALSE )
	{
		xErrorOccurred = pdTRUE;
	}

	/* Reset to the original task priority ready for the other tests. */
	vTaskPrioritySet( NULL, bktPRIMARY_PRIORITY );
}
/*-----------------------------------------------------------*/

BaseType_t xAreBlockTimeTestTasksStillRunning( void )
{
static BaseType_t xLastPrimaryCycleCount = 0, xLastSecondaryCycleCount = 0;
BaseType_t xReturn = pdPASS;

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
