/*
 * FreeRTOS Kernel V10.0.1
 * Copyright (C) 2017 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 * This file contains some test scenarios that ensure tasks respond correctly
 * to xTaskAbortDelay() calls.  It also ensures tasks return the correct state
 * of eBlocked when blocked indefinitely in both the case where a task is
 * blocked on an object and when a task is blocked on a notification.
 */

/* Standard includes. */
#include "limits.h"

/* Kernel includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"
#include "semphr.h"
#include "event_groups.h"
#include "stream_buffer.h"

/* Demo includes. */
#include "AbortDelay.h"

/* This file can only be used if the functionality it tests is included in the
build.  Remove the whole file if this is not the case. */
#if( INCLUDE_xTaskAbortDelay == 1 )

#if( INCLUDE_xTaskGetHandle != 1 )
	#error This test file uses the xTaskGetHandle() API function so INCLUDE_xTaskGetHandle must be set to 1 in FreeRTOSConfig.h.
#endif

/* Task priorities.  Allow these to be overridden. */
#ifndef abtCONTROLLING_PRIORITY
	#define abtCONTROLLING_PRIORITY		( configMAX_PRIORITIES - 3 )
#endif

#ifndef abtBLOCKING_PRIORITY
	#define abtBLOCKING_PRIORITY	( configMAX_PRIORITIES - 2 )
#endif

/* The tests that are performed. */
#define abtNOTIFY_WAIT_ABORTS		0
#define abtNOTIFY_TAKE_ABORTS		1
#define abtDELAY_ABORTS				2
#define abtDELAY_UNTIL_ABORTS		3
#define abtSEMAPHORE_TAKE_ABORTS	4
#define abtEVENT_GROUP_ABORTS		5
#define abtQUEUE_SEND_ABORTS		6
#define abtSTREAM_BUFFER_RECEIVE	7
#define abtMAX_TESTS				8

/*-----------------------------------------------------------*/

/*
 * The two test tasks.  The controlling task specifies which test to executed.
 * More information is provided in the comments within the tasks.
 */
static void prvControllingTask( void *pvParameters );
static void prvBlockingTask( void *pvParameters );

/*
 * Test functions called by the blocking task.  Each function follows the same
 * pattern, but the way the task blocks is different in each case.
 *
 * In each function three blocking calls are made.  The first and third
 * blocking call is expected to time out, while the middle blocking call is
 * expected to be aborted by the controlling task half way through the block
 * time.
 */
static void prvTestAbortingTaskNotifyWait( void );
static void prvTestAbortingTaskNotifyTake( void );
static void prvTestAbortingTaskDelay( void );
static void prvTestAbortingTaskDelayUntil( void );
static void prvTestAbortingSemaphoreTake( void );
static void prvTestAbortingEventGroupWait( void );
static void prvTestAbortingQueueSend( void );
static void prvTestAbortingStreamBufferReceive( void );

/*
 * Checks the amount of time a task spent in the Blocked state is within the
 * expected bounds.
 */
static void prvCheckExpectedTimeIsWithinAnAcceptableMargin( TickType_t xStartTime, TickType_t xExpectedBlockTime );

/*-----------------------------------------------------------*/

/* Used to ensure that tasks are still executing without error. */
static volatile BaseType_t xControllingCycles = 0, xBlockingCycles = 0;
static volatile BaseType_t xErrorOccurred = pdFALSE;

/* Each task needs to know the other tasks handle so they can send signals to
each other.  The handle is obtained from the task's name. */
static const char *pcControllingTaskName = "AbtCtrl", *pcBlockingTaskName = "AbtBlk";

/* The maximum amount of time a task will block for. */
const TickType_t xMaxBlockTime = pdMS_TO_TICKS( 100 );
const TickType_t xHalfMaxBlockTime = pdMS_TO_TICKS( 50 );

/* The actual block time is dependent on the priority of other tasks in the
system so the actual block time might be greater than that expected, but it
should be within an acceptable upper bound. */
const TickType_t xAllowableMargin = pdMS_TO_TICKS( 7 );

/*-----------------------------------------------------------*/

void vCreateAbortDelayTasks( void )
{
	/* Create the two test tasks described above. */
	xTaskCreate( prvControllingTask, pcControllingTaskName, configMINIMAL_STACK_SIZE, NULL, abtCONTROLLING_PRIORITY, NULL );
	xTaskCreate( prvBlockingTask, pcBlockingTaskName, configMINIMAL_STACK_SIZE, NULL, abtBLOCKING_PRIORITY, NULL );
}
/*-----------------------------------------------------------*/

static void prvControllingTask( void *pvParameters )
{
TaskHandle_t xBlockingTask;
uint32_t ulTestToPerform = abtNOTIFY_WAIT_ABORTS;
TickType_t xTimeAtStart;
const TickType_t xStartMargin = 2UL;

	/* Just to remove compiler warnings. */
	( void ) pvParameters;

	xBlockingTask = xTaskGetHandle( pcBlockingTaskName );
	configASSERT( xBlockingTask );

	for( ;; )
	{
		/* Tell the secondary task to perform the next test. */
		xTimeAtStart = xTaskGetTickCount();
		xTaskNotify( xBlockingTask, ulTestToPerform, eSetValueWithOverwrite );

		/* The secondary task has a higher priority, so will now be in the
		Blocked state to wait for a maximum of xMaxBlockTime.  It expects that
		period to complete with a timeout.  It will then block for
		xMaxBlockTimeAgain, but this time it expects to the block time to abort
		half way through.  Block until it is time to send the abort to the
		secondary task.  xStartMargin is used because this task takes timing
		from the beginning of the test, whereas the blocking task takes timing
		from the entry into the Blocked state - and as the tasks run at
		different priorities, there may be some discrepancy.  Also, temporarily
		raise the priority of the controlling task to that of the blocking
		task to minimise discrepancies. */
		vTaskPrioritySet( NULL, abtBLOCKING_PRIORITY );
		vTaskDelay( xMaxBlockTime + xHalfMaxBlockTime + xStartMargin );
		if( xTaskAbortDelay( xBlockingTask ) != pdPASS )
		{
			xErrorOccurred = pdTRUE;
		}

		/* Reset the priority to the normal controlling priority. */
		vTaskPrioritySet( NULL, abtCONTROLLING_PRIORITY );

		/* Now wait to be notified that the secondary task has completed its
		test. */
		ulTaskNotifyTake( pdTRUE, portMAX_DELAY );

		/* Did the entire test run for the expected time, which is two full
		block times plus the half block time caused by calling
		xTaskAbortDelay()? */
		prvCheckExpectedTimeIsWithinAnAcceptableMargin( xTimeAtStart, ( xMaxBlockTime + xMaxBlockTime + xHalfMaxBlockTime ) );

		/* Move onto the next test. */
		ulTestToPerform++;

		if( ulTestToPerform >= abtMAX_TESTS )
		{
			ulTestToPerform = 0;
		}

		/* To indicate this task is still executing. */
		xControllingCycles++;
	}
}
/*-----------------------------------------------------------*/

static void prvBlockingTask( void *pvParameters )
{
TaskHandle_t xControllingTask;
uint32_t ulNotificationValue;
const uint32_t ulMax = 0xffffffffUL;

	/* Just to remove compiler warnings. */
	( void ) pvParameters;

	xControllingTask = xTaskGetHandle( pcControllingTaskName );
	configASSERT( xControllingTask );

	for( ;; )
	{
		/* Wait to be notified of the test that is to be performed next. */
		xTaskNotifyWait( 0, ulMax, &ulNotificationValue, portMAX_DELAY );

		switch( ulNotificationValue )
		{
			case abtNOTIFY_WAIT_ABORTS:
				prvTestAbortingTaskNotifyWait();
				break;

			case abtNOTIFY_TAKE_ABORTS:
				prvTestAbortingTaskNotifyTake();
				break;

			case abtDELAY_ABORTS:
				prvTestAbortingTaskDelay();
				break;

			case abtDELAY_UNTIL_ABORTS:
				prvTestAbortingTaskDelayUntil();
				break;

			case abtSEMAPHORE_TAKE_ABORTS:
				prvTestAbortingSemaphoreTake();
				break;

			case abtEVENT_GROUP_ABORTS:
				prvTestAbortingEventGroupWait();
				break;

			case abtQUEUE_SEND_ABORTS:
				prvTestAbortingQueueSend();
				break;

			case abtSTREAM_BUFFER_RECEIVE:
				prvTestAbortingStreamBufferReceive();
				break;

			default:
				/* Should not get here. */
				break;
		}

		/* Let the primary task know the test is complete. */
		xTaskNotifyGive( xControllingTask );

		/* To indicate this task is still executing. */
		xBlockingCycles++;
	}
}
/*-----------------------------------------------------------*/

static void prvTestAbortingTaskDelayUntil( void )
{
TickType_t xTimeAtStart, xLastBlockTime;

	/* Note the time before the delay so the length of the delay is known. */
	xTimeAtStart = xTaskGetTickCount();

	/* Take a copy of the time as it is updated in the call to
	vTaskDelayUntil() but its original value is needed to determine the actual
	time spend in the Blocked state. */
	xLastBlockTime = xTimeAtStart;

	/* This first delay should just time out. */
	vTaskDelayUntil( &xLastBlockTime, xMaxBlockTime );
	prvCheckExpectedTimeIsWithinAnAcceptableMargin( xTimeAtStart, xMaxBlockTime );

	/* This second delay should be aborted by the primary task half way
	through.  Again take a copy of the time as it is updated in the call to
	vTaskDelayUntil() buts its original value is needed to determine the amount
	of time actually spent in the Blocked state. */
	xTimeAtStart = xTaskGetTickCount();
	xLastBlockTime = xTimeAtStart;
	vTaskDelayUntil( &xLastBlockTime, xMaxBlockTime );
	prvCheckExpectedTimeIsWithinAnAcceptableMargin( xTimeAtStart, xHalfMaxBlockTime );

	/* As with the other tests, the third block period should not time out. */
	xTimeAtStart = xTaskGetTickCount();
	xLastBlockTime = xTimeAtStart;
	vTaskDelayUntil( &xLastBlockTime, xMaxBlockTime );
	prvCheckExpectedTimeIsWithinAnAcceptableMargin( xTimeAtStart, xMaxBlockTime );
}
/*-----------------------------------------------------------*/

static void prvTestAbortingTaskDelay( void )
{
TickType_t xTimeAtStart;

	/* Note the time before the delay so the length of the delay is known. */
	xTimeAtStart = xTaskGetTickCount();

	/* This first delay should just time out. */
	vTaskDelay( xMaxBlockTime );
	prvCheckExpectedTimeIsWithinAnAcceptableMargin( xTimeAtStart, xMaxBlockTime );

	/* Note the time before the delay so the length of the delay is known. */
	xTimeAtStart = xTaskGetTickCount();

	/* This second delay should be aborted by the primary task half way
	through. */
	vTaskDelay( xMaxBlockTime );
	prvCheckExpectedTimeIsWithinAnAcceptableMargin( xTimeAtStart, xHalfMaxBlockTime );

	/* Note the time before the delay so the length of the delay is known. */
	xTimeAtStart = xTaskGetTickCount();

	/* This third delay should just time out again. */
	vTaskDelay( xMaxBlockTime );
	prvCheckExpectedTimeIsWithinAnAcceptableMargin( xTimeAtStart, xMaxBlockTime );
}
/*-----------------------------------------------------------*/

static void prvTestAbortingTaskNotifyTake( void )
{
TickType_t xTimeAtStart;
uint32_t ulReturn;

	/* Note the time before the delay so the length of the delay is known. */
	xTimeAtStart = xTaskGetTickCount();

	/* This first delay should just time out. */
	ulReturn = ulTaskNotifyTake( pdFALSE, xMaxBlockTime );
	if( ulReturn != 0 )
	{
		xErrorOccurred = pdTRUE;
	}
	prvCheckExpectedTimeIsWithinAnAcceptableMargin( xTimeAtStart, xMaxBlockTime );

	/* Note the time before the delay so the length of the delay is known. */
	xTimeAtStart = xTaskGetTickCount();

	/* This second delay should be aborted by the primary task half way
	through. */
	ulReturn = ulTaskNotifyTake( pdFALSE, xMaxBlockTime );
	if( ulReturn != 0 )
	{
		xErrorOccurred = pdTRUE;
	}
	prvCheckExpectedTimeIsWithinAnAcceptableMargin( xTimeAtStart, xHalfMaxBlockTime );

	/* Note the time before the delay so the length of the delay is known. */
	xTimeAtStart = xTaskGetTickCount();

	/* This third delay should just time out again. */
	ulReturn = ulTaskNotifyTake( pdFALSE, xMaxBlockTime );
	if( ulReturn != 0 )
	{
		xErrorOccurred = pdTRUE;
	}
	prvCheckExpectedTimeIsWithinAnAcceptableMargin( xTimeAtStart, xMaxBlockTime );
}
/*-----------------------------------------------------------*/

static void prvTestAbortingEventGroupWait( void )
{
TickType_t xTimeAtStart;
EventGroupHandle_t xEventGroup;
EventBits_t xBitsToWaitFor = ( EventBits_t ) 0x01, xReturn;

	#if( configSUPPORT_STATIC_ALLOCATION == 1 )
	{
		static StaticEventGroup_t xEventGroupBuffer;

		/* Create the event group.  Statically allocated memory is used so the
		creation cannot fail. */
		xEventGroup = xEventGroupCreateStatic( &xEventGroupBuffer );
	}
	#else
	{
		xEventGroup = xEventGroupCreate();
		configASSERT( xEventGroup );
	}
	#endif

	/* Note the time before the delay so the length of the delay is known. */
	xTimeAtStart = xTaskGetTickCount();

	/* This first delay should just time out. */
	xReturn = xEventGroupWaitBits( xEventGroup, xBitsToWaitFor, pdTRUE, pdTRUE, xMaxBlockTime );
	if( xReturn != 0x00 )
	{
		xErrorOccurred = pdTRUE;
	}
	prvCheckExpectedTimeIsWithinAnAcceptableMargin( xTimeAtStart, xMaxBlockTime );

	/* Note the time before the delay so the length of the delay is known. */
	xTimeAtStart = xTaskGetTickCount();

	/* This second delay should be aborted by the primary task half way
	through. */
	xReturn = xEventGroupWaitBits( xEventGroup, xBitsToWaitFor, pdTRUE, pdTRUE, xMaxBlockTime );
	if( xReturn != 0x00 )
	{
		xErrorOccurred = pdTRUE;
	}
	prvCheckExpectedTimeIsWithinAnAcceptableMargin( xTimeAtStart, xHalfMaxBlockTime );

	/* Note the time before the delay so the length of the delay is known. */
	xTimeAtStart = xTaskGetTickCount();

	/* This third delay should just time out again. */
	xReturn = xEventGroupWaitBits( xEventGroup, xBitsToWaitFor, pdTRUE, pdTRUE, xMaxBlockTime );
	if( xReturn != 0x00 )
	{
		xErrorOccurred = pdTRUE;
	}
	prvCheckExpectedTimeIsWithinAnAcceptableMargin( xTimeAtStart, xMaxBlockTime );

	/* Not really necessary in this case, but for completeness. */
	vEventGroupDelete( xEventGroup );
}
/*-----------------------------------------------------------*/

static void prvTestAbortingStreamBufferReceive( void )
{
TickType_t xTimeAtStart;
StreamBufferHandle_t xStreamBuffer;
EventBits_t xReturn;
const size_t xTriggerLevelBytes = ( size_t ) 1;
uint8_t uxRxData;

	#if( configSUPPORT_STATIC_ALLOCATION == 1 )
	{
		/* Defines the memory that will actually hold the streams within the
		stream buffer. */
		static uint8_t ucStorageBuffer[ sizeof( configMESSAGE_BUFFER_LENGTH_TYPE ) + 1 ];

		/* The variable used to hold the stream buffer structure. */
		StaticStreamBuffer_t xStreamBufferStruct;


		xStreamBuffer = xStreamBufferCreateStatic( sizeof( ucStorageBuffer ),
												   xTriggerLevelBytes,
												   ucStorageBuffer,
												   &xStreamBufferStruct );
	}
	#else
	{
		xStreamBuffer = xStreamBufferCreate( sizeof( uint8_t ), xTriggerLevelBytes );
		configASSERT( xStreamBuffer );
	}
	#endif

	/* Note the time before the delay so the length of the delay is known. */
	xTimeAtStart = xTaskGetTickCount();

	/* This first delay should just time out. */
	xReturn = xStreamBufferReceive( xStreamBuffer, &uxRxData, sizeof( uxRxData ), xMaxBlockTime );
	if( xReturn != 0x00 )
	{
		xErrorOccurred = pdTRUE;
	}
	prvCheckExpectedTimeIsWithinAnAcceptableMargin( xTimeAtStart, xMaxBlockTime );

	/* Note the time before the delay so the length of the delay is known. */
	xTimeAtStart = xTaskGetTickCount();

	/* This second delay should be aborted by the primary task half way
	through xMaxBlockTime. */
	xReturn = xStreamBufferReceive( xStreamBuffer, &uxRxData, sizeof( uxRxData ), xMaxBlockTime );
	if( xReturn != 0x00 )
	{
		xErrorOccurred = pdTRUE;
	}
	prvCheckExpectedTimeIsWithinAnAcceptableMargin( xTimeAtStart, xHalfMaxBlockTime );

	/* Note the time before the delay so the length of the delay is known. */
	xTimeAtStart = xTaskGetTickCount();

	/* This third delay should just time out again. */
	xReturn = xStreamBufferReceive( xStreamBuffer, &uxRxData, sizeof( uxRxData ), xMaxBlockTime );
	if( xReturn != 0x00 )
	{
		xErrorOccurred = pdTRUE;
	}
	prvCheckExpectedTimeIsWithinAnAcceptableMargin( xTimeAtStart, xMaxBlockTime );

	/* Not really necessary in this case, but for completeness. */
	vStreamBufferDelete( xStreamBuffer );
}
/*-----------------------------------------------------------*/

static void prvTestAbortingQueueSend( void )
{
TickType_t xTimeAtStart;
BaseType_t xReturn;
const UBaseType_t xQueueLength = ( UBaseType_t ) 1;
QueueHandle_t xQueue;
uint8_t ucItemToQueue;

	#if( configSUPPORT_STATIC_ALLOCATION == 1 )
	{
		static StaticQueue_t xQueueBuffer;
		static uint8_t ucQueueStorage[ sizeof( uint8_t ) ];

		/* Create the queue.  Statically allocated memory is used so the
		creation cannot fail. */
		xQueue = xQueueCreateStatic( xQueueLength, sizeof( uint8_t ), ucQueueStorage, &xQueueBuffer );
	}
	#else
	{
		xQueue = xQueueCreate( xQueueLength, sizeof( uint8_t ) );
		configASSERT( xQueue );
	}
	#endif

	/* This function tests aborting when in the blocked state waiting to send,
	so the queue must be full.  There is only one space in the queue. */
	xReturn = xQueueSend( xQueue, &ucItemToQueue, xMaxBlockTime );
	if( xReturn != pdPASS )
	{
		xErrorOccurred = pdTRUE;
	}

	/* Note the time before the delay so the length of the delay is known. */
	xTimeAtStart = xTaskGetTickCount();

	/* This first delay should just time out. */
	xReturn = xQueueSend( xQueue, &ucItemToQueue, xMaxBlockTime );
	if( xReturn != pdFALSE )
	{
		xErrorOccurred = pdTRUE;
	}
	prvCheckExpectedTimeIsWithinAnAcceptableMargin( xTimeAtStart, xMaxBlockTime );

	/* Note the time before the delay so the length of the delay is known. */
	xTimeAtStart = xTaskGetTickCount();

	/* This second delay should be aborted by the primary task half way
	through. */
	xReturn = xQueueSend( xQueue, &ucItemToQueue, xMaxBlockTime );
	if( xReturn != pdFALSE )
	{
		xErrorOccurred = pdTRUE;
	}
	prvCheckExpectedTimeIsWithinAnAcceptableMargin( xTimeAtStart, xHalfMaxBlockTime );

	/* Note the time before the delay so the length of the delay is known. */
	xTimeAtStart = xTaskGetTickCount();

	/* This third delay should just time out again. */
	xReturn = xQueueSend( xQueue, &ucItemToQueue, xMaxBlockTime );
	if( xReturn != pdFALSE )
	{
		xErrorOccurred = pdTRUE;
	}
	prvCheckExpectedTimeIsWithinAnAcceptableMargin( xTimeAtStart, xMaxBlockTime );

	/* Not really necessary in this case, but for completeness. */
	vQueueDelete( xQueue );
}
/*-----------------------------------------------------------*/

static void prvTestAbortingSemaphoreTake( void )
{
TickType_t xTimeAtStart;
BaseType_t xReturn;
SemaphoreHandle_t xSemaphore;

	#if( configSUPPORT_STATIC_ALLOCATION == 1 )
	{
		static StaticSemaphore_t xSemaphoreBuffer;

		/* Create the semaphore.  Statically allocated memory is used so the
		creation cannot fail. */
		xSemaphore = xSemaphoreCreateBinaryStatic( &xSemaphoreBuffer );
	}
	#else
	{
		xSemaphore = xSemaphoreCreateBinary();
	}
	#endif

	/* Note the time before the delay so the length of the delay is known. */
	xTimeAtStart = xTaskGetTickCount();

	/* This first delay should just time out. */
	xReturn = xSemaphoreTake( xSemaphore, xMaxBlockTime );
	if( xReturn != pdFALSE )
	{
		xErrorOccurred = pdTRUE;
	}
	prvCheckExpectedTimeIsWithinAnAcceptableMargin( xTimeAtStart, xMaxBlockTime );

	/* Note the time before the delay so the length of the delay is known. */
	xTimeAtStart = xTaskGetTickCount();

	/* This second delay should be aborted by the primary task half way
	through xMaxBlockTime. */
	xReturn = xSemaphoreTake( xSemaphore, portMAX_DELAY );
	if( xReturn != pdFALSE )
	{
		xErrorOccurred = pdTRUE;
	}
	prvCheckExpectedTimeIsWithinAnAcceptableMargin( xTimeAtStart, xHalfMaxBlockTime );

	/* Note the time before the delay so the length of the delay is known. */
	xTimeAtStart = xTaskGetTickCount();

	/* This third delay should just time out again. */
	xReturn = xSemaphoreTake( xSemaphore, xMaxBlockTime );
	if( xReturn != pdFALSE )
	{
		xErrorOccurred = pdTRUE;
	}
	prvCheckExpectedTimeIsWithinAnAcceptableMargin( xTimeAtStart, xMaxBlockTime );

	/* Not really necessary in this case, but for completeness. */
	vSemaphoreDelete( xSemaphore );
}
/*-----------------------------------------------------------*/

static void prvTestAbortingTaskNotifyWait( void )
{
TickType_t xTimeAtStart;
BaseType_t xReturn;

	/* Note the time before the delay so the length of the delay is known. */
	xTimeAtStart = xTaskGetTickCount();

	/* This first delay should just time out. */
	xReturn = xTaskNotifyWait( 0, 0, NULL, xMaxBlockTime );
	if( xReturn != pdFALSE )
	{
		xErrorOccurred = pdTRUE;
	}
	prvCheckExpectedTimeIsWithinAnAcceptableMargin( xTimeAtStart, xMaxBlockTime );

	/* Note the time before the delay so the length of the delay is known. */
	xTimeAtStart = xTaskGetTickCount();

	/* This second delay should be aborted by the primary task half way
	through xMaxBlockTime. */
	xReturn = xTaskNotifyWait( 0, 0, NULL, portMAX_DELAY );
	if( xReturn != pdFALSE )
	{
		xErrorOccurred = pdTRUE;
	}
	prvCheckExpectedTimeIsWithinAnAcceptableMargin( xTimeAtStart, xHalfMaxBlockTime );

	/* Note the time before the delay so the length of the delay is known. */
	xTimeAtStart = xTaskGetTickCount();

	/* This third delay should just time out again. */
	xReturn = xTaskNotifyWait( 0, 0, NULL, xMaxBlockTime );
	if( xReturn != pdFALSE )
	{
		xErrorOccurred = pdTRUE;
	}
	prvCheckExpectedTimeIsWithinAnAcceptableMargin( xTimeAtStart, xMaxBlockTime );
}
/*-----------------------------------------------------------*/

static void prvCheckExpectedTimeIsWithinAnAcceptableMargin( TickType_t xStartTime, TickType_t xExpectedBlockTime )
{
TickType_t xTimeNow, xActualBlockTime;

	xTimeNow = xTaskGetTickCount();
	xActualBlockTime = xTimeNow - xStartTime;

	/* The actual block time should not be less than the expected block time. */
	if( xActualBlockTime < xExpectedBlockTime )
	{
		xErrorOccurred = pdTRUE;
	}

	/* The actual block time can be greater than the expected block time, as it
	depends on the priority of the other tasks, but it should be within an
	acceptable margin. */
	if( xActualBlockTime > ( xExpectedBlockTime + xAllowableMargin ) )
	{
		xErrorOccurred = pdTRUE;
	}
}
/*-----------------------------------------------------------*/

BaseType_t xAreAbortDelayTestTasksStillRunning( void )
{
static BaseType_t xLastControllingCycleCount = 0, xLastBlockingCycleCount = 0;
BaseType_t xReturn = pdPASS;

	/* Have both tasks performed at least one cycle since this function was
	last called? */
	if( xControllingCycles == xLastControllingCycleCount )
	{
		xReturn = pdFAIL;
	}

	if( xBlockingCycles == xLastBlockingCycleCount )
	{
		xReturn = pdFAIL;
	}

	if( xErrorOccurred == pdTRUE )
	{
		xReturn = pdFAIL;
	}

	xLastBlockingCycleCount = xBlockingCycles;
	xLastControllingCycleCount = xControllingCycles;

	return xReturn;
}

#endif /* INCLUDE_xTaskAbortDelay == 1 */
