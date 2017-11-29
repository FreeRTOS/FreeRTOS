/*
 * FreeRTOS Kernel V10.0.0
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
 * copies or substantial portions of the Software. If you wish to use our Amazon
 * FreeRTOS name, please do so in a fair use way that does not cause confusion.
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
 * Simple demonstration of the usage of counting semaphore.
 */

/* Scheduler include files. */
#include "FreeRTOS.h"
#include "task.h"
#include "semphr.h"

/* Demo program include files. */
#include "countsem.h"

/* The maximum count value that the semaphore used for the demo can hold. */
#define countMAX_COUNT_VALUE	( 200 )

/* Constants used to indicate whether or not the semaphore should have been
created with its maximum count value, or its minimum count value.  These
numbers are used to ensure that the pointers passed in as the task parameters
are valid. */
#define countSTART_AT_MAX_COUNT	( 0xaa )
#define countSTART_AT_ZERO		( 0x55 )

/* Two tasks are created for the test.  One uses a semaphore created with its
count value set to the maximum, and one with the count value set to zero. */
#define countNUM_TEST_TASKS		( 2 )
#define countDONT_BLOCK			( 0 )

/*-----------------------------------------------------------*/

/* Flag that will be latched to pdTRUE should any unexpected behaviour be
detected in any of the tasks. */
static volatile BaseType_t xErrorDetected = pdFALSE;

/*-----------------------------------------------------------*/

/*
 * The demo task.  This simply counts the semaphore up to its maximum value,
 * the counts it back down again.  The result of each semaphore 'give' and
 * 'take' is inspected, with an error being flagged if it is found not to be
 * the expected result.
 */
static void prvCountingSemaphoreTask( void *pvParameters );

/*
 * Utility function to increment the semaphore count value up from zero to
 * countMAX_COUNT_VALUE.
 */
static void prvIncrementSemaphoreCount( SemaphoreHandle_t xSemaphore, volatile UBaseType_t *puxLoopCounter );

/*
 * Utility function to decrement the semaphore count value up from
 * countMAX_COUNT_VALUE to zero.
 */
static void prvDecrementSemaphoreCount( SemaphoreHandle_t xSemaphore, volatile UBaseType_t *puxLoopCounter );

/*-----------------------------------------------------------*/

/* The structure that is passed into the task as the task parameter. */
typedef struct COUNT_SEM_STRUCT
{
	/* The semaphore to be used for the demo. */
	SemaphoreHandle_t xSemaphore;

	/* Set to countSTART_AT_MAX_COUNT if the semaphore should be created with
	its count value set to its max count value, or countSTART_AT_ZERO if it
	should have been created with its count value set to 0. */
	UBaseType_t uxExpectedStartCount;

	/* Incremented on each cycle of the demo task.  Used to detect a stalled
	task. */
	volatile UBaseType_t uxLoopCounter;
} xCountSemStruct;

/* Two structures are defined, one is passed to each test task. */
static xCountSemStruct xParameters[ countNUM_TEST_TASKS ];

/*-----------------------------------------------------------*/

void vStartCountingSemaphoreTasks( void )
{
	/* Create the semaphores that we are going to use for the test/demo.  The
	first should be created such that it starts at its maximum count value,
	the second should be created such that it starts with a count value of zero. */
	xParameters[ 0 ].xSemaphore = xSemaphoreCreateCounting( countMAX_COUNT_VALUE, countMAX_COUNT_VALUE );
	xParameters[ 0 ].uxExpectedStartCount = countSTART_AT_MAX_COUNT;
	xParameters[ 0 ].uxLoopCounter = 0;

	xParameters[ 1 ].xSemaphore = xSemaphoreCreateCounting( countMAX_COUNT_VALUE, 0 );
	xParameters[ 1 ].uxExpectedStartCount = 0;
	xParameters[ 1 ].uxLoopCounter = 0;

	/* Were the semaphores created? */
	if( ( xParameters[ 0 ].xSemaphore != NULL ) || ( xParameters[ 1 ].xSemaphore != NULL ) )
	{
		/* vQueueAddToRegistry() adds the semaphore to the registry, if one is
		in use.  The registry is provided as a means for kernel aware
		debuggers to locate semaphores and has no purpose if a kernel aware
		debugger is not being used.  The call to vQueueAddToRegistry() will be
		removed by the pre-processor if configQUEUE_REGISTRY_SIZE is not
		defined or is defined to be less than 1. */
		vQueueAddToRegistry( ( QueueHandle_t ) xParameters[ 0 ].xSemaphore, "Counting_Sem_1" );
		vQueueAddToRegistry( ( QueueHandle_t ) xParameters[ 1 ].xSemaphore, "Counting_Sem_2" );

		/* Create the demo tasks, passing in the semaphore to use as the parameter. */
		xTaskCreate( prvCountingSemaphoreTask, "CNT1", configMINIMAL_STACK_SIZE, ( void * ) &( xParameters[ 0 ] ), tskIDLE_PRIORITY, NULL );
		xTaskCreate( prvCountingSemaphoreTask, "CNT2", configMINIMAL_STACK_SIZE, ( void * ) &( xParameters[ 1 ] ), tskIDLE_PRIORITY, NULL );
	}
}
/*-----------------------------------------------------------*/

static void prvDecrementSemaphoreCount( SemaphoreHandle_t xSemaphore, volatile UBaseType_t *puxLoopCounter )
{
UBaseType_t ux;

	/* If the semaphore count is at its maximum then we should not be able to
	'give' the semaphore. */
	if( xSemaphoreGive( xSemaphore ) == pdPASS )
	{
		xErrorDetected = pdTRUE;
	}

	/* We should be able to 'take' the semaphore countMAX_COUNT_VALUE times. */
	for( ux = 0; ux < countMAX_COUNT_VALUE; ux++ )
	{
		configASSERT( uxSemaphoreGetCount( xSemaphore ) == ( countMAX_COUNT_VALUE - ux ) );

		if( xSemaphoreTake( xSemaphore, countDONT_BLOCK ) != pdPASS )
		{
			/* We expected to be able to take the semaphore. */
			xErrorDetected = pdTRUE;
		}

		( *puxLoopCounter )++;
	}

	#if configUSE_PREEMPTION == 0
		taskYIELD();
	#endif

	/* If the semaphore count is zero then we should not be able to	'take'
	the semaphore. */
	configASSERT( uxSemaphoreGetCount( xSemaphore ) == 0 );
	if( xSemaphoreTake( xSemaphore, countDONT_BLOCK ) == pdPASS )
	{
		xErrorDetected = pdTRUE;
	}
}
/*-----------------------------------------------------------*/

static void prvIncrementSemaphoreCount( SemaphoreHandle_t xSemaphore, volatile UBaseType_t *puxLoopCounter )
{
UBaseType_t ux;

	/* If the semaphore count is zero then we should not be able to	'take'
	the semaphore. */
	if( xSemaphoreTake( xSemaphore, countDONT_BLOCK ) == pdPASS )
	{
		xErrorDetected = pdTRUE;
	}

	/* We should be able to 'give' the semaphore countMAX_COUNT_VALUE times. */
	for( ux = 0; ux < countMAX_COUNT_VALUE; ux++ )
	{
		configASSERT( uxSemaphoreGetCount( xSemaphore ) == ux );

		if( xSemaphoreGive( xSemaphore ) != pdPASS )
		{
			/* We expected to be able to take the semaphore. */
			xErrorDetected = pdTRUE;
		}

		( *puxLoopCounter )++;
	}

	#if configUSE_PREEMPTION == 0
		taskYIELD();
	#endif

	/* If the semaphore count is at its maximum then we should not be able to
	'give' the semaphore. */
	if( xSemaphoreGive( xSemaphore ) == pdPASS )
	{
		xErrorDetected = pdTRUE;
	}
}
/*-----------------------------------------------------------*/

static void prvCountingSemaphoreTask( void *pvParameters )
{
xCountSemStruct *pxParameter;

	#ifdef USE_STDIO
	void vPrintDisplayMessage( const char * const * ppcMessageToSend );

		const char * const pcTaskStartMsg = "Counting semaphore demo started.\r\n";

		/* Queue a message for printing to say the task has started. */
		vPrintDisplayMessage( &pcTaskStartMsg );
	#endif

	/* The semaphore to be used was passed as the parameter. */
	pxParameter = ( xCountSemStruct * ) pvParameters;

	/* Did we expect to find the semaphore already at its max count value, or
	at zero? */
	if( pxParameter->uxExpectedStartCount == countSTART_AT_MAX_COUNT )
	{
		prvDecrementSemaphoreCount( pxParameter->xSemaphore, &( pxParameter->uxLoopCounter ) );
	}

	/* Now we expect the semaphore count to be 0, so this time there is an
	error if we can take the semaphore. */
	if( xSemaphoreTake( pxParameter->xSemaphore, 0 ) == pdPASS )
	{
		xErrorDetected = pdTRUE;
	}

	for( ;; )
	{
		prvIncrementSemaphoreCount( pxParameter->xSemaphore, &( pxParameter->uxLoopCounter ) );
		prvDecrementSemaphoreCount( pxParameter->xSemaphore, &( pxParameter->uxLoopCounter ) );
	}
}
/*-----------------------------------------------------------*/

BaseType_t xAreCountingSemaphoreTasksStillRunning( void )
{
static UBaseType_t uxLastCount0 = 0, uxLastCount1 = 0;
BaseType_t xReturn = pdPASS;

	/* Return fail if any 'give' or 'take' did not result in the expected
	behaviour. */
	if( xErrorDetected != pdFALSE )
	{
		xReturn = pdFAIL;
	}

	/* Return fail if either task is not still incrementing its loop counter. */
	if( uxLastCount0 == xParameters[ 0 ].uxLoopCounter )
	{
		xReturn = pdFAIL;
	}
	else
	{
		uxLastCount0 = xParameters[ 0 ].uxLoopCounter;
	}

	if( uxLastCount1 == xParameters[ 1 ].uxLoopCounter )
	{
		xReturn = pdFAIL;
	}
	else
	{
		uxLastCount1 = xParameters[ 1 ].uxLoopCounter;
	}

	return xReturn;
}


