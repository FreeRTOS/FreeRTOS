/*
    FreeRTOS V6.0.3 - Copyright (C) 2010 Real Time Engineers Ltd.

    ***************************************************************************
    *                                                                         *
    * If you are:                                                             *
    *                                                                         *
    *    + New to FreeRTOS,                                                   *
    *    + Wanting to learn FreeRTOS or multitasking in general quickly       *
    *    + Looking for basic training,                                        *
    *    + Wanting to improve your FreeRTOS skills and productivity           *
    *                                                                         *
    * then take a look at the FreeRTOS eBook                                  *
    *                                                                         *
    *        "Using the FreeRTOS Real Time Kernel - a Practical Guide"        *
    *                  http://www.FreeRTOS.org/Documentation                  *
    *                                                                         *
    * A pdf reference manual is also available.  Both are usually delivered   *
    * to your inbox within 20 minutes to two hours when purchased between 8am *
    * and 8pm GMT (although please allow up to 24 hours in case of            *
    * exceptional circumstances).  Thank you for your support!                *
    *                                                                         *
    ***************************************************************************

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation AND MODIFIED BY the FreeRTOS exception.
    ***NOTE*** The exception to the GPL is included to allow you to distribute
    a combined work that includes FreeRTOS without being obliged to provide the
    source code for proprietary components outside of the FreeRTOS kernel.
    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT
    ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
    FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
    more details. You should have received a copy of the GNU General Public 
    License and the FreeRTOS license exception along with FreeRTOS; if not it 
    can be viewed here: http://www.freertos.org/a00114.html and also obtained 
    by writing to Richard Barry, contact details for whom are available on the
    FreeRTOS WEB site.

    1 tab == 4 spaces!

    http://www.FreeRTOS.org - Documentation, latest information, license and
    contact details.

    http://www.SafeRTOS.com - A version that is certified for use in safety
    critical systems.

    http://www.OpenRTOS.com - Commercial support, development, porting,
    licensing and training services.
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
static volatile portBASE_TYPE xErrorDetected = pdFALSE;

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
static void prvIncrementSemaphoreCount( xSemaphoreHandle xSemaphore, unsigned portBASE_TYPE *puxLoopCounter );

/*
 * Utility function to decrement the semaphore count value up from 
 * countMAX_COUNT_VALUE to zero.
 */
static void prvDecrementSemaphoreCount( xSemaphoreHandle xSemaphore, unsigned portBASE_TYPE *puxLoopCounter );

/*-----------------------------------------------------------*/

/* The structure that is passed into the task as the task parameter. */
typedef struct COUNT_SEM_STRUCT
{
	/* The semaphore to be used for the demo. */
	xSemaphoreHandle xSemaphore;

	/* Set to countSTART_AT_MAX_COUNT if the semaphore should be created with
	its count value set to its max count value, or countSTART_AT_ZERO if it
	should have been created with its count value set to 0. */
	unsigned portBASE_TYPE uxExpectedStartCount;	

	/* Incremented on each cycle of the demo task.  Used to detect a stalled
	task. */
	unsigned portBASE_TYPE uxLoopCounter;			
} xCountSemStruct;

/* Two structures are defined, one is passed to each test task. */
static volatile xCountSemStruct xParameters[ countNUM_TEST_TASKS ];

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

	/* vQueueAddToRegistry() adds the semaphore to the registry, if one is
	in use.  The registry is provided as a means for kernel aware 
	debuggers to locate semaphores and has no purpose if a kernel aware debugger
	is not being used.  The call to vQueueAddToRegistry() will be removed
	by the pre-processor if configQUEUE_REGISTRY_SIZE is not defined or is 
	defined to be less than 1. */
	vQueueAddToRegistry( ( xQueueHandle ) xParameters[ 0 ].xSemaphore, ( signed portCHAR * ) "Counting_Sem_1" );
	vQueueAddToRegistry( ( xQueueHandle ) xParameters[ 1 ].xSemaphore, ( signed portCHAR * ) "Counting_Sem_2" );


	/* Were the semaphores created? */
	if( ( xParameters[ 0 ].xSemaphore != NULL ) || ( xParameters[ 1 ].xSemaphore != NULL ) )
	{
		/* Create the demo tasks, passing in the semaphore to use as the parameter. */
		xTaskCreate( prvCountingSemaphoreTask, ( signed portCHAR * ) "CNT1", configMINIMAL_STACK_SIZE, ( void * ) &( xParameters[ 0 ] ), tskIDLE_PRIORITY, NULL );
		xTaskCreate( prvCountingSemaphoreTask, ( signed portCHAR * ) "CNT2", configMINIMAL_STACK_SIZE, ( void * ) &( xParameters[ 1 ] ), tskIDLE_PRIORITY, NULL );		
	}
}
/*-----------------------------------------------------------*/

static void prvDecrementSemaphoreCount( xSemaphoreHandle xSemaphore, unsigned portBASE_TYPE *puxLoopCounter )
{
unsigned portBASE_TYPE ux;

	/* If the semaphore count is at its maximum then we should not be able to
	'give' the semaphore. */
	if( xSemaphoreGive( xSemaphore ) == pdPASS )
	{
		xErrorDetected = pdTRUE;
	}

	/* We should be able to 'take' the semaphore countMAX_COUNT_VALUE times. */
	for( ux = 0; ux < countMAX_COUNT_VALUE; ux++ )
	{
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
	if( xSemaphoreTake( xSemaphore, countDONT_BLOCK ) == pdPASS )
	{
		xErrorDetected = pdTRUE;
	}
}
/*-----------------------------------------------------------*/

static void prvIncrementSemaphoreCount( xSemaphoreHandle xSemaphore, unsigned portBASE_TYPE *puxLoopCounter )
{
unsigned portBASE_TYPE ux;

	/* If the semaphore count is zero then we should not be able to	'take' 
	the semaphore. */
	if( xSemaphoreTake( xSemaphore, countDONT_BLOCK ) == pdPASS )
	{
		xErrorDetected = pdTRUE;
	}

	/* We should be able to 'give' the semaphore countMAX_COUNT_VALUE times. */
	for( ux = 0; ux < countMAX_COUNT_VALUE; ux++ )
	{
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
	void vPrintDisplayMessage( const portCHAR * const * ppcMessageToSend );
	
		const portCHAR * const pcTaskStartMsg = "Counting semaphore demo started.\r\n";

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

portBASE_TYPE xAreCountingSemaphoreTasksStillRunning( void )
{
static unsigned portBASE_TYPE uxLastCount0 = 0, uxLastCount1 = 0;
portBASE_TYPE xReturn = pdPASS;

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


