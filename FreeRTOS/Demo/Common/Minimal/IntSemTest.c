/*
    FreeRTOS V9.0.1 - Copyright (C) 2017 Real Time Engineers Ltd.
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
 * Demonstrates and tests mutexes being used from an interrupt.
 */


#include <stdlib.h>

/* Scheduler include files. */
#include "FreeRTOS.h"
#include "task.h"
#include "semphr.h"

/* Demo program include files. */
#include "IntSemTest.h"

/*-----------------------------------------------------------*/

/* The priorities of the test tasks. */
#define intsemMASTER_PRIORITY		( tskIDLE_PRIORITY )
#define intsemSLAVE_PRIORITY		( tskIDLE_PRIORITY + 1 )

/* The rate at which the tick hook will give the mutex. */
#define intsemINTERRUPT_MUTEX_GIVE_PERIOD_MS ( 100 )

/* A block time of 0 means 'don't block'. */
#define intsemNO_BLOCK				0

/* The maximum count value for the counting semaphore given from an
interrupt. */
#define intsemMAX_COUNT				3

/*-----------------------------------------------------------*/

/*
 * The master is a task that receives a mutex that is given from an interrupt -
 * although generally mutexes should not be used given in interrupts (and
 * definitely never taken in an interrupt) there are some circumstances when it
 * may be desirable.
 *
 * The slave task is just used by the master task to force priority inheritance
 * on a mutex that is shared between the master and the slave - which is a
 * separate mutex to that given by the interrupt.
 */
static void vInterruptMutexSlaveTask( void *pvParameters );
static void vInterruptMutexMasterTask( void *pvParameters );

/*
 * A test whereby the master takes the shared and interrupt mutexes in that
 * order, then gives them back in the same order, ensuring the priority
 * inheritance is behaving as expected at each step.
 */
static void prvTakeAndGiveInTheSameOrder( void );

/*
 * A test whereby the master takes the shared and interrupt mutexes in that
 * order, then gives them back in the opposite order to which they were taken,
 * ensuring the priority inheritance is behaving as expected at each step.
 */
static void prvTakeAndGiveInTheOppositeOrder( void );

/*
 * A simple task that interacts with an interrupt using a counting semaphore,
 * primarily for code coverage purposes.
 */
static void vInterruptCountingSemaphoreTask( void *pvParameters );

/*-----------------------------------------------------------*/

/* Flag that will be latched to pdTRUE should any unexpected behaviour be
detected in any of the tasks. */
static volatile BaseType_t xErrorDetected = pdFALSE;

/* Counters that are incremented on each cycle of a test.  This is used to
detect a stalled task - a test that is no longer running. */
static volatile uint32_t ulMasterLoops = 0, ulCountingSemaphoreLoops = 0;

/* Handles of the test tasks that must be accessed from other test tasks. */
static TaskHandle_t xSlaveHandle;

/* A mutex which is given from an interrupt - although generally mutexes should
not be used given in interrupts (and definitely never taken in an interrupt)
there are some circumstances when it may be desirable. */
static SemaphoreHandle_t xISRMutex = NULL;

/* A counting semaphore which is given from an interrupt. */
static SemaphoreHandle_t xISRCountingSemaphore = NULL;

/* A mutex which is shared between the master and slave tasks - the master
does both sharing of this mutex with the slave and receiving a mutex from the
interrupt. */
static SemaphoreHandle_t xMasterSlaveMutex = NULL;

/* Flag that allows the master task to control when the interrupt gives or does
not give the mutex.  There is no mutual exclusion on this variable, but this is
only test code and it should be fine in the 32=bit test environment. */
static BaseType_t xOkToGiveMutex = pdFALSE, xOkToGiveCountingSemaphore = pdFALSE;

/* Used to coordinate timing between tasks and the interrupt. */
const TickType_t xInterruptGivePeriod = pdMS_TO_TICKS( intsemINTERRUPT_MUTEX_GIVE_PERIOD_MS );

/*-----------------------------------------------------------*/

void vStartInterruptSemaphoreTasks( void )
{
	/* Create the semaphores that are given from an interrupt. */
	xISRMutex = xSemaphoreCreateMutex();
	configASSERT( xISRMutex );
	xISRCountingSemaphore = xSemaphoreCreateCounting( intsemMAX_COUNT, 0 );
	configASSERT( xISRCountingSemaphore );

	/* Create the mutex that is shared between the master and slave tasks (the
	master receives a mutex from an interrupt and shares a mutex with the
	slave. */
	xMasterSlaveMutex = xSemaphoreCreateMutex();
	configASSERT( xMasterSlaveMutex );

	/* Create the tasks that share mutexes between then and with interrupts. */
	xTaskCreate( vInterruptMutexSlaveTask, "IntMuS", configMINIMAL_STACK_SIZE, NULL, intsemSLAVE_PRIORITY, &xSlaveHandle );
	xTaskCreate( vInterruptMutexMasterTask, "IntMuM", configMINIMAL_STACK_SIZE, NULL, intsemMASTER_PRIORITY, NULL );

	/* Create the task that blocks on the counting semaphore. */
	xTaskCreate( vInterruptCountingSemaphoreTask, "IntCnt", configMINIMAL_STACK_SIZE, NULL, tskIDLE_PRIORITY, NULL );
}
/*-----------------------------------------------------------*/

static void vInterruptMutexMasterTask( void *pvParameters )
{
	/* Just to avoid compiler warnings. */
	( void ) pvParameters;

	for( ;; )
	{
		prvTakeAndGiveInTheSameOrder();

		/* Ensure not to starve out other tests. */
		ulMasterLoops++;
		vTaskDelay( intsemINTERRUPT_MUTEX_GIVE_PERIOD_MS );

		prvTakeAndGiveInTheOppositeOrder();

		/* Ensure not to starve out other tests. */
		ulMasterLoops++;
		vTaskDelay( intsemINTERRUPT_MUTEX_GIVE_PERIOD_MS );
	}
}
/*-----------------------------------------------------------*/

static void prvTakeAndGiveInTheSameOrder( void )
{
	/* Ensure the slave is suspended, and that this task is running at the
	lower priority as expected as the start conditions. */
	#if( INCLUDE_eTaskGetState == 1 )
	{
		configASSERT( eTaskGetState( xSlaveHandle ) == eSuspended );
	}
	#endif /* INCLUDE_eTaskGetState */

	if( uxTaskPriorityGet( NULL ) != intsemMASTER_PRIORITY )
	{
		xErrorDetected = pdTRUE;
	}

	/* Take the semaphore that is shared with the slave. */
	if( xSemaphoreTake( xMasterSlaveMutex, intsemNO_BLOCK ) != pdPASS )
	{
		xErrorDetected = pdTRUE;
	}

	/* This task now has the mutex.  Unsuspend the slave so it too
	attempts to take the mutex. */
	vTaskResume( xSlaveHandle );

	/* The slave has the higher priority so should now have executed and
	blocked on the semaphore. */
	#if( INCLUDE_eTaskGetState == 1 )
	{
		configASSERT( eTaskGetState( xSlaveHandle ) == eBlocked );
	}
	#endif /* INCLUDE_eTaskGetState */

	/* This task should now have inherited the priority of the slave
	task. */
	if( uxTaskPriorityGet( NULL ) != intsemSLAVE_PRIORITY )
	{
		xErrorDetected = pdTRUE;
	}

	/* Now wait a little longer than the time between ISR gives to also
	obtain the ISR mutex. */
	xOkToGiveMutex = pdTRUE;
	if( xSemaphoreTake( xISRMutex, ( xInterruptGivePeriod * 2 ) ) != pdPASS )
	{
		xErrorDetected = pdTRUE;
	}
	xOkToGiveMutex = pdFALSE;

	/* Attempting to take again immediately should fail as the mutex is
	already held. */
	if( xSemaphoreTake( xISRMutex, intsemNO_BLOCK ) != pdFAIL )
	{
		xErrorDetected = pdTRUE;
	}

	/* Should still be at the priority of the slave task. */
	if( uxTaskPriorityGet( NULL ) != intsemSLAVE_PRIORITY )
	{
		xErrorDetected = pdTRUE;
	}

	/* Give back the ISR semaphore to ensure the priority is not
	disinherited as the shared mutex (which the higher priority task is
	attempting to obtain) is still held. */
	if( xSemaphoreGive( xISRMutex ) != pdPASS )
	{
		xErrorDetected = pdTRUE;
	}

	if( uxTaskPriorityGet( NULL ) != intsemSLAVE_PRIORITY )
	{
		xErrorDetected = pdTRUE;
	}

	/* Finally give back the shared mutex.  This time the higher priority
	task should run before this task runs again - so this task should have
	disinherited the priority and the higher priority task should be in the
	suspended state again. */
	if( xSemaphoreGive( xMasterSlaveMutex ) != pdPASS )
	{
		xErrorDetected = pdTRUE;
	}

	if( uxTaskPriorityGet( NULL ) != intsemMASTER_PRIORITY )
	{
		xErrorDetected = pdTRUE;
	}

	#if( INCLUDE_eTaskGetState == 1 )
	{
		configASSERT( eTaskGetState( xSlaveHandle ) == eSuspended );
	}
	#endif /* INCLUDE_eTaskGetState */

	/* Reset the mutex ready for the next round. */
	xQueueReset( xISRMutex );
}
/*-----------------------------------------------------------*/

static void prvTakeAndGiveInTheOppositeOrder( void )
{
	/* Ensure the slave is suspended, and that this task is running at the
	lower priority as expected as the start conditions. */
	#if( INCLUDE_eTaskGetState == 1 )
	{
		configASSERT( eTaskGetState( xSlaveHandle ) == eSuspended );
	}
	#endif /* INCLUDE_eTaskGetState */

	if( uxTaskPriorityGet( NULL ) != intsemMASTER_PRIORITY )
	{
		xErrorDetected = pdTRUE;
	}

	/* Take the semaphore that is shared with the slave. */
	if( xSemaphoreTake( xMasterSlaveMutex, intsemNO_BLOCK ) != pdPASS )
	{
		xErrorDetected = pdTRUE;
	}

	/* This task now has the mutex.  Unsuspend the slave so it too
	attempts to take the mutex. */
	vTaskResume( xSlaveHandle );

	/* The slave has the higher priority so should now have executed and
	blocked on the semaphore. */
	#if( INCLUDE_eTaskGetState == 1 )
	{
		configASSERT( eTaskGetState( xSlaveHandle ) == eBlocked );
	}
	#endif /* INCLUDE_eTaskGetState */

	/* This task should now have inherited the priority of the slave
	task. */
	if( uxTaskPriorityGet( NULL ) != intsemSLAVE_PRIORITY )
	{
		xErrorDetected = pdTRUE;
	}

	/* Now wait a little longer than the time between ISR gives to also
	obtain the ISR mutex. */
	xOkToGiveMutex = pdTRUE;
	if( xSemaphoreTake( xISRMutex, ( xInterruptGivePeriod * 2 ) ) != pdPASS )
	{
		xErrorDetected = pdTRUE;
	}
	xOkToGiveMutex = pdFALSE;

	/* Attempting to take again immediately should fail as the mutex is
	already held. */
	if( xSemaphoreTake( xISRMutex, intsemNO_BLOCK ) != pdFAIL )
	{
		xErrorDetected = pdTRUE;
	}

	/* Should still be at the priority of the slave task. */
	if( uxTaskPriorityGet( NULL ) != intsemSLAVE_PRIORITY )
	{
		xErrorDetected = pdTRUE;
	}

	/* Give back the shared semaphore to ensure the priority is not disinherited
	as the ISR mutex is still held.  The higher priority slave task should run
	before this task runs again. */
	if( xSemaphoreGive( xMasterSlaveMutex ) != pdPASS )
	{
		xErrorDetected = pdTRUE;
	}

	/* Should still be at the priority of the slave task as this task still
	holds one semaphore (this is a simplification in the priority inheritance
	mechanism. */
	if( uxTaskPriorityGet( NULL ) != intsemSLAVE_PRIORITY )
	{
		xErrorDetected = pdTRUE;
	}

	/* Give back the ISR semaphore, which should result in the priority being
	disinherited as it was the last mutex held. */
	if( xSemaphoreGive( xISRMutex ) != pdPASS )
	{
		xErrorDetected = pdTRUE;
	}

	if( uxTaskPriorityGet( NULL ) != intsemMASTER_PRIORITY )
	{
		xErrorDetected = pdTRUE;
	}

	/* Reset the mutex ready for the next round. */
	xQueueReset( xISRMutex );
}
/*-----------------------------------------------------------*/

static void vInterruptMutexSlaveTask( void *pvParameters )
{
	/* Just to avoid compiler warnings. */
	( void ) pvParameters;

	for( ;; )
	{
		/* This task starts by suspending itself so when it executes can be
		controlled by the master task. */
		vTaskSuspend( NULL );

		/* This task will execute when the master task already holds the mutex.
		Attempting to take the mutex will place this task in the Blocked
		state. */
		if( xSemaphoreTake( xMasterSlaveMutex, portMAX_DELAY ) != pdPASS )
		{
			xErrorDetected = pdTRUE;
		}

		if( xSemaphoreGive( xMasterSlaveMutex ) != pdPASS )
		{
			xErrorDetected = pdTRUE;
		}
	}
}
/*-----------------------------------------------------------*/

static void vInterruptCountingSemaphoreTask( void *pvParameters )
{
BaseType_t xCount;
const TickType_t xDelay = pdMS_TO_TICKS( intsemINTERRUPT_MUTEX_GIVE_PERIOD_MS ) * ( intsemMAX_COUNT + 1 );

	( void ) pvParameters;

	for( ;; )
	{
		/* Expect to start with the counting semaphore empty. */
		if( uxQueueMessagesWaiting( ( QueueHandle_t ) xISRCountingSemaphore ) != 0 )
		{
			xErrorDetected = pdTRUE;
		}

		/* Wait until it is expected that the interrupt will have filled the
		counting semaphore. */
		xOkToGiveCountingSemaphore = pdTRUE;
		vTaskDelay( xDelay );
		xOkToGiveCountingSemaphore = pdFALSE;

		/* Now it is expected that the counting semaphore is full. */
		if( uxQueueMessagesWaiting( ( QueueHandle_t ) xISRCountingSemaphore ) != intsemMAX_COUNT )
		{
			xErrorDetected = pdTRUE;
		}

		if( uxQueueSpacesAvailable( ( QueueHandle_t ) xISRCountingSemaphore ) != 0 )
		{
			xErrorDetected = pdTRUE;
		}

		ulCountingSemaphoreLoops++;

		/* Expect to be able to take the counting semaphore intsemMAX_COUNT
		times.  A block time of 0 is used as the semaphore should already be
		there. */
		xCount = 0;
		while( xSemaphoreTake( xISRCountingSemaphore, 0 ) == pdPASS )
		{
			xCount++;
		}

		if( xCount != intsemMAX_COUNT )
		{
			xErrorDetected = pdTRUE;
		}

		/* Now raise the priority of this task so it runs immediately that the
		semaphore is given from the interrupt. */
		vTaskPrioritySet( NULL, configMAX_PRIORITIES - 1 );

		/* Block to wait for the semaphore to be given from the interrupt. */
		xOkToGiveCountingSemaphore = pdTRUE;
		xSemaphoreTake( xISRCountingSemaphore, portMAX_DELAY );
		xSemaphoreTake( xISRCountingSemaphore, portMAX_DELAY );
		xOkToGiveCountingSemaphore = pdFALSE;

		/* Reset the priority so as not to disturbe other tests too much. */
		vTaskPrioritySet( NULL, tskIDLE_PRIORITY );

		ulCountingSemaphoreLoops++;
	}
}
/*-----------------------------------------------------------*/

void vInterruptSemaphorePeriodicTest( void )
{
static TickType_t xLastGiveTime = 0;
BaseType_t xHigherPriorityTaskWoken = pdFALSE;
TickType_t xTimeNow;

	/* No mutual exclusion on xOkToGiveMutex, but this is only test code (and
	only executed on a 32-bit architecture) so ignore that in this case. */
	xTimeNow = xTaskGetTickCountFromISR();
	if( ( ( TickType_t ) ( xTimeNow - xLastGiveTime ) ) >= pdMS_TO_TICKS( intsemINTERRUPT_MUTEX_GIVE_PERIOD_MS ) )
	{
		configASSERT( xISRMutex );
		if( xOkToGiveMutex != pdFALSE )
		{
			/* Null is used as the second parameter in this give, and non-NULL
			in the other gives for code coverage reasons. */
			xSemaphoreGiveFromISR( xISRMutex, NULL );

			/* Second give attempt should fail. */
			configASSERT( xSemaphoreGiveFromISR( xISRMutex, &xHigherPriorityTaskWoken ) == pdFAIL );
		}

		if( xOkToGiveCountingSemaphore != pdFALSE )
		{
			xSemaphoreGiveFromISR( xISRCountingSemaphore, &xHigherPriorityTaskWoken );
		}
		xLastGiveTime = xTimeNow;
	}

	/* Remove compiler warnings about the value being set but not used. */
	( void ) xHigherPriorityTaskWoken;
}
/*-----------------------------------------------------------*/

/* This is called to check that all the created tasks are still running. */
BaseType_t xAreInterruptSemaphoreTasksStillRunning( void )
{
static uint32_t ulLastMasterLoopCounter = 0, ulLastCountingSemaphoreLoops = 0;

	/* If the demo tasks are running then it is expected that the loop counters
	will have changed since this function was last called. */
	if( ulLastMasterLoopCounter == ulMasterLoops )
	{
		xErrorDetected = pdTRUE;
	}

	ulLastMasterLoopCounter = ulMasterLoops;

	if( ulLastCountingSemaphoreLoops == ulCountingSemaphoreLoops )
	{
		xErrorDetected = pdTRUE;
	}

	ulLastCountingSemaphoreLoops = ulCountingSemaphoreLoops++;

	/* Errors detected in the task itself will have latched xErrorDetected
	to true. */

	return ( BaseType_t ) !xErrorDetected;
}


