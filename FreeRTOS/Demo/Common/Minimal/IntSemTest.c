/*
    FreeRTOS V8.1.2 - Copyright (C) 2014 Real Time Engineers Ltd.
    All rights reserved

    VISIT http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

    ***************************************************************************
     *                                                                       *
     *    FreeRTOS provides completely free yet professionally developed,    *
     *    robust, strictly quality controlled, supported, and cross          *
     *    platform software that has become a de facto standard.             *
     *                                                                       *
     *    Help yourself get started quickly and support the FreeRTOS         *
     *    project by purchasing a FreeRTOS tutorial book, reference          *
     *    manual, or both from: http://www.FreeRTOS.org/Documentation        *
     *                                                                       *
     *    Thank you!                                                         *
     *                                                                       *
    ***************************************************************************

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation >>!AND MODIFIED BY!<< the FreeRTOS exception.

    >>!   NOTE: The modification to the GPL is included to allow you to     !<<
    >>!   distribute a combined work that includes FreeRTOS without being   !<<
    >>!   obliged to provide the source code for proprietary components     !<<
    >>!   outside of the FreeRTOS kernel.                                   !<<

    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT ANY
    WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
    FOR A PARTICULAR PURPOSE.  Full license text is available from the following
    link: http://www.freertos.org/a00114.html

    1 tab == 4 spaces!

    ***************************************************************************
     *                                                                       *
     *    Having a problem?  Start by reading the FAQ "My application does   *
     *    not run, what could be wrong?"                                     *
     *                                                                       *
     *    http://www.FreeRTOS.org/FAQHelp.html                               *
     *                                                                       *
    ***************************************************************************

    http://www.FreeRTOS.org - Documentation, books, training, latest versions,
    license and Real Time Engineers Ltd. contact details.

    http://www.FreeRTOS.org/plus - A selection of FreeRTOS ecosystem products,
    including FreeRTOS+Trace - an indispensable productivity tool, a DOS
    compatible FAT file system, and our tiny thread aware UDP/IP stack.

    http://www.OpenRTOS.com - Real Time Engineers ltd license FreeRTOS to High
    Integrity Systems to sell under the OpenRTOS brand.  Low cost OpenRTOS
    licenses offer ticketed support, indemnification and middleware.

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

/*-----------------------------------------------------------*/

/* Flag that will be latched to pdTRUE should any unexpected behaviour be
detected in any of the tasks. */
static volatile BaseType_t xErrorDetected = pdFALSE;

/* Counters that are incremented on each cycle of a test.  This is used to
detect a stalled task - a test that is no longer running. */
static volatile uint32_t ulMasterLoops = 0;

/* Handles of the test tasks that must be accessed from other test tasks. */
static TaskHandle_t xSlaveHandle;

/* A mutex which is given from an interrupt - although generally mutexes should
not be used given in interrupts (and definitely never taken in an interrupt)
there are some circumstances when it may be desirable. */
static SemaphoreHandle_t xISRMutex = NULL;

/* A mutex which is shared between the master and slave tasks - the master
does both sharing of this mutex with the slave and receiving a mutex from the
interrupt. */
static SemaphoreHandle_t xMasterSlaveMutex = NULL;

/* Flag that allows the master task to control when the interrupt gives or does
not give the mutex.  There is no mutual exclusion on this variable, but this is
only test code and it should be fine in the 32=bit test environment. */
static BaseType_t xOkToGiveMutex = pdFALSE;

/*-----------------------------------------------------------*/

void vStartInterruptSemaphoreTasks( void )
{
	/* Create the mutex that is given from an interrupt. */
	xISRMutex = xSemaphoreCreateMutex();
	configASSERT( xISRMutex );

	/* Create the mutex that is shared between the master and slave tasks (the
	master receives a mutex from an interrupt and shares a mutex with the
	slave. */
	xMasterSlaveMutex = xSemaphoreCreateMutex();
	configASSERT( xMasterSlaveMutex );

	/* Create the tasks that share mutexes between then and with interrupts. */
	xTaskCreate( vInterruptMutexSlaveTask, "IntMuS", configMINIMAL_STACK_SIZE, NULL, intsemSLAVE_PRIORITY, &xSlaveHandle );
	xTaskCreate( vInterruptMutexMasterTask, "IntMuM", configMINIMAL_STACK_SIZE, NULL, intsemMASTER_PRIORITY, NULL );
}
/*-----------------------------------------------------------*/

static void vInterruptMutexMasterTask( void *pvParameters )
{
const TickType_t xInterruptGivePeriod = pdMS_TO_TICKS( intsemINTERRUPT_MUTEX_GIVE_PERIOD_MS );

	/* Just to avoid compiler warnings. */
	( void ) pvParameters;

	for( ;; )
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

		/* Ensure not to starve out other tests. */
		ulMasterLoops++;
		vTaskDelay( intsemINTERRUPT_MUTEX_GIVE_PERIOD_MS );


		/* Repeat exactly up to the point where the mutexes are given back.
		This time the shared mutex is given back first. */
		if( xSemaphoreTake( xMasterSlaveMutex, intsemNO_BLOCK ) != pdPASS )
		{
			xErrorDetected = pdTRUE;
		}

		vTaskResume( xSlaveHandle );

		#if( INCLUDE_eTaskGetState == 1 )
		{
			configASSERT( eTaskGetState( xSlaveHandle ) == eBlocked );
		}
		#endif /* INCLUDE_eTaskGetState */

		if( uxTaskPriorityGet( NULL ) != intsemSLAVE_PRIORITY )
		{
			xErrorDetected = pdTRUE;
		}

		xOkToGiveMutex = pdTRUE;
		if( xSemaphoreTake( xISRMutex, ( xInterruptGivePeriod * 2 ) ) != pdPASS )
		{
			xErrorDetected = pdTRUE;
		}
		xOkToGiveMutex = pdFALSE;

		if( uxTaskPriorityGet( NULL ) != intsemSLAVE_PRIORITY )
		{
			xErrorDetected = pdTRUE;
		}

		/* This is where the differences start as this time the shared mutex is
		given back first.  This time to the higher priority task should run
		before this task gets to the point of releasing the interrupt mutex - so
		this task should have disinherited the priority and the higher priority
		task should be in the suspended state again. */
		if( xSemaphoreGive( xMasterSlaveMutex ) != pdPASS )
		{
			xErrorDetected = pdTRUE;
		}

		/* Give back the interrupt semaphore too, so the mutex held count goes
		back to 0.  The mutex will then have to be reset so the ISR can give it
		in the next cycle. */
		xSemaphoreGive( xISRMutex );
		xQueueReset( ( QueueHandle_t ) xISRMutex );

		/* Ensure not to starve out other tests. */
		ulMasterLoops++;
		vTaskDelay( intsemINTERRUPT_MUTEX_GIVE_PERIOD_MS );
	}
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

void vInterruptSemaphorePeriodicTest( void )
{
static TickType_t xLastGiveTime = 0;
TickType_t xTimeNow;

	/* No mutual exclusion on xOkToGiveMutex, but this is only test code (and
	only executed on a 32-bit architecture) so ignore that in this case. */
	xTimeNow = xTaskGetTickCountFromISR();
	if( ( xTimeNow - xLastGiveTime ) >= pdMS_TO_TICKS( intsemINTERRUPT_MUTEX_GIVE_PERIOD_MS ) )
	{
		configASSERT( xISRMutex );
		if( xOkToGiveMutex != pdFALSE )
		{
			xSemaphoreGiveFromISR( xISRMutex, NULL );

			/* Second give attempt should fail. */
			configASSERT( xSemaphoreGiveFromISR( xISRMutex, NULL ) == pdFAIL );
		}
		xLastGiveTime = xTimeNow;
	}
}
/*-----------------------------------------------------------*/

/* This is called to check that all the created tasks are still running. */
BaseType_t xAreInterruptSemaphoreTasksStillRunning( void )
{
static uint32_t ulLastMasterLoopCounter = 0;

	/* If the demo tasks are running then it is expected that the loop counters
	will have changed since this function was last called. */
	if( ulLastMasterLoopCounter == ulMasterLoops )
	{
		xErrorDetected = pdTRUE;
	}

	ulLastMasterLoopCounter = ulMasterLoops;

	/* Errors detected in the task itself will have latched xErrorDetected
	to true. */

	return ( BaseType_t ) !xErrorDetected;
}


