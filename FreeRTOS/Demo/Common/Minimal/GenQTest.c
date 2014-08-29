/*
    FreeRTOS V8.1.1 - Copyright (C) 2014 Real Time Engineers Ltd.
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
 * Tests the extra queue functionality introduced in FreeRTOS.org V4.5.0 -
 * including xQueueSendToFront(), xQueueSendToBack(), xQueuePeek() and
 * mutex behaviour.
 *
 * See the comments above the prvSendFrontAndBackTest() and
 * prvLowPriorityMutexTask() prototypes below for more information.
 */


#include <stdlib.h>

/* Scheduler include files. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"
#include "semphr.h"

/* Demo program include files. */
#include "GenQTest.h"

#define genqQUEUE_LENGTH		( 5 )
#define genqNO_BLOCK			( 0 )

#define genqMUTEX_LOW_PRIORITY		( tskIDLE_PRIORITY )
#define genqMUTEX_TEST_PRIORITY		( tskIDLE_PRIORITY + 1 )
#define genqMUTEX_MEDIUM_PRIORITY	( tskIDLE_PRIORITY + 2 )
#define genqMUTEX_HIGH_PRIORITY		( tskIDLE_PRIORITY + 3 )

#define genqINTERRUPT_MUTEX_GIVE_PERIOD_MS ( 100 )
/*-----------------------------------------------------------*/

/*
 * Tests the behaviour of the xQueueSendToFront() and xQueueSendToBack()
 * macros by using both to fill a queue, then reading from the queue to
 * check the resultant queue order is as expected.  Queue data is also
 * peeked.
 */
static void prvSendFrontAndBackTest( void *pvParameters );

/*
 * The following three tasks are used to demonstrate the mutex behaviour.
 * Each task is given a different priority to demonstrate the priority
 * inheritance mechanism.
 *
 * The low priority task obtains a mutex.  After this a high priority task
 * attempts to obtain the same mutex, causing its priority to be inherited
 * by the low priority task.  The task with the inherited high priority then
 * resumes a medium priority task to ensure it is not blocked by the medium
 * priority task while it holds the inherited high priority.  Once the mutex
 * is returned the task with the inherited priority returns to its original
 * low priority, and is therefore immediately preempted by first the high
 * priority task and then the medium prioroity task before it can continue.
 */
static void prvLowPriorityMutexTask( void *pvParameters );
static void prvMediumPriorityMutexTask( void *pvParameters );
static void prvHighPriorityMutexTask( void *pvParameters );

/*
 * Exercises the priority inheritance when a task takes two mutexes, returning
 * them in a different order to which they were taken.
 */
static void prvTakeTwoMutexesReturnInDifferentOrder( SemaphoreHandle_t xMutex, SemaphoreHandle_t xLocalMutex );

/*
 * Exercises the priority inheritance when a task takes two mutexes, returning
 * them in the same order in which they were taken.
 */
static void prvTakeTwoMutexesReturnInSameOrder( SemaphoreHandle_t xMutex, SemaphoreHandle_t xLocalMutex );

/*
 * Task that receives an a mutex that is given from an interrupt - although
 * generally mutexes should not be used given in interrupts (and definitely
 * never taken in an interrupt) there are some circumstances when it may be
 * desirable.  NOTE:  This function is not declared static to prevent compiler
 * warnings being generated in demos where the function is declared but not
 * used.
 */
void vInterruptMutexTask( void *pvParameters );

/*-----------------------------------------------------------*/

/* Flag that will be latched to pdTRUE should any unexpected behaviour be
detected in any of the tasks. */
static volatile BaseType_t xErrorDetected = pdFALSE;

/* Counters that are incremented on each cycle of a test.  This is used to
detect a stalled task - a test that is no longer running. */
static volatile uint32_t ulLoopCounter = 0;
static volatile uint32_t ulLoopCounter2 = 0;

/* The variable that is guarded by the mutex in the mutex demo tasks. */
static volatile uint32_t ulGuardedVariable = 0;

/* Handles used in the mutext test to suspend and resume the high and medium
priority mutex test tasks. */
static TaskHandle_t xHighPriorityMutexTask, xMediumPriorityMutexTask;

/* A mutex which is given from an interrupt - although generally mutexes should
not be used given in interrupts (and definitely never taken in an interrupt)
there are some circumstances when it may be desirable. */
static SemaphoreHandle_t xISRMutex = NULL;

/*-----------------------------------------------------------*/

void vStartGenericQueueTasks( UBaseType_t uxPriority )
{
QueueHandle_t xQueue;
SemaphoreHandle_t xMutex;

	xISRMutex = xSemaphoreCreateMutex();
	configASSERT( xISRMutex );

	/* Create the queue that we are going to use for the
	prvSendFrontAndBackTest demo. */
	xQueue = xQueueCreate( genqQUEUE_LENGTH, sizeof( uint32_t ) );

	/* vQueueAddToRegistry() adds the queue to the queue registry, if one is
	in use.  The queue registry is provided as a means for kernel aware
	debuggers to locate queues and has no purpose if a kernel aware debugger
	is not being used.  The call to vQueueAddToRegistry() will be removed
	by the pre-processor if configQUEUE_REGISTRY_SIZE is not defined or is
	defined to be less than 1. */
	vQueueAddToRegistry( xQueue, "Gen_Queue_Test" );

	/* Create the demo task and pass it the queue just created.  We are
	passing the queue handle by value so it does not matter that it is
	declared on the stack here. */
	xTaskCreate( prvSendFrontAndBackTest, "GenQ", configMINIMAL_STACK_SIZE, ( void * ) xQueue, uxPriority, NULL );

	/* Create the mutex used by the prvMutexTest task. */
	xMutex = xSemaphoreCreateMutex();

	/* vQueueAddToRegistry() adds the mutex to the registry, if one is
	in use.  The registry is provided as a means for kernel aware
	debuggers to locate mutexes and has no purpose if a kernel aware debugger
	is not being used.  The call to vQueueAddToRegistry() will be removed
	by the pre-processor if configQUEUE_REGISTRY_SIZE is not defined or is
	defined to be less than 1. */
	vQueueAddToRegistry( ( QueueHandle_t ) xMutex, "Gen_Queue_Mutex" );

	/* Create the mutex demo tasks and pass it the mutex just created.  We are
	passing the mutex handle by value so it does not matter that it is declared
	on the stack here. */
	xTaskCreate( prvLowPriorityMutexTask, "MuLow", configMINIMAL_STACK_SIZE, ( void * ) xMutex, genqMUTEX_LOW_PRIORITY, NULL );
	xTaskCreate( prvMediumPriorityMutexTask, "MuMed", configMINIMAL_STACK_SIZE, NULL, genqMUTEX_MEDIUM_PRIORITY, &xMediumPriorityMutexTask );
	xTaskCreate( prvHighPriorityMutexTask, "MuHigh", configMINIMAL_STACK_SIZE, ( void * ) xMutex, genqMUTEX_HIGH_PRIORITY, &xHighPriorityMutexTask );

	/* Only when the windows simulator is being used - create the task that
	receives a mutex from an interrupt. */
	#ifdef _WINDOWS_
	{
		xTaskCreate( vInterruptMutexTask, "IntMu", configMINIMAL_STACK_SIZE, NULL, genqMUTEX_MEDIUM_PRIORITY, NULL );
	}
	#endif /* __WINDOWS__ */
}
/*-----------------------------------------------------------*/

static void prvSendFrontAndBackTest( void *pvParameters )
{
uint32_t ulData, ulData2;
QueueHandle_t xQueue;

	#ifdef USE_STDIO
	void vPrintDisplayMessage( const char * const * ppcMessageToSend );

		const char * const pcTaskStartMsg = "Queue SendToFront/SendToBack/Peek test started.\r\n";

		/* Queue a message for printing to say the task has started. */
		vPrintDisplayMessage( &pcTaskStartMsg );
	#endif

	xQueue = ( QueueHandle_t ) pvParameters;

	for( ;; )
	{
		/* The queue is empty, so sending an item to the back of the queue
		should have the same efect as sending it to the front of the queue.

		First send to the front and check everything is as expected. */
		xQueueSendToFront( xQueue, ( void * ) &ulLoopCounter, genqNO_BLOCK );

		if( uxQueueMessagesWaiting( xQueue ) != 1 )
		{
			xErrorDetected = pdTRUE;
		}

		if( xQueueReceive( xQueue, ( void * ) &ulData, genqNO_BLOCK ) != pdPASS )
		{
			xErrorDetected = pdTRUE;
		}

		/* The data we sent to the queue should equal the data we just received
		from the queue. */
		if( ulLoopCounter != ulData )
		{
			xErrorDetected = pdTRUE;
		}

		/* Then do the same, sending the data to the back, checking everything
		is as expected. */
		if( uxQueueMessagesWaiting( xQueue ) != 0 )
		{
			xErrorDetected = pdTRUE;
		}

		xQueueSendToBack( xQueue, ( void * ) &ulLoopCounter, genqNO_BLOCK );

		if( uxQueueMessagesWaiting( xQueue ) != 1 )
		{
			xErrorDetected = pdTRUE;
		}

		if( xQueueReceive( xQueue, ( void * ) &ulData, genqNO_BLOCK ) != pdPASS )
		{
			xErrorDetected = pdTRUE;
		}

		if( uxQueueMessagesWaiting( xQueue ) != 0 )
		{
			xErrorDetected = pdTRUE;
		}

		/* The data we sent to the queue should equal the data we just received
		from the queue. */
		if( ulLoopCounter != ulData )
		{
			xErrorDetected = pdTRUE;
		}

		#if configUSE_PREEMPTION == 0
			taskYIELD();
		#endif



		/* Place 2, 3, 4 into the queue, adding items to the back of the queue. */
		for( ulData = 2; ulData < 5; ulData++ )
		{
			xQueueSendToBack( xQueue, ( void * ) &ulData, genqNO_BLOCK );
		}

		/* Now the order in the queue should be 2, 3, 4, with 2 being the first
		thing to be read out.  Now add 1 then 0 to the front of the queue. */
		if( uxQueueMessagesWaiting( xQueue ) != 3 )
		{
			xErrorDetected = pdTRUE;
		}
		ulData = 1;
		xQueueSendToFront( xQueue, ( void * ) &ulData, genqNO_BLOCK );
		ulData = 0;
		xQueueSendToFront( xQueue, ( void * ) &ulData, genqNO_BLOCK );

		/* Now the queue should be full, and when we read the data out we
		should receive 0, 1, 2, 3, 4. */
		if( uxQueueMessagesWaiting( xQueue ) != 5 )
		{
			xErrorDetected = pdTRUE;
		}

		if( xQueueSendToFront( xQueue, ( void * ) &ulData, genqNO_BLOCK ) != errQUEUE_FULL )
		{
			xErrorDetected = pdTRUE;
		}

		if( xQueueSendToBack( xQueue, ( void * ) &ulData, genqNO_BLOCK ) != errQUEUE_FULL )
		{
			xErrorDetected = pdTRUE;
		}

		#if configUSE_PREEMPTION == 0
			taskYIELD();
		#endif

		/* Check the data we read out is in the expected order. */
		for( ulData = 0; ulData < genqQUEUE_LENGTH; ulData++ )
		{
			/* Try peeking the data first. */
			if( xQueuePeek( xQueue, &ulData2, genqNO_BLOCK ) != pdPASS )
			{
				xErrorDetected = pdTRUE;
			}

			if( ulData != ulData2 )
			{
				xErrorDetected = pdTRUE;
			}


			/* Now try receiving the data for real.  The value should be the
			same.  Clobber the value first so we know we really received it. */
			ulData2 = ~ulData2;
			if( xQueueReceive( xQueue, &ulData2, genqNO_BLOCK ) != pdPASS )
			{
				xErrorDetected = pdTRUE;
			}

			if( ulData != ulData2 )
			{
				xErrorDetected = pdTRUE;
			}
		}

		/* The queue should now be empty again. */
		if( uxQueueMessagesWaiting( xQueue ) != 0 )
		{
			xErrorDetected = pdTRUE;
		}

		#if configUSE_PREEMPTION == 0
			taskYIELD();
		#endif


		/* Our queue is empty once more, add 10, 11 to the back. */
		ulData = 10;
		if( xQueueSend( xQueue, &ulData, genqNO_BLOCK ) != pdPASS )
		{
			xErrorDetected = pdTRUE;
		}
		ulData = 11;
		if( xQueueSend( xQueue, &ulData, genqNO_BLOCK ) != pdPASS )
		{
			xErrorDetected = pdTRUE;
		}

		if( uxQueueMessagesWaiting( xQueue ) != 2 )
		{
			xErrorDetected = pdTRUE;
		}

		/* Now we should have 10, 11 in the queue.  Add 7, 8, 9 to the
		front. */
		for( ulData = 9; ulData >= 7; ulData-- )
		{
			if( xQueueSendToFront( xQueue, ( void * ) &ulData, genqNO_BLOCK ) != pdPASS )
			{
				xErrorDetected = pdTRUE;
			}
		}

		/* Now check that the queue is full, and that receiving data provides
		the expected sequence of 7, 8, 9, 10, 11. */
		if( uxQueueMessagesWaiting( xQueue ) != 5 )
		{
			xErrorDetected = pdTRUE;
		}

		if( xQueueSendToFront( xQueue, ( void * ) &ulData, genqNO_BLOCK ) != errQUEUE_FULL )
		{
			xErrorDetected = pdTRUE;
		}

		if( xQueueSendToBack( xQueue, ( void * ) &ulData, genqNO_BLOCK ) != errQUEUE_FULL )
		{
			xErrorDetected = pdTRUE;
		}

		#if configUSE_PREEMPTION == 0
			taskYIELD();
		#endif

		/* Check the data we read out is in the expected order. */
		for( ulData = 7; ulData < ( 7 + genqQUEUE_LENGTH ); ulData++ )
		{
			if( xQueueReceive( xQueue, &ulData2, genqNO_BLOCK ) != pdPASS )
			{
				xErrorDetected = pdTRUE;
			}

			if( ulData != ulData2 )
			{
				xErrorDetected = pdTRUE;
			}
		}

		if( uxQueueMessagesWaiting( xQueue ) != 0 )
		{
			xErrorDetected = pdTRUE;
		}

		ulLoopCounter++;
	}
}
/*-----------------------------------------------------------*/

static void prvTakeTwoMutexesReturnInDifferentOrder( SemaphoreHandle_t xMutex, SemaphoreHandle_t xLocalMutex )
{
	/* Take the mutex.  It should be available now. */
	if( xSemaphoreTake( xMutex, genqNO_BLOCK ) != pdPASS )
	{
		xErrorDetected = pdTRUE;
	}

	/* Set the guarded variable to a known start value. */
	ulGuardedVariable = 0;

	/* This task's priority should be as per that assigned when the task was
	created. */
	if( uxTaskPriorityGet( NULL ) != genqMUTEX_LOW_PRIORITY )
	{
		xErrorDetected = pdTRUE;
	}

	/* Now unsuspend the high priority task.  This will attempt to take the
	mutex, and block when it finds it cannot obtain it. */
	vTaskResume( xHighPriorityMutexTask );

	#if configUSE_PREEMPTION == 0
		taskYIELD();
	#endif

	/* Ensure the task is reporting its priority as blocked and not
	suspended (as it would have done in versions up to V7.5.3). */
	#if( INCLUDE_eTaskGetState == 1 )
	{
		configASSERT( eTaskGetState( xHighPriorityMutexTask ) == eBlocked );
	}
	#endif /* INCLUDE_eTaskGetState */

	/* The priority of the high priority task should now have been inherited
	as by now it will have attempted to get the mutex. */
	if( uxTaskPriorityGet( NULL ) != genqMUTEX_HIGH_PRIORITY )
	{
		xErrorDetected = pdTRUE;
	}

	/* Attempt to set the priority of this task to the test priority -
	between the	idle priority and the medium/high test priorities, but the
	actual priority should remain at the high priority. */
	vTaskPrioritySet( NULL, genqMUTEX_TEST_PRIORITY );
	if( uxTaskPriorityGet( NULL ) != genqMUTEX_HIGH_PRIORITY )
	{
		xErrorDetected = pdTRUE;
	}

	/* Now unsuspend the medium priority task.  This should not run as the
	inherited priority of this task is above that of the medium priority
	task. */
	vTaskResume( xMediumPriorityMutexTask );

	/* If the medium priority task did run then it will have incremented the
	guarded variable. */
	if( ulGuardedVariable != 0 )
	{
		xErrorDetected = pdTRUE;
	}

	/* Take the local mutex too, so two mutexes are now held. */
	if( xSemaphoreTake( xLocalMutex, genqNO_BLOCK ) != pdPASS )
	{
		xErrorDetected = pdTRUE;
	}

	/* When the semaphore is given back the priority of this task should not
	yet be disinherited because the local mutex is still held.  This is a
	simplification to allow FreeRTOS to be integrated with middleware that
	attempts to hold multiple mutexes without bloating the code with complex
	algorithms.  It is possible that the high priority mutex task will
	execute as it shares a priority with this task. */
	if( xSemaphoreGive( xMutex ) != pdPASS )
	{
		xErrorDetected = pdTRUE;
	}

	#if configUSE_PREEMPTION == 0
		taskYIELD();
	#endif

	/* The guarded variable is only incremented by the medium priority task,
	which still should not have executed as this task should remain at the
	higher priority, ensure this is the case. */
	if( ulGuardedVariable != 0 )
	{
		xErrorDetected = pdTRUE;
	}

	if( uxTaskPriorityGet( NULL ) != genqMUTEX_HIGH_PRIORITY )
	{
		xErrorDetected = pdTRUE;
	}

	/* Now also give back the local mutex, taking the held count back to 0.
	This time the priority of this task should be disinherited back to the
	priority to which it was set while the mutex was held.  This means
	the medium priority task should execute and increment the guarded
	variable.   When this task next	runs both the high and medium priority
	tasks will have been suspended again. */
	if( xSemaphoreGive( xLocalMutex ) != pdPASS )
	{
		xErrorDetected = pdTRUE;
	}

	#if configUSE_PREEMPTION == 0
		taskYIELD();
	#endif

	/* Check the guarded variable did indeed increment... */
	if( ulGuardedVariable != 1 )
	{
		xErrorDetected = pdTRUE;
	}

	/* ... and that the priority of this task has been disinherited to
	genqMUTEX_TEST_PRIORITY. */
	if( uxTaskPriorityGet( NULL ) != genqMUTEX_TEST_PRIORITY )
	{
		xErrorDetected = pdTRUE;
	}

	/* Set the priority of this task back to its original value, ready for
	the next loop around this test. */
	vTaskPrioritySet( NULL, genqMUTEX_LOW_PRIORITY );
}
/*-----------------------------------------------------------*/

static void prvTakeTwoMutexesReturnInSameOrder( SemaphoreHandle_t xMutex, SemaphoreHandle_t xLocalMutex )
{
	/* Take the mutex.  It should be available now. */
	if( xSemaphoreTake( xMutex, genqNO_BLOCK ) != pdPASS )
	{
		xErrorDetected = pdTRUE;
	}

	/* Set the guarded variable to a known start value. */
	ulGuardedVariable = 0;

	/* This task's priority should be as per that assigned when the task was
	created. */
	if( uxTaskPriorityGet( NULL ) != genqMUTEX_LOW_PRIORITY )
	{
		xErrorDetected = pdTRUE;
	}

	/* Now unsuspend the high priority task.  This will attempt to take the
	mutex, and block when it finds it cannot obtain it. */
	vTaskResume( xHighPriorityMutexTask );

	#if configUSE_PREEMPTION == 0
		taskYIELD();
	#endif

	/* Ensure the task is reporting its priority as blocked and not
	suspended (as it would have done in versions up to V7.5.3). */
	#if( INCLUDE_eTaskGetState == 1 )
	{
		configASSERT( eTaskGetState( xHighPriorityMutexTask ) == eBlocked );
	}
	#endif /* INCLUDE_eTaskGetState */

	/* The priority of the high priority task should now have been inherited
	as by now it will have attempted to get the mutex. */
	if( uxTaskPriorityGet( NULL ) != genqMUTEX_HIGH_PRIORITY )
	{
		xErrorDetected = pdTRUE;
	}

	/* Now unsuspend the medium priority task.  This should not run as the
	inherited priority of this task is above that of the medium priority
	task. */
	vTaskResume( xMediumPriorityMutexTask );

	/* If the medium priority task did run then it will have incremented the
	guarded variable. */
	if( ulGuardedVariable != 0 )
	{
		xErrorDetected = pdTRUE;
	}

	/* Take the local mutex too, so two mutexes are now held. */
	if( xSemaphoreTake( xLocalMutex, genqNO_BLOCK ) != pdPASS )
	{
		xErrorDetected = pdTRUE;
	}

	/* When the local semaphore is given back the priority of this task should
	not	yet be disinherited because the shared mutex is still held.  This is a
	simplification to allow FreeRTOS to be integrated with middleware that
	attempts to hold multiple mutexes without bloating the code with complex
	algorithms.  It is possible that the high priority mutex task will
	execute as it shares a priority with this task. */
	if( xSemaphoreGive( xLocalMutex ) != pdPASS )
	{
		xErrorDetected = pdTRUE;
	}

	#if configUSE_PREEMPTION == 0
		taskYIELD();
	#endif

	/* The guarded variable is only incremented by the medium priority task,
	which still should not have executed as this task should remain at the
	higher priority, ensure this is the case. */
	if( ulGuardedVariable != 0 )
	{
		xErrorDetected = pdTRUE;
	}

	if( uxTaskPriorityGet( NULL ) != genqMUTEX_HIGH_PRIORITY )
	{
		xErrorDetected = pdTRUE;
	}

	/* Now also give back the shared mutex, taking the held count back to 0.
	This time the priority of this task should be disinherited back to the
	priority at which it was created.  This means the medium priority task
	should execute and increment the guarded variable.  When this task next runs
	both the high and medium priority tasks will have been suspended again. */
	if( xSemaphoreGive( xMutex ) != pdPASS )
	{
		xErrorDetected = pdTRUE;
	}

	#if configUSE_PREEMPTION == 0
		taskYIELD();
	#endif

	/* Check the guarded variable did indeed increment... */
	if( ulGuardedVariable != 1 )
	{
		xErrorDetected = pdTRUE;
	}

	/* ... and that the priority of this task has been disinherited to
	genqMUTEX_LOW_PRIORITY. */
	if( uxTaskPriorityGet( NULL ) != genqMUTEX_LOW_PRIORITY )
	{
		xErrorDetected = pdTRUE;
	}
}
/*-----------------------------------------------------------*/

static void prvLowPriorityMutexTask( void *pvParameters )
{
SemaphoreHandle_t xMutex = ( SemaphoreHandle_t ) pvParameters, xLocalMutex;

	#ifdef USE_STDIO
	void vPrintDisplayMessage( const char * const * ppcMessageToSend );

		const char * const pcTaskStartMsg = "Mutex with priority inheritance test started.\r\n";

		/* Queue a message for printing to say the task has started. */
		vPrintDisplayMessage( &pcTaskStartMsg );
	#endif

	/* The local mutex is used to check the 'mutexs held' count. */
	xLocalMutex = xSemaphoreCreateMutex();
	configASSERT( xLocalMutex );

	for( ;; )
	{
		/* The first tests exercise the priority inheritance when two mutexes
		are taken then returned in a different order to which they were
		taken. */
		prvTakeTwoMutexesReturnInDifferentOrder( xMutex, xLocalMutex );

		/* Just to show this task is still running. */
		ulLoopCounter2++;

		#if configUSE_PREEMPTION == 0
			taskYIELD();
		#endif

		/* The second tests exercise the priority inheritance when two mutexes
		are taken then returned in the same order in which they were taken. */
		prvTakeTwoMutexesReturnInSameOrder( xMutex, xLocalMutex );

		/* Just to show this task is still running. */
		ulLoopCounter2++;

		#if configUSE_PREEMPTION == 0
			taskYIELD();
		#endif
	}
}
/*-----------------------------------------------------------*/

static void prvMediumPriorityMutexTask( void *pvParameters )
{
	( void ) pvParameters;

	for( ;; )
	{
		/* The medium priority task starts by suspending itself.  The low
		priority task will unsuspend this task when required. */
		vTaskSuspend( NULL );

		/* When this task unsuspends all it does is increment the guarded
		variable, this is so the low priority task knows that it has
		executed. */
		ulGuardedVariable++;
	}
}
/*-----------------------------------------------------------*/

static void prvHighPriorityMutexTask( void *pvParameters )
{
SemaphoreHandle_t xMutex = ( SemaphoreHandle_t ) pvParameters;

	for( ;; )
	{
		/* The high priority task starts by suspending itself.  The low
		priority task will unsuspend this task when required. */
		vTaskSuspend( NULL );

		/* When this task unsuspends all it does is attempt to obtain
		the mutex.  It should find the mutex is not available so a
		block time is specified. */
		if( xSemaphoreTake( xMutex, portMAX_DELAY ) != pdPASS )
		{
			xErrorDetected = pdTRUE;
		}

		/* When the mutex is eventually obtained it is just given back before
		returning to suspend ready for the next cycle. */
		if( xSemaphoreGive( xMutex ) != pdPASS )
		{
			xErrorDetected = pdTRUE;
		}
	}
}
/*-----------------------------------------------------------*/

/* NOTE: This function is not declared static to prevent compiler warnings in
demos where the function is declared but not used. */
void vInterruptMutexTask( void *pvParameters )
{
const TickType_t xInterruptGivePeriod = pdMS_TO_TICKS( genqINTERRUPT_MUTEX_GIVE_PERIOD_MS );
volatile uint32_t ulLoops = 0;

	/* Just to avoid compiler warnings. */
	( void ) pvParameters;

	for( ;; )
	{
		/* Has to wait longer than the time between gives to make sure it
		should definitely have received the mutex. */
		if( xSemaphoreTake( xISRMutex, ( xInterruptGivePeriod * 2 ) ) != pdPASS )
		{
			xErrorDetected = pdTRUE;
		}
		else
		{
			ulLoops++;
		}
	}
}
/*-----------------------------------------------------------*/

void vMutexISRInteractionTest( void )
{
static TickType_t xLastGiveTime = 0;
TickType_t xTimeNow;

	xTimeNow = xTaskGetTickCountFromISR();
	if( ( xTimeNow - xLastGiveTime ) >= pdMS_TO_TICKS( genqINTERRUPT_MUTEX_GIVE_PERIOD_MS ) )
	{
		configASSERT( xISRMutex );
		xSemaphoreGiveFromISR( xISRMutex, NULL );
		xLastGiveTime = xTimeNow;
	}
}
/*-----------------------------------------------------------*/

/* This is called to check that all the created tasks are still running. */
BaseType_t xAreGenericQueueTasksStillRunning( void )
{
static uint32_t ulLastLoopCounter = 0, ulLastLoopCounter2 = 0;

	/* If the demo task is still running then we expect the loop counters to
	have incremented since this function was last called. */
	if( ulLastLoopCounter == ulLoopCounter )
	{
		xErrorDetected = pdTRUE;
	}

	if( ulLastLoopCounter2 == ulLoopCounter2 )
	{
		xErrorDetected = pdTRUE;
	}

	ulLastLoopCounter = ulLoopCounter;
	ulLastLoopCounter2 = ulLoopCounter2;

	/* Errors detected in the task itself will have latched xErrorDetected
	to true. */

	return ( BaseType_t ) !xErrorDetected;
}


