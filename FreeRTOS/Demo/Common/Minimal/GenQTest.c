/*
    FreeRTOS V7.5.2 - Copyright (C) 2013 Real Time Engineers Ltd.

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

    >>! NOTE: The modification to the GPL is included to allow you to distribute
    >>! a combined work that includes FreeRTOS without being obliged to provide
    >>! the source code for proprietary components outside of the FreeRTOS
    >>! kernel.

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

/*-----------------------------------------------------------*/

/* Flag that will be latched to pdTRUE should any unexpected behaviour be
detected in any of the tasks. */
static volatile portBASE_TYPE xErrorDetected = pdFALSE;

/* Counters that are incremented on each cycle of a test.  This is used to
detect a stalled task - a test that is no longer running. */
static volatile unsigned portLONG ulLoopCounter = 0;
static volatile unsigned portLONG ulLoopCounter2 = 0;

/* The variable that is guarded by the mutex in the mutex demo tasks. */
static volatile unsigned portLONG ulGuardedVariable = 0;

/* Handles used in the mutext test to suspend and resume the high and medium
priority mutex test tasks. */
static xTaskHandle xHighPriorityMutexTask, xMediumPriorityMutexTask;

/*-----------------------------------------------------------*/

void vStartGenericQueueTasks( unsigned portBASE_TYPE uxPriority )
{
xQueueHandle xQueue;
xSemaphoreHandle xMutex;

	/* Create the queue that we are going to use for the
	prvSendFrontAndBackTest demo. */
	xQueue = xQueueCreate( genqQUEUE_LENGTH, sizeof( unsigned portLONG ) );

	/* vQueueAddToRegistry() adds the queue to the queue registry, if one is
	in use.  The queue registry is provided as a means for kernel aware 
	debuggers to locate queues and has no purpose if a kernel aware debugger
	is not being used.  The call to vQueueAddToRegistry() will be removed
	by the pre-processor if configQUEUE_REGISTRY_SIZE is not defined or is 
	defined to be less than 1. */
	vQueueAddToRegistry( xQueue, ( signed portCHAR * ) "Gen_Queue_Test" );

	/* Create the demo task and pass it the queue just created.  We are
	passing the queue handle by value so it does not matter that it is
	declared on the stack here. */
	xTaskCreate( prvSendFrontAndBackTest, ( signed portCHAR * )"GenQ", configMINIMAL_STACK_SIZE, ( void * ) xQueue, uxPriority, NULL );

	/* Create the mutex used by the prvMutexTest task. */
	xMutex = xSemaphoreCreateMutex();

	/* vQueueAddToRegistry() adds the mutex to the registry, if one is
	in use.  The registry is provided as a means for kernel aware 
	debuggers to locate mutexes and has no purpose if a kernel aware debugger
	is not being used.  The call to vQueueAddToRegistry() will be removed
	by the pre-processor if configQUEUE_REGISTRY_SIZE is not defined or is 
	defined to be less than 1. */
	vQueueAddToRegistry( ( xQueueHandle ) xMutex, ( signed portCHAR * ) "Gen_Queue_Mutex" );

	/* Create the mutex demo tasks and pass it the mutex just created.  We are
	passing the mutex handle by value so it does not matter that it is declared
	on the stack here. */
	xTaskCreate( prvLowPriorityMutexTask, ( signed portCHAR * )"MuLow", configMINIMAL_STACK_SIZE, ( void * ) xMutex, genqMUTEX_LOW_PRIORITY, NULL );
	xTaskCreate( prvMediumPriorityMutexTask, ( signed portCHAR * )"MuMed", configMINIMAL_STACK_SIZE, NULL, genqMUTEX_MEDIUM_PRIORITY, &xMediumPriorityMutexTask );
	xTaskCreate( prvHighPriorityMutexTask, ( signed portCHAR * )"MuHigh", configMINIMAL_STACK_SIZE, ( void * ) xMutex, genqMUTEX_HIGH_PRIORITY, &xHighPriorityMutexTask );
}
/*-----------------------------------------------------------*/

static void prvSendFrontAndBackTest( void *pvParameters )
{
unsigned portLONG ulData, ulData2;
xQueueHandle xQueue;

	#ifdef USE_STDIO
	void vPrintDisplayMessage( const portCHAR * const * ppcMessageToSend );
	
		const portCHAR * const pcTaskStartMsg = "Queue SendToFront/SendToBack/Peek test started.\r\n";

		/* Queue a message for printing to say the task has started. */
		vPrintDisplayMessage( &pcTaskStartMsg );
	#endif

	xQueue = ( xQueueHandle ) pvParameters;

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

static void prvLowPriorityMutexTask( void *pvParameters )
{
xSemaphoreHandle xMutex = ( xSemaphoreHandle ) pvParameters;

	#ifdef USE_STDIO
	void vPrintDisplayMessage( const portCHAR * const * ppcMessageToSend );
	
		const portCHAR * const pcTaskStartMsg = "Mutex with priority inheritance test started.\r\n";

		/* Queue a message for printing to say the task has started. */
		vPrintDisplayMessage( &pcTaskStartMsg );
	#endif

	for( ;; )
	{
		/* Take the mutex.  It should be available now. */
		if( xSemaphoreTake( xMutex, genqNO_BLOCK ) != pdPASS )
		{
			xErrorDetected = pdTRUE;
		}

		/* Set our guarded variable to a known start value. */
		ulGuardedVariable = 0;

		/* Our priority should be as per that assigned when the task was
		created. */
		if( uxTaskPriorityGet( NULL ) != genqMUTEX_LOW_PRIORITY )
		{
			xErrorDetected = pdTRUE;
		}

		/* Now unsuspend the high priority task.  This will attempt to take the
		mutex, and block when it finds it cannot obtain it. */
		vTaskResume( xHighPriorityMutexTask );

		/* We should now have inherited the prioritoy of the high priority task,
		as by now it will have attempted to get the mutex. */
		if( uxTaskPriorityGet( NULL ) != genqMUTEX_HIGH_PRIORITY )
		{
			xErrorDetected = pdTRUE;
		}

		/* We can attempt to set our priority to the test priority - between the
		idle priority and the medium/high test priorities, but our actual
		prioroity should remain at the high priority. */
		vTaskPrioritySet( NULL, genqMUTEX_TEST_PRIORITY );
		if( uxTaskPriorityGet( NULL ) != genqMUTEX_HIGH_PRIORITY )
		{
			xErrorDetected = pdTRUE;
		}

		/* Now unsuspend the medium priority task.  This should not run as our
		inherited priority is above that of the medium priority task. */
		vTaskResume( xMediumPriorityMutexTask );

		/* If the did run then it will have incremented our guarded variable. */
		if( ulGuardedVariable != 0 )
		{
			xErrorDetected = pdTRUE;
		}

		/* When we give back the semaphore our priority should be disinherited
		back to the priority to which we attempted to set ourselves.  This means
		that when the high priority task next blocks, the medium priority task
		should execute and increment the guarded variable.   When we next run
		both the high and medium priority tasks will have been suspended again. */
		if( xSemaphoreGive( xMutex ) != pdPASS )
		{
			xErrorDetected = pdTRUE;
		}

		/* Check that the guarded variable did indeed increment... */
		if( ulGuardedVariable != 1 )
		{
			xErrorDetected = pdTRUE;
		}

		/* ... and that our priority has been disinherited to
		genqMUTEX_TEST_PRIORITY. */
		if( uxTaskPriorityGet( NULL ) != genqMUTEX_TEST_PRIORITY )
		{
			xErrorDetected = pdTRUE;
		}

		/* Set our priority back to our original priority ready for the next
		loop around this test. */
		vTaskPrioritySet( NULL, genqMUTEX_LOW_PRIORITY );

		/* Just to show we are still running. */
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
xSemaphoreHandle xMutex = ( xSemaphoreHandle ) pvParameters;

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

		/* When we eventually obtain the mutex we just give it back then
		return to suspend ready for the next test. */
		if( xSemaphoreGive( xMutex ) != pdPASS )
		{
			xErrorDetected = pdTRUE;
		}		
	}
}
/*-----------------------------------------------------------*/

/* This is called to check that all the created tasks are still running. */
portBASE_TYPE xAreGenericQueueTasksStillRunning( void )
{
static unsigned portLONG ulLastLoopCounter = 0, ulLastLoopCounter2 = 0;

	/* If the demo task is still running then we expect the loopcounters to
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

	return ( portBASE_TYPE ) !xErrorDetected;
}


