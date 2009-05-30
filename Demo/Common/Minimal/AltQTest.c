/*
	FreeRTOS.org V5.3.0 - Copyright (C) 2003-2009 Richard Barry.

	This file is part of the FreeRTOS.org distribution.

	FreeRTOS.org is free software; you can redistribute it and/or modify it
	under the terms of the GNU General Public License (version 2) as published
	by the Free Software Foundation and modified by the FreeRTOS exception.
	**NOTE** The exception to the GPL is included to allow you to distribute a
	combined work that includes FreeRTOS.org without being obliged to provide
	the source code for any proprietary components.  Alternative commercial
	license and support terms are also available upon request.  See the 
	licensing section of http://www.FreeRTOS.org for full details.

	FreeRTOS.org is distributed in the hope that it will be useful,	but WITHOUT
	ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
	FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
	more details.

	You should have received a copy of the GNU General Public License along
	with FreeRTOS.org; if not, write to the Free Software Foundation, Inc., 59
	Temple Place, Suite 330, Boston, MA  02111-1307  USA.


	***************************************************************************
	*                                                                         *
	* Get the FreeRTOS eBook!  See http://www.FreeRTOS.org/Documentation      *
	*                                                                         *
	* This is a concise, step by step, 'hands on' guide that describes both   *
	* general multitasking concepts and FreeRTOS specifics. It presents and   *
	* explains numerous examples that are written using the FreeRTOS API.     *
	* Full source code for all the examples is provided in an accompanying    *
	* .zip file.                                                              *
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
 * This file implements the same demo and test as GenQTest.c, but uses the 
 * light weight API in place of the fully featured API.
 *
 * See the comments at the top of GenQTest.c for a description.
 */


#include <stdlib.h>

/* Scheduler include files. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"
#include "semphr.h"

/* Demo program include files. */
#include "AltQTest.h"

#define genqQUEUE_LENGTH		( 5 )
#define genqNO_BLOCK			( 0 )

#define genqMUTEX_LOW_PRIORITY		( tskIDLE_PRIORITY )
#define genqMUTEX_TEST_PRIORITY		( tskIDLE_PRIORITY + 1 )
#define genqMUTEX_MEDIUM_PRIORITY	( tskIDLE_PRIORITY + 2 )
#define genqMUTEX_HIGH_PRIORITY		( tskIDLE_PRIORITY + 3 )

/*-----------------------------------------------------------*/

/*
 * Tests the behaviour of the xQueueAltSendToFront() and xQueueAltSendToBack()
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
static portBASE_TYPE xErrorDetected = pdFALSE;

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

void vStartAltGenericQueueTasks( unsigned portBASE_TYPE uxPriority )
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
	vQueueAddToRegistry( xQueue, ( signed portCHAR * ) "Alt_Gen_Test_Queue" );

	/* Create the demo task and pass it the queue just created.  We are
	passing the queue handle by value so it does not matter that it is
	declared on the stack here. */
	xTaskCreate( prvSendFrontAndBackTest, ( signed portCHAR * ) "FGenQ", configMINIMAL_STACK_SIZE, ( void * ) xQueue, uxPriority, NULL );

	/* Create the mutex used by the prvMutexTest task. */
	xMutex = xSemaphoreCreateMutex();

	/* vQueueAddToRegistry() adds the mutex to the registry, if one is
	in use.  The registry is provided as a means for kernel aware 
	debuggers to locate mutex and has no purpose if a kernel aware debugger
	is not being used.  The call to vQueueAddToRegistry() will be removed
	by the pre-processor if configQUEUE_REGISTRY_SIZE is not defined or is 
	defined to be less than 1. */
	vQueueAddToRegistry( ( xQueueHandle ) xMutex, ( signed portCHAR * ) "Alt_Q_Mutex" );

	/* Create the mutex demo tasks and pass it the mutex just created.  We are
	passing the mutex handle by value so it does not matter that it is declared
	on the stack here. */
	xTaskCreate( prvLowPriorityMutexTask, ( signed portCHAR * ) "FMuLow", configMINIMAL_STACK_SIZE, ( void * ) xMutex, genqMUTEX_LOW_PRIORITY, NULL );
	xTaskCreate( prvMediumPriorityMutexTask, ( signed portCHAR * ) "FMuMed", configMINIMAL_STACK_SIZE, NULL, genqMUTEX_MEDIUM_PRIORITY, &xMediumPriorityMutexTask );
	xTaskCreate( prvHighPriorityMutexTask, ( signed portCHAR * ) "FMuHigh", configMINIMAL_STACK_SIZE, ( void * ) xMutex, genqMUTEX_HIGH_PRIORITY, &xHighPriorityMutexTask );
}
/*-----------------------------------------------------------*/

static void prvSendFrontAndBackTest( void *pvParameters )
{
unsigned portLONG ulData, ulData2;
xQueueHandle xQueue;

	#ifdef USE_STDIO
	void vPrintDisplayMessage( const portCHAR * const * ppcMessageToSend );
	
		const portCHAR * const pcTaskStartMsg = "Alt queue SendToFront/SendToBack/Peek test started.\r\n";

		/* Queue a message for printing to say the task has started. */
		vPrintDisplayMessage( &pcTaskStartMsg );
	#endif

	xQueue = ( xQueueHandle ) pvParameters;

	for( ;; )
	{
		/* The queue is empty, so sending an item to the back of the queue
		should have the same efect as sending it to the front of the queue.

		First send to the front and check everything is as expected. */
		xQueueAltSendToFront( xQueue, ( void * ) &ulLoopCounter, genqNO_BLOCK );

		if( uxQueueMessagesWaiting( xQueue ) != 1 )
		{
			xErrorDetected = pdTRUE;
		}

		if( xQueueAltReceive( xQueue, ( void * ) &ulData, genqNO_BLOCK ) != pdPASS )
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

		xQueueAltSendToBack( xQueue, ( void * ) &ulLoopCounter, genqNO_BLOCK );

		if( uxQueueMessagesWaiting( xQueue ) != 1 )
		{
			xErrorDetected = pdTRUE;
		}

		if( xQueueAltReceive( xQueue, ( void * ) &ulData, genqNO_BLOCK ) != pdPASS )
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
			xQueueAltSendToBack( xQueue, ( void * ) &ulData, genqNO_BLOCK );
		}

		/* Now the order in the queue should be 2, 3, 4, with 2 being the first
		thing to be read out.  Now add 1 then 0 to the front of the queue. */
		if( uxQueueMessagesWaiting( xQueue ) != 3 )
		{
			xErrorDetected = pdTRUE;
		}
		ulData = 1;
		xQueueAltSendToFront( xQueue, ( void * ) &ulData, genqNO_BLOCK );
		ulData = 0;
		xQueueAltSendToFront( xQueue, ( void * ) &ulData, genqNO_BLOCK );

		/* Now the queue should be full, and when we read the data out we
		should receive 0, 1, 2, 3, 4. */
		if( uxQueueMessagesWaiting( xQueue ) != 5 )
		{
			xErrorDetected = pdTRUE;
		}

		if( xQueueAltSendToFront( xQueue, ( void * ) &ulData, genqNO_BLOCK ) != errQUEUE_FULL )
		{
			xErrorDetected = pdTRUE;
		}

		if( xQueueAltSendToBack( xQueue, ( void * ) &ulData, genqNO_BLOCK ) != errQUEUE_FULL )
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
			if( xQueueAltPeek( xQueue, &ulData2, genqNO_BLOCK ) != pdPASS )
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
			if( xQueueAltReceive( xQueue, &ulData2, genqNO_BLOCK ) != pdPASS )
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
		if( xQueueAltSendToBack( xQueue, &ulData, genqNO_BLOCK ) != pdPASS )
		{
			xErrorDetected = pdTRUE;
		}
		ulData = 11;
		if( xQueueAltSendToBack( xQueue, &ulData, genqNO_BLOCK ) != pdPASS )
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
			if( xQueueAltSendToFront( xQueue, ( void * ) &ulData, genqNO_BLOCK ) != pdPASS )
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

		if( xQueueAltSendToFront( xQueue, ( void * ) &ulData, genqNO_BLOCK ) != errQUEUE_FULL )
		{
			xErrorDetected = pdTRUE;
		}

		if( xQueueAltSendToBack( xQueue, ( void * ) &ulData, genqNO_BLOCK ) != errQUEUE_FULL )
		{
			xErrorDetected = pdTRUE;
		}

		#if configUSE_PREEMPTION == 0
			taskYIELD();
		#endif

		/* Check the data we read out is in the expected order. */
		for( ulData = 7; ulData < ( 7 + genqQUEUE_LENGTH ); ulData++ )
		{
			if( xQueueAltReceive( xQueue, &ulData2, genqNO_BLOCK ) != pdPASS )
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
	
		const portCHAR * const pcTaskStartMsg = "Fast mutex with priority inheritance test started.\r\n";

		/* Queue a message for printing to say the task has started. */
		vPrintDisplayMessage( &pcTaskStartMsg );
	#endif

	( void ) pvParameters;


	for( ;; )
	{
		/* Take the mutex.  It should be available now. */
		if( xSemaphoreAltTake( xMutex, genqNO_BLOCK ) != pdPASS )
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
		if( xSemaphoreAltGive( xMutex ) != pdPASS )
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

	( void ) pvParameters;

	for( ;; )
	{
		/* The high priority task starts by suspending itself.  The low
		priority task will unsuspend this task when required. */
		vTaskSuspend( NULL );

		/* When this task unsuspends all it does is attempt to obtain
		the mutex.  It should find the mutex is not available so a
		block time is specified. */
		if( xSemaphoreAltTake( xMutex, portMAX_DELAY ) != pdPASS )
		{
			xErrorDetected = pdTRUE;
		}

		/* When we eventually obtain the mutex we just give it back then
		return to suspend ready for the next test. */
		if( xSemaphoreAltGive( xMutex ) != pdPASS )
		{
			xErrorDetected = pdTRUE;
		}		
	}
}
/*-----------------------------------------------------------*/

/* This is called to check that all the created tasks are still running. */
portBASE_TYPE xAreAltGenericQueueTasksStillRunning( void )
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

	return !xErrorDetected;
}


