/*
	FreeRTOS.org V5.1.1 - Copyright (C) 2003-2008 Richard Barry.

	This file is part of the FreeRTOS.org distribution.

	FreeRTOS.org is free software; you can redistribute it and/or modify
	it under the terms of the GNU General Public License as published by
	the Free Software Foundation; either version 2 of the License, or
	(at your option) any later version.

	FreeRTOS.org is distributed in the hope that it will be useful,
	but WITHOUT ANY WARRANTY; without even the implied warranty of
	MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
	GNU General Public License for more details.

	You should have received a copy of the GNU General Public License
	along with FreeRTOS.org; if not, write to the Free Software
	Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA

	A special exception to the GPL can be applied should you wish to distribute
	a combined work that includes FreeRTOS.org, without being obliged to provide
	the source code for any proprietary components.  See the licensing section
	of http://www.FreeRTOS.org for full details of how and when the exception
	can be applied.

    ***************************************************************************
    ***************************************************************************
    *                                                                         *
    * SAVE TIME AND MONEY!  We can port FreeRTOS.org to your own hardware,    *
    * and even write all or part of your application on your behalf.          *
    * See http://www.OpenRTOS.com for details of the services we provide to   *
    * expedite your project.                                                  *
    *                                                                         *
    ***************************************************************************
    ***************************************************************************

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
 * Tests the behaviour when data is peeked from a queue when there are
 * multiple tasks blocked on the queue.
 */


#include <stdlib.h>

/* Scheduler include files. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"
#include "semphr.h"

/* Demo program include files. */
#include "QPeek.h"

#define qpeekQUEUE_LENGTH		( 5 )
#define qpeekNO_BLOCK			( 0 )
#define qpeekSHORT_DELAY		( 10 )

#define qpeekLOW_PRIORITY			( tskIDLE_PRIORITY + 0 )
#define qpeekMEDIUM_PRIORITY		( tskIDLE_PRIORITY + 1 )
#define qpeekHIGH_PRIORITY			( tskIDLE_PRIORITY + 2 )
#define qpeekHIGHEST_PRIORITY		( tskIDLE_PRIORITY + 3 )

/*-----------------------------------------------------------*/

/*
 * The following three tasks are used to demonstrate the peeking behaviour.
 * Each task is given a different priority to demonstrate the order in which
 * tasks are woken as data is peeked from a queue.
 */
static void prvLowPriorityPeekTask( void *pvParameters );
static void prvMediumPriorityPeekTask( void *pvParameters );
static void prvHighPriorityPeekTask( void *pvParameters );
static void prvHighestPriorityPeekTask( void *pvParameters );

/*-----------------------------------------------------------*/

/* Flag that will be latched to pdTRUE should any unexpected behaviour be
detected in any of the tasks. */
static volatile portBASE_TYPE xErrorDetected = pdFALSE;

/* Counter that is incremented on each cycle of a test.  This is used to
detect a stalled task - a test that is no longer running. */
static volatile unsigned portLONG ulLoopCounter = 0;

/* Handles to the test tasks. */
xTaskHandle xMediumPriorityTask, xHighPriorityTask, xHighestPriorityTask;
/*-----------------------------------------------------------*/

void vStartQueuePeekTasks( void )
{
xQueueHandle xQueue;

	/* Create the queue that we are going to use for the test/demo. */
	xQueue = xQueueCreate( qpeekQUEUE_LENGTH, sizeof( unsigned portLONG ) );

	/* vQueueAddToRegistry() adds the queue to the queue registry, if one is
	in use.  The queue registry is provided as a means for kernel aware 
	debuggers to locate queues and has no purpose if a kernel aware debugger
	is not being used.  The call to vQueueAddToRegistry() will be removed
	by the pre-processor if configQUEUE_REGISTRY_SIZE is not defined or is 
	defined to be less than 1. */
	vQueueAddToRegistry( xQueue, ( signed portCHAR * ) "QPeek_Test_Queue" );

	/* Create the demo tasks and pass it the queue just created.  We are
	passing the queue handle by value so it does not matter that it is declared
	on the stack here. */
	xTaskCreate( prvLowPriorityPeekTask, ( signed portCHAR * )"PeekL", configMINIMAL_STACK_SIZE, ( void * ) xQueue, qpeekLOW_PRIORITY, NULL );
	xTaskCreate( prvMediumPriorityPeekTask, ( signed portCHAR * )"PeekM", configMINIMAL_STACK_SIZE, ( void * ) xQueue, qpeekMEDIUM_PRIORITY, &xMediumPriorityTask );
	xTaskCreate( prvHighPriorityPeekTask, ( signed portCHAR * )"PeekH1", configMINIMAL_STACK_SIZE, ( void * ) xQueue, qpeekHIGH_PRIORITY, &xHighPriorityTask );
	xTaskCreate( prvHighestPriorityPeekTask, ( signed portCHAR * )"PeekH2", configMINIMAL_STACK_SIZE, ( void * ) xQueue, qpeekHIGHEST_PRIORITY, &xHighestPriorityTask );
}
/*-----------------------------------------------------------*/

static void prvHighestPriorityPeekTask( void *pvParameters )
{
xQueueHandle xQueue = ( xQueueHandle ) pvParameters;
unsigned portLONG ulValue;

	#ifdef USE_STDIO
	{
		void vPrintDisplayMessage( const portCHAR * const * ppcMessageToSend );
	
		const portCHAR * const pcTaskStartMsg = "Queue peek test started.\r\n";

		/* Queue a message for printing to say the task has started. */
		vPrintDisplayMessage( &pcTaskStartMsg );
	}
	#endif

	for( ;; )
	{
		/* Try peeking from the queue.  The queue should be empty so we will
		block, allowing the high priority task to execute. */
		if( xQueuePeek( xQueue, &ulValue, portMAX_DELAY ) != pdPASS )
		{
			/* We expected to have received something by the time we unblock. */
			xErrorDetected = pdTRUE;
		}

		/* When we reach here the high and medium priority tasks should still
		be blocked on the queue.  We unblocked because the low priority task
		wrote a value to the queue, which we should have peeked.  Peeking the
		data (rather than receiving it) will leave the data on the queue, so
		the high priority task should then have also been unblocked, but not
		yet executed. */
		if( ulValue != 0x11223344 )
		{
			/* We did not receive the expected value. */
			xErrorDetected = pdTRUE;
		}

		if( uxQueueMessagesWaiting( xQueue ) != 1 )
		{
			/* The message should have been left on the queue. */
			xErrorDetected = pdTRUE;
		}

		/* Now we are going to actually receive the data, so when the high
		priority task runs it will find the queue empty and return to the
		blocked state. */
		ulValue = 0;
		if( xQueueReceive( xQueue, &ulValue, qpeekNO_BLOCK ) != pdPASS )
		{
			/* We expected to receive the value. */
			xErrorDetected = pdTRUE;
		}

		if( ulValue != 0x11223344 )
		{
			/* We did not receive the expected value - which should have been
			the same value as was peeked. */
			xErrorDetected = pdTRUE;
		}

		/* Now we will block again as the queue is once more empty.  The low 
		priority task can then execute again. */
		if( xQueuePeek( xQueue, &ulValue, portMAX_DELAY ) != pdPASS )
		{
			/* We expected to have received something by the time we unblock. */
			xErrorDetected = pdTRUE;
		}

		/* When we get here the low priority task should have again written to the
		queue. */
		if( ulValue != 0x01234567 )
		{
			/* We did not receive the expected value. */
			xErrorDetected = pdTRUE;
		}

		if( uxQueueMessagesWaiting( xQueue ) != 1 )
		{
			/* The message should have been left on the queue. */
			xErrorDetected = pdTRUE;
		}

		/* We only peeked the data, so suspending ourselves now should enable
		the high priority task to also peek the data.  The high priority task
		will have been unblocked when we peeked the data as we left the data
		in the queue. */
		vTaskSuspend( NULL );



		/* This time we are going to do the same as the above test, but the
		high priority task is going to receive the data, rather than peek it.
		This means that the medium priority task should never peek the value. */
		if( xQueuePeek( xQueue, &ulValue, portMAX_DELAY ) != pdPASS )
		{
			xErrorDetected = pdTRUE;
		}

		if( ulValue != 0xaabbaabb )
		{
			xErrorDetected = pdTRUE;
		}

		vTaskSuspend( NULL );		
	}
}
/*-----------------------------------------------------------*/

static void prvHighPriorityPeekTask( void *pvParameters )
{
xQueueHandle xQueue = ( xQueueHandle ) pvParameters;
unsigned portLONG ulValue;

	for( ;; )
	{
		/* Try peeking from the queue.  The queue should be empty so we will
		block, allowing the medium priority task to execute.  Both the high
		and highest priority tasks will then be blocked on the queue. */
		if( xQueuePeek( xQueue, &ulValue, portMAX_DELAY ) != pdPASS )
		{
			/* We expected to have received something by the time we unblock. */
			xErrorDetected = pdTRUE;
		}

		/* When we get here the highest priority task should have peeked the data
		(unblocking this task) then suspended (allowing this task to also peek
		the data). */
		if( ulValue != 0x01234567 )
		{
			/* We did not receive the expected value. */
			xErrorDetected = pdTRUE;
		}

		if( uxQueueMessagesWaiting( xQueue ) != 1 )
		{
			/* The message should have been left on the queue. */
			xErrorDetected = pdTRUE;
		}

		/* We only peeked the data, so suspending ourselves now should enable
		the medium priority task to also peek the data.  The medium priority task
		will have been unblocked when we peeked the data as we left the data
		in the queue. */
		vTaskSuspend( NULL );


		/* This time we are going actually receive the value, so the medium
		priority task will never peek the data - we removed it from the queue. */
		if( xQueueReceive( xQueue, &ulValue, portMAX_DELAY ) != pdPASS )
		{
			xErrorDetected = pdTRUE;
		}

		if( ulValue != 0xaabbaabb )
		{
			xErrorDetected = pdTRUE;
		}

		vTaskSuspend( NULL );				
	}
}
/*-----------------------------------------------------------*/

static void prvMediumPriorityPeekTask( void *pvParameters )
{
xQueueHandle xQueue = ( xQueueHandle ) pvParameters;
unsigned portLONG ulValue;

	for( ;; )
	{
		/* Try peeking from the queue.  The queue should be empty so we will
		block, allowing the low priority task to execute.  The highest, high
		and medium priority tasks will then all be blocked on the queue. */
		if( xQueuePeek( xQueue, &ulValue, portMAX_DELAY ) != pdPASS )
		{
			/* We expected to have received something by the time we unblock. */
			xErrorDetected = pdTRUE;
		}

		/* When we get here the high priority task should have peeked the data
		(unblocking this task) then suspended (allowing this task to also peek
		the data). */
		if( ulValue != 0x01234567 )
		{
			/* We did not receive the expected value. */
			xErrorDetected = pdTRUE;
		}

		if( uxQueueMessagesWaiting( xQueue ) != 1 )
		{
			/* The message should have been left on the queue. */
			xErrorDetected = pdTRUE;
		}

		/* Just so we know the test is still running. */
		ulLoopCounter++;

		/* Now we can suspend ourselves so the low priority task can execute
		again. */
		vTaskSuspend( NULL );
	}
}
/*-----------------------------------------------------------*/

static void prvLowPriorityPeekTask( void *pvParameters )
{
xQueueHandle xQueue = ( xQueueHandle ) pvParameters;
unsigned portLONG ulValue;

	for( ;; )
	{
		/* Write some data to the queue.  This should unblock the highest 
		priority task that is waiting to peek data from the queue. */
		ulValue = 0x11223344;
		if( xQueueSendToBack( xQueue, &ulValue, qpeekNO_BLOCK ) != pdPASS )
		{
			/* We were expecting the queue to be empty so we should not of
			had a problem writing to the queue. */
			xErrorDetected = pdTRUE;
		}

		/* By the time we get here the data should have been removed from
		the queue. */
		if( uxQueueMessagesWaiting( xQueue ) != 0 )
		{
			xErrorDetected = pdTRUE;
		}

		/* Write another value to the queue, again waking the highest priority
		task that is blocked on the queue. */
		ulValue = 0x01234567;
		if( xQueueSendToBack( xQueue, &ulValue, qpeekNO_BLOCK ) != pdPASS )
		{
			/* We were expecting the queue to be empty so we should not of
			had a problem writing to the queue. */
			xErrorDetected = pdTRUE;
		}

		/* All the other tasks should now have successfully peeked the data.
		The data is still in the queue so we should be able to receive it. */
		ulValue = 0;
		if( xQueueReceive( xQueue, &ulValue, qpeekNO_BLOCK ) != pdPASS )
		{
			/* We expected to receive the data. */
			xErrorDetected = pdTRUE;
		}

		if( ulValue != 0x01234567 )
		{
			/* We did not receive the expected value. */
		}
		
		/* Lets just delay a while as this is an intensive test as we don't
		want to starve other tests of processing time. */
		vTaskDelay( qpeekSHORT_DELAY );

		/* Unsuspend the other tasks so we can repeat the test - this time
		however not all the other tasks will peek the data as the high
		priority task is actually going to remove it from the queue.  Send
		to front is used just to be different.  As the queue is empty it
		makes no difference to the result. */
		vTaskResume( xMediumPriorityTask );
		vTaskResume( xHighPriorityTask );
		vTaskResume( xHighestPriorityTask );

		ulValue = 0xaabbaabb;
		if( xQueueSendToFront( xQueue, &ulValue, qpeekNO_BLOCK ) != pdPASS )
		{
			/* We were expecting the queue to be empty so we should not of
			had a problem writing to the queue. */
			xErrorDetected = pdTRUE;
		}

		/* This time we should find that the queue is empty.  The high priority
		task actually removed the data rather than just peeking it. */
		if( xQueuePeek( xQueue, &ulValue, qpeekNO_BLOCK ) != errQUEUE_EMPTY )
		{
			/* We expected to receive the data. */
			xErrorDetected = pdTRUE;
		}

		/* Unsuspend the highest and high priority tasks so we can go back
		and repeat the whole thing.  The medium priority task should not be
		suspended as it was not able to peek the data in this last case. */
		vTaskResume( xHighPriorityTask );
		vTaskResume( xHighestPriorityTask );		

		/* Lets just delay a while as this is an intensive test as we don't
		want to starve other tests of processing time. */
		vTaskDelay( qpeekSHORT_DELAY );
	}
}
/*-----------------------------------------------------------*/

/* This is called to check that all the created tasks are still running. */
portBASE_TYPE xAreQueuePeekTasksStillRunning( void )
{
static unsigned portLONG ulLastLoopCounter = 0;

	/* If the demo task is still running then we expect the loopcounter to
	have incremented since this function was last called. */
	if( ulLastLoopCounter == ulLoopCounter )
	{
		xErrorDetected = pdTRUE;
	}

	ulLastLoopCounter = ulLoopCounter;

	/* Errors detected in the task itself will have latched xErrorDetected
	to true. */

	return !xErrorDetected;
}

