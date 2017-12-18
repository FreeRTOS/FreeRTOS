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
 * The first test creates three tasks - two counter tasks (one continuous count
 * and one limited count) and one controller.  A "count" variable is shared
 * between all three tasks.  The two counter tasks should never be in a "ready"
 * state at the same time.  The controller task runs at the same priority as
 * the continuous count task, and at a lower priority than the limited count
 * task.
 *
 * One counter task loops indefinitely, incrementing the shared count variable
 * on each iteration.  To ensure it has exclusive access to the variable it
 * raises it's priority above that of the controller task before each
 * increment, lowering it again to it's original priority before starting the
 * next iteration.
 *
 * The other counter task increments the shared count variable on each
 * iteration of it's loop until the count has reached a limit of 0xff - at
 * which point it suspends itself.  It will not start a new loop until the
 * controller task has made it "ready" again by calling vTaskResume ().
 * This second counter task operates at a higher priority than controller
 * task so does not need to worry about mutual exclusion of the counter
 * variable.
 *
 * The controller task is in two sections.  The first section controls and
 * monitors the continuous count task.  When this section is operational the
 * limited count task is suspended.  Likewise, the second section controls
 * and monitors the limited count task.  When this section is operational the
 * continuous count task is suspended.
 *
 * In the first section the controller task first takes a copy of the shared
 * count variable.  To ensure mutual exclusion on the count variable it
 * suspends the continuous count task, resuming it again when the copy has been
 * taken.  The controller task then sleeps for a fixed period - during which
 * the continuous count task will execute and increment the shared variable.
 * When the controller task wakes it checks that the continuous count task
 * has executed by comparing the copy of the shared variable with its current
 * value.  This time, to ensure mutual exclusion, the scheduler itself is
 * suspended with a call to vTaskSuspendAll ().  This is for demonstration
 * purposes only and is not a recommended technique due to its inefficiency.
 *
 * After a fixed number of iterations the controller task suspends the
 * continuous count task, and moves on to its second section.
 *
 * At the start of the second section the shared variable is cleared to zero.
 * The limited count task is then woken from it's suspension by a call to
 * vTaskResume ().  As this counter task operates at a higher priority than
 * the controller task the controller task should not run again until the
 * shared variable has been counted up to the limited value causing the counter
 * task to suspend itself.  The next line after vTaskResume () is therefore
 * a check on the shared variable to ensure everything is as expected.
 *
 *
 * The second test consists of a couple of very simple tasks that post onto a
 * queue while the scheduler is suspended.  This test was added to test parts
 * of the scheduler not exercised by the first test.
 *
 */

#include <stdlib.h>

/* Scheduler include files. */
#include "FreeRTOS.h"
#include "task.h"
#include "semphr.h"

/* Demo app include files. */
#include "dynamic.h"

/* Function that implements the "limited count" task as described above. */
static portTASK_FUNCTION_PROTO( vLimitedIncrementTask, pvParameters );

/* Function that implements the "continuous count" task as described above. */
static portTASK_FUNCTION_PROTO( vContinuousIncrementTask, pvParameters );

/* Function that implements the controller task as described above. */
static portTASK_FUNCTION_PROTO( vCounterControlTask, pvParameters );

static portTASK_FUNCTION_PROTO( vQueueReceiveWhenSuspendedTask, pvParameters );
static portTASK_FUNCTION_PROTO( vQueueSendWhenSuspendedTask, pvParameters );

/* Demo task specific constants. */
#define priSTACK_SIZE				( configMINIMAL_STACK_SIZE )
#define priSLEEP_TIME				( ( TickType_t ) 128 / portTICK_PERIOD_MS )
#define priLOOPS					( 5 )
#define priMAX_COUNT				( ( unsigned long ) 0xff )
#define priNO_BLOCK					( ( TickType_t ) 0 )
#define priSUSPENDED_QUEUE_LENGTH	( 1 )

/*-----------------------------------------------------------*/

/* Handles to the two counter tasks.  These could be passed in as parameters
to the controller task to prevent them having to be file scope. */
static TaskHandle_t xContinousIncrementHandle, xLimitedIncrementHandle;

/* The shared counter variable.  This is passed in as a parameter to the two
counter variables for demonstration purposes. */
static unsigned long ulCounter;

/* Variables used to check that the tasks are still operating without error.
Each complete iteration of the controller task increments this variable
provided no errors have been found.  The variable maintaining the same value
is therefore indication of an error. */
static volatile unsigned short usCheckVariable = ( unsigned short ) 0;
static volatile portBASE_TYPE xSuspendedQueueSendError = pdFALSE;
static volatile portBASE_TYPE xSuspendedQueueReceiveError = pdFALSE;

/* Queue used by the second test. */
static QueueHandle_t xSuspendedTestQueue;

/*-----------------------------------------------------------*/
/*
 * Start the three tasks as described at the top of the file.
 * Note that the limited count task is given a higher priority.
 */
void vStartDynamicPriorityTasks( void )
{
	xSuspendedTestQueue = xQueueCreate( priSUSPENDED_QUEUE_LENGTH, sizeof( unsigned long ) );

	/* vQueueAddToRegistry() adds the queue to the queue registry, if one is
	in use.  The queue registry is provided as a means for kernel aware
	debuggers to locate queues and has no purpose if a kernel aware debugger
	is not being used.  The call to vQueueAddToRegistry() will be removed
	by the pre-processor if configQUEUE_REGISTRY_SIZE is not defined or is
	defined to be less than 1. */
	vQueueAddToRegistry( xSuspendedTestQueue, ( signed char * ) "Suspended_Test_Queue" );

	xTaskCreate( vContinuousIncrementTask, "CNT_INC", priSTACK_SIZE, ( void * ) &ulCounter, tskIDLE_PRIORITY, &xContinousIncrementHandle );
	xTaskCreate( vLimitedIncrementTask, "LIM_INC", priSTACK_SIZE, ( void * ) &ulCounter, tskIDLE_PRIORITY + 1, &xLimitedIncrementHandle );
	xTaskCreate( vCounterControlTask, "C_CTRL", priSTACK_SIZE, NULL, tskIDLE_PRIORITY, NULL );
	xTaskCreate( vQueueSendWhenSuspendedTask, "SUSP_TX", priSTACK_SIZE, NULL, tskIDLE_PRIORITY, NULL );
	xTaskCreate( vQueueReceiveWhenSuspendedTask, "SUSP_RX", priSTACK_SIZE, NULL, tskIDLE_PRIORITY, NULL );
}
/*-----------------------------------------------------------*/

/*
 * Just loops around incrementing the shared variable until the limit has been
 * reached.  Once the limit has been reached it suspends itself.
 */
static portTASK_FUNCTION( vLimitedIncrementTask, pvParameters )
{
unsigned long *pulCounter;

	/* Take a pointer to the shared variable from the parameters passed into
	the task. */
	pulCounter = ( unsigned long * ) pvParameters;

	/* This will run before the control task, so the first thing it does is
	suspend - the control task will resume it when ready. */
	vTaskSuspend( NULL );

	for( ;; )
	{
		/* Just count up to a value then suspend. */
		( *pulCounter )++;

		if( *pulCounter >= priMAX_COUNT )
		{
			vTaskSuspend( NULL );
		}
	}
}
/*-----------------------------------------------------------*/

/*
 * Just keep counting the shared variable up.  The control task will suspend
 * this task when it wants.
 */
static portTASK_FUNCTION( vContinuousIncrementTask, pvParameters )
{
unsigned long *pulCounter;
unsigned portBASE_TYPE uxOurPriority;

	/* Take a pointer to the shared variable from the parameters passed into
	the task. */
	pulCounter = ( unsigned long * ) pvParameters;

	/* Query our priority so we can raise it when exclusive access to the
	shared variable is required. */
	uxOurPriority = uxTaskPriorityGet( NULL );

	for( ;; )
	{
		/* Raise our priority above the controller task to ensure a context
		switch does not occur while we are accessing this variable. */
		vTaskPrioritySet( NULL, uxOurPriority + 1 );
			( *pulCounter )++;
		vTaskPrioritySet( NULL, uxOurPriority );
	}
}
/*-----------------------------------------------------------*/

/*
 * Controller task as described above.
 */
static portTASK_FUNCTION( vCounterControlTask, pvParameters )
{
unsigned long ulLastCounter;
short sLoops;
short sError = pdFALSE;

	/* Just to stop warning messages. */
	( void ) pvParameters;

	for( ;; )
	{
		/* Start with the counter at zero. */
		ulCounter = ( unsigned long ) 0;

		/* First section : */

		/* Check the continuous count task is running. */
		for( sLoops = 0; sLoops < priLOOPS; sLoops++ )
		{
			/* Suspend the continuous count task so we can take a mirror of the
			shared variable without risk of corruption. */
			vTaskSuspend( xContinousIncrementHandle );
				ulLastCounter = ulCounter;
			vTaskResume( xContinousIncrementHandle );

			/* Now delay to ensure the other task has processor time. */
			vTaskDelay( priSLEEP_TIME );

			/* Check the shared variable again.  This time to ensure mutual
			exclusion the whole scheduler will be locked.  This is just for
			demo purposes! */
			vTaskSuspendAll();
			{
				if( ulLastCounter == ulCounter )
				{
					/* The shared variable has not changed.  There is a problem
					with the continuous count task so flag an error. */
					sError = pdTRUE;
				}
			}
			xTaskResumeAll();
		}


		/* Second section: */

		/* Suspend the continuous counter task so it stops accessing the shared variable. */
		vTaskSuspend( xContinousIncrementHandle );

		/* Reset the variable. */
		ulCounter = ( unsigned long ) 0;

		/* Resume the limited count task which has a higher priority than us.
		We should therefore not return from this call until the limited count
		task has suspended itself with a known value in the counter variable. */
		vTaskResume( xLimitedIncrementHandle );

		/* Does the counter variable have the expected value? */
		if( ulCounter != priMAX_COUNT )
		{
			sError = pdTRUE;
		}

		if( sError == pdFALSE )
		{
			/* If no errors have occurred then increment the check variable. */
			portENTER_CRITICAL();
				usCheckVariable++;
			portEXIT_CRITICAL();
		}

		/* Resume the continuous count task and do it all again. */
		vTaskResume( xContinousIncrementHandle );
	}
}
/*-----------------------------------------------------------*/

static portTASK_FUNCTION( vQueueSendWhenSuspendedTask, pvParameters )
{
static unsigned long ulValueToSend = ( unsigned long ) 0;

	/* Just to stop warning messages. */
	( void ) pvParameters;

	for( ;; )
	{
		vTaskSuspendAll();
		{
			/* We must not block while the scheduler is suspended! */
			if( xQueueSend( xSuspendedTestQueue, ( void * ) &ulValueToSend, priNO_BLOCK ) != pdTRUE )
			{
				xSuspendedQueueSendError = pdTRUE;
			}
		}
		xTaskResumeAll();

		vTaskDelay( priSLEEP_TIME );

		++ulValueToSend;
	}
}
/*-----------------------------------------------------------*/

static portTASK_FUNCTION( vQueueReceiveWhenSuspendedTask, pvParameters )
{
static unsigned long ulExpectedValue = ( unsigned long ) 0, ulReceivedValue;
portBASE_TYPE xGotValue;

	/* Just to stop warning messages. */
	( void ) pvParameters;

	for( ;; )
	{
		do
		{
			/* Suspending the scheduler here is fairly pointless and
			undesirable for a normal application.  It is done here purely
			to test the scheduler.  The inner xTaskResumeAll() should
			never return pdTRUE as the scheduler is still locked by the
			outer call. */
			vTaskSuspendAll();
			{
				vTaskSuspendAll();
				{
					xGotValue = xQueueReceive( xSuspendedTestQueue, ( void * ) &ulReceivedValue, priNO_BLOCK );
				}
				if( xTaskResumeAll() )
				{
					xSuspendedQueueReceiveError = pdTRUE;
				}
			}
			xTaskResumeAll();

			#if configUSE_PREEMPTION == 0
			{
				taskYIELD();
			}
			#endif

		} while( xGotValue == pdFALSE );

		if( ulReceivedValue != ulExpectedValue )
		{
			xSuspendedQueueReceiveError = pdTRUE;
		}

		++ulExpectedValue;
	}
}
/*-----------------------------------------------------------*/

/* Called to check that all the created tasks are still running without error. */
portBASE_TYPE xAreDynamicPriorityTasksStillRunning( void )
{
/* Keep a history of the check variables so we know if it has been incremented
since the last call. */
static unsigned short usLastTaskCheck = ( unsigned short ) 0;
portBASE_TYPE xReturn = pdTRUE;

	/* Check the tasks are still running by ensuring the check variable
	is still incrementing. */

	if( usCheckVariable == usLastTaskCheck )
	{
		/* The check has not incremented so an error exists. */
		xReturn = pdFALSE;
	}

	if( xSuspendedQueueSendError == pdTRUE )
	{
		xReturn = pdFALSE;
	}

	if( xSuspendedQueueReceiveError == pdTRUE )
	{
		xReturn = pdFALSE;
	}

	usLastTaskCheck = usCheckVariable;
	return xReturn;
}
