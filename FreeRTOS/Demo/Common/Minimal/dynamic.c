/*
    FreeRTOS V8.2.3 - Copyright (C) 2015 Real Time Engineers Ltd.
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
 * The first test creates three tasks - two counter tasks (one continuous count
 * and one limited count) and one controller.  A "count" variable is shared
 * between all three tasks.  The two counter tasks should never be in a "ready"
 * state at the same time.  The controller task runs at the same priority as
 * the continuous count task, and at a lower priority than the limited count
 * task.
 *
 * One counter task loops indefinitely, incrementing the shared count variable
 * on each iteration.  To ensure it has exclusive access to the variable it
 * raises its priority above that of the controller task before each
 * increment, lowering it again to its original priority before starting the
 * next iteration.
 *
 * The other counter task increments the shared count variable on each
 * iteration of its loop until the count has reached a limit of 0xff - at
 * which point it suspends itself.  It will not start a new loop until the
 * controller task has made it "ready" again by calling vTaskResume().
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
 * The limited count task is then woken from its suspension by a call to
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
#define priSLEEP_TIME				pdMS_TO_TICKS( 128 )
#define priLOOPS					( 5 )
#define priMAX_COUNT				( ( uint32_t ) 0xff )
#define priNO_BLOCK					( ( TickType_t ) 0 )
#define priSUSPENDED_QUEUE_LENGTH	( 1 )

/*-----------------------------------------------------------*/

/* Handles to the two counter tasks.  These could be passed in as parameters
to the controller task to prevent them having to be file scope. */
static TaskHandle_t xContinuousIncrementHandle, xLimitedIncrementHandle;

/* The shared counter variable.  This is passed in as a parameter to the two
counter variables for demonstration purposes. */
static volatile uint32_t ulCounter;

/* Variables used to check that the tasks are still operating without error.
Each complete iteration of the controller task increments this variable
provided no errors have been found.  The variable maintaining the same value
is therefore indication of an error. */
static volatile uint16_t usCheckVariable = ( uint16_t ) 0;
static volatile BaseType_t xSuspendedQueueSendError = pdFALSE;
static volatile BaseType_t xSuspendedQueueReceiveError = pdFALSE;

/* Queue used by the second test. */
QueueHandle_t xSuspendedTestQueue;

/* The value the queue receive task expects to receive next.  This is file
scope so xAreDynamicPriorityTasksStillRunning() can ensure it is still
incrementing. */
static uint32_t ulExpectedValue = ( uint32_t ) 0;

/*-----------------------------------------------------------*/
/*
 * Start the three tasks as described at the top of the file.
 * Note that the limited count task is given a higher priority.
 */
void vStartDynamicPriorityTasks( void )
{
	xSuspendedTestQueue = xQueueCreate( priSUSPENDED_QUEUE_LENGTH, sizeof( uint32_t ) );

	/* vQueueAddToRegistry() adds the queue to the queue registry, if one is
	in use.  The queue registry is provided as a means for kernel aware
	debuggers to locate queues and has no purpose if a kernel aware debugger
	is not being used.  The call to vQueueAddToRegistry() will be removed
	by the pre-processor if configQUEUE_REGISTRY_SIZE is not defined or is
	defined to be less than 1. */
	vQueueAddToRegistry( xSuspendedTestQueue, "Suspended_Test_Queue" );

	xTaskCreate( vContinuousIncrementTask, "CNT_INC", priSTACK_SIZE, ( void * ) &ulCounter, tskIDLE_PRIORITY, &xContinuousIncrementHandle );
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
uint32_t *pulCounter;

	/* Take a pointer to the shared variable from the parameters passed into
	the task. */
	pulCounter = ( uint32_t * ) pvParameters;

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
volatile uint32_t *pulCounter;
UBaseType_t uxOurPriority;

	/* Take a pointer to the shared variable from the parameters passed into
	the task. */
	pulCounter = ( uint32_t * ) pvParameters;

	/* Query our priority so we can raise it when exclusive access to the
	shared variable is required. */
	uxOurPriority = uxTaskPriorityGet( NULL );

	for( ;; )
	{
		/* Raise the priority above the controller task to ensure a context
		switch does not occur while the variable is being accessed. */
		vTaskPrioritySet( NULL, uxOurPriority + 1 );
		{
			configASSERT( ( uxTaskPriorityGet( NULL ) == ( uxOurPriority + 1 ) ) );
			( *pulCounter )++;
		}
		vTaskPrioritySet( NULL, uxOurPriority );

		#if( configUSE_PREEMPTION == 0 )
			taskYIELD();
		#endif

		configASSERT( ( uxTaskPriorityGet( NULL ) == uxOurPriority ) );
	}
}
/*-----------------------------------------------------------*/

/*
 * Controller task as described above.
 */
static portTASK_FUNCTION( vCounterControlTask, pvParameters )
{
uint32_t ulLastCounter;
short sLoops;
short sError = pdFALSE;

	/* Just to stop warning messages. */
	( void ) pvParameters;

	for( ;; )
	{
		/* Start with the counter at zero. */
		ulCounter = ( uint32_t ) 0;

		/* First section : */

		/* Check the continuous count task is running. */
		for( sLoops = 0; sLoops < priLOOPS; sLoops++ )
		{
			/* Suspend the continuous count task so we can take a mirror of the
			shared variable without risk of corruption.  This is not really
			needed as the other task raises its priority above this task's
			priority. */
			vTaskSuspend( xContinuousIncrementHandle );
			{
				#if( INCLUDE_eTaskGetState == 1 )
				{
					configASSERT( eTaskGetState( xContinuousIncrementHandle ) == eSuspended );
				}
				#endif /* INCLUDE_eTaskGetState */

				ulLastCounter = ulCounter;
			}
			vTaskResume( xContinuousIncrementHandle );

			#if( configUSE_PREEMPTION == 0 )
				taskYIELD();
			#endif

			#if( INCLUDE_eTaskGetState == 1 )
			{
				configASSERT( eTaskGetState( xContinuousIncrementHandle ) == eReady );
			}
			#endif /* INCLUDE_eTaskGetState */

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

		/* Suspend the continuous counter task so it stops accessing the shared
		variable. */
		vTaskSuspend( xContinuousIncrementHandle );

		/* Reset the variable. */
		ulCounter = ( uint32_t ) 0;

		#if( INCLUDE_eTaskGetState == 1 )
		{
			configASSERT( eTaskGetState( xLimitedIncrementHandle ) == eSuspended );
		}
		#endif /* INCLUDE_eTaskGetState */

		/* Resume the limited count task which has a higher priority than us.
		We should therefore not return from this call until the limited count
		task has suspended itself with a known value in the counter variable. */
		vTaskResume( xLimitedIncrementHandle );

		#if( configUSE_PREEMPTION == 0 )
			taskYIELD();
		#endif

		/* This task should not run again until xLimitedIncrementHandle has
		suspended itself. */
		#if( INCLUDE_eTaskGetState == 1 )
		{
			configASSERT( eTaskGetState( xLimitedIncrementHandle ) == eSuspended );
		}
		#endif /* INCLUDE_eTaskGetState */

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
		vTaskResume( xContinuousIncrementHandle );

		#if( configUSE_PREEMPTION == 0 )
			taskYIELD();
		#endif
	}
}
/*-----------------------------------------------------------*/

static portTASK_FUNCTION( vQueueSendWhenSuspendedTask, pvParameters )
{
static uint32_t ulValueToSend = ( uint32_t ) 0;

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
uint32_t ulReceivedValue;
BaseType_t xGotValue;

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
				if( xTaskResumeAll() != pdFALSE )
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

		if( xSuspendedQueueReceiveError != pdTRUE )
		{
			/* Only increment the variable if an error has not occurred.  This
			allows xAreDynamicPriorityTasksStillRunning() to check for stalled
			tasks as well as explicit errors. */
			++ulExpectedValue;
		}
	}
}
/*-----------------------------------------------------------*/

/* Called to check that all the created tasks are still running without error. */
BaseType_t xAreDynamicPriorityTasksStillRunning( void )
{
/* Keep a history of the check variables so we know if it has been incremented
since the last call. */
static uint16_t usLastTaskCheck = ( uint16_t ) 0;
static uint32_t ulLastExpectedValue = ( uint32_t ) 0U;
BaseType_t xReturn = pdTRUE;

	/* Check the tasks are still running by ensuring the check variable
	is still incrementing. */

	if( usCheckVariable == usLastTaskCheck )
	{
		/* The check has not incremented so an error exists. */
		xReturn = pdFALSE;
	}

	if( ulExpectedValue == ulLastExpectedValue )
	{
		/* The value being received by the queue receive task has not
		incremented so an error exists. */
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
	ulLastExpectedValue = ulExpectedValue;

	return xReturn;
}
