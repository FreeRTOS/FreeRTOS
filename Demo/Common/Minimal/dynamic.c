/*
	FreeRTOS V4.0.1 - Copyright (C) 2003-2006 Richard Barry.

	This file is part of the FreeRTOS distribution.

	FreeRTOS is free software; you can redistribute it and/or modify
	it under the terms of the GNU General Public License as published by
	the Free Software Foundation; either version 2 of the License, or
	(at your option) any later version.

	FreeRTOS is distributed in the hope that it will be useful,
	but WITHOUT ANY WARRANTY; without even the implied warranty of
	MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
	GNU General Public License for more details.

	You should have received a copy of the GNU General Public License
	along with FreeRTOS; if not, write to the Free Software
	Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA

	A special exception to the GPL can be applied should you wish to distribute
	a combined work that includes FreeRTOS, without being obliged to provide
	the source code for any proprietary components.  See the licensing section 
	of http://www.FreeRTOS.org for full details of how and when the exception
	can be applied.

	***************************************************************************
	See http://www.FreeRTOS.org for documentation, latest information, license 
	and contact details.  Please ensure to read the configuration and relevant 
	port sections of the online documentation.
	***************************************************************************
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
#define priSTACK_SIZE				( ( unsigned portSHORT ) 128 )
#define priSLEEP_TIME				( ( portTickType ) 50 )
#define priLOOPS					( 5 )
#define priMAX_COUNT				( ( unsigned portLONG ) 0xff )
#define priNO_BLOCK					( ( portTickType ) 0 )
#define priSUSPENDED_QUEUE_LENGTH	( 1 )

/*-----------------------------------------------------------*/

/* Handles to the two counter tasks.  These could be passed in as parameters
to the controller task to prevent them having to be file scope. */
static xTaskHandle xContinousIncrementHandle, xLimitedIncrementHandle;

/* The shared counter variable.  This is passed in as a parameter to the two 
counter variables for demonstration purposes. */
static unsigned portLONG ulCounter;

/* Variables used to check that the tasks are still operating without error.
Each complete iteration of the controller task increments this variable
provided no errors have been found.  The variable maintaining the same value
is therefore indication of an error. */
static unsigned portSHORT usCheckVariable = ( unsigned portSHORT ) 0;
static portBASE_TYPE xSuspendedQueueSendError = pdFALSE;
static portBASE_TYPE xSuspendedQueueReceiveError = pdFALSE;

/* Queue used by the second test. */
xQueueHandle xSuspendedTestQueue;

/*-----------------------------------------------------------*/
/*
 * Start the three tasks as described at the top of the file.
 * Note that the limited count task is given a higher priority.
 */
void vStartDynamicPriorityTasks( void )
{
	xSuspendedTestQueue = xQueueCreate( priSUSPENDED_QUEUE_LENGTH, sizeof( unsigned portLONG ) );
	xTaskCreate( vContinuousIncrementTask, ( signed portCHAR * ) "CNT_INC", priSTACK_SIZE, ( void * ) &ulCounter, tskIDLE_PRIORITY, &xContinousIncrementHandle );
	xTaskCreate( vLimitedIncrementTask, ( signed portCHAR * ) "LIM_INC", priSTACK_SIZE, ( void * ) &ulCounter, tskIDLE_PRIORITY + 1, &xLimitedIncrementHandle );
	xTaskCreate( vCounterControlTask, ( signed portCHAR * ) "C_CTRL", priSTACK_SIZE, NULL, tskIDLE_PRIORITY, NULL );
	xTaskCreate( vQueueSendWhenSuspendedTask, ( signed portCHAR * ) "SUSP_TX", priSTACK_SIZE, NULL, tskIDLE_PRIORITY, NULL );
	xTaskCreate( vQueueReceiveWhenSuspendedTask, ( signed portCHAR * ) "SUSP_RX", priSTACK_SIZE, NULL, tskIDLE_PRIORITY, NULL );
}
/*-----------------------------------------------------------*/

/*
 * Just loops around incrementing the shared variable until the limit has been
 * reached.  Once the limit has been reached it suspends itself. 
 */
static portTASK_FUNCTION( vLimitedIncrementTask, pvParameters )
{
unsigned portLONG *pulCounter;

	/* Take a pointer to the shared variable from the parameters passed into
	the task. */
	pulCounter = ( unsigned portLONG * ) pvParameters;

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
unsigned portLONG *pulCounter;
unsigned portBASE_TYPE uxOurPriority;

	/* Take a pointer to the shared variable from the parameters passed into
	the task. */
	pulCounter = ( unsigned portLONG * ) pvParameters;

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
unsigned portLONG ulLastCounter;
portSHORT sLoops;
portSHORT sError = pdFALSE;

	/* Just to stop warning messages. */
	( void ) pvParameters;

	for( ;; )
	{
		/* Start with the counter at zero. */
		ulCounter = ( unsigned portLONG ) 0;

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
		ulCounter = ( unsigned portLONG ) 0;

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
static unsigned portLONG ulValueToSend = ( unsigned portLONG ) 0;

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
static unsigned portLONG ulExpectedValue = ( unsigned portLONG ) 0, ulReceivedValue;
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
static unsigned portSHORT usLastTaskCheck = ( unsigned portSHORT ) 0;
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
