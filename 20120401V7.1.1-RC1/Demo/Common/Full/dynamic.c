/*
    FreeRTOS V7.1.0 - Copyright (C) 2011 Real Time Engineers Ltd.
	

    ***************************************************************************
     *                                                                       *
     *    FreeRTOS tutorial books are available in pdf and paperback.        *
     *    Complete, revised, and edited pdf reference manuals are also       *
     *    available.                                                         *
     *                                                                       *
     *    Purchasing FreeRTOS documentation will not only help you, by       *
     *    ensuring you get running as quickly as possible and with an        *
     *    in-depth knowledge of how to use FreeRTOS, it will also help       *
     *    the FreeRTOS project to continue with its mission of providing     *
     *    professional grade, cross platform, de facto standard solutions    *
     *    for microcontrollers - completely free of charge!                  *
     *                                                                       *
     *    >>> See http://www.FreeRTOS.org/Documentation for details. <<<     *
     *                                                                       *
     *    Thank you for using FreeRTOS, and thank you for your support!      *
     *                                                                       *
    ***************************************************************************


    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation AND MODIFIED BY the FreeRTOS exception.
    >>>NOTE<<< The modification to the GPL is included to allow you to
    distribute a combined work that includes FreeRTOS without being obliged to
    provide the source code for proprietary components outside of the FreeRTOS
    kernel.  FreeRTOS is distributed in the hope that it will be useful, but
    WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
    or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
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

/**
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
 *
 * The final set of two tasks implements a third test.  This simply raises the
 * priority of a task while the scheduler is suspended.  Again this test was
 * added to exercise parts of the code not covered by the first test.
 *
 * \page Priorities dynamic.c
 * \ingroup DemoFiles
 * <HR>
 */

/*
Changes from V2.0.0

	+ Delay periods are now specified using variables and constants of
	  portTickType rather than unsigned long.
	+ Added a second, simple test that uses the functions 
	  vQueueReceiveWhenSuspendedTask() and vQueueSendWhenSuspendedTask().

Changes from V3.1.1

	+ Added a third simple test that uses the vTaskPrioritySet() function
	  while the scheduler is suspended.
	+ Modified the controller task slightly to test the calling of 
	  vTaskResumeAll() while the scheduler is suspended.
*/

#include <stdlib.h>

/* Scheduler include files. */
#include "FreeRTOS.h"
#include "task.h"
#include "semphr.h"

/* Demo app include files. */
#include "dynamic.h"
#include "print.h"

/* Function that implements the "limited count" task as described above. */
static void vLimitedIncrementTask( void * pvParameters );

/* Function that implements the "continuous count" task as described above. */
static void vContinuousIncrementTask( void * pvParameters );

/* Function that implements the controller task as described above. */
static void vCounterControlTask( void * pvParameters );

/* The simple test functions that check sending and receiving while the
scheduler is suspended. */
static void vQueueReceiveWhenSuspendedTask( void *pvParameters );
static void vQueueSendWhenSuspendedTask( void *pvParameters );

/* The simple test functions that check raising and lowering of task priorities
while the scheduler is suspended. */
static void prvChangePriorityWhenSuspendedTask( void *pvParameters );
static void prvChangePriorityHelperTask( void *pvParameters );


/* Demo task specific constants. */
#define priSTACK_SIZE				( ( unsigned short ) configMINIMAL_STACK_SIZE )
#define priSLEEP_TIME				( ( portTickType ) 50 )
#define priLOOPS					( 5 )
#define priMAX_COUNT				( ( unsigned long ) 0xff )
#define priNO_BLOCK					( ( portTickType ) 0 )
#define priSUSPENDED_QUEUE_LENGTH	( 1 )

/*-----------------------------------------------------------*/

/* Handles to the two counter tasks.  These could be passed in as parameters
to the controller task to prevent them having to be file scope. */
static xTaskHandle xContinuousIncrementHandle, xLimitedIncrementHandle, xChangePriorityWhenSuspendedHandle;

/* The shared counter variable.  This is passed in as a parameter to the two 
counter variables for demonstration purposes. */
static unsigned long ulCounter;

/* Variable used in a similar way by the test that checks the raising and
lowering of task priorities while the scheduler is suspended. */
static unsigned long ulPrioritySetCounter;

/* Variables used to check that the tasks are still operating without error.
Each complete iteration of the controller task increments this variable
provided no errors have been found.  The variable maintaining the same value
is therefore indication of an error. */
static unsigned short usCheckVariable = ( unsigned short ) 0;
static portBASE_TYPE xSuspendedQueueSendError = pdFALSE;
static portBASE_TYPE xSuspendedQueueReceiveError = pdFALSE;
static portBASE_TYPE xPriorityRaiseWhenSuspendedError = pdFALSE;

/* Queue used by the second test. */
xQueueHandle xSuspendedTestQueue;

/*-----------------------------------------------------------*/
/*
 * Start the seven tasks as described at the top of the file.
 * Note that the limited count task is given a higher priority.
 */
void vStartDynamicPriorityTasks( void )
{
	xSuspendedTestQueue = xQueueCreate( priSUSPENDED_QUEUE_LENGTH, sizeof( unsigned long ) );
	xTaskCreate( vContinuousIncrementTask, "CONT_INC", priSTACK_SIZE, ( void * ) &ulCounter, tskIDLE_PRIORITY, &xContinuousIncrementHandle );
	xTaskCreate( vLimitedIncrementTask, "LIM_INC", priSTACK_SIZE, ( void * ) &ulCounter, tskIDLE_PRIORITY + 1, &xLimitedIncrementHandle );
	xTaskCreate( vCounterControlTask, "C_CTRL", priSTACK_SIZE, NULL, tskIDLE_PRIORITY, NULL );
	xTaskCreate( vQueueSendWhenSuspendedTask, "SUSP_SEND", priSTACK_SIZE, NULL, tskIDLE_PRIORITY, NULL );
	xTaskCreate( vQueueReceiveWhenSuspendedTask, "SUSP_RECV", priSTACK_SIZE, NULL, tskIDLE_PRIORITY, NULL );
	xTaskCreate( prvChangePriorityWhenSuspendedTask, "1st_P_CHANGE", priSTACK_SIZE, NULL, tskIDLE_PRIORITY + 1, NULL );
	xTaskCreate( prvChangePriorityHelperTask, "2nd_P_CHANGE", priSTACK_SIZE, NULL, tskIDLE_PRIORITY, &xChangePriorityWhenSuspendedHandle );
}
/*-----------------------------------------------------------*/

/*
 * Just loops around incrementing the shared variable until the limit has been
 * reached.  Once the limit has been reached it suspends itself. 
 */
static void vLimitedIncrementTask( void * pvParameters )
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
static void vContinuousIncrementTask( void * pvParameters )
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

		#if configUSE_PREEMPTION == 0
			taskYIELD();
		#endif
	}
}
/*-----------------------------------------------------------*/

/*
 * Controller task as described above.
 */
static void vCounterControlTask( void * pvParameters )
{
unsigned long ulLastCounter;
short sLoops;
short sError = pdFALSE;
const char * const pcTaskStartMsg = "Priority manipulation tasks started.\r\n";
const char * const pcTaskFailMsg = "Priority manipulation Task Failed\r\n";

	/* Just to stop warning messages. */
	( void ) pvParameters;

	/* Queue a message for printing to say the task has started. */
	vPrintDisplayMessage( &pcTaskStartMsg );

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
			vTaskSuspend( xContinuousIncrementHandle );
				ulLastCounter = ulCounter;
			vTaskResume( xContinuousIncrementHandle );
			
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
					xTaskResumeAll();
						vPrintDisplayMessage( &pcTaskFailMsg );
					vTaskSuspendAll();
				}
			}
			xTaskResumeAll();
		}


		/* Second section: */

		/* Suspend the continuous counter task so it stops accessing the shared variable. */
		vTaskSuspend( xContinuousIncrementHandle );

		/* Reset the variable. */
		ulCounter = ( unsigned long ) 0;

		/* Resume the limited count task which has a higher priority than us.
		We should therefore not return from this call until the limited count
		task has suspended itself with a known value in the counter variable. 
		The scheduler suspension is not necessary but is included for test
		purposes. */
		vTaskSuspendAll();
			vTaskResume( xLimitedIncrementHandle );
		xTaskResumeAll();

		/* Does the counter variable have the expected value? */
		if( ulCounter != priMAX_COUNT )
		{
			sError = pdTRUE;
			vPrintDisplayMessage( &pcTaskFailMsg );
		}

		if( sError == pdFALSE )
		{
			/* If no errors have occurred then increment the check variable. */
			portENTER_CRITICAL();
				usCheckVariable++;
			portEXIT_CRITICAL();
		}

		#if configUSE_PREEMPTION == 0
			taskYIELD();
		#endif

		/* Resume the continuous count task and do it all again. */
		vTaskResume( xContinuousIncrementHandle );
	}
}
/*-----------------------------------------------------------*/

static void vQueueSendWhenSuspendedTask( void *pvParameters )
{
static unsigned long ulValueToSend = ( unsigned long ) 0;
const char * const pcTaskStartMsg = "Queue send while suspended task started.\r\n";
const char * const pcTaskFailMsg = "Queue send while suspended failed.\r\n";

	/* Just to stop warning messages. */
	( void ) pvParameters;

	/* Queue a message for printing to say the task has started. */
	vPrintDisplayMessage( &pcTaskStartMsg );

	for( ;; )
	{
		vTaskSuspendAll();
		{
			/* We must not block while the scheduler is suspended! */
			if( xQueueSend( xSuspendedTestQueue, ( void * ) &ulValueToSend, priNO_BLOCK ) != pdTRUE )
			{
				if( xSuspendedQueueSendError == pdFALSE )
				{
					xTaskResumeAll();
						vPrintDisplayMessage( &pcTaskFailMsg );
					vTaskSuspendAll();
				}

				xSuspendedQueueSendError = pdTRUE;
			}
		}
		xTaskResumeAll();

		vTaskDelay( priSLEEP_TIME );

		++ulValueToSend;
	}
}
/*-----------------------------------------------------------*/

static void vQueueReceiveWhenSuspendedTask( void *pvParameters )
{
static unsigned long ulExpectedValue = ( unsigned long ) 0, ulReceivedValue;
const char * const pcTaskStartMsg = "Queue receive while suspended task started.\r\n";
const char * const pcTaskFailMsg = "Queue receive while suspended failed.\r\n";
portBASE_TYPE xGotValue;

	/* Just to stop warning messages. */
	( void ) pvParameters;

	/* Queue a message for printing to say the task has started. */
	vPrintDisplayMessage( &pcTaskStartMsg );

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
				taskYIELD();
			#endif

		} while( xGotValue == pdFALSE );

		if( ulReceivedValue != ulExpectedValue )
		{
			if( xSuspendedQueueReceiveError == pdFALSE )
			{
				vPrintDisplayMessage( &pcTaskFailMsg );
			}
			xSuspendedQueueReceiveError = pdTRUE;
		}

		++ulExpectedValue;
	}
}
/*-----------------------------------------------------------*/

static void prvChangePriorityWhenSuspendedTask( void *pvParameters )
{
const char * const pcTaskStartMsg = "Priority change when suspended task started.\r\n";
const char * const pcTaskFailMsg = "Priority change when suspended task failed.\r\n";

	/* Just to stop warning messages. */
	( void ) pvParameters;

	/* Queue a message for printing to say the task has started. */
	vPrintDisplayMessage( &pcTaskStartMsg );	
	
	for( ;; )
	{
		/* Start with the counter at 0 so we know what the counter should be
		when we check it next. */
		ulPrioritySetCounter = ( unsigned long ) 0;

		/* Resume the helper task.  At this time it has a priority lower than
		ours so no context switch should occur. */
		vTaskResume( xChangePriorityWhenSuspendedHandle );

		/* Check to ensure the task just resumed has not executed. */
		portENTER_CRITICAL();
		{
			if( ulPrioritySetCounter != ( unsigned long ) 0 )
			{
				xPriorityRaiseWhenSuspendedError = pdTRUE;
				vPrintDisplayMessage( &pcTaskFailMsg );
			}
		}
		portEXIT_CRITICAL();

		/* Now try raising the priority while the scheduler is suspended. */
		vTaskSuspendAll();
		{
			vTaskPrioritySet( xChangePriorityWhenSuspendedHandle, ( configMAX_PRIORITIES - 1 ) );

			/* Again, even though the helper task has a priority greater than 
			ours, it should not have executed yet because the scheduler is
			suspended. */
			portENTER_CRITICAL();
			{
				if( ulPrioritySetCounter != ( unsigned long ) 0 )
				{
					xPriorityRaiseWhenSuspendedError = pdTRUE;
					vPrintDisplayMessage( &pcTaskFailMsg );
				}
			}
			portEXIT_CRITICAL();
		}
		xTaskResumeAll();
		
		/* Now the scheduler has been resumed the helper task should 
		immediately preempt us and execute.  When it executes it will increment
		the ulPrioritySetCounter exactly once before suspending itself.

		We should now always find the counter set to 1. */
		portENTER_CRITICAL();
		{
			if( ulPrioritySetCounter != ( unsigned long ) 1 )
			{
				xPriorityRaiseWhenSuspendedError = pdTRUE;
				vPrintDisplayMessage( &pcTaskFailMsg );
			}
		}
		portEXIT_CRITICAL();

		/* Delay until we try this again. */		
		vTaskDelay( priSLEEP_TIME * 2 );
		
		/* Set the priority of the helper task back ready for the next 
		execution of this task. */
		vTaskSuspendAll();
			vTaskPrioritySet( xChangePriorityWhenSuspendedHandle, tskIDLE_PRIORITY );				
		xTaskResumeAll();				
	}
}
/*-----------------------------------------------------------*/

static void prvChangePriorityHelperTask( void *pvParameters )
{
	/* Just to stop warning messages. */
	( void ) pvParameters;

	for( ;; )
	{
		/* This is the helper task for prvChangePriorityWhenSuspendedTask().
		It has it's priority raised and lowered.  When it runs it simply 
		increments the counter then suspends itself again.  This allows
		prvChangePriorityWhenSuspendedTask() to know how many times it has
		executed. */
		ulPrioritySetCounter++;
		vTaskSuspend( NULL );
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

	if( xPriorityRaiseWhenSuspendedError == pdTRUE )
	{
		xReturn = pdFALSE;
	}

	usLastTaskCheck = usCheckVariable;
	return xReturn;
}




