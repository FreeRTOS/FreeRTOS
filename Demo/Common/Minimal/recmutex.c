/*
    FreeRTOS V6.0.3 - Copyright (C) 2010 Real Time Engineers Ltd.

    ***************************************************************************
    *                                                                         *
    * If you are:                                                             *
    *                                                                         *
    *    + New to FreeRTOS,                                                   *
    *    + Wanting to learn FreeRTOS or multitasking in general quickly       *
    *    + Looking for basic training,                                        *
    *    + Wanting to improve your FreeRTOS skills and productivity           *
    *                                                                         *
    * then take a look at the FreeRTOS eBook                                  *
    *                                                                         *
    *        "Using the FreeRTOS Real Time Kernel - a Practical Guide"        *
    *                  http://www.FreeRTOS.org/Documentation                  *
    *                                                                         *
    * A pdf reference manual is also available.  Both are usually delivered   *
    * to your inbox within 20 minutes to two hours when purchased between 8am *
    * and 8pm GMT (although please allow up to 24 hours in case of            *
    * exceptional circumstances).  Thank you for your support!                *
    *                                                                         *
    ***************************************************************************

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation AND MODIFIED BY the FreeRTOS exception.
    ***NOTE*** The exception to the GPL is included to allow you to distribute
    a combined work that includes FreeRTOS without being obliged to provide the
    source code for proprietary components outside of the FreeRTOS kernel.
    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT
    ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
    FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
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

/*
	The tasks defined on this page demonstrate the use of recursive mutexes.

	For recursive mutex functionality the created mutex should be created using
	xSemaphoreCreateRecursiveMutex(), then be manipulated
	using the xSemaphoreTakeRecursive() and xSemaphoreGiveRecursive() API
	functions.

	This demo creates three tasks all of which access the same recursive mutex:

	prvRecursiveMutexControllingTask() has the highest priority so executes 
	first and grabs the mutex.  It then performs some recursive accesses - 
	between each of which it sleeps for a short period to let the lower 
	priority tasks execute.  When it has completed its demo functionality
	it gives the mutex back before suspending itself.

	prvRecursiveMutexBlockingTask() attempts to access the mutex by performing
	a blocking 'take'.  The blocking task has a lower priority than the 
	controlling	task so by the time it executes the mutex has already been
	taken by the controlling task,  causing the blocking task to block.  It 
	does not unblock until the controlling task has given the mutex back, 
	and it does not actually run until the controlling task has suspended 
	itself (due to the relative priorities).  When it eventually does obtain
	the mutex all it does is give the mutex back prior to also suspending 
	itself.  At this point both the controlling task and the blocking task are 
	suspended.

	prvRecursiveMutexPollingTask() runs at the idle priority.  It spins round
	a tight loop attempting to obtain the mutex with a non-blocking call.  As
	the lowest priority task it will not successfully obtain the mutex until
	both the controlling and blocking tasks are suspended.  Once it eventually 
	does obtain the mutex it first unsuspends both the controlling task and
	blocking task prior to giving the mutex back - resulting in the polling
	task temporarily inheriting the controlling tasks priority.
*/

/* Scheduler include files. */
#include "FreeRTOS.h"
#include "task.h"
#include "semphr.h"

/* Demo app include files. */
#include "recmutex.h"

/* Priorities assigned to the three tasks. */
#define recmuCONTROLLING_TASK_PRIORITY	( tskIDLE_PRIORITY + 2 )
#define recmuBLOCKING_TASK_PRIORITY		( tskIDLE_PRIORITY + 1 )
#define recmuPOLLING_TASK_PRIORITY		( tskIDLE_PRIORITY + 0 )

/* The recursive call depth. */
#define recmuMAX_COUNT					( 10 )

/* Misc. */
#define recmuSHORT_DELAY				( 20 / portTICK_RATE_MS )
#define recmuNO_DELAY					( ( portTickType ) 0 )
#define recmuTWO_TICK_DELAY				( ( portTickType ) 2 )

/* The three tasks as described at the top of this file. */
static void prvRecursiveMutexControllingTask( void *pvParameters );
static void prvRecursiveMutexBlockingTask( void *pvParameters );
static void prvRecursiveMutexPollingTask( void *pvParameters );

/* The mutex used by the demo. */
static xSemaphoreHandle xMutex;

/* Variables used to detect and latch errors. */
static volatile portBASE_TYPE xErrorOccurred = pdFALSE, xControllingIsSuspended = pdFALSE, xBlockingIsSuspended = pdFALSE;
static volatile unsigned portBASE_TYPE uxControllingCycles = 0, uxBlockingCycles, uxPollingCycles = 0;

/* Handles of the two higher priority tasks, required so they can be resumed 
(unsuspended). */
static xTaskHandle xControllingTaskHandle, xBlockingTaskHandle;

/*-----------------------------------------------------------*/

void vStartRecursiveMutexTasks( void )
{
	/* Just creates the mutex and the three tasks. */

	xMutex = xSemaphoreCreateRecursiveMutex();

	/* vQueueAddToRegistry() adds the mutex to the registry, if one is
	in use.  The registry is provided as a means for kernel aware 
	debuggers to locate mutex and has no purpose if a kernel aware debugger
	is not being used.  The call to vQueueAddToRegistry() will be removed
	by the pre-processor if configQUEUE_REGISTRY_SIZE is not defined or is 
	defined to be less than 1. */
	vQueueAddToRegistry( ( xQueueHandle ) xMutex, ( signed portCHAR * ) "Recursive_Mutex" );


	if( xMutex != NULL )
	{
		xTaskCreate( prvRecursiveMutexControllingTask, ( signed portCHAR * ) "Rec1", configMINIMAL_STACK_SIZE, NULL, recmuCONTROLLING_TASK_PRIORITY, &xControllingTaskHandle );
        xTaskCreate( prvRecursiveMutexBlockingTask, ( signed portCHAR * ) "Rec2", configMINIMAL_STACK_SIZE, NULL, recmuBLOCKING_TASK_PRIORITY, &xBlockingTaskHandle );
        xTaskCreate( prvRecursiveMutexPollingTask, ( signed portCHAR * ) "Rec3", configMINIMAL_STACK_SIZE, NULL, recmuPOLLING_TASK_PRIORITY, NULL );
	}
}
/*-----------------------------------------------------------*/

static void prvRecursiveMutexControllingTask( void *pvParameters )
{
unsigned portBASE_TYPE ux;

	/* Just to remove compiler warning. */
	( void ) pvParameters;

	for( ;; )
	{
		/* Should not be able to 'give' the mutex, as we have not yet 'taken'
		it. */
		if( xSemaphoreGiveRecursive( xMutex ) == pdPASS )
		{
			xErrorOccurred = pdTRUE;
		}

		for( ux = 0; ux < recmuMAX_COUNT; ux++ )
		{
			/* We should now be able to take the mutex as many times as
			we like.  A one tick delay is used so the polling task will
			inherit our priority on all but the first cycle of this task. 
			If we did not block attempting to receive the mutex then no
			priority inheritance would occur. */
			if( xSemaphoreTakeRecursive( xMutex, recmuTWO_TICK_DELAY ) != pdPASS )
			{
				xErrorOccurred = pdTRUE;
			}

			/* Ensure the other task attempting to access the mutex (and the
			other demo tasks) are able to execute. */
			vTaskDelay( recmuSHORT_DELAY );
		}

		/* For each time we took the mutex, give it back. */
		for( ux = 0; ux < recmuMAX_COUNT; ux++ )
		{
			/* Ensure the other task attempting to access the mutex (and the
			other demo tasks) are able to execute. */
			vTaskDelay( recmuSHORT_DELAY );

			/* We should now be able to give the mutex as many times as we
			took it. */
			if( xSemaphoreGiveRecursive( xMutex ) != pdPASS )
			{
				xErrorOccurred = pdTRUE;
			}
		}

		/* Having given it back the same number of times as it was taken, we
		should no longer be the mutex owner, so the next give sh ould fail. */
		if( xSemaphoreGiveRecursive( xMutex ) == pdPASS )
		{
			xErrorOccurred = pdTRUE;
		}

		/* Keep count of the number of cycles this task has performed so a 
		stall can be detected. */
		uxControllingCycles++;

		/* Suspend ourselves to the blocking task can execute. */
		xControllingIsSuspended = pdTRUE;
		vTaskSuspend( NULL );
		xControllingIsSuspended = pdFALSE;
	}
}
/*-----------------------------------------------------------*/

static void prvRecursiveMutexBlockingTask( void *pvParameters )
{
	/* Just to remove compiler warning. */
	( void ) pvParameters;

	for( ;; )
	{
		/* Attempt to obtain the mutex.  We should block until the 
		controlling task has given up the mutex, and not actually execute
		past this call until the controlling task is suspended. */
		if( xSemaphoreTakeRecursive( xMutex, portMAX_DELAY ) == pdPASS )
		{
			if( xControllingIsSuspended != pdTRUE )
			{
				/* Did not expect to execute until the controlling task was
				suspended. */
				xErrorOccurred = pdTRUE;
			}
			else
			{
				/* Give the mutex back before suspending ourselves to allow
				the polling task to obtain the mutex. */
				if( xSemaphoreGiveRecursive( xMutex ) != pdPASS )
				{
					xErrorOccurred = pdTRUE;
				}

				xBlockingIsSuspended = pdTRUE;
				vTaskSuspend( NULL );
				xBlockingIsSuspended = pdFALSE;
			}
		}
		else
		{
			/* We should not leave the xSemaphoreTakeRecursive() function
			until the mutex was obtained. */
			xErrorOccurred = pdTRUE;
		}

		/* The controlling and blocking tasks should be in lock step. */
		if( uxControllingCycles != ( uxBlockingCycles + 1 ) )
		{
			xErrorOccurred = pdTRUE;
		}

		/* Keep count of the number of cycles this task has performed so a 
		stall can be detected. */
		uxBlockingCycles++;
	}
}
/*-----------------------------------------------------------*/

static void prvRecursiveMutexPollingTask( void *pvParameters )
{
	/* Just to remove compiler warning. */
	( void ) pvParameters;

	for( ;; )
	{
		/* Keep attempting to obtain the mutex.  We should only obtain it when
		the blocking task has suspended itself. */
		if( xSemaphoreTakeRecursive( xMutex, recmuNO_DELAY ) == pdPASS )
		{
			/* Is the blocking task suspended? */
			if( xBlockingIsSuspended != pdTRUE )
			{
				xErrorOccurred = pdTRUE;
			}
			else
			{
				/* Keep count of the number of cycles this task has performed so 
				a stall can be detected. */
				uxPollingCycles++;

				/* We can resume the other tasks here even though they have a
				higher priority than the polling task.  When they execute they
				will attempt to obtain the mutex but fail because the polling
				task is still the mutex holder.  The polling task (this task)
				will then inherit the higher priority. */				
				vTaskResume( xBlockingTaskHandle );
                vTaskResume( xControllingTaskHandle );
			
				/* Release the mutex, disinheriting the higher priority again. */
				if( xSemaphoreGiveRecursive( xMutex ) != pdPASS )
				{
					xErrorOccurred = pdTRUE;
				}
			}
		}

		#if configUSE_PREEMPTION == 0
		{
			taskYIELD();
		}
		#endif
	}
}
/*-----------------------------------------------------------*/

/* This is called to check that all the created tasks are still running. */
portBASE_TYPE xAreRecursiveMutexTasksStillRunning( void )
{
portBASE_TYPE xReturn;
static unsigned portBASE_TYPE uxLastControllingCycles = 0, uxLastBlockingCycles = 0, uxLastPollingCycles = 0;

	/* Is the controlling task still cycling? */
	if( uxLastControllingCycles == uxControllingCycles )
	{
		xErrorOccurred = pdTRUE;
	}
	else
	{
		uxLastControllingCycles = uxControllingCycles;
	}

	/* Is the blocking task still cycling? */
	if( uxLastBlockingCycles == uxBlockingCycles )
	{
		xErrorOccurred = pdTRUE;
	}
	else
	{
		uxLastBlockingCycles = uxBlockingCycles;
	}

	/* Is the polling task still cycling? */
	if( uxLastPollingCycles == uxPollingCycles )
	{
		xErrorOccurred = pdTRUE;
	}
	else
	{
		uxLastPollingCycles = uxPollingCycles;
	}

	if( xErrorOccurred == pdTRUE )
	{
		xReturn = pdFAIL;
	}
	else
	{
		xReturn = pdTRUE;
	}

	return xReturn;
}




