/*
    FreeRTOS V7.1.1 - Copyright (C) 2012 Real Time Engineers Ltd.
	

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
    
    ***************************************************************************
     *                                                                       *
     *    Having a problem?  Start by reading the FAQ "My application does   *
     *    not run, what could be wrong?                                      *
     *                                                                       *
     *    http://www.FreeRTOS.org/FAQHelp.html                               *
     *                                                                       *
    ***************************************************************************

    
    http://www.FreeRTOS.org - Documentation, training, latest information, 
    license and contact details.
    
    http://www.FreeRTOS.org/plus - A selection of FreeRTOS ecosystem products,
    including FreeRTOS+Trace - an indispensable productivity tool.

    Real Time Engineers ltd license FreeRTOS to High Integrity Systems, who sell 
    the code with commercial support, indemnification, and middleware, under 
    the OpenRTOS brand: http://www.OpenRTOS.com.  High Integrity Systems also
    provide a safety engineered and independently SIL3 certified version under 
    the SafeRTOS brand: http://www.SafeRTOS.com.
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

/* In this version the tick period is very long, so the short delay cannot be
for too many ticks, or the check task will execute and find that the recmutex
tasks have not completed their functionality and then signal an error.  The
delay does however have to be long enough to allow the lower priority tasks
a chance of executing - this is basically achieved by reducing the number
of times the loop that takes/gives the recursive mutex executes. */
#define recmuMAX_COUNT					( 2 )
#define recmuSHORT_DELAY				( 20 )
#define recmuNO_DELAY					( ( portTickType ) 0 )
#define recmuFIVE_TICK_DELAY			( ( portTickType ) 5 )

/* The three tasks as described at the top of this file. */
static void prvRecursiveMutexControllingTask( void *pvParameters );
static void prvRecursiveMutexBlockingTask( void *pvParameters );
static void prvRecursiveMutexPollingTask( void *pvParameters );

/* The mutex used by the demo. */
static xSemaphoreHandle xMutex;

/* Variables used to detect and latch errors. */
static volatile portBASE_TYPE xErrorOccurred = pdFALSE, xControllingIsSuspended = pdFALSE, xBlockingIsSuspended = pdFALSE;
static volatile unsigned portBASE_TYPE uxControllingCycles = 0, uxBlockingCycles = 0, uxPollingCycles = 0;

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
		xTaskCreate( prvRecursiveMutexControllingTask, ( signed portCHAR * ) "Rec1Ctrl", configMINIMAL_STACK_SIZE, NULL, recmuCONTROLLING_TASK_PRIORITY, &xControllingTaskHandle );
        xTaskCreate( prvRecursiveMutexBlockingTask, ( signed portCHAR * ) "Rec2Blck", configMINIMAL_STACK_SIZE, NULL, recmuBLOCKING_TASK_PRIORITY, &xBlockingTaskHandle );
        xTaskCreate( prvRecursiveMutexPollingTask, ( signed portCHAR * ) "Rec3Poll", configMINIMAL_STACK_SIZE, NULL, recmuPOLLING_TASK_PRIORITY, NULL );
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
		it.   The first time through, the mutex will not have been used yet,
		subsequent times through, at this point the mutex will be held by the
		polling task. */
		if( xSemaphoreGiveRecursive( xMutex ) == pdPASS )
		{
			xErrorOccurred = pdTRUE;
		}

		for( ux = 0; ux < recmuMAX_COUNT; ux++ )
		{
			/* We should now be able to take the mutex as many times as
			we like.
			
			The first time through the mutex will be immediately available, on
			subsequent times through the mutex will be held by the polling task
			at this point and this Take will cause the polling task to inherit
			the priority of this task.  In this case the block time must be
			long enough to ensure the polling task will execute again before the
			block time expires.  If the block time does expire then the error
			flag will be set here. */
			if( xSemaphoreTakeRecursive( xMutex, recmuFIVE_TICK_DELAY ) != pdPASS )
			{
				xErrorOccurred = pdTRUE;
			}

			/* Ensure the other task attempting to access the mutex (and the
			other demo tasks) are able to execute to ensure they either block
			(where a block time is specified) or return an error (where no 
			block time is specified) as the mutex is held by this task. */
			vTaskDelay( recmuSHORT_DELAY );
		}

		/* For each time we took the mutex, give it back. */
		for( ux = 0; ux < recmuMAX_COUNT; ux++ )
		{
			/* Ensure the other task attempting to access the mutex (and the
			other demo tasks) are able to execute. */
			vTaskDelay( recmuSHORT_DELAY );

			/* We should now be able to give the mutex as many times as we
			took it.  When the mutex is available again the Blocking task
			should be unblocked but not run because it has a lower priority
			than this task.  The polling task should also not run at this point
			as it too has a lower priority than this task. */
			if( xSemaphoreGiveRecursive( xMutex ) != pdPASS )
			{
				xErrorOccurred = pdTRUE;
			}
		}

		/* Having given it back the same number of times as it was taken, we
		should no longer be the mutex owner, so the next give should fail. */
		if( xSemaphoreGiveRecursive( xMutex ) == pdPASS )
		{
			xErrorOccurred = pdTRUE;
		}

		/* Keep count of the number of cycles this task has performed so a 
		stall can be detected. */
		uxControllingCycles++;

		/* Suspend ourselves so the blocking task can execute. */
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
		/* This task will run while the controlling task is blocked, and the
		controlling task will block only once it has the mutex - therefore
		this call should block until the controlling task has given up the 
		mutex, and not actually execute	past this call until the controlling 
		task is suspended. */
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
		the blocking task has suspended itself, which in turn should only
		happen when the controlling task is also suspended. */
		if( xSemaphoreTakeRecursive( xMutex, recmuNO_DELAY ) == pdPASS )
		{
			/* Is the blocking task suspended? */
			if( ( xBlockingIsSuspended != pdTRUE ) || ( xControllingIsSuspended != pdTRUE ) )
			{
				xErrorOccurred = pdTRUE;
			}
			else
			{
				/* Keep count of the number of cycles this task has performed 
				so a stall can be detected. */
				uxPollingCycles++;

				/* We can resume the other tasks here even though they have a
				higher priority than the polling task.  When they execute they
				will attempt to obtain the mutex but fail because the polling
				task is still the mutex holder.  The polling task (this task)
				will then inherit the higher priority.  The Blocking task will
				block indefinitely when it attempts to obtain the mutex, the
				Controlling task will only block for a fixed period and an
				error will be latched if the polling task has not returned the
				mutex by the time this fixed period has expired. */
				vTaskResume( xBlockingTaskHandle );
                vTaskResume( xControllingTaskHandle );
			
				/* The other two tasks should now have executed and no longer
				be suspended. */
				if( ( xBlockingIsSuspended == pdTRUE ) || ( xControllingIsSuspended == pdTRUE ) )
				{
					xErrorOccurred = pdTRUE;
				}				
			
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




