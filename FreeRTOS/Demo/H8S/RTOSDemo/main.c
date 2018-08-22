/*
 * FreeRTOS Kernel V10.1.0
 * Copyright (C) 2018 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 * Creates all the demo application tasks, then starts the scheduler.  The WEB
 * documentation provides more details of the demo application tasks.
 *
 * Main.c also creates a task called "Check".  This only executes every three
 * seconds but has the highest priority so is guaranteed to get processor time.
 * Its main function is to check that all the other tasks are still operational.
 * Each task (other than the "flash" tasks) maintains a unique count that is
 * incremented each time the task successfully completes its function.  Should
 * any error occur within such a task the count is permanently halted.  The
 * check task inspects the count of each task to ensure it has changed since
 * the last time the check task executed.  If all the count variables have
 * changed all the tasks are still executing error free, and the check task
 * toggles the onboard LED.  Should any task contain an error at any time
 * the LED toggle rate will change from 3 seconds to 500ms.
 *
 * To check the operation of the memory allocator the check task also
 * dynamically creates a task before delaying, and deletes it again when it
 * wakes.  If memory cannot be allocated for the new task the call to xTaskCreate
 * will fail and an error is signalled.  The dynamically created task itself
 * allocates and frees memory just to give the allocator a bit more exercise.
 *
 */

/* Standard includes. */
#include <stdlib.h>
#include <string.h>

/* Scheduler include files. */
#include "FreeRTOS.h"
#include "task.h"

/* Demo application file headers. */
#include "flash.h"
#include "integer.h"
#include "PollQ.h"
#include "comtest2.h"
#include "semtest.h"
#include "flop.h"
#include "dynamic.h"
#include "BlockQ.h"
#include "serial.h"
#include "partest.h"

/* Priority definitions for most of the tasks in the demo application.  Some
tasks just use the idle priority. */
#define mainLED_TASK_PRIORITY			( tskIDLE_PRIORITY + 1 )
#define mainCOM_TEST_PRIORITY			( tskIDLE_PRIORITY + 2 )
#define mainQUEUE_POLL_PRIORITY			( tskIDLE_PRIORITY + 2 )
#define mainCHECK_TASK_PRIORITY			( tskIDLE_PRIORITY + 3 )
#define mainSEM_TEST_PRIORITY			( tskIDLE_PRIORITY + 1 )
#define mainBLOCK_Q_PRIORITY			( tskIDLE_PRIORITY + 2 )

/* Baud rate used by the serial port tasks (ComTest tasks). */
#define mainCOM_TEST_BAUD_RATE			( ( unsigned long ) 115200 )

/* LED used by the serial port tasks.  This is toggled on each character Tx,
and mainCOM_TEST_LED + 1 is toggles on each character Rx. */
#define mainCOM_TEST_LED				( 3 )

/* LED that is toggled by the check task.  The check task periodically checks
that all the other tasks are operating without error.  If no errors are found
the LED is toggled with mainCHECK_PERIOD frequency.  If an error is found
the the toggle rate increases to mainERROR_CHECK_PERIOD. */
#define mainCHECK_TASK_LED				( 5 )
#define mainCHECK_PERIOD				( ( TickType_t ) 3000 / portTICK_PERIOD_MS  )
#define mainERROR_CHECK_PERIOD			( ( TickType_t ) 500 / portTICK_PERIOD_MS )

/* Constants used by the vMemCheckTask() task. */
#define mainCOUNT_INITIAL_VALUE		( ( unsigned long ) 0 )
#define mainNO_TASK					( 0 )

/* The size of the memory blocks allocated by the vMemCheckTask() task. */
#define mainMEM_CHECK_SIZE_1		( ( size_t ) 51 )
#define mainMEM_CHECK_SIZE_2		( ( size_t ) 52 )
#define mainMEM_CHECK_SIZE_3		( ( size_t ) 151 )

/*
 * The 'Check' task.
 */
static void vErrorChecks( void *pvParameters );

/*
 * Checks the unique counts of other tasks to ensure they are still operational.
 */
static long prvCheckOtherTasksAreStillRunning( unsigned long ulMemCheckTaskCount );

/*
 * Dynamically created and deleted during each cycle of the vErrorChecks()
 * task.  This is done to check the operation of the memory allocator.
 * See the top of vErrorChecks for more details.
 */
static void vMemCheckTask( void *pvParameters );

/*-----------------------------------------------------------*/

/*
 * Start all the tasks then start the scheduler.
 */
int main( void )
{
	/* Setup the LED's for output. */
	vParTestInitialise();

	/* Start the various standard demo application tasks. */
	vStartIntegerMathTasks( tskIDLE_PRIORITY );
	vAltStartComTestTasks( mainCOM_TEST_PRIORITY, mainCOM_TEST_BAUD_RATE, mainCOM_TEST_LED );
	vStartLEDFlashTasks( mainLED_TASK_PRIORITY );
	vStartPolledQueueTasks( mainQUEUE_POLL_PRIORITY );
	vStartMathTasks( tskIDLE_PRIORITY );
	vStartSemaphoreTasks( mainSEM_TEST_PRIORITY );
	vStartDynamicPriorityTasks();
	vStartBlockingQueueTasks( mainBLOCK_Q_PRIORITY );

	/* Start the 'Check' task. */
	xTaskCreate( vErrorChecks, "Check", configMINIMAL_STACK_SIZE, NULL, mainCHECK_TASK_PRIORITY, NULL );

	/* In this port, to use preemptive scheduler define configUSE_PREEMPTION
	as 1 in portmacro.h.  To use the cooperative scheduler define
	configUSE_PREEMPTION as 0. */
	vTaskStartScheduler();

	/* Should never get here! */
	return 0;
}
/*-----------------------------------------------------------*/

/*
 * Cycle for ever, delaying then checking all the other tasks are still
 * operating without error.  If an error is detected then the delay period
 * is decreased from mainCHECK_PERIOD to mainERROR_CHECK_PERIOD so
 * the on board LED flash rate will increase.
 *
 * In addition to the standard tests the memory allocator is tested through
 * the dynamic creation and deletion of a task each cycle.  Each time the
 * task is created memory must be allocated for its stack.  When the task is
 * deleted this memory is returned to the heap.  If the task cannot be created
 * then it is likely that the memory allocation failed.   In addition the
 * dynamically created task allocates and frees memory while it runs.
 */
static void vErrorChecks( void *pvParameters )
{
TickType_t xDelayPeriod = mainCHECK_PERIOD;
volatile unsigned long ulMemCheckTaskRunningCount;
TaskHandle_t xCreatedTask;
TickType_t xLastWakeTime;

	/* Initialise xLastWakeTime to ensure the first call to vTaskDelayUntil()
	functions correctly. */
	xLastWakeTime = xTaskGetTickCount();

	for( ;; )
	{
		/* Set ulMemCheckTaskRunningCount to a known value so we can check
		later that it has changed. */
		ulMemCheckTaskRunningCount = mainCOUNT_INITIAL_VALUE;

		/* Dynamically create a task - passing ulMemCheckTaskRunningCount as a
		parameter. */
		xCreatedTask = mainNO_TASK;
		if( xTaskCreate( vMemCheckTask, "MEM_CHECK", configMINIMAL_STACK_SIZE, ( void * ) &ulMemCheckTaskRunningCount, tskIDLE_PRIORITY, &xCreatedTask ) != pdPASS )
		{
			/* Could not create the task - we have probably run out of heap. */
			xDelayPeriod = mainERROR_CHECK_PERIOD;
		}


		/* Delay until it is time to execute again.  The delay period is
		shorter following an error. */
		vTaskDelayUntil( &xLastWakeTime, xDelayPeriod );


		/* Delete the dynamically created task. */
		if( xCreatedTask != mainNO_TASK )
		{
			vTaskDelete( xCreatedTask );
		}

		/* Check all the standard demo application tasks are executing without
		error.  ulMemCheckTaskRunningCount is checked to ensure it was
		modified by the task just deleted. */
		if( prvCheckOtherTasksAreStillRunning( ulMemCheckTaskRunningCount ) != pdPASS )
		{
			/* An error has been detected in one of the tasks - flash faster. */
			xDelayPeriod = mainERROR_CHECK_PERIOD;
		}

		vParTestToggleLED( mainCHECK_TASK_LED );
	}
}
/*-----------------------------------------------------------*/

/*
 * 	Check each set of tasks in turn to see if they have experienced any
 *	error conditions.
 */
static long prvCheckOtherTasksAreStillRunning( unsigned long ulMemCheckTaskCount )
{
long lNoErrorsDiscovered = ( long ) pdTRUE;

	if( xAreIntegerMathsTaskStillRunning() != pdTRUE )
	{
		lNoErrorsDiscovered = pdFALSE;
	}

	if( xAreComTestTasksStillRunning() != pdTRUE )
	{
		lNoErrorsDiscovered = pdFALSE;
	}

	if( xArePollingQueuesStillRunning() != pdTRUE )
	{
		lNoErrorsDiscovered = pdFALSE;
	}

	if( xAreMathsTaskStillRunning() != pdTRUE )
	{
		lNoErrorsDiscovered = pdFALSE;
	}

	if( xAreSemaphoreTasksStillRunning() != pdTRUE )
	{
		lNoErrorsDiscovered = pdFALSE;
	}

	if( xAreDynamicPriorityTasksStillRunning() != pdTRUE )
	{
		lNoErrorsDiscovered = pdFALSE;
	}

	if( xAreBlockingQueuesStillRunning() != pdTRUE )
	{
		lNoErrorsDiscovered = pdFALSE;
	}

	if( ulMemCheckTaskCount == mainCOUNT_INITIAL_VALUE )
	{
		/* The vMemCheckTask task did not increment the counter - it must
		have failed. */
		lNoErrorsDiscovered = pdFALSE;
	}

	return lNoErrorsDiscovered;
}
/*-----------------------------------------------------------*/

static void vMemCheckTask( void *pvParameters )
{
unsigned long *pulMemCheckTaskRunningCounter;
void *pvMem1, *pvMem2, *pvMem3;
static long lErrorOccurred = pdFALSE;

	/* This task is dynamically created then deleted during each cycle of the
	vErrorChecks task to check the operation of the memory allocator.  Each time
	the task is created memory is allocated for the stack and TCB.  Each time
	the task is deleted this memory is returned to the heap.  This task itself
	exercises the allocator by allocating and freeing blocks.

	The task executes at the idle priority so does not require a delay.

	pulMemCheckTaskRunningCounter is incremented each cycle to indicate to the
	vErrorChecks() task that this task is still executing without error. */

	pulMemCheckTaskRunningCounter = ( unsigned long * ) pvParameters;

	for( ;; )
	{
		if( lErrorOccurred == pdFALSE )
		{
			/* We have never seen an error so increment the counter. */
			( *pulMemCheckTaskRunningCounter )++;
		}
		else
		{
			/* Reset the count so an error is detected by the
			prvCheckOtherTasksAreStillRunning() function. */
			*pulMemCheckTaskRunningCounter = mainCOUNT_INITIAL_VALUE;
		}

		/* Allocate some memory - just to give the allocator some extra
		exercise.  This has to be in a critical section to ensure the
		task does not get deleted while it has memory allocated. */
		vTaskSuspendAll();
		{
			pvMem1 = pvPortMalloc( mainMEM_CHECK_SIZE_1 );
			if( pvMem1 == NULL )
			{
				lErrorOccurred = pdTRUE;
			}
			else
			{
				memset( pvMem1, 0xaa, mainMEM_CHECK_SIZE_1 );
				vPortFree( pvMem1 );
			}
		}
		xTaskResumeAll();

		/* Again - with a different size block. */
		vTaskSuspendAll();
		{
			pvMem2 = pvPortMalloc( mainMEM_CHECK_SIZE_2 );
			if( pvMem2 == NULL )
			{
				lErrorOccurred = pdTRUE;
			}
			else
			{
				memset( pvMem2, 0xaa, mainMEM_CHECK_SIZE_2 );
				vPortFree( pvMem2 );
			}
		}
		xTaskResumeAll();

		/* Again - with a different size block. */
		vTaskSuspendAll();
		{
			pvMem3 = pvPortMalloc( mainMEM_CHECK_SIZE_3 );
			if( pvMem3 == NULL )
			{
				lErrorOccurred = pdTRUE;
			}
			else
			{
				memset( pvMem3, 0xaa, mainMEM_CHECK_SIZE_3 );
				vPortFree( pvMem3 );
			}
		}
		xTaskResumeAll();
	}
}
/*-----------------------------------------------------------*/

/*
 * Called by the startup code.  Initial processor setup can be placed in this
 * function.
 */
void hw_initialise (void)
{
}

