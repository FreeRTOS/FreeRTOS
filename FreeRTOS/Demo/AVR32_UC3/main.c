/*This file has been prepared for Doxygen automatic documentation generation.*/
/*! \file *********************************************************************
 *
 * \brief FreeRTOS Real Time Kernel example.
 *
 * Creates all the demo application tasks, then starts the scheduler.  The WEB
 * documentation provides more details of the demo application tasks.
 *
 * Main. c also creates a task called "Check".  This only executes every three
 * seconds but has the highest priority so is guaranteed to get processor time.
 * Its main function is to check that all the other tasks are still operational.
 * Each task that does not flash an LED maintains a unique count that is
 * incremented each time the task successfully completes its function.  Should
 * any error occur within such a task the count is permanently halted.  The
 * check task inspects the count of each task to ensure it has changed since
 * the last time the check task executed.  If all the count variables have
 * changed all the tasks are still executing error free, and the check task
 * toggles an LED.  Should any task contain an error at any time the LED toggle
 * will stop.
 *
 * The LED flash and communications test tasks do not maintain a count.
 *
 * - Compiler:           IAR EWAVR32 and GNU GCC for AVR32
 * - Supported devices:  All AVR32 devices with GPIO.
 * - AppNote:
 *
 * \author               Atmel Corporation: http://www.atmel.com \n
 *                       Support and FAQ: http://support.atmel.no/
 *
 *****************************************************************************/

/*
 * FreeRTOS Kernel V10.0.0
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
 * copies or substantial portions of the Software. If you wish to use our Amazon
 * FreeRTOS name, please do so in a fair use way that does not cause confusion.
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


#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* Environment header files. */
#include "pm.h"

/* Scheduler header files. */
#include "FreeRTOS.h"
#include "task.h"

/* Demo file headers. */
#include "partest.h"
#include "serial.h"
#include "integer.h"
#include "comtest.h"
#include "flash.h"
#include "PollQ.h"
#include "semtest.h"
#include "dynamic.h"
#include "BlockQ.h"
#include "death.h"
#include "flop.h"

/*! \name Priority definitions for most of the tasks in the demo application.
 * Some tasks just use the idle priority.
 */
//! @{
#define mainLED_TASK_PRIORITY     ( tskIDLE_PRIORITY + 1 )
#define mainCOM_TEST_PRIORITY     ( tskIDLE_PRIORITY + 2 )
#define mainQUEUE_POLL_PRIORITY   ( tskIDLE_PRIORITY + 2 )
#define mainSEM_TEST_PRIORITY     ( tskIDLE_PRIORITY + 1 )
#define mainBLOCK_Q_PRIORITY      ( tskIDLE_PRIORITY + 3 )
#define mainCHECK_TASK_PRIORITY   ( tskIDLE_PRIORITY + 4 )
#define mainCREATOR_TASK_PRIORITY ( tskIDLE_PRIORITY + 3 )
//! @}

//! Baud rate used by the serial port tasks.
#define mainCOM_TEST_BAUD_RATE    ( ( unsigned long ) 57600 )

//! LED used by the serial port tasks.  This is toggled on each character Tx,
//! and mainCOM_TEST_LED + 1 is toggled on each character Rx.
#define mainCOM_TEST_LED          ( 3 )

//! LED that is toggled by the check task.  The check task periodically checks
//! that all the other tasks are operating without error.  If no errors are found
//! the LED is toggled.  If an error is found at any time the LED toggles faster.
#define mainCHECK_TASK_LED        ( 6 )

//! LED that is set upon error.
#define mainERROR_LED             ( 7 )

//! The period between executions of the check task.
#define mainCHECK_PERIOD          ( ( TickType_t ) 3000 / portTICK_PERIOD_MS  )

//! If an error is detected in a task, the vErrorChecks task will enter in an
//! infinite loop flashing the LED at this rate.
#define mainERROR_FLASH_RATE      ( (TickType_t) 500 / portTICK_PERIOD_MS )

/*! \name Constants used by the vMemCheckTask() task.
 */
//! @{
#define mainCOUNT_INITIAL_VALUE   ( ( unsigned long ) 0 )
#define mainNO_TASK               ( 0 )
//! @}

/*! \name The size of the memory blocks allocated by the vMemCheckTask() task.
 */
//! @{
#define mainMEM_CHECK_SIZE_1      ( ( size_t ) 51 )
#define mainMEM_CHECK_SIZE_2      ( ( size_t ) 52 )
#define mainMEM_CHECK_SIZE_3      ( ( size_t ) 15 )
//! @}


/*-----------------------------------------------------------*/

/*
 * The task that executes at the highest priority and calls
 * prvCheckOtherTasksAreStillRunning().  See the description at the top
 * of the file.
 */
static void vErrorChecks( void *pvParameters );

/*
 * Checks that all the demo application tasks are still executing without error
 * - as described at the top of the file.
 */
static portBASE_TYPE prvCheckOtherTasksAreStillRunning( void );

/*
 * A task that exercises the memory allocator.
 */
static void vMemCheckTask( void *pvParameters );

/*
 * Called by the check task following the detection of an error to set the
 * LEDs into a state that shows an error has beeen found.
 */
static void prvIndicateError( void );

/*-----------------------------------------------------------*/

int main( void )
{
	/* Start the crystal oscillator 0 and switch the main clock to it. */
	pm_switch_to_osc0(&AVR32_PM, FOSC0, OSC0_STARTUP);

	portDBG_TRACE("Starting the FreeRTOS AVR32 UC3 Demo...");

	/* Setup the LED's for output. */
	vParTestInitialise();

	/* Start the standard demo tasks.  See the WEB documentation for more
	information. */
	vStartLEDFlashTasks( mainLED_TASK_PRIORITY );
	vAltStartComTestTasks( mainCOM_TEST_PRIORITY, mainCOM_TEST_BAUD_RATE, mainCOM_TEST_LED );
	vStartPolledQueueTasks( mainQUEUE_POLL_PRIORITY );
	vStartIntegerMathTasks( tskIDLE_PRIORITY );
	vStartSemaphoreTasks( mainSEM_TEST_PRIORITY );
	vStartDynamicPriorityTasks();
	vStartBlockingQueueTasks( mainBLOCK_Q_PRIORITY );
	vStartMathTasks( tskIDLE_PRIORITY );

	/* Start the demo tasks defined within this file, specifically the check
	task as described at the top of this file. */
	xTaskCreate(
		vErrorChecks
		,  "ErrCheck"
		,  configMINIMAL_STACK_SIZE
		,  NULL
		,  mainCHECK_TASK_PRIORITY
		,  NULL );

	/* Start the scheduler. */
	vTaskStartScheduler();

	/* Will only get here if there was insufficient memory to create the idle
	task. */

	return 0;
}
/*-----------------------------------------------------------*/

/*!
 * \brief The task function for the "Check" task.
 */
static void vErrorChecks( void *pvParameters )
{
static volatile unsigned long ulDummyVariable = 3UL;
unsigned long ulMemCheckTaskRunningCount;
TaskHandle_t xCreatedTask;
portBASE_TYPE bSuicidalTask = 0;

	/* The parameters are not used.  Prevent compiler warnings. */
	( void ) pvParameters;

	/* Cycle for ever, delaying then checking all the other tasks are still
	operating without error.

	In addition to the standard tests the memory allocator is tested through
	the dynamic creation and deletion of a task each cycle.  Each time the
	task is created memory must be allocated for its stack.  When the task is
	deleted this memory is returned to the heap.  If the task cannot be created
	then it is likely that the memory allocation failed. */

	for( ;; )
	{
		/* Do this only once. */
		if( bSuicidalTask == 0 )
		{
			bSuicidalTask++;

			/* This task has to be created last as it keeps account of the number of
			tasks it expects to see running. However its implementation expects
			to be called before vTaskStartScheduler(). We're in the case here where
			vTaskStartScheduler() has already been called (thus the hidden IDLE task
			has already been spawned). Since vCreateSuicidalTask() supposes that the
			IDLE task isn't included in the response from uxTaskGetNumberOfTasks(),
			let the MEM_CHECK task play that role. => this is why vCreateSuicidalTasks()
			is not called as the last task. */
			vCreateSuicidalTasks( mainCREATOR_TASK_PRIORITY );
		}

		/* Reset xCreatedTask.  This is modified by the task about to be
		created so we can tell if it is executing correctly or not. */
		xCreatedTask = mainNO_TASK;

		/* Dynamically create a task - passing ulMemCheckTaskRunningCount as a
		parameter. */
		ulMemCheckTaskRunningCount = mainCOUNT_INITIAL_VALUE;

		if( xTaskCreate( vMemCheckTask,
			"MEM_CHECK",
			configMINIMAL_STACK_SIZE,
			( void * ) &ulMemCheckTaskRunningCount,
			tskIDLE_PRIORITY, &xCreatedTask ) != pdPASS )
		{
			/* Could not create the task - we have probably run out of heap.
			Don't go any further and flash the LED faster to provide visual
			feedback of the error. */
			prvIndicateError();
		}

		/* Delay until it is time to execute again. */
		vTaskDelay( mainCHECK_PERIOD );

		/* Delete the dynamically created task. */
		if( xCreatedTask != mainNO_TASK )
		{
			vTaskDelete( xCreatedTask );
		}

		/* Perform a bit of 32bit maths to ensure the registers used by the
		integer tasks get some exercise. The result here is not important -
		see the demo application documentation for more info. */
		ulDummyVariable *= 3;

		/* Check all other tasks are still operating without error.
		Check that vMemCheckTask did increment the counter. */
		if( ( prvCheckOtherTasksAreStillRunning() != pdFALSE )
		 || ( ulMemCheckTaskRunningCount == mainCOUNT_INITIAL_VALUE ) )
		{
			/* An error has occurred in one of the tasks.
			Don't go any further and flash the LED faster to give visual
			feedback of the error. */
			prvIndicateError();
		}
		else
		{
			/* Toggle the LED if everything is okay. */
			vParTestToggleLED( mainCHECK_TASK_LED );
		}
	}
}
/*-----------------------------------------------------------*/


/*!
 * \brief Checks that all the demo application tasks are still executing without error.
 */
static portBASE_TYPE prvCheckOtherTasksAreStillRunning( void )
{
static portBASE_TYPE xErrorHasOccurred = pdFALSE;

	if( xAreComTestTasksStillRunning() != pdTRUE )
	{
		xErrorHasOccurred = pdTRUE;
	}

	if( xArePollingQueuesStillRunning() != pdTRUE )
	{
		xErrorHasOccurred = pdTRUE;
	}

	if( xAreIntegerMathsTaskStillRunning() != pdTRUE )
	{
		xErrorHasOccurred = pdTRUE;
	}

	if( xAreSemaphoreTasksStillRunning() != pdTRUE )
	{
		xErrorHasOccurred = pdTRUE;
	}

	if( xAreBlockingQueuesStillRunning() != pdTRUE )
	{
		xErrorHasOccurred = pdTRUE;
	}

	if( xAreDynamicPriorityTasksStillRunning() != pdTRUE )
	{
		xErrorHasOccurred = pdTRUE;
	}

	if( xAreMathsTaskStillRunning() != pdTRUE )
	{
		xErrorHasOccurred = pdTRUE;
	}

	if( xIsCreateTaskStillRunning() != pdTRUE )
	{
		xErrorHasOccurred = pdTRUE;
	}

	return ( xErrorHasOccurred );
}
/*-----------------------------------------------------------*/


/*!
 * \brief Dynamically created and deleted during each cycle of the vErrorChecks()
 * task.  This is done to check the operation of the memory allocator.
 * See the top of vErrorChecks for more details.
 *
 * \param *pvParameters Parameters for the task (can be of any kind)
 */
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
			/* There has been an error so reset the counter so the check task
			can tell that an error occurred. */
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

static void prvIndicateError( void )
{
	/* The check task has found an error in one of the other tasks.
	Set the LEDs to a state that indicates this. */
	vParTestSetLED(mainERROR_LED,pdTRUE);

	for(;;)
	{
		#if( BOARD==EVK1100 )
			vParTestToggleLED( mainCHECK_TASK_LED );
			vTaskDelay( mainERROR_FLASH_RATE );
		#endif
		#if ( BOARD==EVK1101 )
			vParTestSetLED( 0, pdTRUE );
			vParTestSetLED( 1, pdTRUE );
			vParTestSetLED( 2, pdTRUE );
			vParTestSetLED( 3, pdTRUE );
		#endif
	}
}

