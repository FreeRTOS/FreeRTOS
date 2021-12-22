/*
 * FreeRTOS V202112.00
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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

/******************************************************************************
 * NOTE 1:  This project provides two demo applications.  A simple blinky style
 * project, and a more comprehensive test and demo application.  The
 * mainCREATE_SIMPLE_BLINKY_DEMO_ONLY setting in main.c is used to select
 * between the two.  See the notes on using mainCREATE_SIMPLE_BLINKY_DEMO_ONLY
 * in main.c.  This file implements the comprehensive test and demo version.
 *
 * NOTE 2:  This file only contains the source code that is specific to the
 * full demo.  Generic functions, such FreeRTOS hook functions, and functions
 * required to configure the hardware, are defined in main.c.
 *
 ******************************************************************************
 *
 * See http://www.FreeRTOS.org/RTOS_Intel_Quark_Galileo_GCC.html for usage
 * instructions.
 *
 * main_full() creates all the demo application tasks and software timers, then
 * starts the scheduler.  The web documentation provides more details of the
 * standard demo application tasks, which provide no particular functionality,
 * but do provide a good example of how to use the FreeRTOS API.
 *
 * In addition to the standard demo tasks, the following tasks and tests are
 * defined and/or created within this file:
 *
 * "Reg test" tasks - These fill both the core and floating point registers with
 * known values, then check that each register maintains its expected value for
 * the lifetime of the task.  Each task uses a different set of values.  The reg
 * test tasks execute with a very low priority, so get preempted very
 * frequently.  A register containing an unexpected value is indicative of an
 * error in the context switching mechanism.
 *
 * "Check" task - The check task period is set to five seconds.  The task checks
 * that all the standard demo tasks, and the register check tasks, are not only
 * still executing, but are executing without reporting any errors.  The check
 * task toggles an LED on each iteration.  If the LED toggles every 5 seconds
 * then no errors have been found.  If the LED toggles every 1 second then a
 * potential error has been detected.
 */

/* Standard includes. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "timers.h"

/* Standard demo includes. */
#include "blocktim.h"
#include "flash_timer.h"
#include "semtest.h"
#include "GenQTest.h"
#include "QPeek.h"
#include "countsem.h"
#include "dynamic.h"
#include "QueueOverwrite.h"
#include "QueueSet.h"
#include "recmutex.h"
#include "EventGroupsDemo.h"
#include "death.h"
#include "TimerDemo.h"
#include "BlockQ.h"
#include "flop.h"
#include "TaskNotify.h"
#include "IntQueue.h"

/* Galileo includes. */
#include "galileo_support.h"

/* The rate at which the check task cycles if no errors have been detected, and
if a [potential] error has been detected.  Increasing the toggle rate in the
presense of an error gives visual feedback of the system status. */
#define mainNO_ERROR_CHECK_TASK_PERIOD		pdMS_TO_TICKS( 5000UL )
#define mainERROR_CHECK_TASK_PERIOD			pdMS_TO_TICKS( 1000UL )

/* The priorities of the various demo application tasks. */
#define mainSEM_TEST_PRIORITY				( tskIDLE_PRIORITY + 1 )
#define mainBLOCK_Q_PRIORITY				( tskIDLE_PRIORITY + 1 )
#define mainGEN_QUEUE_TASK_PRIORITY			( tskIDLE_PRIORITY )
#define mainQUEUE_OVERWRITE_TASK_PRIORITY	( tskIDLE_PRIORITY )
#define mainMATHS_TASK_PRIORITY				( tskIDLE_PRIORITY )

/* The base period used by the timer test tasks. */
#define mainTIMER_TEST_PERIOD				( 50 )

/* Parameters that are passed into the check tasks for no other purpose other
than to check the port does this correctly. */
#define mainREG_TEST_1_PARAMETER			( 0x12345678UL )
#define mainREG_TEST_2_PARAMETER			( 0x87654321UL )

/*-----------------------------------------------------------*/

/*
 * The function that implements the check task, as described at the top of this
 * file.
 */
static void prvCheckTask( void *pvParameters );

/*
 * Entry points for the register check tasks, as described at the top of this
 * file.
 */
static void prvRegTest1Entry( void *pvParameters );
static void prvRegTest2Entry( void *pvParameters );

/*
 * The implementation of the register check tasks, which are implemented in
 * RegTest.S.  These functions are called by prvRegTest1Entry() and
 * prvRegTest2Entry() respectively.
 */
extern void vRegTest1( void );
extern void vRegTest2( void );

/*-----------------------------------------------------------*/

/* Constants used by the register check tasks when checking the FPU registers. */
const double dRegTest1_st7 = 7.0, dRegTest1_st6 = 6.0, dRegTest1_st5 = 5.0, dRegTest1_st4 = 4.0, dRegTest1_st3 = 3.0, dRegTest1_st2 = 2.0, dRegTest1_st1 = 1.0;
const double dRegTest2_st7 = 700.0, dRegTest2_st6 = 600.0, dRegTest2_st5 = 500.0, dRegTest2_st4 = 400.0, dRegTest2_st3 = 300.0, dRegTest2_st2 = 200.0, dRegTest2_st1 = 100.0;

/* Counters used by the register check tasks to indicate that they are still
executing without having discovered any errors. */
volatile uint32_t ulRegTest1Counter, ulRegTest2Counter;
volatile uint32_t ulCheckLoops = 0;

/*-----------------------------------------------------------*/

/* See http://www.FreeRTOS.org/RTOS_Intel_Quark_Galileo_GCC.html for usage
instructions. */
void main_full( void )
{
	/* Create all the other standard demo tasks. */
	vCreateBlockTimeTasks();
	vStartSemaphoreTasks( mainSEM_TEST_PRIORITY );
	vStartGenericQueueTasks( mainGEN_QUEUE_TASK_PRIORITY );
	vStartQueuePeekTasks();
	vStartCountingSemaphoreTasks();
	vStartDynamicPriorityTasks();
	vStartQueueOverwriteTask( mainQUEUE_OVERWRITE_TASK_PRIORITY );
	vStartQueueSetTasks();
	vStartRecursiveMutexTasks();
	vStartEventGroupTasks();
	vStartTimerDemoTask( mainTIMER_TEST_PERIOD );
	vStartBlockingQueueTasks( mainBLOCK_Q_PRIORITY );
	vStartTaskNotifyTask();
	vStartInterruptQueueTasks();

	#if configSUPPORT_FPU == 1
	{
		vStartMathTasks( mainMATHS_TASK_PRIORITY );
	}
	#endif /* configSUPPORT_FPU */

	/* Create the 'check' task, as described at the top of this file. */
	xTaskCreate( prvCheckTask, "Check", configMINIMAL_STACK_SIZE * 2, NULL, configMAX_PRIORITIES - 1, NULL );

	/* Create the register test tasks, as described at the top of this file. */
	xTaskCreate( prvRegTest1Entry, "Reg1", configMINIMAL_STACK_SIZE, ( void * ) mainREG_TEST_1_PARAMETER, tskIDLE_PRIORITY, NULL );
	xTaskCreate( prvRegTest2Entry, "Reg2", configMINIMAL_STACK_SIZE, ( void * ) mainREG_TEST_2_PARAMETER, tskIDLE_PRIORITY, NULL );

	/* Death tasks must be created last as they check the number of tasks
	running against the number of tasks expected to be running as part of their
	sanity checks. */
	vCreateSuicidalTasks( tskIDLE_PRIORITY );

	/* Display HPET Information (Disable in HPET.H). */
	vCreateHPETInfoUpdateTask();

	/* Start the scheduler itself. */
	vTaskStartScheduler();

	/* If all is well, the scheduler will now be running, and the following line
	will never be reached.  If the following line does execute, then there was
	insufficient FreeRTOS heap memory available for the idle and/or timer tasks
	to be created.  See the memory management section on the FreeRTOS web site
	for more details. */
	for( ;; );
}
/*-----------------------------------------------------------*/

static void prvRegTest1Entry( void *pvParameters )
{
	/* Remove compiler warning if configASSERT() is not defined. */
	( void ) pvParameters;

	/* Check the parameter is passed in correctly. */
	configASSERT( ( ( uint32_t) pvParameters ) == mainREG_TEST_1_PARAMETER );

	/* Tell FreeRTOS that this task needs a floating point context. */
	portTASK_USES_FLOATING_POINT();

	/* Call the assembly file routine that performs the 'reg test' functionality
	as described at the top of this file. */
	vRegTest1();
}
/*-----------------------------------------------------------*/

static void prvRegTest2Entry( void *pvParameters )
{
	/* Remove compiler warning if configASSERT() is not defined. */
	( void ) pvParameters;

	/* Check the parameter is passed in correctly. */
	configASSERT( ( ( uint32_t) pvParameters ) == mainREG_TEST_2_PARAMETER );

	/* Tell FreeRTOS that this task needs a floating point context. */
	portTASK_USES_FLOATING_POINT();

	/* Call the assembly file routine that performs the 'reg test' functionality
	as described at the top of this file. */
	vRegTest2();
}
/*-----------------------------------------------------------*/

static void prvCheckTask( void *pvParameters )
{
uint32_t ulLastRegTest1Counter = 0UL, ulLastRegTest2Counter = 0UL;
uint32_t ulErrorOccurred, ulElapsedTimeInSeconds = 0UL;
TickType_t xLastExpireTime, xBlockTime = mainNO_ERROR_CHECK_TASK_PERIOD;
BaseType_t xErrorFlag = pdFALSE;

	/* Avoid compiler warnings. */
	( void ) pvParameters;

	/* Initialise the last expire time to the current time. */
	xLastExpireTime = xTaskGetTickCount();

	/* Message to wait for an update - first update won't happen for X seconds. */
	g_printf_rcc( 5, 2, DEFAULT_SCREEN_COLOR, "Starting task check loop - Please wait for a status update." );
	g_printf_rcc( 6, 2, DEFAULT_SCREEN_COLOR, "No task errors encountered." );

	for( ;; )
	{
		vTaskDelayUntil( &xLastExpireTime, xBlockTime );
		ulElapsedTimeInSeconds += xBlockTime;

		/* Have any of the standard demo tasks detected an error in their
		operation?  If so, latch the offending test in a bit map so it can be
		printed to the terminal.  Once one error has occurred the cycle rate is
		increased to increase the rate at which the LED toggles, which can cause
		further errors to be detected (as some tests will not expect the
		increased cycle rate). */

		ulErrorOccurred = 0UL;

		if( xAreQueuePeekTasksStillRunning() != pdTRUE )
		{
			ulErrorOccurred |= ( 0x01UL << 0UL );
		}

		if( xAreGenericQueueTasksStillRunning() != pdTRUE )
		{
			ulErrorOccurred |= ( 0x01UL << 1UL );
		}

		if( xAreBlockTimeTestTasksStillRunning() != pdTRUE )
		{
			ulErrorOccurred |= ( 0x01UL << 2UL );
		}

		if( xAreSemaphoreTasksStillRunning() != pdTRUE )
		{
			ulErrorOccurred |= ( 0x01UL << 3UL );
		}

		if( xAreCountingSemaphoreTasksStillRunning() != pdTRUE )
		{
			ulErrorOccurred |= ( 0x01UL << 4UL );
		}

		if( xAreDynamicPriorityTasksStillRunning() != pdTRUE )
		{
			ulErrorOccurred |= ( 0x01UL << 5UL );
		}

		if( xIsQueueOverwriteTaskStillRunning() != pdTRUE )
		{
			ulErrorOccurred |= ( 0x01UL << 6UL );
		}

		if( xAreQueueSetTasksStillRunning() != pdTRUE )
		{
			ulErrorOccurred |= ( 0x01UL << 7UL );
		}

		if( xAreRecursiveMutexTasksStillRunning() != pdTRUE )
		{
			ulErrorOccurred |= ( 0x01UL << 8UL );
		}

		if( xAreEventGroupTasksStillRunning() != pdTRUE )
		{
			ulErrorOccurred |= ( 0x01UL << 9UL );
		}

		if( xIsCreateTaskStillRunning() != pdTRUE )
		{
			ulErrorOccurred |= ( 0x01UL << 10UL );
		}

		if( xAreTimerDemoTasksStillRunning( xBlockTime ) != pdTRUE )
		{
			ulErrorOccurred |= ( 0x01UL << 11UL );
		}

		if( xAreBlockingQueuesStillRunning() != pdTRUE )
		{
			ulErrorOccurred |= ( 0x01UL << 12UL );
		}

		if( xAreTaskNotificationTasksStillRunning() != pdTRUE )
		{
			ulErrorOccurred |= ( 1UL << 13UL );
		}

		if( xAreIntQueueTasksStillRunning() != pdTRUE )
		{
			ulErrorOccurred |= ( 1UL << 14UL );
		}

		#if configSUPPORT_FPU == 1
		{
			if( xAreMathsTaskStillRunning() != pdTRUE )
			{
				ulErrorOccurred |= ( 0x01UL << 15UL );
			}
		}
		#endif /* configSUPPORT_FPU */

		/* Check the register test tasks are still looping. */
		if( ulRegTest1Counter == ulLastRegTest1Counter )
		{
			ulErrorOccurred |= ( 0x01UL << 16UL );
		}
		else
		{
			ulLastRegTest1Counter = ulRegTest1Counter;
		}

		if( ulRegTest2Counter == ulLastRegTest2Counter )
		{
			ulErrorOccurred |= ( 0x01UL << 17UL );
		}
		else
		{
			ulLastRegTest2Counter = ulRegTest2Counter;
		}

		if( ulErrorOccurred != 0UL )
		{
			/* Decrease the block time, which will increase the rate at
			which the LED blinks - and in so doing - give visual feedback of
			the error status. */
			xBlockTime = mainERROR_CHECK_TASK_PERIOD;
		}

		/* Print the hex bit pattern, time, and the loop number - just to make
		sure the task is still cycling. */
		g_printf_rcc( 5, 2, DEFAULT_SCREEN_COLOR,
			"Status code: 0x%08x at task check time : %8ds,  loop #: %8d\r",
			ulErrorOccurred, ( ulElapsedTimeInSeconds / 1000 ), ( ulCheckLoops + 1 ) );

		/* Print the current free heap size and the minimum ever free heap
		size. */
		g_printf_rcc( 6, 2, DEFAULT_SCREEN_COLOR,
			"Current free heap: %d bytes, Min. free heap: %d bytes\r",
			xPortGetFreeHeapSize(), xPortGetMinimumEverFreeHeapSize() );

		/* Show the first error that occurred on a separate line. */
		if( ( xErrorFlag == pdFALSE ) && ( ulErrorOccurred != pdFALSE ) )
		{
			xErrorFlag = pdTRUE;
			g_printf_rcc( 7, 2, ANSI_COLOR_RED,
				"Error  code: 0x%08x at check time : %8ds (First Error),  loop#: %8d \r",
				ulErrorOccurred, (  ulElapsedTimeInSeconds / 1000 ), ( ulCheckLoops + 1 ) );
		}

		/* Flash the LED */
		ulBlinkLED();

		/* Crude Overflow check to keep printf() statements <= 8 digits long */
		ulCheckLoops++;
		if( ulCheckLoops > 10000000UL )
		{
			ulCheckLoops = 0UL;
		}
	}
}
/*-----------------------------------------------------------*/

