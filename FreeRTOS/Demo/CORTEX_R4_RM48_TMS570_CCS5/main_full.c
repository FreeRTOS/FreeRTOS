/*
 * FreeRTOS Kernel V10.4.1
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
 ******************************************************************************
 *
 * main_full() creates all the demo application tasks and software timers,
 * then starts the scheduler.  The web documentation provides more details of
 * the standard demo application tasks, which provide no particular
 * functionality, but do provide a good example of how to use the FreeRTOS API.
 *
 * In addition to the standard demo tasks, the following tasks and tests are
 * defined and/or created within this file:
 *
 * "Check" timer - The check software timer period is set to three seconds.
 * The callback function associated with the check software timer checks that
 * all the standard demo tasks are not only still executing, but are executing
 * without reporting any errors.  If the check software timer discovers that a
 * task has either stalled, or reported an error, then the error is logged and
 * the check software timer toggles the red LEDs.  If an error has never been
 * latched, the check software timer toggles the green LEDs.  Therefore, if the
 * system is executing correctly, the green LEDs will toggle every three
 * seconds, and if an error has ever been detected, the red LEDs will toggle
 * every three seconds.
 *
 * "Reg test" tasks - These fill both the core and floating point registers
 * with known values, then check that each register maintains its expected
 * value for the lifetime of the tasks.  Each task uses a different set of
 * values.  The reg test tasks execute with a very low priority, so get
 * preempted very frequently.  A register containing an unexpected value is
 * indicative of an error in the context switching mechanism.
 *
 * "LED" software timer - The callback function associated with the LED
 * software time maintains a pattern of spinning white LEDs.
 *
 * See the documentation page for this demo on the FreeRTOS.org web site for
 * full information, including hardware setup requirements.
 */

/* Standard includes. */
#include <stdio.h>

/* Kernel includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "timers.h"
#include "semphr.h"

/* Standard demo application includes. */
#include "integer.h"
#include "PollQ.h"
#include "semtest.h"
#include "dynamic.h"
#include "BlockQ.h"
#include "blocktim.h"
#include "countsem.h"
#include "GenQTest.h"
#include "recmutex.h"
#include "death.h"
#include "partest.h"
#include "flop.h"
#include "serial.h"
#include "comtest.h"

/* Priorities for the demo application tasks. */
#define mainQUEUE_POLL_PRIORITY				( tskIDLE_PRIORITY + 2UL )
#define mainSEM_TEST_PRIORITY				( tskIDLE_PRIORITY + 1UL )
#define mainBLOCK_Q_PRIORITY				( tskIDLE_PRIORITY + 2UL )
#define mainCREATOR_TASK_PRIORITY			( tskIDLE_PRIORITY + 3UL )
#define mainFLOP_TASK_PRIORITY				( tskIDLE_PRIORITY )
#define mainCOM_TEST_PRIORITY				( tskIDLE_PRIORITY + 2 )
#define mainFLOP_TASK_PRIORITY				( tskIDLE_PRIORITY )

/* A block time of zero simply means "don't block". */
#define mainDONT_BLOCK						( 0UL )

/* The period after which the check timer will expire, converted to ticks. */
#define mainCHECK_TIMER_PERIOD_MS			( 3000UL / portTICK_PERIOD_MS )

/* The period after which the LED timer will expire, converted to ticks. */
#define mainLED_TIMER_PERIOD_MS				( 75UL / portTICK_PERIOD_MS )

/* Constants for the ComTest tasks. */
#define mainCOM_TEST_BAUD_RATE				( ( unsigned long ) 19200 )
#define mainCOM_TEST_LED					( 100 )

/*-----------------------------------------------------------*/

/*
 * The check timer callback function, as described at the top of this file.
 */
static void prvCheckTimerCallback( TimerHandle_t xTimer );

/*
 * The LED timer callback function, as described at the top of this file.
 */
static void prvLEDTimerCallback( TimerHandle_t xTimer );

/*
 * The reg test tasks, as described at the top of this file.
 */
extern void vRegTestTask1( void *pvParameters );
extern void vRegTestTask2( void *pvParameters );

/*-----------------------------------------------------------*/

/* Variables that are incremented on each iteration of the reg test tasks -
provided the tasks have not reported any errors.  The check task inspects these
variables to ensure they are still incrementing as expected.  If a variable
stops incrementing then it is likely that its associate task has stalled. */
volatile unsigned long ulRegTest1Counter = 0, ulRegTest2Counter = 0;

/*-----------------------------------------------------------*/

void main_full( void )
{
TimerHandle_t xTimer = NULL;

	/* Start all the standard demo/test tasks.  These have not particular
	functionality, but do demonstrate how to use the FreeRTOS API, and test the
	kernel port. */
	vStartIntegerMathTasks( tskIDLE_PRIORITY );
	vStartDynamicPriorityTasks();
	vStartBlockingQueueTasks( mainBLOCK_Q_PRIORITY );
	vCreateBlockTimeTasks();
	vStartCountingSemaphoreTasks();
	vStartGenericQueueTasks( tskIDLE_PRIORITY );
	vStartRecursiveMutexTasks();
	vStartPolledQueueTasks( mainQUEUE_POLL_PRIORITY );
	vStartSemaphoreTasks( mainSEM_TEST_PRIORITY );
	vStartMathTasks( mainFLOP_TASK_PRIORITY );
	vAltStartComTestTasks( mainCOM_TEST_PRIORITY, mainCOM_TEST_BAUD_RATE, mainCOM_TEST_LED );

	/* Create the register test tasks, as described at the top of this file. */
	xTaskCreate( vRegTestTask1, "Reg1...", configMINIMAL_STACK_SIZE, NULL, tskIDLE_PRIORITY, NULL );
	xTaskCreate( vRegTestTask2, "Reg2...", configMINIMAL_STACK_SIZE, NULL, tskIDLE_PRIORITY, NULL );


	/* Create the software timer that performs the 'check' functionality,
	as described at the top of this file. */
	xTimer = xTimerCreate( "CheckTimer",					/* A text name, purely to help debugging. */
							( mainCHECK_TIMER_PERIOD_MS ),	/* The timer period, in this case 3000ms (3s). */
							pdTRUE,							/* This is an auto-reload timer, so xAutoReload is set to pdTRUE. */
							( void * ) 0,					/* The ID is not used, so can be set to anything. */
							prvCheckTimerCallback			/* The callback function that inspects the status of all the other tasks. */
						 );

	if( xTimer != NULL )
	{
		xTimerStart( xTimer, mainDONT_BLOCK );
	}

	/* Create the software timer that performs the 'LED spin' functionality,
	as described at the top of this file. */
	xTimer = xTimerCreate( "LEDTimer",					/* A text name, purely to help debugging. */
							( mainLED_TIMER_PERIOD_MS ),/* The timer period, in this case 75ms. */
							pdTRUE,						/* This is an auto-reload timer, so xAutoReload is set to pdTRUE. */
							( void * ) 0,				/* The ID is not used, so can be set to anything. */
							prvLEDTimerCallback			/* The callback function that toggles the white LEDs. */
						 );

	if( xTimer != NULL )
	{
		xTimerStart( xTimer, mainDONT_BLOCK );
	}

	/* The set of tasks created by the following function call have to be
	created last as they keep account of the number of tasks they expect to see
	running. */
	vCreateSuicidalTasks( mainCREATOR_TASK_PRIORITY );

	/* Start the scheduler. */
	vTaskStartScheduler();

	/* If all is well, the scheduler will now be running, and the following line
	will never be reached.  If the following line does execute, then there was
	insufficient FreeRTOS heap memory available for the idle and/or timer tasks
	to be created.  See the memory management section on the FreeRTOS web site
	for more details. */
	for( ;; );
}
/*-----------------------------------------------------------*/

static void prvCheckTimerCallback( TimerHandle_t xTimer )
{
static long lChangeToRedLEDsAlready = pdFALSE;
static unsigned long ulLastRegTest1Counter = 0, ulLastRegTest2Counter = 0;
unsigned long ulErrorFound = pdFALSE;
/* LEDs are defaulted to use the Green LEDs.  The Red LEDs are used if an error
is found. */
static unsigned long ulLED1 = 8, ulLED2 = 11;
const unsigned long ulRedLED1 = 6, ulRedLED2 = 9;

	/* Check all the demo tasks (other than the flash tasks) to ensure
	they are all still running, and that none have detected an error. */

	if( xAreIntegerMathsTaskStillRunning() != pdTRUE )
	{
		ulErrorFound = pdTRUE;
	}

	if( xAreDynamicPriorityTasksStillRunning() != pdTRUE )
	{
		ulErrorFound = pdTRUE;
	}

	if( xAreBlockingQueuesStillRunning() != pdTRUE )
	{
		ulErrorFound = pdTRUE;
	}

	if ( xAreBlockTimeTestTasksStillRunning() != pdTRUE )
	{
		ulErrorFound = pdTRUE;
	}

	if ( xAreGenericQueueTasksStillRunning() != pdTRUE )
	{
		ulErrorFound = pdTRUE;
	}

	if ( xAreRecursiveMutexTasksStillRunning() != pdTRUE )
	{
		ulErrorFound = pdTRUE;
	}

	if( xIsCreateTaskStillRunning() != pdTRUE )
	{
		ulErrorFound = pdTRUE;
	}

	if( xArePollingQueuesStillRunning() != pdTRUE )
	{
		ulErrorFound = pdTRUE;
	}

	if( xAreSemaphoreTasksStillRunning() != pdTRUE )
	{
		ulErrorFound = pdTRUE;
	}

	if( xAreMathsTaskStillRunning() != pdTRUE )
	{
		ulErrorFound = pdTRUE;
	}

	if( xAreComTestTasksStillRunning() != pdTRUE )
	{
		ulErrorFound = pdTRUE;
	}

	/* Check the reg test tasks are still cycling.  They will stop
	incrementing their loop counters if they encounter an error. */
	if( ulRegTest1Counter == ulLastRegTest1Counter )
	{
		ulErrorFound = pdTRUE;
	}

	if( ulRegTest2Counter == ulLastRegTest2Counter )
	{
		ulErrorFound = pdTRUE;
	}

	ulLastRegTest1Counter = ulRegTest1Counter;
	ulLastRegTest2Counter = ulRegTest2Counter;

	/* Toggle the check LEDs to give an indication of the system status.  If
	the green LEDs are toggling, then no errors have been detected.  If the red
	LEDs are toggling, then an error has been reported in at least one task. */
	vParTestToggleLED( ulLED1 );
	vParTestToggleLED( ulLED2 );

	/* Have any errors been latch in ulErrorFound?  If so, ensure the gree LEDs
	are off, then switch to using the red LEDs. */
	if( ulErrorFound != pdFALSE )
	{
		if( lChangeToRedLEDsAlready == pdFALSE )
		{
			lChangeToRedLEDsAlready = pdTRUE;

			/* An error has been found.  Switch to use the red LEDs. */
			vParTestSetLED( ulLED1, pdFALSE );
			vParTestSetLED( ulLED2, pdFALSE );
			ulLED1 = ulRedLED1;
			ulLED2 = ulRedLED2;
		}
	}
}
/*-----------------------------------------------------------*/

static void prvLEDTimerCallback( TimerHandle_t xTimer )
{
const unsigned long ulNumWhiteLEDs = 6;
static unsigned long ulLit1 = 2, ulLit2 = 1;

	vParTestSetLED( ulLit2, pdFALSE );

	ulLit2 = ulLit1;
	ulLit1++;

	if( ulLit1 >= ulNumWhiteLEDs )
	{
		ulLit1 = 0;
	}

	vParTestSetLED( ulLit1, pdTRUE );
}
/*-----------------------------------------------------------*/

