/*
 * FreeRTOS Kernel V10.1.1
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
 * main_full() creates all the demo application tasks and a software timer, then
 * starts the scheduler.  The web documentation provides more details of the
 * standard demo application tasks, which provide no particular functionality,
 * but do provide a good example of how to use the FreeRTOS API.
 *
 * In addition to the standard demo tasks, the following tasks and tests are
 * defined and/or created within this file:
 *
 * "Check" timer - The check software timer period is initially set to three
 * seconds.  The callback function associated with the check software timer
 * checks that all the standard demo tasks are not only still executing, but
 * are executing without reporting any errors.  If the check software timer
 * discovers that a task has either stalled, or reported an error, then it
 * changes its own execution period from the initial three seconds, to just
 * 200ms.  The check software timer callback function also toggles the green
 * LED each time it is called.  This provides a visual indication of the system
 * status:  If the green LED toggles every three seconds, then no issues have
 * been discovered.  If the green LED toggles every 200ms, then an issue has
 * been discovered with at least one task.
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
#include "flash_timer.h"
#include "partest.h"
#include "comtest2.h"
#include "QueueSet.h"
#include "IntQueue.h"
#include "TaskNotify.h"
#include "TimerDemo.h"
#include "EventGroupsDemo.h"
#include "IntSemTest.h"

/* Atmel library includes. */
#include "asf.h"

/* Priorities for the demo application tasks. */
#define mainQUEUE_POLL_PRIORITY				( tskIDLE_PRIORITY + 2UL )
#define mainSEM_TEST_PRIORITY				( tskIDLE_PRIORITY + 1UL )
#define mainBLOCK_Q_PRIORITY				( tskIDLE_PRIORITY + 2UL )
#define mainCREATOR_TASK_PRIORITY			( tskIDLE_PRIORITY + 3UL )
#define mainFLOP_TASK_PRIORITY				( tskIDLE_PRIORITY )
#define mainCOM_TEST_PRIORITY				( tskIDLE_PRIORITY + 2 )

/* A block time of zero simply means "don't block". */
#define mainDONT_BLOCK						( 0UL )

/* The period after which the check timer will expire, in ms, provided no errors
have been reported by any of the standard demo tasks.  ms are converted to the
equivalent in ticks using the portTICK_PERIOD_MS constant. */
#define mainCHECK_TIMER_PERIOD_MS			( pdMS_TO_TICKS( 3000UL ) )

/* The period at which the check timer will expire, in ms, if an error has been
reported in one of the standard demo tasks.  ms are converted to the equivalent
in ticks using the portTICK_PERIOD_MS constant. */
#define mainERROR_CHECK_TIMER_PERIOD_MS 	( pdMS_TO_TICKS( 200UL ) )

/* The standard demo flash timers can be used to flash any number of LEDs.  In
this case, because only three LEDs are available, and one is in use by the
check timer, only two are used by the flash timers. */
#define mainNUMBER_OF_FLASH_TIMERS_LEDS		( 2 )

/* The LED toggled by the check timer.  The first two LEDs are toggle by the
standard demo flash timers. */
#define mainCHECK_LED						( 2 )

/* Baud rate used by the comtest tasks. */
#define mainCOM_TEST_BAUD_RATE				( 115200 )

/* The LED used by the comtest tasks. In this case, there are no LEDs available
for the comtest, so the LED number is deliberately out of range. */
#define mainCOM_TEST_LED					( 3 )

/* Used by the standard demo timer tasks. */
#define mainTIMER_TEST_PERIOD				( 50 )

/*-----------------------------------------------------------*/

/*
 * Called by the idle hook function when the project is configured to run the
 * full (as opposed to the blinky) demo.
 */
void vFullDemoIdleHook( void );

/*
 * Called by the tick hook function when the project is configured to run the
 * full (as opposed to the blinky) demo.
 */
void vFullDemoTickHook( void );

/*
 * The check timer callback function, as described at the top of this file.
 */
static void prvCheckTimerCallback( TimerHandle_t xTimer );

/*-----------------------------------------------------------*/

void main_full( void )
{
	/* Start all the other standard demo/test tasks.  The have not particular
	functionality, but do demonstrate how to use the FreeRTOS API and test the
	kernel port. */
	vStartInterruptQueueTasks();
	vStartIntegerMathTasks( tskIDLE_PRIORITY );
	vStartDynamicPriorityTasks();
	vStartBlockingQueueTasks( mainBLOCK_Q_PRIORITY );
	vCreateBlockTimeTasks();
	vStartCountingSemaphoreTasks();
	vStartGenericQueueTasks( tskIDLE_PRIORITY );
	vStartRecursiveMutexTasks();
	vStartPolledQueueTasks( mainQUEUE_POLL_PRIORITY );
	vStartSemaphoreTasks( mainSEM_TEST_PRIORITY );
	vAltStartComTestTasks( mainCOM_TEST_PRIORITY, mainCOM_TEST_BAUD_RATE, mainCOM_TEST_LED );
	vStartQueueSetTasks();
	vStartTaskNotifyTask();
	vStartTimerDemoTask( mainTIMER_TEST_PERIOD );
	vStartEventGroupTasks();
	vStartInterruptSemaphoreTasks();

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
static long lChangedTimerPeriodAlready = pdFALSE;
unsigned long ulErrorFound = pdFALSE;

	/* Check all the demo tasks (other than the flash tasks) to ensure
	they are all still running, and that none have detected an error. */

	if( xAreIntQueueTasksStillRunning() != pdTRUE )
	{
		ulErrorFound |= 1UL << 0UL;
	}

	if( xAreIntegerMathsTaskStillRunning() != pdTRUE )
	{
		ulErrorFound |= 1UL << 1UL;
	}

	if( xAreDynamicPriorityTasksStillRunning() != pdTRUE )
	{
		ulErrorFound |= 1UL << 2UL;
	}

	if( xAreBlockingQueuesStillRunning() != pdTRUE )
	{
		ulErrorFound |= 1UL << 3UL;
	}

	if ( xAreBlockTimeTestTasksStillRunning() != pdTRUE )
	{
		ulErrorFound |= 1UL << 4UL;
	}

	if ( xAreGenericQueueTasksStillRunning() != pdTRUE )
	{
		ulErrorFound |= 1UL << 5UL;
	}

	if ( xAreRecursiveMutexTasksStillRunning() != pdTRUE )
	{
		ulErrorFound |= 1UL << 6UL;
	}

	if( xIsCreateTaskStillRunning() != pdTRUE )
	{
		ulErrorFound |= 1UL << 7UL;
	}

	if( xArePollingQueuesStillRunning() != pdTRUE )
	{
		ulErrorFound |= 1UL << 8UL;
	}

	if( xAreSemaphoreTasksStillRunning() != pdTRUE )
	{
		ulErrorFound |= 1UL << 9UL;
	}

	if( xAreComTestTasksStillRunning() != pdTRUE )
	{
		ulErrorFound |= 1UL << 10UL;
	}

	if( xAreQueueSetTasksStillRunning() != pdTRUE )
	{
		ulErrorFound |= 1UL << 11UL;
	}
	
	if( xAreTaskNotificationTasksStillRunning() != pdTRUE )
	{
		ulErrorFound |= 1UL << 12UL;
	}
	
	if( xAreTimerDemoTasksStillRunning( mainCHECK_TIMER_PERIOD_MS ) != pdTRUE )
	{
		ulErrorFound |= 1UL << 13UL;
	}
	
	if( xAreEventGroupTasksStillRunning() != pdTRUE )
	{
		ulErrorFound |= 1UL << 14UL;
	}
	
	if( xAreInterruptSemaphoreTasksStillRunning() != pdTRUE )
	{
		ulErrorFound |= 1UL << 15UL;
	}
	

	/* Toggle the check LED to give an indication of the system status.  If
	the LED toggles every mainCHECK_TIMER_PERIOD_MS milliseconds then
	everything is ok.  A faster toggle indicates an error. */
	vParTestToggleLED( mainCHECK_LED );

	/* Have any errors been latch in ulErrorFound?  If so, shorten the
	period of the check timer to mainERROR_CHECK_TIMER_PERIOD_MS milliseconds.
	This will result in an increase in the rate at which mainCHECK_LED
	toggles. */
	if( ulErrorFound != pdFALSE )
	{
		if( lChangedTimerPeriodAlready == pdFALSE )
		{
			lChangedTimerPeriodAlready = pdTRUE;

			/* This call to xTimerChangePeriod() uses a zero block time.
			Functions called from inside of a timer callback function must
			*never* attempt	to block. */
			xTimerChangePeriod( xTimer, ( mainERROR_CHECK_TIMER_PERIOD_MS ), mainDONT_BLOCK );
		}
	}
}
/*-----------------------------------------------------------*/

void vFullDemoIdleHook( void )
{
static TimerHandle_t xCheckTimer = NULL;
		
	if( xCheckTimer == NULL )
	{
		/* Create the software timer that performs the 'check' 
		functionality, in the full demo.  This is not done before the
		scheduler is started as to do so would prevent the standard demo
		timer tasks from passing their tests (they expect the timer
		command queue to be empty. */
		xCheckTimer = xTimerCreate( "CheckTimer",				/* A text name, purely to help debugging. */
									mainCHECK_TIMER_PERIOD_MS,	/* The timer period, in this case 3000ms (3s). */
									pdTRUE,						/* This is an auto-reload timer, so xAutoReload is set to pdTRUE. */
									( void * ) 0,				/* The ID is not used, so can be set to anything. */
									prvCheckTimerCallback		/* The callback function that inspects the status of all the other tasks. */
									);

		if( xCheckTimer != NULL )
		{
			xTimerStart( xCheckTimer, mainDONT_BLOCK );
		}
		
		/* Also start some timers that just flash LEDs. */
		vStartLEDFlashTimers( mainNUMBER_OF_FLASH_TIMERS_LEDS );
	}
}
/*-----------------------------------------------------------*/

void vFullDemoTickHook( void )
{
	/* In this case the tick hook is used as part of the queue set test. */
	vQueueSetAccessQueueSetFromISR();
		
	/* Use task notifications from an interrupt. */
	xNotifyTaskFromISR();
		
	/* Use timers from an interrupt. */
	vTimerPeriodicISRTests();
	
	/* Use event groups from an interrupt. */
	vPeriodicEventGroupsProcessing();
	
	/* Use mutexes from interrupts. */
	vInterruptSemaphorePeriodicTest();
}
