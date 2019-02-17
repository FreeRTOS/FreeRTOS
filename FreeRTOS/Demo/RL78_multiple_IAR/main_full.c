/*
 * FreeRTOS Kernel V10.2.0
 * Copyright (C) 2019 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 * required to configure the hardware, along with an example of how to write an
 * interrupt service routine, are defined in main.c.
 ******************************************************************************
 *
 * main_full() creates all the demo application tasks and two software timers,
 * then starts the scheduler.  The web documentation provides more details of
 * the standard demo application tasks, which provide no particular
 * functionality, but do provide a good example of how to use the FreeRTOS API.
 *
 * In addition to the standard demo tasks, the following tasks, tests and
 * timers are created within this file:
 *
 * "Reg test" tasks - These fill the registers with known values, then check
 * that each register still contains its expected value.  Each task uses a
 * different set of values.  The reg test tasks execute with a very low priority,
 * so get preempted very frequently.  A register containing an unexpected value
 * is indicative of an error in the context switching mechanism.
 *
 * The "Demo" Timer and Callback Function:
 * The demo timer callback function does nothing more than increment a variable.
 * The period of the demo timer is set relative to the period of the check timer
 * (described below).  This allows the check timer to know how many times the
 * demo timer callback function should execute between each execution of the
 * check timer callback function.  The variable incremented in the demo timer
 * callback function is used to determine how many times the callback function
 * has executed.
 *
 * The "Check" Timer and Callback Function:
 * The check timer period is initially set to three seconds.  The check timer
 * callback function checks that all the standard demo tasks, the reg test
 * tasks, and the demo timer are not only still executing, but are executing
 * without reporting any errors.  If the check timer discovers that a task or
 * timer has stalled, or reported an error, then it changes its own period from
 * the initial three seconds, to just 200ms.  The check timer callback function
 * also toggles an LED each time it is called.  This provides a visual
 * indication of the system status:  If the LED toggles every three seconds,
 * then no issues have been discovered.  If the LED toggles every 200ms, then
 * an issue has been discovered with at least one task.
 *
 * ENSURE TO READ THE DOCUMENTATION PAGE FOR THIS PORT AND DEMO APPLICATION ON
 * THE http://www.FreeRTOS.org WEB SITE FOR FULL INFORMATION ON USING THIS DEMO
 * APPLICATION, AND ITS ASSOCIATE FreeRTOS ARCHITECTURE PORT!
 *
 */

/* Scheduler include files. */
#include "FreeRTOS.h"
#include "task.h"
#include "timers.h"

/* Standard demo includes. */
#include "dynamic.h"
#include "PollQ.h"
#include "blocktim.h"

/* Hardware includes. */
#include "demo_specific_io.h"

/* The period at which the check timer will expire, in ms, provided no errors
have been reported by any of the standard demo tasks.  ms are converted to the
equivalent in ticks using the portTICK_PERIOD_MS constant. */
#define mainCHECK_TIMER_PERIOD_MS			( 3000UL / portTICK_PERIOD_MS )

/* The period at which the check timer will expire, in ms, if an error has been
reported in one of the standard demo tasks, the check tasks, or the demo timer.
ms are converted to the equivalent in ticks using the portTICK_PERIOD_MS
constant. */
#define mainERROR_CHECK_TIMER_PERIOD_MS 	( 200UL / portTICK_PERIOD_MS )

/* These two definitions are used to set the period of the demo timer.  The demo
timer period is always relative to the check timer period, so the check timer
can determine if the demo timer has expired the expected number of times between
its own executions. */
#define mainDEMO_TIMER_INCREMENTS_PER_CHECK_TIMER_TIMEOUT	( 100UL )
#define mainDEMO_TIMER_PERIOD_MS			( mainCHECK_TIMER_PERIOD_MS / mainDEMO_TIMER_INCREMENTS_PER_CHECK_TIMER_TIMEOUT )

/* A block time of zero simply means "don't block". */
#define mainDONT_BLOCK						( 0U )

/* Values that are passed as parameters into the reg test tasks (purely to
ensure task parameters are passed correctly). */
#define mainREG_TEST_1_PARAMETER			( ( void * ) 0x1234 )
#define mainREG_TEST_2_PARAMETER			( ( void * ) 0x5678 )

/*-----------------------------------------------------------*/

/*
 * The 'check' timer callback function, as described at the top of this file.
 */
static void prvCheckTimerCallback( TimerHandle_t xTimer );

/*
 * The 'demo' timer callback function, as described at the top of this file.
 */
static void prvDemoTimerCallback( TimerHandle_t xTimer );

/*
 * Functions that define the RegTest tasks, as described at the top of this
 * file.  The RegTest tasks are written (necessarily) in assembler.  Their
 * entry points are written in C to allow for easy checking of the task
 * parameter values.
 */
extern void vRegTest1Task( void );
extern void vRegTest2Task( void );
static void prvRegTest1Entry( void *pvParameters );
static void prvRegTest2Entry( void *pvParameters );

/*
 * Called if a RegTest task discovers an error as a mechanism to stop the
 * tasks loop counter incrementing (so the check task can detect that an
 * error exists).
 */
void vRegTestError( void );

/*
 * Called by main() to create the more comprehensive application if
 * mainCREATE_SIMPLE_BLINKY_DEMO_ONLY is set to 0.
 */
void main_full( void );

/*-----------------------------------------------------------*/

/* Variables that are incremented on each cycle of the two reg tests to allow
the check timer to know that they are still executing. */
unsigned short usRegTest1LoopCounter = 0, usRegTest2LoopCounter;

/* The check timer.  This uses prvCheckTimerCallback() as its callback
function. */
static TimerHandle_t xCheckTimer = NULL;

/* The demo timer.  This uses prvDemoTimerCallback() as its callback function. */
static TimerHandle_t xDemoTimer = NULL;

/* This variable is incremented each time the demo timer expires. */
static volatile unsigned long ulDemoSoftwareTimerCounter = 0UL;

/*-----------------------------------------------------------*/

void main_full( void )
{
	/* Creates all the tasks and timers, then starts the scheduler. */

	/* First create the 'standard demo' tasks.  These are used to demonstrate
	API functions being used and also to test the kernel port.  More information
	is provided on the FreeRTOS.org WEB site. */
	vStartDynamicPriorityTasks();
	vStartPolledQueueTasks( tskIDLE_PRIORITY );
	vCreateBlockTimeTasks();

	/* Create the RegTest tasks as described at the top of this file. */
	xTaskCreate( prvRegTest1Entry,				/* The function that implements the task. */
				 "Reg1",						/* Text name for the task - to assist debugging only, not used by the kernel. */
				 configMINIMAL_STACK_SIZE, 		/* The size of the stack allocated to the task (in words, not bytes). */
				 mainREG_TEST_1_PARAMETER,  	/* The parameter passed into the task. */
				 tskIDLE_PRIORITY, 				/* The priority at which the task will execute. */
				 NULL );						/* Used to pass the handle of the created task out to the function caller - not used in this case. */

	xTaskCreate( prvRegTest2Entry, "Reg2", configMINIMAL_STACK_SIZE, mainREG_TEST_2_PARAMETER, tskIDLE_PRIORITY, NULL );

	/* Create the software timer that performs the 'check' functionality,
	as described at the top of this file. */
	xCheckTimer = xTimerCreate( "CheckTimer",					/* A text name, purely to help debugging. */
								( mainCHECK_TIMER_PERIOD_MS ),	/* The timer period, in this case 3000ms (3s). */
								pdTRUE,							/* This is an auto-reload timer, so xAutoReload is set to pdTRUE. */
								( void * ) 0,					/* The ID is not used, so can be set to anything. */
								prvCheckTimerCallback			/* The callback function that inspects the status of all the other tasks. */
							  );

	/* Create the software timer that just increments a variable for demo
	purposes. */
	xDemoTimer = xTimerCreate(  "DemoTimer",/* A text name, purely to help debugging. */
								( mainDEMO_TIMER_PERIOD_MS ),		/* The timer period, in this case it is always calculated relative to the check timer period (see the definition of mainDEMO_TIMER_PERIOD_MS). */
								pdTRUE,								/* This is an auto-reload timer, so xAutoReload is set to pdTRUE. */
								( void * ) 0,						/* The ID is not used, so can be set to anything. */
								prvDemoTimerCallback				/* The callback function that inspects the status of all the other tasks. */
							  );

	/* Start both the check timer and the demo timer.  The timers won't actually
	start until the scheduler is started. */
	xTimerStart( xCheckTimer, mainDONT_BLOCK );
	xTimerStart( xDemoTimer, mainDONT_BLOCK );

	/* Finally start the scheduler running. */
	vTaskStartScheduler();

	/* If all is well execution will never reach here as the scheduler will be
	running.  If this null loop is reached then it is likely there was
	insufficient FreeRTOS heap available for the idle task and/or timer task to
	be created.  See http://www.freertos.org/a00111.html. */
	for( ;; );
}
/*-----------------------------------------------------------*/

static void prvDemoTimerCallback( TimerHandle_t xTimer )
{
	/* Remove compiler warning about unused parameter. */
	( void ) xTimer;

	/* The demo timer has expired.  All it does is increment a variable.  The
	period of the demo timer is relative to that of the check timer, so the
	check timer knows how many times this variable should have been incremented
	between each execution of the check timer's own callback. */
	ulDemoSoftwareTimerCounter++;
}
/*-----------------------------------------------------------*/

static void prvCheckTimerCallback( TimerHandle_t xTimer )
{
static portBASE_TYPE xChangedTimerPeriodAlready = pdFALSE, xErrorStatus = pdPASS;
static unsigned short usLastRegTest1Counter = 0, usLastRegTest2Counter = 0;

	/* Remove compiler warning about unused parameter. */
	( void ) xTimer;

	/* Inspect the status of the standard demo tasks. */
	if( xAreDynamicPriorityTasksStillRunning() != pdTRUE )
	{
		xErrorStatus = pdFAIL;
	}

	if( xArePollingQueuesStillRunning() != pdTRUE )
	{
		xErrorStatus = pdFAIL;
	}

	if( xAreBlockTimeTestTasksStillRunning() != pdTRUE )
	{
		xErrorStatus = pdFAIL;
	}

	/* Indicate an error if either of the reg test loop counters have not
	incremented since the last time this function was called. */
	if( usLastRegTest1Counter == usRegTest1LoopCounter )
	{
		xErrorStatus = pdFAIL;
	}
	else
	{
		usLastRegTest1Counter = usRegTest1LoopCounter;
	}

	if( usLastRegTest2Counter == usRegTest2LoopCounter )
	{
		xErrorStatus = pdFAIL;
	}
	else
	{
		usLastRegTest2Counter = usRegTest2LoopCounter;
	}

	/* Ensure that the demo software timer has expired
	mainDEMO_TIMER_INCREMENTS_PER_CHECK_TIMER_TIMEOUT times in between
	each call of this function.  A critical section is not required to access
	ulDemoSoftwareTimerCounter as the variable is only accessed from another
	software timer callback, and only one software timer callback can be
	executing at any time. */
	if( ( ulDemoSoftwareTimerCounter < ( mainDEMO_TIMER_INCREMENTS_PER_CHECK_TIMER_TIMEOUT - 1 ) ) ||
	    ( ulDemoSoftwareTimerCounter > ( mainDEMO_TIMER_INCREMENTS_PER_CHECK_TIMER_TIMEOUT + 1 ) )
	  )
	{
		xErrorStatus = pdFAIL;
	}
	else
	{
		ulDemoSoftwareTimerCounter = 0UL;
	}

	if( ( xErrorStatus == pdFAIL ) && ( xChangedTimerPeriodAlready == pdFALSE ) )
	{
		/* An error has occurred, but the timer's period has not yet been changed,
		change it now, and remember that it has been changed.  Shortening the
		timer's period means the LED will toggle at a faster rate, giving a
		visible indication that something has gone wrong. */
		xChangedTimerPeriodAlready = pdTRUE;

		/* This call to xTimerChangePeriod() uses a zero block time.  Functions
		called from inside of a timer callback function must *never* attempt to
		block. */
		xTimerChangePeriod( xCheckTimer, ( mainERROR_CHECK_TIMER_PERIOD_MS ), mainDONT_BLOCK );
	}

	/* Toggle the LED.  The toggle rate will depend on whether or not an error
	has been found in any tasks. */
	LED_BIT = !LED_BIT;
}
/*-----------------------------------------------------------*/

void vRegTestError( void )
{
	/* Called by both reg test tasks if an error is found.  There is no way out
	of this function so the loop counter of the calling task will stop
	incrementing, which will result in the check timer signaling an error. */
	for( ;; );
}
/*-----------------------------------------------------------*/

static void prvRegTest1Entry( void *pvParameters )
{
	/* If the parameter has its expected value then start the first reg test
	task (this is only done to test that the RTOS port is correctly handling
	task parameters. */
	if( pvParameters == mainREG_TEST_1_PARAMETER )
	{
		vRegTest1Task();
	}
	else
	{
		vRegTestError();
	}

	/* It is not possible to get here as neither of the two functions called
	above will ever return. */
}
/*-----------------------------------------------------------*/

static void prvRegTest2Entry( void *pvParameters )
{
	/* If the parameter has its expected value then start the first reg test
	task (this is only done to test that the RTOS port is correctly handling
	task parameters. */
	if( pvParameters == mainREG_TEST_2_PARAMETER )
	{
		vRegTest2Task();
	}
	else
	{
		vRegTestError();
	}

	/* It is not possible to get here as neither of the two functions called
	above will ever return. */
}
/*-----------------------------------------------------------*/

