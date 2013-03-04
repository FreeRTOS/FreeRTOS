/*
    FreeRTOS V7.4.0 - Copyright (C) 2013 Real Time Engineers Ltd.

    FEATURES AND PORTS ARE ADDED TO FREERTOS ALL THE TIME.  PLEASE VISIT
    http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

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

    >>>>>>NOTE<<<<<< The modification to the GPL is included to allow you to
    distribute a combined work that includes FreeRTOS without being obliged to
    provide the source code for proprietary components outside of the FreeRTOS
    kernel.

    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT ANY
    WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
    FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more
    details. You should have received a copy of the GNU General Public License
    and the FreeRTOS license exception along with FreeRTOS; if not itcan be
    viewed here: http://www.freertos.org/a00114.html and also obtained by
    writing to Real Time Engineers Ltd., contact details for whom are available
    on the FreeRTOS WEB site.

    1 tab == 4 spaces!

    ***************************************************************************
     *                                                                       *
     *    Having a problem?  Start by reading the FAQ "My application does   *
     *    not run, what could be wrong?"                                     *
     *                                                                       *
     *    http://www.FreeRTOS.org/FAQHelp.html                               *
     *                                                                       *
    ***************************************************************************


    http://www.FreeRTOS.org - Documentation, books, training, latest versions,
    license and Real Time Engineers Ltd. contact details.

    http://www.FreeRTOS.org/plus - A selection of FreeRTOS ecosystem products,
    including FreeRTOS+Trace - an indispensable productivity tool, and our new
    fully thread aware and reentrant UDP/IP stack.

    http://www.OpenRTOS.com - Real Time Engineers ltd license FreeRTOS to High
    Integrity Systems, who sell the code with commercial support,
    indemnification and middleware, under the OpenRTOS brand.

    http://www.SafeRTOS.com - High Integrity Systems also provide a safety
    engineered and independently SIL3 certified version for use in safety and
    mission critical applications that require provable dependability.
*/

/*
 *
 * ENSURE TO READ THE DOCUMENTATION PAGE FOR THIS PORT AND DEMO APPLICATION ON
 * THE http://www.FreeRTOS.org WEB SITE FOR FULL INFORMATION ON USING THIS DEMO
 * APPLICATION, AND ITS ASSOCIATE FreeRTOS ARCHITECTURE PORT!
 *
 *
 * main() creates the demo application tasks and timers, then starts the
 * scheduler.
 *
 * This demo is configured to run on the RL78/G13 Promotion Board, which is
 * fitted with a R5F100LEA microcontroller.  The R5F100LEA contains a little
 * under 4K bytes of usable internal RAM.  The RAM size restricts the number of
 * demo tasks that can be created, and the demo creates 13 tasks, 4 queues and
 * two timers.  The RL78 range does however include parts with up to 32K bytes
 * of RAM (at the time of writing).  Using FreeRTOS on such a part will allow an
 * application to make a more comprehensive use of FreeRTOS tasks, and other
 * FreeRTOS features.
 *
 * In addition to the standard demo tasks, the following tasks, tests and timers
 * are created within this file:
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
 * callback function checks that all the standard demo tasks, the reg test tasks,
 * and the demo timer are not only still executing, but are executing without
 * reporting any errors.  If the check timer discovers that a task or timer has
 * stalled, or reported an error, then it changes its own period from the
 * initial three seconds, to just 200ms.  The check timer callback function also
 * toggles the user LED each time it is called.  This provides a visual
 * indication of the system status:  If the LED toggles every three seconds,
 * then no issues have been discovered.  If the LED toggles every 200ms, then an
 * issue has been discovered with at least one task.
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
#include "port_iodefine.h"
#include "port_iodefine_ext.h"
#include "LED.h"

/* The period at which the check timer will expire, in ms, provided no errors
have been reported by any of the standard demo tasks.  ms are converted to the
equivalent in ticks using the portTICK_RATE_MS constant. */
#define mainCHECK_TIMER_PERIOD_MS			( 3000UL / portTICK_RATE_MS )

/* The period at which the check timer will expire, in ms, if an error has been
reported in one of the standard demo tasks, the check tasks, or the demo timer.
ms are converted to the equivalent in ticks using the portTICK_RATE_MS
constant. */
#define mainERROR_CHECK_TIMER_PERIOD_MS 	( 200UL / portTICK_RATE_MS )

/* These two definitions are used to set the period of the demo timer.  The demo
timer period is always relative to the check timer period, so the check timer
can determine if the demo timer has expired the expected number of times between
its own executions. */
#define mainDEMO_TIMER_INCREMENTS_PER_CHECK_TIMER_TIMEOUT	( 100UL )
#define mainDEMO_TIMER_PERIOD_MS			( mainCHECK_TIMER_PERIOD_MS / mainDEMO_TIMER_INCREMENTS_PER_CHECK_TIMER_TIMEOUT )

/* A block time of zero simple means "don't block". */
#define mainDONT_BLOCK						( 0U )

/*-----------------------------------------------------------*/

/*
 * The 'check' timer callback function, as described at the top of this file.
 */
static void prvCheckTimerCallback( xTimerHandle xTimer );

/*
 * The 'demo' timer callback function, as described at the top of this file.
 */
static void prvDemoTimerCallback( xTimerHandle xTimer );

/*
 * Functions that define the RegTest tasks, as described at the top of this file.
 */
extern void vRegTest1( void *pvParameters );
extern void vRegTest2( void *pvParameters );


/*-----------------------------------------------------------*/

/* Variables that are incremented on each cycle of the two reg tests to allow
the check timer to know that they are still executing. */
unsigned short usRegTest1LoopCounter = 0, usRegTest2LoopCounter;

/* The check timer.  This uses prvCheckTimerCallback() as its callback
function. */
static xTimerHandle xCheckTimer = NULL;

/* The demo timer.  This uses prvDemoTimerCallback() as its callback function. */
static xTimerHandle xDemoTimer = NULL;

/* This variable is incremented each time the demo timer expires. */
static volatile unsigned long ulDemoSoftwareTimerCounter = 0UL;

/*-----------------------------------------------------------*/
volatile unsigned char ucTemp;
short main( void )
{
	ucTemp = RESF;
	ucTemp = sizeof( char* );
	ucTemp = sizeof( pdTASK_CODE );

	/* Creates all the tasks and timers, then starts the scheduler. */

	/* First create the 'standard demo' tasks.  These are used to demonstrate
	API functions being used and also to test the kernel port.  More information
	is provided on the FreeRTOS.org WEB site. */
	vStartDynamicPriorityTasks();
	vStartPolledQueueTasks( tskIDLE_PRIORITY );
	vCreateBlockTimeTasks();

	/* Create the RegTest tasks as described at the top of this file. */
//	xTaskCreate( vRegTest1, "Reg1", configMINIMAL_STACK_SIZE, NULL, 0, NULL );
//	xTaskCreate( vRegTest2, "Reg2", configMINIMAL_STACK_SIZE, NULL, 0, NULL );

	/* Create the software timer that performs the 'check' functionality,
	as described at the top of this file. */
	xCheckTimer = xTimerCreate( ( const signed char * ) "CheckTimer",/* A text name, purely to help debugging. */
								( mainCHECK_TIMER_PERIOD_MS ),		/* The timer period, in this case 3000ms (3s). */
								pdTRUE,								/* This is an auto-reload timer, so xAutoReload is set to pdTRUE. */
								( void * ) 0,						/* The ID is not used, so can be set to anything. */
								prvCheckTimerCallback				/* The callback function that inspects the status of all the other tasks. */
							  );

	/* Create the software timer that just increments a variable for demo
	purposes. */
	xDemoTimer = xTimerCreate( ( const signed char * ) "DemoTimer",/* A text name, purely to help debugging. */
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

	/* If this line is reached then vTaskStartScheduler() returned because there
	was insufficient heap memory remaining for the idle task to be created. */
	for( ;; );
}
/*-----------------------------------------------------------*/

static void prvDemoTimerCallback( xTimerHandle xTimer )
{
	/* The demo timer has expired.  All it does is increment a variable.  The
	period of the demo timer is relative to that of the check timer, so the
	check timer knows how many times this variable should have been incremented
	between each execution of the check timer's own callback. */
	ulDemoSoftwareTimerCounter++;
}
/*-----------------------------------------------------------*/

static void prvCheckTimerCallback( xTimerHandle xTimer )
{
static portBASE_TYPE xChangedTimerPeriodAlready = pdFALSE, xErrorStatus = pdPASS;
static unsigned short usLastRegTest1Counter = 0, usLastRegTest2Counter = 0;

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
	incrementing, which will result in the check timer signialling an error. */
	for( ;; );
}
/*-----------------------------------------------------------*/

void vApplicationMallocFailedHook( void )
{
	/* Called if a call to pvPortMalloc() fails because there is insufficient
	free memory available in the FreeRTOS heap.  pvPortMalloc() is called
	internally by FreeRTOS API functions that create tasks, queues, software
	timers, and semaphores.  The size of the FreeRTOS heap is set by the
	configTOTAL_HEAP_SIZE configuration constant in FreeRTOSConfig.h. */
	taskDISABLE_INTERRUPTS();
	for( ;; );
}
/*-----------------------------------------------------------*/

void vApplicationStackOverflowHook( xTaskHandle pxTask, signed char *pcTaskName )
{
	( void ) pcTaskName;
	( void ) pxTask;

	/* Run time stack overflow checking is performed if
	configCHECK_FOR_STACK_OVERFLOW is defined to 1 or 2.  This hook
	function is called if a stack overflow is detected. */
	taskDISABLE_INTERRUPTS();
	for( ;; );
}
/*-----------------------------------------------------------*/

void vApplicationIdleHook( void )
{
volatile size_t xFreeHeapSpace;

	/* This is just a trivial example of an idle hook.  It is called on each
	cycle of the idle task.  It must *NOT* attempt to block.  In this case the
	idle task just queries the amount of FreeRTOS heap that remains.  See the
	memory management section on the http://www.FreeRTOS.org web site for memory
	management options.  If there is a lot of heap memory free then the
	configTOTAL_HEAP_SIZE value in FreeRTOSConfig.h can be reduced to free up
	RAM. */
	xFreeHeapSpace = xPortGetFreeHeapSize();
}
/*-----------------------------------------------------------*/

