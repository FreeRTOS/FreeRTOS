/*
 * FreeRTOS V202012.00
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

/* The LED toggled by the check timer. */
#define mainLED_0   						P7_bit.no7

/* A block time of zero simple means "don't block". */
#define mainDONT_BLOCK						( 0U )

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
 * This function is called from the C startup routine to setup the processor -
 * in particular the clock source.
 */
int __low_level_init(void);

/*
 * Functions that define the RegTest tasks, as described at the top of this file.
 */
extern void vRegTest1( void *pvParameters );
extern void vRegTest2( void *pvParameters );


/*-----------------------------------------------------------*/

/* If an error is discovered by one of the RegTest tasks then this flag is set
to pdFAIL.  The 'check' timer then inspects this flag to detect errors within
the RegTest tasks. */
static short sRegTestStatus = pdPASS;

/* The check timer.  This uses prvCheckTimerCallback() as its callback
function. */
static TimerHandle_t xCheckTimer = NULL;

/* The demo timer.  This uses prvDemoTimerCallback() as its callback function. */
static TimerHandle_t xDemoTimer = NULL;

/* This variable is incremented each time the demo timer expires. */
static volatile unsigned long ulDemoSoftwareTimerCounter = 0UL;

/* RL78 Option Byte Definition. Watchdog disabled, LVI enabled, OCD interface
enabled. */
__root __far const unsigned char OptionByte[] @ 0x00C0 =
{
	0x6eU, 0xffU, 0xe8U, 0x85U
};

/* Security byte definition */
__root __far const unsigned char SecuIDCode[]  @ 0x00C4 =
{
	0x55, 0x55, 0x55, 0x55, 0x55, 0x55, 0x55, 0x55, 0x55, 0x54
};

/*-----------------------------------------------------------*/

short main( void )
{
	/* Creates all the tasks and timers, then starts the scheduler. */

	/* First create the 'standard demo' tasks.  These are used to demonstrate
	API functions being used and also to test the kernel port.  More information
	is provided on the FreeRTOS.org WEB site. */
	vStartDynamicPriorityTasks();
	vStartPolledQueueTasks( tskIDLE_PRIORITY );
	vCreateBlockTimeTasks();

	/* Create the RegTest tasks as described at the top of this file. */
	xTaskCreate( vRegTest1, "Reg1", configMINIMAL_STACK_SIZE, NULL, 0, NULL );
	xTaskCreate( vRegTest2, "Reg2", configMINIMAL_STACK_SIZE, NULL, 0, NULL );

	/* Create the software timer that performs the 'check' functionality,
	as described at the top of this file. */
	xCheckTimer = xTimerCreate( "CheckTimer",/* A text name, purely to help debugging. */
								( mainCHECK_TIMER_PERIOD_MS ),		/* The timer period, in this case 3000ms (3s). */
								pdTRUE,								/* This is an auto-reload timer, so xAutoReload is set to pdTRUE. */
								( void * ) 0,						/* The ID is not used, so can be set to anything. */
								prvCheckTimerCallback				/* The callback function that inspects the status of all the other tasks. */
							  );

	/* Create the software timer that just increments a variable for demo
	purposes. */
	xDemoTimer = xTimerCreate( "DemoTimer",/* A text name, purely to help debugging. */
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

static void prvDemoTimerCallback( TimerHandle_t xTimer )
{
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

	/* Inspect the status of the reg test tasks. */
	if( sRegTestStatus != pdPASS )
	{
		xErrorStatus = pdFAIL;
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
	mainLED_0 = !mainLED_0;
}
/*-----------------------------------------------------------*/

int __low_level_init(void)
{
unsigned char ucResetFlag = RESF;

	portDISABLE_INTERRUPTS();

	/* Clock Configuration:
	In this port, to use the internal high speed clock source of the
	microcontroller, define the configCLOCK_SOURCE as 1 in FreeRTOSConfig.h.  To
	use an external	clock define configCLOCK_SOURCE as 0. */
	#if configCLOCK_SOURCE == 1
	{
		/* Set fMX */
		CMC = 0x00;
		MSTOP = 1U;

		/* Set fMAIN */
		MCM0 = 0U;

		/* Set fSUB */
		XTSTOP = 1U;
		OSMC = 0x10;

		/* Set fCLK */
		CSS = 0U;

		/* Set fIH */
		HIOSTOP = 0U;
	}
	#else
	{
		unsigned char ucTempStabset, ucTempStabWait;

		/* Set fMX */
		CMC = 0x41;
		OSTS = 0x07;
		MSTOP = 0U;
		ucTempStabset = 0xFF;

		do
		{
			ucTempStabWait = OSTC;
			ucTempStabWait &= ucTempStabset;
		}
		while( ucTempStabWait != ucTempStabset );

		/* Set fMAIN */
		MCM0 = 1U;

		/* Set fSUB */
		XTSTOP = 1U;
		OSMC = 0x10;

		/* Set fCLK */
		CSS = 0U;

		/* Set fIH */
		HIOSTOP = 0U;
	}
	#endif /* configCLOCK_SOURCE == 1 */

	/* LED port initialization - set port register. */
	P7 &= 0x7F;

	/* Set port mode register. */
	PM7 &= 0x7F;

	/* Switch pin initialization - enable pull-up resistor. */
	PU12_bit.no0  = 1;

	return pdTRUE;
}
/*-----------------------------------------------------------*/

void vRegTestError( void )
{
	/* Called by the RegTest tasks if an error is found.  lRegTestStatus is
	inspected by the check task. */
	sRegTestStatus = pdFAIL;

	/* Do not return from here as the reg test tasks clobber all registers so
	function calls may not function correctly. */
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

void vApplicationStackOverflowHook( TaskHandle_t pxTask, char *pcTaskName )
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

