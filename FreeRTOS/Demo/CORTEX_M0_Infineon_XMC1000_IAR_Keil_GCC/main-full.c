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
 * main_full() creates a set of standard demo tasks, some application specific
 * tasks, and four timers.  It then starts the scheduler.  The web documentation
 * provides more details of the standard demo application tasks, which provide
 * no particular functionality, but do provide a good example of how to use the
 * FreeRTOS API.
 *
 * In addition to the standard demo tasks, the following tasks and timer are
 * defined and/or created within this file:
 *
 * "Reg test" tasks - These fill the registers with known values, then check
 * that each register maintains its expected value for the lifetime of the
 * task.  Each task uses a different set of values.  The reg test tasks execute
 * with a very low priority, so get preempted very frequently.  A register
 * containing an unexpected value is indicative of an error in the context
 * switching mechanism.
 *
 * "Interrupt semaphore take" task - This task does nothing but block on a
 * semaphore that is 'given' from the tick hook function (which is defined in
 * main.c).  It toggles the fourth LED each time it receives the semaphore.  The
 * Semahore is given every 50ms, so LED 4 toggles every 50ms.
 *
 * "Flash timers" - A software timer callback function is defined that does
 * nothing but toggle an LED.  Three software timers are created that each
 * use the same callback function, but each toggles a different LED at a
 * different frequency.  The timers control the first three LEDs.
 *
 * "Check" software timer - The check timer period is initially set to three
 * seconds.  Its callback function checks that all the standard demo tasks, and
 * the register check tasks, are not only still executing, but are executing
 * without reporting any errors.  If the check timer callback discovers that a
 * task has either stalled, or reported an error, then it changes the period of
 * the check timer from the initial three seconds, to just 200ms.  The callback
 * function also toggles the fifth LED each time it is called.  This provides a
 * visual indication of the system status:  If the LED toggles every three
 * seconds then no issues have been discovered.  If the LED toggles every 200ms,
 * then an issue has been discovered with at least one task.
 */

/* Kernel includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"
#include "semphr.h"
#include "timers.h"

/* Common demo includes. */
#include "blocktim.h"
#include "countsem.h"
#include "recmutex.h"
#include "partest.h"
#include "dynamic.h"
#include "QueueOverwrite.h"
#include "QueueSet.h"

/* The period after which the check timer will expire provided no errors have
been reported by any of the standard demo tasks.  ms are converted to the
equivalent in ticks using the portTICK_PERIOD_MS constant. */
#define mainCHECK_TIMER_PERIOD_MS			( 3000UL / portTICK_PERIOD_MS )

/* The period at which the check timer will expire if an error has been
reported in one of the standard demo tasks.  ms are converted to the equivalent
in ticks using the portTICK_PERIOD_MS constant. */
#define mainERROR_CHECK_TIMER_PERIOD_MS 	( 200UL / portTICK_PERIOD_MS )

/* A block time of zero simply means "don't block". */
#define mainDONT_BLOCK						( 0UL )

/* The base toggle rate used by the flash timers.  Each toggle rate is a
multiple of this. */
#define mainFLASH_TIMER_BASE_RATE			( 200UL / portTICK_PERIOD_MS )

/* The LED toggle by the check timer. */
#define mainCHECK_LED						( 4 )

/* The LED toggled each time the task implemented by the prvSemaphoreTakeTask()
function takes the semaphore that is given by the tick hook function. */
#define mainSEMAPHORE_LED					( 3 )

/*-----------------------------------------------------------*/

/*
 * Register check tasks, as described at the top of this file.  The nature of
 * these files necessitates that they are written in an assembly.
 */
extern void vRegTest1Task( void *pvParameters );
extern void vRegTest2Task( void *pvParameters );

/*
 * The hardware only has a single LED.  Simply toggle it.
 */
extern void vMainToggleLED( void );

/*
 * The check timer callback function, as described at the top of this file.
 */
static void prvCheckTimerCallback( TimerHandle_t xTimer );

/*
 * The flash timer callback function, as described at the top of this file.
 * This callback function is assigned to three separate software timers.
 */
static void prvFlashTimerCallback( TimerHandle_t xTimer );

/*
 * The task that toggles an LED each time the semaphore 'given' by the tick
 * hook function (which is defined in main.c) is 'taken' in the task.
 */
static void prvSemaphoreTakeTask( void *pvParameters );

/*
 * Called by main() to create the comprehensive test/demo application if
 * mainCREATE_SIMPLE_BLINKY_DEMO_ONLY is not set to 1.
 */
void main_full( void );

/*-----------------------------------------------------------*/

/* The following two variables are used to communicate the status of the
register check tasks to the check software timer.  If the variables keep
incrementing, then the register check tasks have not discovered any errors.  If
a variable stops incrementing, then an error has been found. */
volatile unsigned long ulRegTest1LoopCounter = 0UL, ulRegTest2LoopCounter = 0UL;

/* The semaphore that is given by the tick hook function (defined in main.c)
and taken by the task implemented by the prvSemaphoreTakeTask() function.  The
task toggles LED mainSEMAPHORE_LED each time the semaphore is taken. */
SemaphoreHandle_t xLEDSemaphore = NULL;
/*-----------------------------------------------------------*/

void main_full( void )
{
TimerHandle_t xTimer = NULL;
unsigned long ulTimer;
const unsigned long ulTimersToCreate = 3L;
/* The register test tasks are asm functions that don't use a stack.  The
stack allocated just has to be large enough to hold the task context, and
for the additional required for the stack overflow checking to work (if
configured). */
const size_t xRegTestStackSize = 25U;

	/* Create the standard demo tasks */
	vCreateBlockTimeTasks();
	vStartDynamicPriorityTasks();
	vStartCountingSemaphoreTasks();
	vStartRecursiveMutexTasks();
	vStartQueueOverwriteTask( tskIDLE_PRIORITY );
	vStartQueueSetTasks();

	/* Create that is given from the tick hook function, and the task that
	toggles an LED each time the semaphore is given. */
	vSemaphoreCreateBinary( xLEDSemaphore );
	xTaskCreate( 	prvSemaphoreTakeTask, 		/* Function that implements the task. */
					"Sem", 						/* Text name of the task. */
					configMINIMAL_STACK_SIZE, 	/* Stack allocated to the task (in words). */
					NULL, 						/* The task parameter is not used. */
					configMAX_PRIORITIES - 2, 	/* The priority of the task. */
					NULL );						/* Don't receive a handle back, it is not needed. */

	/* Create the register test tasks as described at the top of this file.
	These are naked functions that don't use any stack.  A stack still has
	to be allocated to hold the task context. */
	xTaskCreate( 	vRegTest1Task,			/* Function that implements the task. */
					"Reg1", 				/* Text name of the task. */
					xRegTestStackSize,		/* Stack allocated to the task. */
					NULL, 					/* The task parameter is not used. */
					tskIDLE_PRIORITY, 		/* The priority to assign to the task. */
					NULL );					/* Don't receive a handle back, it is not needed. */

	xTaskCreate( 	vRegTest2Task,			/* Function that implements the task. */
					"Reg2", 				/* Text name of the task. */
					xRegTestStackSize,		/* Stack allocated to the task. */
					NULL, 					/* The task parameter is not used. */
					tskIDLE_PRIORITY, 		/* The priority to assign to the task. */
					NULL );					/* Don't receive a handle back, it is not needed. */

	/* Create the three flash timers. */
	for( ulTimer = 0UL; ulTimer < ulTimersToCreate; ulTimer++ )
	{
		xTimer = xTimerCreate( 	"FlashTimer",							/* A text name, purely to help debugging. */
								( mainFLASH_TIMER_BASE_RATE * ( ulTimer + 1UL ) ),	/* The timer period, in this case 3000ms (3s). */
								pdTRUE,									/* This is an auto-reload timer, so xAutoReload is set to pdTRUE. */
								( void * ) ulTimer,						/* The ID is used to hold the number of the LED that will be flashed. */
								prvFlashTimerCallback					/* The callback function that inspects the status of all the other tasks. */
							);

		if( xTimer != NULL )
		{
			xTimerStart( xTimer, mainDONT_BLOCK );
		}
	}

	/* Create the software timer that performs the 'check' functionality,
	as described at the top of this file. */
	xTimer = xTimerCreate( 	"CheckTimer",					/* A text name, purely to help debugging. */
							( mainCHECK_TIMER_PERIOD_MS ),	/* The timer period, in this case 3000ms (3s). */
							pdTRUE,							/* This is an auto-reload timer, so xAutoReload is set to pdTRUE. */
							( void * ) 0,					/* The ID is not used, so can be set to anything. */
							prvCheckTimerCallback			/* The callback function that inspects the status of all the other tasks. */
					  	);

	/* If the software timer was created successfully, start it.  It won't
	actually start running until the scheduler starts.  A block time of
	zero is used in this call, although any value could be used as the block
	time will be ignored because the scheduler has not started yet. */
	if( xTimer != NULL )
	{
		xTimerStart( xTimer, mainDONT_BLOCK );
	}

	/* Start the kernel.  From here on, only tasks and interrupts will run. */
	vTaskStartScheduler();

	/* If all is well, the scheduler will now be running, and the following
	line will never be reached.  If the following line does execute, then there
	was	insufficient FreeRTOS heap memory available for the idle and/or timer
	tasks to be created.  See the memory management section on the FreeRTOS web
	site, or the FreeRTOS tutorial books for more details. */
	for( ;; );
}
/*-----------------------------------------------------------*/

/* See the description at the top of this file. */
static void prvCheckTimerCallback( TimerHandle_t xTimer )
{
static long lChangedTimerPeriodAlready = pdFALSE;
static unsigned long ulLastRegTest1Value = 0, ulLastRegTest2Value = 0;
unsigned long ulErrorFound = pdFALSE;

	/* Check all the demo and test tasks to ensure that they are all still
	running, and that none have detected an error. */
	if( xAreDynamicPriorityTasksStillRunning() != pdPASS )
	{
		ulErrorFound |= ( 0x01UL << 0UL );
	}

	if( xAreBlockTimeTestTasksStillRunning() != pdPASS )
	{
		ulErrorFound |= ( 0x01UL << 1UL );
	}

	if( xAreCountingSemaphoreTasksStillRunning() != pdPASS )
	{
		ulErrorFound |= ( 0x01UL << 2UL );
	}

	if( xAreRecursiveMutexTasksStillRunning() != pdPASS )
	{
		ulErrorFound |= ( 0x01UL << 3UL );
	}

	/* Check that the register test 1 task is still running. */
	if( ulLastRegTest1Value == ulRegTest1LoopCounter )
	{
		ulErrorFound |= ( 0x01UL << 4UL );
	}
	ulLastRegTest1Value = ulRegTest1LoopCounter;

	/* Check that the register test 2 task is still running. */
	if( ulLastRegTest2Value == ulRegTest2LoopCounter )
	{
		ulErrorFound |= ( 0x01UL << 5UL );
	}
	ulLastRegTest2Value = ulRegTest2LoopCounter;

	if( xAreQueueSetTasksStillRunning() != pdPASS )
	{
		ulErrorFound |= ( 0x01UL << 6UL );
	}

	if( xIsQueueOverwriteTaskStillRunning() != pdPASS )
	{
		ulErrorFound |= ( 0x01UL << 7UL );
	}

	/* Toggle the check LED to give an indication of the system status.  If
	the LED toggles every mainCHECK_TIMER_PERIOD_MS milliseconds then
	everything is ok.  A faster toggle indicates an error. */
	vParTestToggleLED( mainCHECK_LED );

	/* Have any errors been latched in ulErrorFound?  If so, shorten the
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

static void prvSemaphoreTakeTask( void *pvParameters )
{
	configASSERT( xLEDSemaphore );

	for( ;; )
	{
		/* Wait to obtain the semaphore - which is given by the tick hook
		function every 50ms. */
		xSemaphoreTake( xLEDSemaphore, portMAX_DELAY );
		vParTestToggleLED( mainSEMAPHORE_LED );
	}
}
/*-----------------------------------------------------------*/

static void prvFlashTimerCallback( TimerHandle_t xTimer )
{
unsigned long ulLED;

	/* This callback function is assigned to three separate software timers.
	Each timer toggles a different LED.  Obtain the number of the LED that
	this timer is toggling. */
	ulLED = ( unsigned long ) pvTimerGetTimerID( xTimer );

	/* Toggle the LED. */
	vParTestToggleLED( ulLED );
}

