/*
    FreeRTOS V7.5.2 - Copyright (C) 2013 Real Time Engineers Ltd.

    VISIT http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

    ***************************************************************************
     *                                                                       *
     *    FreeRTOS provides completely free yet professionally developed,    *
     *    robust, strictly quality controlled, supported, and cross          *
     *    platform software that has become a de facto standard.             *
     *                                                                       *
     *    Help yourself get started quickly and support the FreeRTOS         *
     *    project by purchasing a FreeRTOS tutorial book, reference          *
     *    manual, or both from: http://www.FreeRTOS.org/Documentation        *
     *                                                                       *
     *    Thank you!                                                         *
     *                                                                       *
    ***************************************************************************

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation >>!AND MODIFIED BY!<< the FreeRTOS exception.

    >>! NOTE: The modification to the GPL is included to allow you to distribute
    >>! a combined work that includes FreeRTOS without being obliged to provide
    >>! the source code for proprietary components outside of the FreeRTOS
    >>! kernel.

    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT ANY
    WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
    FOR A PARTICULAR PURPOSE.  Full license text is available from the following
    link: http://www.freertos.org/a00114.html

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
    including FreeRTOS+Trace - an indispensable productivity tool, a DOS
    compatible FAT file system, and our tiny thread aware UDP/IP stack.

    http://www.OpenRTOS.com - Real Time Engineers ltd license FreeRTOS to High
    Integrity Systems to sell under the OpenRTOS brand.  Low cost OpenRTOS
    licenses offer ticketed support, indemnification and middleware.

    http://www.SafeRTOS.com - High Integrity Systems also provide a safety
    engineered and independently SIL3 certified version for use in safety and
    mission critical applications that require provable dependability.

    1 tab == 4 spaces!
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
 * "Flash timers" - A software timer callback function is defined that does
 * nothing but toggle an LED.  Three software timers are created that each
 * use the same callback function, but each toggles a different LED at a
 * different frequency.  One software timer uses LED1, another LED2 and the
 * third LED3.
 *
 * "Check" software timer - The check timer period is initially set to three
 * seconds.  Its callback function checks that all the standard demo tasks, and
 * the register check tasks, are not only still executing, but are executing
 * without reporting any errors.  If the check timer callback discovers that a
 * task has either stalled, or reported an error, then it changes the period of
 * the check timer from the initial three seconds, to just 200ms.  The callback
 * function also toggles LED 4 each time it is called.  This provides a visual
 * indication of the system status:  If the LED toggles every three seconds,
 * then no issues have been discovered.  If the LED toggles every 200ms, then
 * an issue has been discovered with at least one task.
 */

/* Kernel includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"
#include "timers.h"

/* Common demo includes. */
#include "blocktim.h"
#include "countsem.h"
#include "recmutex.h"
#include "ParTest.h"
#include "dynamic.h"

/* The period after which the check timer will expire provided no errors have
been reported by any of the standard demo tasks.  ms are converted to the
equivalent in ticks using the portTICK_RATE_MS constant. */
#define mainCHECK_TIMER_PERIOD_MS			( 3000UL / portTICK_RATE_MS )

/* The period at which the check timer will expire if an error has been
reported in one of the standard demo tasks.  ms are converted to the equivalent
in ticks using the portTICK_RATE_MS constant. */
#define mainERROR_CHECK_TIMER_PERIOD_MS 	( 200UL / portTICK_RATE_MS )

/* A block time of zero simply means "don't block". */
#define mainDONT_BLOCK						( 0UL )

/* The base toggle rate used by the flash timers.  Each toggle rate is a
multiple of this. */
#define mainFLASH_TIMER_BASE_RATE			( 200UL / portTICK_RATE_MS )

/* The LED toggle by the check timer. */
#define mainCHECK_LED						( 3 )
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
static void prvCheckTimerCallback( xTimerHandle xTimer );

/*
 * The flash timer callback function, as described at the top of this file.
 * This callback function is assigned to three separate software timers.
 */
static void prvFlashTimerCallback( xTimerHandle xTimer );

/*
 * Called by main() to create the comprehensive test/demo application if
 * mainCREATE_SIMPLE_BLINKY_DEMO_ONLY is not set to 1.
 */
void main_full( void );

/*-----------------------------------------------------------*/

/* The following two variables are used to communicate the status of the
register check tasks to the check software timer.  If the variables keep
incrementing, then the register check tasks has not discovered any errors.  If
a variable stops incrementing, then an error has been found. */
volatile unsigned long ulRegTest1LoopCounter = 0UL, ulRegTest2LoopCounter = 0UL;

/*-----------------------------------------------------------*/

void main_full( void )
{
xTimerHandle xTimer = NULL;
unsigned long ulTimer;
const unsigned long ulTimersToCreate = 3L;
/* The register test tasks are asm functions that don't use a stack.  The
stack allocated just has to be large enough to hold the task context, and
for the additional required for the stack overflow checking to work (if
configured). */
const size_t xRegTestStackSize = 25U;

	/* Create the standard demo tasks */
	vCreateBlockTimeTasks();
	vStartCountingSemaphoreTasks();
	vStartRecursiveMutexTasks();
	vStartDynamicPriorityTasks();

	/* Create the register test tasks as described at the top of this file.
	These are naked functions that don't use any stack.  A stack still has
	to be allocated to hold the task context. */
	xTaskCreate( 	vRegTest1Task,			/* Function that implements the task. */
					( signed char * ) "Reg1", /* Text name of the task. */
					xRegTestStackSize,		/* Stack allocated to the task. */
					NULL, 					/* The task parameter is not used. */
					tskIDLE_PRIORITY, 		/* The priority to assign to the task. */
					NULL );					/* Don't receive a handle back, it is not needed. */

	xTaskCreate( 	vRegTest2Task,			/* Function that implements the task. */
					( signed char * ) "Reg2", /* Text name of the task. */
					xRegTestStackSize,		/* Stack allocated to the task. */
					NULL, 					/* The task parameter is not used. */
					tskIDLE_PRIORITY, 		/* The priority to assign to the task. */
					NULL );					/* Don't receive a handle back, it is not needed. */

	/* Create the three flash timers. */
	for( ulTimer = 0UL; ulTimer < ulTimersToCreate; ulTimer++ )
	{
		xTimer = xTimerCreate( 	( const signed char * ) "FlashTimer",	/* A text name, purely to help debugging. */
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
	xTimer = xTimerCreate( 	( const signed char * ) "CheckTimer",/* A text name, purely to help debugging. */
							( mainCHECK_TIMER_PERIOD_MS ),		/* The timer period, in this case 3000ms (3s). */
							pdTRUE,								/* This is an auto-reload timer, so xAutoReload is set to pdTRUE. */
							( void * ) 0,						/* The ID is not used, so can be set to anything. */
							prvCheckTimerCallback				/* The callback function that inspects the status of all the other tasks. */
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
static void prvCheckTimerCallback( xTimerHandle xTimer )
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

static void prvFlashTimerCallback( xTimerHandle xTimer )
{
unsigned long ulLED;

	/* This callback function is assigned to three separate software timers.
	Each timer toggles a different LED.  Obtain the number of the LED that
	this timer is toggling. */
	ulLED = ( unsigned long ) pvTimerGetTimerID( xTimer );

	/* Toggle the LED. */
	vParTestToggleLED( ulLED );	
}

