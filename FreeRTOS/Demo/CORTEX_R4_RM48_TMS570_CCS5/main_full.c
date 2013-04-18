/*
    FreeRTOS V7.4.1 - Copyright (C) 2013 Real Time Engineers Ltd.

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
    and the FreeRTOS license exception along with FreeRTOS; if not it can be
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
#define mainCHECK_TIMER_PERIOD_MS			( 3000UL / portTICK_RATE_MS )

/* The period after which the LED timer will expire, converted to ticks. */
#define mainLED_TIMER_PERIOD_MS				( 75UL / portTICK_RATE_MS )

/* Constants for the ComTest tasks. */
#define mainCOM_TEST_BAUD_RATE				( ( unsigned long ) 19200 )
#define mainCOM_TEST_LED					( 100 )

/*-----------------------------------------------------------*/

/*
 * The check timer callback function, as described at the top of this file.
 */
static void prvCheckTimerCallback( xTimerHandle xTimer );

/*
 * The LED timer callback function, as described at the top of this file.
 */
static void prvLEDTimerCallback( xTimerHandle xTimer );

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
xTimerHandle xTimer = NULL;

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
	xTaskCreate( vRegTestTask1, ( const signed char * ) "Reg1...", configMINIMAL_STACK_SIZE, NULL, tskIDLE_PRIORITY, NULL );
	xTaskCreate( vRegTestTask2, ( const signed char * ) "Reg2...", configMINIMAL_STACK_SIZE, NULL, tskIDLE_PRIORITY, NULL );
	

	/* Create the software timer that performs the 'check' functionality,
	as described at the top of this file. */
	xTimer = xTimerCreate( ( const signed char * ) "CheckTimer",/* A text name, purely to help debugging. */
							( mainCHECK_TIMER_PERIOD_MS ),		/* The timer period, in this case 3000ms (3s). */
							pdTRUE,								/* This is an auto-reload timer, so xAutoReload is set to pdTRUE. */
							( void * ) 0,						/* The ID is not used, so can be set to anything. */
							prvCheckTimerCallback				/* The callback function that inspects the status of all the other tasks. */
						 );
	
	if( xTimer != NULL )
	{
		xTimerStart( xTimer, mainDONT_BLOCK );
	}

	/* Create the software timer that performs the 'LED spin' functionality,
	as described at the top of this file. */
	xTimer = xTimerCreate( ( const signed char * ) "LEDTimer",	/* A text name, purely to help debugging. */
							( mainLED_TIMER_PERIOD_MS ),		/* The timer period, in this case 75ms. */
							pdTRUE,								/* This is an auto-reload timer, so xAutoReload is set to pdTRUE. */
							( void * ) 0,						/* The ID is not used, so can be set to anything. */
							prvLEDTimerCallback					/* The callback function that toggles the white LEDs. */
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

static void prvCheckTimerCallback( xTimerHandle xTimer )
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

static void prvLEDTimerCallback( xTimerHandle xTimer )
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

