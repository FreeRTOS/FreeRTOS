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

/******************************************************************************
 * NOTE 1:  This project provides two demo applications.  A low power tickless
 * project, and a more comprehensive test and demo application.  The
 * configCREATE_LOW_POWER_DEMO setting in FreeRTOSConfig.h is used to
 * select between the two.  See the notes on using
 * configCREATE_LOW_POWER_DEMO in FreeRTOSConfig.h.  This file implements
 * the comprehensive test and demo version.
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
 * 200ms.  The check software timer callback function also toggles an LED each
 * time it is called.  This provides a visual indication of the system status:
 * If the LED toggles every three seconds, then no issues have been discovered.
 * If the LED toggles every 200ms, then an issue has been discovered with at
 * least one task.
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
#include "PollQ.h"
#include "semtest.h"
#include "dynamic.h"
#include "BlockQ.h"
#include "blocktim.h"
#include "countsem.h"
#include "GenQTest.h"
#include "recmutex.h"
#include "partest.h"

/* Atmel library includes. */
#include "asf.h"

/* Priorities for the demo application tasks. */
#define mainQUEUE_POLL_PRIORITY				( tskIDLE_PRIORITY + 2UL )
#define mainSEM_TEST_PRIORITY				( tskIDLE_PRIORITY + 1UL )
#define mainBLOCK_Q_PRIORITY				( tskIDLE_PRIORITY + 2UL )

/* A block time of zero simply means "don't block". */
#define mainDONT_BLOCK						( 0UL )

/* The period after which the check timer will expire providing no errors
have been reported by any of the standard demo tasks.  ms are converted to the
equivalent in ticks using the portTICK_RATE_MS constant. */
#define mainCHECK_TIMER_PERIOD_MS			( 3000UL / portTICK_RATE_MS )

/* The period at which the check timer will expire, in ms, if an error has been
reported in one of the standard demo tasks.  ms are converted to the equivalent
in ticks using the portTICK_RATE_MS constant. */
#define mainERROR_CHECK_TIMER_PERIOD_MS 	( 200UL / portTICK_RATE_MS )

/* The LED toggled by the check timer. */
#define mainCHECK_LED						( 0 )

/*-----------------------------------------------------------*/

/*
 * The check timer callback function, as described at the top of this file.
 */
static void prvCheckTimerCallback( xTimerHandle xTimer );

/*-----------------------------------------------------------*/

void main_full( void )
{
xTimerHandle xCheckTimer = NULL;

	/* Start all the other standard demo/test tasks.  They have not particular
	functionality, but do demonstrate how to use the FreeRTOS API and test the
	kernel port. */
	vStartDynamicPriorityTasks();
	vStartBlockingQueueTasks( mainBLOCK_Q_PRIORITY );
	vCreateBlockTimeTasks();
	vStartCountingSemaphoreTasks();
	vStartGenericQueueTasks( tskIDLE_PRIORITY );
	vStartRecursiveMutexTasks();
	vStartPolledQueueTasks( mainQUEUE_POLL_PRIORITY );
	vStartSemaphoreTasks( mainSEM_TEST_PRIORITY );

	/* Create the software timer that performs the 'check' functionality,
	as described at the top of this file. */
	xCheckTimer = xTimerCreate( ( const signed char * ) "CheckTimer",/* A text name, purely to help debugging. */
								( mainCHECK_TIMER_PERIOD_MS ),		/* The timer period, in this case 3000ms (3s). */
								pdTRUE,								/* This is an auto-reload timer, so xAutoReload is set to pdTRUE. */
								( void * ) 0,						/* The ID is not used, so can be set to anything. */
								prvCheckTimerCallback				/* The callback function that inspects the status of all the other tasks. */
							  );

	if( xCheckTimer != NULL )
	{
		xTimerStart( xCheckTimer, mainDONT_BLOCK );
	}

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
static long lChangedTimerPeriodAlready = pdFALSE;
unsigned long ulErrorFound = pdFALSE;

	/* Check all the demo tasks (other than the flash tasks) to ensure
	they are all still running, and that none have detected an error. */

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

	if( xArePollingQueuesStillRunning() != pdTRUE )
	{
		ulErrorFound = pdTRUE;
	}

	if( xAreSemaphoreTasksStillRunning() != pdTRUE )
	{
		ulErrorFound = pdTRUE;
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

