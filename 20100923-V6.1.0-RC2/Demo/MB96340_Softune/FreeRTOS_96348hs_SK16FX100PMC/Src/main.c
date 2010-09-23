/*
    FreeRTOS V6.1.0 - Copyright (C) 2010 Real Time Engineers Ltd.

    ***************************************************************************
    *                                                                         *
    * If you are:                                                             *
    *                                                                         *
    *    + New to FreeRTOS,                                                   *
    *    + Wanting to learn FreeRTOS or multitasking in general quickly       *
    *    + Looking for basic training,                                        *
    *    + Wanting to improve your FreeRTOS skills and productivity           *
    *                                                                         *
    * then take a look at the FreeRTOS books - available as PDF or paperback  *
    *                                                                         *
    *        "Using the FreeRTOS Real Time Kernel - a Practical Guide"        *
    *                  http://www.FreeRTOS.org/Documentation                  *
    *                                                                         *
    * A pdf reference manual is also available.  Both are usually delivered   *
    * to your inbox within 20 minutes to two hours when purchased between 8am *
    * and 8pm GMT (although please allow up to 24 hours in case of            *
    * exceptional circumstances).  Thank you for your support!                *
    *                                                                         *
    ***************************************************************************

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation AND MODIFIED BY the FreeRTOS exception.
    ***NOTE*** The exception to the GPL is included to allow you to distribute
    a combined work that includes FreeRTOS without being obliged to provide the
    source code for proprietary components outside of the FreeRTOS kernel.
    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT
    ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
    FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
    more details. You should have received a copy of the GNU General Public 
    License and the FreeRTOS license exception along with FreeRTOS; if not it 
    can be viewed here: http://www.freertos.org/a00114.html and also obtained 
    by writing to Richard Barry, contact details for whom are available on the
    FreeRTOS WEB site.

    1 tab == 4 spaces!

    http://www.FreeRTOS.org - Documentation, latest information, license and
    contact details.

    http://www.SafeRTOS.com - A version that is certified for use in safety
    critical systems.

    http://www.OpenRTOS.com - Commercial support, development, porting,
    licensing and training services.
*/

/*
 * Creates all the demo application tasks, then starts the scheduler.  The WEB
 * documentation provides more details of the demo application tasks.
 * 
 * In addition to the standard demo tasks, the follow demo specific tasks are
 * create:
 *
 * The "Check" task.  This only executes every three seconds but has the highest 
 * priority so is guaranteed to get processor time.  Its main function is to 
 * check that all the other tasks are still operational.  Most tasks maintain 
 * a unique count that is incremented each time the task successfully completes 
 * its function.  Should any error occur within such a task the count is 
 * permanently halted.  The check task inspects the count of each task to ensure 
 * it has changed since the last time the check task executed.  If all the count 
 * variables have changed all the tasks are still executing error free, and the 
 * check task toggles the onboard LED.  Should any task contain an error at any time 
 * the LED toggle rate will change from 3 seconds to 500ms.
 *
 * The "Trace Utility" task.  This can be used to obtain trace and debug 
 * information via UART1.
 */


/* Scheduler includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "semphr.h"

/* Demo application includes. */
#include "flash.h"
#include "integer.h"
#include "comtest2.h"
#include "PollQ.h"
#include "semtest.h"
#include "BlockQ.h"
#include "dynamic.h"
#include "flop.h"
#include "GenQTest.h"
#include "QPeek.h"
#include "blocktim.h"
#include "death.h"
#include "taskutility.h"
#include "partest.h"
#include "crflash.h"
#include "watchdog.h"

/* Library includes. */
#include <watchdog.h>

/*-----------------------------------------------------------*/

/* Demo task priorities. */
#define WTC_TASK_PRIORITY			( tskIDLE_PRIORITY + 5 )
#define mainCHECK_TASK_PRIORITY		( tskIDLE_PRIORITY + 4 )
#define TASK_UTILITY_PRIORITY		( tskIDLE_PRIORITY )
#define mainSEM_TEST_PRIORITY		( tskIDLE_PRIORITY + 3 )
#define mainCOM_TEST_PRIORITY		( tskIDLE_PRIORITY + 2 )
#define mainQUEUE_POLL_PRIORITY		( tskIDLE_PRIORITY + 2 )
#define mainQUEUE_BLOCK_PRIORITY	( tskIDLE_PRIORITY + 2 )
#define mainDEATH_PRIORITY			( tskIDLE_PRIORITY + 1 )
#define mainLED_TASK_PRIORITY		( tskIDLE_PRIORITY + 1 )
#define mainGENERIC_QUEUE_PRIORITY	( tskIDLE_PRIORITY )

/* Baud rate used by the COM test tasks. */
#define mainCOM_TEST_BAUD_RATE	( ( unsigned long ) 19200 )

/* The frequency at which the 'Check' tasks executes.  See the comments at the 
top of the page.  When the system is operating error free the 'Check' task
toggles an LED every three seconds.  If an error is discovered in any task the
rate is increased to 500 milliseconds.  [in this case the '*' characters on the 
LCD represent LED's] */
#define mainNO_ERROR_CHECK_DELAY	( (portTickType) 3000 / portTICK_RATE_MS )
#define mainERROR_CHECK_DELAY		( (portTickType) 500 / portTICK_RATE_MS )

/* LED assignments for the demo tasks. */
#define mainNUM_FLASH_CO_ROUTINES	8
#define mainCOM_TEST_LED			0x05
#define mainCHECK_TEST_LED			0x07

/*-----------------------------------------------------------*/

/* 
 * The function that implements the Check task.  See the comments at the head
 * of the page for implementation details.
 */
static void	vErrorChecks( void *pvParameters );

/*
 * Called by the Check task.  Returns pdPASS if all the other tasks are found
 * to be operating without error - otherwise returns pdFAIL.
 */
static short prvCheckOtherTasksAreStillRunning( void );

/*
 * Perform any hardware setup necessary for the demo.
 */
static void prvSetupHardware( void );

/*-----------------------------------------------------------*/

void main( void )
{
	InitIrqLevels();		/* Initialize interrupts */
	__set_il( 7 );			/* Allow all levels      */

	prvSetupHardware();

	#if WATCHDOG == WTC_IN_TASK
		vStartWatchdogTask( WTC_TASK_PRIORITY );
	#endif

	/* Start the standard demo application tasks. */
	vStartLEDFlashTasks( mainLED_TASK_PRIORITY );
	vStartIntegerMathTasks( tskIDLE_PRIORITY );	
	vStartPolledQueueTasks( mainQUEUE_POLL_PRIORITY );
	vStartSemaphoreTasks( mainSEM_TEST_PRIORITY );
	vStartBlockingQueueTasks( mainQUEUE_BLOCK_PRIORITY );
	vStartDynamicPriorityTasks();
	vStartFlashCoRoutines( mainNUM_FLASH_CO_ROUTINES );
	vStartGenericQueueTasks( mainGENERIC_QUEUE_PRIORITY );
	vCreateBlockTimeTasks();

	/* The definition INCLUDE_TraceListTasks is set within FreeRTOSConfig.h. */
	#if INCLUDE_TraceListTasks == 1
		vUtilityStartTraceTask( TASK_UTILITY_PRIORITY );
	#else
		vAltStartComTestTasks( mainCOM_TEST_PRIORITY, mainCOM_TEST_BAUD_RATE, mainCOM_TEST_LED - 1 );
	#endif

	/* Start the 'Check' task which is defined in this file. */
	xTaskCreate( vErrorChecks, (signed char *) "Check", configMINIMAL_STACK_SIZE, NULL, mainCHECK_TASK_PRIORITY, NULL );

	/* The suicide tasks must be started last as they record the number of other
	tasks that exist within the system.  The value is then used to ensure at run
	time the number of tasks that exists is within expected bounds. */
	vCreateSuicidalTasks( mainDEATH_PRIORITY );

	/* Now start the scheduler.  Following this call the created tasks should
	be executing. */	
	vTaskStartScheduler( );
	
	/* vTaskStartScheduler() will only return if an error occurs while the 
	idle task is being created. */
	for( ;; );
}
/*-----------------------------------------------------------*/

static void prvSetupHardware( void )
{
	/* Initialise the port used by the LEDs. */
	vParTestInitialise();

	/* See watchdog.h for definitions relating to the watchdog use. */
	#if WATCHDOG != WTC_NONE
		InitWatchdog();
	#endif
}
/*-----------------------------------------------------------*/

static void vErrorChecks( void *pvParameters )
{
portTickType xDelayPeriod = mainNO_ERROR_CHECK_DELAY;

	/* Just to remove compiler warnings. */
	( void ) pvParameters;

	/* Cycle for ever, delaying then checking all the other tasks are still
	operating without error. */
	for( ;; )
	{
		/* Wait until it is time to check again.  The time we wait here depends
		on whether an error has been detected or not.  When an error is 
		detected the time is shortened resulting in a faster LED flash rate. */
		vTaskDelay( xDelayPeriod );

		/* See if the other tasks are all ok. */
		if( prvCheckOtherTasksAreStillRunning() != pdPASS )
		{
			/* An error occurred in one of the tasks so shorten the delay 
			period - which has the effect of increasing the frequency of the
			LED toggle. */
			xDelayPeriod = mainERROR_CHECK_DELAY;
		}

		/* Flash! */
		vParTestToggleLED( mainCHECK_TEST_LED );
	}
}
/*-----------------------------------------------------------*/

static short prvCheckOtherTasksAreStillRunning( void )
{
	static short	sNoErrorFound = pdTRUE;

	/* The demo tasks maintain a count that increments every cycle of the task
	provided that the task has never encountered an error.  This function 
	checks the counts maintained by the tasks to ensure they are still being
	incremented.  A count remaining at the same value between calls therefore
	indicates that an error has been detected.  Only tasks that do not flash
	an LED are checked. */
	if( xAreIntegerMathsTaskStillRunning() != pdTRUE )
	{
		sNoErrorFound = pdFALSE;
	}

	if( xArePollingQueuesStillRunning() != pdTRUE )
	{
		sNoErrorFound = pdFALSE;
	}

	if( xAreSemaphoreTasksStillRunning() != pdTRUE )
	{
		sNoErrorFound = pdFALSE;
	}

	if( xAreBlockingQueuesStillRunning() != pdTRUE )
	{
		sNoErrorFound = pdFALSE;
	}

	if( xAreDynamicPriorityTasksStillRunning() != pdTRUE )
	{
		sNoErrorFound = pdFALSE;
	}

	if( xAreFlashCoRoutinesStillRunning() != pdTRUE )
	{
		sNoErrorFound = pdFALSE;
	}

	if( xAreGenericQueueTasksStillRunning() != pdTRUE )
	{
		sNoErrorFound = pdFALSE;
	}

	if( xAreBlockTimeTestTasksStillRunning() != pdTRUE )
	{
		sNoErrorFound = pdFALSE;
	}

	if( xIsCreateTaskStillRunning() != pdTRUE )
	{
		sNoErrorFound = pdFALSE;
	}

	#if INCLUDE_TraceListTasks == 0
	{
		if( xAreComTestTasksStillRunning() != pdTRUE )
		{
			sNoErrorFound = pdFALSE;
		}
	}
	#endif

	return sNoErrorFound;
}
/*-----------------------------------------------------------*/

/* Idle hook function. */
#if configUSE_IDLE_HOOK == 1
	void vApplicationIdleHook( void )
	{
		/* Are we using the idle task to kick the watchdog?  See watchdog.h
		for watchdog kicking options. Note this is for demonstration only
		and is not a suggested method of servicing the watchdog in a real
		application. */
		#if WATCHDOG == WTC_IN_IDLE
			Kick_Watchdog();
		#endif

		vCoRoutineSchedule();
	}
#else
	#if WATCHDOG == WTC_IN_IDLE
		#error configUSE_IDLE_HOOK must be set to 1 in FreeRTOSConfig.h if the watchdog is being cleared in the idle task hook.
	#endif
#endif

/*-----------------------------------------------------------*/

/* Tick hook function. */
#if configUSE_TICK_HOOK == 1
	void vApplicationTickHook( void )
	{
		/* Are we using the tick to kick the watchdog?  See watchdog.h
		for watchdog kicking options.  Note this is for demonstration
		only and is not a suggested method of servicing the watchdog in
		a real application. */
		#if WATCHDOG == WTC_IN_TICK
			Kick_Watchdog();
		#endif
	}
#else
	#if WATCHDOG == WTC_IN_TICK
		#error configUSE_TICK_HOOK must be set to 1 in FreeRTOSConfig.h if the watchdog is being cleared in the tick hook.
	#endif
#endif
/*-----------------------------------------------------------*/
