/*
    FreeRTOS V6.0.5 - Copyright (C) 2010 Real Time Engineers Ltd.

    ***************************************************************************
    *                                                                         *
    * If you are:                                                             *
    *                                                                         *
    *    + New to FreeRTOS,                                                   *
    *    + Wanting to learn FreeRTOS or multitasking in general quickly       *
    *    + Looking for basic training,                                        *
    *    + Wanting to improve your FreeRTOS skills and productivity           *
    *                                                                         *
    * then take a look at the FreeRTOS eBook                                  *
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
 * This is a simple demo that creates a number of tasks from a pool of
 * 'standard demo tasks' which are used by all the FreeRTOS port demos.  The
 * standard demo tasks don't provide any useful functionality other than to
 * demonstrate the FreeRTOS API being used and show how the scheduler behaves.
 *
 * A COM test is included whereby one task transmits characters on the UART
 * which are then received by another task.  A loopback connector is required
 * on the UART1 connector for this test to pass (pins 2 and 3 need to be
 * connected together - a paper clip is usually all that is required).  LED
 * 5 red and green are under the control of the COM test tasks.  Red will toggle
 * each time a character is successfully transmitted, and the green LED toggles
 * for each received character.
 *
 * In addition this file creates a 'Check' task.  This periodically inspects
 * the standard demo tasks and makes a few other simple tests to see if the
 * system is performing as expected.  The check task toggles LED 6 green every
 * 3 seconds provided no errors exist and sets it to red if an error has
 * occurred.  The toggle rate will increase to 500ms if an error is detected
 * at any time.  This mechanism can be tested by removing the loopback
 * connector from UART1, and in so doing deliberately generating an error in
 * the COM test task.
 *
 * LED 1 through 4 are controlled by simple LED flashing tasks.  Each should
 * toggle at a fixed but different frequency.
 *
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* Environment header files. */
#include "pm.h"

/* Scheduler header files. */
#include "FreeRTOS.h"
#include "task.h"

/* Demo file headers. */
#include "partest.h"
#include "serial.h"
#include "integer.h"
#include "comtest.h"
#include "PollQ.h"
#include "semtest.h"
#include "dynamic.h"
#include "BlockQ.h"
#include "death.h"
#include "flop.h"
#include "flash.h"

/* Task priorities. */
#define mainLED_TASK_PRIORITY     ( tskIDLE_PRIORITY + 1 )
#define mainCOM_TEST_PRIORITY     ( tskIDLE_PRIORITY + 2 )
#define mainQUEUE_POLL_PRIORITY   ( tskIDLE_PRIORITY + 2 )
#define mainSEM_TEST_PRIORITY     ( tskIDLE_PRIORITY + 1 )
#define mainBLOCK_Q_PRIORITY      ( tskIDLE_PRIORITY + 3 )
#define mainCHECK_TASK_PRIORITY   ( tskIDLE_PRIORITY + 4 )
#define mainCREATOR_TASK_PRIORITY ( tskIDLE_PRIORITY + 3 )
#define mainFLASH_TASK_PRIORITY   ( tskIDLE_PRIORITY + 1 )

/* Baud rate used by the loopback test task. */
#define mainCOM_TEST_BAUD_RATE    ( ( unsigned long ) 38400 )

/* LED used by the serial port tasks.  This is toggled on each character Tx,
and mainCOM_TEST_LED + 1 is toggled on each character Rx. */
#define mainCOM_TEST_LED          ( 4 )

/* LED that is toggled by the check task.  The check task periodically checks
that all the other tasks are operating without error.  If an error is found at
any time the LED toggle frequency increases. */
#define mainCHECK_TASK_LED        ( 6 )

/* The frequency at which the check task executes assuming no errors have been
found.  portTICK_RATE_MS is used to convert milliseconds to ticks, depending on
the tick frequency. */
#define mainNO_ERROR_FLASH_RATE	  ( ( portTickType ) 3000 / portTICK_RATE_MS  )

/* The frequency at which the check task executes if an error has been found
in any of the demo tasks. */
#define mainERROR_FLASH_RATE      ( (portTickType) 500 / portTICK_RATE_MS )

/* The LED to use by the simple flash task. */
#define mainSIMPLE_FLASH_LED      ( 0 )

/* The frequency of the simple flashing LED. */
#define mainSIMPLE_FLASH_RATE     ( ( portTickType ) 200 / portTICK_RATE_MS )
/*-----------------------------------------------------------*/

/*
 * The 'Check' task that executes at the highest priority and calls
 * prvCheckOtherTasksAreStillRunning().  See the description at the top
 * of the file.
 */
static void prvErrorChecks( void *pvParameters );

/*
 * Checks that all the demo application tasks are still executing without error
 * - as described at the top of the file.
 */
static portBASE_TYPE prvCheckOtherTasksAreStillRunning( void );
/*-----------------------------------------------------------*/

int main( void )
{
	/* Start the crystal oscillator 0 and switch the main clock to it. */
	pm_switch_to_osc0(&AVR32_PM, FOSC0, OSC0_STARTUP);

	/* Setup the LED's for output. */
	vParTestInitialise();

	/* Start the standard demo tasks. */
	vAltStartComTestTasks( mainCOM_TEST_PRIORITY, mainCOM_TEST_BAUD_RATE, mainCOM_TEST_LED );
	vStartPolledQueueTasks( mainQUEUE_POLL_PRIORITY );
	vStartIntegerMathTasks( tskIDLE_PRIORITY );
	vStartSemaphoreTasks( mainSEM_TEST_PRIORITY );
	vStartDynamicPriorityTasks();
	vStartBlockingQueueTasks( mainBLOCK_Q_PRIORITY );
	vStartMathTasks( tskIDLE_PRIORITY );
	vStartLEDFlashTasks( mainLED_TASK_PRIORITY );

	/* Start the demo tasks defined within this file, first the check
	task as described at the top of this file. */
	xTaskCreate( prvErrorChecks,						/* The function that implements the task. */
			     ( const signed char * ) "ErrCheck",	/* The name of the task.  The kernel does not use this, its just to facilitate debugging. */
			     configMINIMAL_STACK_SIZE,  			/* The size of the stack (in words) that should be allocated to the task. */
			     NULL,  								/* No task parameter is being used. */
			     mainCHECK_TASK_PRIORITY,  				/* The priority to assign to the task, 0 being the lowest priority, configMAX_PRIORITIES - 1 being the highest priority. */
			     NULL );								/* Not interested in receiving a handle to the task being created, so just passing in NULL. */

	/* This task has to be created last as it keeps account of the number of
	tasks it expects to see running. */
	vCreateSuicidalTasks( mainCREATOR_TASK_PRIORITY );

	/* Start the scheduler. */
	vTaskStartScheduler();

	/* Will only get here if there was insufficient memory to create the idle
	task. */
	for( ;; );
}
/*-----------------------------------------------------------*/

static void prvErrorChecks( void *pvParameters )
{
portTickType xDelayPeriod = mainNO_ERROR_FLASH_RATE;

	/* The parameters are not used.  Prevent compiler warnings. */
	( void ) pvParameters;

	/* Cycle for ever, delaying then checking all the other tasks are still
	operating without error. */
	vParTestSetLED( mainCHECK_TASK_LED, pdFALSE );

	for( ;; )
	{
		/* Delay until it is time to execute again. */
		vTaskDelay( xDelayPeriod );

		/* Check all other tasks are still operating without error.
		Check that vMemCheckTask did increment the counter. */
		if( prvCheckOtherTasksAreStillRunning() != pdPASS )
		{
			/* An error has occurred in one of the tasks.  Increase the
			frequency at which this task executes and in so doing increase
			the rate at which the mainCHECK_TASK_LED toggles. */
			xDelayPeriod = mainERROR_FLASH_RATE;
			vParTestSetLED( mainCHECK_TASK_LED, pdTRUE );
		}

		/* Toggle the LED - the frequency of the LED toggle indicates the
		health of the system. */
		vParTestToggleLED( mainCHECK_TASK_LED + 1 );
	}
}
/*-----------------------------------------------------------*/

static portBASE_TYPE prvCheckOtherTasksAreStillRunning( void )
{
portBASE_TYPE xStatus = pdPASS;

	if( xAreComTestTasksStillRunning() != pdPASS )
	{
		xStatus = pdFAIL;
	}

	if( xArePollingQueuesStillRunning() != pdPASS )
	{
		xStatus = pdFAIL;
	}

	if( xAreIntegerMathsTaskStillRunning() != pdPASS )
	{
		xStatus = pdFAIL;
	}

	if( xAreSemaphoreTasksStillRunning() != pdPASS )
	{
		xStatus = pdFAIL;
	}

	if( xAreBlockingQueuesStillRunning() != pdPASS )
	{
		xStatus = pdFAIL;
	}

	if( xAreDynamicPriorityTasksStillRunning() != pdPASS )
	{
		xStatus = pdFAIL;
	}

	if( xAreMathsTaskStillRunning() != pdPASS )
	{
		xStatus = pdFAIL;
	}

	if( xIsCreateTaskStillRunning() != pdPASS )
	{
		xStatus = pdFAIL;
	}

	return xStatus;
}
/*-----------------------------------------------------------*/
