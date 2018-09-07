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

/*
Changes from V3.0.0

Changes from V3.0.1
*/

/*
 * Instead of the normal single demo application, the PIC18F demo is split
 * into several smaller programs of which this is the sixth.  This enables the
 * demo's to be executed on the RAM limited PIC-devices.
 *
 * The Demo6 project is configured for a PIC18F4620 device.  Main.c starts 4
 * tasks (including the idle task). See the indicated files in the demo/common
 * directory for more information.
 *
 * demo/common/minimal/comtest.c:	Creates 2 tasks
 * ATTENTION: Comtest needs a loopback-connector on the serial port.
 *
 * Main.c also creates a check task.  This periodically checks that all the
 * other tasks are still running and have not experienced any unexpected
 * results.  If all the other tasks are executing correctly an LED is flashed
 * once every mainCHECK_PERIOD milliseconds.  If any of the tasks have not
 * executed, or report an error, the frequency of the LED flash will increase
 * to mainERROR_FLASH_RATE.
 *
 * http://www.FreeRTOS.org contains important information on the use of the
 * wizC PIC18F port.
 */

/* Scheduler include files. */
#include <FreeRTOS.h>
#include <task.h>

/* Demo app include files. */
#include "partest.h"
#include "serial.h"
#include "comtest.h"

/* The period between executions of the check task before and after an error
has been discovered.  If an error has been discovered the check task runs
more frequently - increasing the LED flash rate. */
#define mainNO_ERROR_CHECK_PERIOD	( ( TickType_t ) 10000 / portTICK_PERIOD_MS )
#define mainERROR_CHECK_PERIOD		( ( TickType_t )  1000 / portTICK_PERIOD_MS )
#define mainCHECK_TASK_LED			( ( unsigned char ) 3 )

/* Priority definitions for some of the tasks.  Other tasks just use the idle
priority. */
#define mainCHECK_TASK_PRIORITY	( tskIDLE_PRIORITY + ( unsigned char ) 2 )
#define mainCOMM_TEST_PRIORITY	( tskIDLE_PRIORITY + ( unsigned char ) 1 )

/* The LED that is toggled whenever a character is transmitted.
mainCOMM_TX_RX_LED + 1 will be toggled every time a character is received. */
#define mainCOMM_TX_RX_LED		( ( unsigned char ) 0 )

/* Constants required for the communications. */
#define mainBAUD_RATE			( ( unsigned long ) 57600 )

/*
 * The task function for the "Check" task.
 */
static portTASK_FUNCTION_PROTO( vErrorChecks, pvParameters );

/*
 * Checks the unique counts of other tasks to ensure they are still operational.
 * Returns pdTRUE if an error is detected, otherwise pdFALSE.
 */
static char prvCheckOtherTasksAreStillRunning( void );

/*-----------------------------------------------------------*/

/* Creates the tasks, then starts the scheduler. */
void main( void )
{
	/* Initialise the required hardware. */
	vParTestInitialise();

	/* Start a few of the standard demo tasks found in the demo\common directory. */
	vAltStartComTestTasks( mainCOMM_TEST_PRIORITY, mainBAUD_RATE, mainCOMM_TX_RX_LED );

	/* Start the check task defined in this file. */
	xTaskCreate( vErrorChecks, "Check", portMINIMAL_STACK_SIZE, NULL, mainCHECK_TASK_PRIORITY, NULL );

	/* Start the scheduler.  Will never return here. */
	vTaskStartScheduler();

	while(1)	/* This point should never be reached. */
	{
	}
}
/*-----------------------------------------------------------*/

static portTASK_FUNCTION( vErrorChecks, pvParameters )
{
TickType_t xLastCheckTime;
TickType_t xDelayTime = mainNO_ERROR_CHECK_PERIOD;
char cErrorOccurred;

	/* We need to initialise xLastCheckTime prior to the first call to
	vTaskDelayUntil(). */
	xLastCheckTime = xTaskGetTickCount();

	/* Cycle for ever, delaying then checking all the other tasks are still
	operating without error. */
	for( ;; )
	{
		/* Wait until it is time to check the other tasks again. */
		vTaskDelayUntil( &xLastCheckTime, xDelayTime );

		/* Check all the other tasks are running, and running without ever
		having an error. */
		cErrorOccurred = prvCheckOtherTasksAreStillRunning();

		/* If an error was detected increase the frequency of the LED flash. */
		if( cErrorOccurred == pdTRUE )
		{
			xDelayTime = mainERROR_CHECK_PERIOD;
		}

		/* Flash the LED for visual feedback. */
		vParTestToggleLED( mainCHECK_TASK_LED );
	}
}
/*-----------------------------------------------------------*/

static char prvCheckOtherTasksAreStillRunning( void )
{
	char cErrorHasOccurred = ( char ) pdFALSE;

	if( xAreComTestTasksStillRunning() != pdTRUE )
	{
		cErrorHasOccurred = ( char ) pdTRUE;
	}

	return cErrorHasOccurred;
}
/*-----------------------------------------------------------*/


