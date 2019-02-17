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

/*
Changes from V3.0.0

Changes from V3.0.1
*/

/*
 * Instead of the normal single demo application, the PIC18F demo is split
 * into several smaller programs of which this is the seventh.  This enables the
 * demo's to be executed on the RAM limited PIC-devices.
 *
 * The Demo7 project is configured for a PIC18F4620 device.  Main.c starts 10
 * tasks (including the idle task). See the indicated files in the demo/common
 * directory for more information.
 *
 * demo/common/minimal/flash.c:		Creates 3 tasks
 * demo/common/minimal/death.c:		Creates 1 controltask and
 *									creates/deletes 4 suicidaltasks
 *
 * Main.c also creates a check task.  This periodically checks that all the
 * other tasks are still running and have not experienced any unexpected
 * results.  If all the other tasks are executing correctly an LED is flashed
 * once every mainCHECK_PERIOD milliseconds.  If any of the tasks have not
 * executed, or report an error, the frequency of the LED flash will increase
 * to mainERROR_FLASH_RATE.
 *
 * On entry to main an 'X' is transmitted.  Monitoring the serial port using a
 * dumb terminal allows for verification that the device is not continuously
 * being reset (no more than one 'X' should be transmitted).
 *
 * http://www.FreeRTOS.org contains important information on the use of the
 * wizC PIC18F port.
 */

/* Scheduler include files. */
#include <FreeRTOS.h>
#include <task.h>

/* Demo app include files. */
#include "death.h"
#include "flash.h"
#include "partest.h"
#include "serial.h"

/* The period between executions of the check task before and after an error
has been discovered.  If an error has been discovered the check task runs
more frequently - increasing the LED flash rate. */
#define mainNO_ERROR_CHECK_PERIOD	( ( TickType_t ) 10000 / portTICK_PERIOD_MS )
#define mainERROR_CHECK_PERIOD		( ( TickType_t )  1000 / portTICK_PERIOD_MS )
#define mainCHECK_TASK_LED			( ( unsigned char ) 3 )

/* Priority definitions for some of the tasks.  Other tasks just use the idle
priority. */
#define mainCHECK_TASK_PRIORITY		( tskIDLE_PRIORITY + ( unsigned char ) 2 )
#define mainLED_FLASH_PRIORITY		( tskIDLE_PRIORITY + ( unsigned char ) 2 )
#define mainCREATOR_TASK_PRIORITY	( tskIDLE_PRIORITY + ( unsigned char ) 1 )

/* Constants required for the communications.  Only one character is ever
transmitted. */
#define mainCOMMS_QUEUE_LENGTH		( ( unsigned char ) 5 )
#define mainNO_BLOCK				( ( TickType_t ) 0 )
#define mainBAUD_RATE				( ( unsigned long ) 57600 )

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

	/* Send a character so we have some visible feedback of a reset. */
	xSerialPortInitMinimal( mainBAUD_RATE, mainCOMMS_QUEUE_LENGTH );
	xSerialPutChar( NULL, 'X', mainNO_BLOCK );

	/* Start a few of the standard demo tasks found in the demo\common directory. */
	vStartLEDFlashTasks( mainLED_FLASH_PRIORITY );

	/* Start the check task defined in this file. */
	xTaskCreate( vErrorChecks, "Check", portMINIMAL_STACK_SIZE, NULL, mainCHECK_TASK_PRIORITY, NULL );

	/* This task has to be created last as it keeps account of the number of tasks
	it expects to see running. */
	vCreateSuicidalTasks( mainCREATOR_TASK_PRIORITY );

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

	if( xIsCreateTaskStillRunning() != pdTRUE )
	{
		cErrorHasOccurred = ( char ) pdTRUE;
	}

	return cErrorHasOccurred;
}
/*-----------------------------------------------------------*/


