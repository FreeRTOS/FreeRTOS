/*
 * FreeRTOS Kernel V10.4.1
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
 * Instead of the normal single demo application, the PIC18F demo is split
 * into several smaller programs of which this is the first.  This enables the
 * demo's to be executed on the RAM limited 40 pin devices.  The 64 and 80 pin
 * devices require a more costly development platform and are not so readily
 * available.
 *
 * The RTOSDemo1 project is configured for a PIC18F452 device.  Main1.c starts 5
 * tasks (including the idle task).
 *
 * The first task runs at the idle priority.  It repeatedly performs a 32bit
 * calculation and checks it's result against the expected value.  This checks
 * that the temporary storage utilised by the compiler to hold intermediate
 * results does not get corrupted when the task gets switched in and out.  See
 * demo/common/minimal/integer.c for more information.
 *
 * The second and third tasks pass an incrementing value between each other on
 * a message queue.  See demo/common/minimal/PollQ.c for more information.
 *
 * Main1.c also creates a check task.  This periodically checks that all the
 * other tasks are still running and have not experienced any unexpected
 * results.  If all the other tasks are executing correctly an LED is flashed
 * once every mainCHECK_PERIOD milliseconds.  If any of the tasks have not
 * executed, or report and error, the frequency of the LED flash will increase
 * to mainERROR_FLASH_RATE.
 *
 * On entry to main an 'X' is transmitted.  Monitoring the serial port using a
 * dumb terminal allows for verification that the device is not continuously
 * being reset (no more than one 'X' should be transmitted).
 *
 * http://www.FreeRTOS.org contains important information on the use of the
 * PIC18F port.
 */

/*
Changes from V2.0.0

	+ Delay periods are now specified using variables and constants of
	  TickType_t rather than unsigned long.
*/

/* Scheduler include files. */
#include "FreeRTOS.h"
#include "task.h"

/* Demo app include files. */
#include "PollQ.h"
#include "integer.h"
#include "partest.h"
#include "serial.h"

/* The period between executions of the check task before and after an error
has been discovered.  If an error has been discovered the check task runs
more frequently - increasing the LED flash rate. */
#define mainNO_ERROR_CHECK_PERIOD		( ( TickType_t ) 1000 / portTICK_PERIOD_MS )
#define mainERROR_CHECK_PERIOD			( ( TickType_t ) 100 / portTICK_PERIOD_MS )

/* Priority definitions for some of the tasks.  Other tasks just use the idle
priority. */
#define mainQUEUE_POLL_PRIORITY			( tskIDLE_PRIORITY + 2 )
#define mainCHECK_TASK_PRIORITY			( tskIDLE_PRIORITY + 3 )

/* The LED that is flashed by the check task. */
#define mainCHECK_TASK_LED				( 0 )

/* Constants required for the communications.  Only one character is ever
transmitted. */
#define mainCOMMS_QUEUE_LENGTH			( 5 )
#define mainNO_BLOCK					( ( TickType_t ) 0 )
#define mainBAUD_RATE					( ( unsigned long ) 9600 )

/*
 * The task function for the "Check" task.
 */
static void vErrorChecks( void *pvParameters );

/*
 * Checks the unique counts of other tasks to ensure they are still operational.
 * Returns pdTRUE if an error is detected, otherwise pdFALSE.
 */
static portBASE_TYPE prvCheckOtherTasksAreStillRunning( void );

/*-----------------------------------------------------------*/

/* Creates the tasks, then starts the scheduler. */
void main( void )
{
	/* Initialise the required hardware. */
	vParTestInitialise();
	vPortInitialiseBlocks();

	/* Send a character so we have some visible feedback of a reset. */
	xSerialPortInitMinimal( mainBAUD_RATE, mainCOMMS_QUEUE_LENGTH );
	xSerialPutChar( NULL, 'X', mainNO_BLOCK );

	/* Start the standard demo tasks found in the demo\common directory. */
	vStartIntegerMathTasks( tskIDLE_PRIORITY );
	vStartPolledQueueTasks( mainQUEUE_POLL_PRIORITY );

	/* Start the check task defined in this file. */
	xTaskCreate( vErrorChecks, "Check", configMINIMAL_STACK_SIZE, NULL, mainCHECK_TASK_PRIORITY, NULL );

	/* Start the scheduler.  Will never return here. */
	vTaskStartScheduler();
}
/*-----------------------------------------------------------*/

static void vErrorChecks( void *pvParameters )
{
TickType_t xDelayTime = mainNO_ERROR_CHECK_PERIOD;
portBASE_TYPE xErrorOccurred;

	/* Cycle for ever, delaying then checking all the other tasks are still
	operating without error. */
	for( ;; )
	{
		/* Wait until it is time to check the other tasks. */
		vTaskDelay( xDelayTime );

		/* Check all the other tasks are running, and running without ever
		having an error. */
		xErrorOccurred = prvCheckOtherTasksAreStillRunning();

		/* If an error was detected increase the frequency of the LED flash. */
		if( xErrorOccurred == pdTRUE )
		{
			xDelayTime = mainERROR_CHECK_PERIOD;
		}

		/* Flash the LED for visual feedback. */
		vParTestToggleLED( mainCHECK_TASK_LED );
	}
}
/*-----------------------------------------------------------*/

static portBASE_TYPE prvCheckOtherTasksAreStillRunning( void )
{
portBASE_TYPE xErrorHasOccurred = pdFALSE;

	if( xAreIntegerMathsTaskStillRunning() != pdTRUE )
	{
		xErrorHasOccurred = pdTRUE;
	}

	if( xArePollingQueuesStillRunning() != pdTRUE )
	{
		xErrorHasOccurred = pdTRUE;
	}

	return xErrorHasOccurred;
}
/*-----------------------------------------------------------*/


