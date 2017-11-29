/*
 * FreeRTOS Kernel V10.0.0
 * Copyright (C) 2017 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software. If you wish to use our Amazon
 * FreeRTOS name, please do so in a fair use way that does not cause confusion.
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
 * THIS DEMO APPLICATION REQUIRES A LOOPBACK CONNECTOR TO BE FITTED TO THE PIC
 * USART PORT - connect pin 2 to pin 3 on J2.
 *
 * Instead of the normal single demo application, the PIC18F demo is split
 * into several smaller programs of which this is the third.  This enables the
 * demo's to be executed on the RAM limited 40 pin devices.  The 64 and 80 pin
 * devices require a more costly development platform and are not so readily
 * available.
 *
 * The RTOSDemo3 project is configured for a PIC18F452 device.  Main3.c starts
 * 5 tasks (including the idle task).
 *
 * The first task repeatedly transmits a string of characters on the PIC USART
 * port.  The second task receives the characters, checking that the correct
 * sequence is maintained (i.e. what is transmitted is identical to that
 * received).  Each transmitted and each received character causes an LED to
 * flash.  See demo/common/minimal/comtest. c for more information.
 *
 * The third task continuously performs a 32 bit calculation.  This is a good
 * test of the context switch mechanism as the 8 bit architecture requires
 * the use of several file registers to perform the 32 bit operations.  See
 * demo/common/minimal/integer. c for more information.
 *
 * The third task is the check task.  This periodically checks that the other
 * tasks are still running and have not experienced any errors.  If no errors
 * have been reported by either the comms or integer tasks an LED is flashed
 * with a frequency mainNO_ERROR_CHECK_PERIOD.  If an error is discovered the
 * frequency is increased to mainERROR_FLASH_RATE.
 *
 * The check task also provides a visual indication of a system reset by
 * flashing the one remaining LED (mainRESET_LED) when it starts.  After
 * this initial flash mainRESET_LED should remain off.
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
#include "partest.h"
#include "serial.h"
#include "comtest.h"
#include "integer.h"

/* Priority definitions for the LED tasks.  Other tasks just use the idle
priority. */
#define mainCOMM_TEST_PRIORITY			( tskIDLE_PRIORITY + ( unsigned portBASE_TYPE ) 2 )
#define mainCHECK_TASK_PRIORITY			( tskIDLE_PRIORITY + ( unsigned portBASE_TYPE ) 3 )

/* The period between executions of the check task before and after an error
has been discovered.  If an error has been discovered the check task runs
more frequently - increasing the LED flash rate. */
#define mainNO_ERROR_CHECK_PERIOD		( ( TickType_t ) 1000 / portTICK_PERIOD_MS )
#define mainERROR_CHECK_PERIOD			( ( TickType_t ) 100 / portTICK_PERIOD_MS )

/* The period for which mainRESET_LED remain on every reset. */
#define mainRESET_LED_PERIOD			( ( TickType_t ) 500 / portTICK_PERIOD_MS )

/* The LED that is toggled whenever a character is transmitted.
mainCOMM_TX_RX_LED + 1 will be toggled every time a character is received. */
#define mainCOMM_TX_RX_LED				( ( unsigned portBASE_TYPE ) 2 )

/* The LED that is flashed by the check task at a rate that indicates the
error status. */
#define mainCHECK_TASK_LED				( ( unsigned portBASE_TYPE ) 1 )

/* The LED that is flashed once upon every reset. */
#define mainRESET_LED					( ( unsigned portBASE_TYPE ) 0 )

/* Constants required for the communications. */
#define mainCOMMS_QUEUE_LENGTH			( ( unsigned portBASE_TYPE ) 5 )
#define mainBAUD_RATE					( ( unsigned long ) 57600 )
/*-----------------------------------------------------------*/

/*
 * Task function which periodically checks the other tasks for errors.  Flashes
 * an LED at a rate that indicates whether an error has ever been detected.
 */
static void vErrorChecks( void *pvParameters );

/*-----------------------------------------------------------*/

/* Creates the tasks, then starts the scheduler. */
void main( void )
{
	/* Initialise the required hardware. */
	vParTestInitialise();

	/* Initialise the block memory allocator. */
	vPortInitialiseBlocks();

	/* Start the standard comtest tasks as defined in demo/common/minimal. */
	vAltStartComTestTasks( mainCOMM_TEST_PRIORITY, mainBAUD_RATE, mainCOMM_TX_RX_LED );

	/* Start the standard 32bit calculation task as defined in
	demo/common/minimal. */
	vStartIntegerMathTasks( tskIDLE_PRIORITY );

	/* Start the check task defined in this file. */
	xTaskCreate( vErrorChecks, "Check", configMINIMAL_STACK_SIZE, NULL, mainCHECK_TASK_PRIORITY, NULL );

	/* Start the scheduler.  This will never return. */
	vTaskStartScheduler();
}
/*-----------------------------------------------------------*/

static void vErrorChecks( void *pvParameters )
{
TickType_t xDelayTime = mainNO_ERROR_CHECK_PERIOD;
volatile unsigned long ulDummy = 3UL;

	/* Toggle the LED so we can see when a reset occurs. */
	vParTestSetLED( mainRESET_LED, pdTRUE );
	vTaskDelay( mainRESET_LED_PERIOD );
	vParTestSetLED( mainRESET_LED, pdFALSE );

	/* Cycle for ever, delaying then checking all the other tasks are still
	operating without error. */
	for( ;; )
	{
		/* Wait until it is time to check the other tasks. */
		vTaskDelay( xDelayTime );

		/* Perform an integer calculation - just to ensure the registers
		get used.  The result is not important. */
		ulDummy *= 3UL;

		/* Check all the other tasks are running, and running without ever
		having an error.  The delay period is lowered if an error is reported,
		causing the LED to flash at a higher rate. */
		if( xAreIntegerMathsTaskStillRunning() == pdFALSE )
		{
			xDelayTime = mainERROR_CHECK_PERIOD;
		}

		if( xAreComTestTasksStillRunning() == pdFALSE )
		{
			xDelayTime = mainERROR_CHECK_PERIOD;
		}

		/* Flash the LED for visual feedback.  The rate of the flash will
		indicate the health of the system. */
		vParTestToggleLED( mainCHECK_TASK_LED );
	}
}
/*-----------------------------------------------------------*/

