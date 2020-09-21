/*
 * FreeRTOS Kernel V10.3.0
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
 * into several smaller programs of which this is the second.  This enables the
 * demo's to be executed on the RAM limited 40 pin devices.  The 64 and 80 pin
 * devices require a more costly development platform and are not so readily
 * available.
 *
 * The RTOSDemo2 project is configured for a PIC18F452 device.  Main2.c starts
 * 5 tasks (including the idle task).
 *
 * The first, second and third tasks do nothing but flash an LED.  This gives
 * visual feedback that everything is executing as expected.  One task flashes
 * an LED every 333ms (i.e. on and off every 333/2 ms), then next every 666ms
 * and the last every 999ms.
 *
 * The last task runs at the idle priority.  It repeatedly performs a 32bit
 * calculation and checks it's result against the expected value.  This checks
 * that the temporary storage utilised by the compiler to hold intermediate
 * results does not get corrupted when the task gets switched in and out.
 * should the calculation ever provide an incorrect result the final LED is
 * turned on.
 *
 * On entry to main() an 'X' is transmitted.  Monitoring the serial port using a
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
#include "flash.h"
#include "partest.h"
#include "serial.h"

/* Priority definitions for the LED tasks.  Other tasks just use the idle
priority. */
#define mainLED_FLASH_PRIORITY			( tskIDLE_PRIORITY + ( unsigned portBASE_TYPE ) 1 )

/* The LED that is lit when should the calculation fail. */
#define mainCHECK_TASK_LED				( ( unsigned portBASE_TYPE ) 3 )

/* Constants required for the communications.  Only one character is ever
transmitted. */
#define mainCOMMS_QUEUE_LENGTH			( ( unsigned portBASE_TYPE ) 5 )
#define mainNO_BLOCK					( ( TickType_t ) 0 )
#define mainBAUD_RATE					( ( unsigned long ) 9600 )

/*
 * The task that performs the 32 bit calculation at the idle priority.
 */
static void vCalculationTask( void *pvParameters );

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

	/* Start the standard LED flash tasks as defined in demo/common/minimal. */
	vStartLEDFlashTasks( mainLED_FLASH_PRIORITY );

	/* Start the check task defined in this file. */
	xTaskCreate( vCalculationTask, "Check", configMINIMAL_STACK_SIZE, NULL, tskIDLE_PRIORITY, NULL );

	/* Start the scheduler. */
	vTaskStartScheduler();
}
/*-----------------------------------------------------------*/

static void vCalculationTask( void *pvParameters )
{
volatile unsigned long ulCalculatedValue; /* Volatile to ensure optimisation is minimal. */

	/* Continuously perform a calculation.  If the calculation result is ever
	incorrect turn the LED on. */
	for( ;; )
	{
		/* A good optimising compiler would just remove all this! */
		ulCalculatedValue = 1234UL;
		ulCalculatedValue *= 99UL;

		if( ulCalculatedValue != 122166UL )
		{
			vParTestSetLED( mainCHECK_TASK_LED, pdTRUE );
		}

		ulCalculatedValue *= 9876UL;

		if( ulCalculatedValue != 1206511416UL )
		{
			vParTestSetLED( mainCHECK_TASK_LED, pdTRUE );
		}

		ulCalculatedValue /= 15UL;

		if( ulCalculatedValue != 80434094UL )
		{
			vParTestSetLED( mainCHECK_TASK_LED, pdTRUE );
		}

		ulCalculatedValue += 918273UL;

		if( ulCalculatedValue != 81352367UL )
		{
			vParTestSetLED( mainCHECK_TASK_LED, pdTRUE );
		}
	}
}
/*-----------------------------------------------------------*/

