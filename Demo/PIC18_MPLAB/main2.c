/*
	FreeRTOS.org V4.1.2 - Copyright (C) 2003-2006 Richard Barry.

	This file is part of the FreeRTOS.org distribution.

	FreeRTOS.org is free software; you can redistribute it and/or modify
	it under the terms of the GNU General Public License as published by
	the Free Software Foundation; either version 2 of the License, or
	(at your option) any later version.

	FreeRTOS.org is distributed in the hope that it will be useful,
	but WITHOUT ANY WARRANTY; without even the implied warranty of
	MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
	GNU General Public License for more details.

	You should have received a copy of the GNU General Public License
	along with FreeRTOS.org; if not, write to the Free Software
	Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA

	A special exception to the GPL can be applied should you wish to distribute
	a combined work that includes FreeRTOS.org, without being obliged to provide
	the source code for any proprietary components.  See the licensing section 
	of http://www.FreeRTOS.org for full details of how and when the exception
	can be applied.

	***************************************************************************
	See http://www.FreeRTOS.org for documentation, latest information, license 
	and contact details.  Please ensure to read the configuration and relevant 
	port sections of the online documentation.
	***************************************************************************
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
	  portTickType rather than unsigned portLONG.
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
#define mainNO_BLOCK					( ( portTickType ) 0 )
#define mainBAUD_RATE					( ( unsigned portLONG ) 9600 )

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
	xTaskCreate( vCalculationTask, ( const portCHAR * const ) "Check", configMINIMAL_STACK_SIZE, NULL, tskIDLE_PRIORITY, NULL );

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

