/*
	FreeRTOS.org V4.3.1 - Copyright (C) 2003-2007 Richard Barry.

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

	Also see http://www.SafeRTOS.com for an IEC 61508 compliant version along
	with commercial development and support options.
	***************************************************************************
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
#define mainNO_ERROR_CHECK_PERIOD	( ( portTickType ) 10000 / portTICK_RATE_MS )
#define mainERROR_CHECK_PERIOD		( ( portTickType )  1000 / portTICK_RATE_MS )
#define mainCHECK_TASK_LED			( ( unsigned portCHAR ) 3 )

/* Priority definitions for some of the tasks.  Other tasks just use the idle
priority. */
#define mainCHECK_TASK_PRIORITY		( tskIDLE_PRIORITY + ( unsigned portCHAR ) 2 )
#define mainLED_FLASH_PRIORITY		( tskIDLE_PRIORITY + ( unsigned portCHAR ) 2 )
#define mainCREATOR_TASK_PRIORITY	( tskIDLE_PRIORITY + ( unsigned portCHAR ) 1 )

/* Constants required for the communications.  Only one character is ever 
transmitted. */
#define mainCOMMS_QUEUE_LENGTH		( ( unsigned portCHAR ) 5 )
#define mainNO_BLOCK				( ( portTickType ) 0 )
#define mainBAUD_RATE				( ( unsigned portLONG ) 57600 )

/*
 * The task function for the "Check" task.
 */
static portTASK_FUNCTION_PROTO( vErrorChecks, pvParameters );

/*
 * Checks the unique counts of other tasks to ensure they are still operational.
 * Returns pdTRUE if an error is detected, otherwise pdFALSE.
 */
static portCHAR prvCheckOtherTasksAreStillRunning( void );

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
	xTaskCreate( vErrorChecks, ( const portCHAR * const ) "Check", portMINIMAL_STACK_SIZE, NULL, mainCHECK_TASK_PRIORITY, NULL );

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
portTickType xLastCheckTime;
portTickType xDelayTime = mainNO_ERROR_CHECK_PERIOD;
portCHAR cErrorOccurred;

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

static portCHAR prvCheckOtherTasksAreStillRunning( void )
{
	portCHAR cErrorHasOccurred = ( portCHAR ) pdFALSE;

	if( xIsCreateTaskStillRunning() != pdTRUE )
	{
		cErrorHasOccurred = ( portCHAR ) pdTRUE;
	}

	return cErrorHasOccurred;
}
/*-----------------------------------------------------------*/


