/*
	FreeRTOS V5.4.2 - Copyright (C) 2009 Real Time Engineers Ltd.

	This file is part of the FreeRTOS distribution.

	FreeRTOS is free software; you can redistribute it and/or modify it	under 
	the terms of the GNU General Public License (version 2) as published by the 
	Free Software Foundation and modified by the FreeRTOS exception.
	**NOTE** The exception to the GPL is included to allow you to distribute a
	combined work that includes FreeRTOS without being obliged to provide the 
	source code for proprietary components outside of the FreeRTOS kernel.  
	Alternative commercial license and support terms are also available upon 
	request.  See the licensing section of http://www.FreeRTOS.org for full 
	license details.

	FreeRTOS is distributed in the hope that it will be useful,	but WITHOUT
	ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
	FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
	more details.

	You should have received a copy of the GNU General Public License along
	with FreeRTOS; if not, write to the Free Software Foundation, Inc., 59
	Temple Place, Suite 330, Boston, MA  02111-1307  USA.


	***************************************************************************
	*                                                                         *
	* Looking for a quick start?  Then check out the FreeRTOS eBook!          *
	* See http://www.FreeRTOS.org/Documentation for details                   *
	*                                                                         *
	***************************************************************************

	1 tab == 4 spaces!

	Please ensure to read the configuration and relevant port sections of the
	online documentation.

	http://www.FreeRTOS.org - Documentation, latest information, license and
	contact details.

	http://www.SafeRTOS.com - A version that is certified for use in safety
	critical systems.

	http://www.OpenRTOS.com - Commercial support, development, porting,
	licensing and training services.
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
#define mainNO_ERROR_CHECK_PERIOD	( ( portTickType ) 10000 / portTICK_RATE_MS )
#define mainERROR_CHECK_PERIOD		( ( portTickType )  1000 / portTICK_RATE_MS )
#define mainCHECK_TASK_LED			( ( unsigned portCHAR ) 3 )

/* Priority definitions for some of the tasks.  Other tasks just use the idle
priority. */
#define mainCHECK_TASK_PRIORITY	( tskIDLE_PRIORITY + ( unsigned portCHAR ) 2 )
#define mainCOMM_TEST_PRIORITY	( tskIDLE_PRIORITY + ( unsigned portCHAR ) 1 )

/* The LED that is toggled whenever a character is transmitted.
mainCOMM_TX_RX_LED + 1 will be toggled every time a character is received. */
#define mainCOMM_TX_RX_LED		( ( unsigned portCHAR ) 0 )

/* Constants required for the communications. */
#define mainBAUD_RATE			( ( unsigned portLONG ) 57600 )

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

	/* Start a few of the standard demo tasks found in the demo\common directory. */
	vAltStartComTestTasks( mainCOMM_TEST_PRIORITY, mainBAUD_RATE, mainCOMM_TX_RX_LED );

	/* Start the check task defined in this file. */
	xTaskCreate( vErrorChecks, ( const portCHAR * const ) "Check", portMINIMAL_STACK_SIZE, NULL, mainCHECK_TASK_PRIORITY, NULL );

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

	if( xAreComTestTasksStillRunning() != pdTRUE )
	{
		cErrorHasOccurred = ( portCHAR ) pdTRUE;
	}

	return cErrorHasOccurred;
}
/*-----------------------------------------------------------*/


