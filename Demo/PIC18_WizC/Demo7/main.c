/*
    FreeRTOS V7.0.2 - Copyright (C) 2011 Real Time Engineers Ltd.
	

    ***************************************************************************
     *                                                                       *
     *    FreeRTOS tutorial books are available in pdf and paperback.        *
     *    Complete, revised, and edited pdf reference manuals are also       *
     *    available.                                                         *
     *                                                                       *
     *    Purchasing FreeRTOS documentation will not only help you, by       *
     *    ensuring you get running as quickly as possible and with an        *
     *    in-depth knowledge of how to use FreeRTOS, it will also help       *
     *    the FreeRTOS project to continue with its mission of providing     *
     *    professional grade, cross platform, de facto standard solutions    *
     *    for microcontrollers - completely free of charge!                  *
     *                                                                       *
     *    >>> See http://www.FreeRTOS.org/Documentation for details. <<<     *
     *                                                                       *
     *    Thank you for using FreeRTOS, and thank you for your support!      *
     *                                                                       *
    ***************************************************************************


    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation AND MODIFIED BY the FreeRTOS exception.
    >>>NOTE<<< The modification to the GPL is included to allow you to
    distribute a combined work that includes FreeRTOS without being obliged to
    provide the source code for proprietary components outside of the FreeRTOS
    kernel.  FreeRTOS is distributed in the hope that it will be useful, but
    WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
    or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
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
#define mainCHECK_TASK_LED			( ( unsigned char ) 3 )

/* Priority definitions for some of the tasks.  Other tasks just use the idle
priority. */
#define mainCHECK_TASK_PRIORITY		( tskIDLE_PRIORITY + ( unsigned char ) 2 )
#define mainLED_FLASH_PRIORITY		( tskIDLE_PRIORITY + ( unsigned char ) 2 )
#define mainCREATOR_TASK_PRIORITY	( tskIDLE_PRIORITY + ( unsigned char ) 1 )

/* Constants required for the communications.  Only one character is ever 
transmitted. */
#define mainCOMMS_QUEUE_LENGTH		( ( unsigned char ) 5 )
#define mainNO_BLOCK				( ( portTickType ) 0 )
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
	xTaskCreate( vErrorChecks, ( const char * const ) "Check", portMINIMAL_STACK_SIZE, NULL, mainCHECK_TASK_PRIORITY, NULL );

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


