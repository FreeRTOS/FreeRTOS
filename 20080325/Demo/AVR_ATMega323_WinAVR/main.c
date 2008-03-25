/*
	FreeRTOS.org V4.7.2 - Copyright (C) 2003-2008 Richard Barry.

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

	Please ensure to read the configuration and relevant port sections of the 
	online documentation.

	+++ http://www.FreeRTOS.org +++
	Documentation, latest information, license and contact details.  

	+++ http://www.SafeRTOS.com +++
	A version that is certified for use in safety critical systems.

	+++ http://www.OpenRTOS.com +++
	Commercial support, development, porting, licensing and training services.

	***************************************************************************
*/

/*
 * Creates all the demo application tasks, then starts the scheduler.  The WEB
 * documentation provides more details of the demo application tasks.
 * 
 * Main. c also creates a task called "Check".  This only executes every three 
 * seconds but has the highest priority so is guaranteed to get processor time.  
 * Its main function is to check that all the other tasks are still operational.  
 * Each task that does not flash an LED maintains a unique count that is 
 * incremented each time the task successfully completes its function.  Should 
 * any error occur within such a task the count is permanently halted.  The 
 * check task inspects the count of each task to ensure it has changed since
 * the last time the check task executed.  If all the count variables have 
 * changed all the tasks are still executing error free, and the check task
 * toggles an LED.  Should any task contain an error at any time the LED toggle
 * will stop.
 *
 * The LED flash and communications test tasks do not maintain a count.
 */

/*
Changes from V1.2.0
	
	+ Changed the baud rate for the serial test from 19200 to 57600.

Changes from V1.2.3

	+ The integer and comtest tasks are now used when the cooperative scheduler 
	  is being used.  Previously they were only used with the preemptive
	  scheduler.

Changes from V1.2.5

	+ Set the baud rate to 38400.  This has a smaller error percentage with an
	  8MHz clock (according to the manual).

Changes from V2.0.0

	+ Delay periods are now specified using variables and constants of
	  portTickType rather than unsigned portLONG.

Changes from V2.6.1

	+ The IAR and WinAVR AVR ports are now maintained separately.

Changes from V4.0.5

	+ Modified to demonstrate the use of co-routines.

*/

#include <stdlib.h>
#include <string.h>

#ifdef GCC_MEGA_AVR
	/* EEPROM routines used only with the WinAVR compiler. */
	#include <avr/eeprom.h> 
#endif

/* Scheduler include files. */
#include "FreeRTOS.h"
#include "task.h"
#include "croutine.h"

/* Demo file headers. */
#include "PollQ.h"
#include "integer.h"
#include "serial.h"
#include "comtest.h"
#include "crflash.h"
#include "print.h"
#include "partest.h"
#include "regtest.h"

/* Priority definitions for most of the tasks in the demo application.  Some
tasks just use the idle priority. */
#define mainLED_TASK_PRIORITY			( tskIDLE_PRIORITY + 1 )
#define mainCOM_TEST_PRIORITY			( tskIDLE_PRIORITY + 2 )
#define mainQUEUE_POLL_PRIORITY			( tskIDLE_PRIORITY + 2 )
#define mainCHECK_TASK_PRIORITY			( tskIDLE_PRIORITY + 3 )

/* Baud rate used by the serial port tasks. */
#define mainCOM_TEST_BAUD_RATE			( ( unsigned portLONG ) 38400 )

/* LED used by the serial port tasks.  This is toggled on each character Tx,
and mainCOM_TEST_LED + 1 is toggles on each character Rx. */
#define mainCOM_TEST_LED				( 4 )

/* LED that is toggled by the check task.  The check task periodically checks
that all the other tasks are operating without error.  If no errors are found
the LED is toggled.  If an error is found at any time the LED is never toggles
again. */
#define mainCHECK_TASK_LED				( 7 )

/* The period between executions of the check task. */
#define mainCHECK_PERIOD				( ( portTickType ) 3000 / portTICK_RATE_MS  )

/* An address in the EEPROM used to count resets.  This is used to check that
the demo application is not unexpectedly resetting. */
#define mainRESET_COUNT_ADDRESS			( ( void * ) 0x50 )

/* The number of coroutines to create. */
#define mainNUM_FLASH_COROUTINES		( 3 )

/*
 * The task function for the "Check" task.
 */
static void vErrorChecks( void *pvParameters );

/*
 * Checks the unique counts of other tasks to ensure they are still operational.
 * Flashes an LED if everything is okay. 
 */
static void prvCheckOtherTasksAreStillRunning( void );

/*
 * Called on boot to increment a count stored in the EEPROM.  This is used to 
 * ensure the CPU does not reset unexpectedly.
 */
static void prvIncrementResetCount( void );

/*
 * The idle hook is used to scheduler co-routines.
 */
void vApplicationIdleHook( void );

/*-----------------------------------------------------------*/

portSHORT main( void )
{
	prvIncrementResetCount();

	/* Setup the LED's for output. */
	vParTestInitialise();

	/* Create the standard demo tasks. */
	vStartIntegerMathTasks( tskIDLE_PRIORITY );
	vAltStartComTestTasks( mainCOM_TEST_PRIORITY, mainCOM_TEST_BAUD_RATE, mainCOM_TEST_LED );
	vStartPolledQueueTasks( mainQUEUE_POLL_PRIORITY );
	vStartRegTestTasks();
	
	/* Create the tasks defined within this file. */
	xTaskCreate( vErrorChecks, "Check", configMINIMAL_STACK_SIZE, NULL, mainCHECK_TASK_PRIORITY, NULL );

	/* Create the co-routines that flash the LED's. */
	vStartFlashCoRoutines( mainNUM_FLASH_COROUTINES );
	
	/* In this port, to use preemptive scheduler define configUSE_PREEMPTION 
	as 1 in portmacro.h.  To use the cooperative scheduler define 
	configUSE_PREEMPTION as 0. */
	vTaskStartScheduler();

	return 0;
}
/*-----------------------------------------------------------*/

static void vErrorChecks( void *pvParameters )
{
static volatile unsigned portLONG ulDummyVariable = 3UL;

	/* The parameters are not used. */
	( void ) pvParameters;

	/* Cycle for ever, delaying then checking all the other tasks are still
	operating without error. */
	for( ;; )
	{
		vTaskDelay( mainCHECK_PERIOD );

		/* Perform a bit of 32bit maths to ensure the registers used by the 
		integer tasks get some exercise. The result here is not important - 
		see the demo application documentation for more info. */
		ulDummyVariable *= 3;
		
		prvCheckOtherTasksAreStillRunning();
	}
}
/*-----------------------------------------------------------*/

static void prvCheckOtherTasksAreStillRunning( void )
{
static portBASE_TYPE xErrorHasOccurred = pdFALSE;

	if( xAreIntegerMathsTaskStillRunning() != pdTRUE )
	{
		xErrorHasOccurred = pdTRUE;
	}

	if( xAreComTestTasksStillRunning() != pdTRUE )
	{
		xErrorHasOccurred = pdTRUE;
	}

	if( xArePollingQueuesStillRunning() != pdTRUE )
	{
		xErrorHasOccurred = pdTRUE;
	}

	if( xAreRegTestTasksStillRunning() != pdTRUE )
	{
		xErrorHasOccurred = pdTRUE;
	}
	
	if( xErrorHasOccurred == pdFALSE )
	{
		/* Toggle the LED if everything is okay so we know if an error occurs even if not
		using console IO. */
		vParTestToggleLED( mainCHECK_TASK_LED );
	}
}
/*-----------------------------------------------------------*/

static void prvIncrementResetCount( void )
{
unsigned portCHAR ucCount;

	eeprom_read_block( &ucCount, mainRESET_COUNT_ADDRESS, sizeof( ucCount ) );
	ucCount++;
	eeprom_write_byte( mainRESET_COUNT_ADDRESS, ucCount );
}
/*-----------------------------------------------------------*/

void vApplicationIdleHook( void )
{
	vCoRoutineSchedule();
}

