/*
 * FreeRTOS Kernel V10.1.0
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
	NOTE : Tasks run in system mode and the scheduler runs in Supervisor mode.
	The processor MUST be in supervisor mode when vTaskStartScheduler is 
	called.  The demo applications included in the FreeRTOS.org download switch
	to supervisor mode prior to main being called.  If you are not using one of
	these demo application projects then ensure Supervisor mode is used.
*/


/*
 * Creates all the demo application tasks, then starts the scheduler.  The WEB
 * documentation provides more details of the demo application tasks.
 * 
 * Main.c also creates a task called "Check".  This only executes every three 
 * seconds but has the highest priority so is guaranteed to get processor time.  
 * Its main function is to check that all the other tasks are still operational.
 * Each task (other than the "flash" tasks) maintains a unique count that is 
 * incremented each time the task successfully completes its function.  Should 
 * any error occur within such a task the count is permanently halted.  The 
 * check task inspects the count of each task to ensure it has changed since
 * the last time the check task executed.  If all the count variables have 
 * changed all the tasks are still executing error free, and the check task
 * toggles the onboard LED.  Should any task contain an error at any time 
 * the LED toggle rate will change from 3 seconds to 500ms.
 *
 */

/* Standard includes. */
#include <stdlib.h>

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "task.h"

/* Demo application includes. */
#include "partest.h"
#include "flash.h"
#include "comtest2.h"
#include "serial.h"
#include "PollQ.h"
#include "BlockQ.h"
#include "semtest.h"
#include "dynamic.h"

/*-----------------------------------------------------------*/

/* Constants to setup I/O and processor. */
#define mainTX_ENABLE		( ( unsigned long ) 0x00010000 )	/* UART1. */
#define mainRX_ENABLE		( ( unsigned long ) 0x00040000 ) 	/* UART1. */
#define mainBUS_CLK_FULL	( ( unsigned char ) 0x01 )
#define mainLED_TO_OUTPUT	( ( unsigned long ) 0xff0000 )

/* Constants for the ComTest demo application tasks. */
#define mainCOM_TEST_BAUD_RATE	( ( unsigned long ) 115200 )
#define mainCOM_TEST_LED		( 3 )

/* Priorities for the demo application tasks. */
#define mainLED_TASK_PRIORITY		( tskIDLE_PRIORITY + 2 )
#define mainCOM_TEST_PRIORITY		( tskIDLE_PRIORITY + 2 )
#define mainQUEUE_POLL_PRIORITY		( tskIDLE_PRIORITY + 2 )
#define mainBLOCK_Q_PRIORITY		( tskIDLE_PRIORITY + 2 )
#define mainSEM_TEST_PRIORITY		( tskIDLE_PRIORITY + 1 )
#define mainCHECK_TASK_PRIORITY		( tskIDLE_PRIORITY + 3 )

/* Constants used by the "check" task.  As described at the head of this file
the check task toggles an LED.  The rate at which the LED flashes is used to
indicate whether an error has been detected or not.  If the LED toggles every
3 seconds then no errors have been detected.  If the rate increases to 500ms
then an error has been detected in at least one of the demo application tasks. */
#define mainCHECK_LED				( 7 )
#define mainNO_ERROR_FLASH_PERIOD	( ( TickType_t ) 3000 / portTICK_PERIOD_MS  )
#define mainERROR_FLASH_PERIOD		( ( TickType_t ) 500 / portTICK_PERIOD_MS  )

/*-----------------------------------------------------------*/

/*
 * Checks that all the demo application tasks are still executing without error
 * - as described at the top of the file.
 */
static long prvCheckOtherTasksAreStillRunning( void );

/*
 * The task that executes at the highest priority and calls 
 * prvCheckOtherTasksAreStillRunning().  See the description at the top
 * of the file.
 */
static void vErrorChecks( void *pvParameters );

/*
 * Configure the processor for use with the Keil demo board.  This is very
 * minimal as most of the setup is managed by the settings in the project
 * file.
 */
static void prvSetupHardware( void );

/*-----------------------------------------------------------*/



/*
 * Application entry point:
 * Starts all the other tasks, then starts the scheduler. 
 */
int main( void )
{
	/* Setup the hardware for use with the Keil demo board. */
	prvSetupHardware();

	/* Start the demo/test application tasks. */
	vAltStartComTestTasks( mainCOM_TEST_PRIORITY, mainCOM_TEST_BAUD_RATE, mainCOM_TEST_LED );
	vStartLEDFlashTasks( mainLED_TASK_PRIORITY );
	vStartPolledQueueTasks( mainQUEUE_POLL_PRIORITY );
	vStartBlockingQueueTasks( mainBLOCK_Q_PRIORITY );
	vStartSemaphoreTasks( mainSEM_TEST_PRIORITY );
	vStartDynamicPriorityTasks();

	/* Start the check task - which is defined in this file.  This is the task
	that periodically checks to see that all the other tasks are executing 
	without error. */
	xTaskCreate( vErrorChecks, "Check", configMINIMAL_STACK_SIZE, NULL, mainCHECK_TASK_PRIORITY, NULL );

	/* Now all the tasks have been started - start the scheduler.

	NOTE : Tasks run in system mode and the scheduler runs in Supervisor mode.
	The processor MUST be in supervisor mode when vTaskStartScheduler is 
	called.  The demo applications included in the FreeRTOS.org download switch
	to supervisor mode prior to main being called.  If you are not using one of
	these demo application projects then ensure Supervisor mode is used here. */
	vTaskStartScheduler();

	/* Should never reach here!  If you do then there was not enough heap
	available for the idle task to be created. */
	for( ;; );
}
/*-----------------------------------------------------------*/

static void vErrorChecks( void *pvParameters )
{
TickType_t xDelayPeriod = mainNO_ERROR_FLASH_PERIOD;

	/* Parameters are not used. */
	( void ) pvParameters;

	/* Cycle for ever, delaying then checking all the other tasks are still
	operating without error.  If an error is detected then the delay period
	is decreased from mainNO_ERROR_FLASH_PERIOD to mainERROR_FLASH_PERIOD so
	the on board LED flash rate will increase.

	This task runs at the highest priority. */

	for( ;; )
	{
		/* The period of the delay depends on whether an error has been 
		detected or not.  If an error has been detected then the period
		is reduced to increase the LED flash rate. */
		vTaskDelay( xDelayPeriod );

		if( prvCheckOtherTasksAreStillRunning() != pdPASS )
		{
			/* An error has been detected in one of the tasks - flash faster. */
			xDelayPeriod = mainERROR_FLASH_PERIOD;
		}

		/* Toggle the LED before going back to wait for the next cycle. */
		vParTestToggleLED( mainCHECK_LED );
	}
}
/*-----------------------------------------------------------*/

static void prvSetupHardware( void )
{
	/* Perform the hardware setup required.  This is minimal as most of the
	setup is managed by the settings in the project file. */

	/* Configure the UART1 pins.  All other pins remain at their default of 0. */
	PINSEL0 |= mainTX_ENABLE;
	PINSEL0 |= mainRX_ENABLE;

	/* LED pins need to be output. */
	IODIR1 = mainLED_TO_OUTPUT;

	/* Setup the peripheral bus to be the same as the PLL output. */
	VPBDIV = mainBUS_CLK_FULL;
}
/*-----------------------------------------------------------*/

static long prvCheckOtherTasksAreStillRunning( void )
{
long lReturn = pdPASS;

	/* Check all the demo tasks (other than the flash tasks) to ensure
	that they are all still running, and that none of them have detected
	an error. */
	if( xAreComTestTasksStillRunning() != pdPASS )
	{
		lReturn = pdFAIL;
	}

	if( xArePollingQueuesStillRunning() != pdTRUE )
	{
		lReturn = pdFAIL;
	}

	if( xAreBlockingQueuesStillRunning() != pdTRUE )
	{
		lReturn = pdFAIL;
	}

	if( xAreSemaphoreTasksStillRunning() != pdTRUE )
	{
		lReturn = pdFAIL;
	}

	if( xAreDynamicPriorityTasksStillRunning() != pdTRUE )
	{
		lReturn = pdFAIL;
	}

	return lReturn;
}
/*-----------------------------------------------------------*/


