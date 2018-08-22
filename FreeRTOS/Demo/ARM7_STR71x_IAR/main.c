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

/* Library includes. */
#include "RCCU.h"
#include "wdg.h"

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "task.h"

/* Demo application includes. */
#include "flash.h"
#include "integer.h"
#include "PollQ.h"
#include "BlockQ.h"
#include "semtest.h"
#include "dynamic.h"
#include "partest.h"
#include "comtest2.h"

/* Priorities for the demo application tasks. */
#define mainLED_TASK_PRIORITY		( tskIDLE_PRIORITY + 3 )
#define mainQUEUE_POLL_PRIORITY		( tskIDLE_PRIORITY + 2 )
#define mainCHECK_TASK_PRIORITY		( tskIDLE_PRIORITY + 4 )
#define mainSEM_TEST_PRIORITY		( tskIDLE_PRIORITY + 1 )
#define mainBLOCK_Q_PRIORITY		( tskIDLE_PRIORITY + 2 )
#define mainCOM_TEST_PRIORITY		( tskIDLE_PRIORITY + 2 )

/* Constants required by the 'Check' task. */
#define mainNO_ERROR_FLASH_PERIOD	( ( TickType_t ) 3000 / portTICK_PERIOD_MS  )
#define mainERROR_FLASH_PERIOD		( ( TickType_t ) 500 / portTICK_PERIOD_MS  )
#define mainCHECK_TASK_LED			( 4 )

/* Constants for the ComTest tasks. */
#define mainCOM_TEST_BAUD_RATE		( ( unsigned long ) 115200 )
#define mainCOM_TEST_LED			( 6 ) /* The LED built onto the kickstart board. */

/*
 * The task that executes at the highest priority and calls
 * prvCheckOtherTasksAreStillRunning().  See the description at the top
 * of the file.
 */
static void vErrorChecks( void *pvParameters );

/*
 * Configure the processor for use with the IAR STR71x demo board.  This
 * just sets the PLL for the required frequency.
 */
static void prvSetupHardware( void );

/*
 * Checks that all the demo application tasks are still executing without error
 * - as described at the top of the file.  Called by vErrorChecks().
 */
static long prvCheckOtherTasksAreStillRunning( void );


/*-----------------------------------------------------------*/

/*
 * Starts all the other tasks, then starts the scheduler.
 */
void main( void )
{
	/* Setup any hardware that has not already been configured by the low
	level init routines. */
	prvSetupHardware();

	/* Initialise the LED outputs for use by the demo application tasks. */
	vParTestInitialise();

	/* Start all the standard demo application tasks. */
	vStartIntegerMathTasks( tskIDLE_PRIORITY );
	vStartLEDFlashTasks( mainLED_TASK_PRIORITY );
	vStartPolledQueueTasks( mainQUEUE_POLL_PRIORITY );
	vStartSemaphoreTasks( mainSEM_TEST_PRIORITY );
	vStartBlockingQueueTasks( mainBLOCK_Q_PRIORITY );
	vStartDynamicPriorityTasks();
	vAltStartComTestTasks( mainCOM_TEST_PRIORITY, mainCOM_TEST_BAUD_RATE, mainCOM_TEST_LED );

	/* Start the check task - which is defined in this file. */
	xTaskCreate( vErrorChecks, "Check", configMINIMAL_STACK_SIZE, NULL, mainCHECK_TASK_PRIORITY, NULL );

	/* Start the scheduler.

	NOTE : Tasks run in system mode and the scheduler runs in Supervisor mode.
	The processor MUST be in supervisor mode when vTaskStartScheduler is
	called.  The demo applications included in the FreeRTOS.org download switch
	to supervisor mode prior to main being called.  If you are not using one of
	these demo application projects then ensure Supervisor mode is used here. */

	vTaskStartScheduler();

	/* We should never get here as control is now taken by the scheduler. */
	return;
}
/*-----------------------------------------------------------*/

static void prvSetupHardware( void )
{
    /* Setup the PLL to generate a 48MHz clock from the 4MHz CLK. */

    /* Turn of the div by two. */
	RCCU_Div2Config( DISABLE );

    /* 48MHz = ( 4MHz * 12 ) / 1 */
	RCCU_PLL1Config( RCCU_PLL1_Mul_12, RCCU_Div_1 );
    RCCU_RCLKSourceConfig( RCCU_PLL1_Output );
}
/*-----------------------------------------------------------*/

static void vErrorChecks( void *pvParameters )
{
TickType_t xDelayPeriod = mainNO_ERROR_FLASH_PERIOD;
TickType_t xLastWakeTime;

	/* The parameters are not used in this task. */
	( void ) pvParameters;

	/* Initialise xLastWakeTime to ensure the first call to vTaskDelayUntil()
	functions correctly. */
	xLastWakeTime = xTaskGetTickCount();

	/* Cycle for ever, delaying then checking all the other tasks are still
	operating without error.  If an error is detected then the delay period
	is decreased from mainNO_ERROR_FLASH_PERIOD to mainERROR_FLASH_PERIOD so
	the on board LED flash rate will increase. */

	for( ;; )
	{
		/* Delay until it is time to execute again.  The delay period is
		shorter following an error so the LED flashes faster. */
		vTaskDelayUntil( &xLastWakeTime, xDelayPeriod );
	
		/* Check all the standard demo application tasks are executing without
		error. */
		if( prvCheckOtherTasksAreStillRunning() != pdPASS )
		{
			/* An error has been detected in one of the tasks - flash faster. */
			xDelayPeriod = mainERROR_FLASH_PERIOD;
		}
		
		vParTestToggleLED( mainCHECK_TASK_LED );
	}
}
/*-----------------------------------------------------------*/

static long prvCheckOtherTasksAreStillRunning( void )
{
long lReturn = ( long ) pdPASS;

	/* Check all the demo tasks (other than the flash tasks) to ensure
	that they are all still running, and that none of them have detected
	an error. */

	if( xAreIntegerMathsTaskStillRunning() != pdTRUE )
	{
		lReturn = ( long ) pdFAIL;
	}

	if( xArePollingQueuesStillRunning() != pdTRUE )
	{
		lReturn = ( long ) pdFAIL;
	}

	if( xAreSemaphoreTasksStillRunning() != pdTRUE )
	{
		lReturn = ( long ) pdFAIL;
	}

	if( xAreBlockingQueuesStillRunning() != pdTRUE )
	{
		lReturn = ( long ) pdFAIL;
	}

	if( xAreComTestTasksStillRunning() != pdTRUE )
	{
		lReturn = ( long ) pdFAIL;
	}

	if( xAreDynamicPriorityTasksStillRunning() != pdTRUE )
	{
		lReturn = ( long ) pdFAIL;
	}

	return lReturn;
}
/*-----------------------------------------------------------*/


