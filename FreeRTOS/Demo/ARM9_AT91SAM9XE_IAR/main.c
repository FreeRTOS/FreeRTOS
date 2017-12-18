/*
 * FreeRTOS Kernel V10.0.1
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
 * Creates all the demo application tasks, then starts the scheduler.  The WEB
 * documentation provides more details of the standard demo application tasks.
 *
 * A "Check" task is created in addition to the standard demo tasks.    This
 * only executes every three seconds but has a high priority to ensure it gets
 * processor time.  Its main function is to check that all the standard demo
 * tasks are still operational.  If everything is running as expected then the
 * check task will toggle an LED every 3 seconds.  An error being discovered in
 * any task will cause the toggle rate to increase to 500ms.
 *
 */

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"

/* Standard demo includes. */
#include "BlockQ.h"
#include "blocktim.h"
#include "countsem.h"
#include "death.h"
#include "dynamic.h"
#include "GenQTest.h"
#include "integer.h"
#include "PollQ.h"
#include "QPeek.h"
#include "recmutex.h"
#include "semtest.h"
#include "ParTest.h"
#include "comtest2.h"

/* Standard includes. */
#include <stdio.h>

/* Atmel library includes. */
#include <pio/pio.h>

/* Priorities for the demo application tasks. */
#define mainCOM_TEST_PRIORITY		( tskIDLE_PRIORITY + 2 )
#define mainQUEUE_POLL_PRIORITY		( tskIDLE_PRIORITY + 0 )
#define mainCHECK_TASK_PRIORITY		( tskIDLE_PRIORITY + 4 )
#define mainSEM_TEST_PRIORITY		( tskIDLE_PRIORITY + 0 )
#define mainBLOCK_Q_PRIORITY		( tskIDLE_PRIORITY + 2 )
#define mainCREATOR_TASK_PRIORITY 	( tskIDLE_PRIORITY + 3 )
#define mainGENERIC_QUEUE_PRIORITY	( tskIDLE_PRIORITY )

/* The period of the check task both in and out of the presense of an error. */
#define mainNO_ERROR_PERIOD			( 5000 / portTICK_PERIOD_MS )
#define mainERROR_PERIOD			( 500 / portTICK_PERIOD_MS );

/* Constants used by the ComTest task. */
#define mainCOM_TEST_BAUD_RATE		( 38400 )
#define mainCOM_TEST_LED			( LED_DS1 )

/*-----------------------------------------------------------*/

/* Simple hardware setup required by the demo. */
static void prvSetupHardware( void );

/* The check task as described at the top of this file. */
static void prvCheckTask( void *pvParameters );

/*-----------------------------------------------------------*/
int main()
{
	/* Perform any hardware setup necessary to run the demo. */
	prvSetupHardware();
	
	/* First create the 'standard demo' tasks.  These exist just to to
	demonstrate API functions being used and test the kernel port.  More
	information is provided on the FreeRTOS.org WEB site. */
	vStartIntegerMathTasks( tskIDLE_PRIORITY );
	vStartPolledQueueTasks( mainQUEUE_POLL_PRIORITY );
	vStartSemaphoreTasks( mainSEM_TEST_PRIORITY );
	vStartDynamicPriorityTasks();
	vStartBlockingQueueTasks( mainBLOCK_Q_PRIORITY );
	vCreateBlockTimeTasks();
	vStartCountingSemaphoreTasks();
	vStartGenericQueueTasks( tskIDLE_PRIORITY );
	vStartQueuePeekTasks();
	vStartRecursiveMutexTasks();
	vAltStartComTestTasks( mainCOM_TEST_PRIORITY, mainCOM_TEST_BAUD_RATE, mainCOM_TEST_LED );
	
	/* Create the check task - this is the task that checks all the other tasks
	are executing as expected and without reporting any errors. */
	xTaskCreate( prvCheckTask, "Check", configMINIMAL_STACK_SIZE, NULL, configMAX_PRIORITIES - 1, NULL );
	
	/* The death demo tasks must be started last as the sanity checks performed
	require knowledge of the number of other tasks in the system. */
	vCreateSuicidalTasks( mainCREATOR_TASK_PRIORITY );
	
	/* Start the scheduler.  From this point on the execution will be under
	the control of the kernel. */
	vTaskStartScheduler();
	
	/* Will only get here if there was insufficient heap availale for the
	idle task to be created. */
	for( ;; );
}
/*-----------------------------------------------------------*/

static void prvCheckTask( void * pvParameters )
{
TickType_t xNextWakeTime, xPeriod = mainNO_ERROR_PERIOD;
static volatile unsigned long ulErrorCode = 0UL;

	/* Just to remove the compiler warning. */
	( void ) pvParameters;

	/* Initialise xNextWakeTime prior to its first use.  From this point on
	the value of the variable is handled automatically by the kernel. */
	xNextWakeTime = xTaskGetTickCount();
	
	for( ;; )
	{
		/* Delay until it is time for this task to execute again. */
		vTaskDelayUntil( &xNextWakeTime, xPeriod );
		
		/* Check all the other tasks in the system - latch any reported errors
		into the ulErrorCode variable. */
		if( xAreBlockingQueuesStillRunning() != pdTRUE )
		{
			ulErrorCode |= 0x01UL;
		}

		if( xAreBlockTimeTestTasksStillRunning() != pdTRUE )
		{
			ulErrorCode |= 0x02UL;
		}

		if( xAreCountingSemaphoreTasksStillRunning() != pdTRUE )
		{
			ulErrorCode |= 0x04UL;
		}

		if( xIsCreateTaskStillRunning() != pdTRUE )
		{
			ulErrorCode |= 0x08UL;
		}

		if( xAreDynamicPriorityTasksStillRunning() != pdTRUE )
		{
			ulErrorCode |= 0x10UL;
		}

		if( xAreGenericQueueTasksStillRunning() != pdTRUE )
		{
			ulErrorCode |= 0x20UL;
		}

		if( xAreIntegerMathsTaskStillRunning() != pdTRUE )
		{
			ulErrorCode |= 0x40UL;
		}

		if( xArePollingQueuesStillRunning() != pdTRUE )
		{
			ulErrorCode |= 0x80UL;
		}

		if( xAreQueuePeekTasksStillRunning() != pdTRUE )
		{
			ulErrorCode |= 0x100UL;
		}

		if( xAreRecursiveMutexTasksStillRunning() != pdTRUE )
		{
			ulErrorCode |= 0x200UL;
		}

		if( xAreSemaphoreTasksStillRunning() != pdTRUE )
		{
			ulErrorCode |= 0x400UL;
		}
		
		if( xAreComTestTasksStillRunning() != pdTRUE )
		{
			ulErrorCode |= 0x800UL;
		}
		
		/* Reduce the block period and in so doing increase the frequency at
		which this task executes if any errors have been latched.  The increased
		frequency causes the LED toggle rate to increase and so gives some
		visual feedback that an error has occurred. */
		if( ulErrorCode != 0x00 )
		{
			xPeriod = mainERROR_PERIOD;
		}
		
		/* Finally toggle the LED. */
		vParTestToggleLED( LED_POWER );
	}
}
/*-----------------------------------------------------------*/

static void prvSetupHardware( void )
{
const Pin xPins[] = { PIN_USART0_RXD, PIN_USART0_TXD };

	/* Setup the LED outputs. */
	vParTestInitialise();
	
	/* Setup the pins for the UART. */
	PIO_Configure( xPins, PIO_LISTSIZE( xPins ) );	
}
