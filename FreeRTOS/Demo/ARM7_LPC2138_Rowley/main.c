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
 * This file contains a demo created to execute on the Rowley Associates
 * LPC2138 CrossFire development board.
 *
 * main() creates all the demo application tasks, then starts the scheduler.
 * The WEB documentation provides more details of the standard demo application
 * tasks.
 *
 * Main.c also creates a task called "Check".  This only executes every few
 * seconds but has a high priority so is guaranteed to get processor time.
 * Its function is to check that all the other tasks are still operational.
 * Each standard demo task maintains a unique count that is incremented each
 * time the task successfully completes its function.  Should any error occur
 * within such a task the count is permanently halted.  The check task inspects
 * the count of each task to ensure it has changed since the last time the
 * check task executed.  If all the count variables have changed all the tasks
 * are still executing error free, and the check task writes "PASS" to the
 * CrossStudio terminal IO window.  Should any task contain an error at any time
 * the error is latched and "FAIL" written to the terminal IO window.
 *
 * Finally, main() sets up an interrupt service routine and task to handle
 * pushes of the button that is built into the CrossFire board.  When the button
 * is pushed the ISR wakes the button task - which generates a table of task
 * status information which is also displayed on the terminal IO window.
 *
 * A print task is defined to ensure exclusive and consistent access to the
 * terminal IO.  This is the only task that is allowed to access the terminal.
 * The check and button task therefore do not access the terminal directly but
 * instead pass a pointer to the message they wish to display to the print task.
 */

/* Standard includes. */
#include <__cross_studio_io.h>

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"
#include "semphr.h"

/* Demo app includes. */
#include "BlockQ.h"
#include "death.h"
#include "dynamic.h"
#include "integer.h"
#include "PollQ.h"
#include "blocktim.h"
#include "recmutex.h"
#include "semtest.h"

/* Hardware configuration definitions. */
#define mainBUS_CLK_FULL					( ( unsigned char ) 0x01 )
#define mainLED_BIT							0x80000000
#define mainP0_14__EINT_1					( 2 << 28 )
#define mainEINT_1_EDGE_SENSITIVE			2
#define mainEINT_1_FALLING_EDGE_SENSITIVE	0
#define mainEINT_1_CHANNEL					15
#define mainEINT_1_VIC_CHANNEL_BIT			( 1 << mainEINT_1_CHANNEL )
#define mainEINT_1_ENABLE_BIT				( 1 << 5 )

/* Demo application definitions. */
#define mainQUEUE_SIZE						( 3 )
#define mainLED_DELAY						( ( TickType_t ) 500 / portTICK_PERIOD_MS )
#define mainERROR_LED_DELAY					( ( TickType_t ) 50 / portTICK_PERIOD_MS )
#define mainCHECK_DELAY						( ( TickType_t ) 5000 / portTICK_PERIOD_MS )
#define mainLIST_BUFFER_SIZE				2048
#define mainNO_DELAY						( 0 )
#define mainSHORT_DELAY						( 150 / portTICK_PERIOD_MS )

/* Task priorities. */
#define mainLED_TASK_PRIORITY				( tskIDLE_PRIORITY + 2 )
#define mainQUEUE_POLL_PRIORITY				( tskIDLE_PRIORITY + 2 )
#define mainCHECK_TASK_PRIORITY				( tskIDLE_PRIORITY + 3 )
#define mainSEM_TEST_PRIORITY				( tskIDLE_PRIORITY + 1 )
#define mainBLOCK_Q_PRIORITY				( tskIDLE_PRIORITY + 2 )
#define mainPRINT_TASK_PRIORITY				( tskIDLE_PRIORITY + 0 )

/*-----------------------------------------------------------*/

/* The semaphore used to wake the button task from within the external interrupt
handler. */
SemaphoreHandle_t xButtonSemaphore;

/* The queue that is used to send message to vPrintTask for display in the
terminal output window. */
QueueHandle_t xPrintQueue;

/* The rate at which the LED will toggle.  The toggle rate increases if an
error is detected in any task. */
static TickType_t xLED_Delay = mainLED_DELAY;
/*-----------------------------------------------------------*/

/*
 * Simply flashes the on board LED every mainLED_DELAY milliseconds.
 */
static void vLEDTask( void *pvParameters );

/*
 * Checks the status of all the demo tasks then prints a message to the
 * CrossStudio terminal IO windows.  The message will be either PASS or FAIL
 * depending on the status of the demo applications tasks.  A FAIL status will
 * be latched.
 *
 * Messages are not written directly to the terminal, but passed to vPrintTask
 * via a queue.
 */
static void vCheckTask( void *pvParameters );

/*
 * Controls all terminal output.  If a task wants to send a message to the
 * terminal IO it posts a pointer to the text to vPrintTask via a queue.  This
 * ensures serial access to the terminal IO.
 */
static void vPrintTask( void *pvParameter );

/*
 * Simply waits for an interrupt to be generated from the built in button, then
 * generates a table of tasks states that is then written by vPrintTask to the
 * terminal output window within CrossStudio.
 */
static void vButtonHandlerTask( void *pvParameters );

/*-----------------------------------------------------------*/

int main( void )
{
	/* Setup the peripheral bus to be the same as the PLL output. */
	VPBDIV = mainBUS_CLK_FULL;

	/* Create the queue used to pass message to vPrintTask. */
	xPrintQueue = xQueueCreate( mainQUEUE_SIZE, sizeof( char * ) );

	/* Create the semaphore used to wake vButtonHandlerTask(). */
	vSemaphoreCreateBinary( xButtonSemaphore );
	xSemaphoreTake( xButtonSemaphore, 0 );

	/* Start the standard demo tasks. */
	vStartIntegerMathTasks( tskIDLE_PRIORITY );
	vStartPolledQueueTasks( mainQUEUE_POLL_PRIORITY );
	vStartSemaphoreTasks( mainSEM_TEST_PRIORITY );
	vStartDynamicPriorityTasks();
	vStartBlockingQueueTasks( mainBLOCK_Q_PRIORITY );

	#if configUSE_PREEMPTION == 1
	{
		/* The timing of console output when not using the preemptive
		scheduler causes the block time tests to detect a timing problem. */
		vCreateBlockTimeTasks();
	}
	#endif

    vStartRecursiveMutexTasks();

	/* Start the tasks defined within this file. */
	xTaskCreate( vLEDTask, "LED", configMINIMAL_STACK_SIZE, NULL, mainLED_TASK_PRIORITY, NULL );
    xTaskCreate( vCheckTask, "Check", configMINIMAL_STACK_SIZE, NULL, mainCHECK_TASK_PRIORITY, NULL );
    xTaskCreate( vPrintTask, "Print", configMINIMAL_STACK_SIZE, NULL, mainPRINT_TASK_PRIORITY, NULL );
    xTaskCreate( vButtonHandlerTask, "Button", configMINIMAL_STACK_SIZE, NULL, mainCHECK_TASK_PRIORITY, NULL );

	/* Start the scheduler. */
	vTaskStartScheduler();

	/* The scheduler should now be running, so we will only ever reach here if we
	ran out of heap space. */

	return 0;
}
/*-----------------------------------------------------------*/

static void vLEDTask( void *pvParameters )
{
	/* Just to remove compiler warnings. */
	( void ) pvParameters;

	/* Configure IO. */
	IO0DIR |= mainLED_BIT;
	IO0SET = mainLED_BIT;

	for( ;; )
	{
		/* Not very exiting - just delay... */
		vTaskDelay( xLED_Delay );

		/* ...set the IO ... */
        IO0CLR = mainLED_BIT;

		/* ...delay again... */
		vTaskDelay( xLED_Delay );

		/* ...then clear the IO. */
		IO0SET = mainLED_BIT;
	}
}
/*-----------------------------------------------------------*/

static void vCheckTask( void *pvParameters )
{
portBASE_TYPE xErrorOccurred = pdFALSE;
TickType_t xLastExecutionTime;
const char * const pcPassMessage = "PASS\n";
const char * const pcFailMessage = "FAIL\n";

	/* Just to remove compiler warnings. */
	( void ) pvParameters;

	/* Initialise xLastExecutionTime so the first call to vTaskDelayUntil()
	works correctly. */
	xLastExecutionTime = xTaskGetTickCount();

	for( ;; )
	{
		/* Perform this check every mainCHECK_DELAY milliseconds. */
		vTaskDelayUntil( &xLastExecutionTime, mainCHECK_DELAY );

		/* Has an error been found in any task? */

		if( xAreIntegerMathsTaskStillRunning() != pdTRUE )
		{
			xErrorOccurred = pdTRUE;
		}

		if( xArePollingQueuesStillRunning() != pdTRUE )
		{
			xErrorOccurred = pdTRUE;
		}

		if( xAreSemaphoreTasksStillRunning() != pdTRUE )
		{
			xErrorOccurred = pdTRUE;
		}

		if( xAreDynamicPriorityTasksStillRunning() != pdTRUE )
		{
			xErrorOccurred = pdTRUE;
		}

		if( xAreBlockingQueuesStillRunning() != pdTRUE )
		{
			xErrorOccurred = pdTRUE;
		}

		#if configUSE_PREEMPTION == 1
		{
			/* The timing of console output when not using the preemptive
			scheduler causes the block time tests to detect a timing problem. */
			if( xAreBlockTimeTestTasksStillRunning() != pdTRUE )
			{
				xErrorOccurred = pdTRUE;
			}
		}
		#endif

		if( xAreRecursiveMutexTasksStillRunning() != pdTRUE )
		{
			xErrorOccurred = pdTRUE;
		}

		/* Send either a pass or fail message.  If an error is found it is
		never cleared again. */
		if( xErrorOccurred == pdTRUE )
		{
			xLED_Delay = mainERROR_LED_DELAY;
			xQueueSend( xPrintQueue, &pcFailMessage, portMAX_DELAY );
		}
		else
		{
			xQueueSend( xPrintQueue, &pcPassMessage, portMAX_DELAY );
		}
	}
}
/*-----------------------------------------------------------*/

static void vPrintTask( void *pvParameters )
{
char *pcMessage;

	/* Just to stop compiler warnings. */
	( void ) pvParameters;

	for( ;; )
	{
		/* Wait for a message to arrive. */
		while( xQueueReceive( xPrintQueue, &pcMessage, portMAX_DELAY ) != pdPASS );

		/* Write the message to the terminal IO. */
		#ifndef NDEBUG
			debug_printf( "%s", pcMessage );
		#endif
	}
}
/*-----------------------------------------------------------*/

static void vButtonHandlerTask( void *pvParameters )
{
static char cListBuffer[ mainLIST_BUFFER_SIZE ];
const char *pcList = &( cListBuffer[ 0 ] );
const char * const pcHeader = "\nTask          State  Priority  Stack	#\n************************************************";
extern void (vButtonISRWrapper) ( void );

	/* Just to stop compiler warnings. */
	( void ) pvParameters;

	/* Configure the interrupt. */
	portENTER_CRITICAL();
	{
		/* Configure P0.14 to generate interrupts. */
		PINSEL0 |= mainP0_14__EINT_1;
		EXTMODE = mainEINT_1_EDGE_SENSITIVE;
		EXTPOLAR = mainEINT_1_FALLING_EDGE_SENSITIVE;

		/* Setup the VIC for EINT 1. */
		VICIntSelect &= ~mainEINT_1_VIC_CHANNEL_BIT;
		VICIntEnable |= mainEINT_1_VIC_CHANNEL_BIT;
		VICVectAddr1 = ( long ) vButtonISRWrapper;
		VICVectCntl1 = mainEINT_1_ENABLE_BIT | mainEINT_1_CHANNEL;
	}
	portEXIT_CRITICAL();

	for( ;; )
	{
		/* For debouncing, wait a while then clear the semaphore. */
		vTaskDelay( mainSHORT_DELAY );
		xSemaphoreTake( xButtonSemaphore, mainNO_DELAY );

		/* Wait for an interrupt. */
		xSemaphoreTake( xButtonSemaphore, portMAX_DELAY );

		/* Send the column headers to the print task for display. */
		xQueueSend( xPrintQueue, &pcHeader, portMAX_DELAY );

		/* Create the list of task states. */
		vTaskList( cListBuffer );

		/* Send the task status information to the print task for display. */
		xQueueSend( xPrintQueue, &pcList, portMAX_DELAY );
	}
}
/*-----------------------------------------------------------*/

void vApplicationStackOverflowHook( TaskHandle_t pxTask, char *pcTaskName )
{
	/* Check pcTaskName for the name of the offending task, or pxCurrentTCB
	if pcTaskName has itself been corrupted. */
	( void ) pxTask;
	( void ) pcTaskName;
	for( ;; );
}






