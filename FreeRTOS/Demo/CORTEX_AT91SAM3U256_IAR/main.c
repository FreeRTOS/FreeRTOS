/*
 * FreeRTOS Kernel V10.4.1
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
 * Creates all the demo application tasks, then starts the scheduler.  The WEB
 * documentation provides more details of the standard demo application tasks
 * (which just exist to test the kernel port and provide an example of how to use
 * each FreeRTOS API function).
 *
 * In addition to the standard demo tasks, the following tasks and tests are
 * defined and/or created within this file:
 *
 * "LCD" task - the LCD task is a 'gatekeeper' task.  It is the only task that
 * is permitted to access the display directly.  Other tasks wishing to write a
 * message to the LCD send the message on a queue to the LCD task instead of
 * accessing the LCD themselves.  The LCD task just blocks on the queue waiting
 * for messages - waking and displaying the messages as they arrive.  The use
 * of a gatekeeper in this manner permits both tasks and interrupts to write to
 * the LCD without worrying about mutual exclusion.  This is demonstrated by the
 * check hook (see below) which sends messages to the display even though it
 * executes from an interrupt context.
 *
 * "Check" hook -  This only executes fully every five seconds from the tick
 * hook.  Its main function is to check that all the standard demo tasks are
 * still operational.  Should any unexpected behaviour be discovered within a
 * demo task then the tick hook will write an error to the LCD (via the LCD task).
 * If all the demo tasks are executing with their expected behaviour then the
 * check task writes PASS to the LCD (again via the LCD task), as described above.
 *
 */

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"
#include "semphr.h"

/* Demo app includes. */
#include "BlockQ.h"
#include "integer.h"
#include "blocktim.h"
#include "flash.h"
#include "partest.h"
#include "semtest.h"
#include "PollQ.h"
#include "lcd_message.h"
#include "GenQTest.h"
#include "QPeek.h"
#include "recmutex.h"
#include "flash.h"
#include "comtest2.h"

/* Atmel library includes. */
#include <board.h>
#include <lcd/color.h>
#include <lcd/lcdd.h>
#include <lcd/draw.h>


/*-----------------------------------------------------------*/

/* The time between cycles of the 'check' functionality (defined within the
tick hook). */
#define mainCHECK_DELAY						( ( TickType_t ) 5000 / portTICK_PERIOD_MS )

/* The LCD task uses the sprintf function so requires a little more stack too. */
#define mainLCD_TASK_STACK_SIZE				( configMINIMAL_STACK_SIZE * 2 )

/* Task priorities. */
#define mainQUEUE_POLL_PRIORITY				( tskIDLE_PRIORITY + 2 )
#define mainSEM_TEST_PRIORITY				( tskIDLE_PRIORITY + 1 )
#define mainBLOCK_Q_PRIORITY				( tskIDLE_PRIORITY + 2 )
#define mainLED_TASK_PRIORITY				( tskIDLE_PRIORITY + 1 )
#define mainCOM_TEST_PRIORITY				( tskIDLE_PRIORITY + 2 )
#define mainINTEGER_TASK_PRIORITY           ( tskIDLE_PRIORITY )
#define mainGEN_QUEUE_TASK_PRIORITY			( tskIDLE_PRIORITY )

/* The maximum number of message that can be waiting for display at any one
time. */
#define mainLCD_QUEUE_SIZE					( 3 )

/* Constants used by the comtest tasks.  There isn't a spare LED so an invalid
LED is specified. */
#define mainBAUD_RATE						( 115200 )
#define mainCOM_TEST_LED					( 10 )

/*-----------------------------------------------------------*/

/*
 * Configure the hardware for the demo.
 */
static void prvSetupHardware( void );

/*
 * The LCD gatekeeper task.  Tasks wishing to write to the LCD do not access
 * the LCD directly, but instead send the message to the LCD gatekeeper task.
 */
static void prvLCDTask( void *pvParameters );

/*
 * Hook functions that can get called by the kernel.  The 'check' functionality
 * is implemented within the tick hook.
 */
void vApplicationStackOverflowHook( TaskHandle_t pxTask, char *pcTaskName );

/*
 * The tick hook function as described in the comments at the top of this file.
 * The tick hook is used to monitor all the standard demo tasks to look for
 * errors.  The tick hook is also used to demonstrate how the LCD gatekeeper
 * task can be used to allow interrupts to write to the LCD.
 */
void vApplicationTickHook( void );


/*-----------------------------------------------------------*/

/* The queue used to send messages to the LCD task. */
static QueueHandle_t xLCDQueue;

/*-----------------------------------------------------------*/

int main( void )
{
	/* Prepare the hardware. */
	prvSetupHardware();

	/* Create the queue used by the LCD task.  Messages for display on the LCD
	are received via this queue. */
	xLCDQueue = xQueueCreate( mainLCD_QUEUE_SIZE, sizeof( xLCDMessage ) );

	/* Start the standard demo tasks.  These do nothing other than test the
	port and provide some APU usage examples. */
    vStartIntegerMathTasks( mainINTEGER_TASK_PRIORITY );
    vStartGenericQueueTasks( mainGEN_QUEUE_TASK_PRIORITY );
	vStartRecursiveMutexTasks();
	vStartBlockingQueueTasks( mainBLOCK_Q_PRIORITY );
	vCreateBlockTimeTasks();
	vStartSemaphoreTasks( mainSEM_TEST_PRIORITY );
	vStartPolledQueueTasks( mainQUEUE_POLL_PRIORITY );
	vStartQueuePeekTasks();
	vStartLEDFlashTasks( mainLED_TASK_PRIORITY );
	vAltStartComTestTasks( mainCOM_TEST_PRIORITY, mainBAUD_RATE, mainCOM_TEST_LED );

	/* Start the tasks defined within this file/specific to this demo. */
	xTaskCreate( prvLCDTask, "LCD", mainLCD_TASK_STACK_SIZE, NULL, tskIDLE_PRIORITY, NULL );

	/* Start the scheduler. */
	vTaskStartScheduler();

    /* Will only get here if there was insufficient memory to create the idle
    task. */
	return 0;
}
/*-----------------------------------------------------------*/

void prvSetupHardware( void )
{
	/* Initialise the port used for the LED outputs. */
	vParTestInitialise();
}
/*-----------------------------------------------------------*/

void vApplicationTickHook( void )
{
static xLCDMessage xMessage = { "PASS" };
static unsigned long ulTicksSinceLastDisplay = 0;
portBASE_TYPE xHigherPriorityTaskWoken = pdFALSE;

	/* Called from every tick interrupt.  Have enough ticks passed to make it
	time to perform our health status check again? */
	ulTicksSinceLastDisplay++;
	if( ulTicksSinceLastDisplay >= mainCHECK_DELAY )
	{
		ulTicksSinceLastDisplay = 0;

		/* Has an error been found in any task? */
		if( xAreGenericQueueTasksStillRunning() != pdTRUE )
		{
			xMessage.pcMessage = "ERROR IN GEN Q";
		}
	    if( xAreIntegerMathsTaskStillRunning() != pdTRUE )
	    {
	        xMessage.pcMessage = "ERROR IN MATH";
	    }
		else if( xAreBlockingQueuesStillRunning() != pdTRUE )
		{
			xMessage.pcMessage = "ERROR IN BLOCK Q";
		}
		else if( xAreBlockTimeTestTasksStillRunning() != pdTRUE )
		{
			xMessage.pcMessage = "ERROR IN BLOCK TIME";
		}
		else if( xAreSemaphoreTasksStillRunning() != pdTRUE )
		{
			xMessage.pcMessage = "ERROR IN SEMAPHORE";
		}
		else if( xArePollingQueuesStillRunning() != pdTRUE )
		{
			xMessage.pcMessage = "ERROR IN POLL Q";
		}
		else if( xAreQueuePeekTasksStillRunning() != pdTRUE )
		{
			xMessage.pcMessage = "ERROR IN PEEK Q";
		}
		else if( xAreRecursiveMutexTasksStillRunning() != pdTRUE )
		{
			xMessage.pcMessage = "ERROR IN REC MUTEX";
		}
		else if( xAreComTestTasksStillRunning() != pdTRUE )
		{
			xMessage.pcMessage = "ERROR IN COMTEST";
		}

		/* Send the message to the LCD gatekeeper for display. */
		xHigherPriorityTaskWoken = pdFALSE;
		xQueueSendFromISR( xLCDQueue, &xMessage, &xHigherPriorityTaskWoken );
	}
}
/*-----------------------------------------------------------*/

void vApplicationStackOverflowHook( TaskHandle_t pxTask, char *pcTaskName )
{
	( void ) pxTask;
	( void ) pcTaskName;

	/* If the parameters have been corrupted then inspect pxCurrentTCB to
	identify which task has overflowed its stack. */
	for( ;; );
}
/*-----------------------------------------------------------*/

static void prvLCDTask( void *pvParameters )
{
xLCDMessage xMessage;
unsigned long ulY = 0;
const unsigned long ulX = 5;
const unsigned long ulMaxY = 250, ulYIncrement = 22, ulWidth = 250, ulHeight = 20;;

    /* Initialize LCD. */
    LCDD_Initialize();
    LCDD_Start();
	LCDD_Fill( ( void * ) BOARD_LCD_BASE, COLOR_WHITE );
	LCDD_DrawString( ( void * ) BOARD_LCD_BASE, 1, ulY + 3, "  www.FreeRTOS.org", COLOR_BLACK );

	for( ;; )
	{
		/* Wait for a message from the check function (which is executed in
		the tick hook). */
		xQueueReceive( xLCDQueue, &xMessage, portMAX_DELAY );

		/* Clear the space where the old message was. */
        LCDD_DrawRectangle( ( void * ) BOARD_LCD_BASE, 0, ulY, ulWidth, ulHeight, COLOR_WHITE );

		/* Increment to the next drawing position. */
		ulY += ulYIncrement;

		/* Have the Y position moved past the end of the LCD? */
		if( ulY >= ulMaxY )
		{
			ulY = 0;
		}

		/* Draw a new rectangle, in which the message will be written. */
        LCDD_DrawRectangle( ( void * ) BOARD_LCD_BASE, 0, ulY, ulWidth, ulHeight, COLOR_GREEN );

		/* Write the message. */
        LCDD_DrawString( ( void * ) BOARD_LCD_BASE, ulX, ulY + 3, xMessage.pcMessage, COLOR_BLACK );
	}
}
