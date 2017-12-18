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

/* Environment includes. */
#include <targets/LPC2368.h>

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"
#include "semphr.h"

/* Demo app includes. */
#include "BlockQ.h"
#include "death.h"
#include "integer.h"
#include "blocktim.h"
#include "portlcd.h"
#include "flash.h"
#include "partest.h"
#include "semtest.h"
#include "PollQ.h"

/* Demo application definitions. */
#define mainQUEUE_SIZE						( 3 )
#define mainCHECK_DELAY						( ( TickType_t ) 5000 / portTICK_PERIOD_MS )
#define mainBASIC_WEB_STACK_SIZE            ( configMINIMAL_STACK_SIZE * 2 )

/* Task priorities. */
#define mainQUEUE_POLL_PRIORITY				( tskIDLE_PRIORITY + 2 )
#define mainCHECK_TASK_PRIORITY				( tskIDLE_PRIORITY + 3 )
#define mainSEM_TEST_PRIORITY				( tskIDLE_PRIORITY + 1 )
#define mainBLOCK_Q_PRIORITY				( tskIDLE_PRIORITY + 2 )
#define mainFLASH_PRIORITY                  ( tskIDLE_PRIORITY + 2 )
#define mainCREATOR_TASK_PRIORITY           ( tskIDLE_PRIORITY + 3 )
#define mainINTEGER_TASK_PRIORITY           ( tskIDLE_PRIORITY )


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
 * The task that handles the uIP stack.  All TCP/IP processing is performed in
 * this task.
 */
extern void vuIP_Task( void *pvParameters );

/*
 * The LCD is written two by more than one task so is controlled by a
 * 'gatekeeper' task.  This is the only task that is actually permitted to
 * access the LCD directly.  Other tasks wanting to display a message send
 * the message to the gatekeeper.
 */
static void vLCDTask( void *pvParameters );

/* The queue used to send messages to the LCD task. */
QueueHandle_t xLCDQueue;

/*-----------------------------------------------------------*/

int main (void)
{
	/* Setup the led's on the MCB2300 board */
	vParTestInitialise();

	/* Create the queue used by the LCD task.  Messages for display on the LCD
	are received via this queue. */
	xLCDQueue = xQueueCreate( mainQUEUE_SIZE, sizeof( xLCDMessage ) );

	/* Create the lwIP task.  This uses the lwIP RTOS abstraction layer.*/
    xTaskCreate( vuIP_Task, "uIP", mainBASIC_WEB_STACK_SIZE, NULL, mainCHECK_TASK_PRIORITY - 1, NULL );

	/* Start the standard demo tasks - these serve no useful purpose other than
	to demonstrate the FreeRTOS API being used and to test the port. */
	vStartBlockingQueueTasks( mainBLOCK_Q_PRIORITY );
    vCreateBlockTimeTasks();
    vStartLEDFlashTasks( mainFLASH_PRIORITY );
    vStartSemaphoreTasks( mainSEM_TEST_PRIORITY );
    vStartPolledQueueTasks( mainQUEUE_POLL_PRIORITY );
    vStartIntegerMathTasks( mainINTEGER_TASK_PRIORITY );

	/* Start the tasks defined within this file/specific to this demo. */
    xTaskCreate( vCheckTask, "Check", configMINIMAL_STACK_SIZE, NULL, mainCHECK_TASK_PRIORITY, NULL );
	xTaskCreate( vLCDTask, "LCD", configMINIMAL_STACK_SIZE, NULL, mainCHECK_TASK_PRIORITY - 1, NULL );

	/* The suicide tasks must be created last as they need to know how many
	tasks were running prior to their creation in order to ascertain whether
	or not the correct/expected number of tasks are running at any given time. */
    vCreateSuicidalTasks( mainCREATOR_TASK_PRIORITY );

	/* Start the scheduler. */
	vTaskStartScheduler();

    /* Will only get here if there was insufficient memory to create the idle
    task. */
	return 0;
}
/*-----------------------------------------------------------*/

static void vCheckTask( void *pvParameters )
{
portBASE_TYPE xErrorOccurred = pdFALSE;
TickType_t xLastExecutionTime;
unsigned portBASE_TYPE uxColumn = 0;
xLCDMessage xMessage;

	xLastExecutionTime = xTaskGetTickCount();

	xMessage.xColumn = 0;
	xMessage.pcMessage = "PASS";

    for( ;; )
	{
		/* Perform this check every mainCHECK_DELAY milliseconds. */
		vTaskDelayUntil( &xLastExecutionTime, mainCHECK_DELAY );

		/* Has an error been found in any task? */

        if( xAreBlockingQueuesStillRunning() != pdTRUE )
		{
			xErrorOccurred = pdTRUE;
		}

		if( xAreBlockTimeTestTasksStillRunning() != pdTRUE )
		{
			xErrorOccurred = pdTRUE;
		}

        if( xAreSemaphoreTasksStillRunning() != pdTRUE )
        {
            xErrorOccurred = pdTRUE;
        }

        if( xArePollingQueuesStillRunning() != pdTRUE )
        {
            xErrorOccurred = pdTRUE;
        }

        if( xIsCreateTaskStillRunning() != pdTRUE )
        {
            xErrorOccurred = pdTRUE;
        }

        if( xAreIntegerMathsTaskStillRunning() != pdTRUE )
        {
            xErrorOccurred = pdTRUE;
        }

        LCD_cls();
        xMessage.xColumn++;
        LCD_gotoxy( ( uxColumn & 0x07 ) + 1, ( uxColumn & 0x01 ) + 1 );

        if( xErrorOccurred == pdTRUE )
        {
            xMessage.pcMessage = "FAIL";
        }

		/* Send the message to the LCD gatekeeper for display. */
		xQueueSend( xLCDQueue, &xMessage, portMAX_DELAY );
	}
}
/*-----------------------------------------------------------*/

void vLCDTask( void *pvParameters )
{
xLCDMessage xMessage;

	/* Initialise the LCD and display a startup message. */
	LCD_init();
	LCD_cur_off();
    LCD_cls();
    LCD_gotoxy( 1, 1 );
    LCD_puts( ( signed char * ) "www.FreeRTOS.org" );

	for( ;; )
	{
		/* Wait for a message to arrive that requires displaying. */
		while( xQueueReceive( xLCDQueue, &xMessage, portMAX_DELAY ) != pdPASS );

		/* Display the message.  Print each message to a different position. */
		LCD_cls();
		LCD_gotoxy( ( xMessage.xColumn & 0x07 ) + 1, ( xMessage.xColumn & 0x01 ) + 1 );
		LCD_puts( xMessage.pcMessage );
	}

}
/*-----------------------------------------------------------*/

/* Keep the compiler quiet. */
#include <stdio.h>
int __putchar( int c )
{
    return EOF;
}





