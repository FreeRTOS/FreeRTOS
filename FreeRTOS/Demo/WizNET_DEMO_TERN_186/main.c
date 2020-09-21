/*
 * FreeRTOS Kernel V10.3.0
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
 * Creates all the demo application tasks then starts the scheduler.  In 
 * addition to the standard demo application tasks main() creates the 
 * HTTPServer task, and a "Check" task.  The Check task periodically inspects
 * all the other tasks in the system to see if any errors have been reported.
 * The error status is then displayed on the served WEB page.
 */

/* Tern includes. */
#include <ae.h>
#include <embedded.h>

/* FreeRTOS.org includes. */
#include <FreeRTOS.h>
#include <task.h>

/* Demo application includes. */
#include "HTTPTask.h"
#include "integer.h"
#include "PollQ.h"
#include "semtest.h"
#include "dynamic.h"
#include "BlockQ.h"
#include "death.h"
#include "serial.h"
#include "comtest.h"

/* How often should the "check" task execute? */
#define mainCHECK_DELAY		( 3000 / portTICK_PERIOD_MS )

/* Priorities allocated to the various tasks. */
#define mainQUEUE_POLL_PRIORITY		( tskIDLE_PRIORITY + 2 )
#define mainCHECK_TASK_PRIORITY		( tskIDLE_PRIORITY + 4 )
#define mainSEM_TEST_PRIORITY		( tskIDLE_PRIORITY + 1 )
#define mainBLOCK_Q_PRIORITY		( tskIDLE_PRIORITY + 2 )
#define mainHTTP_TASK_PRIORITY		( tskIDLE_PRIORITY + 3 )
#define mainSUICIDE_TASKS_PRIORITY  ( tskIDLE_PRIORITY + 1 )
#define mainCOM_TEST_PRIORITY		( tskIDLE_PRIORITY + 2 )

/* Used to indicate the error status.  A value of 0 means that an error has not
been detected in any task.  A non zero value indicates which group of demo 
tasks has reported an error.  See prvCheckTask() for bit definitions. */
unsigned short usCheckStatus = 0;

/*-----------------------------------------------------------*/

/*
 * Setup any hardware required by the demo - other than the RTOS tick which
 * is configured when the scheduler is started.
 */
static void prvSetupHardware( void );

/*
 * Periodically inspect all the other tasks, updating usCheckStatus should an
 * error be discovered in any task.
 */
static void prvCheckTask( void *pvParameters );
/*-----------------------------------------------------------*/

void main(void)
{
	prvSetupHardware();

    /* Start the HTTP server task. */
	xTaskCreate( vHTTPTask, "WizNet", configMINIMAL_STACK_SIZE, NULL, mainHTTP_TASK_PRIORITY, NULL );

	/* Start the demo/test application tasks.  See the demo application 
	section of the FreeRTOS.org WEB site for more information. */
	vStartIntegerMathTasks( tskIDLE_PRIORITY );
	vStartPolledQueueTasks( mainQUEUE_POLL_PRIORITY );
	vStartSemaphoreTasks( mainSEM_TEST_PRIORITY );
  	vStartDynamicPriorityTasks();
	vStartBlockingQueueTasks( mainBLOCK_Q_PRIORITY );
    vStartComTestTasks( mainCOM_TEST_PRIORITY, serCOM2, ser57600 );

	/* Start the task that checks the other demo tasks for errors. */
    xTaskCreate( prvCheckTask, "Check", configMINIMAL_STACK_SIZE, NULL, mainCHECK_TASK_PRIORITY, NULL );

	/* The suicide tasks must be created last as they monitor the number of
	tasks in the system to ensure there are no more or fewer than expected
	compared to the number that were executing when the task started. */
   	vCreateSuicidalTasks( mainSUICIDE_TASKS_PRIORITY );
        
	/* Finally start the scheduler. */
    vTaskStartScheduler();

	/* Should not get here! */
	for( ;; );
}
/*-----------------------------------------------------------*/

static void prvSetupHardware( void )
{
	ae_init();
}
/*-----------------------------------------------------------*/

static void prvCheckTask( void *pvParameters )
{
	( void ) pvParameters;

	/* Check all the demo tasks to ensure that they are all still running, and
    that none of them have detected	an error. */
    for( ;; )
    {
		/* Block until it is time to check again. */
    	vTaskDelay( mainCHECK_DELAY );
        
		if( xAreIntegerMathsTaskStillRunning() != pdTRUE )
		{
			usCheckStatus |= 0x01;
		}

		if( xArePollingQueuesStillRunning() != pdTRUE )
		{
			usCheckStatus |= 0x02;
		}

		if( xAreSemaphoreTasksStillRunning() != pdTRUE )
		{
			usCheckStatus |= 0x04;
		}

		if( xAreDynamicPriorityTasksStillRunning() != pdTRUE )
		{
			usCheckStatus |= 0x08;
		}

		if( xAreBlockingQueuesStillRunning() != pdTRUE )
		{
			usCheckStatus |= 0x10;
		}

        if( xIsCreateTaskStillRunning() != pdTRUE )
        {
        	usCheckStatus |= 0x20;
        }

        if( xAreComTestTasksStillRunning() != pdTRUE )
        {
        	usCheckStatus |= 0x40;
        }
	}
}
/*-----------------------------------------------------------*/

/* This is included to prevent link errors - allowing the 'full' version of
the comtest tasks to be used.  It can be ignored. */
void vPrintDisplayMessage( const char * const * ppcMessageToSend )
{
	( void ) ppcMessageToSend;
}












