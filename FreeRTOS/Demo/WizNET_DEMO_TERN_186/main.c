/*
    FreeRTOS V8.2.2 - Copyright (C) 2015 Real Time Engineers Ltd.
    All rights reserved

    VISIT http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation >>!AND MODIFIED BY!<< the FreeRTOS exception.

    ***************************************************************************
    >>!   NOTE: The modification to the GPL is included to allow you to     !<<
    >>!   distribute a combined work that includes FreeRTOS without being   !<<
    >>!   obliged to provide the source code for proprietary components     !<<
    >>!   outside of the FreeRTOS kernel.                                   !<<
    ***************************************************************************

    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT ANY
    WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
    FOR A PARTICULAR PURPOSE.  Full license text is available on the following
    link: http://www.freertos.org/a00114.html

    ***************************************************************************
     *                                                                       *
     *    FreeRTOS provides completely free yet professionally developed,    *
     *    robust, strictly quality controlled, supported, and cross          *
     *    platform software that is more than just the market leader, it     *
     *    is the industry's de facto standard.                               *
     *                                                                       *
     *    Help yourself get started quickly while simultaneously helping     *
     *    to support the FreeRTOS project by purchasing a FreeRTOS           *
     *    tutorial book, reference manual, or both:                          *
     *    http://www.FreeRTOS.org/Documentation                              *
     *                                                                       *
    ***************************************************************************

    http://www.FreeRTOS.org/FAQHelp.html - Having a problem?  Start by reading
    the FAQ page "My application does not run, what could be wrong?".  Have you
    defined configASSERT()?

    http://www.FreeRTOS.org/support - In return for receiving this top quality
    embedded software for free we request you assist our global community by
    participating in the support forum.

    http://www.FreeRTOS.org/training - Investing in training allows your team to
    be as productive as possible as early as possible.  Now you can receive
    FreeRTOS training directly from Richard Barry, CEO of Real Time Engineers
    Ltd, and the world's leading authority on the world's leading RTOS.

    http://www.FreeRTOS.org/plus - A selection of FreeRTOS ecosystem products,
    including FreeRTOS+Trace - an indispensable productivity tool, a DOS
    compatible FAT file system, and our tiny thread aware UDP/IP stack.

    http://www.FreeRTOS.org/labs - Where new FreeRTOS products go to incubate.
    Come and try FreeRTOS+TCP, our new open source TCP/IP stack for FreeRTOS.

    http://www.OpenRTOS.com - Real Time Engineers ltd. license FreeRTOS to High
    Integrity Systems ltd. to sell under the OpenRTOS brand.  Low cost OpenRTOS
    licenses offer ticketed support, indemnification and commercial middleware.

    http://www.SafeRTOS.com - High Integrity Systems also provide a safety
    engineered and independently SIL3 certified version for use in safety and
    mission critical applications that require provable dependability.

    1 tab == 4 spaces!
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












