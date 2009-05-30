/*
	FreeRTOS.org V5.3.0 - Copyright (C) 2003-2009 Richard Barry.

	This file is part of the FreeRTOS.org distribution.

	FreeRTOS.org is free software; you can redistribute it and/or modify it
	under the terms of the GNU General Public License (version 2) as published
	by the Free Software Foundation and modified by the FreeRTOS exception.
	**NOTE** The exception to the GPL is included to allow you to distribute a
	combined work that includes FreeRTOS.org without being obliged to provide
	the source code for any proprietary components.  Alternative commercial
	license and support terms are also available upon request.  See the 
	licensing section of http://www.FreeRTOS.org for full details.

	FreeRTOS.org is distributed in the hope that it will be useful,	but WITHOUT
	ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
	FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
	more details.

	You should have received a copy of the GNU General Public License along
	with FreeRTOS.org; if not, write to the Free Software Foundation, Inc., 59
	Temple Place, Suite 330, Boston, MA  02111-1307  USA.


	***************************************************************************
	*                                                                         *
	* Get the FreeRTOS eBook!  See http://www.FreeRTOS.org/Documentation      *
	*                                                                         *
	* This is a concise, step by step, 'hands on' guide that describes both   *
	* general multitasking concepts and FreeRTOS specifics. It presents and   *
	* explains numerous examples that are written using the FreeRTOS API.     *
	* Full source code for all the examples is provided in an accompanying    *
	* .zip file.                                                              *
	*                                                                         *
	***************************************************************************

	1 tab == 4 spaces!

	Please ensure to read the configuration and relevant port sections of the
	online documentation.

	http://www.FreeRTOS.org - Documentation, latest information, license and
	contact details.

	http://www.SafeRTOS.com - A version that is certified for use in safety
	critical systems.

	http://www.OpenRTOS.com - Commercial support, development, porting,
	licensing and training services.
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
#define mainCHECK_DELAY		( 3000 / portTICK_RATE_MS )

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
unsigned portSHORT usCheckStatus = 0;

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
void vPrintDisplayMessage( const portCHAR * const * ppcMessageToSend )
{
	( void ) ppcMessageToSend;
}












