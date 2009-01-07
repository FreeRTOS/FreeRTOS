/*
	FreeRTOS.org V5.1.1 - Copyright (C) 2003-2008 Richard Barry.

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
    ***************************************************************************
    *                                                                         *
    * SAVE TIME AND MONEY!  We can port FreeRTOS.org to your own hardware,    *
    * and even write all or part of your application on your behalf.          *
    * See http://www.OpenRTOS.com for details of the services we provide to   *
    * expedite your project.                                                  *
    *                                                                         *
    ***************************************************************************
    ***************************************************************************

	Please ensure to read the configuration and relevant port sections of the
	online documentation.

	http://www.FreeRTOS.org - Documentation, latest information, license and
	contact details.

	http://www.SafeRTOS.com - A version that is certified for use in safety
	critical systems.

	http://www.OpenRTOS.com - Commercial support, development, porting,
	licensing and training services.
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
#include "flash.h"
#include "GenQTest.h"
#include "integer.h"
#include "PollQ.h"
#include "QPeek.h"
#include "recmutex.h"
#include "semtest.h"
#include "ParTest.h"

/* Standard includes. */
#include <stdio.h>

/* Priorities for the demo application tasks. */
#define mainLED_TASK_PRIORITY		( tskIDLE_PRIORITY + 3 )
#define mainCOM_TEST_PRIORITY		( tskIDLE_PRIORITY + 2 )
#define mainQUEUE_POLL_PRIORITY		( tskIDLE_PRIORITY + 0 )
#define mainCHECK_TASK_PRIORITY		( tskIDLE_PRIORITY + 4 )
#define mainSEM_TEST_PRIORITY		( tskIDLE_PRIORITY + 0 )
#define mainBLOCK_Q_PRIORITY		( tskIDLE_PRIORITY + 2 )
#define mainCREATOR_TASK_PRIORITY 	( tskIDLE_PRIORITY + 3 )
#define mainGENERIC_QUEUE_PRIORITY	( tskIDLE_PRIORITY )

/* The period of the check task both in and out of the presense of an error. */
#define mainNO_ERROR_PERIOD			( 5000 / portTICK_RATE_MS )
#define mainERROR_PERIOD			( 500 / portTICK_RATE_MS );
/*-----------------------------------------------------------*/

/* Simple hardware setup required by the demo. */
static void prvSetupHardware( void );

/* The check task as described at the top of this file. */
static void prvCheckTask( void *pvParameters );

/*-----------------------------------------------------------*/
int main()
{
	prvSetupHardware();
	
	/* Start the standard demo tasks. */
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
portTickType xNextWakeTime, xPeriod = mainNO_ERROR_PERIOD;
static volatile unsigned portLONG ulErrorCode = 0UL;

	/* Initialise xNextWakeTime prior to its first use.  From this point on
	the value of the variable is handled automatically by the kernel. */
	xNextWakeTime = xTaskGetTickCount();
	
	for( ;; )
	{
		vTaskDelayUntil( &xNextWakeTime, xPeriod );
		
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
		
		if( ulErrorCode != 0x00 )
		{
			xPeriod = mainERROR_PERIOD;
		}
		
		vParTestToggleLED( LED_DS1 );
	}
}
/*-----------------------------------------------------------*/

static void prvSetupHardware( void )
{
	vParTestInitialise();
}
