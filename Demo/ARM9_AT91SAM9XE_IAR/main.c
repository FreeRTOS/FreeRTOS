/*
	FreeRTOS.org V5.4.0 - Copyright (C) 2003-2009 Richard Barry.

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
#define mainNO_ERROR_PERIOD			( 5000 / portTICK_RATE_MS )
#define mainERROR_PERIOD			( 500 / portTICK_RATE_MS );

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
portTickType xNextWakeTime, xPeriod = mainNO_ERROR_PERIOD;
static volatile unsigned portLONG ulErrorCode = 0UL;

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
