/*
	FreeRTOS.org V5.1.0 - Copyright (C) 2003-2008 Richard Barry.

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


/*
 * Creates all the demo application tasks, then starts the scheduler.  The WEB
 * documentation provides more details of the standard demo application tasks.
 * In addition to the standard demo tasks, the following tasks and tests are
 * defined and/or created within this file:
 *
 * "Check" task -  This only executes every five seconds but has a high priority
 * to ensure it gets processor time.  Its main function is to check that all the
 * standard demo tasks are still operational.  While no errors have been
 * discovered the check task will toggle an LED every 5 seconds - the toggle
 * rate increasing to 500ms being a visual indication that at least one task has
 * reported unexpected behaviour.
 *
 * "Reg test" tasks - These fill the registers with known values, then check
 * that each register still contains its expected value.  Each task uses
 * different values.  The tasks run with very low priority so get preempted very
 * frequently.  A register containing an unexpected value is indicative of an
 * error in the context switching mechanism.
 *
 */

/* Standard includes. */
#include <stdio.h>

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"
#include "semphr.h"

/* Demo app includes. */
#include "BlockQ.h"
#include "death.h"
#include "blocktim.h"
#include "flash.h"
#include "partest.h"
#include "semtest.h"
#include "PollQ.h"
#include "GenQTest.h"
#include "QPeek.h"
#include "recmutex.h"
#include "IntQueue.h"
#include "comtest2.h"

/*-----------------------------------------------------------*/

/* The time between cycles of the 'check' functionality - as described at the
top of this file. */
#define mainNO_ERROR_PERIOD					( ( portTickType ) 5000 / portTICK_RATE_MS )

/* The rate at which the LED controlled by the 'check' task will flash should an
error have been detected. */
#define mainERROR_PERIOD 					( ( portTickType ) 500 / portTICK_RATE_MS )

/* The LED controlled by the 'check' task. */
#define mainCHECK_LED						( 3 )

/* ComTest constants - there is no free LED for the comtest tasks. */
#define mainCOM_TEST_BAUD_RATE				( ( unsigned portLONG ) 19200 )
#define mainCOM_TEST_LED					( 5 )

/* Task priorities. */
#define mainCOM_TEST_PRIORITY				( tskIDLE_PRIORITY + 2 )
#define mainQUEUE_POLL_PRIORITY				( tskIDLE_PRIORITY + 2 )
#define mainCHECK_TASK_PRIORITY				( tskIDLE_PRIORITY + 3 )
#define mainSEM_TEST_PRIORITY				( tskIDLE_PRIORITY + 1 )
#define mainBLOCK_Q_PRIORITY				( tskIDLE_PRIORITY + 2 )
#define mainGEN_QUEUE_TASK_PRIORITY			( tskIDLE_PRIORITY )

/* The WEB server task uses more stack than most other tasks because of its
reliance on using sprintf(). */
#define mainBASIC_WEB_STACK_SIZE			( configMINIMAL_STACK_SIZE * 2 )

static unsigned portLONG ulErrorCode = 0UL;

/*
 * Configure the hardware for the demo.
 */
static void prvSetupHardware( void );

/*
 * Implements the 'check' task functionality as described at the top of this
 * file.
 */
static void prvCheckTask( void *pvParameters );

/*
 * The task that implements the WEB server.
 */
extern void vuIP_Task( void *pvParameters );

/*-----------------------------------------------------------*/

int main( void )
{
	/* Setup the hardware ready for this demo. */
	prvSetupHardware();

	/* Create the WEB server task. */
	xTaskCreate( vuIP_Task, ( signed portCHAR * ) "uIP", mainBASIC_WEB_STACK_SIZE, NULL, mainCHECK_TASK_PRIORITY - 1, NULL );

	/* Start the standard demo tasks. */
	vStartLEDFlashTasks( tskIDLE_PRIORITY );
	vStartBlockingQueueTasks( mainBLOCK_Q_PRIORITY );
    vCreateBlockTimeTasks();
	vStartSemaphoreTasks( mainSEM_TEST_PRIORITY );
	vStartPolledQueueTasks( mainQUEUE_POLL_PRIORITY );
	vStartGenericQueueTasks( mainGEN_QUEUE_TASK_PRIORITY );
	vStartQueuePeekTasks();
    vStartRecursiveMutexTasks();

	/* Create the check task. */
	xTaskCreate( prvCheckTask, ( signed portCHAR * ) "Check", configMINIMAL_STACK_SIZE, NULL, mainCHECK_TASK_PRIORITY, NULL );

	/* Start the scheduler. */
	vTaskStartScheduler();

    /* Will only get here if there was insufficient memory to create the idle
    task. */
	for( ;; );
}
/*-----------------------------------------------------------*/

static void prvCheckTask( void *pvParameters )
{
portTickType xLastExecutionTime;

	( void ) pvParameters;

	/* Initialise the variable used to control our iteration rate prior to
	its first use. */
	xLastExecutionTime = xTaskGetTickCount();

	for( ;; )
	{
		/* Wait until it is time to run the tests again. */
		vTaskDelayUntil( &xLastExecutionTime, mainNO_ERROR_PERIOD );

		/* Has an error been found in any task? */
		if( xAreGenericQueueTasksStillRunning() != pdTRUE )
		{
			ulErrorCode |= 0x01UL;
		}

		if( xAreQueuePeekTasksStillRunning() != pdTRUE )
		{
			ulErrorCode |= 0x02UL;
		}

		if( xAreBlockingQueuesStillRunning() != pdTRUE )
		{
			ulErrorCode |= 0x04UL;
		}

		if( xAreSemaphoreTasksStillRunning() != pdTRUE )
	    {
	    	ulErrorCode |= 0x20UL;
	    }

		if( xArePollingQueuesStillRunning() != pdTRUE )
	    {
	    	ulErrorCode |= 0x40UL;
	    }

		if( xAreBlockTimeTestTasksStillRunning() != pdTRUE )
		{
			ulErrorCode |= 0x80UL;
		}

	    if( xAreRecursiveMutexTasksStillRunning() != pdTRUE )
	    {
	    	ulErrorCode |= 0x100UL;
	    }
	}
}
/*-----------------------------------------------------------*/

unsigned portLONG ulGetErrorCode( void )
{
	return ulErrorCode;
}
/*-----------------------------------------------------------*/

void prvSetupHardware( void )
{
__attribute__ ((section(".cfmconfig")))
static const unsigned long _cfm[6] = {
	0, /* KEY_UPPER 0x00000400 */
	0, /* KEY_LOWER 0x00000404 */
	0, /* CFMPROT 0x00000408 */
	0, /* CFMSACC 0x0000040C */
	0, /* CFMDACC 0x00000410 */
	0, /* CFMSEC 0x00000414 */
};

	/* Just to stop compiler warnings. */
	( void ) _cfm;

	/* Ensure the watchdog is disabled. */
	MCF_SCM_CWCR = 0;

    /* Initialize IPSBAR (0x40000000). */
	asm volatile(
		"move.l  #0x40000000,%d0	\n"
		"andi.l  #0xC0000000,%d0	\n"
		"add.l   #0x1,%d0			\n"
		"move.l  %d0,0x40000000		"
	);

    /* Initialize FLASHBAR (0x00) */
	asm volatile(
		"move.l  #0x00,%d0			\n"
		"andi.l  #0xFFF80000,%d0	\n"
		"add.l   #0x41,%d0			\n"
		"movec   %d0,%FLASHBAR		"
	);

	portDISABLE_INTERRUPTS();

	/* RAMBAR. */
	MCF_SCM_RAMBAR = MCF_SCM_RAMBAR_BA( RAMBAR_ADDRESS ) | MCF_SCM_RAMBAR_BDE;

	/* Multiply 25MHz crystal by 12 to get 60MHz clock. */
	MCF_CLOCK_SYNCR = MCF_CLOCK_SYNCR_MFD(4) | MCF_CLOCK_SYNCR_CLKSRC| MCF_CLOCK_SYNCR_PLLMODE | MCF_CLOCK_SYNCR_PLLEN ;
	while (!(MCF_CLOCK_SYNSR & MCF_CLOCK_SYNSR_LOCK))
	{
	}

	/* Setup the port used to toggle LEDs. */
	vParTestInitialise();
}
/*-----------------------------------------------------------*/

void vApplicationStackOverflowHook( xTaskHandle *pxTask, signed portCHAR *pcTaskName )
{
	/* This will get called if a stack overflow is detected during the context
	switch.  Set configCHECK_FOR_STACK_OVERFLOWS to 2 to also check for stack
	problems within nested interrupts, but only do this for debug purposes as
	it will increase the context switch time. */

	( void ) pxTask;
	( void ) pcTaskName;

	for( ;; );
}
/*-----------------------------------------------------------*/

