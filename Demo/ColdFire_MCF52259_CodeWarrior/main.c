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
 * "Web server" - Very basic demonstration of the lwIP stack.  The WEB server
 * simply generates a page that shows the current state of all the tasks within
 * the system, including the high water mark of each task stack. The high water
 * mark is displayed as the amount of stack that has never been used, so the
 * closer the value is to zero the closer the task has come to overflowing its
 * stack.  The IP address and net mask are set within FreeRTOSConfig.h.
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
#include "flash.h"
#include "partest.h"
#include "semtest.h"
#include "PollQ.h"
#include "GenQTest.h"
#include "QPeek.h"
#include "recmutex.h"

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
#define mainCREATOR_TASK_PRIORITY           ( tskIDLE_PRIORITY + 2 )
#define mainINTEGER_TASK_PRIORITY           ( tskIDLE_PRIORITY )
#define mainGEN_QUEUE_TASK_PRIORITY			( tskIDLE_PRIORITY )
#define mainWEB_TASK_PRIORITY       		( tskIDLE_PRIORITY + 2 )

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
 * Implement the 'Reg test' functionality as described at the top of this file.
 */
static void vRegTest1Task( void *pvParameters );
static void vRegTest2Task( void *pvParameters );

/*-----------------------------------------------------------*/

/* Counters used to detect errors within the reg test tasks. */
static volatile unsigned portLONG ulRegTest1Counter = 0x11111111, ulRegTest2Counter = 0x22222222;

/*-----------------------------------------------------------*/

int main( void )
{
extern void vBasicWEBServer( void *pv );

	/* Setup the hardware ready for this demo. */
	prvSetupHardware();
	( void )sys_thread_new("HTTPD", vBasicWEBServer, NULL, 320, mainWEB_TASK_PRIORITY );

	/* Start the standard demo tasks. */
	vStartLEDFlashTasks( tskIDLE_PRIORITY );
	vStartSemaphoreTasks( mainSEM_TEST_PRIORITY );
	vStartPolledQueueTasks( mainQUEUE_POLL_PRIORITY );
	vStartGenericQueueTasks( mainGEN_QUEUE_TASK_PRIORITY );
	vStartQueuePeekTasks();
	vStartRecursiveMutexTasks();
	vStartBlockingQueueTasks( mainBLOCK_Q_PRIORITY );

	/* Start the reg test tasks - defined in this file. */
	xTaskCreate( vRegTest1Task, ( signed portCHAR * ) "Reg1", configMINIMAL_STACK_SIZE, ( void * ) &ulRegTest1Counter, tskIDLE_PRIORITY, NULL );
	xTaskCreate( vRegTest2Task, ( signed portCHAR * ) "Reg2", configMINIMAL_STACK_SIZE, ( void * ) &ulRegTest2Counter, tskIDLE_PRIORITY, NULL );

	/* Create the check task. */
	xTaskCreate( prvCheckTask, ( signed portCHAR * ) "Check", configMINIMAL_STACK_SIZE, NULL, mainCHECK_TASK_PRIORITY, NULL );

	/* The suicide tasks must be created last as they need to know how many
	tasks were running prior to their creation in order to ascertain whether
	or not the correct/expected number of tasks are running at any given time. */
    vCreateSuicidalTasks( mainCREATOR_TASK_PRIORITY );

	/* Start the scheduler. */
	vTaskStartScheduler();

    /* Will only get here if there was insufficient memory to create the idle
    task. */
	for( ;; )
	{
	}
}
/*-----------------------------------------------------------*/

static void prvCheckTask( void *pvParameters )
{
unsigned ulTicksToWait = mainNO_ERROR_PERIOD, ulError = 0, ulLastRegTest1Count = 0, ulLastRegTest2Count = 0;
portTickType xLastExecutionTime;

	( void ) pvParameters;

	/* Initialise the variable used to control our iteration rate prior to
	its first use. */
	xLastExecutionTime = xTaskGetTickCount();

	for( ;; )
	{
		/* Wait until it is time to run the tests again. */
		vTaskDelayUntil( &xLastExecutionTime, ulTicksToWait );

		/* Has an error been found in any task? */
		if( xAreGenericQueueTasksStillRunning() != pdTRUE )
		{
			ulError |= 0x01UL;
		}

		if( xAreQueuePeekTasksStillRunning() != pdTRUE )
		{
			ulError |= 0x02UL;
		}

		if( xAreBlockingQueuesStillRunning() != pdTRUE )
		{
			ulError |= 0x04UL;
		}

		if( xAreSemaphoreTasksStillRunning() != pdTRUE )
	    {
	    	ulError |= 0x20UL;
	    }

		if( xArePollingQueuesStillRunning() != pdTRUE )
	    {
	    	ulError |= 0x40UL;
	    }

		if( xIsCreateTaskStillRunning() != pdTRUE )
	    {
	    	ulError |= 0x80UL;
	    }

		if( xAreRecursiveMutexTasksStillRunning() != pdTRUE )
	    {
	    	ulError |= 0x200UL;
	    }

		if( ulLastRegTest1Count == ulRegTest1Counter )
		{
			ulError |= 0x1000UL;
		}

		if( ulLastRegTest2Count == ulRegTest2Counter )
		{
			ulError |= 0x1000UL;
		}

		ulLastRegTest1Count = ulRegTest1Counter;
		ulLastRegTest2Count = ulRegTest2Counter;

		/* If an error has been found then increase our cycle rate, and in so
		going increase the rate at which the check task LED toggles. */
		if( ulError != 0 )
		{
	    	ulTicksToWait = mainERROR_PERIOD;
		}

		/* Toggle the LED each itteration. */
		vParTestToggleLED( mainCHECK_LED );
	}
}
/*-----------------------------------------------------------*/

void prvSetupHardware( void )
{
	portDISABLE_INTERRUPTS();

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

	for( ;; )
	{
	}
}
/*-----------------------------------------------------------*/

static void vRegTest1Task( void *pvParameters )
{
	/* Sanity check - did we receive the parameter expected? */
	if( pvParameters != &ulRegTest1Counter )
	{
		/* Change here so the check task can detect that an error occurred. */
		for( ;; )
		{
		}
	}

	/* Set all the registers to known values, then check that each retains its
	expected value - as described at the top of this file.  If an error is
	found then the loop counter will no longer be incremented allowing the check
	task to recognise the error. */
	asm volatile 	(	"reg_test_1_start:						\n\t"
						"	moveq		#1, d0					\n\t"
						"	moveq		#2, d1					\n\t"
						"	moveq		#3, d2					\n\t"
						"	moveq		#4, d3					\n\t"
						"	moveq		#5, d4					\n\t"
						"	moveq		#6, d5					\n\t"
						"	moveq		#7, d6					\n\t"
						"	moveq		#8, d7					\n\t"
						"	move		#9, a0					\n\t"
						"	move		#10, a1					\n\t"
						"	move		#11, a2					\n\t"
						"	move		#12, a3					\n\t"
						"	move		#13, a4					\n\t"
						"	move		#14, a5					\n\t"
						"	move		#15, a6					\n\t"
						"										\n\t"
						"	cmpi.l		#1, d0					\n\t"
						"	bne			reg_test_1_error		\n\t"
						"	cmpi.l		#2, d1					\n\t"
						"	bne			reg_test_1_error		\n\t"
						"	cmpi.l		#3, d2					\n\t"
						"	bne			reg_test_1_error		\n\t"
						"	cmpi.l		#4, d3					\n\t"
						"	bne			reg_test_1_error		\n\t"
						"	cmpi.l		#5, d4					\n\t"
						"	bne			reg_test_1_error		\n\t"
						"	cmpi.l		#6, d5					\n\t"
						"	bne			reg_test_1_error		\n\t"
						"	cmpi.l		#7, d6					\n\t"
						"	bne			reg_test_1_error		\n\t"
						"	cmpi.l		#8, d7					\n\t"
						"	bne			reg_test_1_error		\n\t"
						"	move		a0, d0					\n\t"
						"	cmpi.l		#9, d0					\n\t"
						"	bne			reg_test_1_error		\n\t"
						"	move		a1, d0					\n\t"
						"	cmpi.l		#10, d0					\n\t"
						"	bne			reg_test_1_error		\n\t"
						"	move		a2, d0					\n\t"
						"	cmpi.l		#11, d0					\n\t"
						"	bne			reg_test_1_error		\n\t"
						"	move		a3, d0					\n\t"
						"	cmpi.l		#12, d0					\n\t"
						"	bne			reg_test_1_error		\n\t"
						"	move		a4, d0					\n\t"
						"	cmpi.l		#13, d0					\n\t"
						"	bne			reg_test_1_error		\n\t"
						"	move		a5, d0					\n\t"
						"	cmpi.l		#14, d0					\n\t"
						"	bne			reg_test_1_error		\n\t"
						"	move		a6, d0					\n\t"
						"	cmpi.l		#15, d0					\n\t"
						"	bne			reg_test_1_error		\n\t"
						"	move		ulRegTest1Counter, d0	\n\t"
						"	addq		#1, d0					\n\t"
						"	move		d0, ulRegTest1Counter	\n\t"
						"	bra			reg_test_1_start		\n\t"
						"reg_test_1_error:						\n\t"
						"	bra			reg_test_1_error		\n\t"
					);
}
/*-----------------------------------------------------------*/

static void vRegTest2Task( void *pvParameters )
{
	/* Sanity check - did we receive the parameter expected? */
	if( pvParameters != &ulRegTest2Counter )
	{
		/* Change here so the check task can detect that an error occurred. */
		for( ;; )
		{
		}
	}

	/* Set all the registers to known values, then check that each retains its
	expected value - as described at the top of this file.  If an error is
	found then the loop counter will no longer be incremented allowing the check
	task to recognise the error. */
	asm volatile 	(	"reg_test_2_start:						\n\t"
						"	moveq		#10, d0					\n\t"
						"	moveq		#20, d1					\n\t"
						"	moveq		#30, d2					\n\t"
						"	moveq		#40, d3					\n\t"
						"	moveq		#50, d4					\n\t"
						"	moveq		#60, d5					\n\t"
						"	moveq		#70, d6					\n\t"
						"	moveq		#80, d7					\n\t"
						"	move		#90, a0					\n\t"
						"	move		#100, a1				\n\t"
						"	move		#110, a2				\n\t"
						"	move		#120, a3				\n\t"
						"	move		#130, a4				\n\t"
						"	move		#140, a5				\n\t"
						"	move		#150, a6				\n\t"
						"										\n\t"
						"	cmpi.l		#10, d0					\n\t"
						"	bne			reg_test_2_error		\n\t"
						"	cmpi.l		#20, d1					\n\t"
						"	bne			reg_test_2_error		\n\t"
						"	cmpi.l		#30, d2					\n\t"
						"	bne			reg_test_2_error		\n\t"
						"	cmpi.l		#40, d3					\n\t"
						"	bne			reg_test_2_error		\n\t"
						"	cmpi.l		#50, d4					\n\t"
						"	bne			reg_test_2_error		\n\t"
						"	cmpi.l		#60, d5					\n\t"
						"	bne			reg_test_2_error		\n\t"
						"	cmpi.l		#70, d6					\n\t"
						"	bne			reg_test_2_error		\n\t"
						"	cmpi.l		#80, d7					\n\t"
						"	bne			reg_test_2_error		\n\t"
						"	move		a0, d0					\n\t"
						"	cmpi.l		#90, d0					\n\t"
						"	bne			reg_test_2_error		\n\t"
						"	move		a1, d0					\n\t"
						"	cmpi.l		#100, d0				\n\t"
						"	bne			reg_test_2_error		\n\t"
						"	move		a2, d0					\n\t"
						"	cmpi.l		#110, d0				\n\t"
						"	bne			reg_test_2_error		\n\t"
						"	move		a3, d0					\n\t"
						"	cmpi.l		#120, d0				\n\t"
						"	bne			reg_test_2_error		\n\t"
						"	move		a4, d0					\n\t"
						"	cmpi.l		#130, d0				\n\t"
						"	bne			reg_test_2_error		\n\t"
						"	move		a5, d0					\n\t"
						"	cmpi.l		#140, d0				\n\t"
						"	bne			reg_test_2_error		\n\t"
						"	move		a6, d0					\n\t"
						"	cmpi.l		#150, d0				\n\t"
						"	bne			reg_test_2_error		\n\t"
						"	move		ulRegTest1Counter, d0	\n\t"
						"	addq		#1, d0					\n\t"
						"	move		d0, ulRegTest2Counter	\n\t"
						"	bra			reg_test_2_start		\n\t"
						"reg_test_2_error:						\n\t"
						"	bra			reg_test_2_error		\n\t"
					);
}
/*-----------------------------------------------------------*/



