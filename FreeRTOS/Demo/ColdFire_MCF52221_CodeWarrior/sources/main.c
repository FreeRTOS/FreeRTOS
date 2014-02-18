/*
    FreeRTOS V8.0.0 - Copyright (C) 2014 Real Time Engineers Ltd.
    All rights reserved

    VISIT http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

    ***************************************************************************
     *                                                                       *
     *    FreeRTOS provides completely free yet professionally developed,    *
     *    robust, strictly quality controlled, supported, and cross          *
     *    platform software that has become a de facto standard.             *
     *                                                                       *
     *    Help yourself get started quickly and support the FreeRTOS         *
     *    project by purchasing a FreeRTOS tutorial book, reference          *
     *    manual, or both from: http://www.FreeRTOS.org/Documentation        *
     *                                                                       *
     *    Thank you!                                                         *
     *                                                                       *
    ***************************************************************************

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation >>!AND MODIFIED BY!<< the FreeRTOS exception.

    >>! NOTE: The modification to the GPL is included to allow you to distribute
    >>! a combined work that includes FreeRTOS without being obliged to provide
    >>! the source code for proprietary components outside of the FreeRTOS
    >>! kernel.

    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT ANY
    WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
    FOR A PARTICULAR PURPOSE.  Full license text is available from the following
    link: http://www.freertos.org/a00114.html

    1 tab == 4 spaces!

    ***************************************************************************
     *                                                                       *
     *    Having a problem?  Start by reading the FAQ "My application does   *
     *    not run, what could be wrong?"                                     *
     *                                                                       *
     *    http://www.FreeRTOS.org/FAQHelp.html                               *
     *                                                                       *
    ***************************************************************************

    http://www.FreeRTOS.org - Documentation, books, training, latest versions,
    license and Real Time Engineers Ltd. contact details.

    http://www.FreeRTOS.org/plus - A selection of FreeRTOS ecosystem products,
    including FreeRTOS+Trace - an indispensable productivity tool, a DOS
    compatible FAT file system, and our tiny thread aware UDP/IP stack.

    http://www.OpenRTOS.com - Real Time Engineers ltd license FreeRTOS to High
    Integrity Systems to sell under the OpenRTOS brand.  Low cost OpenRTOS
    licenses offer ticketed support, indemnification and middleware.

    http://www.SafeRTOS.com - High Integrity Systems also provide a safety
    engineered and independently SIL3 certified version for use in safety and
    mission critical applications that require provable dependability.

    1 tab == 4 spaces!
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
#include "crflash.h"
#include "partest.h"
#include "semtest.h"
#include "GenQTest.h"
#include "QPeek.h"
#include "comtest2.h"

/*-----------------------------------------------------------*/

/* The time between cycles of the 'check' functionality - as described at the
top of this file. */
#define mainNO_ERROR_PERIOD					( ( TickType_t ) 5000 / portTICK_PERIOD_MS )

/* The rate at which the LED controlled by the 'check' task will flash should an
error have been detected. */
#define mainERROR_PERIOD 					( ( TickType_t ) 500 / portTICK_PERIOD_MS )

/* The LED controlled by the 'check' task. */
#define mainCHECK_LED						( 3 )

/* ComTest constants - there is no free LED for the comtest tasks. */
#define mainCOM_TEST_BAUD_RATE				( ( unsigned long ) 19200 )
#define mainCOM_TEST_LED					( 5 )

/* Task priorities. */
#define mainCOM_TEST_PRIORITY				( tskIDLE_PRIORITY + 2 )
#define mainCHECK_TASK_PRIORITY				( tskIDLE_PRIORITY + 3 )
#define mainSEM_TEST_PRIORITY				( tskIDLE_PRIORITY + 1 )
#define mainBLOCK_Q_PRIORITY				( tskIDLE_PRIORITY + 2 )
#define mainGEN_QUEUE_TASK_PRIORITY			( tskIDLE_PRIORITY )

/* Co-routines are used to flash the LEDs. */
#define mainNUM_FLASH_CO_ROUTINES			( 3 )

/* The baud rate used by the comtest tasks. */
#define mainBAUD_RATE 						( 38400 )

/* There is no spare LED for the comtest tasks, so this is set to an invalid
number. */
#define mainCOM_LED							( 4 )

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
static volatile unsigned long ulRegTest1Counter = 0x11111111, ulRegTest2Counter = 0x22222222;

/*-----------------------------------------------------------*/

int main( void )
{
	/* Setup the hardware ready for this demo. */
	prvSetupHardware();

	/* Start the standard demo tasks. */
	vStartSemaphoreTasks( mainSEM_TEST_PRIORITY );
	vStartGenericQueueTasks( mainGEN_QUEUE_TASK_PRIORITY );
	vStartQueuePeekTasks();
	vStartBlockingQueueTasks( mainBLOCK_Q_PRIORITY );
	vAltStartComTestTasks( mainCOM_TEST_PRIORITY, mainBAUD_RATE, mainCOM_LED );

	/* For demo purposes use some co-routines to flash the LEDs. */
	vStartFlashCoRoutines( mainNUM_FLASH_CO_ROUTINES );

	/* Create the check task. */
	xTaskCreate( prvCheckTask, "Check", configMINIMAL_STACK_SIZE, NULL, mainCHECK_TASK_PRIORITY, NULL );


	/* Start the reg test tasks - defined in this file. */
	xTaskCreate( vRegTest1Task, "Reg1", configMINIMAL_STACK_SIZE, ( void * ) &ulRegTest1Counter, tskIDLE_PRIORITY, NULL );
	xTaskCreate( vRegTest2Task, "Reg2", configMINIMAL_STACK_SIZE, ( void * ) &ulRegTest2Counter, tskIDLE_PRIORITY, NULL );

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
unsigned long ulTicksToWait = mainNO_ERROR_PERIOD, ulError = 0, ulLastRegTest1Count = 0, ulLastRegTest2Count = 0;
TickType_t xLastExecutionTime;
volatile unsigned portBASE_TYPE uxUnusedStack;

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

	    if( xAreComTestTasksStillRunning() != pdTRUE )
	    {
	    	ulError |= 0x40UL;
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
		doing increase the rate at which the check task LED toggles. */
		if( ulError != 0 )
		{
	    	ulTicksToWait = mainERROR_PERIOD;
		}

		/* Toggle the LED each itteration. */
		vParTestToggleLED( mainCHECK_LED );

		/* For demo only - how much unused stack does this task have? */
		uxUnusedStack = uxTaskGetStackHighWaterMark( NULL );
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

void vApplicationStackOverflowHook( TaskHandle_t *pxTask, signed char *pcTaskName )
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

void vApplicationIdleHook( void );
void vApplicationIdleHook( void )
{
	/* The co-routines run in the idle task. */
	vCoRoutineSchedule();
}
/*-----------------------------------------------------------*/

void exit( int n )
{
	/* To keep the linker happy only as the libraries have been removed from
	the build. */
	( void ) n;
	for( ;; ) {}
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



