/*
 * FreeRTOS Kernel V10.4.1
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


/*
 * Creates all the demo application tasks, then starts the scheduler.  The WEB
 * documentation provides more details of the standard demo application tasks.
 * In addition to the standard demo tasks, the following tasks and tests are
 * defined and/or created within this file:
 *
 * "uIP" task -  This is the task that handles the uIP stack.  All TCP/IP
 * processing is performed in this task.  It manages the WEB server functionality.
 *
 * "Check" task -  This only executes every five seconds but has a high priority
 * to ensure it gets processor time.  Its main function is to check that all the
 * standard demo tasks are still operational.  An error found in any task will be
 * latched in the ulErrorCode variable for display through the WEB server (the
 * error code is displayed at the foot of the table that contains information on
 * the state of each task).
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
#define mainCHECK_TASK_PERIOD					( ( portTickType ) 5000 / portTICK_RATE_MS )

/* Task priorities. */
#define mainQUEUE_POLL_PRIORITY				( tskIDLE_PRIORITY + 2 )
#define mainCHECK_TASK_PRIORITY				( tskIDLE_PRIORITY + 3 )
#define mainSEM_TEST_PRIORITY				( tskIDLE_PRIORITY + 1 )
#define mainBLOCK_Q_PRIORITY				( tskIDLE_PRIORITY + 2 )
#define mainGEN_QUEUE_TASK_PRIORITY			( tskIDLE_PRIORITY )

/* The WEB server task uses more stack than most other tasks because of its
reliance on using sprintf(). */
#define mainBASIC_WEB_STACK_SIZE			( configMINIMAL_STACK_SIZE * 2 )

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

/*
 * Implement the 'Reg test' functionality as described at the top of this file.
 */
static void vRegTest1Task( void *pvParameters );
static void vRegTest2Task( void *pvParameters );

/*-----------------------------------------------------------*/

/* Counters used to detect errors within the reg test tasks. */
static volatile unsigned long ulRegTest1Counter = 0x11111111, ulRegTest2Counter = 0x22222222;

/* Any errors that the check task finds in any tasks are latched into
ulErrorCode, and then displayed via the WEB server. */
static unsigned long ulErrorCode = 0UL;

/*-----------------------------------------------------------*/

int main( void )
{
	/* Setup the hardware ready for this demo. */
	prvSetupHardware();

	/* Create the WEB server task. */
	xTaskCreate( vuIP_Task, "uIP", mainBASIC_WEB_STACK_SIZE, NULL, mainCHECK_TASK_PRIORITY - 1, NULL );

	/* Start the standard demo tasks. */
	vStartLEDFlashTasks( tskIDLE_PRIORITY );
	vStartBlockingQueueTasks( mainBLOCK_Q_PRIORITY );
    vCreateBlockTimeTasks();
	vStartSemaphoreTasks( mainSEM_TEST_PRIORITY );
	vStartPolledQueueTasks( mainQUEUE_POLL_PRIORITY );
	vStartGenericQueueTasks( mainGEN_QUEUE_TASK_PRIORITY );
	vStartQueuePeekTasks();
    vStartRecursiveMutexTasks();

	/* Start the reg test tasks - defined in this file. */
	xTaskCreate( vRegTest1Task, "Reg1", configMINIMAL_STACK_SIZE, ( void * ) &ulRegTest1Counter, tskIDLE_PRIORITY, NULL );
	xTaskCreate( vRegTest2Task, "Reg2", configMINIMAL_STACK_SIZE, ( void * ) &ulRegTest2Counter, tskIDLE_PRIORITY, NULL );

	/* Create the check task. */
	xTaskCreate( prvCheckTask, "Check", configMINIMAL_STACK_SIZE, NULL, mainCHECK_TASK_PRIORITY, NULL );

	/* Start the scheduler. */
	vTaskStartScheduler();

    /* Will only get here if there was insufficient heap to create the idle
    task. */
	for( ;; );
}
/*-----------------------------------------------------------*/

static void prvCheckTask( void *pvParameters )
{
unsigned ulLastRegTest1Count = 0, ulLastRegTest2Count = 0;
portTickType xLastExecutionTime;

	/* To prevent compiler warnings. */
	( void ) pvParameters;

	/* Initialise the variable used to control our iteration rate prior to
	its first use. */
	xLastExecutionTime = xTaskGetTickCount();

	for( ;; )
	{
		/* Wait until it is time to run the tests again. */
		vTaskDelayUntil( &xLastExecutionTime, mainCHECK_TASK_PERIOD );

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

		if( ulLastRegTest1Count == ulRegTest1Counter )
		{
			ulErrorCode |= 0x200UL;
		}

		if( ulLastRegTest2Count == ulRegTest2Counter )
		{
			ulErrorCode |= 0x200UL;
		}

		/* Remember the reg test counts so a stall in their values can be
		detected next time around. */
		ulLastRegTest1Count = ulRegTest1Counter;
		ulLastRegTest2Count = ulRegTest2Counter;
	}
}
/*-----------------------------------------------------------*/

unsigned long ulGetErrorCode( void )
{
	/* Returns the error code for display via the WEB server. */
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

void vApplicationStackOverflowHook( xTaskHandle pxTask, char *pcTaskName )
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

static void vRegTest1Task( void *pvParameters )
{
	/* Sanity check - did we receive the parameter expected? */
	if( pvParameters != &ulRegTest1Counter )
	{
		/* Change here so the check task can detect that an error occurred. */
		for( ;; );
	}

	/* Set all the registers to known values, then check that each retains its
	expected value - as described at the top of this file.  If an error is
	found then the loop counter will no longer be incremented allowing the check
	task to recognise the error. */
	asm volatile 	(	"reg_test_1_start:						\n\t"
						"	moveq		#1, %d0					\n\t"
						"	moveq		#2, %d1					\n\t"
						"	moveq		#3, %d2					\n\t"
						"	moveq		#4, %d3					\n\t"
						"	moveq		#5, %d4					\n\t"
						"	moveq		#6, %d5					\n\t"
						"	moveq		#7, %d6					\n\t"
						"	moveq		#8, %d7					\n\t"
						"	move		#9, %a0					\n\t"
						"	move		#10, %a1				\n\t"
						"	move		#11, %a2				\n\t"
						"	move		#12, %a3				\n\t"
						"	move		#13, %a4				\n\t"
						"	move		#14, %a5				\n\t"
						"	move		#15, %a6				\n\t"
						"										\n\t"
						"	cmpi.l		#1, %d0					\n\t"
						"	bne			reg_test_1_error		\n\t"
						"	cmpi.l		#2, %d1					\n\t"
						"	bne			reg_test_1_error		\n\t"
						"	cmpi.l		#3, %d2					\n\t"
						"	bne			reg_test_1_error		\n\t"
						"	cmpi.l		#4, %d3					\n\t"
						"	bne			reg_test_1_error		\n\t"
						"	cmpi.l		#5, %d4					\n\t"
						"	bne			reg_test_1_error		\n\t"
						"	cmpi.l		#6, %d5					\n\t"
						"	bne			reg_test_1_error		\n\t"
						"	cmpi.l		#7, %d6					\n\t"
						"	bne			reg_test_1_error		\n\t"
						"	cmpi.l		#8, %d7					\n\t"
						"	bne			reg_test_1_error		\n\t"
						"	move		%a0, %d0				\n\t"
						"	cmpi.l		#9, %d0					\n\t"
						"	bne			reg_test_1_error		\n\t"
						"	move		%a1, %d0				\n\t"
						"	cmpi.l		#10, %d0				\n\t"
						"	bne			reg_test_1_error		\n\t"
						"	move		%a2, %d0				\n\t"
						"	cmpi.l		#11, %d0				\n\t"
						"	bne			reg_test_1_error		\n\t"
						"	move		%a3, %d0				\n\t"
						"	cmpi.l		#12, %d0				\n\t"
						"	bne			reg_test_1_error		\n\t"
						"	move		%a4, %d0				\n\t"
						"	cmpi.l		#13, %d0				\n\t"
						"	bne			reg_test_1_error		\n\t"
						"	move		%a5, %d0				\n\t"
						"	cmpi.l		#14, %d0				\n\t"
						"	bne			reg_test_1_error		\n\t"
						"	move		%a6, %d0				\n\t"
						"	cmpi.l		#15, %d0				\n\t"
						"	bne			reg_test_1_error		\n\t"
						"	movel		ulRegTest1Counter, %d0	\n\t"
						"	addql		#1, %d0					\n\t"
						"	movel		%d0, ulRegTest1Counter	\n\t"
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
		for( ;; );
	}

	/* Set all the registers to known values, then check that each retains its
	expected value - as described at the top of this file.  If an error is
	found then the loop counter will no longer be incremented allowing the check
	task to recognise the error. */
	asm volatile 	(	"reg_test_2_start:						\n\t"
						"	moveq		#10, %d0				\n\t"
						"	moveq		#20, %d1				\n\t"
						"	moveq		#30, %d2				\n\t"
						"	moveq		#40, %d3				\n\t"
						"	moveq		#50, %d4				\n\t"
						"	moveq		#60, %d5				\n\t"
						"	moveq		#70, %d6				\n\t"
						"	moveq		#80, %d7				\n\t"
						"	move		#90, %a0				\n\t"
						"	move		#100, %a1				\n\t"
						"	move		#110, %a2				\n\t"
						"	move		#120, %a3				\n\t"
						"	move		#130, %a4				\n\t"
						"	move		#140, %a5				\n\t"
						"	move		#150, %a6				\n\t"
						"										\n\t"
						"	cmpi.l		#10, %d0				\n\t"
						"	bne			reg_test_2_error		\n\t"
						"	cmpi.l		#20, %d1				\n\t"
						"	bne			reg_test_2_error		\n\t"
						"	cmpi.l		#30, %d2				\n\t"
						"	bne			reg_test_2_error		\n\t"
						"	cmpi.l		#40, %d3				\n\t"
						"	bne			reg_test_2_error		\n\t"
						"	cmpi.l		#50, %d4				\n\t"
						"	bne			reg_test_2_error		\n\t"
						"	cmpi.l		#60, %d5				\n\t"
						"	bne			reg_test_2_error		\n\t"
						"	cmpi.l		#70, %d6				\n\t"
						"	bne			reg_test_2_error		\n\t"
						"	cmpi.l		#80, %d7				\n\t"
						"	bne			reg_test_2_error		\n\t"
						"	move		%a0, %d0				\n\t"
						"	cmpi.l		#90, %d0				\n\t"
						"	bne			reg_test_2_error		\n\t"
						"	move		%a1, %d0				\n\t"
						"	cmpi.l		#100, %d0				\n\t"
						"	bne			reg_test_2_error		\n\t"
						"	move		%a2, %d0				\n\t"
						"	cmpi.l		#110, %d0				\n\t"
						"	bne			reg_test_2_error		\n\t"
						"	move		%a3, %d0				\n\t"
						"	cmpi.l		#120, %d0				\n\t"
						"	bne			reg_test_2_error		\n\t"
						"	move		%a4, %d0				\n\t"
						"	cmpi.l		#130, %d0				\n\t"
						"	bne			reg_test_2_error		\n\t"
						"	move		%a5, %d0				\n\t"
						"	cmpi.l		#140, %d0				\n\t"
						"	bne			reg_test_2_error		\n\t"
						"	move		%a6, %d0				\n\t"
						"	cmpi.l		#150, %d0				\n\t"
						"	bne			reg_test_2_error		\n\t"
						"	movel		ulRegTest1Counter, %d0	\n\t"
						"	addql		#1, %d0					\n\t"
						"	movel		%d0, ulRegTest2Counter	\n\t"
						"	bra			reg_test_2_start		\n\t"
						"reg_test_2_error:						\n\t"
						"	bra			reg_test_2_error		\n\t"
					);
}
/*-----------------------------------------------------------*/

