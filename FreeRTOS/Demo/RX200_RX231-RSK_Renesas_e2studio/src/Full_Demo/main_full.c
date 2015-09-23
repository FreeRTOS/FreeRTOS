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

/******************************************************************************
 * NOTE 1:  This project provides two demo applications.  A simple blinky
 * style project, and a more comprehensive test and demo application.  The
 * mainCREATE_SIMPLE_BLINKY_DEMO_ONLY setting in main.c is used to
 * select between the two.  See the notes on using
 * mainCREATE_SIMPLE_BLINKY_DEMO_ONLY in main.c.  This file implements the
 * comprehensive version.
 *
 * NOTE 2:  This file only contains the source code that is specific to the
 * full demo.  Generic functions, such FreeRTOS hook functions, and functions
 * required to configure the hardware, are defined in main.c.
 *
 ******************************************************************************
 *
 * main_full() creates all the demo application tasks and software timers, then
 * starts the scheduler.  The web documentation provides more details of the
 * standard demo application tasks, which provide no particular functionality,
 * but do provide a good example of how to use the FreeRTOS API.
 *
 * In addition to the standard demo tasks, the following tasks and tests are
 * defined and/or created within this file:
 *
 * "Reg test" tasks - These fill both the core and floating point registers with
 * known values, then check that each register maintains its expected value for
 * the lifetime of the task.  Each task uses a different set of values.  The reg
 * test tasks execute with a very low priority, so get preempted very
 * frequently.  A register containing an unexpected value is indicative of an
 * error in the context switching mechanism.
 *
 * "Check" task - The check task period is initially set to three seconds.  The
 * task checks that all the standard demo tasks, and the register check tasks,
 * are not only still executing, but are executing without reporting any errors.
 * If the check task discovers that a task has either stalled, or reported an
 * error, then it changes its own execution period from the initial three
 * seconds, to just 200ms.  The check task also toggles an LED each time it is
 * called.  This provides a visual indication of the system status:  If the LED
 * toggles every three seconds, then no issues have been discovered.  If the LED
 * toggles every 200ms, then an issue has been discovered with at least one
 * task.
 */

/* Standard includes. */
#include <stdio.h>

/* Kernel includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "timers.h"
#include "semphr.h"

/* Standard demo application includes. */
#include "flop.h"
#include "semtest.h"
#include "dynamic.h"
#include "BlockQ.h"
#include "blocktim.h"
#include "countsem.h"
#include "GenQTest.h"
#include "recmutex.h"
#include "death.h"
#include "partest.h"
#include "comtest2.h"
#include "serial.h"
#include "TimerDemo.h"
#include "QueueOverwrite.h"
#include "IntQueue.h"
#include "EventGroupsDemo.h"
#include "TaskNotify.h"
#include "IntSemTest.h"

/* Priorities for the demo application tasks. */
#define mainSEM_TEST_PRIORITY				( tskIDLE_PRIORITY + 1UL )
#define mainBLOCK_Q_PRIORITY				( tskIDLE_PRIORITY + 2UL )
#define mainCREATOR_TASK_PRIORITY			( tskIDLE_PRIORITY + 3UL )
#define mainFLOP_TASK_PRIORITY				( tskIDLE_PRIORITY )
#define mainUART_COMMAND_CONSOLE_STACK_SIZE	( configMINIMAL_STACK_SIZE * 3UL )
#define mainCOM_TEST_TASK_PRIORITY			( tskIDLE_PRIORITY + 2 )
#define mainCHECK_TASK_PRIORITY				( configMAX_PRIORITIES - 1 )
#define mainQUEUE_OVERWRITE_PRIORITY		( tskIDLE_PRIORITY )

/* The priority used by the UART command console task. */
#define mainUART_COMMAND_CONSOLE_TASK_PRIORITY	( configMAX_PRIORITIES - 2 )

/* A block time of zero simply means "don't block". */
#define mainDONT_BLOCK						( 0UL )

/* The period after which the check timer will expire, in ms, provided no errors
have been reported by any of the standard demo tasks.  ms are converted to the
equivalent in ticks using the portTICK_PERIOD_MS constant. */
#define mainNO_ERROR_CHECK_TASK_PERIOD		( 3000UL / portTICK_PERIOD_MS )

/* The period at which the check timer will expire, in ms, if an error has been
reported in one of the standard demo tasks.  ms are converted to the equivalent
in ticks using the portTICK_PERIOD_MS constant. */
#define mainERROR_CHECK_TASK_PERIOD 		( 200UL / portTICK_PERIOD_MS )

/* Parameters that are passed into the register check tasks solely for the
purpose of ensuring parameters are passed into tasks correctly. */
#define mainREG_TEST_1_PARAMETER	( ( void * ) 0x12121212UL )
#define mainREG_TEST_2_PARAMETER	( ( void * ) 0x12345678UL )

/* The base period used by the timer test tasks. */
#define mainTIMER_TEST_PERIOD				( 50 )

/*-----------------------------------------------------------*/

/*
 * Entry point for the comprehensive demo (as opposed to the simple blinky
 * demo).
 */
void main_full( void );

/*
 * The full demo includes some functionality called from the tick hook.
 */
void vFullDemoTickHook( void );

 /*
 * The check task, as described at the top of this file.
 */
static void prvCheckTask( void *pvParameters );

/*
 * Register check tasks, and the tasks used to write over and check the contents
 * of the registers, as described at the top of this file.  The nature of these
 * files necessitates that they are written in assembly, but the entry points
 * are kept in the C file for the convenience of checking the task parameter.
 */
static void prvRegTest1Task( void *pvParameters );
static void prvRegTest2Task( void *pvParameters );
static void prvRegTest1Implementation( void );
static void prvRegTest2Implementation( void );

/*
 * A high priority task that does nothing other than execute at a pseudo random
 * time to ensure the other test tasks don't just execute in a repeating
 * pattern.
 */
static void prvPseudoRandomiser( void *pvParameters );

/*-----------------------------------------------------------*/

/* The following two variables are used to communicate the status of the
register check tasks to the check task.  If the variables keep incrementing,
then the register check tasks have not discovered any errors.  If a variable
stops incrementing, then an error has been found. */
volatile unsigned long ulRegTest1LoopCounter = 0UL, ulRegTest2LoopCounter = 0UL;

/* String for display in the web server.  It is set to an error message if the
check task detects an error.  */
const char *pcStatusMessage = "All tasks running without error";
/*-----------------------------------------------------------*/

void main_full( void )
{
	/* Start all the other standard demo/test tasks.  They have no particular
	functionality, but do demonstrate how to use the FreeRTOS API and test the
	kernel port. */
	vStartInterruptQueueTasks();
	vStartDynamicPriorityTasks();
	vStartBlockingQueueTasks( mainBLOCK_Q_PRIORITY );
	vCreateBlockTimeTasks();
	vStartCountingSemaphoreTasks();
	vStartGenericQueueTasks( tskIDLE_PRIORITY );
	vStartRecursiveMutexTasks();
	vStartSemaphoreTasks( mainSEM_TEST_PRIORITY );
	vStartMathTasks( mainFLOP_TASK_PRIORITY );
	vStartTimerDemoTask( mainTIMER_TEST_PERIOD );
	vStartQueueOverwriteTask( mainQUEUE_OVERWRITE_PRIORITY );
	vStartEventGroupTasks();
	vStartTaskNotifyTask();
	vStartInterruptSemaphoreTasks();

	/* Create the register check tasks, as described at the top of this	file */
	xTaskCreate( prvRegTest1Task, "RegTst1", configMINIMAL_STACK_SIZE, mainREG_TEST_1_PARAMETER, tskIDLE_PRIORITY, NULL );
	xTaskCreate( prvRegTest2Task, "RegTst2", configMINIMAL_STACK_SIZE, mainREG_TEST_2_PARAMETER, tskIDLE_PRIORITY, NULL );

	/* Create the task that just adds a little random behaviour. */
	xTaskCreate( prvPseudoRandomiser, "Rnd", configMINIMAL_STACK_SIZE, NULL, configMAX_PRIORITIES - 1, NULL );

	/* Create the task that performs the 'check' functionality,	as described at
	the top of this file. */
	xTaskCreate( prvCheckTask, "Check", configMINIMAL_STACK_SIZE, NULL, mainCHECK_TASK_PRIORITY, NULL );

	/* The set of tasks created by the following function call have to be
	created last as they keep account of the number of tasks they expect to see
	running. */
	vCreateSuicidalTasks( mainCREATOR_TASK_PRIORITY );

	/* Start the scheduler. */
	vTaskStartScheduler();

	/* If all is well, the scheduler will now be running, and the following
	line will never be reached.  If the following line does execute, then
	there was either insufficient FreeRTOS heap memory available for the idle
	and/or timer tasks to be created, or vTaskStartScheduler() was called from
	User mode.  See the memory management section on the FreeRTOS web site for
	more details on the FreeRTOS heap http://www.freertos.org/a00111.html.  The
	mode from which main() is called is set in the C start up code and must be
	a privileged mode (not user mode). */
	for( ;; );
}
/*-----------------------------------------------------------*/

static void prvCheckTask( void *pvParameters )
{
TickType_t xDelayPeriod = mainNO_ERROR_CHECK_TASK_PERIOD;
TickType_t xLastExecutionTime;
static unsigned long ulLastRegTest1Value = 0, ulLastRegTest2Value = 0;
unsigned long ulErrorFound = pdFALSE;

	/* Just to stop compiler warnings. */
	( void ) pvParameters;

	/* Initialise xLastExecutionTime so the first call to vTaskDelayUntil()
	works correctly. */
	xLastExecutionTime = xTaskGetTickCount();

	/* Cycle for ever, delaying then checking all the other tasks are still
	operating without error.  The onboard LED is toggled on each iteration.
	If an error is detected then the delay period is decreased from
	mainNO_ERROR_CHECK_TASK_PERIOD to mainERROR_CHECK_TASK_PERIOD.  This has the
	effect of increasing the rate at which the onboard LED toggles, and in so
	doing gives visual feedback of the system status. */
	for( ;; )
	{
		/* Delay until it is time to execute again. */
		vTaskDelayUntil( &xLastExecutionTime, xDelayPeriod );

		/* Check all the demo tasks (other than the flash tasks) to ensure
		that they are all still running, and that none have detected an error. */
		if( xAreIntQueueTasksStillRunning() != pdTRUE )
		{
			ulErrorFound |= 1UL << 0UL;
		}

		if( xAreMathsTaskStillRunning() != pdTRUE )
		{
			ulErrorFound |= 1UL << 1UL;
		}

		if( xAreDynamicPriorityTasksStillRunning() != pdTRUE )
		{
			ulErrorFound |= 1UL << 2UL;
		}

		if( xAreBlockingQueuesStillRunning() != pdTRUE )
		{
			ulErrorFound |= 1UL << 3UL;
		}

		if ( xAreBlockTimeTestTasksStillRunning() != pdTRUE )
		{
			ulErrorFound |= 1UL << 4UL;
		}

		if ( xAreGenericQueueTasksStillRunning() != pdTRUE )
		{
			ulErrorFound |= 1UL << 5UL;
		}

		if ( xAreRecursiveMutexTasksStillRunning() != pdTRUE )
		{
			ulErrorFound |= 1UL << 6UL;
		}

		if( xIsCreateTaskStillRunning() != pdTRUE )
		{
			ulErrorFound |= 1UL << 7UL;
		}

		if( xAreSemaphoreTasksStillRunning() != pdTRUE )
		{
			ulErrorFound |= 1UL << 8UL;
		}

		if( xAreTimerDemoTasksStillRunning( ( TickType_t ) mainNO_ERROR_CHECK_TASK_PERIOD ) != pdPASS )
		{
			ulErrorFound |= 1UL << 9UL;
		}

		if( xAreCountingSemaphoreTasksStillRunning() != pdTRUE )
		{
			ulErrorFound |= 1UL << 10UL;
		}

		if( xIsQueueOverwriteTaskStillRunning() != pdPASS )
		{
			ulErrorFound |= 1UL << 11UL;
		}

		if( xAreEventGroupTasksStillRunning() != pdPASS )
		{
			ulErrorFound |= 1UL << 12UL;
		}

		if( xAreTaskNotificationTasksStillRunning() != pdTRUE )
		{
			ulErrorFound |= 1UL << 13UL;
		}

		if( xAreInterruptSemaphoreTasksStillRunning() != pdTRUE )
		{
			ulErrorFound |= 1UL << 14UL;
		}

		/* Check that the register test 1 task is still running. */
		if( ulLastRegTest1Value == ulRegTest1LoopCounter )
		{
			ulErrorFound |= 1UL << 15UL;
		}
		ulLastRegTest1Value = ulRegTest1LoopCounter;

		/* Check that the register test 2 task is still running. */
		if( ulLastRegTest2Value == ulRegTest2LoopCounter )
		{
			ulErrorFound |= 1UL << 16UL;
		}
		ulLastRegTest2Value = ulRegTest2LoopCounter;

		/* Toggle the check LED to give an indication of the system status.  If
		the LED toggles every mainNO_ERROR_CHECK_TASK_PERIOD milliseconds then
		everything is ok.  A faster toggle indicates an error. */
//_RB_		LED0 = !LED0;

		if( ulErrorFound != pdFALSE )
		{
			/* An error has been detected in one of the tasks - flash the LED
			at a higher frequency to give visible feedback that something has
			gone wrong (it might just be that the loop back connector required
			by the comtest tasks has not been fitted). */
			xDelayPeriod = mainERROR_CHECK_TASK_PERIOD;
			pcStatusMessage = "Error found in at least one task.";
		}
	}
}
/*-----------------------------------------------------------*/

static void prvPseudoRandomiser( void *pvParameters )
{
const uint32_t ulMultiplier = 0x015a4e35UL, ulIncrement = 1UL, ulMinDelay = ( 35 / portTICK_PERIOD_MS );
volatile uint32_t ulNextRand = ( uint32_t ) &pvParameters, ulValue;

	/* This task does nothing other than ensure there is a little bit of
	disruption in the scheduling pattern of the other tasks.  Normally this is
	done by generating interrupts at pseudo random times. */
	for( ;; )
	{
		ulNextRand = ( ulMultiplier * ulNextRand ) + ulIncrement;
		ulValue = ( ulNextRand >> 16UL ) & 0xffUL;

		if( ulValue < ulMinDelay )
		{
			ulValue = ulMinDelay;
		}

		vTaskDelay( ulValue );

		while( ulValue > 0 )
		{
			nop();
			nop();
			nop();
			nop();
			nop();
			nop();
			nop();
			nop();

			ulValue--;
		}
	}
}
/*-----------------------------------------------------------*/

void vFullDemoTickHook( void )
{
	/* The full demo includes a software timer demo/test that requires
	prodding periodically from the tick interrupt. */
	vTimerPeriodicISRTests();

	/* Call the periodic queue overwrite from ISR demo. */
	vQueueOverwritePeriodicISRDemo();

	/* Call the periodic event group from ISR demo. */
	vPeriodicEventGroupsProcessing();

	/* Use task notifications from an interrupt. */
	xNotifyTaskFromISR();

	/* Use mutexes from interrupts. */
	vInterruptSemaphorePeriodicTest();
}
/*-----------------------------------------------------------*/

/* This function is explained in the comments at the top of this file. */
static void prvRegTest1Task( void *pvParameters )
{
	if( pvParameters != mainREG_TEST_1_PARAMETER )
	{
		/* The parameter did not contain the expected value. */
		for( ;; )
		{
			/* Stop the tick interrupt so its obvious something has gone wrong. */
			taskDISABLE_INTERRUPTS();
		}
	}

	/* This is an inline asm function that never returns. */
	prvRegTest1Implementation();
}
/*-----------------------------------------------------------*/

/* This function is explained in the comments at the top of this file. */
static void prvRegTest2Task( void *pvParameters )
{
	if( pvParameters != mainREG_TEST_2_PARAMETER )
	{
		/* The parameter did not contain the expected value. */
		for( ;; )
		{
			/* Stop the tick interrupt so its obvious something has gone wrong. */
			taskDISABLE_INTERRUPTS();
		}
	}

	/* This is an inline asm function that never returns. */
	prvRegTest2Implementation();
}
/*-----------------------------------------------------------*/

/* This function is explained in the comments at the top of this file. */
#pragma inline_asm prvRegTest1Implementation
static void prvRegTest1Implementation( void )
{
	; Put a known value in each register.
	MOV.L	#1, R1
	MOV.L	#2, R2
	MOV.L	#3, R3
	MOV.L	#4, R4
	MOV.L	#5, R5
	MOV.L	#6, R6
	MOV.L	#7, R7
	MOV.L	#8, R8
	MOV.L	#9, R9
	MOV.L	#10, R10
	MOV.L	#11, R11
	MOV.L	#12, R12
	MOV.L	#13, R13
	MOV.L	#14, R14
	MOV.L	#15, R15

	; Loop, checking each itteration that each register still contains the
	; expected value.
TestLoop1:

	; Push the registers that are going to get clobbered.
	PUSHM	R14-R15

	; Increment the loop counter to show this task is still getting CPU time.
	MOV.L	#_ulRegTest1LoopCounter, R14
	MOV.L	[ R14 ], R15
	ADD		#1, R15
	MOV.L	R15, [ R14 ]

	; Yield to extend the text coverage.  Set the bit in the ITU SWINTR register.
	MOV.L	#1, R14
	MOV.L 	#0872E0H, R15
	MOV.B	R14, [R15]
	NOP
	NOP

	; Restore the clobbered registers.
	POPM	R14-R15

	; Now compare each register to ensure it still contains the value that was
	; set before this loop was entered.
	CMP		#1, R1
	BNE		RegTest1Error
	CMP		#2, R2
	BNE		RegTest1Error
	CMP		#3, R3
	BNE		RegTest1Error
	CMP		#4, R4
	BNE		RegTest1Error
	CMP		#5, R5
	BNE		RegTest1Error
	CMP		#6, R6
	BNE		RegTest1Error
	CMP		#7, R7
	BNE		RegTest1Error
	CMP		#8, R8
	BNE		RegTest1Error
	CMP		#9, R9
	BNE		RegTest1Error
	CMP		#10, R10
	BNE		RegTest1Error
	CMP		#11, R11
	BNE		RegTest1Error
	CMP		#12, R12
	BNE		RegTest1Error
	CMP		#13, R13
	BNE		RegTest1Error
	CMP		#14, R14
	BNE		RegTest1Error
	CMP		#15, R15
	BNE		RegTest1Error

	; All comparisons passed, start a new itteratio of this loop.
	BRA		TestLoop1

RegTest1Error:
	; A compare failed, just loop here so the loop counter stops incrementing
	; causing the check task to indicate the error.
	BRA RegTest1Error
}
/*-----------------------------------------------------------*/

/* This function is explained in the comments at the top of this file. */
#pragma inline_asm prvRegTest2Implementation
static void prvRegTest2Implementation( void )
{
	; Put a known value in each register.
	MOV.L	#10, R1
	MOV.L	#20, R2
	MOV.L	#30, R3
	MOV.L	#40, R4
	MOV.L	#50, R5
	MOV.L	#60, R6
	MOV.L	#70, R7
	MOV.L	#80, R8
	MOV.L	#90, R9
	MOV.L	#100, R10
	MOV.L	#110, R11
	MOV.L	#120, R12
	MOV.L	#130, R13
	MOV.L	#140, R14
	MOV.L	#150, R15

	; Loop, checking on each itteration that each register still contains the
	; expected value.
TestLoop2:

	; Push the registers that are going to get clobbered.
	PUSHM	R14-R15

	; Increment the loop counter to show this task is still getting CPU time.
	MOV.L	#_ulRegTest2LoopCounter, R14
	MOV.L	[ R14 ], R15
	ADD		#1, R15
	MOV.L	R15, [ R14 ]

	; Restore the clobbered registers.
	POPM	R14-R15

	CMP		#10, R1
	BNE		RegTest2Error
	CMP		#20, R2
	BNE		RegTest2Error
	CMP		#30, R3
	BNE		RegTest2Error
	CMP		#40, R4
	BNE		RegTest2Error
	CMP		#50, R5
	BNE		RegTest2Error
	CMP		#60, R6
	BNE		RegTest2Error
	CMP		#70, R7
	BNE		RegTest2Error
	CMP		#80, R8
	BNE		RegTest2Error
	CMP		#90, R9
	BNE		RegTest2Error
	CMP		#100, R10
	BNE		RegTest2Error
	CMP		#110, R11
	BNE		RegTest2Error
	CMP		#120, R12
	BNE		RegTest2Error
	CMP		#130, R13
	BNE		RegTest2Error
	CMP		#140, R14
	BNE		RegTest2Error
	CMP		#150, R15
	BNE		RegTest2Error

	; All comparisons passed, start a new itteratio of this loop.
	BRA		TestLoop2

RegTest2Error:
	; A compare failed, just loop here so the loop counter stops incrementing
	; - causing the check task to indicate the error.
	BRA RegTest2Error
}
/*-----------------------------------------------------------*/




