/*
    FreeRTOS V9.0.1 - Copyright (C) 2017 Real Time Engineers Ltd.
    All rights reserved

    VISIT http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation >>>> AND MODIFIED BY <<<< the FreeRTOS exception.

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
 * NOTE 1:  This project provides two demo applications.  A simple blinky style
 * project that demonstrates the tickless low power features of FreeRTOS, and a
 * more comprehensive test and demo application.  The configCREATE_LOW_POWER_DEMO
 * setting in FreeRTOSConifg.h is used to select between the two, and to select
 * the clock used when tickless mode is used.  See the notes on using
 * conifgCREATE_LOW_POWER_DEMO in main.c.  This file implements the
 * comprehensive test and demo version.
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

/* SiLabs includes. */
#include "bsp.h"

/* Standard demo application includes. */
#include "flop.h"
#include "semtest.h"
#include "dynamic.h"
#include "blocktim.h"
#include "GenQTest.h"
#include "recmutex.h"
#include "TimerDemo.h"
#include "EventGroupsDemo.h"
#include "TaskNotify.h"
#include "StaticAllocation.h"

/* Priorities for the demo application tasks. */
#define mainSEM_TEST_PRIORITY				( tskIDLE_PRIORITY + 1UL )
#define mainCREATOR_TASK_PRIORITY			( tskIDLE_PRIORITY + 3UL )
#define mainFLOP_TASK_PRIORITY				( tskIDLE_PRIORITY )
#define mainCHECK_TASK_PRIORITY				( configMAX_PRIORITIES - 1 )

/* A block time of zero simply means "don't block". */
#define mainDONT_BLOCK						( 0UL )

/* The period of the check task, in ms, provided no errors have been reported by
any of the standard demo tasks.  ms are converted to the equivalent in ticks
using the portTICK_PERIOD_MS constant. */
#define mainNO_ERROR_CHECK_TASK_PERIOD		pdMS_TO_TICKS( 3000UL )

/* The period of the check task, in ms, if an error has been reported in one of
the standard demo tasks.  ms are converted to the equivalent in ticks using the
portTICK_PERIOD_MS constant. */
#define mainERROR_CHECK_TASK_PERIOD 		pdMS_TO_TICKS( 200UL )

/* Parameters that are passed into the register check tasks solely for the
purpose of ensuring parameters are passed into tasks correctly. */
#define mainREG_TEST_TASK_1_PARAMETER		( ( void * ) 0x12345678 )
#define mainREG_TEST_TASK_2_PARAMETER		( ( void * ) 0x87654321 )

/* The base period used by the timer test tasks. */
#define mainTIMER_TEST_PERIOD				( 50 )

/* The LED toggled by the check task. */
#define mainTASK_LED						( 0 )

/*-----------------------------------------------------------*/

/*
 * Called by main() to run the full demo (as opposed to the blinky demo) when
 * mainCREATE_LOW_POWER_DEMO is set to 0.
 */
void main_full( void );

/*
 * The check task, as described at the top of this file.
 */
static void prvCheckTask( void *pvParameters );

/*
 * Some of the tests and demo tasks executed by the full demo include
 * interaction from an interrupt - for which the tick interrupt is used via the
 * tick hook function.
 */
void vFullDemoTickHook( void );

/*
 * Register check tasks, and the tasks used to write over and check the contents
 * of the FPU registers, as described at the top of this file.  The nature of
 * these files necessitates that they are written in an assembly file, but the
 * entry points are kept in the C file for the convenience of checking the task
 * parameter.
 */
static void prvRegTestTaskEntry1( void *pvParameters );
extern void vRegTest1Implementation( void );
static void prvRegTestTaskEntry2( void *pvParameters );
extern void vRegTest2Implementation( void );

/*-----------------------------------------------------------*/

/* The following two variables are used to communicate the status of the
register check tasks to the check task.  If the variables keep incrementing,
then the register check tasks have not discovered any errors.  If a variable
stops incrementing, then an error has been found. */
volatile unsigned long ulRegTest1LoopCounter = 0UL, ulRegTest2LoopCounter = 0UL;

/* The variable incremented in lieu of having a proper LED outout. */
extern volatile uint32_t ulLED;

/*-----------------------------------------------------------*/

void main_full( void )
{
	/* Start all the other standard demo/test tasks.  They have no particular
	functionality, but do demonstrate how to use the FreeRTOS API and test the
	kernel port. */
	vStartDynamicPriorityTasks();
	vCreateBlockTimeTasks();
	vStartGenericQueueTasks( tskIDLE_PRIORITY );
	vStartRecursiveMutexTasks();
	vStartSemaphoreTasks( mainSEM_TEST_PRIORITY );
	vStartMathTasks( mainFLOP_TASK_PRIORITY );
	vStartTimerDemoTask( mainTIMER_TEST_PERIOD );
	vStartEventGroupTasks();
	vStartTaskNotifyTask();
	vStartStaticallyAllocatedTasks();

	/* Create the register check tasks, as described at the top of this	file */
	xTaskCreate( prvRegTestTaskEntry1, "Reg1", configMINIMAL_STACK_SIZE, mainREG_TEST_TASK_1_PARAMETER, tskIDLE_PRIORITY, NULL );
	xTaskCreate( prvRegTestTaskEntry2, "Reg2", configMINIMAL_STACK_SIZE, mainREG_TEST_TASK_2_PARAMETER, tskIDLE_PRIORITY, NULL );

	/* Create the task that performs the 'check' functionality,	as described at
	the top of this file. */
	xTaskCreate( prvCheckTask, "Check", configMINIMAL_STACK_SIZE, NULL, mainCHECK_TASK_PRIORITY, NULL );

	/* Start the scheduler. */
	vTaskStartScheduler();

	/* If all is well, the scheduler will now be running, and the following
	line will never be reached.  If the following line does execute, then
	there was insufficient FreeRTOS heap memory available for the Idle and/or
	timer tasks to be created.  See the memory management section on the
	FreeRTOS web site for more details on the FreeRTOS heap
	http://www.freertos.org/a00111.html. */
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
		if( xAreMathsTaskStillRunning() != pdTRUE )
		{
			ulErrorFound = 1UL << 1UL;
		}

		if( xAreDynamicPriorityTasksStillRunning() != pdTRUE )
		{
			ulErrorFound = 1UL << 2UL;
		}

		if( xAreStaticAllocationTasksStillRunning() != pdPASS )
		{
			ulErrorFound = 1UL << 3UL;
		}

		if ( xAreBlockTimeTestTasksStillRunning() != pdTRUE )
		{
			ulErrorFound = 1UL << 4UL;
		}

		if ( xAreGenericQueueTasksStillRunning() != pdTRUE )
		{
			ulErrorFound = 1UL << 5UL;
		}

		if ( xAreRecursiveMutexTasksStillRunning() != pdTRUE )
		{
			ulErrorFound = 1UL << 6UL;
		}

		if( xAreSemaphoreTasksStillRunning() != pdTRUE )
		{
			ulErrorFound = 1UL << 8UL;
		}

		if( xAreTimerDemoTasksStillRunning( ( TickType_t ) xDelayPeriod ) != pdPASS )
		{
			ulErrorFound = 1UL << 9UL;
		}

		if( xAreEventGroupTasksStillRunning() != pdPASS )
		{
			ulErrorFound = 1UL << 12UL;
		}

		if( xAreTaskNotificationTasksStillRunning() != pdPASS )
		{
			ulErrorFound = 1UL << 14UL;
		}

		/* Check that the register test 1 task is still running. */
		if( ulLastRegTest1Value == ulRegTest1LoopCounter )
		{
			ulErrorFound = 1UL << 15UL;
		}
		ulLastRegTest1Value = ulRegTest1LoopCounter;

		/* Check that the register test 2 task is still running. */
		if( ulLastRegTest2Value == ulRegTest2LoopCounter )
		{
			ulErrorFound = 1UL << 16UL;
		}
		ulLastRegTest2Value = ulRegTest2LoopCounter;

		/* Toggle the check LED to give an indication of the system status.  If
		the LED toggles every mainNO_ERROR_CHECK_TASK_PERIOD milliseconds then
		everything is ok.  A faster toggle indicates an error. */
		BSP_LedToggle( mainTASK_LED );

		if( ulErrorFound != pdFALSE )
		{
			/* An error has been detected in one of the tasks - flash the LED
			at a higher frequency to give visible feedback that something has
			gone wrong. */
			xDelayPeriod = mainERROR_CHECK_TASK_PERIOD;
		}

		configASSERT( ulErrorFound == pdFALSE );
	}
}
/*-----------------------------------------------------------*/

static void prvRegTestTaskEntry1( void *pvParameters )
{
	/* Although the regtest task is written in assembler, its entry point is
	written in C for convenience of checking the task parameter is being passed
	in correctly. */
	if( pvParameters == mainREG_TEST_TASK_1_PARAMETER )
	{
		/* Start the part of the test that is written in assembler. */
		vRegTest1Implementation();
	}

	/* The following line will only execute if the task parameter is found to
	be incorrect.  The check task will detect that the regtest loop counter is
	not being incremented and flag an error. */
	vTaskDelete( NULL );
}
/*-----------------------------------------------------------*/

static void prvRegTestTaskEntry2( void *pvParameters )
{
	/* Although the regtest task is written in assembler, its entry point is
	written in C for convenience of checking the task parameter is being passed
	in correctly. */
	if( pvParameters == mainREG_TEST_TASK_2_PARAMETER )
	{
		/* Start the part of the test that is written in assembler. */
		vRegTest2Implementation();
	}

	/* The following line will only execute if the task parameter is found to
	be incorrect.  The check task will detect that the regtest loop counter is
	not being incremented and flag an error. */
	vTaskDelete( NULL );
}
/*-----------------------------------------------------------*/

void vFullDemoTickHook( void )
{
	/* Some of the tests and demo tasks executed by the full demo include
	interaction from an interrupt - for which the tick interrupt is used via
	the tick hook function. */

	/* The full demo includes a software timer demo/test that requires
	prodding periodically from the tick interrupt. */
	vTimerPeriodicISRTests();

	/* Call the periodic event group from ISR demo. */
	vPeriodicEventGroupsProcessing();

	/* Call the code that 'gives' a task notification from an ISR. */
	xNotifyTaskFromISR();
}






