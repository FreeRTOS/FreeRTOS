/*
 * FreeRTOS V202012.00
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 * main_full() creates a set of demo application tasks and software timers, then
 * starts the scheduler.  The web documentation provides more details of the
 * standard demo application tasks, which provide no particular functionality,
 * but do provide a good example of how to use the FreeRTOS API.
 *
 * In addition to the standard demo tasks, the following tasks and tests are
 * defined and/or created within this file:
 *
 * "FreeRTOS+CLI command console" -  The command console uses SCI1 for its
 * input and output.  The baud rate is set to 19200.  Type "help" to see a list
 * of registered commands.  The FreeRTOS+CLI license is different to the
 * FreeRTOS license, see http://www.FreeRTOS.org/cli for license and usage
 * details.
 *
 * "Reg test" tasks - These fill both the core and floating point registers with
 * known values, then check that each register maintains its expected value for
 * the lifetime of the task.  Each task uses a different set of values.  The reg
 * test tasks execute with a very low priority, so get preempted very
 * frequently.  A register containing an unexpected value is indicative of an
 * error in the context switching mechanism.
 *
 * "Check" task - The check task period is initially set to three seconds.  The
 * task checks that all the standard demo tasks are not only still executing,
 * but are executing without reporting any errors.  If the check task discovers
 * that a task has either stalled, or reported an error, then it changes its own
 * execution period from the initial three seconds, to just 200ms.  The check
 * task also toggles an LED on each iteration of its loop.  This provides a
 * visual indication of the system status:  If the LED toggles every three
 * seconds, then no issues have been discovered.  If the LED toggles every
 * 200ms, then an issue has been discovered with at least one task.
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

/* Renesas includes. */
#include <rskrx71mdef.h>
#include "r_cg_macrodriver.h"
#include "r_cg_userdefine.h"

/* Priorities for the demo application tasks. */
#define mainSEM_TEST_PRIORITY				( tskIDLE_PRIORITY + 1UL )
#define mainBLOCK_Q_PRIORITY				( tskIDLE_PRIORITY + 2UL )
#define mainCREATOR_TASK_PRIORITY			( tskIDLE_PRIORITY + 3UL )
#define mainFLOP_TASK_PRIORITY				( tskIDLE_PRIORITY )
#define mainUART_COMMAND_CONSOLE_STACK_SIZE	( configMINIMAL_STACK_SIZE * 3UL )
#define mainCHECK_TASK_PRIORITY				( configMAX_PRIORITIES - 1 )
#define mainQUEUE_OVERWRITE_PRIORITY		( tskIDLE_PRIORITY )

/* The priority used by the UART command console task. */
#define mainUART_COMMAND_CONSOLE_TASK_PRIORITY	( configMAX_PRIORITIES - 2 )

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
#define mainREG_TEST_1_PARAMETER			( ( void * ) 0x12121212UL )
#define mainREG_TEST_2_PARAMETER			( ( void * ) 0x12345678UL )

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
void vRegTest1Implementation( void );
void vRegTest2Implementation( void );

/*
 * A high priority task that does nothing other than execute at a pseudo random
 * time to ensure the other test tasks don't just execute in a repeating
 * pattern.
 */
static void prvPseudoRandomiser( void *pvParameters );

/*
 * Register commands that can be used with FreeRTOS+CLI.  The commands are
 * defined in CLI-Commands.c and File-Related-CLI-Command.c respectively.
 */
extern void vRegisterSampleCLICommands( void );

/*
 * The task that manages the FreeRTOS+CLI input and output.
 */
extern void vUARTCommandConsoleStart( uint16_t usStackSize, UBaseType_t uxPriority );

/*-----------------------------------------------------------*/

/* The following two variables are used to communicate the status of the
register check tasks to the check task.  If the variables keep incrementing,
then the register check tasks have not discovered any errors.  If a variable
stops incrementing, then an error has been found. */
volatile unsigned long ulRegTest1LoopCounter = 0UL, ulRegTest2LoopCounter = 0UL;

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
	xTaskCreate( prvPseudoRandomiser, "Rnd", configMINIMAL_STACK_SIZE, NULL, configMAX_PRIORITIES - 2, NULL );

	/* Start the tasks that implements the command console on the UART, as
	described above. */
	vUARTCommandConsoleStart( mainUART_COMMAND_CONSOLE_STACK_SIZE, mainUART_COMMAND_CONSOLE_TASK_PRIORITY );

	/* Register the standard CLI commands. */
	vRegisterSampleCLICommands();

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
		LED0 = !LED0;

		if( ulErrorFound != pdFALSE )
		{
			/* An error has been detected in one of the tasks - flash the LED
			at a higher frequency to give visible feedback that something has
			gone wrong (it might just be that the loop back connector required
			by the comtest tasks has not been fitted). */
			xDelayPeriod = mainERROR_CHECK_TASK_PERIOD;
		}
	}
}
/*-----------------------------------------------------------*/

static void prvPseudoRandomiser( void *pvParameters )
{
const uint32_t ulMultiplier = 0x015a4e35UL, ulIncrement = 1UL, ulMinDelay = pdMS_TO_TICKS( 35 );
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
			__asm volatile( "NOP" );
			__asm volatile( "NOP" );
			__asm volatile( "NOP" );
			__asm volatile( "NOP" );
			__asm volatile( "NOP" );
			__asm volatile( "NOP" );
			__asm volatile( "NOP" );

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
	vRegTest1Implementation();
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
	vRegTest2Implementation();
}
/*-----------------------------------------------------------*/

