/*
 * FreeRTOS Kernel V10.3.0
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
 * NOTE 1:  This project provides two demo applications.  A simple blinky style
 * project, and a more comprehensive test and demo application.  The
 * mainCREATE_SIMPLE_BLINKY_DEMO_ONLY setting in main.c is used to select
 * between the two.  See the notes on using mainCREATE_SIMPLE_BLINKY_DEMO_ONLY
 * in main.c.  This file implements the comprehensive test and demo version.
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
 * "Reg test" tasks - These fill both the core registers with known values, then
 * check that each register maintains its expected value for the lifetime of the
 * task.  Each task uses a different set of values.  The reg test tasks execute
 * with a very low priority, so get preempted very frequently.  A register
 * containing an unexpected value is indicative of an error in the context
 * switching mechanism.
 *
 * "Check" task - The check executes every three seconds.  It checks that all
 * the standard demo tasks, and the register check tasks, are not only still
 * executing, but are executing without reporting any errors.  If the check task
 * discovers that a task has either stalled, or reported an error, then it
 * prints an error message to the UART, otherwise it prints "Pass.".
 */

/* Standard includes. */
#include <stdio.h>
#include <string.h>

/* Kernel includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "timers.h"
#include "semphr.h"

/* Microsemi incldues. */
#include "core_timer.h"
#include "riscv_hal.h"

/* Standard demo application includes. */
#include "dynamic.h"
#include "blocktim.h"
#include "GenQTest.h"
#include "recmutex.h"
#include "TimerDemo.h"
#include "EventGroupsDemo.h"
#include "TaskNotify.h"
#include "AbortDelay.h"
#include "countsem.h"
#include "death.h"
#include "MessageBufferDemo.h"
#include "StreamBufferDemo.h"
#include "StreamBufferInterrupt.h"

/* Priorities for the demo application tasks. */
#define mainCHECK_TASK_PRIORITY				( configMAX_PRIORITIES - 1 )
#define mainCREATOR_TASK_PRIORITY			( tskIDLE_PRIORITY + 3UL )

/* The period of the check task, in ms, converted to ticks using the
pdMS_TO_TICKS() macro.  mainNO_ERROR_CHECK_TASK_PERIOD is used if no errors have
been found, mainERROR_CHECK_TASK_PERIOD is used if an error has been found. */
#define mainNO_ERROR_CHECK_TASK_PERIOD		pdMS_TO_TICKS( 3000UL )
#define mainERROR_CHECK_TASK_PERIOD		pdMS_TO_TICKS( 500UL )

/* Parameters that are passed into the register check tasks solely for the
purpose of ensuring parameters are passed into tasks correctly. */
#define mainREG_TEST_TASK_1_PARAMETER		( ( void * ) 0x12345678 )
#define mainREG_TEST_TASK_2_PARAMETER		( ( void * ) 0x87654321 )

/* The base period used by the timer test tasks. */
#define mainTIMER_TEST_PERIOD				( 50 )

/* The size of the stack allocated to the check task (as described in the
comments at the top of this file. */
#define mainCHECK_TASK_STACK_SIZE_WORDS 100

/* Size of the stacks to allocated for the register check tasks. */
#define mainREG_TEST_STACK_SIZE_WORDS 70

/*-----------------------------------------------------------*/

/*
 * Called by main() to run the full demo (as opposed to the blinky demo) when
 * mainCREATE_SIMPLE_BLINKY_DEMO_ONLY is set to 0.
 */
void main_full( void );

/*
 * The check task, as described at the top of this file.
 */
static void prvCheckTask( void *pvParameters );

/*
 * Initialise and start the peripheral timers that are used to exercise external
 * interrupt processing.
 */
static void prvSetupPeripheralTimers( void );

/*
 * Register check tasks as described at the top of this file.  The nature of
 * these files necessitates that they are written in an assembly file, but the
 * entry points are kept in the C file for the convenience of checking the task
 * parameter.
 */
static void prvRegTestTaskEntry1( void *pvParameters );
extern void vRegTest1Implementation( void );
static void prvRegTestTaskEntry2( void *pvParameters );
extern void vRegTest2Implementation( void );

/*
 * Tick hook used by the full demo, which includes code that interacts with
 * some of the tests.
 */
void vFullDemoTickHook( void );

/*-----------------------------------------------------------*/

/* Timers used to exercise external interrupt processing. */
static timer_instance_t g_timer0, g_timer1;

/* Variables incremented by the peripheral timers used to exercise external
interrupts. */
volatile uint32_t ulTimer0Interrupts = 0, ulTimer1Interrupts = 0;

/* The following two variables are used to communicate the status of the
register check tasks to the check task.  If the variables keep incrementing,
then the register check tasks have not discovered any errors.  If a variable
stops incrementing, then an error has been found. */
volatile uint32_t ulRegTest1LoopCounter = 0UL, ulRegTest2LoopCounter = 0UL;

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
	vStartTimerDemoTask( mainTIMER_TEST_PERIOD );
	vStartEventGroupTasks();
	vStartTaskNotifyTask();
	vCreateAbortDelayTasks();
	vStartCountingSemaphoreTasks();
	vStartMessageBufferTasks( configMINIMAL_STACK_SIZE  );
	vStartStreamBufferTasks();
	vStartStreamBufferInterruptDemo();

	/* Create the register check tasks, as described at the top of this	file.
	Use xTaskCreateStatic() to create a task using only statically allocated
	memory. */
	xTaskCreate( prvRegTestTaskEntry1, 			/* The function that implements the task. */
				 "Reg1", 						/* The name of the task. */
				 mainREG_TEST_STACK_SIZE_WORDS, /* Size of stack to allocate for the task - in words not bytes!. */
				 mainREG_TEST_TASK_1_PARAMETER, /* Parameter passed into the task. */
				 tskIDLE_PRIORITY, 				/* Priority of the task. */
				 NULL );						/* Can be used to pass out a handle to the created task. */
	xTaskCreate( prvRegTestTaskEntry2, "Reg2", mainREG_TEST_STACK_SIZE_WORDS, mainREG_TEST_TASK_2_PARAMETER, tskIDLE_PRIORITY, NULL );

	/* Create the task that performs the 'check' functionality,	as described at
	the top of this file. */
	xTaskCreate( prvCheckTask, "Check", mainCHECK_TASK_STACK_SIZE_WORDS, NULL, mainCHECK_TASK_PRIORITY, NULL );

	/* The set of tasks created by the following function call have to be
	created last as they keep account of the number of tasks they expect to see
	running. */
	vCreateSuicidalTasks( mainCREATOR_TASK_PRIORITY );

	/* Start the timers that are used to exercise external interrupt handling. */
	prvSetupPeripheralTimers();

	/* Start the scheduler. */
	vSendString( "Starting" );
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
uint32_t ulLastRegTest1Value = 0, ulLastRegTest2Value = 0;
uint32_t ulLastTimer0Interrupts = 0, ulLastTimer1Interrupts = 0;
char * const pcPassMessage = ".";
char * pcStatusMessage = pcPassMessage;
extern void vToggleLED( void );

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
		if( xAreDynamicPriorityTasksStillRunning() == pdFALSE )
		{
			pcStatusMessage = "ERROR: Dynamic priority demo/tests.\r\n";
		}

		if( xAreBlockTimeTestTasksStillRunning() == pdFALSE )
		{
			pcStatusMessage = "ERROR: Block time demo/tests.\r\n";
		}

		if( xAreGenericQueueTasksStillRunning() == pdFALSE )
		{
			pcStatusMessage = "ERROR: Generic queue demo/tests.\r\n";
		}

		if( xAreRecursiveMutexTasksStillRunning() == pdFALSE )
		{
			pcStatusMessage = "ERROR: Recursive mutex demo/tests.\r\n";
		}

		if( xAreTimerDemoTasksStillRunning( ( TickType_t ) xDelayPeriod ) == pdFALSE )
		{
			pcStatusMessage = "ERROR: Timer demo/tests.\r\n";
		}

		if( xAreEventGroupTasksStillRunning() == pdFALSE )
		{
			pcStatusMessage = "ERROR: Event group demo/tests.\r\n";
		}

		if( xAreTaskNotificationTasksStillRunning() == pdFALSE )
		{
			pcStatusMessage = "ERROR: Task notification demo/tests.\r\n";
		}

		if( xAreAbortDelayTestTasksStillRunning() == pdFALSE )
		{
			pcStatusMessage = "ERROR: Abort delay.\r\n";
		}

		if( xAreCountingSemaphoreTasksStillRunning() == pdFALSE )
		{
			pcStatusMessage = "ERROR: Counting semaphores.\r\n";
		}

		if( xIsCreateTaskStillRunning() == pdFALSE )
		{
			pcStatusMessage = "ERROR: Suicide tasks.\r\n";
		}

		if( xAreMessageBufferTasksStillRunning() == pdFALSE )
		{
			pcStatusMessage = "ERROR: Message buffer.\r\n";
		}

		if( xAreStreamBufferTasksStillRunning() == pdFALSE )
		{
			pcStatusMessage = "ERROR: Stream buffer.\r\n";
		}

		if( xIsInterruptStreamBufferDemoStillRunning() == pdFALSE )
		{
			pcStatusMessage = "ERROR: Stream buffer interrupt.\r\n";
		}

		/* Check that the register test 1 task is still running. */
		if( ulLastRegTest1Value == ulRegTest1LoopCounter )
		{
			pcStatusMessage = "ERROR: Register test 1.\r\n";
		}
		ulLastRegTest1Value = ulRegTest1LoopCounter;

		/* Check that the register test 2 task is still running. */
		if( ulLastRegTest2Value == ulRegTest2LoopCounter )
		{
			pcStatusMessage = "ERROR: Register test 2.\r\n";
		}
		ulLastRegTest2Value = ulRegTest2LoopCounter;

		/* Check interrupts from the peripheral timers are being handled. */
		if( ulLastTimer0Interrupts == ulTimer0Interrupts )
		{
			pcStatusMessage = "ERROR: Peripheral timer 0.\r\n";
		}
		ulLastTimer0Interrupts = ulTimer0Interrupts;

		if( ulLastTimer1Interrupts == ulTimer1Interrupts )
		{
			pcStatusMessage = "ERROR: Peripheral timer 1.\r\n";
		}
		ulLastTimer1Interrupts = ulTimer1Interrupts;

		/* Write the status message to the UART. */
		vSendString( pcStatusMessage );

		/* If an error has been found then increase the LED toggle rate by
		increasing the cycle frequency. */
		if( pcStatusMessage != pcPassMessage )
		{
			xDelayPeriod = mainERROR_CHECK_TASK_PERIOD;
		}
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
	/* The full demo includes a software timer demo/test that requires
	prodding periodically from the tick interrupt. */
	vTimerPeriodicISRTests();

	/* Call the periodic event group from ISR demo. */
	vPeriodicEventGroupsProcessing();

	/* Use task notifications from an interrupt. */
	xNotifyTaskFromISR();

	/* Writes to stream buffer byte by byte to test the stream buffer trigger
	level functionality. */
	vPeriodicStreamBufferProcessing();

	/* Writes a string to a string buffer four bytes at a time to demonstrate
	a stream being sent from an interrupt to a task. */
	vBasicStreamBufferSendFromISR();

	/* Called from vApplicationTickHook() when the project is configured to
	build the full test/demo applications. */
}
/*-----------------------------------------------------------*/

static void prvSetupPeripheralTimers( void )
{
	TMR_init( 	&g_timer0,
				CORETIMER0_BASE_ADDR,
				TMR_CONTINUOUS_MODE,
				PRESCALER_DIV_1024,
				83000 );

    TMR_init( 	&g_timer1,
				CORETIMER1_BASE_ADDR,
				TMR_CONTINUOUS_MODE,
				PRESCALER_DIV_512,
				42000 );

	/* In this version of the PLIC, the priorities are fixed at 1.
	Lower numbered devices have higher priorities. But this code is given as
	an example.
	*/
	PLIC_SetPriority( External_30_IRQn, 1 );
	PLIC_SetPriority( External_31_IRQn, 1 );

	/*Enable Timer 1 & 0 Interrupt*/
	PLIC_EnableIRQ( External_30_IRQn );
	PLIC_EnableIRQ( External_31_IRQn );

	/* Enable the timers */
	TMR_enable_int( &g_timer0 );
	TMR_enable_int( &g_timer1 );

	/* Make sure timers don't interrupt until the scheduler is running. */
	portDISABLE_INTERRUPTS();

	/*Start the timer*/
	TMR_start( &g_timer0 );
	TMR_start( &g_timer1 );
}
/*-----------------------------------------------------------*/

/*Core Timer 0 Interrupt Handler*/
uint8_t External_30_IRQHandler( void )
{
	ulTimer0Interrupts++;
    TMR_clear_int(&g_timer0);
    return( EXT_IRQ_KEEP_ENABLED );
}
/*-----------------------------------------------------------*/

/*Core Timer 1 Interrupt Handler*/
uint8_t External_31_IRQHandler( void )
{
	ulTimer1Interrupts++;
    TMR_clear_int(&g_timer1);

    return( EXT_IRQ_KEEP_ENABLED );
}
