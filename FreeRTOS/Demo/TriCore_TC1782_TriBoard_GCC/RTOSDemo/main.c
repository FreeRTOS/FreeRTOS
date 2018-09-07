/*
 * FreeRTOS Kernel V10.1.1
 * Copyright (C) 2018 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 * >>>>>> NOTE: <<<<<<
 *
 * main() can be configured to create either a very simple LED flasher demo, or
 * a more comprehensive test/demo application.
 *
 * To create a very simple LED flasher example, set the
 * mainCREATE_SIMPLE_LED_FLASHER_DEMO_ONLY constant (defined below) to 1.  When
 * this is done, only the standard demo flash tasks are created.  The standard
 * demo flash example creates three tasks, each toggle an LED at a fixed but
 * different frequency.
 *
 * To create a more comprehensive test and demo application, set
 * mainCREATE_SIMPLE_LED_FLASHER_DEMO_ONLY to 0.
 *
 * Two build configurations are provided, one that executes from RAM and one
 * that executes from Flash.  The RAM build uses size optimisation, the Flash
 * build has optimisation completely turned off.  The documentation page for
 * this port on the FreeRTOS.org web site provides full information.
 ******************************************************************************
 *
 * main() creates all the demo application tasks and timers, then starts the
 * scheduler.  The web documentation provides more details of the standard demo
 * application tasks, which provide no particular functionality, but do provide
 * a good example of how to use the FreeRTOS API.
 *
 * In addition to the standard demo tasks, the following tasks and tests are
 * defined and/or created within this file:
 *
 * "Reg test" tasks - These fill the registers with known values, then check
 * that each register maintains its expected value for the lifetime of the
 * task.  Each task uses a different set of values.  The reg test tasks execute
 * with a very low priority, so get preempted very frequently.  A register
 * containing an unexpected value is indicative of an error in the context
 * switching mechanism.
 *
 * "Check" task - The check task period is initially set to five seconds.
 * Each time it executes, the check task checks that all the standard demo
 * tasks, and the register check tasks, are not only still executing, but are
 * executing without reporting any errors.  If the check task discovers that a
 * task has either stalled, or reported an error, then it changes its own
 * execution period from the initial five seconds, to just 500ms.  The check
 * task  also toggles an LED each time it is called.  This provides a visual
 * indication of the system status:  If the LED toggles every five seconds,
 * then no issues have been discovered.  If the LED toggles every 500ms, then
 * an issue has been discovered with at least one task.
 *
 * ***NOTE*** This demo uses the standard comtest tasks, which has special
 * hardware requirements as a loopback connector, or UART echo server are
 * required.  See the documentation page for this demo on the FreeRTOS.org web
 * site for more information.  Note that the comtest tasks were tested by
 * placing the UART into loopback mode directly in the serial initialisation
 * sequence, and as such, the baud rate used has not been verified as actually
 * being correct.
 */

/* Standard includes. */
#include <stdlib.h>
#include <string.h>

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "croutine.h"

/* Demo application includes. */
#include "partest.h"
#include "flash.h"
#include "integer.h"
#include "PollQ.h"
#include "comtest2.h"
#include "semtest.h"
#include "dynamic.h"
#include "BlockQ.h"
#include "blocktim.h"
#include "countsem.h"
#include "GenQTest.h"
#include "recmutex.h"
#include "serial.h"
#include "death.h"
#include "TimerDemo.h"
#include "InterruptNestTest.h"

/*-----------------------------------------------------------*/

/* Constants for the ComTest tasks. */
#define mainCOM_TEST_BAUD_RATE		( ( unsigned long ) 200000 )

#define mainCOM_TEST_LED			( 5 )

/* Priorities for the demo application tasks. */
#define mainLED_TASK_PRIORITY		( tskIDLE_PRIORITY + 1 )
#define mainCOM_TEST_PRIORITY		( tskIDLE_PRIORITY + 2 )
#define mainQUEUE_POLL_PRIORITY		( tskIDLE_PRIORITY + 2 )
#define mainCHECK_TASK_PRIORITY		( tskIDLE_PRIORITY + 4 )
#define mainSEM_TEST_PRIORITY		( tskIDLE_PRIORITY + 1 )
#define mainBLOCK_Q_PRIORITY		( tskIDLE_PRIORITY + 2 )
#define mainCREATOR_TASK_PRIORITY	( tskIDLE_PRIORITY + 3 )

/* The rate at which the on board LED will toggle when there is/is not an
error. */
#define mainNO_ERROR_FLASH_PERIOD_MS	( ( TickType_t ) 5000 / portTICK_PERIOD_MS	)
#define mainERROR_FLASH_PERIOD_MS		( ( TickType_t ) 500 / portTICK_PERIOD_MS  )
#define mainON_BOARD_LED_BIT			( ( unsigned long ) 7 )

/* Constant used by the standard timer test functions.  The timers created by
the timer test functions will all have a period that is a multiple of this
value. */
#define mainTIMER_TEST_PERIOD		( 200 )

/* Set mainCREATE_SIMPLE_LED_FLASHER_DEMO_ONLY to 1 to create a simple demo.
Set mainCREATE_SIMPLE_LED_FLASHER_DEMO_ONLY to 0 to create a much more
comprehensive test application.  See the comments at the top of this file, and
the documentation page on the http://www.FreeRTOS.org web site for more
information. */
#define mainCREATE_SIMPLE_LED_FLASHER_DEMO_ONLY		0

/*-----------------------------------------------------------*/

/*
 * Checks that all the demo application tasks are still executing without error
 * - as described at the top of the file.
 */
static long prvCheckOtherTasksAreStillRunning( void );

/*
 * The task that executes at the highest priority and calls
 * prvCheckOtherTasksAreStillRunning().	 See the description at the top
 * of the file.
 */
static void prvCheckTask( void *pvParameters );

/*
 * Configure the processor ready to run this demo.
 */
static void prvSetupHardware( void );

/*
 * Writes to and checks the value of each register that is used in the context
 * of a task.  See the comments at the top of this file.
 */
static void prvRegisterCheckTask1( void *pvParameters );
static void prvRegisterCheckTask2( void *pvParameters );

/*
 * Specific check to see if the register test functions are still operating
 * correctly.
 */
static portBASE_TYPE prvAreRegTestTasksStillRunning( void );

/*
 * This file can be used to create either a simple LED flasher example, or a
 * comprehensive test/demo application - depending on the setting of the
 * mainCREATE_SIMPLE_LED_FLASHER_DEMO_ONLY constant defined above.  If
 * mainCREATE_SIMPLE_LED_FLASHER_DEMO_ONLY is set to 1, then the following
 * function will create a lot of additional tasks and timers.  If
 * mainCREATE_SIMPLE_LED_FLASHER_DEMO_ONLY is set to 0, then the following
 * function will do nothing.
 */
static void prvOptionallyCreateComprehensveTestApplication( void );

/*-----------------------------------------------------------*/

/* Used by the register test tasks to indicated liveness. */
static unsigned long ulRegisterTest1Count = 0;
static unsigned long ulRegisterTest2Count = 0;

/*-----------------------------------------------------------*/

/*
 * Starts all the tasks, then starts the scheduler.
 */
int main( void )
{
	/* Setup the hardware for use with the TriCore evaluation board. */
	prvSetupHardware();

	/* Start standard demo/test application flash tasks.  See the comments at
	the top of this file.  The LED flash tasks are always created.  The other
	tasks are only created if mainCREATE_SIMPLE_LED_FLASHER_DEMO_ONLY is set to
	0 (at the top of this file).  See the comments at the top of this file for
	more information. */
	vStartLEDFlashTasks( mainLED_TASK_PRIORITY );

	/* The following function will only create more tasks and timers if
	mainCREATE_SIMPLE_LED_FLASHER_DEMO_ONLY is set to 0 (at the top of this
	file).  See the comments at the top of this file for more information. */
	prvOptionallyCreateComprehensveTestApplication();

	/* Now all the tasks have been started - start the scheduler. */
	vTaskStartScheduler();

	/* If all is well then the following line will never be reached.  If
	execution does reach here, then it is highly probably that the heap size
	is too small for the idle and/or timer tasks to be created within
	vTaskStartScheduler(). */
	for( ;; );
}
/*-----------------------------------------------------------*/

static void prvCheckTask( void *pvParameters )
{
TickType_t xDelayPeriod = mainNO_ERROR_FLASH_PERIOD_MS;
TickType_t xLastExecutionTime;

	/* Just to stop compiler warnings. */
	( void ) pvParameters;

	/* Initialise xLastExecutionTime so the first call to vTaskDelayUntil()
	works correctly. */
	xLastExecutionTime = xTaskGetTickCount();

	/* Cycle for ever, delaying then checking all the other tasks are still
	operating without error.  If an error is detected then the delay period
	is decreased from mainNO_ERROR_FLASH_PERIOD_MS to mainERROR_FLASH_PERIOD_MS so
	the on board LED flash rate will increase.  NOTE:  This task could easily
	be replaced by a software timer callback to remove the overhead of having
	an extra task. */

	for( ;; )
	{
		/* Delay until it is time to execute again. */
		vTaskDelayUntil( &xLastExecutionTime, xDelayPeriod );

		/* Check all the standard demo application tasks are executing without
		error.	*/
		if( prvCheckOtherTasksAreStillRunning() != pdPASS )
		{
			/* An error has been detected in one of the tasks - flash the LED
			at a higher frequency to give visible feedback that something has
			gone wrong (it might just be that the loop back connector required
			by the comtest tasks has not been fitted). */
			xDelayPeriod = mainERROR_FLASH_PERIOD_MS;
		}

		/* The toggle rate of the LED depends on how long this task delays for.
		An error reduces the delay period and so increases the toggle rate. */
		vParTestToggleLED( mainON_BOARD_LED_BIT );
	}
}
/*-----------------------------------------------------------*/

static long prvCheckOtherTasksAreStillRunning( void )
{
long lReturn = pdPASS;
unsigned long ulHighFrequencyTimerTaskIterations, ulExpectedIncFrequency_ms;

	/* Check all the demo tasks (other than the flash tasks) to ensure
	that they are all still running, and that none have detected an error. */

	if( xAreIntegerMathsTaskStillRunning() != pdTRUE )
	{
		lReturn = pdFAIL;
	}

	if( xAreComTestTasksStillRunning() != pdTRUE )
	{
		lReturn = pdFAIL;
	}

	if( xAreDynamicPriorityTasksStillRunning() != pdTRUE )
	{
		lReturn = pdFAIL;
	}

	if( xAreBlockingQueuesStillRunning() != pdTRUE )
	{
		lReturn = pdFAIL;
	}

	if ( xAreBlockTimeTestTasksStillRunning() != pdTRUE )
	{
		lReturn = pdFAIL;
	}

	if ( xAreGenericQueueTasksStillRunning() != pdTRUE )
	{
		lReturn = pdFAIL;
	}

	if ( xAreRecursiveMutexTasksStillRunning() != pdTRUE )
	{
		lReturn = pdFAIL;
	}

	if( prvAreRegTestTasksStillRunning() != pdTRUE )
	{
		lReturn = pdFAIL;
	}

	if( xIsCreateTaskStillRunning() != pdTRUE )
	{
		lReturn = pdFAIL;
	}

	if( xAreTimerDemoTasksStillRunning( mainNO_ERROR_FLASH_PERIOD_MS ) != pdTRUE )
	{
		lReturn = pdFAIL;
	}

	if( xArePollingQueuesStillRunning() != pdTRUE )
	{
		lReturn = pdFAIL;
	}

	if( xAreSemaphoreTasksStillRunning() != pdTRUE )
	{
		lReturn = pdFAIL;
	}

	/* Obtain the number of times the task associated with the high frequency
	(interrupt nesting) timer test has increment since the check task last
	executed, and the frequency at which it is expected to execute in ms. */
	ulHighFrequencyTimerTaskIterations = ulInterruptNestingTestGetIterationCount( &ulExpectedIncFrequency_ms );
	if( ( ulHighFrequencyTimerTaskIterations < ( ( mainNO_ERROR_FLASH_PERIOD_MS / ulExpectedIncFrequency_ms ) - 1 ) )
		||
		( ulHighFrequencyTimerTaskIterations > ( ( mainNO_ERROR_FLASH_PERIOD_MS / ulExpectedIncFrequency_ms ) +5 ) )
	  )
	{
		/* Would have expected the high frequency timer task to have
		incremented its execution count more times that reported. */
		lReturn = pdFAIL;
	}

	return lReturn;
}
/*-----------------------------------------------------------*/

static void prvSetupHardware( void )
{
extern void set_cpu_frequency(void);

	/* Set-up the PLL. */
	set_cpu_frequency();

	/* Initialise LED outputs. */
	vParTestInitialise();
}
/*-----------------------------------------------------------*/

void vApplicationMallocFailedHook( void )
{
	/* vApplicationMallocFailedHook() will only be called if
	configUSE_MALLOC_FAILED_HOOK is set to 1 in FreeRTOSConfig.h.  It is a hook
	function that will get called if a call to pvPortMalloc() fails.
	pvPortMalloc() is called internally by the kernel whenever a task, queue,
	timer or semaphore is created.  It is also called by various parts of the
	demo application.  If heap_1.c or heap_2.c are used, then the size of the
	heap available to pvPortMalloc() is defined by configTOTAL_HEAP_SIZE in
	FreeRTOSConfig.h, and the xPortGetFreeHeapSize() API function can be used
	to query the size of free heap space that remains (although it does not
	provide information on how the remaining heap might be fragmented). */
	taskDISABLE_INTERRUPTS();
	for( ;; );
}
/*-----------------------------------------------------------*/

void vApplicationTickHook( void )
{
	#if mainCREATE_SIMPLE_LED_FLASHER_DEMO_ONLY != 1
	{
		/* vApplicationTickHook() will only be called if configUSE_TICK_HOOK is set
		to 1 in FreeRTOSConfig.h.  It is a hook function that will get called during
		each FreeRTOS tick interrupt.  Note that vApplicationTickHook() is called
		from an interrupt context. */

		/* Call the periodic timer test, which tests the timer API functions that
		can be called from an ISR. */
		vTimerPeriodicISRTests();
	}
	#endif /* mainCREATE_SIMPLE_LED_FLASHER_DEMO_ONLY */
}
/*-----------------------------------------------------------*/

void vApplicationIdleHook( void )
{
	/* vApplicationIdleHook() will only be called if configUSE_IDLE_HOOK is set
	to 1 in FreeRTOSConfig.h.  It will be called on each iteration of the idle
	task.  It is essential that code added to this hook function never attempts
	to block in any way (for example, call xQueueReceive() with a block time
	specified, or call vTaskDelay()).  If the application makes use of the
	vTaskDelete() API function (as this demo application does) then it is also
	important that vApplicationIdleHook() is permitted to return to its calling
	function, because it is the responsibility of the idle task to clean up
	memory allocated by the kernel to any task that has since been deleted. */
}
/*-----------------------------------------------------------*/

static portBASE_TYPE prvAreRegTestTasksStillRunning( void )
{
static unsigned long ulPreviousRegisterTest1Count = 0;
static unsigned long ulPreviousRegisterTest2Count = 0;
portBASE_TYPE xReturn = pdPASS;

	/* Check to see if the Counts have changed since the last check. */
	if( ulRegisterTest1Count == ulPreviousRegisterTest1Count )
	{
		xReturn = pdFAIL;
	}

	if( ulRegisterTest2Count == ulPreviousRegisterTest2Count )
	{
		xReturn = pdFAIL;
	}

	/* Remember the current count for the next time this function is called. */
	ulPreviousRegisterTest1Count = ulRegisterTest1Count;
	ulPreviousRegisterTest2Count = ulRegisterTest2Count;

	return xReturn;
}
/*-----------------------------------------------------------*/

static void prvOptionallyCreateComprehensveTestApplication( void )
{
	#if mainCREATE_SIMPLE_LED_FLASHER_DEMO_ONLY == 0
	{
		vStartIntegerMathTasks( tskIDLE_PRIORITY );
		vStartDynamicPriorityTasks();
		vStartBlockingQueueTasks( mainBLOCK_Q_PRIORITY );
		vCreateBlockTimeTasks();
		vStartCountingSemaphoreTasks();
		vStartGenericQueueTasks( tskIDLE_PRIORITY );
		vStartRecursiveMutexTasks();
		vAltStartComTestTasks( mainCOM_TEST_PRIORITY, mainCOM_TEST_BAUD_RATE, mainCOM_TEST_LED );
		vSetupInterruptNestingTest();
		vStartTimerDemoTask( mainTIMER_TEST_PERIOD );
		vStartPolledQueueTasks( mainQUEUE_POLL_PRIORITY );
		vStartSemaphoreTasks( mainSEM_TEST_PRIORITY );

		/* Create the register test tasks, as described at the top of this file. */
		xTaskCreate( prvRegisterCheckTask1, "Reg 1", configMINIMAL_STACK_SIZE, &ulRegisterTest1Count, tskIDLE_PRIORITY, NULL );
		xTaskCreate( prvRegisterCheckTask2, "Reg 2", configMINIMAL_STACK_SIZE, &ulRegisterTest2Count, tskIDLE_PRIORITY, NULL );

		/* Start the check task - which is defined in this file. */
		xTaskCreate( prvCheckTask, "Check", configMINIMAL_STACK_SIZE, NULL, mainCHECK_TASK_PRIORITY, NULL );

		/* This task has to be created last as it keeps account of the number of tasks
		it expects to see running. */
		vCreateSuicidalTasks( mainCREATOR_TASK_PRIORITY );
	}
	#else /* mainCREATE_SIMPLE_LED_FLASHER_DEMO_ONLY */
	{
		/* Just to prevent compiler warnings when the configuration options are
		set such that these static functions are not used. */
		( void ) prvCheckTask;
		( void ) prvRegisterCheckTask1;
		( void ) prvRegisterCheckTask2;
	}
	#endif /* mainCREATE_SIMPLE_LED_FLASHER_DEMO_ONLY */
}
/*-----------------------------------------------------------*/

static void prvRegisterCheckTask1( void *pvParameters )
{
	/* Make space on the stack for the parameter and a counter. */
	__asm volatile( " sub.a %sp, 4 			\n"
					" st.a [%sp], %a4		\n"
					" mov %d15, 0			\n"
					" st.w [%sp]4, %d15		\n" );

	/* Change all of the Context sensitive registers (except SP and RA). */
	__asm volatile(
			" mov %d0, 0		\n"
			" mov %d1, 1		\n"
			" mov %d2, 2		\n"
			" mov %d3, 3		\n"
			" mov %d4, 4		\n"
			" mov %d5, 5		\n"
			" mov %d6, 6		\n"
			" mov %d7, 7		\n"
			" mov %d8, 8		\n"
			" mov %d9, 9		\n"
			" mov %d10, 10		\n"
			" mov %d11, 11		\n"
			" mov %d12, 12		\n"
			" mov %d13, 13		\n"
			" mov %d14, 14		\n"
			" mov %d15, 15		\n"
			" mov.a %a2, 2		\n"
			" mov.a %a3, 3		\n"
			" mov.a %a4, 4		\n"
			" mov.a %a5, 5		\n"
			" mov.a %a6, 6		\n"
			" mov.a %a7, 7		\n"
			" mov.a %a12, 12	\n"
			" mov.a %a13, 13	\n"
			" mov.a %a14, 14	\n" );

	/* Check the values of the registers. */
	__asm(	" _task1_loop:							\n" \
			" eq %d1, %d0, 0						\n" \
			" jne %d1, 1, _task1_error_loop			\n" \
			" eq %d1, %d1, 1						\n" \
			" jne %d1, 1, _task1_error_loop			\n" \
			" eq %d1, %d2, 2						\n" \
			" jne %d1, 1, _task1_error_loop			\n" \
			" eq %d1, %d3, 3						\n" \
			" jne %d1, 1, _task1_error_loop			\n" \
			" eq %d1, %d4, 4						\n" \
			" jne %d1, 1, _task1_error_loop			\n" \
			" eq %d1, %d5, 5						\n" \
			" jne %d1, 1, _task1_error_loop			\n" \
			" eq %d1, %d6, 6						\n" \
			" jne %d1, 1, _task1_error_loop			\n" \
			" eq %d1, %d7, 7						\n" \
			" jne %d1, 1, _task1_error_loop			\n" \
			" eq %d1, %d8, 8						\n" \
			" jne %d1, 1, _task1_error_loop			\n" \
			" eq %d1, %d9, 9						\n" \
			" jne %d1, 1, _task1_error_loop			\n" \
			" eq %d1, %d10, 10						\n" \
			" jne %d1, 1, _task1_error_loop			\n" \
			" eq %d1, %d11, 11						\n" \
			" jne %d1, 1, _task1_error_loop			\n" \
			" eq %d1, %d12, 12						\n" \
			" jne %d1, 1, _task1_error_loop			\n" \
			" eq %d1, %d13, 13						\n" \
			" jne %d1, 1, _task1_error_loop			\n" \
			" eq %d1, %d14, 14						\n" \
			" jne %d1, 1, _task1_error_loop			\n" \
			" eq %d1, %d15, 15						\n" \
			" jne %d1, 1, _task1_error_loop			\n" \
			" mov.a %a15, 2							\n" \
			" jne.a %a15, %a2, _task1_error_loop	\n" \
			" mov.a %a15, 3							\n" \
			" jne.a %a15, %a3, _task1_error_loop	\n" \
			" mov.a %a15, 4							\n" \
			" jne.a %a15, %a4, _task1_error_loop	\n" \
			" mov.a %a15, 5							\n" \
			" jne.a %a15, %a5, _task1_error_loop	\n" \
			" mov.a %a15, 6							\n" \
			" jne.a %a15, %a6, _task1_error_loop	\n" \
			" mov.a %a15, 7							\n" \
			" jne.a %a15, %a7, _task1_error_loop	\n" \
			" mov.a %a15, 12						\n" \
			" jne.a %a15, %a12, _task1_error_loop	\n" \
			" mov.a %a15, 13						\n" \
			" jne.a %a15, %a13, _task1_error_loop	\n" \
			" mov.a %a15, 14						\n" \
			" jne.a %a15, %a14, _task1_error_loop	\n" \
			" j _task1_skip_error_loop				\n"	\
			"_task1_error_loop:						\n"	/* Hitting this error loop will stop the counter incrementing, allowing the check task to recognise an error. */ \
			"	debug								\n"	\
			" j _task1_error_loop					\n"	\
			"_task1_skip_error_loop:				\n" );

	/* Load the parameter address from the stack and modify the value. */
	__asm volatile(									\
			" ld.w %d1, [%sp]4						\n"	\
			" add %d1, 1							\n"	\
			" st.w [%sp]4, %d1						\n"	\
			" ld.a %a15, [%sp]						\n"	\
			" st.w [%a15], %d1						\n"	\
			" j _task1_loop							\n" );

	/* The parameter is used but in the assembly. */
	(void)pvParameters;
}
/*-----------------------------------------------------------*/

static void prvRegisterCheckTask2( void *pvParameters )
{
	/* Make space on the stack for the parameter and a counter. */
	__asm volatile( " sub.a %sp, 4 		\n" \
					" st.a [%sp], %a4	\n" \
					" mov %d15, 0		\n" \
					" st.w [%sp]4, %d15	\n" );

	/* Change all of the Context sensitive registers (except SP and RA). */
	__asm volatile(	" mov %d0, 7		\n" \
					" mov %d1, 1		\n" \
					" mov %d2, 5		\n" \
					" mov %d3, 4		\n" \
					" mov %d4, 3		\n" \
					" mov %d5, 2		\n" \
					" mov %d6, 1		\n" \
					" mov %d7, 0		\n" \
					" mov %d8, 15		\n" \
					" mov %d9, 14		\n" \
					" mov %d10, 13		\n" \
					" mov %d11, 12		\n" \
					" mov %d12, 11		\n" \
					" mov %d13, 10		\n" \
					" mov %d14, 9		\n" \
					" mov %d15, 8		\n" \
					" mov.a %a2, 14		\n" \
					" mov.a %a3, 13		\n" \
					" mov.a %a4, 12		\n" \
					" mov.a %a5, 7		\n" \
					" mov.a %a6, 6		\n" \
					" mov.a %a7, 5		\n" \
					" mov.a %a12, 4		\n" \
					" mov.a %a13, 3		\n" \
					" mov.a %a14, 2		\n" );

	/* Check the values of the registers. */
	__asm volatile(	" _task2_loop:							\n" \
					" syscall 0								\n" \
					" eq %d1, %d0, 7						\n" \
					" jne %d1, 1, _task2_error_loop			\n" \
					" eq %d1, %d1, 1						\n" \
					" jne %d1, 1, _task2_error_loop			\n" \
					" eq %d1, %d2, 5						\n" \
					" jne %d1, 1, _task2_error_loop			\n" \
					" eq %d1, %d3, 4						\n" \
					" jne %d1, 1, _task2_error_loop			\n" \
					" eq %d1, %d4, 3						\n" \
					" jne %d1, 1, _task2_error_loop			\n" \
					" eq %d1, %d5, 2						\n" \
					" jne %d1, 1, _task2_error_loop			\n" \
					" eq %d1, %d6, 1						\n" \
					" jne %d1, 1, _task2_error_loop			\n" \
					" eq %d1, %d7, 0						\n" \
					" jne %d1, 1, _task2_error_loop			\n" \
					" eq %d1, %d8, 15						\n" \
					" jne %d1, 1, _task2_error_loop			\n" \
					" eq %d1, %d9, 14						\n" \
					" jne %d1, 1, _task2_error_loop			\n" \
					" eq %d1, %d10, 13						\n" \
					" jne %d1, 1, _task2_error_loop			\n" \
					" eq %d1, %d11, 12						\n" \
					" jne %d1, 1, _task2_error_loop			\n" \
					" eq %d1, %d12, 11						\n" \
					" jne %d1, 1, _task2_error_loop			\n" \
					" eq %d1, %d13, 10						\n" \
					" jne %d1, 1, _task2_error_loop			\n" \
					" eq %d1, %d14, 9						\n" \
					" jne %d1, 1, _task2_error_loop			\n" \
					" eq %d1, %d15, 8						\n" \
					" jne %d1, 1, _task2_error_loop			\n" \
					" mov.a %a15, 14						\n" \
					" jne.a %a15, %a2, _task2_error_loop	\n" \
					" mov.a %a15, 13						\n" \
					" jne.a %a15, %a3, _task2_error_loop	\n" \
					" mov.a %a15, 12						\n" \
					" jne.a %a15, %a4, _task2_error_loop	\n" \
					" mov.a %a15, 7							\n" \
					" jne.a %a15, %a5, _task2_error_loop	\n" \
					" mov.a %a15, 6							\n" \
					" jne.a %a15, %a6, _task2_error_loop	\n" \
					" mov.a %a15, 5							\n" \
					" jne.a %a15, %a7, _task2_error_loop	\n" \
					" mov.a %a15, 4							\n" \
					" jne.a %a15, %a12, _task2_error_loop 	\n" \
					" mov.a %a15, 3							\n" \
					" jne.a %a15, %a13, _task2_error_loop	\n" \
					" mov.a %a15, 2							\n" \
					" jne.a %a15, %a14, _task2_error_loop	\n" \
					" j _task2_skip_error_loop				\n"	\
					"_task2_error_loop:						\n"	/* Hitting this error loop will stop the counter incrementing, allowing the check task to recognise an error. */ \
					" debug									\n" \
					" j _task2_error_loop					\n"	\
					"_task2_skip_error_loop:				\n"	);

	/* Load the parameter address from the stack and modify the value. */
	__asm volatile(	" ld.w %d1, [%sp]4						\n"	\
					" add %d1, %d1, 1						\n"	\
					" st.w [%sp]4, %d1						\n"	\
					" ld.a %a15, [%sp]						\n"	\
					" st.w [%a15], %d1						\n"	\
					" j _task2_loop                			\n"  );

	/* The parameter is used but in the assembly. */
	(void)pvParameters;
}

/*-----------------------------------------------------------*/

