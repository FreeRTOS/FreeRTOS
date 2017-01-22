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
 * >>>>>> NOTE 1: <<<<<<
 *
 * main() can be configured to create either a very simple LED flasher demo, or
 * a more comprehensive test/demo application.
 *
 * To create a very simple LED flasher example, set the
 * mainCREATE_SIMPLE_LED_FLASHER_DEMO_ONLY constant (defined below) to 1.  When
 * this is done, only the standard demo flash tasks are created.  The standard
 * demo flash example creates three tasks, each of which toggle an LED at a
 * fixed but different frequency.
 *
 * To create a more comprehensive test and demo application, set
 * mainCREATE_SIMPLE_LED_FLASHER_DEMO_ONLY to 0.
 ******************************************************************************
 *
 * main() creates all the demo application tasks and software timers, then starts
 * the scheduler.  The web documentation provides more details of the standard
 * demo application tasks, which provide no particular functionality, but do
 * provide a good example of how to use the FreeRTOS API.
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
 * "Check" timer - The check software timer period is initially set to three
 * seconds.  The callback function associated with the check software timer
 * checks that all the standard demo tasks, and the register check tasks, are
 * not only still executing, but are executing without reporting any errors.  If
 * the check software timer discovers that a task has either stalled, or
 * reported an error, then it changes its own execution period from the initial
 * three seconds, to just 200ms.  The check software timer callback function
 * also toggles an LED each time it is called.  This provides a visual
 * indication of the system status:  If the LED toggles every three seconds,
 * then no issues have been discovered.  If the LED toggles every 200ms, then
 * an issue has been discovered with at least one task.
 */

/* Standard includes. */
#include <stdio.h>

/* Kernel includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "timers.h"
#include "semphr.h"

/* Demo application includes. */
#include "partest.h"
#include "flash.h"
#include "flop.h"
#include "integer.h"
#include "PollQ.h"
#include "semtest.h"
#include "dynamic.h"
#include "BlockQ.h"
#include "blocktim.h"
#include "countsem.h"
#include "GenQTest.h"
#include "recmutex.h"
#include "death.h"

/* Hardware includes. */
#include "platform_config.h"

/* Priorities for the demo application tasks. */
#define mainFLASH_TASK_PRIORITY				( tskIDLE_PRIORITY + 1UL )
#define mainQUEUE_POLL_PRIORITY				( tskIDLE_PRIORITY + 2UL )
#define mainSEM_TEST_PRIORITY				( tskIDLE_PRIORITY + 1UL )
#define mainBLOCK_Q_PRIORITY				( tskIDLE_PRIORITY + 2UL )
#define mainCREATOR_TASK_PRIORITY			( tskIDLE_PRIORITY + 3UL )
#define mainFLOP_TASK_PRIORITY				( tskIDLE_PRIORITY )

/* The LED used by the check timer. */
#define mainCHECK_LED 						( 3UL )

/* A block time of zero simply means "don't block". */
#define mainDONT_BLOCK						( 0UL )

/* The period after which the check timer will expire, in ms, provided no errors
have been reported by any of the standard demo tasks.  ms are converted to the
equivalent in ticks using the portTICK_PERIOD_MS constant. */
#define mainCHECK_TIMER_PERIOD_MS			( 3000UL / portTICK_PERIOD_MS )

/* The period at which the check timer will expire, in ms, if an error has been
reported in one of the standard demo tasks.  ms are converted to the equivalent
in ticks using the portTICK_PERIOD_MS constant. */
#define mainERROR_CHECK_TIMER_PERIOD_MS 	( 200UL / portTICK_PERIOD_MS )

/* Set mainCREATE_SIMPLE_LED_FLASHER_DEMO_ONLY to 1 to create a simple demo.
Set mainCREATE_SIMPLE_LED_FLASHER_DEMO_ONLY to 0 to create a much more
comprehensive test application.  See the comments at the top of this file, and
the documentation page on the http://www.FreeRTOS.org web site for more
information. */
#define mainCREATE_SIMPLE_LED_FLASHER_DEMO_ONLY		0

/*-----------------------------------------------------------*/

/*
 * Set up the hardware ready to run this demo.
 */
static void prvSetupHardware( void );

/*
 * The check timer callback function, as described at the top of this file.
 */
static void prvCheckTimerCallback( TimerHandle_t xTimer );

/*
 * Register check tasks, and the tasks used to write over and check the contents
 * of the FPU registers, as described at the top of this file.  The nature of
 * these files necessitates that they are written in an assembly file.
 */
extern void vRegTest1Task( void *pvParameters );
extern void vRegTest2Task( void *pvParameters );
extern void vRegTestClearFlopRegistersToParameterValue( unsigned long ulValue );
extern unsigned long ulRegTestCheckFlopRegistersContainParameterValue( unsigned long ulValue );

/*
 * This file can be used to create either a simple LED flasher example, or a
 * comprehensive test/demo application - depending on the setting of the
 * mainCREATE_SIMPLE_LED_FLASHER_DEMO_ONLY constant defined above.  If
 * mainCREATE_SIMPLE_LED_FLASHER_DEMO_ONLY is set to 1, then the following
 * function will create a lot of additional tasks and a software timer.  If
 * mainCREATE_SIMPLE_LED_FLASHER_DEMO_ONLY is set to 0, then the following
 * function will do nothing.
 */
static void prvOptionallyCreateComprehensveTestApplication( void );

/*-----------------------------------------------------------*/

/* The following two variables are used to communicate the status of the
register check tasks to the check software timer.  If the variables keep
incrementing, then the register check tasks have not discovered any errors.  If
a variable stops incrementing, then an error has been found. */
volatile unsigned long ulRegTest1LoopCounter = 0UL, ulRegTest2LoopCounter = 0UL;

/*-----------------------------------------------------------*/

int main( void )
{
	/* Configure the hardware ready to run the test. */
	prvSetupHardware();

	/* Start standard demo/test application flash tasks.  See the comments at
	the top of this file.  The LED flash tasks are always created.  The other
	tasks are only created if mainCREATE_SIMPLE_LED_FLASHER_DEMO_ONLY is set to
	0 (at the top of this file).  See the comments at the top of this file for
	more information. */
	vStartLEDFlashTasks( mainFLASH_TASK_PRIORITY );

	/* The following function will only create more tasks and timers if
	mainCREATE_SIMPLE_LED_FLASHER_DEMO_ONLY is set to 0 (at the top of this
	file).  See the comments at the top of this file for more information. */
	prvOptionallyCreateComprehensveTestApplication();

	/* Start the scheduler. */
	vTaskStartScheduler();

	/* Infinite loop */
	for( ;; );
}
/*-----------------------------------------------------------*/

static void prvCheckTimerCallback( TimerHandle_t xTimer )
{
static long lChangedTimerPeriodAlready = pdFALSE;
static unsigned long ulLastRegTest1Value = 0, ulLastRegTest2Value = 0;
unsigned long ulErrorFound = pdFALSE;

	/* Check all the demo tasks (other than the flash tasks) to ensure
	that they are all still running, and that none have detected an error. */

	if( xAreMathsTaskStillRunning() != pdTRUE )
	{
		ulErrorFound |= 0x01UL << 0UL;
	}

	if( xAreIntegerMathsTaskStillRunning() != pdTRUE )
	{
		ulErrorFound |= 0x01UL << 1UL;
	}

	if( xAreDynamicPriorityTasksStillRunning() != pdTRUE )
	{
		ulErrorFound |= 0x01UL << 2UL;
	}

	if( xAreBlockingQueuesStillRunning() != pdTRUE )
	{
		ulErrorFound |= 0x01UL << 3UL;
	}

	if ( xAreBlockTimeTestTasksStillRunning() != pdTRUE )
	{
		ulErrorFound |= 0x01UL << 4UL;
	}

	if ( xAreGenericQueueTasksStillRunning() != pdTRUE )
	{
		ulErrorFound |= 0x01UL << 5UL;
	}

	if ( xAreRecursiveMutexTasksStillRunning() != pdTRUE )
	{
		ulErrorFound |= 0x01UL << 6UL;
	}

	if( xIsCreateTaskStillRunning() != pdTRUE )
	{
		ulErrorFound |= 0x01UL << 7UL;
	}

	if( xArePollingQueuesStillRunning() != pdTRUE )
	{
		ulErrorFound |= 0x01UL << 8UL;
	}

	if( xAreSemaphoreTasksStillRunning() != pdTRUE )
	{
		ulErrorFound |= 0x01UL << 9UL;
	}

	/* Check that the register test 1 task is still running. */
	if( ulLastRegTest1Value == ulRegTest1LoopCounter )
	{
		ulErrorFound |= 0x01UL << 10UL;
	}
	ulLastRegTest1Value = ulRegTest1LoopCounter;

	/* Check that the register test 2 task is still running. */
	if( ulLastRegTest2Value == ulRegTest2LoopCounter )
	{
		ulErrorFound |= 0x01UL << 11UL;
	}
	ulLastRegTest2Value = ulRegTest2LoopCounter;

	/* Toggle the check LED to give an indication of the system status.  If
	the LED toggles every mainCHECK_TIMER_PERIOD_MS milliseconds then
	everything is ok.  A faster toggle indicates an error. */
	vParTestToggleLED( mainCHECK_LED );

	/* Have any errors been latch in ulErrorFound?  If so, shorten the
	period of the check timer to mainERROR_CHECK_TIMER_PERIOD_MS milliseconds.
	This will result in an increase in the rate at which mainCHECK_LED
	toggles. */
	if( ulErrorFound != pdFALSE )
	{
		if( lChangedTimerPeriodAlready == pdFALSE )
		{
			lChangedTimerPeriodAlready = pdTRUE;

			/* This call to xTimerChangePeriod() uses a zero block time.
			Functions called from inside of a timer callback function must
			*never* attempt	to block. */
			xTimerChangePeriod( xTimer, ( mainERROR_CHECK_TIMER_PERIOD_MS ), mainDONT_BLOCK );
		}
	}
}
/*-----------------------------------------------------------*/

static void prvSetupHardware( void )
{
extern void Hitex_CGU_Init( void );

	/* Setup system (clock, PLL and Flash configuration) */
	platformInit();

	/* Wind the clock speed up in steps to its maximum. */
	Hitex_CGU_Init();

	/* Ensure all priority bits are assigned as preemption priority bits. */
	NVIC_SetPriorityGrouping( 0 );

	/* Setup the LED outputs. */
	vParTestInitialise();
}
/*-----------------------------------------------------------*/

static void prvOptionallyCreateComprehensveTestApplication( void )
{
	#if ( mainCREATE_SIMPLE_LED_FLASHER_DEMO_ONLY == 0 )
	{
	TimerHandle_t xCheckTimer = NULL;

		/* Start all the other standard demo/test tasks. */
		vStartIntegerMathTasks( tskIDLE_PRIORITY );
		vStartDynamicPriorityTasks();
		vStartBlockingQueueTasks( mainBLOCK_Q_PRIORITY );
		vCreateBlockTimeTasks();
		vStartCountingSemaphoreTasks();
		vStartGenericQueueTasks( tskIDLE_PRIORITY );
		vStartRecursiveMutexTasks();
		vStartPolledQueueTasks( mainQUEUE_POLL_PRIORITY );
		vStartSemaphoreTasks( mainSEM_TEST_PRIORITY );

		/* Most importantly, start the tasks that use the FPU. */
		vStartMathTasks( mainFLOP_TASK_PRIORITY );

		/* Create the register check tasks, as described at the top of this
		file */
		xTaskCreate( vRegTest1Task, "Reg1", configMINIMAL_STACK_SIZE, ( void * ) NULL, tskIDLE_PRIORITY, NULL );
		xTaskCreate( vRegTest2Task, "Reg2", configMINIMAL_STACK_SIZE, ( void * ) NULL, tskIDLE_PRIORITY, NULL );

		/* Create the software timer that performs the 'check' functionality,
		as described at the top of this file. */
		xCheckTimer = xTimerCreate( "CheckTimer",					/* A text name, purely to help debugging. */
									( mainCHECK_TIMER_PERIOD_MS ),	/* The timer period, in this case 3000ms (3s). */
									pdTRUE,							/* This is an auto-reload timer, so xAutoReload is set to pdTRUE. */
									( void * ) 0,					/* The ID is not used, so can be set to anything. */
									prvCheckTimerCallback			/* The callback function that inspects the status of all the other tasks. */
								  );

		if( xCheckTimer != NULL )
		{
			xTimerStart( xCheckTimer, mainDONT_BLOCK );
		}

		/* This task has to be created last as it keeps account of the number of
		tasks it expects to see running. */
		vCreateSuicidalTasks( mainCREATOR_TASK_PRIORITY );
	}
	#else /* mainCREATE_SIMPLE_LED_FLASHER_DEMO_ONLY */
	{
		/* Just to prevent compiler warnings when the configuration options are
		set such that these static functions are not used. */
		( void ) vRegTest1Task;
		( void ) vRegTest2Task;
		( void ) prvCheckTimerCallback;
		( void ) prvSetupNestedFPUInterruptsTest;
	}
	#endif /* mainCREATE_SIMPLE_LED_FLASHER_DEMO_ONLY */
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

void vApplicationStackOverflowHook( TaskHandle_t pxTask, char *pcTaskName )
{
	( void ) pcTaskName;
	( void ) pxTask;

	/* Run time stack overflow checking is performed if
	configCHECK_FOR_STACK_OVERFLOW is defined to 1 or 2.  This hook
	function is called if a stack overflow is detected. */
	taskDISABLE_INTERRUPTS();
	for( ;; );
}
/*-----------------------------------------------------------*/

void vApplicationTickHook( void )
{
	/* This function will be called by each tick interrupt if
	configUSE_TICK_HOOK is set to 1 in FreeRTOSConfig.h.  User code can be
	added here, but the tick hook is called from an interrupt context, so
	code must not attempt to block, and only the interrupt safe FreeRTOS API
	functions can be used (those that end in FromISR()). */
}
/*-----------------------------------------------------------*/
