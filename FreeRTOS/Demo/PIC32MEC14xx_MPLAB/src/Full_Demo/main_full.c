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
 * NOTE 1:  This project provides two demo applications.  A simple blinky style
 * project, and a more comprehensive test and demo application.  The
 * mainCREATE_SIMPLE_BLINKY_DEMO_ONLY setting in main.c is used to select
 * between the two.  See the notes on using mainCREATE_SIMPLE_BLINKY_DEMO_ONLY
 * in main.c.  This file implements the comprehensive test and demo version.
 *
 * NOTE 2:  This file only contains the source code that is specific to the
 * full demo.  Generic functions, such as FreeRTOS hook functions, and functions
 * required to configure the hardware, are defined in main.c.
 ******************************************************************************
 *
 * main_full() creates all the demo application tasks and software timers, then
 * starts the scheduler.  The WEB documentation provides more details of the
 * standard demo application tasks.  In addition to the standard demo tasks, the
 * following tasks and tests are also defined:
 *
 * "Register test" tasks - These tasks are used in part to test the kernel port.
 * They set each processor register to a known value, then check that the
 * register still contains that value.  Each of the tasks sets the registers
 * to different values, and will get swapping in and out between setting and
 * then subsequently checking the register values.  Discovery of an incorrect
 * value would be indicative of an error in the task switching mechanism.
 *
 * "High Frequency Timer Test" - The high frequency timer is created to test
 * the interrupt nesting method.  The standard demo interrupt nesting test tasks
 * are created with priorities at or below configMAX_SYSCALL_INTERRUPT_PRIORITY
 * because they use interrupt safe FreeRTOS API functions.  The high frequency
 * time is created with a priority above configMAX_SYSCALL_INTERRUPT_PRIORITY,
 * so cannot us the same API functions.
 *
 * "Check" timer - The check software timer period is initially set to three
 * seconds.  The callback function associated with the check software timer
 * checks that all the standard demo tasks, and the register check tasks, are
 * not only still executing, but are executing without reporting any errors.  If
 * the check software timer discovers that a task has either stalled, or
 * reported an error, then it changes its own execution period from the initial
 * three seconds, to just 200ms.  The check software timer also toggle LED
 * mainCHECK_LED;  If mainCHECK_LED toggles every 3 seconds, no errors have
 * been detected.  If mainCHECK_LED toggles every 200ms then an error has been
 * detected in at least one task.
 *
 */

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"
#include "semphr.h"
#include "timers.h"

/* Demo application includes. */
#include "blocktim.h"
#include "semtest.h"
#include "GenQTest.h"
#include "IntQueue.h"
#include "countsem.h"

/*-----------------------------------------------------------*/

/* The period after which the check timer will expire, in ms, provided no errors
have been reported by any of the standard demo tasks.  ms are converted to the
equivalent in ticks using the portTICK_PERIOD_MS constant. */
#define mainCHECK_TIMER_PERIOD_MS			pdMS_TO_TICKS( 3000UL )

/* The period at which the check timer will expire, in ms, if an error has been
reported in one of the standard demo tasks.  ms are converted to the equivalent
in ticks using the portTICK_PERIOD_MS constant. */
#define mainERROR_CHECK_TIMER_PERIOD_MS 	pdMS_TO_TICKS( 200UL )

/* The priorities of the various demo application tasks. */
#define mainSEM_TEST_PRIORITY				( tskIDLE_PRIORITY + 1 )
#define mainGEN_QUEUE_TASK_PRIORITY			( tskIDLE_PRIORITY )

/* The LED controlled by the 'check' software timer. */
#define mainCHECK_LED						( 2 )

/* Misc. */
#define mainDONT_BLOCK						( 0 )

/* The frequency at which the "high frequency interrupt" interrupt will
occur. */
#define mainTEST_INTERRUPT_FREQUENCY		( 20000 )

/*-----------------------------------------------------------*/

/*
 * The check timer callback function, as described at the top of this file.
 */
static void prvCheckTimerCallback( TimerHandle_t xTimer );

/*
 * It is important to ensure the high frequency timer test does not start before
 * the kernel.  It is therefore started from inside a software timer callback
 * function, which will not execute until the timer service/daemon task is
 * executing.  A one-shot timer is used, so the callback function will only
 * execute once (unless it is manually reset/restarted).
 */
static void prvSetupHighFrequencyTimerTest( TimerHandle_t xTimer );

/*
 * Tasks that test the context switch mechanism by filling the processor
 * registers with known values, then checking that the values contained
 * within the registers is as expected.  The tasks are likely to get swapped
 * in and out between setting the register values and checking the register
 * values.
 */
static void prvRegTestTask1( void *pvParameters );
static void prvRegTestTask2( void *pvParameters );

/*
 * LED toggle function that uses a critical section to ensure thread safety.
 */
extern void vToggleLED( uint8_t ucLED );

/*-----------------------------------------------------------*/

/* Variables incremented by prvRegTestTask1() and prvRegTestTask2() respectively
on each iteration of their function.  These are used to detect errors in the
reg test tasks. */
volatile unsigned long ulRegTest1Cycles = 0, ulRegTest2Cycles = 0;

/*-----------------------------------------------------------*/

/*
 * Create the demo tasks then start the scheduler.
 */
int main_full( void )
{
TimerHandle_t xTimer = NULL;

	/* Create all the other standard demo tasks. */
	vCreateBlockTimeTasks();
	vStartSemaphoreTasks( mainSEM_TEST_PRIORITY );
	vStartGenericQueueTasks( mainGEN_QUEUE_TASK_PRIORITY );
	vStartInterruptQueueTasks();
	vStartCountingSemaphoreTasks();

	/* Create the tasks defined within this file. */
	xTaskCreate( prvRegTestTask1,			/* The function that implements the task. */
				"Reg1",						/* Text name for the task to assist debugger - not used by FreeRTOS itself. */
				configMINIMAL_STACK_SIZE,	/* The stack size to allocate for the task - specified in words not bytes. */
				NULL,						/* The parameter to pass into the task - not used in this case so set to NULL. */
				tskIDLE_PRIORITY,			/* The priority to assign to the task. */
				NULL );						/* Used to obtain a handle to the task being created - not used in this case so set to NULL. */

	xTaskCreate( prvRegTestTask2, "Reg2", configMINIMAL_STACK_SIZE, NULL, tskIDLE_PRIORITY, NULL );

	/* Create the software timer that performs the 'check' functionality, as
	described at the top of this file. */
	xTimer = xTimerCreate( 	"CheckTimer",/* A text name, purely to help debugging. */
							( mainCHECK_TIMER_PERIOD_MS ),		/* The timer period, in this case 3000ms (3s). */
							pdTRUE,								/* This is an auto-reload timer, so xAutoReload is set to pdTRUE. */
							( void * ) 0,						/* The ID is not used, so can be set to anything. */
							prvCheckTimerCallback );			/* The callback function that inspects the status of all the other tasks. */

	if( xTimer != NULL )
	{
		xTimerStart( xTimer, mainDONT_BLOCK );
	}

	/* A software timer is also used to start the high frequency timer test.
	This is to ensure the test does not start before the kernel.  This time a
	one-shot software timer is used. */
	xTimer = xTimerCreate( "HighHzTimerSetup", 1, pdFALSE, ( void * ) 0, prvSetupHighFrequencyTimerTest );
	if( xTimer != NULL )
	{
		xTimerStart( xTimer, mainDONT_BLOCK );
	}

	/* Finally start the scheduler. */
	vTaskStartScheduler();

	/* If all is well, the scheduler will now be running, and the following line
	will never be reached.  If the following line does execute, then there was
	insufficient FreeRTOS heap memory available for the idle and/or timer tasks
	to be created.  See the memory management section on the FreeRTOS web site
	for more details.  http://www.freertos.org/a00111.html */
	for( ;; );
}
/*-----------------------------------------------------------*/

static void prvRegTestTask1( void *pvParameters )
{
extern void vRegTest1( volatile unsigned long * );

	/* Avoid compiler warnings. */
	( void ) pvParameters;

	/* Pass the address of the RegTest1 loop counter into the test function,
	which is necessarily implemented in assembler. */
	vRegTest1( &ulRegTest1Cycles );

	/* vRegTest1 should never exit! */
	vTaskDelete( NULL );
}
/*-----------------------------------------------------------*/

static void prvRegTestTask2( void *pvParameters )
{
extern void vRegTest2( volatile unsigned long * );

	/* Avoid compiler warnings. */
	( void ) pvParameters;

	/* Pass the address of the RegTest2 loop counter into the test function,
	which is necessarily implemented in assembler. */
	vRegTest2( &ulRegTest2Cycles );

	/* vRegTest1 should never exit! */
	vTaskDelete( NULL );
}
/*-----------------------------------------------------------*/

static void prvCheckTimerCallback( TimerHandle_t xTimer )
{
static long lChangedTimerPeriodAlready = pdFALSE;
static unsigned long ulLastRegTest1Value = 0, ulLastRegTest2Value = 0, ulLastHighFrequencyTimerInterrupts = 0;
static const unsigned long ulExpectedHighFrequencyInterrupts = ( ( mainTEST_INTERRUPT_FREQUENCY / 1000UL ) * mainCHECK_TIMER_PERIOD_MS ) - 10; /* 10 allows for a margin of error. */
unsigned long ulErrorOccurred = pdFALSE;
/* The count of the high frequency timer interrupts. */
extern unsigned long ulHighFrequencyTimerInterrupts;

	/* Avoid compiler warnings. */
	( void ) xTimer;

	/* Check that the register test 1 task is still running. */
	if( ulLastRegTest1Value == ulRegTest1Cycles )
	{
		ulErrorOccurred |= ( 0x01UL << 1UL );
	}
	ulLastRegTest1Value = ulRegTest1Cycles;

	/* Check that the register test 2 task is still running. */
	if( ulLastRegTest2Value == ulRegTest2Cycles )
	{
		ulErrorOccurred |= ( 0x01UL << 2UL );
	}
	ulLastRegTest2Value = ulRegTest2Cycles;

	/* Have any of the standard demo tasks detected an error in their
	operation? */
	if( xAreGenericQueueTasksStillRunning() != pdTRUE )
	{
		ulErrorOccurred |= ( 0x01UL << 3UL );
	}
	else if( xAreBlockTimeTestTasksStillRunning() != pdTRUE )
	{
		ulErrorOccurred |= ( 0x01UL << 4UL );
	}
	else if( xAreSemaphoreTasksStillRunning() != pdTRUE )
	{
		ulErrorOccurred |= ( 0x01UL << 5UL );
	}
	else if( xAreIntQueueTasksStillRunning() != pdTRUE )
	{
		ulErrorOccurred |= ( 0x01UL << 6UL );
	}
	else if( xAreCountingSemaphoreTasksStillRunning() != pdTRUE )
	{
		ulErrorOccurred |= ( 0x01UL << 7UL );
	}

	/* Ensure the expected number of high frequency interrupts have occurred. */
	if( ulLastHighFrequencyTimerInterrupts != 0 )
	{
		if( ( ulHighFrequencyTimerInterrupts - ulLastHighFrequencyTimerInterrupts ) < ulExpectedHighFrequencyInterrupts )
		{
			ulErrorOccurred |= ( 0x01UL << 8UL );
		}
	}
	ulLastHighFrequencyTimerInterrupts = ulHighFrequencyTimerInterrupts;

	if( ulErrorOccurred != pdFALSE )
	{
		/* An error occurred.  Increase the frequency at which the check timer
		toggles its LED to give visual feedback of the potential error
		condition. */
		if( lChangedTimerPeriodAlready == pdFALSE )
		{
			lChangedTimerPeriodAlready = pdTRUE;

			/* This call to xTimerChangePeriod() uses a zero block time.
			Functions called from inside of a timer callback function must
			*never* attempt	to block as to do so could impact other software
			timers. */
			xTimerChangePeriod( xTimer, ( mainERROR_CHECK_TIMER_PERIOD_MS ), mainDONT_BLOCK );
		}
	}

	vToggleLED( mainCHECK_LED );
}
/*-----------------------------------------------------------*/

static void prvSetupHighFrequencyTimerTest( TimerHandle_t xTimer )
{
void vSetupTimerTest( unsigned short usFrequencyHz );

	/* Prevent compiler warnings */
	(void) xTimer;

	/* Setup the high frequency, high priority, timer test.  It is setup in this
	software timer callback to ensure it does not start before the kernel does.
	This is a one-shot timer - so the setup routine will only be executed once. */

	vSetupTimerTest( mainTEST_INTERRUPT_FREQUENCY );
}
/*-----------------------------------------------------------*/

