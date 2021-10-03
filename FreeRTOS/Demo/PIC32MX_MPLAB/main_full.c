/*
 * FreeRTOS V202107.00
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
 ******************************************************************************
 *
 * main_full() creates all the demo application tasks and software timers, then
 * starts the scheduler.  The WEB documentation provides more details of the
 * standard demo application tasks.  In addition to the standard demo tasks, the
 * following tasks and tests are defined and/or created within this file:
 *
 * "LCD" task - the LCD task is a 'gatekeeper' task.  It is the only task that
 * is permitted to access the display directly.  Other tasks wishing to write a
 * message to the LCD send the message on a queue to the LCD task instead of
 * accessing the LCD themselves.  The LCD task just blocks on the queue waiting
 * for messages - waking and displaying the messages as they arrive.
 * **NOTE** The LCD driver has a dependency on the PLIB library, which is no
 * longer provided by Microchip, so LCD functionality has been removed from this
 * demo - however the source files remain in the distribution.
 *
 * "Check" timer - The check software timer period is initially set to three
 * seconds.  The callback function associated with the check software timer
 * checks that all the standard demo tasks, and the register check tasks, are
 * not only still executing, but are executing without reporting any errors.  If
 * the check software timer discovers that a task has either stalled, or
 * reported an error, then it changes its own execution period from the initial
 * three seconds, to just 200ms.  The check software timer callback function
 * also writes a status message to the LCD (via the LCD task).  If all the demo
 * tasks are executing with their expected behaviour then the check task writes
 * a count of the number of times the high frequency interrupt has incremented
 * ulHighFrequencyTimerInterrupts - which is one in every 20,000 interrupts.
 *
 * "Register test" tasks - These tasks are used in part to test the kernel port.
 * They set each processor register to a known value, then check that the
 * register still contains that value.  Each of the tasks sets the registers
 * to different values, and will get swapping in and out between setting and
 * then subsequently checking the register values.  Discovery of an incorrect
 * value would be indicative of an error in the task switching mechanism.
 *
 * By way of demonstration, the demo application defines
 * configMAX_SYSCALL_INTERRUPT_PRIORITY to be 3, configKERNEL_INTERRUPT_PRIORITY
 * to be 1, and all other interrupts as follows:
 *
 *	+ The UART is allocated a priority of 2. This means it can interrupt the
 *    RTOS tick, and can also safely use queues.
 *    **NOTE** The UART driver has a dependency on the PLIB library, which is no
 *    longer provided by Microchip, so UART functionality has been removed from
 *    this demo - however the source files remain in the distribution.
 *
 *  + Two timers are configured to generate interrupts just to test the nesting
 *    and queue access mechanisms. These timers are allocated priorities 2 and 3
 *    respectively. Even though they both access the same two queues, the
 *    priority 3 interrupt can safely interrupt the priority 2 interrupt. Both
 *    can interrupt the RTOS tick.
 *  + Finally a high frequency timer interrupt is configured to use priority 4 -
 *    therefore kernel activity will never prevent the high frequency timer from
 *    executing immediately that the interrupt is raised (within the limitations
 *    of the hardware itself). It would not be safe to access a queue from this
 *    interrupt as it is above configMAX_SYSCALL_INTERRUPT_PRIORITY.
 *
 * See the online documentation for this demo for more information on interrupt
 * usage.
 */

/* Standard includes. */
#include <stdio.h>

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"
#include "timers.h"

/* Demo application includes. */
#include "partest.h"
#include "blocktim.h"
#include "flash_timer.h"
#include "semtest.h"
#include "GenQTest.h"
#include "QPeek.h"
#include "lcd.h"
#include "timertest.h"
#include "IntQueue.h"

/*-----------------------------------------------------------*/

/* The period after which the check timer will expire, in ms, provided no errors
have been reported by any of the standard demo tasks.  ms are converted to the
equivalent in ticks using the portTICK_PERIOD_MS constant. */
#define mainCHECK_TIMER_PERIOD_MS			( 3000UL / portTICK_PERIOD_MS )

/* The period at which the check timer will expire, in ms, if an error has been
reported in one of the standard demo tasks.  ms are converted to the equivalent
in ticks using the portTICK_PERIOD_MS constant. */
#define mainERROR_CHECK_TIMER_PERIOD_MS 	( 200UL / portTICK_PERIOD_MS )

/* The priorities of the various demo application tasks. */
#define mainSEM_TEST_PRIORITY				( tskIDLE_PRIORITY + 1 )
#define mainBLOCK_Q_PRIORITY				( tskIDLE_PRIORITY + 2 )
#define mainCOM_TEST_PRIORITY				( tskIDLE_PRIORITY + 2 )
#define mainINTEGER_TASK_PRIORITY           ( tskIDLE_PRIORITY )
#define mainGEN_QUEUE_TASK_PRIORITY			( tskIDLE_PRIORITY )

/* Misc. */
#define mainDONT_BLOCK						( 0 )

/* Dimension the buffer used to hold the value of the high frequency timer
count when it is converted to a string. */
#define mainMAX_STRING_LENGTH				( 20 )

/* The frequency at which the "fast interrupt test" interrupt will occur. */
#define mainTEST_INTERRUPT_FREQUENCY		( 20000 )

/* The number of timer clocks expected to occur between each "fast interrupt
test" interrupt. */
#define mainEXPECTED_CLOCKS_BETWEEN_INTERRUPTS ( ( configCPU_CLOCK_HZ >> 1 ) / mainTEST_INTERRUPT_FREQUENCY )

/* The number of nano seconds between each core clock. */
#define mainNS_PER_CLOCK ( ( unsigned long ) ( ( 1.0 / ( double ) ( configCPU_CLOCK_HZ >> 1 ) ) * 1000000000.0 ) )

/* The number of LEDs that should be controlled by the flash software timer
standard demo and the LED to be toggle by the check task.  The starter kit only
has three LEDs so when the demo is configured to run on the starter kit there
is one less flash timer so the check task can use the third LED. */
#ifdef PIC32_STARTER_KIT
	#define mainNUM_FLASH_TIMER_LEDS			( 2 )
	#define mainCHECK_LED						( 2 )
#else
	#define mainNUM_FLASH_TIMER_LEDS			( 3 )
	#define mainCHECK_LED						( 7 )
#endif

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

/*-----------------------------------------------------------*/

/* The queue used to send messages to the LCD task. */
static QueueHandle_t xLCDQueue;

/* Variables incremented by prvRegTestTask1() and prvRegTestTask2() respectively on
each iteration of their function.  This is used to detect either task stopping
their execution.. */
volatile unsigned long ulRegTest1Cycles = 0, ulRegTest2Cycles = 0;

/*-----------------------------------------------------------*/

/*
 * Create the demo tasks then start the scheduler.
 */
int main_full( void )
{
TimerHandle_t xTimer = NULL;

	/* Create all the other standard demo tasks. */
	vStartLEDFlashTimers( mainNUM_FLASH_TIMER_LEDS );
    vCreateBlockTimeTasks();
    vStartSemaphoreTasks( mainSEM_TEST_PRIORITY );
    vStartGenericQueueTasks( mainGEN_QUEUE_TASK_PRIORITY );
    vStartQueuePeekTasks();
	vStartInterruptQueueTasks();

	/* Create the tasks defined within this file. */
	xTaskCreate( prvRegTestTask1, "Reg1", configMINIMAL_STACK_SIZE, NULL, tskIDLE_PRIORITY, NULL );
	xTaskCreate( prvRegTestTask2, "Reg2", configMINIMAL_STACK_SIZE, NULL, tskIDLE_PRIORITY, NULL );

	/* Create the software timer that performs the 'check' functionality, as
	described at the top of this file. */
	xTimer = xTimerCreate( 	"CheckTimer",/* A text name, purely to help debugging. */
							( mainCHECK_TIMER_PERIOD_MS ),		/* The timer period, in this case 3000ms (3s). */
							pdTRUE,								/* This is an auto-reload timer, so xAutoReload is set to pdTRUE. */
							( void * ) 0,						/* The ID is not used, so can be set to anything. */
							prvCheckTimerCallback				/* The callback function that inspects the status of all the other tasks. */
						);

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
	for more details. */
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
static unsigned long ulLastRegTest1Value = 0, ulLastRegTest2Value = 0;

/* Buffer into which the high frequency timer count is written as a string. */
static char cStringBuffer[ mainMAX_STRING_LENGTH ];

/* The count of the high frequency timer interrupts. */
extern unsigned long ulHighFrequencyTimerInterrupts;
static xLCDMessage xMessage = { ( 200 / portTICK_PERIOD_MS ), cStringBuffer };

	/* Check that the register test 1 task is still running. */
	if( ulLastRegTest1Value == ulRegTest1Cycles )
	{
		xMessage.pcMessage = "Error: Reg test2";
	}
	ulLastRegTest1Value = ulRegTest1Cycles;


	/* Check that the register test 2 task is still running. */
	if( ulLastRegTest2Value == ulRegTest2Cycles )
	{
		xMessage.pcMessage = "Error: Reg test3";
	}
	ulLastRegTest2Value = ulRegTest2Cycles;


	/* Have any of the standard demo tasks detected an error in their
	operation? */
	if( xAreGenericQueueTasksStillRunning() != pdTRUE )
	{
		xMessage.pcMessage = "Error: Gen Q";
	}
	else if( xAreQueuePeekTasksStillRunning() != pdTRUE )
	{
		xMessage.pcMessage = "Error: Q Peek";
	}
	else if( xAreBlockTimeTestTasksStillRunning() != pdTRUE )
	{
		xMessage.pcMessage = "Error: Blck time";
	}
	else if( xAreSemaphoreTasksStillRunning() != pdTRUE )
	{
		xMessage.pcMessage = "Error: Sem test";
	}
	else if( xAreIntQueueTasksStillRunning() != pdTRUE )
	{
		xMessage.pcMessage = "Error: Int queue";
	}

	if( xMessage.pcMessage != cStringBuffer )
	{
		/* An error string has been logged.  If the timer period has not yet
		been changed it should be changed now.  Increasing the frequency of the
		LED gives visual feedback of the error status. */
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
	else
	{
		/* Write the ulHighFrequencyTimerInterrupts value to the string
		buffer.  It will only be displayed if no errors have been detected. */
		sprintf( cStringBuffer, "Pass %u", ( unsigned int ) ulHighFrequencyTimerInterrupts );
	}

	vParTestToggleLED( mainCHECK_LED );
}
/*-----------------------------------------------------------*/

static void prvSetupHighFrequencyTimerTest( TimerHandle_t xTimer )
{
	/* Setup the high frequency, high priority, timer test.  It is setup in this
	software timer callback to ensure it does not start before the kernel does.
	This is a one-shot timer - so the setup routine will only be executed once. */
	vSetupTimerTest( mainTEST_INTERRUPT_FREQUENCY );
}

