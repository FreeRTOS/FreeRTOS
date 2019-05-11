/*
 * FreeRTOS Kernel V10.2.1
 * Copyright (C) 2019 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 * main_full() creates a set of standard demo tasks, some application specific
 * tasks, and a timer.  It then starts the scheduler.  The web documentation
 * provides more details of the standard demo application tasks, which provide
 * no particular functionality, but do provide a good example of how to use the
 * FreeRTOS API.
 *
 * In addition to the standard demo tasks, the following tasks and timer are
 * defined and/or created within this file:
 *
 * "Command console task" - This uses the Atmel USART driver to provide the
 * input and output to FreeRTOS+CLI - the FreeRTOS Command Line Interface.  To
 * use the CLI:
 *  - Power the SAMD20 XPlained board through the USB debugger connector.  This
 *    will create a virtual COM port through the USB.
 *  - Build and run the demo application.  
 *  - Start a dumb terminal program such as TerraTerm or Hyper Terminal.
 *  - In the dumb terminal select the UART port associated with the XPlained
 *    debugger connection, using 19200 baud.
 *  - Type 'help' in the terminal window to see a lit of command registered by
 *    the demo.
 *
 * "Reg test" tasks - These fill the registers with known values, then check
 * that each register maintains its expected value for the lifetime of the
 * task.  Each task uses a different set of values.  The reg test tasks execute
 * with a very low priority, so get preempted very frequently.  A register
 * containing an unexpected value is indicative of an error in the context
 * switching mechanism.
 *
 * "Check" software timer - The check timer period is initially set to three
 * seconds.  Its callback function checks that all the standard demo tasks, and
 * the register check tasks, are not only still executing, but are executing
 * without reporting any errors.  If the check timer callback discovers that a
 * task has either stalled, or reported an error, then it changes the period of
 * the check timer from the initial three seconds, to just 200ms.  The callback
 * function also toggles the LED each time it is called.  This provides a
 * visual indication of the system status:  If the LED toggles every three
 * seconds then no issues have been discovered.  If the LED toggles every 200ms,
 * then an issue has been discovered with at least one task.
 */

/* Kernel includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"
#include "semphr.h"
#include "timers.h"

/* Common demo includes. */
#include "blocktim.h"
#include "countsem.h"
#include "recmutex.h"
#include "ParTest.h"
#include "dynamic.h"
#include "QueueOverwrite.h"
#include "QueueSet.h"
#include "GenQTest.h"
#include "QPeek.h"

/* The period after which the check timer will expire provided no errors have
been reported by any of the standard demo tasks.  ms are converted to the
equivalent in ticks using the portTICK_PERIOD_MS constant. */
#define mainCHECK_TIMER_PERIOD_MS			( 3000UL / portTICK_PERIOD_MS )

/* The period at which the check timer will expire if an error has been
reported in one of the standard demo tasks.  ms are converted to the equivalent
in ticks using the portTICK_PERIOD_MS constant. */
#define mainERROR_CHECK_TIMER_PERIOD_MS 	( 200UL / portTICK_PERIOD_MS )

/* A block time of zero simply means "don't block". */
#define mainDONT_BLOCK						( 0UL )


/*-----------------------------------------------------------*/

/*
 * Register check tasks, as described at the top of this file.  The nature of
 * these files necessitates that they are written in an assembly.
 */
extern void vRegTest1Task( void *pvParameters );
extern void vRegTest2Task( void *pvParameters );

/*
 * Function that starts the command console task.
 */
extern void vUARTCommandConsoleStart( uint16_t usStackSize, unsigned portBASE_TYPE uxPriority );

/*
 * The check timer callback function, as described at the top of this file.
 */
static void prvCheckTimerCallback( TimerHandle_t xTimer );

/*
 * Called by main() to create the comprehensive test/demo application if
 * mainCREATE_SIMPLE_BLINKY_DEMO_ONLY is not set to 1.
 */
void main_full( void );

/*-----------------------------------------------------------*/

/* The following two variables are used to communicate the status of the
register check tasks to the check software timer.  If the variables keep
incrementing, then the register check tasks have not discovered any errors.  If
a variable stops incrementing, then an error has been found. */
volatile unsigned long ulRegTest1LoopCounter = 0UL, ulRegTest2LoopCounter = 0UL;

/*-----------------------------------------------------------*/

void main_full( void )
{
TimerHandle_t xTimer = NULL;

/* The register test tasks are asm functions that don't use a stack.  The
stack allocated just has to be large enough to hold the task context, and
for the additional required for the stack overflow checking to work (if
configured). */
const size_t xRegTestStackSize = 25U;

	/* Create the standard demo tasks */
	vCreateBlockTimeTasks();
	vStartDynamicPriorityTasks();
	vStartCountingSemaphoreTasks();
	vStartRecursiveMutexTasks();
	vStartQueueOverwriteTask( tskIDLE_PRIORITY );
	vStartQueueSetTasks();
	vStartGenericQueueTasks( tskIDLE_PRIORITY );
	vStartQueuePeekTasks();
	
	/* Start the task that manages the command console for FreeRTOS+CLI. */
	vUARTCommandConsoleStart( ( configMINIMAL_STACK_SIZE * 3 ), tskIDLE_PRIORITY );	

	/* Create the register test tasks as described at the top of this file.
	These are naked functions that don't use any stack.  A stack still has
	to be allocated to hold the task context. */
	xTaskCreate( 	vRegTest1Task,			/* Function that implements the task. */
					"Reg1",					/* Text name of the task. */
					xRegTestStackSize,		/* Stack allocated to the task. */
					NULL, 					/* The task parameter is not used. */
					tskIDLE_PRIORITY, 		/* The priority to assign to the task. */
					NULL );					/* Don't receive a handle back, it is not needed. */

	xTaskCreate( 	vRegTest2Task,			/* Function that implements the task. */
					"Reg2",					/* Text name of the task. */
					xRegTestStackSize,		/* Stack allocated to the task. */
					NULL, 					/* The task parameter is not used. */
					tskIDLE_PRIORITY, 		/* The priority to assign to the task. */
					NULL );					/* Don't receive a handle back, it is not needed. */

	/* Create the software timer that performs the 'check' functionality,
	as described at the top of this file. */
	xTimer = xTimerCreate( 	"CheckTimer",						/* A text name, purely to help debugging. */
							( mainCHECK_TIMER_PERIOD_MS ),		/* The timer period, in this case 3000ms (3s). */
							pdTRUE,								/* This is an auto-reload timer, so xAutoReload is set to pdTRUE. */
							( void * ) 0,						/* The ID is not used, so can be set to anything. */
							prvCheckTimerCallback				/* The callback function that inspects the status of all the other tasks. */
					  	);

	/* If the software timer was created successfully, start it.  It won't
	actually start running until the scheduler starts.  A block time of
	zero is used in this call, although any value could be used as the block
	time will be ignored because the scheduler has not started yet. */
	configASSERT( xTimer );
	if( xTimer != NULL )
	{
		xTimerStart( xTimer, mainDONT_BLOCK );
	}

	/* Start the kernel.  From here on, only tasks and interrupts will run. */
	vTaskStartScheduler();

	/* If all is well, the scheduler will now be running, and the following
	line will never be reached.  If the following line does execute, then there
	was	insufficient FreeRTOS heap memory available for the idle and/or timer
	tasks to be created.  See the memory management section on the FreeRTOS web
	site, or the FreeRTOS tutorial books for more details. */
	for( ;; );
}
/*-----------------------------------------------------------*/

/* See the description at the top of this file. */
static void prvCheckTimerCallback( TimerHandle_t xTimer )
{
static long lChangedTimerPeriodAlready = pdFALSE;
static unsigned long ulLastRegTest1Value = 0, ulLastRegTest2Value = 0;
unsigned long ulErrorFound = pdFALSE;

	/* Check all the demo and test tasks to ensure that they are all still
	running, and that none have detected an error. */
	if( xAreDynamicPriorityTasksStillRunning() != pdPASS )
	{
		ulErrorFound = pdTRUE;
	}

	if( xAreBlockTimeTestTasksStillRunning() != pdPASS )
	{
		ulErrorFound = pdTRUE;
	}

	if( xAreCountingSemaphoreTasksStillRunning() != pdPASS )
	{
		ulErrorFound = pdTRUE;
	}

	if( xAreRecursiveMutexTasksStillRunning() != pdPASS )
	{
		ulErrorFound = pdTRUE;
	}

	/* Check that the register test 1 task is still running. */
	if( ulLastRegTest1Value == ulRegTest1LoopCounter )
	{
		ulErrorFound = pdTRUE;
	}
	ulLastRegTest1Value = ulRegTest1LoopCounter;

	/* Check that the register test 2 task is still running. */
	if( ulLastRegTest2Value == ulRegTest2LoopCounter )
	{
		ulErrorFound = pdTRUE;
	}
	ulLastRegTest2Value = ulRegTest2LoopCounter;

	
	if( xAreQueueSetTasksStillRunning() != pdPASS )
	{
		ulErrorFound = pdTRUE;
	}

	if( xIsQueueOverwriteTaskStillRunning() != pdPASS )
	{
		ulErrorFound = pdTRUE;
	}
	
	if( xAreGenericQueueTasksStillRunning() != pdPASS )
	{
		ulErrorFound = pdTRUE;
	}
	
	if( xAreQueuePeekTasksStillRunning() != pdPASS )
	{
		ulErrorFound = pdTRUE;
	}

	/* Toggle the check LED to give an indication of the system status.  If
	the LED toggles every mainCHECK_TIMER_PERIOD_MS milliseconds then
	everything is ok.  A faster toggle indicates an error. */
	port_pin_toggle_output_level( LED_0_PIN );

	/* Have any errors been latched in ulErrorFound?  If so, shorten the
	period of the check timer to mainERROR_CHECK_TIMER_PERIOD_MS milliseconds.
	This will result in an increase in the rate at which the LED toggles. */
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

