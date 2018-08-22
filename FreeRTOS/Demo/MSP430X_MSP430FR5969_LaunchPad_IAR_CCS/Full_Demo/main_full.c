/*
 * FreeRTOS Kernel V10.1.0
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
 * "Reg test" tasks - These fill both the microcontroller registers with known
 * values, then check that each register maintains its expected value for the
 * lifetime of the task.  Each task uses a different set of values.  The reg
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
#include "dynamic.h"
#include "blocktim.h"
#include "countsem.h"
#include "GenQTest.h"
#include "recmutex.h"
#include "partest.h"
#include "EventGroupsDemo.h"
#include "TaskNotify.h"

/* Priorities for the check task, as described at the top of this file. */
#define mainCHECK_TASK_PRIORITY				( configMAX_PRIORITIES - 1 )

/* Parameters for the task that handles the UART command console. */
#define mainCOMMAND_CONSOLE_TASK_PRIORITY	( tskIDLE_PRIORITY )
#define mainCOMMAND_CONSOLE_STACK_SIZE		( configMINIMAL_STACK_SIZE * 2 )

/* The LED used by the check timer as described at the top of this file. */
#define mainCHECK_LED						( 0 )

/* The period after which the check timer will expire, in ms, provided no errors
have been reported by any of the standard demo tasks.  ms are converted to the
equivalent in ticks using the pdMS_TO_TICKS() macro. */
#define mainNO_ERROR_CHECK_TASK_PERIOD		pdMS_TO_TICKS( 3000 )

/* The period at which the check timer will expire, in ms, if an error has been
reported in one of the standard demo tasks.  ms are converted to the equivalent
in ticks using the pdMS_TO_TICKS() macro. */
#define mainERROR_CHECK_TASK_PERIOD 		pdMS_TO_TICKS( 200 )

/* Parameters that are passed into the register check tasks solely for the
purpose of ensuring parameters are passed into tasks correctly. */
#define mainREG_TEST_TASK_1_PARAMETER		( ( void * ) 0x1234 )
#define mainREG_TEST_TASK_2_PARAMETER		( ( void * ) 0x8765 )

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
 * Register check tasks, as described at the top of this file.  The nature of
 * these files necessitates that they are written in an assembly file, but the
 * entry points are kept in the C file for the convenience of checking the task
 * parameter.
 */
static void prvRegTestTaskEntry1( void *pvParameters );
extern void vRegTest1Implementation( void );
static void prvRegTestTaskEntry2( void *pvParameters );
extern void vRegTest2Implementation( void );

/* Starts the 'standard' UART command console task.  UART 0 is used at 19200
baud. */
extern void vUARTCommandConsoleStart( uint16_t usStackSize, UBaseType_t uxPriority );

/* Registers a set of example commands that can be used in the command
console. */
void vRegisterSampleCLICommands( void );

/*-----------------------------------------------------------*/

/* The following two variables are used to communicate the status of the
register check tasks to the check task.  If the variables keep incrementing,
then the register check tasks have not discovered any errors.  If a variable
stops incrementing, then an error has been found. */
volatile uint16_t usRegTest1LoopCounter = 0UL, usRegTest2LoopCounter = 0UL;

/* cOutputBuffer is used by FreeRTOS+CLI.  It is declared here so the
persistent qualifier can be used.  For the buffer to be declared here, rather
than in FreeRTOS_CLI.c, configAPPLICATION_PROVIDES_cOutputBuffer must be set to
1 in FreeRTOSConfig.h. */
#ifdef __ICC430__
	__persistent 							/* IAR version. */
#else
	#pragma PERSISTENT( cOutputBuffer ) 	/* CCS version. */
#endif
char cOutputBuffer[ configCOMMAND_INT_MAX_OUTPUT_SIZE ] = { 0 };

/* Used for maintaining a 32-bit run time stats counter from a 16-bit timer. */
volatile uint32_t ulRunTimeCounterOverflows = 0;

/*-----------------------------------------------------------*/

void main_full( void )
{
	/* Start all the standard demo/test tasks.  They have no particular
	functionality, but do demonstrate how to use the FreeRTOS API and test the
	kernel port. */
	vStartDynamicPriorityTasks();
	vCreateBlockTimeTasks();
	vStartCountingSemaphoreTasks();
	vStartGenericQueueTasks( tskIDLE_PRIORITY );
	vStartRecursiveMutexTasks();
	vStartEventGroupTasks();
	vStartTaskNotifyTask();

	/* Create the register check tasks, as described at the top of this	file */
	xTaskCreate( prvRegTestTaskEntry1, 			/* Task entry point. */
				 "Reg1", 						/* Text name for the task - not used by the kernel. */
				 configMINIMAL_STACK_SIZE, 		/* Stack to allocate to the task - in words not bytes! */
				 mainREG_TEST_TASK_1_PARAMETER, /* The parameter passed into the task. */
				 tskIDLE_PRIORITY, 				/* The task's priority. */
				 NULL );						/* Task handle is not needed, so NULL is passed. */

	xTaskCreate( prvRegTestTaskEntry2, "Reg2", configMINIMAL_STACK_SIZE, mainREG_TEST_TASK_2_PARAMETER, tskIDLE_PRIORITY, NULL );

	/* Create the task that performs the 'check' functionality, as described at
	the top of this file. */
	xTaskCreate( prvCheckTask, "Check", configMINIMAL_STACK_SIZE, NULL, mainCHECK_TASK_PRIORITY, NULL );

	/* Register an example set of CLI commands, then start the task that manages
	the CLI using a UART for input and output. */
	vRegisterSampleCLICommands();
	vUARTCommandConsoleStart( mainCOMMAND_CONSOLE_STACK_SIZE, mainCOMMAND_CONSOLE_TASK_PRIORITY );

	/* Start the scheduler. */
	vTaskStartScheduler();

	/* If all is well, the scheduler will now be running, and the following
	line will never be reached.  If the following line does execute, then
	there was either insufficient FreeRTOS heap memory available for the idle
	and/or timer tasks to be created.  See the memory management section on the
	FreeRTOS web site for more details on the FreeRTOS heap
	http://www.freertos.org/a00111.html. */
	for( ;; );
}
/*-----------------------------------------------------------*/

static void prvCheckTask( void *pvParameters )
{
TickType_t xDelayPeriod = mainNO_ERROR_CHECK_TASK_PERIOD;
TickType_t xLastExecutionTime;
static uint16_t usLastRegTest1Value = 0, usLastRegTest2Value = 0;
uint16_t usErrorFound = pdFALSE;

	/* Just to stop compiler warnings. */
	( void ) pvParameters;

	/* Initialise xLastExecutionTime so the first call to vTaskDelayUntil()
	works correctly. */
	xLastExecutionTime = xTaskGetTickCount();

	/* Cycle for ever, delaying then checking all the other tasks are still
	operating without error.  An on-board LED is toggled on each iteration.
	If an error is detected then the delay period is decreased from
	mainNO_ERROR_CHECK_TASK_PERIOD to mainERROR_CHECK_TASK_PERIOD.  This has the
	effect of increasing the rate at which the on-board LED toggles, and in so
	doing gives visual feedback of the system status. */
	for( ;; )
	{
		/* Delay until it is time to execute again. */
		vTaskDelayUntil( &xLastExecutionTime, xDelayPeriod );

		/* Check all the demo tasks to ensure they are all still running, and
		that none have detected an error. */
		if( xAreDynamicPriorityTasksStillRunning() != pdTRUE )
		{
			usErrorFound = 1UL << 0UL;
		}

		if ( xAreBlockTimeTestTasksStillRunning() != pdTRUE )
		{
			usErrorFound = 1UL << 1UL;
		}

		if ( xAreGenericQueueTasksStillRunning() != pdTRUE )
		{
			usErrorFound = 1UL << 2UL;
		}

		if ( xAreRecursiveMutexTasksStillRunning() != pdTRUE )
		{
			usErrorFound = 1UL << 3UL;
		}

		if( xAreCountingSemaphoreTasksStillRunning() != pdTRUE )
		{
			usErrorFound = 1UL << 4UL;
		}

		if( xAreEventGroupTasksStillRunning() != pdPASS )
		{
			usErrorFound = 1UL << 5UL;
		}

		if( xAreTaskNotificationTasksStillRunning() != pdPASS )
		{
			usErrorFound = 1UL << 6UL;
		}

		/* Check that the register test 1 task is still running. */
		if( usLastRegTest1Value == usRegTest1LoopCounter )
		{
			usErrorFound = 1UL << 7UL;
		}
		usLastRegTest1Value = usRegTest1LoopCounter;

		/* Check that the register test 2 task is still running. */
		if( usLastRegTest2Value == usRegTest2LoopCounter )
		{
			usErrorFound = 1UL << 8UL;
		}
		usLastRegTest2Value = usRegTest2LoopCounter;

		/* Toggle the check LED to give an indication of the system status.  If
		the LED toggles every mainNO_ERROR_CHECK_TASK_PERIOD milliseconds then
		everything is ok.  A faster toggle indicates an error. */
		vParTestToggleLED( mainCHECK_LED );

		if( usErrorFound != pdFALSE )
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

void vConfigureTimerForRunTimeStats( void )
{
	/* Configure a timer that is used as the time base for run time stats.  See
	http://www.freertos.org/rtos-run-time-stats.html */

	/* Ensure the timer is stopped. */
	TA1CTL = 0;

	/* Start up clean. */
	TA1CTL |= TACLR;

	/* Run the timer from the ACLK/8, continuous mode, interrupt enable. */
	TA1CTL = TASSEL_1 | ID__8 | MC__CONTINUOUS | TAIE;
}
/*-----------------------------------------------------------*/

#pragma vector=TIMER1_A1_VECTOR
__interrupt void v4RunTimeStatsTimerOverflow( void )
{
	TA1CTL &= ~TAIFG;
	
	/* 16-bit overflow, so add 17th bit. */
	ulRunTimeCounterOverflows += 0x10000;
	__bic_SR_register_on_exit( SCG1 + SCG0 + OSCOFF + CPUOFF );
}




