/*
 * FreeRTOS Kernel V10.0.1
 * Copyright (C) 2017 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 * NOTE:  This file only contains the source code that is specific to the
 * basic demo.  Generic functions, such FreeRTOS hook functions, are defined
 * in main.c.
 ******************************************************************************
 *
 * main_full() creates all the demo application tasks, then starts the scheduler.
 * The web documentation provides more details of the standard demo application
 * tasks, which provide no particular functionality but do provide a good
 * example of how to use the FreeRTOS API.
 *
 * In addition to the standard demo tasks, the following tasks and tests are
 * defined and/or created within this file:
 *
 * "Register tests":
 * prvRegTest1Task and prvRegTest2Task implement register tests. These functions
 * are just entry points and actual tests are written in the assembler file
 * regtest_xtensa.S. These tests populate core registers with a known set of
 * values and keep verifying them in a loop. Any corruption will indicate an
 * error in context switching mechanism.
 *
 * "Check" task:
 * This only executes every five seconds but has a high priority to ensure it
 * gets processor time. Its main function is to check that all the standard demo
 * tasks are still operational. While no errors have been discovered the check
 * task will print out "No errors", the current simulated tick time, free heap
 * size and the minimum free heap size so far. If an error is discovered in the
 * execution of a task then the check task will print out an appropriate error
 * message.
 */


/* Standard includes. */
#include <stdio.h>
#include <stdlib.h>

/* Kernel includes. */
#include <FreeRTOS.h>
#include <task.h>
#include <queue.h>
#include <timers.h>
#include <semphr.h>

/* Standard demo includes. */
#include "BlockQ.h"
#include "integer.h"
#include "semtest.h"
#include "PollQ.h"
#include "GenQTest.h"
#include "QPeek.h"
#include "recmutex.h"
#include "flop.h"
#include "TimerDemo.h"
#include "countsem.h"
#include "death.h"
#include "QueueSet.h"
#include "QueueOverwrite.h"
#include "EventGroupsDemo.h"
#include "IntSemTest.h"
#include "TaskNotify.h"
#include "QueueSetPolling.h"
#include "StaticAllocation.h"
#include "blocktim.h"
#include "AbortDelay.h"
#include "MessageBufferDemo.h"
#include "StreamBufferDemo.h"
#include "StreamBufferInterrupt.h"

/**
 * Priorities at which the tasks are created.
 */
#define mainCHECK_TASK_PRIORITY			( configMAX_PRIORITIES - 2 )
#define mainQUEUE_POLL_PRIORITY			( tskIDLE_PRIORITY + 1 )
#define mainSEM_TEST_PRIORITY			( tskIDLE_PRIORITY + 1 )
#define mainBLOCK_Q_PRIORITY			( tskIDLE_PRIORITY + 2 )
#define mainCREATOR_TASK_PRIORITY		( tskIDLE_PRIORITY + 3 )
#define mainFLASH_TASK_PRIORITY			( tskIDLE_PRIORITY + 1 )
#define mainINTEGER_TASK_PRIORITY		( tskIDLE_PRIORITY )
#define mainGEN_QUEUE_TASK_PRIORITY		( tskIDLE_PRIORITY )
#define mainFLOP_TASK_PRIORITY			( tskIDLE_PRIORITY )
#define mainQUEUE_OVERWRITE_PRIORITY	( tskIDLE_PRIORITY )

/**
 * Period used in timer tests.
 */
#define mainTIMER_TEST_PERIOD			( 50 )

/**
 * Parameters that are passed into the register check tasks solely for the
 * purpose of ensuring parameters are passed into tasks correctly.
 */
#define mainREG_TEST_TASK_1_PARAMETER	( ( void * ) 0x12345678 )
#define mainREG_TEST_TASK_2_PARAMETER	( ( void * ) 0x87654321 )

/**
 * Determines whether to enable interrupt queue tests.
 *
 * Interrupt queue tests are used to test interrupt nesting and enabling them
 * interferes with proper functioning of other tests. This macro controls
 * whether to enable interrupt queue tests or all other tests:
 *
 * * When mainENABLE_INT_QUEUE_TESTS is set to 1, interrupt queue tests are
 *   enabled and every other test is disabled.
 * * When mainENABLE_INT_QUEUE_TESTS is set to 0, interrupt queue tests are
 *   disabled and every other test is enabled.
 */
#define mainENABLE_INT_QUEUE_TESTS		( 0 )
/*-----------------------------------------------------------*/

/**
 * The task that periodically checks that all the standard demo tasks are
 * still executing and error free.
 */
static void prvCheckTask( void *pvParameters );

/**
 * Tasks that implement register tests.
 */
static void prvRegTest1Task( void *pvParameters );
static void prvRegTest2Task( void *pvParameters );

/**
 * Functions that implement register tests.
 *
 * These are implemented in assembler file regtest_xtensa.S.
 */
extern void vRegTest1( void );
extern void vRegTest2( void );
/*-----------------------------------------------------------*/

/**
 * The variable into which error messages are latched.
 */
static char *pcStatusMessage = "No errors";

/**
 * The following two variables are used to communicate the status of the
 * register check tasks to the check task.  If the variables keep incrementing,
 * then the register check tasks have not discovered any errors.  If a variable
 * stops incrementing, then an error has been found.
 */
volatile unsigned long ulRegTest1Counter = 0UL, ulRegTest2Counter = 0UL;

/**
 * The following variable is used to communicate whether the timers for the
 * IntQueue tests have been Initialized. This is needed to ensure that the queues
 * are accessed from the tick hook only after they have been created in the
 * interrupt queue test.
 */
volatile BaseType_t xTimerForQueueTestInitialized = pdFALSE;
/*-----------------------------------------------------------*/

int main_full( void )
{
	/* Start the check task as described at the top of this file. */
	xTaskCreate( prvCheckTask, "Check", configMINIMAL_STACK_SIZE, NULL, mainCHECK_TASK_PRIORITY, NULL );

	#if( mainENABLE_INT_QUEUE_TESTS == 0 )
	{
		/* Create the standard demo tasks. */
		vStartTaskNotifyTask();
		vStartBlockingQueueTasks( mainBLOCK_Q_PRIORITY );
		vStartSemaphoreTasks( mainSEM_TEST_PRIORITY );
		vStartPolledQueueTasks( mainQUEUE_POLL_PRIORITY );
		vStartIntegerMathTasks( mainINTEGER_TASK_PRIORITY );
		vStartGenericQueueTasks( mainGEN_QUEUE_TASK_PRIORITY );

		vStartQueuePeekTasks();
		vStartMathTasks( mainFLOP_TASK_PRIORITY );
		vStartRecursiveMutexTasks();
		vStartCountingSemaphoreTasks();
		vStartQueueSetTasks();

		vStartQueueOverwriteTask( mainQUEUE_OVERWRITE_PRIORITY );
		vStartEventGroupTasks();
		vStartInterruptSemaphoreTasks();
		vStartQueueSetPollingTask();
		vCreateBlockTimeTasks();

		#if( configUSE_PREEMPTION != 0  )
		{
			/* Don't expect these tasks to pass when preemption is not used. */
			vStartTimerDemoTask( mainTIMER_TEST_PERIOD );
		}
		#endif

		vCreateAbortDelayTasks();
		vStartMessageBufferTasks( configMINIMAL_STACK_SIZE );

		vStartStreamBufferTasks();
		vStartStreamBufferInterruptDemo();

		/* Create the register check tasks, as described at the top of this	file */
		xTaskCreate( prvRegTest1Task, "Reg1", configMINIMAL_STACK_SIZE, mainREG_TEST_TASK_1_PARAMETER, tskIDLE_PRIORITY, NULL );
		xTaskCreate( prvRegTest2Task, "Reg2", configMINIMAL_STACK_SIZE, mainREG_TEST_TASK_2_PARAMETER, tskIDLE_PRIORITY, NULL );

		/* The suicide tasks must be created last as they need to know how many
		 * tasks were running prior to their creation.  This then allows them to
		 * ascertain whether or not the correct/expected number of tasks are
		 * running at any given time. */
		vCreateSuicidalTasks( mainCREATOR_TASK_PRIORITY );
	}
	#else /* mainENABLE_INT_QUEUE_TESTS */
	{
		/* Start interrupt queue test tasks. */
		vStartInterruptQueueTasks();
	}
	#endif /* mainENABLE_INT_QUEUE_TESTS */

	/* Start the scheduler itself. */
	vTaskStartScheduler();

	/* Should never get here unless there was not enough heap space to create
	 * the idle and other system tasks. */
	return 0;
}
/*-----------------------------------------------------------*/

static void prvCheckTask( void *pvParameters )
{
TickType_t xNextWakeTime;
const TickType_t xCycleFrequency = pdMS_TO_TICKS( 5000UL );
static unsigned long ulLastRegTest1Value = 0, ulLastRegTest2Value = 0;

	/* Just to remove compiler warning. */
	( void ) pvParameters;

	/* Initialise xNextWakeTime - this only needs to be done once. */
	xNextWakeTime = xTaskGetTickCount();

	for( ;; )
	{
		/* Place this task in the blocked state until it is time to run again. */
		vTaskDelayUntil( &xNextWakeTime, xCycleFrequency );

		#if( mainENABLE_INT_QUEUE_TESTS == 0 )
		{
			/* Check the standard demo tasks are running without error. */
			#if( configUSE_PREEMPTION != 0 )
			{
				/* These tasks are only created when preemption is used. */
				if( xAreTimerDemoTasksStillRunning( xCycleFrequency ) != pdTRUE )
				{
					pcStatusMessage = "Error: TimerDemo";
				}
			}
			#endif

			if( xAreTaskNotificationTasksStillRunning() != pdTRUE )
			{
				pcStatusMessage = "Error:  Notification";
			}
			else if( xAreBlockingQueuesStillRunning() != pdTRUE )
			{
				pcStatusMessage = "Error: BlockQueue";
			}
			else if( xAreSemaphoreTasksStillRunning() != pdTRUE )
			{
				pcStatusMessage = "Error: SemTest";
			}
			else if( xArePollingQueuesStillRunning() != pdTRUE )
			{
				pcStatusMessage = "Error: PollQueue";
			}
			else if( xAreIntegerMathsTaskStillRunning() != pdTRUE )
			{
				pcStatusMessage = "Error: IntMath";
			}
			else if( xAreGenericQueueTasksStillRunning() != pdTRUE )
			{
				pcStatusMessage = "Error: GenQueue";
			}
			else if( xAreQueuePeekTasksStillRunning() != pdTRUE )
			{
				pcStatusMessage = "Error: QueuePeek";
			}
			else if( xAreMathsTaskStillRunning() != pdPASS )
			{
				pcStatusMessage = "Error: Flop";
			}
			else if( xAreRecursiveMutexTasksStillRunning() != pdTRUE )
			{
				pcStatusMessage = "Error: RecMutex";
			}
			else if( xAreCountingSemaphoreTasksStillRunning() != pdTRUE )
			{
				pcStatusMessage = "Error: CountSem";
			}
			else if( xAreQueueSetTasksStillRunning() != pdPASS )
			{
				pcStatusMessage = "Error: Queue set";
			}
			else if( xIsQueueOverwriteTaskStillRunning() != pdPASS )
			{
				pcStatusMessage = "Error: Queue overwrite";
			}
			else if( xAreEventGroupTasksStillRunning() != pdTRUE )
			{
				pcStatusMessage = "Error: EventGroup";
			}
			else if( xAreInterruptSemaphoreTasksStillRunning() != pdTRUE )
			{
				pcStatusMessage = "Error: IntSem";
			}
			else if( xAreQueueSetPollTasksStillRunning() != pdPASS )
			{
				pcStatusMessage = "Error: Queue set polling";
			}
			else if( xAreBlockTimeTestTasksStillRunning() != pdPASS )
			{
				pcStatusMessage = "Error: Block time";
			}
			else if( xAreAbortDelayTestTasksStillRunning() != pdPASS )
			{
				pcStatusMessage = "Error: Abort delay";
			}
			else if( xAreMessageBufferTasksStillRunning() != pdTRUE )
			{
				pcStatusMessage = "Error:  MessageBuffer";
			}
			else if( xAreStreamBufferTasksStillRunning() != pdTRUE )
			{
				pcStatusMessage = "Error:  StreamBuffer";
			}
			else if( xIsInterruptStreamBufferDemoStillRunning() != pdPASS )
			{
				pcStatusMessage = "Error: Stream buffer interrupt";
			}
			else if( xIsCreateTaskStillRunning() != pdTRUE )
			{
				pcStatusMessage = "Error: Death";
			}
			else if( ulLastRegTest1Value == ulRegTest1Counter )
			{
				pcStatusMessage = "Error: Reg Test 1";
			}
			else if( ulLastRegTest2Value == ulRegTest2Counter )
			{
				pcStatusMessage = "Error: Reg Test 2";
			}

			/* Update register test counters. */
			ulLastRegTest1Value = ulRegTest1Counter;
			ulLastRegTest2Value = ulRegTest2Counter;
		}
		#else /* mainENABLE_INT_QUEUE_TESTS */
		{
			if( xAreIntQueueTasksStillRunning() != pdTRUE )
			{
				pcStatusMessage = "Error: IntQueue";
			}
		}
		#endif /* mainENABLE_INT_QUEUE_TESTS */

		/* This is the only task that uses stdout so its ok to call printf()
		 * directly. Do not call printf from any other task. */
		printf( "%s - tick count %zu - free heap %zu - min free heap %zu\r\n", pcStatusMessage,
																			   xTaskGetTickCount(),
																			   xPortGetFreeHeapSize(),
																			   xPortGetMinimumEverFreeHeapSize() );
	}
}
/*-----------------------------------------------------------*/

/* Called by vApplicationTickHook(), which is defined in main.c. */
void vFullDemoTickHookFunction( void )
{
TaskHandle_t xTimerTask;

	#if( mainENABLE_INT_QUEUE_TESTS == 0 )
	{
		/* Exercise using task notifications from an interrupt. */
		xNotifyTaskFromISR();

		/* Write to a queue that is in use as part of the queue set demo to
		 * demonstrate using queue sets from an ISR. */
		vQueueSetAccessQueueSetFromISR();

		/* Call the periodic queue overwrite from ISR demo. */
		vQueueOverwritePeriodicISRDemo();

		/* Exercise event groups from interrupts. */
		vPeriodicEventGroupsProcessing();

		/* Exercise giving mutexes from an interrupt. */
		vInterruptSemaphorePeriodicTest();

		/* Queue set access from interrupt. */
		vQueueSetPollingInterruptAccess();

		/* Call the periodic timer test, which tests the timer API functions that
		 * can be called from an ISR. */
		#if( configUSE_PREEMPTION != 0 )
		{
			/* Only created when preemption is used. */
			vTimerPeriodicISRTests();
		}
		#endif

		/* Writes to stream buffer byte by byte to test the stream buffer trigger
		 * level functionality. */
		vPeriodicStreamBufferProcessing();

		/* Writes a string to a string buffer four bytes at a time to demonstrate
		 * a stream being sent from an interrupt to a task. */
		vBasicStreamBufferSendFromISR();
	}
	#else /* mainENABLE_INT_QUEUE_TESTS */
	{
		/* Access queues from interrupt. Make sure to access after the queues have
		 * been created. */
		if( xTimerForQueueTestInitialized == pdTRUE )
		{
			portYIELD_FROM_ISR( xFirstTimerHandler() );
		}
	}
	#endif /* mainENABLE_INT_QUEUE_TESTS */
}
/*-----------------------------------------------------------*/

static void prvRegTest1Task( void *pvParameters )
{
	/* Although the regtest task is written in assembly, its entry point is
	 * written in C for convenience of checking the task parameter is being
	 * passed in correctly. */
	if( pvParameters == mainREG_TEST_TASK_1_PARAMETER )
	{
		/* Start the part of the test that is written in assembly. */
		vRegTest1();
	}

	/* The following line will only execute if the task parameter is found to
	 * be incorrect. The check task will detect that the regtest loop counter is
	 * not being incremented and flag an error. */
	vTaskDelete( NULL );
}
/*-----------------------------------------------------------*/

static void prvRegTest2Task( void *pvParameters )
{
	/* Although the regtest task is written in assembly, its entry point is
	 * written in C for convenience of checking the task parameter is being
	 * passed in correctly. */
	if( pvParameters == mainREG_TEST_TASK_2_PARAMETER )
	{
		/* Start the part of the test that is written in assembly. */
		vRegTest2();
	}

	/* The following line will only execute if the task parameter is found to
	 * be incorrect. The check task will detect that the regtest loop counter is
	 * not being incremented and flag an error. */
	vTaskDelete( NULL );
}
/*-----------------------------------------------------------*/
