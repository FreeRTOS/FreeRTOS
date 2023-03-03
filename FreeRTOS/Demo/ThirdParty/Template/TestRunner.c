/*
 * FreeRTOS V202212.01
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
 * https://www.FreeRTOS.org
 * https://github.com/FreeRTOS
 *
 */

/* Standard includes. */
#include <stdio.h>
#include <stdlib.h>

/* Kernel includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"
#include "timers.h"
#include "semphr.h"

/* Various test includes. */
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
#include "IntQueue.h"
#include "TaskNotify.h"
#include "TaskNotifyArray.h"
#include "QueueSetPolling.h"
#include "StaticAllocation.h"
#include "blocktim.h"
#include "AbortDelay.h"
#include "MessageBufferDemo.h"
#include "StreamBufferDemo.h"
#include "StreamBufferInterrupt.h"
#include "RegTests.h"

/**
 * Priorities at which the tasks are created.
 */
#define testrunnerCHECK_TASK_PRIORITY			( configMAX_PRIORITIES - 2 )
#define testrunnerQUEUE_POLL_PRIORITY			( tskIDLE_PRIORITY + 1 )
#define testrunnerSEM_TEST_PRIORITY				( tskIDLE_PRIORITY + 1 )
#define testrunnerBLOCK_Q_PRIORITY				( tskIDLE_PRIORITY + 2 )
#define testrunnerCREATOR_TASK_PRIORITY			( tskIDLE_PRIORITY + 3 )
#define testrunnerFLASH_TASK_PRIORITY			( tskIDLE_PRIORITY + 1 )
#define testrunnerINTEGER_TASK_PRIORITY			( tskIDLE_PRIORITY )
#define testrunnerGEN_QUEUE_TASK_PRIORITY		( tskIDLE_PRIORITY )
#define testrunnerFLOP_TASK_PRIORITY			( tskIDLE_PRIORITY )
#define testrunnerQUEUE_OVERWRITE_PRIORITY		( tskIDLE_PRIORITY )
#define testrunnerREGISTER_TEST_PRIORITY		( tskIDLE_PRIORITY )

/**
 * Period used in timer tests.
 */
#define testrunnerTIMER_TEST_PERIOD				( 50 )
/*-----------------------------------------------------------*/

/**
 * The variable into which error messages are latched.
 */
static char *pcStatusMessage = "No errors";
/*-----------------------------------------------------------*/

/**
 * The task that periodically checks that all the standard demo tasks are
 * still executing and error free.
 */
static void prvCheckTask( void *pvParameters );
/*-----------------------------------------------------------*/

void vStartTests( void )
{
	BaseType_t xResult;

	xResult = xTaskCreate( prvCheckTask,
						  "Check",
						  configMINIMAL_STACK_SIZE,
						  NULL,
						  testrunnerCHECK_TASK_PRIORITY,
						  NULL );

	if( xResult == pdPASS )
	{
		#if( configSTART_TASK_NOTIFY_TESTS == 1 )
		{
			vStartTaskNotifyTask();
		}
		#endif /* configSTART_TASK_NOTIFY_TESTS */

		#if( configSTART_TASK_NOTIFY_ARRAY_TESTS == 1 )
		{
			vStartTaskNotifyArrayTask();
		}
		#endif /* configSTART_TASK_NOTIFY_ARRAY_TESTS */

		#if( configSTART_BLOCKING_QUEUE_TESTS == 1 )
		{
			vStartBlockingQueueTasks( testrunnerBLOCK_Q_PRIORITY );
		}
		#endif /* configSTART_BLOCKING_QUEUE_TESTS */

		#if( configSTART_SEMAPHORE_TESTS == 1 )
		{
			vStartSemaphoreTasks( testrunnerSEM_TEST_PRIORITY );
		}
		#endif /* configSTART_SEMAPHORE_TESTS */

		#if( configSTART_POLLED_QUEUE_TESTS == 1 )
		{
			vStartPolledQueueTasks( testrunnerQUEUE_POLL_PRIORITY );
		}
		#endif /* configSTART_POLLED_QUEUE_TESTS */

		#if( configSTART_INTEGER_MATH_TESTS == 1 )
		{
			vStartIntegerMathTasks( testrunnerINTEGER_TASK_PRIORITY );
		}
		#endif /* configSTART_INTEGER_MATH_TESTS */

		#if( configSTART_GENERIC_QUEUE_TESTS == 1 )
		{
			vStartGenericQueueTasks( testrunnerGEN_QUEUE_TASK_PRIORITY );
		}
		#endif /* configSTART_GENERIC_QUEUE_TESTS */

		#if( configSTART_PEEK_QUEUE_TESTS == 1 )
		{
			vStartQueuePeekTasks();
		}
		#endif /* configSTART_PEEK_QUEUE_TESTS */

		#if( configSTART_MATH_TESTS == 1 )
		{
			vStartMathTasks( testrunnerFLOP_TASK_PRIORITY );
		}
		#endif /* configSTART_MATH_TESTS */

		#if( configSTART_RECURSIVE_MUTEX_TESTS == 1 )
		{
			vStartRecursiveMutexTasks();
		}
		#endif /* configSTART_RECURSIVE_MUTEX_TESTS */

		#if( configSTART_COUNTING_SEMAPHORE_TESTS == 1 )
		{
			vStartCountingSemaphoreTasks();
		}
		#endif /* configSTART_COUNTING_SEMAPHORE_TESTS */

		#if( configSTART_QUEUE_SET_TESTS == 1 )
		{
			vStartQueueSetTasks();
		}
		#endif /* configSTART_QUEUE_SET_TESTS */

		#if( configSTART_QUEUE_OVERWRITE_TESTS == 1 )
		{
			vStartQueueOverwriteTask( testrunnerQUEUE_OVERWRITE_PRIORITY );
		}
		#endif /* configSTART_QUEUE_OVERWRITE_TESTS */

		#if( configSTART_EVENT_GROUP_TESTS == 1 )
		{
			vStartEventGroupTasks();
		}
		#endif /* configSTART_EVENT_GROUP_TESTS */

		#if( configSTART_INTERRUPT_SEMAPHORE_TESTS == 1 )
		{
			vStartInterruptSemaphoreTasks();
		}
		#endif /* configSTART_INTERRUPT_SEMAPHORE_TESTS */

		#if( configSTART_QUEUE_SET_POLLING_TESTS == 1 )
		{
			vStartQueueSetPollingTask();
		}
		#endif /* configSTART_QUEUE_SET_POLLING_TESTS */

		#if( configSTART_BLOCK_TIME_TESTS == 1 )
		{
			vCreateBlockTimeTasks();
		}
		#endif /* configSTART_BLOCK_TIME_TESTS */

		#if( configSTART_ABORT_DELAY_TESTS == 1 )
		{
			vCreateAbortDelayTasks();
		}
		#endif /* configSTART_ABORT_DELAY_TESTS */

		#if( configSTART_MESSAGE_BUFFER_TESTS == 1 )
		{
			vStartMessageBufferTasks( configMINIMAL_STACK_SIZE );
		}
		#endif /* configSTART_MESSAGE_BUFFER_TESTS */

		#if(configSTART_STREAM_BUFFER_TESTS  == 1 )
		{
			vStartStreamBufferTasks();
		}
		#endif /* configSTART_STREAM_BUFFER_TESTS */

		#if( configSTART_STREAM_BUFFER_INTERRUPT_TESTS == 1 )
		{
			vStartStreamBufferInterruptDemo();
		}
		#endif /* configSTART_STREAM_BUFFER_INTERRUPT_TESTS */

		#if( ( configSTART_TIMER_TESTS == 1 ) && ( configUSE_PREEMPTION != 0 ) )
		{
			/* Don't expect these tasks to pass when preemption is not used. */
			vStartTimerDemoTask( testrunnerTIMER_TEST_PERIOD );
		}
		#endif /* ( configSTART_TIMER_TESTS == 1 ) && ( configUSE_PREEMPTION != 0 ) */

		#if( configSTART_INTERRUPT_QUEUE_TESTS == 1 )
		{
			vStartInterruptQueueTasks();
		}
		#endif /* configSTART_INTERRUPT_QUEUE_TESTS */

		#if( configSTART_REGISTER_TESTS == 1 )
		{
			vStartRegisterTasks( testrunnerREGISTER_TEST_PRIORITY );
		}
		#endif /* configSTART_REGISTER_TESTS */

		#if( configSTART_DELETE_SELF_TESTS == 1 )
		{
			/* The suicide tasks must be created last as they need to know how many
			* tasks were running prior to their creation.  This then allows them to
			* ascertain whether or not the correct/expected number of tasks are
			* running at any given time. */
			vCreateSuicidalTasks( testrunnerCREATOR_TASK_PRIORITY );
		}
		#endif /* configSTART_DELETE_SELF_TESTS */
	}

	vTaskStartScheduler();
}
/*-----------------------------------------------------------*/

void vApplicationTickHook( void )
{
	#if( configSTART_TASK_NOTIFY_TESTS == 1 )
	{
		xNotifyTaskFromISR();
	}
	#endif /* configSTART_TASK_NOTIFY_TESTS */

	#if( configSTART_TASK_NOTIFY_ARRAY_TESTS == 1 )
	{
		xNotifyArrayTaskFromISR();
	}
	#endif /* configSTART_TASK_NOTIFY_ARRAY_TESTS */

	#if( configSTART_QUEUE_SET_TESTS == 1 )
	{
		vQueueSetAccessQueueSetFromISR();
	}
	#endif /* configSTART_QUEUE_SET_TESTS */

	#if( configSTART_QUEUE_OVERWRITE_TESTS == 1 )
	{
		vQueueOverwritePeriodicISRDemo();
	}
	#endif /* configSTART_QUEUE_OVERWRITE_TESTS */

	#if( configSTART_EVENT_GROUP_TESTS == 1 )
	{
		vPeriodicEventGroupsProcessing();
	}
	#endif /* configSTART_EVENT_GROUP_TESTS */

	#if( configSTART_INTERRUPT_SEMAPHORE_TESTS == 1 )
	{
		vInterruptSemaphorePeriodicTest();
	}
	#endif /* configSTART_INTERRUPT_SEMAPHORE_TESTS */

	#if( configSTART_QUEUE_SET_POLLING_TESTS == 1 )
	{
		vQueueSetPollingInterruptAccess();
	}
	#endif /* configSTART_QUEUE_SET_POLLING_TESTS */

	#if( configSTART_STREAM_BUFFER_TESTS == 1 )
	{
		vPeriodicStreamBufferProcessing();
	}
	#endif /* configSTART_STREAM_BUFFER_TESTS */

	#if( configSTART_STREAM_BUFFER_INTERRUPT_TESTS == 1 )
	{
		vBasicStreamBufferSendFromISR();
	}
	#endif /* configSTART_STREAM_BUFFER_INTERRUPT_TESTS */

	#if( ( configSTART_TIMER_TESTS == 1 ) && ( configUSE_PREEMPTION != 0 ) )
	{
		/* Only created when preemption is used. */
		vTimerPeriodicISRTests();
	}
	#endif /* ( configSTART_TIMER_TESTS == 1 ) && ( configUSE_PREEMPTION != 0 ) */

	#if( configSTART_INTERRUPT_QUEUE_TESTS == 1 )
	{
		portYIELD_FROM_ISR( xFirstTimerHandler() );
	}
	#endif /* configSTART_INTERRUPT_QUEUE_TESTS */
}
/*-----------------------------------------------------------*/

static void prvCheckTask( void *pvParameters )
{
TickType_t xNextWakeTime;
const TickType_t xCycleFrequency = pdMS_TO_TICKS( 5000UL );

	/* Silence compiler warnings about unused variables. */
	( void ) pvParameters;

	/* Initialise xNextWakeTime - this only needs to be done once. */
	xNextWakeTime = xTaskGetTickCount();

	for( ;; )
	{
		/* Place this task in the blocked state until it is time to run again. */
		vTaskDelayUntil( &xNextWakeTime, xCycleFrequency );

		#if( configSTART_TASK_NOTIFY_TESTS == 1 )
		{
			if( xAreTaskNotificationTasksStillRunning() != pdTRUE )
			{
				pcStatusMessage = "Error:  Notification";
			}
		}
		#endif /* configSTART_TASK_NOTIFY_TESTS */

		#if( configSTART_TASK_NOTIFY_ARRAY_TESTS == 1 )
		{
			if( xAreTaskNotificationArrayTasksStillRunning() != pdTRUE )
			{
				pcStatusMessage = "Error:  Notification Array";
			}
		}
		#endif /* configSTART_TASK_NOTIFY_ARRAY_TESTS */

		#if( configSTART_BLOCKING_QUEUE_TESTS == 1 )
		{
			if( xAreBlockingQueuesStillRunning() != pdTRUE )
			{
				pcStatusMessage = "Error: BlockQueue";
			}
		}
		#endif /* configSTART_BLOCKING_QUEUE_TESTS */

		#if( configSTART_SEMAPHORE_TESTS == 1 )
		{
			if( xAreSemaphoreTasksStillRunning() != pdTRUE )
			{
				pcStatusMessage = "Error: SemTest";
			}
		}
		#endif /* configSTART_SEMAPHORE_TESTS */

		#if( configSTART_POLLED_QUEUE_TESTS == 1 )
		{
			if( xArePollingQueuesStillRunning() != pdTRUE )
			{
				pcStatusMessage = "Error: PollQueue";
			}
		}
		#endif /* configSTART_POLLED_QUEUE_TESTS */

		#if( configSTART_INTEGER_MATH_TESTS == 1 )
		{
			if( xAreIntegerMathsTaskStillRunning() != pdTRUE )
			{
				pcStatusMessage = "Error: IntMath";
			}
		}
		#endif /* configSTART_INTEGER_MATH_TESTS */

		#if( configSTART_GENERIC_QUEUE_TESTS == 1 )
		{
			if( xAreGenericQueueTasksStillRunning() != pdTRUE )
			{
				pcStatusMessage = "Error: GenQueue";
			}
		}
		#endif /* configSTART_GENERIC_QUEUE_TESTS */

		#if( configSTART_PEEK_QUEUE_TESTS == 1 )
		{
			if( xAreQueuePeekTasksStillRunning() != pdTRUE )
			{
				pcStatusMessage = "Error: QueuePeek";
			}
		}
		#endif /* configSTART_PEEK_QUEUE_TESTS */

		#if( configSTART_MATH_TESTS == 1 )
		{
			if( xAreMathsTaskStillRunning() != pdPASS )
			{
				pcStatusMessage = "Error: Flop";
			}
		}
		#endif /* configSTART_MATH_TESTS */

		#if( configSTART_RECURSIVE_MUTEX_TESTS == 1 )
		{
			if( xAreRecursiveMutexTasksStillRunning() != pdTRUE )
			{
				pcStatusMessage = "Error: RecMutex";
			}
		}
		#endif /* configSTART_RECURSIVE_MUTEX_TESTS */

		#if( configSTART_COUNTING_SEMAPHORE_TESTS == 1 )
		{
			if( xAreCountingSemaphoreTasksStillRunning() != pdTRUE )
			{
				pcStatusMessage = "Error: CountSem";
			}
		}
		#endif /* configSTART_COUNTING_SEMAPHORE_TESTS */

		#if( configSTART_QUEUE_SET_TESTS == 1 )
		{
			if( xAreQueueSetTasksStillRunning() != pdPASS )
			{
				pcStatusMessage = "Error: Queue set";
			}
		}
		#endif /* configSTART_QUEUE_SET_TESTS */

		#if( configSTART_QUEUE_OVERWRITE_TESTS == 1 )
		{
			if( xIsQueueOverwriteTaskStillRunning() != pdPASS )
			{
				pcStatusMessage = "Error: Queue overwrite";
			}
		}
		#endif /* configSTART_QUEUE_OVERWRITE_TESTS */

		#if( configSTART_EVENT_GROUP_TESTS == 1 )
		{
			if( xAreEventGroupTasksStillRunning() != pdTRUE )
			{
				pcStatusMessage = "Error: EventGroup";
			}
		}
		#endif /* configSTART_EVENT_GROUP_TESTS */

		#if( configSTART_INTERRUPT_SEMAPHORE_TESTS == 1 )
		{
			if( xAreInterruptSemaphoreTasksStillRunning() != pdTRUE )
			{
				pcStatusMessage = "Error: IntSem";
			}
		}
		#endif /* configSTART_INTERRUPT_SEMAPHORE_TESTS */

		#if( configSTART_QUEUE_SET_POLLING_TESTS == 1 )
		{
			if( xAreQueueSetPollTasksStillRunning() != pdPASS )
			{
				pcStatusMessage = "Error: Queue set polling";
			}
		}
		#endif /* configSTART_QUEUE_SET_POLLING_TESTS */

		#if( configSTART_BLOCK_TIME_TESTS == 1 )
		{
			if( xAreBlockTimeTestTasksStillRunning() != pdPASS )
			{
				pcStatusMessage = "Error: Block time";
			}
		}
		#endif /* configSTART_BLOCK_TIME_TESTS */

		#if( configSTART_ABORT_DELAY_TESTS == 1 )
		{
			if( xAreAbortDelayTestTasksStillRunning() != pdPASS )
			{
				pcStatusMessage = "Error: Abort delay";
			}
		}
		#endif /* configSTART_ABORT_DELAY_TESTS */

		#if( configSTART_MESSAGE_BUFFER_TESTS == 1 )
		{
			if( xAreMessageBufferTasksStillRunning() != pdTRUE )
			{
				pcStatusMessage = "Error:  MessageBuffer";
			}
		}
		#endif /* configSTART_MESSAGE_BUFFER_TESTS */

		#if( configSTART_STREAM_BUFFER_TESTS == 1 )
		{
			if( xAreStreamBufferTasksStillRunning() != pdTRUE )
			{
				pcStatusMessage = "Error:  StreamBuffer";
			}
		}
		#endif /* configSTART_STREAM_BUFFER_TESTS */

		#if( configSTART_STREAM_BUFFER_INTERRUPT_TESTS == 1 )
		{
			if( xIsInterruptStreamBufferDemoStillRunning() != pdPASS )
			{
				pcStatusMessage = "Error: Stream buffer interrupt";
			}
		}
		#endif /* configSTART_STREAM_BUFFER_INTERRUPT_TESTS */

		#if( ( configSTART_TIMER_TESTS == 1 ) && ( configUSE_PREEMPTION != 0 ) )
		{
			if( xAreTimerDemoTasksStillRunning( xCycleFrequency ) != pdTRUE )
			{
				pcStatusMessage = "Error: TimerDemo";
			}
		}
		#endif /* ( configSTART_TIMER_TESTS == 1 ) && ( configUSE_PREEMPTION != 0 ) */

		#if( configSTART_INTERRUPT_QUEUE_TESTS == 1 )
		{
			if( xAreIntQueueTasksStillRunning() != pdTRUE )
			{
				pcStatusMessage = "Error: IntQueue";
			}
		}
		#endif /* configSTART_INTERRUPT_QUEUE_TESTS */

		#if( configSTART_REGISTER_TESTS == 1 )
		{
			if( xAreRegisterTasksStillRunning() != pdTRUE )
			{
				pcStatusMessage = "Error: RegTests";
			}
		}
		#endif /* configSTART_REGISTER_TESTS */

		#if( configSTART_DELETE_SELF_TESTS == 1 )
		{
			if( xIsCreateTaskStillRunning() != pdTRUE )
			{
				pcStatusMessage = "Error: Death";
			}
		}
		#endif /* configSTART_DELETE_SELF_TESTS */

		configPRINTF( ( "%s \r\n", pcStatusMessage ) );
	}
}
/*-----------------------------------------------------------*/
