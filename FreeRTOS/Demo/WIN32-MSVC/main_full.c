/*
 * FreeRTOS Kernel V10.2.0
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

/*
 *******************************************************************************
 * NOTE 1: The Win32 port is a simulation (or is that emulation?) only!  Do not
 * expect to get real time behaviour from the Win32 port or this demo
 * application.  It is provided as a convenient development and demonstration
 * test bed only.
 *
 * Windows will not be running the FreeRTOS simulator threads continuously, so
 * the timing information in the FreeRTOS+Trace logs have no meaningful units.
 * See the documentation page for the Windows simulator for an explanation of
 * the slow timing:
 * http://www.freertos.org/FreeRTOS-Windows-Simulator-Emulator-for-Visual-Studio-and-Eclipse-MingW.html
 * - READ THE WEB DOCUMENTATION FOR THIS PORT FOR MORE INFORMATION ON USING IT -
 *
 * NOTE 2:  This project provides two demo applications.  A simple blinky style
 * project, and a more comprehensive test and demo application.  The
 * mainCREATE_SIMPLE_BLINKY_DEMO_ONLY setting in main.c is used to select
 * between the two.  See the notes on using mainCREATE_SIMPLE_BLINKY_DEMO_ONLY
 * in main.c.  This file implements the comprehensive test and demo version.
 *
 * NOTE 3:  This file only contains the source code that is specific to the
 * full demo.  Generic functions, such FreeRTOS hook functions, are defined in
 * main.c.
 *******************************************************************************
 *
 * main() creates all the demo application tasks, then starts the scheduler.
 * The web documentation provides more details of the standard demo application
 * tasks, which provide no particular functionality but do provide a good
 * example of how to use the FreeRTOS API.
 *
 * In addition to the standard demo tasks, the following tasks and tests are
 * defined and/or created within this file:
 *
 * "Check" task - This only executes every five seconds but has a high priority
 * to ensure it gets processor time.  Its main function is to check that all the
 * standard demo tasks are still operational.  While no errors have been
 * discovered the check task will print out "OK" and the current simulated tick
 * time.  If an error is discovered in the execution of a task then the check
 * task will print out an appropriate error message.
 *
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
#include "dynamic.h"
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
#include "MessageBufferAMP.h"

/* Priorities at which the tasks are created. */
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

#define mainTIMER_TEST_PERIOD			( 50 )

/* Task function prototypes. */
static void prvCheckTask( void *pvParameters );

/* A task that is created from the idle task to test the functionality of
eTaskStateGet(). */
static void prvTestTask( void *pvParameters );

/*
 * Called from the idle task hook function to demonstrate a few utility
 * functions that are not demonstrated by any of the standard demo tasks.
 */
static void prvDemonstrateTaskStateAndHandleGetFunctions( void );

/*
 * Called from the idle task hook function to demonstrate the use of
 * xTimerPendFunctionCall() as xTimerPendFunctionCall() is not demonstrated by
 * any of the standard demo tasks.
 */
static void prvDemonstratePendingFunctionCall( void );

/*
 * The function that is pended by prvDemonstratePendingFunctionCall().
 */
static void prvPendedFunction( void *pvParameter1, uint32_t ulParameter2 );

/*
 * prvDemonstrateTimerQueryFunctions() is called from the idle task hook
 * function to demonstrate the use of functions that query information about a
 * software timer.  prvTestTimerCallback() is the callback function for the
 * timer being queried.
 */
static void prvDemonstrateTimerQueryFunctions( void );
static void prvTestTimerCallback( TimerHandle_t xTimer );

/*
 * A task to demonstrate the use of the xQueueSpacesAvailable() function.
 */
static void prvDemoQueueSpaceFunctions( void *pvParameters );

/*
 * Tasks that ensure indefinite delays are truly indefinite.
 */
static void prvPermanentlyBlockingSemaphoreTask( void *pvParameters );
static void prvPermanentlyBlockingNotificationTask( void *pvParameters );

/*-----------------------------------------------------------*/

/* The variable into which error messages are latched. */
static char *pcStatusMessage = "No errors";

/* This semaphore is created purely to test using the vSemaphoreDelete() and
semaphore tracing API functions.  It has no other purpose. */
static SemaphoreHandle_t xMutexToDelete = NULL;

/*-----------------------------------------------------------*/

int main_full( void )
{
	/* Start the check task as described at the top of this file. */
	xTaskCreate( prvCheckTask, "Check", configMINIMAL_STACK_SIZE, NULL, mainCHECK_TASK_PRIORITY, NULL );

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
	vStartDynamicPriorityTasks();
	vStartQueueSetTasks();
	vStartQueueOverwriteTask( mainQUEUE_OVERWRITE_PRIORITY );
	vStartEventGroupTasks();
	vStartInterruptSemaphoreTasks();
	vStartQueueSetPollingTask();
	vCreateBlockTimeTasks();
	vCreateAbortDelayTasks();
	xTaskCreate( prvDemoQueueSpaceFunctions, "QSpace", configMINIMAL_STACK_SIZE, NULL, tskIDLE_PRIORITY, NULL );
	xTaskCreate( prvPermanentlyBlockingSemaphoreTask, "BlockSem", configMINIMAL_STACK_SIZE, NULL, tskIDLE_PRIORITY, NULL );
	xTaskCreate( prvPermanentlyBlockingNotificationTask, "BlockNoti", configMINIMAL_STACK_SIZE, NULL, tskIDLE_PRIORITY, NULL );

	vStartMessageBufferTasks( configMINIMAL_STACK_SIZE );
	vStartStreamBufferTasks();
	vStartStreamBufferInterruptDemo();
	vStartMessageBufferAMPTasks( configMINIMAL_STACK_SIZE );

	#if( configSUPPORT_STATIC_ALLOCATION == 1 )
	{
		vStartStaticallyAllocatedTasks();
	}
	#endif

	#if( configUSE_PREEMPTION != 0  )
	{
		/* Don't expect these tasks to pass when preemption is not used. */
		vStartTimerDemoTask( mainTIMER_TEST_PERIOD );
	}
	#endif

	/* The suicide tasks must be created last as they need to know how many
	tasks were running prior to their creation.  This then allows them to
	ascertain whether or not the correct/expected number of tasks are running at
	any given time. */
	vCreateSuicidalTasks( mainCREATOR_TASK_PRIORITY );

	/* Create the semaphore that will be deleted in the idle task hook.  This
	is done purely to test the use of vSemaphoreDelete(). */
	xMutexToDelete = xSemaphoreCreateMutex();

	/* Start the scheduler itself. */
	vTaskStartScheduler();

	/* Should never get here unless there was not enough heap space to create
	the idle and other system tasks. */
	return 0;
}
/*-----------------------------------------------------------*/

static void prvCheckTask( void *pvParameters )
{
TickType_t xNextWakeTime;
const TickType_t xCycleFrequency = pdMS_TO_TICKS( 2500UL );

	/* Just to remove compiler warning. */
	( void ) pvParameters;

	/* Initialise xNextWakeTime - this only needs to be done once. */
	xNextWakeTime = xTaskGetTickCount();

	for( ;; )
	{
		/* Place this task in the blocked state until it is time to run again. */
		vTaskDelayUntil( &xNextWakeTime, xCycleFrequency );

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

		if( xAreStreamBufferTasksStillRunning() != pdTRUE )
		{
			pcStatusMessage = "Error:  StreamBuffer";
		}
		else if( xAreMessageBufferTasksStillRunning() != pdTRUE )
		{
			pcStatusMessage = "Error:  MessageBuffer";
		}
		else if( xAreTaskNotificationTasksStillRunning() != pdTRUE )
		{
			pcStatusMessage = "Error:  Notification";
		}
		else if( xAreInterruptSemaphoreTasksStillRunning() != pdTRUE )
		{
			pcStatusMessage = "Error: IntSem";
		}
		else if( xAreEventGroupTasksStillRunning() != pdTRUE )
		{
			pcStatusMessage = "Error: EventGroup";
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
		else if( xIsCreateTaskStillRunning() != pdTRUE )
		{
			pcStatusMessage = "Error: Death";
		}
		else if( xAreDynamicPriorityTasksStillRunning() != pdPASS )
		{
			pcStatusMessage = "Error: Dynamic";
		}
		else if( xAreQueueSetTasksStillRunning() != pdPASS )
		{
			pcStatusMessage = "Error: Queue set";
		}
		else if( xIsQueueOverwriteTaskStillRunning() != pdPASS )
		{
			pcStatusMessage = "Error: Queue overwrite";
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
		else if( xIsInterruptStreamBufferDemoStillRunning() != pdPASS )
		{
			pcStatusMessage = "Error: Stream buffer interrupt";
		}
		else if( xAreMessageBufferAMPTasksStillRunning() != pdPASS )
		{
			pcStatusMessage = "Error: Message buffer AMP";
		}

		#if( configSUPPORT_STATIC_ALLOCATION == 1 )
			else if( xAreStaticAllocationTasksStillRunning() != pdPASS )
			{
				pcStatusMessage = "Error: Static allocation";
			}
		#endif /* configSUPPORT_STATIC_ALLOCATION */

		/* This is the only task that uses stdout so its ok to call printf()
		directly. */
		printf( "%s - tick count %zu - free heap %zu - min free heap %zu\r\n", pcStatusMessage,
																			   xTaskGetTickCount(),
																			   xPortGetFreeHeapSize(),
																			   xPortGetMinimumEverFreeHeapSize() );
	}
}
/*-----------------------------------------------------------*/

static void prvTestTask( void *pvParameters )
{
const unsigned long ulMSToSleep = 5;

	/* Just to remove compiler warnings. */
	( void ) pvParameters;

	/* This task is just used to test the eTaskStateGet() function.  It
	does not have anything to do. */
	for( ;; )
	{
		/* Sleep to reduce CPU load, but don't sleep indefinitely in case there are
		tasks waiting to be terminated by the idle task. */
		Sleep( ulMSToSleep );
	}
}
/*-----------------------------------------------------------*/

/* Called from vApplicationIdleHook(), which is defined in main.c. */
void vFullDemoIdleFunction( void )
{
const unsigned long ulMSToSleep = 15;
void *pvAllocated;

	/* Sleep to reduce CPU load, but don't sleep indefinitely in case there are
	tasks waiting to be terminated by the idle task. */
	Sleep( ulMSToSleep );

	/* Demonstrate a few utility functions that are not demonstrated by any of
	the standard demo tasks. */
	prvDemonstrateTaskStateAndHandleGetFunctions();

	/* Demonstrate the use of xTimerPendFunctionCall(), which is not
	demonstrated by any of the standard demo tasks. */
	prvDemonstratePendingFunctionCall();

	/* Demonstrate the use of functions that query information about a software
	timer. */
	prvDemonstrateTimerQueryFunctions();


	/* If xMutexToDelete has not already been deleted, then delete it now.
	This is done purely to demonstrate the use of, and test, the
	vSemaphoreDelete() macro.  Care must be taken not to delete a semaphore
	that has tasks blocked on it. */
	if( xMutexToDelete != NULL )
	{
		/* For test purposes, add the mutex to the registry, then remove it
		again, before it is deleted - checking its name is as expected before
		and after the assertion into the registry and its removal from the
		registry. */
		configASSERT( pcQueueGetName( xMutexToDelete ) == NULL );
		vQueueAddToRegistry( xMutexToDelete, "Test_Mutex" );
		configASSERT( strcmp( pcQueueGetName( xMutexToDelete ), "Test_Mutex" ) == 0 );
		vQueueUnregisterQueue( xMutexToDelete );
		configASSERT( pcQueueGetName( xMutexToDelete ) == NULL );

		vSemaphoreDelete( xMutexToDelete );
		xMutexToDelete = NULL;
	}

	/* Exercise heap_5 a bit.  The malloc failed hook will trap failed
	allocations so there is no need to test here. */
	pvAllocated = pvPortMalloc( ( rand() % 500 ) + 1 );
	vPortFree( pvAllocated );
}
/*-----------------------------------------------------------*/

/* Called by vApplicationTickHook(), which is defined in main.c. */
void vFullDemoTickHookFunction( void )
{
TaskHandle_t xTimerTask;

	/* Call the periodic timer test, which tests the timer API functions that
	can be called from an ISR. */
	#if( configUSE_PREEMPTION != 0 )
	{
		/* Only created when preemption is used. */
		vTimerPeriodicISRTests();
	}
	#endif

	/* Call the periodic queue overwrite from ISR demo. */
	vQueueOverwritePeriodicISRDemo();

	/* Write to a queue that is in use as part of the queue set demo to
	demonstrate using queue sets from an ISR. */
	vQueueSetAccessQueueSetFromISR();
	vQueueSetPollingInterruptAccess();

	/* Exercise event groups from interrupts. */
	vPeriodicEventGroupsProcessing();

	/* Exercise giving mutexes from an interrupt. */
	vInterruptSemaphorePeriodicTest();

	/* Exercise using task notifications from an interrupt. */
	xNotifyTaskFromISR();

	/* Writes to stream buffer byte by byte to test the stream buffer trigger
	level functionality. */
	vPeriodicStreamBufferProcessing();

	/* Writes a string to a string buffer four bytes at a time to demonstrate
	a stream being sent from an interrupt to a task. */
	vBasicStreamBufferSendFromISR();

	/* For code coverage purposes. */
	xTimerTask = xTimerGetTimerDaemonTaskHandle();
	configASSERT( uxTaskPriorityGetFromISR( xTimerTask ) == configTIMER_TASK_PRIORITY );
}
/*-----------------------------------------------------------*/

static void prvPendedFunction( void *pvParameter1, uint32_t ulParameter2 )
{
static uint32_t ulLastParameter1 = 1000UL, ulLastParameter2 = 0UL;
uint32_t ulParameter1;

	ulParameter1 = ( uint32_t ) pvParameter1;

	/* Ensure the parameters are as expected. */
	configASSERT( ulParameter1 == ( ulLastParameter1 + 1 ) );
	configASSERT( ulParameter2 == ( ulLastParameter2 + 1 ) );

	/* Remember the parameters for the next time the function is called. */
	ulLastParameter1 = ulParameter1;
	ulLastParameter2 = ulParameter2;
}
/*-----------------------------------------------------------*/

static void prvTestTimerCallback( TimerHandle_t xTimer )
{
	/* This is the callback function for the timer accessed by
	prvDemonstrateTimerQueryFunctions().  The callback does not do anything. */
	( void ) xTimer;
}
/*-----------------------------------------------------------*/

static void prvDemonstrateTimerQueryFunctions( void )
{
static TimerHandle_t xTimer = NULL;
const char *pcTimerName = "TestTimer";
volatile TickType_t xExpiryTime;
const TickType_t xDontBlock = 0;

	if( xTimer == NULL )
	{
		xTimer = xTimerCreate( pcTimerName, portMAX_DELAY, pdTRUE, NULL, prvTestTimerCallback );

		if( xTimer != NULL )
		{
			/* Called from the idle task so a block time must not be
			specified. */
			xTimerStart( xTimer, xDontBlock );
		}
	}

	if( xTimer != NULL )
	{
		/* Demonstrate querying a timer's name. */
		configASSERT( strcmp( pcTimerGetName( xTimer ), pcTimerName ) == 0 );

		/* Demonstrate querying a timer's period. */
		configASSERT( xTimerGetPeriod( xTimer ) == portMAX_DELAY );

		/* Demonstrate querying a timer's next expiry time, although nothing is
		done with the returned value.  Note if the expiry time is less than the
		maximum tick count then the expiry time has overflowed from the current
		time.  In this case the expiry time was set to portMAX_DELAY, so it is
		expected to be less than the current time until the current time has
		itself overflowed. */
		xExpiryTime = xTimerGetExpiryTime( xTimer );
		( void ) xExpiryTime;
	}
}
/*-----------------------------------------------------------*/

static void prvDemonstratePendingFunctionCall( void )
{
static uint32_t ulParameter1 = 1000UL, ulParameter2 = 0UL;
const TickType_t xDontBlock = 0; /* This is called from the idle task so must *not* attempt to block. */

	/* prvPendedFunction() just expects the parameters to be incremented by one
	each time it is called. */
	ulParameter1++;
	ulParameter2++;

	/* Pend the function call, sending the parameters. */
	xTimerPendFunctionCall( prvPendedFunction, ( void * ) ulParameter1, ulParameter2, xDontBlock );
}
/*-----------------------------------------------------------*/

static void prvDemonstrateTaskStateAndHandleGetFunctions( void )
{
TaskHandle_t xIdleTaskHandle, xTimerTaskHandle;
char *pcTaskName;
static portBASE_TYPE xPerformedOneShotTests = pdFALSE;
TaskHandle_t xTestTask;
TaskStatus_t xTaskInfo;
extern StackType_t uxTimerTaskStack[];

	/* Demonstrate the use of the xTimerGetTimerDaemonTaskHandle() and
	xTaskGetIdleTaskHandle() functions.  Also try using the function that sets
	the task number. */
	xIdleTaskHandle = xTaskGetIdleTaskHandle();
	xTimerTaskHandle = xTimerGetTimerDaemonTaskHandle();

	/* This is the idle hook, so the current task handle should equal the
	returned idle task handle. */
	if( xTaskGetCurrentTaskHandle() != xIdleTaskHandle )
	{
		pcStatusMessage = "Error:  Returned idle task handle was incorrect";
	}

	/* Check the same handle is obtained using the idle task's name.  First try
	with the wrong name, then the right name. */
	if( xTaskGetHandle( "Idle" ) == xIdleTaskHandle )
	{
		pcStatusMessage = "Error:  Returned handle for name Idle was incorrect";
	}

	if( xTaskGetHandle( "IDLE" ) != xIdleTaskHandle )
	{
		pcStatusMessage = "Error:  Returned handle for name Idle was incorrect";
	}

	/* Check the timer task handle was returned correctly. */
	pcTaskName = pcTaskGetName( xTimerTaskHandle );
	if( strcmp( pcTaskName, "Tmr Svc" ) != 0 )
	{
		pcStatusMessage = "Error:  Returned timer task handle was incorrect";
	}

	if( xTaskGetHandle( "Tmr Svc" ) != xTimerTaskHandle )
	{
		pcStatusMessage = "Error:  Returned handle for name Tmr Svc was incorrect";
	}

	/* This task is running, make sure it's state is returned as running. */
	if( eTaskStateGet( xIdleTaskHandle ) != eRunning )
	{
		pcStatusMessage = "Error:  Returned idle task state was incorrect";
	}

	/* If this task is running, then the timer task must be blocked. */
	if( eTaskStateGet( xTimerTaskHandle ) != eBlocked )
	{
		pcStatusMessage = "Error:  Returned timer task state was incorrect";
	}

	/* Also with the vTaskGetInfo() function. */
	vTaskGetInfo( xTimerTaskHandle, /* The task being queried. */
					  &xTaskInfo,		/* The structure into which information on the task will be written. */
					  pdTRUE,			/* Include the task's high watermark in the structure. */
					  eInvalid );		/* Include the task state in the structure. */

	/* Check the information returned by vTaskGetInfo() is as expected. */
	if( ( xTaskInfo.eCurrentState != eBlocked )						 ||
		( strcmp( xTaskInfo.pcTaskName, "Tmr Svc" ) != 0 )			 ||
		( xTaskInfo.uxCurrentPriority != configTIMER_TASK_PRIORITY ) ||
		( xTaskInfo.pxStackBase != uxTimerTaskStack )				 ||
		( xTaskInfo.xHandle != xTimerTaskHandle ) )
	{
		pcStatusMessage = "Error:  vTaskGetInfo() returned incorrect information about the timer task";
	}

	/* Other tests that should only be performed once follow.  The test task
	is not created on each iteration because to do so would cause the death
	task to report an error (too many tasks running). */
	if( xPerformedOneShotTests == pdFALSE )
	{
		/* Don't run this part of the test again. */
		xPerformedOneShotTests = pdTRUE;

		/* Create a test task to use to test other eTaskStateGet() return values. */
		if( xTaskCreate( prvTestTask, "Test", configMINIMAL_STACK_SIZE, NULL, tskIDLE_PRIORITY, &xTestTask ) == pdPASS )
		{
			/* If this task is running, the test task must be in the ready state. */
			if( eTaskStateGet( xTestTask ) != eReady )
			{
				pcStatusMessage = "Error: Returned test task state was incorrect 1";
			}

			/* Now suspend the test task and check its state is reported correctly. */
			vTaskSuspend( xTestTask );
			if( eTaskStateGet( xTestTask ) != eSuspended )
			{
				pcStatusMessage = "Error: Returned test task state was incorrect 2";
			}

			/* Now delete the task and check its state is reported correctly. */
			vTaskDelete( xTestTask );
			if( eTaskStateGet( xTestTask ) != eDeleted )
			{
				pcStatusMessage = "Error: Returned test task state was incorrect 3";
			}
		}
	}
}
/*-----------------------------------------------------------*/

static void prvDemoQueueSpaceFunctions( void *pvParameters )
{
QueueHandle_t xQueue = NULL;
const unsigned portBASE_TYPE uxQueueLength = 10;
unsigned portBASE_TYPE uxReturn, x;

	/* Remove compiler warnings. */
	( void ) pvParameters;

	/* Create the queue that will be used.  Nothing is actually going to be
	sent or received so the queue item size is set to 0. */
	xQueue = xQueueCreate( uxQueueLength, 0 );
	configASSERT( xQueue );

	for( ;; )
	{
		for( x = 0; x < uxQueueLength; x++ )
		{
			/* Ask how many messages are available... */
			uxReturn = uxQueueMessagesWaiting( xQueue );

			/* Check the number of messages being reported as being available
			is as expected, and force an assert if not. */
			if( uxReturn != x )
			{
				/* xQueue cannot be NULL so this is deliberately causing an
				assert to be triggered as there is an error. */
				configASSERT( xQueue == NULL );
			}

			/* Ask how many spaces remain in the queue... */
			uxReturn = uxQueueSpacesAvailable( xQueue );

			/* Check the number of spaces being reported as being available
			is as expected, and force an assert if not. */
			if( uxReturn != ( uxQueueLength - x ) )
			{
				/* xQueue cannot be NULL so this is deliberately causing an
				assert to be triggered as there is an error. */
				configASSERT( xQueue == NULL );
			}

			/* Fill one more space in the queue. */
			xQueueSendToBack( xQueue, NULL, 0 );
		}

		/* Perform the same check while the queue is full. */
		uxReturn = uxQueueMessagesWaiting( xQueue );
		if( uxReturn != uxQueueLength )
		{
			configASSERT( xQueue == NULL );
		}

		uxReturn = uxQueueSpacesAvailable( xQueue );

		if( uxReturn != 0 )
		{
			configASSERT( xQueue == NULL );
		}

		/* The queue is full, start again. */
		xQueueReset( xQueue );

		#if( configUSE_PREEMPTION == 0 )
			taskYIELD();
		#endif
	}
}
/*-----------------------------------------------------------*/

static void prvPermanentlyBlockingSemaphoreTask( void *pvParameters )
{
SemaphoreHandle_t xSemaphore;

	/* Prevent compiler warning about unused parameter in the case that
	configASSERT() is not defined. */
	( void ) pvParameters;

	/* This task should block on a semaphore, and never return. */
	xSemaphore = xSemaphoreCreateBinary();
	configASSERT( xSemaphore );

	xSemaphoreTake( xSemaphore, portMAX_DELAY );

	/* The above xSemaphoreTake() call should never return, force an assert if
	it does. */
	configASSERT( pvParameters != NULL );
	vTaskDelete( NULL );
}
/*-----------------------------------------------------------*/

static void prvPermanentlyBlockingNotificationTask( void *pvParameters )
{
	/* Prevent compiler warning about unused parameter in the case that
	configASSERT() is not defined. */
	( void ) pvParameters;

	/* This task should block on a task notification, and never return. */
	ulTaskNotifyTake( pdTRUE, portMAX_DELAY );

	/* The above ulTaskNotifyTake() call should never return, force an assert
	if it does. */
	configASSERT( pvParameters != NULL );
	vTaskDelete( NULL );
}



