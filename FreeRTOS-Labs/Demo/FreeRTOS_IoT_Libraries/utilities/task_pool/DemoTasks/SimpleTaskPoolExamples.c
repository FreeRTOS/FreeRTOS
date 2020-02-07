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


/* Kernel includes. */
#include "FreeRTOS.h"
#include "task.h"

/* Standard includes. */
#include <stdio.h>

/* IoT SDK includes. */
#include "iot_taskpool_freertos.h"

/* Demo includes. */
#include "demo_config.h"

/* The priority at which that tasks in the task pool (the worker tasks) get
created. */
#define tpTASK_POOL_WORKER_PRIORITY		1

/*
 * Prototypes for the functions that demonstrate the task pool API.
 * See the implementation of the prvTaskPoolDemoTask() function within this file
 * for a description of the individual functions.  A configASSERT() is hit if
 * any of the demos encounter any unexpected behavior.
 */
static void prvExample_BasicSingleJob( void );
static void prvExample_DeferredJobAndCancellingJobs( void );

/*
 * Prototypes of the callback functions used in the examples.  The callback
 * simply sends a signal (in the form of a direct task notification) to the
 * prvTaskPoolDemoTask() task to let the task know that the callback execute.
 * The handle of the prvTaskPoolDemoTask() task is not accessed directly, but
 * instead passed into the task pool job as the job's context.
 */
static void prvSimpleTaskNotifyCallback( IotTaskPool_t pTaskPool, IotTaskPoolJob_t pJob, void *pUserContext );

/*
 * The task used to demonstrate the task pool API.  This task just loops through
 * each demo in turn.
 */
static void prvTaskPoolDemoTask( void *pvParameters );

/*-----------------------------------------------------------*/

/* Parameters used to create the system task pool - see TBD for more information
 * as the task pool used in this example is a slimmed down version of the full
 * library - the slimmed down version being intended specifically for FreeRTOS
 * kernel use cases. */
static const IotTaskPoolInfo_t xTaskPoolParameters = {
														/* minThreads:
														 * Minimum number of threads in a task pool.
														 * Note the slimmed down version of the task
														 * pool used by this library does not auto-scale
														 * the number of tasks in the pool so in this
														 * case this sets the number of tasks in the
														 * pool. */
														IOT_TASKPOOL_NUMBER_OF_WORKERS,
														/* maxThreads:
														 * Maximum number of threads in a task pool.
														 * Note the slimmed down version of the task
														 * pool used by this library does not auto-scale
														 * the number of tasks in the pool so in this
														 * case this parameter must match minThreads. */
														IOT_TASKPOOL_NUMBER_OF_WORKERS,
														/* Stack size for every task pool thread - in
														 * bytes, hence multiplying by the number of bytes
														 * in a word as configMINIMAL_STACK_SIZE is
														 * specified in words. */
														configMINIMAL_STACK_SIZE * sizeof( portSTACK_TYPE ),
														/* Priority for every task pool thread. */
														tpTASK_POOL_WORKER_PRIORITY,
													 };

/*-----------------------------------------------------------*/

void vStartSimpleTaskPoolDemo( void )
{
	/* This example uses a single application task, which in turn is used to
	 * create and send jobs to task pool tasks. */
	xTaskCreate( prvTaskPoolDemoTask,		/* Function that implements the task. */
				 "PoolDemo",				/* Text name for the task - only used for debugging. */
				 democonfigDEMO_STACKSIZE,	/* Size of stack (in words, not bytes) to allocate for the task. */
				 NULL,						/* Task parameter - not used in this case. */
				 tskIDLE_PRIORITY,			/* Task priority, must be between 0 and configMAX_PRIORITIES - 1. */
				 NULL );					/* Used to pass out a handle to the created task - not used in this case. */
}
/*-----------------------------------------------------------*/

static void prvTaskPoolDemoTask( void *pvParameters )
{
IotTaskPoolError_t xResult;
uint32_t ulLoops = 0;

	/* Remove compiler warnings about unused parameters. */
	( void ) pvParameters;

	configPRINTF( ( "---------STARTING DEMO---------\r\n" ) );

	/* The task pool must be created before it can be used.  The system task
	 * pool is the task pool managed by the task pool library itself - the storage
	 * used by the task pool is provided by the library. */
	xResult = IotTaskPool_CreateSystemTaskPool( &xTaskPoolParameters );
	configASSERT( xResult == IOT_TASKPOOL_SUCCESS );

	for( ;; )
	{
		/* Demonstrate the most basic use case where a non persistent job is
		 * created and scheduled to run immediately.  The task pool worker tasks
		 * (in which the job callback function executes) have a priority above the
		 * priority of this task so the job's callback executes as soon as it is
		 * scheduled. */
		prvExample_BasicSingleJob();

		/* Demonstrate a job being scheduled to run at some time in the
		 * future, and how a job scheduled to run in the future can be canceled
		 * if it has not yet started executing.  */
		prvExample_DeferredJobAndCancellingJobs();

		ulLoops++;
		if( ( ulLoops % 10UL ) == 0 )
		{
			configPRINTF( ( "prvTaskPoolDemoTask() performed %u iterations successfully.\r\n", ulLoops ) );
			configPRINTF( ( "Demo completed successfully.\r\n" ) );
			fflush( stdout );
		}
	}
}
/*-----------------------------------------------------------*/

static void prvSimpleTaskNotifyCallback( IotTaskPool_t pTaskPool, IotTaskPoolJob_t pJob, void *pUserContext )
{
/* The jobs context is the handle of the task to which a notification should
 * be sent. */
TaskHandle_t xTaskToNotify = ( TaskHandle_t ) pUserContext;

	/* Remove warnings about unused parameters. */
	( void ) pTaskPool;
	( void ) pJob;

	/* Notify the task that created this job. */
	xTaskNotifyGive( xTaskToNotify );
}
/*-----------------------------------------------------------*/

static void prvExample_BasicSingleJob( void )
{
IotTaskPoolJobStorage_t xJobStorage;
IotTaskPoolJob_t xJob;
IotTaskPoolError_t xResult;
uint32_t ulReturn;
const uint32_t ulNoFlags = 0UL;
const TickType_t xNoDelay = ( TickType_t ) 0;
size_t xFreeHeapBeforeCreatingJob = xPortGetFreeHeapSize();
IotTaskPoolJobStatus_t xJobStatus;

	/* Direct to task notifications are used to communicate between worker tasks
	and this task.  Don't expect any notifications to be pending before commencing. */
	configASSERT( ulTaskNotifyTake( pdTRUE, xNoDelay ) == 0 );

	/* Create and schedule a job using the handle of this task as the job's
	 * context and the function that sends a notification to the task handle as
	 * the job's callback function.  This is not a recyclable job so the storage
	 * required to hold information about the job is provided by this task - in
	 * this case the storage is on the stack of this task so no memory is allocated
	 * dynamically but the stack frame must remain in scope for the lifetime of
	 * the job. */
	xResult = IotTaskPool_CreateJob(  prvSimpleTaskNotifyCallback, /* Callback function. */
									  ( void * ) xTaskGetCurrentTaskHandle(), /* Job context. */
									  &xJobStorage,
									  &xJob );
	configASSERT( xResult == IOT_TASKPOOL_SUCCESS );

	/* The job has been created but not scheduled so is now ready. */
	IotTaskPool_GetStatus( NULL, xJob, &xJobStatus );
	configASSERT( xJobStatus == IOT_TASKPOOL_STATUS_READY );

	/* This is not a persistent (recyclable) job and its storage is on the
	 * stack of this function, so the amount of heap space available should not
	 * have changed since entering this function. */
	configASSERT( xFreeHeapBeforeCreatingJob == xPortGetFreeHeapSize() );

	/* In the full task pool implementation the first parameter is used to
	 * pass the handle of the task pool to schedule.  The lean task pool
	 * implementation used in this demo only supports a single task pool, which
	 * is created internally within the library, so the first parameter is NULL. */
	xResult = IotTaskPool_Schedule( NULL, xJob, ulNoFlags );
	configASSERT( xResult == IOT_TASKPOOL_SUCCESS );

	/* Look for the notification coming from the job's callback function.  The
	 * priority of the task pool worker task that executes the callback is higher
	 * than the priority of this task so a block time is not needed - the task pool
	 * worker task preempts this task and sends the notification (from the job's
	 * callback) as soon as the job is scheduled. */
	ulReturn = ulTaskNotifyTake( pdTRUE, xNoDelay );
	configASSERT( ulReturn );

	/* The job's callback has executed so the job has now completed. */
	IotTaskPool_GetStatus( NULL, xJob, &xJobStatus );
	configASSERT( xJobStatus == IOT_TASKPOOL_STATUS_COMPLETED );
}
/*-----------------------------------------------------------*/

static void prvExample_DeferredJobAndCancellingJobs( void )
{
IotTaskPoolJobStorage_t xJobStorage;
IotTaskPoolJob_t xJob;
IotTaskPoolError_t xResult;
uint32_t ulReturn;
const uint32_t ulShortDelay_ms = 100UL;
const TickType_t xNoDelay = ( TickType_t ) 0, xAllowableMargin = ( TickType_t ) 5; /* Large margin for Windows port, which is not real time. */
TickType_t xTimeBefore, xElapsedTime, xShortDelay_ticks;
size_t xFreeHeapBeforeCreatingJob = xPortGetFreeHeapSize();
IotTaskPoolJobStatus_t xJobStatus;

	/* Don't expect any notifications to be pending yet. */
	configASSERT( ulTaskNotifyTake( pdTRUE, xNoDelay ) == 0 );

	/* Create a job using the handle of this task as the job's context and the
	 * function that sends a notification to the task handle as the job's callback
	 * function.  The job is created using storage allocated on the stack of this
	 * function - so no memory is allocated. */
	xResult = IotTaskPool_CreateJob(  prvSimpleTaskNotifyCallback, /* Callback function. */
									  ( void * ) xTaskGetCurrentTaskHandle(), /* Job context. */
									  &xJobStorage,
									  &xJob );
	configASSERT( xResult == IOT_TASKPOOL_SUCCESS );

	/* The job has been created but not scheduled so is now ready. */
	IotTaskPool_GetStatus( NULL, xJob, &xJobStatus );
	configASSERT( xJobStatus == IOT_TASKPOOL_STATUS_READY );

	/* This is not a persistent (recyclable) job and its storage is on the
	 * stack of this function, so the amount of heap space available should not
	 * have changed since entering this function. */
	configASSERT( xFreeHeapBeforeCreatingJob == xPortGetFreeHeapSize() );

	/* Schedule the job to run its callback in ulShortDelay_ms milliseconds time.
	 * In the full task pool implementation the first parameter is used to	pass the
	 * handle of the task pool to schedule.  The lean task pool implementation used
	 * in this demo only supports a single task pool, which is created internally
	 * within the library, so the first parameter is NULL. */
	xResult = IotTaskPool_ScheduleDeferred( NULL, xJob, ulShortDelay_ms );
	configASSERT( xResult == IOT_TASKPOOL_SUCCESS );

	/* The scheduled job should not have executed yet, so don't expect any
	 * notifications and expect the job's status to be 'deferred'. */
	ulReturn = ulTaskNotifyTake( pdTRUE, xNoDelay );
	configASSERT( ulReturn == 0 );
	IotTaskPool_GetStatus( NULL, xJob, &xJobStatus );
	configASSERT( xJobStatus == IOT_TASKPOOL_STATUS_DEFERRED );

	/* As the job has not yet been executed it can be canceled. */
	xResult = IotTaskPool_TryCancel( NULL, xJob, &xJobStatus );
	configASSERT( xResult == IOT_TASKPOOL_SUCCESS );
	IotTaskPool_GetStatus( NULL, xJob, &xJobStatus );
	configASSERT( xJobStatus == IOT_TASKPOOL_STATUS_CANCELED );

	/* Schedule the job again, and this time wait until its callback is
	 * executed (the callback function sends a notification to this task) to see
	 * that it executes at the right time. */
	xTimeBefore = xTaskGetTickCount();
	xResult = IotTaskPool_ScheduleDeferred( NULL, xJob, ulShortDelay_ms );
	configASSERT( xResult == IOT_TASKPOOL_SUCCESS );

	/* Wait twice the deferred execution time to ensure the callback is executed
	 * before the call below times out. */
	ulReturn = ulTaskNotifyTake( pdTRUE, pdMS_TO_TICKS( ulShortDelay_ms * 2UL ) );
	xElapsedTime = xTaskGetTickCount() - xTimeBefore;

	/* A single notification should have been received... */
	configASSERT( ulReturn == 1 );

	/* ...and the time since scheduling the job should be greater than or
	 * equal to the deferred execution time - which is converted to ticks for
	 * comparison. */
	xShortDelay_ticks = pdMS_TO_TICKS( ulShortDelay_ms );
	configASSERT( ( xElapsedTime >= xShortDelay_ticks ) && ( xElapsedTime  < ( xShortDelay_ticks + xAllowableMargin ) ) );
}
/*-----------------------------------------------------------*/
