/*
 * FreeRTOS Kernel V10.2.1
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

/* Kernel includes. */
#include "FreeRTOS.h"
#include "task.h"

/* Standard includes. */
#include <stdio.h>

/* IoT SDK includes. */
#include "iot_taskpool.h"

/* The priority at which that tasks in the task pool (the worker tasks) get
created. */
#define tpTASK_POOL_WORKER_PRIORITY		1

/*
 * Prototypes for the functions that demonstrate the task pool API.
 */
static void prvExample_BasicSingleJob( void );
static void prvExample_DeferredSingleJob( void );
static void prvExample_BasicRecyclableJob( void );
static void prvExample_ReuseRecyclableJobFromLowPriorityTask( void );
static void prvExample_ReuseRecyclableJobFromHighPriorityTask( void );

/* Prototypes of the callback functions used in the examples. */
static void prvSimpleTaskNotifyCallback( IotTaskPool_t pTaskPool, IotTaskPoolJob_t pJob, void *pUserContext );

/*
 * Prototypes for the standard FreeRTOS application hook (callback) functions
 * implemented within this file.  See http://www.freertos.org/a00016.html .
 */
void vApplicationMallocFailedHook( void );
void vApplicationIdleHook( void );
void vApplicationStackOverflowHook( TaskHandle_t pxTask, char *pcTaskName );
void vApplicationTickHook( void );
void vApplicationGetIdleTaskMemory( StaticTask_t **ppxIdleTaskTCBBuffer, StackType_t **ppxIdleTaskStackBuffer, uint32_t *pulIdleTaskStackSize );
void vApplicationGetTimerTaskMemory( StaticTask_t **ppxTimerTaskTCBBuffer, StackType_t **ppxTimerTaskStackBuffer, uint32_t *pulTimerTaskStackSize );

/*
 * The task used to demonstrate the task pool API.
 */
static void prvTaskPoolDemoTask( void *pvParameters );

static const IotTaskPoolInfo_t xTaskPoolParameters = {
														/* Minimum number of threads in a task pool. */
														2,
														/* Maximum number of threads in a task pool. */
														2,
														/* Stack size for every task pool thread - in words, not bytes. */
														configMINIMAL_STACK_SIZE,
														/* Priority for every task pool thread. */
														tpTASK_POOL_WORKER_PRIORITY,
													 };

/*-----------------------------------------------------------*/

int main( void )
{
	/* This example uses a single application task, which in turn is used to
	create and send jobs to task pool tasks. */
	xTaskCreate( prvTaskPoolDemoTask,		/* Function that implements the task. */
				 "PoolDemo",				/* Text name for the task - only used for debugging. */
				 configMINIMAL_STACK_SIZE,	/* Size of stack (in words, not bytes) to allocate for the task. */
				 NULL,						/* Task parameter - not used in this case. */
				 tskIDLE_PRIORITY,			/* Task priority, must be between 0 and configMAX_PRIORITIES - 1. */
				 NULL );					/* Used to pass out a handle to the created tsak - not used in this case. */

	vTaskStartScheduler();

	/* Should not reach here as vTaskStartScheduler() will only return if there
	was insufficient FreeRTOS heap memory to create the Idle or Timer
	Daemon task. */
	return 0;
}
/*-----------------------------------------------------------*/

static void prvTaskPoolDemoTask( void *pvParameters )
{
IotTaskPoolError_t xResult;
uint32_t ulLoops;

	/* Remove compiler warnings about unused parameters. */
	( void ) pvParameters;

	/* The task pool must be created before it can be used. */
	xResult = IotTaskPool_CreateSystemTaskPool( &xTaskPoolParameters );
	configASSERT( xResult == IOT_TASKPOOL_SUCCESS );

	/* Attempting to create the task pool again should then appear to succeed
	(in case it is initialised by more than one library), but have no effect. */
	xResult = IotTaskPool_CreateSystemTaskPool( &xTaskPoolParameters );
	configASSERT( xResult == IOT_TASKPOOL_SUCCESS );

	for( ;; )
	{
		/* Demonstrate the most basic use case where a non persistent job is
		created and scheduled to run immediately.  The task pool worker tasks
		(in which the job callback function executes) have a priority above the
		priority of this task so the job's callback executes as soon as it is
		scheduled. */
		prvExample_BasicSingleJob();

		/* Demonstrate a job being scheduled to run at some time in the
		future, and how a job scheduled to run in the future can be cancelled if
		it has not yet started executing.  */
		prvExample_DeferredSingleJob();

		/* Demonstrate the most basic use of a recyclable job.  This is similar
		to prvExample_BasicSingleJob() but using a recyclable job.  Creating a
		recyclable job will re-use a previously created and now spare job from
		the task pool's job cache if one is available, or otherwise dynamically
		create a new job if a spare job is not available in the cache but space
		remains in the cache. */
		prvExample_BasicRecyclableJob();

		/* Demonstrate multiple recyclable jobs being created, used, and then
		re-used.  In this the task pool worker tasks (in which the job callback
		functions execute) have a priority above the priority of this task so
		the job's callback functions execute as soon as they are scheduled. */
		prvExample_ReuseRecyclableJobFromLowPriorityTask();

		/* Again demonstrate multiple recyclable jobs being used, but this time
		the priority of the task pool worker tasks (in which the job callback
		functions execute) are lower than the priority of this task so the job's
		callback functions don't execute until this task enteres the blocked
		state. */
		prvExample_ReuseRecyclableJobFromHighPriorityTask();

		ulLoops++;
		if( ( ulLoops % 10UL ) == 0 )
		{
			printf( "Performed %u successful iterations.\r\n", ulLoops );
			fflush( stdout );
		}
	}
}
/*-----------------------------------------------------------*/

static void prvSimpleTaskNotifyCallback( IotTaskPool_t pTaskPool, IotTaskPoolJob_t pJob, void *pUserContext )
{
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

	/* Don't expect any notifications to be pending yet. */
	configASSERT( ulTaskNotifyTake( pdTRUE, 0 ) == 0 );

	/* Create and schedule a job using the handle of this task as the job's
	context and the function that sends a notification to the task handle as
	the jobs callback function.  The job is created using storage allocated on
	the stack of this function - so no memory is allocated. */
	xResult = IotTaskPool_CreateJob(  prvSimpleTaskNotifyCallback, /* Callback function. */
									  ( void * ) xTaskGetCurrentTaskHandle(), /* Job context. */
									  &xJobStorage,
									  &xJob );
	configASSERT( xResult == IOT_TASKPOOL_SUCCESS );

	/* The job has been created but not scheduled so is now ready. */
	IotTaskPool_GetStatus( NULL, xJob, &xJobStatus );
	configASSERT( xJobStatus == IOT_TASKPOOL_STATUS_READY );

	/* This is not a persistent (recyclable) job and its storage is on the
	stack of this function, so the amount of heap space available should not
	have chanced since entering this function. */
	configASSERT( xFreeHeapBeforeCreatingJob == xPortGetFreeHeapSize() );

	/* In the full task pool implementation the first parameter is used to
	pass the handle of the task pool to schedule.  The lean task pool
	implementation used in this demo only supports a single task pool, which
	is created internally within the library, so the first parameter is NULL. */
	xResult = IotTaskPool_Schedule( NULL, xJob, ulNoFlags );
	configASSERT( xResult == IOT_TASKPOOL_SUCCESS );

	/* Look for the notification coming from the job's callback function.  The
	priority of the task pool worker task that executes the callback is higher
	than the priority of this task so a block time is not needed - the task pool
	worker task	pre-empts this task and sends the notification (from the job's
	callback) as soon as the job is scheduled. */
	ulReturn = ulTaskNotifyTake( pdTRUE, xNoDelay );
	configASSERT( ulReturn );

	/* The job's callback has executed so the job has now completed. */
	IotTaskPool_GetStatus( NULL, xJob, &xJobStatus );
	configASSERT( xJobStatus == IOT_TASKPOOL_STATUS_COMPLETED );
}
/*-----------------------------------------------------------*/

static void prvExample_DeferredSingleJob( void )
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
	configASSERT( ulTaskNotifyTake( pdTRUE, 0 ) == 0 );

	/* Create a job using the handle of this task as the job's context and the
	function that sends a notification to the task handle as the jobs callback
	function.  The job is created using storage allocated on the stack of this
	function - so no memory is allocated. */
	xResult = IotTaskPool_CreateJob(  prvSimpleTaskNotifyCallback, /* Callback function. */
									  ( void * ) xTaskGetCurrentTaskHandle(), /* Job context. */
									  &xJobStorage,
									  &xJob );
	configASSERT( xResult == IOT_TASKPOOL_SUCCESS );

	/* The job has been created but not scheduled so is now ready. */
	IotTaskPool_GetStatus( NULL, xJob, &xJobStatus );
	configASSERT( xJobStatus == IOT_TASKPOOL_STATUS_READY );

	/* This is not a persistent (recyclable) job and its storage is on the
	stack of this function, so the amount of heap space available should not
	have chanced since entering this function. */
	configASSERT( xFreeHeapBeforeCreatingJob == xPortGetFreeHeapSize() );

	/* Schedule the job to run its callback in xShortDelay_ms milliseconds time.
	In the full task pool implementation the first parameter is used to	pass the
	handle of the task pool to schedule.  The lean task pool implementation used
	in this demo only supports a single task pool, which is created internally
	within the library, so the first parameter is NULL. */
	xResult = IotTaskPool_ScheduleDeferred( NULL, xJob, ulShortDelay_ms );
	configASSERT( xResult == IOT_TASKPOOL_SUCCESS );

	/* The scheduled job should not have executed yet, so don't expect any
	notifications and expect the job's status to be 'deferred'. */
	ulReturn = ulTaskNotifyTake( pdTRUE, xNoDelay );
	configASSERT( ulReturn == 0 );
	IotTaskPool_GetStatus( NULL, xJob, &xJobStatus );
	configASSERT( xJobStatus == IOT_TASKPOOL_STATUS_DEFERRED );

	/* As the job has not yet been executed it can be stopped. */
	xResult = IotTaskPool_TryCancel( NULL, xJob, &xJobStatus );
	configASSERT( xResult == IOT_TASKPOOL_SUCCESS );
	IotTaskPool_GetStatus( NULL, xJob, &xJobStatus );
	configASSERT( xJobStatus == IOT_TASKPOOL_STATUS_CANCELED );

	/* Schedule the job again, and this time wait until its callback is
	executed (the callback function sends a notification to this task) to see
	that it executes at the right time. */
	xTimeBefore = xTaskGetTickCount();
	xResult = IotTaskPool_ScheduleDeferred( NULL, xJob, ulShortDelay_ms );
	configASSERT( xResult == IOT_TASKPOOL_SUCCESS );

	/* Wait twice the deferred execution time to ensure the callback is executed
	before the call below times out. */
	ulReturn = ulTaskNotifyTake( pdTRUE, pdMS_TO_TICKS( ulShortDelay_ms * 2UL ) );
	xElapsedTime = xTaskGetTickCount() - xTimeBefore;

	/* A single notification should not have been received... */
	configASSERT( ulReturn == 1 );

	/* ...and the time since scheduling the job should be greater than or
	equal to the deferred execution time - which is converted to ticks for
	comparison. */
	xShortDelay_ticks = pdMS_TO_TICKS( ulShortDelay_ms );
	configASSERT( ( xElapsedTime >= xShortDelay_ticks ) && ( xElapsedTime  < ( xShortDelay_ticks + xAllowableMargin ) ) );
}
/*-----------------------------------------------------------*/

static void prvExample_BasicRecyclableJob( void )
{
IotTaskPoolJob_t xJob;
IotTaskPoolError_t xResult;
uint32_t ulReturn;
const uint32_t ulNoFlags = 0UL;
const TickType_t xNoDelay = ( TickType_t ) 0;
size_t xFreeHeapBeforeCreatingJob = xPortGetFreeHeapSize();

	/* Don't expect any notifications to be pending yet. */
	configASSERT( ulTaskNotifyTake( pdTRUE, 0 ) == 0 );

	/* Create and schedule a job using the handle of this task as the job's
	context and the function that sends a notification to the task handle as
	the jobs callback function.  The job is created as a recyclable job and in
	this case the memory used to hold the job status is allocated inside the
	create function.  As the job is persistent it can be used multiple times,
	as demonstrated in other examples within this demo.  In the full task pool
	implementation the first parameter is used to pass the handle of the task
	pool this recyclable job is to be associated with.  In the lean
	implementation of the task pool used by this demo there	is only one task
	pool (the system task pool created within the task pool library) so the
	first parameter is NULL. */
	xResult = IotTaskPool_CreateRecyclableJob( NULL,
											   prvSimpleTaskNotifyCallback,
											   (void * ) xTaskGetCurrentTaskHandle(),
											   &xJob );
	configASSERT( xResult == IOT_TASKPOOL_SUCCESS );

	/* This recyclable job is persistent, and in this case created dynamically,
	so expect there to be less heap space then when entering the function. */
	configASSERT( xPortGetFreeHeapSize() < xFreeHeapBeforeCreatingJob );

	/* In the full task pool implementation the first parameter is used to
	pass the handle of the task pool to schedule.  The lean task pool
	implementation used in this demo only supports a single task pool, which
	is created internally within the library, so the first parameter is NULL. */
	xResult = IotTaskPool_Schedule( NULL, xJob, ulNoFlags );
	configASSERT( xResult == IOT_TASKPOOL_SUCCESS );

	/* Look for the notification coming from the job's callback function.  The
	priority of the task pool worker task that executes the callback is higher
	than the priority of this task so a block time is not needed - the task pool
	worker task	pre-empts this task and sends the notification (from the job's
	callback) as soon as the job is scheduled. */
	ulReturn = ulTaskNotifyTake( pdTRUE, xNoDelay );
	configASSERT( ulReturn );

	/* Clean up recyclable job.  In the full implementation of the task pool
	the first parameter is used to pass a handle to the task pool the job is
	associated with.  In the lean implementation of the task pool used by this
	demo there is only one task pool (the system task pool created in the
	task pool library itself) so the first parameter is NULL. */
	IotTaskPool_DestroyRecyclableJob( NULL, xJob );

	/* Once the job has been deleted the memory used to hold the job is
	returned, so the available heap should be exactly as when entering this
	function. */
	configASSERT( xPortGetFreeHeapSize() == xFreeHeapBeforeCreatingJob );
}
/*-----------------------------------------------------------*/

static void prvExample_ReuseRecyclableJobFromLowPriorityTask( void )
{
IotTaskPoolError_t xResult;
uint32_t x, xIndex, ulNotificationValue;
const uint32_t ulJobsToCreate = 5UL, ulNoFlags = 0UL;
IotTaskPoolJob_t xJobs[ ulJobsToCreate ];
size_t xFreeHeapBeforeCreatingJob = xPortGetFreeHeapSize();
IotTaskPoolJobStatus_t xJobStatus;

	/* Don't expect any notifications to be pending yet. */
	configASSERT( ulTaskNotifyTake( pdTRUE, 0 ) == 0 );

	/* Create ulJobsToCreate jobs using the handle of this task as the job's
	context and the function that sends a notification to the task handle as
	the jobs callback function.  The jobs are created as a recyclable job and
	in this case the memory to store the job information is allocated within
	the create function as at this time there are no recyclable jobs in the
	task pool jobs cache. As the jobs are persistent they can be used multiple
	times.  In the full task pool implementation the first parameter is used to
	pass the handle of the task pool this recyclable job is to be associated
	with.  In the lean implementation of the task pool used by this demo there
	is only one task pool (the system task pool created within the task pool
	library) so the first parameter is NULL. */
	for( x = 0; x < ulJobsToCreate; x++ )
	{
		xResult = IotTaskPool_CreateRecyclableJob( NULL,
												   prvSimpleTaskNotifyCallback,
												   (void * ) xTaskGetCurrentTaskHandle(),
												   &( xJobs[ x ] ) );
		configASSERT( xResult == IOT_TASKPOOL_SUCCESS );

		/* The job has been created but not scheduled so is now ready. */
		IotTaskPool_GetStatus( NULL, xJobs[ x ], &xJobStatus );
		configASSERT( xJobStatus == IOT_TASKPOOL_STATUS_READY );
	}

	/* Demonstrate that the jobs can be recycled by performing twice the number
	of iterations of scheduling jobs than there actually are created jobs.  This
	works because the task pool task priorities are above the priority of this
	task, so the tasks that run the jobs pre-empt this task as soon as a job is
	ready. */
	for( x = 0; x < ( ulJobsToCreate * 2UL ); x++ )
	{
		/* Make sure array index does not go out of bounds. */
		xIndex = x % ulJobsToCreate;

		xResult = IotTaskPool_Schedule( NULL, xJobs[ xIndex ], ulNoFlags );
		configASSERT( xResult == IOT_TASKPOOL_SUCCESS );

		/* The priority of the task pool task(s) is higher than the priority
		of this task, so the job's callback function should have already
		executed, sending a notification to this task, and incrementing this
		task's notification value. */
		xTaskNotifyWait( 0UL, /* Don't clear any bits on entry. */
						 0UL, /* Don't clear any bits on exit. */
						 &ulNotificationValue, /* Obtain the notification value. */
						 0UL ); /* No block time, return immediately. */
		configASSERT( ulNotificationValue == ( x + 1 ) );

		/* The job's callback has executed so the job is now completed. */
		IotTaskPool_GetStatus( NULL, xJobs[ xIndex ], &xJobStatus );
		configASSERT( xJobStatus == IOT_TASKPOOL_STATUS_COMPLETED );

		/* To leave the list of jobs empty we can stop re-creating jobs half
		way through iterations of this loop. */
		if( x < ulJobsToCreate )
		{
			/* Recycle the job so it can be used again.  In the full task pool
			implementation the first parameter is used to pass the handle of the
			task pool this job will be associated with.  In this lean task pool
			implementation only the system task pool exists (the task pool created
			internally to the task pool library) so the first parameter is just
			passed as NULL. *//*_RB_ Why not recycle it automatically? */
			IotTaskPool_RecycleJob( NULL, xJobs[ xIndex ] );
			xResult = IotTaskPool_CreateRecyclableJob( NULL,
													   prvSimpleTaskNotifyCallback,
													   (void * ) xTaskGetCurrentTaskHandle(),
													   &( xJobs[ xIndex ] ) );
		}
	}

	/* Clear all the notification value bits again. */
	xTaskNotifyWait( portMAX_DELAY, /* Clear all bits on entry - portMAX_DELAY is used as it is a portable way of having all bits set. */
					 0UL, /* Don't clear any bits on exit. */
					 NULL, /* Don't need the notification value this time. */
					 0UL ); /* No block time, return immediately. */
	configASSERT( ulTaskNotifyTake( pdTRUE, 0 ) == 0 );

	/* Clean up all the recyclable job.  In the full implementation of the task
	pool the first parameter is used to pass a handle to the task pool the job
	is associated with.  In the lean implementation of the task pool used by
	this demo there is only one task pool (the system task pool created in the
	task pool library itself) so the first parameter is NULL. */
	for( x = 0; x < ulJobsToCreate; x++ )
	{
		xResult = IotTaskPool_DestroyRecyclableJob( NULL, xJobs[ x ] );
		configASSERT( xResult == IOT_TASKPOOL_SUCCESS );

		/* Attempting to destroy the same job twice will fail. */
//_RB_ vPortFree() asserts because it attempts to free memory again.		xResult = IotTaskPool_DestroyRecyclableJob( NULL, xJobs[ x ] );
//		configASSERT( xResult != IOT_TASKPOOL_SUCCESS );
	}

	/* Once the job has been deleted the memory used to hold the job is
	returned, so the available heap should be exactly as when entering this
	function. */
	configASSERT( xPortGetFreeHeapSize() == xFreeHeapBeforeCreatingJob );
}
/*-----------------------------------------------------------*/

static void prvExample_ReuseRecyclableJobFromHighPriorityTask( void )
{
IotTaskPoolError_t xResult;
uint32_t x, ulNotificationValue;
const uint32_t ulJobsToCreate = 5UL;
const uint32_t ulNoFlags = 0UL;
IotTaskPoolJob_t xJobs[ ulJobsToCreate ];
IotTaskPoolJobStorage_t xJobStorage[ ulJobsToCreate ];
size_t xFreeHeapBeforeCreatingJob = xPortGetFreeHeapSize();
TickType_t xShortDelay = pdMS_TO_TICKS( 150 );
IotTaskPoolJobStatus_t xJobStatus;

	/* Don't expect any notifications to be pending yet. */
	configASSERT( ulTaskNotifyTake( pdTRUE, 0 ) == 0 );

	/* prvExample_ReuseRecyclableJobFromLowPriorityTask() executes in a task
	that has a lower [task] priority than the task pool's worker tasks.
	Therefore a talk pool worker preempts the task that calls
	prvExample_ReuseRecyclableJobFromHighPriorityTask() as soon as the job is
	scheduled.  prvExample_ReuseRecyclableJobFromHighPriorityTask() reverses the
	priorities - prvExample_ReuseRecyclableJobFromHighPriorityTask() raises its
	priority to above the task pool's worker tasks, so the worker tasks do not
	execute until the calling task enters the blocked state.  First raise the
	priority - passing NULL means raise the priority of the calling task. */
	vTaskPrioritySet( NULL, tpTASK_POOL_WORKER_PRIORITY + 1 );

	/* Create ulJobsToCreate jobs using the handle of this task as the job's
	context and the function that sends a notification to the task handle as
	the jobs callback function. */
	for( x = 0; x < ulJobsToCreate; x++ )
	{
		xResult = IotTaskPool_CreateJob(  prvSimpleTaskNotifyCallback, /* Callback function. */
										  ( void * ) xTaskGetCurrentTaskHandle(), /* Job context. */
										  &( xJobStorage[ x ] ),
										  &( xJobs[ x ] ) );
		configASSERT( xResult == IOT_TASKPOOL_SUCCESS );

		/* This is not a persistent (recyclable) job and its storage is on the
		stack of this function, so the amount of heap space available should not
		have chanced since entering this function. */
		configASSERT( xFreeHeapBeforeCreatingJob == xPortGetFreeHeapSize() );
	}

	for( x = 0; x < ulJobsToCreate; x++ )
	{
		/* Schedule the next job. */
		xResult = IotTaskPool_Schedule( NULL, xJobs[ x ], ulNoFlags );
		configASSERT( xResult == IOT_TASKPOOL_SUCCESS );

		/* Although scheduled, the job's callback has not executed, so the job
		reports itself as scheduled. */
		IotTaskPool_GetStatus( NULL, xJobs[ x ], &xJobStatus );
		configASSERT( xJobStatus == IOT_TASKPOOL_STATUS_SCHEDULED );

		/* The priority of the task pool task(s) is lower than the priority
		of this task, so the job's callback function should not have executed
		yes, so don't expect the notification value for this task to have
		changed. */
		xTaskNotifyWait( 0UL, /* Don't clear any bits on entry. */
						 0UL, /* Don't clear any bits on exit. */
						 &ulNotificationValue, /* Obtain the notification value. */
						 0UL ); /* No block time, return immediately. */
		configASSERT( ulNotificationValue == 0 );
	}

	/* At this point there are ulJobsToCreate scheduled, but none have executed
	their callbacks because the priority of this task is higher than the
	priority of the task pool worker threads.  When this task blocks to wait for
	a notification a worker thread will be able to executes - but as soon as its
	callback function sends a notification to this task this task will
	preempt it (because it has a higher priority) so this task only expects to
	receive one notification at a time. */
	for( x = 0; x < ulJobsToCreate; x++ )
	{
		xTaskNotifyWait( 0UL, /* Don't clear any bits on entry. */
						 0UL, /* Don't clear any bits on exit. */
						 &ulNotificationValue, /* Obtain the notification value. */
						 xShortDelay ); /* Short delay to allow a task pool worker to execute. */
		configASSERT( ulNotificationValue == ( x + 1 ) );
	}

	/* All the scheduled jobs have now executed, so waiting for another
	notification should timeout without the notification value changing. */
	xTaskNotifyWait( 0UL, /* Don't clear any bits on entry. */
					 0UL, /* Don't clear any bits on exit. */
					 &ulNotificationValue, /* Obtain the notification value. */
					 xShortDelay ); /* Short delay to allow a task pool worker to execute. */
	configASSERT( ulNotificationValue == x );

	/* Reset the priority of this task and clear the notifications ready for the
	next example. */
	vTaskPrioritySet( NULL, tskIDLE_PRIORITY );
	xTaskNotifyWait( portMAX_DELAY, /* Clear all bits on entry - portMAX_DELAY is used as it is a portable way of having all bits set. */
					 0UL, /* Don't clear any bits on exit. */
					 NULL, /* Don't need the notification value this time. */
					 0UL ); /* No block time, return immediately. */
}
/*-----------------------------------------------------------*/

void vApplicationMallocFailedHook( void )
{
	/* vApplicationMallocFailedHook() will only be called if
	configUSE_MALLOC_FAILED_HOOK is set to 1 in FreeRTOSConfig.h.  It is a hook
	function that will get called if a call to pvPortMalloc() fails.
	pvPortMalloc() is called internally by the kernel whenever a task, queue,
	timer or semaphore is created.  It is also called by various parts of the
	demo application.  If heap_1.c, heap_2.c or heap_4.c is being used, then the
	size of the	heap available to pvPortMalloc() is defined by
	configTOTAL_HEAP_SIZE in FreeRTOSConfig.h, and the xPortGetFreeHeapSize()
	API function can be used to query the size of free heap space that remains
	(although it does not provide information on how the remaining heap might be
	fragmented).  See http://www.freertos.org/a00111.html for more
	information. */
	vAssertCalled( __LINE__, __FILE__ );
}
/*-----------------------------------------------------------*/

void vApplicationIdleHook( void )
{
	/* vApplicationIdleHook() will only be called if configUSE_IDLE_HOOK is set
	to 1 in FreeRTOSConfig.h.  It will be called on each iteration of the idle
	task.  It is essential that code added to this hook function never attempts
	to block in any way (for example, call xQueueReceive() with a block time
	specified, or call vTaskDelay()).  If application tasks make use of the
	vTaskDelete() API function to delete themselves then it is also important
	that vApplicationIdleHook() is permitted to return to its calling function,
	because it is the responsibility of the idle task to clean up memory
	allocated by the kernel to any task that has since deleted itself. */
}
/*-----------------------------------------------------------*/

void vApplicationStackOverflowHook( TaskHandle_t pxTask, char *pcTaskName )
{
	( void ) pcTaskName;
	( void ) pxTask;

	/* Run time stack overflow checking is performed if
	configCHECK_FOR_STACK_OVERFLOW is defined to 1 or 2.  This hook
	function is called if a stack overflow is detected.  This function is
	provided as an example only as stack overflow checking does not function
	when running the FreeRTOS Windows port. */
	vAssertCalled( __LINE__, __FILE__ );
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

void vApplicationDaemonTaskStartupHook( void )
{
	/* This function will be called once only, when the daemon task starts to
	execute	(sometimes called the timer task).  This is useful if the
	application includes initialisation code that would benefit from executing
	after the scheduler has been started. */
}
/*-----------------------------------------------------------*/

void vAssertCalled( unsigned long ulLine, const char * const pcFileName )
{
volatile uint32_t ulSetToNonZeroInDebuggerToContinue = 0;

	/* Called if an assertion passed to configASSERT() fails.  See
	http://www.freertos.org/a00110.html#configASSERT for more information. */

	/* Parameters are not used. */
	( void ) ulLine;
	( void ) pcFileName;


 	taskENTER_CRITICAL();
	{
 		printf( "Assert hit on line %lu of %s\r\n", ulLine, pcFileName );
 		fflush( stdout );

		/* You can step out of this function to debug the assertion by using
		the debugger to set ulSetToNonZeroInDebuggerToContinue to a non-zero
		value. */
		while( ulSetToNonZeroInDebuggerToContinue == 0 )
		{
			__asm volatile( "NOP" );
			__asm volatile( "NOP" );
		}
	}
	taskEXIT_CRITICAL();
}
/*-----------------------------------------------------------*/

/* configUSE_STATIC_ALLOCATION is set to 1, so the application must provide an
implementation of vApplicationGetIdleTaskMemory() to provide the memory that is
used by the Idle task. */
void vApplicationGetIdleTaskMemory( StaticTask_t **ppxIdleTaskTCBBuffer, StackType_t **ppxIdleTaskStackBuffer, uint32_t *pulIdleTaskStackSize )
{
/* If the buffers to be provided to the Idle task are declared inside this
function then they must be declared static - otherwise they will be allocated on
the stack and so not exists after this function exits. */
static StaticTask_t xIdleTaskTCB;
static StackType_t uxIdleTaskStack[ configMINIMAL_STACK_SIZE ];

	/* Pass out a pointer to the StaticTask_t structure in which the Idle task's
	state will be stored. */
	*ppxIdleTaskTCBBuffer = &xIdleTaskTCB;

	/* Pass out the array that will be used as the Idle task's stack. */
	*ppxIdleTaskStackBuffer = uxIdleTaskStack;

	/* Pass out the size of the array pointed to by *ppxIdleTaskStackBuffer.
	Note that, as the array is necessarily of type StackType_t,
	configMINIMAL_STACK_SIZE is specified in words, not bytes. */
	*pulIdleTaskStackSize = configMINIMAL_STACK_SIZE;
}
/*-----------------------------------------------------------*/

/* configUSE_STATIC_ALLOCATION and configUSE_TIMERS are both set to 1, so the
application must provide an implementation of vApplicationGetTimerTaskMemory()
to provide the memory that is used by the Timer service task. */
void vApplicationGetTimerTaskMemory( StaticTask_t **ppxTimerTaskTCBBuffer, StackType_t **ppxTimerTaskStackBuffer, uint32_t *pulTimerTaskStackSize )
{
/* If the buffers to be provided to the Timer task are declared inside this
function then they must be declared static - otherwise they will be allocated on
the stack and so not exists after this function exits. */
static StaticTask_t xTimerTaskTCB;
static StackType_t uxTimerTaskStack[ configTIMER_TASK_STACK_DEPTH ];

	/* Pass out a pointer to the StaticTask_t structure in which the Timer
	task's state will be stored. */
	*ppxTimerTaskTCBBuffer = &xTimerTaskTCB;

	/* Pass out the array that will be used as the Timer task's stack. */
	*ppxTimerTaskStackBuffer = uxTimerTaskStack;

	/* Pass out the size of the array pointed to by *ppxTimerTaskStackBuffer.
	Note that, as the array is necessarily of type StackType_t,
	configMINIMAL_STACK_SIZE is specified in words, not bytes. */
	*pulTimerTaskStackSize = configTIMER_TASK_STACK_DEPTH;
}

