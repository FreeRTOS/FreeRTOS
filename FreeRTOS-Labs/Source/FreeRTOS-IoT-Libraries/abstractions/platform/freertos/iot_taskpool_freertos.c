/*
 * FreeRTOS Task Pool v1.0.0
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
 */

/**
 * @file iot_taskpool_freertos.c
 * @brief Implements the task pool functions in iot_taskpool.h for FreeRTOS.
 */


/*
 * The full IoT Task Pool Library has many use cases, including Linux development.
 * Typical FreeRTOS use cases do not require the full functionality so an optimized
 * implementation is provided specifically for use with FreeRTOS.  The optimized
 * version has a fixed number of tasks in the pool, each of which uses statically
 * allocated memory to ensure creation of the pool is guaranteed (it does not run out
 * of heap space).  The constant IOT_TASKPOOL_NUMBER_OF_WORKERS sets the number of
 * tasks in the pool.
 *
 * Unlike the full version, this optimized version:
 *   + Only supports a single task pool (system task pool) at a time.
 *   + Does not auto-scale by dynamically adding more tasks if the number of
 *     tasks in the pool becomes exhausted.  The number of tasks in the pool
 *     are fixed at compile time. See the task pool configuration options for
 *     more information.
 *   + Cannot be shut down - it exists for the lifetime of the application.
 *
 * Users who are interested in the functionality of the full IoT Task Pool
 * library can us it in place of this optimized version.
 */


/* Kernel includes. */
#include "FreeRTOS.h"
#include "semphr.h"

/* IoT libraries includes. */
#include "iot_config.h"

/* Standard includes. */
#include <stdbool.h>
#include <stdio.h>
#include <stddef.h>
#include <stdint.h>
#include <string.h>

#if !defined( configSUPPORT_STATIC_ALLOCATION ) || ( configSUPPORT_STATIC_ALLOCATION != 1 )
    #error configSUPPORT_STATIC_ALLOCATION must be set to 1 in FreeRTOSConfig.h to build this file.
#endif

/* Task pool internal include. */
#include "private/iot_taskpool_internal_freertos.h"

/**
 * @brief Maximum semaphore value for wait operations.
 */
#define TASKPOOL_MAX_SEM_VALUE              ( ( UBaseType_t ) 0xFFFF )

/**
 * @brief Reschedule delay in milliseconds for deferred jobs.
 */
#define TASKPOOL_JOB_RESCHEDULE_DELAY_MS    ( 10ULL )

/* ---------------------------------------------------------------------------------- */

/**
 * @brief Get the job associated with a timer.
 *
 * @warning This only works on a _taskPoolTimerEvent_t within a _taskPoolJob_t.
 */
#define GET_JOB_FROM_TIMER(t) ((_taskPoolJob_t *)((uint8_t*)(t) - offsetof(_taskPoolJob_t, timer)))

/**
 * brief The maximum time to wait when attempting to obtain an internal semaphore.
 * Don't wait indefinitely to give the application a chance to recover in the case
 * of an error.
 */
#define MAX_SEMAPHORE_TAKE_WAIT_TIME_MS ( pdMS_TO_TICKS( 10000UL ) )
/* ---------------------------------------------------------------------------------- */

/**
 * Doxygen should ignore this section.
 *
 * @brief The system task pool handle for all libraries to use.
 * User application can use the system task pool as well knowing that the usage will be shared with
 * the system libraries as well. The system task pool needs to be initialized before any library is used or
 * before any code that posts jobs to the task pool runs.
 */
static _taskPool_t _IotSystemTaskPool = { 0 };

/* -------------- Convenience functions to create/recycle/destroy jobs -------------- */

/**
 * @brief Initialize a job.
 *
 * @param[in] pJob The job to initialize.
 * @param[in] userCallback The user callback for the job.
 * @param[in] pUserContext The context to be passed to the callback.
 */
static void _initializeJob( _taskPoolJob_t * const pJob,
                            IotTaskPoolRoutine_t userCallback,
                            void * pUserContext );

/* -------------- The worker thread procedure for a task pool thread -------------- */

/**
 * The procedure for a task pool worker thread.
 *
 * @param[in] pUserContext The user context.
 *
 */
static void _taskPoolWorker( void * pUserContext );

/* -------------- Convenience functions to handle timer events  -------------- */

/**
 * Comparer for the time list.
 *
 * param[in] pTimerEventLink1 The link to the first timer event.
 * param[in] pTimerEventLink1 The link to the first timer event.
 */
static int32_t _timerEventCompare( const IotLink_t * const pTimerEventLink1,
                                   const IotLink_t * const pTimerEventLink2 );

/**
 * Reschedules the timer for handling deferred jobs to the next timeout.
 *
 * param[in] timer The timer to reschedule.
 * param[in] pFirstTimerEvent The timer event that carries the timeout and job information.
 */
static void _rescheduleDeferredJobsTimer( TimerHandle_t const timer,
                                          _taskPoolTimerEvent_t * const pFirstTimerEvent );

/**
 * The task pool timer procedure for scheduling deferred jobs.
 *
 * param[in] timer The timer to handle.
 */
static void _timerCallback( TimerHandle_t xTimer );

/* -------------- Convenience functions to create/initialize/destroy the task pool -------------- */

/**
 * Initializes a pre-allocated instance of a task pool.
 */
static void _initTaskPoolControlStructures( void );

/**
 * Initializes a pre-allocated instance of a task pool.
 *
 * @param[in] pInfo The initialization information for the task pool.
 *
 */
static IotTaskPoolError_t _createTaskPool( const IotTaskPoolInfo_t * const pInfo );

/**
 * Places a job in the dispatch queue.
 *
 * @param[in] pJob The job to schedule.
 *
 */
static void _scheduleInternal( _taskPoolJob_t * const pJob );
/**
 * Matches a deferred job in the timer queue with its timer event wrapper.
 *
 * @param[in] pLink A pointer to the timer event link in the timer queue.
 * @param[in] pMatch A pointer to the job to match.
 *
 */
static bool _matchJobByPointer( const IotLink_t * const pLink,
                                void * pMatch );

/**
 * Tries to cancel a job.
 *
 * @param[in] pJob The job to cancel.
 * @param[out] pStatus The status of the job at the time of cancellation.
 *
 */
static IotTaskPoolError_t _tryCancelInternal( _taskPoolJob_t * const pJob,
                                              IotTaskPoolJobStatus_t * const pStatus );

/* ---------------------------------------------------------------------------------------------- */

IotTaskPoolError_t IotTaskPool_CreateSystemTaskPool( const IotTaskPoolInfo_t * const pInfo )
{
    IotTaskPoolError_t status;
    static BaseType_t isInitialized = pdFALSE;

    configASSERT( pInfo );
    configASSERT( pInfo->minThreads >= 1UL );

    /* This version of the task pool does not auto-scale so the specified minimum
    number of threads in the pool must match the specified maximum number of threads
    in the pool. */
    configASSERT( pInfo->maxThreads == pInfo->minThreads );

    /* Guard against multiple attempts to create the system task pool in case
    this function is called by more than one library initialization routine. */
    taskENTER_CRITICAL();
    {
        /* If the task pool has already been initialized then
        IOT_TASKPOOL_ILLEGAL_OPERATION will be returned - but that does not guarantee
        the initialization operation is complete as the task to which
        IOT_TASKPOOL_ILLEGAL_OPERATION is returned may have preempted the task that
        was performing the initialization before the initialization was complete -
        hence the assert to catch this occurrence during development and debug. */
        configASSERT( isInitialized == pdFALSE );

        if( isInitialized == pdFALSE )
        {
            /* The task pool has not been initialized already so will be initialized
            now. */
            status = IOT_TASKPOOL_SUCCESS;
            isInitialized = pdTRUE;
        }
        else
        {
            /* This function has already been called but executing this path does
            not guarantee the task pool has already been initialized as the task
            to which this error is returned may have preempted the task that was
            performing the initialization before the initialization was complete. */
            status = IOT_TASKPOOL_ILLEGAL_OPERATION;
        }
    }
    taskEXIT_CRITICAL();

    if( status == IOT_TASKPOOL_SUCCESS )
    {
        /* Create the system task pool.  Note in this version _createTaskPool()
        cannot fail because it is using statically allocated memory.  Therefore the
        return value can be safely ignored and there is no need to consider resetting
        isInitialized in a failure case. */
        ( void ) _createTaskPool( pInfo );
    }

    return status;
}
/*-----------------------------------------------------------*/

IotTaskPoolError_t IotTaskPool_CreateJob( IotTaskPoolRoutine_t userCallback,
                                          void * pUserContext,
                                          IotTaskPoolJobStorage_t * const pJobStorage,
                                          IotTaskPoolJob_t * const ppJob )
{
    /* Parameter checking. */
    configASSERT( userCallback != NULL );
    configASSERT( pJobStorage != NULL );
    configASSERT( ppJob != NULL );

    /* Build a job around the user-provided storage. */
    _initializeJob( ( _taskPoolJob_t * ) pJobStorage, userCallback, pUserContext );

    *ppJob = ( IotTaskPoolJob_t ) pJobStorage;

    return IOT_TASKPOOL_SUCCESS;
}

/*-----------------------------------------------------------*/

IotTaskPoolError_t IotTaskPool_Schedule( IotTaskPool_t taskPoolHandle,
                                         IotTaskPoolJob_t pJob,
                                         uint32_t flags )
{
    IotTaskPoolError_t status = IOT_TASKPOOL_SUCCESS;

    /* Task pool must have been created. */
    configASSERT( _IotSystemTaskPool.running != false );

    /* This lean version of the task pool only supports the task pool created
    by this library (the system task pool).  NULL means use the system task
    pool - no other values are allowed.  Use the full implementation of this
    library if you want multiple task pools (there is more than one task in
    each pool. */
    configASSERT( ( taskPoolHandle == NULL ) || ( taskPoolHandle == &_IotSystemTaskPool ) );

    /* Avoid compiler warnings about unused parameters if configASSERT() is not
    defined. */
    ( void ) taskPoolHandle;

    configASSERT( pJob != NULL );
    configASSERT( ( flags == 0UL ) || ( flags == IOT_TASKPOOL_JOB_HIGH_PRIORITY ) );

    /* Acquire the mutex for manipulating the job timer queue. */
    if ( xSemaphoreTake( _IotSystemTaskPool.xTimerEventMutex, MAX_SEMAPHORE_TAKE_WAIT_TIME_MS ) == pdTRUE )
    {
        _scheduleInternal( pJob );
        if ( xSemaphoreGive( _IotSystemTaskPool.xTimerEventMutex ) == pdFALSE )
        {
            /* This can only be reached if semaphores are configured incorrectly. */
            status =  IOT_TASKPOOL_GENERAL_FAILURE;
        }
        /* Signal a worker task that a job was queued. */
        if ( xSemaphoreGive( _IotSystemTaskPool.dispatchSignal ) == pdFALSE )
        {
            /* This can only be reached if semaphores are configured incorrectly. */
            status = IOT_TASKPOOL_GENERAL_FAILURE;
        }
    }
    else
    {
        status =  IOT_TASKPOOL_GENERAL_FAILURE;
    }

    return status;
}

/*-----------------------------------------------------------*/

IotTaskPoolError_t IotTaskPool_ScheduleDeferred( IotTaskPool_t taskPoolHandle,
                                                 IotTaskPoolJob_t job,
                                                 uint32_t timeMs )
{
    TickType_t now;
    IotTaskPoolError_t status = IOT_TASKPOOL_SUCCESS;

    /* This lean version of the task pool only supports the task pool created
    by this library (the system task pool).  NULL means use the system task
    pool - no other values are allowed.  Use the full implementation of this
    library if you want multiple task pools (there is more than one task in
    each pool. */
    configASSERT( ( taskPoolHandle == NULL ) || ( taskPoolHandle == &_IotSystemTaskPool ) );

    configASSERT( job != NULL );

    /* If the timer period is zero, just immediately queue the job for execution. */
    if( timeMs == 0UL )
    {
        status = IotTaskPool_Schedule( &_IotSystemTaskPool, job, 0 );
    }
    else
    {
        _taskPoolTimerEvent_t* pTimerEvent = &(job->timer);

        configASSERT( job->timer.link.pNext == NULL );

        IotLink_t* pTimerEventLink;

        pTimerEvent->link.pNext = NULL;
        pTimerEvent->link.pPrevious = NULL;

        now = xTaskGetTickCount();
        pTimerEvent->expirationTime = now + pdMS_TO_TICKS( timeMs );

        if ( xSemaphoreTake( _IotSystemTaskPool.xTimerEventMutex, MAX_SEMAPHORE_TAKE_WAIT_TIME_MS ) == pdTRUE )
        {

            /* Append the timer event to the timer list. */
            IotListDouble_InsertSorted( &( _IotSystemTaskPool.timerEventsList ), &( pTimerEvent->link ), _timerEventCompare );

            /* Update the job status to 'scheduled'. */
            job->status = IOT_TASKPOOL_STATUS_DEFERRED;

            /* Peek the first event in the timer event list. There must be at least one,
             * since we just inserted it. */
            pTimerEventLink = IotListDouble_PeekHead( &( _IotSystemTaskPool.timerEventsList ) );
            configASSERT( pTimerEventLink != NULL );

            /* If the event we inserted is at the front of the queue, then
                * we need to reschedule the underlying timer. */
            if ( pTimerEventLink == &( pTimerEvent->link ) )
            {
                pTimerEvent = IotLink_Container( _taskPoolTimerEvent_t, pTimerEventLink, link );

                _rescheduleDeferredJobsTimer( _IotSystemTaskPool.timer, pTimerEvent );
            }

            if ( xSemaphoreGive( _IotSystemTaskPool.xTimerEventMutex ) == pdFALSE )
            {
                /* This can only be reached if semaphores are configured incorrectly. */
                status = IOT_TASKPOOL_GENERAL_FAILURE;
            }

        }
        else
        {
            status = IOT_TASKPOOL_GENERAL_FAILURE;
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

IotTaskPoolError_t IotTaskPool_GetStatus( IotTaskPool_t taskPoolHandle,
                                          IotTaskPoolJob_t job,
                                          IotTaskPoolJobStatus_t * const pStatus )
{

    /* This lean version of the task pool only supports the task pool created by
    this library (the system task pool).  NULL means use the system task pool -
    no other values are allowed.  Use the full implementation of this library if you
    want multiple task pools (there is more than one task in each pool. */
    configASSERT( ( taskPoolHandle == NULL ) || ( taskPoolHandle == &_IotSystemTaskPool ) );

    /* Remove warning about unused parameter. */
    ( void ) taskPoolHandle;

    /* Parameter checking. */
    configASSERT( job != NULL );
    configASSERT( pStatus != NULL );

    taskENTER_CRITICAL();
    {
        *pStatus = job->status;
    }
    taskEXIT_CRITICAL();

    return IOT_TASKPOOL_SUCCESS;
}

/*-----------------------------------------------------------*/

IotTaskPoolError_t IotTaskPool_TryCancel( IotTaskPool_t taskPoolHandle,
                                          IotTaskPoolJob_t job,
                                          IotTaskPoolJobStatus_t * const pStatus )
{
    IotTaskPoolError_t status = IOT_TASKPOOL_SUCCESS;
    const TickType_t dontBlock = ( TickType_t ) 0;

    /* This lean version of the task pool only supports the task pool created
    by this library (the system task pool).  NULL means use the system task
    pool - no other values are allowed.  Use the full implementation of this
    library if you want multiple task pools (there is more than one task in
    each pool. */
    configASSERT( ( taskPoolHandle == NULL ) || ( taskPoolHandle == &_IotSystemTaskPool ) );

    if( job != NULL )
    {
        if( pStatus != NULL )
        {
            *pStatus = IOT_TASKPOOL_STATUS_UNDEFINED;
        }

        if ( xSemaphoreTake( _IotSystemTaskPool.xTimerEventMutex, dontBlock ) != pdFALSE )
        {
            status = _tryCancelInternal( job, pStatus );
            if ( xSemaphoreGive( _IotSystemTaskPool.xTimerEventMutex ) == pdFALSE )
            {
                /* This can only be reached if semaphores are configured incorrectly. */
                status = IOT_TASKPOOL_GENERAL_FAILURE;
            }
        }
        else
        {
            /* If we fail to take the semaphore, just abort the cancel. */
            status = IOT_TASKPOOL_CANCEL_FAILED;
        }
    }
    else
    {
        status = IOT_TASKPOOL_BAD_PARAMETER;
    }

    return status;
}

/*-----------------------------------------------------------*/

IotTaskPoolJobStorage_t * IotTaskPool_GetJobStorageFromHandle( IotTaskPoolJob_t pJob )
{
    return ( IotTaskPoolJobStorage_t * ) pJob;
}

/*-----------------------------------------------------------*/

const char * IotTaskPool_strerror( IotTaskPoolError_t status )
{
    const char * pMessage = NULL;

    switch( status )
    {
        case IOT_TASKPOOL_SUCCESS:
            pMessage = "SUCCESS";
            break;

        case IOT_TASKPOOL_BAD_PARAMETER:
            pMessage = "BAD PARAMETER";
            break;

        case IOT_TASKPOOL_ILLEGAL_OPERATION:
            pMessage = "ILLEGAL OPERATION";
            break;

        case IOT_TASKPOOL_NO_MEMORY:
            pMessage = "NO MEMORY";
            break;

        case IOT_TASKPOOL_SHUTDOWN_IN_PROGRESS:
            pMessage = "SHUTDOWN IN PROGRESS";
            break;

        case IOT_TASKPOOL_CANCEL_FAILED:
            pMessage = "CANCEL FAILED";
            break;

        case IOT_TASKPOOL_GENERAL_FAILURE:
            pMessage = "GENERAL FAILURE";
            break;

        default:
            pMessage = "INVALID STATUS";
            break;
    }

    return pMessage;
}

/* ---------------------------------------------------------------------------------------------- */
/* ---------------------------------------------------------------------------------------------- */
/* ---------------------------------------------------------------------------------------------- */

static void _initTaskPoolControlStructures( void )
{
    /* Initialize a job data structures that require no de-initialization.
     * All other data structures carry a value of 'NULL' before initialization.
     */
    IotDeQueue_Create( &( _IotSystemTaskPool.dispatchQueue ) );
    IotListDouble_Create( &( _IotSystemTaskPool.timerEventsList ) );

    /* Initialize the semaphore for waiting for incoming work.  Cannot fail as
    statically allocated. */
    _IotSystemTaskPool.dispatchSignal = xSemaphoreCreateCountingStatic( TASKPOOL_MAX_SEM_VALUE, 0, &( _IotSystemTaskPool.dispatchSignalBuffer ) );
    _IotSystemTaskPool.xTimerEventMutex = xSemaphoreCreateMutexStatic( &( _IotSystemTaskPool.xTimerEventMutexBuffer ) );
}

static IotTaskPoolError_t _createTaskPool( const IotTaskPoolInfo_t * const pInfo )
{
    /* The taskpool will create a number of threads equal to the minThreads
    setting. The number of workers should be equal to avoid over/under
    allocation.    */
    configASSERT( IOT_TASKPOOL_NUMBER_OF_WORKERS == pInfo->minThreads );

    /* Static TCB structures and arrays to be used by statically allocated worker
    tasks. */
    static StaticTask_t workerTaskTCBs[ IOT_TASKPOOL_NUMBER_OF_WORKERS ];
    static StackType_t workerTaskStacks[ IOT_TASKPOOL_NUMBER_OF_WORKERS ][ IOT_TASKPOOL_WORKER_STACK_SIZE_BYTES / sizeof( portSTACK_TYPE ) ];

    /* Static structure to hold the software timer. */
    static StaticTimer_t staticTimer;

    uint32_t threadsCreated = 0; /* Although initialized before use removing the initializer here results in compiler warnings. */
    char taskName[ 10 ];


    /* This assert is primarily to catch the function being called more than once,
    but will also ensure the C start up code has zeroed out the structure
    correctly. */
    #if( configASSERT_DEFINED == 1 )
    {
    size_t x;
    uint8_t *pucNextByte = ( uint8_t * ) &_IotSystemTaskPool;

        for( x = 0; x < sizeof( _taskPool_t ); x++ )
        {
            configASSERT( pucNextByte[ x ] == ( uint8_t ) 0x00 );
        }
    }
    #endif /* configASSERT_DEFINED */



    /* Initialize all internal data structure prior to creating all threads. */
    _initTaskPoolControlStructures();

    /* Create the FreeRTOS timer for managing Task Pool timers. */
    _IotSystemTaskPool.timer = xTimerCreateStatic( NULL, /* Text name for the timer, only used for debugging. */
                                                  portMAX_DELAY, /* Timer period in ticks. */
                                                  pdFALSE, /* pdFALSE means its a one-shot timer. */
                                                  ( void * ) &_IotSystemTaskPool, /* Parameter passed into callback. */
                                                  _timerCallback, /* Callback that executes when the timer expires. */
                                                  &staticTimer ); /* Static storage for the timer's data structure. */

    /* The task pool will initialize the minimum number of threads requested by the user upon start.
    Note this tailored version of the task pool does not auto-scale, but fixes the number of tasks
    in the pool to the originally specified minimum, and the specified maximum value is ignored. */
    /* Create the minimum number of threads specified by the user, and if one fails shutdown and return error. */
    for( threadsCreated = 0; threadsCreated < pInfo->minThreads; )
    {
        /* Generate a unique name for the task. */
        snprintf( taskName, sizeof( taskName ), "pool%d", ( int ) threadsCreated );

        xTaskCreateStatic( _taskPoolWorker, /* Function that implements the task. */
                           taskName,       /* Text name for the task, used for debugging only. */
                           IOT_TASKPOOL_WORKER_STACK_SIZE_BYTES / sizeof( portSTACK_TYPE ), /* xTaskCreate() expects the stack size to be specified in words. */
                           &_IotSystemTaskPool,       /* Parameter passed into the task. */
                           pInfo->priority, /* Priority at which the task starts running. */
                           &( workerTaskStacks[ threadsCreated ][ 0 ] ), /* Pointer to static storage for the task's stack. */
                           &( workerTaskTCBs[ threadsCreated ] ) ); /* Pointer to static storage for the task's TCB. */

        ++threadsCreated;
    }
    _IotSystemTaskPool.running = true;

    /* This version of this function cannot fail as all the memory is allocated
    statically at compile time. */
    return IOT_TASKPOOL_SUCCESS;
}

/* ---------------------------------------------------------------------------------------------- */

static void _taskPoolWorker( void * pUserContext )
{
    configASSERT( pUserContext != NULL );

    IotTaskPoolRoutine_t userCallback = NULL;

    /* Extract pTaskPool pointer from context. */
    _taskPool_t * pTaskPool = ( _taskPool_t * ) pUserContext;

    /* OUTER LOOP: it controls the lifetime of the worker thread. */
    for( ; ; )
    {
    IotLink_t * pFirst = NULL;
    _taskPoolJob_t * pJob = NULL;

        /* Wait on incoming notifications... */
        configASSERT( pTaskPool->dispatchSignal );

        /* If the semaphore for job dispatch expires without a job, a critical
           precondition of this task has not been met. See the xBlockTime
           parameter of xSemaphoreTake for details. */
        configASSERT( xSemaphoreTake( pTaskPool->dispatchSignal, portMAX_DELAY ) );

        /* Acquire the lock to check for incoming notifications. This call
           should not expire. See the xBlockTime parameter of xSemaphoreTake
           for details. */
        configASSERT( xSemaphoreTake( pTaskPool->xTimerEventMutex, portMAX_DELAY ) );

        /* Dequeue the first job in FIFO order. */
        pFirst = IotDeQueue_DequeueHead( &pTaskPool->dispatchQueue );

        /* If there is indeed a job, then update status under lock, and release the lock before processing the job. */
        if( pFirst != NULL )
        {
            /* Extract the job from its link. */
            pJob = IotLink_Container( _taskPoolJob_t, pFirst, link );

            /* Update status to 'completed' to indicate it is queued for execution. */
            pJob->status = IOT_TASKPOOL_STATUS_COMPLETED;
            userCallback = pJob->userCallback;
        }

        /* Release the lock now that the job dispatch queue has been checked.
           This call should not expire. See the xBlockTime parameter of
           xSemaphoreTake for details. */
        configASSERT( xSemaphoreGive( pTaskPool->xTimerEventMutex ) );

        /* INNER LOOP: it controls the execution of jobs: the exit condition is the lack of a job to execute. */
        while( pJob != NULL )
        {
            /* Process the job by invoking the associated callback with the user context.
             * This task pool thread will not be available until the user callback returns.
             */
            {
                configASSERT( IotLink_IsLinked( &pJob->link ) == false );
                configASSERT( userCallback != NULL );

                userCallback( pTaskPool, pJob, pJob->pUserContext );

                /* This job is finished, clear its pointer. */
                pJob = NULL;
                userCallback = NULL;
            }

            /* Acquire the lock to check for incoming notifications. This call
            should not expire. See the xBlockTime parameter of xSemaphoreTake
            for details. */
            configASSERT( xSemaphoreTake( pTaskPool->xTimerEventMutex, portMAX_DELAY ) );
            {
                /* Try and dequeue the next job in the dispatch queue. */
                IotLink_t * pItem = NULL;

                /* Dequeue the next job from the dispatch queue. */
                pItem = IotDeQueue_DequeueHead( &( pTaskPool->dispatchQueue ) );

                /* If there is no job left in the dispatch queue, update the worker status and leave. */
                if( pItem == NULL )
                {
                    /* Release the lock before exiting the loop. */
                    configASSERT( xSemaphoreGive( pTaskPool->xTimerEventMutex ) );

                    /* Abandon the INNER LOOP. Execution will transfer back to the OUTER LOOP condition. */
                    break;
                }
                else
                {
                    pJob = IotLink_Container( _taskPoolJob_t, pItem, link );

                    userCallback = pJob->userCallback;
                }

                pJob->status = IOT_TASKPOOL_STATUS_COMPLETED;
            }
            /* Release the lock now that the job dispatch queue has been checked. */
            configASSERT( xSemaphoreGive( pTaskPool->xTimerEventMutex ) );
        }
    }
}

/* ---------------------------------------------------------------------------------------------- */

static void _initializeJob( _taskPoolJob_t * const pJob,
                            IotTaskPoolRoutine_t userCallback,
                            void * pUserContext )
{
    memset( ( void * ) pJob, 0x00, sizeof( _taskPoolJob_t ) );

    pJob->userCallback = userCallback;
    pJob->pUserContext = pUserContext;
    pJob->status = IOT_TASKPOOL_STATUS_READY;
}

/* ---------------------------------------------------------------------------------------------- */

static void _scheduleInternal( _taskPoolJob_t * const pJob )
{
    /* Update the job status to 'scheduled'. */
    pJob->status = IOT_TASKPOOL_STATUS_SCHEDULED;

    /* Append the job to the dispatch queue. */
    IotDeQueue_EnqueueTail( &( _IotSystemTaskPool.dispatchQueue ), &( pJob->link ) );

    /* NOTE:  Every call to this function must be followed by giving the
    dispatchSignal semaphore - but do not give the semaphore directly in
    this function as giving the semaphore will result in the execution of
    a task pool worker task (depending on relative priorities) and we don't
    want the worker task to execute until all semaphores obtained before calling
    this function have been released. */
}

/*-----------------------------------------------------------*/

static bool _matchJobByPointer( const IotLink_t * const pLink,
                                void * pMatch )
{
    const _taskPoolJob_t * const pJob = ( _taskPoolJob_t * ) pMatch;

    const _taskPoolTimerEvent_t * const pTimerEvent = IotLink_Container( _taskPoolTimerEvent_t, pLink, link );

    if( pJob == GET_JOB_FROM_TIMER( pTimerEvent ) )
    {
        return true;
    }

    return false;
}

/*-----------------------------------------------------------*/

static IotTaskPoolError_t _tryCancelInternal( _taskPoolJob_t * const pJob,
                                              IotTaskPoolJobStatus_t * const pStatus )
{
    IotTaskPoolError_t result = IOT_TASKPOOL_SUCCESS;

    bool cancelable = false;

    /* We can only cancel jobs that are either 'ready' (waiting to be scheduled). 'deferred', or 'scheduled'. */

    IotTaskPoolJobStatus_t currentStatus = pJob->status;

    switch( currentStatus )
    {
        case IOT_TASKPOOL_STATUS_READY:
        case IOT_TASKPOOL_STATUS_DEFERRED:
        case IOT_TASKPOOL_STATUS_SCHEDULED:
        case IOT_TASKPOOL_STATUS_CANCELED:
            cancelable = true;
            break;

        case IOT_TASKPOOL_STATUS_COMPLETED:
            /* Log message for debug purposes. */
            IotLogWarn( "Attempt to cancel a job that is already executing, or canceled." );
            break;

        default:
            /* Log message for debug purposes. */
            IotLogError( "Attempt to cancel a job with an undefined state." );
            break;
    }

    /* Update the returned status to the current status of the job. */
    if( pStatus != NULL )
    {
        *pStatus = currentStatus;
    }

    if( cancelable == false )
    {
        result = IOT_TASKPOOL_CANCEL_FAILED;
    }
    else
    {
        /* Update the status of the job. */
        pJob->status = IOT_TASKPOOL_STATUS_CANCELED;

        /* If the job is cancelable and its current status is 'scheduled' then unlink it from the dispatch
         * queue and signal any waiting threads. */
        if( currentStatus == IOT_TASKPOOL_STATUS_SCHEDULED )
        {
            /* A scheduled work items must be in the dispatch queue. */
            configASSERT( IotLink_IsLinked( &pJob->link ) );

            IotDeQueue_Remove( &pJob->link );
        }

        /* If the job current status is 'deferred' then the job has to be pending
         * in the timeouts queue. */
        else if( currentStatus == IOT_TASKPOOL_STATUS_DEFERRED )
        {
            /* Find the timer event associated with the current job. There MUST be one, hence assert if not. */
            IotLink_t * pTimerEventLink = IotListDouble_FindFirstMatch( &( _IotSystemTaskPool.timerEventsList ), NULL, _matchJobByPointer, pJob );
            configASSERT( pTimerEventLink != NULL );

            if( pTimerEventLink != NULL )
            {
                bool shouldReschedule = false;

                /* If the job being canceled was at the head of the timeouts queue, then we need to reschedule the timer
                 * with the next job timeout */
                IotLink_t * pHeadLink = IotListDouble_PeekHead( &( _IotSystemTaskPool.timerEventsList ) );

                if( pHeadLink == pTimerEventLink )
                {
                    shouldReschedule = true;
                }

                /* Remove the timer event associated with the canceled job and free the associated memory. */
                IotListDouble_Remove( pTimerEventLink );
                memset( IotLink_Container( _taskPoolTimerEvent_t, pTimerEventLink, link ), 0, sizeof( IotLink_t ) );

                if( shouldReschedule )
                {
                    IotLink_t * pNextTimerEventLink = IotListDouble_PeekHead( &( _IotSystemTaskPool.timerEventsList ) );

                    if( pNextTimerEventLink != NULL )
                    {
                        _rescheduleDeferredJobsTimer( _IotSystemTaskPool.timer, IotLink_Container( _taskPoolTimerEvent_t, pNextTimerEventLink, link ) );
                    }
                }
            }
        }
        else
        {
            /* A cancelable job status should be either 'scheduled' or 'deferred'. */
            configASSERT( ( currentStatus == IOT_TASKPOOL_STATUS_READY ) || ( currentStatus == IOT_TASKPOOL_STATUS_CANCELED ) );
        }
    }

    return result;
}

/*-----------------------------------------------------------*/

static int32_t _timerEventCompare( const IotLink_t * const pTimerEventLink1,
                                   const IotLink_t * const pTimerEventLink2 )
{
    const _taskPoolTimerEvent_t * const pTimerEvent1 = IotLink_Container( _taskPoolTimerEvent_t,
                                                                          pTimerEventLink1,
                                                                          link );
    const _taskPoolTimerEvent_t * const pTimerEvent2 = IotLink_Container( _taskPoolTimerEvent_t,
                                                                          pTimerEventLink2,
                                                                          link );

    if( pTimerEvent1->expirationTime < pTimerEvent2->expirationTime )
    {
        return -1;
    }

    if( pTimerEvent1->expirationTime > pTimerEvent2->expirationTime )
    {
        return 1;
    }

    return 0;
}

/*-----------------------------------------------------------*/

static void _rescheduleDeferredJobsTimer( TimerHandle_t const timer,
                                          _taskPoolTimerEvent_t * const pFirstTimerEvent )
{
    uint64_t delta = 0;
    TickType_t now = xTaskGetTickCount();

    configASSERT( pFirstTimerEvent != NULL );
    configASSERT( timer != NULL );

     /* Determine how much time is left for the deferred job. */
    if( pFirstTimerEvent->expirationTime > now )
    {
        delta = pFirstTimerEvent->expirationTime - now;
    }

    /* If the job timer has exceeded it's period, schedule it to be executed shortly. */
    if( delta < TASKPOOL_JOB_RESCHEDULE_DELAY_MS )
    {
        delta = TASKPOOL_JOB_RESCHEDULE_DELAY_MS; /* The job will be late... */
    }

    /* Change the period of the task pools timer to be the period of this
       timer. A precondition of this function is that this TimerEvent is the
       timer event with the shortest deadline.
    */
    if( xTimerChangePeriod( timer, ( uint32_t ) delta, portMAX_DELAY ) == pdFAIL )
    {
        IotLogWarn( "Failed to re-arm timer for task pool" );
    }
}

/*-----------------------------------------------------------*/

static void _timerCallback( TimerHandle_t xTimer )
{
    _taskPool_t * pTaskPool = pvTimerGetTimerID( xTimer );

    configASSERT( pTaskPool );

    _taskPoolTimerEvent_t * pTimerEvent = NULL;
    BaseType_t numberOfSchedules = 0;

    IotLogDebug( "Timer thread started for task pool %p.", pTaskPool );

    /* Attempt to lock the timer mutex. Return immediately if the mutex cannot be locked.
     * If this mutex cannot be locked it means that another thread is manipulating the
     * timeouts list, and will reset the timer to fire again, although it will be late.
     */
    if ( xSemaphoreTake( pTaskPool->xTimerEventMutex, 0 ) == pdPASS )
    {

        /* Dispatch all deferred job whose timer expired, then reset the timer for the next
         * job down the line. */
        for( ; ; )
        {
            /* Peek the first event in the timer event list. */
            IotLink_t * pLink = IotListDouble_PeekHead( &pTaskPool->timerEventsList );

            /* Check if the timer misfired for any reason.  */
            if( pLink != NULL )
            {
                /* Record the current time. */
                TickType_t now = xTaskGetTickCount();

                /* Extract the job from its envelope. */
                pTimerEvent = IotLink_Container( _taskPoolTimerEvent_t, pLink, link );

                /* Check if the first event should be processed now. */
                if( pTimerEvent->expirationTime <= now )
                {
                    /*  Remove the timer event for immediate processing. */
                    IotListDouble_Remove( &( pTimerEvent->link ) );
                }
                else
                {
                    /* The first element in the timer queue shouldn't be processed yet.
                     * Arm the timer for when it should be processed and leave altogether. */
                    _rescheduleDeferredJobsTimer( pTaskPool->timer, pTimerEvent );
                    break;
                }
            }
            /* If there are no timer events to process, terminate this thread. */
            else
            {
                IotLogDebug( "Finished scheduling deferred jobs." );
                break;
            }

            /* Queue the job associated with the received timer event. */
            _scheduleInternal( GET_JOB_FROM_TIMER( pTimerEvent ) );
            numberOfSchedules++;
            IotLogDebug( "Scheduled a job." );

            /* Free the timer event. */
            memset( &( pTimerEvent->link ), 0, sizeof( pTimerEvent->link ) );
        }

        /* Release mutex guarding the timer list. */
        configASSERT( xSemaphoreGive( pTaskPool->xTimerEventMutex ) == pdPASS );

        for (; numberOfSchedules > 0; numberOfSchedules--)
        {
            /* Signal a worker task that a job was queued. */
            configASSERT( xSemaphoreGive( pTaskPool->dispatchSignal ) );
        }
    }

}
