/*
 * Amazon FreeRTOS Common V1.0.0
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
 * http://aws.amazon.com/freertos
 * http://www.FreeRTOS.org
 */
/**
 * @file iot_taskpool.c
 * @brief Implements the task pool functions in iot_taskpool.h
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
#include "private/iot_taskpool_internal.h"

/**
 * @brief Maximum semaphore value for wait operations.
 */
#define TASKPOOL_MAX_SEM_VALUE              0xFFFF

/**
 * @brief Reschedule delay in milliseconds for deferred jobs.
 */
#define TASKPOOL_JOB_RESCHEDULE_DELAY_MS    ( 10ULL )

/* ---------------------------------------------------------------------------------- */

/**
 * Doxygen should ignore this section.
 *
 * @brief The system task pool handle for all libraries to use.
 * User application can use the system task pool as well knowing that the usage will be shared with
 * the system libraries as well. The system task pool needs to be initialized before any library is used or
 * before any code that posts jobs to the task pool runs.
 */
static _taskPool_t _IotSystemTaskPool = { .dispatchQueue = IOT_DEQUEUE_INITIALIZER };

/* -------------- Convenience functions to create/recycle/destroy jobs -------------- */

/**
 * @brief Initializes one instance of a Task pool cache.
 *
 * @param[in] pCache The pre-allocated instance of the cache to initialize.
 */
static void _initJobsCache( _taskPoolCache_t * const pCache );

/**
 * @brief Initialize a job.
 *
 * @param[in] pJob The job to initialize.
 * @param[in] userCallback The user callback for the job.
 * @param[in] pUserContext The context tp be passed to the callback.
 * @param[in] isStatic A flag to indicate whether the job is statically or synamically allocated.
 */
static void _initializeJob( _taskPoolJob_t * const pJob,
                            IotTaskPoolRoutine_t userCallback,
                            void * pUserContext,
                            bool isStatic );

/**
 * @brief Extracts and initializes one instance of a job from the cache or, if there is none available, it allocates and initialized a new one.
 *
 * @param[in] pCache The instance of the cache to extract the job from.
 */
static _taskPoolJob_t * _fetchOrAllocateJob( _taskPoolCache_t * const pCache );

/**
 * Recycles one instance of a job into the cache or, if the cache is full, it destroys it.
 *
 * @param[in] pCache The instance of the cache to recycle the job into.
 * @param[in] pJob The job to recycle.
 *
 */
static void _recycleJob( _taskPoolCache_t * const pCache,
                         _taskPoolJob_t * const pJob );

/**
 * Destroys one instance of a job.
 *
 * @param[in] pJob The job to destroy.
 *
 */
static void _destroyJob( _taskPoolJob_t * const pJob );

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
 * param[in] pFirstTimerEvent The timer event that carries the timeout and job inforamtion.
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
 * Parameter validation for a task pool initialization.
 *
 * @param[in] pInfo The initialization information for the task pool.
 *
 */
static IotTaskPoolError_t _performTaskPoolParameterValidation( const IotTaskPoolInfo_t * const pInfo );

/**
 * Initializes a pre-allocated instance of a task pool.
 *
 * @param[in] pTaskPool The pre-allocated instance of the task pool to initialize.
 *
 */
static void _initTaskPoolControlStructures( _taskPool_t * const pTaskPool );

/**
 * Initializes a pre-allocated instance of a task pool.
 *
 * @param[in] pInfo The initialization information for the task pool.
 * @param[out] pTaskPool A pointer to the task pool data structure to initialize.
 *
 */
static IotTaskPoolError_t _createTaskPool( const IotTaskPoolInfo_t * const pInfo,
                                           _taskPool_t * const pTaskPool );

/**
 * Destroys one instance of a task pool.
 *
 * @param[in] pTaskPool The task pool to destroy.
 *
 */
static void _destroyTaskPool( _taskPool_t * const pTaskPool );

/**
 * Places a job in the dispatch queue.
 *
 * @param[in] pTaskPool The task pool to scheduel the job with.
 * @param[in] pJob The job to schedule.
 * @param[in] flags The job flags.
 *
 */
static IotTaskPoolError_t _scheduleInternal( _taskPool_t * const pTaskPool,
                                             _taskPoolJob_t * const pJob );
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
 * @param[in] pTaskPool The task pool to cancel an operation against.
 * @param[in] pJob The job to cancel.
 * @param[out] pStatus The status of the job at the time of cancellation.
 *
 */
static IotTaskPoolError_t _tryCancelInternal( _taskPool_t * const pTaskPool,
                                              _taskPoolJob_t * const pJob,
                                              IotTaskPoolJobStatus_t * const pStatus );

/* ---------------------------------------------------------------------------------------------- */

/*
 * The full IoT Task Pool Library has many use cases, including Linux
 * development.  Typical FreeRTOS use cases do not require the full
 * functionality so optimised version is provided specifically for use with
 * FreeRTOS.  Unlike the full version, this optimised version:
 *   + Only supports a single task pool (system task pool) at a time.
 *   + Does not auto-scale by dynamically adding more tasks if the number of
 *   + tasks in the pool becomes exhausted.  The number of tasks in the pool
 *     are fixed at compile time.  See the task pool configuration options for
 *     more information.
 *   + Cannot be shut down - it exists for the lifetime of the application.
 *
 * As such this file does not implement the following API functions:
 *   + IotTaskPool_GetSystemTaskPool()
 *   + IotTaskPool_Create()
 *   + IotTaskPool_Destroy()
 *   + IotTaskPool_SetMaxThreads()
 *
 * Users who are interested in the functionality of the full IoT Task Pool
 * library can us it in place of this optimised version.
 */

IotTaskPoolError_t IotTaskPool_CreateSystemTaskPool( const IotTaskPoolInfo_t * const pInfo )
{
    TASKPOOL_FUNCTION_ENTRY( IOT_TASKPOOL_SUCCESS );

    /* At this time the task pool cannot be created before the scheduler has
    started because the function attempts to block on synchronization
    primitives (although I'm not sure why). */
    configASSERT( xTaskGetSchedulerState() != taskSCHEDULER_NOT_STARTED );

    /* Guard against multiple attempts to create the system task pool in case
    this function is called by more than one library initialization routine. */
    if( _IotSystemTaskPool.running == false )
    {
        /* Parameter checking. */
        TASKPOOL_ON_ERROR_GOTO_CLEANUP( _performTaskPoolParameterValidation( pInfo ) );

        /* Create the system task pool pool. */
        TASKPOOL_SET_AND_GOTO_CLEANUP( _createTaskPool( pInfo, &_IotSystemTaskPool ) );
    }

    TASKPOOL_NO_FUNCTION_CLEANUP();
}
/*-----------------------------------------------------------*/

IotTaskPoolError_t IotTaskPool_CreateJob( IotTaskPoolRoutine_t userCallback,
                                          void * pUserContext,
                                          IotTaskPoolJobStorage_t * const pJobStorage,
                                          IotTaskPoolJob_t * const ppJob )
{
    TASKPOOL_FUNCTION_ENTRY( IOT_TASKPOOL_SUCCESS );

    /* Parameter checking. */
    TASKPOOL_ON_NULL_ARG_GOTO_CLEANUP( userCallback );
    TASKPOOL_ON_NULL_ARG_GOTO_CLEANUP( pJobStorage );
    TASKPOOL_ON_NULL_ARG_GOTO_CLEANUP( ppJob );

    /* Build a job around the user-provided storage. */
    _initializeJob( ( _taskPoolJob_t * ) pJobStorage, userCallback, pUserContext, true );

    *ppJob = ( IotTaskPoolJob_t ) pJobStorage;

    TASKPOOL_NO_FUNCTION_CLEANUP();
}

/*-----------------------------------------------------------*/

IotTaskPoolError_t IotTaskPool_CreateRecyclableJob( IotTaskPool_t taskPoolHandle,
                                                    IotTaskPoolRoutine_t userCallback,
                                                    void * pUserContext,
                                                    IotTaskPoolJob_t * const ppJob )
{
    TASKPOOL_FUNCTION_ENTRY( IOT_TASKPOOL_SUCCESS );

    _taskPool_t * const pTaskPool = &_IotSystemTaskPool;
    _taskPoolJob_t * pTempJob = NULL;

    /* This lean version of the task pool only supports the task pool created
    by this library (the system task pool).  NULL means use the system task
    pool - no other values are allowed.  Use the full implementation of this
    library if you want multiple task pools (there is more than one task in
    each pool. */
    configASSERT( ( taskPoolHandle == NULL ) || ( taskPoolHandle == &_IotSystemTaskPool ) );

    /* Avoid compiler warnings about unused parameters if configASSERT() is not
    defined. */
    ( void ) taskPoolHandle;

    /* Parameter checking. */
    TASKPOOL_ON_NULL_ARG_GOTO_CLEANUP( userCallback );
    TASKPOOL_ON_NULL_ARG_GOTO_CLEANUP( ppJob );

    taskENTER_CRITICAL();
    {
        /* Bail out early if this task pool is shutting down. */
        pTempJob = _fetchOrAllocateJob( &pTaskPool->jobsCache );
    }
    taskEXIT_CRITICAL();

    if( pTempJob == NULL )
    {
        IotLogInfo( "Failed to allocate a job." );

        TASKPOOL_SET_AND_GOTO_CLEANUP( IOT_TASKPOOL_NO_MEMORY );
    }

    _initializeJob( pTempJob, userCallback, pUserContext, false );

    *ppJob = pTempJob;

    TASKPOOL_NO_FUNCTION_CLEANUP();
}

/*-----------------------------------------------------------*/

IotTaskPoolError_t IotTaskPool_DestroyRecyclableJob( IotTaskPool_t taskPoolHandle,
                                                     IotTaskPoolJob_t pJobHandle )
{
    TASKPOOL_FUNCTION_ENTRY( IOT_TASKPOOL_SUCCESS );

    _taskPoolJob_t * pJob = ( _taskPoolJob_t * ) pJobHandle;

    /* This lean version of the task pool only supports the task pool created
    by this library (the system task pool).  NULL means use the system task
    pool - no other values are allowed.  Use the full implementation of this
    library if you want multiple task pools (there is more than one task in
    each pool. */
    configASSERT( ( taskPoolHandle == NULL ) || ( taskPoolHandle == &_IotSystemTaskPool ) );

    /* Avoid compiler warnings about unused parameters if configASSERT() is not
    defined. */
    ( void ) taskPoolHandle;

    /* Parameter checking. */
    TASKPOOL_ON_NULL_ARG_GOTO_CLEANUP( pJobHandle );

    IotTaskPool_Assert( IotLink_IsLinked( &pJob->link ) == false );

    _destroyJob( pJob );

    TASKPOOL_NO_FUNCTION_CLEANUP();
}

/*-----------------------------------------------------------*/

IotTaskPoolError_t IotTaskPool_RecycleJob( IotTaskPool_t taskPoolHandle,
                                           IotTaskPoolJob_t pJob )
{
    TASKPOOL_FUNCTION_ENTRY( IOT_TASKPOOL_SUCCESS );

    _taskPool_t * pTaskPool = ( _taskPool_t * ) &_IotSystemTaskPool;

    /* This lean version of the task pool only supports the task pool created
    by this library (the system task pool).  NULL means use the system task
    pool - no other values are allowed.  Use the full implementation of this
    library if you want multiple task pools (there is more than one task in
    each pool. */
    configASSERT( ( taskPoolHandle == NULL ) || ( taskPoolHandle == &_IotSystemTaskPool ) );

    /* Ensure unused parameters do not cause compiler warnings in case
    configASSERT() is not defined. */
    ( void ) taskPoolHandle;

    TASKPOOL_ON_NULL_ARG_GOTO_CLEANUP( pJob );

    taskENTER_CRITICAL();
    {
        IotTaskPool_Assert( IotLink_IsLinked( &pJob->link ) == false );

        _recycleJob( &pTaskPool->jobsCache, pJob );
    }
    taskEXIT_CRITICAL();

    TASKPOOL_NO_FUNCTION_CLEANUP();
}

/*-----------------------------------------------------------*/

IotTaskPoolError_t IotTaskPool_Schedule( IotTaskPool_t taskPoolHandle,
                                         IotTaskPoolJob_t pJob,
                                         uint32_t flags )
{
    TASKPOOL_FUNCTION_ENTRY( IOT_TASKPOOL_SUCCESS );

    _taskPool_t * const pTaskPool = &_IotSystemTaskPool;

    /* Task pool must have been created. */
    configASSERT( pTaskPool->running != false );

    /* This lean version of the task pool only supports the task pool created
    by this library (the system task pool).  NULL means use the system task
    pool - no other values are allowed.  Use the full implementation of this
    library if you want multiple task pools (there is more than one task in
    each pool. */
    configASSERT( ( taskPoolHandle == NULL ) || ( taskPoolHandle == &_IotSystemTaskPool ) );

    /* Avoid compiler warnings about unused parameters if configASSERT() is not
    defined. */
    ( void ) taskPoolHandle;

    /* Parameter checking. */
    TASKPOOL_ON_NULL_ARG_GOTO_CLEANUP( pJob );
    TASKPOOL_ON_ARG_ERROR_GOTO_CLEANUP( ( flags != 0UL ) && ( flags != IOT_TASKPOOL_JOB_HIGH_PRIORITY ) );

    taskENTER_CRITICAL(); //_RB_ Critical section is too long - does the whole thing need to be protected?
    {
        _scheduleInternal( pTaskPool, pJob );
    }
    taskEXIT_CRITICAL();

    TASKPOOL_NO_FUNCTION_CLEANUP();
}

/*-----------------------------------------------------------*/

IotTaskPoolError_t IotTaskPool_ScheduleDeferred( IotTaskPool_t taskPoolHandle,
                                                 IotTaskPoolJob_t job,
                                                 uint32_t timeMs )
{
    TASKPOOL_FUNCTION_ENTRY( IOT_TASKPOOL_SUCCESS );

    _taskPool_t * pTaskPool = &_IotSystemTaskPool;

    /* This lean version of the task pool only supports the task pool created
    by this library (the system task pool).  NULL means use the system task
    pool - no other values are allowed.  Use the full implementation of this
    library if you want multiple task pools (there is more than one task in
    each pool. */
    configASSERT( ( taskPoolHandle == NULL ) || ( taskPoolHandle == &_IotSystemTaskPool ) );

    TASKPOOL_ON_NULL_ARG_GOTO_CLEANUP( job );

    if( timeMs == 0UL )
    {
        TASKPOOL_SET_AND_GOTO_CLEANUP( IotTaskPool_Schedule( pTaskPool, job, 0 ) );
    }

    taskENTER_CRITICAL();
    {
        _taskPoolTimerEvent_t * pTimerEvent = IotTaskPool_MallocTimerEvent( sizeof( _taskPoolTimerEvent_t ) );

        if( pTimerEvent == NULL )
        {
            taskEXIT_CRITICAL();

            TASKPOOL_SET_AND_GOTO_CLEANUP( IOT_TASKPOOL_NO_MEMORY );
        }

        IotLink_t * pTimerEventLink;

        TickType_t now = xTaskGetTickCount();

        pTimerEvent->link.pNext = NULL;
        pTimerEvent->link.pPrevious = NULL;
        pTimerEvent->expirationTime = now + pdMS_TO_TICKS( timeMs );
        pTimerEvent->job = job; //_RB_ Think up to here can be outside the critical section.

        /* Append the timer event to the timer list. */
        IotListDouble_InsertSorted( &pTaskPool->timerEventsList, &pTimerEvent->link, _timerEventCompare );

        /* Update the job status to 'scheduled'. */
        job->status = IOT_TASKPOOL_STATUS_DEFERRED;

        /* Peek the first event in the timer event list. There must be at least one,
         * since we just inserted it. */
        pTimerEventLink = IotListDouble_PeekHead( &pTaskPool->timerEventsList );
        IotTaskPool_Assert( pTimerEventLink != NULL );

        /* If the event we inserted is at the front of the queue, then
         * we need to reschedule the underlying timer. */
        if( pTimerEventLink == &pTimerEvent->link )
        {
            pTimerEvent = IotLink_Container( _taskPoolTimerEvent_t, pTimerEventLink, link );

            _rescheduleDeferredJobsTimer( pTaskPool->timer, pTimerEvent );
        }
    }
    taskEXIT_CRITICAL();

    TASKPOOL_NO_FUNCTION_CLEANUP();
}

/*-----------------------------------------------------------*/

IotTaskPoolError_t IotTaskPool_GetStatus( IotTaskPool_t taskPoolHandle,
                                          IotTaskPoolJob_t job,
                                          IotTaskPoolJobStatus_t * const pStatus )
{
    TASKPOOL_FUNCTION_ENTRY( IOT_TASKPOOL_SUCCESS );

    /* This lean version of the task pool only supports the task pool created
    by this library (the system task pool).  NULL means use the system task
    pool - no other values are allowed.  Use the full implementation of this
    library if you want multiple task pools (there is more than one task in
    each pool. */
    configASSERT( ( taskPoolHandle == NULL ) || ( taskPoolHandle == &_IotSystemTaskPool ) );
    ( void ) taskPoolHandle;

    /* Parameter checking. */
    TASKPOOL_ON_NULL_ARG_GOTO_CLEANUP( job );
    TASKPOOL_ON_NULL_ARG_GOTO_CLEANUP( pStatus );
    *pStatus = IOT_TASKPOOL_STATUS_UNDEFINED;

    taskENTER_CRITICAL();
    {
        *pStatus = job->status;
    }
    taskEXIT_CRITICAL();

    TASKPOOL_NO_FUNCTION_CLEANUP();
}

/*-----------------------------------------------------------*/

IotTaskPoolError_t IotTaskPool_TryCancel( IotTaskPool_t taskPoolHandle,
                                          IotTaskPoolJob_t job,
                                          IotTaskPoolJobStatus_t * const pStatus )
{
    TASKPOOL_FUNCTION_ENTRY( IOT_TASKPOOL_SUCCESS );

    _taskPool_t * const pTaskPool = &_IotSystemTaskPool;

    /* This lean version of the task pool only supports the task pool created
    by this library (the system task pool).  NULL means use the system task
    pool - no other values are allowed.  Use the full implementation of this
    library if you want multiple task pools (there is more than one task in
    each pool. */
    configASSERT( ( taskPoolHandle == NULL ) || ( taskPoolHandle == &_IotSystemTaskPool ) );
    TASKPOOL_ON_NULL_ARG_GOTO_CLEANUP( job );

    if( pStatus != NULL )
    {
        *pStatus = IOT_TASKPOOL_STATUS_UNDEFINED;
    }

    taskENTER_CRITICAL();
    {
        status = _tryCancelInternal( pTaskPool, job, pStatus );
    }
    taskEXIT_CRITICAL();

    TASKPOOL_NO_FUNCTION_CLEANUP();
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

        default:
            pMessage = "INVALID STATUS";
            break;
    }

    return pMessage;
}

/* ---------------------------------------------------------------------------------------------- */
/* ---------------------------------------------------------------------------------------------- */
/* ---------------------------------------------------------------------------------------------- */

static IotTaskPoolError_t _performTaskPoolParameterValidation( const IotTaskPoolInfo_t * const pInfo )
{
    TASKPOOL_FUNCTION_ENTRY( IOT_TASKPOOL_SUCCESS );

    /* Check input values for consistency. */
    TASKPOOL_ON_NULL_ARG_GOTO_CLEANUP( pInfo );
    TASKPOOL_ON_ARG_ERROR_GOTO_CLEANUP( pInfo->minThreads > pInfo->maxThreads );
    TASKPOOL_ON_ARG_ERROR_GOTO_CLEANUP( pInfo->minThreads < 1UL );
    TASKPOOL_ON_ARG_ERROR_GOTO_CLEANUP( pInfo->maxThreads < 1UL );

    TASKPOOL_NO_FUNCTION_CLEANUP();
}

static void _initTaskPoolControlStructures( _taskPool_t * const pTaskPool )
{
    /* Initialize a job data structures that require no de-initialization.
     * All other data structures carry a value of 'NULL' before initailization.
     */
    IotDeQueue_Create( &pTaskPool->dispatchQueue );
    IotListDouble_Create( &pTaskPool->timerEventsList );

    _initJobsCache( &pTaskPool->jobsCache );

    /* Initialize the semaphore for waiting for incoming work.  Cannot fail as
    statically allocated. */
    pTaskPool->dispatchSignal = xSemaphoreCreateCountingStatic( TASKPOOL_MAX_SEM_VALUE, 0, &pTaskPool->dispatchSignalBuffer );
}

static IotTaskPoolError_t _createTaskPool( const IotTaskPoolInfo_t * const pInfo,
                                           _taskPool_t * const pTaskPool )
{
    TASKPOOL_FUNCTION_ENTRY( IOT_TASKPOOL_SUCCESS );

    uint32_t threadsCreated = 0; /* Although initialised before use removing the initialiser here results in compiler warnings. */
    char cTaskName[ 10 ];

    /* Check input values for consistency. */
    TASKPOOL_ON_NULL_ARG_GOTO_CLEANUP( pTaskPool );

    /* Zero out all data structures. */
    memset( ( void * ) pTaskPool, 0x00, sizeof( _taskPool_t ) );

    /* Initialize all internal data structure prior to creating all threads. */
    _initTaskPoolControlStructures( pTaskPool );

    /* Create the timer for a new connection. */
    pTaskPool->timer = xTimerCreate( NULL, portMAX_DELAY, pdFALSE, ( void * ) pTaskPool, _timerCallback );

    if( pTaskPool->timer == NULL )
    {
        IotLogError( "Failed to create timer for task pool." );

        TASKPOOL_SET_AND_GOTO_CLEANUP( IOT_TASKPOOL_NO_MEMORY );
    }

    /* The task pool will initialize the minimum number of threads requested by the user upon start.
    Note this tailored version of the task pool does not autoscale, but fixes the number of tasks
    in the pool to the originally specified minimum, and the specified maximum value is ignored. */
    /* Create the minimum number of threads specified by the user, and if one fails shutdown and return error. */
    for( threadsCreated = 0; threadsCreated < pInfo->minThreads; )
    {
        TaskHandle_t task = NULL;

        /* Generate a unique name for the task. */
        snprintf( cTaskName, sizeof( cTaskName ), "pool%d", ( int ) threadsCreated );

        BaseType_t res = xTaskCreate( _taskPoolWorker,
                                      cTaskName,
                                      pInfo->stackSize / sizeof( portSTACK_TYPE ), /* xTaskCreate() expects the stack size to be specified in words. */
                                      pTaskPool,
                                      pInfo->priority,
                                      &task );

        /* Create one thread. */
        if( res == pdFALSE ) //_RB_ would not be needed if tasks are created statically.
        {
            IotLogError( "Could not create worker thread! Exiting..." );

            /* If creating one thread fails, set error condition and exit the loop. */
            TASKPOOL_SET_AND_GOTO_CLEANUP( IOT_TASKPOOL_NO_MEMORY );
        }

        /* Upon successful thread creation, increase the number of active threads. */
        pTaskPool->activeThreads++;
        IotTaskPool_Assert( task != NULL );

        ++threadsCreated;
    }

    TASKPOOL_FUNCTION_CLEANUP();

    /* In case of failure, wait on the created threads to exit. */
    if( TASKPOOL_FAILED( status ) )
    {
        /* Set the exit condition for the newly created threads. */
#pragma message( "Threads need to be created statically here to ensure creation cannot fail as there is no shutdown mechanism." )
        _destroyTaskPool( pTaskPool );
    }

    pTaskPool->running = true;

    TASKPOOL_FUNCTION_CLEANUP_END();
}

/*-----------------------------------------------------------*/

static void _destroyTaskPool( _taskPool_t * const pTaskPool )
{
    if( pTaskPool->timer != NULL )
    {
        xTimerDelete( pTaskPool->timer, 0 );
    }
}

/* ---------------------------------------------------------------------------------------------- */

static void _taskPoolWorker( void * pUserContext )
{
    IotTaskPool_Assert( pUserContext != NULL );

    IotTaskPoolRoutine_t userCallback = NULL;

    /* Extract pTaskPool pointer from context. */
    _taskPool_t * pTaskPool = ( _taskPool_t * ) pUserContext;

    /* OUTER LOOP: it controls the lifetime of the worker thread. */
    for( ;; )
    {
        IotLink_t * pFirst = NULL;
        _taskPoolJob_t * pJob = NULL;

        /* Wait on incoming notifications... */
        configASSERT( pTaskPool->dispatchSignal );
        xSemaphoreTake( pTaskPool->dispatchSignal, portMAX_DELAY );

        /* Acquire the lock to check for incoming notifications. */
        taskENTER_CRITICAL();
        {
            /* Dequeue the first job in FIFO order. */
            pFirst = IotDeQueue_DequeueHead( &pTaskPool->dispatchQueue );

            /* If there is indeed a job, then update status under lock, and release the lock before processing the job. */
            if( pFirst != NULL )
            {
                /* Extract the job from its link. */
                pJob = IotLink_Container( _taskPoolJob_t, pFirst, link );

                /* Update status to 'executing'. */
                pJob->status = IOT_TASKPOOL_STATUS_COMPLETED; /*_RB_ Should this be 'executing'? */
                userCallback = pJob->userCallback;
            }
        }
        taskEXIT_CRITICAL();

        /* INNER LOOP: it controls the execution of jobs: the exit condition is the lack of a job to execute. */
        while( pJob != NULL )
        {
            /* Process the job by invoking the associated callback with the user context.
             * This task pool thread will not be available until the user callback returns.
             */
            {
                IotTaskPool_Assert( IotLink_IsLinked( &pJob->link ) == false );
                IotTaskPool_Assert( userCallback != NULL );

                userCallback( pTaskPool, pJob, pJob->pUserContext );

                /* This job is finished, clear its pointer. */
                pJob = NULL;
                userCallback = NULL;
            }

            /* Acquire the lock before updating the job status. */
            taskENTER_CRITICAL();
            {
                /* Try and dequeue the next job in the dispatch queue. */
                IotLink_t * pItem = NULL;

                /* Dequeue the next job from the dispatch queue. */
                pItem = IotDeQueue_DequeueHead( &pTaskPool->dispatchQueue );

                /* If there is no job left in the dispatch queue, update the worker status and leave. */
                if( pItem == NULL )
                {
                    taskEXIT_CRITICAL();

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
            taskEXIT_CRITICAL();
        }
    }
}

/* ---------------------------------------------------------------------------------------------- */

static void _initJobsCache( _taskPoolCache_t * const pCache )
{
    IotDeQueue_Create( &pCache->freeList );

    pCache->freeCount = 0;
}

/*-----------------------------------------------------------*/

static void _initializeJob( _taskPoolJob_t * const pJob,
                            IotTaskPoolRoutine_t userCallback,
                            void * pUserContext,
                            bool isStatic )
{
    pJob->link.pNext = NULL;
    pJob->link.pPrevious = NULL;
    pJob->userCallback = userCallback;
    pJob->pUserContext = pUserContext;

    if( isStatic )
    {
        pJob->flags = IOT_TASK_POOL_INTERNAL_STATIC;
        pJob->status = IOT_TASKPOOL_STATUS_READY;
    }
    else
    {
        pJob->status = IOT_TASKPOOL_STATUS_READY;
    }
}

static _taskPoolJob_t * _fetchOrAllocateJob( _taskPoolCache_t * const pCache )
{
    _taskPoolJob_t * pJob = NULL;
    IotLink_t * pLink = IotListDouble_RemoveHead( &( pCache->freeList ) );

    if( pLink != NULL )
    {
        pJob = IotLink_Container( _taskPoolJob_t, pLink, link );
    }

    /* If there is no available job in the cache, then allocate one. */
    if( pJob == NULL )
    {
        pJob = ( _taskPoolJob_t * ) IotTaskPool_MallocJob( sizeof( _taskPoolJob_t ) );

        if( pJob != NULL )
        {
            memset( pJob, 0x00, sizeof( _taskPoolJob_t ) );
        }
        else
        {
            /* Log allocation failure for troubleshooting purposes. */
            IotLogInfo( "Failed to allocate job." );
        }
    }
    /* If there was a job in the cache, then make sure we keep the counters up-to-date. */
    else
    {
        IotTaskPool_Assert( pCache->freeCount > 0 );

        pCache->freeCount--;
    }

    return pJob;
}

/*-----------------------------------------------------------*/

static void _recycleJob( _taskPoolCache_t * const pCache,
                         _taskPoolJob_t * const pJob )
{
    /* We should never try and recycling a job that is linked into some queue. */
    IotTaskPool_Assert( IotLink_IsLinked( &pJob->link ) == false );//_RB_ Seems to be duplicate of test before this is called.

    /* We will recycle the job if there is space in the cache. */
    if( pCache->freeCount < IOT_TASKPOOL_JOBS_RECYCLE_LIMIT )
    {
        /* Destroy user data, for added safety&security. */
        pJob->userCallback = NULL;
        pJob->pUserContext = NULL;

        /* Reset the status for added debuggability. */
        pJob->status = IOT_TASKPOOL_STATUS_UNDEFINED;

        IotListDouble_InsertTail( &pCache->freeList, &pJob->link );

        pCache->freeCount++;

        IotTaskPool_Assert( pCache->freeCount >= 1 );
    }
    else
    {
        _destroyJob( pJob );
    }
}

/*-----------------------------------------------------------*/

static void _destroyJob( _taskPoolJob_t * const pJob )
{
    /* Destroy user data, for added safety & security. */
    pJob->userCallback = NULL;
    pJob->pUserContext = NULL;

    /* Reset the status for added debuggability. */
    pJob->status = IOT_TASKPOOL_STATUS_UNDEFINED;

    /* Only dispose of dynamically allocated jobs. */
    if( ( pJob->flags & IOT_TASK_POOL_INTERNAL_STATIC ) == 0UL )
    {
        IotTaskPool_FreeJob( pJob );
    }
}

/* ---------------------------------------------------------------------------------------------- */

static IotTaskPoolError_t _scheduleInternal( _taskPool_t * const pTaskPool,
                                             _taskPoolJob_t * const pJob )
{
    TASKPOOL_FUNCTION_ENTRY( IOT_TASKPOOL_SUCCESS );

    /* Update the job status to 'scheduled'. */
    pJob->status = IOT_TASKPOOL_STATUS_SCHEDULED;

    /* Append the job to the dispatch queue. */
    IotDeQueue_EnqueueTail( &pTaskPool->dispatchQueue, &pJob->link );

    /* Signal a worker to pick up the job. */
    xSemaphoreGive( pTaskPool->dispatchSignal );

    TASKPOOL_NO_FUNCTION_CLEANUP_NOLABEL();
}

/*-----------------------------------------------------------*/

static bool _matchJobByPointer( const IotLink_t * const pLink,
                                void * pMatch )
{
    const _taskPoolJob_t * const pJob = ( _taskPoolJob_t * ) pMatch;

    const _taskPoolTimerEvent_t * const pTimerEvent = IotLink_Container( _taskPoolTimerEvent_t, pLink, link );

    if( pJob == pTimerEvent->job )
    {
        return true;
    }

    return false;
}

/*-----------------------------------------------------------*/

static IotTaskPoolError_t _tryCancelInternal( _taskPool_t * const pTaskPool,
                                              _taskPoolJob_t * const pJob,
                                              IotTaskPoolJobStatus_t * const pStatus )
{
    TASKPOOL_FUNCTION_ENTRY( IOT_TASKPOOL_SUCCESS );

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
            /* Log message for debug purposes purposes. */
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
        TASKPOOL_SET_AND_GOTO_CLEANUP( IOT_TASKPOOL_CANCEL_FAILED );
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
            IotTaskPool_Assert( IotLink_IsLinked( &pJob->link ) );

            IotDeQueue_Remove( &pJob->link );
        }

        /* If the job current status is 'deferred' then the job has to be pending
         * in the timeouts queue. */
        else if( currentStatus == IOT_TASKPOOL_STATUS_DEFERRED )
        {
            /* Find the timer event associated with the current job. There MUST be one, hence assert if not. */
            IotLink_t * pTimerEventLink = IotListDouble_FindFirstMatch( &pTaskPool->timerEventsList, NULL, _matchJobByPointer, pJob );
            IotTaskPool_Assert( pTimerEventLink != NULL );

            if( pTimerEventLink != NULL )
            {
                bool shouldReschedule = false;

                /* If the job being canceled was at the head of the timeouts queue, then we need to reschedule the timer
                 * with the next job timeout */
                IotLink_t * pHeadLink = IotListDouble_PeekHead( &pTaskPool->timerEventsList );

                if( pHeadLink == pTimerEventLink )
                {
                    shouldReschedule = true;
                }

                /* Remove the timer event associated with the canceled job and free the associated memory. */
                IotListDouble_Remove( pTimerEventLink );
                IotTaskPool_FreeTimerEvent( IotLink_Container( _taskPoolTimerEvent_t, pTimerEventLink, link ) );

                if( shouldReschedule )
                {
                    IotLink_t * pNextTimerEventLink = IotListDouble_PeekHead( &pTaskPool->timerEventsList );

                    if( pNextTimerEventLink != NULL )
                    {
                        _rescheduleDeferredJobsTimer( pTaskPool->timer, IotLink_Container( _taskPoolTimerEvent_t, pNextTimerEventLink, link ) );
                    }
                }
            }
        }
        else
        {
            /* A cancelable job status should be either 'scheduled' or 'deferrred'. */
            IotTaskPool_Assert( ( currentStatus == IOT_TASKPOOL_STATUS_READY ) || ( currentStatus == IOT_TASKPOOL_STATUS_CANCELED ) );
        }
    }

    TASKPOOL_NO_FUNCTION_CLEANUP();
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

    if( pFirstTimerEvent->expirationTime > now )
    {
        delta = pFirstTimerEvent->expirationTime - now;
    }

    if( delta < TASKPOOL_JOB_RESCHEDULE_DELAY_MS )
    {
        delta = TASKPOOL_JOB_RESCHEDULE_DELAY_MS; /* The job will be late... */
    }

    IotTaskPool_Assert( delta > 0 );

    if( xTimerChangePeriod( timer, ( uint32_t ) delta, portMAX_DELAY ) == pdFAIL )
    {
        IotLogWarn( "Failed to re-arm timer for task pool" );
    }
}

/*-----------------------------------------------------------*/

static void _timerCallback( TimerHandle_t xTimer )
{
    _taskPool_t * pTaskPool = pvTimerGetTimerID( xTimer );

    IotTaskPool_Assert( pTaskPool );

    _taskPoolTimerEvent_t * pTimerEvent = NULL;

    IotLogDebug( "Timer thread started for task pool %p.", pTaskPool );

    /* Attempt to lock the timer mutex. Return immediately if the mutex cannot be locked.
     * If this mutex cannot be locked it means that another thread is manipulating the
     * timeouts list, and will reset the timer to fire again, although it will be late.
     */
    taskENTER_CRITICAL(); //_RB_ Critical section is too long.
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
                IotLogDebug( "No further timer events to process. Exiting timer thread." );

                break;
            }

            IotLogDebug( "Scheduling job from timer event." );

            /* Queue the job associated with the received timer event. */
            ( void ) _scheduleInternal( pTaskPool, pTimerEvent->job );

            /* Free the timer event. */
            IotTaskPool_FreeTimerEvent( pTimerEvent );
        }
    }
    taskEXIT_CRITICAL();
}
