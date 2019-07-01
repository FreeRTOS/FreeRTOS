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

/* The config header is always included first. */
#include "iot_config.h"

/* Standard includes. */
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <string.h>

/* Platform layer includes. */
#include "platform/iot_threads.h"
#include "platform/iot_clock.h"

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
_taskPool_t _IotSystemTaskPool = { .dispatchQueue = IOT_DEQUEUE_INITIALIZER };

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
 * @param[in] pInfo The initialization information for the task pool.
 * @param[in] pTaskPool The pre-allocated instance of the task pool to initialize.
 *
 */
static IotTaskPoolError_t _initTaskPoolControlStructures( const IotTaskPoolInfo_t * const pInfo,
                                                          _taskPool_t * const pTaskPool );

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
 * Check for the exit condition.
 *
 * @param[in] pTaskPool The task pool to destroy.
 *
 */
static bool _IsShutdownStarted( const _taskPool_t * const pTaskPool );

/**
 * Set the exit condition.
 *
 * @param[in] pTaskPool The task pool to destroy.
 * @param[in] threads The number of threads active in the task pool at shutdown time.
 *
 */
static void _signalShutdown( _taskPool_t * const pTaskPool,
                             uint32_t threads );

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

IotTaskPool_t IotTaskPool_GetSystemTaskPool( void )
{
    return &_IotSystemTaskPool;
}

/*-----------------------------------------------------------*/

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

IotTaskPoolError_t IotTaskPool_Create( const IotTaskPoolInfo_t * const pInfo,
                                       IotTaskPool_t * const pTaskPool )
{
    TASKPOOL_FUNCTION_ENTRY( IOT_TASKPOOL_SUCCESS );

    _taskPool_t * pTempTaskPool = NULL;

    /* Verify that the task pool storage is valid. */
    TASKPOOL_ON_NULL_ARG_GOTO_CLEANUP( pTaskPool );

    /* Parameter checking. */
    TASKPOOL_ON_ERROR_GOTO_CLEANUP( _performTaskPoolParameterValidation( pInfo ) );

    /* Allocate the memory for the task pool */
    pTempTaskPool = ( _taskPool_t * ) IotTaskPool_MallocTaskPool( sizeof( _taskPool_t ) );

    if( pTempTaskPool == NULL )
    {
        TASKPOOL_SET_AND_GOTO_CLEANUP( IOT_TASKPOOL_NO_MEMORY );
    }

    memset( pTempTaskPool, 0x00, sizeof( _taskPool_t ) );

    TASKPOOL_SET_AND_GOTO_CLEANUP( _createTaskPool( pInfo, pTempTaskPool ) );

    TASKPOOL_FUNCTION_CLEANUP();

    if( TASKPOOL_FAILED( status ) )
    {
        if( pTempTaskPool != NULL )
        {
            IotTaskPool_FreeTaskPool( pTempTaskPool );
        }
    }
    else
    {
        *pTaskPool = pTempTaskPool;
    }

    TASKPOOL_FUNCTION_CLEANUP_END();
}

/*-----------------------------------------------------------*/

IotTaskPoolError_t IotTaskPool_Destroy( IotTaskPool_t taskPoolHandle )
{
    TASKPOOL_FUNCTION_ENTRY( IOT_TASKPOOL_SUCCESS );

    uint32_t count;
    bool completeShutdown = true;

    _taskPool_t * pTaskPool = ( _taskPool_t * ) taskPoolHandle;

    /* Track how many threads the task pool owns. */
    uint32_t activeThreads;

    /* Parameter checking. */
    TASKPOOL_ON_NULL_ARG_GOTO_CLEANUP( pTaskPool );

    /* Destroying the task pool should be safe, and therefore we will grab the task pool lock.
     * No worker thread or application thread should access any data structure
     * in the task pool while the task pool is being destroyed. */
    taskENTER_CRITICAL();
    {
        IotLink_t * pItemLink;

        /* Record how many active threads in the task pool. */
        activeThreads = pTaskPool->activeThreads;

        /* Destroying a Task pool happens in six (6) stages: First, (1) we clear the job queue and (2) the timer queue.
         * Then (3) we clear the jobs cache. We will then (4) wait for all worker threads to signal exit,
         * before (5) setting the exit condition and wake up all active worker threads. Finally (6) destroying
         * all task pool data structures and release the associated memory.
         */

        /* (1) Clear the job queue. */
        do
        {
            pItemLink = NULL;

            pItemLink = IotDeQueue_DequeueHead( &pTaskPool->dispatchQueue );

            if( pItemLink != NULL )
            {
                _taskPoolJob_t * pJob = IotLink_Container( _taskPoolJob_t, pItemLink, link );

                _destroyJob( pJob );
            }
        } while( pItemLink );

        /* (2) Clear the timer queue. */
        {
            _taskPoolTimerEvent_t * pTimerEvent;

            /* A deferred job may have fired already. Since deferred jobs will go through the same mutex
             * the shutdown sequence is holding at this stage, there is no risk for race conditions. Yet, we
             * need to let the deferred job to destroy the task pool. */

            pItemLink = IotListDouble_PeekHead( &pTaskPool->timerEventsList );

            if( pItemLink != NULL )
            {
                TickType_t now = xTaskGetTickCount();

                pTimerEvent = IotLink_Container( _taskPoolTimerEvent_t, pItemLink, link );

                if( pTimerEvent->expirationTime <= now )
                {
                    IotLogDebug( "Shutdown will be deferred to the timer thread" );

                    /* Timer may have fired already! Let the timer thread destroy
                     * complete the taskpool destruction sequence. */
                    completeShutdown = false;
                }

                /* Remove all timers from the timeout list. */
                for( ; ; )
                {
                    pItemLink = IotListDouble_RemoveHead( &pTaskPool->timerEventsList );

                    if( pItemLink == NULL )
                    {
                        break;
                    }

                    pTimerEvent = IotLink_Container( _taskPoolTimerEvent_t, pItemLink, link );

                    _destroyJob( pTimerEvent->job );

                    IotTaskPool_FreeTimerEvent( pTimerEvent );
                }
            }
        }

        /* (3) Clear the job cache. */
        do
        {
            pItemLink = NULL;

            pItemLink = IotListDouble_RemoveHead( &pTaskPool->jobsCache.freeList );

            if( pItemLink != NULL )
            {
                _taskPoolJob_t * pJob = IotLink_Container( _taskPoolJob_t, pItemLink, link );

                _destroyJob( pJob );
            }
        } while( pItemLink );

        /* (4) Set the exit condition. */
        _signalShutdown( pTaskPool, activeThreads );
    }
    taskEXIT_CRITICAL();

    /* (5) Wait for all active threads to reach the end of their life-span. */
    for( count = 0; count < activeThreads; ++count )
    {
        xSemaphoreTake( pTaskPool->startStopSignal, portMAX_DELAY );
    }

    IotTaskPool_Assert( uxSemaphoreGetCount( pTaskPool->startStopSignal ) == 0 );
    IotTaskPool_Assert( pTaskPool->activeThreads == 0 );

    /* (6) Destroy all signaling objects. */
    if( completeShutdown == true )
    {
        _destroyTaskPool( pTaskPool );

        /* Do not free the system task pool which is statically allocated. */
        if( pTaskPool != &_IotSystemTaskPool )
        {
            IotTaskPool_FreeTaskPool( pTaskPool );
        }
    }

    TASKPOOL_NO_FUNCTION_CLEANUP();
}

/*-----------------------------------------------------------*/

IotTaskPoolError_t IotTaskPool_SetMaxThreads( IotTaskPool_t taskPoolHandle,
                                              uint32_t maxThreads )
{
    TASKPOOL_FUNCTION_ENTRY( IOT_TASKPOOL_SUCCESS );

    _taskPool_t * pTaskPool = ( _taskPool_t * ) taskPoolHandle;

    /* Parameter checking. */
    TASKPOOL_ON_NULL_ARG_GOTO_CLEANUP( pTaskPool );
    TASKPOOL_ON_ARG_ERROR_GOTO_CLEANUP( maxThreads < 1UL );

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

IotTaskPoolError_t IotTaskPool_CreateRecyclableSystemJob( IotTaskPoolRoutine_t userCallback,
                                                          void * pUserContext,
                                                          IotTaskPoolJob_t * const pJob )
{
    return IotTaskPool_CreateRecyclableJob ( &_IotSystemTaskPool, userCallback, pUserContext, pJob );
}

/*-----------------------------------------------------------*/

IotTaskPoolError_t IotTaskPool_CreateRecyclableJob( IotTaskPool_t taskPoolHandle,
                                                    IotTaskPoolRoutine_t userCallback,
                                                    void * pUserContext,
                                                    IotTaskPoolJob_t * const ppJob )
{
    TASKPOOL_FUNCTION_ENTRY( IOT_TASKPOOL_SUCCESS );

    _taskPool_t * pTaskPool = ( _taskPool_t * ) taskPoolHandle;
    _taskPoolJob_t * pTempJob = NULL;

    /* Parameter checking. */
    TASKPOOL_ON_NULL_ARG_GOTO_CLEANUP( taskPoolHandle );
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

    ( void ) taskPoolHandle;

    _taskPoolJob_t * pJob = ( _taskPoolJob_t * ) pJobHandle;

    /* Parameter checking. */
    TASKPOOL_ON_NULL_ARG_GOTO_CLEANUP( taskPoolHandle );
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

    _taskPool_t * pTaskPool = ( _taskPool_t * ) taskPoolHandle;

    /* Parameter checking. */
    TASKPOOL_ON_NULL_ARG_GOTO_CLEANUP( taskPoolHandle );
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

    _taskPool_t * pTaskPool = ( _taskPool_t * ) taskPoolHandle;

    configASSERT( pTaskPool->running != false );

    /* Parameter checking. */
    TASKPOOL_ON_NULL_ARG_GOTO_CLEANUP( taskPoolHandle );
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

IotTaskPoolError_t IotTaskPool_ScheduleSystemJob( IotTaskPoolJob_t pJob,
                                                  uint32_t flags )
{
    return IotTaskPool_Schedule( &_IotSystemTaskPool, pJob, flags );
}

/*-----------------------------------------------------------*/

IotTaskPoolError_t IotTaskPool_ScheduleDeferred( IotTaskPool_t taskPoolHandle,
                                                 IotTaskPoolJob_t job,
                                                 uint32_t timeMs )
{
    TASKPOOL_FUNCTION_ENTRY( IOT_TASKPOOL_SUCCESS );

    _taskPool_t * pTaskPool = ( _taskPool_t * ) taskPoolHandle;

    /* Parameter checking. */
    TASKPOOL_ON_NULL_ARG_GOTO_CLEANUP( taskPoolHandle );
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
        pTimerEvent->job = job;

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

    /* Parameter checking. */
    TASKPOOL_ON_NULL_ARG_GOTO_CLEANUP( taskPoolHandle );
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

    _taskPool_t * pTaskPool = ( _taskPool_t * ) taskPoolHandle;

    /* Parameter checking. */
    TASKPOOL_ON_NULL_ARG_GOTO_CLEANUP( taskPoolHandle );
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

static IotTaskPoolError_t _initTaskPoolControlStructures( const IotTaskPoolInfo_t * const pInfo,
                                                          _taskPool_t * const pTaskPool )
{
    TASKPOOL_FUNCTION_ENTRY( IOT_TASKPOOL_SUCCESS );

    bool semStartStopInit = false;
    bool semDispatchInit = false;

    /* Initialize a job data structures that require no de-initialization.
     * All other data structures carry a value of 'NULL' before initailization.
     */
    IotDeQueue_Create( &pTaskPool->dispatchQueue );
    IotListDouble_Create( &pTaskPool->timerEventsList );

    _initJobsCache( &pTaskPool->jobsCache );

    /* Initialize the semaphore to ensure all threads have started. */
    pTaskPool->startStopSignal = xSemaphoreCreateCountingStatic( pInfo->minThreads, 0, &pTaskPool->startStopSignalBuffer );

    if( pTaskPool->startStopSignal != NULL )
    {
        semStartStopInit = true;

        /* Initialize the semaphore for waiting for incoming work. */
        pTaskPool->dispatchSignal = xSemaphoreCreateCountingStatic( TASKPOOL_MAX_SEM_VALUE, 0, &pTaskPool->dispatchSignalBuffer );

        if( pTaskPool->dispatchSignal != NULL )
        {
            semDispatchInit = true;
        }
        else
        {
            TASKPOOL_SET_AND_GOTO_CLEANUP( IOT_TASKPOOL_NO_MEMORY );
        }
    }
    else
    {
        TASKPOOL_SET_AND_GOTO_CLEANUP( IOT_TASKPOOL_NO_MEMORY );
    }

    TASKPOOL_FUNCTION_CLEANUP();

    if( TASKPOOL_FAILED( status ) )
    {
        if( semStartStopInit )
        {
            vSemaphoreDelete( &pTaskPool->startStopSignal );
        }

        if( semDispatchInit )
        {
            vSemaphoreDelete( &pTaskPool->dispatchSignal );
        }
    }

    TASKPOOL_FUNCTION_CLEANUP_END();
}

static IotTaskPoolError_t _createTaskPool( const IotTaskPoolInfo_t * const pInfo,
                                           _taskPool_t * const pTaskPool )
{
    TASKPOOL_FUNCTION_ENTRY( IOT_TASKPOOL_SUCCESS );

    uint32_t count;
    uint32_t threadsCreated;

    /* Check input values for consistency. */
    TASKPOOL_ON_NULL_ARG_GOTO_CLEANUP( pTaskPool );

    /* Zero out all data structures. */
    memset( ( void * ) pTaskPool, 0x00, sizeof( _taskPool_t ) );

    /* Initialize all internal data structure prior to creating all threads. */
    TASKPOOL_ON_ERROR_GOTO_CLEANUP( _initTaskPoolControlStructures( pInfo, pTaskPool ) );

    /* Create the timer for a new connection. */
    pTaskPool->timer = xTimerCreate( NULL, portMAX_DELAY, pdFALSE, ( void * ) pTaskPool, _timerCallback );

    if( pTaskPool->timer == NULL )
    {
        IotLogError( "Failed to create timer for task pool." );

        TASKPOOL_SET_AND_GOTO_CLEANUP( IOT_TASKPOOL_NO_MEMORY );
    }

    /* The task pool will initialize the minimum number of threads requested by the user upon start. */
    /* When a thread is created, it will signal a semaphore to signify that it is about to wait on incoming */
    /* jobs. A thread can be woken up for exit or for new jobs only at that point in time.  */
    /* The exit condition is setting the maximum number of threads to 0. */

    /* Create the minimum number of threads specified by the user, and if one fails shutdown and return error. */
    for( threadsCreated = 0; threadsCreated < pInfo->minThreads; )
    {
        TaskHandle_t task = NULL;

        BaseType_t res = xTaskCreate( _taskPoolWorker,
                                      NULL,
                                      pInfo->stackSize,
                                      pTaskPool,
                                      pInfo->priority,
                                      &task );

        /* Create one thread. */
        if( res == pdFALSE )
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

    /* Wait for threads to be ready to wait on the condition, so that threads are actually able to receive messages. */
    for( count = 0; count < threadsCreated; ++count )
    {
        xSemaphoreTake( pTaskPool->startStopSignal, portMAX_DELAY ); /*_RB_ Is waiting necessary, and if so, is a semaphore necessary? */
    }

    /* In case of failure, wait on the created threads to exit. */
    if( TASKPOOL_FAILED( status ) )
    {
        /* Set the exit condition for the newly created threads. */
        _signalShutdown( pTaskPool, threadsCreated );

        /* Signal all threads to exit. */
        for( count = 0; count < threadsCreated; ++count )
        {
            xSemaphoreTake( pTaskPool->startStopSignal, portMAX_DELAY );
        }

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

    if( pTaskPool->dispatchSignal != NULL )
    {
        vSemaphoreDelete( pTaskPool->dispatchSignal );
    }

    if( pTaskPool->startStopSignal != NULL )
    {
        vSemaphoreDelete( pTaskPool->startStopSignal );
    }
}

/* ---------------------------------------------------------------------------------------------- */

static void _taskPoolWorker( void * pUserContext )
{
    IotTaskPool_Assert( pUserContext != NULL );

    IotTaskPoolRoutine_t userCallback = NULL;
    bool running = true;

    /* Extract pTaskPool pointer from context. */
    _taskPool_t * pTaskPool = ( _taskPool_t * ) pUserContext;

    /* Signal that this worker completed initialization and it is ready to receive notifications. */
    ( void ) xSemaphoreGive( pTaskPool->startStopSignal );

    /* OUTER LOOP: it controls the lifetiem of the worker thread: exit condition for a worker thread
     * is setting maxThreads to zero. A worker thread is running until the maximum number of allowed
     * threads is not zero and the active threads are less than the maximum number of allowed threads.
     */
    do
    {
        IotLink_t * pFirst = NULL;
        _taskPoolJob_t * pJob = NULL;

        /* Wait on incoming notifications... */
        xSemaphoreTake( pTaskPool->dispatchSignal, portMAX_DELAY );

        /* Acquire the lock to check the exit condition, and release the lock if the exit condition is verified,
         * or before waiting for incoming notifications.
         */
        taskENTER_CRITICAL();
        {
            /* If the exit condition is verified, update the number of active threads and exit the loop. */
            if( _IsShutdownStarted( pTaskPool ) )
            {
                IotLogDebug( "Worker thread exiting because exit condition was set." );

                /* Decrease the number of active threads. */
                pTaskPool->activeThreads--;

                taskEXIT_CRITICAL();

                /* Signal that this worker is exiting. */
                xSemaphoreGive( pTaskPool->startStopSignal );

                /* On shutdown, abandon the OUTER LOOP immediately. */
                break;
            }

            /* Dequeue the first job in FIFO order. */
            pFirst = IotDeQueue_DequeueHead( &pTaskPool->dispatchQueue );

            /* If there is indeed a job, then update status under lock, and release the lock before processing the job. */
            if( pFirst != NULL )
            {
                /* Extract the job from its link. */
                pJob = IotLink_Container( _taskPoolJob_t, pFirst, link );

                /* Update status to 'executing'. */
                pJob->status = IOT_TASKPOOL_STATUS_COMPLETED;
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

                /* If this thread exceeded the quota, then let it terminate. */
                if( running == false )
                {
                    /* Abandon the INNER LOOP. Execution will tranfer back to the OUTER LOOP condition. */
                    break;
                }
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

                    /* Abandon the INNER LOOP. Execution will tranfer back to the OUTER LOOP condition. */
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
    } while( running == true );

    vTaskDelete( NULL );
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
            /* Log alocation failure for troubleshooting purposes. */
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
    IotTaskPool_Assert( IotLink_IsLinked( &pJob->link ) == false );

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

static bool _IsShutdownStarted( const _taskPool_t * const pTaskPool )
{
    return( pTaskPool->running == false );
}

/*-----------------------------------------------------------*/

static void _signalShutdown( _taskPool_t * const pTaskPool,
                             uint32_t threads )
{
    uint32_t count;

    /* Set the exit condition. */
    pTaskPool->running = false;

    /* Broadcast to all active threads to wake-up. Active threads do check the exit condition right after wakein up. */
    for( count = 0; count < threads; ++count )
    {
        ( void ) xSemaphoreGive( pTaskPool->dispatchSignal );
    }
}

/* ---------------------------------------------------------------------------------------------- */

static IotTaskPoolError_t _scheduleInternal( _taskPool_t * const pTaskPool,
                                             _taskPoolJob_t * const pJob )
{
    TASKPOOL_FUNCTION_ENTRY( IOT_TASKPOOL_SUCCESS );

    /* Update the job status to 'scheduled'. */
    pJob->status = IOT_TASKPOOL_STATUS_SCHEDULED;

    BaseType_t higherPriorityTaskWoken;

    /* Append the job to the dispatch queue. */
    IotDeQueue_EnqueueTail( &pTaskPool->dispatchQueue, &pJob->link );

    /* Signal a worker to pick up the job. */
    ( void ) xSemaphoreGiveFromISR( pTaskPool->dispatchSignal, &higherPriorityTaskWoken );

    portYIELD_FROM_ISR( higherPriorityTaskWoken );

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
            /* Log mesggesong purposes. */
            IotLogWarn( "Attempt to cancel a job that is already executing, or canceled." );
            break;

        default:
            /* Log mesggesong purposes. */
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

                /* If the job being cancelled was at the head of the timeouts queue, then we need to reschedule the timer
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
    taskENTER_CRITICAL();
    {
        /* Check again for shutdown and bail out early in case. */
        if( _IsShutdownStarted( pTaskPool ) )
        {
            taskEXIT_CRITICAL();

            /* Complete the shutdown sequence. */
            _destroyTaskPool( pTaskPool );

            return;
        }

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
