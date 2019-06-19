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
 * @file iot_taskpool_internal.h
 * @brief Internal header of task pool library. This header should not be included in
 * typical application code.
 */

#ifndef IOT_TASKPOOL_INTERNAL_H_
#define IOT_TASKPOOL_INTERNAL_H_

/* The config header is always included first. */
#include "iot_config.h"

/* Task pool include. */
#include "private/iot_error.h"
#include "iot_taskpool.h"

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "semphr.h"
#include "timers.h"

/* Establish a few convenience macros to handle errors in a standard way. */

/**
 * @brief Every public API return an enumeration value with an undelying value of 0 in case of success.
 */
#define TASKPOOL_SUCCEEDED( x )               ( ( x ) == IOT_TASKPOOL_SUCCESS )

/**
 * @brief Every public API returns an enumeration value with an undelying value different than 0 in case of success.
 */
#define TASKPOOL_FAILED( x )                  ( ( x ) != IOT_TASKPOOL_SUCCESS )

/**
 * @brief Jump to the cleanup area.
 */
#define TASKPOOL_GOTO_CLEANUP()               IOT_GOTO_CLEANUP()

/**
 * @brief Declare the storage for the error status variable.
 */
#define  TASKPOOL_FUNCTION_ENTRY( result )    IOT_FUNCTION_ENTRY( IotTaskPoolError_t, result )

/**
 * @brief Check error and leave in case of failure.
 */
#define TASKPOOL_ON_ERROR_GOTO_CLEANUP( expr )                           \
    { if( TASKPOOL_FAILED( status = ( expr ) ) ) { IOT_GOTO_CLEANUP(); } \
    }

/**
 * @brief Exit if an argument is NULL.
 */
#define TASKPOOL_ON_NULL_ARG_GOTO_CLEANUP( ptr )      IOT_VALIDATE_PARAMETER( IOT_TASKPOOL, ( ptr != NULL ) )

/**
 * @brief Exit if an argument is NULL.
 */
#define TASKPOOL_ON_ARG_ERROR_GOTO_CLEANUP( expr )    IOT_VALIDATE_PARAMETER( IOT_TASKPOOL, ( ( expr ) == false ) )

/**
 * @brief Set error and leave.
 */
#define TASKPOOL_SET_AND_GOTO_CLEANUP( expr )         IOT_SET_AND_GOTO_CLEANUP( expr )

/**
 * @brief Initialize error and declare start of cleanup area.
 */
#define TASKPOOL_FUNCTION_CLEANUP()                   IOT_FUNCTION_CLEANUP_BEGIN()

/**
 * @brief Initialize error and declare end of cleanup area.
 */
#define TASKPOOL_FUNCTION_CLEANUP_END()               IOT_FUNCTION_CLEANUP_END()

/**
 * @brief Create an empty cleanup area.
 */
#define TASKPOOL_NO_FUNCTION_CLEANUP()                IOT_FUNCTION_EXIT_NO_CLEANUP()

/**
 * @brief Does not create a cleanup area.
 */
#define TASKPOOL_NO_FUNCTION_CLEANUP_NOLABEL()        return status

/**
 * @def IotTaskPool_Assert( expression )
 * @brief Assertion macro for the Task pool library.
 *
 * Set @ref IOT_TASKPOOL_ENABLE_ASSERTS to `1` to enable assertions in the Task pool
 * library.
 *
 * @param[in] expression Expression to be evaluated.
 */
#if IOT_TASKPOOL_ENABLE_ASSERTS == 1
    #ifndef IotTaskPool_Assert
        #include <assert.h>
        #define IotTaskPool_Assert( expression )    assert( expression )
    #endif
#else
    #define IotTaskPool_Assert( expression )
#endif

/* Configure logs for TASKPOOL functions. */
#ifdef IOT_LOG_LEVEL_TASKPOOL
    #define LIBRARY_LOG_LEVEL        IOT_LOG_LEVEL_TASKPOOL
#else
    #ifdef IOT_LOG_LEVEL_GLOBAL
        #define LIBRARY_LOG_LEVEL    IOT_LOG_LEVEL_GLOBAL
    #else
        #define LIBRARY_LOG_LEVEL    IOT_LOG_NONE
    #endif
#endif

#define LIBRARY_LOG_NAME    ( "TASKPOOL" )
#include "iot_logging_setup.h"

/*
 * Provide default values for undefined memory allocation functions based on
 * the usage of dynamic memory allocation.
 */
#if IOT_STATIC_MEMORY_ONLY == 1
    #include "private/iot_static_memory.h"

/**
 * @brief Allocate an #_taskPool_t. This function should have the
 * same signature as [malloc].
 */
    void * IotTaskPool_MallocTaskPool( size_t size );

/**
 * @brief Free an #_taskPool_t. This function should have the
 * same signature as [malloc].
 */
    void IotTaskPool_FreeTaskPool( void * ptr );

/**
 * @brief Allocate an #IotTaskPoolJob_t. This function should have the
 * same signature as [malloc].
 */
    void * IotTaskPool_MallocJob( size_t size );

/**
 * @brief Free an #IotTaskPoolJob_t. This function should have the same
 * same signature as [malloc].
 * (http://pubs.opengroup.org/onlinepubs/9699919799/functions/malloc.html).
 */
    void IotTaskPool_FreeJob( void * ptr );

/**
 * @brief Allocate an #_taskPoolTimerEvent_t. This function should have the
 * same signature as [malloc].
 */
    void * IotTaskPool_MallocTimerEvent( size_t size );

/**
 * @brief Free an #_taskPoolTimerEvent_t. This function should have the
 * same signature as[ free ].
 */
    void IotTaskPool_FreeTimerEvent( void * ptr );

#else /* if IOT_STATIC_MEMORY_ONLY == 1 */
    #include <stdlib.h>

    #ifndef IotTaskPool_MallocTaskPool
        #define IotTaskPool_MallocTaskPool    malloc
    #endif

    #ifndef IotTaskPool_FreeTaskPool
        #define IotTaskPool_FreeTaskPool    free
    #endif

    #ifndef IotTaskPool_MallocJob
        #define IotTaskPool_MallocJob    malloc
    #endif

    #ifndef IotTaskPool_FreeJob
        #define IotTaskPool_FreeJob    free
    #endif

    #ifndef IotTaskPool_MallocTimerEvent
        #define IotTaskPool_MallocTimerEvent    malloc
    #endif

    #ifndef IotTaskPool_FreeTimerEvent
        #define IotTaskPool_FreeTimerEvent    free
    #endif

#endif /* if IOT_STATIC_MEMORY_ONLY == 1 */

/* ---------------------------------------------------------------------------------------------- */

/**
 * @cond DOXYGEN_IGNORE
 * Doxygen should ignore this section.
 *
 * A macros to manage task pool memory allocation.
 */
#define IOT_TASK_POOL_INTERNAL_STATIC    ( ( uint32_t ) 0x00000001 )      /* Flag to mark a job as user-allocated. */
/** @endcond */

/**
 * @brief Task pool jobs cache.
 *
 * @warning This is a system-level data type that should not be modified or used directly in any application.
 * @warning This is a system-level data type that can and will change across different versions of the platform, with no regards for backward compatibility.
 *
 */
typedef struct _taskPoolCache
{
    IotListDouble_t freeList; /**< @brief A list ot hold cached jobs. */

    uint32_t freeCount;       /**< @brief A counter to track the number of jobs in the cache. */
} _taskPoolCache_t;

/**
 * @brief The task pool data structure keeps track of the internal state and the signals for the dispatcher threads.
 * The task pool is a thread safe data structure.
 *
 * @warning This is a system-level data type that should not be modified or used directly in any application.
 * @warning This is a system-level data type that can and will change across different versions of the platform, with no regards for backward compatibility.
 *
 */
typedef struct _taskPool
{
    IotDeQueue_t dispatchQueue;              /**< @brief The queue for the jobs waiting to be executed. */
    IotListDouble_t timerEventsList;         /**< @brief The timeouts queue for all deferred jobs waiting to be executed. */
    _taskPoolCache_t jobsCache;              /**< @brief A cache to re-use jobs in order to limit memory allocations. */
    uint32_t activeThreads;                  /**< @brief The number of threads in the task pool at any given time. */
    int32_t priority;                        /**< @brief The priority for all task pool threads. */
    SemaphoreHandle_t dispatchSignal;        /**< @brief The synchronization object on which threads are waiting for incoming jobs. */
    StaticSemaphore_t dispatchSignalBuffer;  /**< @brief The semaphore buffer. */
    SemaphoreHandle_t startStopSignal;       /**< @brief The synchronization object for threads to signal start and stop condition. */
    StaticSemaphore_t startStopSignalBuffer; /**< @brief The semaphore buffer. */
    TimerHandle_t timer;                     /**< @brief The timer for deferred jobs. */
    StaticTimer_t timerBuffer;               /**< @brief The timer buffer. */
    bool running;                            /**< @brief A flag to track whether the task pool is operational or should shut down. */
} _taskPool_t;

/**
 * @brief The job data structure keeps track of the user callback and context, as well as the status of the job.
 *
 * @warning This is a system-level data type that should not be modified or used directly in any application.
 * @warning This is a system-level data type that can and will change across different versions of the platform, with no regards for backward compatibility.
 *
 */
typedef struct _taskPoolJob
{
    IotLink_t link;                    /**< @brief The link to insert the job in the dispatch queue. */
    IotTaskPoolRoutine_t userCallback; /**< @brief The user provided callback. */
    void * pUserContext;               /**< @brief The user provided context. */
    uint32_t flags;                    /**< @brief Internal flags. */
    IotTaskPoolJobStatus_t status;     /**< @brief The status for the job. */
} _taskPoolJob_t;

/**
 * @brief Represents an operation that is subject to a timer.
 *
 * These events are queued per MQTT connection. They are sorted by their
 * expiration time.
 */
typedef struct _taskPoolTimerEvent
{
    IotLink_t link;            /**< @brief List link member. */
    TickType_t expirationTime; /**< @brief When this event should be processed. */
    IotTaskPoolJob_t job;      /**< @brief The task pool job associated with this event. */
} _taskPoolTimerEvent_t;

#endif /* ifndef IOT_TASKPOOL_INTERNAL_H_ */