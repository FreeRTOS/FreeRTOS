/*
 * FreeRTOS Internal System Task Pool V1.0.0
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
 */

/**
 * @file taskpool_freertos.h
 * @brief Types and functions of the system task pool (for internal use).
 */

#ifndef TASKPOOL_H_
#define TASKPOOL_H_

/* Standard includes. */
#include <stdint.h>

/* FreeRTOS includes. */
#include "timers.h"

/*-------------------------- Task pool error codes and Job statuses --------------------------*/

/**
 * @ingroup taskpool_datatypes_enums
 * @brief Return codes of taskpool functions
 */
typedef enum taskPoolError
{
    /**
     * @brief Task pool operation general failure.
     */
    TASKPOOL_GENERAL_FAILURE = 0,

    /**
     * @brief Task pool operation completed successfully.
     */
    TASKPOOL_SUCCESS,

    /**
     * @brief Task pool operation failed because it is illegal.
     */
    TASKPOOL_ILLEGAL_OPERATION,

    /**
     * @brief Task pool operation failed due to an OS error.
     */
    TASKPOOL_FAILED_OPERATION,
} taskPoolError_t;

/*------------------------- Task pool types --------------------------*/

/**
 * @ingroup taskpool_datatypes_structs
 * @brief Count outcomes of Task Pool actions.
 *
 * @note Counting may be disabled by defining TASKPOOL_KEEP_COUNTS to 0.
 */
#ifndef TASKPOOL_KEEP_COUNTS
    #define TASKPOOL_KEEP_COUNTS    1
#endif
#if TASKPOOL_KEEP_COUNTS == 1
    struct taskPoolUsageCounts
    {
        UBaseType_t initialized;            /**< jobs initialized */

        UBaseType_t schedule_illegal;       /**< illegal to schedule a job not ready */
        UBaseType_t direct_dispatch;        /**< job with 0 wait directly dispatched */
        UBaseType_t direct_dispatch_failed; /**< direct dispatch failed */
        UBaseType_t timer_start;            /**< job timer started */

        UBaseType_t cancel;                 /**< deferred job cancelled before execution */
        UBaseType_t cancel_illegal;         /**< illegal to cancel job in non-deferred state */

        UBaseType_t timer_callback;         /**< callback runs for expired timers */
        UBaseType_t callback_dispatch;      /**< job added to dispatch queue */
        UBaseType_t callback_reschedule;    /**< timer reset due to full dispatch queue */
        UBaseType_t reschedule_failed;      /**< jobs cancelled due to failed reschedule */

        UBaseType_t job_started;            /**< worker to call job callback */
        UBaseType_t job_done;               /**< worker done with job callback */
    };

    extern struct taskPoolUsageCounts taskPoolCounts;

    #define taskPoolDumpCounts()                                   \
    do {                                                           \
        configPRINTF( ( "%24s: %5u\n", "initialized",              \
                        taskPoolCounts.initialized ) );            \
        configPRINTF( ( "%24s: %5u\n", "schedule_illegal",         \
                        taskPoolCounts.schedule_illegal ) );       \
        configPRINTF( ( "%24s: %5u\n", "direct_dispatch",          \
                        taskPoolCounts.direct_dispatch ) );        \
        configPRINTF( ( "%24s: %5u\n", "direct_dispatch_failed",   \
                        taskPoolCounts.direct_dispatch_failed ) ); \
        configPRINTF( ( "%24s: %5u\n", "timer_start",              \
                        taskPoolCounts.timer_start ) );            \
        configPRINTF( ( "%24s: %5u\n", "cancel",                   \
                        taskPoolCounts.cancel ) );                 \
        configPRINTF( ( "%24s: %5u\n", "cancel_illegal",           \
                        taskPoolCounts.cancel_illegal ) );         \
        configPRINTF( ( "%24s: %5u\n", "timer_callback",           \
                        taskPoolCounts.timer_callback ) );         \
        configPRINTF( ( "%24s: %5u\n", "callback_dispatch",        \
                        taskPoolCounts.callback_dispatch ) );      \
        configPRINTF( ( "%24s: %5u\n", "callback_reschedule",      \
                        taskPoolCounts.callback_reschedule ) );    \
        configPRINTF( ( "%24s: %5u\n", "reschedule_failed",        \
                        taskPoolCounts.reschedule_failed ) );      \
        configPRINTF( ( "%24s: %5u\n", "job_started",              \
                        taskPoolCounts.job_started ) );            \
        configPRINTF( ( "%24s: %5u\n", "job_done",                 \
                        taskPoolCounts.job_done ) );               \
    } while( 0 )
#else /* if TASKPOOL_KEEP_COUNTS == 1 */
    #define taskPoolDumpCounts( ... )
#endif /* if TASKPOOL_KEEP_COUNTS == 1 */

/**
 * @ingroup taskpool_datatypes_handles
 * @brief Forward declaration of the type for a Job instance in the Task Pool.
 *
 * This type identifies a Task Pool Job instance, which is valid after a successful
 * call to @ref taskPoolInitializeJob.
 *
 */
typedef struct taskPoolJob taskPoolJob_t;

/**
 * @ingroup taskpool_datatypes_functionpointers
 * @brief Callback type for a user callback.
 *
 * This type identifies the user callback signature to execute a task pool job.
 * This callback will be invoked by the task pool threads with the `pUserContext`
 * parameter, as specified by the user when calling @ref taskPoolSchedule, and
 * @ref taskPoolScheduleDeferred.
 *
 */
typedef void ( * taskPoolRoutine_t )( taskPoolJob_t * job,
                                      void * userContext );

/**
 * @ingroup taskpool_datatypes_structs
 * @brief Definition of a Task Pool Job instance.
 *
 * @warning This is a system-level data type that should not be modified or
 * used directly in any application.
 * @warning This is a system-level data type that can and will change across
 * different versions of the platform, with no regards for backward
 * compatibility.
 *
 */
struct taskPoolJob
{
    UBaseType_t status;             /**< status of the job */
    taskPoolRoutine_t userCallback; /**< user provided callback */
    void * userContext;             /**< user provided context */
    TimerHandle_t timer;            /**< timer for deferring a job */
    StaticTimer_t timerStorage;     /**< storage for the above timer */
};

/*------------------------- Task Pool library functions --------------------------*/

/**
 * @brief Creates the system task pool.
 *
 * This function should be called once by the application to initialize
 * the one single instance of the system task pool.  An application
 * should initialize the system task pool early in the boot sequence,
 * before posting any jobs, or initializing any other library (e.g. MQTT)
 * that uses the system task pool.
 *
 */
void taskPoolCreateSystemTaskPool( void );

/**
 * @brief Initializes a job with the user-provided storage.
 *
 * @param[in] userCallback A user-specified callback for the job.
 * @param[in] userContext A user-specified context for the callback.
 * @param[in] jobStorage The storage memory for the job data structure.
 *
 * @note This function is not thread-safe in initializing the provided job memory
 * while another task context is accessing the same memory.
 *
 * @warning A job's memory is safe for re-use ONLY when the job has been
 * executed or cancelled. Also, the contents of the job memory SHOULD NOT
 * be modified directly by the caller.
 */
void taskPoolInitializeJob( taskPoolRoutine_t userCallback,
                            void * userContext,
                            taskPoolJob_t * jobStorage );

/**
 * @brief Helper function to determine if a job memory has been initialised.
 *
 * @param[in] jobStorage The job memory.
 */
BaseType_t taskPoolIsJobInitialised( taskPoolJob_t * job );

/**
 * @brief Schedule a job to be executed after a given time interval.
 *
 * @param[in] job The job to schedule for execution. This must be first initialized
 * with a call to @ref taskPoolInitializeJob
 * @param[in] timeMs The time in milliseconds to wait before executing the job.
 *
 * @return One of the following:
 * - #TASKPOOL_SUCCESS
 * - #TASKPOOL_ILLEGAL_OPERATION
 * - #TASKPOOL_FAILED_OPERATION
 *
 * @note Be aware of the following:
 * 1. The calling task MUST have a lower priority than the timer (service) task
 * to ensure reliable behavior of the taskpool.
 * 2. This is a blocking function for starting the timer for deferred jobs.
 *
 * <b>Example</b>
 * @code{c}
 * // An example of a user context to pass to a callback through a task pool thread.
 * typedef struct JobUserContext
 * {
 *     uint32_t counter;
 * } JobUserContext_t;
 *
 * // Statically allocate job and callback context instances.
 * static taskPoolJob_t job;
 * static JobUserContext_t userContext;
 *
 * // An example of a user callback to invoke through a task pool thread.
 * static void ExecutionCb( taskPoolJob_t * job, void * context )
 * {
 *     ( void )job;
 *
 *     JobUserContext_t * pUserContext = ( JobUserContext_t * )context;
 *
 *     pUserContext->counter++;
 * }
 *
 * void TaskPoolExample( )
 * {
 *     taskPoolError_t error;
 *     taskPoolInitializeJob( ExecutionCb, &userContext, &job );
 *
 *     error = taskPoolScheduleDeferred( &job, 10 );
 *
 *     switch ( error )
 *     {
 *     case TASKPOOL_SUCCESS:
 *         break;
 *     case TASKPOOL_ILLEGAL_OPERATION:
 *         // a job that was previously scheduled or cancelled
 *         // ASSERT
 *     case TASKPOOL_GENERAL_FAILURE:
 *         // dispatch queue and timer command queue are both full
 *         logError("resource exhaustion");
 *         break;
 *     default:
 *         // ASSERT
 *     }
 *     //
 *     // ... Perform other operations ...
 *     //
 * }
 * @endcode
 */
taskPoolError_t taskPoolScheduleDeferred( taskPoolJob_t * job,
                                          uint32_t timeMs );
#define taskPoolSchedule( x )    taskPoolScheduleDeferred( x, 0 )

/**
 * @brief Attempt to cancel a job
 *
 * A job can be cancelled only if it is defer scheduled. Once it is dispatched
 * for execution, it cannot be cancelled.
 *
 * @param[in] job The job to cancel.
 *
 * @return One of the following:
 * - #TASKPOOL_SUCCESS
 * - #TASKPOOL_ILLEGAL_OPERATION
 *
 * @note Be aware of the following:
 * 1. The calling task must have a lower priority than the timer (service) task
 * to ensure reliable behavior of the taskpool.
 * 2. This is a blocking function for cancelling the timer associated with a deferred job.
 *
 */
taskPoolError_t taskPoolTryCancel( taskPoolJob_t * job );

/**
 * @brief Returns a string that describes an @ref taskPoolError_t.
 *
 * Like the POSIX's `strerror`, this function returns a string describing a
 * return code. In this case, the return code is a task pool library error code,
 * `status`.
 *
 * @param[in] status The status to describe.
 *
 * @return A read-only string that describes `status`.
 *
 * @warning The string returned by this function must never be modified.
 */
const char * taskPoolStrError( taskPoolError_t status );

#endif /* ifndef TASKPOOL_H_ */
