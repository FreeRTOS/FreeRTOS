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
 * @file taskpool_freertos.c
 * @brief Implements the internal system task pool functions for FreeRTOS.
 *
 * Internal FreeRTOS use cases do not require a general task pool, so an optimized
 * implementation is provided specifically for use with FreeRTOS.  The optimized
 * version has a fixed number of tasks in the pool, each of which uses statically
 * allocated memory to ensure creation of the pool is guaranteed (it does not run out
 * of heap space).  The constant TASKPOOL_NUMBER_OF_WORKERS sets the number of
 * tasks in the pool.
 *
 * This version:
 *   + Only supports a single task pool (system task pool) at a time.
 *   + Does not auto-scale by dynamically adding more tasks.  The number of tasks
 *     in the pool are fixed at compile time. See the task pool configuration
 *     options for more information.
 *   + Cannot be shut down - it exists for the lifetime of the application.
 */


/* Kernel includes. */
#include "FreeRTOS.h"
#include "queue.h"
#include "timers.h"

/* Standard includes. */
#include <stdint.h>

#if configSUPPORT_STATIC_ALLOCATION != 1
    #error configSUPPORT_STATIC_ALLOCATION must be set to 1 in FreeRTOSConfig.h
#endif

#if configUSE_TIMERS != 1
    #error configUSE_TIMERS must be set to 1 in FreeRTOSConfig.h
#endif

#if INCLUDE_vTaskSuspend != 1
    #error INCLUDE_vTaskSuspend must be set to 1 in FreeRTOSConfig.h
#endif

/* Task pool include. */
#include "taskpool_freertos.h"

#ifndef configTASKPOOL_DISPATCH_QUEUE_LENGTH
    #define configTASKPOOL_DISPATCH_QUEUE_LENGTH    16U
#endif
#ifndef configTASKPOOL_NUMBER_OF_WORKERS
    #error configTASKPOOL_NUMBER_OF_WORKERS must be defined for the task pool.
#endif
#ifndef configTASKPOOL_WORKER_PRIORITY
    #error configTASKPOOL_WORKER_PRIORITY must be defined for the task pool.
#endif
#ifndef configTASKPOOL_WORKER_STACK_SIZE_BYTES
    #define configTASKPOOL_WORKER_STACK_SIZE_BYTES    2048U
#endif

#if TASKPOOL_KEEP_COUNTS == 1
    #define increment( x )    ( taskPoolCounts.x++ )
#else
    #define increment( x )
#endif

/*
 * Macros for states of a task pool job.
 * These are not thread-safe and thus, are internal to the taskpool.
 */

/**
 * Job is uninitialized.
 */
#define TASKPOOL_JOB_STATUS_UNDEFINED          0U

/**
 * Job is ready to be dispatched or scheduled.
 */
#define TASKPOOL_JOB_STATUS_READY              1U

/**
 * Job has been queued for execution.
 */
#define TASKPOOL_JOB_STATUS_DISPATCHED         2U

/**
 * Job has been scheduled for deferred execution.
 */
#define TASKPOOL_JOB_STATUS_DEFERRED           3U

/**
 * Job is executing. This is a terminal state.
 */
#define TASKPOOL_JOB_STATUS_EXECUTING          4U

/**
 * Job has been cancelled before executing.
 * This is a terminal state.
 */
#define TASKPOOL_JOB_STATUS_CANCELLED          5U

/**
 * Job has been submitted for scheduling, and
 * cannot be cancelled.
 */
#define TASKPOOL_JOB_STATUS_NOT_CANCELLABLE    6U

/* ------------------------------------------------------------------------------ */

/* @cond
 * Do not expose internal details via doxygen.
 */

/* Define instance for tracking task pool usage outcomes. */
#if TASKPOOL_KEEP_COUNTS == 1
    struct taskPoolUsageCounts taskPoolCounts;
#endif

/**
 * This internal unnamed structure holds the global state of the system task pool.
 */
#define QUEUE_BYTES    ( configTASKPOOL_DISPATCH_QUEUE_LENGTH * sizeof( struct taskPoolJob * ) )
#define STACK_WORDS    ( configTASKPOOL_WORKER_STACK_SIZE_BYTES / sizeof( portSTACK_TYPE ) )
static struct
{
    QueueHandle_t dispatchQueue;                                                     /**< queue of jobs to be executed */
    uint8_t queueData[ QUEUE_BYTES ];                                                /**< hold copies of enqueued values */
    StaticQueue_t queueBuffer;                                                       /**< static storage for queue itself */
    BaseType_t running;                                                              /**< has the task pool been started */
    StaticTask_t workerTaskTCBs[ configTASKPOOL_NUMBER_OF_WORKERS ];                 /**< static storage of TCBs for workers tasks */
    StackType_t workerTaskStacks[ configTASKPOOL_NUMBER_OF_WORKERS ][ STACK_WORDS ]; /**< static storage for stack memory of workers tasks */
}
taskPool;

/**
 * Each task pool worker runs this function perpetually.
 *
 * @param[in] userContext The user context.
 *
 */
static void taskPoolWorker( void * pContext );

/**
 * Dispatch a job for execution whose timer has expired.
 *
 * param[in] timer The timer to handle.
 */
static void timerCallback( TimerHandle_t xTimer );

/* @endcond */

/* ------------------------------------------------------------------------------ */

/* These functions have descriptions in the header file. */

void taskPoolCreateSystemTaskPool( void )
{
    BaseType_t running;
    uint8_t    x;

    /* Has the task pool already been started? */
    taskENTER_CRITICAL();
    running          = taskPool.running;
    taskPool.running = pdTRUE;
    taskEXIT_CRITICAL();

    if( running == pdFALSE )
    {
        /*
         * The schedule function and timer callbacks add jobs to this queue.
         * Workers read and execute jobs from this queue.
         */
        taskPool.dispatchQueue =
            xQueueCreateStatic( configTASKPOOL_DISPATCH_QUEUE_LENGTH,
                                sizeof( struct taskPoolJob * ),
                                taskPool.queueData,
                                &taskPool.queueBuffer );

        configASSERT( taskPool.dispatchQueue != NULL );

        /* Launch the worker task(s). */
        for( x = 0; x < ( UBaseType_t ) configTASKPOOL_NUMBER_OF_WORKERS; x++ )
        {
            /* a unique name for the task. */
            char taskName[]   = "worker.n";
            taskName[ sizeof( taskName ) - 2U ] = '0' + x;

            /* Coverity suggests adding const qualification to the local variable `task`.
             * There is no value in making the task handle variable const as it is defined
             * only for the purpose of assert checking.
             */
            /* coverity[misra_c_2012_rule_8_13_violation] */
            TaskHandle_t task =
                xTaskCreateStatic( taskPoolWorker,
                                   taskName,
                                   ( uint32_t ) STACK_WORDS,
                                   NULL,
                                   configTASKPOOL_WORKER_PRIORITY,
                                   &( taskPool.workerTaskStacks[ x ][ 0 ] ),
                                   &( taskPool.workerTaskTCBs[ x ] ) );

            configASSERT( task != NULL );

            /* Suppress unused local variable compiler warning. */
            ( void ) task;
        }
    }
}

/*-----------------------------------------------------------*/

void taskPoolInitializeJob( taskPoolRoutine_t userCallback,
                            void * userContext,
                            taskPoolJob_t * jobStorage )
{
    configASSERT( taskPool.running == pdTRUE );

    /* Parameter checking. */
    configASSERT( userCallback != NULL );
    configASSERT( jobStorage != NULL );

    /* Initialize the job within the user-provided storage instance. */
    jobStorage->userCallback = userCallback;
    jobStorage->userContext  = userContext;
    jobStorage->status       = TASKPOOL_JOB_STATUS_READY;

    increment( initialized );
}

/*-----------------------------------------------------------*/

BaseType_t taskPoolIsJobInitialised( taskPoolJob_t * job )
{
    return( job->status != TASKPOOL_JOB_STATUS_UNDEFINED );
}

/*-----------------------------------------------------------*/

taskPoolError_t taskPoolScheduleDeferred( taskPoolJob_t * job,
                                          uint32_t timeMs )
{
    taskPoolError_t status = TASKPOOL_GENERAL_FAILURE;
    BaseType_t      result;
    UBaseType_t     savedStatus;

    /*
     * Check that the timer task priority is higher than that of the calling task.
     * Reason: Deferred scheduling of a job requires starting the job's timer. To guarantee
     * that the timer has been started before this function returns, we have to wait for the
     * timer (service) task to process the timer start command that is enqueued by xTimerStart.
     * The enqueue operation within FreeRTOS contains a "yield" operation that will ensure
     * processing of the timer start command, IF the timer task has a higher priority than this
     * function's calling task.
     */
    configASSERT( uxTaskPriorityGet( xTaskGetCurrentTaskHandle() ) < configTIMER_TASK_PRIORITY );

    configASSERT( taskPool.running == pdTRUE );
    configASSERT( ( job != NULL ) && ( job->status != TASKPOOL_JOB_STATUS_UNDEFINED ) );

    /* This critical section complements synchronization with TryCancel function. */
    taskENTER_CRITICAL();
    savedStatus = job->status;

    if( job->status == TASKPOOL_JOB_STATUS_READY )
    {
        /* Prevent job from being cancelled (temporarily).*/
        job->status = TASKPOOL_JOB_STATUS_NOT_CANCELLABLE;
    }

    taskEXIT_CRITICAL();

    if( savedStatus != TASKPOOL_JOB_STATUS_READY )
    {
        /* Only a job in the ready state may be scheduled. */
        status = TASKPOOL_ILLEGAL_OPERATION;
        increment( schedule_illegal );
    }
    else
    {
        /* If not deferred, dispatch the job without starting the timer. */
        if( timeMs == 0UL )
        {
            /*
             * Update the job state before enqueueing the job to avoid data race
             * in case when job's callback re-uses the job memory for scheduling a new job.
             */
            job->status = TASKPOOL_JOB_STATUS_DISPATCHED;

            /*
             * Do not block on the enqueue operation as the job has been requested
             * to be executed immediately.
             */
            if( xQueueSendToBack( taskPool.dispatchQueue, &job, 0 ) == pdPASS )
            {
                status = TASKPOOL_SUCCESS;
                increment( direct_dispatch );
            }
            else
            {
                job->status = TASKPOOL_JOB_STATUS_CANCELLED;
                status      = TASKPOOL_FAILED_OPERATION;
                increment( direct_dispatch_failed );
            }
        }
        else
        {
            /* Software timer will manage the time delay for the deferred job. */
            job->timer  =
                xTimerCreateStatic( NULL,
                                    pdMS_TO_TICKS( timeMs ),
                                    pdFALSE,
                                    job,
                                    timerCallback,
                                    &job->timerStorage );

            configASSERT( job->timer != NULL );

            /*
             * Block on sending the timer start command to the timer command queue
             * to ensure that the job's timer is started before this function returns.
             * Reason: Blocking indefinitely on the call causes the timer task (of higher
             * priority ) to be executed which ensures that the timer start command has
             * been processed to start the job's timer.
             */
            result      = xTimerStart( job->timer, portMAX_DELAY );
            configASSERT( result == pdPASS );

            job->status = TASKPOOL_JOB_STATUS_DEFERRED;
            status      = TASKPOOL_SUCCESS;
            increment( timer_start );
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

taskPoolError_t taskPoolTryCancel( taskPoolJob_t * job )
{
    taskPoolError_t status = TASKPOOL_GENERAL_FAILURE;
    UBaseType_t     savedStatus;
    BaseType_t      result = pdFAIL;

    /*
     * Check that the timer task priority is higher than that of the calling task.
     * Reason: Cancelling a job requires cancellation of the job's associated timer,
     * and this function needs to wait for the timer (service) task to cancel the timer
     * before this function returns. The enqueue operation, that is part of the xTimerDelete
     * call, contains a "yield" operation that will ensure the timer (service) task runs,
     * only IF the timer task has a higher priority than this function's calling task.
     */
    configASSERT( uxTaskPriorityGet( xTaskGetCurrentTaskHandle() ) < configTIMER_TASK_PRIORITY );

    configASSERT( taskPool.running == pdTRUE );
    configASSERT( ( job != NULL ) && ( job->status != TASKPOOL_JOB_STATUS_UNDEFINED ) );

    /* This critical section complements the one in timerCallback() for synchronization. */
    taskENTER_CRITICAL();
    savedStatus = job->status;

    if( ( savedStatus == TASKPOOL_JOB_STATUS_READY ) ||
        ( savedStatus == TASKPOOL_JOB_STATUS_DEFERRED ) ||
        ( savedStatus == TASKPOOL_JOB_STATUS_CANCELLED ) )
    {
        job->status = TASKPOOL_JOB_STATUS_CANCELLED;
        status      = TASKPOOL_SUCCESS;
        increment( cancel );
    }
    else
    {
        status = TASKPOOL_ILLEGAL_OPERATION;
        increment( cancel_illegal );
    }

    taskEXIT_CRITICAL();

    if( savedStatus == TASKPOOL_JOB_STATUS_DEFERRED )
    {
        /*
         * Block on sending the delete command to the timer task's command queue
         * to ensure that the job's timer is either deleted OR the job is not dispatched
         * (if the job's timer has expired and has invoked the timer's callback).
         * Reason: Blocking indefinitely on the call causes the timer task (of higher
         * priority ) to be executed which ensures that the timer delete command has
         * been processed, and the job is not executed.
         */
        result = xTimerDelete( job->timer, portMAX_DELAY );
        configASSERT( result == pdTRUE );
    }

    return status;
}

/*-----------------------------------------------------------*/

const char * taskPoolStrError( taskPoolError_t status )
{
    const char * pMessage = NULL;

    switch( status )
    {
        case TASKPOOL_SUCCESS:
            pMessage = "SUCCESS";
            break;

        case TASKPOOL_ILLEGAL_OPERATION:
            pMessage = "OPERATION NOT ALLOWED";
            break;

        case TASKPOOL_FAILED_OPERATION:
            pMessage = "OPERATION FAILED";
            break;

        case TASKPOOL_GENERAL_FAILURE:
            pMessage = "GENERAL FAILURE";
            break;

        default:
            pMessage = "INVALID STATUS";
            break;
    }

    return pMessage;
}

/* ------------------------------------------------------------------------------ */

/*
 * The timer callback runs from the timer task at configTIMER_TASK_PRIORITY.
 * Both taskPoolTryCancel() and taskPoolScheduleDeferred() run at a lower priority,
 * as enforced by assert.  Being called by the timer, this function will run to
 * completion without being interleaved with the others.
 */
static void timerCallback( TimerHandle_t xTimer )
{
    struct taskPoolJob * job;

    increment( timer_callback );
    configASSERT( xTimer != NULL );

    job = ( struct taskPoolJob * ) pvTimerGetTimerID( xTimer );
    configASSERT( job != NULL );

    configASSERT( ( job->status == TASKPOOL_JOB_STATUS_READY ) ||
                  ( job->status == TASKPOOL_JOB_STATUS_DEFERRED ) ||
                  ( job->status == TASKPOOL_JOB_STATUS_CANCELLED ) );

    /*
     * Skip enqueue of a job that's been cancelled.
     */
    if( job->status != TASKPOOL_JOB_STATUS_CANCELLED )
    {
        /* No blocking time for the enqueue operation to avoid blocking operation on timer task. */
        if( xQueueSendToBack( taskPool.dispatchQueue, &job, 0 ) == pdPASS )
        {
            job->status = TASKPOOL_JOB_STATUS_DISPATCHED;
            increment( callback_dispatch );
        }
        else
        {
            /*
             * The queue must be full.  Re-try dispatching the job after some delay
             * by resetting the job's timer.
             */
            if( xTimerReset( job->timer, 0 ) == pdPASS )
            {
                job->status = TASKPOOL_JOB_STATUS_DEFERRED;
                increment( callback_reschedule );
            }
            else
            {
                job->status = TASKPOOL_JOB_STATUS_CANCELLED;
                increment( reschedule_failed );
            }
        }
    }
}

/*-----------------------------------------------------------*/

/* Coverity suggests adding const qualification to the parameter.
 * Suppress the violation as this function follows the signature of
 * the `TaskFunction_t` type required by `xTaskCreateStatic` function.
 */
/* coverity[misra_c_2012_rule_8_13_violation] */
static void taskPoolWorker( void * pContext )
{
    /*
     * Timer task is critical to the functioning of the task pool. Thus, we want to
     * prevent possibility of context switch from timer task during execution of the
     * timer callback by requiring task pool worker(s) to have lower priority than timer
     * task.
     */
    configASSERT( configTASKPOOL_WORKER_PRIORITY < configTIMER_TASK_PRIORITY );

    /* Suppress unused parameter compiler warning. */
    ( void ) pContext;

    for( ; ; )
    {
        struct taskPoolJob * job;
        BaseType_t           result;

        /* block until a job arrives */
        result      = xQueueReceive( taskPool.dispatchQueue, &job, portMAX_DELAY );
        configASSERT( result == pdTRUE );
        configASSERT( ( job != NULL ) && ( job->userCallback != NULL ) );

        job->status = TASKPOOL_JOB_STATUS_EXECUTING;

        /* The job may reuse job storage within the callback for a new job. */
        increment( job_started );
        job->userCallback( job, job->userContext );
        increment( job_done );
    }
}
