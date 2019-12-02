/*
 * IoT Common V1.0.0
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
 * @file iot_taskpool.h
 * @brief User-facing functions of the task pool library.
 */

#ifndef IOT_TASKPOOL_H_
#define IOT_TASKPOOL_H_

/* The config header is always included first. */
#include "iot_config.h"

/* Standard includes. */
#include <stdbool.h>
#include <stdint.h>
#include <stddef.h>

/* Task pool types. */
#include "types/iot_taskpool_types_freertos.h"

/*------------------------- Task Pool library functions --------------------------*/

/**
 * @functionspage{taskpool,task pool library}
 * - @functionname{taskpool_function_createsystemtaskpool}
 * - @functionname{taskpool_function_createjob}
 * - @functionname{taskpool_function_schedule}
 * - @functionname{taskpool_function_scheduledeferred}
 * - @functionname{taskpool_function_getstatus}
 * - @functionname{taskpool_function_trycancel}
 * - @functionname{taskpool_function_getjobstoragefromhandle}
 * - @functionname{taskpool_function_strerror}
 */

/**
 * @functionpage{IotTaskPool_CreateSystemTaskPool,taskpool,createsystemtaskpool}
 * @functionpage{IotTaskPool_CreateJob,taskpool,createjob}
 * @functionpage{IotTaskPool_Schedule,taskpool,schedule}
 * @functionpage{IotTaskPool_ScheduleDeferred,taskpool,scheduledeferred}
 * @functionpage{IotTaskPool_GetStatus,taskpool,getstatus}
 * @functionpage{IotTaskPool_TryCancel,taskpool,trycancel}
 * @functionpage{IotTaskPool_GetJobStorageFromHandle,taskpool,getjobstoragefromhandle}
 * @functionpage{IotTaskPool_strerror,taskpool,strerror}
 */

/**
 * @brief Creates the one single instance of the system task pool.
 *
 * This function should be called once by the application to initialize the one single instance of the system task pool.
 * An application should initialize the system task pool early in the boot sequence, before initializing any other library
 * (e.g. MQTT) that uses the system task pool. An application should also initialize the system
 * task pool before posting any jobs. Early initialization is typically easy to accomplish by creating the system task pool
 * before the scheduler is started.
 *
 * The shortcut @ref IOT_SYSTEM_TASKPOOL contains the system task pool handle.
 *
 * @param[in] pInfo A pointer to the task pool initialization data.
 *
 * @return One of the following:
 * - #IOT_TASKPOOL_SUCCESS
 * - #IOT_TASKPOOL_BAD_PARAMETER
 * - #IOT_TASKPOOL_NO_MEMORY
 *
 * @warning This function should be called only once. Calling this function more that once will result in
 * undefined behavior.
 *
 */
/* @[declare_taskpool_createsystemtaskpool] */
IotTaskPoolError_t IotTaskPool_CreateSystemTaskPool( const IotTaskPoolInfo_t * const pInfo );
/* @[declare_taskpool_createsystemtaskpool] */

/**
 * @brief Creates a job for the task pool around a user-provided storage.
 *
 * @param[in] userCallback A user-specified callback for the job.
 * @param[in] pUserContext A user-specified context for the callback.
 * @param[in,out] pJobStorage The storage for the job data structure.
 * @param[out] pJob A pointer to an instance of @ref IotTaskPoolJob_t that will be initialized when this
 * function returns successfully. This handle can be used to inspect the job status with
 * @ref IotTaskPool_GetStatus or cancel the job with @ref IotTaskPool_TryCancel, etc....
 *
 * @return One of the following:
 * - #IOT_TASKPOOL_SUCCESS
 * - #IOT_TASKPOOL_BAD_PARAMETER
 *
 *
 */
/* @[declare_taskpool_createjob] */
IotTaskPoolError_t IotTaskPool_CreateJob( IotTaskPoolRoutine_t userCallback,
                                          void * pUserContext,
                                          IotTaskPoolJobStorage_t * const pJobStorage,
                                          IotTaskPoolJob_t * const pJob );
/* @[declare_taskpool_createjob] */

/**
 * @brief This function schedules a job created with @ref IotTaskPool_CreateJob against the task pool pointed to by `taskPool`.
 *
 * @param[in] taskPool A handle to an initialized taskpool.
 * @param[in] job A job to schedule for execution. This must be first initialized with a call to @ref IotTaskPool_CreateJob.
 * @param[in] flags Flags to be passed by the user, e.g. to identify the job as high priority by specifying #IOT_TASKPOOL_JOB_HIGH_PRIORITY.
 *
 * @return One of the following:
 * - #IOT_TASKPOOL_SUCCESS
 * - #IOT_TASKPOOL_BAD_PARAMETER
 * - #IOT_TASKPOOL_ILLEGAL_OPERATION
 * - #IOT_TASKPOOL_NO_MEMORY
 * - #IOT_TASKPOOL_SHUTDOWN_IN_PROGRESS
 *
 * @note This function will not allocate memory, so it is guaranteed to succeed if the parameters are correct and the task pool
 * was correctly initialized, and not yet destroyed.
 *
 * <b>Example</b>
 * @code{c}
 * // An example of a user context to pass to a callback through a task pool thread.
 * typedef struct JobUserContext
 * {
 *     uint32_t counter;
 * } JobUserContext_t;
 *
 * // An example of a user callback to invoke through a task pool thread.
 * static void ExecutionCb( IotTaskPool_t taskPool, IotTaskPoolJob_t job, void * context )
 * {
 *     ( void )taskPool;
 *     ( void )job;
 *
 *     JobUserContext_t * pUserContext = ( JobUserContext_t * )context;
 *
 *     pUserContext->counter++;
 * }
 *
 * void TaskPoolExample( )
 * {
 *     JobUserContext_t userContext = { 0 };
 *     IotTaskPoolJob_t job;
 *     IotTaskPool_t taskPool;
 *
 *     // Configure the task pool to hold one thread.
 *     // Provide proper stack size and priority per the application needs.
 *
 *     const IotTaskPoolInfo_t tpInfo = { .minThreads = 1, .maxThreads = 1, .stackSize = 512, .priority = 0 };
 *
 *     // Create a task pool.
 *     IotTaskPool_Create( &tpInfo, &taskPool );
 *
 *     // Statically allocate one job, schedule it.
 *     IotTaskPool_CreateJob( &ExecutionCb, &userContext, &job );
 *
 *     IotTaskPoolError_t errorSchedule = IotTaskPool_Schedule( taskPool, &job, 0 );
 *
 *     switch ( errorSchedule )
 *     {
 *     case IOT_TASKPOOL_SUCCESS:
 *         break;
 *     case IOT_TASKPOOL_BAD_PARAMETER:          // Invalid parameters, such as a NULL handle, can trigger this error.
 *     case IOT_TASKPOOL_ILLEGAL_OPERATION:      // Scheduling a job that was previously scheduled or destroyed could trigger this error.
 *     case IOT_TASKPOOL_NO_MEMORY:              // Scheduling a with flag #IOT_TASKPOOL_JOB_HIGH_PRIORITY could trigger this error.
 *     case IOT_TASKPOOL_SHUTDOWN_IN_PROGRESS:   // Scheduling a job after trying to destroy the task pool could trigger this error.
 *         // ASSERT
 *         break;
 *     default:
 *         // ASSERT
 *     }
 *
 *     //
 *     // ... Perform other operations ...
 *     //
 *
 *     IotTaskPool_Destroy( taskPool );
 * }
 * @endcode
 */
/* @[declare_taskpool_schedule] */
IotTaskPoolError_t IotTaskPool_Schedule( IotTaskPool_t taskPool,
                                         IotTaskPoolJob_t job,
                                         uint32_t flags );
/* @[declare_taskpool_schedule] */

/**
 * @brief This function schedules a job created with @ref IotTaskPool_CreateJob to be executed after a user-defined time interval.
 *
 * @param[in] taskPool A handle to an initialized taskpool.
 * @param[in] job A job to schedule for execution. This must be first initialized with a call to @ref IotTaskPool_CreateJob.
 * @param[in] timeMs The time in milliseconds to wait before scheduling the job.
 *
 * @return One of the following:
 * - #IOT_TASKPOOL_SUCCESS
 * - #IOT_TASKPOOL_BAD_PARAMETER
 * - #IOT_TASKPOOL_ILLEGAL_OPERATION
 * - #IOT_TASKPOOL_SHUTDOWN_IN_PROGRESS
 *
 *
 * @note This function will not allocate memory.
 *
 * @warning The `taskPool` used in this function should be the same
 * used to create the job pointed to by `job`, or the results will be undefined.
 *
 */
/* @[declare_taskpool_scheduledeferred] */
IotTaskPoolError_t IotTaskPool_ScheduleDeferred( IotTaskPool_t taskPool,
                                                 IotTaskPoolJob_t job,
                                                 uint32_t timeMs );
/* @[declare_taskpool_scheduledeferred] */

/**
 * @brief This function retrieves the current status of a job.
 *
 * @param[in] taskPool A handle to an initialized taskpool.
 * @param[in] job The job to cancel.
 * @param[out] pStatus The status of the job at the time of cancellation.
 *
 * @return One of the following:
 * - #IOT_TASKPOOL_SUCCESS
 * - #IOT_TASKPOOL_BAD_PARAMETER
 * - #IOT_TASKPOOL_SHUTDOWN_IN_PROGRESS
 *
 * @warning This function is not thread safe and the job status returned in `pStatus` may be invalid by the time
 * the calling thread has a chance to inspect it.
 */
/* @[declare_taskpool_getstatus] */
IotTaskPoolError_t IotTaskPool_GetStatus( IotTaskPool_t taskPool,
                                          IotTaskPoolJob_t job,
                                          IotTaskPoolJobStatus_t * const pStatus );
/* @[declare_taskpool_getstatus] */

/**
 * @brief This function tries to cancel a job that was previously scheduled with @ref IotTaskPool_Schedule.
 *
 * A job can be canceled only if it is not yet executing, i.e. if its status is
 * @ref IOT_TASKPOOL_STATUS_READY or @ref IOT_TASKPOOL_STATUS_SCHEDULED. Calling
 * @ref IotTaskPool_TryCancel on a job whose status is @ref IOT_TASKPOOL_STATUS_COMPLETED,
 * or #IOT_TASKPOOL_STATUS_CANCELED will yield a #IOT_TASKPOOL_CANCEL_FAILED return result.
 *
 * @param[in] taskPool A handle to an initialized taskpool.
 * @param[in] job The job to cancel.
 * @param[out] pStatus The status of the job at the time of cancellation.
 *
 * @return One of the following:
 * - #IOT_TASKPOOL_SUCCESS
 * - #IOT_TASKPOOL_BAD_PARAMETER
 * - #IOT_TASKPOOL_SHUTDOWN_IN_PROGRESS
 * - #IOT_TASKPOOL_CANCEL_FAILED
 *
 * @warning The `taskPool` used in this function should be the same
 * used to create the job pointed to by `job`, or the results will be undefined.
 *
 */
/* @[declare_taskpool_trycancel] */
IotTaskPoolError_t IotTaskPool_TryCancel( IotTaskPool_t taskPool,
                                          IotTaskPoolJob_t job,
                                          IotTaskPoolJobStatus_t * const pStatus );
/* @[declare_taskpool_trycancel] */

/**
 * @brief Returns a pointer to the job storage from an instance of a job handle
 * of type @ref IotTaskPoolJob_t. This function is guaranteed to succeed for a
 * valid job handle.
 *
 * @param[in] job The job handle.
 *
 * @return A pointer to the storage associated with the job handle `job`.
 *
 * @warning If the `job` handle used is invalid, the results will be undefined.
 */
/* @[declare_taskpool_getjobstoragefromhandle] */
IotTaskPoolJobStorage_t * IotTaskPool_GetJobStorageFromHandle( IotTaskPoolJob_t job );
/* @[declare_taskpool_getjobstoragefromhandle] */

/**
 * @brief Returns a string that describes an @ref IotTaskPoolError_t.
 *
 * Like the POSIX's `strerror`, this function returns a string describing a
 * return code. In this case, the return code is a task pool library error code,
 * `status`.
 *
 * The string returned by this function <b>MUST</b> be treated as read-only: any
 * attempt to modify its contents may result in a crash. Therefore, this function
 * is limited to usage in logging.
 *
 * @param[in] status The status to describe.
 *
 * @return A read-only string that describes `status`.
 *
 * @warning The string returned by this function must never be modified.
 */
/* @[declare_taskpool_strerror] */
const char * IotTaskPool_strerror( IotTaskPoolError_t status );
/* @[declare_taskpool_strerror] */

#endif /* ifndef IOT_TASKPOOL_H_ */
