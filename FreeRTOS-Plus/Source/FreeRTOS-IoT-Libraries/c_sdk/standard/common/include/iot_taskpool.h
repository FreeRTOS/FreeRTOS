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
#include "types/iot_taskpool_types.h"

/*------------------------- Task Pool library functions --------------------------*/

/**
 * @functionspage{taskpool,task pool library}
 * - @functionname{taskpool_function_createsystemtaskpool}
 * - @functionname{taskpool_function_getsystemtaskpool}
 * - @functionname{taskpool_function_create}
 * - @functionname{taskpool_function_destroy}
 * - @functionname{taskpool_function_setmaxthreads}
 * - @functionname{taskpool_function_createjob}
 * - @functionname{taskpool_function_createrecyclablejob}
 * - @functionname{taskpool_function_destroyrecyclablejob}
 * - @functionname{taskpool_function_recyclejob}
 * - @functionname{taskpool_function_schedule}
 * - @functionname{taskpool_function_scheduledeferred}
 * - @functionname{taskpool_function_getstatus}
 * - @functionname{taskpool_function_trycancel}
 * - @functionname{taskpool_function_getjobstoragefromhandle}
 * - @functionname{taskpool_function_strerror}
 */

/**
 * @functionpage{IotTaskPool_CreateSystemTaskPool,taskpool,createsystemtaskpool}
 * @functionpage{IotTaskPool_GetSystemTaskPool,taskpool,getsystemtaskpool}
 * @functionpage{IotTaskPool_Create,taskpool,create}
 * @functionpage{IotTaskPool_Destroy,taskpool,destroy}
 * @functionpage{IotTaskPool_SetMaxThreads,taskpool,setmaxthreads}
 * @functionpage{IotTaskPool_CreateJob,taskpool,createjob}
 * @functionpage{IotTaskPool_CreateRecyclableJob,taskpool,createrecyclablejob}
 * @functionpage{IotTaskPool_DestroyRecyclableJob,taskpool,destroyrecyclablejob}
 * @functionpage{IotTaskPool_RecycleJob,taskpool,recyclejob}
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
 * and before posting any jobs. Early initialization it typically easy to accomplish by creating the system task pool
 * before starting the scheduler.
 *
 * This function does not allocate memory to hold the task pool data structures and state, but it
 * may allocate memory to hold the dependent entities and data structures, e.g. the threads of the task
 * pool. The system task pool handle is recoverable for later use by calling @ref IotTaskPool_GetSystemTaskPool or
 * the shortcut @ref IOT_SYSTEM_TASKPOOL.
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
 * @brief Retrieves the one and only instance of a system task pool
 *
 * This function retrieves the system task pool created with @ref IotTaskPool_CreateSystemTaskPool, and it is functionally
 * equivalent to using the shortcut @ref IOT_SYSTEM_TASKPOOL.
 *
 * @return The system task pool handle.
 *
 * @warning This function should be called after creating the system task pool with @ref IotTaskPool_CreateSystemTaskPool.
 * Calling this function before creating the system task pool may return a pointer to an uninitialized task pool, NULL, or otherwise
 * fail with undefined behaviour.
 *
 */
/* @[declare_taskpool_getsystemtaskpool] */
IotTaskPool_t IotTaskPool_GetSystemTaskPool( void );
/* @[declare_taskpool_getsystemtaskpool] */

/**
 * @brief Creates one instance of a task pool.
 *
 * This function should be called by the user to initialize one instance of a task
 * pool. The task pool instance will be created around the storage pointed to by the `pTaskPool`
 * parameter. This function will create the minimum number of threads requested by the user
 * through an instance of the #IotTaskPoolInfo_t type specified with the `pInfo` parameter.
 * This function does not allocate memory to hold the task pool data structures and state, but it
 * may allocates memory to hold the dependent data structures, e.g. the threads of the task
 * pool.
 *
 * @param[in] pInfo A pointer to the task pool initialization data.
 * @param[out] pTaskPool A pointer to the task pool handle to be used after initialization.
 * The pointer `pTaskPool` will hold a valid handle only if (@ref IotTaskPool_Create)
 * completes successfully.
 *
 * @return One of the following:
 * - #IOT_TASKPOOL_SUCCESS
 * - #IOT_TASKPOOL_BAD_PARAMETER
 * - #IOT_TASKPOOL_NO_MEMORY
 *
 */
/* @[declare_taskpool_create] */
IotTaskPoolError_t IotTaskPool_Create( const IotTaskPoolInfo_t * const pInfo,
                                       IotTaskPool_t * const pTaskPool );
/* @[declare_taskpool_create] */

/**
 * @brief Destroys a task pool instance and collects all memory associated with a task pool and its
 * satellite data structures.
 *
 * This function should be called to destroy one instance of a task pool previously created with a call
 * to @ref IotTaskPool_Create or @ref IotTaskPool_CreateSystemTaskPool.
 * Calling this fuction release all underlying resources. After calling this function, any job scheduled but not yet executed
 * will be canceled and destroyed.
 * The `taskPool` instance will no longer be valid after this function returns.
 *
 * @param[in] taskPool A handle to the task pool, e.g. as returned by a call to @ref IotTaskPool_Create or
 * @ref IotTaskPool_CreateSystemTaskPool. The `taskPool` instance will no longer be valid after this function returns.
 *
 * @return One of the following:
 * - #IOT_TASKPOOL_SUCCESS
 * - #IOT_TASKPOOL_BAD_PARAMETER
 *
 */
/* @[declare_taskpool_destroy] */
IotTaskPoolError_t IotTaskPool_Destroy( IotTaskPool_t taskPool );
/* @[declare_taskpool_destroy] */

/**
 * @brief Sets the maximum number of threads for one instance of a task pool.
 *
 * This function sets the maximum number of threads for the task pool
 * pointed to by `taskPool`.
 *
 * If the number of currently active threads in the task pool is greater than `maxThreads`, this
 * function causes the task pool to shrink the number of active threads.
 *
 * @param[in] taskPool A handle to the task pool that must have been previously initialized with
 * a call to @ref IotTaskPool_Create or @ref IotTaskPool_CreateSystemTaskPool.
 * @param[in] maxThreads The maximum number of threads for the task pool.
 *
 * @return One of the following:
 * - #IOT_TASKPOOL_SUCCESS
 * - #IOT_TASKPOOL_BAD_PARAMETER
 * - #IOT_TASKPOOL_SHUTDOWN_IN_PROGRESS
 *
 */
/* @[declare_taskpool_setmaxthreads] */
IotTaskPoolError_t IotTaskPool_SetMaxThreads( IotTaskPool_t taskPool,
                                              uint32_t maxThreads );
/* @[declare_taskpool_setmaxthreads] */

/**
 * @brief Creates a job for the task pool around a user-provided storage.
 *
 * This function may allocate memory to hold the state for a job.
 *
 * @param[in] userCallback A user-specified callback for the job.
 * @param[in] pUserContext A user-specified context for the callback.
 * @param[in] pJobStorage The storage for the job data structure.
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
 * brief Creates a job for the task pool by allocating the job dynamically.
 *
 * A recyclable job does not need to be allocated twice, but it can rather be reused through
 * subsequent calls to @ref IotTaskPool_CreateRecyclableJob.
 *
 * @param[in] taskPool A handle to the task pool for which to create a recyclable job.
 * @param[in] userCallback A user-specified callback for the job.
 * @param[in] pUserContext A user-specified context for the callback.
 * @param[out] pJob A pointer to an instance of @ref IotTaskPoolJob_t that will be initialized when this
 * function returns successfully. This handle can be used to inspect the job status with
 * @ref IotTaskPool_GetStatus or cancel the job with @ref IotTaskPool_TryCancel, etc....
 *
 * @return One of the following:
 * - #IOT_TASKPOOL_SUCCESS
 * - #IOT_TASKPOOL_BAD_PARAMETER
 * - #IOT_TASKPOOL_NO_MEMORY
 * - #IOT_TASKPOOL_SHUTDOWN_IN_PROGRESS
 *
 * @note This function will not allocate memory. //_RB_ Incorrect comment.
 *
 * @warning A recyclable job should be recycled with a call to @ref IotTaskPool_RecycleJob rather than destroyed.
 *
 */
/* @[declare_taskpool_createrecyclablejob] */
IotTaskPoolError_t IotTaskPool_CreateRecyclableJob( IotTaskPool_t taskPool,
                                                    IotTaskPoolRoutine_t userCallback,
                                                    void * pUserContext,
                                                    IotTaskPoolJob_t * const pJob );
/* @[declare_taskpool_createrecyclablejob] */

/**
 * @brief This function un-initializes a job.
 *
 * This function will destroy a job created with @ref IotTaskPool_CreateRecyclableJob.
 * A job should not be destroyed twice. A job that was previously scheduled but has not completed yet should not be destroyed,
 * but rather the application should attempt to cancel it first by calling @ref IotTaskPool_TryCancel.
 * An attempt to destroy a job that was scheduled but not yet executed or canceled, may result in a
 * @ref IOT_TASKPOOL_ILLEGAL_OPERATION error.
 *
 * @param[in] taskPool A handle to the task pool, e.g. as returned by a call to @ref IotTaskPool_Create or @ref IotTaskPool_CreateSystemTaskPool.
 * @param[in] job A handle to a job that was create with a call to @ref IotTaskPool_CreateJob.
 *
 * @return One of the following:
 * - #IOT_TASKPOOL_SUCCESS
 * - #IOT_TASKPOOL_BAD_PARAMETER
 * - #IOT_TASKPOOL_ILLEGAL_OPERATION
 * - #IOT_TASKPOOL_SHUTDOWN_IN_PROGRESS
 *
 * @warning The task pool will try and prevent destroying jobs that are currently queued for execution, but does
 * not enforce strict ordering of operations. It is up to the user to make sure @ref IotTaskPool_DestroyRecyclableJob is not called
 * our of order.
 *
 * @warning Calling this function on job that was not previously created with @ref IotTaskPool_CreateRecyclableJob
 * will result in a @ref IOT_TASKPOOL_ILLEGAL_OPERATION error.
 *
 */
/* @[declare_taskpool_destroyrecyclablejob] */
IotTaskPoolError_t IotTaskPool_DestroyRecyclableJob( IotTaskPool_t taskPool,
                                                     IotTaskPoolJob_t job );
/* @[declare_taskpool_destroyrecyclablejob] */

/**
 * @brief Recycles a job into the task pool job cache.
 *
 * This function will try and recycle the job into the task pool cache. If the cache is full,
 * the job memory is destroyed as if the user called @ref IotTaskPool_DestroyRecyclableJob. The job should be recycled into
 * the task pool instance from where it was allocated.
 * Failure to do so will yield undefined results. A job should not be recycled twice. A job
 * that was previously scheduled but not completed or canceled cannot be safely recycled. An attempt to do so will result
 * in an @ref IOT_TASKPOOL_ILLEGAL_OPERATION error.
 *
 * @param[in] taskPool A handle to the task pool, e.g. as returned by a call to @ref IotTaskPool_Create.
 * @param[out] job A pointer to a job that was create with a call to @ref IotTaskPool_CreateJob.
 *
 * @return One of the following:
 * - #IOT_TASKPOOL_SUCCESS
 * - #IOT_TASKPOOL_BAD_PARAMETER
 * - #IOT_TASKPOOL_ILLEGAL_OPERATION
 * - #IOT_TASKPOOL_SHUTDOWN_IN_PROGRESS
 *
 * @warning The `taskPool` used in this function should be the same
 * used to create the job pointed to by `job`, or the results will be undefined.
 *
 * @warning Attempting to call this function on a statically allocated job will result in @ref IOT_TASKPOOL_ILLEGAL_OPERATION
 * error.
 *
 * @warning This function should be used to recycle a job in the task pool cache when after the job executed.
 * Failing to call either this function or @ref IotTaskPool_DestroyRecyclableJob will result is a memory leak. Statically
 * allocated jobs do not need to be recycled or destroyed.
 *
 */
/* @[declare_taskpool_recyclejob] */
IotTaskPoolError_t IotTaskPool_RecycleJob( IotTaskPool_t taskPool,
                                           IotTaskPoolJob_t job );
/* @[declare_taskpool_recyclejob] */

/**
 * @brief This function schedules a job created with @ref IotTaskPool_CreateJob or @ref IotTaskPool_CreateRecyclableJob
 * against the task pool pointed to by `taskPool`.
 *
 * See @ref taskpool_design for a description of the jobs lifetime and interaction with the threads used in the task pool
 * library.
 *
 * @param[in] taskPool A handle to the task pool that must have been previously initialized with.
 * a call to @ref IotTaskPool_Create.
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
 *
 * @note This function will not allocate memory, so it is guaranteed to succeed if the paramters are correct and the task pool
 * was correctly initialized, and not yet destroyed.
 *
 * @warning The `taskPool` used in this function should be the same used to create the job pointed to by `job`, or the
 * results will be undefined.
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
 *     // Configure the task pool to hold at least two threads and three at the maximum.
 *     // Provide proper stack size and priority per the application needs.
 *
 *     const IotTaskPoolInfo_t tpInfo = { .minThreads = 2, .maxThreads = 3, .stackSize = 512, .priority = 0 };
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
 * @brief This function schedules a job created with @ref IotTaskPool_CreateJob against the task pool
 * pointed to by `taskPool` to be executed after a user-defined time interval.
 *
 * See @ref taskpool_design for a description of the jobs lifetime and interaction with the threads used in the task pool
 * library.
 *
 * @param[in] taskPool A handle to the task pool that must have been previously initialized with.
 * a call to @ref IotTaskPool_Create.
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
 * @param[in] taskPool A handle to the task pool that must have been previously initialized with
 * a call to @ref IotTaskPool_Create or @ref IotTaskPool_CreateSystemTaskPool.
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
 * @param[in] taskPool A handle to the task pool that must have been previously initialized with
 * a call to @ref IotTaskPool_Create.
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

/**
 * @brief The maximum number of task pools to be created when using
 * a memory pool.
 */
#ifndef IOT_TASKPOOLS
#define IOT_TASKPOOLS                          ( 4 )
#endif

/**
 * @brief The maximum number of jobs to cache.
 */
#ifndef IOT_TASKPOOL_JOBS_RECYCLE_LIMIT
    #define IOT_TASKPOOL_JOBS_RECYCLE_LIMIT    ( 8UL )
#endif

/**
 * @brief The maximum timeout in milliseconds to wait for a job to be scheduled before waking up a worker thread.
 * A worker thread that wakes up as a result of a timeout may exit to allow the task pool to fold back to its
 * minimum number of threads.
 */
#ifndef IOT_TASKPOOL_JOB_WAIT_TIMEOUT_MS
    #define IOT_TASKPOOL_JOB_WAIT_TIMEOUT_MS    ( 60 * 1000UL )
#endif

#endif /* ifndef IOT_TASKPOOL_H_ */
