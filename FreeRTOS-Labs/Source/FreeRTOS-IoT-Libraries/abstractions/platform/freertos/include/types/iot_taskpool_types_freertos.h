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
 * @file iot_taskpool_types.h
 * @brief Types of the task pool.
 */

#ifndef IOT_TASKPOOL_TYPES_H_
#define IOT_TASKPOOL_TYPES_H_

/* The config header is always included first. */
#include "iot_config.h"

/* Standard includes. */
#include <stdbool.h>
#include <stdint.h>

/* Platform types includes. */
#include "types/iot_platform_types.h"

/* Linear containers (lists and queues) include. */
#include "iot_linear_containers.h"

/*-------------------------- Task pool enumerated types --------------------------*/

/**
 * @ingroup taskpool_datatypes_enums
 * @brief Return codes of [task pool functions](@ref taskpool_functions).
 */
typedef enum IotTaskPoolError
{
    /**
     * @brief Task pool operation completed successfully.
     */
    IOT_TASKPOOL_SUCCESS = 0,

    /**
     * @brief Task pool operation failed because at least one parameter is invalid.
     */
    IOT_TASKPOOL_BAD_PARAMETER,

    /**
     * @brief Task pool operation failed because it is illegal.
     */
    IOT_TASKPOOL_ILLEGAL_OPERATION,

    /**
     * @brief Task pool operation failed because allocating memory failed.
     */
    IOT_TASKPOOL_NO_MEMORY,

    /**
     * @brief Task pool operation failed because of an invalid parameter.
     */
    IOT_TASKPOOL_SHUTDOWN_IN_PROGRESS,

    /**
     * @brief Task pool cancellation failed.
     */
    IOT_TASKPOOL_CANCEL_FAILED,

    /**
     * @brief Task pool operation general failure.
     */
    IOT_TASKPOOL_GENERAL_FAILURE,
} IotTaskPoolError_t;

/**
 * @enums{taskpool,Task pool library}
 */

/**
 * @ingroup taskpool_datatypes_enums
 * @brief Status codes of [task pool Job](@ref IotTaskPoolJob_t).
 *
 */
typedef enum IotTaskPoolJobStatus
{
    /**
     * @brief Job is ready to be scheduled.
     *
     */
    IOT_TASKPOOL_STATUS_READY = 0,

    /**
     * @brief Job has been queued for execution.
     *
     */
    IOT_TASKPOOL_STATUS_SCHEDULED,

    /**
     * @brief Job has been scheduled for deferred execution.
     *
     */
    IOT_TASKPOOL_STATUS_DEFERRED,

    /**
     * @brief Job is executing.
     *
     */
    IOT_TASKPOOL_STATUS_COMPLETED,

    /**
     * @brief Job has been canceled before executing.
     *
     */
    IOT_TASKPOOL_STATUS_CANCELED,

    /**
     * @brief Job status is undefined.
     *
     */
    IOT_TASKPOOL_STATUS_UNDEFINED,
} IotTaskPoolJobStatus_t;

/*------------------------- Task pool types and handles --------------------------*/

/**
 * @ingroup taskpool_datatypes_handles
 * @brief Opaque handle of a Task Pool instance.
 *
 * This type identifies a Task Pool instance, which is valid after a successful call
 * to @ref taskpool_function_createsystemtaskpool. 
 *
 * @initializer{IotTaskPool_t,IOT_TASKPOOL_INITIALIZER}
 */
typedef struct _taskPool * IotTaskPool_t;

/**
 * @ingroup taskpool_datatypes_handles
 * @brief A storage placeholder for TaskPool Jobs.
 *
 * This type provides a means to statically allocate an IoT TaskPool Job while
 * hiding internal details.
 */
typedef struct IotTaskPoolJobStorage IotTaskPoolJobStorage_t;

/**
 * @ingroup taskpool_datatypes_structs
 * @brief A storage placeholder for private data in the IotTaskPoolJobStorage struct.
 *
 * @warning This is a system-level data type that should not be modified or used directly in any application.
 * @warning This is a system-level data type that can and will change across different versions of the platform, with no regards for backward compatibility.
 */
struct PrivateMember
{
	IotLink_t dummy1;  /**< @brief Placeholder. */
	TickType_t dummy2; /**< @brief Placeholder. */
};

/**
 * @ingroup taskpool_datatypes_structs
 * @brief The job storage data structure provides the storage for a statically allocated Task Pool Job instance.
 *
 * @warning This is a system-level data type that should not be modified or used directly in any application.
 * @warning This is a system-level data type that can and will change across different versions of the platform, with no regards for backward compatibility.
 *
 */
struct IotTaskPoolJobStorage
{
    IotLink_t link;                 /**< @brief Placeholder. */
    void * dummy2;                  /**< @brief Placeholder. */
    void * dummy3;                  /**< @brief Placeholder. */
    IotTaskPoolJobStatus_t status;  /**< @brief Placeholder. */
    struct PrivateMember dummy6;    /**< @brief Placeholder. */
};

/**
 * @ingroup taskpool_datatypes_handles
 * @brief Opaque handle of a Task Pool Job.
 * 
 * This type identifies a Task Pool Job instance, which is valid after a successful call
 * to @ref taskpool_function_createjob.
 *
 * @initializer{IotTaskPoolJob_t,IOT_TASKPOOL_JOB_INITIALIZER}
 *
 */
typedef struct _taskPoolJob * IotTaskPoolJob_t;

/*------------------------- Task pool parameter structs --------------------------*/

/**
 * @ingroup taskpool_datatypes_functionpointers
 * @brief Callback type for a user callback.
 *
 * This type identifies the user callback signature to execute a task pool job. This callback will be invoked
 * by the task pool threads with the `pUserContext` parameter, as specified by the user when
 * calling @ref IotTaskPool_Schedule.
 *
 */
typedef void ( * IotTaskPoolRoutine_t )( IotTaskPool_t pTaskPool,
                                         IotTaskPoolJob_t pJob,
                                         void * pUserContext );

/**
 * @ingroup taskpool_datatypes_paramstructs
 * @brief Initialization information to create one task pool instance.
 *
 * @paramfor  @ref taskpool_function_createsystemtaskpool
 *
 * @initializer{IotTaskPoolInfo_t,IOT_TASKPOOL_INFO_INITIALIZER}
 */
typedef struct IotTaskPoolInfo
{
    /**
     * @brief Specifies the operating parameters for a task pool.
     *
     * @attention #IotTaskPoolInfo_t.minThreads <b>MUST</b> be at least 1.
     */

    uint32_t minThreads; /**< @brief Minimum number of threads in a task pool. These tasks will be statically allocated. */
    uint32_t maxThreads; /**< @brief Maximum number of threads in a task pool. This is fixed for the lifetime of the taskpool. */
    uint32_t stackSize;  /**< @brief Stack size for every task pool thread. The stack size for each thread is fixed after the task pool is created and cannot be changed. */
    int32_t priority;    /**< @brief priority for every task pool thread. The priority for each thread is fixed after the task pool is created and cannot be changed. */
} IotTaskPoolInfo_t;

/*------------------------- TASKPOOL defined constants --------------------------*/

/**
 * @constantspage{taskpool,task pool library}
 *
 * @section taskpool_constants_initializers Task pool Initializers
 * @brief Provides default values for initializing the data types of the task pool library.
 *
 * @snippet this define_taskpool_initializers
 *
 * All user-facing data types of the task pool library can be initialized using
 * one of the following.
 *
 * @warning Failure to initialize a task pool data type with the appropriate initializer
 * may result in a runtime error!
 * @note The initializers may change at any time in future versions, but their
 * names will remain the same.
 *
 * <b>Example</b>
 * @code{c}
 *
 * IotTaskPool_t * pTaskPool;
 *
 * const IotTaskPoolInfo_t tpInfo = IOT_TASKPOOL_INFO_INITIALIZER_LARGE;
 *
 * IotTaskPoolError_t error = IotTaskPool_Create( &tpInfo, &pTaskPool );
 *
 * // Use the task pool
 * // ...
 *
 * @endcode
 *
 */
/* @[define_taskpool_initializers] */
/** @brief Initializer for a small #IotTaskPoolInfo_t. */
#define IOT_TASKPOOL_INFO_INITIALIZER_SMALL     { .minThreads = 1, .maxThreads = 1, .stackSize = IOT_THREAD_DEFAULT_STACK_SIZE, .priority = IOT_THREAD_DEFAULT_PRIORITY }
/** @brief Initializer for a medium #IotTaskPoolInfo_t. */
#define IOT_TASKPOOL_INFO_INITIALIZER_MEDIUM    { .minThreads = 1, .maxThreads = 2, .stackSize = IOT_THREAD_DEFAULT_STACK_SIZE, .priority = IOT_THREAD_DEFAULT_PRIORITY }
/** @brief Initializer for a large #IotTaskPoolInfo_t. */
#define IOT_TASKPOOL_INFO_INITIALIZER_LARGE     { .minThreads = 2, .maxThreads = 3, .stackSize = IOT_THREAD_DEFAULT_STACK_SIZE, .priority = IOT_THREAD_DEFAULT_PRIORITY }
/** @brief Initializer for a very large #IotTaskPoolInfo_t. */
#define IOT_TASKPOOL_INFO_INITIALIZER_XLARGE    { .minThreads = 2, .maxThreads = 4, .stackSize = IOT_THREAD_DEFAULT_STACK_SIZE, .priority = IOT_THREAD_DEFAULT_PRIORITY }
/** @brief Initializer for a typical #IotTaskPoolInfo_t. */
#define IOT_TASKPOOL_INFO_INITIALIZER           IOT_TASKPOOL_INFO_INITIALIZER_MEDIUM
/** @brief Initializer for a #IotTaskPool_t. */
#define IOT_TASKPOOL_INITIALIZER                NULL
/** @brief Initializer for a #IotTaskPoolJobStorage_t. */
#define IOT_TASKPOOL_JOB_STORAGE_INITIALIZER    { { NULL, NULL }, NULL, NULL, 0, IOT_TASKPOOL_STATUS_UNDEFINED }
/** @brief Initializer for a #IotTaskPoolJob_t. */
#define IOT_TASKPOOL_JOB_INITIALIZER            NULL
/* @[define_taskpool_initializers] */

/**
 * @brief Flag for scheduling a job to execute immediately, even if the maximum number of threads in the
 * task pool was reached already.
 *
 * @warning This flag may cause the task pool to create a worker to serve the job immediately, and
 * therefore using this flag may incur in additional memory usage and potentially fail scheduling the job.
 */
#define IOT_TASKPOOL_JOB_HIGH_PRIORITY    ( ( uint32_t ) 0x00000001 )

/**
 * @brief Allows the use of the handle to the system task pool.
 *
 * @warning The system task pool handle is not valid unless @ref IotTaskPool_CreateSystemTaskPool is
 * called before the handle is used.
 */
#define IOT_SYSTEM_TASKPOOL               ( NULL )

#endif /* ifndef IOT_TASKPOOL_TYPES_H_ */
