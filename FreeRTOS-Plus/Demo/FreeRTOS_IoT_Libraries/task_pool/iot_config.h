/*
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
 */

/* This file contains configuration settings for the demos. */

#ifndef IOT_CONFIG_H_
#define IOT_CONFIG_H_

/* Use platform types on FreeRTOS. */
#include "FreeRTOS.h"
#include "platform/iot_platform_types_freertos.h" //_RB_Makes common config file FreeRTOS specific

/*
 * Set this to the number of recyclable tasks for the task pool to cache.
 *
 * Caching dynamically allocated tasks (recyclable tasks) helps the application
 * to limit the number of allocations at runtime. Caching recyclable tasks may
 * help making the application more responsive and predictable, by removing a
 * potential for memory allocation failures, but it may also have negative
 * repercussions on the amount of memory available at any given time. It is up
 * to the application developer to strike the correct balance these competing
 * needs. The task pool will cache when the application calling
 * IotTaskPool_RecycleJob. Any recycled tasks in excess of
 * IOT_TASKPOOL_JOBS_RECYCLE_LIMIT will be destroyed and its memory will be
 * release.
 *
 * Default value (if undefined): 8
 */
#define IOT_TASKPOOL_JOBS_RECYCLE_LIMIT 8

/*
 * Set this to 1 to perform sanity checks when using the task pool library.
 *
 * Asserts are useful for debugging, but should be disabled in production code.
 * If this is set to 1, IotTaskPool_Assert can be defined to set the assertion
 * function; otherwise, the standard library's assert function will be used.
 *
 * Possible values: 0 (asserts disabled) or 1 (asserts enabled)
 * Recommended values: 1 when debugging; 0 in production code.
 * Default value (if undefined): 0
 */
#define IOT_TASKPOOL_ENABLE_ASSERTS 1

/*
 * The full IoT Task Pool Library has many use cases, including Linux
 * development.  Typical FreeRTOS use cases do not require the full
 * functionality so an optimised implementation is provided specifically for use
 * with FreeRTOS.  The optimised version has a fixed number of tasks in the
 * pool, each of which uses statically allocated memory to ensure creation of
 * the pool is guaranteed (it does not run out of heap space).
 * IOT_TASKPOOL_NUMBER_OF_WORKERS sets the number of tasks in the pool.
 */
#define IOT_TASKPOOL_NUMBER_OF_WORKERS               3

/*
 * Set the log level of the task pool library.
 *
 * Log messages from the task pool library at or below this setting will be
 * printed.
 *
 * Possible values: One of the Log levels.
 * Default value (if undefined): IOT_LOG_LEVEL_GLOBAL; if that is undefined,
 * then IOT_LOG_NONE.
 */
#define IOT_LOG_LEVEL_TASKPOOL IOT_LOG_INFO


/**
 * @brief The stack size (in bytes) for each worker task in the task pool.
 * 
 * The minimal version of the of task pool library only supports one task pool
 * and the configuration of each worker task fixed at the compile time.
 */
#define IOT_TASKPOOL_WORKER_STACK_SIZE_BYTES        2048

/* Include the common configuration file for FreeRTOS. */
#include "iot_config_common.h"

#endif /* ifndef IOT_CONFIG_H_ */
