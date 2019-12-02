/*
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

/* This file contains configuration settings for the demos. */

#ifndef IOT_CONFIG_H_
#define IOT_CONFIG_H_

/* Configure the IoT Libraries for FreeRTOS by including the FreeRTOS header and
 * the FreeRTOS platform types. */
#include "FreeRTOS.h"
#include "platform/iot_platform_types_freertos.h"

/**
 * @brief Set a global default for log levels.
 *
 * This setting is overridden by log level settings of specific libraries.
 * Undefined library-specific log levels will default to this value.
 *
 * Possible values: One of the Log levels.
 * Default value (if undefined): IOT_LOG_NONE.
 */
#define IOT_LOG_LEVEL_GLOBAL                    IOT_LOG_NONE

/**
 * @brief Set the log level of the platform libraries except the network
 * component.
 *
 * Log messages from the platform libraries at or below this setting
 * will be printed. As the network component is more verbose, its logging
 * is controlled by its own setting, IOT_LOG_LEVEL_NETWORK.
 *
 * Possible values: One of the Log levels.
 * Default value (if undefined): IOT_LOG_LEVEL_GLOBAL; if that is undefined,
 * then IOT_LOG_NONE.
 */
#define IOT_LOG_LEVEL_PLATFORM                  IOT_LOG_NONE

/**
 * @brief Set the log level of the platform network library.
 *
 * Log messages from the platform network library at or below this setting
 * will be printed.
 *
 * Possible values: One of the Log levels.
 * Default value (if undefined): IOT_LOG_LEVEL_GLOBAL; if that is undefined,
 * then IOT_LOG_NONE.
 */
#define IOT_LOG_LEVEL_NETWORK                   IOT_LOG_WARN

/*
 * @brief Set the log level of the task pool library.
 *
 * Log messages from the task pool library at or below this setting will be
 * printed.
 *
 * Possible values: One of the Log levels.
 * Default value (if undefined): IOT_LOG_LEVEL_GLOBAL; if that is undefined,
 * then IOT_LOG_NONE.
 */
#define IOT_LOG_LEVEL_TASKPOOL                  IOT_LOG_WARN

/**
 * @brief Set the log level of the HTTPS Client library.
 *
 * Log messages from the HTTPS Client library at or below this setting will be printed.
 *
 * Possible values: One of the Log levels.
 * Default value (if undefined): IOT_LOG_LEVEL_GLOBAL; if that is undefined,
 * then IOT_LOG_NONE.
 */
#define IOT_LOG_LEVEL_HTTPS                     IOT_LOG_WARN

/**
 * @brief Enable/Disable asserts for the task pool library.
 *
 * Set this to 1 to perform sanity checks when using the task pool library.
 * Asserts are useful for debugging, but should be disabled in production code.
 * If this is set to 1, IotTaskPool_Assert can be defined to set the assertion
 * function; otherwise, the standard library's assert function will be used.
 *
 * Possible values: 0 (asserts disabled) or 1 (asserts enabled)
 * Recommended values: 1 when debugging; 0 in production code.
 * Default value (if undefined): 0
 */
#define IOT_TASKPOOL_ENABLE_ASSERTS             1

/**
 * @brief The number of worker tasks in the task pool.
 *
 * The full IoT Task Pool Library has many use cases, including Linux
 * development. Typical FreeRTOS use cases do not require the full
 * functionality so an optimized implementation is provided specifically for use
 * with FreeRTOS. The optimized version has a fixed number of tasks in the
 * task pool, each of which uses statically allocated memory to ensure creation
 * of the task pool is guaranteed (it does not run out of heap space).
 */
#define IOT_TASKPOOL_NUMBER_OF_WORKERS          1

/**
 * @brief The stack size (in bytes) for each worker task in the task pool.
 *
 * The minimal version of the of task pool library only supports one task pool
 * and the configuration of each worker task fixed at the compile time.
 */
#define IOT_TASKPOOL_WORKER_STACK_SIZE_BYTES    2048

/**
 * @brief Enable/Disable asserts for the linear containers library.
 *
 * Set this to 1 to perform sanity checks when using the linear containers library.
 * Asserts are useful for debugging, but should be disabled in production code.
 * If this is set to 1, IotContainers_Assert can be defined to set the assertion
 * function; otherwise, the standard library's assert function will be used.
 *
 * Possible values: 0 (asserts disabled) or 1 (asserts enabled)
 * Recommended values: 1 when debugging; 0 in production code.
 * Default value (if undefined): 0
 */
#define IOT_CONTAINERS_ENABLE_ASSERTS           1

/* Common settings for FreeRTOS; settings below this line generally do not need
 * to be changed. */

/* Logging puts function on FreeRTOS. */
#define IotLogging_Puts( str )                configPRINTF( ( "%s\r\n", str ) )

/* Assert functions on FreeRTOS. */
#define IotContainers_Assert( expression )    configASSERT( expression )
#define IotTaskPool_Assert( expression )      configASSERT( expression )

/* Memory allocation functions on FreeRTOS. */
#define IotThreads_Malloc               pvPortMalloc
#define IotThreads_Free                 vPortFree

#define IotLogging_Malloc               pvPortMalloc
#define IotLogging_Free                 vPortFree

#define IotTaskPool_MallocTaskPool      pvPortMalloc
#define IotTaskPool_FreeTaskPool        vPortFree
#define IotTaskPool_MallocJob           pvPortMalloc
#define IotTaskPool_FreeJob             vPortFree
#define IotTaskPool_MallocTimerEvent    pvPortMalloc
#define IotTaskPool_FreeTimerEvent      vPortFree

#endif /* ifndef IOT_CONFIG_H_ */
