/*
 * IoT Platform V1.1.0
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

/**
 * @file iot_metrics.h
 * @brief Functions for retrieving [Device Defender](@ref defender) metrics.
 *
 * The functions in this header are only required by Device Defender. They do not
 * need to be implemented if Device Defender is not used.
 */

#ifndef IOT_METRICS_H_
#define IOT_METRICS_H_

/* The config header is always included first. */
#include "iot_config.h"

/* Standard includes. */
#include <stdbool.h>

/* Linear containers (lists and queues) include. */
#include "iot_linear_containers.h"

/**
 * @functionspage{platform_metrics,platform metrics component,Metrics}
 * - @functionname{platform_metrics_function_init}
 * - @functionname{platform_metrics_function_cleanup}
 * - @functionname{platform_metrics_function_gettcpconnections}
 */

/**
 * @functionpage{IotMetrics_Init,platform_metrics,init}
 * @functionpage{IotMetrics_Cleanup,platform_metrics,cleanup}
 * @functionpage{IotMetrics_GetTcpConnections,platform_metrics,gettcpconnections}
 */

/**
 * @brief One-time initialization function for the platform metrics component.
 *
 * This function initializes the platform metrics component. <b>It must be called
 * once (and only once) before calling any other metrics or [Device Defender function]
 * (@ref defender_functions).</b> Calling this function more than once without first
 * calling @ref platform_metrics_function_cleanup may result in a crash.
 *
 * @return `true` is initialization succeeded; `false` otherwise.
 *
 * @warning No thread-safety guarantees are provided for this function.
 */
/* @[declare_platform_metrics_init] */
bool IotMetrics_Init( void );
/* @[declare_platform_metrics_init] */

/**
 * @brief One-time deinitialization function for the platform metrics component.
 *
 * This function frees resources taken in @ref platform_metrics_function_init.
 * No other metrics or [Device Defender functions](@ref defender_functions) may
 * be called unless @ref platform_metrics_function_init is called again.
 *
 * @warning No thread-safety guarantees are provided for this function.
 */
/* @[declare_platform_metrics_cleanup] */
void IotMetrics_Cleanup( void );
/* @[declare_platform_metrics_cleanup] */

/**
 * @brief Retrieve a list of active TCP connections from the system.
 *
 * The provided connections are reported by Device Defender.
 *
 * @param[in] pContext Context passed as the first parameter of `metricsCallback`.
 * @param[in] metricsCallback Called by this function to provide the list of TCP
 * connections. The list given by this function is should not be used after the
 * callback returns.
 */
/* @[declare_platform_metrics_gettcpconnections] */
void IotMetrics_GetTcpConnections( void * pContext,
                                   void ( * metricsCallback )( void *, const IotListDouble_t * ) );
/* @[declare_platform_metrics_gettcpconnections] */

#endif /* ifndef IOT_METRICS_H_ */
