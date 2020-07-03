/*
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
#define IOT_LOG_LEVEL_GLOBAL             IOT_LOG_NONE

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
#define IOT_LOG_LEVEL_PLATFORM           IOT_LOG_NONE

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
#define IOT_LOG_LEVEL_NETWORK            IOT_LOG_WARN

/**
 * @brief Set the log level of the MQTT library.
 *
 * Log messages from the MQTT library at or below this setting will be printed.
 *
 * Possible values: One of the Log levels.
 * Default value (if undefined): IOT_LOG_LEVEL_GLOBAL; if that is undefined,
 * then IOT_LOG_NONE.
 */
#define IOT_LOG_LEVEL_MQTT               IOT_LOG_WARN

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
#define IOT_CONTAINERS_ENABLE_ASSERTS    1

/**
 * @brief Enable/Disable asserts for the MQTT library.
 *
 * Set this to 1 to perform sanity checks when using the MQTT library.
 * Asserts are useful for debugging, but should be disabled in production code.
 * If this is set to 1, IotMqtt_Assert can be defined to set the assertion
 * function; otherwise, the standard library's assert function will be used.
 *
 * Possible values: 0 (asserts disabled) or 1 (asserts enabled)
 * Recommended values: 1 when debugging; 0 in production code.
 * Default value (if undefined): 0
 */
#define IOT_MQTT_ENABLE_ASSERTS          1

/**
 * @brief Enable/Disable anonymous metrics collection when using AWS IoT.
 */
#define AWS_IOT_MQTT_ENABLE_METRICS      0

/* Common settings for FreeRTOS; settings below this line generally do not need
 * to be changed. */

/* Logging puts function on FreeRTOS. */
#define IotLogging_Puts( str )    configPRINTF( ( "%s\r\n", str ) )

/* Assert functions on FreeRTOS. */
#define Iot_DefaultAssert    configASSERT

/* Memory allocation functions on FreeRTOS. */
#define Iot_DefaultMalloc    pvPortMalloc
#define Iot_DefaultFree      vPortFree

#endif /* ifndef IOT_CONFIG_H_ */
