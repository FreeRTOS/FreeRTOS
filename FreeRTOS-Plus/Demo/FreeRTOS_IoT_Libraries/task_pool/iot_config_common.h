/*
 * Amazon FreeRTOS V201906.00 Major
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
 *
 * http://aws.amazon.com/freertos
 * http://www.FreeRTOS.org
 */

/* This file contains default configuration settings for the demos on FreeRTOS. */

#ifndef IOT_CONFIG_COMMON_H_
#define IOT_CONFIG_COMMON_H_

/* FreeRTOS include. */
#include "FreeRTOS.h" //_RB_Makes common config file FreeRTOS specific

/* Use platform types on FreeRTOS. */
#include "platform/iot_platform_types_freertos.h" //_RB_Makes common config file FreeRTOS specific

/* SDK version. */
#define IOT_SDK_VERSION    "4.0.0"

/* This config file is for the demos; disable any test code. */
#define IOT_BUILD_TESTS    ( 0 )

/* Logging puts function. */
#define IotLogging_Puts( str )                 configPRINTF( ( "%s\r\n", str ) )

/* Enable asserts in libraries by default. */
#ifndef IOT_METRICS_ENABLE_ASSERTS
    #define IOT_METRICS_ENABLE_ASSERTS         ( 1 )
#endif
#ifndef IOT_CONTAINERS_ENABLE_ASSERTS
    #define IOT_CONTAINERS_ENABLE_ASSERTS      ( 1 )
#endif
#ifndef IOT_TASKPOOL_ENABLE_ASSERTS
    #define IOT_TASKPOOL_ENABLE_ASSERTS        ( 1 )
#endif
#ifndef IOT_MQTT_ENABLE_ASSERTS
    #define IOT_MQTT_ENABLE_ASSERTS            ( 1 )
#endif
#ifndef AWS_IOT_SHADOW_ENABLE_ASSERTS
    #define AWS_IOT_SHADOW_ENABLE_ASSERTS      ( 1 )
#endif
#ifndef AWS_IOT_DEFENDER_ENABLE_ASSERTS
    #define AWS_IOT_DEFENDER_ENABLE_ASSERTS    ( 1 )
#endif
#ifndef IOT_BLE_ENABLE_ASSERTS
    #define IOT_BLE_ENABLE_ASSERTS             ( 1 )
#endif

/* Assert functions. */
#define IotMetrics_Assert( expression )        configASSERT( expression )
#define IotContainers_Assert( expression )     configASSERT( expression )
#define IotTaskPool_Assert( expression )       configASSERT( expression )
#define IotMqtt_Assert( expression )           configASSERT( expression )
#define AwsIotShadow_Assert( expression )      configASSERT( expression )
#define AwsIotDefender_Assert( expression )    configASSERT( expression )
#define IotBle_Assert( expression )            configASSERT( expression )

/* Control the usage of dynamic memory allocation. */
#ifndef IOT_STATIC_MEMORY_ONLY
    #define IOT_STATIC_MEMORY_ONLY    ( 0 )
#endif

/* Memory allocation configuration. Note that these functions will not be affected
 * by IOT_STATIC_MEMORY_ONLY. */
#define IotNetwork_Malloc    pvPortMalloc
#define IotNetwork_Free      vPortFree
#define IotThreads_Malloc    pvPortMalloc
#define IotThreads_Free      vPortFree
#define IotLogging_Malloc    pvPortMalloc
#define IotLogging_Free      vPortFree
#define IotBle_Malloc        pvPortMalloc
#define IotBle_Free          vPortFree
/* #define IotLogging_StaticBufferSize */

/* Memory allocation function configuration for the MQTT and Defender library.
 * These libraries will be affected by IOT_STATIC_MEMORY_ONLY. */
#if IOT_STATIC_MEMORY_ONLY == 0
    #define IotMetrics_MallocTcpConnection       pvPortMalloc
    #define IotMetrics_FreeTcpConnection         vPortFree
    #define IotMetrics_MallocIpAddress           pvPortMalloc
    #define IotMetrics_FreeIpAddress             vPortFree

    #define IotTaskPool_MallocTaskPool           pvPortMalloc
    #define IotTaskPool_FreeTaskPool             vPortFree
    #define IotTaskPool_MallocJob                pvPortMalloc
    #define IotTaskPool_FreeJob                  vPortFree
    #define IotTaskPool_MallocTimerEvent         pvPortMalloc
    #define IotTaskPool_FreeTimerEvent           vPortFree

    #define IotMqtt_MallocConnection             pvPortMalloc
    #define IotMqtt_FreeConnection               vPortFree
    #define IotMqtt_MallocMessage                pvPortMalloc
    #define IotMqtt_FreeMessage                  vPortFree
    #define IotMqtt_MallocOperation              pvPortMalloc
    #define IotMqtt_FreeOperation                vPortFree
    #define IotMqtt_MallocSubscription           pvPortMalloc
    #define IotMqtt_FreeSubscription             vPortFree

    #define IotSerializer_MallocCborEncoder      pvPortMalloc
    #define IotSerializer_FreeCborEncoder        vPortFree
    #define IotSerializer_MallocCborParser       pvPortMalloc
    #define IotSerializer_FreeCborParser         vPortFree
    #define IotSerializer_MallocCborValue        pvPortMalloc
    #define IotSerializer_FreeCborValue          vPortFree
    #define IotSerializer_MallocDecoderObject    pvPortMalloc
    #define IotSerializer_FreeDecoderObject      vPortFree

    #define AwsIotShadow_MallocOperation         pvPortMalloc
    #define AwsIotShadow_FreeOperation           vPortFree
    #define AwsIotShadow_MallocString            pvPortMalloc
    #define AwsIotShadow_FreeString              vPortFree
    #define AwsIotShadow_MallocSubscription      pvPortMalloc
    #define AwsIotShadow_FreeSubscription        vPortFree

    #define AwsIotDefender_MallocReport          pvPortMalloc
    #define AwsIotDefender_FreeReport            vPortFree
    #define AwsIotDefender_MallocTopic           pvPortMalloc
    #define AwsIotDefender_FreeTopic             vPortFree
#endif /* if IOT_STATIC_MEMORY_ONLY == 0 */

/* Default platform thread stack size and priority. */
#ifndef IOT_THREAD_DEFAULT_STACK_SIZE
    #define IOT_THREAD_DEFAULT_STACK_SIZE    2048
#endif
#ifndef IOT_THREAD_DEFAULT_PRIORITY
    #define IOT_THREAD_DEFAULT_PRIORITY      tskIDLE_PRIORITY
#endif

/* Platform network configuration. */
#ifndef IOT_NETWORK_RECEIVE_TASK_PRIORITY
    #define IOT_NETWORK_RECEIVE_TASK_PRIORITY      ( tskIDLE_PRIORITY + 1 )
#endif
#ifndef IOT_NETWORK_RECEIVE_TASK_STACK_SIZE
    #define IOT_NETWORK_RECEIVE_TASK_STACK_SIZE    IOT_THREAD_DEFAULT_STACK_SIZE
#endif

/* Platform and SDK name for AWS IoT MQTT metrics. Only used when
 * AWS_IOT_MQTT_ENABLE_METRICS is 1. */
#define IOT_SDK_NAME             "AmazonFreeRTOS"
#ifdef configPLATFORM_NAME
    #define IOT_PLATFORM_NAME    configPLATFORM_NAME
#else
    #define IOT_PLATFORM_NAME    "Unknown"
#endif

/* Cloud endpoint to which the device connects to. */
#define IOT_CLOUD_ENDPOINT                    clientcredentialMQTT_BROKER_ENDPOINT

/**
 * @brief Unique identifier used to recognize a device by the cloud.
 * This could be SHA-256 of the device certificate.
 */
extern const char *getDeviceIdentifier( void );
#define IOT_DEVICE_IDENTIFIER                getDeviceIdentifier()

/**
 * @brief Metrics emitted by the device.
 */
extern const char *getDeviceMetrics( void );
#define AWS_IOT_METRICS_USERNAME     getDeviceMetrics()

/**
 * @brief Length of the metrics emitted by device.
 */
extern uint16_t getDeviceMetricsLength( void );
#define AWS_IOT_METRICS_USERNAME_LENGTH getDeviceMetricsLength()

/* Define the data type of metrics connection id as same as Socket_t in aws_secure_socket.h */
#define IotMetricsConnectionId_t            void *

/* Configuration for defender demo: set format to CBOR. */
#define AWS_IOT_DEFENDER_FORMAT             AWS_IOT_DEFENDER_FORMAT_CBOR

/* Configuration for defender demo: use long tag for readable output. Please use short tag for the real application. */
#define AWS_IOT_DEFENDER_USE_LONG_TAG       ( 1 )

#endif /* ifndef IOT_CONFIG_COMMON_H_ */
