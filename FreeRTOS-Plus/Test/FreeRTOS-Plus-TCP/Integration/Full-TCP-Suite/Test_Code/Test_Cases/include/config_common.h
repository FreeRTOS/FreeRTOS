/*
 * FreeRTOS V202112.00
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
 *
 * http://aws.amazon.com/freertos
 * http://www.FreeRTOS.org
 */

/* This file contains default configuration settings for the tests on FreeRTOS. */

#ifndef IOT_CONFIG_COMMON_H_
#define IOT_CONFIG_COMMON_H_

/* FreeRTOS include. */
#include "FreeRTOS.h"

/* Credentials include. */
#include <aws_clientcredential.h>
#include <aws_clientcredential_keys.h>

/* Unity framework includes. */
#include "unity.h"

/* Use platform types on FreeRTOS. */
#include "platform/iot_platform_types_freertos.h"

/* SDK version. */
#define IOT_SDK_VERSION    "4.0.0"

/* This config file is for the tests. */
#ifndef IOT_BUILD_TESTS
    #define IOT_BUILD_TESTS    ( 1 )
#endif

#if IOT_BUILD_TESTS != 1
    #error "IOT_BUILD_TESTS must be 1 for this test project."
#endif

/* Unity on FreeRTOS does not provide malloc overrides. */
#define IOT_TEST_NO_MALLOC_OVERRIDES    ( 1 )

/* Supported network types.*/
#define AWSIOT_NETWORK_TYPE_NONE        0x00000000
#define AWSIOT_NETWORK_TYPE_WIFI        0x00000001
#define AWSIOT_NETWORK_TYPE_BLE         0x00000002

/* Logging puts function. */
#define IotLogging_Puts( str )    configPRINTF( ( "%s\r\n", str ) )

/* Enable asserts in libraries. */
#define IOT_METRICS_ENABLE_ASSERTS         ( 1 )
#define IOT_CONTAINERS_ENABLE_ASSERTS      ( 1 )
#define IOT_TASKPOOL_ENABLE_ASSERTS        ( 1 )
#define IOT_MQTT_ENABLE_ASSERTS            ( 1 )
#define AWS_IOT_SHADOW_ENABLE_ASSERTS      ( 1 )
#define AWS_IOT_DEFENDER_ENABLE_ASSERTS    ( 1 )
#define IOT_BLE_ENABLE_ASSERTS             ( 1 )

/* Assert functions. */
#define IotMetrics_Assert( expression )        if( ( expression ) == 0 ) TEST_FAIL_MESSAGE( "Assertion failure" )
#define IotContainers_Assert( expression )     if( ( expression ) == 0 ) TEST_FAIL_MESSAGE( "Assertion failure" )
#define IotTaskPool_Assert( expression )       if( ( expression ) == 0 ) TEST_FAIL_MESSAGE( "Assertion failure" )
#define IotMqtt_Assert( expression )           if( ( expression ) == 0 ) TEST_FAIL_MESSAGE( "Assertion failure" )
#define AwsIotShadow_Assert( expression )      if( ( expression ) == 0 ) TEST_FAIL_MESSAGE( "Assertion failure" )
#define AwsIotDefender_Assert( expression )    if( ( expression ) == 0 ) TEST_FAIL_MESSAGE( "Assertion failure" )
#define IotBle_Assert( expression )            if( ( expression ) == 0 ) TEST_FAIL_MESSAGE( "Assertion failure" )

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
#define IotTest_Malloc       pvPortMalloc
#define IotTest_Free         vPortFree


/* Memory allocation function configuration for the MQTT library. The MQTT library
 * will be affected by IOT_STATIC_MEMORY_ONLY. */
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

/* Require MQTT serializer overrides for the tests. */
#define IOT_MQTT_ENABLE_SERIALIZER_OVERRIDES    ( 1 )

/* Platform and SDK name for AWS MQTT metrics. Only used when AWS_IOT_MQTT_ENABLE_METRICS is 1. */
#define IOT_SDK_NAME                            "AmazonFreeRTOS"
#ifdef configPLATFORM_NAME
    #define IOT_PLATFORM_NAME                   configPLATFORM_NAME
#else
    #define IOT_PLATFORM_NAME                   "Unknown"
#endif

/* BLE_HAL test suites header file abstraction */
#define IOT_LINEAR_CONTAINERS             "iot_linear_containers.h"
#define IOT_THREADS                       "platform/iot_threads.h"
#define IOT_CLOCK                         "platform/iot_clock.h"
#define IOT_PLATFORM_TYPES                "types/iot_platform_types.h"
#define IOT_BT_HAL_MANAGER_ADAPTER_BLE    "bt_hal_manager_adapter_ble.h"
#define IOT_BT_HAL_MANAGER_ADAPTER        "bt_hal_manager.h"
#define IOT_BT_HAL_GATT_SERVER            "bt_hal_gatt_server.h"
#define IOT_BT_HAL_GATT_TYPES             "bt_hal_gatt_types.h"
#define IOT_UNITY_FIXTURE                 "unity_fixture.h"
#define IOT_UNITY                         "unity.h"
#define IOT_LOG                           "iot_logging_setup.h"

/* Cloud endpoint to which the device connects to. */
#define IOT_CLOUD_ENDPOINT                clientcredentialMQTT_BROKER_ENDPOINT

/* Certificate for the device.*/
#define IOT_DEVICE_CERTIFICATE            keyCLIENT_CERTIFICATE_PEM

/**
 * @brief Unique identifier used to recognize a device by the cloud.
 * This could be SHA-256 of the device certificate.
 */
extern const char * getDeviceIdentifier( void );
#define IOT_DEVICE_IDENTIFIER    getDeviceIdentifier()

/**
 * @brief Metrics emitted by the device.
 */
extern const char * getDeviceMetrics( void );
#define AWS_IOT_METRICS_USERNAME    getDeviceMetrics()

/**
 * @brief Length of the metrics emitted by device.
 */
extern uint16_t getDeviceMetricsLength( void );
#define AWS_IOT_METRICS_USERNAME_LENGTH     getDeviceMetricsLength()

/* Set Thing Name. */
#define AWS_IOT_TEST_SHADOW_THING_NAME      clientcredentialIOT_THING_NAME
#define AWS_IOT_TEST_DEFENDER_THING_NAME    clientcredentialIOT_THING_NAME

/* Configuration for defender demo: set format to CBOR. */
#define AWS_IOT_DEFENDER_FORMAT             AWS_IOT_DEFENDER_FORMAT_CBOR

/* Configuration for defender demo: use long tag for readable output. Please use short tag for the real application. */
#define AWS_IOT_DEFENDER_USE_LONG_TAG       ( 1 )

/* Define the data type of metrics connection id as same as Socket_t in aws_secure_socket.h */
#define IotMetricsConnectionId_t            void *

/* For compatibility with the FreeRTOS test framework, UnityPrint and similar
 * must be redefined. */
extern int snprintf( char *,
                     size_t,
                     const char *,
                     ... );
#define UnityPrint( X )          configPRINTF( ( X ) )
#define UnityPrintNumber( X )    { char number[ 12 ] = { 0 }; snprintf( number, 12, "%d", X ); configPRINTF( ( number ) ); }
#undef UNITY_PRINT_EOL
#define UNITY_PRINT_EOL()        configPRINTF( ( "\r\n" ) )

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

/* Use FreeRTOS Secure Sockets network for tests. */
#ifndef IOT_TEST_NETWORK_HEADER
    #define IOT_TEST_NETWORK_HEADER    "platform/iot_network_freertos.h"
#endif

/* All tests use a secured connection. */
#define IOT_TEST_SECURED_CONNECTION    ( 1 )

/* Allow the network interface to be chosen by at runtime. */
struct IotNetworkInterface;
extern const struct IotNetworkInterface * IotTestNetwork_GetNetworkInterface( void );
#define IOT_TEST_NETWORK_INTERFACE    IotTestNetwork_GetNetworkInterface()

/* Allow the network serializer to be chosen by at runtime. */
struct IotMqttSerializer;
extern const struct IotMqttSerializer * IotTestNetwork_GetSerializer( void );
#define IOT_TEST_MQTT_SERIALIZER                     IotTestNetwork_GetSerializer()

/* Retry the MQTT Connections in the MQTT System unit tests for all hardware
 * platforms supported in FreeRTOS.
 * Set this to the number of connection attempts for the MQTT tests.
 * If undefined, it should default to 1. */
#define IOT_TEST_MQTT_CONNECT_RETRY_COUNT            ( 3 )

/* AWS IoT Service limits only allow 1 connection per MQTT client ID per second.
 * Wait until 1100 ms have elapsed since the last connection. */
#define IOT_TEST_MQTT_CONNECT_INIT_RETRY_DELAY_MS    ( 1100 )

/* Forward declarations of network types used in the tests. */
typedef struct IotNetworkConnection    IotTestNetworkConnection_t;
typedef struct IotNetworkServerInfo    IotTestNetworkServerInfo_t;
typedef struct IotNetworkCredentials   IotTestNetworkCredentials_t;

/* Define test network initializers. */
#define IOT_TEST_NETWORK_CONNECTION_INITIALIZER     IOT_NETWORK_CONNECTION_AFR_INITIALIZER
#define IOT_TEST_NETWORK_SERVER_INFO_INITIALIZER    AWS_IOT_NETWORK_SERVER_INFO_AFR_INITIALIZER

/* Define the credentials initializer based on the server port. Use ALPN if on
 * 443, otherwise disable ALPN. */
#if clientcredentialMQTT_BROKER_PORT == 443
    #define IOT_TEST_NETWORK_CREDENTIALS_INITIALIZER    AWS_IOT_NETWORK_CREDENTIALS_AFR_INITIALIZER
#else
    #define IOT_TEST_NETWORK_CREDENTIALS_INITIALIZER           \
    {                                                          \
        .disableSni = false,                                   \
        .pAlpnProtos = NULL,                                   \
        .pRootCa = NULL,                                       \
        .pClientCert = keyCLIENT_CERTIFICATE_PEM,              \
        .pPrivateKey = keyCLIENT_PRIVATE_KEY_PEM,              \
        .rootCaSize = 0,                                       \
        .clientCertSize = sizeof( keyCLIENT_CERTIFICATE_PEM ), \
        .privateKeySize = sizeof( keyCLIENT_PRIVATE_KEY_PEM )  \
    }
#endif /* if clientcredentialMQTT_BROKER_PORT == 443 */

/* Network initialization and cleanup functions are not needed on FreeRTOS. */
#define IotTestNetwork_Init()    IOT_NETWORK_SUCCESS
#define IotTestNetwork_Cleanup()

#endif /* ifndef IOT_CONFIG_COMMON_H_ */
