/*
 * IoT Platform V1.1.0
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
 * @file iot_platform_types.h
 * @brief Types of the platform layer.
 */

#ifndef IOT_PLATFORM_TYPES_H_
#define IOT_PLATFORM_TYPES_H_

/* The config header is always included first. */
#include "iot_config.h"

/* Linear containers (lists and queues) include for metrics types. */
#include "iot_linear_containers.h"

/*------------------------- Thread management types -------------------------*/

/**
 * @brief Placeholder value that should cause implementations of
 * @ref platform_threads_function_createdetachedthread to ignore the priority argument.
 */
#define IOT_THREAD_IGNORE_PRIORITY      ( -1 )

/**
 * @brief Placeholder value that should cause implementations of
 * @ref platform_threads_function_createdetachedthread to ignore the stack size argument.
 */
#define IOT_THREAD_IGNORE_STACK_SIZE    ( 0 )

/**
 * @brief A value representing the system default for new thread priority.
 */
#ifndef IOT_THREAD_DEFAULT_PRIORITY
    #define IOT_THREAD_DEFAULT_PRIORITY    IOT_THREAD_IGNORE_PRIORITY
#endif

/**
 * @brief A value representhing the system default for new thread stack size.
 */
#ifndef IOT_THREAD_DEFAULT_STACK_SIZE
    #define IOT_THREAD_DEFAULT_STACK_SIZE    IOT_THREAD_IGNORE_STACK_SIZE
#endif

/**
 * @ingroup platform_datatypes_handles
 * @brief The type used to represent mutexes, configured with the type
 * `_IotSystemMutex_t`.
 *
 * For the provided ports, `_IotSystemMutex_t` will be automatically configured.
 * For other ports, `_IotSystemMutex_t` should be set in `iot_config.h`.
 *
 * Mutexes should only be released by the threads that take them.
 *
 * <b>Example</b> <br>
 * To change the type of #IotMutex_t to `long`:
 * @code{c}
 * typedef long _IotSystemMutex_t;
 * #include "iot_threads.h"
 * @endcode
 */
typedef _IotSystemMutex_t       IotMutex_t;

/**
 * @ingroup platform_datatypes_handles
 * @brief The type used to represent semaphores, configured with the type
 * `_IotSystemSemaphore_t`.
 *
 * For the provided ports, `_IotSystemSemaphore_t` will be automatically configured.
 * For other ports, `_IotSystemSemaphore_t` should be set in `iot_config.h`.
 *
 * Semaphores must be counting, and any thread may take (wait on) or release
 * (post to) a semaphore.
 *
 * <b>Example</b> <br>
 * To change the type of #IotSemaphore_t to `long`:
 * @code{c}
 * typedef long _IotSystemSemaphore_t;
 * #include "iot_threads.h"
 * @endcode
 */
typedef _IotSystemSemaphore_t   IotSemaphore_t;

/**
 * @brief Thread routine function.
 *
 * @param[in] pArgument The argument passed to the @ref
 * platform_threads_function_createdetachedthread. For application use.
 */
typedef void ( * IotThreadRoutine_t )( void * pArgument );

/*-------------------------- Clock and timer types --------------------------*/

/**
 * @ingroup platform_datatypes_handles
 * @brief The type used to represent timers, configured with the type
 * `_IotSystemTimer_t`.
 *
 * For the provided ports, `_IotSystemTimer_t` will be automatically configured.
 * For other ports, `_IotSystemTimer_t` should be set in `iot_config.h`.
 *
 * <b>Example</b> <br>
 * To change the type of #IotTimer_t to `long`:
 * @code{c}
 * typedef long _IotSystemTimer_t;
 * #include "iot_clock.h"
 * @endcode
 */
typedef _IotSystemTimer_t          IotTimer_t;

/*--------------------------- Network stack types ---------------------------*/

/**
 * @ingroup platform_datatypes_handles
 * @brief The type used to represent network server info, configured with the
 * type `_IotNetworkServerInfo_t`.
 *
 * For the provided ports, `_IotNetworkServerInfo_t` will be automatically configured.
 * For other ports, `_IotNetworkServerInfo_t` should be set in `iot_config.h`.
 *
 * All of the provided ports configure this to #IotNetworkServerInfo, which provides
 * the necessary information to connect to a TCP peer. For other network protocols,
 * this type should be set to an alternate structure as needed by the other protocol.
 */
typedef _IotNetworkServerInfo_t    IotNetworkServerInfo_t;

/**
 * @ingroup platform_datatypes_handles
 * @brief The type used to represent network credentials, configured with the
 * type `_IotNetworkCredentials_t`.
 *
 * For the provided ports, `_IotNetworkCredentials_t` will be automatically configured.
 * For other ports, `_IotNetworkCredentials_t` should be set in `iot_config.h`.
 *
 * All of the provided ports configure this to #IotNetworkCredentials, which provides
 * the necessary information to connect to a TLS server over TCP. For other network
 * protocols, this type should be set to an alternate structure as needed by the other
 * protocol.
 */
typedef _IotNetworkCredentials_t   IotNetworkCredentials_t;

/**
 * @ingroup platform_datatypes_handles
 * @brief The type used to represent network connections, configured with the
 * type `_IotNetworkConnection_t`.
 *
 * For the provided ports, `_IotNetworkConnection_t` will be automatically configured.
 * For other ports, `_IotNetworkConnection_t` should be set in `iot_config.h`.
 */
typedef _IotNetworkConnection_t    IotNetworkConnection_t;

/*------------------------------ Metrics types ------------------------------*/

/**
 * @brief The length of the buffer used to store IP addresses for metrics.
 *
 * This is the length of the longest IPv6 address plus space for the port number
 * and NULL terminator.
 */
#define IOT_METRICS_IP_ADDRESS_LENGTH    54

/**
 * @brief Represents a TCP connection to a remote IPv4 server.
 *
 * A list of these is provided by @ref platform_metrics_function_gettcpconnections.
 */
typedef struct IotMetricsTcpConnection
{
    IotLink_t link;         /**< @brief List link member. */
    void * pNetworkContext; /**< @brief Context that may be used by metrics or Defender. */
    size_t addressLength;   /**< @brief The length of the address stored in #IotMetricsTcpConnection_t.pRemoteAddress. */

    /**
     * @brief NULL-terminated IP address and port in text format.
     *
     * IPv4 addresses will be in the format `xxx.xxx.xxx.xxx:port`.
     * IPv6 addresses will be in the format `[xxxx:xxxx:xxxx:xxxx:xxxx:xxxx:xxxx:xxxx]:port`.
     */
    char pRemoteAddress[ IOT_METRICS_IP_ADDRESS_LENGTH ];
} IotMetricsTcpConnection_t;

#endif /* ifndef IOT_PLATFORM_TYPES_H_ */
