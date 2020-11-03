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

#ifndef TRANSPORT_INTERFACE_FREERTOS_H_
#define TRANSPORT_INTERFACE_FREERTOS_H_

/**************************************************/
/******* DO NOT CHANGE the following order ********/
/**************************************************/

/* Logging related header files are required to be included in the following order:
 * 1. Include the header file "logging_levels.h".
 * 2. Define LIBRARY_LOG_NAME and  LIBRARY_LOG_LEVEL.
 * 3. Include the header file "logging_stack.h".
 */

/* Include header that defines log levels. */
#include "logging_levels.h"

/* Logging configuration for the Sockets. */
#ifndef LIBRARY_LOG_NAME
    #define LIBRARY_LOG_NAME     "PlaintextTransport"
#endif
#ifndef LIBRARY_LOG_LEVEL
    #define LIBRARY_LOG_LEVEL    LOG_ERROR
#endif

#include "logging_stack.h"

/************ End of logging configuration ****************/

/* FreeRTOS+TCP include. */
#include "FreeRTOS_Sockets.h"

/* Transport interface include. */
#include "transport_interface.h"

/**
 * @brief Network context definition for FreeRTOS sockets.
 */
struct NetworkContext
{
    Socket_t tcpSocket;
};

/**
 * @brief Plain text transport Connect / Disconnect return status.
 */
typedef enum PlaintextTransportStatus
{
    PLAINTEXT_TRANSPORT_SUCCESS = 1,           /**< Function successfully completed. */
    PLAINTEXT_TRANSPORT_INVALID_PARAMETER = 2, /**< At least one parameter was invalid. */
    PLAINTEXT_TRANSPORT_CONNECT_FAILURE = 3    /**< Initial connection to the server failed. */
} PlaintextTransportStatus_t;

/**
 * @brief Create a TCP connection with FreeRTOS sockets.
 *
 * @param[out] pNetworkContext Pointer to a network context to contain the
 * initialized socket handle.
 * @param[in] pHostName The hostname of the remote endpoint.
 * @param[in] port The destination port.
 * @param[in] receiveTimeoutMs Receive socket timeout.
 *
 * @return #PLAINTEXT_TRANSPORT_SUCCESS, #PLAINTEXT_TRANSPORT_INVALID_PARAMETER,
 * or #PLAINTEXT_TRANSPORT_CONNECT_FAILURE.
 */
PlaintextTransportStatus_t Plaintext_FreeRTOS_Connect( NetworkContext_t * pNetworkContext,
                                                       const char * pHostName,
                                                       uint16_t port,
                                                       uint32_t receiveTimeoutMs,
                                                       uint32_t sendTimeoutMs );

/**
 * @brief Gracefully disconnect an established TCP connection.
 *
 * @param[in] pNetworkContext Network context containing the TCP socket handle.
 *
 * @return #PLAINTEXT_TRANSPORT_SUCCESS, or #PLAINTEXT_TRANSPORT_INVALID_PARAMETER.
 */
PlaintextTransportStatus_t Plaintext_FreeRTOS_Disconnect( const NetworkContext_t * pNetworkContext );

/**
 * @brief Receives data from an established TCP connection.
 *
 * @param[in] pNetworkContext The network context containing the TCP socket
 * handle.
 * @param[out] pBuffer Buffer to receive bytes into.
 * @param[in] bytesToRecv Number of bytes to receive from the network.
 *
 * @return Number of bytes received if successful; 0 if the socket times out;
 * Negative value on error.
 */
int32_t Plaintext_FreeRTOS_recv( NetworkContext_t * pNetworkContext,
                                 void * pBuffer,
                                 size_t bytesToRecv );

/**
 * @brief Sends data over an established TCP connection.
 *
 * @param[in] pNetworkContext The network context containing the TCP socket
 * handle.
 * @param[in] pBuffer Buffer containing the bytes to send.
 * @param[in] bytesToSend Number of bytes to send from the buffer.
 *
 * @return Number of bytes sent on success; else a negative value.
 */
int32_t Plaintext_FreeRTOS_send( NetworkContext_t * pNetworkContext,
                                 const void * pBuffer,
                                 size_t bytesToSend );

#endif /* ifndef TRANSPORT_INTERFACE_FREERTOS_H_ */
