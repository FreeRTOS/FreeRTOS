/*
 * FreeRTOS V202212.00
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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
 * https://www.FreeRTOS.org
 * https://github.com/FreeRTOS
 *
 */

/**
 * @file tcp_sockets_wrapper.h
 * @brief TCP transport functions wrapper.
 */

#ifndef TCP_SOCKETS_WRAPPER_H
#define TCP_SOCKETS_WRAPPER_H


/* Standard includes. */
#include <stdint.h>

/* FreeRTOS Kernel includes. */
#include "FreeRTOS.h"

/* Error codes. */
#define TCP_SOCKETS_ERRNO_NONE                ( 0 )   /*!< No error. */
#define TCP_SOCKETS_ERRNO_ERROR               ( -1 )  /*!< Catch-all sockets error code. */
#define TCP_SOCKETS_ERRNO_EWOULDBLOCK         ( -2 )  /*!< A resource is temporarily unavailable. */
#define TCP_SOCKETS_ERRNO_ENOMEM              ( -3 )  /*!< Memory allocation failed. */
#define TCP_SOCKETS_ERRNO_EINVAL              ( -4 )  /*!< Invalid argument. */
#define TCP_SOCKETS_ERRNO_ENOPROTOOPT         ( -5 )  /*!< A bad option was specified . */
#define TCP_SOCKETS_ERRNO_ENOTCONN            ( -6 )  /*!< The supplied socket is not connected. */
#define TCP_SOCKETS_ERRNO_EISCONN             ( -7 )  /*!< The supplied socket is already connected. */
#define TCP_SOCKETS_ERRNO_ECLOSED             ( -8 )  /*!< The supplied socket has already been closed. */
#define TCP_SOCKETS_ERRNO_PERIPHERAL_RESET    ( -9 )  /*!< Communications peripheral has been reset. */
#define TCP_SOCKETS_ERRNO_ENOSPC              ( -10 ) /*!< No space left on device */
#define TCP_SOCKETS_ERRNO_EINTR               ( -11 ) /*!< Interrupted system call */

#ifndef SOCKET_T_TYPEDEFED
    struct xSOCKET;
    typedef struct xSOCKET * Socket_t; /**< @brief Socket handle data type. */
#endif

/**
 * @brief Establish a connection to server.
 *
 * @param[out] pTcpSocket The output parameter to return the created socket descriptor.
 * @param[in] pHostName Server hostname to connect to.
 * @param[in] pServerInfo Server port to connect to.
 * @param[in] receiveTimeoutMs Timeout (in milliseconds) for transport receive.
 * @param[in] sendTimeoutMs Timeout (in milliseconds) for transport send.
 *
 * @note A timeout of 0 means infinite timeout.
 *
 * @return Non-zero value on error, 0 on success.
 */
BaseType_t TCP_Sockets_Connect( Socket_t * pTcpSocket,
                                const char * pHostName,
                                uint16_t port,
                                uint32_t receiveTimeoutMs,
                                uint32_t sendTimeoutMs );

/**
 * @brief End connection to server.
 *
 * @param[in] tcpSocket The socket descriptor.
 */
void TCP_Sockets_Disconnect( Socket_t tcpSocket );

/**
 * @brief Transmit data to the remote socket.
 *
 * The socket must have already been created using a call to TCP_Sockets_Connect().
 *
 * @param[in] xSocket The handle of the sending socket.
 * @param[in] pvBuffer The buffer containing the data to be sent.
 * @param[in] xDataLength The length of the data to be sent.
 *
 * @return
 * * On success, the number of bytes actually sent is returned.
 * * If an error occurred, a negative value is returned. @ref SocketsErrors
 */
int32_t TCP_Sockets_Send( Socket_t xSocket,
                          const void * pvBuffer,
                          size_t xDataLength );

/**
 * @brief Receive data from a TCP socket.
 *
 * The socket must have already been created using a call to TCP_Sockets_Connect().
 *
 * @param[in] xSocket The handle of the socket from which data is being received.
 * @param[out] pvBuffer The buffer into which the received data will be placed.
 * @param[in] xBufferLength The maximum number of bytes which can be received.
 * pvBuffer must be at least xBufferLength bytes long.
 *
 * @return
 * * If the receive was successful then the number of bytes received (placed in the
 *   buffer pointed to by pvBuffer) is returned.
 * * If a timeout occurred before data could be received then 0 is returned (timeout
 *   is set using @ref SOCKETS_SO_RCVTIMEO).
 * * If an error occurred, a negative value is returned. @ref SocketsErrors
 */
int32_t TCP_Sockets_Recv( Socket_t xSocket,
                          void * pvBuffer,
                          size_t xBufferLength );

#endif /* ifndef TCP_SOCKETS_WRAPPER_H */
