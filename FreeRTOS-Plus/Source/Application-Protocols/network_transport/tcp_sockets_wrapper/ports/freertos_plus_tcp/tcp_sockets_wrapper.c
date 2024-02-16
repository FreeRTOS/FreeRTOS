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
 * @file sockets_wrapper.c
 * @brief FreeRTOS Sockets connect and disconnect wrapper implementation.
 */

/* Include header that defines log levels. */
#include "logging_levels.h"

/* FreeRTOS includes. */
#include "FreeRTOS.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_Sockets.h"
#include "FreeRTOS_DNS.h"

/* Logging configuration for the Sockets. */
#ifndef LIBRARY_LOG_NAME
    #define LIBRARY_LOG_NAME     "SocketsWrapper"
#endif
#ifndef LIBRARY_LOG_LEVEL
    #define LIBRARY_LOG_LEVEL    LOG_INFO
#endif

extern void vLoggingPrintf( const char * pcFormatString,
                            ... );

#include "logging_stack.h"

/* Standard includes. */
#include <string.h>

/* TCP Sockets Wrapper include.*/
/* Let sockets wrapper know that Socket_t is defined already. */
#define SOCKET_T_TYPEDEFED
#include "tcp_sockets_wrapper.h"

/**
 * @brief Maximum number of times to call FreeRTOS_recv when initiating a graceful shutdown.
 */
#ifndef FREERTOS_SOCKETS_WRAPPER_SHUTDOWN_LOOPS
    #define FREERTOS_SOCKETS_WRAPPER_SHUTDOWN_LOOPS    ( 3 )
#endif

/**
 * @brief negative error code indicating a network failure.
 */
#define FREERTOS_SOCKETS_WRAPPER_NETWORK_ERROR    ( -1 )

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
                                uint32_t sendTimeoutMs )
{
    Socket_t tcpSocket = FREERTOS_INVALID_SOCKET;
    BaseType_t socketStatus = 0;
    struct freertos_sockaddr serverAddress = { 0 };
    TickType_t transportTimeout = 0;

    configASSERT( pTcpSocket != NULL );
    configASSERT( pHostName != NULL );

    /* Create a new TCP socket. */
    tcpSocket = FreeRTOS_socket( FREERTOS_AF_INET, FREERTOS_SOCK_STREAM, FREERTOS_IPPROTO_TCP );

    if( tcpSocket == FREERTOS_INVALID_SOCKET )
    {
        LogError( ( "Failed to create new socket." ) );
        socketStatus = FREERTOS_SOCKETS_WRAPPER_NETWORK_ERROR;
    }
    else
    {
        LogDebug( ( "Created new TCP socket." ) );

        /* Connection parameters. */
        serverAddress.sin_family = FREERTOS_AF_INET;
        serverAddress.sin_port = FreeRTOS_htons( port );
        serverAddress.sin_len = ( uint8_t ) sizeof( serverAddress );

        #if defined( ipconfigIPv4_BACKWARD_COMPATIBLE ) && ( ipconfigIPv4_BACKWARD_COMPATIBLE == 0 )
            serverAddress.sin_address.ulIP_IPv4 = ( uint32_t ) FreeRTOS_gethostbyname( pHostName );

            /* Check for errors from DNS lookup. */
            if( serverAddress.sin_address.ulIP_IPv4 == 0U )
        #else
            serverAddress.sin_addr = ( uint32_t ) FreeRTOS_gethostbyname( pHostName );

            /* Check for errors from DNS lookup. */
            if( serverAddress.sin_addr == 0U )
        #endif /* defined( ipconfigIPv4_BACKWARD_COMPATIBLE ) && ( ipconfigIPv4_BACKWARD_COMPATIBLE == 0 ) */

        {
            LogError( ( "Failed to connect to server: DNS resolution failed: Hostname=%s.",
                        pHostName ) );
            socketStatus = FREERTOS_SOCKETS_WRAPPER_NETWORK_ERROR;
        }
    }

    if( socketStatus == 0 )
    {
        /* Establish connection. */
        LogDebug( ( "Creating TCP Connection to %s.", pHostName ) );
        socketStatus = FreeRTOS_connect( tcpSocket, &serverAddress, sizeof( serverAddress ) );

        if( socketStatus != 0 )
        {
            LogError( ( "Failed to connect to server: FreeRTOS_Connect failed: ReturnCode=%d,"
                        " Hostname=%s, Port=%u.",
                        socketStatus,
                        pHostName,
                        port ) );
        }
    }

    if( socketStatus == 0 )
    {
        /* Set socket receive timeout. */
        transportTimeout = pdMS_TO_TICKS( receiveTimeoutMs );
        /* Setting the receive block time cannot fail. */
        ( void ) FreeRTOS_setsockopt( tcpSocket,
                                      0,
                                      FREERTOS_SO_RCVTIMEO,
                                      &transportTimeout,
                                      sizeof( TickType_t ) );

        /* Set socket send timeout. */
        transportTimeout = pdMS_TO_TICKS( sendTimeoutMs );
        /* Setting the send block time cannot fail. */
        ( void ) FreeRTOS_setsockopt( tcpSocket,
                                      0,
                                      FREERTOS_SO_SNDTIMEO,
                                      &transportTimeout,
                                      sizeof( TickType_t ) );
    }

    /* Clean up on failure. */
    if( socketStatus != 0 )
    {
        if( tcpSocket != FREERTOS_INVALID_SOCKET )
        {
            ( void ) FreeRTOS_closesocket( tcpSocket );
            tcpSocket = FREERTOS_INVALID_SOCKET;
        }
    }
    else
    {
        /* Set the socket. */
        *pTcpSocket = tcpSocket;
        LogInfo( ( "Established TCP connection with %s.", pHostName ) );
    }

    return socketStatus;
}

/**
 * @brief End connection to server.
 *
 * @param[in] tcpSocket The socket descriptor.
 */
void TCP_Sockets_Disconnect( Socket_t tcpSocket )
{
    BaseType_t waitForShutdownLoopCount = 0;
    uint8_t pDummyBuffer[ 2 ];

    if( ( tcpSocket != NULL ) && ( tcpSocket != FREERTOS_INVALID_SOCKET ) )
    {
        /* Initiate graceful shutdown. */
        ( void ) FreeRTOS_shutdown( tcpSocket, FREERTOS_SHUT_RDWR );

        /* Wait for the socket to disconnect gracefully (indicated by FreeRTOS_recv()
         * returning a FREERTOS_EINVAL error) before closing the socket. */
        while( FreeRTOS_recv( tcpSocket, pDummyBuffer, sizeof( pDummyBuffer ), 0 ) >= 0 )
        {
            /* We don't need to delay since FreeRTOS_recv should already have a timeout. */

            if( ++waitForShutdownLoopCount >= FREERTOS_SOCKETS_WRAPPER_SHUTDOWN_LOOPS )
            {
                break;
            }
        }

        ( void ) FreeRTOS_closesocket( tcpSocket );
    }
}

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
                          size_t xBufferLength )
{
    BaseType_t xSendStatus;
    int xReturnStatus = TCP_SOCKETS_ERRNO_ERROR;

    configASSERT( xSocket != NULL );
    configASSERT( pvBuffer != NULL );

    xSendStatus = FreeRTOS_send( xSocket, pvBuffer, xBufferLength, 0 );

    switch( xSendStatus )
    {
        /* Socket was closed or just got closed. */
        case -pdFREERTOS_ERRNO_ENOTCONN:
            xReturnStatus = TCP_SOCKETS_ERRNO_ENOTCONN;
            break;

        /* Not enough memory for the socket to create either an Rx or Tx stream. */
        case -pdFREERTOS_ERRNO_ENOMEM:
            xReturnStatus = TCP_SOCKETS_ERRNO_ENOMEM;
            break;

        /* Socket is not valid, is not a TCP socket, or is not bound. */
        case -pdFREERTOS_ERRNO_EINVAL:
            xReturnStatus = TCP_SOCKETS_ERRNO_EINVAL;
            break;

        /* Socket received a signal, causing the read operation to be aborted. */
        case -pdFREERTOS_ERRNO_EINTR:
            xReturnStatus = TCP_SOCKETS_ERRNO_EINTR;
            break;

        /* A timeout occurred before any data could be sent as the TCP buffer was full. */
        case -pdFREERTOS_ERRNO_ENOSPC:
            xReturnStatus = TCP_SOCKETS_ERRNO_ENOSPC;
            break;

        default:
            xReturnStatus = ( int ) xSendStatus;
            break;
    }

    return xReturnStatus;
}

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
                          size_t xBufferLength )
{
    BaseType_t xRecvStatus;
    int xReturnStatus = TCP_SOCKETS_ERRNO_ERROR;

    configASSERT( xSocket != NULL );
    configASSERT( pvBuffer != NULL );

    xRecvStatus = FreeRTOS_recv( xSocket, pvBuffer, xBufferLength, 0 );

    switch( xRecvStatus )
    {
        /* Socket was closed or just got closed. */
        case -pdFREERTOS_ERRNO_ENOTCONN:
            xReturnStatus = TCP_SOCKETS_ERRNO_ENOTCONN;
            break;

        /* Not enough memory for the socket to create either an Rx or Tx stream. */
        case -pdFREERTOS_ERRNO_ENOMEM:
            xReturnStatus = TCP_SOCKETS_ERRNO_ENOMEM;
            break;

        /* Socket is not valid, is not a TCP socket, or is not bound. */
        case -pdFREERTOS_ERRNO_EINVAL:
            xReturnStatus = TCP_SOCKETS_ERRNO_EINVAL;
            break;

        /* Socket received a signal, causing the read operation to be aborted. */
        case -pdFREERTOS_ERRNO_EINTR:
            xReturnStatus = TCP_SOCKETS_ERRNO_EINTR;
            break;

        default:
            xReturnStatus = ( int ) xRecvStatus;
            break;
    }

    return xReturnStatus;
}
