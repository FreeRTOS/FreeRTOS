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

/* Standard includes. */
#include <string.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "atomic.h"
#include "semphr.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_Sockets.h"

/* Transport interface include. */
#include "plaintext_freertos.h"

/* Maximum number of times to call FreeRTOS_recv when initiating a graceful shutdown. */
#ifndef TRANSPORT_FREERTOS_SHUTDOWN_LOOPS
    #define TRANSPORT_FREERTOS_SHUTDOWN_LOOPS    ( 3 )
#endif

/* A negative error code indicating a network failure. */
#define TRANSPORT_FREERTOS_NETWORK_ERROR    ( -1 )

BaseType_t Plaintext_FreeRTOS_Connect( NetworkContext_t * pNetworkContext,
                                       const char * pHostName,
                                       uint16_t port,
                                       uint32_t receiveTimeoutMs,
                                       uint32_t sendTimeoutMs )
{
    Socket_t tcpSocket = FREERTOS_INVALID_SOCKET;
    BaseType_t socketStatus = 0;
    struct freertos_sockaddr serverAddress = { 0 };
    TickType_t transportTimeout = 0;

    /* Create a new TCP socket. */
    tcpSocket = FreeRTOS_socket( FREERTOS_AF_INET, FREERTOS_SOCK_STREAM, FREERTOS_IPPROTO_TCP );

    if( tcpSocket == FREERTOS_INVALID_SOCKET )
    {
        LogError( ( "Failed to create new socket." ) );
        socketStatus = TRANSPORT_FREERTOS_NETWORK_ERROR;
    }
    else
    {
        LogDebug( ( "Created new TCP socket." ) );

        /* Connection parameters. */
        serverAddress.sin_family = FREERTOS_AF_INET;
        serverAddress.sin_port = FreeRTOS_htons( port );
        serverAddress.sin_addr = FreeRTOS_gethostbyname( pHostName );
        serverAddress.sin_len = ( uint8_t ) sizeof( serverAddress );

        /* Check for errors from DNS lookup. */
        if( serverAddress.sin_addr == 0 )
        {
            LogError( ( "Failed to resolve %s.", pHostName ) );
            socketStatus = TRANSPORT_FREERTOS_NETWORK_ERROR;
        }
    }

    if( socketStatus == 0 )
    {
        /* Establish connection. */
        LogDebug( ( "Creating TCP Connection to %s.", pHostName ) );
        socketStatus = FreeRTOS_connect( tcpSocket, &serverAddress, sizeof( serverAddress ) );

        if( socketStatus != 0 )
        {
            LogError( ( "Failed to establish TCP Connection: ReturnCode=%d.", socketStatus ) );
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
            FreeRTOS_closesocket( tcpSocket );
        }
    }
    else
    {
        /* Set the socket. */
        pNetworkContext->tcpSocket = tcpSocket;
        LogDebug( ( "TCP Connection to %s established.", pHostName ) );
    }

    return socketStatus;
}

void Plaintext_FreeRTOS_Disconnect( const NetworkContext_t * pNetworkContext )
{
    BaseType_t waitForShutdownLoopCount = 0;
    uint8_t pDummyBuffer[ 2 ];

    if( pNetworkContext->tcpSocket != FREERTOS_INVALID_SOCKET )
    {
        /* Initiate graceful shutdown. */
        ( void ) FreeRTOS_shutdown( pNetworkContext->tcpSocket, FREERTOS_SHUT_RDWR );

        /* Wait for the socket to disconnect gracefully (indicated by FreeRTOS_recv()
         * returning a FREERTOS_EINVAL error) before closing the socket. */
        while( FreeRTOS_recv( pNetworkContext->tcpSocket, pDummyBuffer, sizeof( pDummyBuffer ), 0 ) >= 0 )
        {
            /* We don't need to delay since FreeRTOS_recv should already have a timeout. */

            if( ++waitForShutdownLoopCount >= TRANSPORT_FREERTOS_SHUTDOWN_LOOPS )
            {
                break;
            }
        }

        ( void ) FreeRTOS_closesocket( pNetworkContext->tcpSocket );
    }
}

int32_t Plaintext_FreeRTOS_recv( NetworkContext_t * pNetworkContext,
                                 void * pBuffer,
                                 size_t bytesToRecv )
{
    int32_t socketStatus = 0;

    socketStatus = FreeRTOS_recv( pNetworkContext->tcpSocket, pBuffer, bytesToRecv, 0 );

    return socketStatus;
}

int32_t Plaintext_FreeRTOS_send( NetworkContext_t * pNetworkContext,
                                 const void * pBuffer,
                                 size_t bytesToSend )
{
    int32_t socketStatus = 0;

    socketStatus = FreeRTOS_send( pNetworkContext->tcpSocket, pBuffer, bytesToSend, 0 );

    return socketStatus;
}
