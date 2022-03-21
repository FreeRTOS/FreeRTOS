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
 * https://www.FreeRTOS.org
 * https://github.com/FreeRTOS
 *
 */

/**
 * @file sockets_wrapper.c
 * @brief FreeRTOS Sockets connect and disconnect wrapper implementation.
 */

/* Standard includes. */
#include <string.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"

#include "sockets_wrapper.h"

/*-----------------------------------------------------------*/

/* Maximum number of times to call FreeRTOS_recv when initiating a graceful shutdown. */
#ifndef FREERTOS_SOCKETS_WRAPPER_SHUTDOWN_LOOPS
    #define FREERTOS_SOCKETS_WRAPPER_SHUTDOWN_LOOPS    ( 3 )
#endif

/* A negative error code indicating a network failure. */
#define FREERTOS_SOCKETS_WRAPPER_NETWORK_ERROR    ( -1 )

/*-----------------------------------------------------------*/

BaseType_t Sockets_Connect( Socket_t * pTcpSocket,
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
        socketStatus = FREERTOS_SOCKETS_WRAPPER_NETWORK_ERROR;
    }
    else
    {
        LogDebug( ( "Created new TCP socket." ) );

        /* Connection parameters. */
        serverAddress.sin_family = FREERTOS_AF_INET;
        serverAddress.sin_port = FreeRTOS_htons( port );
        serverAddress.sin_addr = ( uint32_t ) FreeRTOS_gethostbyname( pHostName );
        serverAddress.sin_len = ( uint8_t ) sizeof( serverAddress );

        /* Check for errors from DNS lookup. */
        if( serverAddress.sin_addr == 0U )
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

/*-----------------------------------------------------------*/

void Sockets_Disconnect( Socket_t tcpSocket )
{
    BaseType_t waitForShutdownLoopCount = 0;
    uint8_t pDummyBuffer[ 2 ];

    if( tcpSocket != FREERTOS_INVALID_SOCKET )
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

/*-----------------------------------------------------------*/
