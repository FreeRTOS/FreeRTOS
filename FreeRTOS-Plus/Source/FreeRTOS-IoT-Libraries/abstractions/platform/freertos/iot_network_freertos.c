/*
 * Amazon FreeRTOS Platform V1.0.0
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

/**
 * @file iot_network_freertos.c
 * @brief Implementation of the network-related functions from iot_network_freertos.h
 * for FreeRTOS+TCP sockets.
 */

/* The config header is always included first. */
#include "iot_config.h"

/* Standard includes. */
#include <string.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "semphr.h"
#include "event_groups.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_Sockets.h"

/* FreeRTOS-IoT-Libraries includes. */
#include "private/iot_error.h"
#include "platform/iot_network_freertos.h"

/* Configure logs for the functions in this file. */
#ifdef IOT_LOG_LEVEL_NETWORK
    #define LIBRARY_LOG_LEVEL        IOT_LOG_LEVEL_NETWORK
#else
    #ifdef IOT_LOG_LEVEL_GLOBAL
        #define LIBRARY_LOG_LEVEL    IOT_LOG_LEVEL_GLOBAL
    #else
        #define LIBRARY_LOG_LEVEL    IOT_LOG_NONE
    #endif
#endif

#define LIBRARY_LOG_NAME    ( "NET" )
#include "iot_logging_setup.h"

/* Provide a default value for the number of milliseconds for a socket poll.
 * This is a temporary workaround to deal with the lack of poll(). */
#ifndef IOT_NETWORK_SOCKET_POLL_MS
    #define IOT_NETWORK_SOCKET_POLL_MS      ( 1000 )
#endif

/**
 * @brief The event group bit to set when a connection's socket is shut down.
 */
#define _SHUTDOWN_BITMASK                   ( 1UL << 0UL )

/**
 * @brief The event group bit to set when a connection's receive task exits.
 */
#define _RECEIVE_TASK_EXITED_BITMASK        ( 1UL << 1UL )

/**
 * @brief The event group bit to set when the connection is destroyed from the
 * receive task.
 */
#define _CONNECTION_DESTROYED_BITMASK       ( 1UL << 2UL )

/**
 * @brief Maximum length of a DNS name.
 *
 * Per https://tools.ietf.org/html/rfc1035, 253 is the maximum string length
 * of a DNS name.
 */
#define _MAX_DNS_NAME_LENGTH                ( 253 )
/*-----------------------------------------------------------*/

typedef struct _networkConnection
{
    Socket_t socket;                                /**< @brief FreeRTOS+TCP sockets handle. */
    SemaphoreHandle_t socketMutex;                  /**< @brief Prevents concurrent threads from sending on a socket. */
    StaticSemaphore_t socketMutexStorage;           /**< @brief Storage space for socketMutex. */
    EventGroupHandle_t connectionEventGroup;        /**< @brief Synchronizes with the receive task. */
    StaticEventGroup_t connectionEventGroupStorage; /**< @brief Storage space for connectionEventGroup. */
    TaskHandle_t receiveTask;                       /**< @brief Handle of the receive task, if any. */
    IotNetworkReceiveCallback_t receiveCallback;    /**< @brief Network receive callback, if any. */
    void * pReceiveContext;                         /**< @brief The context for the receive callback. */
    bool bufferedByteValid;                         /**< @brief Used to determine if the buffered byte is valid. */
    uint8_t bufferedByte;                           /**< @brief A single byte buffered from a receive, since FreeRTOS+TCP sockets does not have poll(). */
} _networkConnection_t;
/*-----------------------------------------------------------*/

/**
 * @brief An #IotNetworkInterface_t that uses the functions in this file.
 */
const IotNetworkInterface_t IotNetworkFreeRTOS =
{
    .create             = IotNetworkFreeRTOS_Create,
    .setReceiveCallback = IotNetworkFreeRTOS_SetReceiveCallback,
    .send               = IotNetworkFreeRTOS_Send,
    .receive            = IotNetworkFreeRTOS_Receive,
    .close              = IotNetworkFreeRTOS_Close,
    .destroy            = IotNetworkFreeRTOS_Destroy
};
/*-----------------------------------------------------------*/

/**
 * @brief Destroys a network connection.
 *
 * @param[in] pNetworkConnection The connection to destroy.
 */
static void _destroyConnection( _networkConnection_t * pNetworkConnection )
{
    /* Call FreeRTOS+TCP close function to free resources. */
    ( void ) FreeRTOS_closesocket( pNetworkConnection->socket  );

    /* Free the network connection. */
    vPortFree( pNetworkConnection );
}
/*-----------------------------------------------------------*/

/**
 * @brief Task routine that waits on incoming network data.
 *
 * @param[in] pArgument The network connection.
 */
static void _networkReceiveTask( void * pArgument )
{
    bool destroyConnection = false;
    int32_t socketStatus = 0;
    EventBits_t connectionEventGroupBits = 0;

    /* Cast network connection to the correct type. */
    _networkConnection_t * pNetworkConnection = pArgument;

    while( true )
    {
        /* No buffered byte should be in the connection. */
        configASSERT( pNetworkConnection->bufferedByteValid == false );

        /* Block and wait for 1 byte of data. This simulates the behavior of poll().
         * THIS IS A TEMPORARY WORKAROUND AND DOES NOT PROVIDE THREAD-SAFETY AGAINST
         * MULTIPLE CALLS OF RECEIVE. */
        do
        {
            socketStatus = FreeRTOS_recv( pNetworkConnection->socket,
                                          &( pNetworkConnection->bufferedByte ),
                                          1,
                                          0 );

            connectionEventGroupBits = xEventGroupGetBits( pNetworkConnection->connectionEventGroup );

            if( ( connectionEventGroupBits & _SHUTDOWN_BITMASK ) == _SHUTDOWN_BITMASK )
            {
                socketStatus = FREERTOS_ECLOSED;
            }

            /* Check for timeout. Some ports return 0, some return EWOULDBLOCK. */
        } while( ( socketStatus == 0 ) || ( socketStatus == FREERTOS_EWOULDBLOCK ) );

        if( socketStatus <= 0 )
        {
            break;
        }

        pNetworkConnection->bufferedByteValid = true;

        /* Invoke the network callback. */
        pNetworkConnection->receiveCallback( pNetworkConnection,
                                             pNetworkConnection->pReceiveContext );

        /* Check if the connection was destroyed by the receive callback. This
         * does not need to be thread-safe because the destroy connection function
         * may only be called once (per its API doc). */
        connectionEventGroupBits = xEventGroupGetBits( pNetworkConnection->connectionEventGroup );

        if( ( connectionEventGroupBits & _CONNECTION_DESTROYED_BITMASK ) == _CONNECTION_DESTROYED_BITMASK )
        {
            destroyConnection = true;
            break;
        }
    }

    IotLogDebug( "Network receive task terminating." );

    /* If necessary, destroy the network connection before exiting. */
    if( destroyConnection == true )
    {
        _destroyConnection( pNetworkConnection );
    }
    else
    {
        /* Set the bit to indicate that the receive task has exited. */
        ( void ) xEventGroupSetBits( pNetworkConnection->connectionEventGroup,
                                     _RECEIVE_TASK_EXITED_BITMASK );
    }

    vTaskDelete( NULL );
}
/*-----------------------------------------------------------*/

IotNetworkError_t IotNetworkFreeRTOS_Create( void * pConnectionInfo,
                                             void * pCredentialInfo,
                                             void ** pConnection ) //_RB_ Why all void* and why a void**?
{
    IOT_FUNCTION_ENTRY( IotNetworkError_t, IOT_NETWORK_SUCCESS );
    Socket_t tcpSocket = FREERTOS_INVALID_SOCKET;
    int32_t socketStatus = 0;
    struct freertos_sockaddr serverAddress = { 0 };
    const TickType_t receiveTimeout = pdMS_TO_TICKS( IOT_NETWORK_SOCKET_POLL_MS );
    _networkConnection_t * pNewNetworkConnection = NULL;

    /* TLS is not enabled in this version and therefore pCredentialInfo
    must be NULL. */
    configASSERT( pCredentialInfo == NULL );

    /* Cast function parameters to correct types. */
    const IotNetworkServerInfo_t * pServerInfo = pConnectionInfo;
    _networkConnection_t ** pNetworkConnection = ( _networkConnection_t ** ) pConnection;

    /* Check host name length against the maximum length allowed. */
    const size_t hostnameLength = strlen( pServerInfo->pHostName );

    if( hostnameLength > ( size_t ) _MAX_DNS_NAME_LENGTH )
    {
        IotLogError( "Host name length exceeds %d, which is the maximum allowed.",
                     _MAX_DNS_NAME_LENGTH );
        IOT_SET_AND_GOTO_CLEANUP( IOT_NETWORK_BAD_PARAMETER );
    }

    pNewNetworkConnection = pvPortMalloc( sizeof( _networkConnection_t ) );

    if( pNewNetworkConnection == NULL )
    {
        IotLogError( "Failed to allocate memory for new network connection." );
        IOT_SET_AND_GOTO_CLEANUP( IOT_NETWORK_NO_MEMORY );
    }

    /* Clear the connection information. */
    ( void ) memset( pNewNetworkConnection, 0x00, sizeof( _networkConnection_t ) );

    /* Create a new TCP socket. */
    tcpSocket = FreeRTOS_socket( FREERTOS_AF_INET,
                                 FREERTOS_SOCK_STREAM,
                                 FREERTOS_IPPROTO_TCP );

    if( tcpSocket == FREERTOS_INVALID_SOCKET )
    {
        IotLogError( "Failed to create new socket." );
        IOT_SET_AND_GOTO_CLEANUP( IOT_NETWORK_SYSTEM_ERROR );
    }

    /* Establish connection. */
    serverAddress.sin_family = FREERTOS_AF_INET;
    serverAddress.sin_port = FreeRTOS_htons( pServerInfo->port );
    serverAddress.sin_addr = FreeRTOS_gethostbyname( pServerInfo->pHostName );
    serverAddress.sin_len = ( uint8_t ) sizeof( serverAddress );

    /* Check for errors from DNS lookup. */
    if( serverAddress.sin_addr == 0 )
    {
        IotLogError( "Failed to resolve %s.", pServerInfo->pHostName );
        IOT_SET_AND_GOTO_CLEANUP( IOT_NETWORK_SYSTEM_ERROR );
    }
    //_RB_ Connects without setting a read block time.
    socketStatus = FreeRTOS_connect( tcpSocket,
                                     &serverAddress,
                                     sizeof( serverAddress ) );

    if( socketStatus != 0 )
    {
        IotLogError( "Failed to establish new connection." );
        IOT_SET_AND_GOTO_CLEANUP( IOT_NETWORK_SYSTEM_ERROR );
    }

    /* Set a long timeout for receive. */
    socketStatus = FreeRTOS_setsockopt( tcpSocket,
                                        0,
                                        FREERTOS_SO_RCVTIMEO,
                                        &receiveTimeout,
                                        sizeof( TickType_t ) );

    if( socketStatus != 0 )
    {
        IotLogError( "Failed to set socket receive timeout." );
        IOT_SET_AND_GOTO_CLEANUP( IOT_NETWORK_SYSTEM_ERROR );
    }

    IOT_FUNCTION_CLEANUP_BEGIN();

    /* Clean up on failure. */
    if( status != IOT_NETWORK_SUCCESS )
    {
        if( tcpSocket != FREERTOS_INVALID_SOCKET )
        {
            FreeRTOS_closesocket( tcpSocket );
        }

        /* Clear the connection information. */
        if( pNewNetworkConnection != NULL )
        {
            vPortFree( pNewNetworkConnection );
        }
    }
    else
    {
        /* Set the socket. */
        pNewNetworkConnection->socket = tcpSocket;

        /* Create the connection event group and socket mutex. */
        pNewNetworkConnection->connectionEventGroup = xEventGroupCreateStatic( &( pNewNetworkConnection->connectionEventGroupStorage ) );
        pNewNetworkConnection->socketMutex = xSemaphoreCreateMutexStatic( &( pNewNetworkConnection->socketMutexStorage ) );

        /* Set the output parameter. */
        *pNetworkConnection = pNewNetworkConnection;
    }

    IOT_FUNCTION_CLEANUP_END();
}
/*-----------------------------------------------------------*/

IotNetworkError_t IotNetworkFreeRTOS_SetReceiveCallback( void * pConnection,
                                                         IotNetworkReceiveCallback_t receiveCallback,
                                                         void * pContext )
{
    IotNetworkError_t status = IOT_NETWORK_SUCCESS;

    /* Cast network connection to the correct type. */
    _networkConnection_t * pNetworkConnection = ( _networkConnection_t * ) pConnection;

    /* Set the receive callback and context. */
    pNetworkConnection->receiveCallback = receiveCallback;
    pNetworkConnection->pReceiveContext = pContext;

    /* No bit should be set in the connection event group. */
    configASSERT( xEventGroupGetBits( pNetworkConnection->connectionEventGroup ) == 0 );

    /* Create task that waits for incoming data. */
    if( xTaskCreate( _networkReceiveTask,
                     "NetRecv",
                     IOT_NETWORK_RECEIVE_TASK_STACK_SIZE,
                     pNetworkConnection,
                     IOT_NETWORK_RECEIVE_TASK_PRIORITY,
                     &( pNetworkConnection->receiveTask ) ) != pdPASS )
    {
        IotLogError( "Failed to create network receive task." );

        status = IOT_NETWORK_SYSTEM_ERROR;
    }

    return status;
}
/*-----------------------------------------------------------*/

size_t IotNetworkFreeRTOS_Send( void * pConnection,
                                const uint8_t * pMessage,
                                size_t messageLength )
{
    size_t bytesSent = 0;
    int32_t socketStatus = 0;

    /* Cast network connection to the correct type. */
    _networkConnection_t * pNetworkConnection = ( _networkConnection_t * ) pConnection;

    /* Only one thread at a time may send on the connection. Lock the socket
     * mutex to prevent other threads from sending. */
    if( xSemaphoreTake( pNetworkConnection->socketMutex, portMAX_DELAY ) == pdTRUE )
    {
        socketStatus = FreeRTOS_send( pNetworkConnection->socket,
                                      pMessage,
                                      messageLength,
                                      0 );

        if( socketStatus > 0 )
        {
            bytesSent = ( size_t ) socketStatus;
        }

        xSemaphoreGive( pNetworkConnection->socketMutex );
    }

    return bytesSent;
}
/*-----------------------------------------------------------*/

size_t IotNetworkFreeRTOS_Receive( void * pConnection,
                                   uint8_t * pBuffer,
                                   size_t bytesRequested )
{
    int32_t socketStatus = 0;
    size_t bytesReceived = 0, bytesRemaining = bytesRequested;

    /* Cast network connection to the correct type. */
    _networkConnection_t * pNetworkConnection = ( _networkConnection_t * ) pConnection;

    /* Write the buffered byte. THIS IS A TEMPORARY WORKAROUND AND ASSUMES THIS
     * FUNCTION IS ALWAYS CALLED FROM THE RECEIVE CALLBACK. */
    if( pNetworkConnection->bufferedByteValid == true )
    {
        *pBuffer = pNetworkConnection->bufferedByte;
        bytesReceived = 1;
        bytesRemaining--;
        pNetworkConnection->bufferedByteValid = false;
    }

    /* Block and wait for incoming data. */
    while( bytesRemaining > 0 )
    {
        socketStatus = FreeRTOS_recv( pNetworkConnection->socket,
                                      pBuffer + bytesReceived,
                                      bytesRemaining,
                                      0 );

        if( socketStatus == FREERTOS_EWOULDBLOCK )
        {
            /* The return value EWOULDBLOCK means no data was received within
             * the socket timeout. Ignore it and try again. */
            continue;
        }
        else if( socketStatus <= 0 )
        {
            IotLogError( "Error %ld while receiving data.", ( long int ) socketStatus );
            break;
        }
        else
        {
            bytesReceived += ( size_t ) socketStatus;
            bytesRemaining -= ( size_t ) socketStatus;

            configASSERT( bytesReceived + bytesRemaining == bytesRequested );
        }
    }

    if( bytesReceived < bytesRequested )
    {
        IotLogWarn( "Receive requested %lu bytes, but %lu bytes received instead.",
                    ( unsigned long ) bytesRequested,
                    ( unsigned long ) bytesReceived );
    }
    else
    {
        IotLogDebug( "Successfully received %lu bytes.",
                     ( unsigned long ) bytesRequested );
    }

    return bytesReceived;
}
/*-----------------------------------------------------------*/

IotNetworkError_t IotNetworkFreeRTOS_Close( void * pConnection )
{
    int32_t socketStatus = 0;

    /* Cast network connection to the correct type. */
    _networkConnection_t * pNetworkConnection = ( _networkConnection_t * ) pConnection;

    /* Call socket shutdown function to close connection. */
    socketStatus = FreeRTOS_shutdown( pNetworkConnection->socket,
                                      FREERTOS_SHUT_RDWR );

    if( socketStatus != 0 )
    {
        IotLogWarn( "Failed to close connection." );
    }

    /* Set the shutdown bit in the connection event group. */
    ( void ) xEventGroupSetBits( pNetworkConnection->connectionEventGroup,
                                 _SHUTDOWN_BITMASK );

    return IOT_NETWORK_SUCCESS;
}
/*-----------------------------------------------------------*/

IotNetworkError_t IotNetworkFreeRTOS_Destroy( void * pConnection )
{
    /* Cast network connection to the correct type. */
    _networkConnection_t * pNetworkConnection = ( _networkConnection_t * ) pConnection;

    /* Check if this function is being called from the receive task. */
    if( xTaskGetCurrentTaskHandle() == pNetworkConnection->receiveTask )
    {
        /* Set the bit specifying that the connection is destroyed. */
        ( void ) xEventGroupSetBits( pNetworkConnection->connectionEventGroup,
                                     _CONNECTION_DESTROYED_BITMASK );
    }
    else
    {
        /* If a receive task was created, wait for it to exit. */
        if( pNetworkConnection->receiveTask != NULL )
        {
            ( void ) xEventGroupWaitBits( pNetworkConnection->connectionEventGroup,
                                          _RECEIVE_TASK_EXITED_BITMASK,
                                          pdTRUE,
                                          pdTRUE,
                                          portMAX_DELAY );
        }

        _destroyConnection( pNetworkConnection );
    }

    return IOT_NETWORK_SUCCESS;
}
/*-----------------------------------------------------------*/
