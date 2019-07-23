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
 * for Amazon FreeRTOS secure sockets.
 */

/* The config header is always included first. */
#include "iot_config.h"

/* Standard includes. */
#include <string.h>

/* FreeRTOS includes. */
#include "semphr.h"
#include "event_groups.h"

/* Error handling include. */
#include "private/iot_error.h"

/* Amazon FreeRTOS network include. */
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
    #define IOT_NETWORK_SOCKET_POLL_MS    ( 1000 )
#endif

/**
 * @brief The event group bit to set when a connection's socket is shut down.
 */
#define _FLAG_SHUTDOWN                ( 1 )

/**
 * @brief The event group bit to set when a connection's receive task exits.
 */
#define _FLAG_RECEIVE_TASK_EXITED     ( 2 )

/**
 * @brief The event group bit to set when the connection is destroyed from the
 * receive task.
 */
#define _FLAG_CONNECTION_DESTROYED    ( 4 )

/*-----------------------------------------------------------*/

typedef struct _networkConnection
{
    Socket_t socket;                             /**< @brief Amazon FreeRTOS Secure Sockets handle. */
    StaticSemaphore_t socketMutex;               /**< @brief Prevents concurrent threads from sending on a socket. */
    StaticEventGroup_t connectionFlags;          /**< @brief Synchronizes with the receive task. */
    TaskHandle_t receiveTask;                    /**< @brief Handle of the receive task, if any. */
    IotNetworkReceiveCallback_t receiveCallback; /**< @brief Network receive callback, if any. */
    void * pReceiveContext;                      /**< @brief The context for the receive callback. */
    bool bufferedByteValid;                      /**< @brief Used to determine if the buffered byte is valid. */
    uint8_t bufferedByte;                        /**< @brief A single byte buffered from a receive, since AFR Secure Sockets does not have poll(). */
} _networkConnection_t;

/*-----------------------------------------------------------*/

/**
 * @brief An #IotNetworkInterface_t that uses the functions in this file.
 */
const IotNetworkInterface_t IotNetworkAfr =
{
    .create             = IotNetworkAfr_Create,
    .setReceiveCallback = IotNetworkAfr_SetReceiveCallback,
    .send               = IotNetworkAfr_Send,
    .receive            = IotNetworkAfr_Receive,
    .close              = IotNetworkAfr_Close,
    .destroy            = IotNetworkAfr_Destroy
};

/*-----------------------------------------------------------*/

/**
 * @brief Destroys a network connection.
 *
 * @param[in] pNetworkConnection The connection to destroy.
 */
static void _destroyConnection( _networkConnection_t * pNetworkConnection )
{
    /* Call Secure Sockets close function to free resources. */
    int32_t socketStatus = SOCKETS_Close( pNetworkConnection->socket );

    if( socketStatus != SOCKETS_ERROR_NONE )
    {
        IotLogWarn( "Failed to destroy connection." );
    }

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
    EventBits_t connectionFlags = 0;

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
            socketStatus = SOCKETS_Recv( pNetworkConnection->socket,
                                         &( pNetworkConnection->bufferedByte ),
                                         1,
                                         0 );

            connectionFlags = xEventGroupGetBits( ( EventGroupHandle_t ) &( pNetworkConnection->connectionFlags ) );

            if( ( connectionFlags & _FLAG_SHUTDOWN ) == _FLAG_SHUTDOWN )
            {
                socketStatus = SOCKETS_ECLOSED;
            }

            /* Check for timeout. Some ports return 0, some return EWOULDBLOCK. */
        } while( ( socketStatus == 0 ) || ( socketStatus == SOCKETS_EWOULDBLOCK ) );

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
        connectionFlags = xEventGroupGetBits( ( EventGroupHandle_t ) &( pNetworkConnection->connectionFlags ) );

        if( ( connectionFlags & _FLAG_CONNECTION_DESTROYED ) == _FLAG_CONNECTION_DESTROYED )
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
        /* Set the flag to indicate that the receive task has exited. */
        ( void ) xEventGroupSetBits( ( EventGroupHandle_t ) &( pNetworkConnection->connectionFlags ),
                                     _FLAG_RECEIVE_TASK_EXITED );
    }

    vTaskDelete( NULL );
}

/*-----------------------------------------------------------*/

/**
 * @brief Set up a secured TLS connection.
 *
 * @param[in] pAfrCredentials Credentials for the secured connection.
 * @param[in] tcpSocket An initialized socket to secure.
 * @param[in] pHostName Remote server name for SNI.
 * @param[in] hostnameLength The length of `pHostName`.
 *
 * @return #IOT_NETWORK_SUCCESS or #IOT_NETWORK_SYSTEM_ERROR.
 */
static IotNetworkError_t _tlsSetup( const IotNetworkCredentials_t * pAfrCredentials,
                                    Socket_t tcpSocket,
                                    const char * pHostName,
                                    size_t hostnameLength )
{
    IOT_FUNCTION_ENTRY( IotNetworkError_t, IOT_NETWORK_SUCCESS );
    int32_t socketStatus = SOCKETS_ERROR_NONE;

    /* ALPN options for AWS IoT. */
    const char * ppcALPNProtos[] = { socketsAWS_IOT_ALPN_MQTT };

    /* Set secured option. */
    socketStatus = SOCKETS_SetSockOpt( tcpSocket,
                                       0,
                                       SOCKETS_SO_REQUIRE_TLS,
                                       NULL,
                                       0 );

    if( socketStatus != SOCKETS_ERROR_NONE )
    {
        IotLogError( "Failed to set secured option for new connection." );
        IOT_SET_AND_GOTO_CLEANUP( IOT_NETWORK_SYSTEM_ERROR );
    }

    /* Set ALPN option. */
    if( pAfrCredentials->pAlpnProtos != NULL )
    {
        socketStatus = SOCKETS_SetSockOpt( tcpSocket,
                                           0,
                                           SOCKETS_SO_ALPN_PROTOCOLS,
                                           ppcALPNProtos,
                                           sizeof( ppcALPNProtos ) / sizeof( ppcALPNProtos[ 0 ] ) );

        if( socketStatus != SOCKETS_ERROR_NONE )
        {
            IotLogError( "Failed to set ALPN option for new connection." );
            IOT_SET_AND_GOTO_CLEANUP( IOT_NETWORK_SYSTEM_ERROR );
        }
    }

    /* Set SNI option. */
    if( pAfrCredentials->disableSni == false )
    {
        socketStatus = SOCKETS_SetSockOpt( tcpSocket,
                                           0,
                                           SOCKETS_SO_SERVER_NAME_INDICATION,
                                           pHostName,
                                           hostnameLength + 1 );

        if( socketStatus != SOCKETS_ERROR_NONE )
        {
            IotLogError( "Failed to set SNI option for new connection." );
            IOT_SET_AND_GOTO_CLEANUP( IOT_NETWORK_SYSTEM_ERROR );
        }
    }

    /* Set custom server certificate. */
    if( pAfrCredentials->pRootCa != NULL )
    {
        socketStatus = SOCKETS_SetSockOpt( tcpSocket,
                                           0,
                                           SOCKETS_SO_TRUSTED_SERVER_CERTIFICATE,
                                           pAfrCredentials->pRootCa,
                                           pAfrCredentials->rootCaSize );

        if( socketStatus != SOCKETS_ERROR_NONE )
        {
            IotLogError( "Failed to set server certificate option for new connection." );
            IOT_SET_AND_GOTO_CLEANUP( IOT_NETWORK_SYSTEM_ERROR );
        }
    }

    IOT_FUNCTION_EXIT_NO_CLEANUP();
}

/*-----------------------------------------------------------*/

IotNetworkError_t IotNetworkAfr_Create( void * pConnectionInfo,
                                        void * pCredentialInfo,
                                        void ** pConnection )
{
    IOT_FUNCTION_ENTRY( IotNetworkError_t, IOT_NETWORK_SUCCESS );
    Socket_t tcpSocket = SOCKETS_INVALID_SOCKET;
    int32_t socketStatus = SOCKETS_ERROR_NONE;
    SocketsSockaddr_t serverAddress = { 0 };
    EventGroupHandle_t pConnectionFlags = NULL;
    SemaphoreHandle_t pConnectionMutex = NULL;
    const TickType_t receiveTimeout = pdMS_TO_TICKS( IOT_NETWORK_SOCKET_POLL_MS );
    _networkConnection_t * pNewNetworkConnection = NULL;

    /* Cast function parameters to correct types. */
    const IotNetworkServerInfo_t * pServerInfo = pConnectionInfo;
    const IotNetworkCredentials_t * pAfrCredentials = pCredentialInfo;
    _networkConnection_t ** pNetworkConnection = ( _networkConnection_t ** ) pConnection;

    /* Check host name length against the maximum length allowed by Secure
     * Sockets. */
    const size_t hostnameLength = strlen( pServerInfo->pHostName );

    if( hostnameLength > ( size_t ) securesocketsMAX_DNS_NAME_LENGTH )
    {
        IotLogError( "Host name length exceeds %d, which is the maximum allowed.",
                     securesocketsMAX_DNS_NAME_LENGTH );
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
    tcpSocket = SOCKETS_Socket( SOCKETS_AF_INET,
                                SOCKETS_SOCK_STREAM,
                                SOCKETS_IPPROTO_TCP );

    if( tcpSocket == SOCKETS_INVALID_SOCKET )
    {
        IotLogError( "Failed to create new socket." );
        IOT_SET_AND_GOTO_CLEANUP( IOT_NETWORK_SYSTEM_ERROR );
    }

    /* Set up connection encryption if credentials are provided. */
    if( pAfrCredentials != NULL )
    {
        status = _tlsSetup( pAfrCredentials, tcpSocket, pServerInfo->pHostName, hostnameLength );

        if( status != IOT_NETWORK_SUCCESS )
        {
            IOT_GOTO_CLEANUP();
        }
    }

    /* Establish connection. */
    serverAddress.ucSocketDomain = SOCKETS_AF_INET;
    serverAddress.usPort = SOCKETS_htons( pServerInfo->port );
    serverAddress.ulAddress = SOCKETS_GetHostByName( pServerInfo->pHostName );

    /* Check for errors from DNS lookup. */
    if( serverAddress.ulAddress == 0 )
    {
        IotLogError( "Failed to resolve %s.", pServerInfo->pHostName );
        IOT_SET_AND_GOTO_CLEANUP( IOT_NETWORK_SYSTEM_ERROR );
    }

    socketStatus = SOCKETS_Connect( tcpSocket,
                                    &serverAddress,
                                    sizeof( SocketsSockaddr_t ) );

    if( socketStatus != SOCKETS_ERROR_NONE )
    {
        IotLogError( "Failed to establish new connection." );
        IOT_SET_AND_GOTO_CLEANUP( IOT_NETWORK_SYSTEM_ERROR );
    }

    /* Set a long timeout for receive. */
    socketStatus = SOCKETS_SetSockOpt( tcpSocket,
                                       0,
                                       SOCKETS_SO_RCVTIMEO,
                                       &receiveTimeout,
                                       sizeof( TickType_t ) );

    if( socketStatus != SOCKETS_ERROR_NONE )
    {
        IotLogError( "Failed to set socket receive timeout." );
        IOT_SET_AND_GOTO_CLEANUP( IOT_NETWORK_SYSTEM_ERROR );
    }

    IOT_FUNCTION_CLEANUP_BEGIN();

    /* Clean up on failure. */
    if( status != IOT_NETWORK_SUCCESS )
    {
        if( tcpSocket != SOCKETS_INVALID_SOCKET )
        {
            SOCKETS_Close( tcpSocket );
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

        /* Create the connection event flags and mutex. */
        pConnectionFlags = xEventGroupCreateStatic( &( pNewNetworkConnection->connectionFlags ) );
        pConnectionMutex = xSemaphoreCreateMutexStatic( &( pNewNetworkConnection->socketMutex ) );

        /* Static event flags and mutex creation should never fail. The handles
         * should point inside the connection object. */
        configASSERT( pConnectionFlags == ( EventGroupHandle_t ) &( pNewNetworkConnection->connectionFlags ) );
        configASSERT( pConnectionMutex == ( SemaphoreHandle_t ) &( pNewNetworkConnection->socketMutex ) );

        /* Set the output parameter. */
        *pNetworkConnection = pNewNetworkConnection;
    }

    IOT_FUNCTION_CLEANUP_END();
}

/*-----------------------------------------------------------*/

IotNetworkError_t IotNetworkAfr_SetReceiveCallback( void * pConnection,
                                                    IotNetworkReceiveCallback_t receiveCallback,
                                                    void * pContext )
{
    IotNetworkError_t status = IOT_NETWORK_SUCCESS;

    /* Cast network connection to the correct type. */
    _networkConnection_t * pNetworkConnection = ( _networkConnection_t * ) pConnection;

    /* Set the receive callback and context. */
    pNetworkConnection->receiveCallback = receiveCallback;
    pNetworkConnection->pReceiveContext = pContext;

    /* No flags should be set. */
    configASSERT( xEventGroupGetBits( ( EventGroupHandle_t ) &( pNetworkConnection->connectionFlags ) ) == 0 );

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

size_t IotNetworkAfr_Send( void * pConnection,
                           const uint8_t * pMessage,
                           size_t messageLength )
{
    size_t bytesSent = 0;
    int32_t socketStatus = SOCKETS_ERROR_NONE;

    /* Cast network connection to the correct type. */
    _networkConnection_t * pNetworkConnection = ( _networkConnection_t * ) pConnection;

    /* Only one thread at a time may send on the connection. Lock the socket
     * mutex to prevent other threads from sending. */
    if( xSemaphoreTake( ( QueueHandle_t ) &( pNetworkConnection->socketMutex ),
                        portMAX_DELAY ) == pdTRUE )
    {
        socketStatus = SOCKETS_Send( pNetworkConnection->socket,
                                     pMessage,
                                     messageLength,
                                     0 );

        if( socketStatus > 0 )
        {
            bytesSent = ( size_t ) socketStatus;
        }

        xSemaphoreGive( ( QueueHandle_t ) &( pNetworkConnection->socketMutex ) );
    }

    return bytesSent;
}

/*-----------------------------------------------------------*/

size_t IotNetworkAfr_Receive( void * pConnection,
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
        socketStatus = SOCKETS_Recv( pNetworkConnection->socket,
                                     pBuffer + bytesReceived,
                                     bytesRemaining,
                                     0 );

        if( socketStatus == SOCKETS_EWOULDBLOCK )
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

IotNetworkError_t IotNetworkAfr_Close( void * pConnection )
{
    int32_t socketStatus = SOCKETS_ERROR_NONE;

    /* Cast network connection to the correct type. */
    _networkConnection_t * pNetworkConnection = ( _networkConnection_t * ) pConnection;

    /* Call Secure Sockets shutdown function to close connection. */
    socketStatus = SOCKETS_Shutdown( pNetworkConnection->socket,
                                     SOCKETS_SHUT_RDWR );

    if( socketStatus != SOCKETS_ERROR_NONE )
    {
        IotLogWarn( "Failed to close connection." );
    }

    /* Set the shutdown flag. */
    ( void ) xEventGroupSetBits( ( EventGroupHandle_t ) &( pNetworkConnection->connectionFlags ),
                                 _FLAG_SHUTDOWN );

    return IOT_NETWORK_SUCCESS;
}

/*-----------------------------------------------------------*/

IotNetworkError_t IotNetworkAfr_Destroy( void * pConnection )
{
    /* Cast network connection to the correct type. */
    _networkConnection_t * pNetworkConnection = ( _networkConnection_t * ) pConnection;

    /* Check if this function is being called from the receive task. */
    if( xTaskGetCurrentTaskHandle() == pNetworkConnection->receiveTask )
    {
        /* Set the flag specifying that the connection is destroyed. */
        ( void ) xEventGroupSetBits( ( EventGroupHandle_t ) &( pNetworkConnection->connectionFlags ),
                                     _FLAG_CONNECTION_DESTROYED );
    }
    else
    {
        /* If a receive task was created, wait for it to exit. */
        if( pNetworkConnection->receiveTask != NULL )
        {
            ( void ) xEventGroupWaitBits( ( EventGroupHandle_t ) &( pNetworkConnection->connectionFlags ),
                                          _FLAG_RECEIVE_TASK_EXITED,
                                          pdTRUE,
                                          pdTRUE,
                                          portMAX_DELAY );
        }

        _destroyConnection( pNetworkConnection );
    }

    return IOT_NETWORK_SUCCESS;
}

/*-----------------------------------------------------------*/
