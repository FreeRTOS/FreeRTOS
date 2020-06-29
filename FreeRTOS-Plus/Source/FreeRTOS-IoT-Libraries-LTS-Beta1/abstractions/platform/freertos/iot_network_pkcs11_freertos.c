/*
 * FreeRTOS Platform V1.1.1
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 *
 * http://aws.amazon.com/freertos
 * http://www.FreeRTOS.org
 */

/**
 * @file iot_network_freertos.c
 * @brief Implementation of the network-related functions from
 * iot_network_freertos.h for FreeRTOS+TCP sockets.
 */

/* The config header is always included first. */
#include "iot_config.h"

/* Standard includes. */
#include <string.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "atomic.h"
#include "semphr.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_Sockets.h"

/* FreeRTOS-IoT-Libraries-LTS-Beta1 includes. */
#include "iot_error.h"
#include "platform/iot_network_freertos.h"
#include "mbedtls/threading.h"
#include "iot_pkcs11.h"
#include "iot_tls.h"


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

/* Provide a default value for socket timeout and network task parameters. */
#ifndef IOT_NETWORK_SOCKET_TIMEOUT_MS
    #define IOT_NETWORK_SOCKET_TIMEOUT_MS    ( 5000 )
#endif
#ifndef IOT_NETWORK_TASK_STACK_SIZE
    #define IOT_NETWORK_TASK_STACK_SIZE      ( 2048 )
#endif
#ifndef IOT_NETWORK_TASK_PRIORITY
    #define IOT_NETWORK_TASK_PRIORITY        ( tskIDLE_PRIORITY )
#endif

/* Maximum number of simultaneous socket receive callbacks. */
#ifndef IOT_NETWORK_MAX_RECEIVE_CALLBACKS
    #define IOT_NETWORK_MAX_RECEIVE_CALLBACKS    ( 2 )
#endif

/**
 * @brief Maximum length of a DNS name.
 *
 * Per https://tools.ietf.org/html/rfc1035, 253 is the maximum string length
 * of a DNS name.
 */
#define MAX_DNS_NAME_LENGTH    ( 253 )
/*-----------------------------------------------------------*/

/**
 * @brief Internal network context.
 */
typedef struct _networkConnection
{
    Socket_t socket;               /**< @brief FreeRTOS+TCP sockets handle. */
    SemaphoreHandle_t socketMutex; /**< @brief Prevents concurrent threads from
                                    * using a socket. */
    StaticSemaphore_t
        socketMutexStorage;        /**< @brief Storage space for socketMutex. */
    IotNetworkReceiveCallback_t
        receiveCallback;           /**< @brief Network receive callback, if any. */
    void * pReceiveContext;        /**< @brief The context for the receive callback. */
    void * pvTLSContext;           /**< @brief TLS handle. */
    BaseType_t secured;            /**< @brief Flag that marks a connection as secured. */
} _networkConnection_t;
/*-----------------------------------------------------------*/

/**
 * @brief Handle of the network task.
 */
static TaskHandle_t _networkTaskHandle;

/**
 * @brief Socket set for the network task.
 */
static SocketSet_t _socketSet;

/**
 * @brief Connections in _socketSet.
 */
static _networkConnection_t * _connections[ IOT_NETWORK_MAX_RECEIVE_CALLBACKS ];

/**
 * @brief An #IotNetworkInterface_t that uses the functions in this file.
 */
const IotNetworkInterface_t IotNetworkFreeRTOS =
{
    .create             = IotNetworkFreeRTOS_Create,
    .setReceiveCallback = IotNetworkFreeRTOS_SetReceiveCallback,
    .send               = IotNetworkFreeRTOS_Send,
    .receive            = IotNetworkFreeRTOS_Receive,
    .receiveUpto        = IotNetworkFreeRTOS_ReceiveUpto,
    .close              = IotNetworkFreeRTOS_Close,
    .destroy            = IotNetworkFreeRTOS_Destroy
};
/*-----------------------------------------------------------*/

/**
 * @brief Set up TLS on a TCP connection.
 *
 * @param[in] pNetworkConnection An established TCP connection.
 * @param[in] pServerName Remote host name, used for server name indication.
 * @param[in] pCredentials TLS setup parameters.
 *
 * @return #IOT_NETWORK_SUCCESS, #IOT_NETWORK_FAILURE, #IOT_NETWORK_NO_MEMORY,
 * or #IOT_NETWORK_SYSTEM_ERROR.
 */
static IotNetworkError_t _tlsSetup( _networkConnection_t * pNetworkConnection,
                                    const char * pServerName,
                                    IotNetworkCredentials_t pCredentials )
{
    int mbedtlsError = 0;

    TLSParams_t tlsParams = { 0 };

    tlsParams.ulSize = sizeof( tlsParams );
    tlsParams.pcDestination = pServerName;
    tlsParams.pcServerCertificate = pCredentials->pRootCa;
    tlsParams.ulServerCertificateLength = pCredentials->rootCaSize;
    tlsParams.ppcAlpnProtocols = ( const char ** ) pCredentials->pAlpnProtos;
    tlsParams.ulAlpnProtocolsCount = 0;
    tlsParams.pxNetworkSend = mbedtls_platform_send;
    tlsParams.pxNetworkRecv = mbedtls_platform_recv;
    tlsParams.pvCallerContext = pNetworkConnection->socket;

    /* Initialize TLS context and underlying crypto libraries */
    mbedtlsError = TLS_Init( &pNetworkConnection->pvTLSContext, &tlsParams );

    if( mbedtlsError != CKR_OK )
    {
        IotLogError( "Failed to initialize TLS, error %d", mbedtlsError );
    }

    /* Attempt to establish a TLS connection. PKCS is used to acquire
     * credential objects. */
    mbedtlsError = TLS_Connect( pNetworkConnection->pvTLSContext );

    if( mbedtlsError == CKR_OK )
    {
        pNetworkConnection->secured = pdTRUE;
        IotLogInfo( "TLS Handshake sucecessful." );
    }
    else
    {
        IotLogError(
            "Failed to perform TLS handshake, error %d.", mbedtlsError );
        TLS_Cleanup( pNetworkConnection->pvTLSContext );
    }

    return mbedtlsError;
}
/*-----------------------------------------------------------*/

static void _networkTask( void * pvParameters )
{
    _networkConnection_t * pConnection = NULL;
    BaseType_t socketEvents = 0, i = 0, socketStatus = 0;
    SocketSet_t socketSet = pvParameters;

    while( true )
    {
        socketEvents =
            FreeRTOS_select( socketSet, IOT_NETWORK_SOCKET_TIMEOUT_MS );

        if( socketEvents > 0 )
        {
            for( i = 0; i < IOT_NETWORK_MAX_RECEIVE_CALLBACKS; i++ )
            {
                pConnection = _connections[ i ];

                if( pConnection != NULL )
                {
                    socketStatus =
                        FreeRTOS_FD_ISSET( pConnection->socket, socketSet );

                    if( socketStatus & eSELECT_READ )
                    {
                        /* A receive callback must be set; otherwise, select
                         * should not have returned this socket. */
                        configASSERT( pConnection->receiveCallback != NULL );

                        pConnection->receiveCallback(
                            pConnection, pConnection->pReceiveContext );
                    }
                }
            }
        }

        /* This task will receive a notification when cleanup is called. Exit
         * when cleanup is called. */
        if( ulTaskNotifyTake( pdTRUE, 0 ) != 0 )
        {
            break;
        }
    }

    FreeRTOS_DeleteSocketSet( socketSet );
    vTaskDelete( NULL );
}
/*-----------------------------------------------------------*/

IotNetworkError_t IotNetworkFreeRTOS_Init( void )
{
    IOT_FUNCTION_ENTRY( IotNetworkError_t, IOT_NETWORK_SUCCESS );

    /* Create socket set for network task. */
    _socketSet = FreeRTOS_CreateSocketSet();

    if( _socketSet == NULL )
    {
        IOT_SET_AND_GOTO_CLEANUP( IOT_NETWORK_FAILURE );
    }

    static StaticTask_t networkTask;
    static StackType_t networkTaskStack[ IOT_NETWORK_TASK_STACK_SIZE ];

    /* Create the network task. Since valid parameters are provided, this should
     * never fail. */
    _networkTaskHandle = xTaskCreateStatic(
        _networkTask, "Network", IOT_NETWORK_TASK_STACK_SIZE, _socketSet,
        IOT_NETWORK_TASK_PRIORITY, ( StackType_t * const ) &networkTaskStack,
        &networkTask );
    configASSERT( _networkTaskHandle != NULL );

    IotLogInfo( "Network successfully initialized." );

    IOT_FUNCTION_EXIT_NO_CLEANUP();
}
/*-----------------------------------------------------------*/

void IotNetworkFreeRTOS_Cleanup( void )
{
    xTaskNotifyGive( _networkTaskHandle );

    IotLogInfo( "Network cleanup done." );
}
/*-----------------------------------------------------------*/

IotNetworkError_t IotNetworkFreeRTOS_Create( IotNetworkServerInfo_t pServerInfo,
                                             IotNetworkCredentials_t pCredentialInfo,
                                             IotNetworkConnection_t * pConnection )
{
    IOT_FUNCTION_ENTRY( IotNetworkError_t, IOT_NETWORK_SUCCESS );
    Socket_t tcpSocket = FREERTOS_INVALID_SOCKET;
    BaseType_t socketStatus = 0;
    struct freertos_sockaddr serverAddress = { 0 };
    const TickType_t receiveTimeout =
        pdMS_TO_TICKS( IOT_NETWORK_SOCKET_TIMEOUT_MS );
    _networkConnection_t * pNewNetworkConnection = NULL;

    /* Credentials are not used if TLS is disabled. */
    ( void ) pCredentialInfo;

    /* Check host name length against the maximum length allowed. */
    const size_t hostnameLength = strlen( pServerInfo->pHostName );

    if( hostnameLength > ( size_t ) MAX_DNS_NAME_LENGTH )
    {
        IotLogError(
            "Host name length exceeds %d, which is the maximum allowed.",
            MAX_DNS_NAME_LENGTH );
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
    tcpSocket = FreeRTOS_socket(
        FREERTOS_AF_INET, FREERTOS_SOCK_STREAM, FREERTOS_IPPROTO_TCP );

    if( tcpSocket == FREERTOS_INVALID_SOCKET )
    {
        IotLogError( "Failed to create new socket." );
        IOT_SET_AND_GOTO_CLEANUP( IOT_NETWORK_SYSTEM_ERROR );
    }

    /* Set the timeout for receive. */
    socketStatus = FreeRTOS_setsockopt(
        tcpSocket, 0, FREERTOS_SO_RCVTIMEO, &receiveTimeout,
        sizeof( TickType_t ) );

    if( socketStatus != 0 )
    {
        IotLogError( "Failed to set socket receive timeout." );
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

    socketStatus =
        FreeRTOS_connect( tcpSocket, &serverAddress, sizeof( serverAddress ) );

    if( socketStatus != 0 )
    {
        IotLogError(
            "Failed to establish new connection. Socket status %d.",
            socketStatus );
        IOT_SET_AND_GOTO_CLEANUP( IOT_NETWORK_SYSTEM_ERROR );
    }

    /* Set the socket. */
    pNewNetworkConnection->socket = tcpSocket;
    /* Create the socket mutex. */
    pNewNetworkConnection->socketMutex = xSemaphoreCreateMutexStatic(
        &( pNewNetworkConnection->socketMutexStorage ) );

    /* Set up TLS if credentials are provided. */
    if( pCredentialInfo != NULL )
    {
        status = _tlsSetup(
            pNewNetworkConnection, pServerInfo->pHostName, pCredentialInfo );
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
        /* Set the output parameter. */
        *pConnection = pNewNetworkConnection;

        IotLogInfo(
            "(Network connection %p) Connection to %s established.",
            pNewNetworkConnection, pServerInfo->pHostName );
    }

    IOT_FUNCTION_CLEANUP_END();
}
/*-----------------------------------------------------------*/

IotNetworkError_t IotNetworkFreeRTOS_SetReceiveCallback( IotNetworkConnection_t pConnection,
                                                         IotNetworkReceiveCallback_t receiveCallback,
                                                         void * pContext )
{
    IotNetworkError_t status = IOT_NETWORK_SUCCESS;
    BaseType_t i = 0;

    /* Set the receive callback and context. */
    pConnection->receiveCallback = receiveCallback;
    pConnection->pReceiveContext = pContext;

    /* Add this connection to the list of connections that select should check.
     */
    for( i = 0; i < IOT_NETWORK_MAX_RECEIVE_CALLBACKS; i++ )
    {
        if( Atomic_CompareAndSwapPointers_p32(
                &_connections[ i ], pConnection, NULL )
            == 1 )
        {
            break;
        }
    }

    if( i == IOT_NETWORK_MAX_RECEIVE_CALLBACKS )
    {
        status = IOT_NETWORK_NO_MEMORY;
    }
    else
    {
        /* Add this socket to the socket set for the network task. */
        FreeRTOS_FD_SET( pConnection->socket, _socketSet, eSELECT_READ );
    }

    return status;
}
/*-----------------------------------------------------------*/

size_t IotNetworkFreeRTOS_Send( IotNetworkConnection_t pConnection,
                                const uint8_t * pMessage,
                                size_t messageLength )
{
    size_t bytesSent = 0;
    BaseType_t socketStatus = 0;

    /* Only one thread at a time may send on the connection. Lock the send
     * mutex to prevent other threads from sending. */
    if( xSemaphoreTake( pConnection->socketMutex, IOT_NETWORK_SOCKET_TIMEOUT_MS )
        == pdTRUE )
    {
        if( pConnection->secured == pdTRUE )
        {
            socketStatus =
                TLS_Send( pConnection->pvTLSContext, pMessage, messageLength );
        }
        else
        {
            IotLogError(
                "Attempted to send data over a TLS connection that is "
                "insecure." );
        }

        if( socketStatus > 0 )
        {
            bytesSent = ( size_t ) socketStatus;
        }
        else
        {
            IotLogError(
                "Failed to send data over TLS connection with error code %d.",
                socketStatus );
        }

        xSemaphoreGive( pConnection->socketMutex );
    }

    IotLogDebug(
        "(Network connection %p) Sent %lu bytes.", pConnection,
        ( unsigned long ) bytesSent );

    return bytesSent;
}
/*-----------------------------------------------------------*/

size_t IotNetworkFreeRTOS_Receive( IotNetworkConnection_t pConnection,
                                   uint8_t * pBuffer,
                                   size_t bytesRequested )
{
    BaseType_t socketStatus = 0;
    size_t bytesReceived = 0, bytesRemaining = bytesRequested;

    /* Block and wait for incoming data. */

    if( pConnection->secured == pdTRUE )
    {
        if( xSemaphoreTake(
                pConnection->socketMutex, IOT_NETWORK_SOCKET_TIMEOUT_MS )
            == pdTRUE )
        {
            socketStatus =
                TLS_Recv( pConnection->pvTLSContext, pBuffer, bytesRequested );

            if( socketStatus > 0 )
            {
                bytesReceived = ( size_t ) socketStatus;
            }
            else
            {
                IotLogError(
                    "Failed to recieve data over TLS connection with error "
                    "code "
                    "%d.",
                    socketStatus );
            }

            xSemaphoreGive( pConnection->socketMutex );
        }
    }
    else
    {
        IotLogError(
            "Attempted to send data over a TLS connection that is insecure." );
    }

    if( bytesReceived < bytesRequested )
    {
        IotLogWarn(
            "(Network connection %p) Receive requested %lu bytes, but %lu "
            "bytes received instead.",
            pConnection, ( unsigned long ) bytesRequested,
            ( unsigned long ) bytesReceived );
    }
    else
    {
        IotLogDebug(
            "(Network connection %p) Successfully received %lu bytes.",
            pConnection, ( unsigned long ) bytesRequested );
    }

    return bytesReceived;
}

/*-----------------------------------------------------------*/

size_t IotNetworkFreeRTOS_ReceiveUpto( IotNetworkConnection_t pConnection,
                                       uint8_t * pBuffer,
                                       size_t bufferSize )
{
    int32_t socketStatus = 0;
    size_t bytesReceived = 0;

    /* Caller should never pass a zero-length buffer. */
    configASSERT( bufferSize > 0 );

    if( pConnection->secured == pdTRUE )
    {
        if( xSemaphoreTake(
                pConnection->socketMutex, IOT_NETWORK_SOCKET_TIMEOUT_MS )
            == pdTRUE )
        {
            socketStatus =
                TLS_Recv( pConnection->pvTLSContext, pBuffer, bufferSize );
            bytesReceived = socketStatus;

            xSemaphoreGive( pConnection->socketMutex );
        }
        else
        {
            IotLogError( "Could not obtain the socket mutex." );
        }
    }
    else

    {
        IotLogError(
            "Attempted to send data over a TLS connection that is insecure." );
    }

    if( socketStatus <= 0 )
    {
        IotLogError( "Error %ld while receiving data.", ( long int ) socketStatus );
    }
    else
    {
        bytesReceived += ( size_t ) socketStatus;
    }

    IotLogDebug( "Received %lu bytes.", ( unsigned long ) bytesReceived );

    return bytesReceived;
}

/*-----------------------------------------------------------*/

IotNetworkError_t IotNetworkFreeRTOS_Close( IotNetworkConnection_t pConnection )
{
    BaseType_t socketStatus = 0, i = 0;


    /* Notify the peer that the TLS connection is being closed. */
    if( pConnection->secured == pdTRUE )
    {
        if( xSemaphoreTake(
                pConnection->socketMutex, IOT_NETWORK_SOCKET_TIMEOUT_MS )
            == pdTRUE )
        {
            /* Clean up memory used by TLS Connection. */
            TLS_Cleanup( pConnection->pvTLSContext );
            pConnection->pvTLSContext = NULL;

            xSemaphoreGive( pConnection->socketMutex );
        }
    }

    /* Call socket shutdown function to close connection. */
    socketStatus = FreeRTOS_shutdown( pConnection->socket, FREERTOS_SHUT_RDWR );

    if( socketStatus != 0 )
    {
        IotLogWarn(
            "(Network connection %p) Failed to close connection.", pConnection );
    }
    else
    {
        IotLogInfo( "(Network connection %p) Connection closed.", pConnection );
    }

    /* Remove this connection from Select's socket set (if present). */
    for( i = 0; i < IOT_NETWORK_MAX_RECEIVE_CALLBACKS; i++ )
    {
        if( Atomic_CompareAndSwapPointers_p32(
                &_connections[ i ], NULL, pConnection )
            == 1 )
        {
            FreeRTOS_FD_CLR( pConnection->socket, _socketSet, eSELECT_ALL );
        }
    }

    return IOT_NETWORK_SUCCESS;
}
/*-----------------------------------------------------------*/

IotNetworkError_t IotNetworkFreeRTOS_Destroy( IotNetworkConnection_t pConnection )
{
    FreeRTOS_closesocket( pConnection->socket );

    /* Free memory used by network connection. */
    vPortFree( pConnection );

    IotLogInfo( "(Network connection %p) Connection destroyed.", pConnection );

    return IOT_NETWORK_SUCCESS;
}
/*-----------------------------------------------------------*/
