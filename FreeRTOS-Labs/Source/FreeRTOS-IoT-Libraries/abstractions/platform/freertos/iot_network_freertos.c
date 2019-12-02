/*
 * Amazon FreeRTOS Platform V1.1.0
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
#include "atomic.h"
#include "semphr.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_Sockets.h"

/* FreeRTOS-IoT-Libraries includes. */
#include "iot_error.h"
#include "platform/iot_network_freertos.h"

#if ( IOT_NETWORK_ENABLE_TLS == 1 )
    /* mbed TLS includes. */
    #include "mbedtls/ctr_drbg.h"
    #include "mbedtls/entropy.h"
    #include "mbedtls/ssl.h"
    #include "mbedtls/threading.h"
    #include "mbedtls/x509.h"
#endif

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
    Socket_t socket;                             /**< @brief FreeRTOS+TCP sockets handle. */
    SemaphoreHandle_t socketMutex;               /**< @brief Prevents concurrent threads from using a socket. */
    StaticSemaphore_t socketMutexStorage;        /**< @brief Storage space for socketMutex. */
    IotNetworkReceiveCallback_t receiveCallback; /**< @brief Network receive callback, if any. */
    void * pReceiveContext;                      /**< @brief The context for the receive callback. */

    #if ( IOT_NETWORK_ENABLE_TLS == 1 )
        BaseType_t secured; /**< @brief Flag that marks a connection as secured. */

        /**
         * @brief Secured connection context. Valid if `secured` is `pdTRUE`.
         */
        struct
        {
            mbedtls_ssl_config config;            /**< @brief SSL connection configuration. */
            mbedtls_ssl_context context;          /**< @brief SSL connection context */
            mbedtls_x509_crt_profile certProfile; /**< @brief Certificate security profile for this connection. */
            mbedtls_x509_crt rootCa;              /**< @brief Root CA certificate context. */
            mbedtls_x509_crt clientCert;          /**< @brief Client certificate context. */
            mbedtls_pk_context privKey;           /**< @brief Client private key context. */
        } ssl;
    #endif /* if ( IOT_NETWORK_ENABLE_TLS == 1 ) */
} _networkConnection_t;
/*-----------------------------------------------------------*/

#if ( IOT_NETWORK_ENABLE_TLS == 1 )

/**
 * @brief mbed TLS entropy context for generation of random numbers.
 */
    static mbedtls_entropy_context _entropyContext;

/**
 * @brief mbed TLS CTR DRBG context for generation of random numbers.
 */
    static mbedtls_ctr_drbg_context _ctrDrgbContext;
#endif

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

#if ( IOT_NETWORK_ENABLE_TLS == 1 )

/**
 * @brief Initialize the mbed TLS structures in a network connection.
 *
 * @param[in] pNetworkConnection The network connection to initialize.
 */
    static void _sslContextInit( _networkConnection_t * pNetworkConnection )
    {
        mbedtls_ssl_config_init( &( pNetworkConnection->ssl.config ) );
        mbedtls_x509_crt_init( &( pNetworkConnection->ssl.rootCa ) );
        mbedtls_pk_init( &( pNetworkConnection->ssl.privKey ) );
        mbedtls_x509_crt_init( &( pNetworkConnection->ssl.clientCert ) );
        mbedtls_ssl_init( &( pNetworkConnection->ssl.context ) );
    }
/*-----------------------------------------------------------*/

/**
 * @brief Free the mbed TLS structures in a network connection.
 *
 * @param[in] pNetworkConnection The network connection with the contexts to free.
 */
    static void _sslContextFree( _networkConnection_t * pNetworkConnection )
    {
        mbedtls_ssl_free( &( pNetworkConnection->ssl.context ) );
        mbedtls_x509_crt_free( &( pNetworkConnection->ssl.rootCa ) );
        mbedtls_x509_crt_free( &( pNetworkConnection->ssl.clientCert ) );
        mbedtls_pk_free( &( pNetworkConnection->ssl.privKey ) );
        mbedtls_ssl_config_free( &( pNetworkConnection->ssl.config ) );
    }
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
        IOT_FUNCTION_ENTRY( IotNetworkError_t, IOT_NETWORK_SUCCESS );
        int mbedtlsError = 0;

        /* Initialize the mbed TLS context structures. */
        _sslContextInit( pNetworkConnection );

        mbedtlsError = mbedtls_ssl_config_defaults( &( pNetworkConnection->ssl.config ),
                                                    MBEDTLS_SSL_IS_CLIENT,
                                                    MBEDTLS_SSL_TRANSPORT_STREAM,
                                                    MBEDTLS_SSL_PRESET_DEFAULT );

        if( mbedtlsError != 0 )
        {
            IotLogError( "Failed to set default SSL configuration, error %d.", mbedtlsError );

            /* Per mbed TLS docs, mbedtls_ssl_config_defaults only fails on memory allocation. */
            IOT_SET_AND_GOTO_CLEANUP( IOT_NETWORK_NO_MEMORY );
        }

        /* Set up the certificate security profile, starting from the default value. */
        pNetworkConnection->ssl.certProfile = mbedtls_x509_crt_profile_default;

        /* test.mosquitto.org only provides a 1024-bit RSA certificate, which is
         * not acceptable by the default mbed TLS certificate security profile.
         * For the purposes of this demo, allow the use of 1024-bit RSA certificates.
         * This block should be removed otherwise. */
        if( strncmp( pServerName, "test.mosquitto.org", strlen( pServerName ) ) == 0 )
        {
            pNetworkConnection->ssl.certProfile.rsa_min_bitlen = 1024;
        }

        /* Set SSL authmode and the RNG context. */
        mbedtls_ssl_conf_authmode( &( pNetworkConnection->ssl.config ),
                                   MBEDTLS_SSL_VERIFY_REQUIRED );
        mbedtls_ssl_conf_rng( &( pNetworkConnection->ssl.config ),
                              mbedtls_ctr_drbg_random,
                              &_ctrDrgbContext );
        mbedtls_ssl_conf_cert_profile( &( pNetworkConnection->ssl.config ),
                                       &( pNetworkConnection->ssl.certProfile ) );

        /* Parse the server root CA certificate into the SSL context. */
        mbedtlsError = mbedtls_x509_crt_parse( &( pNetworkConnection->ssl.rootCa ),
                                               ( const unsigned char * ) pCredentials->pRootCa,
                                               pCredentials->rootCaSize );

        if( mbedtlsError != 0 )
        {
            IotLogError( "Failed to parse server root CA certificate, error %d.",
                         mbedtlsError );

            IOT_SET_AND_GOTO_CLEANUP( IOT_NETWORK_SYSTEM_ERROR );
        }

        mbedtls_ssl_conf_ca_chain( &( pNetworkConnection->ssl.config ),
                                   &( pNetworkConnection->ssl.rootCa ),
                                   NULL );

        if( ( pCredentials->pPrivateKey != NULL ) && ( pCredentials->pClientCert != NULL ) )
        {
            /* Setup the client private key. */
            mbedtlsError = mbedtls_pk_parse_key( &( pNetworkConnection->ssl.privKey ),
                                                 ( const unsigned char * ) pCredentials->pPrivateKey,
                                                 pCredentials->privateKeySize,
                                                 0,
                                                 0 );

            if( mbedtlsError != 0 )
            {
                IotLogError( "Failed to parse client certificate, error %d.",
                             mbedtlsError );

                IOT_SET_AND_GOTO_CLEANUP( IOT_NETWORK_SYSTEM_ERROR );
            }

            /* Setup the client certificate. */
            mbedtlsError = mbedtls_x509_crt_parse( &( pNetworkConnection->ssl.clientCert ),
                                                   ( const unsigned char * ) pCredentials->pClientCert,
                                                   pCredentials->clientCertSize );

            if( mbedtlsError != 0 )
            {
                IotLogError( "Failed to parse the client private key, error %d.",
                             mbedtlsError );

                IOT_SET_AND_GOTO_CLEANUP( IOT_NETWORK_SYSTEM_ERROR );
            }

            mbedtls_ssl_conf_own_cert( &( pNetworkConnection->ssl.config ),
                                       &( pNetworkConnection->ssl.clientCert ),
                                       &( pNetworkConnection->ssl.privKey ) );
        }

        /* Initialize the mbed TLS secured connection context. */
        mbedtlsError = mbedtls_ssl_setup( &( pNetworkConnection->ssl.context ),
                                          &( pNetworkConnection->ssl.config ) );

        if( mbedtlsError != 0 )
        {
            IotLogError( "Failed to set up mbed TLS SSL context, error %d.",
                         mbedtlsError );

            IOT_SET_AND_GOTO_CLEANUP( IOT_NETWORK_SYSTEM_ERROR );
        }

        /* Set the underlying IO for the TLS connection. */
        mbedtls_ssl_set_bio( &( pNetworkConnection->ssl.context ),
                             pNetworkConnection->socket,
                             mbedtls_platform_send,
                             mbedtls_platform_recv,
                             NULL );

        /* Enable SNI if requested. */
        if( pCredentials->disableSni == false )
        {
            mbedtlsError = mbedtls_ssl_set_hostname( &( pNetworkConnection->ssl.context ),
                                                     pServerName );

            if( mbedtlsError != 0 )
            {
                IotLogError( "Failed to set server name, error %d.", mbedtlsError );

                IOT_SET_AND_GOTO_CLEANUP( IOT_NETWORK_SYSTEM_ERROR );
            }
        }

        /* Perform the TLS handshake. */
        do
        {
            mbedtlsError = mbedtls_ssl_handshake( &( pNetworkConnection->ssl.context ) );
        } while( ( mbedtlsError == MBEDTLS_ERR_SSL_WANT_READ ) ||
                 ( mbedtlsError == MBEDTLS_ERR_SSL_WANT_WRITE ) );

        if( mbedtlsError != 0 )
        {
            IotLogError( "Failed to perform TLS handshake, error %d.", mbedtlsError );

            IOT_SET_AND_GOTO_CLEANUP( IOT_NETWORK_FAILURE );
        }

        /* Clean up on error. */
        IOT_FUNCTION_CLEANUP_BEGIN();

        if( status != IOT_NETWORK_SUCCESS )
        {
            _sslContextFree( pNetworkConnection );
        }
        else
        {
            pNetworkConnection->secured = pdTRUE;

            IotLogInfo( "(Network connection %p) TLS handshake successful.",
                        pNetworkConnection );
        }

        IOT_FUNCTION_CLEANUP_END();
    }
#endif /* if ( IOT_NETWORK_ENABLE_TLS == 1 ) */
/*-----------------------------------------------------------*/

static void _networkTask( void * pvParameters )
{
    _networkConnection_t * pConnection = NULL;
    BaseType_t socketEvents = 0, i = 0, socketStatus = 0;
    SocketSet_t socketSet = pvParameters;

    while( true )
    {
        socketEvents = FreeRTOS_select( socketSet, IOT_NETWORK_SOCKET_TIMEOUT_MS );

        if( socketEvents > 0 )
        {
            for( i = 0; i < IOT_NETWORK_MAX_RECEIVE_CALLBACKS; i++ )
            {
                pConnection = _connections[ i ];

                if( pConnection != NULL )
                {
                    socketStatus = FreeRTOS_FD_ISSET( pConnection->socket, socketSet );

                    if( socketStatus & eSELECT_READ )
                    {
                        /* A receive callback must be set; otherwise, select should not
                         * have returned this socket. */
                        configASSERT( pConnection->receiveCallback != NULL );

                        pConnection->receiveCallback( pConnection,
                                                      pConnection->pReceiveContext );
                    }
                }
            }
        }

        /* This task will receive a notification when cleanup is called. Exit when
         * cleanup is called. */
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

    #if ( IOT_NETWORK_ENABLE_TLS == 1 )
        int mbedtlsError = 0;

        /* Set the mutex functions for mbed TLS thread safety. */
        mbedtls_threading_set_alt( mbedtls_platform_mutex_init,
                                   mbedtls_platform_mutex_free,
                                   mbedtls_platform_mutex_lock,
                                   mbedtls_platform_mutex_unlock );

        /* Initialize contexts for random number generation. */
        mbedtls_entropy_init( &_entropyContext );
        mbedtls_ctr_drbg_init( &_ctrDrgbContext );

        /* Add a strong entropy source. At least one is required. */
        mbedtlsError = mbedtls_entropy_add_source( &_entropyContext,
                                                   mbedtls_platform_entropy_poll,
                                                   NULL,
                                                   32,
                                                   MBEDTLS_ENTROPY_SOURCE_STRONG );

        if( mbedtlsError != 0 )
        {
            IotLogError( "Failed to add entropy source, error %d.", mbedtlsError );

            IOT_SET_AND_GOTO_CLEANUP( IOT_NETWORK_FAILURE );
        }

        /* Seed the random number generator. */
        mbedtlsError = mbedtls_ctr_drbg_seed( &_ctrDrgbContext,
                                              mbedtls_entropy_func,
                                              &_entropyContext,
                                              NULL,
                                              0 );

        if( mbedtlsError != 0 )
        {
            IotLogError( "Failed to seed PRNG, error %d.", mbedtlsError );

            IOT_SET_AND_GOTO_CLEANUP( IOT_NETWORK_FAILURE );
        }
    #endif /* if ( IOT_NETWORK_ENABLE_TLS == 1 ) */

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
    _networkTaskHandle = xTaskCreateStatic( _networkTask,
                                            "Network",
                                            IOT_NETWORK_TASK_STACK_SIZE,
                                            _socketSet,
                                            IOT_NETWORK_TASK_PRIORITY,
                                            ( StackType_t * const ) &networkTaskStack,
                                            &networkTask );
    configASSERT( _networkTaskHandle != NULL );

    IotLogInfo( "Network successfully initialized." );

    IOT_FUNCTION_EXIT_NO_CLEANUP();
}
/*-----------------------------------------------------------*/

void IotNetworkFreeRTOS_Cleanup( void )
{
    #if ( IOT_NETWORK_ENABLE_TLS == 1 )
        /* Free the contexts for random number generation. */
        mbedtls_ctr_drbg_free( &_ctrDrgbContext );
        mbedtls_entropy_free( &_entropyContext );

        /* Clear the mutex functions for mbed TLS thread safety. */
        mbedtls_threading_free_alt();
    #endif

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
    const TickType_t receiveTimeout = pdMS_TO_TICKS( IOT_NETWORK_SOCKET_TIMEOUT_MS );
    _networkConnection_t * pNewNetworkConnection = NULL;

    /* Credentials are not used if TLS is disabled. */
    ( void ) pCredentialInfo;

    /* Check host name length against the maximum length allowed. */
    const size_t hostnameLength = strlen( pServerInfo->pHostName );

    if( hostnameLength > ( size_t ) MAX_DNS_NAME_LENGTH )
    {
        IotLogError( "Host name length exceeds %d, which is the maximum allowed.",
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
    tcpSocket = FreeRTOS_socket( FREERTOS_AF_INET,
                                 FREERTOS_SOCK_STREAM,
                                 FREERTOS_IPPROTO_TCP );

    if( tcpSocket == FREERTOS_INVALID_SOCKET )
    {
        IotLogError( "Failed to create new socket." );
        IOT_SET_AND_GOTO_CLEANUP( IOT_NETWORK_SYSTEM_ERROR );
    }

    /* Set the timeout for receive. */
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

    socketStatus = FreeRTOS_connect( tcpSocket,
                                     &serverAddress,
                                     sizeof( serverAddress ) );

    if( socketStatus != 0 )
    {
        IotLogError( "Failed to establish new connection. Socket status %d.", socketStatus );
        IOT_SET_AND_GOTO_CLEANUP( IOT_NETWORK_SYSTEM_ERROR );
    }

    /* Set the socket. */
    pNewNetworkConnection->socket = tcpSocket;

    #if ( IOT_NETWORK_ENABLE_TLS == 1 )
        /* Set up TLS if credentials are provided. */
        if( pCredentialInfo != NULL )
        {
            status = _tlsSetup( pNewNetworkConnection,
                                pServerInfo->pHostName,
                                pCredentialInfo );
        }
    #endif

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
        /* Create the socket mutex. */
        pNewNetworkConnection->socketMutex = xSemaphoreCreateMutexStatic( &( pNewNetworkConnection->socketMutexStorage ) );

        /* Set the output parameter. */
        *pConnection = pNewNetworkConnection;

        IotLogInfo( "(Network connection %p) Connection to %s established.",
                    pNewNetworkConnection,
                    pServerInfo->pHostName );
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

    /* Add this connection to the list of connections that select should check. */
    for( i = 0; i < IOT_NETWORK_MAX_RECEIVE_CALLBACKS; i++ )
    {
        if( Atomic_CompareAndSwapPointers_p32( &_connections[ i ],
                                               pConnection,
                                               NULL ) == 1 )
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
        FreeRTOS_FD_SET( pConnection->socket,
                         _socketSet,
                         eSELECT_READ );
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
    if( xSemaphoreTake( pConnection->socketMutex,
                        IOT_NETWORK_SOCKET_TIMEOUT_MS ) == pdTRUE )
    {
        #if ( IOT_NETWORK_ENABLE_TLS == 1 )
            if( pConnection->secured == pdTRUE )
            {
                while( bytesSent < messageLength )
                {
                    socketStatus = ( BaseType_t ) mbedtls_ssl_write( &( pConnection->ssl.context ),
                                                                     pMessage + bytesSent,
                                                                     messageLength - bytesSent );

                    if( ( socketStatus == ( BaseType_t ) MBEDTLS_ERR_SSL_WANT_WRITE ) ||
                        ( socketStatus == ( BaseType_t ) MBEDTLS_ERR_SSL_WANT_READ ) )
                    {
                        /* Try again for WANT_WRITE and WANT_READ errors. */
                        continue;
                    }
                    else if( socketStatus < 0 )
                    {
                        /* Exit on other errors. */
                        break;
                    }
                    else
                    {
                        bytesSent += ( size_t ) socketStatus;
                        configASSERT( bytesSent <= messageLength );
                    }
                }
            }
            else
        #endif /* if ( IOT_NETWORK_ENABLE_TLS == 1 ) */
        {
            socketStatus = FreeRTOS_send( pConnection->socket,
                                          pMessage,
                                          messageLength,
                                          0 );
        }

        if( socketStatus > 0 )
        {
            bytesSent = ( size_t ) socketStatus;
        }

        xSemaphoreGive( pConnection->socketMutex );
    }

    IotLogDebug( "(Network connection %p) Sent %lu bytes.",
                 pConnection,
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
    while( bytesRemaining > 0 )
    {
        #if ( IOT_NETWORK_ENABLE_TLS == 1 )
            if( pConnection->secured == pdTRUE )
            {
                if( xSemaphoreTake( pConnection->socketMutex,
                                    IOT_NETWORK_SOCKET_TIMEOUT_MS ) == pdTRUE )
                {
                    socketStatus = ( BaseType_t ) mbedtls_ssl_read( &( pConnection->ssl.context ),
                                                                    pBuffer + bytesReceived,
                                                                    bytesRequested - bytesReceived );

                    xSemaphoreGive( pConnection->socketMutex );

                    if( ( socketStatus == ( BaseType_t ) MBEDTLS_ERR_SSL_WANT_READ ) ||
                        ( socketStatus == ( BaseType_t ) MBEDTLS_ERR_SSL_WANT_WRITE ) )
                    {
                        /* Try again for WANT_WRITE and WANT_READ errors. */
                        continue;
                    }
                }
                else
                {
                    /* Could not obtain socket mutex, exit. */
                    break;
                }
            }
            else
        #endif /* if ( IOT_NETWORK_ENABLE_TLS == 1 ) */
        {
            socketStatus = FreeRTOS_recv( pConnection->socket,
                                          pBuffer + bytesReceived,
                                          bytesRemaining,
                                          0 );

            if( socketStatus == FREERTOS_EWOULDBLOCK )
            {
                /* The return value EWOULDBLOCK means no data was received within
                 * the socket timeout. Ignore it and try again. */
                continue;
            }
        }

        if( socketStatus < 0 )
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
        IotLogWarn( "(Network connection %p) Receive requested %lu bytes, but %lu bytes received instead.",
                    pConnection,
                    ( unsigned long ) bytesRequested,
                    ( unsigned long ) bytesReceived );
    }
    else
    {
        IotLogDebug( "(Network connection %p) Successfully received %lu bytes.",
                     pConnection,
                     ( unsigned long ) bytesRequested );
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

    #if ( IOT_NETWORK_ENABLE_TLS == 1 )
        if( pConnection->secured == pdTRUE )
        {
            if( xSemaphoreTake( pConnection->socketMutex,
                                IOT_NETWORK_SOCKET_TIMEOUT_MS ) == pdTRUE )
            {
                do
                {
                    socketStatus = ( BaseType_t ) mbedtls_ssl_read( &( pConnection->ssl.context ),
                                                                    pBuffer + bytesReceived,
                                                                    bufferSize - bytesReceived );
                } while( ( socketStatus == ( BaseType_t ) MBEDTLS_ERR_SSL_WANT_READ ) ||
                         ( socketStatus == ( BaseType_t ) MBEDTLS_ERR_SSL_WANT_WRITE ) );

                xSemaphoreGive( pConnection->socketMutex );
            }
            else
            {
                IotLogError( "Could not obtain the socket mutex." );
            }
        }
        else
    #endif /* if ( IOT_NETWORK_ENABLE_TLS == 1 ) */
    {
        socketStatus = FreeRTOS_recv( pConnection->socket,
                                      pBuffer + bytesReceived,
                                      bufferSize - bytesReceived,
                                      0 );
    }

    if( socketStatus <= 0 )
    {
        IotLogError( "Error %ld while receiving data.", ( long int ) socketStatus );
    }
    else
    {
        bytesReceived += ( size_t ) socketStatus;
    }

    IotLogDebug( "Received %lu bytes.",
                 ( unsigned long ) bytesReceived );

    return bytesReceived;
}

/*-----------------------------------------------------------*/

IotNetworkError_t IotNetworkFreeRTOS_Close( IotNetworkConnection_t pConnection )
{
    BaseType_t socketStatus = 0, i = 0;

    #if ( IOT_NETWORK_ENABLE_TLS == 1 )
        /* Notify the peer that the TLS connection is being closed. */
        if( pConnection->secured == pdTRUE )
        {
            if( xSemaphoreTake( pConnection->socketMutex,
                                IOT_NETWORK_SOCKET_TIMEOUT_MS ) == pdTRUE )
            {
                socketStatus = ( BaseType_t ) mbedtls_ssl_close_notify( &( pConnection->ssl.context ) );

                /* Ignore the WANT_READ and WANT_WRITE return values. */
                if( ( socketStatus != ( BaseType_t ) MBEDTLS_ERR_SSL_WANT_READ ) &&
                    ( socketStatus != ( BaseType_t ) MBEDTLS_ERR_SSL_WANT_WRITE ) )
                {
                    if( socketStatus == 0 )
                    {
                        IotLogInfo( "(Network connection %p) TLS close-notify sent.",
                                    pConnection );
                    }
                    else
                    {
                        IotLogWarn( "(Network connection %p) Failed to send TLS close-notify, error %d.",
                                    pConnection,
                                    socketStatus );
                    }
                }

                xSemaphoreGive( pConnection->socketMutex );
            }
        }
    #endif /* if ( IOT_NETWORK_ENABLE_TLS == 1 ) */

    /* Call socket shutdown function to close connection. */
    socketStatus = FreeRTOS_shutdown( pConnection->socket,
                                      FREERTOS_SHUT_RDWR );

    if( socketStatus != 0 )
    {
        IotLogWarn( "(Network connection %p) Failed to close connection.",
                    pConnection );
    }
    else
    {
        IotLogInfo( "(Network connection %p) Connection closed.",
                    pConnection );
    }

    /* Remove this connection from Select's socket set (if present). */
    for( i = 0; i < IOT_NETWORK_MAX_RECEIVE_CALLBACKS; i++ )
    {
        if( Atomic_CompareAndSwapPointers_p32( &_connections[ i ], NULL, pConnection ) == 1 )
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

    #if ( IOT_NETWORK_ENABLE_TLS == 1 )
        /* Free mbed TLS contexts. */
        if( pConnection->secured == pdTRUE )
        {
            _sslContextFree( pConnection );
        }
    #endif

    /* Free memory used by network connection. */
    vPortFree( pConnection );

    IotLogInfo( "(Network connection %p) Connection destroyed.",
                pConnection );

    return IOT_NETWORK_SUCCESS;
}
/*-----------------------------------------------------------*/
