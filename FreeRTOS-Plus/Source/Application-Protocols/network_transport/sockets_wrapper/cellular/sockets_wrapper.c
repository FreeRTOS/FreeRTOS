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

/* Standard includes. */
#include <stdio.h>
#include <string.h>
#include <stdlib.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "event_groups.h"

/* Sockets wrapper includes. */
#include "sockets_wrapper.h"

/* FreeRTOS Cellular Library api includes. */
#include "cellular_config.h"
#include "cellular_config_defaults.h"
#include "cellular_api.h"

/* Configure logs for the functions in this file. */
#include "logging_levels.h"
#ifndef LIBRARY_LOG_NAME
    #define LIBRARY_LOG_NAME     "CELLULAR_SOCKETS"
#endif
#ifndef LIBRARY_LOG_LEVEL
    #define LIBRARY_LOG_LEVEL    LOG_INFO
#endif
#include "logging_stack.h"

/*-----------------------------------------------------------*/

/* Cellular socket wrapper needs application provide the cellular handle and pdn context id. */
/* User of cellular socket wrapper should provide this variable. */
/* coverity[misra_c_2012_rule_8_6_violation] */
extern CellularHandle_t CellularHandle;

/* User of cellular socket wrapper should provide this variable. */
/* coverity[misra_c_2012_rule_8_6_violation] */
extern uint8_t CellularSocketPdnContextId;

/*-----------------------------------------------------------*/

/* Windows simulator implementation. */
#if defined( _WIN32 ) || defined( _WIN64 )
    #define strtok_r                         strtok_s
#endif

#define CELLULAR_SOCKET_OPEN_FLAG            ( 1UL << 0 )
#define CELLULAR_SOCKET_CONNECT_FLAG         ( 1UL << 1 )

#define SOCKET_DATA_RECEIVED_CALLBACK_BIT    ( 0x00000001U )
#define SOCKET_OPEN_CALLBACK_BIT             ( 0x00000002U )
#define SOCKET_OPEN_FAILED_CALLBACK_BIT      ( 0x00000004U )
#define SOCKET_CLOSE_CALLBACK_BIT            ( 0x00000008U )

/* Ticks MS conversion macros. */
#define TICKS_TO_MS( xTicks )    ( ( ( xTicks ) * 1000U ) / ( ( uint32_t ) configTICK_RATE_HZ ) )
#define UINT32_MAX_DELAY_MS                    ( 0xFFFFFFFFUL )
#define UINT32_MAX_MS_TICKS                    ( UINT32_MAX_DELAY_MS / ( TICKS_TO_MS( 1U ) ) )

/* Cellular socket access mode. */
#define CELLULAR_SOCKET_ACCESS_MODE            CELLULAR_ACCESSMODE_BUFFER

/* Cellular socket open timeout. */
#define CELLULAR_SOCKET_OPEN_TIMEOUT_TICKS     ( portMAX_DELAY )
#define CELLULAR_SOCKET_CLOSE_TIMEOUT_TICKS    ( pdMS_TO_TICKS( 10000U ) )

/* Cellular socket AT command timeout. */
#define CELLULAR_SOCKET_RECV_TIMEOUT_MS        ( 1000UL )

/* Time conversion constants. */
#define _MILLISECONDS_PER_SECOND               ( 1000 )                                          /**< @brief Milliseconds per second. */
#define _MILLISECONDS_PER_TICK                 ( _MILLISECONDS_PER_SECOND / configTICK_RATE_HZ ) /**< Milliseconds per FreeRTOS tick. */

/* Logging macros definition. */
#define IotLogError( ... )    LogError( ( __VA_ARGS__ ) )
#define IotLogWarn( ... )     LogWarn( ( __VA_ARGS__ ) )
#define IotLogInfo( ... )     LogInfo( ( __VA_ARGS__ ) )
#define IotLogDebug( ... )    LogDebug( ( __VA_ARGS__ ) )

/*-----------------------------------------------------------*/

typedef struct xSOCKET
{
    CellularSocketHandle_t cellularSocketHandle;
    uint32_t ulFlags;

    TickType_t receiveTimeout;
    TickType_t sendTimeout;

    EventGroupHandle_t socketEventGroupHandle;
} cellularSocketWrapper_t;

/*-----------------------------------------------------------*/

/**
 * @brief Get the count of milliseconds since vTaskStartScheduler was called.
 *
 * @return The count of milliseconds since vTaskStartScheduler was called.
 */
static uint64_t getTimeMs( void );

/**
 * @brief Receive data from cellular socket.
 *
 * @param[in] pCellularSocketContext Cellular socket wrapper context for socket operations.
 * @param[out] buf The data buffer for receiving data.
 * @param[in] len The length of the data buffer
 *
 * @note This function receives data. It returns when non-zero bytes of data is received,
 * when an error occurs, or when timeout occurs. Receive timeout unit is TickType_t.
 * Any timeout value bigger than portMAX_DELAY will be regarded as portMAX_DELAY.
 * In this case, this function waits portMAX_DELAY until non-zero bytes of data is received
 * or until an error occurs.
 *
 * @return Positive value indicate the number of bytes received. Otherwise, error code defined
 * in sockets_wrapper.h is returned.
 */
static BaseType_t prvNetworkRecvCellular( const cellularSocketWrapper_t * pCellularSocketContext,
                                          uint8_t * buf,
                                          size_t len );

/**
 * @brief Callback used to inform about the status of socket open.
 *
 * @param[in] urcEvent URC Event that happened.
 * @param[in] socketHandle Socket handle for which data is ready.
 * @param[in] pCallbackContext pCallbackContext parameter in
 * Cellular_SocketRegisterSocketOpenCallback function.
 */
static void prvCellularSocketOpenCallback( CellularUrcEvent_t urcEvent,
                                           CellularSocketHandle_t socketHandle,
                                           void * pCallbackContext );

/**
 * @brief Callback used to inform that data is ready for reading on a socket.
 *
 * @param[in] socketHandle Socket handle for which data is ready.
 * @param[in] pCallbackContext pCallbackContext parameter in
 * Cellular_SocketRegisterDataReadyCallback function.
 */
static void prvCellularSocketDataReadyCallback( CellularSocketHandle_t socketHandle,
                                                void * pCallbackContext );


/**
 * @brief Callback used to inform that remote end closed the connection for a
 * connected socket.
 *
 * @param[in] socketHandle Socket handle for which remote end closed the
 * connection.
 * @param[in] pCallbackContext pCallbackContext parameter in
 * Cellular_SocketRegisterClosedCallback function.
 */
static void prvCellularSocketClosedCallback( CellularSocketHandle_t socketHandle,
                                             void * pCallbackContext );

/**
 * @brief Setup socket receive timeout.
 *
 * @param[in] pCellularSocketContext Cellular socket wrapper context for socket operations.
 * @param[out] receiveTimeout Socket receive timeout in TickType_t.
 *
 * @return On success, SOCKETS_ERROR_NONE is returned. If an error occurred, error code defined
 * in sockets_wrapper.h is returned.
 */
static BaseType_t prvSetupSocketRecvTimeout( cellularSocketWrapper_t * pCellularSocketContext,
                                             TickType_t receiveTimeout );

/**
 * @brief Setup socket send timeout.
 *
 * @param[in] pCellularSocketContext Cellular socket wrapper context for socket operations.
 * @param[out] sendTimeout Socket send timeout in TickType_t.
 *
 * @note Send timeout unit is TickType_t. The underlying cellular API uses miliseconds for timeout.
 * Any send timeout greater than UINT32_MAX_MS_TICKS( UINT32_MAX_DELAY_MS/MS_PER_TICKS ) or
 * portMAX_DELAY is regarded as UINT32_MAX_DELAY_MS for cellular API.
 *
 * @return On success, SOCKETS_ERROR_NONE is returned. If an error occurred, error code defined
 * in sockets_wrapper.h is returned.
 */
static BaseType_t prvSetupSocketSendTimeout( cellularSocketWrapper_t * pCellularSocketContext,
                                             TickType_t sendTimeout );

/**
 * @brief Setup cellular socket callback function.
 *
 * @param[in] CellularSocketHandle_t Cellular socket handle for cellular socket operations.
 * @param[in] pCellularSocketContext Cellular socket wrapper context for socket operations.
 *
 * @return On success, SOCKETS_ERROR_NONE is returned. If an error occurred, error code defined
 * in sockets_wrapper.h is returned.
 */
static BaseType_t prvCellularSocketRegisterCallback( CellularSocketHandle_t cellularSocketHandle,
                                                     cellularSocketWrapper_t * pCellularSocketContext );

/**
 * @brief Calculate elapsed time from current time and input parameters.
 *
 * @param[in] entryTimeMs The entry time to be compared with current time.
 * @param[in] timeoutValueMs Timeout value for the comparison between entry time and current time.
 * @param[out] pElapsedTimeMs The elapsed time if timeout condition is true.
 *
 * @return True if the difference between entry time and current time is bigger or
 * equal to timeoutValueMs. Otherwise, return false.
 */
static bool _calculateElapsedTime( uint64_t entryTimeMs,
                                   uint32_t timeoutValueMs,
                                   uint64_t * pElapsedTimeMs );

/*-----------------------------------------------------------*/

static uint64_t getTimeMs( void )
{
    TimeOut_t xCurrentTime = { 0 };

    /* This must be unsigned because the behavior of signed integer overflow is undefined. */
    uint64_t ullTickCount = 0ULL;

    /* Get the current tick count and overflow count. vTaskSetTimeOutState()
     * is used to get these values because they are both static in tasks.c. */
    vTaskSetTimeOutState( &xCurrentTime );

    /* Adjust the tick count for the number of times a TickType_t has overflowed. */
    ullTickCount = ( uint64_t ) ( xCurrentTime.xOverflowCount ) << ( sizeof( TickType_t ) * 8 );

    /* Add the current tick count. */
    ullTickCount += xCurrentTime.xTimeOnEntering;

    /* Return the ticks converted to milliseconds. */
    return ullTickCount * _MILLISECONDS_PER_TICK;
}

/*-----------------------------------------------------------*/

static BaseType_t prvNetworkRecvCellular( const cellularSocketWrapper_t * pCellularSocketContext,
                                          uint8_t * buf,
                                          size_t len )
{
    CellularSocketHandle_t cellularSocketHandle = NULL;
    BaseType_t retRecvLength = 0;
    uint32_t recvLength = 0;
    TickType_t recvTimeout = 0;
    TickType_t recvStartTime = 0;
    CellularError_t socketStatus = CELLULAR_SUCCESS;
    EventBits_t waitEventBits = 0;

    cellularSocketHandle = pCellularSocketContext->cellularSocketHandle;

    if( pCellularSocketContext->receiveTimeout >= portMAX_DELAY )
    {
        recvTimeout = portMAX_DELAY;
    }
    else
    {
        recvTimeout = pCellularSocketContext->receiveTimeout;
    }

    recvStartTime = xTaskGetTickCount();

    ( void ) xEventGroupClearBits( pCellularSocketContext->socketEventGroupHandle,
                                   SOCKET_DATA_RECEIVED_CALLBACK_BIT );
    socketStatus = Cellular_SocketRecv( CellularHandle, cellularSocketHandle, buf, len, &recvLength );

    /* Calculate remain recvTimeout. */
    if( recvTimeout != portMAX_DELAY )
    {
        if( ( recvStartTime + recvTimeout ) > xTaskGetTickCount() )
        {
            recvTimeout = recvTimeout - ( xTaskGetTickCount() - recvStartTime );
        }
        else
        {
            recvTimeout = 0;
        }
    }

    if( ( socketStatus == CELLULAR_SUCCESS ) && ( recvLength == 0U ) &&
        ( recvTimeout != 0U ) )
    {
        waitEventBits = xEventGroupWaitBits( pCellularSocketContext->socketEventGroupHandle,
                                             SOCKET_DATA_RECEIVED_CALLBACK_BIT | SOCKET_CLOSE_CALLBACK_BIT,
                                             pdTRUE,
                                             pdFALSE,
                                             recvTimeout );

        if( ( waitEventBits & SOCKET_CLOSE_CALLBACK_BIT ) != 0U )
        {
            socketStatus = CELLULAR_SOCKET_CLOSED;
        }
        else if( ( waitEventBits & SOCKET_DATA_RECEIVED_CALLBACK_BIT ) != 0U )
        {
            socketStatus = Cellular_SocketRecv( CellularHandle, cellularSocketHandle, buf, len, &recvLength );
        }
        else
        {
            IotLogInfo( "prvNetworkRecv timeout" );
            socketStatus = CELLULAR_SUCCESS;
            recvLength = 0;
        }
    }

    if( socketStatus == CELLULAR_SUCCESS )
    {
        retRecvLength = ( BaseType_t ) recvLength;
    }
    else
    {
        IotLogError( "prvNetworkRecv failed %d", socketStatus );
        retRecvLength = SOCKETS_SOCKET_ERROR;
    }

    IotLogDebug( "prvNetworkRecv expect %d read %d", len, recvLength );
    return retRecvLength;
}

/*-----------------------------------------------------------*/

static void prvCellularSocketOpenCallback( CellularUrcEvent_t urcEvent,
                                           CellularSocketHandle_t socketHandle,
                                           void * pCallbackContext )
{
    cellularSocketWrapper_t * pCellularSocketContext = ( cellularSocketWrapper_t * ) pCallbackContext;

    ( void ) socketHandle;

    if( pCellularSocketContext != NULL )
    {
        IotLogDebug( "Socket open callback on Socket %p %d %d.",
                     pCellularSocketContext, socketHandle, urcEvent );

        if( urcEvent == CELLULAR_URC_SOCKET_OPENED )
        {
            pCellularSocketContext->ulFlags = pCellularSocketContext->ulFlags | CELLULAR_SOCKET_CONNECT_FLAG;
            ( void ) xEventGroupSetBits( pCellularSocketContext->socketEventGroupHandle,
                                         SOCKET_OPEN_CALLBACK_BIT );
        }
        else
        {
            /* Socket open failed. */
            ( void ) xEventGroupSetBits( pCellularSocketContext->socketEventGroupHandle,
                                         SOCKET_OPEN_FAILED_CALLBACK_BIT );
        }
    }
    else
    {
        IotLogError( "Spurious socket open callback." );
    }
}

/*-----------------------------------------------------------*/

static void prvCellularSocketDataReadyCallback( CellularSocketHandle_t socketHandle,
                                                void * pCallbackContext )
{
    cellularSocketWrapper_t * pCellularSocketContext = ( cellularSocketWrapper_t * ) pCallbackContext;

    ( void ) socketHandle;

    if( pCellularSocketContext != NULL )
    {
        IotLogDebug( "Data ready on Socket %p", pCellularSocketContext );
        ( void ) xEventGroupSetBits( pCellularSocketContext->socketEventGroupHandle,
                                     SOCKET_DATA_RECEIVED_CALLBACK_BIT );
    }
    else
    {
        IotLogError( "spurious data callback" );
    }
}

/*-----------------------------------------------------------*/

static void prvCellularSocketClosedCallback( CellularSocketHandle_t socketHandle,
                                             void * pCallbackContext )
{
    cellularSocketWrapper_t * pCellularSocketContext = ( cellularSocketWrapper_t * ) pCallbackContext;

    ( void ) socketHandle;

    if( pCellularSocketContext != NULL )
    {
        IotLogInfo( "Socket Close on Socket %p", pCellularSocketContext );
        pCellularSocketContext->ulFlags = pCellularSocketContext->ulFlags & ( ~CELLULAR_SOCKET_CONNECT_FLAG );
        ( void ) xEventGroupSetBits( pCellularSocketContext->socketEventGroupHandle,
                                     SOCKET_CLOSE_CALLBACK_BIT );
    }
    else
    {
        IotLogError( "spurious socket close callback" );
    }
}

/*-----------------------------------------------------------*/

static BaseType_t prvSetupSocketRecvTimeout( cellularSocketWrapper_t * pCellularSocketContext,
                                             TickType_t receiveTimeout )
{
    BaseType_t retSetSockOpt = SOCKETS_ERROR_NONE;

    if( pCellularSocketContext == NULL )
    {
        retSetSockOpt = SOCKETS_EINVAL;
    }
    else
    {
        if( receiveTimeout >= portMAX_DELAY )
        {
            pCellularSocketContext->receiveTimeout = portMAX_DELAY;
        }
        else
        {
            pCellularSocketContext->receiveTimeout = receiveTimeout;
        }
    }

    return retSetSockOpt;
}

/*-----------------------------------------------------------*/

static BaseType_t prvSetupSocketSendTimeout( cellularSocketWrapper_t * pCellularSocketContext,
                                             TickType_t sendTimeout )
{
    CellularError_t socketStatus = CELLULAR_SUCCESS;
    BaseType_t retSetSockOpt = SOCKETS_ERROR_NONE;
    uint32_t sendTimeoutMs = 0;
    CellularSocketHandle_t cellularSocketHandle = NULL;

    if( pCellularSocketContext == NULL )
    {
        retSetSockOpt = SOCKETS_EINVAL;
    }
    else
    {
        cellularSocketHandle = pCellularSocketContext->cellularSocketHandle;

        if( sendTimeout >= UINT32_MAX_MS_TICKS )
        {
            /* Check if the ticks cause overflow. */
            pCellularSocketContext->sendTimeout = portMAX_DELAY;
            sendTimeoutMs = UINT32_MAX_DELAY_MS;
        }
        else if( sendTimeout >= portMAX_DELAY )
        {
            IotLogWarn( "Sendtimeout %d longer than portMAX_DELAY, %d ms is used instead",
                        sendTimeout, UINT32_MAX_DELAY_MS );
            pCellularSocketContext->sendTimeout = portMAX_DELAY;
            sendTimeoutMs = UINT32_MAX_DELAY_MS;
        }
        else
        {
            pCellularSocketContext->sendTimeout = sendTimeout;
            sendTimeoutMs = TICKS_TO_MS( sendTimeout );
        }

        socketStatus = Cellular_SocketSetSockOpt( CellularHandle,
                                                  cellularSocketHandle,
                                                  CELLULAR_SOCKET_OPTION_LEVEL_TRANSPORT,
                                                  CELLULAR_SOCKET_OPTION_SEND_TIMEOUT,
                                                  ( const uint8_t * ) &sendTimeoutMs,
                                                  sizeof( uint32_t ) );

        if( socketStatus != CELLULAR_SUCCESS )
        {
            retSetSockOpt = SOCKETS_EINVAL;
        }
    }

    return retSetSockOpt;
}

/*-----------------------------------------------------------*/

static BaseType_t prvCellularSocketRegisterCallback( CellularSocketHandle_t cellularSocketHandle,
                                                     cellularSocketWrapper_t * pCellularSocketContext )
{
    BaseType_t retRegCallback = SOCKETS_ERROR_NONE;
    CellularError_t socketStatus = CELLULAR_SUCCESS;

    if( cellularSocketHandle == NULL )
    {
        retRegCallback = SOCKETS_EINVAL;
    }

    if( retRegCallback == SOCKETS_ERROR_NONE )
    {
        socketStatus = Cellular_SocketRegisterDataReadyCallback( CellularHandle, cellularSocketHandle,
                                                                 prvCellularSocketDataReadyCallback, ( void * ) pCellularSocketContext );

        if( socketStatus != CELLULAR_SUCCESS )
        {
            IotLogError( "Failed to SocketRegisterDataReadyCallback. Socket status %d.", socketStatus );
            retRegCallback = SOCKETS_SOCKET_ERROR;
        }
    }

    if( retRegCallback == SOCKETS_ERROR_NONE )
    {
        socketStatus = Cellular_SocketRegisterSocketOpenCallback( CellularHandle, cellularSocketHandle,
                                                                  prvCellularSocketOpenCallback, ( void * ) pCellularSocketContext );

        if( socketStatus != CELLULAR_SUCCESS )
        {
            IotLogError( "Failed to SocketRegisterSocketOpenCallbac. Socket status %d.", socketStatus );
            retRegCallback = SOCKETS_SOCKET_ERROR;
        }
    }

    if( retRegCallback == SOCKETS_ERROR_NONE )
    {
        socketStatus = Cellular_SocketRegisterClosedCallback( CellularHandle, cellularSocketHandle,
                                                              prvCellularSocketClosedCallback, ( void * ) pCellularSocketContext );

        if( socketStatus != CELLULAR_SUCCESS )
        {
            IotLogError( "Failed to SocketRegisterClosedCallback. Socket status %d.", socketStatus );
            retRegCallback = SOCKETS_SOCKET_ERROR;
        }
    }

    return retRegCallback;
}

/*-----------------------------------------------------------*/

static bool _calculateElapsedTime( uint64_t entryTimeMs,
                                   uint32_t timeoutValueMs,
                                   uint64_t * pElapsedTimeMs )
{
    uint64_t currentTimeMs = getTimeMs();
    bool isExpired = false;

    /* timeoutValueMs with UINT32_MAX_DELAY_MS means wait for ever, same behavior as freertos_plus_tcp. */
    if( timeoutValueMs == UINT32_MAX_DELAY_MS )
    {
        isExpired = false;
    }

    /* timeoutValueMs = 0 means none blocking mode. */
    else if( timeoutValueMs == 0U )
    {
        isExpired = true;
    }
    else
    {
        *pElapsedTimeMs = currentTimeMs - entryTimeMs;

        if( ( currentTimeMs - entryTimeMs ) >= timeoutValueMs )
        {
            isExpired = true;
        }
        else
        {
            isExpired = false;
        }
    }

    return isExpired;
}

/*-----------------------------------------------------------*/

BaseType_t Sockets_Connect( Socket_t * pTcpSocket,
                            const char * pHostName,
                            uint16_t port,
                            uint32_t receiveTimeoutMs,
                            uint32_t sendTimeoutMs )
{
    CellularSocketHandle_t cellularSocketHandle = NULL;
    cellularSocketWrapper_t * pCellularSocketContext = NULL;
    CellularError_t cellularSocketStatus = CELLULAR_INVALID_HANDLE;

    CellularSocketAddress_t serverAddress = { 0 };
    EventBits_t waitEventBits = 0;
    BaseType_t retConnect = SOCKETS_ERROR_NONE;
    const uint32_t defaultReceiveTimeoutMs = CELLULAR_SOCKET_RECV_TIMEOUT_MS;

    /* Create a new TCP socket. */
    cellularSocketStatus = Cellular_CreateSocket( CellularHandle,
                                                  CellularSocketPdnContextId,
                                                  CELLULAR_SOCKET_DOMAIN_AF_INET,
                                                  CELLULAR_SOCKET_TYPE_STREAM,
                                                  CELLULAR_SOCKET_PROTOCOL_TCP,
                                                  &cellularSocketHandle );

    if( cellularSocketStatus != CELLULAR_SUCCESS )
    {
        IotLogError( "Failed to create cellular sockets. %d", cellularSocketStatus );
        retConnect = SOCKETS_SOCKET_ERROR;
    }

    /* Allocate socket context. */
    if( retConnect == SOCKETS_ERROR_NONE )
    {
        pCellularSocketContext = pvPortMalloc( sizeof( cellularSocketWrapper_t ) );

        if( pCellularSocketContext == NULL )
        {
            IotLogError( "Failed to allocate new socket context." );
            ( void ) Cellular_SocketClose( CellularHandle, cellularSocketHandle );
            retConnect = SOCKETS_ENOMEM;
        }
        else
        {
            /* Initialize all the members to sane values. */
            IotLogDebug( "Created CELLULAR Socket %p.", pCellularSocketContext );
            ( void ) memset( pCellularSocketContext, 0, sizeof( cellularSocketWrapper_t ) );
            pCellularSocketContext->cellularSocketHandle = cellularSocketHandle;
            pCellularSocketContext->ulFlags |= CELLULAR_SOCKET_OPEN_FLAG;
            pCellularSocketContext->socketEventGroupHandle = NULL;
        }
    }

    /* Allocate event group for callback function. */
    if( retConnect == SOCKETS_ERROR_NONE )
    {
        pCellularSocketContext->socketEventGroupHandle = xEventGroupCreate();

        if( pCellularSocketContext->socketEventGroupHandle == NULL )
        {
            IotLogError( "Failed create cellular socket eventGroupHandle %p.", pCellularSocketContext );
            retConnect = SOCKETS_ENOMEM;
        }
    }

    /* Register cellular socket callback function. */
    if( retConnect == SOCKETS_ERROR_NONE )
    {
        serverAddress.ipAddress.ipAddressType = CELLULAR_IP_ADDRESS_V4;
        strncpy( serverAddress.ipAddress.ipAddress, pHostName, CELLULAR_IP_ADDRESS_MAX_SIZE );
        serverAddress.port = port;

        IotLogDebug( "Ip address %s port %d\r\n", serverAddress.ipAddress.ipAddress, serverAddress.port );
        retConnect = prvCellularSocketRegisterCallback( cellularSocketHandle, pCellularSocketContext );
    }

    /* Setup cellular socket recv AT command default timeout. */
    if( retConnect == SOCKETS_ERROR_NONE )
    {
        cellularSocketStatus = Cellular_SocketSetSockOpt( CellularHandle,
                                                          cellularSocketHandle,
                                                          CELLULAR_SOCKET_OPTION_LEVEL_TRANSPORT,
                                                          CELLULAR_SOCKET_OPTION_RECV_TIMEOUT,
                                                          ( const uint8_t * ) &defaultReceiveTimeoutMs,
                                                          sizeof( uint32_t ) );

        if( cellularSocketStatus != CELLULAR_SUCCESS )
        {
            IotLogError( "Failed to setup cellular AT command receive timeout %d.", cellularSocketStatus );
            retConnect = SOCKETS_SOCKET_ERROR;
        }
    }

    /* Setup cellular socket send/recv timeout. */
    if( retConnect == SOCKETS_ERROR_NONE )
    {
        retConnect = prvSetupSocketSendTimeout( pCellularSocketContext, pdMS_TO_TICKS( sendTimeoutMs ) );
    }

    if( retConnect == SOCKETS_ERROR_NONE )
    {
        retConnect = prvSetupSocketRecvTimeout( pCellularSocketContext, pdMS_TO_TICKS( receiveTimeoutMs ) );
    }

    /* Cellular socket connect. */
    if( retConnect == SOCKETS_ERROR_NONE )
    {
        ( void ) xEventGroupClearBits( pCellularSocketContext->socketEventGroupHandle,
                                       SOCKET_DATA_RECEIVED_CALLBACK_BIT | SOCKET_OPEN_FAILED_CALLBACK_BIT );
        cellularSocketStatus = Cellular_SocketConnect( CellularHandle, cellularSocketHandle, CELLULAR_SOCKET_ACCESS_MODE, &serverAddress );

        if( cellularSocketStatus != CELLULAR_SUCCESS )
        {
            IotLogError( "Failed to establish new connection. Socket status %d.", cellularSocketStatus );
            retConnect = SOCKETS_SOCKET_ERROR;
        }
    }

    /* Wait the socket connection. */
    if( retConnect == SOCKETS_ERROR_NONE )
    {
        waitEventBits = xEventGroupWaitBits( pCellularSocketContext->socketEventGroupHandle,
                                             SOCKET_OPEN_CALLBACK_BIT | SOCKET_OPEN_FAILED_CALLBACK_BIT,
                                             pdTRUE,
                                             pdFALSE,
                                             CELLULAR_SOCKET_OPEN_TIMEOUT_TICKS );

        if( waitEventBits != SOCKET_OPEN_CALLBACK_BIT )
        {
            IotLogError( "Socket connect timeout." );
            retConnect = SOCKETS_ENOTCONN;
        }
    }

    /* Cleanup the socket if any error. */
    if( retConnect != SOCKETS_ERROR_NONE )
    {
        if( cellularSocketHandle != NULL )
        {
            ( void ) Cellular_SocketClose( CellularHandle, cellularSocketHandle );
            ( void ) Cellular_SocketRegisterDataReadyCallback( CellularHandle, cellularSocketHandle, NULL, NULL );
            ( void ) Cellular_SocketRegisterSocketOpenCallback( CellularHandle, cellularSocketHandle, NULL, NULL );
            ( void ) Cellular_SocketRegisterClosedCallback( CellularHandle, cellularSocketHandle, NULL, NULL );

            if( pCellularSocketContext != NULL )
            {
                pCellularSocketContext->cellularSocketHandle = NULL;
            }
        }

        if( ( pCellularSocketContext != NULL ) && ( pCellularSocketContext->socketEventGroupHandle != NULL ) )
        {
            vEventGroupDelete( pCellularSocketContext->socketEventGroupHandle );
            pCellularSocketContext->socketEventGroupHandle = NULL;
        }

        if( pCellularSocketContext != NULL )
        {
            vPortFree( pCellularSocketContext );
            pCellularSocketContext = NULL;
        }
    }

    *pTcpSocket = pCellularSocketContext;

    return retConnect;
}

/*-----------------------------------------------------------*/

void Sockets_Disconnect( Socket_t xSocket )
{
    int32_t retClose = SOCKETS_ERROR_NONE;
    cellularSocketWrapper_t * pCellularSocketContext = ( cellularSocketWrapper_t * ) xSocket;
    CellularSocketHandle_t cellularSocketHandle = NULL;
    uint32_t recvLength = 0;
    uint8_t buf[ 128 ] = { 0 };
    CellularError_t cellularSocketStatus = CELLULAR_SUCCESS;

    /* xSocket need to be check against SOCKET_INVALID_SOCKET. */
    /* coverity[misra_c_2012_rule_11_4_violation] */
    if( ( pCellularSocketContext == NULL ) || ( xSocket == SOCKETS_INVALID_SOCKET ) )
    {
        IotLogError( "Invalid xSocket %p", pCellularSocketContext );
        retClose = SOCKETS_EINVAL;
    }
    else
    {
        cellularSocketHandle = pCellularSocketContext->cellularSocketHandle;
    }

    if( retClose == SOCKETS_ERROR_NONE )
    {
        if( cellularSocketHandle != NULL )
        {
            /* Receive all the data before socket close. */
            do
            {
                recvLength = 0;
                cellularSocketStatus = Cellular_SocketRecv( CellularHandle, cellularSocketHandle, buf, 128, &recvLength );
                IotLogDebug( "%u bytes received in close", recvLength );
            } while( ( recvLength != 0 ) && ( cellularSocketStatus == CELLULAR_SUCCESS ) );

            /* Close sockets. */
            if( Cellular_SocketClose( CellularHandle, cellularSocketHandle ) != CELLULAR_SUCCESS )
            {
                IotLogWarn( "Failed to destroy connection." );
                retClose = SOCKETS_SOCKET_ERROR;
            }

            ( void ) Cellular_SocketRegisterDataReadyCallback( CellularHandle, cellularSocketHandle, NULL, NULL );
            ( void ) Cellular_SocketRegisterSocketOpenCallback( CellularHandle, cellularSocketHandle, NULL, NULL );
            ( void ) Cellular_SocketRegisterClosedCallback( CellularHandle, cellularSocketHandle, NULL, NULL );
            pCellularSocketContext->cellularSocketHandle = NULL;
        }

        if( pCellularSocketContext->socketEventGroupHandle != NULL )
        {
            vEventGroupDelete( pCellularSocketContext->socketEventGroupHandle );
            pCellularSocketContext->socketEventGroupHandle = NULL;
        }

        vPortFree( pCellularSocketContext );
    }

    IotLogDebug( "Sockets close exit with code %d", retClose );
}

/*-----------------------------------------------------------*/

int32_t Sockets_Recv( Socket_t xSocket,
                      void * pvBuffer,
                      size_t xBufferLength )
{
    cellularSocketWrapper_t * pCellularSocketContext = ( cellularSocketWrapper_t * ) xSocket;
    uint8_t * buf = ( uint8_t * ) pvBuffer;
    BaseType_t retRecvLength = 0;

    if( pCellularSocketContext == NULL )
    {
        IotLogError( "Cellular prvNetworkRecv Invalid xSocket %p", pCellularSocketContext );
        retRecvLength = ( BaseType_t ) SOCKETS_EINVAL;
    }
    else if( ( ( pCellularSocketContext->ulFlags & CELLULAR_SOCKET_OPEN_FLAG ) == 0U ) ||
             ( ( pCellularSocketContext->ulFlags & CELLULAR_SOCKET_CONNECT_FLAG ) == 0U ) )
    {
        IotLogError( "Cellular prvNetworkRecv Invalid xSocket flag %p %u",
                     pCellularSocketContext, pCellularSocketContext->ulFlags );
        retRecvLength = ( BaseType_t ) SOCKETS_ENOTCONN;
    }
    else
    {
        retRecvLength = ( BaseType_t ) prvNetworkRecvCellular( pCellularSocketContext, buf, xBufferLength );
    }

    return retRecvLength;
}

/*-----------------------------------------------------------*/

/* This function sends the data until timeout or data is completely sent to server.
 * Send timeout unit is TickType_t. Any timeout value greater than UINT32_MAX_MS_TICKS
 * or portMAX_DELAY will be regarded as MAX delay. In this case, this function
 * will not return until all bytes of data are sent successfully or until an error occurs. */
int32_t Sockets_Send( Socket_t xSocket,
                      const void * pvBuffer,
                      size_t xDataLength )
{
    uint8_t * buf = ( uint8_t * ) pvBuffer;
    CellularSocketHandle_t cellularSocketHandle = NULL;
    BaseType_t retSendLength = 0;
    uint32_t sentLength = 0;
    CellularError_t socketStatus = CELLULAR_SUCCESS;
    cellularSocketWrapper_t * pCellularSocketContext = ( cellularSocketWrapper_t * ) xSocket;
    uint32_t bytesToSend = xDataLength;
    uint64_t entryTimeMs = getTimeMs();
    uint64_t elapsedTimeMs = 0;
    uint32_t sendTimeoutMs = 0;

    if( pCellularSocketContext == NULL )
    {
        IotLogError( "Cellular Sockets_Send Invalid xSocket %p", pCellularSocketContext );
        retSendLength = ( BaseType_t ) SOCKETS_SOCKET_ERROR;
    }
    else if( ( ( pCellularSocketContext->ulFlags & CELLULAR_SOCKET_OPEN_FLAG ) == 0U ) ||
             ( ( pCellularSocketContext->ulFlags & CELLULAR_SOCKET_CONNECT_FLAG ) == 0U ) )
    {
        IotLogError( "Cellular Sockets_Send Invalid xSocket flag %p 0x%08x",
                     pCellularSocketContext, pCellularSocketContext->ulFlags );
        retSendLength = ( BaseType_t ) SOCKETS_SOCKET_ERROR;
    }
    else
    {
        cellularSocketHandle = pCellularSocketContext->cellularSocketHandle;

        /* Convert ticks to ms delay. */
        if( ( pCellularSocketContext->sendTimeout >= UINT32_MAX_MS_TICKS ) || ( pCellularSocketContext->sendTimeout >= portMAX_DELAY ) )
        {
            /* Check if the ticks cause overflow. */
            sendTimeoutMs = UINT32_MAX_DELAY_MS;
        }
        else
        {
            sendTimeoutMs = TICKS_TO_MS( pCellularSocketContext->sendTimeout );
        }

        /* Loop sending data until data is sent completely or timeout. */
        while( bytesToSend > 0U )
        {
            socketStatus = Cellular_SocketSend( CellularHandle,
                                                cellularSocketHandle,
                                                &buf[ retSendLength ],
                                                bytesToSend,
                                                &sentLength );

            if( socketStatus == CELLULAR_SUCCESS )
            {
                retSendLength = retSendLength + ( BaseType_t ) sentLength;
                bytesToSend = bytesToSend - sentLength;
            }

            /* Check socket status or timeout break. */
            if( ( socketStatus != CELLULAR_SUCCESS ) ||
                ( _calculateElapsedTime( entryTimeMs, sendTimeoutMs, &elapsedTimeMs ) ) )
            {
                if( socketStatus == CELLULAR_SOCKET_CLOSED )
                {
                    /* Socket already closed. No data is sent. */
                    retSendLength = 0;
                }
                else if( socketStatus != CELLULAR_SUCCESS )
                {
                    retSendLength = ( BaseType_t ) SOCKETS_SOCKET_ERROR;
                }

                break;
            }
        }

        IotLogDebug( "Sockets_Send expect %d write %d", len, sentLength );
    }

    return retSendLength;
}

/*-----------------------------------------------------------*/
