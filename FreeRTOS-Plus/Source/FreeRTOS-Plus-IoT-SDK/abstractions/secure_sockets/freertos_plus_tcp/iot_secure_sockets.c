/*
 * Amazon FreeRTOS Secure Sockets V1.1.5
 * Copyright (C) 2018 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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

/* Define _SECURE_SOCKETS_WRAPPER_NOT_REDEFINE to prevent secure sockets functions
 * from redefining in iot_secure_sockets_wrapper_metrics.h */
#define _SECURE_SOCKETS_WRAPPER_NOT_REDEFINE

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "FreeRTOSIPConfig.h"
#include "list.h"
#include "semphr.h"
#include "FreeRTOS_IP.h"
#include "FreeRTOS_Sockets.h"
#include "iot_secure_sockets.h"
#include "task.h"

#undef _SECURE_SOCKETS_WRAPPER_NOT_REDEFINE

/* Internal context structure. */
typedef struct SSOCKETContext
{
    Socket_t xSocket;
    char * pcDestination;
    BaseType_t xSendFlags;
    BaseType_t xRecvFlags;
    BaseType_t xConnectAttempted;
} SSOCKETContext_t, * SSOCKETContextPtr_t;

/*
 * Helper routines.
 */

/*
 * @brief Network send callback.
 */
static BaseType_t prvNetworkSend( void * pvContext,
                                  const unsigned char * pucData,
                                  size_t xDataLength )
{
    SSOCKETContextPtr_t pxContext = ( SSOCKETContextPtr_t ) pvContext; /*lint !e9087 cast used for portability. */

    return FreeRTOS_send( pxContext->xSocket, pucData, xDataLength, pxContext->xSendFlags );
}
/*-----------------------------------------------------------*/

/*
 * @brief Network receive callback.
 */
static BaseType_t prvNetworkRecv( void * pvContext,
                                  unsigned char * pucReceiveBuffer,
                                  size_t xReceiveLength )
{
    SSOCKETContextPtr_t pxContext = ( SSOCKETContextPtr_t ) pvContext; /*lint !e9087 cast used for portability. */

    return FreeRTOS_recv( pxContext->xSocket, pucReceiveBuffer, xReceiveLength, pxContext->xRecvFlags );
}
/*-----------------------------------------------------------*/

/*
 * Interface routines.
 */

int32_t SOCKETS_Close( Socket_t xSocket )
{
    SSOCKETContextPtr_t pxContext = ( SSOCKETContextPtr_t ) xSocket; /*lint !e9087 cast used for portability. */
    int32_t lReturn;

    if( ( xSocket != SOCKETS_INVALID_SOCKET ) && ( NULL != pxContext ) )
    {
        /* Clean-up destination string. */
        if( NULL != pxContext->pcDestination )
        {
            vPortFree( pxContext->pcDestination );
        }

        /* Close the underlying socket handle. */
        ( void ) FreeRTOS_closesocket( pxContext->xSocket );

        /* Free the context. */
        vPortFree( pxContext );
        lReturn = SOCKETS_ERROR_NONE;
    }
    else
    {
        lReturn = SOCKETS_EINVAL;
    }

    return lReturn;
}
/*-----------------------------------------------------------*/

int32_t SOCKETS_Connect( Socket_t xSocket,
                         SocketsSockaddr_t * pxAddress,
                         Socklen_t xAddressLength )
{
    int32_t lStatus = SOCKETS_ERROR_NONE;
    SSOCKETContextPtr_t pxContext = ( SSOCKETContextPtr_t ) xSocket; /*lint !e9087 cast used for portability. */
    struct freertos_sockaddr xTempAddress = { 0 };

    if( ( pxContext != SOCKETS_INVALID_SOCKET ) && ( pxAddress != NULL ) )
    {
        /* A connection was attempted. If this function fails, then the socket is invalid and the user
         * must call SOCKETS_Close(), on this socket, and SOCKETS_Socket() to get a new socket. */
        pxContext->xConnectAttempted = pdTRUE;

        /* Connect the wrapped socket. */
        xTempAddress.sin_addr = pxAddress->ulAddress;
        xTempAddress.sin_family = pxAddress->ucSocketDomain;
        xTempAddress.sin_len = ( uint8_t ) sizeof( xTempAddress );
        xTempAddress.sin_port = pxAddress->usPort;
        lStatus = FreeRTOS_connect( pxContext->xSocket, &xTempAddress, xAddressLength );
    }
    else
    {
        lStatus = SOCKETS_SOCKET_ERROR;
    }

    return lStatus;
}
/*-----------------------------------------------------------*/

uint32_t SOCKETS_GetHostByName( const char * pcHostName )
{
    return FreeRTOS_gethostbyname( pcHostName );
}
/*-----------------------------------------------------------*/

int32_t SOCKETS_Recv( Socket_t xSocket,
                      void * pvBuffer,
                      size_t xBufferLength,
                      uint32_t ulFlags )
{
    int32_t lStatus = SOCKETS_SOCKET_ERROR;
    SSOCKETContextPtr_t pxContext = ( SSOCKETContextPtr_t ) xSocket; /*lint !e9087 cast used for portability. */

    if( ( xSocket != SOCKETS_INVALID_SOCKET ) &&
        ( pvBuffer != NULL ) )
    {
        pxContext->xRecvFlags = ( BaseType_t ) ulFlags;

        /* Receive unencrypted. */
        lStatus = prvNetworkRecv( pxContext, pvBuffer, xBufferLength );
    }
    else
    {
        lStatus = SOCKETS_EINVAL;
    }

    return lStatus;
}
/*-----------------------------------------------------------*/

int32_t SOCKETS_Send( Socket_t xSocket,
                      const void * pvBuffer,
                      size_t xDataLength,
                      uint32_t ulFlags )
{
    int32_t lStatus = SOCKETS_SOCKET_ERROR;
    SSOCKETContextPtr_t pxContext = ( SSOCKETContextPtr_t ) xSocket; /*lint !e9087 cast used for portability. */

    if( ( xSocket != SOCKETS_INVALID_SOCKET ) &&
        ( pvBuffer != NULL ) )
    {
        pxContext->xSendFlags = ( BaseType_t ) ulFlags;

        /* Send unencrypted. */
        lStatus = prvNetworkSend( pxContext, pvBuffer, xDataLength );
    }
    else
    {
        lStatus = SOCKETS_EINVAL;
    }

    return lStatus;
}
/*-----------------------------------------------------------*/

int32_t SOCKETS_SetSockOpt( Socket_t xSocket,
                            int32_t lLevel,
                            int32_t lOptionName,
                            const void * pvOptionValue,
                            size_t xOptionLength )
{
    int32_t lStatus = SOCKETS_ERROR_NONE;
    TickType_t xTimeout;
    SSOCKETContextPtr_t pxContext = ( SSOCKETContextPtr_t ) xSocket; /*lint !e9087 cast used for portability. */

    if( ( xSocket != SOCKETS_INVALID_SOCKET ) && ( xSocket != NULL ) )
    {
        switch( lOptionName )
        {
            case SOCKETS_SO_NONBLOCK:
                xTimeout = 0;

                /* Non-blocking connect is not supported.  Socket may be set to nonblocking
                 * only after a connection is made. */
                if( pdTRUE == pxContext->xConnectAttempted )
                {
                    lStatus = FreeRTOS_setsockopt( pxContext->xSocket,
                                                   lLevel,
                                                   SOCKETS_SO_RCVTIMEO,
                                                   &xTimeout,
                                                   sizeof( xTimeout ) );

                    if( lStatus == SOCKETS_ERROR_NONE )
                    {
                        lStatus = FreeRTOS_setsockopt( pxContext->xSocket,
                                                       lLevel,
                                                       SOCKETS_SO_SNDTIMEO,
                                                       &xTimeout,
                                                       sizeof( xTimeout ) );
                    }
                }
                else
                {
                    lStatus = SOCKETS_EISCONN;
                }

                break;

            case SOCKETS_SO_RCVTIMEO:
            case SOCKETS_SO_SNDTIMEO:
                /* Comply with Berkeley standard - a 0 timeout is wait forever. */
                xTimeout = *( ( const TickType_t * ) pvOptionValue ); /*lint !e9087 pvOptionValue passed should be of TickType_t */

                if( xTimeout == 0U )
                {
                    xTimeout = portMAX_DELAY;
                }

                lStatus = FreeRTOS_setsockopt( pxContext->xSocket,
                                               lLevel,
                                               lOptionName,
                                               &xTimeout,
                                               xOptionLength );
                break;

            default:
                lStatus = FreeRTOS_setsockopt( pxContext->xSocket,
                                               lLevel,
                                               lOptionName,
                                               pvOptionValue,
                                               xOptionLength );
                break;
        }
    }
    else
    {
        lStatus = SOCKETS_EINVAL;
    }

    return lStatus;
}
/*-----------------------------------------------------------*/

int32_t SOCKETS_Shutdown( Socket_t xSocket,
                          uint32_t ulHow )
{
    int32_t lReturn;
    SSOCKETContextPtr_t pxContext = ( SSOCKETContextPtr_t ) xSocket; /*lint !e9087 cast used for portability. */

    if( ( xSocket != SOCKETS_INVALID_SOCKET ) && ( xSocket != NULL ) )
    {
        lReturn = FreeRTOS_shutdown( pxContext->xSocket, ( BaseType_t ) ulHow );
    }
    else
    {
        lReturn = SOCKETS_EINVAL;
    }

    return lReturn;
}
/*-----------------------------------------------------------*/

Socket_t SOCKETS_Socket( int32_t lDomain,
                         int32_t lType,
                         int32_t lProtocol )
{
    SSOCKETContextPtr_t pxContext = NULL;
    Socket_t xSocket;

    /* Ensure that only supported values are supplied. */
    configASSERT( lDomain == SOCKETS_AF_INET );
    configASSERT( lType == SOCKETS_SOCK_STREAM );
    configASSERT( lProtocol == SOCKETS_IPPROTO_TCP );

    /* Create the wrapped socket. */
    xSocket = FreeRTOS_socket( lDomain, lType, lProtocol );

    if( xSocket != FREERTOS_INVALID_SOCKET )
    {
        /* Allocate the internal context structure. */
        if( NULL == ( pxContext = pvPortMalloc( sizeof( SSOCKETContext_t ) ) ) )
        {
            /* Need to close socket. */
            ( void ) FreeRTOS_closesocket( xSocket );
            pxContext = SOCKETS_INVALID_SOCKET;
        }
        else
        {
            memset( pxContext, 0, sizeof( SSOCKETContext_t ) );
            pxContext->xSocket = xSocket;
        }
    }
    else
    {
        pxContext = SOCKETS_INVALID_SOCKET;
    }

    return pxContext;
}
/*-----------------------------------------------------------*/

BaseType_t SOCKETS_Init( void )
{
    /* Empty initialization for this port. */
    return pdPASS;
}
/*-----------------------------------------------------------*/
