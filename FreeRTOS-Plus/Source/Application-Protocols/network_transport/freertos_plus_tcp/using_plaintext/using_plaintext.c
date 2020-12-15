/*
 * FreeRTOS V202012.00
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
#include <string.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_Sockets.h"

/* FreeRTOS Socket wrapper include. */
#include "sockets_wrapper.h"

/* Transport interface include. */
#include "using_plaintext.h"

/*-----------------------------------------------------------*/

/** 
 * @brief Each compilation unit that consumes the NetworkContext must define it. 
 * It should contain a single pointer as seen below whenever the header file
 * of this transport implementation is included to your project.
 *
 * @note When using multiple transports in the same compilation unit,
 *       define this pointer as void *.
 */
struct NetworkContext
{
    PlaintextTransportParams_t * pParams;
};

/*-----------------------------------------------------------*/

PlaintextTransportStatus_t Plaintext_FreeRTOS_Connect( NetworkContext_t * pNetworkContext,
                                                       const char * pHostName,
                                                       uint16_t port,
                                                       uint32_t receiveTimeoutMs,
                                                       uint32_t sendTimeoutMs )
{
    PlaintextTransportParams_t * pPlaintextTransportParams = NULL;
    PlaintextTransportStatus_t plaintextStatus = PLAINTEXT_TRANSPORT_SUCCESS;
    BaseType_t socketStatus = 0;

    if( ( pNetworkContext == NULL ) || ( pNetworkContext->pParams == NULL ) || ( pHostName == NULL ) )
    {
        LogError( ( "Invalid input parameter(s): Arguments cannot be NULL. pNetworkContext=%p, "
                    "pHostName=%p.",
                    pNetworkContext,
                    pHostName ) );
        plaintextStatus = PLAINTEXT_TRANSPORT_INVALID_PARAMETER;
    }
    else
    {
        pPlaintextTransportParams = pNetworkContext->pParams;
        /* Establish a TCP connection with the server. */
        socketStatus = Sockets_Connect( &( pPlaintextTransportParams->tcpSocket ),
                                        pHostName,
                                        port,
                                        receiveTimeoutMs,
                                        sendTimeoutMs );

        /* A non zero status is an error. */
        if( socketStatus != 0 )
        {
            LogError( ( "Failed to connect to %s with error %d.",
                        pHostName,
                        socketStatus ) );
            plaintextStatus = PLAINTEXT_TRANSPORT_CONNECT_FAILURE;
        }
    }

    return plaintextStatus;
}

PlaintextTransportStatus_t Plaintext_FreeRTOS_Disconnect( const NetworkContext_t * pNetworkContext )
{
    PlaintextTransportParams_t * pPlaintextTransportParams = NULL;
    PlaintextTransportStatus_t plaintextStatus = PLAINTEXT_TRANSPORT_SUCCESS;

    if( ( pNetworkContext == NULL ) || ( pNetworkContext->pParams == NULL ) )
    {
        LogError( ( "pNetworkContext cannot be NULL." ) );
        plaintextStatus = PLAINTEXT_TRANSPORT_INVALID_PARAMETER;
    }
    else if( pNetworkContext->pParams->tcpSocket == FREERTOS_INVALID_SOCKET )
    {
        LogError( ( "pPlaintextTransportParams->tcpSocket cannot be an invalid socket." ) );
        plaintextStatus = PLAINTEXT_TRANSPORT_INVALID_PARAMETER;
    }
    else
    {
        pPlaintextTransportParams = pNetworkContext->pParams;
        /* Call socket disconnect function to close connection. */
        Sockets_Disconnect( pPlaintextTransportParams->tcpSocket );
    }

    return plaintextStatus;
}

int32_t Plaintext_FreeRTOS_recv( NetworkContext_t * pNetworkContext,
                                 void * pBuffer,
                                 size_t bytesToRecv )
{
    PlaintextTransportParams_t * pPlaintextTransportParams = NULL;
    int32_t socketStatus = 1;

    configASSERT( ( pNetworkContext != NULL ) && ( pNetworkContext->pParams != NULL ) );

    pPlaintextTransportParams = pNetworkContext->pParams;

    /* The TCP socket may have a receive block time.  If bytesToRecv is greater 
     * than 1 then a frame is likely already part way through reception and 
     * blocking to wait for the desired number of bytes to be available is the
     * most efficient thing to do.  If bytesToRecv is 1 then this may be a 
     * speculative call to read to find the start of a new frame, in which case 
     * blocking is not desirable as it could block an entire protocol agent 
     * task for the duration of the read block time and therefore negatively 
     * impact performance.  So if bytesToRecv is 1 then don't call recv unless 
     * it is known that bytes are already available. */
    if( bytesToRecv == 1 )
    {
        socketStatus = ( int32_t ) FreeRTOS_recvcount( pPlaintextTransportParams->tcpSocket );
    }

    if( socketStatus > 0 )
    {
        socketStatus = FreeRTOS_recv( pPlaintextTransportParams->tcpSocket,
                                      pBuffer,
                                      bytesToRecv,
                                      0 );
    }

    return socketStatus;
}

int32_t Plaintext_FreeRTOS_send( NetworkContext_t * pNetworkContext,
                                 const void * pBuffer,
                                 size_t bytesToSend )
{
    PlaintextTransportParams_t * pPlaintextTransportParams = NULL;
    int32_t socketStatus = 0;

    configASSERT( ( pNetworkContext != NULL ) && ( pNetworkContext->pParams != NULL ) );

    pPlaintextTransportParams = pNetworkContext->pParams;
    socketStatus = FreeRTOS_send( pPlaintextTransportParams->tcpSocket,
                                  pBuffer,
                                  bytesToSend,
                                  0 );

    if( socketStatus == -pdFREERTOS_ERRNO_ENOSPC )
    {
        /* The TCP buffers could not accept any more bytes so zero bytes were sent.
         * This is not necessarily an error that should cause a disconnect
         * unless it persists. */
        socketStatus = 0;
    }

    return socketStatus;
}
