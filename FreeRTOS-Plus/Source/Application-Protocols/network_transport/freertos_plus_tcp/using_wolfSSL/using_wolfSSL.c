/*
 * FreeRTOS V202011.00
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
 * @file using_wolfSSL.c
 * @brief TLS transport interface implementations. This implementation uses
 * wolfSSL.
 */

/* Standard includes. */
#include <string.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_Sockets.h"

/* TLS transport header. */
#include "using_wolfSSL.h"

/* FreeRTOS Socket wrapper include. */
#include "sockets_wrapper.h"


/* wolfSSL user settings header */
#include "user_settings.h"

/**
 * @brief Initialize the TLS structures in a network connection.
 *
 * @param[in] pSslContext The SSL context to initialize.
 */
static void sslContextInit( SSLContext_t * pSslContext );

/**
 * @brief Free the TLS structures in a network connection.
 *
 * @param[in] pSslContext The SSL context to free.
 */
static void sslContextFree( SSLContext_t * pSslContext );

/**
 * @brief Set up TLS on a TCP connection.
 *
 * @param[in] pNetworkContext Network context.
 * @param[in] pHostName Remote host name, used for server name indication.
 * @param[in] pNetworkCredentials TLS setup parameters.
 *
 * @return #TLS_TRANSPORT_SUCCESS, #TLS_TRANSPORT_INSUFFICIENT_MEMORY, #TLS_TRANSPORT_INVALID_CREDENTIALS,
 * #TLS_TRANSPORT_HANDSHAKE_FAILED, or #TLS_TRANSPORT_INTERNAL_ERROR.
 */
static TlsTransportStatus_t tlsSetup( NetworkContext_t * pNetworkContext,
                                      const char * pHostName,
                                      const NetworkCredentials_t * pNetworkCredentials );

/**
 * @brief  Initialize TLS component.
 *
 * @return #TLS_TRANSPORT_SUCCESS, #TLS_TRANSPORT_INSUFFICIENT_MEMORY, or #TLS_TRANSPORT_INTERNAL_ERROR.
 */
static TlsTransportStatus_t initTLS(void);

/*
*  @brief  Receive date from the socket passed as the context
*
*  @param[in] ssl WOLFSSL object.
*  @param[in] buf Buffer for received data
*  @param[in] sz  Size to receive
*  @param[in] context Socket to be received from 
*  
*  @return received size( > 0 ), #WOLFSSL_CBIO_ERR_CONN_CLOSE, #WOLFSSL_CBIO_ERR_WANT_READ. 
*/
static int wolfSSL_IORecvGlue(WOLFSSL* ssl, char* buf, int sz, void* context);





/*-----------------------------------------------------------*/
static int wolfSSL_IORecvGlue(WOLFSSL* ssl, char* buf, int sz, void* context)
{
    ssl;    /* to prevent unused warning*/

    Socket_t xSocket = (Socket_t)context;

    BaseType_t read;
  
    read = FreeRTOS_recv(xSocket, (void*)buf, (size_t)sz, 0);


    if ((read == 0 ) ||
        (read == -pdFREERTOS_ERRNO_EWOULDBLOCK))
    {
        read = WOLFSSL_CBIO_ERR_WANT_READ;
    }
    else if (read == -pdFREERTOS_ERRNO_ENOTCONN)
    {
        read = WOLFSSL_CBIO_ERR_CONN_CLOSE;
    }
    else
    {
        /* do nothing */
    }
    return (int)read;
}
/*-----------------------------------------------------------*/

static int wolfSSL_IOSendGlue(WOLFSSL* ssl, char* buf, int sz, void* context)
{
    ssl;    /* to prevent unused warning*/

    Socket_t xSocket = (Socket_t)context;

    BaseType_t sent = FreeRTOS_send(xSocket, (void*)buf, (size_t)sz, 0);

    if ( sent == -pdFREERTOS_ERRNO_EWOULDBLOCK )
    {
        sent = WOLFSSL_CBIO_ERR_WANT_WRITE;
    }
    else if ( sent == -pdFREERTOS_ERRNO_ENOTCONN )
    {
        sent = WOLFSSL_CBIO_ERR_CONN_CLOSE;
    }
    else
    {
        /* do nothing */
    }
    return (int)sent;
}

/*-----------------------------------------------------------*/
static TlsTransportStatus_t initTLS(void)
{
    /* initialize wolfSSL */
    wolfSSL_Init();

#ifdef DEBUG_WOLFSSL
    wolfSSL_Debugging_ON();
#endif

    return TLS_TRANSPORT_SUCCESS;
}

/*-----------------------------------------------------------*/

static TlsTransportStatus_t tlsSetup( NetworkContext_t * pNetworkContext,
                                      const char * pHostName,
                                      const NetworkCredentials_t * pNetworkCredentials )
{
    TlsTransportStatus_t returnStatus = TLS_TRANSPORT_SUCCESS;
    int iResult = SSL_SUCCESS;
    /*char errString[80];*/

    configASSERT( pNetworkContext != NULL );
    configASSERT( pHostName != NULL );
    configASSERT( pNetworkCredentials != NULL );
    configASSERT( pNetworkCredentials->pRootCa != NULL );
    configASSERT( pNetworkContext->tcpSocket != NULL );
    
    if (pNetworkContext->sslContext.ctx == NULL)
    {
        /* Attempt to create a context that uses the TLS 1.3 or 1.2 client protocol. */
        pNetworkContext->sslContext.ctx = wolfSSL_CTX_new(wolfSSLv23_client_method_ex(NULL));
    }

    if (pNetworkContext->sslContext.ctx == NULL)
    {
        LogError(("Failed to create a wolfSSL_CTX"));
        returnStatus = TLS_TRANSPORT_CONNECT_FAILURE;
        return returnStatus;
    }

    /* attempt to load ca cert file, client cert file and client private key file */
    iResult = wolfSSL_CTX_load_verify_locations(pNetworkContext->sslContext.ctx,
        (const char*)(pNetworkCredentials->pRootCa), NULL);

    if (iResult == SSL_SUCCESS)
    {
        iResult = wolfSSL_CTX_use_certificate_file(pNetworkContext->sslContext.ctx,
            (const char*)(pNetworkCredentials->pClientCert), SSL_FILETYPE_PEM);
    }
    else
    {
        LogError(("Failed to load ca-certificate file"));
        returnStatus = TLS_TRANSPORT_INVALID_CREDENTIALS;
    }
 
    if (iResult == SSL_SUCCESS)
    {
        iResult = wolfSSL_CTX_use_PrivateKey_file(pNetworkContext->sslContext.ctx,
            (const char*)(pNetworkCredentials->pPrivateKey), SSL_FILETYPE_PEM);
    }
    else
    {
        LogError(("Failed to load client-certificate file"));
        returnStatus = TLS_TRANSPORT_INVALID_CREDENTIALS;
    }

    if (iResult != SSL_SUCCESS)
    {
        LogError(("Failed to load client-private-key file"));
        returnStatus = TLS_TRANSPORT_INVALID_CREDENTIALS;
    }
 
    /* on success of file loading, attempt to create a ssl object */
    if (returnStatus == TLS_TRANSPORT_SUCCESS)
    {
        /* create a ssl object */
        pNetworkContext->sslContext.ssl = wolfSSL_new(pNetworkContext->sslContext.ctx);
        Socket_t xSocket = pNetworkContext->tcpSocket;

        if (pNetworkContext->sslContext.ssl != NULL)
        {
            /* set Recv/Send glue functions to the WOLFSSL object */
            wolfSSL_SSLSetIORecv(pNetworkContext->sslContext.ssl, wolfSSL_IORecvGlue);
            wolfSSL_SSLSetIOSend(pNetworkContext->sslContext.ssl, wolfSSL_IOSendGlue);

            /* set FreeRTOS socket as the context of read/send glue functions */
            wolfSSL_SetIOReadCtx(pNetworkContext->sslContext.ssl, xSocket);
            wolfSSL_SetIOWriteCtx(pNetworkContext->sslContext.ssl, xSocket);

            /* let wolfSSL perform tls handshake */
            iResult = wolfSSL_connect( pNetworkContext->sslContext.ssl );

            if (iResult != SSL_SUCCESS)
            {
                wolfSSL_shutdown(pNetworkContext->sslContext.ssl);
                wolfSSL_free(pNetworkContext->sslContext.ssl);
                pNetworkContext->sslContext.ssl = NULL;

                LogError(("Failed to establish a TLS connection"));
                returnStatus = TLS_TRANSPORT_HANDSHAKE_FAILED;
            }
        }
    }

    return returnStatus;
}

/*-----------------------------------------------------------*/


/*-----------------------------------------------------------*/

TlsTransportStatus_t TLS_FreeRTOS_Connect( NetworkContext_t * pNetworkContext,
                                           const char * pHostName,
                                           uint16_t port,
                                           const NetworkCredentials_t * pNetworkCredentials,
                                           uint32_t receiveTimeoutMs,
                                           uint32_t sendTimeoutMs )
{
    TlsTransportStatus_t returnStatus = TLS_TRANSPORT_SUCCESS;
    BaseType_t socketStatus = 0;
    

    if( ( pNetworkContext == NULL ) ||
        ( pHostName == NULL ) ||
        ( pNetworkCredentials == NULL ) )
    {
        LogError( ( "Invalid input parameter(s): Arguments cannot be NULL. pNetworkContext=%p, "
                    "pHostName=%p, pNetworkCredentials=%p.",
                    pNetworkContext,
                    pHostName,
                    pNetworkCredentials ) );
        returnStatus = TLS_TRANSPORT_INVALID_PARAMETER;
    }
    else if( ( pNetworkCredentials->pRootCa == NULL ) )
    {
        LogError( ( "pRootCa cannot be NULL." ) );
        returnStatus = TLS_TRANSPORT_INVALID_PARAMETER;
    }

    /* Establish a TCP connection with the server. */
    if( returnStatus == TLS_TRANSPORT_SUCCESS )
    {
        socketStatus = Sockets_Connect( &( pNetworkContext->tcpSocket ),
                                        pHostName,
                                        port,
                                        receiveTimeoutMs,
                                        sendTimeoutMs );

        if( socketStatus != 0 )
        {
            LogError( ( "Failed to connect to %s with error %d.",
                        pHostName,
                        socketStatus ) );
            returnStatus = TLS_TRANSPORT_CONNECT_FAILURE;
        }
    }

    /* Initialize tls. */
    if( returnStatus == TLS_TRANSPORT_SUCCESS )
    { 
        returnStatus = initTLS();
    }

    /* Perform TLS handshake. */
    if( returnStatus == TLS_TRANSPORT_SUCCESS )
    {
        returnStatus = tlsSetup( pNetworkContext, pHostName, pNetworkCredentials );
    }

    /* Clean up on failure. */
    if( returnStatus != TLS_TRANSPORT_SUCCESS )
    {
        if( pNetworkContext->tcpSocket != FREERTOS_INVALID_SOCKET )
        {
            FreeRTOS_closesocket( pNetworkContext->tcpSocket );
        }
    }
    else
    {
        LogInfo( ( "(Network connection %p) Connection to %s established.",
                   pNetworkContext,
                   pHostName ) );
    }

    return returnStatus;
}

/*-----------------------------------------------------------*/

void TLS_FreeRTOS_Disconnect( NetworkContext_t * pNetworkContext )
{
    WOLFSSL* pSsl = pNetworkContext->sslContext.ssl;

    /* shutdown an active TLS connection */
    wolfSSL_shutdown(pSsl);

    /* cleanup WOLFSSL object */
    wolfSSL_free(pSsl);
    pNetworkContext->sslContext.ssl = NULL;

    /* Call socket shutdown function to close connection. */
    Sockets_Disconnect(pNetworkContext->tcpSocket);

    /* free WOLFSSL_CTX object*/
    WOLFSSL_CTX* pCtx = pNetworkContext->sslContext.ctx;
    wolfSSL_CTX_free(pCtx);
    pNetworkContext->sslContext.ctx = NULL;

    wolfSSL_Cleanup();
}

/*-----------------------------------------------------------*/

int32_t TLS_FreeRTOS_recv( NetworkContext_t * pNetworkContext,
                           void * pBuffer,
                           size_t bytesToRecv )
{
    int32_t tlsStatus = 0;
    int  iResult = 0;
    WOLFSSL* pSsl = pNetworkContext->sslContext.ssl;
    
    iResult = wolfSSL_read( pSsl, pBuffer, bytesToRecv );

    
    if (iResult > 0)
        tlsStatus = iResult;
    else
        tlsStatus = 0;
        
    return tlsStatus;
}

/*-----------------------------------------------------------*/

int32_t TLS_FreeRTOS_send( NetworkContext_t * pNetworkContext,
                           const void * pBuffer,
                           size_t bytesToSend )
{
    int32_t tlsStatus = 0;
    int  iResult = 0;
    
    iResult = wolfSSL_write(pNetworkContext->sslContext.ssl, pBuffer, bytesToSend);
    
    if (iResult > 0)
        tlsStatus = iResult;
    else
        tlsStatus = 0;

    return tlsStatus;
}
/*-----------------------------------------------------------*/
