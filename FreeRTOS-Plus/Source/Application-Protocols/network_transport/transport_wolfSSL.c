/*
 * FreeRTOS V202212.00
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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
#include "transport_wolfSSL.h"

/* FreeRTOS Socket wrapper include. */
#include "tcp_sockets_wrapper.h"

/* wolfSSL user settings header */
#include "user_settings.h"

/* Demo Specific configs. */
#include "demo_config.h"

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
static TlsTransportStatus_t initTLS( void );

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
static int wolfSSL_IORecvGlue( WOLFSSL * ssl,
                               char * buf,
                               int sz,
                               void * context );

/*
 *  @brief  Send date to the socket passed as the context
 *
 *  @param[in] ssl WOLFSSL object.
 *  @param[in] buf Buffer for data to be sent
 *  @param[in] sz  Size to send
 *  @param[in] context Socket to be sent to
 *
 *  @return received size( > 0 ), #WOLFSSL_CBIO_ERR_CONN_CLOSE, #WOLFSSL_CBIO_ERR_WANT_WRITE.
 */
static int wolfSSL_IOSendGlue( WOLFSSL * ssl,
                               char * buf,
                               int sz,
                               void * context );

/*
 *  @brief  Load credentials from file/buffer
 *
 *  @param[in] pNetCtx  NetworkContext_t
 *  @param[in] pNetCred NetworkCredentials_t
 *
 *  @return #TLS_TRANSPORT_SUCCESS, #TLS_TRANSPORT_INVALID_CREDENTIALS.
 */
static TlsTransportStatus_t loadCredentials( NetworkContext_t * pNetCtx,
                                             const NetworkCredentials_t * pNetCred );

/*-----------------------------------------------------------*/
static int wolfSSL_IORecvGlue( WOLFSSL * ssl,
                               char * buf,
                               int sz,
                               void * context )
{
    ( void ) ssl; /* to prevent unused warning*/
    BaseType_t read = 0;

    Socket_t xSocket = ( Socket_t ) context;


    read = TCP_Sockets_Recv( xSocket, ( void * ) buf, ( size_t ) sz );

    if( ( read == 0 ) ||
        ( read == TCP_SOCKETS_ERRNO_EWOULDBLOCK ) )
    {
        read = WOLFSSL_CBIO_ERR_WANT_READ;
    }
    else if( read == TCP_SOCKETS_ERRNO_ENOTCONN )
    {
        read = WOLFSSL_CBIO_ERR_CONN_CLOSE;
    }
    else
    {
        /* do nothing */
    }

    return ( int ) read;
}
/*-----------------------------------------------------------*/

static int wolfSSL_IOSendGlue( WOLFSSL * ssl,
                               char * buf,
                               int sz,
                               void * context )
{
    ( void ) ssl; /* to prevent unused warning*/
    Socket_t xSocket = ( Socket_t ) context;
    BaseType_t sent = TCP_Sockets_Send( xSocket, ( void * ) buf, ( size_t ) sz );

    if( sent == TCP_SOCKETS_ERRNO_EWOULDBLOCK )
    {
        sent = WOLFSSL_CBIO_ERR_WANT_WRITE;
    }
    else if( sent == TCP_SOCKETS_ERRNO_ENOTCONN )
    {
        sent = WOLFSSL_CBIO_ERR_CONN_CLOSE;
    }
    else
    {
        /* do nothing */
    }

    return ( int ) sent;
}

/*-----------------------------------------------------------*/
static TlsTransportStatus_t initTLS( void )
{
    /* initialize wolfSSL */
    wolfSSL_Init();

    #ifdef DEBUG_WOLFSSL
        wolfSSL_Debugging_ON();
    #endif

    return TLS_TRANSPORT_SUCCESS;
}

/*-----------------------------------------------------------*/
static TlsTransportStatus_t loadCredentials( NetworkContext_t * pNetCtx,
                                             const NetworkCredentials_t * pNetCred )
{
    TlsTransportStatus_t returnStatus = TLS_TRANSPORT_SUCCESS;

    configASSERT( pNetCtx != NULL );
    configASSERT( pNetCred != NULL );

    #if defined( democonfigCREDENTIALS_IN_BUFFER )
        if( wolfSSL_CTX_load_verify_buffer( pNetCtx->sslContext.ctx,
                                            ( const byte * ) ( pNetCred->pRootCa ), ( long ) ( pNetCred->rootCaSize ),
                                            SSL_FILETYPE_PEM ) == SSL_SUCCESS )
        {
            if( wolfSSL_CTX_use_certificate_buffer( pNetCtx->sslContext.ctx,
                                                    ( const byte * ) ( pNetCred->pClientCert ), ( long ) ( pNetCred->clientCertSize ),
                                                    SSL_FILETYPE_PEM ) == SSL_SUCCESS )
            {
                if( wolfSSL_CTX_use_PrivateKey_buffer( pNetCtx->sslContext.ctx,
                                                       ( const byte * ) ( pNetCred->pPrivateKey ), ( long ) ( pNetCred->privateKeySize ),
                                                       SSL_FILETYPE_PEM ) == SSL_SUCCESS )
                {
                    returnStatus = TLS_TRANSPORT_SUCCESS;
                }
                else
                {
                    LogError( ( "Failed to load client-private-key from buffer" ) );
                    returnStatus = TLS_TRANSPORT_INVALID_CREDENTIALS;
                }
            }
            else
            {
                LogError( ( "Failed to load client-certificate from buffer" ) );
                returnStatus = TLS_TRANSPORT_INVALID_CREDENTIALS;
            }
        }
        else
        {
            LogError( ( "Failed to load ca-certificate from buffer" ) );
            returnStatus = TLS_TRANSPORT_INVALID_CREDENTIALS;
        }

        return returnStatus;
    #else /* if defined( democonfigCREDENTIALS_IN_BUFFER ) */
        if( wolfSSL_CTX_load_verify_locations( pNetCtx->sslContext.ctx,
                                               ( const char * ) ( pNetCred->pRootCa ), NULL ) == SSL_SUCCESS )
        {
            if( wolfSSL_CTX_use_certificate_file( pNetCtx->sslContext.ctx,
                                                  ( const char * ) ( pNetCred->pClientCert ), SSL_FILETYPE_PEM )
                == SSL_SUCCESS )
            {
                if( wolfSSL_CTX_use_PrivateKey_file( pNetCtx->sslContext.ctx,
                                                     ( const char * ) ( pNetCred->pPrivateKey ), SSL_FILETYPE_PEM )
                    == SSL_SUCCESS )
                {
                    returnStatus = TLS_TRANSPORT_SUCCESS;
                }
                else
                {
                    LogError( ( "Failed to load client-private-key file" ) );
                    returnStatus = TLS_TRANSPORT_INVALID_CREDENTIALS;
                }
            }
            else
            {
                LogError( ( "Failed to load client-certificate file" ) );
                returnStatus = TLS_TRANSPORT_INVALID_CREDENTIALS;
            }
        }
        else
        {
            LogError( ( "Failed to load ca-certificate file" ) );
            returnStatus = TLS_TRANSPORT_INVALID_CREDENTIALS;
        }
        return returnStatus;
    #endif /* if defined( democonfigCREDENTIALS_IN_BUFFER ) */
}

/*-----------------------------------------------------------*/

static TlsTransportStatus_t tlsSetup( NetworkContext_t * pNetCtx,
                                      const char * pHostName,
                                      const NetworkCredentials_t * pNetCred )
{
    TlsTransportStatus_t returnStatus = TLS_TRANSPORT_SUCCESS;
    Socket_t xSocket = { 0 };

    configASSERT( pNetCtx != NULL );
    configASSERT( pHostName != NULL );
    configASSERT( pNetCred != NULL );
    configASSERT( pNetCred->pRootCa != NULL );
    configASSERT( pNetCtx->tcpSocket != NULL );

    if( pNetCtx->sslContext.ctx == NULL )
    {
        /* Attempt to create a context that uses the TLS 1.3 or 1.2 */
        pNetCtx->sslContext.ctx =
            wolfSSL_CTX_new( wolfSSLv23_client_method_ex( NULL ) );
    }

    if( pNetCtx->sslContext.ctx != NULL )
    {
        /* load credentials from file */
        if( loadCredentials( pNetCtx, pNetCred ) == TLS_TRANSPORT_SUCCESS )
        {
            /* create a ssl object */
            pNetCtx->sslContext.ssl =
                wolfSSL_new( pNetCtx->sslContext.ctx );

            if( pNetCtx->sslContext.ssl != NULL )
            {
                xSocket = pNetCtx->tcpSocket;

                /* set Recv/Send glue functions to the WOLFSSL object */
                wolfSSL_SSLSetIORecv( pNetCtx->sslContext.ssl,
                                      wolfSSL_IORecvGlue );
                wolfSSL_SSLSetIOSend( pNetCtx->sslContext.ssl,
                                      wolfSSL_IOSendGlue );

                /* set socket as a context of read/send glue funcs */
                wolfSSL_SetIOReadCtx( pNetCtx->sslContext.ssl, xSocket );
                wolfSSL_SetIOWriteCtx( pNetCtx->sslContext.ssl, xSocket );

                /* let wolfSSL perform tls handshake */
                if( wolfSSL_connect( pNetCtx->sslContext.ssl )
                    == SSL_SUCCESS )
                {
                    returnStatus = TLS_TRANSPORT_SUCCESS;
                }
                else
                {
                    wolfSSL_shutdown( pNetCtx->sslContext.ssl );
                    wolfSSL_free( pNetCtx->sslContext.ssl );
                    pNetCtx->sslContext.ssl = NULL;
                    wolfSSL_CTX_free( pNetCtx->sslContext.ctx );
                    pNetCtx->sslContext.ctx = NULL;

                    LogError( ( "Failed to establish a TLS connection" ) );
                    returnStatus = TLS_TRANSPORT_HANDSHAKE_FAILED;
                }
            }
            else
            {
                wolfSSL_CTX_free( pNetCtx->sslContext.ctx );
                pNetCtx->sslContext.ctx = NULL;

                LogError( ( "Failed to create wolfSSL object" ) );
                returnStatus = TLS_TRANSPORT_INTERNAL_ERROR;
            }
        }
        else
        {
            wolfSSL_CTX_free( pNetCtx->sslContext.ctx );
            pNetCtx->sslContext.ctx = NULL;

            LogError( ( "Failed to load credentials" ) );
            returnStatus = TLS_TRANSPORT_INVALID_CREDENTIALS;
        }
    }
    else
    {
        LogError( ( "Failed to create a wolfSSL_CTX" ) );
        returnStatus = TLS_TRANSPORT_CONNECT_FAILURE;
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
    BaseType_t isSocketConnected = pdFALSE;

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
        pNetworkContext->tcpSocket = NULL;

        socketStatus = TCP_Sockets_Connect( &( pNetworkContext->tcpSocket ),
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
        isSocketConnected = pdTRUE;

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
        if( isSocketConnected == pdTRUE )
        {
            TCP_Sockets_Disconnect( pNetworkContext->tcpSocket );
            pNetworkContext->tcpSocket = NULL;
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
    WOLFSSL * pSsl = pNetworkContext->sslContext.ssl;
    WOLFSSL_CTX * pCtx = NULL;

    /* shutdown an active TLS connection */
    wolfSSL_shutdown( pSsl );

    /* cleanup WOLFSSL object */
    wolfSSL_free( pSsl );
    pNetworkContext->sslContext.ssl = NULL;

    /* Call socket shutdown function to close connection. */
    TCP_Sockets_Disconnect( pNetworkContext->tcpSocket );

    /* free WOLFSSL_CTX object*/
    pCtx = pNetworkContext->sslContext.ctx;

    wolfSSL_CTX_free( pCtx );
    pNetworkContext->sslContext.ctx = NULL;

    wolfSSL_Cleanup();
}

/*-----------------------------------------------------------*/

int32_t TLS_FreeRTOS_recv( NetworkContext_t * pNetworkContext,
                           void * pBuffer,
                           size_t bytesToRecv )
{
    int32_t tlsStatus = 0;
    int iResult = 0;
    WOLFSSL * pSsl = NULL;

    if( ( pNetworkContext == NULL ) || ( pNetworkContext->sslContext.ssl == NULL ) )
    {
        LogError( ( "invalid input, pNetworkContext=%p", pNetworkContext ) );
        tlsStatus = -1;
    }
    else if( pBuffer == NULL )
    {
        LogError( ( "invalid input, pBuffer == NULL" ) );
        tlsStatus = -1;
    }
    else if( bytesToRecv == 0 )
    {
        LogError( ( "invalid input, bytesToRecv == 0" ) );
        tlsStatus = -1;
    }
    else
    {
        pSsl = pNetworkContext->sslContext.ssl;

        iResult = wolfSSL_read( pSsl, pBuffer, bytesToRecv );

        if( iResult > 0 )
        {
            tlsStatus = iResult;
        }
        else if( wolfSSL_want_read( pSsl ) == 1 )
        {
            tlsStatus = 0;
        }
        else
        {
            tlsStatus = wolfSSL_state( pSsl );
            LogError( ( "Error from wolfSSL_read %d : %s ",
                        iResult, wolfSSL_ERR_reason_error_string( tlsStatus ) ) );
        }
    }

    return tlsStatus;
}

/*-----------------------------------------------------------*/

int32_t TLS_FreeRTOS_send( NetworkContext_t * pNetworkContext,
                           const void * pBuffer,
                           size_t bytesToSend )
{
    int32_t tlsStatus = 0;
    int iResult = 0;
    WOLFSSL * pSsl = NULL;

    if( ( pNetworkContext == NULL ) || ( pNetworkContext->sslContext.ssl == NULL ) )
    {
        LogError( ( "invalid input, pNetworkContext=%p", pNetworkContext ) );
        tlsStatus = -1;
    }
    else if( pBuffer == NULL )
    {
        LogError( ( "invalid input, pBuffer == NULL" ) );
        tlsStatus = -1;
    }
    else if( bytesToSend == 0 )
    {
        LogError( ( "invalid input, bytesToSend == 0" ) );
        tlsStatus = -1;
    }
    else
    {
        pSsl = pNetworkContext->sslContext.ssl;

        iResult = wolfSSL_write( pSsl, pBuffer, bytesToSend );

        if( iResult > 0 )
        {
            tlsStatus = iResult;
        }
        else if( wolfSSL_want_write( pSsl ) == 1 )
        {
            tlsStatus = 0;
        }
        else
        {
            tlsStatus = wolfSSL_state( pSsl );
            LogError( ( "Error from wolfSL_write %d : %s ",
                        iResult, wolfSSL_ERR_reason_error_string( tlsStatus ) ) );
        }
    }

    return tlsStatus;
}
/*-----------------------------------------------------------*/
