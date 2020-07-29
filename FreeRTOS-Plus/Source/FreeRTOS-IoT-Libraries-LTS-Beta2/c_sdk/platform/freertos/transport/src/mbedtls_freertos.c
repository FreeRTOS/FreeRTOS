/*
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
 */

/* Standard includes. */
#include <string.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_Sockets.h"

/* Transport interface include. */
#include "mbedtls_freertos.h"

/* FreeRTOS Socket wrapper include. */
#include "sockets_freertos.h"

/*-----------------------------------------------------------*/

/**
 * @brief mbed TLS entropy context for generation of random numbers.
 */
static mbedtls_entropy_context entropyContext;

/**
 * @brief mbed TLS CTR DRBG context for generation of random numbers.
 */
static mbedtls_ctr_drbg_context ctrDrgbContext;

/*-----------------------------------------------------------*/

/**
 * @brief Initialize the mbed TLS structures in a network connection.
 *
 * @param[in] pSslContext The SSL context to initialize.
 */
static void sslContextInit( SSLContext_t * pSslContext );

/**
 * @brief Free the mbed TLS structures in a network connection.
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
 * @return #MBEDTLS_SUCCESS, #MBEDTLS_INSUFFICIENT_MEMORY, #MBEDTLS_INVALID_CREDENTIALS,
 * #MBEDTLS_HANDSHAKE_FAILED, or #MBEDTLS_API_ERROR.
 */
static MbedtlsStatus_t tlsSetup( NetworkContext_t * pNetworkContext,
                                 const char * pHostName,
                                 const NetworkCredentials_t * pNetworkCredentials );

/**
 * @brief Initialize mbedTLS.
 *
 * @return #MBEDTLS_SUCCESS, or #MBEDTLS_API_ERROR.
 */
static MbedtlsStatus_t initMbedtls( void );

/*-----------------------------------------------------------*/

static void sslContextInit( SSLContext_t * pSslContext )
{
    mbedtls_ssl_config_init( &( pSslContext->config ) );
    mbedtls_x509_crt_init( &( pSslContext->rootCa ) );
    mbedtls_pk_init( &( pSslContext->privKey ) );
    mbedtls_x509_crt_init( &( pSslContext->clientCert ) );
    mbedtls_ssl_init( &( pSslContext->context ) );
}
/*-----------------------------------------------------------*/

static void sslContextFree( SSLContext_t * pSslContext )
{
    mbedtls_ssl_free( &( pSslContext->context ) );
    mbedtls_x509_crt_free( &( pSslContext->rootCa ) );
    mbedtls_x509_crt_free( &( pSslContext->clientCert ) );
    mbedtls_pk_free( &( pSslContext->privKey ) );
    mbedtls_ssl_config_free( &( pSslContext->config ) );
}

/*-----------------------------------------------------------*/

static MbedtlsStatus_t tlsSetup( NetworkContext_t * pNetworkContext,
                                 const char * pHostName,
                                 const NetworkCredentials_t * pNetworkCredentials )
{
    MbedtlsStatus_t returnStatus = MBEDTLS_SUCCESS;
    int mbedtlsError = 0;

    /* Initialize the mbed TLS context structures. */
    sslContextInit( &( pNetworkContext->sslContext ) );

    mbedtlsError = mbedtls_ssl_config_defaults( &( pNetworkContext->sslContext.config ),
                                                MBEDTLS_SSL_IS_CLIENT,
                                                MBEDTLS_SSL_TRANSPORT_STREAM,
                                                MBEDTLS_SSL_PRESET_DEFAULT );

    if( mbedtlsError != 0 )
    {
        LogError( ( "Failed to set default SSL configuration, error %d.", mbedtlsError ) );

        /* Per mbed TLS docs, mbedtls_ssl_config_defaults only fails on memory allocation. */
        returnStatus = MBEDTLS_INSUFFICIENT_MEMORY;
    }

    if( returnStatus == MBEDTLS_SUCCESS )
    {
        /* Set up the certificate security profile, starting from the default value. */
        pNetworkContext->sslContext.certProfile = mbedtls_x509_crt_profile_default;

        /* test.mosquitto.org only provides a 1024-bit RSA certificate, which is
         * not acceptable by the default mbed TLS certificate security profile.
         * For the purposes of this demo, allow the use of 1024-bit RSA certificates.
         * This block should be removed otherwise. */
        if( strncmp( pHostName, "test.mosquitto.org", strlen( pHostName ) ) == 0 )
        {
            pNetworkContext->sslContext.certProfile.rsa_min_bitlen = 1024;
        }

        /* Set SSL authmode and the RNG context. */
        mbedtls_ssl_conf_authmode( &( pNetworkContext->sslContext.config ),
                                   MBEDTLS_SSL_VERIFY_REQUIRED );
        mbedtls_ssl_conf_rng( &( pNetworkContext->sslContext.config ),
                              mbedtls_ctr_drbg_random,
                              &ctrDrgbContext );
        mbedtls_ssl_conf_cert_profile( &( pNetworkContext->sslContext.config ),
                                       &( pNetworkContext->sslContext.certProfile ) );
    }

    if( returnStatus == MBEDTLS_SUCCESS )
    {
        /* Parse the server root CA certificate into the SSL context. */
        mbedtlsError = mbedtls_x509_crt_parse( &( pNetworkContext->sslContext.rootCa ),
                                               ( const unsigned char * ) pNetworkCredentials->pRootCa,
                                               pNetworkCredentials->rootCaSize );

        if( mbedtlsError != 0 )
        {
            LogError( ( "Failed to parse server root CA certificate, error %d.",
                        mbedtlsError ) );

            returnStatus = MBEDTLS_INVALID_CREDENTIALS;
        }
        else
        {
            mbedtls_ssl_conf_ca_chain( &( pNetworkContext->sslContext.config ),
                                       &( pNetworkContext->sslContext.rootCa ),
                                       NULL );
        }
    }

    if( returnStatus == MBEDTLS_SUCCESS )
    {
        if( ( pNetworkCredentials->pPrivateKey != NULL ) && ( pNetworkCredentials->pClientCert != NULL ) )
        {
            /* Setup the client private key. */
            mbedtlsError = mbedtls_pk_parse_key( &( pNetworkContext->sslContext.privKey ),
                                                 ( const unsigned char * ) pNetworkCredentials->pPrivateKey,
                                                 pNetworkCredentials->privateKeySize,
                                                 0,
                                                 0 );

            if( mbedtlsError != 0 )
            {
                LogError( ( "Failed to parse client certificate, error %d.",
                            mbedtlsError ) );

                returnStatus = MBEDTLS_INVALID_CREDENTIALS;
            }
            else
            {
                /* Setup the client certificate. */
                mbedtlsError = mbedtls_x509_crt_parse( &( pNetworkContext->sslContext.clientCert ),
                                                       ( const unsigned char * ) pNetworkCredentials->pClientCert,
                                                       pNetworkCredentials->clientCertSize );

                if( mbedtlsError != 0 )
                {
                    LogError( ( "Failed to parse the client private key, error %d.",
                                mbedtlsError ) );

                    returnStatus = MBEDTLS_INVALID_CREDENTIALS;
                }
                else
                {
                    mbedtls_ssl_conf_own_cert( &( pNetworkContext->sslContext.config ),
                                               &( pNetworkContext->sslContext.clientCert ),
                                               &( pNetworkContext->sslContext.privKey ) );
                }
            }
        }
    }

    if( ( returnStatus == MBEDTLS_SUCCESS ) && ( pNetworkCredentials->pAlpnProtos != NULL ) )
    {
        /* Include an application protocol list in the TLS ClientHello
         * message. */
        mbedtlsError = mbedtls_ssl_conf_alpn_protocols( &( pNetworkContext->sslContext.config ),
                                                        &( pNetworkCredentials->pAlpnProtos ) );

        if( mbedtlsError != 0 )
        {
            LogError( ( "Failed to set up mbed TLS alpn protocol, error %d.",
                        mbedtlsError ) );

            returnStatus = MBEDTLS_API_ERROR;
        }
    }

    if( returnStatus == MBEDTLS_SUCCESS )
    {
        /* Initialize the mbed TLS secured connection context. */
        mbedtlsError = mbedtls_ssl_setup( &( pNetworkContext->sslContext.context ),
                                          &( pNetworkContext->sslContext.config ) );

        if( mbedtlsError != 0 )
        {
            LogError( ( "Failed to set up mbed TLS SSL context, error %d.",
                        mbedtlsError ) );

            returnStatus = MBEDTLS_API_ERROR;
        }
        else
        {
            /* Set the underlying IO for the TLS connection. */
            mbedtls_ssl_set_bio( &( pNetworkContext->sslContext.context ),
                                 pNetworkContext->tcpSocket,
                                 mbedtls_platform_send,
                                 mbedtls_platform_recv,
                                 NULL );
        }
    }

    if( returnStatus == MBEDTLS_SUCCESS )
    {
        /* Enable SNI if requested. */
        if( pNetworkCredentials->disableSni == pdFALSE )
        {
            mbedtlsError = mbedtls_ssl_set_hostname( &( pNetworkContext->sslContext.context ),
                                                     pHostName );

            if( mbedtlsError != 0 )
            {
                LogError( ( "Failed to set server name, error %d.", mbedtlsError ) );

                returnStatus = MBEDTLS_API_ERROR;
            }
        }
    }

    if( returnStatus == MBEDTLS_SUCCESS )
    {
        /* Perform the TLS handshake. */
        do
        {
            mbedtlsError = mbedtls_ssl_handshake( &( pNetworkContext->sslContext.context ) );
        } while( ( mbedtlsError == MBEDTLS_ERR_SSL_WANT_READ ) ||
                 ( mbedtlsError == MBEDTLS_ERR_SSL_WANT_WRITE ) );

        if( mbedtlsError != 0 )
        {
            LogError( ( "Failed to perform TLS handshake, error %d.", mbedtlsError ) );

            returnStatus = MBEDTLS_HANDSHAKE_FAILED;
        }
    }

    if( returnStatus != MBEDTLS_SUCCESS )
    {
        sslContextFree( &( pNetworkContext->sslContext ) );
    }
    else
    {
        LogInfo( ( "(Network connection %p) TLS handshake successful.",
                   pNetworkContext ) );
    }

    return returnStatus;
}

/*-----------------------------------------------------------*/

static MbedtlsStatus_t initMbedtls( void )
{
    MbedtlsStatus_t returnStatus = MBEDTLS_SUCCESS;
    int mbedtlsError = 0;

    /* Set the mutex functions for mbed TLS thread safety. */
    mbedtls_threading_set_alt( mbedtls_platform_mutex_init,
                               mbedtls_platform_mutex_free,
                               mbedtls_platform_mutex_lock,
                               mbedtls_platform_mutex_unlock );

    /* Initialize contexts for random number generation. */
    mbedtls_entropy_init( &entropyContext );
    mbedtls_ctr_drbg_init( &ctrDrgbContext );

    /* Add a strong entropy source. At least one is required. */
    mbedtlsError = mbedtls_entropy_add_source( &entropyContext,
                                               mbedtls_platform_entropy_poll,
                                               NULL,
                                               32,
                                               MBEDTLS_ENTROPY_SOURCE_STRONG );

    if( mbedtlsError != 0 )
    {
        LogError( ( "Failed to add entropy source, error %d.", mbedtlsError ) );
        returnStatus = MBEDTLS_API_ERROR;
    }

    if( returnStatus == MBEDTLS_SUCCESS )
    {
        /* Seed the random number generator. */
        mbedtlsError = mbedtls_ctr_drbg_seed( &ctrDrgbContext,
                                              mbedtls_entropy_func,
                                              &entropyContext,
                                              NULL,
                                              0 );

        if( mbedtlsError != 0 )
        {
            LogError( ( "Failed to seed PRNG, error %d.", mbedtlsError ) );
            returnStatus = MBEDTLS_API_ERROR;
        }
    }

    if( returnStatus == MBEDTLS_SUCCESS )
    {
        LogDebug( ( "Successfully Initialized mbedTLS." ) );
    }

    return returnStatus;
}

/*-----------------------------------------------------------*/

MbedtlsStatus_t Mbedtls_FreeRTOS_Connect( NetworkContext_t * pNetworkContext,
                                          const char * pHostName,
                                          uint16_t port,
                                          const NetworkCredentials_t * pNetworkCredentials,
                                          uint32_t receiveTimeoutMs,
                                          uint32_t sendTimeoutMs )
{
    MbedtlsStatus_t returnStatus = MBEDTLS_SUCCESS;
    BaseType_t socketStatus = 0;

    if( ( pNetworkContext == NULL ) ||
        ( pHostName == NULL ) ||
        ( pNetworkCredentials == NULL ) )
    {
        LogError( ( "Arguments cannot be NULL. pNetworkContext=%p, "
                    "pHostName=%p, pNetworkCredentials=%p.",
                    pNetworkContext,
                    pHostName,
                    pNetworkCredentials ) );
        returnStatus = MBEDTLS_INVALID_PARAMETER;
    }
    else if( ( pNetworkCredentials->pRootCa == NULL ) ||
             ( pNetworkCredentials->pClientCert == NULL ) ||
             ( pNetworkCredentials->pPrivateKey == NULL ) )
    {
        LogError( ( "Arguments cannot be NULL. pNetworkCredentials->pRootCa=%p, "
                    "pNetworkCredentials->pClientCert=%p, "
                    "pNetworkCredentials=%p.",
                    pNetworkCredentials->pRootCa,
                    pNetworkCredentials->pClientCert,
                    pNetworkCredentials->pPrivateKey ) );
        returnStatus = MBEDTLS_INVALID_PARAMETER;
    }

    /* Create a FreeRTOS+TCP socket. */
    if( returnStatus == MBEDTLS_SUCCESS )
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
            returnStatus = MBEDTLS_CONNECT_FAILURE;
        }
    }

    /* Initialize mbedtls. */
    if( returnStatus == MBEDTLS_SUCCESS )
    {
        returnStatus = initMbedtls();
    }

    /* Perform TLS handshake. */
    if( returnStatus == MBEDTLS_SUCCESS )
    {
        returnStatus = tlsSetup( pNetworkContext, pHostName, pNetworkCredentials );
    }

    /* Clean up on failure. */
    if( returnStatus != MBEDTLS_SUCCESS )
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

void Mbedtls_FreeRTOS_Disconnect( const NetworkContext_t * pNetworkContext )
{
    BaseType_t socketStatus = 0;

    socketStatus = ( BaseType_t ) mbedtls_ssl_close_notify( &( pNetworkContext->sslContext.context ) );

    /* Ignore the WANT_READ and WANT_WRITE return values. */
    if( ( socketStatus != ( BaseType_t ) MBEDTLS_ERR_SSL_WANT_READ ) &&
        ( socketStatus != ( BaseType_t ) MBEDTLS_ERR_SSL_WANT_WRITE ) )
    {
        if( socketStatus == 0 )
        {
            LogInfo( ( "(Network connection %p) TLS close-notify sent.",
                       pNetworkContext ) );
        }
        else
        {
            LogError( ( "(Network connection %p) Failed to send TLS close-notify, error %d.",
                        pNetworkContext,
                        socketStatus ) );
        }
    }

    /* Call socket shutdown function to close connection. */
    Sockets_Disconnect( pNetworkContext->tcpSocket );

    /* Free mbed TLS contexts. */
    sslContextFree( &( pNetworkContext->sslContext ) );
}

/*-----------------------------------------------------------*/

int32_t Mbedtls_FreeRTOS_recv( NetworkContext_t * pNetworkContext,
                               void * pBuffer,
                               size_t bytesToRecv )
{
    int32_t socketStatus = 0;

    socketStatus = ( int32_t ) mbedtls_ssl_read( &( pNetworkContext->sslContext.context ),
                                                 pBuffer,
                                                 bytesToRecv );

    if( ( socketStatus == MBEDTLS_ERR_SSL_TIMEOUT ) ||
        ( socketStatus == MBEDTLS_ERR_SSL_WANT_READ ) ||
        ( socketStatus == MBEDTLS_ERR_SSL_WANT_WRITE ) )
    {
        /* Mark these set of errors as a timeout for the libraries to retry
         * the read. */
        socketStatus = 0;
    }
    else if( socketStatus < 0 )
    {
        LogError( ( "Error %d while receiving data.", socketStatus ) );
    }
    else
    {
        /* Empty else marker. */
    }

    return socketStatus;
}

/*-----------------------------------------------------------*/

int32_t Mbedtls_FreeRTOS_send( NetworkContext_t * pNetworkContext,
                               const void * pBuffer,
                               size_t bytesToSend )
{
    int32_t socketStatus = 0;

    socketStatus = ( int32_t ) mbedtls_ssl_write( &( pNetworkContext->sslContext.context ),
                                                  pBuffer,
                                                  bytesToSend );

    if( ( socketStatus == MBEDTLS_ERR_SSL_TIMEOUT ) ||
        ( socketStatus == MBEDTLS_ERR_SSL_WANT_READ ) ||
        ( socketStatus == MBEDTLS_ERR_SSL_WANT_WRITE ) )
    {
        /* Mark these set of errors as a timeout for the libraries to retry
         * the send. */
        socketStatus = 0;
    }
    else if( socketStatus < 0 )
    {
        LogError( ( "Error %d while sending data.", socketStatus ) );
    }
    else
    {
        /* Empty else marker. */
    }

    return socketStatus;
}
/*-----------------------------------------------------------*/
