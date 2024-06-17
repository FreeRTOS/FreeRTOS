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
 * @file transport_mbedtls_pkcs11.h
 * @brief TLS transport interface header.
 * @note This file is derived from the tls_freertos.h header file found in the mqtt
 * section of IoT Libraries source code. The file has been modified to support using
 * PKCS #11 when using TLS.
 */

#ifndef TRANSPORT_MBEDTLS_PKCS11
#define TRANSPORT_MBEDTLS_PKCS11

#define MBEDTLS_ALLOW_PRIVATE_ACCESS

#if !defined( MBEDTLS_CONFIG_FILE )
    #include "mbedtls/mbedtls_config.h"
#else
    #include MBEDTLS_CONFIG_FILE
#endif

#include "mbedtls/private_access.h"

/* TCP Sockets Wrapper include.*/
#include "tcp_sockets_wrapper.h"

/* Transport interface include. */
#include "transport_interface.h"

/* mbed TLS includes. */
#include "mbedtls/build_info.h"
#include "mbedtls/ctr_drbg.h"
#include "mbedtls/entropy.h"
#include "mbedtls/ssl.h"
#include "mbedtls/threading.h"
#include "mbedtls/x509.h"
#include "mbedtls/pk.h"
#include "mbedtls/error.h"

#include "pk_wrap.h"

/* PKCS #11 includes. */
#include "core_pkcs11.h"

/**
 * @brief Secured connection context.
 */
typedef struct SSLContext
{
    mbedtls_ssl_config config;            /**< @brief SSL connection configuration. */
    mbedtls_ssl_context context;          /**< @brief SSL connection context */
    mbedtls_x509_crt_profile certProfile; /**< @brief Certificate security profile for this connection. */
    mbedtls_x509_crt rootCa;              /**< @brief Root CA certificate context. */
    mbedtls_x509_crt clientCert;          /**< @brief Client certificate context. */
    mbedtls_pk_context privKey;           /**< @brief Client private key context. */
    mbedtls_pk_info_t privKeyInfo;        /**< @brief Client private key info. */

    /* PKCS#11. */
    CK_FUNCTION_LIST_PTR pxP11FunctionList;
    CK_SESSION_HANDLE xP11Session;
    CK_OBJECT_HANDLE xP11PrivateKey;
} SSLContext_t;

/**
 * @brief Definition of the network context for the transport interface
 * implementation that uses mbedTLS and FreeRTOS+TLS sockets.
 */
typedef struct TlsTransportParams
{
    Socket_t tcpSocket;
    SSLContext_t sslContext;
} TlsTransportParams_t;

/**
 * @brief Contains the credentials necessary for tls connection setup.
 */
typedef struct NetworkCredentials
{
    /**
     * @brief To use ALPN, set this to a NULL-terminated list of supported
     * protocols in decreasing order of preference.
     *
     * See [this link]
     * (https://aws.amazon.com/blogs/iot/mqtt-with-tls-client-authentication-on-port-443-why-it-is-useful-and-how-it-works/)
     * for more information.
     */
    const char ** pAlpnProtos;

    /**
     * @brief Disable server name indication (SNI) for a TLS session.
     */
    BaseType_t disableSni;

    const unsigned char * pRootCa;   /**< @brief String representing a trusted server root certificate. */
    size_t rootCaSize;               /**< @brief Size associated with #NetworkCredentials.pRootCa. */
    const unsigned char * pUserName; /**< @brief username for MQTT. */
    size_t userNameSize;             /**< @brief Size associated with #NetworkCredentials.pUserName. */
    const unsigned char * pPassword; /**< @brief String representing the password for MQTT. */
    size_t passwordSize;             /**< @brief Size associated with #NetworkCredentials.pPassword. */
    const char * pClientCertLabel;   /**< @brief PKCS #11 label string of the client certificate. */
    const char * pPrivateKeyLabel;   /**< @brief PKCS #11 label for the private key. */
} NetworkCredentials_t;

/**
 * @brief TLS Connect / Disconnect return status.
 */
typedef enum TlsTransportStatus
{
    TLS_TRANSPORT_SUCCESS = 0,         /**< Function successfully completed. */
    TLS_TRANSPORT_INVALID_PARAMETER,   /**< At least one parameter was invalid. */
    TLS_TRANSPORT_INSUFFICIENT_MEMORY, /**< Insufficient memory required to establish connection. */
    TLS_TRANSPORT_INVALID_CREDENTIALS, /**< Provided credentials were invalid. */
    TLS_TRANSPORT_HANDSHAKE_FAILED,    /**< Performing TLS handshake with server failed. */
    TLS_TRANSPORT_INTERNAL_ERROR,      /**< A call to a system API resulted in an internal error. */
    TLS_TRANSPORT_CONNECT_FAILURE      /**< Initial connection to the server failed. */
} TlsTransportStatus_t;

/**
 * @brief Create a TLS connection with FreeRTOS sockets.
 *
 * @param[out] pNetworkContext Pointer to a network context to contain the
 * initialized socket handle.
 * @param[in] pHostName The hostname of the remote endpoint.
 * @param[in] port The destination port.
 * @param[in] pNetworkCredentials Credentials for the TLS connection.
 * @param[in] receiveTimeoutMs Receive socket timeout.
 * @param[in] sendTimeoutMs Send socket timeout.
 *
 * @return #TLS_TRANSPORT_SUCCESS, #TLS_TRANSPORT_INSUFFICIENT_MEMORY, #TLS_TRANSPORT_INVALID_CREDENTIALS,
 * #TLS_TRANSPORT_HANDSHAKE_FAILED, #TLS_TRANSPORT_INTERNAL_ERROR, or #TLS_TRANSPORT_CONNECT_FAILURE.
 */
TlsTransportStatus_t TLS_FreeRTOS_Connect( NetworkContext_t * pNetworkContext,
                                           const char * pHostName,
                                           uint16_t port,
                                           const NetworkCredentials_t * pNetworkCredentials,
                                           uint32_t receiveTimeoutMs,
                                           uint32_t sendTimeoutMs );

/**
 * @brief Gracefully disconnect an established TLS connection.
 *
 * @param[in] pNetworkContext Network context.
 */
void TLS_FreeRTOS_Disconnect( NetworkContext_t * pNetworkContext );

/**
 * @brief Receives data from an established TLS connection.
 *
 * This is the TLS version of the transport interface's
 * #TransportRecv_t function.
 *
 * @param[in] pNetworkContext The Network context.
 * @param[out] pBuffer Buffer to receive bytes into.
 * @param[in] bytesToRecv Number of bytes to receive from the network.
 *
 * @return Number of bytes (> 0) received if successful;
 * 0 if the socket times out without reading any bytes;
 * negative value on error.
 */
int32_t TLS_FreeRTOS_recv( NetworkContext_t * pNetworkContext,
                           void * pBuffer,
                           size_t bytesToRecv );

/**
 * @brief Sends data over an established TLS connection.
 *
 * @note This is the TLS version of the transport interface's
 * #TransportSend_t function.
 *
 * @param[in] pNetworkContext The network context.
 * @param[in] pBuffer Buffer containing the bytes to send.
 * @param[in] bytesToSend Number of bytes to send from the buffer.
 *
 * @return Number of bytes (> 0) sent on success;
 * 0 if the socket times out without sending any bytes;
 * else a negative value to represent error.
 */
int32_t TLS_FreeRTOS_send( NetworkContext_t * pNetworkContext,
                           const void * pBuffer,
                           size_t bytesToSend );


#ifdef MBEDTLS_DEBUG_C

/**
 * @brief Write an MBedTLS Debug message to the LogDebug() function
 *
 * @param[in] sslContext Pointer of the SSL Context that is being used
 * @param[in] level The severity level of the debug message from MBedTLS
 * @param[in] file Name of the file that the debug message is from
 * @param[in] line The line number that the debug message is from
 * @param[in] str The full string debug message from MBedTLS
 *
 * @return void
 */
    void mbedtls_string_printf( void * sslContext,
                                int level,
                                const char * file,
                                int line,
                                const char * str );
#endif /* MBEDTLS_DEBUG_C */

#endif /* ifndef TRANSPORT_MBEDTLS_PKCS11 */
