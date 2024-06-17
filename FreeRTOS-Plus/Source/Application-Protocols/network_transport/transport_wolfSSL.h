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
 * @file using_wolfSSL.h
 * @brief TLS transport interface header.
 */

#ifndef USING_WOLFSSL_H
#define USING_WOLFSSL_H

/**************************************************/
/******* DO NOT CHANGE the following order ********/
/**************************************************/

/* Logging related header files are required to be included in the following order:
 * 1. Include the header file "logging_levels.h".
 * 2. Define LIBRARY_LOG_NAME and  LIBRARY_LOG_LEVEL.
 * 3. Include the header file "logging_stack.h".
 */

/* Include header that defines log levels. */
#include "logging_levels.h"

/* Logging configuration for the Sockets. */
#ifndef LIBRARY_LOG_NAME
    #define LIBRARY_LOG_NAME     "TlsTransport"
#endif
#ifndef LIBRARY_LOG_LEVEL
    #define LIBRARY_LOG_LEVEL    LOG_INFO
#endif

#include "logging_stack.h"

/************ End of logging configuration ****************/

/* FreeRTOS+TCP include. */
#include "FreeRTOS_Sockets.h"

/* Transport interface include. */
#include "transport_interface.h"

/* wolfSSL interface include. */
#include "wolfssl/ssl.h"

/**
 * @brief Secured connection context.
 */
typedef struct SSLContext
{
    WOLFSSL_CTX * ctx; /**< @brief wolfSSL context */
    WOLFSSL * ssl;     /**< @brief wolfSSL ssl session context */
} SSLContext_t;

/**
 * @brief Definition of the network context for the transport interface
 * implementation that uses mbedTLS and FreeRTOS+TLS sockets.
 */
struct NetworkContext
{
    Socket_t tcpSocket;
    SSLContext_t sslContext;
};

/**
 * @brief Contains the credentials necessary for tls connection setup.
 */
typedef struct NetworkCredentials
{
    /**
     * @brief Set this to a non-NULL value to use ALPN.
     *
     * This string must be NULL-terminated.
     *
     * See [this link]
     * (https://aws.amazon.com/blogs/iot/mqtt-with-tls-client-authentication-on-port-443-why-it-is-useful-and-how-it-works/)
     * for more information.
     */
    const char * pAlpnProtos;

    /**
     * @brief Disable server name indication (SNI) for a TLS session.
     */
    BaseType_t disableSni;

    const unsigned char * pRootCa;     /**< @brief String representing a trusted server root certificate. */
    size_t rootCaSize;                 /**< @brief Size associated with #IotNetworkCredentials.pRootCa. */
    const unsigned char * pClientCert; /**< @brief String representing the client certificate. */
    size_t clientCertSize;             /**< @brief Size associated with #IotNetworkCredentials.pClientCert. */
    const unsigned char * pPrivateKey; /**< @brief String representing the client certificate's private key. */
    size_t privateKeySize;             /**< @brief Size associated with #IotNetworkCredentials.pPrivateKey. */
    const unsigned char * pUserName;   /**< @brief String representing the username for MQTT. */
    size_t userNameSize;               /**< @brief Size associated with #IotNetworkCredentials.pUserName. */
    const unsigned char * pPassword;   /**< @brief String representing the password for MQTT. */
    size_t passwordSize;               /**< @brief Size associated with #IotNetworkCredentials.pPassword. */
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
 * This is the TLS version of the transport interface's
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

#endif /* ifndef USING_WOLFSSL_H */
