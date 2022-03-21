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

/**
 * @file mbedtls_bio_freertos_plus_tcp.c
 * @brief Implements mbed TLS platform send/receive functions for freertos plus tcp.
 */

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "FreeRTOS_Sockets.h"

/* mbed TLS includes. */
#include "mbedtls_config.h"
#include "threading_alt.h"
#include "mbedtls/entropy.h"
#include "mbedtls/ssl.h"

/*-----------------------------------------------------------*/

/**
 * @brief Sends data over FreeRTOS+TCP sockets.
 *
 * @param[in] ctx The network context containing the socket handle.
 * @param[in] buf Buffer containing the bytes to send.
 * @param[in] len Number of bytes to send from the buffer.
 *
 * @return Number of bytes sent on success; else a negative value.
 */
int mbedtls_platform_send( void * ctx,
                           const unsigned char * buf,
                           size_t len )
{
    BaseType_t sendStatus = 0;
    int returnStatus = -1;

    configASSERT( ctx != NULL );
    configASSERT( buf != NULL );

    sendStatus = FreeRTOS_send( ( Socket_t ) ctx, buf, len, 0 );

    switch( sendStatus )
    {
        /* Socket was closed or just got closed. */
        case -pdFREERTOS_ERRNO_ENOTCONN:
        /* Not enough memory for the socket to create either an Rx or Tx stream. */
        case -pdFREERTOS_ERRNO_ENOMEM:
        /* Socket is not valid, is not a TCP socket, or is not bound. */
        case -pdFREERTOS_ERRNO_EINVAL:
        /* Socket received a signal, causing the read operation to be aborted. */
        case -pdFREERTOS_ERRNO_EINTR:
            returnStatus = MBEDTLS_ERR_SSL_INTERNAL_ERROR;
            break;

        /* A timeout occurred before any data could be sent. */
        case -pdFREERTOS_ERRNO_ENOSPC:
            returnStatus = MBEDTLS_ERR_SSL_TIMEOUT;
            break;

        default:
            returnStatus = ( int ) sendStatus;
            break;
    }

    return returnStatus;
}

/*-----------------------------------------------------------*/

/**
 * @brief Receives data from FreeRTOS+TCP socket.
 *
 * @param[in] ctx The network context containing the socket handle.
 * @param[out] buf Buffer to receive bytes into.
 * @param[in] len Number of bytes to receive from the network.
 *
 * @return Number of bytes received if successful; Negative value on error.
 */
int mbedtls_platform_recv( void * ctx,
                           unsigned char * buf,
                           size_t len )
{
    BaseType_t recvStatus = 0;
    int returnStatus = -1;

    configASSERT( ctx != NULL );
    configASSERT( buf != NULL );

    recvStatus = FreeRTOS_recv( ( Socket_t ) ctx, buf, len, 0 );

    switch( recvStatus )
    {
        /* No data could be sent because the socket was or just got closed. */
        case -pdFREERTOS_ERRNO_ENOTCONN:
        /* No data could be sent because there was insufficient memory. */
        case -pdFREERTOS_ERRNO_ENOMEM:
        /* No data could be sent because xSocket was not a valid TCP socket. */
        case -pdFREERTOS_ERRNO_EINVAL:
            returnStatus = MBEDTLS_ERR_SSL_INTERNAL_ERROR;
            break;

        /* A timeout occurred before any data could be received. */
        case 0:
            returnStatus = MBEDTLS_ERR_SSL_WANT_READ;
            break;

        default:
            returnStatus = ( int ) recvStatus;
            break;
    }

    return returnStatus;
}
