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
 * @file mbedtls_bio_freertos_cellular.c
 * @brief Implements mbed TLS platform send/receive functions for cellular.
 */

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "FreeRTOS_Sockets.h"

/* Sockets wrapper includes. */
#include "sockets_wrapper.h"

/* mbed TLS includes. */
#include "mbedtls_config.h"
#include "threading_alt.h"
#include "mbedtls/entropy.h"
#include "mbedtls/ssl.h"

/*-----------------------------------------------------------*/

/**
 * @brief Sends data over cellular sockets.
 *
 * @param[in] ctx The network context containing the socket handle.
 * @param[in] buf Buffer containing the bytes to send.
 * @param[in] len Number of bytes to send from the buffer.
 *
 * @return Number of bytes sent on success; else a negative value.
 */
int mbedtls_cellular_send( void * ctx,
                           const unsigned char * buf,
                           size_t len )
{
    configASSERT( ctx != NULL );
    configASSERT( buf != NULL );

    return Sockets_Send( ( Socket_t ) ctx, buf, len );
}

/*-----------------------------------------------------------*/

/**
 * @brief Receives data from cellular socket.
 *
 * @param[in] ctx The network context containing the socket handle.
 * @param[out] buf Buffer to receive bytes into.
 * @param[in] len Number of bytes to receive from the network.
 *
 * @return Number of bytes received if successful; Negative value on error.
 */
int mbedtls_cellular_recv( void * ctx,
                           unsigned char * buf,
                           size_t len )
{
    int recvStatus = 0;
    int returnStatus = -1;

    configASSERT( ctx != NULL );
    configASSERT( buf != NULL );

    recvStatus = Sockets_Recv( ( Socket_t ) ctx, buf, len );

    if( recvStatus < 0 )
    {
        returnStatus = MBEDTLS_ERR_SSL_INTERNAL_ERROR;
    }
    else
    {
        returnStatus = recvStatus;
    }

    return returnStatus;
}
