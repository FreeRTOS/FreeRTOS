/*
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
 */

/**
 * @file mbedtls_platform.c
 * @brief Implements mbed TLS platform functions for FreeRTOS.
 */

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "FreeRTOS_Sockets.h"

/* mbed TLS includes. */
#include "mbedtls_config.h"
#include "threading_alt.h"
#include "mbedtls/entropy.h"

/*-----------------------------------------------------------*/

void * mbedtls_platform_calloc( size_t nmemb,
                                size_t size )
{
    size_t totalSize = nmemb * size;
    void * pBuffer = NULL;

    /* Check that neither nmemb nor size were 0. */
    if( totalSize > 0 )
    {
        /* Overflow check. */
        if( totalSize / size == nmemb )
        {
            pBuffer = pvPortMalloc( totalSize );

            if( pBuffer != NULL )
            {
                ( void ) memset( pBuffer, 0x00, totalSize );
            }
        }
    }

    return pBuffer;
}

/*-----------------------------------------------------------*/

void mbedtls_platform_free( void * ptr )
{
    vPortFree( ptr );
}

/*-----------------------------------------------------------*/

int mbedtls_platform_send( void * ctx,
                           const unsigned char * buf,
                           size_t len )
{
    Socket_t socket = ctx;

    return ( int ) FreeRTOS_send( socket, buf, len, 0 );
}

/*-----------------------------------------------------------*/

int mbedtls_platform_recv( void * ctx,
                           unsigned char * buf,
                           size_t len )
{
    Socket_t socket = ctx;

    return ( int ) FreeRTOS_recv( socket, buf, len, 0 );
}

/*-----------------------------------------------------------*/

void mbedtls_platform_mutex_init( mbedtls_threading_mutex_t * pMutex )
{
    /* Create a statically-allocated FreeRTOS mutex. This should never fail as
     * storage is provided. */
    pMutex->mutexHandle = xSemaphoreCreateMutexStatic( &( pMutex->mutexStorage ) );
    configASSERT( pMutex->mutexHandle != NULL );
}

/*-----------------------------------------------------------*/

void mbedtls_platform_mutex_free( mbedtls_threading_mutex_t * pMutex )
{
    /* Nothing needs to be done to free a statically-allocated FreeRTOS mutex. */
    ( void ) pMutex;
}

/*-----------------------------------------------------------*/

int mbedtls_platform_mutex_lock( mbedtls_threading_mutex_t * pMutex )
{
    BaseType_t mutexStatus = 0;

    /* mutexStatus is not used if asserts are disabled. */
    ( void ) mutexStatus;

    /* This function should never fail if the mutex is initialized. */
    mutexStatus = xSemaphoreTake( pMutex->mutexHandle, portMAX_DELAY );
    configASSERT( mutexStatus == pdTRUE );

    return 0;
}

/*-----------------------------------------------------------*/

int mbedtls_platform_mutex_unlock( mbedtls_threading_mutex_t * pMutex )
{
    BaseType_t mutexStatus = 0;

    /* mutexStatus is not used if asserts are disabled. */
    ( void ) mutexStatus;

    /* This function should never fail if the mutex is initialized. */
    mutexStatus = xSemaphoreGive( pMutex->mutexHandle );
    configASSERT( mutexStatus == pdTRUE );

    return 0;
}

/*-----------------------------------------------------------*/

int mbedtls_platform_entropy_poll( void * data,
                                   unsigned char * output,
                                   size_t len,
                                   size_t * olen )
{
    int status = 0;
    NTSTATUS rngStatus = 0;

    /* Context is not used by this function. */
    ( void ) data;

    /* TLS requires a secure random number generator; use the RNG provided
     * by Windows. This function MUST be re-implemented for other platforms. */
    rngStatus = BCryptGenRandom( NULL, output, len, BCRYPT_USE_SYSTEM_PREFERRED_RNG );

    if( rngStatus == 0 )
    {
        /* All random bytes generated. */
        *olen = len;
    }
    else
    {
        /* RNG failure. */
        *olen = 0;
        status = MBEDTLS_ERR_ENTROPY_SOURCE_FAILED;
    }

    return status;
}

/*-----------------------------------------------------------*/
