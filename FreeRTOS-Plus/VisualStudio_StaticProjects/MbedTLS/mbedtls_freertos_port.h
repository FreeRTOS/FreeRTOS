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
 * @file mbedtls_freertos_port.h
 * @brief mbed TLS threading functions implemented for FreeRTOS.
 */

#ifndef MBEDTLS_FREERTOS_PORT_H_
#define MBEDTLS_FREERTOS_PORT_H_

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "semphr.h"

/**
 * @brief mbed TLS mutex type definition for MBEDTLS_THREADING_C implementation.
 */
typedef struct mbedtls_threading_mutex
{
    SemaphoreHandle_t mutexHandle;

    #if ( configSUPPORT_STATIC_ALLOCATION == 1 )
        StaticSemaphore_t mutexStorage;
    #endif /*  configSUPPORT_STATIC_ALLOCATION == 1 */
} mbedtls_threading_mutex_t;

#if defined( MBEDTLS_THREADING_ALT )
    int mbedtls_platform_threading_init( void );
#endif

int mbedtls_platform_send( void * ctx,
                           const unsigned char * buf,
                           size_t len );
int mbedtls_platform_recv( void * ctx,
                           unsigned char * buf,
                           size_t len );

void * mbedtls_platform_calloc( size_t nmemb,
                                size_t size );
void mbedtls_platform_free( void * ptr );

#endif /* ifndef MBEDTLS_FREERTOS_PORT_H_ */
