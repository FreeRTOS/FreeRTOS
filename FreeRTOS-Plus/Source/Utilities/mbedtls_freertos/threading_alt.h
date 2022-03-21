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
 * @file threading_alt.h
 * @brief mbed TLS threading functions implemented for FreeRTOS.
 */


#ifndef MBEDTLS_THREADING_ALT_H_
#define MBEDTLS_THREADING_ALT_H_

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "semphr.h"

/**
 * @brief mbed TLS mutex type.
 *
 * mbed TLS requires platform specific definition for the mutext type. Defining the type for
 * FreeRTOS with FreeRTOS semaphore
 * handle and semaphore storage as members.
 */
typedef struct mbedtls_threading_mutex
{
    SemaphoreHandle_t mutexHandle;
    StaticSemaphore_t mutexStorage;
} mbedtls_threading_mutex_t;

/* mbed TLS mutex functions. */
void mbedtls_platform_mutex_init( mbedtls_threading_mutex_t * pMutex );
void mbedtls_platform_mutex_free( mbedtls_threading_mutex_t * pMutex );
int mbedtls_platform_mutex_lock( mbedtls_threading_mutex_t * pMutex );
int mbedtls_platform_mutex_unlock( mbedtls_threading_mutex_t * pMutex );

#endif /* ifndef MBEDTLS_THREADING_ALT_H_ */
