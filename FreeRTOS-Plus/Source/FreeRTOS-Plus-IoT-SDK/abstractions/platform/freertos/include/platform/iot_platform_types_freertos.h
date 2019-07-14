/*
 * Amazon FreeRTOS Platform V1.0.0
 * Copyright (C) 2019 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 * http://aws.amazon.com/freertos
 * http://www.FreeRTOS.org
 */

/**
 * @file iot_platform_types_posix.h
 * @brief Definitions of platform layer types on POSIX systems.
 */

#ifndef _IOT_PLATFORM_TYPES_AFR_H_
#define _IOT_PLATFORM_TYPES_AFR_H_

#include "timers.h"

typedef struct iot_mutex_internal
{
    StaticSemaphore_t xMutex;      /**< FreeRTOS mutex. */
    BaseType_t recursive;                /**< Type; used for indicating if this is reentrant or normal. */
} iot_mutex_internal_t;

/**
 * @brief The native mutex type on AFR systems.
 */
typedef iot_mutex_internal_t _IotSystemMutex_t;

typedef struct iot_sem_internal
{
    StaticSemaphore_t xSemaphore;       /**< FreeRTOS semaphore. */
} iot_sem_internal_t;

/**
 * @brief The native semaphore type on AFR systems.
 */
typedef iot_sem_internal_t _IotSystemSemaphore_t;

/**
 * @brief Holds information about an active detached thread so that we can
 *        delete the FreeRTOS task when it completes
 */
typedef struct threadInfo
{
    void * pArgument;                 /**< @brief Argument to `threadRoutine`. */
    void ( *threadRoutine )( void * );/**< @brief Thread function to run. */
} threadInfo_t;

/**
 * @brief Holds information about an active timer.
 */
typedef struct timerInfo
{
    TimerHandle_t timer;                    /**< @brief Underlying timer. */
    void ( *threadRoutine )( void * );      /**< @brief Thread function to run on timer expiration. */
    void * pArgument;                       /**< @brief First argument to threadRoutine. */
    StaticTimer_t xTimerBuffer;             /**< Memory that holds the FreeRTOS timer. */
    TickType_t xTimerPeriod;                /**< Period of this timer. */
} timerInfo_t;

/**
 * @brief Represents an #IotTimer_t on AFR systems.
 */
typedef timerInfo_t _IotSystemTimer_t;

#endif /* ifndef _IOT_PLATFORM_TYPES_POSIX_H_ */
