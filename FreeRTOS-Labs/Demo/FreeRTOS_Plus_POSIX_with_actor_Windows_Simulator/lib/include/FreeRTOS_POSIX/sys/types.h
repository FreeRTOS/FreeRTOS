/*
 * Amazon FreeRTOS POSIX V1.1.0
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
 * @file sys/types.h
 * @brief Data types.
 *
 * http://pubs.opengroup.org/onlinepubs/9699919799/basedefs/sys_types.h.html
 */

#ifndef _FREERTOS_POSIX_TYPES_H_
#define _FREERTOS_POSIX_TYPES_H_

/* C standard library includes. */
#include <stdint.h>

/* FreeRTOS types include */
#include "FreeRTOS_POSIX_types.h"

/**
 * @brief Used for system times in clock ticks or CLOCKS_PER_SEC.
 *
 * Enabled/disabled by posixconfigENABLE_CLOCK_T.
 */
#if !defined( posixconfigENABLE_CLOCK_T ) || ( posixconfigENABLE_CLOCK_T == 1 )
    typedef uint32_t                 clock_t;
#endif

/**
 * @brief Used for clock ID type in the clock and timer functions.
 *
 * Enabled/disabled by posixconfigENABLE_CLOCKID_T.
 */
#if !defined( posixconfigENABLE_CLOCKID_T ) || ( posixconfigENABLE_CLOCKID_T == 1 )
    typedef int                      clockid_t;
#endif

/**
 * @brief Used for some file attributes.
 *
 * Enabled/disabled by posixconfigENABLE_MODE_T.
 */
#if !defined( posixconfigENABLE_MODE_T ) || ( posixconfigENABLE_MODE_T == 1 )
    typedef int                      mode_t;
#endif

/**
 * @brief Used for process IDs and process group IDs.
 *
 * Enabled/disabled by posixconfigENABLE_PID_T.
 */
#if !defined( posixconfigENABLE_PID_T ) || ( posixconfigENABLE_PID_T == 1 )
    typedef int                      pid_t;
#endif

/**
 * @brief Used to identify a thread attribute object.
 *
 * Enabled/disabled by posixconfigENABLE_PTHREAD_ATTR_T.
 */
#if !defined( posixconfigENABLE_PTHREAD_ATTR_T ) || ( posixconfigENABLE_PTHREAD_ATTR_T == 1 )
    typedef PthreadAttrType_t        pthread_attr_t;
#endif

/**
 * @brief Used to identify a barrier.
 *
 * Enabled/disabled by posixconfigENABLE_PTHREAD_BARRIER_T.
 */
#if !defined( posixconfigENABLE_PTHREAD_BARRIER_T ) || ( posixconfigENABLE_PTHREAD_BARRIER_T == 1 )
    typedef PthreadBarrierType_t     pthread_barrier_t;
#endif

/**
 * @brief Used to define a barrier attributes object.
 */
typedef void                         * pthread_barrierattr_t;

/**
 * @brief Used for condition variables.
 *
 * Enabled/disabled by posixconfigENABLE_PTHREAD_COND_T.
 */
#if !defined( posixconfigENABLE_PTHREAD_COND_T ) || ( posixconfigENABLE_PTHREAD_COND_T == 1 )
    typedef  PthreadCondType_t       pthread_cond_t;
#endif

/**
 * @brief Used to identify a condition attribute object.
 *
 * Enabled/disabled by posixconfigENABLE_PTHREAD_CONDATTR_T.
 */
#if !defined( posixconfigENABLE_PTHREAD_CONDATTR_T ) || ( posixconfigENABLE_PTHREAD_CONDATTR_T == 1 )
    typedef void                     * pthread_condattr_t;
#endif

/**
 * @brief Used for mutexes.
 *
 * Enabled/disabled by posixconfigENABLE_PTHREAD_MUTEX_T.
 */
#if !defined( posixconfigENABLE_PTHREAD_MUTEX_T ) || ( posixconfigENABLE_PTHREAD_MUTEX_T == 1 )
    typedef PthreadMutexType_t       pthread_mutex_t;
#endif

/**
 * @brief Used to identify a mutex attribute object.
 *
 * Enabled/disabled by posixconfigENABLE_PTHREAD_MUTEXATTR_T.
 */
#if !defined( posixconfigENABLE_PTHREAD_MUTEXATTR_T ) || ( posixconfigENABLE_PTHREAD_MUTEXATTR_T == 1 )
    typedef PthreadMutexAttrType_t   pthread_mutexattr_t;
#endif

/**
 * @brief Used to identify a thread.
 *
 * Enabled/disabled by posixconfigENABLE_PTHREAD_T.
 */
#if !defined( posixconfigENABLE_PTHREAD_T ) || ( posixconfigENABLE_PTHREAD_T == 1 )
    typedef void                     * pthread_t;
#endif

/**
 * @brief Used for a count of bytes or an error indication.
 *
 * Enabled/disabled by posixconfigENABLE_SSIZE_T.
 */
#if !defined( posixconfigENABLE_SSIZE_T ) || ( posixconfigENABLE_SSIZE_T == 1 )
    typedef int                      ssize_t;
#endif

/**
 * @brief Used for time in seconds.
 *
 * Enabled/disabled by posixconfigENABLE_TIME_T.
 */
#if !defined( posixconfigENABLE_TIME_T ) || ( posixconfigENABLE_TIME_T == 1 )
    typedef int64_t                  time_t;
#endif

/**
 * @brief Used for timer ID returned by timer_create().
 *
 * Enabled/disabled by posixconfigENABLE_TIMER_T.
 */
#if !defined( posixconfigENABLE_TIMER_T ) || ( posixconfigENABLE_TIMER_T == 1 )
    typedef void                     * timer_t;
#endif

/**
 * @brief Used for time in microseconds.
 *
 * Enabled/disabled by posixconfigENABLE_USECONDS_T.
 */
#if !defined( posixconfigENABLE_USECONDS_T ) || ( posixconfigENABLE_USECONDS_T == 1 )
    typedef unsigned long            useconds_t;
#endif

/**
 * @brief Used for file sizes.
 *
 * Enabled/disabled by posixconfigENABLE_OFF_T.
 */
#if !defined( posixconfigENABLE_OFF_T ) || ( posixconfigENABLE_OFF_T == 1 )
    typedef long int                 off_t;
#endif

#endif /* ifndef _FREERTOS_POSIX_TYPES_H_ */
