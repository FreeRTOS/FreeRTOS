/*
 * IoT Platform V1.1.0
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
 * @file iot_clock.h
 * @brief Time-related functions used by libraries in this SDK.
 */

#ifndef IOT_CLOCK_H_
#define IOT_CLOCK_H_

/* The config header is always included first. */
#include "iot_config.h"

/* Standard includes. */
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

/* Platform layer types include. */
#include "types/iot_platform_types.h"

/**
 * @functionspage{platform_clock,platform clock component,Clock}
 * - @functionname{platform_clock_function_gettimestring}
 * - @functionname{platform_clock_function_gettimems}
 * - @functionname{platform_clock_function_sleepms}
 * - @functionname{platform_clock_function_timercreate}
 * - @functionname{platform_clock_function_timerdestroy}
 * - @functionname{platform_clock_function_timerarm}
 */

/**
 * @functionpage{IotClock_GetTimestring,platform_clock,gettimestring}
 * @functionpage{IotClock_GetTimeMs,platform_clock,gettimems}
 * @functionpage{IotClock_SleepMs,platform_clock,sleepms}
 * @functionpage{IotClock_TimerCreate,platform_clock,timercreate}
 * @functionpage{IotClock_TimerDestroy,platform_clock,timerdestroy}
 * @functionpage{IotClock_TimerArm,platform_clock,timerarm}
 */

/**
 * @brief Generates a human-readable timestring, such as "01 Jan 2018 12:00".
 *
 * This function uses the system clock to generate a human-readable timestring.
 * This timestring is printed by the [logging functions](@ref logging_functions).
 *
 * @param[out] pBuffer A buffer to store the timestring in.
 * @param[in] bufferSize The size of `pBuffer`.
 * @param[out] pTimestringLength The actual length of the timestring stored in
 * `pBuffer`.
 *
 * @return `true` if a timestring was successfully generated; `false` otherwise.
 *
 * @warning The implementation of this function must not call any [logging functions]
 * (@ref logging_functions).
 *
 * <b>Example</b>
 * @code{c}
 * char timestring[ 32 ];
 * size_t timestringLength = 0;
 *
 * if( IotClock_GetTimestring( timestring, 32, &timestringLength ) == true )
 * {
 *     printf( "Timestring: %.*s", timestringLength, timestring );
 * }
 * @endcode
 */
/* @[declare_platform_clock_gettimestring] */
bool IotClock_GetTimestring( char * pBuffer,
                             size_t bufferSize,
                             size_t * pTimestringLength );
/* @[declare_platform_clock_gettimestring] */

/**
 * @brief Returns a nonzero, monotonically-increasing system time in milliseconds.
 *
 * This function reads a millisecond-resolution system clock. The clock should
 * always be monotonically-increasing; therefore, real-time clocks that may be
 * set by another process are not suitable for this function's implementation.
 *
 * @return The value of the system clock. This function is not expected to fail.
 *
 * <b>Example</b>
 * @code{c}
 * // Get current time.
 * uint64_t currentTime = IotClock_GetTimeMs();
 * @endcode
 */
/* @[declare_platform_clock_gettimems] */
uint64_t IotClock_GetTimeMs( void );
/* @[declare_platform_clock_gettimems] */

/**
 * @brief Delay for the given number of milliseconds.
 *
 * This function suspends its calling thread for at least `sleepTimeMs` milliseconds.
 *
 * @param[in] sleepTimeMs Sleep time (in milliseconds).
 */
/* @[declare_platform_clock_sleepms] */
void IotClock_SleepMs( uint32_t sleepTimeMs );
/* @[declare_platform_clock_sleepms] */

/**
 * @brief Create a new timer.
 *
 * This function creates a new, unarmed timer. It must be called on an uninitialized
 * #IotTimer_t. This function must not be called on an already-initialized #IotTimer_t.
 *
 * @param[out] pNewTimer Set to a new timer handle on success.
 * @param[in] expirationRoutine The function to run when this timer expires. This
 * function should be called in its own <i>detached</i> thread.
 * @param[in] pArgument The argument to pass to `expirationRoutine`.
 *
 * @return `true` if the timer is successfully created; `false` otherwise.
 *
 * @see @ref platform_clock_function_timerdestroy, @ref platform_clock_function_timerarm
 */
/* @[declare_platform_clock_timercreate] */
bool IotClock_TimerCreate( IotTimer_t * pNewTimer,
                           IotThreadRoutine_t expirationRoutine,
                           void * pArgument );
/* @[declare_platform_clock_timercreate] */

/**
 * @brief Free resources used by a timer.
 *
 * This function frees resources used by a timer. It must be called on an initialized
 * #IotTimer_t. No other timer functions should be called on `pTimer` after calling
 * this function (unless the timer is re-created).
 *
 * This function will stop the `pTimer` if it is armed.
 *
 * @param[in] pTimer The timer to destroy.
 *
 * @see @ref platform_clock_function_timercreate, @ref platform_clock_function_timerarm
 */
/* @[declare_platform_clock_timerdestroy] */
void IotClock_TimerDestroy( IotTimer_t * pTimer );
/* @[declare_platform_clock_timerdestroy] */

/**
 * @brief Arm a timer to expire at the given relative timeout.
 *
 * This function arms a timer to run its expiration routine at the given time.
 *
 * If `periodMs` is nonzero, the timer should expire periodically at intervals
 * such as:
 * - `relativeTimeoutMs`
 * - `relativeTimeoutMs + periodMs`
 * - `relativeTimeoutMs + 2 * periodMs`
 * - Etc. (subject to some jitter).
 *
 * Setting `periodMs` to `0` arms a one-shot, non-periodic timer.
 *
 * @param[in] pTimer The timer to arm.
 * @param[in] relativeTimeoutMs When the timer should expire, relative to the time
 * this function is called.
 * @param[in] periodMs How often the timer should expire again after `relativeTimerMs`.
 *
 * @return `true` if the timer was successfully armed; `false` otherwise.
 *
 * @see @ref platform_clock_function_timercreate, @ref platform_clock_function_timerdestroy
 *
 * <b>Example</b>
 * @code{c}
 *
 * void timerExpirationRoutine( void * pArgument );
 *
 * void timerExample( void )
 * {
 *     IotTimer_t timer;
 *
 *     if( IotClock_TimerCreate( &timer, timerExpirationRoutine, NULL ) == true )
 *     {
 *         // Set the timer to periodically expire every 10 seconds.
 *         if( IotClock_TimerArm( &timer, 10000, 10000 ) == true )
 *         {
 *             // Wait for timer to expire.
 *         }
 *
 *         IotClock_TimerDestroy( &timer );
 *     }
 * }
 * @endcode
 */
/* @[declare_platform_clock_timerarm] */
bool IotClock_TimerArm( IotTimer_t * pTimer,
                        uint32_t relativeTimeoutMs,
                        uint32_t periodMs );
/* @[declare_platform_clock_timerarm] */

#endif /* ifndef IOT_CLOCK_H_ */
