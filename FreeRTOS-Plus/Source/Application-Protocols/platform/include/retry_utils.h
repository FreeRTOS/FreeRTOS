/*
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
 */

/**
 * @file retry_utils.h
 * @brief Declaration of the exponential backoff retry logic utility functions
 * and constants.
 */

#ifndef RETRY_UTILS_H_
#define RETRY_UTILS_H_

/* Standard include. */
#include <stdint.h>

/**
 * @page retryutils_page Retry Utilities
 * @brief An abstraction of utilities for retrying with exponential back off and
 * jitter.
 *
 * @section retryutils_overview Overview
 * The retry utilities are a set of APIs that aid in retrying with exponential
 * backoff and jitter. Exponential backoff with jitter is strongly recommended
 * for retrying failed actions over the network with servers. Please see
 * https://aws.amazon.com/blogs/architecture/exponential-backoff-and-jitter/ for
 * more information about the benefits with AWS.
 *
 * Exponential backoff with jitter is typically used when retrying a failed
 * connection to the server. In an environment with poor connectivity, a client
 * can get disconnected at any time. A backoff strategy helps the client to
 * conserve battery by not repeatedly attempting reconnections when they are
 * unlikely to succeed.
 *
 * Before retrying the failed communication to the server there is a quiet period.
 * In this quiet period, the task that is retrying must sleep for some random
 * amount of seconds between 0 and the lesser of a base value and a predefined
 * maximum. The base is doubled with each retry attempt until the maximum is
 * reached.<br>
 *
 * > sleep_seconds = random_between( 0, min( 2<sup>attempts_count</sup> * base_seconds, maximum_seconds ) )
 *
 * @section retryutils_implementation Implementing Retry Utils
 *
 * The functions that must be implemented are:<br>
 * - @ref RetryUtils_ParamsReset
 * - @ref RetryUtils_BackoffAndSleep
 *
 * The functions are used as shown in the diagram below. This is the exponential
 * backoff with jitter loop:
 *
 * @image html retry_utils_flow.png width=25%
 *
 * The following steps give guidance on implementing the Retry Utils. An example
 * implementation of the Retry Utils for a POSIX platform can be found in file
 * @ref retry_utils_posix.c.
 *
 * -# Implementing @ref RetryUtils_ParamsReset
 * @snippet this define_retryutils_paramsreset
 *<br>
 * This function initializes @ref RetryUtilsParams_t. It is expected to set
 * @ref RetryUtilsParams_t.attemptsDone to zero. It is also expected to set
 * @ref RetryUtilsParams_t.nextJitterMax to @ref INITIAL_RETRY_BACKOFF_SECONDS
 * plus some random amount of seconds, jitter. This jitter is a random number
 * between 0 and @ref MAX_JITTER_VALUE_SECONDS. This function must be called
 * before entering the exponential backoff with jitter loop using
 * @ref RetryUtils_BackoffAndSleep.<br><br>
 * Please follow the example below to implement your own @ref RetryUtils_ParamsReset.
 * The lines with FIXME comments should be updated.
 * @code{c}
 * void RetryUtils_ParamsReset( RetryUtilsParams_t * pRetryParams )
 * {
 *     uint32_t jitter = 0;
 *
 *     // Reset attempts done to zero so that the next retry cycle can start.
 *     pRetryParams->attemptsDone = 0;
 *
 *     // Seed pseudo random number generator with the current time. FIXME: Your
 *     // system may have another method to retrieve the current time to seed the
 *     // pseudo random number generator.
 *     srand( time( NULL ) );
 *
 *     // Calculate jitter value using picking a random number.
 *     jitter = ( rand() % MAX_JITTER_VALUE_SECONDS );
 *
 *     // Reset the backoff value to the initial time out value plus jitter.
 *     pRetryParams->nextJitterMax = INITIAL_RETRY_BACKOFF_SECONDS + jitter;
 * }
 * @endcode<br>
 *
 * -# Implementing @ref RetryUtils_BackoffAndSleep
 * @snippet this define_retryutils_backoffandsleep
 * <br>
 * When this function is invoked, the calling task is expected to sleep a random
 * number of seconds between 0 and @ref RetryUtilsParams_t.nextJitterMax. After
 * sleeping this function must double @ref RetryUtilsParams_t.nextJitterMax, but
 * not exceeding @ref MAX_RETRY_BACKOFF_SECONDS. When @ref RetryUtilsParams_t.maxRetryAttempts
 * are reached this function should return @ref RetryUtilsRetriesExhausted, unless
 * @ref RetryUtilsParams_t.maxRetryAttempts is set to zero.
 * When @ref RetryUtilsRetriesExhausted is returned the calling application can
 * stop trying with a failure, or it can call @ref RetryUtils_ParamsReset again
 * and restart the exponential back off with jitter loop.<br><br>
 * Please follow the example below to implement your own @ref RetryUtils_BackoffAndSleep.
 * The lines with FIXME comments should be updated.
 * @code{c}
 * RetryUtilsStatus_t RetryUtils_BackoffAndSleep( RetryUtilsParams_t * pRetryParams )
 * {
 *     RetryUtilsStatus_t status = RetryUtilsRetriesExhausted;
 *     // The quiet period delay in seconds.
 *     int backOffDelay = 0;
 *
 *     // If pRetryParams->maxRetryAttempts is set to 0, try forever.
 *     if( ( pRetryParams->attemptsDone < pRetryParams->maxRetryAttempts ) ||
 *         ( 0U == pRetryParams->maxRetryAttempts ) )
 *     {
 *         // Choose a random value for back-off time between 0 and the max jitter value.
 *         backOffDelay = rand() % pRetryParams->nextJitterMax;
 *
 *         //  Wait for backoff time to expire for the next retry.
 *         ( void ) myThreadSleepFunction( backOffDelay ); // FIXME: Replace with your system's thread sleep function.
 *
 *         // Increment backoff counts.
 *         pRetryParams->attemptsDone++;
 *
 *         // Double the max jitter value for the next retry attempt, only
 *         // if the new value will be less than the max backoff time value.
 *         if( pRetryParams->nextJitterMax < ( MAX_RETRY_BACKOFF_SECONDS / 2U ) )
 *         {
 *             pRetryParams->nextJitterMax += pRetryParams->nextJitterMax;
 *         }
 *         else
 *         {
 *             pRetryParams->nextJitterMax = MAX_RETRY_BACKOFF_SECONDS;
 *         }
 *
 *         status = RetryUtilsSuccess;
 *     }
 *     else
 *     {
 *         // When max retry attempts are exhausted, let application know by
 *         // returning RetryUtilsRetriesExhausted. Application may choose to
 *         // restart the retry process after calling RetryUtils_ParamsReset().
 *         status = RetryUtilsRetriesExhausted;
 *         RetryUtils_ParamsReset( pRetryParams );
 *     }
 *
 *     return status;
 * }
 * @endcode
 */

/**
 * @brief Max number of retry attempts. Set this value to 0 if the client must
 * retry forever.
 */
#define MAX_RETRY_ATTEMPTS               4U

/**
 * @brief Initial fixed backoff value in seconds between two successive
 * retries. A random jitter value is added to every backoff value.
 */
#define INITIAL_RETRY_BACKOFF_SECONDS    1U

/**
 * @brief Max backoff value in seconds.
 */
#define MAX_RETRY_BACKOFF_SECONDS        128U

/**
 * @brief Max jitter value in seconds.
 */
#define MAX_JITTER_VALUE_SECONDS         5U

/**
 * @brief Status for @ref RetryUtils_BackoffAndSleep.
 */
typedef enum RetryUtilsStatus
{
    RetryUtilsSuccess = 0,     /**< @brief The function returned successfully after sleeping. */
    RetryUtilsRetriesExhausted /**< @brief The function exhausted all retry attempts. */
} RetryUtilsStatus_t;

/**
 * @brief Represents parameters required for retry logic.
 */
typedef struct RetryUtilsParams
{
    /**
     * @brief Max number of retry attempts. Set this value to 0 if the client must
     * retry forever.
     */
    uint32_t maxRetryAttempts;

    /**
     * @brief The cumulative count of backoff delay cycles completed
     * for retries.
     */
    uint32_t attemptsDone;

    /**
     * @brief The max jitter value for backoff time in retry attempt.
     */
    uint32_t nextJitterMax;
} RetryUtilsParams_t;


/**
 * @brief Resets the retry timeout value and number of attempts.
 * This function must be called by the application before a new retry attempt.
 *
 * @param[in, out] pRetryParams Structure containing attempts done and timeout
 * value.
 */
void RetryUtils_ParamsReset( RetryUtilsParams_t * pRetryParams );

/**
 * @brief Simple platform specific exponential backoff function. The application
 * must use this function between retry failures to add exponential delay.
 * This function will block the calling task for the current timeout value.
 *
 * @param[in, out] pRetryParams Structure containing retry parameters.
 *
 * @return #RetryUtilsSuccess after a successful sleep, #RetryUtilsRetriesExhausted
 * when all attempts are exhausted.
 */
RetryUtilsStatus_t RetryUtils_BackoffAndSleep( RetryUtilsParams_t * pRetryParams );

#endif /* ifndef RETRY_UTILS_H_ */
