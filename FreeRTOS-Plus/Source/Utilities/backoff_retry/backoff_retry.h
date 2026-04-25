/*
 * FreeRTOS V202212.00
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates. All Rights Reserved.
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 *
 * https://www.FreeRTOS.org
 * https://github.com/FreeRTOS
 */

/**
 * @file backoff_retry.h
 * @brief API for a reusable retry-with-exponential-backoff utility for
 * FreeRTOS-Plus network demos.
 *
 * This utility provides configurable exponential backoff with jitter for
 * network retry operations. It is designed to be used across multiple demo
 * applications that require robust retry logic when connecting to cloud
 * services or network endpoints.
 */

#ifndef BACKOFF_RETRY_H
#define BACKOFF_RETRY_H

/* Standard includes. */
#include <stdint.h>
#include <stddef.h>

/**
 * @brief Status codes returned by the backoff retry API.
 */
typedef enum BackoffRetryStatus
{
    BackoffRetrySuccess = 0,       /**< Operation succeeded. */
    BackoffRetryRetriesExhausted,  /**< All retry attempts have been exhausted. */
    BackoffRetryParamsInvalid,     /**< Invalid parameters provided. */
    BackoffRetryOverflow           /**< Internal overflow detected. */
} BackoffRetryStatus_t;

/**
 * @brief Parameters for the backoff retry context.
 */
typedef struct BackoffRetryParams
{
    uint32_t ulMaxRetries;         /**< Maximum number of retries allowed. Set to 0 for infinite. */
    uint32_t ulBaseDelayMs;        /**< Base delay in milliseconds for the first retry. */
    uint32_t ulMaxDelayMs;         /**< Maximum cap on computed delay in milliseconds. */
    uint32_t ulJitterMaxMs;        /**< Maximum jitter in milliseconds to add to each delay. */
} BackoffRetryParams_t;

/**
 * @brief Context structure maintaining the state of a retry sequence.
 */
typedef struct BackoffRetryContext
{
    BackoffRetryParams_t xParams;     /**< Configured retry parameters. */
    uint32_t ulAttemptsDone;          /**< Number of attempts completed so far. */
    uint32_t ulNextDelayMs;           /**< Computed delay for the next retry. */
    uint32_t ulTotalWaitedMs;         /**< Total time waited across all retries. */
    uint32_t ulRandomSeed;            /**< Seed for pseudo-random jitter generation. */
    uint8_t ucIsExhausted;            /**< Flag indicating whether retries are exhausted. */
} BackoffRetryContext_t;

/**
 * @brief Initialize a backoff retry context with the specified parameters.
 *
 * @param[out] pxContext Pointer to the context to initialize.
 * @param[in] pxParams Pointer to the parameters to use.
 * @param[in] ulRandomSeed Initial seed for the PRNG used in jitter calculation.
 *
 * @return BackoffRetrySuccess if initialization succeeded;
 *         BackoffRetryParamsInvalid if any parameter is invalid.
 */
BackoffRetryStatus_t BackoffRetry_Init( BackoffRetryContext_t * pxContext,
                                        const BackoffRetryParams_t * pxParams,
                                        uint32_t ulRandomSeed );

/**
 * @brief Compute the next backoff delay and advance the attempt counter.
 *
 * @param[in,out] pxContext Pointer to the backoff retry context.
 * @param[out] pulDelayMs Pointer to receive the computed delay in milliseconds.
 *
 * @return BackoffRetrySuccess if a delay was computed;
 *         BackoffRetryRetriesExhausted if all retries have been used;
 *         BackoffRetryParamsInvalid if any pointer is NULL.
 */
BackoffRetryStatus_t BackoffRetry_GetNextBackoff( BackoffRetryContext_t * pxContext,
                                                   uint32_t * pulDelayMs );

/**
 * @brief Reset the retry context to start a new retry sequence, keeping params.
 *
 * @param[in,out] pxContext Pointer to the context to reset.
 *
 * @return BackoffRetrySuccess on success;
 *         BackoffRetryParamsInvalid if pxContext is NULL.
 */
BackoffRetryStatus_t BackoffRetry_Reset( BackoffRetryContext_t * pxContext );

/**
 * @brief Get the number of retry attempts completed so far.
 *
 * @param[in] pxContext Pointer to the backoff retry context.
 *
 * @return Number of attempts done, or 0 if pxContext is NULL.
 */
uint32_t BackoffRetry_GetAttemptsDone( const BackoffRetryContext_t * pxContext );

/**
 * @brief Get the total time waited across all retry attempts so far.
 *
 * @param[in] pxContext Pointer to the backoff retry context.
 *
 * @return Total waited time in milliseconds, or 0 if pxContext is NULL.
 */
uint32_t BackoffRetry_GetTotalWaitedMs( const BackoffRetryContext_t * pxContext );

/**
 * @brief Check whether the retry sequence is exhausted.
 *
 * @param[in] pxContext Pointer to the backoff retry context.
 *
 * @return 1 if exhausted, 0 if retries remain, 0 if pxContext is NULL.
 */
uint8_t BackoffRetry_IsExhausted( const BackoffRetryContext_t * pxContext );

/**
 * @brief Update the random seed used for jitter calculation.
 *
 * @param[in,out] pxContext Pointer to the backoff retry context.
 * @param[in] ulNewSeed The new random seed value.
 *
 * @return BackoffRetrySuccess on success;
 *         BackoffRetryParamsInvalid if pxContext is NULL.
 */
BackoffRetryStatus_t BackoffRetry_SetRandomSeed( BackoffRetryContext_t * pxContext,
                                                  uint32_t ulNewSeed );

#endif /* BACKOFF_RETRY_H */
