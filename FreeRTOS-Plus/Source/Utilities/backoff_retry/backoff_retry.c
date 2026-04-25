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
 * @file backoff_retry.c
 * @brief Implementation of the retry-with-exponential-backoff utility.
 */

#include "backoff_retry.h"

/* Multiplier for LCG pseudo-random number generator. */
#define BACKOFF_PRNG_MULTIPLIER    ( ( uint32_t ) 1103515245U )

/* Increment for LCG pseudo-random number generator. */
#define BACKOFF_PRNG_INCREMENT     ( ( uint32_t ) 12345U )

/* Shift amount for extracting pseudo-random value from LCG state. */
#define BACKOFF_PRNG_SHIFT         ( ( uint32_t ) 16U )

/* Mask applied after shift for extracting a 15-bit pseudo-random value. */
#define BACKOFF_PRNG_MASK          ( ( uint32_t ) 0x7FFFU )

/* Maximum value representable in uint32_t, used for overflow checks. */
#define BACKOFF_UINT32_MAX         ( ( uint32_t ) 0xFFFFFFFFU )

/*-----------------------------------------------------------*/

/**
 * @brief Generate a pseudo-random number using a linear congruential generator.
 *
 * Updates the seed in place and returns a value in [0, ulMax].
 *
 * @param[in,out] pulSeed Pointer to the current PRNG seed.
 * @param[in] ulMax The upper bound (inclusive) for the returned value.
 *
 * @return A pseudo-random value in the range [0, ulMax].
 */
static uint32_t prvGenerateJitter( uint32_t * pulSeed,
                                   uint32_t ulMax )
{
    uint32_t ulRandom;

    /* Advance the LCG state. */
    *pulSeed = ( *pulSeed * BACKOFF_PRNG_MULTIPLIER ) + BACKOFF_PRNG_INCREMENT;

    /* Extract a pseudo-random value from the upper bits of the state. */
    ulRandom = ( *pulSeed >> BACKOFF_PRNG_SHIFT ) & BACKOFF_PRNG_MASK;

    /* Scale to [0, ulMax] range. */
    if( ulMax > 0U )
    {
        ulRandom = ulRandom % ( ulMax + 1U );
    }
    else
    {
        ulRandom = 0U;
    }

    return ulRandom;
}

/*-----------------------------------------------------------*/

/**
 * @brief Compute 2^exponent safely, capping at a maximum value.
 *
 * @param[in] ulExponent The exponent to raise 2 to.
 * @param[in] ulCap The maximum value to return (prevents overflow).
 *
 * @return min(2^ulExponent, ulCap).
 */
static uint32_t prvSafePow2( uint32_t ulExponent,
                              uint32_t ulCap )
{
    uint32_t ulResult = 1U;
    uint32_t i;

    for( i = 0U; i < ulExponent; i++ )
    {
        /* Check for potential overflow before doubling. */
        if( ulResult > ( ulCap / 2U ) )
        {
            ulResult = ulCap;
            break;
        }

        ulResult = ulResult * 2U;
    }

    if( ulResult > ulCap )
    {
        ulResult = ulCap;
    }

    return ulResult;
}

/*-----------------------------------------------------------*/

BackoffRetryStatus_t BackoffRetry_Init( BackoffRetryContext_t * pxContext,
                                        const BackoffRetryParams_t * pxParams,
                                        uint32_t ulRandomSeed )
{
    BackoffRetryStatus_t xStatus = BackoffRetrySuccess;

    if( ( pxContext == NULL ) || ( pxParams == NULL ) )
    {
        xStatus = BackoffRetryParamsInvalid;
    }
    else if( pxParams->ulBaseDelayMs == 0U )
    {
        /* Base delay of zero would cause immediate retries with no backoff. */
        xStatus = BackoffRetryParamsInvalid;
    }
    else if( pxParams->ulMaxDelayMs < pxParams->ulBaseDelayMs )
    {
        /* Max delay must be at least as large as the base delay. */
        xStatus = BackoffRetryParamsInvalid;
    }
    else
    {
        pxContext->xParams.ulMaxRetries = pxParams->ulMaxRetries;
        pxContext->xParams.ulBaseDelayMs = pxParams->ulBaseDelayMs;
        pxContext->xParams.ulMaxDelayMs = pxParams->ulMaxDelayMs;
        pxContext->xParams.ulJitterMaxMs = pxParams->ulJitterMaxMs;
        pxContext->ulAttemptsDone = 0U;
        pxContext->ulNextDelayMs = 0U;
        pxContext->ulTotalWaitedMs = 0U;
        pxContext->ulRandomSeed = ulRandomSeed;
        pxContext->ucIsExhausted = 0U;
    }

    return xStatus;
}

/*-----------------------------------------------------------*/

BackoffRetryStatus_t BackoffRetry_GetNextBackoff( BackoffRetryContext_t * pxContext,
                                                   uint32_t * pulDelayMs )
{
    BackoffRetryStatus_t xStatus = BackoffRetrySuccess;
    uint32_t ulBackoff;
    uint32_t ulJitter;
    uint32_t ulDelay;

    if( ( pxContext == NULL ) || ( pulDelayMs == NULL ) )
    {
        xStatus = BackoffRetryParamsInvalid;
    }
    else if( pxContext->ucIsExhausted != 0U )
    {
        /* Already exhausted from a previous call. */
        xStatus = BackoffRetryRetriesExhausted;
    }
    else if( ( pxContext->xParams.ulMaxRetries > 0U ) &&
             ( pxContext->ulAttemptsDone >= pxContext->xParams.ulMaxRetries ) )
    {
        /* Maximum retry count reached. */
        pxContext->ucIsExhausted = 1U;
        xStatus = BackoffRetryRetriesExhausted;
    }
    else
    {
        /* Compute the exponential backoff: base * 2^attempt, capped at max. */
        ulBackoff = prvSafePow2( pxContext->ulAttemptsDone,
                                  pxContext->xParams.ulMaxDelayMs / pxContext->xParams.ulBaseDelayMs );

        /* Multiply by base delay, checking for overflow. */
        if( ulBackoff > ( BACKOFF_UINT32_MAX / pxContext->xParams.ulBaseDelayMs ) )
        {
            ulDelay = pxContext->xParams.ulMaxDelayMs;
        }
        else
        {
            ulDelay = pxContext->xParams.ulBaseDelayMs * ulBackoff;
        }

        /* Cap at the configured maximum delay. */
        if( ulDelay > pxContext->xParams.ulMaxDelayMs )
        {
            ulDelay = pxContext->xParams.ulMaxDelayMs;
        }

        /* Add jitter if configured. */
        if( pxContext->xParams.ulJitterMaxMs > 0U )
        {
            ulJitter = prvGenerateJitter( &( pxContext->ulRandomSeed ),
                                           pxContext->xParams.ulJitterMaxMs );

            /* Add jitter with overflow protection. */
            if( ulDelay <= ( BACKOFF_UINT32_MAX - ulJitter ) )
            {
                ulDelay = ulDelay + ulJitter;
            }
            else
            {
                ulDelay = BACKOFF_UINT32_MAX;
            }

            /* Re-cap after adding jitter. The total delay including jitter
             * may exceed ulMaxDelayMs by up to ulJitterMaxMs; this is by
             * design to provide effective decorrelation. However, if jitter
             * pushed us past the absolute cap, clamp it. */
            if( ( ulDelay > pxContext->xParams.ulMaxDelayMs ) &&
                ( pxContext->xParams.ulJitterMaxMs < pxContext->xParams.ulMaxDelayMs ) )
            {
                ulDelay = pxContext->xParams.ulMaxDelayMs;
            }
        }

        *pulDelayMs = ulDelay;
        pxContext->ulNextDelayMs = ulDelay;
        pxContext->ulAttemptsDone += 1U;

        /* Track total wait time with overflow protection. */
        if( pxContext->ulTotalWaitedMs <= ( BACKOFF_UINT32_MAX - ulDelay ) )
        {
            pxContext->ulTotalWaitedMs += ulDelay;
        }
        else
        {
            pxContext->ulTotalWaitedMs = BACKOFF_UINT32_MAX;
        }
    }

    return xStatus;
}

/*-----------------------------------------------------------*/

BackoffRetryStatus_t BackoffRetry_Reset( BackoffRetryContext_t * pxContext )
{
    BackoffRetryStatus_t xStatus = BackoffRetrySuccess;

    if( pxContext == NULL )
    {
        xStatus = BackoffRetryParamsInvalid;
    }
    else
    {
        pxContext->ulAttemptsDone = 0U;
        pxContext->ulNextDelayMs = 0U;
        pxContext->ulTotalWaitedMs = 0U;
        pxContext->ucIsExhausted = 0U;
        /* Retain the current random seed for continuity. */
    }

    return xStatus;
}

/*-----------------------------------------------------------*/

uint32_t BackoffRetry_GetAttemptsDone( const BackoffRetryContext_t * pxContext )
{
    uint32_t ulAttempts = 0U;

    if( pxContext != NULL )
    {
        ulAttempts = pxContext->ulAttemptsDone;
    }

    return ulAttempts;
}

/*-----------------------------------------------------------*/

uint32_t BackoffRetry_GetTotalWaitedMs( const BackoffRetryContext_t * pxContext )
{
    uint32_t ulTotal = 0U;

    if( pxContext != NULL )
    {
        ulTotal = pxContext->ulTotalWaitedMs;
    }

    return ulTotal;
}

/*-----------------------------------------------------------*/

uint8_t BackoffRetry_IsExhausted( const BackoffRetryContext_t * pxContext )
{
    uint8_t ucExhausted = 0U;

    if( pxContext != NULL )
    {
        ucExhausted = pxContext->ucIsExhausted;
    }

    return ucExhausted;
}

/*-----------------------------------------------------------*/

BackoffRetryStatus_t BackoffRetry_SetRandomSeed( BackoffRetryContext_t * pxContext,
                                                  uint32_t ulNewSeed )
{
    BackoffRetryStatus_t xStatus = BackoffRetrySuccess;

    if( pxContext == NULL )
    {
        xStatus = BackoffRetryParamsInvalid;
    }
    else
    {
        pxContext->ulRandomSeed = ulNewSeed;
    }

    return xStatus;
}
