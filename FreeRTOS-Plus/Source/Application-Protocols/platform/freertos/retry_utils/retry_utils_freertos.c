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
 * @file retry_utils_freertos.c
 * @brief Utility implementation of backoff logic, used for attempting retries of failed processes.
 */

/* Standard includes. */
#include <stdint.h>

/* Kernel includes. */
#include "FreeRTOS.h"
#include "task.h"

#include "retry_utils.h"

#define MILLISECONDS_PER_SECOND    ( 1000U )                                                         /**< @brief Milliseconds per second. */

extern UBaseType_t uxRand( void );

/*-----------------------------------------------------------*/

RetryUtilsStatus_t RetryUtils_BackoffAndSleep( RetryUtilsParams_t * pRetryParams )
{
    RetryUtilsStatus_t status = RetryUtilsRetriesExhausted;
    uint32_t backOffDelayMs = 0;

    /* If pRetryParams->maxRetryAttempts is set to 0, try forever. */
    if( ( pRetryParams->attemptsDone < pRetryParams->maxRetryAttempts ) ||
        ( 0 == pRetryParams->maxRetryAttempts ) )
    {
        /* Choose a random value for back-off time between 0 and the max jitter value. */
        backOffDelayMs = uxRand() % pRetryParams->nextJitterMax;

        /*  Wait for backoff time to expire for the next retry. */
        vTaskDelay( pdMS_TO_TICKS( backOffDelayMs * MILLISECONDS_PER_SECOND ) );

        /* Increment backoff counts. */
        pRetryParams->attemptsDone++;

        /* Double the max jitter value for the next retry attempt, only
         * if the new value will be less than the max backoff time value. */
        if( pRetryParams->nextJitterMax < ( MAX_RETRY_BACKOFF_SECONDS / 2U ) )
        {
            pRetryParams->nextJitterMax += pRetryParams->nextJitterMax;
        }
        else
        {
            pRetryParams->nextJitterMax = MAX_RETRY_BACKOFF_SECONDS;
        }

        status = RetryUtilsSuccess;
    }
    else
    {
        /* When max retry attempts are exhausted, let application know by
         * returning RetryUtilsRetriesExhausted. Application may choose to
         * restart the retry process after calling RetryUtils_ParamsReset(). */
        status = RetryUtilsRetriesExhausted;
        RetryUtils_ParamsReset( pRetryParams );
    }

    return status;
}

/*-----------------------------------------------------------*/

void RetryUtils_ParamsReset( RetryUtilsParams_t * pRetryParams )
{
    uint32_t jitter = 0;

    /* Reset attempts done to zero so that the next retry cycle can start. */
    pRetryParams->attemptsDone = 0;

    /* Calculate jitter value using picking a random number. */
    jitter = ( uxRand() % MAX_JITTER_VALUE_SECONDS );

    /* Reset the backoff value to the initial time out value plus jitter. */
    pRetryParams->nextJitterMax = INITIAL_RETRY_BACKOFF_SECONDS + jitter;
}

/*-----------------------------------------------------------*/
