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
 * @file backoff_retry_utest.c
 * @brief Unit tests for the backoff_retry utility.
 */

/* Unity test framework. */
#include "unity.h"

/* Module under test. */
#include "backoff_retry.h"

/* ========================== DEFINES ============================== */

#define TEST_BASE_DELAY_MS        ( 1000U )
#define TEST_MAX_DELAY_MS         ( 32000U )
#define TEST_MAX_RETRIES          ( 5U )
#define TEST_JITTER_MAX_MS        ( 500U )
#define TEST_RANDOM_SEED          ( 12345U )
#define TEST_INFINITE_RETRIES     ( 0U )

/* ========================== HELPERS ============================== */

static BackoffRetryContext_t xContext;
static BackoffRetryParams_t xParams;

/* ======================== Unity Fixtures ========================= */

void setUp( void )
{
    xParams.ulBaseDelayMs = TEST_BASE_DELAY_MS;
    xParams.ulMaxDelayMs = TEST_MAX_DELAY_MS;
    xParams.ulMaxRetries = TEST_MAX_RETRIES;
    xParams.ulJitterMaxMs = TEST_JITTER_MAX_MS;

    memset( &xContext, 0, sizeof( xContext ) );
}

void tearDown( void )
{
    /* Nothing to clean up. */
}

/* ========================== TESTS ================================ */

/**
 * @brief BackoffRetry_Init succeeds with valid parameters.
 * @coverage BackoffRetry_Init
 */
void test_BackoffRetry_Init_ValidParams( void )
{
    BackoffRetryStatus_t xStatus;

    xStatus = BackoffRetry_Init( &xContext, &xParams, TEST_RANDOM_SEED );

    TEST_ASSERT_EQUAL( BackoffRetrySuccess, xStatus );
    TEST_ASSERT_EQUAL( 0U, xContext.ulAttemptsDone );
    TEST_ASSERT_EQUAL( 0U, xContext.ulTotalWaitedMs );
    TEST_ASSERT_EQUAL( 0U, xContext.ucIsExhausted );
    TEST_ASSERT_EQUAL( TEST_RANDOM_SEED, xContext.ulRandomSeed );
    TEST_ASSERT_EQUAL( TEST_BASE_DELAY_MS, xContext.xParams.ulBaseDelayMs );
    TEST_ASSERT_EQUAL( TEST_MAX_DELAY_MS, xContext.xParams.ulMaxDelayMs );
}

/**
 * @brief BackoffRetry_Init rejects NULL context pointer.
 * @coverage BackoffRetry_Init
 */
void test_BackoffRetry_Init_NullContext( void )
{
    BackoffRetryStatus_t xStatus;

    xStatus = BackoffRetry_Init( NULL, &xParams, TEST_RANDOM_SEED );

    TEST_ASSERT_EQUAL( BackoffRetryParamsInvalid, xStatus );
}

/**
 * @brief BackoffRetry_Init rejects NULL params pointer.
 * @coverage BackoffRetry_Init
 */
void test_BackoffRetry_Init_NullParams( void )
{
    BackoffRetryStatus_t xStatus;

    xStatus = BackoffRetry_Init( &xContext, NULL, TEST_RANDOM_SEED );

    TEST_ASSERT_EQUAL( BackoffRetryParamsInvalid, xStatus );
}

/**
 * @brief BackoffRetry_Init rejects zero base delay.
 * @coverage BackoffRetry_Init
 */
void test_BackoffRetry_Init_ZeroBaseDelay( void )
{
    BackoffRetryStatus_t xStatus;

    xParams.ulBaseDelayMs = 0U;
    xStatus = BackoffRetry_Init( &xContext, &xParams, TEST_RANDOM_SEED );

    TEST_ASSERT_EQUAL( BackoffRetryParamsInvalid, xStatus );
}

/**
 * @brief BackoffRetry_Init rejects max delay less than base delay.
 * @coverage BackoffRetry_Init
 */
void test_BackoffRetry_Init_MaxLessThanBase( void )
{
    BackoffRetryStatus_t xStatus;

    xParams.ulMaxDelayMs = 500U; /* Less than base of 1000. */
    xStatus = BackoffRetry_Init( &xContext, &xParams, TEST_RANDOM_SEED );

    TEST_ASSERT_EQUAL( BackoffRetryParamsInvalid, xStatus );
}

/**
 * @brief Delays increase exponentially with each attempt.
 * @coverage BackoffRetry_GetNextBackoff
 */
void test_BackoffRetry_GetNextBackoff_ExponentialIncrease( void )
{
    BackoffRetryStatus_t xStatus;
    uint32_t ulDelay;
    uint32_t ulPrevDelay = 0U;
    uint32_t i;

    /* Use zero jitter for deterministic testing. */
    xParams.ulJitterMaxMs = 0U;
    xParams.ulMaxRetries = 6U;
    xParams.ulMaxDelayMs = 64000U;
    BackoffRetry_Init( &xContext, &xParams, TEST_RANDOM_SEED );

    for( i = 0U; i < 6U; i++ )
    {
        xStatus = BackoffRetry_GetNextBackoff( &xContext, &ulDelay );
        TEST_ASSERT_EQUAL( BackoffRetrySuccess, xStatus );

        if( i > 0U )
        {
            /* Each delay should be double the previous (no jitter). */
            TEST_ASSERT_EQUAL( ulPrevDelay * 2U, ulDelay );
        }
        else
        {
            /* First delay should equal base delay. */
            TEST_ASSERT_EQUAL( TEST_BASE_DELAY_MS, ulDelay );
        }

        ulPrevDelay = ulDelay;
    }
}

/**
 * @brief Returns exhausted status when max retries exceeded.
 * @coverage BackoffRetry_GetNextBackoff
 */
void test_BackoffRetry_GetNextBackoff_Exhausted( void )
{
    BackoffRetryStatus_t xStatus;
    uint32_t ulDelay;
    uint32_t i;

    xParams.ulJitterMaxMs = 0U;
    BackoffRetry_Init( &xContext, &xParams, TEST_RANDOM_SEED );

    /* Exhaust all retries. */
    for( i = 0U; i < TEST_MAX_RETRIES; i++ )
    {
        xStatus = BackoffRetry_GetNextBackoff( &xContext, &ulDelay );
        TEST_ASSERT_EQUAL( BackoffRetrySuccess, xStatus );
    }

    /* Next call should report exhaustion. */
    xStatus = BackoffRetry_GetNextBackoff( &xContext, &ulDelay );
    TEST_ASSERT_EQUAL( BackoffRetryRetriesExhausted, xStatus );
    TEST_ASSERT_EQUAL( 1U, BackoffRetry_IsExhausted( &xContext ) );
}

/**
 * @brief Subsequent calls after exhaustion also return exhausted.
 * @coverage BackoffRetry_GetNextBackoff
 */
void test_BackoffRetry_GetNextBackoff_RepeatedExhausted( void )
{
    BackoffRetryStatus_t xStatus;
    uint32_t ulDelay;
    uint32_t i;

    xParams.ulJitterMaxMs = 0U;
    BackoffRetry_Init( &xContext, &xParams, TEST_RANDOM_SEED );

    for( i = 0U; i < TEST_MAX_RETRIES; i++ )
    {
        BackoffRetry_GetNextBackoff( &xContext, &ulDelay );
    }

    /* First exhausted call. */
    xStatus = BackoffRetry_GetNextBackoff( &xContext, &ulDelay );
    TEST_ASSERT_EQUAL( BackoffRetryRetriesExhausted, xStatus );

    /* Second exhausted call should also return exhausted. */
    xStatus = BackoffRetry_GetNextBackoff( &xContext, &ulDelay );
    TEST_ASSERT_EQUAL( BackoffRetryRetriesExhausted, xStatus );
}

/**
 * @brief Delay is capped at max delay.
 * @coverage BackoffRetry_GetNextBackoff
 */
void test_BackoffRetry_GetNextBackoff_CappedAtMax( void )
{
    BackoffRetryStatus_t xStatus;
    uint32_t ulDelay;
    uint32_t i;

    xParams.ulJitterMaxMs = 0U;
    xParams.ulMaxRetries = 20U;
    BackoffRetry_Init( &xContext, &xParams, TEST_RANDOM_SEED );

    /* Advance past the point where delay would exceed max. */
    for( i = 0U; i < 10U; i++ )
    {
        xStatus = BackoffRetry_GetNextBackoff( &xContext, &ulDelay );
        TEST_ASSERT_EQUAL( BackoffRetrySuccess, xStatus );
    }

    /* Delay should be capped at max. */
    TEST_ASSERT_TRUE( ulDelay <= TEST_MAX_DELAY_MS );
}

/**
 * @brief GetNextBackoff rejects NULL context.
 * @coverage BackoffRetry_GetNextBackoff
 */
void test_BackoffRetry_GetNextBackoff_NullContext( void )
{
    BackoffRetryStatus_t xStatus;
    uint32_t ulDelay;

    xStatus = BackoffRetry_GetNextBackoff( NULL, &ulDelay );

    TEST_ASSERT_EQUAL( BackoffRetryParamsInvalid, xStatus );
}

/**
 * @brief GetNextBackoff rejects NULL delay output pointer.
 * @coverage BackoffRetry_GetNextBackoff
 */
void test_BackoffRetry_GetNextBackoff_NullDelayPtr( void )
{
    BackoffRetryStatus_t xStatus;

    BackoffRetry_Init( &xContext, &xParams, TEST_RANDOM_SEED );
    xStatus = BackoffRetry_GetNextBackoff( &xContext, NULL );

    TEST_ASSERT_EQUAL( BackoffRetryParamsInvalid, xStatus );
}

/**
 * @brief Jitter adds randomness to the delay.
 * @coverage BackoffRetry_GetNextBackoff
 */
void test_BackoffRetry_GetNextBackoff_WithJitter( void )
{
    BackoffRetryStatus_t xStatus;
    uint32_t ulDelay;

    BackoffRetry_Init( &xContext, &xParams, TEST_RANDOM_SEED );

    xStatus = BackoffRetry_GetNextBackoff( &xContext, &ulDelay );

    TEST_ASSERT_EQUAL( BackoffRetrySuccess, xStatus );
    /* With jitter, delay should be between base and base+jitterMax. */
    TEST_ASSERT_TRUE( ulDelay >= TEST_BASE_DELAY_MS );
    TEST_ASSERT_TRUE( ulDelay <= TEST_BASE_DELAY_MS + TEST_JITTER_MAX_MS );
}

/**
 * @brief Reset brings context back to initial state.
 * @coverage BackoffRetry_Reset
 */
void test_BackoffRetry_Reset_ResetsState( void )
{
    BackoffRetryStatus_t xStatus;
    uint32_t ulDelay;

    xParams.ulJitterMaxMs = 0U;
    BackoffRetry_Init( &xContext, &xParams, TEST_RANDOM_SEED );

    /* Do a few retries. */
    BackoffRetry_GetNextBackoff( &xContext, &ulDelay );
    BackoffRetry_GetNextBackoff( &xContext, &ulDelay );
    TEST_ASSERT_EQUAL( 2U, BackoffRetry_GetAttemptsDone( &xContext ) );

    /* Reset. */
    xStatus = BackoffRetry_Reset( &xContext );
    TEST_ASSERT_EQUAL( BackoffRetrySuccess, xStatus );
    TEST_ASSERT_EQUAL( 0U, BackoffRetry_GetAttemptsDone( &xContext ) );
    TEST_ASSERT_EQUAL( 0U, BackoffRetry_GetTotalWaitedMs( &xContext ) );
    TEST_ASSERT_EQUAL( 0U, BackoffRetry_IsExhausted( &xContext ) );
}

/**
 * @brief Reset on NULL context returns error.
 * @coverage BackoffRetry_Reset
 */
void test_BackoffRetry_Reset_NullContext( void )
{
    BackoffRetryStatus_t xStatus;

    xStatus = BackoffRetry_Reset( NULL );

    TEST_ASSERT_EQUAL( BackoffRetryParamsInvalid, xStatus );
}

/**
 * @brief Reset allows retrying after exhaustion.
 * @coverage BackoffRetry_Reset
 */
void test_BackoffRetry_Reset_AllowsRetryAfterExhaustion( void )
{
    BackoffRetryStatus_t xStatus;
    uint32_t ulDelay;
    uint32_t i;

    xParams.ulJitterMaxMs = 0U;
    xParams.ulMaxRetries = 2U;
    BackoffRetry_Init( &xContext, &xParams, TEST_RANDOM_SEED );

    /* Exhaust retries. */
    BackoffRetry_GetNextBackoff( &xContext, &ulDelay );
    BackoffRetry_GetNextBackoff( &xContext, &ulDelay );
    xStatus = BackoffRetry_GetNextBackoff( &xContext, &ulDelay );
    TEST_ASSERT_EQUAL( BackoffRetryRetriesExhausted, xStatus );

    /* Reset and retry. */
    BackoffRetry_Reset( &xContext );
    xStatus = BackoffRetry_GetNextBackoff( &xContext, &ulDelay );
    TEST_ASSERT_EQUAL( BackoffRetrySuccess, xStatus );
    TEST_ASSERT_EQUAL( TEST_BASE_DELAY_MS, ulDelay );
}

/**
 * @brief GetAttemptsDone returns correct count.
 * @coverage BackoffRetry_GetAttemptsDone
 */
void test_BackoffRetry_GetAttemptsDone( void )
{
    uint32_t ulDelay;

    xParams.ulJitterMaxMs = 0U;
    BackoffRetry_Init( &xContext, &xParams, TEST_RANDOM_SEED );

    TEST_ASSERT_EQUAL( 0U, BackoffRetry_GetAttemptsDone( &xContext ) );

    BackoffRetry_GetNextBackoff( &xContext, &ulDelay );
    TEST_ASSERT_EQUAL( 1U, BackoffRetry_GetAttemptsDone( &xContext ) );

    BackoffRetry_GetNextBackoff( &xContext, &ulDelay );
    TEST_ASSERT_EQUAL( 2U, BackoffRetry_GetAttemptsDone( &xContext ) );
}

/**
 * @brief GetAttemptsDone with NULL returns 0.
 * @coverage BackoffRetry_GetAttemptsDone
 */
void test_BackoffRetry_GetAttemptsDone_NullContext( void )
{
    TEST_ASSERT_EQUAL( 0U, BackoffRetry_GetAttemptsDone( NULL ) );
}

/**
 * @brief TotalWaitedMs accumulates across retries.
 * @coverage BackoffRetry_GetTotalWaitedMs
 */
void test_BackoffRetry_GetTotalWaitedMs( void )
{
    uint32_t ulDelay;
    uint32_t ulExpectedTotal = 0U;

    xParams.ulJitterMaxMs = 0U;
    xParams.ulMaxRetries = 3U;
    BackoffRetry_Init( &xContext, &xParams, TEST_RANDOM_SEED );

    BackoffRetry_GetNextBackoff( &xContext, &ulDelay );
    ulExpectedTotal += ulDelay;
    TEST_ASSERT_EQUAL( ulExpectedTotal, BackoffRetry_GetTotalWaitedMs( &xContext ) );

    BackoffRetry_GetNextBackoff( &xContext, &ulDelay );
    ulExpectedTotal += ulDelay;
    TEST_ASSERT_EQUAL( ulExpectedTotal, BackoffRetry_GetTotalWaitedMs( &xContext ) );
}

/**
 * @brief GetTotalWaitedMs with NULL returns 0.
 * @coverage BackoffRetry_GetTotalWaitedMs
 */
void test_BackoffRetry_GetTotalWaitedMs_NullContext( void )
{
    TEST_ASSERT_EQUAL( 0U, BackoffRetry_GetTotalWaitedMs( NULL ) );
}

/**
 * @brief IsExhausted with NULL returns 0.
 * @coverage BackoffRetry_IsExhausted
 */
void test_BackoffRetry_IsExhausted_NullContext( void )
{
    TEST_ASSERT_EQUAL( 0U, BackoffRetry_IsExhausted( NULL ) );
}

/**
 * @brief SetRandomSeed updates the seed.
 * @coverage BackoffRetry_SetRandomSeed
 */
void test_BackoffRetry_SetRandomSeed( void )
{
    BackoffRetryStatus_t xStatus;
    uint32_t ulDelay1, ulDelay2;

    BackoffRetry_Init( &xContext, &xParams, TEST_RANDOM_SEED );
    BackoffRetry_GetNextBackoff( &xContext, &ulDelay1 );

    /* Reset and set a different seed — should produce different jitter. */
    BackoffRetry_Reset( &xContext );
    BackoffRetry_SetRandomSeed( &xContext, 99999U );
    BackoffRetry_GetNextBackoff( &xContext, &ulDelay2 );

    /* Delays may or may not differ, but seed should have been updated. */
    TEST_ASSERT_EQUAL( 99999U + 1U, BackoffRetry_GetAttemptsDone( &xContext ) ? 0U : 0U );
    /* Verify the seed was applied by checking internal state. */
    TEST_ASSERT_NOT_EQUAL( TEST_RANDOM_SEED, xContext.ulRandomSeed );
}

/**
 * @brief SetRandomSeed with NULL context returns error.
 * @coverage BackoffRetry_SetRandomSeed
 */
void test_BackoffRetry_SetRandomSeed_NullContext( void )
{
    BackoffRetryStatus_t xStatus;

    xStatus = BackoffRetry_SetRandomSeed( NULL, TEST_RANDOM_SEED );

    TEST_ASSERT_EQUAL( BackoffRetryParamsInvalid, xStatus );
}

/**
 * @brief Infinite retries mode (maxRetries=0) never exhausts.
 * @coverage BackoffRetry_GetNextBackoff
 */
void test_BackoffRetry_InfiniteRetries( void )
{
    BackoffRetryStatus_t xStatus;
    uint32_t ulDelay;
    uint32_t i;

    xParams.ulMaxRetries = TEST_INFINITE_RETRIES;
    xParams.ulJitterMaxMs = 0U;
    BackoffRetry_Init( &xContext, &xParams, TEST_RANDOM_SEED );

    /* Do many retries — should never exhaust. */
    for( i = 0U; i < 100U; i++ )
    {
        xStatus = BackoffRetry_GetNextBackoff( &xContext, &ulDelay );
        TEST_ASSERT_EQUAL( BackoffRetrySuccess, xStatus );
    }

    TEST_ASSERT_EQUAL( 0U, BackoffRetry_IsExhausted( &xContext ) );
    TEST_ASSERT_EQUAL( 100U, BackoffRetry_GetAttemptsDone( &xContext ) );
}

/**
 * @brief Init with equal base and max delay produces constant delay.
 * @coverage BackoffRetry_Init BackoffRetry_GetNextBackoff
 */
void test_BackoffRetry_ConstantDelay( void )
{
    BackoffRetryStatus_t xStatus;
    uint32_t ulDelay;
    uint32_t i;

    xParams.ulBaseDelayMs = 5000U;
    xParams.ulMaxDelayMs = 5000U;
    xParams.ulJitterMaxMs = 0U;
    xParams.ulMaxRetries = 5U;
    BackoffRetry_Init( &xContext, &xParams, TEST_RANDOM_SEED );

    for( i = 0U; i < 5U; i++ )
    {
        xStatus = BackoffRetry_GetNextBackoff( &xContext, &ulDelay );
        TEST_ASSERT_EQUAL( BackoffRetrySuccess, xStatus );
        TEST_ASSERT_EQUAL( 5000U, ulDelay );
    }
}
