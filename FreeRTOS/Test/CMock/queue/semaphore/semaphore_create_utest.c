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
/*! @file semaphore_create_utest.c */

#include "../queue_utest_common.h"
#include "mock_fake_port.h"

/* Queue includes */
#include "FreeRTOS.h"
#include "FreeRTOSConfig.h"
#include "semphr.h"

/* ================================  CONSTANTS ============================== */

/* ============================  GLOBAL VARIABLES =========================== */

/* ==========================  CALLBACK FUNCTIONS =========================== */

/* ============================= Unity Fixtures ============================= */

void setUp( void )
{
    commonSetUp();
}

void tearDown( void )
{
    commonTearDown();
}

void suiteSetUp()
{
    commonSuiteSetUp();
}

int suiteTearDown( int numFailures )
{
    return commonSuiteTearDown( numFailures );
}

/* ==========================  Helper functions =========================== */

/* =============================  Test Cases ============================== */


/**
 * @brief Test xSemaphoreCreateBinary where the call to malloc fails
 * @coverage xQueueGenericCreate
 */
void test_macro_xSemaphoreCreateBinary_malloc_fail( void )
{
    UnityMalloc_MakeMallocFailAfterCount( 0 );

    SemaphoreHandle_t xSemaphore = INVALID_PTR;

    xSemaphore = xSemaphoreCreateBinary();

    /* validate returned semaphore handle */
    TEST_ASSERT_EQUAL( NULL, xSemaphore );
}

/**
 * @brief Test xSemaphoreCreateBinary
 * @details Create a semaphore using xSemaphoreCreateBinary and verify that it
 *          is in the "taken" state upon creation.
 * @coverage xQueueGenericCreateStatic
 */
void test_macro_xSemaphoreCreateBinary_success( void )
{
    SemaphoreHandle_t xSemaphore = xSemaphoreCreateBinary();

    /* validate returned semaphore handle */
    TEST_ASSERT_NOT_EQUAL( NULL, xSemaphore );

    TEST_ASSERT_EQUAL( QUEUE_T_SIZE, getLastMallocSize() );

    TEST_ASSERT_EQUAL( B_SEMPHR_TAKEN, uxSemaphoreGetCount( xSemaphore ) );

    vSemaphoreDelete( xSemaphore );
}

/**
 * @brief Test xSemaphoreCreateBinaryStatic with a null buffer
 * @coverage xQueueGenericCreateStatic
 */
void test_macro_xSemaphoreCreateBinaryStatic_fail( void )
{
    SemaphoreHandle_t xSemaphore = INVALID_PTR;

    /* Expect that xSemaphoreCreate will assert due to the NULL buffer */
    fakeAssertExpectFail();

    xSemaphore = xSemaphoreCreateBinaryStatic( NULL );

    /* verify that configASSERT was called twice */
    fakeAssertVerifyNumAssertsAndClear( 2 );

    TEST_ASSERT_EQUAL( NULL, xSemaphore );
    TEST_ASSERT_EQUAL( 0, getLastMallocSize() );
}

/**
 * @brief Test xSemaphoreCreateBinaryStatic with a valid buffer.
 * @details Create a semaphore using xSemaphoreCreateBinaryStatic and verify
 *  that it is in the "taken" state upon creation.
 * @coverage xQueueGenericCreateStatic
 */
void test_macro_xSemaphoreCreateBinaryStatic_success( void )
{
    SemaphoreHandle_t xSemaphore = NULL;
    StaticSemaphore_t xSemaphoreBuffer;

    xSemaphore = xSemaphoreCreateBinaryStatic( &xSemaphoreBuffer );

    /* Check that no call to malloc occurred */
    TEST_ASSERT_EQUAL( 0, getLastMallocSize() );

    TEST_ASSERT_EQUAL( B_SEMPHR_TAKEN, uxSemaphoreGetCount( xSemaphore ) );

    vSemaphoreDelete( xSemaphore );
}

/**
 * @deprecated
 * @brief Test vSemaphoreCreateBinary where the call to malloc fails
 * @coverage xQueueGenericCreate
 */
void test_macro_vSemaphoreCreateBinary_malloc_fail( void )
{
    SemaphoreHandle_t xSemaphore = INVALID_PTR;

    UnityMalloc_MakeMallocFailAfterCount( 0 );

    vSemaphoreCreateBinary( xSemaphore );

    /* validate returned semaphore handle */
    TEST_ASSERT_EQUAL( NULL, xSemaphore );
}

/**
 * @deprecated
 * @brief Test vSemaphoreCreateBinary
 * @details Create a semaphore using vSemaphoreCreateBinary and verify that it
 *          is in the "given" state upon creation
 * @coverage xQueueGenericCreate xQueueGenericSend
 */
void test_macro_vSemaphoreCreateBinary_success( void )
{
    SemaphoreHandle_t xSemaphore = NULL;

    vSemaphoreCreateBinary( xSemaphore );

    /* validate returned semaphore handle */
    TEST_ASSERT_NOT_EQUAL( NULL, xSemaphore );
    TEST_ASSERT_EQUAL( QUEUE_T_SIZE, getLastMallocSize() );

    TEST_ASSERT_EQUAL( B_SEMPHR_AVAILABLE, uxSemaphoreGetCount( xSemaphore ) );

    vSemaphoreDelete( xSemaphore );
}

/**
 * @brief Test xSemaphoreCreateCounting where the call to malloc fails
 * @coverage
 * @coverage xQueueCreateCountingSemaphore
 */
void test_macro_xSemaphoreCreateCounting_malloc_fail( void )
{
    UnityMalloc_MakeMallocFailAfterCount( 0 );

    SemaphoreHandle_t xSemaphore = INVALID_PTR;

    xSemaphore = xSemaphoreCreateCounting( 10, 0 );

    /* validate returned semaphore handle */
    TEST_ASSERT_EQUAL( NULL, xSemaphore );
}

/**
 * @brief Test xSemaphoreCreateCounting with uxMaxCount=1 and uxInitialCount=2
 * @details This is an invalid initial condition for a counting semaphore since
 *  uxMaxCount >= uxInitialCount.
 * @coverage xQueueCreateCountingSemaphore
 */
void test_macro_xSemaphoreCreateCounting_one_two( void )
{
    /* Expect that xSemaphoreCreateCounting will assert because
     *  uxInitialCount > xMaxCount  is invalid */
    fakeAssertExpectFail();

    SemaphoreHandle_t xSemaphore = xSemaphoreCreateCounting( 1, 2 );

    fakeAssertGetFlagAndClear();

    /* validate returned semaphore handle */
    TEST_ASSERT_EQUAL( NULL, xSemaphore );

    /* Check that no call to malloc occurred */
    TEST_ASSERT_EQUAL( 0, getLastMallocSize() );
}

/**
 * @brief Test xSemaphoreCreateCounting with uxMaxCount=UINT64_MAX - 1 and uxInitialCount=UINT64_MAX
 * @details This is an invalid initial condition for a counting semaphore since
 *  uxMaxCount >= uxInitialCount.
 * @coverage xQueueCreateCountingSemaphore
 */
void test_macro_xSemaphoreCreateCounting_over_upper_bound( void )
{
    /* Expect that xSemaphoreCreateCounting will configASSERT because
     *  uxInitialCount > xMaxCount is invalid */
    fakeAssertExpectFail();

    SemaphoreHandle_t xSemaphore = xSemaphoreCreateCounting( UINT64_MAX - 1, UINT64_MAX );

    /* verify that configASSERT was called */
    TEST_ASSERT_EQUAL( true, fakeAssertGetFlagAndClear() );

    /* validate returned semaphore handle */
    TEST_ASSERT_EQUAL( NULL, xSemaphore );

    /* Check that no call to malloc occurred */
    TEST_ASSERT_EQUAL( 0, getLastMallocSize() );
}

/**
 * @brief Test xSemaphoreCreateCounting with uxMaxCount=1 and uxInitialCount=0
 * @details Create a binary semaphore using xSemaphoreCreateCounting.
 * @coverage xQueueCreateCountingSemaphore
 */
void test_macro_xSemaphoreCreateCounting_one_zero( void )
{
    SemaphoreHandle_t xSemaphore = xSemaphoreCreateCounting( 1, 0 );

    /* validate returned semaphore handle */
    TEST_ASSERT_NOT_EQUAL( NULL, xSemaphore );

    TEST_ASSERT_EQUAL( QUEUE_T_SIZE, getLastMallocSize() );

    /* Check the initial count */
    TEST_ASSERT_EQUAL( 0, uxSemaphoreGetCount( xSemaphore ) );

    vSemaphoreDelete( xSemaphore );
}

/**
 * @brief Test xSemaphoreCreateCounting with uxMaxCount=0 and uxInitialCount=0
 * @details This is an invalid counting semaphore since the following condition
 * is always true for a counting semaphore: uxMaxCount > 0
 * @coverage xQueueCreateCountingSemaphore
 */
void test_macro_xSemaphoreCreateCounting_zero_zero( void )
{
    /* Expect that xSemaphoreCreateCounting will assert because uxMaxCount=0 is invalid */
    fakeAssertExpectFail();

    SemaphoreHandle_t xSemaphore = xSemaphoreCreateCounting( 0, 0 );

    /* verify that configASSERT was called */
    TEST_ASSERT_EQUAL( true, fakeAssertGetFlagAndClear() );

    /* validate returned semaphore handle */
    TEST_ASSERT_EQUAL( NULL, xSemaphore );

    /* Check that no call to malloc occurred */
    TEST_ASSERT_EQUAL( 0, getLastMallocSize() );
}

/**
 * @brief Test xSemaphoreCreateCounting( 100, 50 )
 * @details Test xSemaphoreCreateCounting with uxMaxCount=100 and uxInitialCount=50
 * @coverage xQueueCreateCountingSemaphore
 */
void test_macro_xSemaphoreCreateCounting_100_50_success( void )
{
    SemaphoreHandle_t xSemaphore = xSemaphoreCreateCounting( 100, 50 );

    /* validate returned semaphore handle */
    TEST_ASSERT_NOT_EQUAL( NULL, xSemaphore );

    TEST_ASSERT_EQUAL( QUEUE_T_SIZE, getLastMallocSize() );

    /* Check the initial count */
    TEST_ASSERT_EQUAL( 50, uxSemaphoreGetCount( xSemaphore ) );

    vSemaphoreDelete( xSemaphore );
}

/**
 * @brief Test xSemaphoreCreateCounting( UINT64_MAX, UINT64_MAX-1 )
 * @coverage xQueueCreateCountingSemaphore
 */
void test_macro_xSemaphoreCreateCounting_upper_bound_1( void )
{
    SemaphoreHandle_t xSemaphore = xSemaphoreCreateCounting( UINT64_MAX, UINT64_MAX - 1 );

    /* validate returned semaphore handle */
    TEST_ASSERT_NOT_EQUAL( NULL, xSemaphore );

    TEST_ASSERT_EQUAL( QUEUE_T_SIZE, getLastMallocSize() );

    TEST_ASSERT_EQUAL( UINT64_MAX - 1, uxSemaphoreGetCount( xSemaphore ) );

    vSemaphoreDelete( xSemaphore );
}

/**
 * @brief Test xSemaphoreCreateCounting( UINT64_MAX, UINT64_MAX )
 * @coverage xQueueCreateCountingSemaphore
 */
void test_macro_xSemaphoreCreateCounting_upper_bound_2( void )
{
    SemaphoreHandle_t xSemaphore = xSemaphoreCreateCounting( UINT64_MAX, UINT64_MAX );

    /* validate returned semaphore handle */
    TEST_ASSERT_NOT_EQUAL( NULL, xSemaphore );

    TEST_ASSERT_EQUAL( QUEUE_T_SIZE, getLastMallocSize() );

    TEST_ASSERT_EQUAL( UINT64_MAX, uxSemaphoreGetCount( xSemaphore ) );

    vSemaphoreDelete( xSemaphore );
}

/**
 * @brief Test xSemaphoreCreateCountingStatic with a null buffer
 * @details Calls xSemaphoreCreateCountingStatic with a null buffer and
 * uxMaxCount=2 and uxInitialCount=1
 * @coverage xQueueCreateCountingSemaphoreStatic
 */
void test_macro_xSemaphoreCreateCountingStatic_null_fail( void )
{
    SemaphoreHandle_t xSemaphore = INVALID_PTR;

    /* Expect that xQueueCreate will assert due to the NULL buffer */
    fakeAssertExpectFail();

    xSemaphore = xSemaphoreCreateCountingStatic( 2, 1, NULL );

    /* verify that configASSERT was called twice */
    fakeAssertVerifyNumAssertsAndClear( 2 );

    /* Verify that the returned handle is NULL */
    TEST_ASSERT_EQUAL( NULL, xSemaphore );

    /* check that no call to malloc occurred */
    TEST_ASSERT_EQUAL( 0, getLastMallocSize() );
}

/**
 * @brief Test xSemaphoreCreateCountingStatic with uxMaxCount=0 and uxInitialCount=0
 * @details This is an invalid counting semaphore since uxMaxCount > 0
 * @coverage xQueueCreateCountingSemaphoreStatic
 */
void test_macro_xSemaphoreCreateCountingStatic_zero_zero_fail( void )
{
    SemaphoreHandle_t xSemaphore = NULL;
    StaticSemaphore_t xSemaphoreBuffer;

    /* Expect that xQueueCreate will assert due to the NULL buffer */
    fakeAssertExpectFail();

    xSemaphore = xSemaphoreCreateCountingStatic( 0, 0, &xSemaphoreBuffer );

    /* verify that configASSERT was called */
    TEST_ASSERT_EQUAL( true, fakeAssertGetFlagAndClear() );

    /* validate returned semaphore handle */
    TEST_ASSERT_EQUAL( NULL, xSemaphore );

    /* Check that no malloc occurred */
    TEST_ASSERT_EQUAL( 0, getLastMallocSize() );
}

/**
 * @brief Test xSemaphoreCreateCountingStatic with uxMaxCount=1 and uxInitialCount=2
 * @details This is an invalid initial condition for a counting semaphore since
 *  uxMaxCount >= uxInitialCount.
 * @coverage xQueueCreateCountingSemaphoreStatic
 */
void test_macro_xSemaphoreCreateCountingStatic_one_two( void )
{
    SemaphoreHandle_t xSemaphore = NULL;
    StaticSemaphore_t xSemaphoreBuffer;

    /* Expect that xSemaphoreCreateCountingStatic will assert because
     *  uxInitialCount > xMaxCount is invalid */
    fakeAssertExpectFail();

    xSemaphore = xSemaphoreCreateCountingStatic( 1, 2, &xSemaphoreBuffer );

    fakeAssertGetFlagAndClear();

    /* validate returned semaphore handle */
    TEST_ASSERT_EQUAL( NULL, xSemaphore );

    /* verify that no heap memory allocation occurred */
    TEST_ASSERT_EQUAL( 0, getLastMallocSize() );
}

/**
 * @brief Test xSemaphoreCreateCountingStatic with uxMaxCount=1 and uxInitialCount=0
 * @details Create a binary semaphore using xSemaphoreCreateCountingStatic
 * @coverage xQueueCreateCountingSemaphoreStatic
 */
void test_macro_xSemaphoreCreateCountingStatic_one_zero_success( void )
{
    SemaphoreHandle_t xSemaphore = INVALID_PTR;
    StaticSemaphore_t xSemaphoreBuffer;

    xSemaphore = xSemaphoreCreateCountingStatic( 1, 0, &xSemaphoreBuffer );

    TEST_ASSERT_NOT_EQUAL( NULL, xSemaphore );
    TEST_ASSERT_EQUAL( 0, getLastMallocSize() );

    /* Check the initial count */
    TEST_ASSERT_EQUAL( 0, uxSemaphoreGetCount( xSemaphore ) );

    vSemaphoreDelete( xSemaphore );
}
