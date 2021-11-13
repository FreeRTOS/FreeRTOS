/*
 * FreeRTOS V202111.00
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
/*! @file recursive_mutex_utest.c */

#include "../queue_utest_common.h"

/* Queue includes */
#include "FreeRTOS.h"
#include "FreeRTOSConfig.h"
#include "semphr.h"
#include "mock_fake_port.h"

/* ============================  GLOBAL VARIABLES =========================== */

/* ==========================  CALLBACK FUNCTIONS =========================== */

/* ============================= Unity Fixtures ============================= */

void setUp( void )
{
    commonSetUp();
    xTaskPriorityDisinherit_IgnoreAndReturn( pdFALSE );
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
 * @brief Test xSemaphoreCreateRecursiveMutex where the call to malloc fails
 * @coverage xQueueCreateMutex
 */
void test_macro_xSemaphoreCreateRecursiveMutex_malloc_fail( void )
{
    UnityMalloc_MakeMallocFailAfterCount( 0 );

    SemaphoreHandle_t xSemaphore = INVALID_PTR;

    xSemaphore = xSemaphoreCreateRecursiveMutex();

    /* validate returned semaphore handle */
    TEST_ASSERT_EQUAL( NULL, xSemaphore );
}

/**
 * @brief Test xSemaphoreCreateRecursiveMutex
 * @details Create a mutex using xSemaphoreCreateRecursiveMutex
 * @coverage xQueueCreateMutex
 */
void test_macro_xSemaphoreCreateRecursiveMutex_success( void )
{
    SemaphoreHandle_t xSemaphore = xSemaphoreCreateRecursiveMutex();

    /* validate returned semaphore handle */
    TEST_ASSERT_NOT_EQUAL( NULL, xSemaphore );

    TEST_ASSERT_EQUAL( QUEUE_T_SIZE, getLastMallocSize() );

    TEST_ASSERT_EQUAL( B_SEMPHR_AVAILABLE, uxSemaphoreGetCount( xSemaphore ) );

    vSemaphoreDelete( xSemaphore );
}

/**
 * @brief Test xSemaphoreCreateRecursiveMutexStatic with a null buffer
 * @coverage xQueueCreateMutexStatic
 */
void test_macro_xSemaphoreCreateRecursiveMutexStatic_nullptr( void )
{
    SemaphoreHandle_t xSemaphore = INVALID_PTR;

    /* Expect that xQueueCreate will assert due to the NULL buffer */
    fakeAssertExpectFail();

    xSemaphore = xSemaphoreCreateRecursiveMutexStatic( NULL );

    /* Check that configASSERT was called twice */
    fakeAssertVerifyNumAssertsAndClear( 2 );

    TEST_ASSERT_EQUAL( NULL, xSemaphore );
    TEST_ASSERT_EQUAL( 0, getLastMallocSize() );
}

/**
 * @brief Verify that calling xSemaphoreTakeRecursive with a NULL mutex handle causes a configASSERT failure.
 * @coverage xQueueTakeMutexRecursive
 */
void test_macro_xSemaphoreTakeRecursive_null_handle( void )
{
    EXPECT_ASSERT_BREAK( xSemaphoreTakeRecursive( NULL, 0 ) );
}

/**
 * @brief Test xSemaphoreTakeRecursive with a mutex that is not owned by any task.
 * @coverage xQueueTakeMutexRecursive
 */
void test_macro_xSemaphoreTakeRecursive_not_owned_once( void )
{
    TaskHandle_t xMutexHolder = ( void * ) ( BaseType_t ) getNextMonotonicTestValue();

    SemaphoreHandle_t xSemaphore = xSemaphoreCreateRecursiveMutex();

    TEST_ASSERT_EQUAL( B_SEMPHR_AVAILABLE, uxSemaphoreGetCount( xSemaphore ) );

    xTaskGetCurrentTaskHandle_ExpectAndReturn( xMutexHolder );
    pvTaskIncrementMutexHeldCount_ExpectAndReturn( xMutexHolder );

    TEST_ASSERT_EQUAL( pdTRUE, xSemaphoreTakeRecursive( xSemaphore, 0 ) );

    TEST_ASSERT_EQUAL( B_SEMPHR_TAKEN, uxSemaphoreGetCount( xSemaphore ) );

    vSemaphoreDelete( xSemaphore );
}

/**
 * @brief Test xSemaphoreTakeRecursive with a mutex that is already owned by the current task
 * @coverage xQueueTakeMutexRecursive
 */
void test_macro_xSemaphoreTakeRecursive_self_owned_twice( void )
{
    TaskHandle_t xMutexHolder = ( void * ) ( BaseType_t ) getNextMonotonicTestValue();

    SemaphoreHandle_t xSemaphore = xSemaphoreCreateRecursiveMutex();

    TEST_ASSERT_EQUAL( B_SEMPHR_AVAILABLE, uxSemaphoreGetCount( xSemaphore ) );

    xTaskGetCurrentTaskHandle_ExpectAndReturn( xMutexHolder );
    pvTaskIncrementMutexHeldCount_ExpectAndReturn( xMutexHolder );

    TEST_ASSERT_EQUAL( pdTRUE, xSemaphoreTakeRecursive( xSemaphore, 0 ) );

    TEST_ASSERT_EQUAL( B_SEMPHR_TAKEN, uxSemaphoreGetCount( xSemaphore ) );

    xTaskGetCurrentTaskHandle_ExpectAndReturn( xMutexHolder );

    TEST_ASSERT_EQUAL( pdTRUE, xSemaphoreTakeRecursive( xSemaphore, 0 ) );

    TEST_ASSERT_EQUAL( B_SEMPHR_TAKEN, uxSemaphoreGetCount( xSemaphore ) );

    vSemaphoreDelete( xSemaphore );
}

/**
 * @brief Test xSemaphoreTakeRecursive on a mutex that is already owned by a different task
 * @coverage xQueueTakeMutexRecursive
 */
void test_macro_xSemaphoreTakeRecursive_owned_other_task( void )
{
    TaskHandle_t xMutexHolder1 = ( void * ) ( BaseType_t ) getNextMonotonicTestValue();
    TaskHandle_t xMutexHolder2 = ( void * ) ( BaseType_t ) getNextMonotonicTestValue();

    SemaphoreHandle_t xSemaphore = xSemaphoreCreateRecursiveMutex();

    /* Take the recursive mutex with task handle == xMutexHolder1 */
    xTaskGetCurrentTaskHandle_ExpectAndReturn( xMutexHolder1 );
    pvTaskIncrementMutexHeldCount_ExpectAndReturn( xMutexHolder1 );
    TEST_ASSERT_EQUAL( pdTRUE, xSemaphoreTakeRecursive( xSemaphore, 0 ) );

    /* Attempt to take the recursive mutex with task handle == xMutexHolder2 */
    xTaskGetCurrentTaskHandle_ExpectAndReturn( xMutexHolder2 );
    TEST_ASSERT_EQUAL( pdFALSE, xSemaphoreTakeRecursive( xSemaphore, 0 ) );

    vSemaphoreDelete( xSemaphore );
}

/**
 * @brief Verify that calling xSemaphoreGiveRecursive with a NULL mutex handle causes a configASSERT failure.
 * @coverage xQueueGiveMutexRecursive
 */
void test_macro_xSemaphoreGiveRecursive_null_handle( void )
{
    EXPECT_ASSERT_BREAK( xSemaphoreGiveRecursive( NULL ) );
}

/**
 * @brief Test xSemaphoreGiveRecursive with a mutex that is not already owned by any task.
 * @coverage xQueueGiveMutexRecursive
 */
void test_macro_xSemaphoreGiveRecursive_unowned( void )
{
    TaskHandle_t xMutexHolder = ( void * ) ( BaseType_t ) getNextMonotonicTestValue();

    SemaphoreHandle_t xSemaphore = xSemaphoreCreateRecursiveMutex();

    TEST_ASSERT_EQUAL( B_SEMPHR_AVAILABLE, uxSemaphoreGetCount( xSemaphore ) );

    xTaskGetCurrentTaskHandle_ExpectAndReturn( xMutexHolder );

    TEST_ASSERT_EQUAL( pdFALSE, xSemaphoreGiveRecursive( xSemaphore ) );

    TEST_ASSERT_EQUAL( B_SEMPHR_AVAILABLE, uxSemaphoreGetCount( xSemaphore ) );

    vSemaphoreDelete( xSemaphore );
}

/**
 * @brief Test xSemaphoreGiveRecursive with a mutex that is not owned by any task with a NULL TaskHandle returned by calls to xTaskGetCurrentTaskHandle.
 * @coverage xQueueGiveMutexRecursive
 */
void test_macro_xSemaphoreGiveRecursive_unowned_null_taskhandle( void )
{
    SemaphoreHandle_t xSemaphore = xSemaphoreCreateRecursiveMutex();

    TEST_ASSERT_EQUAL( B_SEMPHR_AVAILABLE, uxSemaphoreGetCount( xSemaphore ) );

    xTaskGetCurrentTaskHandle_ExpectAndReturn( NULL );

    TEST_ASSERT_EQUAL( pdTRUE, xSemaphoreGiveRecursive( xSemaphore ) );

    TEST_ASSERT_EQUAL( B_SEMPHR_AVAILABLE, uxSemaphoreGetCount( xSemaphore ) );

    vSemaphoreDelete( xSemaphore );
}

/**
 * @brief Test xSemaphoreGiveRecursive with a mutex that is already owned by the current task
 * @coverage xQueueGiveMutexRecursive
 */
void test_macro_xSemaphoreGiveRecursive_self_owned( void )
{
    TaskHandle_t xMutexHolder = ( void * ) ( BaseType_t ) getNextMonotonicTestValue();

    SemaphoreHandle_t xSemaphore = xSemaphoreCreateRecursiveMutex();

    /* Take the Recursive Mutex from taskHandle == xMutexHolder */
    xTaskGetCurrentTaskHandle_ExpectAndReturn( xMutexHolder );
    pvTaskIncrementMutexHeldCount_ExpectAndReturn( xMutexHolder );

    xSemaphoreTakeRecursive( xSemaphore, 0 );

    /* Verify that the Recursive Mutex is in the taken state */
    TEST_ASSERT_EQUAL( B_SEMPHR_TAKEN, uxSemaphoreGetCount( xSemaphore ) );

    /* call xSemaphoreGiveRecursive to release the Recursive Mutex */
    xTaskGetCurrentTaskHandle_ExpectAndReturn( xMutexHolder );

    TEST_ASSERT_EQUAL( pdTRUE, xSemaphoreGiveRecursive( xSemaphore ) );

    /* Verify that the Recursive Mutex is now in the available state */
    TEST_ASSERT_EQUAL( B_SEMPHR_AVAILABLE, uxSemaphoreGetCount( xSemaphore ) );

    vSemaphoreDelete( xSemaphore );
}

/**
 * @brief Test xSemaphoreGiveRecursive on a mutex that is already owned by a different task
 * @coverage xQueueGiveMutexRecursive
 */
void test_macro_xSemaphoreGiveRecursive_owned_other_task( void )
{
    TaskHandle_t xMutexHolder1 = ( void * ) ( BaseType_t ) getNextMonotonicTestValue();
    TaskHandle_t xMutexHolder2 = ( void * ) ( BaseType_t ) getNextMonotonicTestValue();

    SemaphoreHandle_t xSemaphore = xSemaphoreCreateRecursiveMutex();

    /* Take the Recursive Mutex from taskHandle == xMutexHolder */
    xTaskGetCurrentTaskHandle_ExpectAndReturn( xMutexHolder1 );
    pvTaskIncrementMutexHeldCount_ExpectAndReturn( xMutexHolder1 );

    xSemaphoreTakeRecursive( xSemaphore, 0 );

    /* Verify that the Recursive Mutex is in the taken state */
    TEST_ASSERT_EQUAL( B_SEMPHR_TAKEN, uxSemaphoreGetCount( xSemaphore ) );

    /* call xSemaphoreGiveRecursive to release the Recursive Mutex */
    xTaskGetCurrentTaskHandle_ExpectAndReturn( xMutexHolder2 );

    TEST_ASSERT_EQUAL( pdFALSE, xSemaphoreGiveRecursive( xSemaphore ) );

    /* Verify that the Recursive Mutex remains in the taken state */
    TEST_ASSERT_EQUAL( B_SEMPHR_TAKEN, uxSemaphoreGetCount( xSemaphore ) );

    vSemaphoreDelete( xSemaphore );
}


/**
 * @brief Call xSemaphoreTakeRecursive and xSemaphoreGiveRecursive each multiple times
 * @coverage xQueueTakeMutexRecursive xQueueGiveMutexRecursive
 */
void test_macro_xSemaphoreTakeRecursive_xSemaphoreGiveRecursive_recursive( void )
{
    TaskHandle_t xMutexHolder = ( void * ) ( BaseType_t ) getNextMonotonicTestValue();

    SemaphoreHandle_t xSemaphore = xSemaphoreCreateRecursiveMutex();

    /* Take the Recursive Mutex */
    xTaskGetCurrentTaskHandle_ExpectAndReturn( xMutexHolder );
    pvTaskIncrementMutexHeldCount_ExpectAndReturn( xMutexHolder );
    xSemaphoreTakeRecursive( xSemaphore, 0 );

    /* Verify that the Recursive Mutex is in the taken state */
    TEST_ASSERT_EQUAL( B_SEMPHR_TAKEN, uxSemaphoreGetCount( xSemaphore ) );

    /* Take the Recursive Mutex a second time */
    xTaskGetCurrentTaskHandle_ExpectAndReturn( xMutexHolder );
    xSemaphoreTakeRecursive( xSemaphore, 0 );

    /* Verify that the Recursive Mutex remains in the taken state */
    TEST_ASSERT_EQUAL( B_SEMPHR_TAKEN, uxSemaphoreGetCount( xSemaphore ) );

    /* call xSemaphoreGiveRecursive to release the Recursive Mutex (first time) */
    xTaskGetCurrentTaskHandle_ExpectAndReturn( xMutexHolder );
    TEST_ASSERT_EQUAL( pdTRUE, xSemaphoreGiveRecursive( xSemaphore ) );

    /* Verify that the Recursive Mutex remains in the taken state */
    TEST_ASSERT_EQUAL( B_SEMPHR_TAKEN, uxSemaphoreGetCount( xSemaphore ) );

    /* call xSemaphoreGiveRecursive to release the Recursive Mutex (second time) */
    xTaskGetCurrentTaskHandle_ExpectAndReturn( xMutexHolder );
    TEST_ASSERT_EQUAL( pdTRUE, xSemaphoreGiveRecursive( xSemaphore ) );

    /* Verify that the Recursive Mutex is now in the available state */
    TEST_ASSERT_EQUAL( B_SEMPHR_AVAILABLE, uxSemaphoreGetCount( xSemaphore ) );

    vSemaphoreDelete( xSemaphore );
}
