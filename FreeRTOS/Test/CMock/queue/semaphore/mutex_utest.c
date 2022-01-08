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
/*! @file mutex_utest.c */

#include "../queue_utest_common.h"

/* Queue includes */
#include "FreeRTOS.h"
#include "FreeRTOSConfig.h"
#include "semphr.h"
#include "mock_fake_port.h"

/* ============================  GLOBAL VARIABLES =========================== */
static SemaphoreHandle_t xSemaphoreHandleStatic = NULL;

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

/* ==========================  Test Cases =========================== */


/**
 * @brief Test xSemaphoreCreateMutex where the call to malloc fails
 * @coverage xQueueCreateMutex
 */
void test_macro_xSemaphoreCreateMutex_malloc_fail( void )
{
    UnityMalloc_MakeMallocFailAfterCount( 0 );

    SemaphoreHandle_t xSemaphore = INVALID_PTR;

    xSemaphore = xSemaphoreCreateMutex();

    /* validate returned semaphore handle */
    TEST_ASSERT_EQUAL( NULL, xSemaphore );
}

/**
 * @brief Test xSemaphoreCreateMutex
 * @details Create a mutex using xSemaphoreCreateMutex
 * @coverage xQueueCreateMutex
 */
void test_macro_xSemaphoreCreateMutex_success( void )
{
    xTaskPriorityDisinherit_ExpectAndReturn( NULL, pdFALSE );
    SemaphoreHandle_t xSemaphore = xSemaphoreCreateMutex();

    /* validate returned semaphore handle */
    TEST_ASSERT_NOT_EQUAL( NULL, xSemaphore );

    TEST_ASSERT_EQUAL( QUEUE_T_SIZE, getLastMallocSize() );

    TEST_ASSERT_EQUAL( B_SEMPHR_AVAILABLE, uxSemaphoreGetCount( xSemaphore ) );

    vSemaphoreDelete( xSemaphore );
}

/**
 * @brief Test xSemaphoreCreateMutexStatic with a null buffer
 * @coverage xQueueCreateMutexStatic
 */
void test_macro_xSemaphoreCreateMutexStatic_nullptr( void )
{
    SemaphoreHandle_t xSemaphore = INVALID_PTR;

    /* Expect that xQueueCreate will assert due to the NULL buffer */
    fakeAssertExpectFail();

    xSemaphore = xSemaphoreCreateMutexStatic( NULL );

    /* Check that configASSERT was called twice */
    fakeAssertVerifyNumAssertsAndClear( 2 );

    TEST_ASSERT_EQUAL( NULL, xSemaphore );
    TEST_ASSERT_EQUAL( 0, getLastMallocSize() );
}

/**
 * @brief Test xSemaphoreCreateMutexStatic with a valid buffer.
 * @details Create a semaphore using xSemaphoreCreateMutexStatic
 * @coverage xQueueCreateMutexStatic
 */
void test_macro_xSemaphoreCreateMutexStatic_success( void )
{
    SemaphoreHandle_t xSemaphore = NULL;
    StaticSemaphore_t xSemaphoreBuffer;

    xTaskPriorityDisinherit_ExpectAndReturn( NULL, pdFALSE );

    xSemaphore = xSemaphoreCreateMutexStatic( &xSemaphoreBuffer );

    /* Check that no call to malloc occurred */
    TEST_ASSERT_EQUAL( 0, getLastMallocSize() );

    TEST_ASSERT_EQUAL( B_SEMPHR_AVAILABLE, uxSemaphoreGetCount( xSemaphore ) );

    vSemaphoreDelete( xSemaphore );
}

/**
 * @brief Test xSemaphoreTake with a Mutex
 * @details Create a mutex using xSemaphoreCreateMutex
 * and verify that an immediate call to xSemaphoreTake succeeds.
 * @coverage xQueueSemaphoreTake
 */
void test_macro_xSemaphoreTake_success( void )
{
    xTaskPriorityDisinherit_ExpectAndReturn( NULL, pdFALSE );

    SemaphoreHandle_t xSemaphore = xSemaphoreCreateMutex();

    /* validate returned semaphore handle */
    TEST_ASSERT_NOT_EQUAL( NULL, xSemaphore );

    TEST_ASSERT_EQUAL( QUEUE_T_SIZE, getLastMallocSize() );

    pvTaskIncrementMutexHeldCount_IgnoreAndReturn( NULL );

    /* Verify that an immediate xSemaphoreTake operation succeeds */
    TEST_ASSERT_EQUAL( pdTRUE, xSemaphoreTake( xSemaphore, 0 ) );

    vSemaphoreDelete( xSemaphore );
}

/**
 * @brief Test xSemaphoreGive with xSemaphoreCreateMutex
 * @details Create a mutex using xSemaphoreCreateMutex
 * and verify that an immediate call to xSemaphoreGive fails.
 * @coverage xQueueGenericSend
 */
void test_macro_xSemaphoreGive_fail( void )
{
    xTaskPriorityDisinherit_ExpectAndReturn( NULL, pdFALSE );
    SemaphoreHandle_t xSemaphore = xSemaphoreCreateMutex();

    /* validate returned semaphore handle */
    TEST_ASSERT_NOT_EQUAL( NULL, xSemaphore );

    TEST_ASSERT_EQUAL( QUEUE_T_SIZE, getLastMallocSize() );

    /* Verify that an immediate xSemaphoreGive operation fails */
    TEST_ASSERT_EQUAL( pdFALSE, xSemaphoreGive( xSemaphore ) );

    vSemaphoreDelete( xSemaphore );
}

/**
 * @brief Test xSemaphoreGive and xSemaphoreTake with xSemaphoreCreateMutex
 * @details Create a mutex using xSemaphoreCreateMutex
 * and verify that an immediate call to xSemaphoreGive succeeds and a subsequent
 * call to xSemaphoreTake succeeds.
 * @coverage xQueueGenericSend xQueueSemaphoreTake
 */
void test_macro_xSemaphoreGive_xSemaphoreTake_success( void )
{
    xTaskPriorityDisinherit_ExpectAndReturn( NULL, pdFALSE );
    SemaphoreHandle_t xSemaphore = xSemaphoreCreateMutex();

    /* validate returned semaphore handle */
    TEST_ASSERT_NOT_EQUAL( NULL, xSemaphore );

    TEST_ASSERT_EQUAL( QUEUE_T_SIZE, getLastMallocSize() );

    pvTaskIncrementMutexHeldCount_ExpectAndReturn( 0 );

    /* Verify that an immediate xSemaphoreTake operation succeeds */
    TEST_ASSERT_EQUAL( pdTRUE, xSemaphoreTake( xSemaphore, 0 ) );

    xTaskPriorityDisinherit_ExpectAndReturn( NULL, pdFALSE );

    /* Verify that a subsequent xSemaphoreGive operation succeeds */
    TEST_ASSERT_EQUAL( pdTRUE, xSemaphoreGive( xSemaphore ) );

    vSemaphoreDelete( xSemaphore );
}

/**
 * @brief Test xSemaphoreGive multiple times on a Mutex.
 * @details Create a mutex using xSemaphoreCreateMutex
 * and verify that an immediate call to xSemaphoreGive succeeds and a subsequent
 * call to xSemaphoreGive fails.
 * @coverage xQueueGenericSend
 */
void test_macro_xSemaphoreGive_multiple_Mutex_fail( void )
{
    xTaskPriorityDisinherit_ExpectAndReturn( NULL, pdFALSE );
    SemaphoreHandle_t xSemaphore = xSemaphoreCreateMutex();

    /* validate returned semaphore handle */
    TEST_ASSERT_NOT_EQUAL( NULL, xSemaphore );

    TEST_ASSERT_EQUAL( QUEUE_T_SIZE, getLastMallocSize() );

    pvTaskIncrementMutexHeldCount_ExpectAndReturn( 0 );
    xTaskPriorityDisinherit_ExpectAndReturn( NULL, pdFALSE );

    xSemaphoreTake( xSemaphore, 0 );

    /* Verify that the first xSemaphoreGive call succeeds */
    TEST_ASSERT_EQUAL( pdTRUE, xSemaphoreGive( xSemaphore ) );

    /* Verify that a second xSemaphoreGive call fails */
    TEST_ASSERT_EQUAL( pdFALSE, xSemaphoreGive( xSemaphore ) );

    vSemaphoreDelete( xSemaphore );
}

/**
 * @brief Test xSemaphoreTake multiple times on a Mutex.
 * @details Create a Mutex using xSemaphoreCreateMutex,
 * verify that an immediate call to xSemaphoreTake succeeds, a subsequent
 * call to xSemaphoreGive succeds, but a second call to xSemaphoreGive fails.
 * @coverage xQueueSemaphoreTake
 */
void test_macro_xSemaphoreTake_multiple_Mutex_fail( void )
{
    xTaskPriorityDisinherit_ExpectAndReturn( NULL, pdFALSE );
    SemaphoreHandle_t xSemaphore = xSemaphoreCreateMutex();

    /* validate returned semaphore handle */
    TEST_ASSERT_NOT_EQUAL( NULL, xSemaphore );

    TEST_ASSERT_EQUAL( QUEUE_T_SIZE, getLastMallocSize() );

    pvTaskIncrementMutexHeldCount_ExpectAndReturn( 0 );

    /* Verify that an immediate xSemaphoreTake operation succeeds */
    TEST_ASSERT_EQUAL( pdTRUE, xSemaphoreTake( xSemaphore, 0 ) );

    /* Verify that the second xSemaphoreTake operation fails */
    TEST_ASSERT_EQUAL( pdFALSE, xSemaphoreTake( xSemaphore, 0 ) );

    vSemaphoreDelete( xSemaphore );
}

/**
 * @brief Test uxSemaphoreGetCount with a Mutex
 * @details Create a Mutex using xSemaphoreCreateMutex.
 *  validate the return value of uxSemaphoreGetCount(),
 *  call xSemaphoreTake() and validate the return value of uxSemaphoreGetCount()
 * @coverage uxQueueMessagesWaiting
 */
void test_macro_uxSemaphoreGetCount_Mutex( void )
{
    SemaphoreHandle_t xSemaphore = NULL;

    xTaskPriorityDisinherit_ExpectAndReturn( NULL, pdFALSE );

    pvTaskIncrementMutexHeldCount_ExpectAndReturn( 0 );

    xSemaphore = xSemaphoreCreateMutex();

    TEST_ASSERT_EQUAL( B_SEMPHR_AVAILABLE, uxSemaphoreGetCount( xSemaphore ) );

    xSemaphoreTake( xSemaphore, 0 );

    TEST_ASSERT_EQUAL( B_SEMPHR_TAKEN, uxSemaphoreGetCount( xSemaphore ) );

    vSemaphoreDelete( xSemaphore );
}

/**
 * @brief Test xSemaphoreGetMutexHolder with an invalid (null) SemaphoreHandle_t
 * @coverage xQueueGetMutexHolder
 */
void test_macro_xSemaphoreGetMutexHolder_NULL( void )
{
    /* This previously caused a segfault, but I patched queue.c */
    EXPECT_ASSERT_BREAK( xSemaphoreGetMutexHolder( NULL ) );
}

/**
 * @brief Test xSemaphoreGetMutexHolder with a handle of a binary semaphore
 * @details Verify that xSemaphoreGetMutexHolder returns NULL when given a handle to a binary semaphore rather than a mutex.
 * @coverage xQueueGetMutexHolder
 */
void test_macro_xSemaphoreGetMutexHolder_binary_semaphore( void )
{
    SemaphoreHandle_t xSemaphore = xSemaphoreCreateBinary();

    TEST_ASSERT_EQUAL( B_SEMPHR_TAKEN, uxSemaphoreGetCount( xSemaphore ) );

    TEST_ASSERT_EQUAL( NULL, xSemaphoreGetMutexHolder( xSemaphore ) );

    vSemaphoreDelete( xSemaphore );
}

/**
 * @brief Test xSemaphoreGetMutexHolder with a valid SemaphoreHandle_t
 * @coverage xQueueGetMutexHolder
 */
void test_macro_xSemaphoreGetMutexHolder_Mutex( void )
{
    TaskHandle_t xMutexHolder = ( void * ) ( BaseType_t ) getNextMonotonicTestValue();

    xTaskPriorityDisinherit_ExpectAndReturn( NULL, pdFALSE );

    SemaphoreHandle_t xSemaphore = xSemaphoreCreateMutex();

    pvTaskIncrementMutexHeldCount_ExpectAndReturn( xMutexHolder );

    TEST_ASSERT_EQUAL( pdTRUE, xSemaphoreTake( xSemaphore, 0 ) );

    TEST_ASSERT_EQUAL( xMutexHolder, xSemaphoreGetMutexHolder( xSemaphore ) );

    vSemaphoreDelete( xSemaphore );
}

/**
 * @brief Test xSemaphoreGetMutexHolderFromISR with an invalid (null) SemaphoreHandle_t
 * @coverage xQueueGetMutexHolderFromISR
 */
void test_macro_xSemaphoreGetMutexHolderFromISR_Mutex_NULL( void )
{
    EXPECT_ASSERT_BREAK( xSemaphoreGetMutexHolderFromISR( NULL ) );
}

/**
 * @brief Test xSemaphoreGetMutexHolderFromISR with a handle of a binary semaphore
 * @details Verify that xSemaphoreGetMutexHolderFromISR returns NULL when given a handle to a binary semaphore rather than a mutex.
 * @coverage xQueueGetMutexHolderFromISR
 */
void test_macro_xSemaphoreGetMutexHolderFromISR_binary_semaphore( void )
{
    SemaphoreHandle_t xSemaphore = xSemaphoreCreateBinary();

    TEST_ASSERT_EQUAL( B_SEMPHR_TAKEN, uxSemaphoreGetCount( xSemaphore ) );

    TEST_ASSERT_EQUAL( NULL, xSemaphoreGetMutexHolderFromISR( xSemaphore ) );

    vSemaphoreDelete( xSemaphore );
}

/**
 * @brief Test xSemaphoreGetMutexHolderFromISR with a valid SemaphoreHandle_t
 * @coverage xQueueGetMutexHolderFromISR
 */
void test_macro_xSemaphoreGetMutexHolderFromISR_Mutex( void )
{
    TaskHandle_t xMutexHolder = ( void * ) ( BaseType_t ) getNextMonotonicTestValue();

    xTaskPriorityDisinherit_ExpectAndReturn( NULL, pdFALSE );

    SemaphoreHandle_t xSemaphore = xSemaphoreCreateMutex();

    pvTaskIncrementMutexHeldCount_ExpectAndReturn( xMutexHolder );

    TEST_ASSERT_EQUAL( pdTRUE, xSemaphoreTake( xSemaphore, 0 ) );

    TEST_ASSERT_EQUAL( xMutexHolder, xSemaphoreGetMutexHolderFromISR( xSemaphore ) );

    vSemaphoreDelete( xSemaphore );
}

/**
 * @brief Test xSemaphoreGiveFromISR with a Mutex that has an owner.
 * @details Verify that xSemaphoreGiveFromISR configASSERTs when an owned mutex is given as the xSemaphore argument.
 * @coverage xQueueGiveFromISR
 */
void test_macro_xSemaphoreGiveFromISR_mutex_owned( void )
{
    TaskHandle_t xMutexHolder = ( void * ) ( BaseType_t ) getNextMonotonicTestValue();

    xTaskPriorityDisinherit_ExpectAndReturn( NULL, pdFALSE );

    SemaphoreHandle_t xSemaphore = xSemaphoreCreateMutex();

    /* Setup mocks for xSemaphoretake */
    pvTaskIncrementMutexHeldCount_ExpectAndReturn( xMutexHolder );
    vFakePortAssertIfInterruptPriorityInvalid_Expect();

    xSemaphoreTake( xSemaphore, 0 );

    /* Expect that xSemaphoreGiveFromISR will assert due to the mutex usage */
    fakeAssertExpectFail();

    TEST_ASSERT_EQUAL( pdTRUE, xSemaphoreGiveFromISR( xSemaphore, NULL ) );

    TEST_ASSERT_EQUAL( true, fakeAssertGetFlagAndClear() );

    TEST_ASSERT_EQUAL( B_SEMPHR_AVAILABLE, uxSemaphoreGetCount( xSemaphore ) );

    vSemaphoreDelete( xSemaphore );
}

/**
 * @brief Test xSemaphoreGiveFromISR with a Mutex that has a NULL owner.
 * @details Verify that xSemaphoreGiveFromISR does not configASSERT when a mutex with a NULL owner is given in the xSemaphore argument.
 * @coverage xQueueGiveFromISR
 */
void test_macro_xSemaphoreGiveFromISR_mutex_not_owned( void )
{
    xTaskPriorityDisinherit_ExpectAndReturn( NULL, pdFALSE );

    SemaphoreHandle_t xSemaphore = xSemaphoreCreateMutex();

    /* Setup mocks for xSemaphoretake */
    pvTaskIncrementMutexHeldCount_ExpectAndReturn( NULL );
    vFakePortAssertIfInterruptPriorityInvalid_Expect();

    xSemaphoreTake( xSemaphore, 0 );

    TEST_ASSERT_EQUAL( pdTRUE, xSemaphoreGiveFromISR( xSemaphore, NULL ) );

    TEST_ASSERT_EQUAL( B_SEMPHR_AVAILABLE, uxSemaphoreGetCount( xSemaphore ) );

    vSemaphoreDelete( xSemaphore );
}

/**
 * @brief Test xSemaphoreTake in blocking mode on an already owned mutex.
 * @details Test xSemaphoreTake on a mutex owned by another task where the owning task has lower priority.
 * @coverage xQueueSemaphoreTake prvGetDisinheritPriorityAfterTimeout
 */
void test_macro_xSemaphoreTake_blocking_mutex_inherit_timeout( void )
{
    xTaskPriorityDisinherit_ExpectAndReturn( NULL, pdFALSE );

    SemaphoreHandle_t xSemaphore = xSemaphoreCreateMutex();

    BaseType_t xFakeMutexHolder = getNextMonotonicTestValue();

    /* Return a test value from the call to pvTaskIncrementMutexHeldCount */
    pvTaskIncrementMutexHeldCount_ExpectAndReturn( ( void * ) xFakeMutexHolder );

    /* Take the mutex */
    TEST_ASSERT_EQUAL( pdTRUE, xSemaphoreTake( xSemaphore, 0 ) );

    for( int i = 0; i < TICKS_TO_WAIT; i++ )
    {
        /* Return pdTRUE to signify that priority inheritance occurred */
        xTaskPriorityInherit_ExpectAndReturn( ( void * ) xFakeMutexHolder, pdTRUE );
    }

    vTaskPriorityDisinheritAfterTimeout_Expect( ( void * ) ( BaseType_t ) getLastMonotonicTestValue(), tskIDLE_PRIORITY );

    TEST_ASSERT_EQUAL( pdFALSE, xSemaphoreTake( xSemaphore, TICKS_TO_WAIT ) );

    TEST_ASSERT_EQUAL( TICKS_TO_WAIT, td_task_getYieldCount() );

    TEST_ASSERT_EQUAL( TICKS_TO_WAIT, td_task_getCount_vPortYieldWithinAPI() );

    vSemaphoreDelete( xSemaphore );
}

/**
 * @brief Test xSemaphoreTake in blocking mode on an already owned mutex.
 * @details Test xSemaphoreTake on a mutex owned by another task with another high priority task waiting and the current task timing out.
 * @coverage xQueueSemaphoreTake prvGetDisinheritPriorityAfterTimeout
 */
void test_macro_xSemaphoreTake_blocking_mutex_inherit_timeout_high_prio_waiting( void )
{
    xTaskPriorityDisinherit_ExpectAndReturn( NULL, pdFALSE );

    SemaphoreHandle_t xSemaphore = xSemaphoreCreateMutex();

    TaskHandle_t xFakeMutexHolder = ( TaskHandle_t ) ( ( uint64_t ) 0 + getNextMonotonicTestValue() );

    /* Return a test value from the call to pvTaskIncrementMutexHeldCount */
    pvTaskIncrementMutexHeldCount_ExpectAndReturn( xFakeMutexHolder );

    /* Take the mutex */
    TEST_ASSERT_EQUAL( pdTRUE, xSemaphoreTake( xSemaphore, 0 ) );

    /* Insert an item into the event list */
    td_task_setFakeTaskPriority( DEFAULT_PRIORITY + 1 );
    td_task_addFakeTaskWaitingToReceiveFromQueue( xSemaphore );

    for( int i = 0; i < TICKS_TO_WAIT; i++ )
    {
        /* Return pdTRUE to signify that priority inheritance occurred */
        xTaskPriorityInherit_ExpectAndReturn( xFakeMutexHolder, pdTRUE );
    }

    vTaskPriorityDisinheritAfterTimeout_Expect( xFakeMutexHolder, DEFAULT_PRIORITY + 1 );


    TEST_ASSERT_EQUAL( pdFALSE, xSemaphoreTake( xSemaphore, TICKS_TO_WAIT ) );

    TEST_ASSERT_EQUAL( TICKS_TO_WAIT + 1, td_task_getYieldCount() );

    TEST_ASSERT_EQUAL( TICKS_TO_WAIT + 1, td_task_getCount_YieldFromTaskResumeAll() );

    vSemaphoreDelete( xSemaphore );
}

/**
 * @brief Callback for test_macro_xSemaphoreTake_blocking_mutex_inherit_disinherit
 */
static BaseType_t xSemaphoreTake_blocking_xTaskResumeAllStub( int cmock_num_calls )
{
    BaseType_t xReturnValue = td_task_xTaskResumeAllStub( cmock_num_calls );

    if( cmock_num_calls == NUM_CALLS_TO_INTERCEPT )
    {
        TEST_ASSERT_TRUE( xSemaphoreGive( xSemaphoreHandleStatic ) );
    }

    return xReturnValue;
}

/**
 * @brief Test priority inheritance during a successful blocking call to xSemaphoreTake
 * @coverage xQueueSemaphoreTake
 */
void test_macro_xSemaphoreTake_blocking_mutex_inherit_disinherit( void )
{
    xTaskPriorityDisinherit_ExpectAndReturn( NULL, pdFALSE );

    SemaphoreHandle_t xSemaphore = xSemaphoreCreateMutex();

    xSemaphoreHandleStatic = xSemaphore;

    TaskHandle_t xFakeMutexHolder = ( TaskHandle_t ) ( ( uint64_t ) 0 + getNextMonotonicTestValue() );

    xTaskResumeAll_Stub( &xSemaphoreTake_blocking_xTaskResumeAllStub );

    /* Return a test value from the call to pvTaskIncrementMutexHeldCount */
    pvTaskIncrementMutexHeldCount_ExpectAndReturn( xFakeMutexHolder );

    /* Take the mutex */
    TEST_ASSERT_EQUAL( pdTRUE, xSemaphoreTake( xSemaphore, 0 ) );

    for( int i = 0; i < NUM_CALLS_TO_INTERCEPT + 1; i++ )
    {
        /* Return pdTRUE to signify that priority inheritance occurred */
        xTaskPriorityInherit_ExpectAndReturn( xFakeMutexHolder, pdTRUE );
    }

    xTaskPriorityDisinherit_ExpectAndReturn( xFakeMutexHolder, pdTRUE );

    /* Return a test value from the call to pvTaskIncrementMutexHeldCount */
    pvTaskIncrementMutexHeldCount_ExpectAndReturn( xFakeMutexHolder );

    TEST_ASSERT_EQUAL( pdTRUE, xSemaphoreTake( xSemaphore, TICKS_TO_WAIT ) );

    TEST_ASSERT_EQUAL( NUM_CALLS_TO_INTERCEPT + 2, td_task_getYieldCount() );

    TEST_ASSERT_EQUAL( NUM_CALLS_TO_INTERCEPT + 2, td_task_getCount_vPortYieldWithinAPI() );

    vSemaphoreDelete( xSemaphore );
}
