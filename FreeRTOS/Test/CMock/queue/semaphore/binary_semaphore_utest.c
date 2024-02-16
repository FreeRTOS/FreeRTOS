/*
 * FreeRTOS V202212.00
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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
/*! @file binary_semaphore_utest.c */

#include "../queue_utest_common.h"
#include "mock_fake_port.h"

/* Queue includes */
#include "FreeRTOS.h"
#include "FreeRTOSConfig.h"
#include "semphr.h"

/* ===============================  CONSTANTS =============================== */

/* ============================  GLOBAL VARIABLES =========================== */

/* Used to share a semaphore handle between a test case and callback */
static SemaphoreHandle_t xSemaphoreHandleStatic;

/* ==========================  CALLBACK FUNCTIONS =========================== */

/**
 * @brief Callback for vTaskYieldTaskWithinAPI used by tests for yield counts
 *
 * NumCalls is checked in the test assert.
 */
static void vTaskYieldWithinAPI_Callback( int NumCalls )
{
    ( void ) NumCalls;

    portYIELD_WITHIN_API();
}

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
 * @brief Test xSemaphoreTake with a Binary Semaphore
 * @details Create a binary semaphore using xSemaphoreCreateBinary
 * and verify that an immediate call to xSemaphoreTake fails.
 * @coverage xQueueSemaphoreTake
 */
void test_macro_xSemaphoreTake_xSemaphoreCreateBinary_fail( void )
{
    SemaphoreHandle_t xSemaphore = xSemaphoreCreateBinary();

    /* validate returned semaphore handle */
    TEST_ASSERT_NOT_EQUAL( NULL, xSemaphore );

    TEST_ASSERT_EQUAL( QUEUE_T_SIZE, getLastMallocSize() );

    /* Verify that an immediate xSemaphoreTake operation fails */
    TEST_ASSERT_EQUAL( pdFALSE, xSemaphoreTake( xSemaphore, 0 ) );

    vSemaphoreDelete( xSemaphore );
}

/**
 * @brief Test xSemaphoreGive with xSemaphoreCreateBinary
 * @details Create a binary semaphore using xSemaphoreCreateBinary
 * and verify that an immediate call to xSemaphoreGive succeeds.
 * @coverage xQueueGenericSend
 */
void test_macro_xSemaphoreGive_xSemaphoreCreateBinary_success( void )
{
    SemaphoreHandle_t xSemaphore = xSemaphoreCreateBinary();

    /* validate returned semaphore handle */
    TEST_ASSERT_NOT_EQUAL( NULL, xSemaphore );

    TEST_ASSERT_EQUAL( QUEUE_T_SIZE, getLastMallocSize() );

    /* Verify that an immediate xSemaphoreGive operation succeeds */
    TEST_ASSERT_EQUAL( pdTRUE, xSemaphoreGive( xSemaphore ) );

    vSemaphoreDelete( xSemaphore );
}

/**
 * @deprecated
 * @brief Test xSemaphoreTake with vSemaphoreCreateBinary
 * @details Create a semaphore using vSemaphoreCreateBinary and verify that a
 *          subsequent call to xSemaphoreTake succeeds.
 * @coverage xQueueSemaphoreTake
 */
void test_macro_xSemaphoreTake_vSemaphoreCreateBinary_success( void )
{
    SemaphoreHandle_t xSemaphore = NULL;

    vSemaphoreCreateBinary( xSemaphore );

    /* validate returned semaphore handle */
    TEST_ASSERT_NOT_EQUAL( NULL, xSemaphore );
    TEST_ASSERT_EQUAL( QUEUE_T_SIZE, getLastMallocSize() );

    /* Verify that an immediate xSemaphoreTake operation succeeds */
    TEST_ASSERT_EQUAL( pdTRUE, xSemaphoreTake( xSemaphore, 0 ) );

    vSemaphoreDelete( xSemaphore );
}

/**
 * @deprecated
 * @brief Test xSemaphoreGive with vSemaphoreCreateBinary
 * @details Create a semaphore using vSemaphoreCreateBinary and verify that a
 *          subsequent call to xSemaphoreGive fails.
 * @coverage xQueueGenericSend
 */
void test_macro_xSemaphoreGive_vSemaphoreCreateBinary_fail( void )
{
    SemaphoreHandle_t xSemaphore = NULL;

    vSemaphoreCreateBinary( xSemaphore );

    /* validate returned semaphore handle */
    TEST_ASSERT_NOT_EQUAL( NULL, xSemaphore );
    TEST_ASSERT_EQUAL( QUEUE_T_SIZE, getLastMallocSize() );

    /* Verify that an immediate xSemaphoreGive operation fails */
    TEST_ASSERT_EQUAL( pdFALSE, xSemaphoreGive( xSemaphore ) );

    vSemaphoreDelete( xSemaphore );
}

/**
 * @brief Test xSemaphoreGive and xSemaphoreTake with xSemaphoreCreateBinary
 * @details Create a binary semaphore using xSemaphoreCreateBinary
 * and verify that an immediate call to xSemaphoreGive succeeds and a subsequent
 * call to xSemaphoreTake succeeds.
 * @coverage xQueueGenericSend xQueueSemaphoreTake
 */
void test_macro_xSemaphoreGive_xSemaphoreTake_success( void )
{
    SemaphoreHandle_t xSemaphore = xSemaphoreCreateBinary();

    /* validate returned semaphore handle */
    TEST_ASSERT_NOT_EQUAL( NULL, xSemaphore );

    TEST_ASSERT_EQUAL( QUEUE_T_SIZE, getLastMallocSize() );

    /* Verify that an immediate xSemaphoreGive operation succeeds */
    TEST_ASSERT_EQUAL( pdTRUE, xSemaphoreGive( xSemaphore ) );

    /* Verify that a subsequent xSemaphoreTake operation succeeds */
    TEST_ASSERT_EQUAL( pdTRUE, xSemaphoreTake( xSemaphore, 0 ) );

    vSemaphoreDelete( xSemaphore );
}

/**
 * @brief Test xSemaphoreGive multiple times on a Binary Semaphore
 * @details Create a binary semaphore using xSemaphoreCreateBinary
 * and verify that an immediate call to xSemaphoreGive succeeds and a subsequent
 * call to xSemaphoreGive fails.
 * @coverage xQueueGenericSend
 */
void test_macro_xSemaphoreGive_multiple_fail( void )
{
    SemaphoreHandle_t xSemaphore = xSemaphoreCreateBinary();

    /* validate returned semaphore handle */
    TEST_ASSERT_NOT_EQUAL( NULL, xSemaphore );

    TEST_ASSERT_EQUAL( QUEUE_T_SIZE, getLastMallocSize() );

    /* Verify that an immediate xSemaphoreGive operation succeeds */
    TEST_ASSERT_EQUAL( pdTRUE, xSemaphoreGive( xSemaphore ) );

    /* Verify that the second xSemaphoreGive operation fails */
    TEST_ASSERT_EQUAL( pdFALSE, xSemaphoreGive( xSemaphore ) );

    vSemaphoreDelete( xSemaphore );
}

/**
 * @brief Test xSemaphoreTake multiple times on a Binary Semaphore
 * @details Create a binary semaphore using xSemaphoreCreateBinary,
 * verify that an immediate call to xSemaphoreGive succeeds, a subsequent
 * call to xSemaphoreTake succeeds, but a second call to xSemaphoreTake fails.
 * @coverage xQueueSemaphoreTake
 */
void test_macro_xSemaphoreTake_multiple_fail( void )
{
    SemaphoreHandle_t xSemaphore = xSemaphoreCreateBinary();

    /* validate returned semaphore handle */
    TEST_ASSERT_NOT_EQUAL( NULL, xSemaphore );

    TEST_ASSERT_EQUAL( QUEUE_T_SIZE, getLastMallocSize() );

    /* Verify that an immediate xSemaphoreGive operation succeeds */
    TEST_ASSERT_EQUAL( pdTRUE, xSemaphoreGive( xSemaphore ) );

    /* Verify that a subsequent xSemaphoreTake operation succeeds */
    TEST_ASSERT_EQUAL( pdTRUE, xSemaphoreTake( xSemaphore, 0 ) );

    /* Verify that a second xSemaphoreTake operation fails */
    TEST_ASSERT_EQUAL( pdFALSE, xSemaphoreTake( xSemaphore, 0 ) );

    vSemaphoreDelete( xSemaphore );
}

/**
 * @brief Test uxSemaphoreGetCount with a Binary Semaphore
 * @details Create a binary semaphore using vSemaphoreCreateBinary.
 *  validate the return value of uxSemaphoreGetCount(),
 *  call xSemaphoreTake() and validate the return value of uxSemaphoreGetCount()
 * @coverage uxQueueMessagesWaiting
 */
void test_macro_uxSemaphoreGetCount( void )
{
    SemaphoreHandle_t xSemaphore = NULL;

    vSemaphoreCreateBinary( xSemaphore );

    TEST_ASSERT_EQUAL( B_SEMPHR_AVAILABLE, uxSemaphoreGetCount( xSemaphore ) );

    ( void ) xSemaphoreTake( xSemaphore, 0 );

    TEST_ASSERT_EQUAL( B_SEMPHR_TAKEN, uxSemaphoreGetCount( xSemaphore ) );

    vSemaphoreDelete( xSemaphore );
}

/**
 * @brief Test xSemaphoreTakeFromISR with a Binary Semaphore
 * @coverage xQueueReceiveFromISR
 **/
void test_macro_xSemaphoreTakeFromISR_success( void )
{
    SemaphoreHandle_t xSemaphore = xSemaphoreCreateBinary();

    vFakePortAssertIfInterruptPriorityInvalid_Expect();

    /* Give the Binary Semaphore */
    ( void ) xSemaphoreGive( xSemaphore );

    TEST_ASSERT_EQUAL( B_SEMPHR_AVAILABLE, uxSemaphoreGetCount( xSemaphore ) );

    TEST_ASSERT_EQUAL( pdTRUE, xSemaphoreTakeFromISR( xSemaphore, NULL ) );

    TEST_ASSERT_EQUAL( B_SEMPHR_TAKEN, uxSemaphoreGetCount( xSemaphore ) );

    vSemaphoreDelete( xSemaphore );
}

/**
 * @brief xSemaphoreGiveFromISR with an empty queue
 * @coverage xQueueGiveFromISR
 */
void test_macro_xSemaphoreGiveFromISR_success( void )
{
    SemaphoreHandle_t xSemaphore = xSemaphoreCreateBinary();

    vFakePortAssertIfInterruptPriorityInvalid_Expect();

    TEST_ASSERT_EQUAL( pdTRUE, xSemaphoreGiveFromISR( xSemaphore, NULL ) );

    TEST_ASSERT_EQUAL( B_SEMPHR_AVAILABLE, uxSemaphoreGetCount( xSemaphore ) );

    vSemaphoreDelete( xSemaphore );
}

/*!
 * @brief xSemaphoreGiveFromISR with a full queue
 * @coverage xQueueGiveFromISR
 */
void test_macro_xSemaphoreGiveFromISR_fail( void )
{
    SemaphoreHandle_t xSemaphore = xSemaphoreCreateBinary();

    vFakePortAssertIfInterruptPriorityInvalid_Expect();
    TEST_ASSERT_EQUAL( pdTRUE, xSemaphoreGiveFromISR( xSemaphore, NULL ) );

    vFakePortAssertIfInterruptPriorityInvalid_Expect();
    TEST_ASSERT_EQUAL( errQUEUE_FULL, xSemaphoreGiveFromISR( xSemaphore, NULL ) );

    TEST_ASSERT_EQUAL( pdTRUE, xSemaphoreTake( xSemaphore, 0 ) );

    vSemaphoreDelete( xSemaphore );
}

/**
 * @brief Test xSemaphoreGiveFromISR with a higher priority task waiting and a null pointer for pxHigherPriorityTaskWoken
 * @details Test xSemaphoreGiveFromISR with a higher priority task waiting and
 *  verifies that a null pxHigherPriorityTaskWoken is handled correctly.
 * @coverage xQueueGiveFromISR
 */
void test_macro_xSemaphoreGiveFromISR_high_priority_pending_null_ptr( void )
{
    SemaphoreHandle_t xSemaphore = xSemaphoreCreateBinary();

    vFakePortAssertIfInterruptPriorityInvalid_Expect();

    /* Insert an item into the event list */
    td_task_setFakeTaskPriority( DEFAULT_PRIORITY + 1 );
    td_task_addFakeTaskWaitingToReceiveFromQueue( xSemaphore );

    /* Give the Binary Semaphore */
    TEST_ASSERT_EQUAL( pdTRUE, xSemaphoreGiveFromISR( xSemaphore, NULL ) );

    TEST_ASSERT_EQUAL( pdTRUE, td_task_getYieldPending() );

    TEST_ASSERT_EQUAL( B_SEMPHR_AVAILABLE, uxSemaphoreGetCount( xSemaphore ) );

    vSemaphoreDelete( xSemaphore );
}

/**
 * @brief Test xSemaphoreGiveFromISR with a higher priority task waiting
 * @details Test xSemaphoreGiveFromISR with a higher priority task waiting and
 *  verify that xHigherPriorityTaskWoken is set accordingly.
 * @coverage xQueueGiveFromISR
 */
void test_macro_xSemaphoreGiveFromISR_high_priority_pending( void )
{
    SemaphoreHandle_t xSemaphore = xSemaphoreCreateBinary();

    vFakePortAssertIfInterruptPriorityInvalid_Expect();

    /* Insert an item into the event list */
    td_task_setFakeTaskPriority( DEFAULT_PRIORITY + 1 );
    td_task_addFakeTaskWaitingToReceiveFromQueue( xSemaphore );

    BaseType_t xHigherPriorityTaskWoken = pdFALSE;

    /* Give the semaphore */
    TEST_ASSERT_EQUAL( pdTRUE, xSemaphoreGiveFromISR( xSemaphore, &xHigherPriorityTaskWoken ) );

    TEST_ASSERT_EQUAL( pdTRUE, xHigherPriorityTaskWoken );

    TEST_ASSERT_EQUAL( pdTRUE, td_task_getYieldPending() );

    TEST_ASSERT_EQUAL( B_SEMPHR_AVAILABLE, uxSemaphoreGetCount( xSemaphore ) );

    vSemaphoreDelete( xSemaphore );
}

/**
 * @brief Test xSemaphoreGiveFromISR with a lower priority task waiting
 * @details Test xSemaphoreGiveFromISR with a lower priority task waiting and
 *  verify that xHigherPriorityTaskWoken is not modified.
 * @coverage xQueueGiveFromISR
 */
void test_macro_xSemaphoreGiveFromISR_low_priority_pending( void )
{
    SemaphoreHandle_t xSemaphore = xSemaphoreCreateBinary();

    vFakePortAssertIfInterruptPriorityInvalid_Expect();

    /* Insert an item into the event list */
    td_task_setFakeTaskPriority( DEFAULT_PRIORITY - 1 );
    td_task_addFakeTaskWaitingToReceiveFromQueue( xSemaphore );

    BaseType_t xHigherPriorityTaskWoken = pdFALSE;

    /* Give the semaphore */
    TEST_ASSERT_EQUAL( pdTRUE, xSemaphoreGiveFromISR( xSemaphore, &xHigherPriorityTaskWoken ) );

    TEST_ASSERT_EQUAL( pdFALSE, xHigherPriorityTaskWoken );

    TEST_ASSERT_EQUAL( pdFALSE, td_task_getYieldPending() );

    TEST_ASSERT_EQUAL( B_SEMPHR_AVAILABLE, uxSemaphoreGetCount( xSemaphore ) );

    vSemaphoreDelete( xSemaphore );
}

/**
 * @brief Test xSemaphoreGiveFromISR with no tasks waiting
 * @details Test xSemaphoreGiveFromISR with no tasks waiting and verify that xHigherPriorityTaskWoken is not modified.
 * @coverage xQueueGiveFromISR
 */
void test_macro_xSemaphoreGiveFromISR_no_pending( void )
{
    SemaphoreHandle_t xSemaphore = xSemaphoreCreateBinary();

    vFakePortAssertIfInterruptPriorityInvalid_Expect();

    BaseType_t xHigherPriorityTaskWoken = pdFALSE;

    /* Give the semaphore */
    TEST_ASSERT_EQUAL( pdTRUE, xSemaphoreGiveFromISR( xSemaphore, &xHigherPriorityTaskWoken ) );

    TEST_ASSERT_EQUAL( pdFALSE, xHigherPriorityTaskWoken );

    TEST_ASSERT_EQUAL( pdFALSE, td_task_getYieldPending() );

    TEST_ASSERT_EQUAL( B_SEMPHR_AVAILABLE, uxSemaphoreGetCount( xSemaphore ) );

    vSemaphoreDelete( xSemaphore );
}

/**
 * @brief Test xSemaphoreGiveFromISR on a semaphore that is locked
 * @coverage xQueueGiveFromISR
 */
void test_xSemaphoreGiveFromISR_locked( void )
{
    SemaphoreHandle_t xSemaphore = xSemaphoreCreateBinary();

    /* Set private lock counters */
    vSetQueueRxLock( xSemaphore, queueLOCKED_UNMODIFIED );
    vSetQueueTxLock( xSemaphore, queueLOCKED_UNMODIFIED );

    vFakePortAssertIfInterruptPriorityInvalid_Expect();
    uxTaskGetNumberOfTasks_IgnoreAndReturn( 1 );

    TEST_ASSERT_EQUAL( pdTRUE, xSemaphoreGiveFromISR( xSemaphore, NULL ) );

    /* Verify that the cRxLock counter has not changed */
    TEST_ASSERT_EQUAL( queueLOCKED_UNMODIFIED, cGetQueueRxLock( xSemaphore ) );

    /* Verify that the cTxLock counter has been incremented */
    TEST_ASSERT_EQUAL( queueLOCKED_UNMODIFIED + 1, cGetQueueTxLock( xSemaphore ) );

    TEST_ASSERT_EQUAL( B_SEMPHR_AVAILABLE, uxSemaphoreGetCount( xSemaphore ) );

    vSemaphoreDelete( xSemaphore );
}

/**
 * @brief Test xSemaphoreGiveFromISR on a semaphore that is locked and cRxLock overflows.
 * @coverage xQueueGiveFromISR
 */
void test_xSemaphoreGiveFromISR_locked_overflow( void )
{
    SemaphoreHandle_t xSemaphore = xSemaphoreCreateBinary();

    /* Set private lock counters */
    vSetQueueRxLock( xSemaphore, INT8_MAX );
    vSetQueueTxLock( xSemaphore, INT8_MAX );

    vFakePortAssertIfInterruptPriorityInvalid_Expect();

    /* The number of tasks need to be more than 127 to trigger the
     * overflow assertion. */
    uxTaskGetNumberOfTasks_IgnoreAndReturn( 128 );


    /* Expect an assertion since the cTxLock value has overflowed */
    fakeAssertExpectFail();

    TEST_ASSERT_EQUAL( pdTRUE, xSemaphoreGiveFromISR( xSemaphore, NULL ) );

    /* Verify that the cRxLock counter has not changed */
    TEST_ASSERT_EQUAL( INT8_MAX, cGetQueueRxLock( xSemaphore ) );

    /* Verify that the cTxLock counter has been incremented */
    TEST_ASSERT_EQUAL( INT8_MIN, cGetQueueTxLock( xSemaphore ) );

    TEST_ASSERT_EQUAL( true, fakeAssertGetFlagAndClear() );

    TEST_ASSERT_EQUAL( B_SEMPHR_AVAILABLE, uxSemaphoreGetCount( xSemaphore ) );

    vSemaphoreDelete( xSemaphore );
}

/**
 * @brief Test xSemaphoreTake with an occupied semaphore with higher priority tasks waiting
 * @coverage xQueueSemaphoreTake
 */
void test_xSemaphoreTake_tasks_waiting_higher_priority( void )
{
    /* Create a new binary semaphore */
    SemaphoreHandle_t xSemaphore = xSemaphoreCreateBinary();

    ( void ) xSemaphoreGive( xSemaphore );

    vTaskYieldWithinAPI_Stub( vTaskYieldWithinAPI_Callback );

    /* Insert an item into the event list */
    td_task_setFakeTaskPriority( DEFAULT_PRIORITY + 1 );
    td_task_addFakeTaskWaitingToSendToQueue( xSemaphore );

    /* take the semaphore */
    TEST_ASSERT_EQUAL( pdTRUE, xSemaphoreTake( xSemaphore, 0 ) );

    TEST_ASSERT_EQUAL( 1, td_task_getYieldCount() );

    TEST_ASSERT_EQUAL( 1, td_task_getCount_vPortYieldWithinAPI() );

    TEST_ASSERT_EQUAL( B_SEMPHR_TAKEN, uxSemaphoreGetCount( xSemaphore ) );

    vSemaphoreDelete( xSemaphore );
}

/**
 * @brief Test xSemaphoreTake with an occupied semaphore with an equal priority task waiting
 * @coverage xQueueSemaphoreTake
 */
void test_xSemaphoreTake_tasks_waiting_equal_priority( void )
{
    /* Create a new binary semaphore */
    SemaphoreHandle_t xSemaphore = xSemaphoreCreateBinary();

    ( void ) xSemaphoreGive( xSemaphore );

    /* Insert an item into the event list */
    td_task_setFakeTaskPriority( DEFAULT_PRIORITY );
    td_task_addFakeTaskWaitingToSendToQueue( xSemaphore );

    /* take the semaphore */
    TEST_ASSERT_EQUAL( pdTRUE, xSemaphoreTake( xSemaphore, 0 ) );

    TEST_ASSERT_EQUAL( 0, td_task_getYieldCount() );

    TEST_ASSERT_EQUAL( 0, td_task_getCount_vPortYieldWithinAPI() );

    TEST_ASSERT_EQUAL( B_SEMPHR_TAKEN, uxSemaphoreGetCount( xSemaphore ) );

    vSemaphoreDelete( xSemaphore );
}

/**
 * @brief Test xSemaphoreTake with an occupied semaphore with lower priority tasks waiting.
 * @coverage xQueueSemaphoreTake
 */
void test_xSemaphoreTake_tasks_waiting_lower_priority( void )
{
    /* Create a new binary semaphore */
    SemaphoreHandle_t xSemaphore = xSemaphoreCreateBinary();

    ( void ) xSemaphoreGive( xSemaphore );

    /* Insert an item into the event list */
    td_task_setFakeTaskPriority( DEFAULT_PRIORITY - 1 );
    td_task_addFakeTaskWaitingToSendToQueue( xSemaphore );

    /* take the semaphore */
    TEST_ASSERT_EQUAL( pdTRUE, xSemaphoreTake( xSemaphore, 0 ) );

    TEST_ASSERT_EQUAL( 0, td_task_getYieldCount() );

    TEST_ASSERT_EQUAL( 0, td_task_getCount_vPortYieldWithinAPI() );

    TEST_ASSERT_EQUAL( B_SEMPHR_TAKEN, uxSemaphoreGetCount( xSemaphore ) );

    vSemaphoreDelete( xSemaphore );
}

/**
 *  @brief Test xSemaphoreTake with taskSCHEDULER_SUSPENDED and timeout=10
 *  @details This should cause xSemaphoreTake to configASSERT because it would
 *  block forever when the semaphore is empty.
 *  @coverage xQueueSemaphoreTake
 */
void test_xSemaphoreTake_blocking_suspended_assert( void )
{
    SemaphoreHandle_t xSemaphore = xSemaphoreCreateBinary();

    fakeAssertExpectFail();
    vTaskYieldWithinAPI_Stub( vTaskYieldWithinAPI_Callback );

    vTaskSuspendAll_Stub( td_task_vTaskSuspendAllStubNoCheck );

    td_task_setSchedulerState( taskSCHEDULER_SUSPENDED );

    TEST_ASSERT_EQUAL( pdFALSE, xSemaphoreTake( xSemaphore, TICKS_TO_WAIT ) );

    TEST_ASSERT_EQUAL( TICKS_TO_WAIT, td_task_getYieldCount() );

    TEST_ASSERT_EQUAL( TICKS_TO_WAIT, td_task_getCount_vPortYieldWithinAPI() );

    TEST_ASSERT_EQUAL( pdTRUE, fakeAssertGetFlagAndClear() );

    td_task_setSchedulerState( taskSCHEDULER_RUNNING );

    vSemaphoreDelete( xSemaphore );
}

/**
 *  @brief Test xSemaphoreTake with taskSCHEDULER_SUSPENDED and timeout=0
 *  @details This should not cause xSemaphoreTake to configASSERT because
 *  xSemaphoreTake is non-blocking when timeout=0.
 *  @coverage xQueueSemaphoreTake
 */
void test_xSemaphoreTake_nonblocking_suspended_noassert( void )
{
    SemaphoreHandle_t xSemaphore = xSemaphoreCreateBinary();

    td_task_setSchedulerState( taskSCHEDULER_SUSPENDED );

    TEST_ASSERT_EQUAL( pdFALSE, xSemaphoreTake( xSemaphore, 0 ) );

    td_task_setSchedulerState( taskSCHEDULER_RUNNING );

    vSemaphoreDelete( xSemaphore );
}

/**
 *  @brief Callback which calls xSemaphoreGive on xSemaphoreHandleStatic
 */
static BaseType_t blocking_success_xTaskCheckForTimeOut_cb( TimeOut_t * const pxTimeOut,
                                                            TickType_t * const pxTicksToWait,
                                                            int cmock_num_calls )
{
    BaseType_t xReturnValue = td_task_xTaskCheckForTimeOutStub( pxTimeOut, pxTicksToWait, cmock_num_calls );

    if( cmock_num_calls == NUM_CALLS_TO_INTERCEPT )
    {
        ( void ) xSemaphoreGiveFromISR( xSemaphoreHandleStatic, NULL );
    }

    return xReturnValue;
}

/**
 * @brief Test xSemaphoreTake in blocking mode with a taken Binary Semaphore
 * which becomes available while a call to xSemaphoreTake is blocking.
 * @coverage xQueueSemaphoreTake
 */
void test_xSemaphoreTake_blocking_success( void )
{
    SemaphoreHandle_t xSemaphore = xSemaphoreCreateBinary();

    /* Export for blocking_success_xTaskCheckForTimeOut_cb callback */
    xSemaphoreHandleStatic = xSemaphore;

    vFakePortAssertIfInterruptPriorityInvalid_Ignore();
    vTaskYieldWithinAPI_Stub( vTaskYieldWithinAPI_Callback );

    xTaskCheckForTimeOut_Stub( &blocking_success_xTaskCheckForTimeOut_cb );
    uxTaskGetNumberOfTasks_IgnoreAndReturn( 1 );


    TEST_ASSERT_EQUAL( pdTRUE, xSemaphoreTake( xSemaphore, TICKS_TO_WAIT ) );

    TEST_ASSERT_EQUAL( NUM_CALLS_TO_INTERCEPT, td_task_getYieldCount() );

    TEST_ASSERT_EQUAL( NUM_CALLS_TO_INTERCEPT, td_task_getCount_vPortYieldWithinAPI() );

    TEST_ASSERT_EQUAL( B_SEMPHR_TAKEN, uxSemaphoreGetCount( xSemaphore ) );
    vSemaphoreDelete( xSemaphore );
}

/**
 *  @brief Callback which calls xSemaphoreGive on xSemaphoreHandleStatic when
 *  cmock_num_calls == TICKS_TO_WAIT
 */
static BaseType_t blocking_last_chance_xTaskCheckForTimeOut_cb( TimeOut_t * const pxTimeOut,
                                                                TickType_t * const pxTicksToWait,
                                                                int cmock_num_calls )
{
    BaseType_t xReturnValue = td_task_xTaskCheckForTimeOutStub( pxTimeOut, pxTicksToWait, cmock_num_calls );

    if( cmock_num_calls == TICKS_TO_WAIT )
    {
        ( void ) xSemaphoreGiveFromISR( xSemaphoreHandleStatic, NULL );
        return pdTRUE;
    }

    return xReturnValue;
}

/**
 * @brief Test xSemaphoreTake in blocking mode with a Binary Semaphore that is initially taken,
 * but becomes available at the end of the blocking time period.
 * @coverage xQueueSemaphoreTake
 */
void test_xSemaphoreTake_blocking_success_last_chance( void )
{
    SemaphoreHandle_t xSemaphore = xSemaphoreCreateBinary();

    /* Export for blocking_success_xTaskCheckForTimeOut_cb callback */
    xSemaphoreHandleStatic = xSemaphore;

    vFakePortAssertIfInterruptPriorityInvalid_Expect();
    vTaskYieldWithinAPI_Stub( vTaskYieldWithinAPI_Callback );

    xTaskCheckForTimeOut_Stub( &blocking_last_chance_xTaskCheckForTimeOut_cb );
    uxTaskGetNumberOfTasks_IgnoreAndReturn( 1 );

    TEST_ASSERT_EQUAL( pdTRUE, xSemaphoreTake( xSemaphore, TICKS_TO_WAIT ) );

    TEST_ASSERT_EQUAL( TICKS_TO_WAIT, td_task_getYieldCount() );

    TEST_ASSERT_EQUAL( TICKS_TO_WAIT, td_task_getCount_vPortYieldWithinAPI() );

    TEST_ASSERT_EQUAL( B_SEMPHR_TAKEN, uxSemaphoreGetCount( xSemaphore ) );
    vSemaphoreDelete( xSemaphore );
}

/**
 * @brief Test xSemaphoreTake in blocking mode with a taken binary semaphore
 * @coverage xQueueSemaphoreTake
 */
void test_xSemaphoreTake_blocking_timeout( void )
{
    SemaphoreHandle_t xSemaphore = xSemaphoreCreateBinary();

    vTaskYieldWithinAPI_Stub( vTaskYieldWithinAPI_Callback );

    TEST_ASSERT_EQUAL( pdFALSE, xSemaphoreTake( xSemaphore, TICKS_TO_WAIT ) );

    TEST_ASSERT_EQUAL( TICKS_TO_WAIT, td_task_getYieldCount() );

    TEST_ASSERT_EQUAL( TICKS_TO_WAIT, td_task_getCount_vPortYieldWithinAPI() );

    vSemaphoreDelete( xSemaphore );
}

/**
 * @brief Test xSemaphoreTake in blocking mode with a taken locked semaphore
 * @details This test case verifies a situation that should never occur
 * ( xSemaphoreTake called on a locked semaphore ).
 * @coverage xQueueSemaphoreTake
 */
void test_xSemaphoreTake_blocking_locked( void )
{
    /* Create a new binary semaphore */
    SemaphoreHandle_t xSemaphore = xSemaphoreCreateBinary();

    vTaskYieldWithinAPI_Stub( vTaskYieldWithinAPI_Callback );

    /* Set private lock counters */
    vSetQueueRxLock( xSemaphore, queueLOCKED_UNMODIFIED );
    vSetQueueTxLock( xSemaphore, queueLOCKED_UNMODIFIED );

    /* Run xSemaphoreTake in blocking mode with the semaphore locked */
    TEST_ASSERT_EQUAL( pdFALSE, xSemaphoreTake( xSemaphore, TICKS_TO_WAIT ) );

    TEST_ASSERT_EQUAL( TICKS_TO_WAIT, td_task_getYieldCount() );

    TEST_ASSERT_EQUAL( TICKS_TO_WAIT, td_task_getCount_vPortYieldWithinAPI() );

    /* Verify that the semaphore is now unlocked */
    TEST_ASSERT_EQUAL( queueUNLOCKED, cGetQueueRxLock( xSemaphore ) );
    TEST_ASSERT_EQUAL( queueUNLOCKED, cGetQueueTxLock( xSemaphore ) );

    vSemaphoreDelete( xSemaphore );
}

/**
 *  @brief Callback for test_xSemaphoreTake_blocking_success_locked_no_pending
 *  which adds an item to it's test queue.
 */
static BaseType_t xSemaphoreTake_xTaskCheckForTimeOutCB( TimeOut_t * const pxTimeOut,
                                                         TickType_t * const pxTicksToWait,
                                                         int cmock_num_calls )
{
    BaseType_t xReturnValue = td_task_xTaskCheckForTimeOutStub( pxTimeOut, pxTicksToWait, cmock_num_calls );

    if( cmock_num_calls == NUM_CALLS_TO_INTERCEPT )
    {
        uxTaskGetNumberOfTasks_IgnoreAndReturn( 1 );
        TEST_ASSERT_TRUE( xSemaphoreGiveFromISR( xSemaphoreHandleStatic, NULL ) );
        TEST_ASSERT_EQUAL( 1, uxQueueMessagesWaiting( xSemaphoreHandleStatic ) );
    }

    return xReturnValue;
}

/**
 *  @brief Test a blocking call to xSemaphoreTake with a locked binary semaphore.
 *  @details Test a blocking call to xSemaphoreTake with a locked binary semaphore with no
 *  tasks in the binary semaphore WaitingToReceiveFrom event list.
 *  @coverage xQueueSemaphoreTake prvUnlockQueue
 */
void test_xSemaphoreTake_blocking_success_locked_no_pending( void )
{
    SemaphoreHandle_t xSemaphore = xSemaphoreCreateBinary();

    vFakePortAssertIfInterruptPriorityInvalid_Ignore();
    vTaskYieldWithinAPI_Stub( vTaskYieldWithinAPI_Callback );

    /* Export for callbacks */
    xSemaphoreHandleStatic = xSemaphore;

    xTaskCheckForTimeOut_Stub( &xSemaphoreTake_xTaskCheckForTimeOutCB );
    xTaskResumeAll_Stub( &td_task_xTaskResumeAllStub );
    uxTaskGetNumberOfTasks_IgnoreAndReturn( 1 );

    TEST_ASSERT_EQUAL( pdTRUE, xSemaphoreTake( xSemaphore, TICKS_TO_WAIT ) );

    TEST_ASSERT_EQUAL( 0, uxSemaphoreGetCount( xSemaphore ) );

    TEST_ASSERT_EQUAL( NUM_CALLS_TO_INTERCEPT, td_task_getYieldCount() );

    TEST_ASSERT_EQUAL( NUM_CALLS_TO_INTERCEPT, td_task_getCount_vPortYieldWithinAPI() );

    vQueueDelete( xSemaphore );
}


/**
 * @brief Callback for xTaskResumeAll used by tests for blocking calls to
 * xSemaphoreTake
 */
static BaseType_t xSemaphoreTake_xTaskResumeAllCallback( int cmock_num_calls )
{
    BaseType_t xReturnValue = td_task_xTaskResumeAllStub( cmock_num_calls );

    /* If td_task_xTaskResumeAllStub returns pdTRUE, a higher priority task is pending
     * Receive from an ISR to block */
    if( pdTRUE == xReturnValue )
    {
        if( cmock_num_calls == NUM_CALLS_TO_INTERCEPT )
        {
            TEST_ASSERT_EQUAL( 1, uxSemaphoreGetCount( xSemaphoreHandleStatic ) );
            TEST_ASSERT_TRUE( xSemaphoreTakeFromISR( xSemaphoreHandleStatic, NULL ) );
        }
    }

    return xReturnValue;
}

/**
 *  @brief Test a blocking call to xSemaphoreTake with a locked binary semaphore.
 *  @details Test a blocking call to xSemaphoreTake with a locked binary semaphore with a
 *  higher priority task in the binary semaphore WaitingToReceiveFrom event list.
 *  @coverage xQueueSemaphoreTake prvUnlockQueue
 */
void test_xSemaphoreTake_blocking_timeout_locked_high_prio_pending( void )
{
    SemaphoreHandle_t xSemaphore = xSemaphoreCreateBinary();

    vFakePortAssertIfInterruptPriorityInvalid_Ignore();
    vTaskYieldWithinAPI_Stub( vTaskYieldWithinAPI_Callback );

    /* Export for callbacks */
    xSemaphoreHandleStatic = xSemaphore;

    xTaskCheckForTimeOut_Stub( &xSemaphoreTake_xTaskCheckForTimeOutCB );
    xTaskResumeAll_Stub( &xSemaphoreTake_xTaskResumeAllCallback );
    uxTaskGetNumberOfTasks_IgnoreAndReturn( 1 );

    td_task_setFakeTaskPriority( DEFAULT_PRIORITY + 1 );

    td_task_addFakeTaskWaitingToReceiveFromQueue( xSemaphore );

    TEST_ASSERT_EQUAL( pdFALSE, xSemaphoreTake( xSemaphore, TICKS_TO_WAIT ) );

    TEST_ASSERT_EQUAL( 0, uxSemaphoreGetCount( xSemaphore ) );

    TEST_ASSERT_EQUAL( TICKS_TO_WAIT, td_task_getYieldCount() );

    TEST_ASSERT_EQUAL( NUM_CALLS_TO_INTERCEPT + 1, td_task_getCount_YieldFromTaskResumeAll() );

    TEST_ASSERT_EQUAL( NUM_CALLS_TO_INTERCEPT - 1, td_task_getCount_vPortYieldWithinAPI() );

    TEST_ASSERT_EQUAL( 1, td_task_getCount_vTaskMissedYield() );

    vQueueDelete( xSemaphore );
}

/**
 *  @brief Test a blocking call to xSemaphoreTake with a locked binary semaphore.
 *  @details Test a blocking call to xSemaphoreTake with a locked binary semaphore with a
 *  lower priority task in the semaphore WaitingToReceiveFrom event list.
 *  @coverage xQueueSemaphoreTake prvUnlockQueue
 */
void test_xSemaphoreTake_blocking_success_locked_low_prio_pending( void )
{
    SemaphoreHandle_t xSemaphore = xSemaphoreCreateBinary();

    vFakePortAssertIfInterruptPriorityInvalid_Ignore();
    vTaskYieldWithinAPI_Stub( vTaskYieldWithinAPI_Callback );

    /* Export for callbacks */
    xSemaphoreHandleStatic = xSemaphore;

    xTaskCheckForTimeOut_Stub( &xSemaphoreTake_xTaskCheckForTimeOutCB );
    xTaskResumeAll_Stub( &xSemaphoreTake_xTaskResumeAllCallback );

    td_task_setFakeTaskPriority( DEFAULT_PRIORITY - 1 );

    td_task_addFakeTaskWaitingToReceiveFromQueue( xSemaphore );

    TEST_ASSERT_EQUAL( pdTRUE, xSemaphoreTake( xSemaphore, TICKS_TO_WAIT ) );

    TEST_ASSERT_EQUAL( 0, uxSemaphoreGetCount( xSemaphore ) );

    TEST_ASSERT_EQUAL( NUM_CALLS_TO_INTERCEPT, td_task_getYieldCount() );

    TEST_ASSERT_EQUAL( NUM_CALLS_TO_INTERCEPT, td_task_getCount_vPortYieldWithinAPI() );

    vQueueDelete( xSemaphore );
}
