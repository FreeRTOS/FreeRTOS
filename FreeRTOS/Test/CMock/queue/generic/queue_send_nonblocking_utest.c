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
/*! @file queue_send_nonblocking_utest.c */

/* C runtime includes. */
#include <stdlib.h>
#include <stdbool.h>
#include <string.h>

#include "../queue_utest_common.h"

/* Queue includes */
#include "FreeRTOS.h"
#include "FreeRTOSConfig.h"
#include "queue.h"
#include "mock_fake_port.h"

/* ===============================  CONSTANTS =============================== */

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
 * @brief Test xQueueSend with an invalid QueueHandle
 * @coverage xQueueGenericSend
 */
void test_macro_xQueueSend_invalid_handle( void )
{
    EXPECT_ASSERT_BREAK( xQueueSend( NULL, NULL, 0 ) );
}

/**
 * @brief xQueueSend with an empty queue
 * @coverage xQueueGenericSend
 */
void test_macro_xQueueSend_success( void )
{
    QueueHandle_t xQueue = xQueueCreate( 1, sizeof( uint32_t ) );

    uint32_t testval = getNextMonotonicTestValue();

    TEST_ASSERT_EQUAL( 0, uxQueueMessagesWaiting( xQueue ) );

    TEST_ASSERT_EQUAL( pdTRUE, xQueueSend( xQueue, &testval, 0 ) );

    TEST_ASSERT_EQUAL( 1, uxQueueMessagesWaiting( xQueue ) );

    uint32_t checkVal = INVALID_UINT32;

    TEST_ASSERT_EQUAL( pdTRUE, xQueueReceive( xQueue, &checkVal, 0 ) );

    TEST_ASSERT_EQUAL( testval, checkVal );

    vQueueDelete( xQueue );
}

/*!
 * @brief xQueueSend with a full queue
 * @details verify that the correct value is returned after a failed send operation.
 * @coverage xQueueGenericSend
 */
void test_macro_xQueueSend_fail_full( void )
{
    QueueHandle_t xQueue = xQueueCreate( 1, sizeof( uint32_t ) );

    uint32_t testVal1 = getNextMonotonicTestValue();

    TEST_ASSERT_EQUAL( 0, uxQueueMessagesWaiting( xQueue ) );

    TEST_ASSERT_EQUAL( pdTRUE, xQueueSend( xQueue, &testVal1, 0 ) );

    TEST_ASSERT_EQUAL( 1, uxQueueMessagesWaiting( xQueue ) );

    uint32_t testVal2 = getNextMonotonicTestValue();

    TEST_ASSERT_EQUAL( errQUEUE_FULL, xQueueSend( xQueue, &testVal2, 0 ) );

    uint32_t checkVal = INVALID_UINT32;

    TEST_ASSERT_EQUAL( pdTRUE, xQueueReceive( xQueue, &checkVal, 0 ) );
    TEST_ASSERT_EQUAL( testVal1, checkVal );

    vQueueDelete( xQueue );
}

/**
 * @brief Test xQueueSend with uxQueueLength=1, uxItemSize=0
 * @details xQueueSend should return pdTRUE because the queue is empty.
 *  This queue is eqivalent to a binary semaphore.
 * @coverage xQueueGenericSend
 */
void test_macro_xQueueSend_oneQueueLength_zeroItemSize( void )
{
    QueueHandle_t xQueue = xQueueCreate( 1, 0 );

    uint8_t testVal = getNextMonotonicTestValue();

    TEST_ASSERT_EQUAL( 0, uxQueueMessagesWaiting( xQueue ) );

    TEST_ASSERT_EQUAL( pdTRUE, xQueueSend( xQueue, &testVal, 0 ) );

    TEST_ASSERT_EQUAL( 1, uxQueueMessagesWaiting( xQueue ) );

    vQueueDelete( xQueue );
}

/**
 * @brief Test xQueueSend with uxQueueLength=1, uxItemSize=0 and null item.
 * @details xQueueSend should return pdTRUE because the queue is empty.
 *  This queue is eqivalent to a binary semaphore.
 * @coverage xQueueGenericSend
 */
void test_macro_xQueueSend_oneQueueLength_zeroItemSize_null( void )
{
    QueueHandle_t xQueue = xQueueCreate( 1, 0 );

    TEST_ASSERT_EQUAL( 0, uxQueueMessagesWaiting( xQueue ) );

    TEST_ASSERT_EQUAL( pdTRUE, xQueueSend( xQueue, NULL, 0 ) );

    TEST_ASSERT_EQUAL( 1, uxQueueMessagesWaiting( xQueue ) );

    vQueueDelete( xQueue );
}

/**
 * @brief Test xQueueSend with uxQueueLength=1, uxItemSize=1
 * @details xQueueSend should return pdTRUE because the queue is empty.
 * @coverage xQueueGenericSend
 */
void test_macro_xQueueSend_oneQueueLength_oneItemSize( void )
{
    QueueHandle_t xQueue = xQueueCreate( 1, 1 );

    uint8_t testVal = getNextMonotonicTestValue();

    TEST_ASSERT_EQUAL( 0, uxQueueMessagesWaiting( xQueue ) );

    TEST_ASSERT_EQUAL( pdTRUE, xQueueSend( xQueue, &testVal, 0 ) );

    TEST_ASSERT_EQUAL( 1, uxQueueMessagesWaiting( xQueue ) );

    vQueueDelete( xQueue );
}

/**
 * @brief Test xQueueSend with uxQueueLength=1, uxItemSize=1 and null item.
 * @details xQueueSend should configASSERT because of the null item pointer.
 * @coverage xQueueGenericSend
 */
void test_macro_xQueueSend_oneQueueLength_oneItemSize_null( void )
{
    QueueHandle_t xQueue = xQueueCreate( 1, 1 );

    EXPECT_ASSERT_BREAK( xQueueSend( xQueue, NULL, 0 ) );

    vQueueDelete( xQueue );
}

/**
 * @brief Test xQueueSend with an equal priority task waiting.
 * @coverage xQueueGenericSend
 */
void test_macro_xQueueSend_task_waiting_equal_priority_success( void )
{
    QueueHandle_t xQueue = xQueueCreate( 1, sizeof( uint32_t ) );

    /* Insert an item into the event list. */
    td_task_setFakeTaskPriority( DEFAULT_PRIORITY );
    td_task_addFakeTaskWaitingToReceiveFromQueue( xQueue );

    uint32_t testVal = getNextMonotonicTestValue();

    TEST_ASSERT_EQUAL( 0, uxQueueMessagesWaiting( xQueue ) );

    /* Add item to queue*/
    TEST_ASSERT_EQUAL( pdTRUE, xQueueSend( xQueue, &testVal, 0 ) );

    TEST_ASSERT_EQUAL( 1, uxQueueMessagesWaiting( xQueue ) );

    TEST_ASSERT_EQUAL( 0, td_task_getYieldCount() );

    uint32_t checkVal = INVALID_UINT32;

    ( void ) xQueueReceive( xQueue, &checkVal, 0 );
    TEST_ASSERT_EQUAL( testVal, checkVal );

    vQueueDelete( xQueue );
}

/**
 * @brief Test xQueueSend with a higher priority task waiting.
 * @coverage xQueueGenericSend
 */
void test_macro_xQueueSend_task_waiting_higher_priority_success( void )
{
    QueueHandle_t xQueue = xQueueCreate( 1, sizeof( uint32_t ) );

    /* Insert an item into the event list */
    td_task_setFakeTaskPriority( DEFAULT_PRIORITY + 1 );
    td_task_addFakeTaskWaitingToReceiveFromQueue( xQueue );

    uint32_t testVal = getNextMonotonicTestValue();

    TEST_ASSERT_EQUAL( 0, uxQueueMessagesWaiting( xQueue ) );

    /* Add item to queue*/
    TEST_ASSERT_EQUAL( pdTRUE, xQueueSend( xQueue, &testVal, 0 ) );

    TEST_ASSERT_EQUAL( 1, uxQueueMessagesWaiting( xQueue ) );

    TEST_ASSERT_EQUAL( 1, td_task_getYieldCount() );

    TEST_ASSERT_EQUAL( 1, td_task_getCount_vPortYieldWithinAPI() );

    /* Check that vTaskMissedYield was not called */
    TEST_ASSERT_EQUAL( 0, td_task_getCount_vTaskMissedYield() );

    uint32_t checkVal = INVALID_UINT32;

    ( void ) xQueueReceive( xQueue, &checkVal, 0 );
    TEST_ASSERT_EQUAL( testVal, checkVal );

    vQueueDelete( xQueue );
}

/**
 * @brief Test xQueueSend with a lower priority task waiting.
 * @coverage xQueueGenericSend
 */
void test_macro_xQueueSend_task_waiting_lower_priority_success( void )
{
    QueueHandle_t xQueue = xQueueCreate( 1, sizeof( uint32_t ) );

    /* Insert an item into the event list. */
    td_task_setFakeTaskPriority( DEFAULT_PRIORITY - 1 );
    td_task_addFakeTaskWaitingToReceiveFromQueue( xQueue );

    uint32_t testVal = getNextMonotonicTestValue();

    TEST_ASSERT_EQUAL( 0, uxQueueMessagesWaiting( xQueue ) );

    /* Add item to queue*/
    TEST_ASSERT_EQUAL( pdTRUE, xQueueSend( xQueue, &testVal, 0 ) );

    TEST_ASSERT_EQUAL( 1, uxQueueMessagesWaiting( xQueue ) );

    TEST_ASSERT_EQUAL( 0, td_task_getYieldCount() );

    uint32_t checkVal = INVALID_UINT32;

    ( void ) xQueueReceive( xQueue, &checkVal, 0 );
    TEST_ASSERT_EQUAL( testVal, checkVal );

    vQueueDelete( xQueue );
}

/**
 *  @brief Test xQueueSend with taskSCHEDULER_SUSPENDED and timeout=0
 *  @details This should not cause xQueueSend to configASSERT because
 *  xQueueSend is non-blocking when timeout=0.
 *  @coverage xQueueGenericSend
 */
void test_macro_xQueueSend_nonblocking_suspended_noassert( void )
{
    QueueHandle_t xQueue = xQueueCreate( 1, sizeof( uint32_t ) );

    uint32_t testVal = getNextMonotonicTestValue();

    td_task_setSchedulerState( taskSCHEDULER_SUSPENDED );

    TEST_ASSERT_EQUAL( 0, uxQueueMessagesWaiting( xQueue ) );

    TEST_ASSERT_EQUAL( pdTRUE, xQueueSend( xQueue, &testVal, 0 ) );

    TEST_ASSERT_EQUAL( 1, uxQueueMessagesWaiting( xQueue ) );

    td_task_setSchedulerState( taskSCHEDULER_RUNNING );

    vQueueDelete( xQueue );
}

/**
 * @brief Test xQueueSendFromISR with an invalid (null) QueueHandle
 * @coverage xQueueGenericSendFromISR
 */
void test_macro_xQueueSendFromISR_invalid_handle( void )
{
    uint32_t testVal = INVALID_UINT32;

    EXPECT_ASSERT_BREAK( xQueueSendFromISR( NULL, &testVal, NULL ) );
}

/**
 * @brief xQueueSendFromISR with an empty queue
 * @coverage xQueueGenericSendFromISR
 */
void test_macro_xQueueSendFromISR_success( void )
{
    QueueHandle_t xQueue = xQueueCreate( 1, sizeof( uint32_t ) );

    uint32_t testval = getNextMonotonicTestValue();

    vFakePortAssertIfInterruptPriorityInvalid_Expect();

    TEST_ASSERT_EQUAL( 0, uxQueueMessagesWaiting( xQueue ) );

    TEST_ASSERT_EQUAL( pdTRUE, xQueueSendFromISR( xQueue, &testval, NULL ) );

    TEST_ASSERT_EQUAL( 1, uxQueueMessagesWaiting( xQueue ) );

    uint32_t checkVal = INVALID_UINT32;

    TEST_ASSERT_EQUAL( pdTRUE, xQueueReceive( xQueue, &checkVal, 0 ) );

    TEST_ASSERT_EQUAL( testval, checkVal );
    vQueueDelete( xQueue );
}

/*!
 * @brief xQueueSendFromISR with a full queue
 * @details verify that the correct value is returned after a failed send operation.
 * @coverage xQueueGenericSendFromISR
 */
void test_macro_xQueueSendFromISR_fail( void )
{
    QueueHandle_t xQueue = xQueueCreate( 1, sizeof( uint32_t ) );

    uint32_t testVal1 = getNextMonotonicTestValue();

    vFakePortAssertIfInterruptPriorityInvalid_Expect();

    TEST_ASSERT_EQUAL( 0, uxQueueMessagesWaiting( xQueue ) );

    TEST_ASSERT_EQUAL( pdTRUE, xQueueSendFromISR( xQueue, &testVal1, NULL ) );

    TEST_ASSERT_EQUAL( 1, uxQueueMessagesWaiting( xQueue ) );

    uint32_t testVal2 = getNextMonotonicTestValue();

    vFakePortAssertIfInterruptPriorityInvalid_Expect();
    TEST_ASSERT_EQUAL( errQUEUE_FULL, xQueueSendFromISR( xQueue, &testVal2, NULL ) );

    TEST_ASSERT_EQUAL( 1, uxQueueMessagesWaiting( xQueue ) );

    uint32_t checkVal = INVALID_UINT32;

    ( void ) xQueueReceive( xQueue, &checkVal, 0 );
    TEST_ASSERT_EQUAL( testVal1, checkVal );
    vQueueDelete( xQueue );
}

/**
 * @brief Test xQueueSendFromISR with uxQueueLength=1, uxItemSize=0
 * @details xQueueSendFromISR should return pdTRUE because the queue is empty.
 *  This queue is eqivalent to a binary semaphore.
 * @coverage xQueueGenericSendFromISR
 */
void test_macro_xQueueSendFromISR_oneQueueLength_zeroItemSize( void )
{
    QueueHandle_t xQueue = xQueueCreate( 1, 0 );

    uint8_t testVal = getNextMonotonicTestValue();

    vFakePortAssertIfInterruptPriorityInvalid_Expect();

    TEST_ASSERT_EQUAL( 0, uxQueueMessagesWaiting( xQueue ) );

    TEST_ASSERT_EQUAL( pdTRUE, xQueueSendFromISR( xQueue, &testVal, 0 ) );

    TEST_ASSERT_EQUAL( 1, uxQueueMessagesWaiting( xQueue ) );

    vQueueDelete( xQueue );
}

/**
 * @brief Test xQueueSendFromISR with uxQueueLength=1, uxItemSize=0 and null item.
 * @details xQueueSendFromISR should return pdTRUE because the queue is empty.
 *  This queue is eqivalent to a binary semaphore.
 * @coverage xQueueGenericSendFromISR
 */
void test_macro_xQueueSendFromISR_oneQueueLength_zeroItemSize_null( void )
{
    QueueHandle_t xQueue = xQueueCreate( 1, 0 );

    vFakePortAssertIfInterruptPriorityInvalid_Expect();

    TEST_ASSERT_EQUAL( 0, uxQueueMessagesWaiting( xQueue ) );

    TEST_ASSERT_EQUAL( pdTRUE, xQueueSendFromISR( xQueue, NULL, 0 ) );

    TEST_ASSERT_EQUAL( 1, uxQueueMessagesWaiting( xQueue ) );

    vQueueDelete( xQueue );
}

/**
 * @brief Test xQueueSendFromISR with uxQueueLength=1, uxItemSize=1
 * @details xQueueSendFromISR should return pdTRUE because the queue is empty.
 * @coverage xQueueGenericSendFromISR
 */
void test_macro_xQueueSendFromISR_oneQueueLength_oneItemSize( void )
{
    QueueHandle_t xQueue = xQueueCreate( 1, 1 );

    uint8_t testVal = getNextMonotonicTestValue();

    vFakePortAssertIfInterruptPriorityInvalid_Expect();

    TEST_ASSERT_EQUAL( 0, uxQueueMessagesWaiting( xQueue ) );

    TEST_ASSERT_EQUAL( pdTRUE, xQueueSendFromISR( xQueue, &testVal, 0 ) );

    TEST_ASSERT_EQUAL( 1, uxQueueMessagesWaiting( xQueue ) );

    vQueueDelete( xQueue );
}

/**
 * @brief Test xQueueSendFromISR with uxQueueLength=1, uxItemSize=1 and null item.
 * @details xQueueSendFromISR should configASSERT because of the null item pointer.
 * @coverage xQueueGenericSendFromISR
 */
void test_macro_xQueueSendFromISR_oneQueueLength_oneItemSize_null( void )
{
    QueueHandle_t xQueue = xQueueCreate( 1, 1 );

    EXPECT_ASSERT_BREAK( xQueueSendFromISR( xQueue, NULL, 0 ) );

    vQueueDelete( xQueue );
}

/**
 * @brief Test xQueueSendFromISR with a null pxHigherPriorityTaskWoken.
 * @details Test xQueueSendFromISR with a NULL pxHigherPriorityTaskWoken
 * in a case where xHigherPriorityTaskWoken would otherwise be written to
 * and cause a null pointer dereference.
 * @coverage xQueueGenericSendFromISR
 */
void test_macro_xQueueSendFromISR_task_waiting_higher_priority_null_pxHigherPriorityTaskWoken( void )
{
    QueueHandle_t xQueue = xQueueCreate( 1, sizeof( uint32_t ) );

    vFakePortAssertIfInterruptPriorityInvalid_Expect();

    /* Insert an item into the event list. */
    td_task_setFakeTaskPriority( DEFAULT_PRIORITY + 1 );
    td_task_addFakeTaskWaitingToReceiveFromQueue( xQueue );

    uint32_t testVal = getNextMonotonicTestValue();

    TEST_ASSERT_EQUAL( 0, uxQueueMessagesWaiting( xQueue ) );

    /* Add item to queue*/
    TEST_ASSERT_EQUAL( pdTRUE, xQueueSendFromISR( xQueue, &testVal, NULL ) );

    TEST_ASSERT_EQUAL( 1, uxQueueMessagesWaiting( xQueue ) );

    TEST_ASSERT_EQUAL( pdTRUE, td_task_getYieldPending() );

    uint32_t checkVal = INVALID_UINT32;

    ( void ) xQueueReceive( xQueue, &checkVal, 0 );
    TEST_ASSERT_EQUAL( testVal, checkVal );

    vQueueDelete( xQueue );
}

/**
 * @brief Test xQueueSendFromISR with a higher priority task waiting
 * @details Test xQueueSendFromISR with a higher priority task waiting and
 *  verifies that xHigherPriorityTaskWoken is set accordingly.
 * @coverage xQueueGenericSendFromISR
 */
void test_macro_xQueueSendFromISR_task_waiting_higher_priority_success( void )
{
    QueueHandle_t xQueue = xQueueCreate( 1, sizeof( uint32_t ) );

    vFakePortAssertIfInterruptPriorityInvalid_Expect();

    /* Insert an item into the event list. */
    td_task_setFakeTaskPriority( DEFAULT_PRIORITY + 1 );
    td_task_addFakeTaskWaitingToReceiveFromQueue( xQueue );

    uint32_t testVal = getNextMonotonicTestValue();

    BaseType_t xHigherPriorityTaskWoken = pdFALSE;

    TEST_ASSERT_EQUAL( 0, uxQueueMessagesWaiting( xQueue ) );

    /* Add item to queue*/
    TEST_ASSERT_EQUAL( pdTRUE, xQueueSendFromISR( xQueue, &testVal, &xHigherPriorityTaskWoken ) );

    TEST_ASSERT_EQUAL( 1, uxQueueMessagesWaiting( xQueue ) );

    TEST_ASSERT_EQUAL( pdTRUE, xHigherPriorityTaskWoken );

    TEST_ASSERT_EQUAL( pdTRUE, td_task_getYieldPending() );

    uint32_t checkVal = INVALID_UINT32;

    ( void ) xQueueReceive( xQueue, &checkVal, 0 );
    TEST_ASSERT_EQUAL( testVal, checkVal );

    vQueueDelete( xQueue );
}

/**
 * @brief Test xQueueSendFromISR with a lower priority task waiting
 * @details Test xQueueSendFromISR with a lower priority task waiting and
 *  verify that xHigherPriorityTaskWoken is not modified.
 * @coverage xQueueGenericSendFromISR
 */
void test_macro_xQueueSendFromISR_task_waiting_lower_priority_success( void )
{
    QueueHandle_t xQueue = xQueueCreate( 1, sizeof( uint32_t ) );

    vFakePortAssertIfInterruptPriorityInvalid_Expect();

    /* Insert an item into the event list. */
    td_task_setFakeTaskPriority( DEFAULT_PRIORITY - 1 );
    td_task_addFakeTaskWaitingToReceiveFromQueue( xQueue );

    uint32_t testVal = getNextMonotonicTestValue();

    BaseType_t xHigherPriorityTaskWoken = pdFALSE;

    TEST_ASSERT_EQUAL( 0, uxQueueMessagesWaiting( xQueue ) );

    /* Add item to queue*/
    TEST_ASSERT_EQUAL( pdTRUE, xQueueSendFromISR( xQueue, &testVal, &xHigherPriorityTaskWoken ) );
    TEST_ASSERT_EQUAL( pdFALSE, xHigherPriorityTaskWoken );

    TEST_ASSERT_EQUAL( 1, uxQueueMessagesWaiting( xQueue ) );

    uint32_t checkVal = INVALID_UINT32;

    ( void ) xQueueReceive( xQueue, &checkVal, 0 );
    TEST_ASSERT_EQUAL( testVal, checkVal );

    vQueueDelete( xQueue );
}

/**
 * @brief Test xQueueSendFromISR on a queue that is locked
 * @coverage xQueueGenericSendFromISR
 */
void test_macro_xQueueSendFromISR_locked( void )
{
    QueueHandle_t xQueue = xQueueCreate( 1, sizeof( uint32_t ) );

    /* Set private lock counters */
    vSetQueueRxLock( xQueue, queueLOCKED_UNMODIFIED );
    vSetQueueTxLock( xQueue, queueLOCKED_UNMODIFIED );

    vFakePortAssertIfInterruptPriorityInvalid_Expect();

    uint32_t testval = getNextMonotonicTestValue();

    TEST_ASSERT_EQUAL( 0, uxQueueMessagesWaiting( xQueue ) );

    TEST_ASSERT_EQUAL( pdTRUE, xQueueSendFromISR( xQueue, &testval, NULL ) );

    TEST_ASSERT_EQUAL( 1, uxQueueMessagesWaiting( xQueue ) );

    /* Verify that the cRxLock counter has not changed */
    TEST_ASSERT_EQUAL( queueLOCKED_UNMODIFIED, cGetQueueRxLock( xQueue ) );

    /* Verify that the cTxLock counter has been incremented */
    TEST_ASSERT_EQUAL( queueLOCKED_UNMODIFIED + 1, cGetQueueTxLock( xQueue ) );

    uint32_t checkVal = INVALID_UINT32;

    ( void ) xQueueReceive( xQueue, &checkVal, 0 );

    TEST_ASSERT_EQUAL( testval, checkVal );
    vQueueDelete( xQueue );
}

/**
 * @brief Test xQueueSendFromISR on a queue that is locked and cRxLock overflows.
 * @coverage xQueueGenericSendFromISR
 */
void test_macro_xQueueSendFromISR_locked_overflow( void )
{
    QueueHandle_t xQueue = xQueueCreate( 1, sizeof( uint32_t ) );

    /* Set private lock counters */
    vSetQueueRxLock( xQueue, INT8_MAX );
    vSetQueueTxLock( xQueue, INT8_MAX );

    vFakePortAssertIfInterruptPriorityInvalid_Expect();

    /* Expect an assertion since the cTxLock value has overflowed */
    fakeAssertExpectFail();

    uint32_t testval = getNextMonotonicTestValue();

    TEST_ASSERT_EQUAL( 0, uxQueueMessagesWaiting( xQueue ) );

    TEST_ASSERT_EQUAL( pdTRUE, xQueueSendFromISR( xQueue, &testval, NULL ) );

    TEST_ASSERT_EQUAL( 1, uxQueueMessagesWaiting( xQueue ) );

    /* Verify that the cRxLock counter has not changed */
    TEST_ASSERT_EQUAL( INT8_MAX, cGetQueueRxLock( xQueue ) );

    /* Verify that the cTxLock counter has been incremented */
    TEST_ASSERT_EQUAL( INT8_MIN, cGetQueueTxLock( xQueue ) );

    TEST_ASSERT_EQUAL( true, fakeAssertGetFlagAndClear() );

    uint32_t checkVal = INVALID_UINT32;

    ( void ) xQueueReceive( xQueue, &checkVal, 0 );

    TEST_ASSERT_EQUAL( testval, checkVal );
    vQueueDelete( xQueue );
}

/**
 * @brief Test xQueueSendToFront with an invalid (NULL) handle
 * @coverage xQueueGenericSend
 */
void test_macro_xQueueSendToFront_invalid_handle( void )
{
    uint32_t testVal = INVALID_UINT32;

    EXPECT_ASSERT_BREAK( xQueueSendToFront( NULL, &testVal, 0 ) );
}

/**
 * @brief Test xQueueSendToFront with a queue of length 6
 * @coverage xQueueGenericSend
 */
void test_macro_xQueueSendToFront( void )
{
    QueueHandle_t xQueue = xQueueCreate( 6, sizeof( uint32_t ) );

    /* Add 5 sequential items to the queue */
    for( int i = 1; i <= 5; i++ )
    {
        TEST_ASSERT_EQUAL( pdTRUE, xQueueSend( xQueue, &i, 0 ) );
    }

    TEST_ASSERT_EQUAL( 5, uxQueueMessagesWaiting( xQueue ) );

    /* Add "random-ish" value to front of queue */
    uint32_t testVal = getNextMonotonicTestValue();

    TEST_ASSERT_EQUAL( pdTRUE, xQueueSendToFront( xQueue, &testVal, 0 ) );

    TEST_ASSERT_EQUAL( 6, uxQueueMessagesWaiting( xQueue ) );

    /* receive the value added to the front */
    uint32_t testValCompare = 0;

    TEST_ASSERT_EQUAL( pdTRUE, xQueueReceive( xQueue, &testValCompare, 0 ) );
    TEST_ASSERT_EQUAL( testVal, testValCompare );

    /* verify the remaining items and remove from the queue */
    for( uint32_t i = 1; i <= 5; i++ )
    {
        uint32_t testVal = INVALID_UINT32;
        TEST_ASSERT_EQUAL( pdTRUE, xQueueReceive( xQueue, &testVal, 0 ) );
        TEST_ASSERT_EQUAL( i, testVal );
    }

    vQueueDelete( xQueue );
}

/**
 * @brief Test xQueueSendToFrontFromISR with a queue of length 6
 * @coverage xQueueGenericSendFromISR
 */
void test_macro_xQueueSendToFrontFromISR_invalid_handle( void )
{
    uint32_t testVal = INVALID_UINT32;

    EXPECT_ASSERT_BREAK( xQueueSendToFrontFromISR( NULL, &testVal, 0 ) );
}

/**
 * @brief Test xQueueSendToFrontFromISR with a queue of length 6
 * @coverage xQueueGenericSendFromISR
 */
void test_macro_xQueueSendToFrontFromISR( void )
{
    QueueHandle_t xQueue = xQueueCreate( 6, sizeof( uint32_t ) );

    /* Add 5 sequential items to the queue */
    for( int i = 1; i <= 5; i++ )
    {
        TEST_ASSERT_EQUAL( pdTRUE, xQueueSend( xQueue, &i, 0 ) );
    }

    vFakePortAssertIfInterruptPriorityInvalid_Expect();

    /* Add "random-ish" value to front of queue */
    uint32_t testVal = getNextMonotonicTestValue();

    TEST_ASSERT_EQUAL( 5, uxQueueMessagesWaiting( xQueue ) );

    TEST_ASSERT_EQUAL( pdTRUE, xQueueSendToFrontFromISR( xQueue, &testVal, 0 ) );

    TEST_ASSERT_EQUAL( 6, uxQueueMessagesWaiting( xQueue ) );

    /* receive the value added to the front */
    uint32_t testValCompare = 0;

    TEST_ASSERT_EQUAL( pdTRUE, xQueueReceive( xQueue, &testValCompare, 0 ) );
    TEST_ASSERT_EQUAL( testVal, testValCompare );

    /* verify the remaining items and remove from the queue */
    for( uint32_t i = 1; i <= 5; i++ )
    {
        uint32_t testVal = INVALID_UINT32;
        TEST_ASSERT_EQUAL( pdTRUE, xQueueReceive( xQueue, &testVal, 0 ) );
        TEST_ASSERT_EQUAL( i, testVal );
    }

    vQueueDelete( xQueue );
}

/**
 * @brief Test xQueueSendToBack with an invalid (NULL) handle
 * @coverage xQueueGenericSend
 */
void test_macro_xQueueSendToBack_invalid_handle( void )
{
    uint32_t testVal = INVALID_UINT32;

    EXPECT_ASSERT_BREAK( xQueueSendToBack( NULL, &testVal, 0 ) );
}

/**
 * @brief Test xQueueSendToBack with a queue of length 6
 * @coverage xQueueGenericSend
 */
void test_macro_xQueueSendToBack( void )
{
    QueueHandle_t xQueue = xQueueCreate( 6, sizeof( uint32_t ) );

    /* Add 5 sequential items to the queue */
    for( int i = 1; i <= 5; i++ )
    {
        TEST_ASSERT_EQUAL( pdTRUE, xQueueSend( xQueue, &i, 0 ) );
    }

    TEST_ASSERT_EQUAL( 5, uxQueueMessagesWaiting( xQueue ) );

    /* Add "random-ish" value to end of queue */
    uint32_t testVal = getNextMonotonicTestValue();

    TEST_ASSERT_EQUAL( pdTRUE, xQueueSendToBack( xQueue, &testVal, 0 ) );

    TEST_ASSERT_EQUAL( 6, uxQueueMessagesWaiting( xQueue ) );

    /* verify the first 5 items and remove from the queue */
    for( uint32_t i = 1; i <= 5; i++ )
    {
        uint32_t testVal = INVALID_UINT32;
        TEST_ASSERT_EQUAL( pdTRUE, xQueueReceive( xQueue, &testVal, 0 ) );
        TEST_ASSERT_EQUAL( i, testVal );
    }

    /* receive the value added to the front */
    uint32_t testValCompare = 0;

    TEST_ASSERT_EQUAL( pdTRUE, xQueueReceive( xQueue, &testValCompare, 0 ) );
    TEST_ASSERT_EQUAL( getLastMonotonicTestValue(), testValCompare );

    vQueueDelete( xQueue );
}

/**
 * @brief Test xQueueSendToBackFromISR with an invalid (NULL) handle.
 * @coverage xQueueGenericSendFromISR
 */
void test_macro_xQueueSendToBackFromISR_invalid_handle( void )
{
    uint32_t testVal = INVALID_UINT32;

    EXPECT_ASSERT_BREAK( xQueueSendToBackFromISR( NULL, &testVal, 0 ) );
}

/**
 * @brief Test xQueueSendToBackFromISR with a queue of length 6
 * @coverage xQueueGenericSendFromISR
 */
void test_macro_xQueueSendToBackFromISR( void )
{
    QueueHandle_t xQueue = xQueueCreate( 6, sizeof( uint32_t ) );

    /* Add 5 sequential items to the queue */
    for( int i = 1; i <= 5; i++ )
    {
        TEST_ASSERT_EQUAL( pdTRUE, xQueueSend( xQueue, &i, 0 ) );
    }

    /* Add "random-ish" value to end of queue */
    uint32_t testVal = getNextMonotonicTestValue();

    TEST_ASSERT_EQUAL( 5, uxQueueMessagesWaiting( xQueue ) );

    vFakePortAssertIfInterruptPriorityInvalid_Expect();
    TEST_ASSERT_EQUAL( pdTRUE, xQueueSendToBackFromISR( xQueue, &testVal, 0 ) );

    TEST_ASSERT_EQUAL( 6, uxQueueMessagesWaiting( xQueue ) );

    /* verify the first 5 items and remove from the queue */
    for( uint32_t i = 1; i <= 5; i++ )
    {
        uint32_t testVal = INVALID_UINT32;
        TEST_ASSERT_EQUAL( pdTRUE, xQueueReceive( xQueue, &testVal, 0 ) );
        TEST_ASSERT_EQUAL( i, testVal );
    }

    /* receive the value added to the front */
    uint32_t testValCompare = 0;

    TEST_ASSERT_EQUAL( pdTRUE, xQueueReceive( xQueue, &testValCompare, 0 ) );
    TEST_ASSERT_EQUAL( testVal, testValCompare );

    vQueueDelete( xQueue );
}

/**
 * @brief Test xQueueOverwrite with an invalid (NULL) queue handle.
 * @coverage xQueueGenericSend
 */
void test_macro_xQueueOverwrite_invalid_handle( void )
{
    uint32_t testVal = INVALID_UINT32;

    EXPECT_ASSERT_BREAK( xQueueOverwrite( NULL, &testVal ) );
}

/**
 * @brief Test xQueueOverwrite on an empty queue of length 1
 * @details Test xQueueOverwrite with an empty queue, equivalent to xQueueSend.
 * @coverage xQueueGenericSend
 */
void test_macro_xQueueOverwrite_empty_queue_1_add_success( void )
{
    QueueHandle_t xQueue = xQueueCreate( 1, sizeof( uint32_t ) );

    /* Send a new value to the queue using xQueueOverwrite */
    uint32_t testVal1 = getNextMonotonicTestValue();

    TEST_ASSERT_EQUAL( 0, uxQueueMessagesWaiting( xQueue ) );

    TEST_ASSERT_EQUAL( pdTRUE, xQueueOverwrite( xQueue, &testVal1 ) );

    /* Check that the queue is now full */
    TEST_ASSERT_EQUAL( 1, uxQueueMessagesWaiting( xQueue ) );

    /* Receive from the queue and verify the received value */
    uint32_t checkVal1 = INVALID_UINT32;

    TEST_ASSERT_EQUAL( pdTRUE, xQueueReceive( xQueue, &checkVal1, 0 ) );
    TEST_ASSERT_EQUAL( testVal1, checkVal1 );

    vQueueDelete( xQueue );
}

/**
 * @brief Test xQueueOverwrite on a full queue of size (1,4)
 * @details Test xQueueOverwrite with a full queue containing one item.
 * @coverage xQueueGenericSend
 */
void test_macro_xQueueOverwrite_overwrite_success( void )
{
    QueueHandle_t xQueue = xQueueCreate( 1, sizeof( uint32_t ) );

    uint32_t testVal1 = getNextMonotonicTestValue();

    TEST_ASSERT_EQUAL( 0, uxQueueMessagesWaiting( xQueue ) );

    /* send a random value to the queue */
    TEST_ASSERT_EQUAL( pdTRUE, xQueueSend( xQueue, &testVal1, 0 ) );

    /* Check that the queue now has a single message waiting */
    TEST_ASSERT_EQUAL( 1, uxQueueMessagesWaiting( xQueue ) );

    /* Peek from the queue and verify that the returned value matches testVal1 */
    uint32_t checkVal1 = 0;

    TEST_ASSERT_EQUAL( pdTRUE, xQueuePeek( xQueue, &checkVal1, 0 ) );
    TEST_ASSERT_EQUAL( testVal1, checkVal1 );
    TEST_ASSERT_NOT_EQUAL( 0, checkVal1 );

    /* Overwrite testVal1 with testVal2 in the queue */
    uint32_t testVal2 = getNextMonotonicTestValue();

    TEST_ASSERT_EQUAL( pdTRUE, xQueueOverwrite( xQueue, &testVal2 ) );

    /* Receive from the queue */
    uint32_t checkVal2 = 0;

    TEST_ASSERT_EQUAL( pdTRUE, xQueueReceive( xQueue, &checkVal2, 0 ) );

    /* Validate that checkVal2 was received from the queue */
    TEST_ASSERT_EQUAL( testVal2, checkVal2 );
    TEST_ASSERT_NOT_EQUAL( 0, checkVal2 );
    TEST_ASSERT_NOT_EQUAL( testVal1, checkVal2 );

    vQueueDelete( xQueue );
}

/**
 * @brief Test xQueueOverwrite on a full queue of size (2,4)
 * @details Test xQueueOverwrite with a full queue containing one item.
 * @note Operation of xQueueOverwrite on queues larger than 1 in length is undefined.
 * The behavior in this test is undefined.
 * @coverage xQueueGenericSend
 */
void test_macro_xQueueOverwrite_full_assert_undefined( void )
{
    QueueHandle_t xQueue = xQueueCreate( 2, sizeof( uint32_t ) );

    uint32_t testVal1 = getNextMonotonicTestValue();

    TEST_ASSERT_EQUAL( 0, uxQueueMessagesWaiting( xQueue ) );

    /* Expect that xQueueOverwrite will assert due to uxQueueLength > 1 */
    fakeAssertExpectFail();
    TEST_ASSERT_EQUAL( pdTRUE, xQueueOverwrite( xQueue, &testVal1 ) );

    /* Check that xQueueOverwrite called configASSERT */
    TEST_ASSERT_EQUAL( true, fakeAssertGetFlagAndClear() );

    /* Check that the queue now has a single message waiting */
    TEST_ASSERT_EQUAL( 1, uxQueueMessagesWaiting( xQueue ) );

    /* Overwrite testVal1 with testVal2 in the queue */
    uint32_t testVal2 = getNextMonotonicTestValue();

    /* Expect that xQueueOverwrite will assert due to uxQueueLength > 1 */
    fakeAssertExpectFail();
    TEST_ASSERT_EQUAL( pdTRUE, xQueueOverwrite( xQueue, &testVal2 ) );
    /* Check that xQueueOverwrite called configASSERT */
    TEST_ASSERT_EQUAL( true, fakeAssertGetFlagAndClear() );

    TEST_ASSERT_EQUAL( 1, uxQueueMessagesWaiting( xQueue ) );

    /* Receive from the queue */
    uint32_t checkVal2 = 0;

    TEST_ASSERT_EQUAL( pdTRUE, xQueueReceive( xQueue, &checkVal2, 0 ) );

    /* Validate that checkVal2 was received from the queue */
    TEST_ASSERT_EQUAL( testVal2, checkVal2 );
    TEST_ASSERT_NOT_EQUAL( 0, checkVal2 );

    vQueueDelete( xQueue );
}

/**
 * @brief Test xQueueOverwriteFromISR with an invalid (NULL) queue handle.
 * @coverage xQueueGenericSendFromISR
 */
void test_macro_xQueueOverwriteFromISR_invalid_handle( void )
{
    uint32_t testVal = INVALID_UINT32;

    EXPECT_ASSERT_BREAK( xQueueOverwriteFromISR( NULL, &testVal, NULL ) );
}

/**
 * @brief Test xQueueOverwriteFromISR on an empty queue of length 1
 * @details Test xQueueOverwriteFromISR with an empty queue, equivalent to xQueueSend.
 * @coverage xQueueGenericSendFromISR
 */
void test_macro_xQueueOverwriteFromISR_empty_queue_1_add_success( void )
{
    QueueHandle_t xQueue = xQueueCreate( 1, sizeof( uint32_t ) );

    vFakePortAssertIfInterruptPriorityInvalid_Expect();

    TEST_ASSERT_EQUAL( 0, uxQueueMessagesWaiting( xQueue ) );

    /* Send a new value to the queue using xQueueOverwriteFromISR */
    uint32_t testVal1 = getNextMonotonicTestValue();

    TEST_ASSERT_EQUAL( pdTRUE, xQueueOverwriteFromISR( xQueue, &testVal1, NULL ) );

    /* Check that the queue is now full */
    TEST_ASSERT_EQUAL( 1, uxQueueMessagesWaiting( xQueue ) );

    /* Receive from the queue and verify the received value */
    uint32_t checkVal1 = INVALID_UINT32;

    TEST_ASSERT_EQUAL( pdTRUE, xQueueReceive( xQueue, &checkVal1, 0 ) );
    TEST_ASSERT_EQUAL( testVal1, checkVal1 );

    vQueueDelete( xQueue );
}

/**
 * @brief Test xQueueOverwriteFromISR on a full queue of size (1,4)
 * @details Test xQueueOverwriteFromISR with a full queue containing one item.
 * @coverage xQueueGenericSendFromISR
 */
void test_macro_xQueueOverwriteFromISR_overwrite_success( void )
{
    QueueHandle_t xQueue = xQueueCreate( 1, sizeof( uint32_t ) );

    uint32_t testVal1 = getNextMonotonicTestValue();

    /* send a random value to the queue */
    TEST_ASSERT_EQUAL( pdTRUE, xQueueSend( xQueue, &testVal1, 0 ) );

    /* Check that the queue now has a single message waiting */
    TEST_ASSERT_EQUAL( 1, uxQueueMessagesWaiting( xQueue ) );

    /* Peek from the queue and verify that the returned value matches testVal1 */
    uint32_t checkVal1 = 0;

    TEST_ASSERT_EQUAL( pdTRUE, xQueuePeek( xQueue, &checkVal1, 0 ) );
    TEST_ASSERT_EQUAL( testVal1, checkVal1 );
    TEST_ASSERT_NOT_EQUAL( 0, checkVal1 );

    vFakePortAssertIfInterruptPriorityInvalid_Expect();

    /* Overwrite testVal1 with testVal2 in the queue */
    uint32_t testVal2 = getNextMonotonicTestValue();

    TEST_ASSERT_EQUAL( pdTRUE, xQueueOverwriteFromISR( xQueue, &testVal2, NULL ) );

    TEST_ASSERT_EQUAL( 1, uxQueueMessagesWaiting( xQueue ) );

    /* Receive from the queue */
    uint32_t checkVal2 = 0;

    TEST_ASSERT_EQUAL( pdTRUE, xQueueReceive( xQueue, &checkVal2, 0 ) );

    /* Validate that checkVal2 was received from the queue */
    TEST_ASSERT_EQUAL( testVal2, checkVal2 );
    TEST_ASSERT_NOT_EQUAL( 0, checkVal2 );
    TEST_ASSERT_NOT_EQUAL( testVal1, checkVal2 );

    /* Verify that the queue is empty */
    TEST_ASSERT_EQUAL( 0, uxQueueMessagesWaiting( xQueue ) );

    vQueueDelete( xQueue );
}

/**
 * @brief Test xQueueOverwriteFromISR on a full queue of size (2,4)
 * @details Test xQueueOverwriteFromISR with a full queue containing one item.
 * @note Operation of xQueueOverwriteFromISR on queues larger than 1 in length is undefined.
 * The behavior in this test is undefined.
 * @coverage xQueueGenericSendFromISR
 */
void test_macro_xQueueOverwriteFromISR_full_assert_undefined( void )
{
    QueueHandle_t xQueue = xQueueCreate( 2, sizeof( uint32_t ) );

    vFakePortAssertIfInterruptPriorityInvalid_Expect();

    uint32_t testVal1 = getNextMonotonicTestValue();

    TEST_ASSERT_EQUAL( 0, uxQueueMessagesWaiting( xQueue ) );

    /* Expect that xQueueOverwriteFromISR will assert due to uxQueueLength > 1 */
    fakeAssertExpectFail();
    TEST_ASSERT_EQUAL( pdTRUE, xQueueOverwriteFromISR( xQueue, &testVal1, NULL ) );

    /* Check that xQueueOverwriteFromISR called configASSERT */
    TEST_ASSERT_EQUAL( true, fakeAssertGetFlagAndClear() );

    /* Check that the queue now has a single message waiting */
    TEST_ASSERT_EQUAL( 1, uxQueueMessagesWaiting( xQueue ) );

    vFakePortAssertIfInterruptPriorityInvalid_Expect();

    /* Overwrite testVal1 with testVal2 in the queue */
    uint32_t testVal2 = getNextMonotonicTestValue();

    /* Expect that xQueueOverwriteFromISR will assert due to uxQueueLength > 1 */
    fakeAssertExpectFail();
    TEST_ASSERT_EQUAL( pdTRUE, xQueueOverwriteFromISR( xQueue, &testVal2, NULL ) );
    /* Check that xQueueOverwriteFromISR called configASSERT */
    TEST_ASSERT_EQUAL( true, fakeAssertGetFlagAndClear() );

    TEST_ASSERT_EQUAL( 1, uxQueueMessagesWaiting( xQueue ) );

    /* Receive from the queue */
    uint32_t checkVal2 = 0;

    TEST_ASSERT_EQUAL( pdTRUE, xQueueReceive( xQueue, &checkVal2, 0 ) );

    /* Validate that checkVal2 was received from the queue */
    TEST_ASSERT_EQUAL( testVal2, checkVal2 );
    TEST_ASSERT_NOT_EQUAL( 0, checkVal2 );

    vQueueDelete( xQueue );
}
