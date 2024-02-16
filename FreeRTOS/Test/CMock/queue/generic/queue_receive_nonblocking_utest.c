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
/*! @file queue_receive_nonblocking_utest.c */

/* C runtime includes. */
#include <stdlib.h>
#include <stdbool.h>
#include <string.h>

#include "../queue_utest_common.h"

#include "mock_fake_port.h"

/* Queue includes */
#include "FreeRTOS.h"
#include "FreeRTOSConfig.h"
#include "queue.h"

/* ============================  GLOBAL VARIABLES =========================== */

/* Used to share a QueueHandle_t between a test case and it's callbacks */
static QueueHandle_t xQueueHandleStatic = NULL;
static BaseType_t xStubExpectedReturnValue = pdFALSE;

/* ==========================  CALLBACK FUNCTIONS =========================== */

/* ============================= Unity Fixtures ============================= */

void setUp( void )
{
    commonSetUp();
    vFakePortAssertIfInterruptPriorityInvalid_Ignore();
    xQueueHandleStatic = NULL;
    xStubExpectedReturnValue = pdFALSE;
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

/* =============================  Test Cases ============================== */

/**
 * @brief Test xQueuePeek with an invalid QueueHandle
 * @coverage xQueuePeek
 */
void test_xQueuePeek_invalid_handle( void )
{
    EXPECT_ASSERT_BREAK( xQueuePeek( NULL, NULL, 0 ) );
}

/**
 * @brief Test xQueuePeek with an empty queue
 * @coverage xQueuePeek
 */
void test_xQueuePeek_fail_empty( void )
{
    /* Create a new queue */
    QueueHandle_t xQueue = xQueueCreate( 1, sizeof( uint32_t ) );

    uint32_t checkVal = INVALID_UINT32;

    /* peek from the queue while empty */
    TEST_ASSERT_EQUAL( pdFALSE, xQueuePeek( xQueue, &checkVal, 0 ) );

    vQueueDelete( xQueue );
}

/**
 * @brief Test xQueuePeek with an empty queue of length 1, items size 0
 * @coverage xQueuePeek
 */
void test_xQueuePeek_zeroItemSize_empty( void )
{
    /* Create a new queue */
    QueueHandle_t xQueue = xQueueCreate( 1, 0 );

    uint32_t checkVal = INVALID_UINT32;

    /* peek from the queue while empty */
    TEST_ASSERT_EQUAL( pdFALSE, xQueuePeek( xQueue, &checkVal, 0 ) );

    vQueueDelete( xQueue );
}

/**
 * @brief Test xQueuePeek with a full queue of length 1, items size 0
 * @coverage xQueuePeek
 */
void test_xQueuePeek_zeroItemSize_full( void )
{
    /* Create a new queue */
    QueueHandle_t xQueue = xQueueCreate( 1, 0 );

    ( void ) xQueueSend( xQueue, NULL, 0 );

    TEST_ASSERT_EQUAL( 1, uxQueueMessagesWaiting( xQueue ) );

    /* peek from the queue while full */
    TEST_ASSERT_EQUAL( pdTRUE, xQueuePeek( xQueue, NULL, 0 ) );

    TEST_ASSERT_EQUAL( 1, uxQueueMessagesWaiting( xQueue ) );

    vQueueDelete( xQueue );
}

/**
 * @brief Test xQueuePeek with a null pvBuffer on an empty queue of length 1, items size 4
 * @coverage xQueuePeek
 */
void test_xQueuePeek_fourItemSize_nullptr_assert_empty( void )
{
    /* Create a new queue */
    QueueHandle_t xQueue = xQueueCreate( 1, sizeof( uint32_t ) );

    fakeAssertExpectFail();

    /* peek from the queue with a nullptr storage location */
    TEST_ASSERT_EQUAL( pdFALSE, xQueuePeek( xQueue, NULL, 0 ) );

    TEST_ASSERT_EQUAL( true, fakeAssertGetFlagAndClear() );

    vQueueDelete( xQueue );
}

/**
 * @brief Test xQueuePeek with a null pvBuffer on a full queue of length 1, items size 4
 * @coverage xQueuePeek
 */
void test_xQueuePeek_fourItemSize_nullptr_assert_full( void )
{
    /* Create a new queue */
    QueueHandle_t xQueue = xQueueCreate( 1, sizeof( uint32_t ) );

    uint32_t testVal = getNextMonotonicTestValue();

    ( void ) xQueueSend( xQueue, &testVal, 0 );

    /* peek from the queue with a nullptr storage location */
    EXPECT_ASSERT_BREAK( xQueuePeek( xQueue, NULL, 0 ) );

    vQueueDelete( xQueue );
}

/**
 * @brief Test xQueuePeek with an occupied queue
 * @coverage xQueuePeek
 */
void test_xQueuePeek_success( void )
{
    /* Create a new queue */
    QueueHandle_t xQueue = xQueueCreate( 1, sizeof( uint32_t ) );

    uint32_t testVal = getNextMonotonicTestValue();

    ( void ) xQueueSend( xQueue, &testVal, 0 );

    uint32_t checkVal = INVALID_UINT32;

    TEST_ASSERT_EQUAL( 1, uxQueueMessagesWaiting( xQueue ) );

    /* Peek from the queue while full */
    TEST_ASSERT_EQUAL( pdTRUE, xQueuePeek( xQueue, &checkVal, 0 ) );
    TEST_ASSERT_EQUAL( testVal, checkVal );

    /* Verify that xQueuePeek did not remove the item from the queue */
    TEST_ASSERT_EQUAL( 1, uxQueueMessagesWaiting( xQueue ) );

    vQueueDelete( xQueue );
}

/**
 * @brief Stub for vPortYieldWithinAPI which calls xQueueReceive
 */
static void vPortYieldWithinAPI_xQueueReceive_Stub( int cmock_num_calls )
{
    td_task_vPortYieldWithinAPIStub( cmock_num_calls );

    vFakePortExitCriticalSection();

    uint32_t checkVal = INVALID_UINT32;

    TEST_ASSERT_EQUAL( xStubExpectedReturnValue == pdTRUE ? 1 : 0, uxQueueMessagesWaiting( xQueueHandleStatic ) );

    TEST_ASSERT_EQUAL( xStubExpectedReturnValue, xQueueReceive( xQueueHandleStatic, &checkVal, 0 ) );

    TEST_ASSERT_EQUAL( 0, uxQueueMessagesWaiting( xQueueHandleStatic ) );

    if( pdTRUE == xStubExpectedReturnValue )
    {
        TEST_ASSERT_EQUAL( getLastMonotonicTestValue(), checkVal );
    }
    else
    {
        TEST_ASSERT_EQUAL( INVALID_UINT32, checkVal );
    }

    vFakePortEnterCriticalSection();
}

/**
 * @brief Stub for vPortYieldWithinAPI which calls xQueuePeek
 */
static void vPortYieldWithinAPI_xQueuePeek_Stub( int cmock_num_calls )
{
    td_task_vPortYieldWithinAPIStub( cmock_num_calls );

    vFakePortExitCriticalSection();

    uint32_t checkVal = INVALID_UINT32;

    TEST_ASSERT_EQUAL( xStubExpectedReturnValue == pdTRUE ? 1 : 0, uxQueueMessagesWaiting( xQueueHandleStatic ) );

    TEST_ASSERT_EQUAL( xStubExpectedReturnValue, xQueuePeek( xQueueHandleStatic, &checkVal, 0 ) );

    TEST_ASSERT_EQUAL( xStubExpectedReturnValue == pdTRUE ? 1 : 0, uxQueueMessagesWaiting( xQueueHandleStatic ) );

    if( pdTRUE == xStubExpectedReturnValue )
    {
        TEST_ASSERT_EQUAL( getLastMonotonicTestValue(), checkVal );
    }
    else
    {
        TEST_ASSERT_EQUAL( INVALID_UINT32, checkVal );
    }

    vFakePortEnterCriticalSection();
}

/**
 * @brief Test xQueuePeek with an occupied queue with a higher priority task waiting that does not modify the queue.
 * @coverage xQueuePeek
 */
void test_xQueuePeek_noop_waiting_higher_priority( void )
{
    /* Create a new queue */
    QueueHandle_t xQueue = xQueueCreate( 1, sizeof( uint32_t ) );

    /* Export for callback */
    xQueueHandleStatic = xQueue;

    /* Add a value to the queue */
    uint32_t testVal = getNextMonotonicTestValue();

    ( void ) xQueueSend( xQueue, &testVal, 0 );

    /* Insert an item into the event list */
    td_task_setFakeTaskPriority( DEFAULT_PRIORITY + 1 );
    td_task_addFakeTaskWaitingToReceiveFromQueue( xQueue );

    /* peek from the queue */
    uint32_t checkVal = INVALID_UINT32;

    vTaskYieldWithinAPI_Stub( vTaskYieldWithinAPI_Callback );

    TEST_ASSERT_EQUAL( 1, uxQueueMessagesWaiting( xQueue ) );

    TEST_ASSERT_EQUAL( pdTRUE, xQueuePeek( xQueue, &checkVal, 0 ) );
    TEST_ASSERT_EQUAL( testVal, checkVal );

    TEST_ASSERT_EQUAL( 1, uxQueueMessagesWaiting( xQueue ) );

    /* Verify that the task Yielded */
    TEST_ASSERT_EQUAL( 1, td_task_getYieldCount() );

    /* Check that vTaskMissedYield was called */
    TEST_ASSERT_EQUAL( 1, td_task_getCount_vPortYieldWithinAPI() );

    vQueueDelete( xQueue );
}

/**
 * @brief Test xQueuePeek with an occupied queue with a higher priority xQueuePeek pending.
 * @coverage xQueuePeek
 */
void test_xQueuePeek_xQueuePeek_waiting_higher_priority( void )
{
    /* Create a new queue */
    QueueHandle_t xQueue = xQueueCreate( 1, sizeof( uint32_t ) );

    /* Export for callback */
    xQueueHandleStatic = xQueue;

    /* Add a value to the queue */
    uint32_t testVal = getNextMonotonicTestValue();

    ( void ) xQueueSend( xQueue, &testVal, 0 );

    /* Insert an item into the event list */
    td_task_setFakeTaskPriority( DEFAULT_PRIORITY + 1 );
    td_task_addFakeTaskWaitingToReceiveFromQueue( xQueue );

    vFakePortYieldWithinAPI_Stub( &vPortYieldWithinAPI_xQueuePeek_Stub );
    vTaskYieldWithinAPI_Stub( vTaskYieldWithinAPI_Callback );

    xStubExpectedReturnValue = pdTRUE;

    /* peek from the queue */
    uint32_t checkVal = INVALID_UINT32;

    TEST_ASSERT_EQUAL( 1, uxQueueMessagesWaiting( xQueue ) );

    TEST_ASSERT_EQUAL( pdTRUE, xQueuePeek( xQueue, &checkVal, 0 ) );
    TEST_ASSERT_EQUAL( testVal, checkVal );

    TEST_ASSERT_EQUAL( 1, uxQueueMessagesWaiting( xQueue ) );

    /* Verify that the task Yielded */
    TEST_ASSERT_EQUAL( 1, td_task_getYieldCount() );

    /* Check that vTaskMissedYield was called */
    TEST_ASSERT_EQUAL( 1, td_task_getCount_vPortYieldWithinAPI() );

    vQueueDelete( xQueue );
}

/**
 * @brief Test xQueuePeek with an occupied queue with a higher priority xQueueReceive pending.
 * @coverage xQueuePeek
 */
void test_xQueuePeek_xQueueReceive_waiting_higher_priority( void )
{
    /* Create a new queue */
    QueueHandle_t xQueue = xQueueCreate( 1, sizeof( uint32_t ) );

    /* Export for callback */
    xQueueHandleStatic = xQueue;

    /* Add a value to the queue */
    uint32_t testVal = getNextMonotonicTestValue();

    ( void ) xQueueSend( xQueue, &testVal, 0 );

    /* Insert an item into the event list */
    td_task_setFakeTaskPriority( DEFAULT_PRIORITY + 1 );
    td_task_addFakeTaskWaitingToReceiveFromQueue( xQueue );

    vFakePortYieldWithinAPI_Stub( &vPortYieldWithinAPI_xQueueReceive_Stub );
    vTaskYieldWithinAPI_Stub( vTaskYieldWithinAPI_Callback );

    xStubExpectedReturnValue = pdTRUE;

    /* peek from the queue */
    uint32_t checkVal = INVALID_UINT32;

    TEST_ASSERT_EQUAL( 1, uxQueueMessagesWaiting( xQueue ) );

    TEST_ASSERT_EQUAL( pdTRUE, xQueuePeek( xQueue, &checkVal, 0 ) );
    TEST_ASSERT_EQUAL( testVal, checkVal );

    TEST_ASSERT_EQUAL( 0, uxQueueMessagesWaiting( xQueue ) );

    /* Verify that the task Yielded */
    TEST_ASSERT_EQUAL( 1, td_task_getYieldCount() );

    /* Check that vTaskMissedYield was called */
    TEST_ASSERT_EQUAL( 1, td_task_getCount_vPortYieldWithinAPI() );

    vQueueDelete( xQueue );
}

/**
 * @brief Test xQueuePeek with an occupied queue with a lower priority task pending which does not modify the queue.
 * @coverage xQueuePeek
 */
void test_xQueuePeek_noop_waiting_lower_priority( void )
{
    /* Create a new queue */
    QueueHandle_t xQueue = xQueueCreate( 1, sizeof( uint32_t ) );

    /* Export for callback */
    xQueueHandleStatic = xQueue;

    /* Add a value to the queue */
    uint32_t testVal = getNextMonotonicTestValue();

    ( void ) xQueueSend( xQueue, &testVal, 0 );

    /* Insert an item into the event list */
    td_task_setFakeTaskPriority( DEFAULT_PRIORITY - 1 );
    td_task_addFakeTaskWaitingToReceiveFromQueue( xQueue );

    uint32_t checkVal = INVALID_UINT32;

    TEST_ASSERT_EQUAL( 1, uxQueueMessagesWaiting( xQueue ) );

    /* peek from the queue */
    TEST_ASSERT_EQUAL( pdTRUE, xQueuePeek( xQueue, &checkVal, 0 ) );
    TEST_ASSERT_EQUAL( testVal, checkVal );

    TEST_ASSERT_EQUAL( 1, uxQueueMessagesWaiting( xQueue ) );

    vQueueDelete( xQueue );
}

/**
 * @brief Test xQueuePeek with an occupied queue with a lower priority xQueuePeek operation pending.
 * @coverage xQueuePeek
 */
void test_xQueuePeek_xQueuePeek_waiting_lower_priority( void )
{
    /* Create a new queue */
    QueueHandle_t xQueue = xQueueCreate( 1, sizeof( uint32_t ) );

    /* Export for callback */
    xQueueHandleStatic = xQueue;

    /* Add a value to the queue */
    uint32_t testVal = getNextMonotonicTestValue();

    ( void ) xQueueSend( xQueue, &testVal, 0 );

    /* Insert an item into the event list */
    td_task_setFakeTaskPriority( DEFAULT_PRIORITY - 1 );
    td_task_addFakeTaskWaitingToReceiveFromQueue( xQueue );

    vFakePortYieldWithinAPI_Stub( &vPortYieldWithinAPI_xQueuePeek_Stub );

    xStubExpectedReturnValue = pdFALSE;

    uint32_t checkVal = INVALID_UINT32;

    TEST_ASSERT_EQUAL( 1, uxQueueMessagesWaiting( xQueue ) );

    /* peek from the queue */
    TEST_ASSERT_EQUAL( pdTRUE, xQueuePeek( xQueue, &checkVal, 0 ) );
    TEST_ASSERT_EQUAL( testVal, checkVal );

    TEST_ASSERT_EQUAL( 1, uxQueueMessagesWaiting( xQueue ) );

    vQueueDelete( xQueue );
}

/**
 * @brief Test xQueuePeek with an occupied queue with a lower priority xQueueReceive operation pending.
 * @coverage xQueuePeek
 */
void test_xQueuePeek_xQueueReceive_waiting_lower_priority( void )
{
    /* Create a new queue */
    QueueHandle_t xQueue = xQueueCreate( 1, sizeof( uint32_t ) );

    /* Export for callback */
    xQueueHandleStatic = xQueue;

    /* Add a value to the queue */
    uint32_t testVal = getNextMonotonicTestValue();

    ( void ) xQueueSend( xQueue, &testVal, 0 );

    /* Insert an item into the event list */
    td_task_setFakeTaskPriority( DEFAULT_PRIORITY - 1 );
    td_task_addFakeTaskWaitingToReceiveFromQueue( xQueue );

    vFakePortYieldWithinAPI_Stub( &vPortYieldWithinAPI_xQueueReceive_Stub );

    xStubExpectedReturnValue = pdFALSE;

    uint32_t checkVal = INVALID_UINT32;

    TEST_ASSERT_EQUAL( 1, uxQueueMessagesWaiting( xQueue ) );

    /* peek from the queue */
    TEST_ASSERT_EQUAL( pdTRUE, xQueuePeek( xQueue, &checkVal, 0 ) );
    TEST_ASSERT_EQUAL( testVal, checkVal );

    TEST_ASSERT_EQUAL( 1, uxQueueMessagesWaiting( xQueue ) );

    vQueueDelete( xQueue );
}

/**
 *  @brief Test xQueuePeek with taskSCHEDULER_SUSPENDED and timeout=0
 *  @details This should not cause xQueuePeek to configASSERT because
 *  xQueuePeek is non-blocking when timeout=0.
 *  @coverage xQueuePeek
 */
void test_xQueuePeek_nonblocking_suspended_noassert( void )
{
    QueueHandle_t xQueue = xQueueCreate( 1, sizeof( uint32_t ) );

    uint32_t checkVal = INVALID_UINT32;

    td_task_setSchedulerState( taskSCHEDULER_SUSPENDED );

    TEST_ASSERT_EQUAL( pdFALSE, xQueuePeek( xQueue, &checkVal, 0 ) );

    td_task_setSchedulerState( taskSCHEDULER_RUNNING );

    vQueueDelete( xQueue );
}

/**
 * @brief Test xQueuePeekFromISR with an invalid QueueHandle
 * @coverage xQueuePeekFromISR
 */
void test_xQueuePeekFromISR_invalid_handle( void )
{
    EXPECT_ASSERT_BREAK( xQueuePeekFromISR( NULL, NULL ) );
}

/**
 * @brief Test xQueuePeekFromISR with a full queue of length 1, items size 0
 * @details xQueuePeekFromISR is not allowed on a semaphore (item size 0) and causes a configASSERT.
 * @coverage xQueuePeekFromISR
 */
void test_xQueuePeekFromISR_zeroItemSize_assert_full( void )
{
    /* Create a new queue */
    QueueHandle_t xQueue = xQueueCreate( 1, 0 );

    ( void ) xQueueSend( xQueue, NULL, 0 );

    vFakePortAssertIfInterruptPriorityInvalid_Expect();
    ulFakePortSetInterruptMaskFromISR_ExpectAndReturn( getNextMonotonicTestValue() );
    vFakePortClearInterruptMaskFromISR_Expect( getLastMonotonicTestValue() );

    /* Expect an assertion failure because xQueuePeekFromISR is not supported for semaphores? */
    fakeAssertExpectFail();

    TEST_ASSERT_EQUAL( 1, uxQueueMessagesWaiting( xQueue ) );

    /* peek from the queue while full */
    TEST_ASSERT_EQUAL( pdTRUE, xQueuePeekFromISR( xQueue, NULL ) );

    TEST_ASSERT_EQUAL( 1, uxQueueMessagesWaiting( xQueue ) );

    TEST_ASSERT_EQUAL( true, fakeAssertGetFlagAndClear() );

    vQueueDelete( xQueue );
}

/**
 * @brief Test xQueuePeekFromISR with a null pvBuffer on an empty queue of length 1, items size 4
 * @coverage xQueuePeekFromISR
 */
void test_xQueuePeekFromISR_fourItemSize_nullptr_assert_empty( void )
{
    /* Create a new queue */
    QueueHandle_t xQueue = xQueueCreate( 1, sizeof( uint32_t ) );

    vFakePortAssertIfInterruptPriorityInvalid_Expect();
    ulFakePortSetInterruptMaskFromISR_ExpectAndReturn( getNextMonotonicTestValue() );
    vFakePortClearInterruptMaskFromISR_Expect( getLastMonotonicTestValue() );

    /* Expect an assertion failure due to the null pointer passed into xqueuePeekFromISR */
    fakeAssertExpectFail();

    /* peek from the queue with a nullptr storage location */
    TEST_ASSERT_EQUAL( pdFALSE, xQueuePeekFromISR( xQueue, NULL ) );

    TEST_ASSERT_EQUAL( true, fakeAssertGetFlagAndClear() );

    vQueueDelete( xQueue );
}

/**
 * @brief Test xQueuePeekFromISR with a null pvBuffer on a full queue of length 1, items size 4
 * @coverage xQueuePeekFromISR
 */
void test_xQueuePeekFromISR_fourItemSize_nullptr_assert_full( void )
{
    /* Create a new queue */
    QueueHandle_t xQueue = xQueueCreate( 1, sizeof( uint32_t ) );

    uint32_t testVal = getNextMonotonicTestValue();

    ( void ) xQueueSend( xQueue, &testVal, 0 );

    /* peek from the queue with a nullptr storage location */
    EXPECT_ASSERT_BREAK( xQueuePeekFromISR( xQueue, NULL ) );

    vQueueDelete( xQueue );
}

/**
 * @brief Test xQueuePeekFromISR with an empty queue
 * @coverage xQueuePeekFromISR
 */
void test_xQueuePeekFromISR_fail_empty( void )
{
    /* Create a new queue */
    QueueHandle_t xQueue = xQueueCreate( 1, sizeof( uint32_t ) );

    uint32_t checkVal = INVALID_UINT32;

    vFakePortAssertIfInterruptPriorityInvalid_Expect();
    ulFakePortSetInterruptMaskFromISR_ExpectAndReturn( getNextMonotonicTestValue() );
    vFakePortClearInterruptMaskFromISR_Expect( getLastMonotonicTestValue() );

    /* peek from the queue while empty */
    TEST_ASSERT_EQUAL( pdFALSE, xQueuePeekFromISR( xQueue, &checkVal ) );

    vQueueDelete( xQueue );
}

/**
 * @brief Test xQueuePeekFromISR with an occupied queue
 * @coverage xQueuePeekFromISR
 */
void test_xQueuePeekFromISR_success( void )
{
    /* Create a new queue */
    QueueHandle_t xQueue = xQueueCreate( 1, sizeof( uint32_t ) );

    uint32_t testVal = getNextMonotonicTestValue();

    ( void ) xQueueSend( xQueue, &testVal, 0 );

    vFakePortAssertIfInterruptPriorityInvalid_Expect();
    ulFakePortSetInterruptMaskFromISR_ExpectAndReturn( getNextMonotonicTestValue() );
    vFakePortClearInterruptMaskFromISR_Expect( getLastMonotonicTestValue() );

    uint32_t checkVal = INVALID_UINT32;

    TEST_ASSERT_EQUAL( 1, uxQueueMessagesWaiting( xQueue ) );

    /* peek from the queue while full */
    TEST_ASSERT_EQUAL( pdTRUE, xQueuePeekFromISR( xQueue, &checkVal ) );
    TEST_ASSERT_EQUAL( testVal, checkVal );

    TEST_ASSERT_EQUAL( 1, uxQueueMessagesWaiting( xQueue ) );

    vQueueDelete( xQueue );
}

/**
 * @brief Test xQueueReceive with an invalid QueueHandle
 * @coverage xQueueReceive
 */
void test_xQueueReceive_invalid_handle( void )
{
    EXPECT_ASSERT_BREAK( xQueueReceive( NULL, NULL, 0 ) );
}

/**
 * @brief Test xQueueReceive with an empty queue
 * @coverage xQueueReceive
 */
void test_xQueueReceive_fail_empty( void )
{
    /* Create a new queue */
    QueueHandle_t xQueue = xQueueCreate( 1, sizeof( uint32_t ) );

    uint32_t checkVal = INVALID_UINT32;

    /* receive from the queue while empty */
    TEST_ASSERT_EQUAL( pdFALSE, xQueueReceive( xQueue, &checkVal, 0 ) );

    vQueueDelete( xQueue );
}

/**
 * @brief Test xQueueReceive with an empty queue of length 1, items size 0
 * @coverage xQueueReceive
 */
void test_xQueueReceive_zeroItemSize_empty( void )
{
    /* Create a new queue */
    QueueHandle_t xQueue = xQueueCreate( 1, 0 );

    uint32_t checkVal = INVALID_UINT32;

    /* receive from the queue while empty */
    TEST_ASSERT_EQUAL( pdFALSE, xQueueReceive( xQueue, &checkVal, 0 ) );

    vQueueDelete( xQueue );
}

/**
 * @brief Test xQueueReceive with a full queue of length 1, items size 0
 * @coverage xQueueReceive
 */
void test_xQueueReceive_zeroItemSize_full( void )
{
    /* Create a new queue */
    QueueHandle_t xQueue = xQueueCreate( 1, 0 );

    ( void ) xQueueSend( xQueue, NULL, 0 );

    TEST_ASSERT_EQUAL( 1, uxQueueMessagesWaiting( xQueue ) );

    /* receive from the queue while full */
    TEST_ASSERT_EQUAL( pdTRUE, xQueueReceive( xQueue, NULL, 0 ) );

    TEST_ASSERT_EQUAL( 0, uxQueueMessagesWaiting( xQueue ) );

    vQueueDelete( xQueue );
}

/**
 * @brief Test xQueueReceive with a null pvBuffer on an empty queue of length 1, items size 4
 * @coverage xQueueReceive
 */
void test_xQueueReceive_fourItemSize_nullptr_assert_empty( void )
{
    /* Create a new queue */
    QueueHandle_t xQueue = xQueueCreate( 1, sizeof( uint32_t ) );

    fakeAssertExpectFail();

    /* receive from the queue with a nullptr storage location */
    TEST_ASSERT_EQUAL( pdFALSE, xQueueReceive( xQueue, NULL, 0 ) );

    TEST_ASSERT_EQUAL( true, fakeAssertGetFlagAndClear() );

    vQueueDelete( xQueue );
}

/**
 * @brief Test xQueueReceive with a null pvBuffer on a full queue of length 1, items size 4
 * @coverage xQueueReceive
 */
void test_xQueueReceive_fourItemSize_nullptr_assert_full( void )
{
    /* Create a new queue */
    QueueHandle_t xQueue = xQueueCreate( 1, sizeof( uint32_t ) );

    uint32_t testVal = getNextMonotonicTestValue();

    ( void ) xQueueSend( xQueue, &testVal, 0 );

    /* receive from the queue with a nullptr storage location */
    EXPECT_ASSERT_BREAK( xQueueReceive( xQueue, NULL, 0 ) );

    vQueueDelete( xQueue );
}

/**
 * @brief Test xQueueReceive with an occupied queue
 * @coverage xQueueReceive
 */
void test_xQueueReceive_success( void )
{
    /* Create a new queue */
    QueueHandle_t xQueue = xQueueCreate( 1, sizeof( uint32_t ) );

    uint32_t testVal = getNextMonotonicTestValue();

    ( void ) xQueueSend( xQueue, &testVal, 0 );

    TEST_ASSERT_EQUAL( 1, uxQueueMessagesWaiting( xQueue ) );

    uint32_t checkVal = INVALID_UINT32;

    /* receive from the queue while full */
    TEST_ASSERT_EQUAL( pdTRUE, xQueueReceive( xQueue, &checkVal, 0 ) );
    TEST_ASSERT_EQUAL( testVal, checkVal );

    TEST_ASSERT_EQUAL( 0, uxQueueMessagesWaiting( xQueue ) );

    vQueueDelete( xQueue );
}

/**
 * @brief Test xQueueReceive with an occupied queue with a higher priority task
 * pending which does not modify the queue.
 * @coverage xQueueReceive
 */
void test_xQueueReceive_noop_waiting_higher_priority( void )
{
    /* Create a new queue */
    QueueHandle_t xQueue = xQueueCreate( 1, sizeof( uint32_t ) );

    /* Add a value to the queue */
    uint32_t testVal = getNextMonotonicTestValue();

    ( void ) xQueueSend( xQueue, &testVal, 0 );

    /* Insert an item into the event list */
    td_task_setFakeTaskPriority( DEFAULT_PRIORITY + 1 );
    td_task_addFakeTaskWaitingToSendToQueue( xQueue );

    uint32_t checkVal = INVALID_UINT32;

    vTaskYieldWithinAPI_Stub( vTaskYieldWithinAPI_Callback );

    TEST_ASSERT_EQUAL( 1, uxQueueMessagesWaiting( xQueue ) );

    /* receive from the queue */
    TEST_ASSERT_EQUAL( pdTRUE, xQueueReceive( xQueue, &checkVal, 0 ) );
    TEST_ASSERT_EQUAL( testVal, checkVal );

    TEST_ASSERT_EQUAL( 0, uxQueueMessagesWaiting( xQueue ) );

    TEST_ASSERT_EQUAL( 1, td_task_getYieldCount() );

    TEST_ASSERT_EQUAL( 1, td_task_getCount_vPortYieldWithinAPI() );


    vQueueDelete( xQueue );
}

/**
 * @brief Test xQueueReceive with an occupied queue with a lower priority task waiting which does not modify the queue.
 * @coverage xQueueReceive
 */
void test_xQueueReceive_noop_waiting_lower_priority( void )
{
    /* Create a new queue */
    QueueHandle_t xQueue = xQueueCreate( 1, sizeof( uint32_t ) );

    /* Add a value to the queue */
    uint32_t testVal = getNextMonotonicTestValue();

    ( void ) xQueueSend( xQueue, &testVal, 0 );

    /* Insert an item into the event list */
    td_task_setFakeTaskPriority( DEFAULT_PRIORITY - 1 );
    td_task_addFakeTaskWaitingToSendToQueue( xQueue );

    uint32_t checkVal = INVALID_UINT32;

    TEST_ASSERT_EQUAL( 1, uxQueueMessagesWaiting( xQueue ) );

    /* receive from the queue */
    TEST_ASSERT_EQUAL( pdTRUE, xQueueReceive( xQueue, &checkVal, 0 ) );
    TEST_ASSERT_EQUAL( testVal, checkVal );

    TEST_ASSERT_EQUAL( 0, uxQueueMessagesWaiting( xQueue ) );

    TEST_ASSERT_EQUAL( 0, td_task_getYieldCount() );

    vQueueDelete( xQueue );
}

/**
 *  @brief Test xQueueReceive with taskSCHEDULER_SUSPENDED and timeout=0
 *  @details This should not cause xQueueReceive to configASSERT because
 *  xQueueReceive is non-blocking when timeout=0.
 *  @coverage xQueueReceive
 */
void test_xQueueReceive_nonblocking_suspended_noassert( void )
{
    QueueHandle_t xQueue = xQueueCreate( 1, sizeof( uint32_t ) );

    uint32_t checkVal = INVALID_UINT32;

    td_task_setSchedulerState( taskSCHEDULER_SUSPENDED );

    TEST_ASSERT_EQUAL( pdFALSE, xQueueReceive( xQueue, &checkVal, 0 ) );

    td_task_setSchedulerState( taskSCHEDULER_RUNNING );

    vQueueDelete( xQueue );
}

/**
 * @brief Test xQueueReceiveFromISR with an invalid QueueHandle
 * @coverage xQueueReceiveFromISR
 */
void test_xQueueReceiveFromISR_invalid_handle( void )
{
    EXPECT_ASSERT_BREAK( xQueueReceiveFromISR( NULL, NULL, NULL ) );
}

/**
 * @brief Test xQueueReceiveFromISR with a full queue of length 1, items size 0
 * @coverage xQueueReceiveFromISR
 */
void test_xQueueReceiveFromISR_zeroItemSize_noassert_full( void )
{
    /* Create a new queue */
    QueueHandle_t xQueue = xQueueCreate( 1, 0 );

    ( void ) xQueueSend( xQueue, NULL, 0 );

    TEST_ASSERT_EQUAL( 1, uxQueueMessagesWaiting( xQueue ) );

    /* receive from the queue while full */
    TEST_ASSERT_EQUAL( pdTRUE, xQueueReceiveFromISR( xQueue, NULL, NULL ) );

    TEST_ASSERT_EQUAL( 0, uxQueueMessagesWaiting( xQueue ) );

    vQueueDelete( xQueue );
}

/**
 * @brief Test xQueueReceiveFromISR with a null pvBuffer on an empty queue of length 1, items size 4
 * @coverage xQueueReceiveFromISR
 */
void test_xQueueReceiveFromISR_fourItemSize_nullptr_assert_empty( void )
{
    /* Create a new queue */
    QueueHandle_t xQueue = xQueueCreate( 1, sizeof( uint32_t ) );

    /* Expect an assertion failure due to the null pointer passed into xqueuePeekFromISR */
    fakeAssertExpectFail();

    /* receive from the queue with a nullptr storage location */
    TEST_ASSERT_EQUAL( pdFALSE, xQueueReceiveFromISR( xQueue, NULL, NULL ) );

    TEST_ASSERT_EQUAL( true, fakeAssertGetFlagAndClear() );

    vQueueDelete( xQueue );
}

/**
 * @brief Test xQueueReceiveFromISR with a null pvBuffer on a full queue of length 1, items size 4
 * @coverage xQueueReceiveFromISR
 */
void test_xQueueReceiveFromISR_fourItemSize_nullptr_assert_full( void )
{
    /* Create a new queue */
    QueueHandle_t xQueue = xQueueCreate( 1, sizeof( uint32_t ) );

    uint32_t testVal = getNextMonotonicTestValue();

    ( void ) xQueueSend( xQueue, &testVal, 0 );

    /* receive from the queue with a nullptr storage location */
    EXPECT_ASSERT_BREAK( xQueueReceiveFromISR( xQueue, NULL, NULL ) );

    vQueueDelete( xQueue );
}

/**
 * @brief Test xQueueReceiveFromISR with an empty queue
 * @coverage xQueueReceiveFromISR
 */
void test_xQueueReceiveFromISR_fail_empty( void )
{
    /* Create a new queue */
    QueueHandle_t xQueue = xQueueCreate( 1, sizeof( uint32_t ) );

    uint32_t checkVal = INVALID_UINT32;

    /* receive from the queue while empty */
    TEST_ASSERT_EQUAL( pdFALSE, xQueueReceiveFromISR( xQueue, &checkVal, NULL ) );

    vQueueDelete( xQueue );
}

/**
 * @brief Test xQueueReceiveFromISR with an occupied queue
 * @coverage xQueueReceiveFromISR
 */
void test_xQueueReceiveFromISR_success( void )
{
    /* Create a new queue */
    QueueHandle_t xQueue = xQueueCreate( 1, sizeof( uint32_t ) );

    uint32_t testVal = getNextMonotonicTestValue();

    ( void ) xQueueSend( xQueue, &testVal, 0 );

    uint32_t checkVal = INVALID_UINT32;

    TEST_ASSERT_EQUAL( 1, uxQueueMessagesWaiting( xQueue ) );

    /* receive from the queue while full */
    TEST_ASSERT_EQUAL( pdTRUE, xQueueReceiveFromISR( xQueue, &checkVal, NULL ) );
    TEST_ASSERT_EQUAL( testVal, checkVal );

    TEST_ASSERT_EQUAL( 0, uxQueueMessagesWaiting( xQueue ) );

    vQueueDelete( xQueue );
}

/**
 * @brief Test xQueueReceiveFromISR on a queue that is locked
 * @coverage xQueueReceiveFromISR
 */
void test_xQueueReceiveFromISR_locked( void )
{
    /* Create a new queue */
    QueueHandle_t xQueue = xQueueCreate( 2, sizeof( uint32_t ) );

    /* Send a test value so the queue is not empty */
    uint32_t testVal = getNextMonotonicTestValue();

    ( void ) xQueueSend( xQueue, &testVal, 0 );
    ( void ) xQueueSend( xQueue, &testVal, 0 );

    uxTaskGetNumberOfTasks_IgnoreAndReturn( 1 );

    /* Set private lock counters */
    vSetQueueRxLock( xQueue, queueLOCKED_UNMODIFIED );
    vSetQueueTxLock( xQueue, queueLOCKED_UNMODIFIED );

    TEST_ASSERT_EQUAL( 2, uxQueueMessagesWaiting( xQueue ) );

    uint32_t checkVal = INVALID_UINT32;

    /* Run xQueueReceiveFromISR with the queue locked */
    TEST_ASSERT_EQUAL( pdTRUE, xQueueReceiveFromISR( xQueue, &checkVal, NULL ) );
    TEST_ASSERT_EQUAL( pdTRUE, xQueueReceiveFromISR( xQueue, &checkVal, NULL ) );

    TEST_ASSERT_EQUAL( 0, uxQueueMessagesWaiting( xQueue ) );

    /* Verify that the cRxLock counter has only been incremented by one
     * even after 2 calls to xQueueReceiveFromISR because there is only
     * one task in the system as returned from uxTaskGetNumberOfTasks. */
    TEST_ASSERT_EQUAL( queueLOCKED_UNMODIFIED + 1, cGetQueueRxLock( xQueue ) );

    /* Verify that the cTxLock counter has not changed */
    TEST_ASSERT_EQUAL( queueLOCKED_UNMODIFIED, cGetQueueTxLock( xQueue ) );

    vQueueDelete( xQueue );
}

/**
 * @brief Test xQueueReceiveFromISR on a queue that is locked and cRxLock overflows.
 * @coverage xQueueReceiveFromISR
 */
void test_xQueueReceiveFromISR_locked_overflow( void )
{
    /* Create a new queue */
    QueueHandle_t xQueue = xQueueCreate( 1, sizeof( uint32_t ) );

    /* Send a test value so the queue is not empty */
    uint32_t testVal = getNextMonotonicTestValue();

    ( void ) xQueueSend( xQueue, &testVal, 0 );

    /* Set private lock counters */
    vSetQueueRxLock( xQueue, INT8_MAX );
    vSetQueueTxLock( xQueue, INT8_MAX );

    uint32_t checkVal = INVALID_UINT32;

    /* The number of tasks need to be more than 127 to trigger the
     * overflow assertion. */
    uxTaskGetNumberOfTasks_IgnoreAndReturn( 128 );

    /* Expect an assertion since the cRxLock value has overflowed */
    fakeAssertExpectFail();

    TEST_ASSERT_EQUAL( 1, uxQueueMessagesWaiting( xQueue ) );

    /* Run xQueueReceiveFromISR with the queue locked */
    TEST_ASSERT_EQUAL( pdTRUE, xQueueReceiveFromISR( xQueue, &checkVal, NULL ) );

    TEST_ASSERT_EQUAL( 0, uxQueueMessagesWaiting( xQueue ) );

    TEST_ASSERT_EQUAL( testVal, checkVal );

    /* Verify that the cRxLock counter has been incremented and overflowed */
    TEST_ASSERT_EQUAL( INT8_MIN, cGetQueueRxLock( xQueue ) );

    /* Verify that the cTxLock counter has not changed */
    TEST_ASSERT_EQUAL( INT8_MAX, cGetQueueTxLock( xQueue ) );

    TEST_ASSERT_EQUAL( true, fakeAssertGetFlagAndClear() );

    vQueueDelete( xQueue );
}

/**
 * @brief Test xQueueReceiveFromISR with an occupied queue with higher priority tasks waiting.
 * @details also verify that calling xQueueReceiveFromISR with a NULL pxHigherPriorityTaskWoken does not cause invalid memory access.
 * @coverage xQueueReceiveFromISR
 */
void test_xQueueReceiveFromISR_tasks_waiting_higher_priority_success( void )
{
    /* Create a new queue */
    QueueHandle_t xQueue = xQueueCreate( 1, sizeof( uint32_t ) );

    /* Add a value to the queue */
    uint32_t testVal = getNextMonotonicTestValue();

    ( void ) xQueueSend( xQueue, &testVal, 0 );

    /* set up mocks for this test case */
    vFakePortAssertIfInterruptPriorityInvalid_Expect();

    /* Insert an item into the event list */
    td_task_setFakeTaskPriority( DEFAULT_PRIORITY + 1 );
    td_task_addFakeTaskWaitingToSendToQueue( xQueue );

    uint32_t checkVal = INVALID_UINT32;

    TEST_ASSERT_EQUAL( 1, uxQueueMessagesWaiting( xQueue ) );

    /* receive from the queue */
    TEST_ASSERT_EQUAL( pdTRUE, xQueueReceiveFromISR( xQueue, &checkVal, NULL ) );
    TEST_ASSERT_EQUAL( testVal, checkVal );

    TEST_ASSERT_EQUAL( 0, uxQueueMessagesWaiting( xQueue ) );

    TEST_ASSERT_EQUAL( 1, td_task_getYieldPending() );

    vQueueDelete( xQueue );
}

/**
 * @brief Test xQueueReceiveFromISR with an occupied queue and verify that the returned pxHigherPriorityTaskWoken value has been set accordingly.
 * @coverage xQueueReceiveFromISR
 */
void test_xQueueReceiveFromISR_tasks_waiting_higher_priority_check_pxHigherPriorityTaskWoken( void )
{
    /* Create a new queue */
    QueueHandle_t xQueue = xQueueCreate( 1, sizeof( uint32_t ) );

    /* Add a value to the queue */
    uint32_t testVal = getNextMonotonicTestValue();

    ( void ) xQueueSend( xQueue, &testVal, 0 );

    /* set up mocks for this test case */
    vFakePortAssertIfInterruptPriorityInvalid_Expect();

    /* Insert an item into the event list */
    td_task_setFakeTaskPriority( DEFAULT_PRIORITY + 1 );
    td_task_addFakeTaskWaitingToSendToQueue( xQueue );

    uint32_t checkVal = INVALID_UINT32;

    BaseType_t xHigherPriorityTaskWoken = false;

    TEST_ASSERT_EQUAL( 1, uxQueueMessagesWaiting( xQueue ) );

    /* receive from the queue */
    TEST_ASSERT_EQUAL( pdTRUE, xQueueReceiveFromISR( xQueue, &checkVal, &xHigherPriorityTaskWoken ) );

    TEST_ASSERT_EQUAL( true, xHigherPriorityTaskWoken );

    TEST_ASSERT_EQUAL( testVal, checkVal );

    TEST_ASSERT_EQUAL( 0, uxQueueMessagesWaiting( xQueue ) );

    TEST_ASSERT_EQUAL( 1, td_task_getYieldPending() );

    vQueueDelete( xQueue );
}

/**
 * @brief Test xQueueReceiveFromISR with an occupied queue with a lower priority task waiting.
 * @coverage xQueueReceiveFromISR
 */
void test_xQueueReceiveFromISR_tasks_waiting_lower_priority_success( void )
{
    /* Create a new queue */
    QueueHandle_t xQueue = xQueueCreate( 1, sizeof( uint32_t ) );

    /* Add a value to the queue */
    uint32_t testVal = getNextMonotonicTestValue();

    ( void ) xQueueSend( xQueue, &testVal, 0 );

    /* set up mocks for this test case */
    vFakePortAssertIfInterruptPriorityInvalid_Expect();

    /* Insert an item into the event list */
    td_task_setFakeTaskPriority( DEFAULT_PRIORITY - 1 );
    td_task_addFakeTaskWaitingToSendToQueue( xQueue );

    uint32_t checkVal = INVALID_UINT32;

    BaseType_t xHigherPriorityTaskWoken = false;

    TEST_ASSERT_EQUAL( 1, uxQueueMessagesWaiting( xQueue ) );

    /* receive from the queue */
    TEST_ASSERT_EQUAL( pdTRUE, xQueueReceiveFromISR( xQueue, &checkVal, &xHigherPriorityTaskWoken ) );

    TEST_ASSERT_EQUAL( 0, uxQueueMessagesWaiting( xQueue ) );

    TEST_ASSERT_EQUAL( false, xHigherPriorityTaskWoken );

    TEST_ASSERT_EQUAL( testVal, checkVal );

    vQueueDelete( xQueue );
}
