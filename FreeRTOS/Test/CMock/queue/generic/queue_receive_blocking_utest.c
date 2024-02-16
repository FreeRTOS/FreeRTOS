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
/*! @file queue_receive_blocking_utest.c */

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
/* ============================  GLOBAL VARIABLES =========================== */

/* Used to share a QueueHandle_t between a test case and it's callbacks */
static QueueHandle_t xQueueHandleStatic;

/* ==========================  CALLBACK FUNCTIONS =========================== */

/* ============================= Unity Fixtures ============================= */

void setUp( void )
{
    commonSetUp();
    vFakePortAssertIfInterruptPriorityInvalid_Ignore();
    xQueueHandleStatic = NULL;
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
 *  @brief Callback for test_xQueueReceive_blocking_success_locked_no_pending
 *  which adds an item to it's test queue.
 */
static BaseType_t xQueueReceive_xTaskCheckForTimeOutCB( TimeOut_t * const pxTimeOut,
                                                        TickType_t * const pxTicksToWait,
                                                        int cmock_num_calls )
{
    BaseType_t xReturnValue = td_task_xTaskCheckForTimeOutStub( pxTimeOut, pxTicksToWait, cmock_num_calls );

    if( cmock_num_calls == NUM_CALLS_TO_INTERCEPT )
    {
        uint32_t testVal = getNextMonotonicTestValue();
        TEST_ASSERT_TRUE( xQueueSendFromISR( xQueueHandleStatic, &testVal, NULL ) );
        TEST_ASSERT_EQUAL( 1, uxQueueMessagesWaiting( xQueueHandleStatic ) );
    }

    return xReturnValue;
}

/**
 *  @brief Test a blocking call to xQueueReceive with a locked queue.
 *  @details Test a blocking call to xQueueReceive with a locked queue with no
 *  tasks in the queue WaitingToReceiveFrom event list.
 *  @coverage xQueueReceive prvUnlockQueue
 */
void test_xQueueReceive_blocking_success_locked_no_pending( void )
{
    QueueHandle_t xQueue = xQueueCreate( 1, sizeof( uint32_t ) );

    /* Export for callbacks */
    xQueueHandleStatic = xQueue;

    xTaskCheckForTimeOut_Stub( &xQueueReceive_xTaskCheckForTimeOutCB );
    xTaskResumeAll_Stub( &td_task_xTaskResumeAllStub );
    uxTaskGetNumberOfTasks_IgnoreAndReturn( 1 );
    vTaskYieldWithinAPI_Stub( vTaskYieldWithinAPI_Callback );

    uint32_t checkVal = INVALID_UINT32;

    TEST_ASSERT_EQUAL( pdTRUE, xQueueReceive( xQueue, &checkVal, TICKS_TO_WAIT ) );

    TEST_ASSERT_EQUAL( 0, uxQueueMessagesWaiting( xQueue ) );

    TEST_ASSERT_EQUAL( NUM_CALLS_TO_INTERCEPT, td_task_getYieldCount() );

    TEST_ASSERT_EQUAL( NUM_CALLS_TO_INTERCEPT, td_task_getCount_vPortYieldWithinAPI() );

    TEST_ASSERT_EQUAL( getLastMonotonicTestValue(), checkVal );

    vQueueDelete( xQueue );
}

/**
 *  @brief Test a blocking call to xQueuePeek with a locked queue.
 *  @details Test a blocking call to xQueuePeek with a locked queue with no tasks
 *  in the queue WaitingToReceiveFrom event list.
 *  @coverage xQueuePeek prvUnlockQueue
 */
void test_xQueuePeek_blocking_success_locked_no_pending( void )
{
    QueueHandle_t xQueue = xQueueCreate( 1, sizeof( uint32_t ) );

    /* Export for callbacks */
    xQueueHandleStatic = xQueue;

    xTaskCheckForTimeOut_Stub( &xQueueReceive_xTaskCheckForTimeOutCB );
    xTaskResumeAll_Stub( &td_task_xTaskResumeAllStub );
    uxTaskGetNumberOfTasks_IgnoreAndReturn( 1 );
    vTaskYieldWithinAPI_Stub( vTaskYieldWithinAPI_Callback );

    uint32_t checkVal = INVALID_UINT32;

    TEST_ASSERT_EQUAL( pdTRUE, xQueuePeek( xQueue, &checkVal, TICKS_TO_WAIT ) );

    TEST_ASSERT_EQUAL( 1, uxQueueMessagesWaiting( xQueue ) );

    TEST_ASSERT_EQUAL( NUM_CALLS_TO_INTERCEPT, td_task_getYieldCount() );

    TEST_ASSERT_EQUAL( NUM_CALLS_TO_INTERCEPT, td_task_getCount_vPortYieldWithinAPI() );

    TEST_ASSERT_EQUAL( getLastMonotonicTestValue(), checkVal );

    vQueueDelete( xQueue );
}

/**
 * @brief Callback for xTaskResumeAll used by tests for blocking calls to
 * xQueueReceive and xQueuePeek
 */
static BaseType_t xQueueReceive_xTaskResumeAllCallback( int cmock_num_calls )
{
    BaseType_t xReturnValue = td_task_xTaskResumeAllStub( cmock_num_calls );

    /* If td_task_xTaskResumeAllStub returns pdTRUE, a higher priority task is pending
     * Receive from an ISR to block */
    if( pdTRUE == xReturnValue )
    {
        if( cmock_num_calls == NUM_CALLS_TO_INTERCEPT )
        {
            uint32_t checkValue = INVALID_UINT32;
            TEST_ASSERT_EQUAL( 1, uxQueueMessagesWaiting( xQueueHandleStatic ) );
            TEST_ASSERT_TRUE( xQueueReceiveFromISR( xQueueHandleStatic, &checkValue, NULL ) );
            TEST_ASSERT_EQUAL( getLastMonotonicTestValue(), checkValue );
        }
    }

    return xReturnValue;
}

/**
 *  @brief Test a blocking call to xQueueReceive with a locked queue.
 *  @details Test a blocking call to xQueueReceive with a locked queue with a
 *  higher priority task in the queue WaitingToReceiveFrom event list.
 *  @coverage xQueueReceive prvUnlockQueue
 */
void test_xQueueReceive_blocking_timeout_locked_high_prio_pending( void )
{
    QueueHandle_t xQueue = xQueueCreate( 1, sizeof( uint32_t ) );

    /* Export for callbacks */
    xQueueHandleStatic = xQueue;

    xTaskCheckForTimeOut_Stub( &xQueueReceive_xTaskCheckForTimeOutCB );
    xTaskResumeAll_Stub( &xQueueReceive_xTaskResumeAllCallback );
    uxTaskGetNumberOfTasks_IgnoreAndReturn( 1 );
    vTaskYieldWithinAPI_Stub( vTaskYieldWithinAPI_Callback );

    td_task_setFakeTaskPriority( DEFAULT_PRIORITY + 1 );

    td_task_addFakeTaskWaitingToReceiveFromQueue( xQueue );

    uint32_t checkVal = INVALID_UINT32;

    TEST_ASSERT_EQUAL( pdFALSE, xQueueReceive( xQueue, &checkVal, TICKS_TO_WAIT ) );

    TEST_ASSERT_EQUAL( 0, uxQueueMessagesWaiting( xQueue ) );

    TEST_ASSERT_EQUAL( TICKS_TO_WAIT, td_task_getYieldCount() );

    TEST_ASSERT_EQUAL( NUM_CALLS_TO_INTERCEPT + 1, td_task_getCount_YieldFromTaskResumeAll() );

    TEST_ASSERT_EQUAL( NUM_CALLS_TO_INTERCEPT - 1, td_task_getCount_vPortYieldWithinAPI() );

    TEST_ASSERT_EQUAL( 1, td_task_getCount_vTaskMissedYield() );

    TEST_ASSERT_EQUAL( INVALID_UINT32, checkVal );

    vQueueDelete( xQueue );
}

/**
 *  @brief Test a blocking call to xQueuePeek with a locked queue.
 *  @details Test a blocking call to xQueuePeek with a locked queue with a
 *  higher priority task in the queue WaitingToReceiveFrom event list.
 *  @coverage xQueuePeek prvUnlockQueue
 */
void test_xQueuePeek_blocking_timeout_locked_high_prio_pending( void )
{
    QueueHandle_t xQueue = xQueueCreate( 1, sizeof( uint32_t ) );

    /* Export for callbacks */
    xQueueHandleStatic = xQueue;

    xTaskCheckForTimeOut_Stub( &xQueueReceive_xTaskCheckForTimeOutCB );
    xTaskResumeAll_Stub( &xQueueReceive_xTaskResumeAllCallback );
    uxTaskGetNumberOfTasks_IgnoreAndReturn( 1 );
    vTaskYieldWithinAPI_Stub( vTaskYieldWithinAPI_Callback );

    td_task_setFakeTaskPriority( DEFAULT_PRIORITY + 1 );

    td_task_addFakeTaskWaitingToReceiveFromQueue( xQueue );

    uint32_t checkVal = INVALID_UINT32;

    TEST_ASSERT_EQUAL( pdFALSE, xQueuePeek( xQueue, &checkVal, TICKS_TO_WAIT ) );

    TEST_ASSERT_EQUAL( 0, uxQueueMessagesWaiting( xQueue ) );

    TEST_ASSERT_EQUAL( TICKS_TO_WAIT, td_task_getYieldCount() );

    TEST_ASSERT_EQUAL( NUM_CALLS_TO_INTERCEPT + 1, td_task_getCount_YieldFromTaskResumeAll() );

    TEST_ASSERT_EQUAL( NUM_CALLS_TO_INTERCEPT - 1, td_task_getCount_vPortYieldWithinAPI() );

    TEST_ASSERT_EQUAL( 1, td_task_getCount_vTaskMissedYield() );

    TEST_ASSERT_EQUAL( INVALID_UINT32, checkVal );

    vQueueDelete( xQueue );
}

/**
 *  @brief Test a blocking call to xQueueReceive with a locked queue.
 *  @details Test a blocking call to xQueueReceive with a locked queue with a
 *  lower priority task in the queue WaitingToReceiveFrom event list.
 *  @coverage xQueueReceive prvUnlockQueue
 */
void test_xQueueReceive_blocking_success_locked_low_prio_pending( void )
{
    QueueHandle_t xQueue = xQueueCreate( 1, sizeof( uint32_t ) );

    /* Export for callbacks */
    xQueueHandleStatic = xQueue;

    xTaskCheckForTimeOut_Stub( &xQueueReceive_xTaskCheckForTimeOutCB );
    xTaskResumeAll_Stub( &xQueueReceive_xTaskResumeAllCallback );
    uxTaskGetNumberOfTasks_IgnoreAndReturn( 1 );
    vTaskYieldWithinAPI_Stub( vTaskYieldWithinAPI_Callback );

    td_task_setFakeTaskPriority( DEFAULT_PRIORITY - 1 );

    td_task_addFakeTaskWaitingToReceiveFromQueue( xQueue );

    uint32_t checkVal = INVALID_UINT32;

    TEST_ASSERT_EQUAL( pdTRUE, xQueueReceive( xQueue, &checkVal, TICKS_TO_WAIT ) );

    TEST_ASSERT_EQUAL( 0, uxQueueMessagesWaiting( xQueue ) );

    TEST_ASSERT_EQUAL( NUM_CALLS_TO_INTERCEPT, td_task_getYieldCount() );

    TEST_ASSERT_EQUAL( NUM_CALLS_TO_INTERCEPT, td_task_getCount_vPortYieldWithinAPI() );

    TEST_ASSERT_EQUAL( getLastMonotonicTestValue(), checkVal );

    vQueueDelete( xQueue );
}

/**
 *  @brief Test a blocking call to xQueuePeek with a locked queue.
 *  @details Test a blocking call to xQueuePeek with a locked queue with a
 *  lower priority task in the queue WaitingToReceiveFrom event list.
 *  @coverage xQueuePeek prvUnlockQueue
 */
void test_xQueuePeek_blocking_success_locked_low_prio_pending( void )
{
    QueueHandle_t xQueue = xQueueCreate( 1, sizeof( uint32_t ) );

    /* Export for callbacks */
    xQueueHandleStatic = xQueue;

    xTaskCheckForTimeOut_Stub( &xQueueReceive_xTaskCheckForTimeOutCB );
    xTaskResumeAll_Stub( &xQueueReceive_xTaskResumeAllCallback );
    uxTaskGetNumberOfTasks_IgnoreAndReturn( 1 );
    vTaskYieldWithinAPI_Stub( vTaskYieldWithinAPI_Callback );

    td_task_setFakeTaskPriority( DEFAULT_PRIORITY - 1 );

    td_task_addFakeTaskWaitingToReceiveFromQueue( xQueue );

    uint32_t checkVal = INVALID_UINT32;

    TEST_ASSERT_EQUAL( pdTRUE, xQueuePeek( xQueue, &checkVal, TICKS_TO_WAIT ) );

    TEST_ASSERT_EQUAL( 1, uxQueueMessagesWaiting( xQueue ) );

    TEST_ASSERT_EQUAL( NUM_CALLS_TO_INTERCEPT, td_task_getYieldCount() );

    TEST_ASSERT_EQUAL( NUM_CALLS_TO_INTERCEPT, td_task_getCount_vPortYieldWithinAPI() );

    TEST_ASSERT_EQUAL( getLastMonotonicTestValue(), checkVal );

    vQueueDelete( xQueue );
}

/**
 *  @brief Test xQueuePeek with taskSCHEDULER_SUSPENDED and timeout=10
 *  @details This should cause xQueuePeek to configASSERT because it would
 *  block forever when the queue is empty.
 *  @coverage xQueuePeek
 */
void test_xQueuePeek_blocking_suspended_assert( void )
{
    QueueHandle_t xQueue = xQueueCreate( 1, sizeof( uint32_t ) );

    td_task_setSchedulerState( taskSCHEDULER_SUSPENDED );

    vTaskSuspendAll_Stub( td_task_vTaskSuspendAllStubNoCheck );
    vTaskYieldWithinAPI_Stub( vTaskYieldWithinAPI_Callback );

    uint32_t checkVal = INVALID_UINT32;

    fakeAssertExpectFail();

    TEST_ASSERT_EQUAL( pdFALSE, xQueuePeek( xQueue, &checkVal, TICKS_TO_WAIT ) );

    TEST_ASSERT_EQUAL( 0, uxQueueMessagesWaiting( xQueue ) );

    TEST_ASSERT_EQUAL( pdTRUE, fakeAssertGetFlagAndClear() );

    TEST_ASSERT_EQUAL( TICKS_TO_WAIT, td_task_getYieldCount() );

    TEST_ASSERT_EQUAL( TICKS_TO_WAIT, td_task_getCount_vPortYieldWithinAPI() );

    td_task_setSchedulerState( taskSCHEDULER_RUNNING );

    vQueueDelete( xQueue );
}

/**
 *  @brief Callback which adds and item to it's test queue.
 *  @details Used in test_xQueuePeek_blocking_success and test_xQueueReceive_blocking_success.
 */
static BaseType_t blocking_success_xTaskCheckForTimeOut_cb( TimeOut_t * const pxTimeOut,
                                                            TickType_t * const pxTicksToWait,
                                                            int cmock_num_calls )
{
    BaseType_t xReturnValue = td_task_xTaskCheckForTimeOutStub( pxTimeOut, pxTicksToWait, cmock_num_calls );

    if( cmock_num_calls == NUM_CALLS_TO_INTERCEPT )
    {
        uint32_t testVal = getNextMonotonicTestValue();
        xQueueSend( xQueueHandleStatic, &testVal, 0 );
        TEST_ASSERT_EQUAL( 1, uxQueueMessagesWaiting( xQueueHandleStatic ) );
    }

    return xReturnValue;
}

/**
 * @brief Test xQueuePeek in blocking mode with a queue that is initially empty,
 * but later becomes full.
 * @coverage xQueuePeek
 */
void test_xQueuePeek_blocking_success( void )
{
    QueueHandle_t xQueue = xQueueCreate( 1, sizeof( uint32_t ) );

    /* Export for blocking_success_xTaskCheckForTimeOut_cb callback */
    xQueueHandleStatic = xQueue;

    xTaskCheckForTimeOut_Stub( &blocking_success_xTaskCheckForTimeOut_cb );
    vTaskYieldWithinAPI_Stub( vTaskYieldWithinAPI_Callback );

    uint32_t checkVal = INVALID_UINT32;

    TEST_ASSERT_EQUAL( pdTRUE, xQueuePeek( xQueue, &checkVal, TICKS_TO_WAIT ) );

    TEST_ASSERT_EQUAL( 1, uxQueueMessagesWaiting( xQueue ) );

    TEST_ASSERT_EQUAL( NUM_CALLS_TO_INTERCEPT, td_task_getYieldCount() );

    TEST_ASSERT_EQUAL( NUM_CALLS_TO_INTERCEPT, td_task_getCount_vPortYieldWithinAPI() );

    TEST_ASSERT_EQUAL( getLastMonotonicTestValue(), checkVal );
    vQueueDelete( xQueue );
}

/**
 *  @brief Callback which adds and item to it's test queue.
 *  @details used in test_xQueuePeek_blocking_success_last_chance and
 *  test_xQueueReceive_blocking_success_last_chance.
 */
static BaseType_t blocking_success_last_chance_xTaskCheckForTimeOut_cb( TimeOut_t * const pxTimeOut,
                                                                        TickType_t * const pxTicksToWait,
                                                                        int cmock_num_calls )
{
    BaseType_t xReturnValue = td_task_xTaskCheckForTimeOutStub( pxTimeOut, pxTicksToWait, cmock_num_calls );

    if( cmock_num_calls == TICKS_TO_WAIT )
    {
        uint32_t testVal = getNextMonotonicTestValue();
        xQueueSend( xQueueHandleStatic, &testVal, 0 );
    }

    return xReturnValue;
}

/**
 * @brief Test xQueuePeek in blocking mode with a queue that is initially empty,
 * but becomes full right before the last chance to remove data from the queue.
 * @coverage xQueuePeek
 */
void test_xQueuePeek_blocking_success_last_chance( void )
{
    QueueHandle_t xQueue = xQueueCreate( 1, sizeof( uint32_t ) );

    /* Export for blocking_success_xTaskCheckForTimeOut_cb callback */
    xQueueHandleStatic = xQueue;

    xTaskCheckForTimeOut_Stub( &blocking_success_last_chance_xTaskCheckForTimeOut_cb );
    vTaskYieldWithinAPI_Stub( vTaskYieldWithinAPI_Callback );

    uint32_t checkVal = INVALID_UINT32;

    TEST_ASSERT_EQUAL( pdTRUE, xQueuePeek( xQueue, &checkVal, TICKS_TO_WAIT ) );

    TEST_ASSERT_EQUAL( 1, uxQueueMessagesWaiting( xQueue ) );

    TEST_ASSERT_EQUAL( TICKS_TO_WAIT, td_task_getYieldCount() );

    TEST_ASSERT_EQUAL( TICKS_TO_WAIT, td_task_getCount_vPortYieldWithinAPI() );

    TEST_ASSERT_EQUAL( getLastMonotonicTestValue(), checkVal );

    vQueueDelete( xQueue );
}

/**
 * @brief Test xQueuePeek in blocking mode with an empty queue.
 * @coverage xQueuePeek
 */
void test_xQueuePeek_blocking_timeout( void )
{
    QueueHandle_t xQueue = xQueueCreate( 1, sizeof( uint32_t ) );

    uint32_t checkVal = INVALID_UINT32;

    vTaskYieldWithinAPI_Stub( vTaskYieldWithinAPI_Callback );

    TEST_ASSERT_EQUAL( pdFALSE, xQueuePeek( xQueue, &checkVal, TICKS_TO_WAIT ) );

    TEST_ASSERT_EQUAL( 0, uxQueueMessagesWaiting( xQueue ) );

    TEST_ASSERT_EQUAL( TICKS_TO_WAIT, td_task_getYieldCount() );

    TEST_ASSERT_EQUAL( TICKS_TO_WAIT, td_task_getCount_vPortYieldWithinAPI() );

    vQueueDelete( xQueue );
}

/**
 *  @brief Test xQueueReceive with taskSCHEDULER_SUSPENDED and timeout=10
 *  @details This should cause xQueueReceive to configASSERT because it would
 *  block forever when the queue is empty.
 *  @coverage xQueueReceive
 */
void test_xQueueReceive_blocking_suspended_assert( void )
{
    QueueHandle_t xQueue = xQueueCreate( 1, sizeof( uint32_t ) );

    uint32_t checkVal = INVALID_UINT32;

    fakeAssertExpectFail();
    vTaskYieldWithinAPI_Stub( vTaskYieldWithinAPI_Callback );

    td_task_setSchedulerState( taskSCHEDULER_SUSPENDED );

    vTaskSuspendAll_Stub( td_task_vTaskSuspendAllStubNoCheck );

    TEST_ASSERT_EQUAL( pdFALSE, xQueueReceive( xQueue, &checkVal, TICKS_TO_WAIT ) );

    TEST_ASSERT_EQUAL( 0, uxQueueMessagesWaiting( xQueue ) );

    TEST_ASSERT_EQUAL( pdTRUE, fakeAssertGetFlagAndClear() );

    TEST_ASSERT_EQUAL( TICKS_TO_WAIT, td_task_getYieldCount() );

    TEST_ASSERT_EQUAL( TICKS_TO_WAIT, td_task_getCount_vPortYieldWithinAPI() );

    td_task_setSchedulerState( taskSCHEDULER_RUNNING );

    vQueueDelete( xQueue );
}

/**
 * @brief Test xQueueReceive in blocking mode with an occupied queue
 * @coverage xQueueReceive
 */
void test_xQueueReceive_blocking_success( void )
{
    QueueHandle_t xQueue = xQueueCreate( 1, sizeof( uint32_t ) );

    /* Export for blocking_success_xTaskCheckForTimeOut_cb callback */
    xQueueHandleStatic = xQueue;

    xTaskCheckForTimeOut_Stub( &blocking_success_xTaskCheckForTimeOut_cb );
    vTaskYieldWithinAPI_Stub( vTaskYieldWithinAPI_Callback );

    uint32_t checkVal = INVALID_UINT32;

    TEST_ASSERT_EQUAL( pdTRUE, xQueueReceive( xQueue, &checkVal, TICKS_TO_WAIT ) );

    TEST_ASSERT_EQUAL( 0, uxQueueMessagesWaiting( xQueue ) );

    TEST_ASSERT_EQUAL( getLastMonotonicTestValue(), checkVal );

    TEST_ASSERT_EQUAL( NUM_CALLS_TO_INTERCEPT, td_task_getYieldCount() );

    TEST_ASSERT_EQUAL( NUM_CALLS_TO_INTERCEPT, td_task_getCount_vPortYieldWithinAPI() );

    vQueueDelete( xQueue );
}


/**
 * @brief Test xQueueReceive in blocking mode with a queue that is initially empty,
 * but becomes full right before the last chance to remove data from the queue.
 * @coverage xQueueReceive
 */
void test_xQueueReceive_blocking_success_last_chance( void )
{
    QueueHandle_t xQueue = xQueueCreate( 1, sizeof( uint32_t ) );

    /* Export for blocking_success_xTaskCheckForTimeOut_cb callback */
    xQueueHandleStatic = xQueue;

    xTaskCheckForTimeOut_Stub( &blocking_success_last_chance_xTaskCheckForTimeOut_cb );
    vTaskYieldWithinAPI_Stub( vTaskYieldWithinAPI_Callback );

    uint32_t checkVal = INVALID_UINT32;

    TEST_ASSERT_EQUAL( pdTRUE, xQueueReceive( xQueue, &checkVal, TICKS_TO_WAIT ) );

    TEST_ASSERT_EQUAL( 0, uxQueueMessagesWaiting( xQueue ) );

    TEST_ASSERT_EQUAL( getLastMonotonicTestValue(), checkVal );

    TEST_ASSERT_EQUAL( TICKS_TO_WAIT, td_task_getYieldCount() );

    TEST_ASSERT_EQUAL( TICKS_TO_WAIT, td_task_getCount_vPortYieldWithinAPI() );

    vQueueDelete( xQueue );
}

/**
 * @brief Test xQueueReceive in blocking mode with an empty queue
 * @coverage xQueueReceive
 */
void test_xQueueReceive_blocking_timeout( void )
{
    QueueHandle_t xQueue = xQueueCreate( 1, sizeof( uint32_t ) );

    uint32_t checkVal = INVALID_UINT32;

    vTaskYieldWithinAPI_Stub( vTaskYieldWithinAPI_Callback );

    TEST_ASSERT_EQUAL( pdFALSE, xQueueReceive( xQueue, &checkVal, TICKS_TO_WAIT ) );

    TEST_ASSERT_EQUAL( 0, uxQueueMessagesWaiting( xQueue ) );

    TEST_ASSERT_EQUAL( TICKS_TO_WAIT, td_task_getYieldCount() );

    TEST_ASSERT_EQUAL( TICKS_TO_WAIT, td_task_getCount_vPortYieldWithinAPI() );

    vQueueDelete( xQueue );
}

/**
 * @brief Test xQueueReceive in blocking mode with an empty locked queue.
 * @details This test case verifies a situation that should never occur
 * ( xQueueReceive called on a locked queue ).
 * @coverage xQueueReceive
 */
void test_xQueueReceive_blocking_locked( void )
{
    /* Create a new binary Queue */
    QueueHandle_t xQueue = xQueueCreate( 1, sizeof( uint32_t ) );

    /* Set private lock counters */
    vSetQueueRxLock( xQueue, queueLOCKED_UNMODIFIED );
    vSetQueueTxLock( xQueue, queueLOCKED_UNMODIFIED );

    uint32_t checkVal = INVALID_UINT32;

    vTaskYieldWithinAPI_Stub( vTaskYieldWithinAPI_Callback );

    /* Run xQueueReceive in blocking mode with the queue locked */
    TEST_ASSERT_EQUAL( pdFALSE, xQueueReceive( xQueue, &checkVal, TICKS_TO_WAIT ) );

    TEST_ASSERT_EQUAL( 0, uxQueueMessagesWaiting( xQueue ) );

    TEST_ASSERT_EQUAL( TICKS_TO_WAIT, td_task_getYieldCount() );

    TEST_ASSERT_EQUAL( TICKS_TO_WAIT, td_task_getCount_vPortYieldWithinAPI() );

    /* Verify that the queue is now unlocked */
    TEST_ASSERT_EQUAL( queueUNLOCKED, cGetQueueRxLock( xQueue ) );
    TEST_ASSERT_EQUAL( queueUNLOCKED, cGetQueueTxLock( xQueue ) );

    vQueueDelete( xQueue );
}

/**
 * @brief Test xQueuePeek in blocking mode with an empty locked queue.
 * @details This test case verifies a situation that should never occur
 * ( xQueuePeek called on a locked queue ).
 * @coverage xQueuePeek
 */
void test_xQueuePeek_blocking_locked( void )
{
    vTaskYieldWithinAPI_Stub( vTaskYieldWithinAPI_Callback );

    /* Create a new binary Queue */
    QueueHandle_t xQueue = xQueueCreate( 1, sizeof( uint32_t ) );

    /* Set private lock counters */
    vSetQueueRxLock( xQueue, queueLOCKED_UNMODIFIED );
    vSetQueueTxLock( xQueue, queueLOCKED_UNMODIFIED );

    uint32_t checkVal = INVALID_UINT32;

    /* Run xQueueReceive in blocking mode with the queue locked */
    TEST_ASSERT_EQUAL( pdFALSE, xQueuePeek( xQueue, &checkVal, TICKS_TO_WAIT ) );



    TEST_ASSERT_EQUAL( TICKS_TO_WAIT, td_task_getYieldCount() );

    TEST_ASSERT_EQUAL( TICKS_TO_WAIT, td_task_getCount_vPortYieldWithinAPI() );

    /* Verify that the queue is now unlocked */
    TEST_ASSERT_EQUAL( queueUNLOCKED, cGetQueueRxLock( xQueue ) );
    TEST_ASSERT_EQUAL( queueUNLOCKED, cGetQueueTxLock( xQueue ) );

    vQueueDelete( xQueue );
}
