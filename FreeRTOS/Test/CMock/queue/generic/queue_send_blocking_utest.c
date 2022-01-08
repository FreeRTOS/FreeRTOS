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
/*! @file queue_send_blocking_utest.c */

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

/* =============================  Test Cases ============================== */

/**
 *  @brief Callback for test_macro_xQueueSend_blocking_success which empties it's test queue.
 */
static BaseType_t xQueueSend_locked_xTaskCheckForTimeOutCB( TimeOut_t * const pxTimeOut,
                                                            TickType_t * const pxTicksToWait,
                                                            int cmock_num_calls )
{
    BaseType_t xReturnValue = td_task_xTaskCheckForTimeOutStub( pxTimeOut, pxTicksToWait, cmock_num_calls );

    if( cmock_num_calls == NUM_CALLS_TO_INTERCEPT )
    {
        uint32_t checkVal = INVALID_UINT32;
        ( void ) xQueueReceiveFromISR( xQueueHandleStatic, &checkVal, NULL );
        TEST_ASSERT_EQUAL( getLastMonotonicTestValue(), checkVal );
    }

    return xReturnValue;
}

/**
 *  @brief Test xQueueSend with timeout=10 on a full queue which is locked and
 *  has no tasks on it's WaitingToSend event list.
 *  @coverage prvUnlockQueue
 */
void test_macro_xQueueSend_blocking_success_locked_no_pending( void )
{
    QueueHandle_t xQueue = xQueueCreate( 1, sizeof( uint32_t ) );

    /* Export for callbacks */
    xQueueHandleStatic = xQueue;

    uint32_t testVal = getNextMonotonicTestValue();

    TEST_ASSERT_EQUAL( 0, uxQueueMessagesWaiting( xQueue ) );

    TEST_ASSERT_EQUAL( pdTRUE, xQueueSend( xQueue, &testVal, 0 ) );

    TEST_ASSERT_EQUAL( 1, uxQueueMessagesWaiting( xQueue ) );

    xTaskCheckForTimeOut_Stub( &xQueueSend_locked_xTaskCheckForTimeOutCB );
    xTaskResumeAll_Stub( &td_task_xTaskResumeAllStub );

    uint32_t testVal2 = getLastMonotonicTestValue() + 12345;

    TEST_ASSERT_EQUAL( pdTRUE, xQueueSend( xQueue, &testVal2, TICKS_TO_WAIT ) );

    TEST_ASSERT_EQUAL( NUM_CALLS_TO_INTERCEPT, td_task_getYieldCount() );

    /* Check that vPortYieldWithinAPI was called and would have yielded */
    TEST_ASSERT_EQUAL( NUM_CALLS_TO_INTERCEPT, td_task_getCount_vPortYieldWithinAPI() );

    /* Check that vTaskMissedYield was not called */
    TEST_ASSERT_EQUAL( 0, td_task_getCount_vTaskMissedYield() );

    vQueueDelete( xQueue );
}

/**
 *  @brief Callback used for xQueueSend blocking_locked tests.
 */
static BaseType_t xQueueSend_xTaskResumeAllCallback( int cmock_num_calls )
{
    BaseType_t xReturnValue = td_task_xTaskResumeAllStub( cmock_num_calls );

    /* If td_task_xTaskResumeAllStub returns pdTRUE, a higher priority task is pending
     * Send from an ISR to block */
    if( pdTRUE == xReturnValue )
    {
        if( cmock_num_calls == NUM_CALLS_TO_INTERCEPT )
        {
            uint32_t testVal = getNextMonotonicTestValue();
            ( void ) xQueueSendFromISR( xQueueHandleStatic, &testVal, NULL );
        }
    }

    return xReturnValue;
}

/**
 *  @brief Test xQueueSend with timeout=10 on a full queue which is locked and
 *  has a higher priority task on it's WaitingToSend event list.
 *  @coverage prvUnlockQueue
 */
void test_macro_xQueueSend_blocking_fail_locked_high_prio_pending( void )
{
    QueueHandle_t xQueue = xQueueCreate( 1, sizeof( uint32_t ) );

    /* Export for callbacks */
    xQueueHandleStatic = xQueue;

    uint32_t testVal = getNextMonotonicTestValue();

    TEST_ASSERT_EQUAL( pdTRUE, xQueueSend( xQueue, &testVal, 0 ) );

    xTaskCheckForTimeOut_Stub( &xQueueSend_locked_xTaskCheckForTimeOutCB );
    xTaskResumeAll_Stub( &xQueueSend_xTaskResumeAllCallback );

    /* this task is lower priority than the pending task */
    td_task_setFakeTaskPriority( DEFAULT_PRIORITY + 1 );

    td_task_addFakeTaskWaitingToSendToQueue( xQueue );

    uint32_t testVal2 = getLastMonotonicTestValue() + 12345;

    TEST_ASSERT_EQUAL( 1, uxQueueMessagesWaiting( xQueue ) );

    TEST_ASSERT_EQUAL( pdFALSE, xQueueSend( xQueue, &testVal2, TICKS_TO_WAIT ) );

    TEST_ASSERT_EQUAL( 1, uxQueueMessagesWaiting( xQueue ) );

    TEST_ASSERT_EQUAL( TICKS_TO_WAIT, td_task_getYieldCount() );

    /* Check that xTaskResumeAll was called and would have yielded */
    TEST_ASSERT_EQUAL( NUM_CALLS_TO_INTERCEPT + 1, td_task_getCount_YieldFromTaskResumeAll() );

    /* Check that vPortYieldWithinAPI was called and would have yielded */
    TEST_ASSERT_EQUAL( NUM_CALLS_TO_INTERCEPT - 1, td_task_getCount_vPortYieldWithinAPI() );

    /* Check that vTaskMissedYield was called */
    TEST_ASSERT_EQUAL( 1, td_task_getCount_vTaskMissedYield() );

    vQueueDelete( xQueue );
}

/**
 *  @brief Test xQueueSend with timeout=10 on a full queue which is locked and
 *  has a lower priority task on it's WaitingToSend event list.
 *  @coverage prvUnlockQueue
 */
void test_macro_xQueueSend_blocking_success_locked_low_prio_pending( void )
{
    QueueHandle_t xQueue = xQueueCreate( 1, sizeof( uint32_t ) );

    /* Export for callbacks */
    xQueueHandleStatic = xQueue;

    uint32_t testVal = getNextMonotonicTestValue();

    TEST_ASSERT_EQUAL( pdTRUE, xQueueSend( xQueue, &testVal, 0 ) );

    xTaskCheckForTimeOut_Stub( &xQueueSend_locked_xTaskCheckForTimeOutCB );
    xTaskResumeAll_Stub( &xQueueSend_xTaskResumeAllCallback );

    /* The pending task is lower priority */
    td_task_setFakeTaskPriority( DEFAULT_PRIORITY - 1 );

    td_task_addFakeTaskWaitingToSendToQueue( xQueue );

    uint32_t testVal2 = getLastMonotonicTestValue() + 12345;

    TEST_ASSERT_EQUAL( 1, uxQueueMessagesWaiting( xQueue ) );

    TEST_ASSERT_EQUAL( pdTRUE, xQueueSend( xQueue, &testVal2, TICKS_TO_WAIT ) );

    TEST_ASSERT_EQUAL( 1, uxQueueMessagesWaiting( xQueue ) );

    TEST_ASSERT_EQUAL( NUM_CALLS_TO_INTERCEPT, td_task_getYieldCount() );

    /* Check that vPortYieldWithinAPI was called and would have yielded */
    TEST_ASSERT_EQUAL( NUM_CALLS_TO_INTERCEPT, td_task_getCount_vPortYieldWithinAPI() );

    /* Check that vTaskMissedYield was not called */
    TEST_ASSERT_EQUAL( 0, td_task_getCount_vTaskMissedYield() );

    vQueueDelete( xQueue );
}

/**
 *  @brief Test xQueueSend with taskSCHEDULER_SUSPENDED and timeout=10
 *  @details This should cause xQueueSend to configASSERT because it would
 *  block forever when the queue is full.
 * @coverage xQueueGenericSend
 */
void test_macro_xQueueSend_blocking_suspended_assert( void )
{
    QueueHandle_t xQueue = xQueueCreate( 1, sizeof( uint32_t ) );

    uint32_t testVal = getNextMonotonicTestValue();

    fakeAssertExpectFail();

    td_task_setSchedulerState( taskSCHEDULER_SUSPENDED );

    TEST_ASSERT_EQUAL( 0, uxQueueMessagesWaiting( xQueue ) );

    TEST_ASSERT_EQUAL( pdTRUE, xQueueSend( xQueue, &testVal, 10 ) );

    TEST_ASSERT_EQUAL( 1, uxQueueMessagesWaiting( xQueue ) );

    TEST_ASSERT_EQUAL( pdTRUE, fakeAssertGetFlagAndClear() );

    td_task_setSchedulerState( taskSCHEDULER_RUNNING );

    vQueueDelete( xQueue );
}

/**
 *  @brief Test xQueueSend with taskSCHEDULER_RUNNING and timeout=10 on a full queue.
 *  @coverage xQueueGenericSend
 */
void test_macro_xQueueSend_blocking_timeout( void )
{
    QueueHandle_t xQueue = xQueueCreate( 1, sizeof( uint32_t ) );

    uint32_t testVal = getNextMonotonicTestValue();

    /* Fill up the queue */
    TEST_ASSERT_EQUAL( pdTRUE, xQueueSend( xQueue, &testVal, 0 ) );

    TEST_ASSERT_EQUAL( 1, uxQueueMessagesWaiting( xQueue ) );

    TEST_ASSERT_EQUAL( errQUEUE_FULL, xQueueSend( xQueue, &testVal, TICKS_TO_WAIT ) );

    TEST_ASSERT_EQUAL( 1, uxQueueMessagesWaiting( xQueue ) );

    TEST_ASSERT_EQUAL( TICKS_TO_WAIT, td_task_getYieldCount() );

    /* Check that vPortYieldWithinAPI was called and would have yielded */
    TEST_ASSERT_EQUAL( TICKS_TO_WAIT, td_task_getCount_vPortYieldWithinAPI() );

    /* Check that vTaskMissedYield was not called */
    TEST_ASSERT_EQUAL( 0, td_task_getCount_vTaskMissedYield() );

    vQueueDelete( xQueue );
}

/**
 * @brief Test xQueueSend in blocking mode with a full locked queue.
 * @details This test case verifies a situation that should never occur ( xQueueSend called on a locked queue ).
 * @coverage xQueueGenericSend
 */
void test_macro_xQueueSend_blocking_locked( void )
{
    /* Create a new binary Queue */
    QueueHandle_t xQueue = xQueueCreate( 1, sizeof( uint32_t ) );

    uint32_t testVal1 = getNextMonotonicTestValue();

    /* Fill the queue */
    TEST_ASSERT_EQUAL( pdTRUE, xQueueSend( xQueue, &testVal1, TICKS_TO_WAIT ) );

    /* Set private lock counters */
    vSetQueueRxLock( xQueue, queueLOCKED_UNMODIFIED );
    vSetQueueTxLock( xQueue, queueLOCKED_UNMODIFIED );

    uint32_t testVal2 = getNextMonotonicTestValue();

    TEST_ASSERT_EQUAL( 1, uxQueueMessagesWaiting( xQueue ) );

    /* Call xQueueSend in blocking mode with the queue locked */
    TEST_ASSERT_EQUAL( pdFALSE, xQueueSend( xQueue, &testVal2, TICKS_TO_WAIT ) );

    TEST_ASSERT_EQUAL( 1, uxQueueMessagesWaiting( xQueue ) );

    TEST_ASSERT_EQUAL( TICKS_TO_WAIT, td_task_getYieldCount() );

    TEST_ASSERT_EQUAL( TICKS_TO_WAIT, td_task_getCount_vPortYieldWithinAPI() );

    /* Verify that the queue is now unlocked */
    TEST_ASSERT_EQUAL( queueUNLOCKED, cGetQueueRxLock( xQueue ) );
    TEST_ASSERT_EQUAL( queueUNLOCKED, cGetQueueTxLock( xQueue ) );

    vQueueDelete( xQueue );
}
