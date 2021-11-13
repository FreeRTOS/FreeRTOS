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
/*! @file queue_in_set_utest.c */

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
/* Share QueueHandle_t / QueueSetHandle_t between a test case and it's callbacks */
static QueueHandle_t xQueueHandleStatic;
static QueueSetHandle_t xQueueSetHandleStatic;

/* ==========================  CALLBACK FUNCTIONS =========================== */

/* ============================= Unity Fixtures ============================= */

void setUp( void )
{
    commonSetUp();
    vFakePortAssertIfInterruptPriorityInvalid_Ignore();
    xQueueHandleStatic = NULL;
    xQueueSetHandleStatic = NULL;
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

/* ===========================  Helper functions ============================ */

/* ==============================  Test Cases =============================== */


/**
 * @brief Test xQueueSend on a member Queue (size 1) of a QueueSet (size 1)
 * @details: Send an item to a queue that is part of a QueueSet.
 *  Verify that the item can be received from the Queue via xQueueSelectFromSet.
 * @coverage xQueueGenericSend
 */
void test_macro_xQueueSend_xQueueSelectFromSet_xQueueReceive_success( void )
{
    QueueSetHandle_t xQueueSet = xQueueCreateSet( 1 );

    QueueHandle_t xQueue = xQueueCreate( 1, sizeof( uint32_t ) );

    TEST_ASSERT_EQUAL( pdTRUE, xQueueAddToSet( xQueue, xQueueSet ) );

    uint32_t testValue = getNextMonotonicTestValue();

    TEST_ASSERT_EQUAL( pdTRUE, xQueueSend( xQueue, &testValue, 0 ) );

    QueueHandle_t xQueue2 = xQueueSelectFromSet( xQueueSet, 0 );

    TEST_ASSERT_EQUAL( xQueue, xQueue2 );

    uint32_t checkValue = INVALID_UINT32;

    TEST_ASSERT_EQUAL( pdTRUE, xQueueReceive( xQueue2, &checkValue, 0 ) );

    TEST_ASSERT_EQUAL( testValue, checkValue );

    vQueueDelete( xQueueSet );
    vQueueDelete( xQueue );
}

/**
 * @brief Test xQueueSendFromISR on a member Queue (size 1) of a QueueSet (size 1)
 * @details: Send an item to a queue that is part of a QueueSet.
 *  Verify that the item can be received from the Queue via xQueueSelectFromSetFromISR and xQueueReceiveFromISR.
 * @coverage xQueueGenericSendFromISR
 */
void test_macro_xQueueSendFromISR_xQueueSelectFromSetFromISR_xQueueReceiveFromISR_success( void )
{
    QueueSetHandle_t xQueueSet = xQueueCreateSet( 1 );

    QueueHandle_t xQueue = xQueueCreate( 1, sizeof( uint32_t ) );

    TEST_ASSERT_EQUAL( pdTRUE, xQueueAddToSet( xQueue, xQueueSet ) );

    vFakePortAssertIfInterruptPriorityInvalid_Expect();

    uint32_t testValue = getNextMonotonicTestValue();

    TEST_ASSERT_EQUAL( pdTRUE, xQueueSendFromISR( xQueue, &testValue, NULL ) );

    vFakePortAssertIfInterruptPriorityInvalid_Expect();
    QueueHandle_t xQueue2 = xQueueSelectFromSetFromISR( xQueueSet );

    TEST_ASSERT_EQUAL( xQueue, xQueue2 );

    vFakePortAssertIfInterruptPriorityInvalid_Expect();

    uint32_t checkValue = INVALID_UINT32;

    TEST_ASSERT_EQUAL( pdTRUE, xQueueReceiveFromISR( xQueue2, &checkValue, NULL ) );

    vQueueDelete( xQueueSet );
    vQueueDelete( xQueue );
}

/**
 * @brief Test xQueueOverwrite on an empty member Queue (size 1) of a QueueSet (size 1)
 * @details: Perform an xQueueOverwrite operation to add a value to a queue.
 * Verify that the item can be received from the Queue via xQueueSelectFromSet.
 * @coverage xQueueGenericSend
 */
void test_macro_xQueueOverwrite_xQueueSelectFromSet_xQueueReceive_success( void )
{
    QueueSetHandle_t xQueueSet = xQueueCreateSet( 1 );

    QueueHandle_t xQueue = xQueueCreate( 1, sizeof( uint32_t ) );

    TEST_ASSERT_EQUAL( pdTRUE, xQueueAddToSet( xQueue, xQueueSet ) );

    uint32_t testVal = getNextMonotonicTestValue();

    TEST_ASSERT_EQUAL( pdTRUE, xQueueOverwrite( xQueue, &testVal ) );

    QueueHandle_t xQueue2 = xQueueSelectFromSet( xQueueSet, 0 );

    TEST_ASSERT_EQUAL( xQueue, xQueue2 );

    uint32_t checkVal = INVALID_UINT32;

    TEST_ASSERT_EQUAL( pdTRUE, xQueueReceive( xQueue2, &checkVal, 0 ) );

    TEST_ASSERT_EQUAL( testVal, checkVal );

    vQueueDelete( xQueueSet );
    vQueueDelete( xQueue );
}

/**
 * @brief Test xQueueOverwriteFromISR on an empty member Queue (size 1) of a QueueSet (size 1)
 * @details: Perform an xQueueOverwriteFromISR operation to add a value to a queue.
 * Verify that the item can be received from the Queue via xQueueSelectFromSetFromISR.
 * @coverage xQueueGenericSendFromISR
 */
void test_macro_xQueueOverwriteFromISR_xQueueSelectFromSetFromISR_xQueueReceive_success( void )
{
    QueueSetHandle_t xQueueSet = xQueueCreateSet( 1 );

    QueueHandle_t xQueue = xQueueCreate( 1, sizeof( uint32_t ) );

    TEST_ASSERT_EQUAL( pdTRUE, xQueueAddToSet( xQueue, xQueueSet ) );

    vFakePortAssertIfInterruptPriorityInvalid_Expect();
    uint32_t testVal = getNextMonotonicTestValue();

    TEST_ASSERT_EQUAL( pdTRUE, xQueueOverwriteFromISR( xQueue, &testVal, NULL ) );

    vFakePortAssertIfInterruptPriorityInvalid_Expect();
    QueueHandle_t xQueue2 = xQueueSelectFromSetFromISR( xQueueSet );

    TEST_ASSERT_EQUAL( xQueue, xQueue2 );

    vFakePortAssertIfInterruptPriorityInvalid_Expect();
    uint32_t checkVal = INVALID_UINT32;

    TEST_ASSERT_EQUAL( pdTRUE, xQueueReceiveFromISR( xQueue2, &checkVal, NULL ) );

    TEST_ASSERT_EQUAL( testVal, checkVal );

    vQueueDelete( xQueueSet );
    vQueueDelete( xQueue );
}

/**
 * @brief Test xQueueOverwrite on a full member Queue (size 1) of a QueueSet (size 1)
 * @details: Send an item to a queue that is part of a QueueSet. Overwrite that same item.
 *  Verify that the item can be received from the Queue via xQueueSelectFromSet.
 * @coverage xQueueGenericSend
 */
void test_macro_xQueueSend_xQueueOverwrite_xQueueSelectFromSet_xQueueReceive_success( void )
{
    QueueSetHandle_t xQueueSet = xQueueCreateSet( 1 );

    QueueHandle_t xQueue = xQueueCreate( 1, sizeof( uint32_t ) );

    TEST_ASSERT_EQUAL( pdTRUE, xQueueAddToSet( xQueue, xQueueSet ) );

    uint32_t testVal1 = getNextMonotonicTestValue();

    TEST_ASSERT_EQUAL( pdTRUE, xQueueSend( xQueue, &testVal1, 0 ) );

    QueueHandle_t xQueue2 = xQueueSelectFromSet( xQueueSet, 0 );

    TEST_ASSERT_EQUAL( xQueue, xQueue2 );

    uint32_t testVal2 = getNextMonotonicTestValue();

    TEST_ASSERT_EQUAL( pdTRUE, xQueueOverwrite( xQueue, &testVal2 ) );

    uint32_t checkVal = INVALID_UINT32;

    TEST_ASSERT_EQUAL( pdTRUE, xQueueReceive( xQueue2, &checkVal, 0 ) );

    TEST_ASSERT_EQUAL( testVal2, checkVal );

    vQueueDelete( xQueueSet );
    vQueueDelete( xQueue );
}

/**
 * @brief Test xQueueOverwriteFromISR on a member Queue (size 1) of a QueueSet (size 1)
 * @details: Send an item to a queue that is part of a QueueSet. Overwrite that same item.
 *  Verify that the item can be received from the Queue via xQueueSelectFromSetFromISR.
 * @coverage xQueueGenericSendFromISR
 */
void test_macro_xQueueSendFromISR_xQueueOverwriteFromISR_in_set_success( void )
{
    QueueSetHandle_t xQueueSet = xQueueCreateSet( 1 );

    QueueHandle_t xQueue = xQueueCreate( 1, sizeof( uint32_t ) );

    TEST_ASSERT_EQUAL( pdTRUE, xQueueAddToSet( xQueue, xQueueSet ) );

    vFakePortAssertIfInterruptPriorityInvalid_Expect();
    uint32_t testVal1 = getNextMonotonicTestValue();

    TEST_ASSERT_EQUAL( pdTRUE, xQueueSendFromISR( xQueue, &testVal1, NULL ) );

    vFakePortAssertIfInterruptPriorityInvalid_Expect();
    QueueHandle_t xQueue2 = xQueueSelectFromSetFromISR( xQueueSet );

    TEST_ASSERT_EQUAL( xQueue, xQueue2 );

    vFakePortAssertIfInterruptPriorityInvalid_Expect();
    uint32_t testVal2 = getNextMonotonicTestValue();

    TEST_ASSERT_EQUAL( pdTRUE, xQueueOverwriteFromISR( xQueue, &testVal2, NULL ) );

    vFakePortAssertIfInterruptPriorityInvalid_Expect();
    uint32_t checkVal = INVALID_UINT32;

    TEST_ASSERT_EQUAL( pdTRUE, xQueueReceiveFromISR( xQueue2, &checkVal, NULL ) );

    TEST_ASSERT_EQUAL( testVal2, checkVal );

    vQueueDelete( xQueueSet );
    vQueueDelete( xQueue );
}

/**
 * @brief Test xQueueSendFromISR with a higher priority task waiting and a null pointer for pxHigherPriorityTaskWoken
 * @details Test xQueueSendFromISR on a queue that is in a Queue Set with a higher priority task waiting.
 *  Verify that a null pxHigherPriorityTaskWoken is handled correctly.
 * @coverage xQueueGenericSendFromISR
 */
void test_macro_xQueueSendFromISR_in_set_high_priority_pending_null_ptr( void )
{
    QueueHandle_t xQueue = xQueueCreate( 1, sizeof( uint32_t ) );

    QueueSetHandle_t xQueueSet = xQueueCreateSet( 1 );

    xQueueAddToSet( xQueue, xQueueSet );

    vFakePortAssertIfInterruptPriorityInvalid_Expect();

    /* Insert an item into the event list */
    td_task_setFakeTaskPriority( DEFAULT_PRIORITY + 1 );
    td_task_addFakeTaskWaitingToReceiveFromQueue( xQueueSet );

    uint32_t testVal = getNextMonotonicTestValue();

    /* Add item to queue*/
    TEST_ASSERT_EQUAL( pdTRUE, xQueueSendFromISR( xQueue, &testVal, NULL ) );

    QueueHandle_t xQueueTemp = xQueueSelectFromSet( xQueueSet, 0 );

    TEST_ASSERT_EQUAL( 0, td_task_getYieldCount() );

    /* Check that the xYieldPending flag was set
     *  (task would normally be added to the pending ready list)  */
    TEST_ASSERT_EQUAL( pdTRUE, td_task_getYieldPending() );

    uint32_t checkVal = INVALID_UINT32;

    xQueueReceive( xQueueTemp, &checkVal, 0 );
    TEST_ASSERT_EQUAL( testVal, checkVal );

    vQueueDelete( xQueue );
    vQueueDelete( xQueueSet );
}

/**
 * @brief Test xQueueSendFromISR with a higher priority task waiting on a queue in and Queue Set
 * @details Test xQueueSendFromISR with a higher priority task waiting and
 *  verifies that xHigherPriorityTaskWoken is set accordingly.
 * @coverage xQueueGenericSendFromISR
 */
void test_macro_xQueueSendFromISR_in_set_high_priority_pending( void )
{
    QueueHandle_t xQueue = xQueueCreate( 1, sizeof( uint32_t ) );

    QueueSetHandle_t xQueueSet = xQueueCreateSet( 1 );

    xQueueAddToSet( xQueue, xQueueSet );

    vFakePortAssertIfInterruptPriorityInvalid_Expect();

    /* Insert an item into the event list */
    td_task_setFakeTaskPriority( DEFAULT_PRIORITY + 1 );
    td_task_addFakeTaskWaitingToReceiveFromQueue( xQueueSet );

    uint32_t testVal = getNextMonotonicTestValue();

    BaseType_t xHigherPriorityTaskWoken = pdFALSE;

    /* Add item to queue*/
    TEST_ASSERT_EQUAL( pdTRUE, xQueueSendFromISR( xQueue, &testVal, &xHigherPriorityTaskWoken ) );

    TEST_ASSERT_EQUAL( pdTRUE, xHigherPriorityTaskWoken );

    /* Check that the xYieldPending flag was set
     *  (task would normally be added to the pending ready list)  */
    TEST_ASSERT_EQUAL( pdTRUE, td_task_getYieldPending() );

    QueueHandle_t xQueueTemp = xQueueSelectFromSet( xQueueSet, 0 );
    uint32_t checkVal = INVALID_UINT32;

    xQueueReceive( xQueueTemp, &checkVal, 0 );
    TEST_ASSERT_EQUAL( testVal, checkVal );

    vQueueDelete( xQueue );
    vQueueDelete( xQueueSet );
}

/**
 * @brief Test xQueueSendFromISR with a lower priority task waiting on a queue in a Queue Set
 * @details Test xQueueSendFromISR on a Queeu in a Queue Set with a lower priority task waiting and
 *  verify that xHigherPriorityTaskWoken is not modified.
 * @coverage xQueueGenericSendFromISR
 */
void test_macro_xQueueSendFromISR_in_set_low_priority_pending( void )
{
    QueueHandle_t xQueue = xQueueCreate( 1, sizeof( uint32_t ) );

    QueueSetHandle_t xQueueSet = xQueueCreateSet( 1 );

    xQueueAddToSet( xQueue, xQueueSet );

    vFakePortAssertIfInterruptPriorityInvalid_Expect();

    /* Insert an item into the event list */
    td_task_setFakeTaskPriority( DEFAULT_PRIORITY - 1 );
    td_task_addFakeTaskWaitingToReceiveFromQueue( xQueueSet );

    uint32_t testVal = getNextMonotonicTestValue();

    BaseType_t xHigherPriorityTaskWoken = pdFALSE;

    /* Add item to queue*/
    TEST_ASSERT_EQUAL( pdTRUE, xQueueSendFromISR( xQueue, &testVal, &xHigherPriorityTaskWoken ) );

    TEST_ASSERT_EQUAL( pdFALSE, xHigherPriorityTaskWoken );

    /* Check that the xYieldPending flag was not set */
    TEST_ASSERT_EQUAL( pdFALSE, td_task_getYieldPending() );

    QueueHandle_t xQueueTemp = xQueueSelectFromSet( xQueueSet, 0 );
    uint32_t checkVal = INVALID_UINT32;

    xQueueReceive( xQueueTemp, &checkVal, 0 );
    TEST_ASSERT_EQUAL( testVal, checkVal );

    vQueueDelete( xQueue );
    vQueueDelete( xQueueSet );
}

/**
 * @brief Test xQueueSendFromISR on a queue in a Queue Set with no tasks waiting
 * @details Test xQueueSendFromISR on a Queue in a Queue Set no tasks waiting and verify that xHigherPriorityTaskWoken is not modified.
 * @coverage xQueueGenericSendFromISR
 */
void test_macro_xQueueSendFromISR_in_set_no_pending( void )
{
    QueueHandle_t xQueue = xQueueCreate( 1, sizeof( uint32_t ) );

    QueueSetHandle_t xQueueSet = xQueueCreateSet( 1 );

    xQueueAddToSet( xQueue, xQueueSet );

    vFakePortAssertIfInterruptPriorityInvalid_Expect();

    uint32_t testVal = getNextMonotonicTestValue();

    BaseType_t xHigherPriorityTaskWoken = pdFALSE;

    /* Add item to queue*/
    TEST_ASSERT_EQUAL( pdTRUE, xQueueSendFromISR( xQueue, &testVal, &xHigherPriorityTaskWoken ) );

    TEST_ASSERT_EQUAL( pdFALSE, xHigherPriorityTaskWoken );

    /* Check that the xYieldPending flag was not set */
    TEST_ASSERT_EQUAL( pdFALSE, td_task_getYieldPending() );

    QueueHandle_t xQueueTemp = xQueueSelectFromSet( xQueueSet, 0 );
    uint32_t checkVal = INVALID_UINT32;

    xQueueReceive( xQueueTemp, &checkVal, 0 );
    TEST_ASSERT_EQUAL( testVal, checkVal );

    vQueueDelete( xQueue );
    vQueueDelete( xQueueSet );
}

/**
 * @brief Test a non-blocking call to xQueueSend on a queue in a Queue Set with a higher priority task pending.
 * @coverage xQueueGenericSend
 */
void test_macro_xQueueSend_in_set_high_priority_pending( void )
{
    QueueHandle_t xQueue = xQueueCreate( 1, sizeof( uint32_t ) );

    QueueSetHandle_t xQueueSet = xQueueCreateSet( 1 );

    xQueueAddToSet( xQueue, xQueueSet );

    /* Insert an item into the event list */
    td_task_setFakeTaskPriority( DEFAULT_PRIORITY + 1 );
    td_task_addFakeTaskWaitingToReceiveFromQueue( xQueueSet );

    uint32_t testVal = getNextMonotonicTestValue();

    /* Add item to queue*/
    TEST_ASSERT_EQUAL( pdTRUE, xQueueSend( xQueue, &testVal, 0 ) );

    /* Check that a yield occurred */
    TEST_ASSERT_EQUAL( 1, td_task_getYieldCount() );

    /* Check that yield was generated by a call to vPortYieldWithinAPI */
    TEST_ASSERT_EQUAL( 1, td_task_getCount_vPortYieldWithinAPI() );

    QueueHandle_t xQueue2 = xQueueSelectFromSet( xQueueSet, 0 );

    uint32_t checkVal = INVALID_UINT32;

    xQueueReceive( xQueue2, &checkVal, 0 );
    TEST_ASSERT_EQUAL( testVal, checkVal );

    vQueueDelete( xQueue );
    vQueueDelete( xQueueSet );
}

/**
 * @brief Test a non-blocking call to xQueueSend on a queue in a Queue Set with a lower priority task pending.
 * @coverage xQueueGenericSend
 */
void test_macro_xQueueSend_in_set_low_priority_pending( void )
{
    QueueHandle_t xQueue = xQueueCreate( 1, sizeof( uint32_t ) );

    QueueSetHandle_t xQueueSet = xQueueCreateSet( 1 );

    xQueueAddToSet( xQueue, xQueueSet );

    /* Insert an item into the event list */
    td_task_setFakeTaskPriority( DEFAULT_PRIORITY - 1 );
    td_task_addFakeTaskWaitingToReceiveFromQueue( xQueueSet );

    uint32_t testVal = getNextMonotonicTestValue();

    /* Add item to queue*/
    TEST_ASSERT_EQUAL( pdTRUE, xQueueSend( xQueue, &testVal, 0 ) );

    /* Check that no yield occurred */
    TEST_ASSERT_EQUAL( 0, td_task_getYieldCount() );

    QueueHandle_t xQueue2 = xQueueSelectFromSet( xQueueSet, 0 );

    uint32_t checkVal = INVALID_UINT32;

    xQueueReceive( xQueue2, &checkVal, 0 );
    TEST_ASSERT_EQUAL( testVal, checkVal );

    vQueueDelete( xQueue );
    vQueueDelete( xQueueSet );
}

/**
 * @brief Test a non-blocking call to xQueueSend on a queue in a Queue Set with no pending tasks.
 * @coverage xQueueGenericSend
 */
void test_macro_xQueueSend_in_set_no_pending( void )
{
    QueueHandle_t xQueue = xQueueCreate( 1, sizeof( uint32_t ) );

    QueueSetHandle_t xQueueSet = xQueueCreateSet( 1 );

    xQueueAddToSet( xQueue, xQueueSet );

    uint32_t testVal = getNextMonotonicTestValue();

    /* Add item to queue*/
    TEST_ASSERT_EQUAL( pdTRUE, xQueueSend( xQueue, &testVal, 0 ) );

    /* Check that no yield occurred */
    TEST_ASSERT_EQUAL( 0, td_task_getYieldCount() );

    QueueHandle_t xQueue2 = xQueueSelectFromSet( xQueueSet, 0 );

    uint32_t checkVal = INVALID_UINT32;

    xQueueReceive( xQueue2, &checkVal, 0 );
    TEST_ASSERT_EQUAL( testVal, checkVal );

    vQueueDelete( xQueue );
    vQueueDelete( xQueueSet );
}

/**
 * @brief Test xQueueSendFromISR on a queue that is locked
 * @coverage prvNotifyQueueSetContainer
 */
void test_xQueueSendFromISR_locked( void )
{
    QueueHandle_t xQueue = xQueueCreate( 2, sizeof( uint32_t ) );

    QueueSetHandle_t xQueueSet = xQueueCreateSet( 2 );

    TEST_ASSERT_EQUAL( pdTRUE, xQueueAddToSet( xQueue, xQueueSet ) );

    /* Set private lock counters on the queue and queueSet */
    vSetQueueRxLock( xQueue, queueLOCKED_UNMODIFIED );
    vSetQueueTxLock( xQueueSet, queueLOCKED_UNMODIFIED );

    vFakePortAssertIfInterruptPriorityInvalid_Expect();

    uint32_t testVal = getNextMonotonicTestValue();

    TEST_ASSERT_EQUAL( pdTRUE, xQueueSendFromISR( xQueue, &testVal, NULL ) );

    /* Verify that the cRxLock counter has not changed */
    TEST_ASSERT_EQUAL( queueLOCKED_UNMODIFIED, cGetQueueRxLock( xQueue ) );

    /* Verify that the cTxLock counter has been incremented */
    TEST_ASSERT_EQUAL( queueLOCKED_UNMODIFIED + 1, cGetQueueTxLock( xQueueSet ) );

    QueueHandle_t xQueue2 = xQueueSelectFromSet( xQueueSet, 0 );

    TEST_ASSERT_EQUAL( xQueue2, xQueue );

    uint32_t checkVal = INVALID_UINT32;

    TEST_ASSERT_EQUAL( pdTRUE, xQueueReceive( xQueue2, &checkVal, 0 ) );

    TEST_ASSERT_EQUAL( testVal, checkVal );

    vQueueDelete( xQueue );
    vQueueDelete( xQueueSet );
}

/**
 * @brief Test xQueueSendFromISR on a queue that is locked where cRxLock overflows.
 * @coverage prvNotifyQueueSetContainer
 */
void test_xQueueSendFromISR_locked_overflow( void )
{
    QueueHandle_t xQueue = xQueueCreate( 2, sizeof( uint32_t ) );

    QueueSetHandle_t xQueueSet = xQueueCreateSet( 2 );

    TEST_ASSERT_EQUAL( pdTRUE, xQueueAddToSet( xQueue, xQueueSet ) );

    /* Set private lock counters */
    vSetQueueRxLock( xQueue, queueLOCKED_UNMODIFIED );
    vSetQueueTxLock( xQueueSet, INT8_MAX );

    vFakePortAssertIfInterruptPriorityInvalid_Expect();

    /* Expect an assertion since the cTxLock value has overflowed */
    fakeAssertExpectFail();

    uint32_t testval = getNextMonotonicTestValue();

    TEST_ASSERT_EQUAL( pdTRUE, xQueueSendFromISR( xQueue, &testval, NULL ) );

    /* Verify that the cRxLock counter has not changed */
    TEST_ASSERT_EQUAL( queueLOCKED_UNMODIFIED, cGetQueueRxLock( xQueue ) );

    /* Verify that the cTxLock counter has been incremented */
    TEST_ASSERT_EQUAL( INT8_MIN, cGetQueueTxLock( xQueueSet ) );

    TEST_ASSERT_EQUAL( true, fakeAssertGetFlagAndClear() );

    /* Call xQueueSend to trigger a call to prvUnlockQueue */
    uint32_t testVal2 = getNextMonotonicTestValue();

    TEST_ASSERT_EQUAL( pdTRUE, xQueueSend( xQueue, &testVal2, 0 ) );

    /* Read back the first value sent to the queue */
    QueueHandle_t xQueue2 = xQueueSelectFromSet( xQueueSet, 0 );

    TEST_ASSERT_TRUE( xQueue2 );

    uint32_t checkVal = INVALID_UINT32;

    TEST_ASSERT_EQUAL( pdTRUE, xQueueReceive( xQueue2, &checkVal, 0 ) );

    TEST_ASSERT_EQUAL( testval, checkVal );

    /* Read back the second value sent to the queue */
    QueueHandle_t xQueue3 = xQueueSelectFromSet( xQueueSet, 0 );

    TEST_ASSERT_TRUE( xQueue3 );

    uint32_t checkVal2 = INVALID_UINT32;

    TEST_ASSERT_EQUAL( pdTRUE, xQueueReceive( xQueue3, &checkVal2, 0 ) );

    TEST_ASSERT_EQUAL( testVal2, checkVal2 );

    vQueueDelete( xQueue );
    vQueueDelete( xQueueSet );
}

/**
 *  @brief Callback for xQueueSend blocking tests which empties the test queue.
 */
static BaseType_t xQueueSend_locked_xTaskCheckForTimeOutCB( TimeOut_t * const pxTimeOut,
                                                            TickType_t * const pxTicksToWait,
                                                            int cmock_num_calls )
{
    BaseType_t xReturnValue = td_task_xTaskCheckForTimeOutStub( pxTimeOut, pxTicksToWait, cmock_num_calls );

    if( cmock_num_calls == NUM_CALLS_TO_INTERCEPT )
    {
        uint32_t checkVal = INVALID_UINT32;
        QueueHandle_t xQueue = xQueueSelectFromSetFromISR( xQueueSetHandleStatic );
        TEST_ASSERT_NOT_NULL( xQueue );
        xQueueReceiveFromISR( xQueue, &checkVal, NULL );
        TEST_ASSERT_EQUAL( getLastMonotonicTestValue(), checkVal );
    }

    return xReturnValue;
}

/**
 * @brief Test a blocking call to xQueueSend on a queue in a Queue Set with no pending tasks.
 * @coverage xQueueGenericSend
 */
void test_macro_xQueueSend_in_set_blocking_success_locked_no_pending( void )
{
    QueueSetHandle_t xQueueSet = xQueueCreateSet( 1 );

    QueueHandle_t xQueue = xQueueCreate( 1, sizeof( uint32_t ) );

    xQueueAddToSet( xQueue, xQueueSet );

    /* Export for callbacks */
    xQueueSetHandleStatic = xQueueSet;

    uint32_t testVal = getNextMonotonicTestValue();

    TEST_ASSERT_EQUAL( pdTRUE, xQueueSend( xQueue, &testVal, 0 ) );

    xTaskCheckForTimeOut_Stub( &xQueueSend_locked_xTaskCheckForTimeOutCB );
    xTaskResumeAll_Stub( &td_task_xTaskResumeAllStub );

    uint32_t testVal2 = getLastMonotonicTestValue() + 12345;

    TEST_ASSERT_EQUAL( pdTRUE, xQueueSend( xQueue, &testVal2, TICKS_TO_WAIT ) );

    TEST_ASSERT_EQUAL( NUM_CALLS_TO_INTERCEPT, td_task_getYieldCount() );

    TEST_ASSERT_EQUAL( 0, td_task_getCount_vTaskMissedYield() );

    /* Check that vPortYieldWithinAPI was called */
    TEST_ASSERT_EQUAL( NUM_CALLS_TO_INTERCEPT, td_task_getCount_vPortYieldWithinAPI() );

    ( void ) xQueueRemoveFromSet( xQueue, xQueueSet );
    vQueueDelete( xQueueSet );
    vQueueDelete( xQueue );
}

/**
 *  @brief Callback for xQueueSend blocking tests which adds an item to the test queue.
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
 * @brief Test a blocking call to xQueueSend on a queue in a Queue Set with a higher priority pending task.
 * @coverage prvUnlockQueue
 */
void test_macro_xQueueSend_in_set_blocking_fail_locked_high_prio_pending( void )
{
    QueueSetHandle_t xQueueSet = xQueueCreateSet( 1 );

    QueueHandle_t xQueue = xQueueCreate( 1, sizeof( uint32_t ) );

    xQueueAddToSet( xQueue, xQueueSet );

    /* Export for callbacks */
    xQueueHandleStatic = xQueue;
    xQueueSetHandleStatic = xQueueSet;

    uint32_t testVal = getNextMonotonicTestValue();

    TEST_ASSERT_EQUAL( pdTRUE, xQueueSend( xQueue, &testVal, 0 ) );

    xTaskCheckForTimeOut_Stub( &xQueueSend_locked_xTaskCheckForTimeOutCB );
    xTaskResumeAll_Stub( &xQueueSend_xTaskResumeAllCallback );

    /* this task is lower priority than the pending task */
    td_task_setFakeTaskPriority( DEFAULT_PRIORITY + 1 );

    td_task_addFakeTaskWaitingToSendToQueue( xQueue );

    uint32_t testVal2 = getLastMonotonicTestValue() + 12345;

    TEST_ASSERT_EQUAL( pdFALSE, xQueueSend( xQueue, &testVal2, TICKS_TO_WAIT ) );

    TEST_ASSERT_EQUAL( TICKS_TO_WAIT, td_task_getYieldCount() );

    /* Check that xTaskResumeAll was called and would have yielded */
    TEST_ASSERT_EQUAL( NUM_CALLS_TO_INTERCEPT + 1, td_task_getCount_YieldFromTaskResumeAll() );

    /* Check that vPortYieldWithinAPI was called and would have yielded */
    TEST_ASSERT_EQUAL( NUM_CALLS_TO_INTERCEPT - 1, td_task_getCount_vPortYieldWithinAPI() );

    /* Check that vTaskMissedYield was called */
    TEST_ASSERT_EQUAL( 1, td_task_getCount_vTaskMissedYield() );

    ( void ) xQueueRemoveFromSet( xQueue, xQueueSet );
    vQueueDelete( xQueueSet );
    vQueueDelete( xQueue );
}

/**
 * @brief Test a blocking call to xQueueSend on a queue in a Queue Set with a lower priority pending task.
 * @coverage prvUnlockQueue
 */
void test_macro_xQueueSend_in_set_blocking_success_locked_low_prio_pending( void )
{
    QueueSetHandle_t xQueueSet = xQueueCreateSet( 1 );

    QueueHandle_t xQueue = xQueueCreate( 1, sizeof( uint32_t ) );

    xQueueAddToSet( xQueue, xQueueSet );

    /* Export for callbacks */
    xQueueHandleStatic = xQueue;
    xQueueSetHandleStatic = xQueueSet;

    uint32_t testVal = getNextMonotonicTestValue();

    TEST_ASSERT_EQUAL( pdTRUE, xQueueSend( xQueue, &testVal, 0 ) );

    xTaskCheckForTimeOut_Stub( &xQueueSend_locked_xTaskCheckForTimeOutCB );
    xTaskResumeAll_Stub( &xQueueSend_xTaskResumeAllCallback );

    /* this task is higher priority than the pending task */
    td_task_setFakeTaskPriority( DEFAULT_PRIORITY - 1 );

    td_task_addFakeTaskWaitingToSendToQueue( xQueue );

    uint32_t testVal2 = getLastMonotonicTestValue() + 12345;

    TEST_ASSERT_EQUAL( pdTRUE, xQueueSend( xQueue, &testVal2, TICKS_TO_WAIT ) );

    TEST_ASSERT_EQUAL( NUM_CALLS_TO_INTERCEPT, td_task_getYieldCount() );

    TEST_ASSERT_EQUAL( NUM_CALLS_TO_INTERCEPT, td_task_getCount_vPortYieldWithinAPI() );

    TEST_ASSERT_EQUAL( 0, td_task_getCount_vTaskMissedYield() );

    ( void ) xQueueRemoveFromSet( xQueue, xQueueSet );
    vQueueDelete( xQueueSet );
    vQueueDelete( xQueue );
}

/**
 *  @brief Callback for test_xQueueReceive_blocking_success_locked_no_pending which adds an item to it's test queue.
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
    }

    return xReturnValue;
}

/**
 * @brief Test a blocking call to xQueueReceive on a queue in a Queue Set with no pending tasks.
 * @coverage prvUnlockQueue
 */
void test_xQueueReceive_in_set_blocking_success_locked_no_pending( void )
{
    QueueSetHandle_t xQueueSet = xQueueCreateSet( 1 );

    QueueHandle_t xQueue = xQueueCreate( 1, sizeof( uint32_t ) );

    TEST_ASSERT_TRUE( xQueueAddToSet( xQueue, xQueueSet ) );

    /* Export for callbacks */
    xQueueHandleStatic = xQueue;

    xTaskCheckForTimeOut_Stub( &xQueueReceive_xTaskCheckForTimeOutCB );
    xTaskResumeAll_Stub( &td_task_xTaskResumeAllStub );

    uint32_t checkVal = INVALID_UINT32;

    QueueHandle_t xQueueFromSet = xQueueSelectFromSet( xQueueSet, TICKS_TO_WAIT );

    TEST_ASSERT_NOT_NULL( xQueueFromSet );

    TEST_ASSERT_EQUAL( pdTRUE, xQueueReceive( xQueueFromSet, &checkVal, 0 ) );

    TEST_ASSERT_EQUAL( getLastMonotonicTestValue(), checkVal );

    TEST_ASSERT_EQUAL( NUM_CALLS_TO_INTERCEPT, td_task_getYieldCount() );

    TEST_ASSERT_EQUAL( NUM_CALLS_TO_INTERCEPT, td_task_getCount_vPortYieldWithinAPI() );

    TEST_ASSERT_EQUAL( 0, td_task_getCount_vTaskMissedYield() );

    ( void ) xQueueRemoveFromSet( xQueue, xQueueSet );
    vQueueDelete( xQueueSet );
    vQueueDelete( xQueue );
}

/**
 * @brief Stub for xTaskResumeAll used in xQueueReceive tests where the queue under test is in a queue set.
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
            QueueHandle_t xQueue = xQueueSelectFromSetFromISR( xQueueSetHandleStatic );
            TEST_ASSERT_TRUE( xQueueReceiveFromISR( xQueue, &checkValue, NULL ) );
            TEST_ASSERT_EQUAL( getLastMonotonicTestValue(), checkValue );
        }
    }

    return xReturnValue;
}

/**
 * @brief Test a blocking call to xQueueReceive on a queue in a Queue Set with a higher priority task pending.
 * @coverage prvUnlockQueue
 */
void test_xQueueReceive_in_set_blocking_fail_locked_high_prio_pending( void )
{
    QueueSetHandle_t xQueueSet = xQueueCreateSet( 1 );

    QueueHandle_t xQueue = xQueueCreate( 1, sizeof( uint32_t ) );

    xQueueAddToSet( xQueue, xQueueSet );

    /* Export for callbacks */
    xQueueHandleStatic = xQueue;
    xQueueSetHandleStatic = xQueueSet;

    xTaskCheckForTimeOut_Stub( &xQueueReceive_xTaskCheckForTimeOutCB );
    xTaskResumeAll_Stub( &xQueueReceive_xTaskResumeAllCallback );

    td_task_setFakeTaskPriority( DEFAULT_PRIORITY + 1 );

    td_task_addFakeTaskWaitingToReceiveFromQueue( xQueueSet );

    QueueHandle_t xQueueFromSet = xQueueSelectFromSet( xQueueSet, TICKS_TO_WAIT );

    TEST_ASSERT_EQUAL( NULL, xQueueFromSet );

    TEST_ASSERT_EQUAL( TICKS_TO_WAIT, td_task_getYieldCount() );

    TEST_ASSERT_EQUAL( NUM_CALLS_TO_INTERCEPT + 1, td_task_getCount_YieldFromTaskResumeAll() );

    TEST_ASSERT_EQUAL( NUM_CALLS_TO_INTERCEPT - 1, td_task_getCount_vPortYieldWithinAPI() );

    /* Check that vTaskMissedYield was called */
    TEST_ASSERT_EQUAL( 1, td_task_getCount_vTaskMissedYield() );

    ( void ) xQueueRemoveFromSet( xQueue, xQueueSet );

    vQueueDelete( xQueueSet );
    vQueueDelete( xQueue );
}

/**
 * @brief Test a blocking call to xQueueReceive on a queue in a Queue Set with a lower priority task pending.
 * @coverage prvUnlockQueue
 */
void test_xQueueReceive_in_set_blocking_success_locked_low_prio_pending( void )
{
    QueueSetHandle_t xQueueSet = xQueueCreateSet( 1 );

    QueueHandle_t xQueue = xQueueCreate( 1, sizeof( uint32_t ) );

    xQueueAddToSet( xQueue, xQueueSet );

    /* Export for callbacks */
    xQueueHandleStatic = xQueue;
    xQueueSetHandleStatic = xQueueSet;

    xTaskCheckForTimeOut_Stub( &xQueueReceive_xTaskCheckForTimeOutCB );
    xTaskResumeAll_Stub( &xQueueReceive_xTaskResumeAllCallback );

    td_task_setFakeTaskPriority( DEFAULT_PRIORITY - 1 );

    td_task_addFakeTaskWaitingToReceiveFromQueue( xQueueSet );

    uint32_t checkVal = INVALID_UINT32;

    QueueHandle_t xQueueFromSet = xQueueSelectFromSet( xQueueSet, NUM_CALLS_TO_INTERCEPT );

    TEST_ASSERT_EQUAL( NUM_CALLS_TO_INTERCEPT, td_task_getYieldCount() );

    TEST_ASSERT_EQUAL( NUM_CALLS_TO_INTERCEPT, td_task_getCount_vPortYieldWithinAPI() );

    /* Check that vTaskMissedYield was not called */
    TEST_ASSERT_EQUAL( pdFALSE, td_task_getCount_vTaskMissedYield() );

    TEST_ASSERT_NOT_NULL( xQueueFromSet );

    TEST_ASSERT_EQUAL( pdTRUE, xQueueReceive( xQueueFromSet, &checkVal, TICKS_TO_WAIT ) );

    TEST_ASSERT_EQUAL( getLastMonotonicTestValue(), checkVal );

    ( void ) xQueueRemoveFromSet( xQueue, xQueueSet );
    vQueueDelete( xQueueSet );
    vQueueDelete( xQueue );
}
