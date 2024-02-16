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
/*! @file counting_semaphore_utest.c */

#include "../queue_utest_common.h"

/* Queue includes */
#include "FreeRTOS.h"
#include "FreeRTOSConfig.h"
#include "semphr.h"
#include "mock_fake_port.h"


/* ============================  GLOBAL VARIABLES =========================== */

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
    xSemaphoreHandleStatic = NULL;
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
 * @brief Test xSemaphoreTake with xSemaphoreCreateCounting( 1, 0 )
 * @details Test xSemaphoreTake with a binary semaphore constructed with
 * xSemaphoreCreateCounting.
 * @coverage xQueueSemaphoreTake
 */
void test_macro_xSemaphoreTake_CountingSemaphore_one_zero_fail( void )
{
    SemaphoreHandle_t xSemaphore = xSemaphoreCreateCounting( 1, 0 );

    /* validate returned semaphore handle */
    TEST_ASSERT_NOT_EQUAL( NULL, xSemaphore );

    TEST_ASSERT_EQUAL( QUEUE_T_SIZE, getLastMallocSize() );

    /* Verify that an xSemaphoreTake fails */
    TEST_ASSERT_EQUAL( pdFALSE, xSemaphoreTake( xSemaphore, 0 ) );

    vSemaphoreDelete( xSemaphore );
}

/**
 * @brief Test xSemaphoreGive with xSemaphoreCreateCounting( 1, 0 )
 * @details Test xSemaphoreGive with a binary semaphore constructed with
 * xSemaphoreCreateCounting.
 * @coverage xQueueGenericSend
 */
void test_macro_xSemaphoreGive_CountingSemaphore_one_zero_success( void )
{
    SemaphoreHandle_t xSemaphore = xSemaphoreCreateCounting( 1, 0 );

    /* validate returned semaphore handle */
    TEST_ASSERT_NOT_EQUAL( NULL, xSemaphore );

    TEST_ASSERT_EQUAL( QUEUE_T_SIZE, getLastMallocSize() );

    /* Verify that an xSemaphoreGive succeeds */
    TEST_ASSERT_EQUAL( pdTRUE, xSemaphoreGive( xSemaphore ) );

    vSemaphoreDelete( xSemaphore );
}

/**
 * @brief Test xSemaphoreGive and xSemaphoreTake with xSemaphoreCreateCounting( 1, 0 )
 * @details Test xSemaphoreGive and xSemaphoreTake with a binary semaphore
 * constructed with xSemaphoreCreateCounting.
 * @coverage xQueueGenericSend xQueueSemaphoreTake
 */
void test_macro_xSemaphoreGive_xSemaphoreTake_CountingSemaphore_one_zero_success( void )
{
    SemaphoreHandle_t xSemaphore = xSemaphoreCreateCounting( 1, 0 );

    /* validate returned semaphore handle */
    TEST_ASSERT_NOT_EQUAL( NULL, xSemaphore );

    TEST_ASSERT_EQUAL( QUEUE_T_SIZE, getLastMallocSize() );

    /* Verify that an xSemaphoreGive succeeds */
    TEST_ASSERT_EQUAL( pdTRUE, xSemaphoreGive( xSemaphore ) );

    /* Verify that an xSemaphoreTake succeeds */
    TEST_ASSERT_EQUAL( pdTRUE, xSemaphoreTake( xSemaphore, 0 ) );

    /* Verify that an xSemaphoreGive succeeds */
    TEST_ASSERT_EQUAL( pdTRUE, xSemaphoreGive( xSemaphore ) );

    vSemaphoreDelete( xSemaphore );
}


/**
 * @brief Test xSemaphoreGive with xSemaphoreCreateCounting( 100, 50 )
 * @details Test multiple xSemaphoreGive calls on a counting semaphore
 * @coverage xQueueGenericSend
 */
void test_macro_xSemaphoreGive_CountingSemaphore_100_50( void )
{
    SemaphoreHandle_t xSemaphore = xSemaphoreCreateCounting( 100, 50 );

    /* validate returned semaphore handle */
    TEST_ASSERT_NOT_EQUAL( NULL, xSemaphore );

    TEST_ASSERT_EQUAL( QUEUE_T_SIZE, getLastMallocSize() );

    /* Call xSemaphoreGive 50 times and verify success */
    for( int i = 0; i < 50; i++ )
    {
        /* Verify that an xSemaphoreGive operation succeeds */
        TEST_ASSERT_EQUAL( pdTRUE, xSemaphoreGive( xSemaphore ) );
    }

    /* Check the count */
    TEST_ASSERT_EQUAL( 100, uxSemaphoreGetCount( xSemaphore ) );

    /* Verify that a subsequent call to xSemaphoreGive fails */
    TEST_ASSERT_EQUAL( pdFALSE, xSemaphoreGive( xSemaphore ) );

    /* Verify that an xSemaphoreTake operation succeeds */
    TEST_ASSERT_EQUAL( pdTRUE, xSemaphoreTake( xSemaphore, 0 ) );

    /* Check the count */
    TEST_ASSERT_EQUAL( 99, uxSemaphoreGetCount( xSemaphore ) );

    vSemaphoreDelete( xSemaphore );
}

/**
 * @brief Test xSemaphoreTake with xSemaphoreCreateCounting( 100, 50 )
 * @details Test multiple xSemaphoreTake calls on a counting semaphore
 * @coverage xQueueSemaphoreTake
 */
void test_macro_xSemaphoreTake_CountingSemaphore_100_50( void )
{
    SemaphoreHandle_t xSemaphore = xSemaphoreCreateCounting( 100, 50 );

    /* validate returned semaphore handle */
    TEST_ASSERT_NOT_EQUAL( NULL, xSemaphore );

    TEST_ASSERT_EQUAL( QUEUE_T_SIZE, getLastMallocSize() );

    /* Call xSemaphoreTake 50 times and verify success */
    for( int i = 0; i < 50; i++ )
    {
        /* Verify that an xSemaphoreTake operation succeeds */
        TEST_ASSERT_EQUAL( pdTRUE, xSemaphoreTake( xSemaphore, 0 ) );
    }

    /* Check the count */
    TEST_ASSERT_EQUAL( 0, uxSemaphoreGetCount( xSemaphore ) );

    /* Verify that a subsequent call to xSemaphoreGive fails */
    TEST_ASSERT_EQUAL( pdFALSE, xSemaphoreTake( xSemaphore, 0 ) );

    /* Verify that an xSemaphoreGive operation succeeds */
    TEST_ASSERT_EQUAL( pdTRUE, xSemaphoreGive( xSemaphore ) );

    /* Check the count */
    TEST_ASSERT_EQUAL( 1, uxSemaphoreGetCount( xSemaphore ) );

    vSemaphoreDelete( xSemaphore );
}

/**
 * @brief Verify that this test case is running on a 64 bit platform.
 */
void test_size_of_UBaseType_is_64_bits( void )
{
    if( TEST_PROTECT() )
    {
        /* Check that UBaseType_t is 64 bits on this platform */
        TEST_ASSERT_EQUAL( sizeof( uint64_t ), sizeof( UBaseType_t ) );
    }
}

/**
 * @brief Test xSemaphoreGive with xSemaphoreCreateCounting( UINT64_MAX, UINT64_MAX-1 )
 * @details Test xSemaphoreGive with a counting semaphore with uxMaxCount=UINT64_MAX and
 *          uxInitialCount=UINT64_MAX-1
 * @coverage xQueueGenericSend
 */
void test_macro_xSemaphoreGive_CountingSemaphore_upper_bound( void )
{
    SemaphoreHandle_t xSemaphore = xSemaphoreCreateCounting( UINT64_MAX, UINT64_MAX - 1 );

    /* validate returned semaphore handle */
    TEST_ASSERT_NOT_EQUAL( NULL, xSemaphore );

    TEST_ASSERT_EQUAL( QUEUE_T_SIZE, getLastMallocSize() );

    /* Check the initial count */
    TEST_ASSERT_EQUAL( UINT64_MAX - 1, uxSemaphoreGetCount( xSemaphore ) );

    /* Verify that a xSemaphoreGive operation succeeds */
    TEST_ASSERT_EQUAL( pdTRUE, xSemaphoreGive( xSemaphore ) );

    /* Check the count */
    TEST_ASSERT_EQUAL( UINT64_MAX, uxSemaphoreGetCount( xSemaphore ) );

    /* Verify that the next xSemaphoreGive operation fails */
    TEST_ASSERT_EQUAL( pdFALSE, xSemaphoreGive( xSemaphore ) );

    vSemaphoreDelete( xSemaphore );
}

/**
 * @brief Test xSemaphoreTake with xSemaphoreCreateCounting( UINT64_MAX, UINT64_MAX )
 * @details Test xSemaphoreTake with a counting semaphore with uxMaxCount=UINT64_MAX and
 *          uxInitialCount=UINT64_MAX
 * @coverage xQueueSemaphoreTake
 */
void test_macro_xSemaphoreTake_CountingSemaphore_upper_bound( void )
{
    SemaphoreHandle_t xSemaphore = xSemaphoreCreateCounting( UINT64_MAX, UINT64_MAX );

    /* validate returned semaphore handle */
    TEST_ASSERT_NOT_EQUAL( NULL, xSemaphore );

    /* Verify that a xSemaphoreTake operation succeeds */
    TEST_ASSERT_EQUAL( pdTRUE, xSemaphoreTake( xSemaphore, 0 ) );

    TEST_ASSERT_EQUAL( UINT64_MAX - 1, uxSemaphoreGetCount( xSemaphore ) );

    /* Verify that a subsequent xSemaphoreGive operation succeeds */
    TEST_ASSERT_EQUAL( pdTRUE, xSemaphoreGive( xSemaphore ) );

    /* Check the count */
    TEST_ASSERT_EQUAL( UINT64_MAX, uxSemaphoreGetCount( xSemaphore ) );

    /* Verify that the next xSemaphoreGive operation fails */
    TEST_ASSERT_EQUAL( pdFALSE, xSemaphoreGive( xSemaphore ) );

    vSemaphoreDelete( xSemaphore );
}

/**
 * @brief xSemaphoreTake with xSemaphoreCreateCounting( UINT64_MAX, 1)
 * @details Test xSemaphoreTake with a counting semaphore with uxMaxCount=UINT64_MAX and
 *          uxInitialCount=1
 * @coverage xQueueSemaphoreTake
 */
void test_macro_xSemaphoreTake_CountingSemaphore_lower_bound( void )
{
    SemaphoreHandle_t xSemaphore = xSemaphoreCreateCounting( UINT64_MAX, 1 );

    /* validate returned semaphore handle */
    TEST_ASSERT_NOT_EQUAL( NULL, xSemaphore );

    /* Check the initial count */
    TEST_ASSERT_EQUAL( 1, uxSemaphoreGetCount( xSemaphore ) );

    /* Verify that a xSemaphoreTake operation succeeds */
    TEST_ASSERT_EQUAL( pdTRUE, xSemaphoreTake( xSemaphore, 0 ) );

    /* Check the count */
    TEST_ASSERT_EQUAL( 0, uxSemaphoreGetCount( xSemaphore ) );

    /* Verify that the next xSemaphoreTake operation fails */
    TEST_ASSERT_EQUAL( pdFALSE, xSemaphoreTake( xSemaphore, 0 ) );

    vSemaphoreDelete( xSemaphore );
}

/**
 * @brief xSemaphoreGive with xSemaphoreCreateCounting( UINT64_MAX, 0)
 * @details Test xSemaphoreGive with a counting semaphore with uxMaxCount=UINT64_MAX and
 *          uxInitialCount=0
 * @coverage xQueueGenericSend
 */
void test_macro_xSemaphoreGive_CountingSemaphore_lower_bound( void )
{
    SemaphoreHandle_t xSemaphore = xSemaphoreCreateCounting( UINT64_MAX, 0 );

    /* validate returned semaphore handle */
    TEST_ASSERT_NOT_EQUAL( NULL, xSemaphore );

    /* Check the initial count */
    TEST_ASSERT_EQUAL( 0, uxSemaphoreGetCount( xSemaphore ) );

    /* Verify that a xSemaphoreGive operation succeeds */
    TEST_ASSERT_EQUAL( pdTRUE, xSemaphoreGive( xSemaphore ) );

    /* Check the count */
    TEST_ASSERT_EQUAL( 1, uxSemaphoreGetCount( xSemaphore ) );

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
    SemaphoreHandle_t xSemaphore = xSemaphoreCreateCounting( 2, 0 );

    fakeAssertExpectFail();

    vTaskSuspendAll_Stub( td_task_vTaskSuspendAllStubNoCheck );
    vTaskYieldWithinAPI_Stub( vTaskYieldWithinAPI_Callback );

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
    SemaphoreHandle_t xSemaphore = xSemaphoreCreateCounting( 2, 0 );

    td_task_setSchedulerState( taskSCHEDULER_SUSPENDED );

    TEST_ASSERT_EQUAL( pdFALSE, xSemaphoreTake( xSemaphore, 0 ) );

    td_task_setSchedulerState( taskSCHEDULER_RUNNING );

    vSemaphoreDelete( xSemaphore );
}

/**
 *  @brief Callback which calls xSemaphoreGive on xSemaphoreHandleStatic when
 *  cmock_num_calls == NUM_CALLS_TO_INTERCEPT
 */
static BaseType_t blocking_xTaskCheckForTimeOut_cb( TimeOut_t * const pxTimeOut,
                                                    TickType_t * const pxTicksToWait,
                                                    int cmock_num_calls )
{
    BaseType_t xReturnValue = td_task_xTaskCheckForTimeOutStub( pxTimeOut, pxTicksToWait, cmock_num_calls );

    if( cmock_num_calls == NUM_CALLS_TO_INTERCEPT )
    {
        ( void ) xSemaphoreGiveFromISR( xSemaphoreHandleStatic, NULL );
        TEST_ASSERT_EQUAL( 1, uxSemaphoreGetCount( xSemaphoreHandleStatic ) );
    }

    return xReturnValue;
}

/**
 * @brief Test xSemaphoreTake in blocking mode with a fully taken Counting Semaphore
 * which becomes available while a call to xSemaphoreTake is blocking.
 * @coverage xQueueSemaphoreTake
 */
void test_xSemaphoreTake_blocking_success( void )
{
    SemaphoreHandle_t xSemaphore = xSemaphoreCreateCounting( 2, 0 );

    /* Export for blocking_success_xTaskCheckForTimeOut_cb callback */
    xSemaphoreHandleStatic = xSemaphore;

    vFakePortAssertIfInterruptPriorityInvalid_Expect();
    vTaskYieldWithinAPI_Stub( vTaskYieldWithinAPI_Callback );

    xTaskCheckForTimeOut_Stub( &blocking_xTaskCheckForTimeOut_cb );
    uxTaskGetNumberOfTasks_IgnoreAndReturn( 1 );

    TEST_ASSERT_EQUAL( 0, uxSemaphoreGetCount( xSemaphore ) );

    TEST_ASSERT_EQUAL( pdTRUE, xSemaphoreTake( xSemaphore, TICKS_TO_WAIT ) );

    TEST_ASSERT_EQUAL( NUM_CALLS_TO_INTERCEPT, td_task_getYieldCount() );

    TEST_ASSERT_EQUAL( NUM_CALLS_TO_INTERCEPT, td_task_getCount_vPortYieldWithinAPI() );

    TEST_ASSERT_EQUAL( 0, uxSemaphoreGetCount( xSemaphore ) );

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
        TEST_ASSERT_EQUAL( 1, uxSemaphoreGetCount( xSemaphoreHandleStatic ) );
        return pdTRUE;
    }

    return xReturnValue;
}

/**
 * @brief Test xSemaphoreTake in blocking mode with a Counting Semaphore that is
 * initially fully taken, but becomes available at the end of the blocking time.
 * @coverage xQueueSemaphoreTake
 */
void test_xSemaphoreTake_blocking_success_last_chance( void )
{
    SemaphoreHandle_t xSemaphore = xSemaphoreCreateCounting( 2, 0 );

    /* Export for blocking_success_xTaskCheckForTimeOut_cb callback */
    xSemaphoreHandleStatic = xSemaphore;

    vFakePortAssertIfInterruptPriorityInvalid_Expect();
    vTaskYieldWithinAPI_Stub( vTaskYieldWithinAPI_Callback );

    xTaskCheckForTimeOut_Stub( &blocking_last_chance_xTaskCheckForTimeOut_cb );
    uxTaskGetNumberOfTasks_IgnoreAndReturn( 1 );

    TEST_ASSERT_EQUAL( 0, uxSemaphoreGetCount( xSemaphore ) );

    TEST_ASSERT_EQUAL( pdTRUE, xSemaphoreTake( xSemaphore, TICKS_TO_WAIT ) );

    TEST_ASSERT_EQUAL( TICKS_TO_WAIT, td_task_getYieldCount() );

    TEST_ASSERT_EQUAL( TICKS_TO_WAIT, td_task_getCount_vPortYieldWithinAPI() );

    TEST_ASSERT_EQUAL( 0, uxSemaphoreGetCount( xSemaphore ) );

    vSemaphoreDelete( xSemaphore );
}

/*
 * @brief Test xSemaphoreTake in blocking mode with a taken binary semaphore
 * @coverage xQueueSemaphoreTake
 */
void test_xSemaphoreTake_blocking_timeout( void )
{
    SemaphoreHandle_t xSemaphore = xSemaphoreCreateCounting( 2, 0 );

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
    SemaphoreHandle_t xSemaphore = xSemaphoreCreateCounting( 2, 0 );

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
        TEST_ASSERT_TRUE( xSemaphoreGiveFromISR( xSemaphoreHandleStatic, NULL ) );
        TEST_ASSERT_EQUAL( 1, uxSemaphoreGetCount( xSemaphoreHandleStatic ) );
    }

    return xReturnValue;
}

/**
 *  @brief Test a blocking call to xSemaphoreTake with a locked counting semaphore.
 *  @details Test a blocking call to xSemaphoreTake with a locked counting semaphore with no
 *  tasks in the counting semaphore WaitingToReceiveFrom event list.
 *  @coverage xQueueSemaphoreTake prvUnlockQueue
 */
void test_xSemaphoreTake_blocking_success_locked_no_pending( void )
{
    SemaphoreHandle_t xSemaphore = xSemaphoreCreateCounting( 2, 0 );

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
 *  @brief Test a blocking call to xSemaphoreTake with a locked counting semaphore.
 *  @details Test a blocking call to xSemaphoreTake with a locked counting semaphore with a
 *  higher priority task in the counting semaphore WaitingToReceiveFrom event list.
 *  @coverage xQueueSemaphoreTake prvUnlockQueue
 */
void test_xSemaphoreTake_blocking_timeout_locked_high_prio_pending( void )
{
    SemaphoreHandle_t xSemaphore = xSemaphoreCreateCounting( 2, 0 );

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
 *  @brief Test a blocking call to xSemaphoreTake with a locked counting semaphore.
 *  @details Test a blocking call to xSemaphoreTake with a locked counting semaphore with a
 *  lower priority task in the semaphore WaitingToReceiveFrom event list.
 *  @coverage xQueueSemaphoreTake prvUnlockQueue
 */
void test_xSemaphoreTake_blocking_success_locked_low_prio_pending( void )
{
    SemaphoreHandle_t xSemaphore = xSemaphoreCreateCounting( 2, 0 );

    vFakePortAssertIfInterruptPriorityInvalid_Ignore();
    vTaskYieldWithinAPI_Stub( vTaskYieldWithinAPI_Callback );

    /* Export for callbacks */
    xSemaphoreHandleStatic = xSemaphore;

    xTaskCheckForTimeOut_Stub( &xSemaphoreTake_xTaskCheckForTimeOutCB );
    xTaskResumeAll_Stub( &xSemaphoreTake_xTaskResumeAllCallback );
    uxTaskGetNumberOfTasks_IgnoreAndReturn( 1 );

    td_task_setFakeTaskPriority( DEFAULT_PRIORITY - 1 );

    td_task_addFakeTaskWaitingToReceiveFromQueue( xSemaphore );

    TEST_ASSERT_EQUAL( pdTRUE, xSemaphoreTake( xSemaphore, TICKS_TO_WAIT ) );

    TEST_ASSERT_EQUAL( 0, uxSemaphoreGetCount( xSemaphore ) );

    TEST_ASSERT_EQUAL( NUM_CALLS_TO_INTERCEPT, td_task_getYieldCount() );

    TEST_ASSERT_EQUAL( NUM_CALLS_TO_INTERCEPT, td_task_getCount_vPortYieldWithinAPI() );

    vQueueDelete( xSemaphore );
}

/**
 * @brief Test xSemaphoreGiveFromISR on a semaphore that is locked
 * @coverage xQueueGiveFromISR
 */
void test_macro_xSemaphoreGiveFromISR_locked( void )
{
    SemaphoreHandle_t xSemaphore = xSemaphoreCreateCounting( 2, 0 );

    /* Set private lock counters */
    vSetQueueRxLock( xSemaphore, queueLOCKED_UNMODIFIED );
    vSetQueueTxLock( xSemaphore, queueLOCKED_UNMODIFIED );

    vFakePortAssertIfInterruptPriorityInvalid_Ignore();
    uxTaskGetNumberOfTasks_IgnoreAndReturn( 1 );

    TEST_ASSERT_EQUAL( pdTRUE, xSemaphoreGiveFromISR( xSemaphore, NULL ) );
    TEST_ASSERT_EQUAL( pdTRUE, xSemaphoreGiveFromISR( xSemaphore, NULL ) );

    /* Verify that the cRxLock counter has not changed */
    TEST_ASSERT_EQUAL( queueLOCKED_UNMODIFIED, cGetQueueRxLock( xSemaphore ) );

    /* Verify that the cTxLock counter has only been incremented by one
     * even after 2 calls to xQueueSendFromISR because there is only
     * one task in the system as returned from uxTaskGetNumberOfTasks. */
    TEST_ASSERT_EQUAL( queueLOCKED_UNMODIFIED + 1, cGetQueueTxLock( xSemaphore ) );

    vSemaphoreDelete( xSemaphore );
}
