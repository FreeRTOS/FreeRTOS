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
/*! @file queue_unblock_utest.c */

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
 * @brief Test xQueueUnblock to unblock a task waiting to receive from a queue.
 * @coverage xQueueUnblock
 */
void test_xQueueUnblock_receive( void )
{
    QueueHandle_t xQueue = xQueueCreate( 1, sizeof( uint32_t ) );

    /* Export for callbacks */
    xQueueHandleStatic = xQueue;

    xTaskCheckForTimeOut_Stub( &xQueueReceive_xTaskCheckForTimeOutCB );
    xTaskResumeAll_Stub( &td_task_xTaskResumeAllStub );
    uxTaskGetNumberOfTasks_IgnoreAndReturn( 1 );
    vTaskYieldWithinAPI_Stub( vTaskYieldWithinAPI_Callback );

    uint32_t checkVal = INVALID_UINT32;

    /* Add a task to the queue's WaitingToReceive event list */
    td_task_addFakeTaskWaitingToReceiveFromQueue( xQueue );

    /* Unblock the task waiting to receive from the queue */
    TEST_ASSERT_EQUAL( pdTRUE, xQueueUnblock( xQueue ) );

    /* Verify that the task was unblocked */
    TEST_ASSERT_EQUAL( 0, listLIST_IS_EMPTY( &( xQueue->xTasksWaitingToReceive ) ) );

    vQueueDelete( xQueue );
}

/**
 * @brief Test xQueueUnblock to unblock a task waiting to send to a queue.
 * @coverage xQueueUnblock
 */
void test_xQueueUnblock_send( void )
{
    QueueHandle_t xQueue = xQueueCreate( 1, sizeof( uint32_t ) );

    /* Export for callbacks */
    xQueueHandleStatic = xQueue;

    xTaskCheckForTimeOut_Stub( &xQueueReceive_xTaskCheckForTimeOutCB );
    xTaskResumeAll_Stub( &td_task_xTaskResumeAllStub );
    uxTaskGetNumberOfTasks_IgnoreAndReturn( 1 );
    vTaskYieldWithinAPI_Stub( vTaskYieldWithinAPI_Callback );

    uint32_t checkVal = INVALID_UINT32;

    /* Add a task to the queue's WaitingToSend event list */
    td_task_addFakeTaskWaitingToSendToQueue( xQueue );

    /* Unblock the task waiting to send to the queue */
    TEST_ASSERT_EQUAL( pdTRUE, xQueueUnblock( xQueue ) );

    /* Verify that the task was unblocked */
    TEST_ASSERT_EQUAL( 0, listLIST_IS_EMPTY( &( xQueue->xTasksWaitingToSend ) ) );

    vQueueDelete( xQueue );
}
