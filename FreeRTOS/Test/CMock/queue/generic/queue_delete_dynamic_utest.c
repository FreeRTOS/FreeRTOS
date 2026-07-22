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
/*! @file queue_delete_dynamic_utest.c */

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

/* =========================== CALLBACK FUNCTIONS =========================== */

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

/* ===========================  Helper functions ============================ */

/* ==============================  Test Cases =============================== */

/**
 * @brief Test vQueueDelete with an invalid QueueHandle
 * @coverage vQueueDelete
 */
void test_vQueueDelete_invalid_handle( void )
{
    EXPECT_ASSERT_BREAK( vQueueDelete( NULL ) );
}

/**
 * @brief Test vQueueDelete with a statically allocated queue of size 6 x 4 bytes
 * @coverage vQueueDelete
 */
void test_vQueueDelete_empty( void )
{
    QueueHandle_t xQueue = xQueueCreate( 6, sizeof( uint32_t ) );

    TEST_ASSERT_EQUAL( QUEUE_T_SIZE + ( 6 * 4 ), getLastMallocSize() );

    vQueueDelete( xQueue );
    TEST_ASSERT_EQUAL_PTR( ( void * ) xQueue, getLastFreedAddress() );
}

/**
 * @brief Test vQueueDelete with a half-full queue of size 6 x 4 bytes
 * @coverage vQueueDelete
 */
void test_vQueueDelete_half_full( void )
{
    QueueHandle_t xQueue = xQueueCreate( 6, sizeof( uint32_t ) );

    TEST_ASSERT_EQUAL( QUEUE_T_SIZE + ( 6 * 4 ), getLastMallocSize() );

    for( uint32_t i = 0; i < 3; i++ )
    {
        xQueueSend( xQueue, &i, 0 );
    }

    vQueueDelete( xQueue );
    TEST_ASSERT_EQUAL_PTR( ( void * ) xQueue, getLastFreedAddress() );
}

/**
 * @brief Test vQueueDelete with a full queue of size 6 x 4 bytes
 * @coverage vQueueDelete
 */
void test_vQueueDelete_full( void )
{
    QueueHandle_t xQueue = xQueueCreate( 6, sizeof( uint32_t ) );

    TEST_ASSERT_EQUAL( QUEUE_T_SIZE + ( 6 * 4 ), getLastMallocSize() );

    for( uint32_t i = 0; i < 6; i++ )
    {
        xQueueSend( xQueue, &i, 0 );
    }

    vQueueDelete( xQueue );
    TEST_ASSERT_EQUAL_PTR( ( void * ) xQueue, getLastFreedAddress() );
}

/**
 * @brief Test vQueueDelete asserts when tasks are waiting to send and waiting to receive
 * @details Verify that vQueueDelete triggers a configASSERT when both the
 * xTasksWaitingToSend and xTasksWaitingToReceive lists are non-empty.
 * @coverage vQueueDelete
 */
void test_vQueueDelete_assert_tasks_waiting_to_send_and_receive( void )
{
    QueueHandle_t xQueue = xQueueCreate( 1, sizeof( uint32_t ) );

    /* Add a fake task to the WaitingToSend list */
    td_task_addFakeTaskWaitingToSendToQueue( xQueue );

    /* Expect the assert to fire due to non-empty WaitingToSend list */
    EXPECT_ASSERT_BREAK( vQueueDelete( xQueue ) );

    /* Clean up the fake task from the list */
    td_task_removeFakeTaskFromList();

    /* Now add a fake task to WaitingToReceive and verify that assert fires too */
    td_task_addFakeTaskWaitingToReceiveFromQueue( xQueue );

    EXPECT_ASSERT_BREAK( vQueueDelete( xQueue ) );

    /* Clean up and delete */
    td_task_removeFakeTaskFromList();
    vQueueDelete( xQueue );
}

/**
 * @brief Test vQueueDelete asserts when tasks are waiting to send only
 * @details Verify that vQueueDelete triggers a configASSERT when the
 * xTasksWaitingToSend list is non-empty.
 * @coverage vQueueDelete
 */
void test_vQueueDelete_assert_tasks_waiting_to_send( void )
{
    QueueHandle_t xQueue = xQueueCreate( 1, sizeof( uint32_t ) );

    /* Add a fake task to the WaitingToSend list */
    td_task_addFakeTaskWaitingToSendToQueue( xQueue );

    /* Expect the assert to fire due to non-empty WaitingToSend list */
    EXPECT_ASSERT_BREAK( vQueueDelete( xQueue ) );

    /* Clean up and delete */
    td_task_removeFakeTaskFromList();
    vQueueDelete( xQueue );
}

/**
 * @brief Test vQueueDelete asserts when tasks are waiting to receive only
 * @details Verify that vQueueDelete triggers a configASSERT when the
 * xTasksWaitingToReceive list is non-empty.
 * @coverage vQueueDelete
 */
void test_vQueueDelete_assert_tasks_waiting_to_receive( void )
{
    QueueHandle_t xQueue = xQueueCreate( 1, sizeof( uint32_t ) );

    /* Add a fake task to the WaitingToReceive list */
    td_task_addFakeTaskWaitingToReceiveFromQueue( xQueue );

    /* Expect the assert to fire due to non-empty WaitingToReceive list */
    EXPECT_ASSERT_BREAK( vQueueDelete( xQueue ) );

    /* Clean up and delete */
    td_task_removeFakeTaskFromList();
    vQueueDelete( xQueue );
}
