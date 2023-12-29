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
/*! @file queue_reset_utest.c */

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

/* ==========================  Test Cases =========================== */

/**
 * @brief Test xQueueReset with an invalid queue handle
 * @coverage xQueueGenericReset
 */
void test_macro_xQueueReset_invalid_handle( void )
{
    EXPECT_ASSERT_BREAK( xQueueReset( NULL ) );
}

/**
 * @brief Test xQueueReset with an empty queue of size 6 x 4 bytes
 * @coverage xQueueGenericReset
 */
void test_macro_xQueueReset_empty( void )
{
    QueueHandle_t xQueue = xQueueCreate( 6, sizeof( uint32_t ) );

    TEST_ASSERT_EQUAL( 0, uxQueueMessagesWaiting( xQueue ) );

    TEST_ASSERT_EQUAL( pdPASS, xQueueReset( xQueue ) );

    TEST_ASSERT_EQUAL( 0, uxQueueMessagesWaiting( xQueue ) );

    vQueueDelete( xQueue );
}

/**
 * @brief Test xQueueReset with a half-full queue of size 6 x 4 bytes
 * @coverage xQueueGenericReset
 */
void test_macro_xQueueReset_half_full( void )
{
    QueueHandle_t xQueue = xQueueCreate( 6, sizeof( uint32_t ) );

    TEST_ASSERT_EQUAL( 0, uxQueueMessagesWaiting( xQueue ) );

    for( uint32_t i = 0; i < 3; i++ )
    {
        xQueueSend( xQueue, &i, 0 );
    }

    TEST_ASSERT_EQUAL( 3, uxQueueMessagesWaiting( xQueue ) );

    TEST_ASSERT_EQUAL( pdPASS, xQueueReset( xQueue ) );

    TEST_ASSERT_EQUAL( 0, uxQueueMessagesWaiting( xQueue ) );

    vQueueDelete( xQueue );
}

/**
 * @brief Test xQueueReset with a full queue of size 6 x 4 bytes
 * @coverage xQueueGenericReset
 */
void test_macro_xQueueReset_full( void )
{
    QueueHandle_t xQueue = xQueueCreate( 6, sizeof( uint32_t ) );

    TEST_ASSERT_EQUAL( 0, uxQueueMessagesWaiting( xQueue ) );

    for( uint32_t i = 0; i < 6; i++ )
    {
        xQueueSend( xQueue, &i, 0 );
    }

    TEST_ASSERT_EQUAL( 6, uxQueueMessagesWaiting( xQueue ) );

    TEST_ASSERT_EQUAL( pdPASS, xQueueReset( xQueue ) );

    TEST_ASSERT_EQUAL( 0, uxQueueMessagesWaiting( xQueue ) );

    vQueueDelete( xQueue );
}

/**
 * @brief Test xQueueReset with a queue of size 6 x 4 bytes
 * and a simulated higher priority task that is blocked waiting send to the queue.
 * @coverage xQueueGenericReset
 */
void test_macro_xQueueReset_tasks_waiting_higher_priority( void )
{
    QueueHandle_t xQueue = xQueueCreate( 6, sizeof( uint32_t ) );

    TEST_ASSERT_EQUAL( 0, uxQueueMessagesWaiting( xQueue ) );

    /* Fill the queue */
    for( uint32_t i = 0; i < 6; i++ )
    {
        xQueueSend( xQueue, &i, 0 );
    }

    /* Insert an item into the event list */
    td_task_setFakeTaskPriority( DEFAULT_PRIORITY + 1 );
    td_task_addFakeTaskWaitingToSendToQueue( xQueue );

    vTaskYieldWithinAPI_Stub( vTaskYieldWithinAPI_Callback );

    TEST_ASSERT_EQUAL( pdTRUE, xQueueReset( xQueue ) );

    TEST_ASSERT_EQUAL( 1, td_task_getYieldCount() );

    TEST_ASSERT_EQUAL( 1, td_task_getCount_vPortYieldWithinAPI() );

    vQueueDelete( xQueue );
}

/**
 * @brief Test xQueueReset with a queue of size 6 x 4 bytes
 * and a simulated lower priority task that is blocked waiting to send to the queue.
 * xTasksWaitingToSend
 * @coverage xQueueGenericReset
 */
void test_macro_xQueueReset_tasks_waiting_lower_priority( void )
{
    QueueHandle_t xQueue = xQueueCreate( 6, sizeof( uint32_t ) );

    TEST_ASSERT_EQUAL( 0, uxQueueMessagesWaiting( xQueue ) );

    /* Fill the queue */
    for( uint32_t i = 0; i < 6; i++ )
    {
        xQueueSend( xQueue, &i, 0 );
    }

    /* Insert an item into the event list */
    td_task_setFakeTaskPriority( DEFAULT_PRIORITY - 1 );
    td_task_addFakeTaskWaitingToSendToQueue( xQueue );

    TEST_ASSERT_EQUAL( pdTRUE, xQueueReset( xQueue ) );

    vQueueDelete( xQueue );
}
