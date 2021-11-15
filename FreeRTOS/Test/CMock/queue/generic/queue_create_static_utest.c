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
/*! @file queue_create_static_utest.c */

/* C runtime includes. */
#include <stdlib.h>
#include <stdbool.h>
#include <string.h>

#include "../queue_utest_common.h"

/* Queue includes */
#include "FreeRTOS.h"
#include "FreeRTOSConfig.h"
#include "queue.h"

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


static void test_long_queue( QueueHandle_t xQueue,
                             uint32_t maxItems )
{
    /* Veify that queue is empty */
    TEST_ASSERT_EQUAL( 0, uxQueueMessagesWaiting( xQueue ) );

    queue_common_add_sequential_to_queue( xQueue, maxItems );

    /* Veify that queue is full */
    TEST_ASSERT_EQUAL( 0, uxQueueSpacesAvailable( xQueue ) );

    queue_common_receive_sequential_from_queue( xQueue, maxItems, maxItems, 0 );

    /* Veify that queue is empty */
    TEST_ASSERT_EQUAL( 0, uxQueueMessagesWaiting( xQueue ) );
}


/* ==========================  Test Cases =========================== */

/**
 * @brief xQueueCreateStatic with a NULL pointer for queueStorage
 * @coverage xQueueGenericCreateStatic
 */
void test_macro_xQueueCreateStatic_null_QueueStorage_fail( void )
{
    /* Expect that xQueueCreate will assert */
    fakeAssertExpectFail();

    StaticQueue_t queueBuffer;
    QueueHandle_t xQueue = xQueueCreateStatic( MAX_QUEUE_ITEMS, sizeof( uint32_t ), NULL, &queueBuffer );

    /* Validate the queue handle */
    TEST_ASSERT_EQUAL( NULL, xQueue );

    TEST_ASSERT_EQUAL( true, fakeAssertGetFlagAndClear() );
}

/**
 * @brief xQueueCreateStatic with a NULL pointer for queueBuffer
 * @coverage xQueueGenericCreateStatic
 */
void test_macro_xQueueCreateStatic_null_queueBuffer_fail( void )
{
    /* Expect that xQueueCreate will assert */
    fakeAssertExpectFail();

    uint32_t queueStorage[ MAX_QUEUE_ITEMS ];
    QueueHandle_t xQueue = INVALID_PTR;

    xQueue = xQueueCreateStatic( MAX_QUEUE_ITEMS, sizeof( uint32_t ), ( void * ) queueStorage, NULL );

    /* Validate that the queue handle is NULL */
    TEST_ASSERT_EQUAL( NULL, xQueue );

    /* Check that configASSERT was called twice */
    fakeAssertVerifyNumAssertsAndClear( 2 );
}

/**
 * @brief Test xQueueCreateStatic with a NULL buffer, uxQueueLength=1, uxItemSize=0
 * @details This configuration is equivalent to a binary semaphore.
 * @coverage xQueueGenericCreateStatic
 */
void test_macro_xQueueCreateStatic_nullQueueStorage_oneItem_zeroLength( void )
{
    StaticQueue_t queueBuffer;
    QueueHandle_t xQueue = xQueueCreateStatic( 1, 0, NULL, &queueBuffer );

    /* validate returned queue handle */
    TEST_ASSERT_NOT_EQUAL( NULL, xQueue );

    /* Veify that new queue is empty */
    TEST_ASSERT_EQUAL( 0, uxQueueMessagesWaiting( xQueue ) );

    /* Valdiate that the queue has 1 space remaining */
    TEST_ASSERT_EQUAL( 1, uxQueueSpacesAvailable( xQueue ) );

    /* Send a test value */
    TEST_ASSERT_EQUAL( pdTRUE, xQueueSend( xQueue, NULL, 0 ) );

    /* Test receive */
    TEST_ASSERT_EQUAL( pdTRUE, xQueueReceive( xQueue, NULL, 0 ) );

    vQueueDelete( xQueue );
}

/**
 * @brief Test xQueueCreateStatic with uxQueueLength=0, uxItemSize=0
 * @details This configuration is invalid and causes a configASSERT.
 * @coverage xQueueGenericCreateStatic
 */
void test_macro_xQueueCreateStatic_validQueueStorage_zeroItem_zeroLength( void )
{
    StaticQueue_t queueBuffer;

    /* Expect that xQueueCreateStatic will assert because a zero length queue is invalid */
    fakeAssertExpectFail();
    QueueHandle_t xQueue = xQueueCreateStatic( 0, 0, NULL, &queueBuffer );

    /* verify that configASSERT was called */
    TEST_ASSERT_EQUAL( true, fakeAssertGetFlagAndClear() );

    /* validate returned queue handle */
    TEST_ASSERT_EQUAL( NULL, xQueue );
}

/**
 * @brief Test xQueueCreateStatic with a valid buffer, uxQueueLength=1, uxItemSize=0
 * @details This configuration is invalid and causes a configASSERT.
 * @coverage xQueueGenericCreateStatic
 */
void test_macro_xQueueCreateStatic_validQueueStorage_oneItem_zeroLength( void )
{
    StaticQueue_t queueBuffer;
    uint32_t queueData;

    /* Expect that xQueueCreateStatic will assert because data storage is
     *   prohibited for a zero itemLength queue */
    fakeAssertExpectFail();
    QueueHandle_t xQueue = xQueueCreateStatic( 1, 0, ( void * ) &queueData, &queueBuffer );

    /* verify that configASSERT was called */
    TEST_ASSERT_EQUAL( true, fakeAssertGetFlagAndClear() );

    /* validate returned queue handle */
    TEST_ASSERT_EQUAL( NULL, xQueue );
}

/**
 * @brief xQueueCreateStatic with a large queue.
 * @coverage xQueueGenericCreateStatic
 */
void test_macro_xQueueCreateStatic_large( void )
{
    uint32_t queueStorage[ MAX_QUEUE_ITEMS ];
    StaticQueue_t queueBuffer;
    QueueHandle_t xQueue = xQueueCreateStatic( MAX_QUEUE_ITEMS, sizeof( uint32_t ), ( void * ) queueStorage, &queueBuffer );

    test_long_queue( xQueue, MAX_QUEUE_ITEMS );
    vQueueDelete( xQueue );
}
