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
/*! @file queue_status_utest.c */

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

/* =============================  Test Cases ============================== */

/**
 * @brief Test uxQueueMessagesWaiting with an invalid QueueHandle
 * @coverage uxQueueMessagesWaiting
 */
void test_uxQueueMessagesWaiting_invalid_handle( void )
{
    EXPECT_ASSERT_BREAK( uxQueueMessagesWaiting( NULL ) );
}

/**
 * @brief Test uxQueueMessagesWaiting with a queue of size 5 x 4 bytes
 * @details Test uxQueueMessagesWaiting with a typical queue when empty and occupied.
 * @coverage uxQueueMessagesWaiting
 */
void test_uxQueueMessagesWaiting_empty_occupied( void )
{
    QueueHandle_t xQueue = xQueueCreate( 5, sizeof( uint32_t ) );

    TEST_ASSERT_EQUAL( 0, uxQueueMessagesWaiting( xQueue ) );

    for( uint32_t i = 0; i < 5; i++ )
    {
        xQueueSend( xQueue, &i, 0 );
        TEST_ASSERT_EQUAL( i + 1, uxQueueMessagesWaiting( xQueue ) );
    }

    vQueueDelete( xQueue );
}

/**
 * @brief Test uxQueueMessagesWaitingFromISR with an invalid Queue Handle
 * @coverage uxQueueMessagesWaitingFromISR
 */
void test_uxQueueMessagesWaitingFromISR_invalid_handle( void )
{
    EXPECT_ASSERT_BREAK( uxQueueMessagesWaitingFromISR( NULL ) );
}

/**
 * @brief Test uxQueueMessagesWaitingFromISR with a queue of size 5 x 4 bytes
 * @details Test uxQueueMessagesWaitingFromISR with a typical queue when empty and occupied.
 * @coverage uxQueueMessagesWaitingFromISR
 */
void test_uxQueueMessagesWaitingFromISR_empty_occupied( void )
{
    QueueHandle_t xQueue = xQueueCreate( 5, sizeof( uint32_t ) );

    TEST_ASSERT_EQUAL( 0, uxQueueMessagesWaitingFromISR( xQueue ) );

    for( uint32_t i = 0; i < 5; i++ )
    {
        xQueueSend( xQueue, &i, 0 );
        TEST_ASSERT_EQUAL( i + 1, uxQueueMessagesWaitingFromISR( xQueue ) );
    }

    vQueueDelete( xQueue );
}

/**
 * @brief Test uxQueueSpacesAvailable with an invalid QueueHandle
 * @coverage uxQueueSpacesAvailable
 */
void test_uxQueueSpacesAvailable_invalid_handle( void )
{
    EXPECT_ASSERT_BREAK( uxQueueSpacesAvailable( NULL ) );
}

/**
 * @brief Test uxQueueSpacesAvailable with a queue of size 5 x 4 bytes
 * @details Test uxQueueSpacesAvailable with a typical queue when empty and occupied.
 * @coverage uxQueueSpacesAvailable
 */
void test_uxQueueSpacesAvailable_empty_occupied( void )
{
    QueueHandle_t xQueue = xQueueCreate( 5, sizeof( uint32_t ) );

    TEST_ASSERT_EQUAL( 5, uxQueueSpacesAvailable( xQueue ) );

    for( uint32_t i = 0; i < 5; i++ )
    {
        xQueueSend( xQueue, &i, 0 );
        TEST_ASSERT_EQUAL( 4 - i, uxQueueSpacesAvailable( xQueue ) );
    }

    vQueueDelete( xQueue );
}


/**
 * @brief Test xQueueIsQueueEmptyFromISR with an invalid QueueHandle
 * @coverage xQueueIsQueueEmptyFromISR
 */
void test_xQueueIsQueueEmptyFromISR_invalid_handle( void )
{
    EXPECT_ASSERT_BREAK( xQueueIsQueueEmptyFromISR( NULL ) );
}

/**
 * @brief Test xQueueIsQueueEmptyFromISR with a queue of size 5 x 4 bytes
 * @details Test xQueueIsQueueEmptyFromISR with a typical queue when empty and occupied.
 * @coverage xQueueIsQueueEmptyFromISR
 */
void test_xQueueIsQueueEmptyFromISR_empty_occupied( void )
{
    QueueHandle_t xQueue = xQueueCreate( 5, sizeof( uint32_t ) );

    TEST_ASSERT_EQUAL( pdTRUE, xQueueIsQueueEmptyFromISR( xQueue ) );

    for( uint32_t i = 0; i < 5; i++ )
    {
        xQueueSend( xQueue, &i, 0 );
        TEST_ASSERT_EQUAL( pdFALSE, xQueueIsQueueEmptyFromISR( xQueue ) );
    }

    vQueueDelete( xQueue );
}

/**
 * @brief Test xQueueIsQueueFullFromISR with an invalid QueueHandle
 * @coverage xQueueIsQueueFullFromISR
 */
void test_xQueueIsQueueFullFromISR_invalid_handle( void )
{
    EXPECT_ASSERT_BREAK( xQueueIsQueueFullFromISR( NULL ) );
}

/**
 * @brief Test xQueueIsQueueFullFromISR with a queue of size 5 x 4 bytes
 * @details Test xQueueIsQueueFullFromISR with a typical queue when empty and occupied.
 * @coverage xQueueIsQueueFullFromISR
 */
void test_xQueueIsQueueFullFromISR_empty_occupied( void )
{
    QueueHandle_t xQueue = xQueueCreate( 5, sizeof( uint32_t ) );

    for( uint32_t i = 0; i < 5; i++ )
    {
        TEST_ASSERT_EQUAL( pdFALSE, xQueueIsQueueFullFromISR( xQueue ) );
        xQueueSend( xQueue, &i, 0 );
    }

    TEST_ASSERT_EQUAL( pdTRUE, xQueueIsQueueFullFromISR( xQueue ) );

    vQueueDelete( xQueue );
}

/**
 * @brief Test vQueueWaitForMessageRestricted with an empty queue.
 * @details Test vQueueWaitForMessageRestricted with various values for
 *  xTicksToWait and xWaitIndefinitely.
 * @coverage vQueueWaitForMessageRestricted
 */
void test_vQueueWaitForMessageRestricted_empty( void )
{
    QueueHandle_t xQueue = xQueueCreate( 5, sizeof( uint32_t ) );

    struct
    {
        TickType_t xTicksToWait;
        BaseType_t xWaitIndefinitely;
    }
    xTestCaseArray[] =
    {
        { 0,     pdFALSE },
        { 0,     pdTRUE  },
        { 1,     pdFALSE },
        { 1,     pdTRUE  },
        { 10,    pdFALSE },
        { 10,    pdTRUE  },
        { 65536, pdTRUE  }
    };

    List_t * pxTasksWaitingToReceive = pxGetTasksWaitingToReceiveFromQueue( xQueue );

    for( uint32_t i = 0; i < ( sizeof( xTestCaseArray ) / sizeof( xTestCaseArray[ 0 ] ) ); i++ )
    {
        vTaskPlaceOnEventListRestricted_Expect( pxTasksWaitingToReceive,
                                                xTestCaseArray[ i ].xTicksToWait,
                                                xTestCaseArray[ i ].xWaitIndefinitely );
        /* call api function */
        vQueueWaitForMessageRestricted( xQueue,
                                        xTestCaseArray[ i ].xTicksToWait,
                                        xTestCaseArray[ i ].xWaitIndefinitely );
    }

    vQueueDelete( xQueue );
}

/**
 * @brief Test vQueueWaitForMessageRestricted with an occupied queue.
 * @details Test vQueueWaitForMessageRestricted with various values for
 *  xTicksToWait and xWaitIndefinitely.
 * @coverage vQueueWaitForMessageRestricted
 */
void test_vQueueWaitForMessageRestricted_occupied( void )
{
    QueueHandle_t xQueue = xQueueCreate( 5, sizeof( uint32_t ) );

    uint32_t testVal = getNextMonotonicTestValue();

    xQueueSend( xQueue, &testVal, 0 );

    const struct
    {
        TickType_t xTicksToWait;
        BaseType_t xWaitIndefinitely;
    }
    xTestCaseArray[] =
    {
        { 0,     pdFALSE },
        { 0,     pdTRUE  },
        { 1,     pdFALSE },
        { 1,     pdTRUE  },
        { 10,    pdFALSE },
        { 10,    pdTRUE  },
        { 65536, pdTRUE  }
    };

    for( uint32_t i = 0; i < ( sizeof( xTestCaseArray ) / sizeof( xTestCaseArray[ 0 ] ) ); i++ )
    {
        /* call api function */
        vQueueWaitForMessageRestricted( xQueue,
                                        xTestCaseArray[ i ].xTicksToWait,
                                        xTestCaseArray[ i ].xWaitIndefinitely );
        /* Do not expect a call to vTaskPlaceOnEventListRestricted */
    }

    vQueueDelete( xQueue );
}

/**
 * @brief Test vQueueWaitForMessageRestricted on an empty locked queue.
 * @details This test case verifies a situation that should never occur ( vQueueWaitForMessageRestricted called on a locked queue ).
 * @coverage vQueueWaitForMessageRestricted
 */
void test_vQueueWaitForMessageRestricted_locked( void )
{
    /* Create a new binary Queue */
    QueueHandle_t xQueue = xQueueCreate( 1, sizeof( uint32_t ) );

    /* Set private lock counters */
    vSetQueueRxLock( xQueue, queueLOCKED_UNMODIFIED );
    vSetQueueTxLock( xQueue, queueLOCKED_UNMODIFIED );

    List_t * pxTasksWaitingToReceive = pxGetTasksWaitingToReceiveFromQueue( xQueue );

    vTaskPlaceOnEventListRestricted_Expect( pxTasksWaitingToReceive,
                                            10,
                                            pdFALSE );

    /* Run vQueueWaitForMessageRestricted with the queue locked */
    vQueueWaitForMessageRestricted( xQueue, 10, pdFALSE );

    /* Verify that the queue is now unlocked */
    TEST_ASSERT_EQUAL( queueUNLOCKED, cGetQueueRxLock( xQueue ) );
    TEST_ASSERT_EQUAL( queueUNLOCKED, cGetQueueTxLock( xQueue ) );

    vQueueDelete( xQueue );
}
