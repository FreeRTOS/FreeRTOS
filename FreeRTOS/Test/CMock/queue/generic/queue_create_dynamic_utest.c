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
/*! @file queue_create_dynamic_utest.c */

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
 * @brief Test xQueueCreate when calls to malloc fail
 * @coverage xQueueGenericCreate
 */
void test_macro_xQueueCreate_malloc_fail( void )
{
    UnityMalloc_MakeMallocFailAfterCount( 0 );

    QueueHandle_t xQueue = INVALID_PTR;

    xQueue = xQueueCreate( 1, 1 );

    TEST_ASSERT_EQUAL( NULL, xQueue );
}

/**
 * @brief Test xQueueCreate with uxQueueLength=0, uxItemSize=0
 * @details This is an invalid queue configuration and causes a failed configASSERT.
 * @coverage xQueueGenericCreate
 */
void test_macro_xQueueCreate_zeroQueueLength_zeroItemSize()
{
    /* Expect that xQueueCreate will assert because a length of 0 is invalid */
    fakeAssertExpectFail();

    QueueHandle_t xQueue = xQueueCreate( 0, 0 );

    /* validate returned queue handle */
    TEST_ASSERT_EQUAL( NULL, xQueue );

    /* verify that configASSERT was called */
    TEST_ASSERT_EQUAL( true, fakeAssertGetFlagAndClear() );
    TEST_ASSERT_EQUAL( 0, getNumberMallocCalls() );
}

/**
 * @brief Test xQueueCreate with uxQueueLength=0, uxItemSize=1
 * @details This is an invalid queue configuration and causes a failed configASSERT.
 * @coverage xQueueGenericCreate
 */
void test_macro_xQueueCreate_zeroQueueLength_oneItemSize( void )
{
    /* Expect that xQueueCreate will assert because a length of 0 is invalid */
    fakeAssertExpectFail();

    QueueHandle_t xQueue = xQueueCreate( 0, 1 );

    /* validate returned queue handle */
    TEST_ASSERT_EQUAL( NULL, xQueue );

    /* verify that configASSERT was called */
    TEST_ASSERT_EQUAL( true, fakeAssertGetFlagAndClear() );
    TEST_ASSERT_EQUAL( 0, getNumberMallocCalls() );
}

/**
 * @brief Test xQueueCreate with uxQueueLength=1, uxItemSize=0
 * @details This configuration is equivalent to a binary semaphore.
 * @coverage xQueueGenericCreate
 */
void test_macro_xQueueCreate_oneItem_zeroLength( void )
{
    QueueHandle_t xQueue = xQueueCreate( 1, 0 );

    /* validate returned queue handle */
    TEST_ASSERT_NOT_EQUAL( NULL, xQueue );

    TEST_ASSERT_EQUAL( QUEUE_T_SIZE, getLastMallocSize() );

    /* Veify that new queue is empty */
    TEST_ASSERT_EQUAL( 0, uxQueueMessagesWaiting( xQueue ) );

    /* Valdiate that the queue has 1 space remaining */
    TEST_ASSERT_EQUAL( 1, uxQueueSpacesAvailable( xQueue ) );

    vQueueDelete( xQueue );
}

/**
 * @brief Test xQueueCreate with uxQueueLength=1, uxItemSize=1
 * @details This configuration is equivalent to a 1 byte mailbox.
 * @coverage xQueueGenericCreate
 */
void test_macro_xQueueCreate_oneItem_oneLength( void )
{
    QueueHandle_t xQueue = xQueueCreate( 1, 1 );

    /* validate returned queue handle */
    TEST_ASSERT_NOT_EQUAL( NULL, xQueue );

    TEST_ASSERT_EQUAL( QUEUE_T_SIZE + 1, getLastMallocSize() );

    /* Veify that new queue is empty */
    TEST_ASSERT_EQUAL( 0, uxQueueMessagesWaiting( xQueue ) );

    uint8_t testval = ( uint8_t ) getNextMonotonicTestValue();

    TEST_ASSERT_EQUAL( pdTRUE, xQueueSend( xQueue, &testval, 0 ) );

    /* Veify that queue is full */
    TEST_ASSERT_EQUAL( 1, uxQueueMessagesWaiting( xQueue ) );
    TEST_ASSERT_EQUAL( 0, uxQueueSpacesAvailable( xQueue ) );

    uint8_t testVal2 = 0xFF;

    /* Receive from the queue */
    TEST_ASSERT_EQUAL( pdTRUE, xQueueReceive( xQueue, &testVal2, 0 ) );
    TEST_ASSERT_EQUAL( testval, testVal2 );

    /* Veify that queue is empty */
    TEST_ASSERT_EQUAL( 0, uxQueueMessagesWaiting( xQueue ) );
    TEST_ASSERT_EQUAL( 1, uxQueueSpacesAvailable( xQueue ) );

    vQueueDelete( xQueue );
}

/*!
 * @brief Test xQueueCreate with uxQueueLength=1, uxItemSize=[2,16]
 * @details End to end test with varied mailbox sizes from 2 to 16 bytes.
 * @coverage xQueueGenericCreate
 */
void test_macro_xQueueCreate_oneItem_multiLength( void )
{
    uint8_t testVal[ MAX_MULTI_LEN ];

    /* Generate test pattern to send to the queue (re-used for each iteration) */
    for( int i = 0; i < MAX_MULTI_LEN; i++ )
    {
        testVal[ i ] = ( uint8_t ) getNextMonotonicTestValue();
    }

    for( uint8_t i = 2; i <= MAX_MULTI_LEN; i++ )
    {
        QueueHandle_t xQueue = xQueueCreate( 1, i );

        TEST_ASSERT_EQUAL( QUEUE_T_SIZE + i, getLastMallocSize() );

        /* Veify that queue is empty */
        TEST_ASSERT_EQUAL( 0, uxQueueMessagesWaiting( xQueue ) );

        /* Mask off the bytes we won't use */
        uint8_t testValCompare[ MAX_MULTI_LEN ];

        for( int j = 0; j < MAX_MULTI_LEN; j++ )
        {
            if( j < i )
            {
                testValCompare[ j ] = testVal[ j ];
            }
            else
            {
                testValCompare[ j ] = 0xFF;
            }
        }

        TEST_ASSERT_EQUAL( pdTRUE, xQueueSend( xQueue, &testVal, 0 ) );

        /* Veify that queue is also full */
        TEST_ASSERT_EQUAL( 0, uxQueueSpacesAvailable( xQueue ) );

        uint8_t testValCheck[ MAX_MULTI_LEN ];
        memset( testValCheck, 0xFF, MAX_MULTI_LEN );

        /* Receive from the queue */
        TEST_ASSERT_EQUAL( pdTRUE, xQueueReceive( xQueue, &testValCheck, 0 ) );
        TEST_ASSERT_EQUAL_MEMORY( testValCompare, testValCheck, MAX_MULTI_LEN );

        /* Veify that queue is empty */
        TEST_ASSERT_EQUAL( 0, uxQueueMessagesWaiting( xQueue ) );

        vQueueDelete( xQueue );
    }
}

/*!
 * @brief xQueueCreate with a large queue.
 * @coverage xQueueCreate
 */
void test_LargeQueueRunThrough( void )
{
    QueueHandle_t xQueue = xQueueCreate( MAX_QUEUE_ITEMS, sizeof( uint32_t ) );

    test_long_queue( xQueue, MAX_QUEUE_ITEMS );

    vQueueDelete( xQueue );
}

/**
 * @brief xQueueCreate where uxQueueLength * uxItemSize results in integer overflow
 * @details In this test case xQueueSizeInBytes > MAX(size_t), but individually
 *  uxQueueLength and uxItemSize are each less than MAX(size_t).
 * @coverage xQueueGenericCreate
 */
void test_macro_xQueueCreate_multiplication_overflow( void )
{
    /* Calculate a test value = 2^( sizeof(size_t) * 8 bits / 2)
     * For a 64 bit size_t, this is 2^(8*8/2) = 2^(32) */
    size_t factor = 1ULL << ( sizeof( size_t ) * 4 );

    EXPECT_ASSERT_BREAK( xQueueCreate( factor, factor ) );
}

/*!
 * @brief xQueueCreate where adding xQueueSizeInBytes and sizeof(StaticQueue_t)
 *  results in integer overflow.
 * @details This test case satisfies the following constraints given that:
 *  xQueueSizeInBytes = (uxQueueLength * uxItemSize),
 *  xQueueSizeInBytes <= MAX(size_t) and
 *  ( xQueueSizeInBytes + sizeof(StaticQueue_t) ) > MAX(size_t)
 * @coverage xQueueGenericCreate
 */
void test_macro_xQueueCreate_addiiton_overflow( void )
{
    /* Based on the formula:
     *  ( 2^x - 1 ) == ( 2^( x/2 ) + 1 ) * ( 2^( x/2 ) - 1 ) */
    size_t powTwo = 1ULL << ( sizeof( size_t ) * 4 );
    size_t factorA = powTwo - 1;
    size_t factorB = powTwo + 1;

    EXPECT_ASSERT_BREAK( xQueueCreate( factorA, factorB ) );
}
