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
/*! @file queue_delete_static_utest.c */

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

/* =============================  Test Cases ============================== */

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
    void * queueBuffer = malloc( sizeof( StaticQueue_t ) );
    void * queueData = malloc( 6 * sizeof( uint32_t ) );
    QueueHandle_t xQueue = xQueueCreateStatic( 6, sizeof( uint32_t ), queueData, queueBuffer );

    /* Verify that no call to malloc occurred */
    TEST_ASSERT_EQUAL( 0, getLastMallocSize() );

    vQueueDelete( xQueue );
    /* Veirfy that free was not called */
    TEST_ASSERT_EQUAL_PTR( NULL, getLastFreedAddress() );
    free( queueBuffer );
    free( queueData );
}

/**
 * @brief Test vQueueDelete with a half-full queue of size 6 x 4 bytes
 * @coverage vQueueDelete
 */
void test_vQueueDelete_half_full( void )
{
    void * queueBuffer = malloc( sizeof( StaticQueue_t ) );
    void * queueData = malloc( 6 * sizeof( uint32_t ) );
    QueueHandle_t xQueue = xQueueCreateStatic( 6, sizeof( uint32_t ), queueData, queueBuffer );

    /* Verify that no call to malloc occurred */
    TEST_ASSERT_EQUAL( 0, getLastMallocSize() );

    for( uint32_t i = 0; i < 3; i++ )
    {
        xQueueSend( xQueue, &i, 0 );
    }

    vQueueDelete( xQueue );

    /* Veirfy that free was not called */
    TEST_ASSERT_EQUAL_PTR( NULL, getLastFreedAddress() );
    free( queueBuffer );
    free( queueData );
}

/**
 * @brief Test vQueueDelete with a full queue of size 6 x 4 bytes
 * @coverage vQueueDelete
 */
void test_vQueueDelete_full( void )
{
    void * queueBuffer = malloc( sizeof( StaticQueue_t ) );
    void * queueData = malloc( 6 * sizeof( uint32_t ) );
    QueueHandle_t xQueue = xQueueCreateStatic( 6, sizeof( uint32_t ), queueData, queueBuffer );

    /* Verify that no call to malloc occurred */
    TEST_ASSERT_EQUAL( 0, getLastMallocSize() );

    for( uint32_t i = 0; i < 6; i++ )
    {
        xQueueSend( xQueue, &i, 0 );
    }

    vQueueDelete( xQueue );

    /* Veirfy that free was not called */
    TEST_ASSERT_EQUAL_PTR( NULL, getLastFreedAddress() );
    free( queueBuffer );
    free( queueData );
}
