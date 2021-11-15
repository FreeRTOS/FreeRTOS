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
/*! @file queue_trace_utest.c */

/* C runtime includes. */
#include <stdlib.h>
#include <stdbool.h>
#include <string.h>

#include "../queue_utest_common.h"

/* Queue includes */
#include "FreeRTOS.h"
#include "FreeRTOSConfig.h"
#include "queue.h"
#include "semphr.h"

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
 * @brief Test vQueueSetQueueNumber and uxQueueGetQueueNumber
 * @details Verify that the queue number set with vQueueSetQueueNumber is returned
 *  by a subsequent call to uxQueueGetQueueNumber.
 * @coverage vQueueSetQueueNumber uxQueueGetQueueNumber
 */
void test_vQueueSetQueueNumber_uxQueueGetQueueNumber( void )
{
    QueueHandle_t xQueue = xQueueCreate( 1, sizeof( uint32_t ) );

    vQueueSetQueueNumber( xQueue, getNextMonotonicTestValue() );

    TEST_ASSERT_EQUAL( getLastMonotonicTestValue(), uxQueueGetQueueNumber( xQueue ) );
    vQueueDelete( xQueue );
}

/**
 * @brief Test vQueueSetQueueNumber and uxQueueGetQueueNumber with UINT64_MAX
 * @details Verify that the queue number of UINT64_MAX set with
 * vQueueSetQueueNumber is returned by a subsequent call to uxQueueGetQueueNumber.
 * @coverage vQueueSetQueueNumber uxQueueGetQueueNumber
 */
void test_vQueueSetQueueNumber_uxQueueGetQueueNumber_max( void )
{
    QueueHandle_t xQueue = xQueueCreate( 1, sizeof( uint32_t ) );

    vQueueSetQueueNumber( xQueue, UINT64_MAX );

    TEST_ASSERT_EQUAL( UINT64_MAX, uxQueueGetQueueNumber( xQueue ) );
    vQueueDelete( xQueue );
}

/**
 * @brief Test vQueueSetQueueNumber and uxQueueGetQueueNumber with 0
 * @details Verify that the queue number of 0 set with vQueueSetQueueNumber
 * is returned by a subsequent call to uxQueueGetQueueNumber.
 * @coverage vQueueSetQueueNumber uxQueueGetQueueNumber
 */
void test_vQueueSetQueueNumber_uxQueueGetQueueNumber_zero( void )
{
    QueueHandle_t xQueue = xQueueCreate( 1, sizeof( uint32_t ) );

    vQueueSetQueueNumber( xQueue, 0 );

    TEST_ASSERT_EQUAL( 0, uxQueueGetQueueNumber( xQueue ) );
    vQueueDelete( xQueue );
}

/**
 * @brief Test ucQueueGetQueueType with a Queue
 * @details Verify that ucQueueGetQueueType returns queueQUEUE_TYPE_BASE for a normal queue.
 * @coverage ucQueueGetQueueType prvInitialiseNewQueue
 */
void test_ucQueueGetQueueType_queue( void )
{
    QueueHandle_t xQueue = xQueueCreate( 1, sizeof( uint32_t ) );

    TEST_ASSERT_EQUAL( queueQUEUE_TYPE_BASE, ucQueueGetQueueType( xQueue ) );
    vQueueDelete( xQueue );
}

/**
 * @brief Test ucQueueGetQueueType with a QueueSet
 * @details Verify that ucQueueGetQueueType returns queueQUEUE_TYPE_SET for a QueueSet.
 * @coverage ucQueueGetQueueType prvInitialiseNewQueue
 */
void test_ucQueueGetQueueType_queue_set( void )
{
    QueueSetHandle_t xQueueSet = xQueueCreateSet( 1 );

    TEST_ASSERT_EQUAL( queueQUEUE_TYPE_SET, ucQueueGetQueueType( xQueueSet ) );
    vQueueDelete( xQueueSet );
}

/**
 * @brief Test ucQueueGetQueueType with a Mutex
 * @details Verify that ucQueueGetQueueType returns queueQUEUE_TYPE_MUTEX for a Mutex.
 * @coverage ucQueueGetQueueType prvInitialiseNewQueue
 */
void test_ucQueueGetQueueType_mutex( void )
{
    xTaskPriorityDisinherit_ExpectAndReturn( NULL, pdFALSE );
    SemaphoreHandle_t xSemaphore = xSemaphoreCreateMutex();

    TEST_ASSERT_EQUAL( queueQUEUE_TYPE_MUTEX, ucQueueGetQueueType( xSemaphore ) );
    vSemaphoreDelete( xSemaphore );
}

/**
 * @brief Test ucQueueGetQueueType with a Counting Semaphore
 * @details Verify that ucQueueGetQueueType returns queueQUEUE_TYPE_COUNTING_SEMAPHORE for a Counting Semaphore.
 * @coverage ucQueueGetQueueType prvInitialiseNewQueue
 */
void test_ucQueueGetQueueType_counting_semaphore( void )
{
    SemaphoreHandle_t xSemaphore = xSemaphoreCreateCounting( 1, 0 );

    TEST_ASSERT_EQUAL( queueQUEUE_TYPE_COUNTING_SEMAPHORE, ucQueueGetQueueType( xSemaphore ) );
    vSemaphoreDelete( xSemaphore );
}

/**
 * @brief Test ucQueueGetQueueType with a Binary Semaphore
 * @details Verify that ucQueueGetQueueType returns queueQUEUE_TYPE_BINARY_SEMAPHORE for a Binary Semaphore.
 * @coverage ucQueueGetQueueType prvInitialiseNewQueue
 */
void test_ucQueueGetQueueType_binary_semaphore( void )
{
    SemaphoreHandle_t xSemaphore = xSemaphoreCreateBinary();

    TEST_ASSERT_EQUAL( queueQUEUE_TYPE_BINARY_SEMAPHORE, ucQueueGetQueueType( xSemaphore ) );
    vSemaphoreDelete( xSemaphore );
}

/**
 * @brief Test ucQueueGetQueueType with a Recursive Mutex
 * @details Verify that ucQueueGetQueueType returns queueQUEUE_TYPE_RECURSIVE_MUTEX for a Recursive Mutex.
 * @coverage ucQueueGetQueueType prvInitialiseNewQueue
 */
void test_ucQueueGetQueueType_recursive_mutex( void )
{
    xTaskPriorityDisinherit_ExpectAndReturn( NULL, pdFALSE );
    SemaphoreHandle_t xSemaphore = xSemaphoreCreateRecursiveMutex();

    TEST_ASSERT_EQUAL( queueQUEUE_TYPE_RECURSIVE_MUTEX, ucQueueGetQueueType( xSemaphore ) );
    vSemaphoreDelete( xSemaphore );
}
