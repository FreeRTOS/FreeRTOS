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
/*! @file queue_set_utest.c */

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

/* ==========================  Test Cases =========================== */

/**
 * @brief Test xQueueCreateSet when calls to malloc fail.
 * @coverage xQueueCreateSet
 */
void test_xQueueCreateSet_malloc_fail( void )
{
    UnityMalloc_MakeMallocFailAfterCount( 0 );

    QueueSetHandle_t xQueueSet = INVALID_PTR;

    xQueueSet = xQueueCreateSet( 1 );

    TEST_ASSERT_EQUAL( NULL, xQueueSet );
}

/**
 * @brief Test xQueueCreateSet with uxEventQueueLength=0
 * @coverage xQueueCreateSet
 */
void test_xQueueCreateSet_zeroLength( void )
{
    /* Expect that xQueueCreateSet will assert because a length of 0 is invalid */
    fakeAssertExpectFail();

    QueueSetHandle_t xQueueSet = xQueueCreateSet( 0 );

    /* validate returned QueueSet handle */
    TEST_ASSERT_EQUAL( NULL, xQueueSet );

    /* verify that configASSERT was called */
    TEST_ASSERT_EQUAL( true, fakeAssertGetFlagAndClear() );
    TEST_ASSERT_EQUAL( 0, getLastMallocSize() );
}

/**
 * @brief Test xQueueCreateSet with uxEventQueueLength=1
 * @coverage xQueueCreateSet
 */
void test_xQueueCreateSet_oneLength( void )
{
    QueueSetHandle_t xQueueSet = xQueueCreateSet( 1 );

    /* validate returned QueueSet handle */
    TEST_ASSERT_NOT_EQUAL( NULL, xQueueSet );

    TEST_ASSERT_EQUAL( QUEUE_T_SIZE + sizeof( void * ), getLastMallocSize() );

    /* Verify that QueueSet is not full */
    TEST_ASSERT_EQUAL( 1, uxQueueSpacesAvailable( xQueueSet ) );

    /* Verify that QueueSet is empty */
    TEST_ASSERT_EQUAL( 0, uxQueueMessagesWaiting( xQueueSet ) );

    vQueueDelete( xQueueSet );
}

/**
 * @brief Test xQueueAddToSet with the same queue twice
 * @coverage xQueueAddToSet
 */
void test_xQueueAddToSet_AlreadyInSameSet( void )
{
    QueueSetHandle_t xQueueSet = xQueueCreateSet( 2 );

    QueueHandle_t xQueue = xQueueCreate( 1, 0 );

    TEST_ASSERT_EQUAL( pdTRUE, xQueueAddToSet( xQueue, xQueueSet ) );

    TEST_ASSERT_EQUAL( pdFALSE, xQueueAddToSet( xQueue, xQueueSet ) );

    ( void ) xQueueRemoveFromSet( xQueue, xQueueSet );
    vQueueDelete( xQueueSet );
    vQueueDelete( xQueue );
}

/**
 * @brief Test xQueueAddToSet with a queue that is already a member of a different QueueSet.
 * @coverage xQueueAddToSet
 */
void test_xQueueAddToSet_AlreadyInDifferentSet( void )
{
    QueueSetHandle_t xQueueSet1 = xQueueCreateSet( 1 );

    QueueSetHandle_t xQueueSet2 = xQueueCreateSet( 1 );

    QueueHandle_t xQueue = xQueueCreate( 1, 0 );

    TEST_ASSERT_EQUAL( pdTRUE, xQueueAddToSet( xQueue, xQueueSet1 ) );

    TEST_ASSERT_EQUAL( pdFALSE, xQueueAddToSet( xQueue, xQueueSet2 ) );

    ( void ) xQueueRemoveFromSet( xQueue, xQueueSet1 );
    vQueueDelete( xQueueSet1 );
    vQueueDelete( xQueueSet2 );
    vQueueDelete( xQueue );
}

/**
 * @brief Test xQueueAddToSet with a queue that was previously a member of a different QueueSet, which was deleted.
 * @coverage xQueueAddToSet
 */
void test_xQueueAddToSet_PreviouslyInDifferentSet( void )
{
    QueueSetHandle_t xQueueSet1 = xQueueCreateSet( 1 );
    QueueSetHandle_t xQueueSet2 = xQueueCreateSet( 1 );

    QueueHandle_t xQueue = xQueueCreate( 1, 0 );

    TEST_ASSERT_EQUAL( pdTRUE, xQueueAddToSet( xQueue, xQueueSet1 ) );

    ( void ) xQueueRemoveFromSet( xQueue, xQueueSet1 );
    vQueueDelete( xQueueSet1 );

    TEST_ASSERT_EQUAL( pdTRUE, xQueueAddToSet( xQueue, xQueueSet2 ) );

    ( void ) xQueueRemoveFromSet( xQueue, xQueueSet2 );
    vQueueDelete( xQueue );
    vQueueDelete( xQueueSet2 );
}

/**
 * @brief Test xQueueAddToSet with a queue that is not empty.
 * @coverage xQueueAddToSet
 */
void test_xQueueAddToSet_QueueNotEmpty( void )
{
    QueueSetHandle_t xQueueSet = xQueueCreateSet( 1 );

    QueueHandle_t xQueue = xQueueCreate( 1, 0 );

    TEST_ASSERT_EQUAL( pdTRUE, xQueueSend( xQueue, NULL, 0 ) );

    TEST_ASSERT_EQUAL( pdFALSE, xQueueAddToSet( xQueue, xQueueSet ) );

    ( void ) xQueueRemoveFromSet( xQueue, xQueueSet );
    vQueueDelete( xQueueSet );
    vQueueDelete( xQueue );
}

/**
 * @brief Test xQueueSelectFromSet with multiple queues in a set.
 * @coverage xQueueSelectFromSet
 */
void test_xQueueSelectFromSet( void )
{
    QueueSetHandle_t xQueueSet = xQueueCreateSet( 3 );

    QueueHandle_t xQueue1 = xQueueCreate( 1, sizeof( uint32_t ) );
    QueueHandle_t xQueue2 = xQueueCreate( 1, sizeof( uint32_t ) );
    QueueHandle_t xQueue3 = xQueueCreate( 1, sizeof( uint32_t ) );

    TEST_ASSERT_EQUAL( pdTRUE, xQueueAddToSet( xQueue1, xQueueSet ) );
    TEST_ASSERT_EQUAL( pdTRUE, xQueueAddToSet( xQueue2, xQueueSet ) );
    TEST_ASSERT_EQUAL( pdTRUE, xQueueAddToSet( xQueue3, xQueueSet ) );

    uint32_t testVal1 = 1;

    TEST_ASSERT_EQUAL( pdTRUE, xQueueSend( xQueue1, &testVal1, 0 ) );

    uint32_t testVal2 = 2;

    TEST_ASSERT_EQUAL( pdTRUE, xQueueSend( xQueue2, &testVal2, 0 ) );

    uint32_t testVal3 = 3;

    TEST_ASSERT_EQUAL( pdTRUE, xQueueSend( xQueue3, &testVal3, 0 ) );

    QueueHandle_t xQueueTemp = xQueueSelectFromSet( xQueueSet, 0 );

    TEST_ASSERT_EQUAL( xQueueTemp, xQueue1 );

    uint32_t checkVal1 = 0;

    TEST_ASSERT_EQUAL( pdTRUE, xQueueReceive( xQueueTemp, &checkVal1, 0 ) );
    TEST_ASSERT_EQUAL( testVal1, checkVal1 );

    xQueueTemp = xQueueSelectFromSet( xQueueSet, 0 );

    TEST_ASSERT_EQUAL( xQueueTemp, xQueue2 );

    uint32_t checkVal2 = 0;

    TEST_ASSERT_EQUAL( pdTRUE, xQueueReceive( xQueueTemp, &checkVal2, 0 ) );
    TEST_ASSERT_EQUAL( testVal2, checkVal2 );

    xQueueTemp = xQueueSelectFromSet( xQueueSet, 0 );

    TEST_ASSERT_EQUAL( xQueueTemp, xQueue3 );

    uint32_t checkVal3 = 0;

    TEST_ASSERT_EQUAL( pdTRUE, xQueueReceive( xQueueTemp, &checkVal3, 0 ) );
    TEST_ASSERT_EQUAL( testVal3, checkVal3 );

    ( void ) xQueueRemoveFromSet( xQueue1, xQueueSet );
    ( void ) xQueueRemoveFromSet( xQueue2, xQueueSet );
    ( void ) xQueueRemoveFromSet( xQueue3, xQueueSet );
    vQueueDelete( xQueueSet );
    vQueueDelete( xQueue1 );
    vQueueDelete( xQueue2 );
    vQueueDelete( xQueue3 );
}

/**
 * @brief Test xQueueSelectFromSetFromISR with multiple queues in a set.
 * @coverage xQueueSelectFromSetFromISR
 */
void test_xQueueSelectFromSetFromISR( void )
{
    QueueSetHandle_t xQueueSet = xQueueCreateSet( 3 );

    QueueHandle_t xQueue1 = xQueueCreate( 1, sizeof( uint32_t ) );
    QueueHandle_t xQueue2 = xQueueCreate( 1, sizeof( uint32_t ) );
    QueueHandle_t xQueue3 = xQueueCreate( 1, sizeof( uint32_t ) );

    TEST_ASSERT_EQUAL( pdTRUE, xQueueAddToSet( xQueue1, xQueueSet ) );
    TEST_ASSERT_EQUAL( pdTRUE, xQueueAddToSet( xQueue2, xQueueSet ) );
    TEST_ASSERT_EQUAL( pdTRUE, xQueueAddToSet( xQueue3, xQueueSet ) );

    uint32_t testVal1 = 1;

    TEST_ASSERT_EQUAL( pdTRUE, xQueueSend( xQueue1, &testVal1, 0 ) );

    uint32_t testVal2 = 2;

    TEST_ASSERT_EQUAL( pdTRUE, xQueueSend( xQueue2, &testVal2, 0 ) );

    uint32_t testVal3 = 3;

    TEST_ASSERT_EQUAL( pdTRUE, xQueueSend( xQueue3, &testVal3, 0 ) );

    vFakePortAssertIfInterruptPriorityInvalid_Expect();
    QueueHandle_t xQueueTemp = xQueueSelectFromSetFromISR( xQueueSet );

    TEST_ASSERT_EQUAL( xQueueTemp, xQueue1 );

    vFakePortAssertIfInterruptPriorityInvalid_Expect();
    uint32_t checkVal1 = 0;

    TEST_ASSERT_EQUAL( pdTRUE, xQueueReceiveFromISR( xQueueTemp, &checkVal1, 0 ) );
    TEST_ASSERT_EQUAL( testVal1, checkVal1 );

    vFakePortAssertIfInterruptPriorityInvalid_Expect();
    xQueueTemp = xQueueSelectFromSetFromISR( xQueueSet );

    TEST_ASSERT_EQUAL( xQueueTemp, xQueue2 );

    vFakePortAssertIfInterruptPriorityInvalid_Expect();
    uint32_t checkVal2 = 0;

    TEST_ASSERT_EQUAL( pdTRUE, xQueueReceiveFromISR( xQueueTemp, &checkVal2, 0 ) );
    TEST_ASSERT_EQUAL( testVal2, checkVal2 );

    vFakePortAssertIfInterruptPriorityInvalid_Expect();
    xQueueTemp = xQueueSelectFromSetFromISR( xQueueSet );

    TEST_ASSERT_EQUAL( xQueueTemp, xQueue3 );

    vFakePortAssertIfInterruptPriorityInvalid_Expect();
    uint32_t checkVal3 = 0;

    TEST_ASSERT_EQUAL( pdTRUE, xQueueReceiveFromISR( xQueueTemp, &checkVal3, 0 ) );
    TEST_ASSERT_EQUAL( testVal3, checkVal3 );

    ( void ) xQueueRemoveFromSet( xQueue1, xQueueSet );
    ( void ) xQueueRemoveFromSet( xQueue2, xQueueSet );
    ( void ) xQueueRemoveFromSet( xQueue3, xQueueSet );
    vQueueDelete( xQueueSet );
    vQueueDelete( xQueue1 );
    vQueueDelete( xQueue2 );
    vQueueDelete( xQueue3 );
}

/**
 * @brief Test xQueueRemoveFromSet where the queue to be removed
 * is not empty.
 * @coverage xQueueRemoveFromSet
 */
void test_xQueueRemoveFromSet_QueueNotEmpty( void )
{
    QueueSetHandle_t xQueueSet = xQueueCreateSet( 1 );

    QueueHandle_t xQueue = xQueueCreate( 1, 0 );

    TEST_ASSERT_EQUAL( pdTRUE, xQueueAddToSet( xQueue, xQueueSet ) );

    TEST_ASSERT_EQUAL( pdTRUE, xQueueSend( xQueue, NULL, 0 ) );

    TEST_ASSERT_EQUAL( pdFALSE, xQueueRemoveFromSet( xQueue, xQueueSet ) );

    vQueueDelete( xQueueSet );
    vQueueDelete( xQueue );
}

/**
 * @brief Test xQueueRemoveFromSet where the queue to be removed
 * is already in a different set.
 * @coverage xQueueRemoveFromSet
 */
void test_xQueueRemoveFromSet_QueueNotInSet( void )
{
    QueueSetHandle_t xQueueSet1 = xQueueCreateSet( 1 );
    QueueSetHandle_t xQueueSet2 = xQueueCreateSet( 1 );

    QueueHandle_t xQueue = xQueueCreate( 1, 0 );

    TEST_ASSERT_EQUAL( pdTRUE, xQueueAddToSet( xQueue, xQueueSet1 ) );

    TEST_ASSERT_EQUAL( pdFALSE, xQueueRemoveFromSet( xQueue, xQueueSet2 ) );

    TEST_ASSERT_EQUAL( pdTRUE, xQueueRemoveFromSet( xQueue, xQueueSet1 ) );

    TEST_ASSERT_EQUAL( pdTRUE, xQueueAddToSet( xQueue, xQueueSet2 ) );

    vQueueDelete( xQueueSet1 );
    vQueueDelete( xQueueSet2 );
    vQueueDelete( xQueue );
}

/**
 * @brief Test xQueueRemoveFromSet where the queue to be removed
 * is in the given set.
 * @coverage xQueueRemoveFromSet
 */
void test_xQueueRemoveFromSet_QueueInSet( void )
{
    QueueSetHandle_t xQueueSet1 = xQueueCreateSet( 1 );
    QueueSetHandle_t xQueueSet2 = xQueueCreateSet( 1 );

    QueueHandle_t xQueue = xQueueCreate( 1, 0 );

    TEST_ASSERT_EQUAL( pdTRUE, xQueueAddToSet( xQueue, xQueueSet1 ) );

    TEST_ASSERT_EQUAL( pdTRUE, xQueueRemoveFromSet( xQueue, xQueueSet1 ) );

    TEST_ASSERT_EQUAL( pdTRUE, xQueueAddToSet( xQueue, xQueueSet2 ) );

    vQueueDelete( xQueueSet1 );
    vQueueDelete( xQueueSet2 );
    vQueueDelete( xQueue );
}
