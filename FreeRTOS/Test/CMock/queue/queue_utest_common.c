/*
 * FreeRTOS V202112.00
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
/*! @file queue_utest_common.c */

#include "queue_utest_common.h"

/* C runtime includes. */
#include <stdlib.h>
#include <stdbool.h>
#include <string.h>

/* Test includes. */
#include "unity.h"
#include "unity_memory.h"

/* Mock includes. */
#include "mock_task.h"
#include "mock_fake_assert.h"
#include "mock_fake_port.h"

/* ============================  GLOBAL VARIABLES =========================== */
static uint32_t ulMonotonicTestValue = 0xFFFF;

#if defined( configASSERT )
    static bool xMaskAssert = false;
    static BaseType_t xNumAssertsMasked = 0;
    bool xMaskAssertAndAbort = false;
#endif

static size_t uxLastMallocSize = 0;
static void * pLastFreedAddress = 0;
static uint32_t ulNumMallocCalls = 0;

/* ===========================  HELPER FUNCTIONS  =========================== */
void setxMaskAssertAndAbort( bool mask )
{
    xMaskAssertAndAbort = mask;
}
bool getxMaskAssertAndAbort()
{
    return xMaskAssertAndAbort;
}
/* ==========================  CALLBACK FUNCTIONS  ========================== */

void * pvPortMalloc( size_t xSize )
{
    uxLastMallocSize = xSize;
    ulNumMallocCalls++;
    return unity_malloc( xSize );
}

void vPortFree( void * pv )
{
    pLastFreedAddress = pv;
    return unity_free( pv );
}


#if defined( configASSERT )
    void fakeAssertCallback( bool assertion,
                             char * file,
                             int line,
                             int num_calls )
    {
        if( !assertion && xMaskAssertAndAbort )
        {
            Throw( configASSERT_E );
        }
        else if( !assertion && !xMaskAssert )
        {
            printf( "ASSERT: File: %s line: %d\n", file, line );
            TEST_FAIL();
        }
        else if( !assertion )
        {
            xNumAssertsMasked++;
        }
    }
#endif /* if defined( configASSERT ) */

/* ============================= Unity Fixtures ============================= */

void commonSetUp( void )
{
    mock_task_Init();
    mock_fake_assert_Init();
    mock_fake_port_Init();

    /* Map configAssert to a local callback */
    vFakeAssert_Stub( fakeAssertCallback );

    /* Reset globals for vFakeAssert() */
    #if defined( configASSERT )
        xMaskAssert = false;
        xNumAssertsMasked = 0;
        xMaskAssertAndAbort = false;
    #endif

    /* Reset malloc related globals */
    uxLastMallocSize = false;
    pLastFreedAddress = false;
    ulNumMallocCalls = 0;

    td_task_register_stubs();
    td_port_register_stubs();

    /* Track calls to malloc / free */
    UnityMalloc_StartTest();
}

void commonTearDown( void )
{
    #if defined( configASSERT )
        TEST_ASSERT_EQUAL_MESSAGE( 0, xNumAssertsMasked,
                                   "An unexpected configASSERT was called in this test case." );
    #endif

    td_task_teardown_check();
    td_port_teardown_check();

    mock_task_Verify();
    mock_task_Destroy();

    mock_fake_assert_Verify();
    mock_fake_assert_Destroy();
    mock_fake_port_Verify();
    mock_fake_port_Destroy();

    UnityMalloc_EndTest();
}

void commonSuiteSetUp()
{
}

int commonSuiteTearDown( int numFailures )
{
    return numFailures;
}

/* ==========================  Helper functions =========================== */
uint32_t getNextMonotonicTestValue()
{
    return ++ulMonotonicTestValue;
}

uint32_t getLastMonotonicTestValue()
{
    return ulMonotonicTestValue;
}

void fakeAssertExpectFail( void )
{
    #if defined( configASSERT )
        /* Verify that there are no pending assertions */
        TEST_ASSERT_TRUE( xNumAssertsMasked == 0 );

        /* Set flag */
        xMaskAssert = true;
    #endif
}

bool fakeAssertGetFlagAndClear( void )
{
    #if defined( configASSERT )
        bool xRetVal = ( xNumAssertsMasked > 0 );

        /* Verify that only one assertion failed since flags were last handled */
        TEST_ASSERT_TRUE_MESSAGE( xNumAssertsMasked <= 1, "Number of asserts > 1 in fakeAssertGetFlagAndClear." );

        /* Reset globals */
        xMaskAssert = false;
        xNumAssertsMasked = 0;
        return xRetVal;
    #else
        return true;
    #endif /* if defined( configASSERT ) */
}

BaseType_t fakeAssertGetNumAssertsAndClear( void )
{
    #if defined( configASSERT )
        BaseType_t xRetVal = xNumAssertsMasked;

        /* Reset globals */
        xMaskAssert = false;
        xNumAssertsMasked = 0;
        return xRetVal;
    #else
        return 0;
    #endif
}

void fakeAssertVerifyNumAssertsAndClear( uint32_t ulNumAssertsExpected )
{
    #if defined( configASSERT )
        TEST_ASSERT_EQUAL( ulNumAssertsExpected, xNumAssertsMasked );

        /* Reset globals */
        xMaskAssert = false;
        xNumAssertsMasked = 0;
    #endif
}

size_t getLastMallocSize( void )
{
    return uxLastMallocSize;
}

void * getLastFreedAddress( void )
{
    return pLastFreedAddress;
}

size_t getNumberMallocCalls( void )
{
    return ulNumMallocCalls;
}

List_t * pxGetTasksWaitingToSendToQueue( QueueHandle_t xQueue )
{
    StaticQueue_t * pxQueue = ( StaticQueue_t * ) xQueue;
    List_t * pxTasksWaitingToSend = ( List_t * ) &( pxQueue->xDummy3[ 0 ] );

    return pxTasksWaitingToSend;
}

List_t * pxGetTasksWaitingToReceiveFromQueue( QueueHandle_t xQueue )
{
    StaticQueue_t * pxQueue = ( StaticQueue_t * ) xQueue;
    List_t * pxTasksWaitingToReceive = ( List_t * ) &( pxQueue->xDummy3[ 1 ] );

    return pxTasksWaitingToReceive;
}

int8_t cGetQueueRxLock( QueueHandle_t xQueue )
{
    /* Access private lock counter */
    StaticQueue_t * pxQueue = ( StaticQueue_t * ) xQueue;
    int8_t * pcRxLock = ( int8_t * ) &( pxQueue->ucDummy5[ 0 ] );

    return *pcRxLock;
}

int8_t cGetQueueTxLock( QueueHandle_t xQueue )
{
    /* Access private lock counter */
    StaticQueue_t * pxQueue = ( StaticQueue_t * ) xQueue;
    int8_t * pcTxLock = ( int8_t * ) &( pxQueue->ucDummy5[ 1 ] );

    return *pcTxLock;
}

void vSetQueueRxLock( QueueHandle_t xQueue,
                      int8_t value )
{
    /* Access private lock counter */
    StaticQueue_t * pxQueue = ( StaticQueue_t * ) xQueue;
    int8_t * pcRxLock = ( int8_t * ) &( pxQueue->ucDummy5[ 0 ] );

    *pcRxLock = value;
}

void vSetQueueTxLock( QueueHandle_t xQueue,
                      int8_t value )
{
    /* Access private lock counter */
    StaticQueue_t * pxQueue = ( StaticQueue_t * ) xQueue;
    int8_t * pcTxLock = ( int8_t * ) &( pxQueue->ucDummy5[ 1 ] );

    *pcTxLock = value;
}

/**
 * @brief Helper function to call xQueueSend with sequential values
 * @param xQueue The handle to the queue to be tested
 * @param numberOfItems Number of sequential items to add to the queue under test.
 */
void queue_common_add_sequential_to_queue( QueueHandle_t xQueue,
                                           uint32_t numberOfItems )
{
    for( uint32_t i = 0; i < numberOfItems; i++ )
    {
        TEST_ASSERT_EQUAL( pdTRUE, xQueueSend( xQueue, &i, 0 ) );
        TEST_ASSERT_EQUAL_UINT32( i + 1, uxQueueMessagesWaiting( xQueue ) );
    }
}

/**
 * @brief Helper function to call xQueueReceive and verify sequential values are received
 * @param xQueue The handle to the queue to be tested
 * @param maxItems Maximum number of items the queue supports
 * @param numberOfItems Number of sequential items to receive from the queue under test.
 * @param expectedFirstValue The first value to expect to receive from the queue
 */
void queue_common_receive_sequential_from_queue( QueueHandle_t xQueue,
                                                 uint32_t maxItems,
                                                 uint32_t numberOfItems,
                                                 uint32_t expectedFirstValue )
{
    for( uint32_t i = 0; i < numberOfItems; i++ )
    {
        uint32_t testVal = 0xFFFFFFFF;
        TEST_ASSERT_EQUAL( pdTRUE, xQueueReceive( xQueue, &testVal, 0 ) );
        TEST_ASSERT_EQUAL( expectedFirstValue + i, testVal );
        TEST_ASSERT_EQUAL_UINT32( i + 1, uxQueueSpacesAvailable( xQueue ) );
        TEST_ASSERT_EQUAL_UINT32( maxItems - i - 1, uxQueueMessagesWaiting( xQueue ) );
    }
}
