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
/*! @file queue_registry_utest.c */

/* C runtime includes. */
#include <stdlib.h>
#include <stdbool.h>
#include <string.h>
#include <assert.h>

#include "../queue_utest_common.h"

/* Queue includes */
#include "FreeRTOS.h"
#include "FreeRTOSConfig.h"
#include "queue.h"

/* ============================  GLOBAL VARIABLES =========================== */

/**
 * @brief Copy of QueueRegistryItem_t from queue.c to allow clearing items between test cases.
 */
typedef struct QUEUE_REGISTRY_ITEM
{
    const char * pcQueueName;
    QueueHandle_t xHandle;
} xQueueRegistryItem;
typedef xQueueRegistryItem QueueRegistryItem_t;

/* Access the xQueueRegistry to clear between test cases */
extern PRIVILEGED_DATA QueueRegistryItem_t xQueueRegistry[ configQUEUE_REGISTRY_SIZE ];

/* ==========================  CALLBACK FUNCTIONS =========================== */

/* ============================= Unity Fixtures ============================= */

void setUp( void )
{
    commonSetUp();
    /* Clear the queue registry between test cases */
    memset( &xQueueRegistry, 0, ( configQUEUE_REGISTRY_SIZE * sizeof( QueueRegistryItem_t ) ) );
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

static bool helper_find_in_queue_registry( QueueHandle_t xQueue,
                                           const char * pcQueueName )
{
    for( int i = 0; i < configQUEUE_REGISTRY_SIZE; i++ )
    {
        if( ( xQueueRegistry[ i ].pcQueueName == pcQueueName ) &&
            ( xQueueRegistry[ i ].xHandle == xQueue ) )
        {
            return true;
        }
    }

    return false;
}

static bool helper_find_handle_in_queue_registry( QueueHandle_t xQueue )
{
    for( int i = 0; i < configQUEUE_REGISTRY_SIZE; i++ )
    {
        if( xQueueRegistry[ i ].xHandle == xQueue )
        {
            return true;
        }
    }

    return false;
}

/* ==============================  Test Cases =============================== */

/**
 * @brief Test vQueueAddToRegistry with a NULL QueueHandle_t
 * @details Verify that a NULL QueueHandle_t results in the string being stored
 *  to the QueueRegistry and a configASSERT failure.
 * @coverage vQueueAddToRegistry
 **/
void test_vQueueAddToRegistry_null_xQueue( void )
{
    const char * pcFakeStringPtr = ( char * ) ( BaseType_t ) getNextMonotonicTestValue();

    /* Expect a failed configASSERT when adding a NULL xQueue to the QueueRegistry */
    fakeAssertExpectFail();

    vQueueAddToRegistry( NULL, pcFakeStringPtr );
    TEST_ASSERT_TRUE( fakeAssertGetFlagAndClear() );

    TEST_ASSERT_TRUE( helper_find_in_queue_registry( NULL, pcFakeStringPtr ) );
}

/**
 * @brief Test vQueueAddToRegistry with a NULL pcQueueName
 * @details Verify that a NULL pcQueueName results in the NULL string being stored
 * in the QueueRegistry and a configASSERT failure.
 * @coverage vQueueAddToRegistry
 **/
void test_vQueueAddToRegistry_null_pcQueueName( void )
{
    QueueHandle_t xFakeHandle = ( QueueHandle_t ) ( BaseType_t ) getNextMonotonicTestValue();

    vQueueAddToRegistry( xFakeHandle, NULL );

    TEST_ASSERT_FALSE( helper_find_in_queue_registry( xFakeHandle, NULL ) );
}

/**
 * @brief Test vQueueAddToRegistry with a valid xQueue and pcQueueName
 * @details Verify that calling vQueueAddToRegistry with a valid xQueue and
 * pcQueueName stores the tuple.
 * @coverage vQueueAddToRegistry
 **/
void test_vQueueAddToRegistry_success( void )
{
    QueueHandle_t xFakeHandle = ( QueueHandle_t ) ( BaseType_t ) getNextMonotonicTestValue();
    const char * pcFakeString = ( char * ) ( BaseType_t ) getNextMonotonicTestValue();

    /* Add an item to the registry */
    vQueueAddToRegistry( xFakeHandle, pcFakeString );

    /* Verify that the value was added to the registry */
    TEST_ASSERT_TRUE( helper_find_in_queue_registry( xFakeHandle, pcFakeString ) );
}

/**
 * @brief Test vQueueAddToRegistry with the same QueueHandle_t twice
 * @details Verify that a given QueueHandle_t can be added to the queue registry
 * multiple times and that the l
 * @coverage vQueueAddToRegistry
 **/
void test_vQueueAddToRegistry_twice( void )
{
    QueueHandle_t xFakeHandle = ( QueueHandle_t ) ( BaseType_t ) getNextMonotonicTestValue();
    const char * pcFakeString1 = ( char * ) ( BaseType_t ) getNextMonotonicTestValue();
    const char * pcFakeString2 = ( char * ) ( BaseType_t ) getNextMonotonicTestValue();

    /* Add an item to the registry */
    vQueueAddToRegistry( xFakeHandle, pcFakeString1 );

    TEST_ASSERT_TRUE( helper_find_in_queue_registry( xFakeHandle, pcFakeString1 ) );

    vQueueAddToRegistry( xFakeHandle, pcFakeString2 );

    /* Verify that pcFakeString2 is now in the queue registry */
    TEST_ASSERT_TRUE( helper_find_in_queue_registry( xFakeHandle, pcFakeString2 ) );

    /* Verify that pcFakeString1 is no longer in the queue registry */
    TEST_ASSERT_FALSE( helper_find_in_queue_registry( xFakeHandle, pcFakeString1 ) );

    vQueueUnregisterQueue( xFakeHandle );

    /* Verify that pcFakeString2 has been removed from the registry */
    TEST_ASSERT_FALSE( helper_find_in_queue_registry( xFakeHandle, pcFakeString2 ) );
}

/**
 * @brief Test vQueueAddToRegistry with a queue registry that is already full.
 * @details Verify that a call to vQueueAddToRegistry with a full queue registry
 * fails silently.
 * @coverage vQueueAddToRegistry
 **/
void test_vQueueAddToRegistry_full( void )
{
    TEST_ASSERT_TRUE( configQUEUE_REGISTRY_SIZE < UINT32_MAX );

    /* Fill the queue registry and verify that the max items were successfully stored.
     * Start at i=1 since a NULL / 0 pcQueueName denotes an empty queue registry location */
    for( BaseType_t i = 1; i <= configQUEUE_REGISTRY_SIZE; i++ )
    {
        QueueHandle_t fakeHandle = ( QueueHandle_t ) i;
        const char * fakeString = ( char * ) i;

        /* Add our fake QueueHandle_t and const char* to the registry */
        vQueueAddToRegistry( fakeHandle, fakeString );

        /* Verify that the fake queue handle was added to the registry */
        TEST_ASSERT_EQUAL( pcQueueGetName( fakeHandle ), fakeString );
    }

    /* Prepare one more fake item to add to the registry */
    QueueHandle_t fakeHandle = ( QueueHandle_t ) ( configQUEUE_REGISTRY_SIZE + 1 );
    const char * fakeString = ( char * ) ( configQUEUE_REGISTRY_SIZE + 1 );

    /* Add one more item */
    vQueueAddToRegistry( fakeHandle, fakeString );

    TEST_ASSERT_FALSE( helper_find_in_queue_registry( fakeHandle, fakeString ) );
}

/**
 * @brief Test pcQueueGetName with a NULL QueueHandle_t
 * @details Verify that a NULL QueueHandle_t can be used as a lookup value with
 * pcQueueGetName, but causes a failed configASSERT.
 * @coverage pcQueueGetName
 **/
void test_pcQueueGetName_null_xQueue( void )
{
    const char * pcFakeString = ( char * ) ( BaseType_t ) getNextMonotonicTestValue();

    /* Expect a failed configASSERT when adding a NULL xQueue to the QueueRegistry */
    fakeAssertExpectFail();

    vQueueAddToRegistry( NULL, pcFakeString );
    fakeAssertGetFlagAndClear();

    TEST_ASSERT_TRUE( helper_find_in_queue_registry( NULL, pcFakeString ) );

    /* Expect a failed configASSERT when pcQueueGetName with a NULL xQueue */
    fakeAssertExpectFail();

    /* Validate the value returned by pcQueueGetName */
    TEST_ASSERT_EQUAL( pcQueueGetName( NULL ), pcFakeString );
    TEST_ASSERT_TRUE( fakeAssertGetFlagAndClear() );
}

/**
 * @brief Test pcQueueGetName with an xQueue handle that was not registered.
 * @details Verify that a call to pcQueueGetName with an unregistered xQueue
 * returns a NULL pointer.
 * @coverage pcQueueGetName
 **/
void test_pcQueueGetName_not_registered( void )
{
    QueueHandle_t xFakeHandle = ( QueueHandle_t ) ( BaseType_t ) getNextMonotonicTestValue();
    const char * pcFakeString = ( char * ) ( BaseType_t ) getNextMonotonicTestValue();

    /* Add an item to the registry */
    vQueueAddToRegistry( xFakeHandle, pcFakeString );

    /* Verify the value returned by pcQueueGetName matches the value added to the registry */
    TEST_ASSERT_EQUAL( pcQueueGetName( xFakeHandle ), pcFakeString );

    vQueueUnregisterQueue( xFakeHandle );

    /* Verify the value returned by pcQueueGetName matches the value added to the registry */
    TEST_ASSERT_EQUAL( NULL, pcQueueGetName( xFakeHandle ) );
}

/**
 * @brief Test pcQueueGetName with an xQueue handle that was previously registered.
 * @details Verify that a call to pcQueueGetName with a registered xQueue handle
 * returns the correct pointer
 * @coverage pcQueueGetName
 **/
void test_pcQueueGetName_registered( void )
{
    QueueHandle_t xFakeHandle = ( QueueHandle_t ) ( BaseType_t ) getNextMonotonicTestValue();
    const char * pcFakeString = ( char * ) ( BaseType_t ) getNextMonotonicTestValue();

    /* Add an item to the registry */
    vQueueAddToRegistry( xFakeHandle, pcFakeString );

    /* Verify the value returned by pcQueueGetName matches the value added to the registry */
    TEST_ASSERT_EQUAL( pcQueueGetName( xFakeHandle ), pcFakeString );
}

/**
 * @brief Test vQueueUnregisterQueue with a NULL xQueue handle
 * @details Verify that calling vQueueUnregisterQueue with a NULL xQueue results
 * in a configASSERT failure.
 * @coverage vQueueUnregisterQueue
 **/
void test_vQueueUnregisterQueue_null_handle( void )
{
    fakeAssertExpectFail();

    vQueueUnregisterQueue( NULL );

    TEST_ASSERT_TRUE( fakeAssertGetFlagAndClear() );
}

/**
 * @brief Test vQueueUnregisterQueue with an unregistered xQueue handle
 * @details Verify that calling vQueueUnregisterQueue does not result in an assertion.
 * @coverage vQueueUnregisterQueue
 **/
void test_vQueueUnregisterQueue_queue_not_registered( void )
{
    QueueHandle_t xFakeHandle = ( QueueHandle_t ) ( BaseType_t ) getNextMonotonicTestValue();

    vQueueUnregisterQueue( xFakeHandle );
}

/**
 * @brief Test vQueueUnregisterQueue on a registered xQueue
 * @details Verify that calling vQueueUnregisterQueue with a registered xQueue
 * removes the xQueue from the Queue Registry and does not result in a
 * configASSERT failure.
 * @coverage vQueueUnregisterQueue
 **/
void test_vQueueUnregisterQueue( void )
{
    QueueHandle_t xFakeHandle = ( QueueHandle_t ) ( BaseType_t ) getNextMonotonicTestValue();
    const char * pcFakeString = ( char * ) ( BaseType_t ) getNextMonotonicTestValue();

    /* Add an item to the registry */
    vQueueAddToRegistry( xFakeHandle, pcFakeString );

    TEST_ASSERT_TRUE( helper_find_handle_in_queue_registry( xFakeHandle ) );
    TEST_ASSERT_EQUAL( pcFakeString, pcQueueGetName( xFakeHandle ) );

    vQueueUnregisterQueue( xFakeHandle );

    TEST_ASSERT_FALSE( helper_find_handle_in_queue_registry( xFakeHandle ) );
}

/**
 * @brief Test two subsequent calls to vQueueUnregisterQueue on a registered xQueue
 * @details Verify that calling vQueueUnregisterQueue twice on a registered xQueue
 * succeeds the first time and results in no change on the second call.
 * @coverage vQueueUnregisterQueue
 **/
void test_vQueueUnregisterQueue_twice( void )
{
    QueueHandle_t xFakeHandle = ( QueueHandle_t ) ( BaseType_t ) getNextMonotonicTestValue();
    const char * pcFakeString = ( char * ) ( BaseType_t ) getNextMonotonicTestValue();

    /* Add an item to the registry */
    vQueueAddToRegistry( xFakeHandle, pcFakeString );

    /* Verify that the value was added to the registry */
    TEST_ASSERT_TRUE( helper_find_handle_in_queue_registry( xFakeHandle ) );

    vQueueUnregisterQueue( xFakeHandle );

    TEST_ASSERT_FALSE( helper_find_handle_in_queue_registry( xFakeHandle ) );

    vQueueUnregisterQueue( xFakeHandle );

    TEST_ASSERT_FALSE( helper_find_handle_in_queue_registry( xFakeHandle ) );
}

/**
 * @brief Test that vQueueDelete removes the xQueue from the Queue Registry
 * @details Verify that vQueueDelete removes a queue from the Queue Registry
 *  by calling vQueueUnregisterQueue.
 * @coverage vQueueDelete vQueueUnregisterQueue
 **/
void test_vQueueDelete_vQueueUnregisterQueue( void )
{
    QueueHandle_t xQueue = xQueueCreate( 1, sizeof( uint32_t ) );
    const char * xQueueName = "Testing 123";

    /* Add the queue to the registry */
    vQueueAddToRegistry( xQueue, xQueueName );

    /* Verify the value returned by pcQueueGetName matches the value added to the registry */
    TEST_ASSERT_EQUAL( xQueueName, pcQueueGetName( xQueue ) );

    vQueueDelete( xQueue );

    /* Verify the value returned by pcQueueGetName is now NULL */
    TEST_ASSERT_EQUAL( NULL, pcQueueGetName( xQueue ) );
}
