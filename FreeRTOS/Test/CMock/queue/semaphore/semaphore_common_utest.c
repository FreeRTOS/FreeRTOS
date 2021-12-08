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
/*! @file semaphore_common_utest.c */

#include "../queue_utest_common.h"

/* Queue includes */
#include "FreeRTOS.h"
#include "FreeRTOSConfig.h"
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

/* ===========================  Helper functions ============================ */

/* ==============================  Test Cases =============================== */

/**
 * @brief Test xSemaphoreTake with an invalid (NULL) handle
 * @coverage xQueueSemaphoreTake
 */
void test_macro_xSemaphoreTake_invalid_handle( void )
{
    EXPECT_ASSERT_BREAK( xSemaphoreTake( NULL, 0 ) );
}

/**
 * @brief Test xSemaphoreTake with a QueueHandle rather than a SemaphoreHandle
 * @coverage xQueueSemaphoreTake
 */
void test_macro_xSemaphoreTake_queue_handle( void )
{
    QueueHandle_t xQueue = xQueueCreate( 1, sizeof( uint32_t ) );

    uint32_t testVal = getNextMonotonicTestValue();

    xQueueSend( xQueue, &testVal, 0 );

    /* Expect that xSemaphoreTake will assert because xQueue is not a semaphore */
    fakeAssertExpectFail();

    TEST_ASSERT_EQUAL( pdTRUE, xSemaphoreTake( xQueue, 0 ) );

    /* verify that configASSERT was called */
    TEST_ASSERT_EQUAL( true, fakeAssertGetFlagAndClear() );

    vQueueDelete( xQueue );
}

/**
 * @brief Test xSemaphoreGive with an invalid (NULL) handle
 * @coverage xQueueGenericSend
 */
void test_macro_xSemaphoreGive_invalid_handle( void )
{
    EXPECT_ASSERT_BREAK( xSemaphoreGive( NULL ) );
}

/**
 * @brief Test xSemaphoreGive with a QueueHandle rather than a SemaphoreHandle
 * @coverage xQueueGenericSend
 */
void test_macro_xSemaphoreGive_queue_handle( void )
{
    QueueHandle_t xQueue = xQueueCreate( 1, sizeof( uint32_t ) );

    EXPECT_ASSERT_BREAK( xSemaphoreGive( xQueue ) );

    vQueueDelete( xQueue );
}

/**
 * @brief Test xSemaphoreTakeFromISR with an invalid (NULL) handle
 * @coverage xQueueReceiveFromISR
 */
void test_macro_xSemaphoreTakeFromISR_invalid_handle( void )
{
    EXPECT_ASSERT_BREAK( xSemaphoreTakeFromISR( NULL, NULL ) );
}

/**
 * @brief Test xSemaphoreTakeFromISR with a QueueHandle rather than a SemaphoreHandle
 * @coverage xQueueReceiveFromISR
 */
void test_macro_xSemaphoreTakeFromISR_queue_handle( void )
{
    QueueHandle_t xQueue = xQueueCreate( 1, sizeof( uint32_t ) );

    /* Expect that xSemaphoreTake will assert because xQueue is not a semaphore */
    fakeAssertExpectFail();

    uint32_t testVal = getNextMonotonicTestValue();

    xQueueSend( xQueue, &testVal, 0 );

    EXPECT_ASSERT_BREAK( xSemaphoreTakeFromISR( xQueue, NULL ) );

    vQueueDelete( xQueue );
}

/**
 * @brief Test xSemaphoreGiveFromISR with an invalid (NULL) handle
 * @coverage xQueueGiveFromISR
 */
void test_macro_xSemaphoreGiveFromISR_invalid_handle( void )
{
    EXPECT_ASSERT_BREAK( xSemaphoreGiveFromISR( NULL, NULL ) );
}

/**
 * @brief Test xSemaphoreGiveFromISR with a QueueHandle rather than a SemaphoreHandle
 * @coverage xQueueGiveFromISR
 */
void test_macro_xSemaphoreGiveFromISR_queue_handle( void )
{
    QueueHandle_t xQueue = xQueueCreate( 1, sizeof( uint32_t ) );

    EXPECT_ASSERT_BREAK( xSemaphoreGiveFromISR( xQueue, NULL ) );

    vQueueDelete( xQueue );
}
