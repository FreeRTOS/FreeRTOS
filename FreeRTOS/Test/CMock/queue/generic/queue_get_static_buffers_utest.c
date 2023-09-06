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
 * @brief Test xQueueGetStaticBuffers with an invalid QueueHandle
 * @coverage xQueueGetStaticBuffers xQueueGenericGetStaticBuffers
 */
void test_macro_xQueueGetStaticBuffers_invalid_handle( void )
{
    uint8_t * pucQueueStorageRet = NULL;
    StaticQueue_t * pxStaticQueueRet = NULL;

    EXPECT_ASSERT_BREAK( xQueueGetStaticBuffers( NULL, &pucQueueStorageRet, &pxStaticQueueRet ) );
    TEST_ASSERT_EQUAL( NULL, pucQueueStorageRet );
    TEST_ASSERT_EQUAL( NULL, pxStaticQueueRet );
}

/**
 * @brief Test xQueueGetStaticBuffers with a null ppxStaticQueue argument
 * @coverage xQueueGetStaticBuffers xQueueGenericGetStaticBuffers
 */
void test_macro_xQueueGetStaticBuffers_null_ppxStaticQueue( void )
{
    uint32_t queueStorage[ 5 ];
    StaticQueue_t queueBuffer;
    uint8_t * pucQueueStorageRet = NULL;
    StaticQueue_t * pxStaticQueueRet = NULL;

    QueueHandle_t xQueue = xQueueCreateStatic( 5, sizeof( uint32_t ), ( void * ) queueStorage, &queueBuffer );

    EXPECT_ASSERT_BREAK( xQueueGetStaticBuffers( xQueue, &pucQueueStorageRet, NULL ) );

    TEST_ASSERT_EQUAL( NULL, pucQueueStorageRet );
    TEST_ASSERT_EQUAL( NULL, pxStaticQueueRet );
}

/**
 * @brief Test xQueueGetStaticBuffers with a null ppucQueueStorage argument
 * @coverage xQueueGetStaticBuffers xQueueGenericGetStaticBuffers
 */
void test_macro_xQueueGetStaticBuffers_null_ppucQueueStorage( void )
{
    uint32_t queueStorage[ 5 ];
    StaticQueue_t queueBuffer;
    StaticQueue_t * pxStaticQueueRet = NULL;

    QueueHandle_t xQueue = xQueueCreateStatic( 5, sizeof( uint32_t ), ( void * ) queueStorage, &queueBuffer );

    TEST_ASSERT_EQUAL( pdTRUE, xQueueGetStaticBuffers( xQueue, NULL, &pxStaticQueueRet ) );
    TEST_ASSERT_EQUAL( &queueBuffer, pxStaticQueueRet );
}

/**
 * @brief xQueueGetStaticBuffers with a statically allocated queue.
 * @details Test xQueueGetStaticBuffers returns the buffers of a statically allocated queue
 * @coverage xQueueGetStaticBuffers xQueueGenericGetStaticBuffers
 */
void test_macro_xQueueGetStaticBuffers_static( void )
{
    uint32_t queueStorage[ 5 ];
    StaticQueue_t queueBuffer;
    uint8_t * pucQueueStorageRet = NULL;
    StaticQueue_t * pxStaticQueueRet = NULL;

    QueueHandle_t xQueue = xQueueCreateStatic( 5, sizeof( uint32_t ), ( void * ) queueStorage, &queueBuffer );

    TEST_ASSERT_EQUAL( pdTRUE, xQueueGetStaticBuffers( xQueue, &pucQueueStorageRet, &pxStaticQueueRet ) );
    TEST_ASSERT_EQUAL( queueStorage, ( uint32_t * ) pucQueueStorageRet );
    TEST_ASSERT_EQUAL( &queueBuffer, pxStaticQueueRet );

    vQueueDelete( xQueue );
}

/**
 * @brief xQueueGetStaticBuffers with a dynamically allocated queue.
 * @details Test xQueueGetStaticBuffers returns an error when called on a dynamically allocated queue.
 * @coverage xQueueGetStaticBuffers xQueueGenericGetStaticBuffers
 */
void test_macro_xQueueGetStaticBuffers_dynamic( void )
{
    #if configSUPPORT_DYNAMIC_ALLOCATION == 1
        uint8_t * pucQueueStorageRet = NULL;
        StaticQueue_t * pxStaticQueueRet = NULL;

        QueueHandle_t xQueue = xQueueCreate( 5, sizeof( uint32_t ) );

        TEST_ASSERT_EQUAL( pdFALSE, xQueueGetStaticBuffers( xQueue, &pucQueueStorageRet, &pxStaticQueueRet ) );
        TEST_ASSERT_EQUAL( NULL, pucQueueStorageRet );
        TEST_ASSERT_EQUAL( NULL, pxStaticQueueRet );

        vQueueDelete( xQueue );
    #endif /* configSUPPORT_DYNAMIC_ALLOCATION == 1 */
}
