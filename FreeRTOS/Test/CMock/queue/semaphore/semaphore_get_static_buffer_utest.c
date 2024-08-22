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
 * @brief Test xSemaphoreGetStaticBuffer with an invalid SemaphoreHandle
 * @coverage xSemaphoreGetStaticBuffer xQueueGenericGetStaticBuffers
 */
void test_macro_xSemaphoreGetStaticBuffer_null_handle( void )
{
    StaticSemaphore_t * pxSemaphoreBufferRet = NULL;

    EXPECT_ASSERT_BREAK( xSemaphoreGetStaticBuffer( NULL, &pxSemaphoreBufferRet ) );

    TEST_ASSERT_EQUAL( NULL, pxSemaphoreBufferRet );
}

/**
 * @brief Test xSemaphoreGetStaticBuffer with a null ppxSemaphoreBuffer argument
 * @coverage xSemaphoreGetStaticBuffer xQueueGenericGetStaticBuffers
 */
void test_macro_xSemaphoreGetStaticBuffer_null_ppxSemaphoreBuffer( void )
{
    SemaphoreHandle_t xSemaphore = NULL;
    StaticSemaphore_t xSemaphoreBuffer;

    xSemaphore = xSemaphoreCreateBinaryStatic( &xSemaphoreBuffer );

    EXPECT_ASSERT_BREAK( xSemaphoreGetStaticBuffer( xSemaphore, NULL ) );

    vSemaphoreDelete( xSemaphore );
}

/**
 * @brief Test xSemaphoreGetStaticBuffer with a static Semaphore
 * @details Test that xSemaphoreGetStaticBuffer returns the buffer of a statically allocated Semaphore
 * @coverage xSemaphoreGetStaticBuffer xQueueGenericGetStaticBuffers
 */
void test_macro_xSemaphoreGetStaticBuffer_static( void )
{
    SemaphoreHandle_t xSemaphore = NULL;
    StaticSemaphore_t xSemaphoreBuffer;
    StaticSemaphore_t * pxSemaphoreBufferRet = NULL;

    xSemaphore = xSemaphoreCreateBinaryStatic( &xSemaphoreBuffer );

    TEST_ASSERT_EQUAL( pdTRUE, xSemaphoreGetStaticBuffer( xSemaphore, &pxSemaphoreBufferRet ) );
    TEST_ASSERT_EQUAL( &xSemaphoreBuffer, pxSemaphoreBufferRet );

    vSemaphoreDelete( xSemaphore );
}

/**
 * @brief Test xSemaphoreGetStaticBuffer with a dynamic Semaphore
 * @details Test that xSemaphoreGetStaticBuffer returns an error when called on a dynamically allocated Semaphore
 * @coverage xSemaphoreGetStaticBuffer xQueueGenericGetStaticBuffers
 */
void test_macro_xSemaphoreGetStaticBuffer_dynamic( void )
{
    #if configSUPPORT_DYNAMIC_ALLOCATION == 1
        StaticSemaphore_t * pxSemaphoreBufferRet = NULL;
        SemaphoreHandle_t xSemaphore = xSemaphoreCreateBinary();

        TEST_ASSERT_EQUAL( pdFALSE, xSemaphoreGetStaticBuffer( xSemaphore, &pxSemaphoreBufferRet ) );
        TEST_ASSERT_EQUAL( NULL, pxSemaphoreBufferRet );

        vSemaphoreDelete( xSemaphore );
    #endif /* configSUPPORT_DYNAMIC_ALLOCATION == 1 */
}
