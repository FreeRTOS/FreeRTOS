/*
 * FreeRTOS V202012.00
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
/*! @file tasks_utest.c */

/* C runtime includes. */
/*#include <stdlib.h> */
/*#include <stdbool.h> */

/* Test includes. */
#include "unity.h"

/* Tasks includes */
#include "FreeRTOS.h"
#include "FreeRTOSConfig.h"

#include "mock_list.h"
/*#include "mock_timers.h" */
/*#include "mock_portable.h" */

#include "task.h"

void vApplicationIdleHook( void )
{
}

void vApplicationMallocFailedHook( void )
{
}

/* ===========================  DEFINES CONSTANTS  ========================== */

/* ===========================  GLOBAL VARIABLES  =========================== */


/* ============================  Unity Fixtures  ============================ */
/*! called before each testcase */
void setUp( void )
{
}

/*! called after each testcase */
void tearDown( void )
{
}

/*! called at the beginning of the whole suite */
void suiteSetUp()
{
}

/*! called at the end of the whole suite */
int suiteTearDown( int numFailures )
{
    return numFailures;
}

/* ===========================  Static Functions  =========================== */


/* ==============================  Test Cases  ============================== */

/*!
 * @brief
 */
void test_xTaskCreateStatic_null_puxStackBuffer( void )
{
    StaticTask_t pxTaskBuffer[ 300 ];
    TaskFunction_t pxTaskCode = NULL;
    const char * const pcName = { "unit test" };
    const uint32_t ulStackDepth = 0;
    void * const pvParameters = NULL;
    UBaseType_t uxPriority = 3;
    TaskHandle_t ret;

    ret = xTaskCreateStatic( pxTaskCode,
                             pcName,
                             ulStackDepth,
                             pvParameters,
                             uxPriority,
                             NULL,
                             pxTaskBuffer );
    TEST_ASSERT_EQUAL( NULL, ret );
}


/*!
 * @brief
 */
void test_xTaskCreateStatic_null_pxTaskBuffer( void )
{
    StackType_t puxStackBuffer[ 300 ];

    TaskFunction_t pxTaskCode = NULL;
    const char * const pcName = { "unit test" };
    const uint32_t ulStackDepth = 0;
    void * const pvParameters = NULL;
    UBaseType_t uxPriority = 3;
    TaskHandle_t ret;

    ret = xTaskCreateStatic( pxTaskCode,
                             pcName,
                             ulStackDepth,
                             pvParameters,
                             uxPriority,
                             puxStackBuffer,
                             NULL );
    TEST_ASSERT_EQUAL( NULL, ret );
}

/*!
 * @brief
 */
void test_xTaskCreateStatic_success( void )
{
    StackType_t puxStackBuffer[ 300 * 8 ];
    StaticTask_t pxTaskBuffer[ 300 * 8 ];
    TaskFunction_t pxTaskCode = NULL;
    const char * const pcName = { "unit test" };
    const uint32_t ulStackDepth = 0;
    void * const pvParameters = NULL;
    UBaseType_t uxPriority = 3;
    TaskHandle_t ret;

    vListInitialise_Ignore();
    ret = xTaskCreateStatic( pxTaskCode,
                             pcName,
                             ulStackDepth,
                             pvParameters,
                             uxPriority,
                             puxStackBuffer,
                             pxTaskBuffer );
    TEST_ASSERT_EQUAL( NULL, ret );
}
