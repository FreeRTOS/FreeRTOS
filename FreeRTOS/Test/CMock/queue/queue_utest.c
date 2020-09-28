/*
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
 * http://aws.amazon.com/freertos
 * http://www.FreeRTOS.org
 */

/* C runtime includes. */
#include <stdlib.h>
#include <stdbool.h>

/* Queue includes */
#include "FreeRTOS.h"
#include "FreeRTOSConfig.h"
#include "queue.h"

/* Test includes. */
#include "unity.h"

/* Mock includes. */
#include "mock_task.h"

/* ============================  GLOBAL VARIABLES =========================== */
static uint16_t usMallocFreeCalls = 0;

/* ==========================  CALLBACK FUNCTIONS =========================== */

void * pvPortMalloc( size_t xSize )
{
    return malloc(xSize);
}
void vPortFree( void * pv )
{
    return free(pv);
}
/*******************************************************************************
 * Unity fixtures
 ******************************************************************************/
void setUp( void )
{
}

/* called before each testcase */
void tearDown( void )
{
    TEST_ASSERT_EQUAL_INT_MESSAGE( 0, usMallocFreeCalls,
                                   "free is not called the same number of times as malloc,"
                                   "you might have a memory leak!!" );
    usMallocFreeCalls = 0;
}

/* called at the beginning of the whole suite */
void suiteSetUp()
{
}

/* called at the end of the whole suite */
int suiteTearDown( int numFailures )
{
    return numFailures;
}

/*!
 * @brief xQueueCreate happy path.
 *
 */
void test_xQueueCreate_Success( void )
{
    QueueHandle_t xQueue = xQueueCreate(1 , 1);
    TEST_ASSERT_NOT_EQUAL( NULL, xQueue );
}
