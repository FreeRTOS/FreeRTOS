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
/*! @file timers_utest.c */

/* C runtime includes. */
#include <stdlib.h>
#include <stdbool.h>

/* Test includes. */
#include "FreeRTOS.h"
#include "FreeRTOSConfig.h"
#include "timers.h"
#include "unity.h"
#include "unity_memory.h"

/* Mock includes. */
#include "mock_queue.h"
#include "mock_list.h"
#include "mock_fake_assert.h"


/* ============================  GLOBAL VARIABLES =========================== */
static uint16_t usMallocFreeCalls = 0;

/* ==========================  CALLBACK FUNCTIONS =========================== */

void * pvPortMalloc( size_t xSize )
{
    return unity_malloc( xSize );
}
void vPortFree( void * pv )
{
    return unity_free( pv );
}

/*******************************************************************************
 * Unity fixtures
 ******************************************************************************/
void setUp( void )
{
    vFakeAssert_Ignore();

    /* Track calls to malloc / free */
    UnityMalloc_StartTest();
}

/*! called before each testcase */
void tearDown( void )
{
    TEST_ASSERT_EQUAL_INT_MESSAGE( 0, usMallocFreeCalls,
                                   "free is not called the same number of times as malloc,"
                                   "you might have a memory leak!!" );
    usMallocFreeCalls = 0;

    UnityMalloc_EndTest();
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

static void xCallback_Test( TimerHandle_t xTimer )
{
}

/**
 * @brief xTimerCreate happy path
 *
 */
void test_xTimerCreate_Success( void )
{
    uint32_t ulID = 0;
    TimerHandle_t xTimer = NULL;

    vListInitialise_Ignore();
    xQueueGenericCreateStatic_IgnoreAndReturn( ( QueueHandle_t ) 1 );
    vQueueAddToRegistry_Ignore();
    vListInitialiseItem_Ignore();

    xTimer = xTimerCreate( "ut-timer",
                           pdMS_TO_TICKS( 1000 ),
                           pdTRUE,
                           &ulID,
                           xCallback_Test );

    TEST_ASSERT_NOT_EQUAL( NULL, xTimer );

    /* HACK: Free the timer directly */
    vPortFree( ( void * ) xTimer );
}

void vApplicationGetTimerTaskMemory( StaticTask_t ** ppxTimerTaskTCBBuffer,
                                     StackType_t ** ppxTimerTaskStackBuffer,
                                     uint32_t * pulTimerTaskStackSize )
{
    static StaticTask_t xTimerTaskTCB;
    static StackType_t uxTimerTaskStack[ configTIMER_TASK_STACK_DEPTH ];

    *ppxTimerTaskTCBBuffer = &xTimerTaskTCB;
    *ppxTimerTaskStackBuffer = uxTimerTaskStack;
    *pulTimerTaskStackSize = configTIMER_TASK_STACK_DEPTH;
}

void vApplicationDaemonTaskStartupHook( void )
{
}
