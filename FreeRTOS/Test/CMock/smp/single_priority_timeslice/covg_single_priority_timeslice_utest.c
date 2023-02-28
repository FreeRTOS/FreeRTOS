/*
 * FreeRTOS V202012.00
 * Copyright (C) 2022 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
/*! @file covg_single_priority_timeslice_utest.c */

/* C runtime includes. */
#include <stdlib.h>
#include <stdbool.h>
#include <stdint.h>
#include <string.h>

/* Tasl includes */
#include "FreeRTOS.h"
#include "FreeRTOSConfig.h"
#include "event_groups.h"
#include "queue.h"

/* Test includes. */
#include "unity.h"
#include "unity_memory.h"
#include "../global_vars.h"
#include "../smp_utest_common.h"

/* Mock includes. */
#include "mock_timers.h"
#include "mock_fake_assert.h"
#include "mock_fake_port.h"
#include "mock_fake_infiniteloop.h"

/* ===========================  EXTERN VARIABLES  =========================== */
extern volatile UBaseType_t uxDeletedTasksWaitingCleanUp;
extern volatile TCB_t * pxCurrentTCBs[ configNUMBER_OF_CORES ];
extern UBaseType_t uxTopReadyPriority;
extern List_t pxReadyTasksLists[ configMAX_PRIORITIES ];

/* ===========================  EXTERN FUNCTIONS  =========================== */
extern void prvIdleTask( void );
extern void prvMinimalIdleTask( void );

/* ============================  Unity Fixtures  ============================ */
/*! called before each testcase */
void setUp( void )
{
    commonSetUp();
}

/*! called after each testcase */
void tearDown( void )
{
    commonTearDown();
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

/* =============================  HELPER FUNCTIONS  ========================= */
void vApplicationMinimalIdleHook( void )
{
}

/* ==============================  Test Cases  ============================== */

/* @brief prvIdleTask - no other idle priority task
 *
 * This test calls the prvMinimalIdleTask to cover the condition that no other idle
 * priority task in the ready list. The task is still the running task on core 0.
 *
 * <b>Coverage</b>
 * @code{c}
 * if( listCURRENT_LIST_LENGTH( &( pxReadyTasksLists[ tskIDLE_PRIORITY ] ) ) > ( UBaseType_t ) configNUMBER_OF_CORES )
 * {
 *     taskYIELD();
 * }
 * else
 * {
 *     mtCOVERAGE_TEST_MARKER();
 * }
 * @endcode
 * ( listCURRENT_LIST_LENGTH( &( pxReadyTasksLists[ tskIDLE_PRIORITY ] ) ) > ( UBaseType_t ) configNUMBER_OF_CORES ) is false.
 */
void test_coverage_prvIdleTask_no_other_idle_priority_task( void )
{
    TCB_t xTaskTCBs[ configNUMBER_OF_CORES ] = { 0 };
    uint32_t i;

    /* Setup the variables and structure. */
    /* Initialize the idle priority ready list and set top ready priority to idle priority. */
    vListInitialise( &( pxReadyTasksLists[ tskIDLE_PRIORITY ] ) );
    uxTopReadyPriority = tskIDLE_PRIORITY;

    /* Create idle tasks and add it into the ready list. */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        xTaskTCBs[ i ].uxPriority = tskIDLE_PRIORITY;
        xTaskTCBs[ i ].xTaskRunState = i;
        xTaskTCBs[ i ].xStateListItem.pvOwner = &xTaskTCBs[ i ];
        xTaskTCBs[ i ].xStateListItem.pxContainer = &pxReadyTasksLists[ tskIDLE_PRIORITY ];
        xTaskTCBs[ i ].uxCoreAffinityMask = ( ( 1U << configNUMBER_OF_CORES ) - 1U );
        pxCurrentTCBs[ i ] = &xTaskTCBs[ i ];
        listINSERT_END( &pxReadyTasksLists[ tskIDLE_PRIORITY ], &xTaskTCBs[ i ].xStateListItem );
    }

    /* Expectations. */
    vFakeInfiniteLoop_ExpectAndReturn( 1 );
    vFakeInfiniteLoop_ExpectAndReturn( 0 );

    /* API calls. Runs the idle task function on core 0. */
    prvIdleTask();

    /* Validations. xTaskTCBs[ 0 ] still runs on core 0. */
    configASSERT( pxCurrentTCBs[ 0 ] == &xTaskTCBs[ 0 ] );
}

/* @brief prvIdleTask - yield for idle priority task
 *
 * This test calls the prvMinimalIdleTask to cover the condition that there are more
 * idle priority level tasks than configNUMBER_OF_CORES. Yield is called in prvMinimalIdleTask.
 *
 * <b>Coverage</b>
 * @code{c}
 * if( listCURRENT_LIST_LENGTH( &( pxReadyTasksLists[ tskIDLE_PRIORITY ] ) ) > ( UBaseType_t ) configNUMBER_OF_CORES )
 * {
 *     taskYIELD();
 * }
 * else
 * {
 *     mtCOVERAGE_TEST_MARKER();
 * }
 * @endcode
 * ( listCURRENT_LIST_LENGTH( &( pxReadyTasksLists[ tskIDLE_PRIORITY ] ) ) > ( UBaseType_t ) configNUMBER_OF_CORES ) is true.
 */
void test_coverage_prvIdleTask_yield_for_idle_priority_task( void )
{
    TCB_t xTaskTCBs[ configNUMBER_OF_CORES + 1 ] = { 0 };
    uint32_t i;

    /* Setup the variables and structure. */
    /* Initialize the idle priority ready list and set top ready priority to idle priority. */
    vListInitialise( &( pxReadyTasksLists[ tskIDLE_PRIORITY ] ) );
    uxTopReadyPriority = tskIDLE_PRIORITY;

    /* Create idle tasks and add it into the ready list. Create one more idle priority level
     * in the loop. */
    for( i = 0; i < ( configNUMBER_OF_CORES + 1U ); i++ )
    {
        xTaskTCBs[ i ].uxPriority = tskIDLE_PRIORITY;
        xTaskTCBs[ i ].xStateListItem.pvOwner = &xTaskTCBs[ i ];
        xTaskTCBs[ i ].xStateListItem.pxContainer = &pxReadyTasksLists[ tskIDLE_PRIORITY ];
        xTaskTCBs[ i ].uxCoreAffinityMask = ( ( 1U << configNUMBER_OF_CORES ) - 1U );
        if( i < configNUMBER_OF_CORES )
        {
            pxCurrentTCBs[ i ] = &xTaskTCBs[ i ];
            xTaskTCBs[ i ].xTaskRunState = i;
        }
        else
        {
            xTaskTCBs[ i ].xTaskRunState = -1;  /* Set run state to taskTASK_NOT_RUNNING. */
        }
        listINSERT_END( &pxReadyTasksLists[ tskIDLE_PRIORITY ], &xTaskTCBs[ i ].xStateListItem );
    }

    /* Expectations. */
    vFakeInfiniteLoop_ExpectAndReturn( 1 );
    vFakeInfiniteLoop_ExpectAndReturn( 0 );

    /* API calls. Runs the idle task function on core 0. */
    prvIdleTask();

    /* Validations. xTaskTCBs[ i ] runs on core 0. */
    configASSERT( pxCurrentTCBs[ 0 ] == &xTaskTCBs[ i ] );
}

/* @brief prvMinimalIdleTask - no other idle priority task
 *
 * This test calls the prvMinimalIdleTask to cover the condition that no other idle
 * priority task in the ready list. The task is still the running task on core 0.
 *
 * <b>Coverage</b>
 * @code{c}
 * if( listCURRENT_LIST_LENGTH( &( pxReadyTasksLists[ tskIDLE_PRIORITY ] ) ) > ( UBaseType_t ) configNUMBER_OF_CORES )
 * {
 *     taskYIELD();
 * }
 * else
 * {
 *     mtCOVERAGE_TEST_MARKER();
 * }
 * @endcode
 * ( listCURRENT_LIST_LENGTH( &( pxReadyTasksLists[ tskIDLE_PRIORITY ] ) ) > ( UBaseType_t ) configNUMBER_OF_CORES ) is false.
 */
void test_coverage_prvMinimalIdleTask_no_other_idle_priority_task( void )
{
    TCB_t xTaskTCBs[ configNUMBER_OF_CORES ] = { 0 };
    uint32_t i;

    /* Setup the variables and structure. */
    /* Initialize the idle priority ready list and set top ready priority to idle priority. */
    vListInitialise( &( pxReadyTasksLists[ tskIDLE_PRIORITY ] ) );
    uxTopReadyPriority = tskIDLE_PRIORITY;

    /* Create idle tasks and add it into the ready list. */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        xTaskTCBs[ i ].uxPriority = tskIDLE_PRIORITY;
        xTaskTCBs[ i ].xTaskRunState = i;
        xTaskTCBs[ i ].xStateListItem.pvOwner = &xTaskTCBs[ i ];
        xTaskTCBs[ i ].xStateListItem.pxContainer = &pxReadyTasksLists[ tskIDLE_PRIORITY ];
        xTaskTCBs[ i ].uxCoreAffinityMask = ( ( 1U << configNUMBER_OF_CORES ) - 1U );
        pxCurrentTCBs[ i ] = &xTaskTCBs[ i ];
        listINSERT_END( &pxReadyTasksLists[ tskIDLE_PRIORITY ], &xTaskTCBs[ i ].xStateListItem );
    }

    /* Expectations. */
    vFakeInfiniteLoop_ExpectAndReturn( 1 );
    vFakeInfiniteLoop_ExpectAndReturn( 0 );

    /* API calls. Runs the idle task function on core 0. */
    prvMinimalIdleTask();

    /* Validations. xTaskTCBs[ 0 ] still runs on core 0. */
    configASSERT( pxCurrentTCBs[ 0 ] == &xTaskTCBs[ 0 ] );
}

/* @brief prvMinimalIdleTask - yield for idle priority task
 *
 * This test calls the prvMinimalIdleTask to cover the condition that there are more
 * idle priority level tasks than configNUMBER_OF_CORES. Yield is called in prvMinimalIdleTask.
 *
 * <b>Coverage</b>
 * @code{c}
 * if( listCURRENT_LIST_LENGTH( &( pxReadyTasksLists[ tskIDLE_PRIORITY ] ) ) > ( UBaseType_t ) configNUMBER_OF_CORES )
 * {
 *     taskYIELD();
 * }
 * else
 * {
 *     mtCOVERAGE_TEST_MARKER();
 * }
 * @endcode
 * ( listCURRENT_LIST_LENGTH( &( pxReadyTasksLists[ tskIDLE_PRIORITY ] ) ) > ( UBaseType_t ) configNUMBER_OF_CORES ) is true.
 */
void test_coverage_prvMinimalIdleTask_yield_for_idle_priority_task( void )
{
    TCB_t xTaskTCBs[ configNUMBER_OF_CORES + 1 ] = { 0 };
    uint32_t i;

    /* Setup the variables and structure. */
    /* Initialize the idle priority ready list and set top ready priority to idle priority. */
    vListInitialise( &( pxReadyTasksLists[ tskIDLE_PRIORITY ] ) );
    uxTopReadyPriority = tskIDLE_PRIORITY;

    /* Create idle tasks and add it into the ready list. Create one more idle priority level
     * in the loop. */
    for( i = 0; i < ( configNUMBER_OF_CORES + 1U ); i++ )
    {
        xTaskTCBs[ i ].uxPriority = tskIDLE_PRIORITY;
        xTaskTCBs[ i ].xStateListItem.pvOwner = &xTaskTCBs[ i ];
        xTaskTCBs[ i ].xStateListItem.pxContainer = &pxReadyTasksLists[ tskIDLE_PRIORITY ];
        xTaskTCBs[ i ].uxCoreAffinityMask = ( ( 1U << configNUMBER_OF_CORES ) - 1U );
        if( i < configNUMBER_OF_CORES )
        {
            pxCurrentTCBs[ i ] = &xTaskTCBs[ i ];
            xTaskTCBs[ i ].xTaskRunState = i;
        }
        else
        {
            xTaskTCBs[ i ].xTaskRunState = -1;  /* Set run state to taskTASK_NOT_RUNNING. */
        }
        listINSERT_END( &pxReadyTasksLists[ tskIDLE_PRIORITY ], &xTaskTCBs[ i ].xStateListItem );
    }

    /* Expectations. */
    vFakeInfiniteLoop_ExpectAndReturn( 1 );
    vFakeInfiniteLoop_ExpectAndReturn( 0 );

    /* API calls. Runs the idle task function on core 0. */
    prvMinimalIdleTask();

    /* Validations. xTaskTCBs[ i ] runs on core 0. */
    configASSERT( pxCurrentTCBs[ 0 ] == &xTaskTCBs[ i ] );
}
