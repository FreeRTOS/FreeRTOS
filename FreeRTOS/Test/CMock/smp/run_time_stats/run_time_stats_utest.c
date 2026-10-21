/*
 * FreeRTOS V202212.00
 * Copyright (C) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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

/**
 * @file run_time_stats_utest.c
 * @brief Characterize the documented run-time statistics rollover limitations.
 * @coverage vTaskSwitchContext
 *
 * These tests intentionally pass without a kernel behavior change. They cover
 * accounting during context switches, not the formatted statistics output.
 */

#include <string.h>
#include "FreeRTOS.h"
#include "task.h"
#include "unity.h"
#include "../global_vars.h"
#include "mock_fake_assert.h"
#include "mock_fake_port.h"

extern List_t pxReadyTasksLists[ configMAX_PRIORITIES ];
extern volatile UBaseType_t uxTopReadyPriority;
extern volatile UBaseType_t uxSchedulerSuspended;
extern volatile BaseType_t xSchedulerRunning;
extern volatile BaseType_t xYieldPendings[ configNUMBER_OF_CORES ];
extern configRUN_TIME_COUNTER_TYPE ulTaskSwitchedInTime[ configNUMBER_OF_CORES ];
extern volatile configRUN_TIME_COUNTER_TYPE ulTotalRunTime[ configNUMBER_OF_CORES ];

#if ( configNUMBER_OF_CORES == 1 )
    extern TCB_t * volatile pxCurrentTCB;
#else
    extern TCB_t * volatile pxCurrentTCBs[ configNUMBER_OF_CORES ];
#endif

configRUN_TIME_COUNTER_TYPE ulTestRunTimeCounter;
static TCB_t xTasks[ configNUMBER_OF_CORES ];

static void prvAssertCallback( bool xCondition,
                               char * pcFile,
                               int iLine,
                               int iCallCount )
{
    ( void ) pcFile;
    ( void ) iLine;
    ( void ) iCallCount;
    TEST_ASSERT_TRUE( xCondition );
}

static void prvSwitchContext( BaseType_t xCoreID )
{
    #if ( configNUMBER_OF_CORES == 1 )
        ( void ) xCoreID;
        vTaskSwitchContext();
        TEST_ASSERT_EQUAL_PTR( &xTasks[ 0 ], pxCurrentTCB );
    #else
        vFakePortGetCoreID_IgnoreAndReturn( ( unsigned int ) xCoreID );
        vTaskSwitchContext( xCoreID );
        TEST_ASSERT_EQUAL_PTR( &xTasks[ xCoreID ], pxCurrentTCBs[ xCoreID ] );
    #endif
}

void setUp( void )
{
    BaseType_t xCoreID;
    UBaseType_t uxPriority;

    vFakeAssert_Stub( prvAssertCallback );
    vFakePortGetTaskLock_Ignore();
    vFakePortGetISRLock_Ignore();
    vFakePortReleaseISRLock_Ignore();
    vFakePortReleaseTaskLock_Ignore();
    vFakePortGetCoreID_IgnoreAndReturn( 0 );
    memset( xTasks, 0, sizeof( xTasks ) );
    memset( ( void * ) xYieldPendings, 0, sizeof( xYieldPendings ) );
    memset( ulTaskSwitchedInTime, 0, sizeof( ulTaskSwitchedInTime ) );
    memset( ( void * ) ulTotalRunTime, 0, sizeof( ulTotalRunTime ) );
    uxSchedulerSuspended = 0;
    uxTopReadyPriority = 1;
    xSchedulerRunning = pdTRUE;
    ulTestRunTimeCounter = 0;

    for( uxPriority = 0; uxPriority < configMAX_PRIORITIES; uxPriority++ )
    {
        vListInitialise( &pxReadyTasksLists[ uxPriority ] );
    }

    /* One running task per core keeps scheduling independent of accounting.
     * Use the same TCB layout and real lists as the existing SMP unit tests. */
    for( xCoreID = 0; xCoreID < configNUMBER_OF_CORES; xCoreID++ )
    {
        xTasks[ xCoreID ].uxPriority = 1;
        vListInitialiseItem( &xTasks[ xCoreID ].xStateListItem );
        listSET_LIST_ITEM_OWNER( &xTasks[ xCoreID ].xStateListItem, &xTasks[ xCoreID ] );
        vListInsertEnd( &pxReadyTasksLists[ 1 ], &xTasks[ xCoreID ].xStateListItem );

        #if ( configNUMBER_OF_CORES == 1 )
            pxCurrentTCB = &xTasks[ xCoreID ];
        #else
            xTasks[ xCoreID ].xTaskRunState = xCoreID;
            xTasks[ xCoreID ].uxCoreAffinityMask = ( UBaseType_t ) 1U << xCoreID;
            pxCurrentTCBs[ xCoreID ] = &xTasks[ xCoreID ];
        #endif
    }
}

void tearDown( void )
{
}

void suiteSetUp( void )
{
}

int suiteTearDown( int iFailures )
{
    return iFailures;
}

/* Link the unused scheduler startup path without starting a host scheduler. */
StackType_t * pxPortInitialiseStack( StackType_t * pxTopOfStack,
                                     TaskFunction_t pxCode,
                                     void * pvParameters )
{
    ( void ) pxCode;
    ( void ) pvParameters;
    return pxTopOfStack;
}

BaseType_t xPortStartScheduler( void )
{
    TEST_FAIL_MESSAGE( "These unit tests must not start a scheduler." );
    return pdFALSE;
}

void vPortEndScheduler( void )
{
    TEST_FAIL_MESSAGE( "These unit tests must not stop a scheduler." );
}

void test_context_switch_accumulates_elapsed_time( void )
{
    BaseType_t xCoreID;

    for( xCoreID = 0; xCoreID < configNUMBER_OF_CORES; xCoreID++ )
    {
        ulTaskSwitchedInTime[ xCoreID ] = 100;
        xTasks[ xCoreID ].ulRunTimeCounter = 12;
        ulTestRunTimeCounter = 116;
        prvSwitchContext( xCoreID );
        TEST_ASSERT_EQUAL_UINT64( 28, xTasks[ xCoreID ].ulRunTimeCounter );
        TEST_ASSERT_EQUAL_UINT64( 116, ulTaskSwitchedInTime[ xCoreID ] );
    }
}

void test_equal_counter_does_not_add_time( void )
{
    ulTaskSwitchedInTime[ 0 ] = 100;
    xTasks[ 0 ].ulRunTimeCounter = 12;
    ulTestRunTimeCounter = 100;
    prvSwitchContext( 0 );
    TEST_ASSERT_EQUAL_UINT64( 12, xTasks[ 0 ].ulRunTimeCounter );

    ulTestRunTimeCounter = 107;
    prvSwitchContext( 0 );
    TEST_ASSERT_EQUAL_UINT64( 19, xTasks[ 0 ].ulRunTimeCounter );
}

void test_clock_rollover_omits_interval_then_resumes( void )
{
    const configRUN_TIME_COUNTER_TYPE ulMaximum = ( configRUN_TIME_COUNTER_TYPE ) - 1;
    BaseType_t xCoreID;

    for( xCoreID = 0; xCoreID < configNUMBER_OF_CORES; xCoreID++ )
    {
        ulTaskSwitchedInTime[ xCoreID ] = ulMaximum - 15U;
        xTasks[ xCoreID ].ulRunTimeCounter = 12;
    }

    /* Every core observes the same shared clock after it rolls over. */
    ulTestRunTimeCounter = 16;

    for( xCoreID = 0; xCoreID < configNUMBER_OF_CORES; xCoreID++ )
    {
        prvSwitchContext( xCoreID );
        TEST_ASSERT_EQUAL_UINT64( 12, xTasks[ xCoreID ].ulRunTimeCounter );
        TEST_ASSERT_EQUAL_UINT64( 16, ulTaskSwitchedInTime[ xCoreID ] );
    }

    ulTestRunTimeCounter = 32;

    for( xCoreID = 0; xCoreID < configNUMBER_OF_CORES; xCoreID++ )
    {
        prvSwitchContext( xCoreID );
        /* Only the interval after rollover is counted. */
        TEST_ASSERT_EQUAL_UINT64( 28, xTasks[ xCoreID ].ulRunTimeCounter );
    }
}

void test_task_accumulator_rolls_over_without_clock_rollover( void )
{
    const configRUN_TIME_COUNTER_TYPE ulMaximum = ( configRUN_TIME_COUNTER_TYPE ) - 1;

    ulTaskSwitchedInTime[ 0 ] = 100;
    xTasks[ 0 ].ulRunTimeCounter = ulMaximum - 7U;
    ulTestRunTimeCounter = 116;
    prvSwitchContext( 0 );
    TEST_ASSERT_EQUAL_UINT64( 8, xTasks[ 0 ].ulRunTimeCounter );
    TEST_ASSERT_EQUAL_UINT64( 116, ulTaskSwitchedInTime[ 0 ] );
}

void test_elapsed_time_uses_full_counter_width( void )
{
    const configRUN_TIME_COUNTER_TYPE ulMaximum = ( configRUN_TIME_COUNTER_TYPE ) - 1;

    ulTaskSwitchedInTime[ 0 ] = ulMaximum - 31U;
    ulTestRunTimeCounter = ulMaximum - 15U;
    prvSwitchContext( 0 );
    TEST_ASSERT_EQUAL_UINT64( 16, xTasks[ 0 ].ulRunTimeCounter );
    TEST_ASSERT_EQUAL_UINT64( ulMaximum - 15U, ulTaskSwitchedInTime[ 0 ] );
}

void test_each_core_has_its_own_switch_in_time( void )
{
    BaseType_t xCoreID;

    for( xCoreID = 0; xCoreID < configNUMBER_OF_CORES; xCoreID++ )
    {
        ulTaskSwitchedInTime[ xCoreID ] = 100U + ( ( configRUN_TIME_COUNTER_TYPE ) xCoreID * 10U );
    }

    ulTestRunTimeCounter = 120;

    for( xCoreID = 0; xCoreID < configNUMBER_OF_CORES; xCoreID++ )
    {
        prvSwitchContext( xCoreID );
        TEST_ASSERT_EQUAL_UINT64( 20U - ( ( configRUN_TIME_COUNTER_TYPE ) xCoreID * 10U ), xTasks[ xCoreID ].ulRunTimeCounter );
    }
}
