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
/*! @file covg_multiple_priority_timeslice_utest.c */

/* C runtime includes. */
#include <stdlib.h>
#include <stdbool.h>
#include <stdint.h>
#include <string.h>

/* Task includes */
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

/* ===========================  EXTERN VARIABLES  =========================== */
extern volatile UBaseType_t uxDeletedTasksWaitingCleanUp;
extern volatile TCB_t * pxCurrentTCBs[ configNUMBER_OF_CORES ];
extern UBaseType_t uxTopReadyPriority;
extern List_t pxReadyTasksLists[ configMAX_PRIORITIES ];
extern List_t xDelayedTaskList1;
extern List_t * pxDelayedTaskList;
extern UBaseType_t uxSchedulerSuspended;
extern BaseType_t xTickCount;
extern BaseType_t xNextTaskUnblockTime;
extern BaseType_t xYieldPendings[ configNUMBER_OF_CORES ];

/* ===========================  EXTERN FUNCTIONS  =========================== */
extern void prvIdleTask( void );
extern void prvPassiveIdleTask( void );
extern BaseType_t xTaskIncrementTick( void );

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

/* ==============================  Test Cases  ============================== */

/**
 * @brief xTaskIncrementTick - no equal priority task for time slice.
 *
 * No equal priority ready task when incrementing tick. Verify that the return value
 * indicates switching is not required.
 *
 * <b>Coverage</b>
 * @code{c}
 * for( x = ( ( UBaseType_t ) 0 ); x < ( ( UBaseType_t ) configNUMBER_OF_CORES ); x++ )
 * {
 *     if( listCURRENT_LIST_LENGTH( &( pxReadyTasksLists[ pxCurrentTCBs[ x ]->uxPriority ] ) ) > ( UBaseType_t ) 1 )
 *     {
 *         xYieldRequiredForCore[ x ] = pdTRUE;
 *     }
 *     else
 *     {
 *         mtCOVERAGE_TEST_MARKER();
 *     }
 * }
 * @endcode
 * ( listCURRENT_LIST_LENGTH( &( pxReadyTasksLists[ pxCurrentTCBs[ x ]->uxPriority ] ) ) > ( UBaseType_t ) 1 ) is false.
 */
void test_coverage_xTaskIncrementTick_no_eq_priority_task( void )
{
    BaseType_t xReturn;
    TCB_t xTaskTCBs[ configNUMBER_OF_CORES ] = { NULL };
    TCB_t xTaskTCB = { NULL };
    uint32_t i;

    /* Setup the variables and structure. */
    /* Initialize the idle priority ready list and set top ready priority to idle priority. */
    vListInitialise( &( pxReadyTasksLists[ tskIDLE_PRIORITY ] ) );
    vListInitialise( &( pxReadyTasksLists[ tskIDLE_PRIORITY + 1 ] ) );
    uxTopReadyPriority = tskIDLE_PRIORITY + 1;
    uxSchedulerSuspended = pdFALSE;
    xTickCount = 0;
    xNextTaskUnblockTime = 0;
    vListInitialise( &xDelayedTaskList1 );
    pxDelayedTaskList = &xDelayedTaskList1;

    /* Create idle tasks and add it into the ready list. */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        xTaskTCBs[ i ].uxPriority = tskIDLE_PRIORITY;
        xTaskTCBs[ i ].xStateListItem.pvOwner = &xTaskTCBs[ i ];
        xTaskTCBs[ i ].uxCoreAffinityMask = ( ( 1U << configNUMBER_OF_CORES ) - 1U );
        pxCurrentTCBs[ i ] = &xTaskTCBs[ i ];
        xTaskTCBs[ i ].xTaskRunState = i;
        xTaskTCBs[ i ].xStateListItem.pxContainer = &pxReadyTasksLists[ tskIDLE_PRIORITY ];
        xTaskTCBs[ i ].uxTaskAttributes = taskATTRIBUTE_IS_IDLE;
        listINSERT_END( &pxReadyTasksLists[ tskIDLE_PRIORITY ], &xTaskTCBs[ i ].xStateListItem );
    }

    /* Create one more higher priority task to run on core 0. */
    xTaskTCBs[ 0 ].xTaskRunState = taskTASK_NOT_RUNNING;
    xTaskTCB.uxPriority = tskIDLE_PRIORITY + 1;
    xTaskTCB.xStateListItem.pvOwner = &xTaskTCB;
    xTaskTCB.uxCoreAffinityMask = ( ( 1U << configNUMBER_OF_CORES ) - 1U );
    pxCurrentTCBs[ 0 ] = &xTaskTCB;
    xTaskTCB.xTaskRunState = 0;
    xTaskTCB.xStateListItem.pxContainer = &pxReadyTasksLists[ tskIDLE_PRIORITY + 1 ];
    xTaskTCB.uxTaskAttributes = 0;
    listINSERT_END( &pxReadyTasksLists[ tskIDLE_PRIORITY + 1 ], &xTaskTCB.xStateListItem );

    /* API calls. */
    xReturn = xTaskIncrementTick();

    /* Validations. */

    /* Core 0 is running a higher priority task. No other task of equal priority is
     * waiting to run. Switching is not required in this test. */
    TEST_ASSERT_EQUAL( pdFALSE, xReturn );
    TEST_ASSERT_EQUAL( portMAX_DELAY, xNextTaskUnblockTime );
}

/**
 * @brief xTaskIncrementTick - current core has yield pending.
 *
 * No equal priority ready task when incrementing tick. However, the current core
 * has yield pending. Verify that the return value indicates switching is required.
 *
 * <b>Coverage</b>
 * @code{c}
 * if( ( xYieldRequiredForCore[ x ] != pdFALSE ) || ( xYieldPendings[ x ] != pdFALSE ) )
 * {
 *     if( x == ( UBaseType_t ) xCoreID )
 *     {
 *         xSwitchRequired = pdTRUE;
 *     }
 *     else
 *     {
 *         prvYieldCore( x );
 *     }
 * }
 * @endcode
 * ( xYieldRequiredForCore[ x ] != pdFALSE ) is false.
 * ( xYieldPendings[ x ] != pdFALSE ) is true.
 * ( x == ( UBaseType_t ) xCoreID ) is true.
 */
void test_coverage_xTaskIncrementTick_no_eq_priority_task_yield_pending( void )
{
    BaseType_t xReturn;
    TCB_t xTaskTCBs[ configNUMBER_OF_CORES ] = { NULL };
    TCB_t xTaskTCB = { NULL };
    uint32_t i;

    /* Setup the variables and structure. */
    /* Initialize the idle priority ready list and set top ready priority to idle priority. */
    vListInitialise( &( pxReadyTasksLists[ tskIDLE_PRIORITY ] ) );
    vListInitialise( &( pxReadyTasksLists[ tskIDLE_PRIORITY + 1 ] ) );
    uxTopReadyPriority = tskIDLE_PRIORITY + 1;
    uxSchedulerSuspended = pdFALSE;
    xTickCount = 0;
    xNextTaskUnblockTime = 0;
    vListInitialise( &xDelayedTaskList1 );
    pxDelayedTaskList = &xDelayedTaskList1;

    /* Create idle tasks and add it into the ready list. */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        xTaskTCBs[ i ].uxPriority = tskIDLE_PRIORITY;
        xTaskTCBs[ i ].xStateListItem.pvOwner = &xTaskTCBs[ i ];
        xTaskTCBs[ i ].uxCoreAffinityMask = ( ( 1U << configNUMBER_OF_CORES ) - 1U );
        pxCurrentTCBs[ i ] = &xTaskTCBs[ i ];
        xTaskTCBs[ i ].xTaskRunState = i;
        xTaskTCBs[ i ].xStateListItem.pxContainer = &pxReadyTasksLists[ tskIDLE_PRIORITY ];
        xTaskTCBs[ i ].uxTaskAttributes = taskATTRIBUTE_IS_IDLE;
        listINSERT_END( &pxReadyTasksLists[ tskIDLE_PRIORITY ], &xTaskTCBs[ i ].xStateListItem );
    }

    /* Create one more higher priority task to run on core 0. */
    xTaskTCBs[ 0 ].xTaskRunState = taskTASK_NOT_RUNNING;
    xTaskTCB.uxPriority = tskIDLE_PRIORITY + 1;
    xTaskTCB.xStateListItem.pvOwner = &xTaskTCB;
    xTaskTCB.uxCoreAffinityMask = ( ( 1U << configNUMBER_OF_CORES ) - 1U );
    pxCurrentTCBs[ 0 ] = &xTaskTCB;
    xYieldPendings[ 0 ] = pdTRUE;
    xTaskTCB.xTaskRunState = 0;
    xTaskTCB.xStateListItem.pxContainer = &pxReadyTasksLists[ tskIDLE_PRIORITY + 1 ];
    xTaskTCB.uxTaskAttributes = 0;
    listINSERT_END( &pxReadyTasksLists[ tskIDLE_PRIORITY + 1 ], &xTaskTCB.xStateListItem );

    /* API calls. */
    xReturn = xTaskIncrementTick();

    /* Validations. */

    /* Core 0 is running a higher priority task. No other task of equal priority is
     * waiting to run. However, core 0 has yield pending. Switching is required for
     * core 0. */
    TEST_ASSERT_EQUAL( pdTRUE, xReturn );
    TEST_ASSERT_EQUAL( portMAX_DELAY, xNextTaskUnblockTime );
}

/**
 * @brief xTaskIncrementTick - task with preemption disabled.
 *
 * The running task has preemption disabled. Verify the return value indicates switching
 * is not required.
 *
 * <b>Coverage</b>
 * @code{c}
 * for( x = ( UBaseType_t ) 0; x < ( UBaseType_t ) configNUMBER_OF_CORES; x++ )
 * {
 *     #if ( configUSE_TASK_PREEMPTION_DISABLE == 1 )
 *         if( pxCurrentTCBs[ x ]->xPreemptionDisable == pdFALSE )
 *     #endif
 *     {
 *         ....
 *     }
 *     ...
 * }
 * @endcode
 * ( pxCurrentTCBs[ x ]->xPreemptionDisable == pdFALSE ) is false.
 */
void test_coverage_xTaskIncrementTick_preemption_disabled_task( void )
{
    BaseType_t xReturn;
    TCB_t xTaskTCBs[ configNUMBER_OF_CORES ] = { NULL };
    TCB_t xTaskTCB = { NULL };
    uint32_t i;

    /* Setup the variables and structure. */
    /* Initialize the idle priority ready list and set top ready priority to idle priority. */
    vListInitialise( &( pxReadyTasksLists[ tskIDLE_PRIORITY ] ) );
    uxTopReadyPriority = tskIDLE_PRIORITY;
    uxSchedulerSuspended = pdFALSE;
    xTickCount = 0;
    xNextTaskUnblockTime = 0;
    vListInitialise( &xDelayedTaskList1 );
    pxDelayedTaskList = &xDelayedTaskList1;

    /* Create idle tasks and add it into the ready list. */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        xTaskTCBs[ i ].uxPriority = tskIDLE_PRIORITY;
        xTaskTCBs[ i ].xStateListItem.pvOwner = &xTaskTCBs[ i ];
        xTaskTCBs[ i ].uxCoreAffinityMask = ( ( 1U << configNUMBER_OF_CORES ) - 1U );
        pxCurrentTCBs[ i ] = &xTaskTCBs[ i ];
        xTaskTCBs[ i ].xTaskRunState = i;
        xTaskTCBs[ i ].xStateListItem.pxContainer = &pxReadyTasksLists[ tskIDLE_PRIORITY ];
        xTaskTCBs[ i ].uxTaskAttributes = taskATTRIBUTE_IS_IDLE;
        listINSERT_END( &pxReadyTasksLists[ tskIDLE_PRIORITY ], &xTaskTCBs[ i ].xStateListItem );
    }

    /* Create one more task with preemption disabled to run on core 0. */
    xTaskTCBs[ 0 ].xTaskRunState = taskTASK_NOT_RUNNING;
    xTaskTCB.uxPriority = tskIDLE_PRIORITY;
    xTaskTCB.xStateListItem.pvOwner = &xTaskTCB;
    xTaskTCB.uxCoreAffinityMask = ( ( 1U << configNUMBER_OF_CORES ) - 1U );
    pxCurrentTCBs[ 0 ] = &xTaskTCB;
    xTaskTCB.xTaskRunState = 0;
    xTaskTCB.xStateListItem.pxContainer = &pxReadyTasksLists[ tskIDLE_PRIORITY ];
    xTaskTCB.uxTaskAttributes = 0;
    xTaskTCB.xPreemptionDisable = pdTRUE;
    listINSERT_END( &pxReadyTasksLists[ tskIDLE_PRIORITY ], &xTaskTCB.xStateListItem );

    /* API calls. */
    xReturn = xTaskIncrementTick();

    /* Validations. */

    /* Equal priority task is waiting to run. Preemption is disabled for task running
     * on core 0. Switching is not required in this test. */
    TEST_ASSERT_EQUAL( pdFALSE, xReturn );
    TEST_ASSERT_EQUAL( portMAX_DELAY, xNextTaskUnblockTime );
}

/**
 * @brief xTaskIncrementTick - ready higher priority delayed task.
 *
 * Verify that the core is yielding when ready a higher priority delayed ready task.
 *
 * <b>Coverage</b>
 * @code{c}
 * prvAddTaskToReadyList( pxTCB );
 * ...
 * #if ( configUSE_PREEMPTION == 1 )
 * {
 *     ...
 *     #if ( configNUMBER_OF_CORES == 1 )
 *     {
 *         ...
 *     }
 *     #else
 *     {
 *         prvYieldForTask( pxTCB );
 *     }
 *     #endif
 * }
 * #endif
 * @endcode
 * prvYieldForTask( pxTCB ) is covered.
 */
void test_coverage_xTaskIncrementTick_ready_higher_priority_delayed_task( void )
{
    BaseType_t xReturn;
    TCB_t xTaskTCBs[ configNUMBER_OF_CORES ] = { NULL };
    TCB_t xTaskTCB = { NULL };
    List_t xEventList = { 0 };
    uint32_t i;

    /* Setup the variables and structure. */
    /* Initialize the idle priority ready list and set top ready priority to idle priority. */
    vListInitialise( &( pxReadyTasksLists[ tskIDLE_PRIORITY ] ) );
    vListInitialise( &( pxReadyTasksLists[ tskIDLE_PRIORITY + 1 ] ) );
    vListInitialise( &xEventList );
    uxTopReadyPriority = tskIDLE_PRIORITY;
    uxSchedulerSuspended = pdFALSE;
    xTickCount = 0;
    xNextTaskUnblockTime = 0;
    vListInitialise( &xDelayedTaskList1 );
    pxDelayedTaskList = &xDelayedTaskList1;

    /* Create idle tasks and add it into the ready list. */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        xTaskTCBs[ i ].uxPriority = tskIDLE_PRIORITY;
        xTaskTCBs[ i ].xStateListItem.pvOwner = &xTaskTCBs[ i ];
        xTaskTCBs[ i ].uxCoreAffinityMask = ( ( 1U << configNUMBER_OF_CORES ) - 1U );
        pxCurrentTCBs[ i ] = &xTaskTCBs[ i ];
        xTaskTCBs[ i ].xTaskRunState = i;
        xTaskTCBs[ i ].xStateListItem.pxContainer = &pxReadyTasksLists[ tskIDLE_PRIORITY ];
        xTaskTCBs[ i ].uxTaskAttributes = taskATTRIBUTE_IS_IDLE;
        listINSERT_END( &pxReadyTasksLists[ tskIDLE_PRIORITY ], &xTaskTCBs[ i ].xStateListItem );
    }

    /* Create one more higher priority task to run on core 0. */
    xTaskTCB.uxPriority = tskIDLE_PRIORITY + 1;
    xTaskTCB.xStateListItem.pvOwner = &xTaskTCB;
    xTaskTCB.uxCoreAffinityMask = ( ( 1U << configNUMBER_OF_CORES ) - 1U );
    xTaskTCB.xTaskRunState = 0;
    xTaskTCB.xStateListItem.pxContainer = pxDelayedTaskList;
    xTaskTCB.uxTaskAttributes = 0;
    xTaskTCB.xPreemptionDisable = pdTRUE;
    listINSERT_END( pxDelayedTaskList, &xTaskTCB.xStateListItem );
    xTaskTCB.xEventListItem.pvOwner = &xTaskTCB;
    xTaskTCB.xEventListItem.pxContainer = &xEventList;
    listINSERT_END( &xEventList, &xTaskTCB.xEventListItem );

    /* API calls. */
    xReturn = xTaskIncrementTick();

    /* Validations. */
    /* Core 0 is running a idle priority task. Switching is required in this test. */
    TEST_ASSERT_EQUAL( pdTRUE, xReturn );

    /* The implementation will select the last core to yield for the higher priority
     * task. Verify that the task running on the last core has state taskTASK_YIELDING. */
    TEST_ASSERT_EQUAL( taskTASK_YIELDING, xTaskTCBs[ configNUMBER_OF_CORES - 1 ].xTaskRunState );
    TEST_ASSERT_EQUAL( portMAX_DELAY, xNextTaskUnblockTime );
}
