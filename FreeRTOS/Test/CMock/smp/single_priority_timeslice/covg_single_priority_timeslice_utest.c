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
/*! @file covg_single_priority_timeslice_utest.c */

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
#include "mock_fake_infiniteloop.h"

/* ===========================  EXTERN VARIABLES  =========================== */
extern volatile UBaseType_t uxDeletedTasksWaitingCleanUp;
extern volatile TCB_t * pxCurrentTCBs[ configNUMBER_OF_CORES ];
extern UBaseType_t uxTopReadyPriority;
extern List_t pxReadyTasksLists[ configMAX_PRIORITIES ];
extern BaseType_t xSchedulerRunning;
extern UBaseType_t uxCurrentNumberOfTasks;
extern volatile BaseType_t xYieldPendings[ configNUMBER_OF_CORES ];

/* ===========================  EXTERN FUNCTIONS  =========================== */
extern void prvIdleTask( void );
extern void prvPassiveIdleTask( void );
extern void prvSelectHighestPriorityTask( BaseType_t xCoreID );

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
void vApplicationPassiveIdleHook( void )
{
    /* Adding this function to pass compilation. */
}

/* ==============================  Test Cases  ============================== */

/* @brief prvIdleTask - no other idle priority task
 *
 * This test calls the prvPassiveIdleTask to cover the condition that no other idle
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
 * This test calls the prvPassiveIdleTask to cover the condition that there are more
 * idle priority level tasks than configNUMBER_OF_CORES. Yield is called in prvPassiveIdleTask.
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
            xTaskTCBs[ i ].xTaskRunState = -1; /* Set run state to taskTASK_NOT_RUNNING. */
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

/* @brief prvPassiveIdleTask - no other idle priority task
 *
 * This test calls the prvPassiveIdleTask to cover the condition that no other idle
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
void test_coverage_prvPassiveIdleTask_no_other_idle_priority_task( void )
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
    prvPassiveIdleTask();

    /* Validations. xTaskTCBs[ 0 ] still runs on core 0. */
    configASSERT( pxCurrentTCBs[ 0 ] == &xTaskTCBs[ 0 ] );
}

/* @brief prvPassiveIdleTask - yield for idle priority task
 *
 * This test calls the prvPassiveIdleTask to cover the condition that there are more
 * idle priority level tasks than configNUMBER_OF_CORES. Yield is called in prvPassiveIdleTask.
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
void test_coverage_prvPassiveIdleTask_yield_for_idle_priority_task( void )
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
            xTaskTCBs[ i ].xTaskRunState = -1; /* Set run state to taskTASK_NOT_RUNNING. */
        }

        listINSERT_END( &pxReadyTasksLists[ tskIDLE_PRIORITY ], &xTaskTCBs[ i ].xStateListItem );
    }

    /* Expectations. */
    vFakeInfiniteLoop_ExpectAndReturn( 1 );
    vFakeInfiniteLoop_ExpectAndReturn( 0 );

    /* API calls. Runs the idle task function on core 0. */
    prvPassiveIdleTask();

    /* Validations. xTaskTCBs[ i ] runs on core 0. */
    configASSERT( pxCurrentTCBs[ 0 ] == &xTaskTCBs[ i ] );
}

/* @brief prvSelectHighestPriorityTask - not schedule none idle task.
 *
 * Verify that none idle task can't be scheduled when there is higher priority task
 * running with single priority config.
 *
 * <b>Coverage</b>
 * @code{c}
 * if( uxCurrentPriority < uxTopReadyPriority )
 * {
 *     if( ( pxTCB->uxTaskAttributes & taskATTRIBUTE_IS_IDLE ) == 0 )
 *     {
 *         continue;
 *     }
 * }
 * @endcode
 * ( ( pxTCB->uxTaskAttributes & taskATTRIBUTE_IS_IDLE ) == 0 ) is true.
 */
void test_coverage_prvSelectHighestPriorityTask_not_schedule_none_idle_task( void )
{
    TCB_t xTaskTCBs[ configNUMBER_OF_CORES + 2U ] = { 0 };
    uint32_t i = 0;

    /* Setup the variables and structure. */

    /* Initialize the idle priority ready list and set top ready priority to higher
     * priority than idle. */
    vListInitialise( &( pxReadyTasksLists[ tskIDLE_PRIORITY ] ) );
    vListInitialise( &( pxReadyTasksLists[ tskIDLE_PRIORITY + 1 ] ) );
    uxTopReadyPriority = tskIDLE_PRIORITY + 1;
    uxCurrentNumberOfTasks = 0;

    /* Create one normal task to be inserted at the beginning of ready list. */
    vCreateStaticTestTaskAffinity( &xTaskTCBs[ 0 ],
                                   ( ( 1U << configNUMBER_OF_CORES ) - 1U ),
                                   tskIDLE_PRIORITY,
                                   taskTASK_NOT_RUNNING,
                                   pdFALSE );
    listINSERT_END( &pxReadyTasksLists[ tskIDLE_PRIORITY ], &xTaskTCBs[ 0 ].xStateListItem );

    /* Create core numbers running idle task. */
    for( i = 1; i < ( configNUMBER_OF_CORES + 1 ); i++ )
    {
        vCreateStaticTestTaskAffinity( &xTaskTCBs[ i ],
                                       ( ( 1U << configNUMBER_OF_CORES ) - 1U ),
                                       tskIDLE_PRIORITY,
                                       ( i - 1 ),
                                       pdTRUE );
        listINSERT_END( &pxReadyTasksLists[ tskIDLE_PRIORITY ], &xTaskTCBs[ i ].xStateListItem );
    }

    /* Create one higher priority normal task running on core one. */
    vCreateStaticTestTaskAffinity( &xTaskTCBs[ i ],
                                   ( ( 1U << configNUMBER_OF_CORES ) - 1U ),
                                   tskIDLE_PRIORITY + 1,
                                   1,
                                   pdFALSE );
    listINSERT_END( &pxReadyTasksLists[ tskIDLE_PRIORITY + 1 ], &xTaskTCBs[ i ].xStateListItem );

    /* The original core 1 idle task now is not running. */
    xTaskTCBs[ 2 ].xTaskRunState = taskTASK_NOT_RUNNING;

    /* The ready list has the following status.
     * Ready list [ 0 ] : T0, T1(0), T2, ..., TN(N-1).
     * Ready list [ 1 ] : TN+1(1). */

    /* API calls. Select task for core 0. */
    prvSelectHighestPriorityTask( 0 );

    /* Validations.*/

    /* T0 won't be selected to run after calling prvSelectHighestPriorityTask since
     * it is not an idle task and top priority is higher than idle. */
    TEST_ASSERT_NOT_EQUAL( &xTaskTCBs[ 0 ], pxCurrentTCBs[ 0 ] );
    /* T1 is not running since other idle task will be selected first. */
    TEST_ASSERT_EQUAL( taskTASK_NOT_RUNNING, xTaskTCBs[ 0 ].xTaskRunState );
    /* T2 is selected to run on core 0. */
    TEST_ASSERT_EQUAL( 0, xTaskTCBs[ 2 ].xTaskRunState );
}

/* @brief prvSelectHighestPriorityTask - yield for previous task with core affinity.
 *
 * prvSelectHighestPriorityTask selects a task to run on specified core. The scheduler
 * also selects another core to yield for previous task if the condition is satisfied.
 * This test verifies the coverage of taskTASK_YIELDING condition.
 *
 * <b>Coverage</b>
 * @code{c}
 * if( ( xTaskPriority < xLowestPriority ) &&
 *     ( taskTASK_IS_RUNNING( pxCurrentTCBs[ uxCore ] ) != pdFALSE ) &&
 *     ( xYieldPendings[ uxCore ] == pdFALSE ) )
 * {
 *     #if ( configUSE_TASK_PREEMPTION_DISABLE == 1 )
 *         if( pxCurrentTCBs[ uxCore ]->xPreemptionDisable == pdFALSE )
 *     #endif
 *     {
 *         xLowestPriority = xTaskPriority;
 *         xLowestPriorityCore = uxCore;
 *     }
 * }
 * @endcode
 * ( taskTASK_IS_RUNNING( pxCurrentTCBs[ uxCore ] ) != pdFALSE ) is false.
 */
void test_coverage_prvSelectHighestPriorityTask_affinity_task_yielding( void )
{
    TCB_t xTaskTCBs[ configNUMBER_OF_CORES + 2 ] = { 0 };
    uint32_t i = 0;

    /* Setup the variables and structure. */

    /* Initialize the idle priority ready list and set top ready priority to higher
     * priority than idle. */
    vListInitialise( &( pxReadyTasksLists[ tskIDLE_PRIORITY ] ) );
    vListInitialise( &( pxReadyTasksLists[ tskIDLE_PRIORITY + 1 ] ) );
    uxTopReadyPriority = tskIDLE_PRIORITY + 1;
    uxCurrentNumberOfTasks = 0;

    /* Create core numbers running idle task. */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        vCreateStaticTestTaskAffinity( &xTaskTCBs[ i ],
                                       ( ( 1U << configNUMBER_OF_CORES ) - 1U ),
                                       tskIDLE_PRIORITY,
                                       i,
                                       pdTRUE );
        listINSERT_END( &pxReadyTasksLists[ tskIDLE_PRIORITY ], &xTaskTCBs[ i ].xStateListItem );
    }

    /* Create two higher priority normal task. */
    for( i = configNUMBER_OF_CORES; i < ( configNUMBER_OF_CORES + 2 ); i++ )
    {
        vCreateStaticTestTaskAffinity( &xTaskTCBs[ i ],
                                       ( ( 1U << configNUMBER_OF_CORES ) - 1U ),
                                       tskIDLE_PRIORITY + 1,
                                       taskTASK_NOT_RUNNING,
                                       pdFALSE );
        listINSERT_END( &pxReadyTasksLists[ tskIDLE_PRIORITY + 1 ], &xTaskTCBs[ i ].xStateListItem );
    }

    /* Core 0 runs task TN. The original core 0 idle task now is not running. */
    xTaskTCBs[ 0 ].xTaskRunState = taskTASK_NOT_RUNNING;
    pxCurrentTCBs[ 0 ] = &xTaskTCBs[ configNUMBER_OF_CORES ];
    xTaskTCBs[ configNUMBER_OF_CORES ].xTaskRunState = 0;

    /* Idle task 1 is yielding. */
    xTaskTCBs[ 1 ].xTaskRunState = taskTASK_YIELDING;

    /* Setup the affinity mask for TN and TN+1. */
    xTaskTCBs[ configNUMBER_OF_CORES ].uxCoreAffinityMask = ( 1 << 0 ) | ( 1 << 1 );
    xTaskTCBs[ configNUMBER_OF_CORES + 1 ].uxCoreAffinityMask = ( 1 << 0 );

    /* The ready list has the following status.
     * Ready list [ 0 ] : T0, T1(yielding), T2(2), ..., TN-1(N-1).
     * Ready list [ 1 ] : TN(0), TN+1. */

    /* API calls. Select task for core 0. Task TN+1 will be selected. Scheduler
     * tries to find another core to yield for TN. The affinity mask limited the
     * core for TN to run on core 1 only ( core 0 is running TN+1 ). Idle task 1 is
     * yielding. Therefore, no core will yield for TN. */
    prvSelectHighestPriorityTask( 0 );

    /* Validations.*/

    /* T0 won't be selected to run after calling prvSelectHighestPriorityTask since
     * it can only runs on core 0 and core 1. Task on core 1 is yielding. */
    TEST_ASSERT_NOT_EQUAL( &xTaskTCBs[ 0 ], pxCurrentTCBs[ 0 ] );
    /* T1 is still running on core 1 since it is yielding. */
    TEST_ASSERT_EQUAL( &xTaskTCBs[ 1 ], pxCurrentTCBs[ 1 ] );
    /* TN+1 is selected to run on core 0. */
    TEST_ASSERT_EQUAL( 0, xTaskTCBs[ configNUMBER_OF_CORES + 1 ].xTaskRunState );
}

/* @brief prvSelectHighestPriorityTask - yield for previous task with core affinity.
 *
 * prvSelectHighestPriorityTask selects a task to run on specified core. The scheduler
 * also selects another core to yield for previous task if the condition is satisfied.
 * This test verifies the coverage of invalid run state condition.
 *
 * <b>Coverage</b>
 * @code{c}
 * if( ( xTaskPriority < xLowestPriority ) &&
 *     ( taskTASK_IS_RUNNING( pxCurrentTCBs[ uxCore ] ) != pdFALSE ) &&
 *     ( xYieldPendings[ uxCore ] == pdFALSE ) )
 * {
 *     #if ( configUSE_TASK_PREEMPTION_DISABLE == 1 )
 *         if( pxCurrentTCBs[ uxCore ]->xPreemptionDisable == pdFALSE )
 *     #endif
 *     {
 *         xLowestPriority = xTaskPriority;
 *         xLowestPriorityCore = uxCore;
 *     }
 * }
 * @endcode
 * ( taskTASK_IS_RUNNING( pxCurrentTCBs[ uxCore ] ) != pdFALSE ) is false.
 */
void test_coverage_prvSelectHighestPriorityTask_affinity_task_state_invalid( void )
{
    TCB_t xTaskTCBs[ configNUMBER_OF_CORES + 2 ] = { 0 };
    uint32_t i = 0;

    /* Setup the variables and structure. */

    /* Initialize the idle priority ready list and set top ready priority to higher
     * priority than idle. */
    vListInitialise( &( pxReadyTasksLists[ tskIDLE_PRIORITY ] ) );
    vListInitialise( &( pxReadyTasksLists[ tskIDLE_PRIORITY + 1 ] ) );
    uxTopReadyPriority = tskIDLE_PRIORITY + 1;
    uxCurrentNumberOfTasks = 0;

    /* Create core numbers running idle task. */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        vCreateStaticTestTaskAffinity( &xTaskTCBs[ i ],
                                       ( ( 1U << configNUMBER_OF_CORES ) - 1U ),
                                       tskIDLE_PRIORITY,
                                       i,
                                       pdTRUE );
        listINSERT_END( &pxReadyTasksLists[ tskIDLE_PRIORITY ], &xTaskTCBs[ i ].xStateListItem );
    }

    /* Create two higher priority normal task. */
    for( i = configNUMBER_OF_CORES; i < ( configNUMBER_OF_CORES + 2 ); i++ )
    {
        vCreateStaticTestTaskAffinity( &xTaskTCBs[ i ],
                                       ( ( 1U << configNUMBER_OF_CORES ) - 1U ),
                                       tskIDLE_PRIORITY + 1,
                                       taskTASK_NOT_RUNNING,
                                       pdFALSE );
        listINSERT_END( &pxReadyTasksLists[ tskIDLE_PRIORITY + 1 ], &xTaskTCBs[ i ].xStateListItem );
    }

    /* Core 0 runs task TN. The original core 0 idle task now is not running. */
    xTaskTCBs[ 0 ].xTaskRunState = taskTASK_NOT_RUNNING;
    pxCurrentTCBs[ 0 ] = &xTaskTCBs[ configNUMBER_OF_CORES ];
    xTaskTCBs[ configNUMBER_OF_CORES ].xTaskRunState = 0;

    /* Idle task 1 is of invalid run state. */
    xTaskTCBs[ 1 ].xTaskRunState = configNUMBER_OF_CORES;

    /* Setup the affinity mask for TN and TN+1. */
    xTaskTCBs[ configNUMBER_OF_CORES ].uxCoreAffinityMask = ( 1 << 0 ) | ( 1 << 1 );
    xTaskTCBs[ configNUMBER_OF_CORES + 1 ].uxCoreAffinityMask = ( 1 << 0 );

    /* The ready list has the following status.
     * Ready list [ 0 ] : T0, T1(yielding), T2(2), ..., TN-1(N-1).
     * Ready list [ 1 ] : TN(0), TN+1. */

    /* API calls. Select task for core 0. Task TN+1 will be selected. Scheduler
     * tries to find another core to yield for TN. The affinity mask limited the
     * core for TN to run on core 1 only ( core 0 is running TN+1 ). Idle task 1 has
     * invalid run state. Therefore, no core will yield for TN. */
    prvSelectHighestPriorityTask( 0 );

    /* Validations.*/

    /* T0 won't be selected to run after calling prvSelectHighestPriorityTask since
     * it can only runs on core 0 and core 1. */
    TEST_ASSERT_NOT_EQUAL( &xTaskTCBs[ 0 ], pxCurrentTCBs[ 0 ] );
    /* TN+1 is selected to run on core 0. */
    TEST_ASSERT_EQUAL( 0, xTaskTCBs[ configNUMBER_OF_CORES + 1 ].xTaskRunState );
}

/* @brief prvSelectHighestPriorityTask - yield for previous task with core affinity.
 *
 * prvSelectHighestPriorityTask selects a task to run on specified core. The scheduler
 * also selects another core to yield for previous task if the condition is satisfied.
 * This test verifies the coverage of yield pending condition.
 *
 * <b>Coverage</b>
 * @code{c}
 * if( ( xTaskPriority < xLowestPriority ) &&
 *     ( taskTASK_IS_RUNNING( pxCurrentTCBs[ uxCore ] ) != pdFALSE ) &&
 *     ( xYieldPendings[ uxCore ] == pdFALSE ) )
 * {
 *     #if ( configUSE_TASK_PREEMPTION_DISABLE == 1 )
 *         if( pxCurrentTCBs[ uxCore ]->xPreemptionDisable == pdFALSE )
 *     #endif
 *     {
 *         xLowestPriority = xTaskPriority;
 *         xLowestPriorityCore = uxCore;
 *     }
 * }
 * @endcode
 * ( xYieldPendings[ uxCore ] == pdFALSE ) is false.
 */
void test_coverage_prvSelectHighestPriorityTask_affinity_task_yield_pending( void )
{
    TCB_t xTaskTCBs[ configNUMBER_OF_CORES + 2 ] = { 0 };
    uint32_t i = 0;

    /* Setup the variables and structure. */

    /* Initialize the idle priority ready list and set top ready priority to higher
     * priority than idle. */
    vListInitialise( &( pxReadyTasksLists[ tskIDLE_PRIORITY ] ) );
    vListInitialise( &( pxReadyTasksLists[ tskIDLE_PRIORITY + 1 ] ) );
    uxTopReadyPriority = tskIDLE_PRIORITY + 1;
    uxCurrentNumberOfTasks = 0;

    /* Create core numbers running idle task. */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        vCreateStaticTestTaskAffinity( &xTaskTCBs[ i ],
                                       ( ( 1U << configNUMBER_OF_CORES ) - 1U ),
                                       tskIDLE_PRIORITY,
                                       i,
                                       pdTRUE );
        listINSERT_END( &pxReadyTasksLists[ tskIDLE_PRIORITY ], &xTaskTCBs[ i ].xStateListItem );
    }

    /* Create two higher priority normal task. */
    for( i = configNUMBER_OF_CORES; i < ( configNUMBER_OF_CORES + 2 ); i++ )
    {
        vCreateStaticTestTaskAffinity( &xTaskTCBs[ i ],
                                       ( ( 1U << configNUMBER_OF_CORES ) - 1U ),
                                       tskIDLE_PRIORITY + 1,
                                       taskTASK_NOT_RUNNING,
                                       pdFALSE );
        listINSERT_END( &pxReadyTasksLists[ tskIDLE_PRIORITY + 1 ], &xTaskTCBs[ i ].xStateListItem );
    }

    /* Core 0 runs task TN. The original core 0 idle task now is not running. */
    xTaskTCBs[ 0 ].xTaskRunState = taskTASK_NOT_RUNNING;
    pxCurrentTCBs[ 0 ] = &xTaskTCBs[ configNUMBER_OF_CORES ];
    xTaskTCBs[ configNUMBER_OF_CORES ].xTaskRunState = 0;

    /* Core 1 has yield pending. */
    xYieldPendings[ 1 ] = pdTRUE;

    /* Setup the affinity mask for TN and TN+1. */
    xTaskTCBs[ configNUMBER_OF_CORES ].uxCoreAffinityMask = ( 1 << 0 ) | ( 1 << 1 );
    xTaskTCBs[ configNUMBER_OF_CORES + 1 ].uxCoreAffinityMask = ( 1 << 0 );

    /* The ready list has the following status.
     * Ready list [ 0 ] : T0, T1(yielding), T2(2), ..., TN-1(N-1).
     * Ready list [ 1 ] : TN(0), TN+1. */

    /* API calls. Select task for core 0. Task TN+1 will be selected. Scheduler
     * tries to find another core to yield for TN. The affinity mask limited the
     * core for TN to run on core 1 only ( core 0 is running TN+1 ). Core 1 has yield
     * pending. Therefore, no core will yield for TN. */
    prvSelectHighestPriorityTask( 0 );

    /* Validations.*/

    /* T0 won't be selected to run after calling prvSelectHighestPriorityTask since
     * it can only runs on core 0 and core 1. Core 1 has yield pending. */
    TEST_ASSERT_NOT_EQUAL( &xTaskTCBs[ 0 ], pxCurrentTCBs[ 0 ] );
    /* T1 is still running on core 1 since it has yield pending. */
    TEST_ASSERT_EQUAL( &xTaskTCBs[ 1 ], pxCurrentTCBs[ 1 ] );
    /* TN+1 is selected to run on core 0. */
    TEST_ASSERT_EQUAL( 0, xTaskTCBs[ configNUMBER_OF_CORES + 1 ].xTaskRunState );
}
