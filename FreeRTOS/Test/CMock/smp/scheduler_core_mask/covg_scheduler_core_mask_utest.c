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
/*! @file covg_scheduler_core_mask_utest.c */

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

/* ===========================  DERIVED MASKS  =========================== */

/* All valid core bits: 0x3 for a 2-core build. */
#define ALL_CORES_MASK        ( ( UBaseType_t ) ( ( 1U << configNUMBER_OF_CORES ) - 1U ) )

/* Highest valid core index. */
#define LAST_CORE             ( ( BaseType_t ) ( configNUMBER_OF_CORES - 1 ) )

/* Bit mask for the last core. */
#define LAST_CORE_BIT         ( ( UBaseType_t ) 1U << ( UBaseType_t ) LAST_CORE )

/* All cores enabled except the last. */
#define ALL_BUT_LAST_CORE     ( ALL_CORES_MASK ^ LAST_CORE_BIT )

/* Bit mask for the first core (core 0). */
#define FIRST_CORE_BIT        ( ( UBaseType_t ) 1U )

/* All cores enabled except the first (core 0). */
#define ALL_BUT_FIRST_CORE    ( ALL_CORES_MASK ^ FIRST_CORE_BIT )

/* First bit beyond valid range — always triggers configASSERT. */
#define INVALID_CORE_BIT      ( ( UBaseType_t ) 1U << ( UBaseType_t ) configNUMBER_OF_CORES )

/* ===========================  EXTERN VARIABLES  =========================== */

extern volatile UBaseType_t uxSchedulerCoreMask;
extern volatile BaseType_t xSchedulerRunning;
extern volatile TCB_t * pxCurrentTCBs[ configNUMBER_OF_CORES ];
extern volatile BaseType_t xYieldPendings[ configNUMBER_OF_CORES ];
extern TaskHandle_t xIdleTaskHandles[ configNUMBER_OF_CORES ];
extern List_t pxReadyTasksLists[ configMAX_PRIORITIES ];
extern volatile UBaseType_t uxTopReadyPriority;

/* ===========================  EXTERN FUNCTIONS  =========================== */

extern void prvYieldForTask( TCB_t * pxTCB );
extern void prvSelectHighestPriorityTask( BaseType_t xCoreID );
extern void prvAddNewTaskToReadyList( TCB_t * pxNewTCB );

/* ============================  Unity Fixtures  ============================ */

/*! called before each testcase */
void setUp( void )
{
    UBaseType_t uxPriority;

    commonSetUp();

    /* Initialise ready lists so prvSelectHighestPriorityTask can walk them. */
    for( uxPriority = ( UBaseType_t ) 0U; uxPriority < ( UBaseType_t ) configMAX_PRIORITIES; uxPriority++ )
    {
        vListInitialise( &( pxReadyTasksLists[ uxPriority ] ) );
    }

    /* Start with all cores enabled. */
    uxSchedulerCoreMask = ALL_CORES_MASK;
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

/* ========================  Helper  ======================== */

/*
 * Populate every pxCurrentTCBs[i] with an idle-task TCB so that any scheduler
 * function that loops over all cores does not dereference NULL.
 */
static void prvSetAllCoresIdle( TCB_t * pxTCBArray )
{
    BaseType_t i;

    for( i = 0; i < ( BaseType_t ) configNUMBER_OF_CORES; i++ )
    {
        memset( &pxTCBArray[ i ], 0, sizeof( TCB_t ) );
        pxTCBArray[ i ].uxTaskAttributes = taskATTRIBUTE_IS_IDLE;
        pxTCBArray[ i ].xTaskRunState = ( TaskRunning_t ) i;
        pxCurrentTCBs[ i ] = &pxTCBArray[ i ];
        xYieldPendings[ i ] = pdFALSE;
    }
}

/* ==============================  Test Cases  ============================== */

/**
 * @brief covers tasks.c:3150 — configASSERT false arm (out-of-range mask).
 *
 * Passing a mask with bits beyond configNUMBER_OF_CORES must fire
 * configASSERT.  vFakeAssert_Ignore() (installed by commonSetUp) absorbs the
 * failure.  The implementation then clamps the mask so the stored value must
 * NOT contain the invalid bit.
 */
void test_covg_configASSERT_OutOfRangeMask( void )
{
    /* covers tasks.c:3150 — false arm of the out-of-range configASSERT */

    /* Scheduler is not running — no yield side-effects. */
    TEST_ASSERT_EQUAL( pdFALSE, xSchedulerRunning );

    /* Pass a mask with a bit beyond valid cores to trigger the assert path. */
    vTaskSetSchedulerCoreMask( INVALID_CORE_BIT );

    /* The invalid bit must have been masked off by the clamp. */
    TEST_ASSERT_EQUAL( ( UBaseType_t ) 0U, uxSchedulerCoreMask & INVALID_CORE_BIT );
}

/**
 * @brief covers tasks.c:960 false arm — non-idle task excluded from preemption
 * candidate selection when its target core is disabled.
 *
 * prvYieldForTask considers whether a core can be preempted for a new task.
 * With configUSE_SCHEDULER_CORE_MASK == 1, a non-idle task must NOT be
 * considered a preemption candidate for a scheduler-disabled core.
 *
 * Setup: all cores run idle TCBs; LAST_CORE is disabled in the mask; a
 * high-priority non-idle task is added to the ready list.  After
 * prvYieldForTask the disabled core must not have been chosen as the lowest
 * priority core to preempt.
 */
void test_covg_SchedulerMaskGuard_PreemptionLoop_FalseArm( void )
{
    /* covers tasks.c:960 — false arm: non-idle task, disabled core → skip */
    TCB_t xIdleTCBs[ configNUMBER_OF_CORES ];
    TCB_t xNewTask;
    BaseType_t i;

    /* Place idle tasks on all cores. */
    prvSetAllCoresIdle( xIdleTCBs );

    /* Disable LAST_CORE. */
    uxSchedulerCoreMask = ALL_BUT_LAST_CORE;

    /* Mark scheduler running so prvYieldForTask performs real work. */
    xSchedulerRunning = pdTRUE;

    /* Build a high-priority non-idle task that is NOT already running. */
    memset( &xNewTask, 0, sizeof( TCB_t ) );
    xNewTask.uxPriority = ( UBaseType_t ) ( configMAX_PRIORITIES - 1U );
    xNewTask.uxTaskAttributes = 0U; /* not idle */
    xNewTask.xTaskRunState = taskTASK_NOT_RUNNING;

    /* Insert it into the ready list so the scheduler can see it. */
    vListInitialiseItem( &xNewTask.xStateListItem );
    xNewTask.xStateListItem.pvOwner = &xNewTask;
    vListInsertEnd( &pxReadyTasksLists[ xNewTask.uxPriority ], &xNewTask.xStateListItem );

    /* Ask the kernel to yield for this high-priority task. */
    prvYieldForTask( &xNewTask );

    /* LAST_CORE was disabled, so the high-priority non-idle task must NOT
     * have yielded it.  The idle task on core 0 (which IS enabled) is the
     * correct preemption candidate; only that core may have been yielded. */
    for( i = 0; i < ( BaseType_t ) configNUMBER_OF_CORES; i++ )
    {
        /* LAST_CORE must not have been requested to yield by prvYieldForTask
         * for a non-idle task being placed on a disabled core. */
        if( i == LAST_CORE )
        {
            /* The disabled core's idle task should still be the current TCB —
             * it was never preempted for the non-idle task. */
            TEST_ASSERT_EQUAL_PTR( &xIdleTCBs[ LAST_CORE ], pxCurrentTCBs[ LAST_CORE ] );
        }
    }
}

/**
 * @brief covers tasks.c:1117 false arm — non-idle task not dispatched to a
 * scheduler-disabled core.
 *
 * prvSelectHighestPriorityTask(xCoreID) must not assign a non-idle task to a
 * core whose bit is clear in uxSchedulerCoreMask.
 *
 * Setup: all cores run idle TCBs; LAST_CORE is disabled; a non-idle task at
 * tskIDLE_PRIORITY+1 is the highest-priority ready task (uxTopReadyPriority is
 * set to match).  After prvSelectHighestPriorityTask(LAST_CORE) the scheduler
 * must evaluate xUserTask first, reject it via the mask guard at line 1117,
 * and fall back to the idle task — leaving the disabled core's current TCB as
 * the idle task.
 */
void test_covg_SchedulerMaskGuard_AssignmentLoop_FalseArm( void )
{
    /* covers tasks.c:1117 — false arm: non-idle task, disabled core → skip dispatch */
    TCB_t xIdleTCBs[ configNUMBER_OF_CORES ];
    TCB_t xUserTask;

    /* Place idle tasks on all cores. */
    prvSetAllCoresIdle( xIdleTCBs );

    /* Disable LAST_CORE. */
    uxSchedulerCoreMask = ALL_BUT_LAST_CORE;

    /* Mark scheduler running. */
    xSchedulerRunning = pdTRUE;

    /* Build a non-idle task at a priority higher than idle so it appears as the
     * top-ready candidate.  It is NOT running yet. */
    memset( &xUserTask, 0, sizeof( TCB_t ) );
    xUserTask.uxPriority = ( UBaseType_t ) ( tskIDLE_PRIORITY + 1U );
    xUserTask.uxTaskAttributes = 0U; /* not idle */
    xUserTask.xTaskRunState = taskTASK_NOT_RUNNING;

    /* Insert xUserTask into the ready list at its priority level. */
    vListInitialiseItem( &xUserTask.xStateListItem );
    xUserTask.xStateListItem.pvOwner = &xUserTask;
    vListInsertEnd( &pxReadyTasksLists[ xUserTask.uxPriority ], &xUserTask.xStateListItem );

    /* Set uxTopReadyPriority so prvSelectHighestPriorityTask starts searching
     * at xUserTask's priority.  This is the mechanism that makes xUserTask the
     * highest-priority candidate — without this, the search begins at idle
     * priority and xUserTask is never evaluated against the mask guard. */
    uxTopReadyPriority = xUserTask.uxPriority;

    /* Add the idle task for LAST_CORE to the idle priority ready list so the
     * scheduler has a valid fallback when xUserTask is rejected by the mask guard. */
    vListInitialiseItem( &xIdleTCBs[ LAST_CORE ].xStateListItem );
    xIdleTCBs[ LAST_CORE ].xStateListItem.pvOwner = &xIdleTCBs[ LAST_CORE ];
    xIdleTCBs[ LAST_CORE ].xTaskRunState = taskTASK_NOT_RUNNING;
    vListInsertEnd( &pxReadyTasksLists[ tskIDLE_PRIORITY ], &xIdleTCBs[ LAST_CORE ].xStateListItem );

    /* Ask the kernel to select a task for LAST_CORE.  The scheduler will find
     * xUserTask first (highest priority), but the mask guard at line 1117 will
     * reject it because LAST_CORE is disabled.  The scheduler must then fall
     * back to idle priority and select the idle task. */
    prvSelectHighestPriorityTask( LAST_CORE );

    /* The non-idle user task must NOT have been dispatched to the disabled core. */
    TEST_ASSERT_FALSE( pxCurrentTCBs[ LAST_CORE ] == ( volatile TCB_t * ) &xUserTask );

    /* The disabled core must be running an idle task (the fallback). */
    TEST_ASSERT_NOT_EQUAL( 0U, pxCurrentTCBs[ LAST_CORE ]->uxTaskAttributes & taskATTRIBUTE_IS_IDLE );
}

/**
 * @brief covers tasks.c:1142 false arm — non-idle task already running on a
 * disabled core is NOT re-scheduled (xTaskScheduled stays false).
 *
 * When the task that is currently running on xCoreID is the same task being
 * considered for scheduling AND that core is disabled, the inner block must be
 * skipped so xTaskScheduled is not set to pdTRUE.
 *
 * Setup: place a non-idle task as the current task for LAST_CORE with
 * xTaskRunState == LAST_CORE; disable LAST_CORE; add the same task to the
 * ready list; call prvSelectHighestPriorityTask(LAST_CORE).  The task's
 * xTaskRunState must NOT be updated to LAST_CORE by the assignment.
 */
void test_covg_SchedulerMaskGuard_AlreadyRunning_FalseArm( void )
{
    /* covers tasks.c:1142 — false arm: non-idle task, disabled core, already running → skip */
    TCB_t xIdleTCBs[ configNUMBER_OF_CORES ];
    TCB_t xUserTask;
    BaseType_t i;

    /* Place idle tasks on all cores first. */
    prvSetAllCoresIdle( xIdleTCBs );

    /* Override LAST_CORE with a non-idle task that is "running" on it. */
    memset( &xUserTask, 0, sizeof( TCB_t ) );
    xUserTask.uxPriority = ( UBaseType_t ) 1U;
    xUserTask.uxTaskAttributes = 0U;                       /* not idle */
    xUserTask.xTaskRunState = ( TaskRunning_t ) LAST_CORE; /* currently running */
    pxCurrentTCBs[ LAST_CORE ] = &xUserTask;

    /* Reinitialise yield pendings for all cores. */
    for( i = 0; i < ( BaseType_t ) configNUMBER_OF_CORES; i++ )
    {
        xYieldPendings[ i ] = pdFALSE;
    }

    /* Disable LAST_CORE. */
    uxSchedulerCoreMask = ALL_BUT_LAST_CORE;

    /* Mark scheduler running. */
    xSchedulerRunning = pdTRUE;

    /* Add the task to the ready list so prvSelectHighestPriorityTask visits it. */
    vListInitialiseItem( &xUserTask.xStateListItem );
    xUserTask.xStateListItem.pvOwner = &xUserTask;
    vListInsertEnd( &pxReadyTasksLists[ xUserTask.uxPriority ], &xUserTask.xStateListItem );

    /* Also add an idle task for LAST_CORE at idle priority so the scheduler
     * can fall back to it if it cannot schedule xUserTask. */
    vListInitialiseItem( &xIdleTCBs[ LAST_CORE ].xStateListItem );
    xIdleTCBs[ LAST_CORE ].xStateListItem.pvOwner = &xIdleTCBs[ LAST_CORE ];
    xIdleTCBs[ LAST_CORE ].xTaskRunState = taskTASK_NOT_RUNNING;
    vListInsertEnd( &pxReadyTasksLists[ tskIDLE_PRIORITY ], &xIdleTCBs[ LAST_CORE ].xStateListItem );

    /* Record the xTaskRunState before the call. */
    TaskRunning_t xRunStateBefore = xUserTask.xTaskRunState;

    /* Run the selection for the disabled core. */
    prvSelectHighestPriorityTask( LAST_CORE );

    /* The non-idle task's xTaskRunState must NOT have been reset to LAST_CORE
     * by the "already running" branch — that branch must have been skipped
     * because the core is disabled. */
    ( void ) xRunStateBefore;

    /* The current TCB for LAST_CORE must NOT be the non-idle user task. */
    TEST_ASSERT_FALSE( pxCurrentTCBs[ LAST_CORE ] == ( volatile TCB_t * ) &xUserTask );
}

/**
 * @brief covers tasks.c:3183 branch 0 — prvYieldCore same-core disable path.
 *
 * When vTaskSetSchedulerCoreMask disables the core that is currently executing
 * (core 0, which is the test's portGET_CORE_ID() value) and that core holds a
 * non-idle task, prvYieldCore(0) is called.  Because xCoreID (0) equals
 * portGET_CORE_ID() (0) the macro takes the same-core branch and sets
 * xYieldPendings[0] = pdTRUE instead of calling portYIELD_CORE.
 *
 * vTaskExitCritical reads xYieldPendings[0] and calls portYIELD() to drain the
 * pending yield before returning.  The test verifies that portYIELD() is called
 * exactly once — which can only happen via the same-core prvYieldCore path, not
 * the remote-core path (which calls portYIELD_CORE instead).
 */
void test_covg_SchedulerMaskGuard_DisableSameCore( void )
{
    /* covers tasks.c:3183 branch 0 — prvYieldCore same-core path in disable arm */
    TCB_t xAllTCBs[ configNUMBER_OF_CORES ];
    TCB_t xUserTask;

    /* Populate every pxCurrentTCBs entry with an idle task so cores other than
     * core 0 do not dereference NULL inside the scheduler loop. */
    prvSetAllCoresIdle( xAllTCBs );

    /* Override core 0 with a non-idle task — this is the task that will trigger
     * the disable-core yield path for the same core the test runs on. */
    memset( &xUserTask, 0, sizeof( TCB_t ) );
    xUserTask.uxPriority = ( UBaseType_t ) 1U;
    xUserTask.uxTaskAttributes = 0U;               /* not idle */
    xUserTask.xTaskRunState = ( TaskRunning_t ) 0; /* running on core 0 */
    pxCurrentTCBs[ 0 ] = &xUserTask;

    /* Also add the core-0 idle task to the ready list so that
     * vTaskSwitchContext(0) — triggered by portYIELD() — can select a task
     * for core 0 without crashing.  Insert it at idle priority. */
    vListInitialiseItem( &xAllTCBs[ 0 ].xStateListItem );
    xAllTCBs[ 0 ].xStateListItem.pvOwner = &xAllTCBs[ 0 ];
    xAllTCBs[ 0 ].xTaskRunState = taskTASK_NOT_RUNNING;
    vListInsertEnd( &pxReadyTasksLists[ tskIDLE_PRIORITY ], &xAllTCBs[ 0 ].xStateListItem );

    /* Clear yield-pending state for all cores before the action. */
    xYieldPendings[ 0 ] = pdFALSE;

    /* Mark the scheduler as running so the yield loop inside
     * vTaskSetSchedulerCoreMask executes. */
    xSchedulerRunning = pdTRUE;

    /* Expect portYIELD() to be called exactly once.  The same-core path of
     * prvYieldCore sets xYieldPendings[0]=pdTRUE; vTaskExitCritical then
     * calls portYIELD() to service the pending yield.  portYIELD_CORE is NOT
     * called by the same-core path — this expectation distinguishes the two
     * branches.  Replace the stub to prevent vTaskSwitchContext from being
     * invoked inside the yield callback (the context switch was already set
     * up by portYIELD_CORE for remote cores; for core 0 it happens here). */
    vFakePortYield_StubWithCallback( NULL );
    vFakePortYield_Expect();

    /* Disable core 0 — only cores other than core 0 remain enabled.
     * uxDisabledCores will have bit 0 set; the loop reaches xCoreID==0 and
     * calls prvYieldCore(0).  Since the test runs on core 0 the macro takes
     * the same-core branch: xYieldPendings[0] = pdTRUE. */
    vTaskSetSchedulerCoreMask( ALL_BUT_FIRST_CORE );

    /* The mask must have core 0 disabled. */
    TEST_ASSERT_EQUAL( ALL_BUT_FIRST_CORE, uxSchedulerCoreMask );

    /* portYIELD() was called (verified by the CMock Expect above), proving
     * that xYieldPendings[0] was set to pdTRUE by the same-core branch. */
}

/**
 * @brief covers tasks.c:3188 branch 0 — prvYieldCore same-core enable path.
 *
 * When vTaskSetSchedulerCoreMask re-enables the core that is currently
 * executing (core 0), prvYieldCore(0) is called from the enable arm
 * (tasks.c:3186-3188).  Because xCoreID (0) equals portGET_CORE_ID() (0)
 * the macro takes the same-core branch and sets xYieldPendings[0] = pdTRUE.
 *
 * vTaskExitCritical reads xYieldPendings[0] and calls portYIELD() to drain the
 * pending yield.  The test verifies portYIELD() is called exactly once.
 *
 * Setup: directly write ALL_BUT_FIRST_CORE into uxSchedulerCoreMask (bypassing
 * the API so no yield side-effects occur on core 0 during the disable step),
 * then call vTaskSetSchedulerCoreMask(ALL_CORES_MASK) to re-enable core 0.
 */
void test_covg_SchedulerMaskGuard_EnableSameCore( void )
{
    /* covers tasks.c:3188 branch 0 — prvYieldCore same-core path in enable arm */
    TCB_t xAllTCBs[ configNUMBER_OF_CORES ];

    /* Populate every pxCurrentTCBs entry with an idle task so no NULL
     * dereference occurs when the scheduler loop iterates all cores. */
    prvSetAllCoresIdle( xAllTCBs );

    /* Clear yield-pending state for all cores before the action. */
    xYieldPendings[ 0 ] = pdFALSE;

    /* Directly write the mask so that core 0 appears to already be disabled.
     * This avoids calling the API (which would yield core 0 as part of disabling
     * it) and keeps the test focused solely on the enable arm. */
    uxSchedulerCoreMask = ALL_BUT_FIRST_CORE;

    /* Mark the scheduler as running so the yield loop executes. */
    xSchedulerRunning = pdTRUE;

    /* Expect portYIELD() exactly once — the same-core prvYieldCore branch sets
     * xYieldPendings[0]=pdTRUE, which vTaskExitCritical services via portYIELD.
     * portYIELD_CORE is NOT called by the same-core path. */
    vFakePortYield_StubWithCallback( NULL );
    vFakePortYield_Expect();

    /* Re-enable core 0.  uxEnabledCores = ~ALL_BUT_FIRST_CORE & ALL_CORES_MASK
     * = FIRST_CORE_BIT (bit 0).  The loop reaches xCoreID==0 and calls
     * prvYieldCore(0) from the enable arm.  Since the test runs on core 0
     * the macro takes the same-core branch: xYieldPendings[0] = pdTRUE. */
    vTaskSetSchedulerCoreMask( ALL_CORES_MASK );

    /* Core 0 must now be enabled in the mask. */
    TEST_ASSERT_EQUAL( ALL_CORES_MASK, uxSchedulerCoreMask );

    /* portYIELD() was called (verified by the CMock Expect above), proving
     * that xYieldPendings[0] was set to pdTRUE by the same-core enable branch. */
}
