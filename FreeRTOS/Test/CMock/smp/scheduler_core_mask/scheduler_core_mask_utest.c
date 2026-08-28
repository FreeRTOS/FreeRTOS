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
/*! @file scheduler_core_mask_utest.c */

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
#define ALL_CORES_MASK       ( ( UBaseType_t ) ( ( 1U << configNUMBER_OF_CORES ) - 1U ) )

/* Highest valid core index. */
#define LAST_CORE            ( ( BaseType_t ) ( configNUMBER_OF_CORES - 1 ) )

/* Bit mask for the last core. */
#define LAST_CORE_BIT        ( ( UBaseType_t ) 1U << ( UBaseType_t ) LAST_CORE )

/* All cores enabled except the last. */
#define ALL_BUT_LAST_CORE    ( ALL_CORES_MASK ^ LAST_CORE_BIT )

/* ===========================  EXTERN VARIABLES  =========================== */

extern volatile UBaseType_t uxSchedulerCoreMask;
extern volatile BaseType_t xSchedulerRunning;
extern volatile TCB_t * pxCurrentTCBs[ configNUMBER_OF_CORES ];
extern volatile BaseType_t xYieldPendings[ configNUMBER_OF_CORES ];
extern TaskHandle_t xIdleTaskHandles[ configNUMBER_OF_CORES ];

/* ============================  Unity Fixtures  ============================ */
/*! called before each testcase */
void setUp( void )
{
    commonSetUp();

    /* Reset the scheduler core mask to all-enabled so every test starts from
     * a known state.  This mirrors what vTaskSetSchedulerCoreMask computes
     * for the initial value of uxSchedulerCoreMask in tasks.c. */
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

/* ==============================  Test Cases  ============================== */

/**
 * @brief Set mask before the scheduler starts.
 *
 * vTaskSetSchedulerCoreMask is called while xSchedulerRunning == pdFALSE.
 * The mask is updated but the inner yield loop (tasks.c:3163) must be skipped.
 * uxTaskGetSchedulerCoreMask must return the written value.
 */
void test_vTaskSetSchedulerCoreMask_BeforeSchedulerStart( void )
{
    UBaseType_t uxReadBack;

    /* Scheduler is not running — commonSetUp sets xSchedulerRunning = pdFALSE. */
    TEST_ASSERT_EQUAL( pdFALSE, xSchedulerRunning );

    /* Disable the last core before the scheduler starts. */
    vTaskSetSchedulerCoreMask( ALL_BUT_LAST_CORE );

    /* The mask must be stored. */
    TEST_ASSERT_EQUAL( ALL_BUT_LAST_CORE, uxSchedulerCoreMask );

    /* The getter must return the same value. */
    uxReadBack = uxTaskGetSchedulerCoreMask();
    TEST_ASSERT_EQUAL( ALL_BUT_LAST_CORE, uxReadBack );
}

/**
 * @brief Round-trip: vTaskSetSchedulerCoreMask then uxTaskGetSchedulerCoreMask.
 *
 * Exercises the full body of uxTaskGetSchedulerCoreMask (tasks.c:3206-3222).
 * After writing a mask before the scheduler starts the getter must echo it
 * exactly.
 */
void test_uxTaskGetSchedulerCoreMask_RoundTrip( void )
{
    UBaseType_t uxWritten;
    UBaseType_t uxRead;

    /* Use a non-trivial mask: only core 0 enabled. */
    uxWritten = ( UBaseType_t ) 1U;

    vTaskSetSchedulerCoreMask( uxWritten );

    uxRead = uxTaskGetSchedulerCoreMask();
    TEST_ASSERT_EQUAL( uxWritten, uxRead );
}

/**
 * @brief Disable a core that is running a non-idle task.
 *
 * After the scheduler starts with configNUMBER_OF_CORES user tasks, all cores
 * run non-idle tasks.  Disabling LAST_CORE must trigger prvYieldCore for that
 * core so the scheduler picks the idle task.  After the context switch the
 * idle task (index 0 — see knowledge file §5) runs on LAST_CORE.
 */
void test_vTaskSetSchedulerCoreMask_DisableCore_NonIdleTask( void )
{
    TaskHandle_t xTaskHandles[ configNUMBER_OF_CORES ] = { NULL };
    BaseType_t i;

    /* Create one user task per core so all cores run non-idle after start. */
    for( i = 0; i < ( BaseType_t ) configNUMBER_OF_CORES; i++ )
    {
        xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 1, &xTaskHandles[ i ] );
    }

    vTaskStartScheduler();

    /* All cores should be running user tasks. */
    for( i = 0; i < ( BaseType_t ) configNUMBER_OF_CORES; i++ )
    {
        verifySmpTask( &xTaskHandles[ i ], eRunning, ( TaskRunning_t ) i );
    }

    /* Disable LAST_CORE — it is currently running a non-idle task, so
     * prvYieldCore must be called and the scheduler context-switches to idle. */
    vTaskSetSchedulerCoreMask( ALL_BUT_LAST_CORE );

    /* LAST_CORE_BIT must be clear in the stored mask. */
    TEST_ASSERT_EQUAL( ALL_BUT_LAST_CORE, uxSchedulerCoreMask );

    /* After the yield LAST_CORE runs the idle task (index 0 per knowledge §5). */
    verifyIdleTask( 0, ( TaskRunning_t ) LAST_CORE );
}

/**
 * @brief Disable a core that is already running an idle task.
 *
 * With one user task and configNUMBER_OF_CORES cores, the remaining cores run
 * idle tasks.  Disabling one of those idle cores must NOT call prvYieldCore
 * (the false arm of tasks.c:3181) because the core is already idle.
 */
void test_vTaskSetSchedulerCoreMask_DisableCore_IdleTask( void )
{
    TaskHandle_t xTaskHandle = NULL;

    /* Create a single user task — it occupies core 0; LAST_CORE runs idle. */
    xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 1, &xTaskHandle );

    vTaskStartScheduler();

    /* Core 0 runs the user task. */
    verifySmpTask( &xTaskHandle, eRunning, ( TaskRunning_t ) 0 );

    /* LAST_CORE already runs an idle task — capture its current TCB pointer. */
    volatile TCB_t * pxIdleTCB = pxCurrentTCBs[ LAST_CORE ];
    TEST_ASSERT_NOT_NULL( pxIdleTCB );
    TEST_ASSERT_NOT_EQUAL( 0U, pxIdleTCB->uxTaskAttributes & taskATTRIBUTE_IS_IDLE );

    /* Disable LAST_CORE — no yield should be triggered for an idle core. */
    vTaskSetSchedulerCoreMask( ALL_BUT_LAST_CORE );

    /* The mask must reflect the disabled core. */
    TEST_ASSERT_EQUAL( ALL_BUT_LAST_CORE, uxSchedulerCoreMask );

    /* LAST_CORE still runs the same idle TCB — no context switch happened. */
    TEST_ASSERT_EQUAL_PTR( pxIdleTCB, pxCurrentTCBs[ LAST_CORE ] );
}

/**
 * @brief Enable a previously-disabled core.
 *
 * Disable LAST_CORE before the scheduler starts, start the scheduler with two
 * user tasks, then re-enable LAST_CORE via vTaskSetSchedulerCoreMask.  The
 * function must call prvYieldCore on LAST_CORE (tasks.c:3186-3188) so the
 * scheduler promptly dispatches the second user task there.
 *
 * With LAST_CORE disabled, only core 0 runs a user task; LAST_CORE idles.
 * After re-enabling, the context switch triggered by prvYieldCore causes
 * LAST_CORE to pick up the second user task — verifying the enable path fired.
 */
void test_vTaskSetSchedulerCoreMask_EnableCore( void )
{
    TaskHandle_t xTaskHandles[ configNUMBER_OF_CORES ] = { NULL };
    BaseType_t i;

    /* Disable LAST_CORE before the scheduler starts. */
    vTaskSetSchedulerCoreMask( ALL_BUT_LAST_CORE );
    TEST_ASSERT_EQUAL( ALL_BUT_LAST_CORE, uxSchedulerCoreMask );

    /* Create one user task per core so there are tasks waiting for each core.
     * With LAST_CORE disabled, only core 0 picks up a user task at startup;
     * the second user task sits in the ready list until LAST_CORE is enabled. */
    for( i = 0; i < ( BaseType_t ) configNUMBER_OF_CORES; i++ )
    {
        xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 1, &xTaskHandles[ i ] );
    }

    vTaskStartScheduler();

    /* LAST_CORE must be running an idle task while it is disabled — at least
     * one core must be idling (the disabled one). */
    TEST_ASSERT_NOT_EQUAL( 0U, pxCurrentTCBs[ LAST_CORE ]->uxTaskAttributes & taskATTRIBUTE_IS_IDLE );

    /* Re-enable LAST_CORE.  prvYieldCore must be called for LAST_CORE
     * (tasks.c:3188) which triggers a context switch on that core. */
    vTaskSetSchedulerCoreMask( ALL_CORES_MASK );

    /* All cores must be enabled again. */
    TEST_ASSERT_EQUAL( ALL_CORES_MASK, uxSchedulerCoreMask );

    /* After the context switch triggered by prvYieldCore, LAST_CORE must now
    * run a user task — confirming that the enable path (line 3186-3188) fired
    * and the scheduler dispatched a ready task to the newly-enabled core. */
    TEST_ASSERT_EQUAL( 0U, pxCurrentTCBs[ LAST_CORE ]->uxTaskAttributes & taskATTRIBUTE_IS_IDLE );
}

/**
 * @brief Unchanged core hits the else branch (mtCOVERAGE_TEST_MARKER).
 *
 * When vTaskSetSchedulerCoreMask is called with the same mask that is already
 * active, no core transitions from disabled to enabled or vice versa.  The
 * else branch (tasks.c:3190-3193) must execute for every core — which is only
 * observable by the absence of spurious yields.
 */
void test_vTaskSetSchedulerCoreMask_UnchangedCore( void )
{
    TaskHandle_t xTaskHandles[ configNUMBER_OF_CORES ] = { NULL };
    BaseType_t i;

    for( i = 0; i < ( BaseType_t ) configNUMBER_OF_CORES; i++ )
    {
        xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 1, &xTaskHandles[ i ] );
    }

    vTaskStartScheduler();

    /* Apply the exact same mask that is already in effect (all cores enabled). */
    vTaskSetSchedulerCoreMask( ALL_CORES_MASK );

    /* Mask unchanged. */
    TEST_ASSERT_EQUAL( ALL_CORES_MASK, uxSchedulerCoreMask );

    /* Every core still runs a user task — no unexpected yields happened. */
    for( i = 0; i < ( BaseType_t ) configNUMBER_OF_CORES; i++ )
    {
        verifySmpTask( &xTaskHandles[ i ], eRunning, ( TaskRunning_t ) i );
    }
}
