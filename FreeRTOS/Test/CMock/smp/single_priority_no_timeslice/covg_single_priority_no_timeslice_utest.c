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
/*! @file single_priority_no_timeslice_covg_utest */

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

#define MAX_TASKS    3

/* ===========================  EXTERN FUNCTIONS  =========================== */
extern void prvCheckForRunStateChange( void );

/* ===========================  EXTERN VARIABLES  =========================== */
extern volatile UBaseType_t uxDeletedTasksWaitingCleanUp;
extern volatile UBaseType_t uxSchedulerSuspended;
extern volatile TCB_t * pxCurrentTCBs[ configNUMBER_OF_CORES ];
extern List_t xSuspendedTaskList;
extern List_t xPendingReadyList;
extern volatile UBaseType_t uxTopReadyPriority;
extern volatile BaseType_t xYieldPendings[ configNUMBER_OF_CORES ];
extern volatile TickType_t xNextTaskUnblockTime;
extern volatile TickType_t xTickCount;
extern TickType_t xPendedTicks;

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

/* ==============================  Helper functions for Test Cases  ============================== */
void created_task( void * arg )
{
    while( 1 )
    {
        vTaskDelay( 100 );
    }
}

static void prvPortEnableInterruptsCb( int cmock_num_calls )
{
    ( void ) cmock_num_calls;

    pxCurrentTCBs[ 0 ]->xTaskRunState = 0;
}

/* ==============================  Test Cases  ============================== */

/**
 * @brief prvCheckForRunStateChange - first time enter critical section.
 *
 * Check for run state when entering the critical section for the first time. Verify
 * that the task is of running state when exiting this function.
 *
 * <b>Coverage</b>
 * @code{c}
 * if( uxPrevCriticalNesting == 0U )
 * {
 *     configASSERT( uxPrevSchedulerSuspended != ( UBaseType_t ) pdFALSE );
 *     portRELEASE_ISR_LOCK();
 * }
 * @endcode
 * ( uxPrevCriticalNesting == 0U ) is false.
 */
void test_coverage_prvCheckForRunStateChange_first_time_critical_section( void )
{
    TCB_t xTaskTCB = { NULL };

    pxCurrentTCBs[ 0 ] = &xTaskTCB;
    xTaskTCB.uxCriticalNesting = 1;
    xTaskTCB.xTaskRunState = taskTASK_YIELDING;
    uxSchedulerSuspended = 0;

    /* Clear callback in commonSetUp. */
    vFakePortCheckIfInISR_StopIgnore();
    vFakePortEnableInterrupts_StopIgnore();
    vFakePortGetISRLock_StubWithCallback( NULL );
    vFakePortGetTaskLock_StubWithCallback( NULL );
    vFakePortReleaseISRLock_StubWithCallback( NULL );
    vFakePortReleaseTaskLock_StubWithCallback( NULL );

    /* Expection. */
    vFakePortEnableInterrupts_StubWithCallback( prvPortEnableInterruptsCb );

    vFakePortReleaseISRLock_Expect();
    vFakePortReleaseTaskLock_Expect();
    vFakePortGetTaskLock_Expect();
    vFakePortGetISRLock_Expect();

    /* API Call. */
    prvCheckForRunStateChange();

    /* Validation. */
    /* Critical nesting count is set correctly. */
    TEST_ASSERT_EQUAL( 1, xTaskTCB.uxCriticalNesting );
    /* Task is of running state now. */
    TEST_ASSERT_EQUAL( 0, xTaskTCB.xTaskRunState );
}

/**
 * @brief prvCheckForRunStateChange - first time suspend scheduler.
 *
 * Check for run state when suspending the scheduler for the first time. Verify
 * that the task is of running state when exiting this function.
 *
 * <b>Coverage</b>
 * @code{c}
 * if( uxPrevCriticalNesting == 0U )
 * {
 *     configASSERT( uxPrevSchedulerSuspended != ( UBaseType_t ) pdFALSE );
 *     portRELEASE_ISR_LOCK();
 * }
 * @endcode
 * ( uxPrevCriticalNesting == 0U ) is true.
 */
void test_coverage_prvCheckForRunStateChange_first_time_suspend_scheduler( void )
{
    TCB_t xTaskTCB = { NULL };

    pxCurrentTCBs[ 0 ] = &xTaskTCB;
    xTaskTCB.uxCriticalNesting = 0;
    xTaskTCB.xTaskRunState = taskTASK_YIELDING;
    uxSchedulerSuspended = 0;

    /* Clear callback in commonSetUp. */
    vFakePortCheckIfInISR_StopIgnore();
    vFakePortEnableInterrupts_StopIgnore();
    vFakePortGetTaskLock_StubWithCallback( NULL );
    vFakePortReleaseTaskLock_StubWithCallback( NULL );

    /* Expection. */
    vFakePortEnableInterrupts_StubWithCallback( prvPortEnableInterruptsCb );

    vFakePortReleaseTaskLock_Expect();
    vFakePortGetTaskLock_Expect();
    vFakePortGetISRLock_Expect();
    vFakePortReleaseISRLock_Expect();

    /* API Call. */
    prvCheckForRunStateChange();

    /* Validation. */
    /* Critical nesting count is set correctly. */
    TEST_ASSERT_EQUAL( 0, uxSchedulerSuspended );
    /* Task is of running state now. */
    TEST_ASSERT_EQUAL( 0, xTaskTCB.xTaskRunState );
}

/*
 * The kernel will be configured as follows:
 #define configNUMBER_OF_CORES                               (N > 1)
 #define configUSE_CORE_AFFINITY                          1
 * Coverage for
 *  static TickType_t prvGetExpectedIdleTime( void )
 */

/*
 * Coverage for: UBaseType_t uxTaskGetSystemState( TaskStatus_t * const pxTaskStatusArray,
 *                                              const UBaseType_t uxArraySize,
 *                                              configRUN_TIME_COUNTER_TYPE * const pulTotalRunTime )
 */
void test_task_get_system_state( void )
{
    TaskStatus_t * tsk_status_array;
    TaskHandle_t created_handles[ 3 ];

    tsk_status_array = calloc( MAX_TASKS, sizeof( TaskStatus_t ) );

    for( int i = 0; i < 3; i++ )
    {
        xTaskCreate( created_task, "Created Task", configMINIMAL_STACK_SIZE, NULL, 1, &created_handles[ i ] );
    }

    /*Get System states */
    int no_of_tasks = uxTaskGetSystemState( tsk_status_array, MAX_TASKS, NULL );
    TEST_ASSERT( ( no_of_tasks > 0 ) && ( no_of_tasks <= MAX_TASKS ) );
}

/*
 * Coverage for: UBaseType_t uxTaskGetSystemState( TaskStatus_t * const pxTaskStatusArray,
 *                                              const UBaseType_t uxArraySize,
 *                                              configRUN_TIME_COUNTER_TYPE * const pulTotalRunTime )
 */
void test_task_get_system_state_custom_time( void )
{
    TaskStatus_t * tsk_status_array;
    TaskHandle_t created_handles[ 3 ];
    uint32_t ulTotalRunTime = ( uint32_t ) 200; /* Custom time value */

    tsk_status_array = calloc( MAX_TASKS, sizeof( TaskStatus_t ) );

    for( int i = 0; i < 3; i++ )
    {
        xTaskCreate( created_task, "Created Task", configMINIMAL_STACK_SIZE, NULL, 1, &created_handles[ i ] );
    }

    /*Get System states */
    int no_of_tasks = uxTaskGetSystemState( tsk_status_array, MAX_TASKS, &ulTotalRunTime );
    TEST_ASSERT( ( no_of_tasks > 0 ) && ( no_of_tasks <= MAX_TASKS ) );
}

/*
 * Coverage for: UBaseType_t uxTaskGetSystemState( TaskStatus_t * const pxTaskStatusArray,
 *                                              const UBaseType_t uxArraySize,
 *                                              configRUN_TIME_COUNTER_TYPE * const pulTotalRunTime )
 */
void test_task_get_system_state_unavilable_task_space( void )
{
    TaskStatus_t * tsk_status_array;
    TaskHandle_t created_handles[ 3 ];

    tsk_status_array = calloc( MAX_TASKS, sizeof( TaskStatus_t ) );

    for( int i = 0; i < 3; i++ )
    {
        xTaskCreate( created_task, "Created Task", configMINIMAL_STACK_SIZE, NULL, 1, &created_handles[ i ] );
    }

    /*Get System states */
    int no_of_tasks = uxTaskGetSystemState( tsk_status_array, MAX_TASKS - 1, NULL );
    TEST_ASSERT( ( no_of_tasks == 0 ) && ( no_of_tasks <= MAX_TASKS ) );
}

/**
 * @brief vTaskStepTick - step ticks to next task unblock time.
 *
 * Step ticks to next task unblock time to increase xPendedTicks. Verify that xTickCount
 * and xPendedTicks are increased accordingly.
 *
 * <b>Coverage</b>
 * @code{c}
 * if( ( xTickCount + xTicksToJump ) == xNextTaskUnblockTime )
 * {
 *     ...
 *     taskENTER_CRITICAL();
 *     {
 *         xPendedTicks++;
 *     }
 *     taskEXIT_CRITICAL();
 *     xTicksToJump--;
 * }
 * @endcode
 * ( ( xTickCount + xTicksToJump ) == xNextTaskUnblockTime ) is true.
 */
void test_coverage_vTaskStepTick_eq_task_unblock_time( void )
{
    TickType_t xTicksToJump;

    /* Setup the variables and structure. */
    xPendedTicks = 0;
    xTickCount = 10;
    xTicksToJump = 10;
    uxSchedulerSuspended = pdTRUE;

    xNextTaskUnblockTime = 20;

    /* Clear callback in commonSetUp. */
    vFakePortEnterCriticalSection_StubWithCallback( NULL );
    vFakePortExitCriticalSection_StubWithCallback( NULL );

    /* Expections. */
    vFakePortEnterCriticalSection_Expect();
    vFakePortExitCriticalSection_Expect();

    /* API call. */
    vTaskStepTick( xTicksToJump );

    /* Validations. */
    /* xTickCount is set to one tick before xNextUnblockTime. */
    TEST_ASSERT_EQUAL( 19, xTickCount );
    /* xPendedTicks is increased. */
    TEST_ASSERT_EQUAL( 1, xPendedTicks );
}

/**
 * @brief xTaskResumeFromISR - resume higher priority suspended task
 *
 * This test resume a higher priority task from ISR when scheduler suspended. The
 * return value of xTaskResumeFromISR indicates yield required for the core calling
 * this API.
 *
 * <b>Coverage</b>
 * @code{c}
 * #if ( ( configNUMBER_OF_CORES > 1 ) && ( configUSE_PREEMPTION == 1 ) )
 * {
 *     prvYieldForTask( pxTCB );
 *
 *     if( xYieldPendings[ portGET_CORE_ID() ] != pdFALSE )
 *     {
 *         xYieldRequired = pdTRUE;
 *     }
 * }
 * #endif
 * @endcode
 * ( xYieldPendings[ portGET_CORE_ID() ] != pdFALSE ) is true.
 */
void test_coverage_xTaskResumeFromISR_resume_higher_priority_suspended_task( void )
{
    TCB_t xTaskTCBs[ configNUMBER_OF_CORES + 1U ] = { NULL };
    uint32_t i;
    BaseType_t xReturn;

    /* Setup the variables and structure. */
    vListInitialise( &xSuspendedTaskList );
    vListInitialise( &xPendingReadyList );

    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        xTaskTCBs[ i ].uxPriority = 1;
        xTaskTCBs[ i ].xTaskRunState = i;
        xYieldPendings[ i ] = pdFALSE;
        pxCurrentTCBs[ i ] = &xTaskTCBs[ i ];
    }

    /* A suspended task is created to be resumed from ISR. The task has higher priority
     * than uxTopReadyPriority and the scheduler is suspended. The task will be added
     * to xPendingReadyList after resumed from ISR. */
    xTaskTCBs[ configNUMBER_OF_CORES ].uxPriority = 2;
    listINSERT_END( &xSuspendedTaskList, &xTaskTCBs[ i ].xStateListItem );
    uxTopReadyPriority = 1;
    uxSchedulerSuspended = pdTRUE;

    /* Expections. */
    vFakePortAssertIfInterruptPriorityInvalid_Ignore();

    /* API calls. */
    xReturn = xTaskResumeFromISR( &xTaskTCBs[ i ] );

    /* Validations. In single priority test, the calling core is requested to yield
     * since a higher priority task is resumed. */
    TEST_ASSERT( xReturn == pdTRUE );
}

/**
 * @brief xTaskResumeFromISR - resume lower priority suspended task
 *
 * This test resume a lower priority task from ISR when scheduler suspended. The
 * return value of xTaskResumeFromISR indicates yield not required for the core
 * calling this API.
 *
 * <b>Coverage</b>
 * @code{c}
 * #if ( ( configNUMBER_OF_CORES > 1 ) && ( configUSE_PREEMPTION == 1 ) )
 * {
 *     prvYieldForTask( pxTCB );
 *
 *     if( xYieldPendings[ portGET_CORE_ID() ] != pdFALSE )
 *     {
 *         xYieldRequired = pdTRUE;
 *     }
 * }
 * #endif
 * @endcode
 * ( xYieldPendings[ portGET_CORE_ID() ] != pdFALSE ) is false.
 */
void test_coverage_xTaskResumeFromISR_resume_lower_priority_suspended_task( void )
{
    TCB_t xTaskTCBs[ configNUMBER_OF_CORES + 1U ] = { NULL };
    uint32_t i;
    BaseType_t xReturn;

    /* Setup the variables and structure. */
    vListInitialise( &xSuspendedTaskList );
    vListInitialise( &xPendingReadyList );

    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        xTaskTCBs[ i ].uxPriority = 2;
        xTaskTCBs[ i ].xTaskRunState = i;
        xYieldPendings[ i ] = pdFALSE;
        pxCurrentTCBs[ i ] = &xTaskTCBs[ i ];
    }

    /* A suspended task is created to be resumed from ISR. The task has lower priority
     * than uxTopReadyPriority and the scheduler is suspended. The task will be added
     * to xPendingReadyList after resumed from ISR. */
    xTaskTCBs[ configNUMBER_OF_CORES ].uxPriority = 1;
    listINSERT_END( &xSuspendedTaskList, &xTaskTCBs[ i ].xStateListItem );
    uxTopReadyPriority = 2;
    uxSchedulerSuspended = pdTRUE;

    /* Expections. */
    vFakePortAssertIfInterruptPriorityInvalid_Ignore();

    /* API calls. */
    xReturn = xTaskResumeFromISR( &xTaskTCBs[ i ] );

    /* Validations. In single priority test, the calling core is not requested to yield
     * since a lower priority task is resumed. */
    TEST_ASSERT( xReturn == pdFALSE );
}
