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
/*! @file covg_multiple_priorities_no_timeslice_utest.c */

/* C runtime includes. */
#include <stdlib.h>
#include <stdbool.h>
#include <stdint.h>
#include <string.h>

/* Tasks includes */
#include "FreeRTOS.h"
#include "FreeRTOSConfig.h"
#include "event_groups.h"
#include "queue.h"

/* Test includes. */
#include "unity.h"
#include "unity_memory.h"
#include "CException.h"
#include "../global_vars.h"
#include "../smp_utest_common.h"
#include <assert.h>

/* Mock includes. */
#include "mock_timers.h"
#include "mock_list.h"
#include "mock_list_macros.h"
#include "mock_fake_assert.h"
#include "mock_fake_port.h"
#include "mock_local_portable.h"

/* =================================  MACROS  =============================== */

/**
 * @brief CException code for when a configASSERT should be intercepted.
 */
#define configASSERT_E    0xAA101
#define EXIT_LOOP         0xAA102

/**
 * @brief Expect a configASSERT from the function called.
 *  Break out of the called function when this occurs.
 * @details Use this macro when the call passed in as a parameter is expected
 * to cause invalid memory access.
 */
#define EXPECT_ASSERT_BREAK( call )                 \
    do                                              \
    {                                               \
        shouldAbortOnAssertion = true;              \
        CEXCEPTION_T e = CEXCEPTION_NONE;           \
        Try                                         \
        {                                           \
            call;                                   \
            TEST_FAIL();                            \
        }                                           \
        Catch( e )                                  \
        {                                           \
            TEST_ASSERT_EQUAL( configASSERT_E, e ); \
        }                                           \
    } while( 0 )

/* ============================  GLOBAL VARIABLES =========================== */

/**
 * @brief Global idle task name pointer.
 */
const char * pcIdleTaskName = "IDLE";

/**
 * @brief Global counter for the number of assertions in code.
 */
static int assertionFailed = 1;

/**
 * @brief Flag which denotes if test need to abort on assertion.
 */
static BaseType_t shouldAbortOnAssertion;

/* ===========================  EXTERN VARIABLES  =========================== */

extern volatile UBaseType_t uxDeletedTasksWaitingCleanUp;
extern volatile UBaseType_t xSchedulerRunning;
extern volatile BaseType_t xYieldPendings[ configNUMBER_OF_CORES ];
extern volatile TCB_t * pxCurrentTCBs[ configNUMBER_OF_CORES ];
extern TaskHandle_t xIdleTaskHandles[ configNUMBER_OF_CORES ];
extern volatile BaseType_t xYieldForTask;
extern volatile BaseType_t xYieldRequired;
extern volatile UBaseType_t uxCurrentNumberOfTasks;
extern volatile UBaseType_t uxSchedulerSuspended;
extern volatile UBaseType_t uxTopReadyPriority;
extern List_t pxReadyTasksLists[ configMAX_PRIORITIES ];
extern UBaseType_t uxTaskNumber;
extern volatile TickType_t xTickCount;
extern volatile TickType_t xNextTaskUnblockTime;

/* ===========================  EXTERN FUNCTIONS  =========================== */

extern BaseType_t prvCreateIdleTasks( void );

/* ==========================  STATIC FUNCTIONS  ========================== */

void vApplicationMinimalIdleHook( void )
{
}

static void vFakeAssertStub( bool x,
                             char * file,
                             int line,
                             int cmock_num_calls )
{
    if( !x )
    {
        assertionFailed++;

        if( shouldAbortOnAssertion == pdTRUE )
        {
            Throw( configASSERT_E );
        }
    }
}

/* ============================  Unity Fixtures  ============================ */
/*! called before each testcase */
void setUp( void )
{
    /* Reset the idle task name to default value. */
    pcIdleTaskName = "IDLE";

    vFakeAssert_StubWithCallback( vFakeAssertStub );

    UnityMalloc_StartTest();
}

/*! called after each testcase */
void tearDown( void )
{
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


/* ==========================  HELPER FUNCTIONS  ========================== */

void * pvPortMalloc( size_t xSize )
{
    return unity_malloc( xSize );
}

void vPortFree( void * pv )
{
    return unity_free( pv );
}

/* ==============================  Test Cases  ============================== */

/**
 * @brief vTaskSuspend - suspends the running task
 *
 * This test is used to suspend a running task when task is actively
 * running and not scheduled to yield.
 *
 * <b>Coverage</b>
 * @code{c}
 * if( xSchedulerRunning != pdFALSE )
 * {
 *      if( xTaskRunningOnCore == portGET_CORE_ID() )
 *      {
 *          configASSERT( uxSchedulerSuspended == 0 );
 *          vTaskYieldWithinAPI();
 *      }
 *      else
 *      {
 *          prvYieldCore( xTaskRunningOnCore );
 *      }
 * }
 * else
 * {
 *      mtCOVERAGE_TEST_MARKER();
 * }
 * @endcode
 * ( xSchedulerRunning != pdFALSE ) is false.
 */
void test_coverage_vTaskSuspend_scheduler_running_false( void )
{
    TCB_t xTaskTCBs[ 1 ] = { NULL };

    /* Setup the variables and structure. */
    xTaskTCBs[ 0 ].uxPriority = 1;
    xYieldPendings[ 0 ] = pdFALSE;
    pxCurrentTCBs[ 0 ] = &xTaskTCBs[ 0 ];
    pxCurrentTCBs[ 0 ]->xTaskRunState = 1;
    xSchedulerRunning = pdFALSE;

    vFakePortEnterCriticalSection_Expect();
    uxListRemove_ExpectAnyArgsAndReturn( pdTRUE );
    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( NULL );
    vListInsertEnd_ExpectAnyArgs();
    vFakePortExitCriticalSection_Expect();

    /* API call. */
    vTaskSuspend( &xTaskTCBs[ 0 ] );

    /* Validation. */
    TEST_ASSERT_EQUAL( pdFALSE, xYieldPendings[ 0 ] );
    TEST_ASSERT_EQUAL( 1, pxCurrentTCBs[ 0 ]->xTaskRunState );
}

/**
 * @brief vTaskSuspend - suspends the task
 *
 * This test is used to ensure that one of the macro's conditions
 * where TaskRunState is greater than zero is set to false.
 *
 * <b>Coverage</b>
 * @code{c}
 * if( taskTASK_IS_RUNNING( pxTCB ) == pdTRUE )
 * @endcode
 * ( taskTASK_IS_RUNNING( pxTCB ) ) is false.
 */

void test_coverage_vTaskSuspend_running_state_below_range( void )
{
    TCB_t xTaskTCBs[ 1 ] = { NULL };

    /* Setup the variables and structure. */
    xTaskTCBs[ 0 ].uxPriority = 1;
    xYieldPendings[ 0 ] = pdFALSE;
    pxCurrentTCBs[ 0 ] = &xTaskTCBs[ 0 ];
    pxCurrentTCBs[ 0 ]->xTaskRunState = -1;
    xSchedulerRunning = pdFALSE;

    vFakePortEnterCriticalSection_Expect();
    uxListRemove_ExpectAnyArgsAndReturn( pdTRUE );
    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( NULL );
    vListInsertEnd_ExpectAnyArgs();
    vFakePortExitCriticalSection_Expect();

    /* API call. */
    vTaskSuspend( &xTaskTCBs[ 0 ] );

    /* Validation. */
    TEST_ASSERT_EQUAL( pdFALSE, xYieldPendings[ 0 ] );
    TEST_ASSERT_EQUAL( -1, pxCurrentTCBs[ 0 ]->xTaskRunState );
}

/**
 * @brief vTaskSuspend - suspends the task
 *
 * This test is used to cover the case where the other macro condition where
 * TaskRunState is less than configNUMBER_OF_CORES is set to false.
 *
 * <b>Coverage</b>
 * @code{c}
 * if( taskTASK_IS_RUNNING( pxTCB ) == pdTRUE )
 * @endcode
 * ( taskTASK_IS_RUNNING( pxTCB ) ) is false.
 */

void test_coverage_vTaskSuspend_running_state_above_range( void )
{
    TCB_t xTaskTCBs[ 1 ] = { NULL };

    /* Setup the variables and structure. */
    xTaskTCBs[ 0 ].uxPriority = 1;
    xYieldPendings[ 0 ] = pdFALSE;
    pxCurrentTCBs[ 0 ] = &xTaskTCBs[ 0 ];
    pxCurrentTCBs[ 0 ]->xTaskRunState = configNUMBER_OF_CORES + 1;

    vFakePortEnterCriticalSection_Expect();
    uxListRemove_ExpectAnyArgsAndReturn( pdTRUE );
    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( NULL );
    vListInsertEnd_ExpectAnyArgs();
    vFakePortExitCriticalSection_Expect();

    /* API call. */
    vTaskSuspend( &xTaskTCBs[ 0 ] );

    /* Validation. */
    TEST_ASSERT_EQUAL( pdFALSE, xYieldPendings[ 0 ] );
    TEST_ASSERT_EQUAL( 17, pxCurrentTCBs[ 0 ]->xTaskRunState );
}

/**
 * @brief vTaskPrioritySet - sets the priority
 *
 * This test is to change the priorities of non
 * running tasks
 *
 * <b>Coverage</b>
 * @code{c}
 * else if( taskTASK_IS_RUNNING( pxTCB ) == pdTRUE )
 * @endcode
 * ( taskTASK_IS_RUNNING( pxTCB ) ) is false.
 */
void test_coverage_vTaskPrioritySet_non_running_state( void )
{
    TCB_t xTaskTCBs[ 1 ] = { NULL };

    /* Setup the variables and structure. */
    xTaskTCBs[ 0 ].uxPriority = 4;
    xTaskTCBs[ 0 ].uxBasePriority = 4;
    xTaskTCBs[ 0 ].xTaskRunState = configNUMBER_OF_CORES + 1;

    vFakeAssert_Ignore();
    vFakePortCheckIfInISR_StopIgnore();
    vFakePortEnterCriticalSection_Ignore();
    vFakePortYieldCore_CMockIgnore();
    listGET_LIST_ITEM_VALUE_ExpectAnyArgsAndReturn( ( TickType_t ) 0x80000000UL );
    listIS_CONTAINED_WITHIN_ExpectAnyArgsAndReturn( pdFALSE );
    vFakePortExitCriticalSection_Ignore();

    /* API call. */
    vTaskPrioritySet( &xTaskTCBs[ 0 ], 2 );

    /* Validation. */
    TEST_ASSERT_EQUAL( 17, xTaskTCBs[ 0 ].xTaskRunState );
    TEST_ASSERT_EQUAL( 2, xTaskTCBs[ 0 ].uxPriority );
}

/**
 * @brief vTaskPrioritySet - sets the priority
 *
 * This test verifies that the current task is not
 * preempted by any other task of higher priority.
 *
 * <b>Coverage</b>
 * @code{c}
 * if( pxTCB->xPreemptionDisable == pdFALSE )
 * @endcode
 * ( pxTCB->xPreemptionDisable == pdFALSE ) is false.
 */
void test_coverage_vTaskPrioritySet_running_state( void )
{
    TCB_t xTaskTCBs[ 1 ] = { NULL };

    /* Setup the variables and structure. */
    xTaskTCBs[ 0 ].uxPriority = 4;
    xTaskTCBs[ 0 ].uxBasePriority = 4;
    xTaskTCBs[ 0 ].xPreemptionDisable = pdTRUE;
    xTaskTCBs[ 0 ].xTaskRunState = 1;

    BaseType_t xYieldRequired = pdFALSE;
    BaseType_t xYieldForTask = pdFALSE;

    vFakeAssert_Ignore();
    vFakePortCheckIfInISR_StopIgnore();
    vFakePortEnterCriticalSection_Ignore();
    vFakePortYieldCore_CMockIgnore();
    listGET_LIST_ITEM_VALUE_ExpectAnyArgsAndReturn( ( TickType_t ) 0x80000000UL );
    listIS_CONTAINED_WITHIN_ExpectAnyArgsAndReturn( pdFALSE );
    vFakePortExitCriticalSection_Ignore();

    /* API call. */
    vTaskPrioritySet( &xTaskTCBs[ 0 ], 2 );

    /* Validation. */
    TEST_ASSERT_EQUAL( pdFALSE, xYieldRequired );
    TEST_ASSERT_EQUAL( pdFALSE, xYieldForTask );
}

/**
 * @brief prvYieldCore - xCoreID is not equal to current core id.
 *
 * This test ensures that the  first condition is true while the second
 * condition is false in the if statement, so we will be performing the
 * action with portYIELD_CORE, and the task is put in the yielding state
 *
 * <b>Coverage</b>
 * @code{c}
 * if( ( portCHECK_IF_IN_ISR() == pdTRUE ) && ( xCoreID == portGET_CORE_ID() ) )
 * ...
 * @endcode
 * ( portCHECK_IF_IN_ISR() == pdTRUE ) is true.
 * ( xCoreID == portGET_CORE_ID() ) is false.
 */
void test_coverage_prvYieldCore_core_id_ne_current_coreid( void )
{
    TCB_t task;
    TCB_t task2;
    TaskHandle_t xTaskHandle;

    task.xTaskRunState = 1;   /* running on core 1 */
    task2.xTaskRunState = -2; /* running on core 2 taskTASK_YIELDING  */
    xTaskHandle = &task;
    pxCurrentTCBs[ 0 ] = &task;
    pxCurrentTCBs[ 1 ] = &task;
    pxCurrentTCBs[ 2 ] = &task2;
    xSchedulerRunning = pdTRUE;

    /* Test Expectations */
    vFakePortEnterCriticalSection_Expect();
    /* Entering prvYieldCore */
    vFakePortCheckIfInISR_ExpectAndReturn( pdTRUE );
    vFakePortGetCoreID_ExpectAndReturn( 2 );
    vFakePortGetCoreID_ExpectAndReturn( 2 );
    vFakePortYieldCore_Expect( 1 );
    /* Leaving prvYieldCore */
    vFakePortExitCriticalSection_Expect();

    /* API call */
    vTaskPreemptionEnable( xTaskHandle );

    /* Test Assertions */
    TEST_ASSERT_EQUAL( pdFALSE, xYieldPendings[ 2 ] );
    TEST_ASSERT_EQUAL( -2, pxCurrentTCBs[ 1 ]->xTaskRunState ); /* yielding state */
    TEST_ASSERT_EQUAL( -2, task.xTaskRunState );                /* yielding state */
}

/**
 * @brief prvYieldCore - task runstate equal to yielding.
 *
 * This test ensures that when the task is already in the yielding state,
 *        nothing is done
 *
 * <b>Coverage</b>
 * @code{c}
 * if( pxCurrentTCBs[ xCoreID ]->xTaskRunState != taskTASK_YIELDING )
 * @endcode
 * ( pxCurrentTCBs[ xCoreID ]->xTaskRunState != taskTASK_YIELDING ) is false.
 */
void test_coverage_prvYieldCore_runstate_eq_yielding( void )
{
    TCB_t task;
    TCB_t task2;
    TaskHandle_t xTaskHandle;

    task.xTaskRunState = 1;   /* running on core 1 */
    task2.xTaskRunState = -2; /* running on core 2 taskTASK_YIELDING  */
    xTaskHandle = &task;
    pxCurrentTCBs[ 0 ] = &task;
    pxCurrentTCBs[ 1 ] = &task2;
    pxCurrentTCBs[ 2 ] = &task2;
    xSchedulerRunning = pdTRUE;

    /* Test Expectations */
    vFakePortEnterCriticalSection_Expect();
    /* Entering prvYieldCore */
    vFakePortCheckIfInISR_ExpectAndReturn( pdTRUE );
    vFakePortGetCoreID_ExpectAndReturn( 2 );
    /* Leaving prvYieldCore */
    vFakePortExitCriticalSection_Expect();

    /* API call */
    vTaskPreemptionEnable( xTaskHandle );

    /* Test Assertions */
    TEST_ASSERT_EQUAL( pdFALSE, xYieldPendings[ 2 ] );
    TEST_ASSERT_EQUAL( -2, pxCurrentTCBs[ 1 ]->xTaskRunState ); /* yielding */
    TEST_ASSERT_EQUAL( 1, task.xTaskRunState );                 /* nothing has changed */
}

/**
 * @brief vTaskDelete - scheduler not running.
 *
 * This test ensures that if xTask Delete is caled and the scheuler is
 * not running, the core is not yielded, but it is removed from the
 * stateList, the eventList and inserted in the taskwaitingtermination
 * list, the uxdeletedtaskwaiting for cleanup is increased and the
 * uxtasknumber is increased
 *
 * <b>Coverage</b>
 * @code{c}
 * if( ( xSchedulerRunning != pdFALSE ) &&
 *     ( taskTASK_IS_RUNNING( pxTCB ) == pdTRUE ) )
 * ...
 * @endcode
 * ( xSchedulerRunning != pdFALSE ) is false.
 */
void test_coverage_vTaskDelete_scheduler_not_running( void )
{
    TCB_t task;
    TaskHandle_t xTaskToDelete;

    task.xTaskRunState = 1; /* running on core 1 */
    xTaskToDelete = &task;
    pxCurrentTCBs[ 0 ] = &task;

    xSchedulerRunning = pdFALSE;

    uxDeletedTasksWaitingCleanUp = 0;
    uxTaskNumber = 1;

    /* Test Expectations */
    vFakePortEnterCriticalSection_Expect();
    uxListRemove_ExpectAnyArgsAndReturn( 0 );
    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( NULL );

    /* if task != taskTaskNOT_RUNNING */
    vListInsertEnd_ExpectAnyArgs();
    vPortCurrentTaskDying_ExpectAnyArgs();

    vFakePortExitCriticalSection_Expect();


    /* API Call */
    vTaskDelete( xTaskToDelete );

    /* Test Verifications */
    TEST_ASSERT_EQUAL( 1, uxDeletedTasksWaitingCleanUp );
    TEST_ASSERT_EQUAL( 2, uxTaskNumber );
}

/**
 * @brief This test ensures that if xTask Delete is caled and the scheuler is
 *        running while the task runstate is more that the configNUMBER_OF_CORES,
 *        the core is not yielded, but it is removed from the
 *        stateList, the eventList and inserted in the taskwaitingtermination
 *        list, the uxdeletedtaskwaiting for cleanup is not changed
 *        uxtasknumber is increased
 *
 * <b>Coverage</b>
 * @code{c}
 * vTaskDelete( xTaskToDelete);
 *
 *   if( ( xSchedulerRunning != pdFALSE ) &&
 *               ( taskTASK_IS_RUNNING( pxTCB ) == pdTRUE ) )
 *
 * @endcode
 *
 * configNMBER_OF_CORES > 1
 * INCLUDE_vTaskDelete = 1
 */
void test_coverage_vTaskDelete_task_not_running( void )
{
    TCB_t task;
    TaskHandle_t xTaskToDelete;

    task.xTaskRunState = configNUMBER_OF_CORES + 2; /* running on core 1 */
    xTaskToDelete = &task;
    pxCurrentTCBs[ 0 ] = &task;

    xSchedulerRunning = pdTRUE;

    uxDeletedTasksWaitingCleanUp = 0;
    uxTaskNumber = 1;

    /* Test Expectations */
    vFakePortEnterCriticalSection_Expect();
    uxListRemove_ExpectAnyArgsAndReturn( 0 );
    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( NULL );

    /* if task != taskTaskNOT_RUNNING */
    vListInsertEnd_ExpectAnyArgs();
    vPortCurrentTaskDying_ExpectAnyArgs();

    vFakePortExitCriticalSection_Expect();

    /* API Call */
    vTaskDelete( xTaskToDelete );

    /* Test Verifications */
    TEST_ASSERT_EQUAL( 1, uxDeletedTasksWaitingCleanUp );
    TEST_ASSERT_EQUAL( 2, uxTaskNumber );
}

/**
 * @brief This test ensures that when we call eTaskGetState with a task that is
 *        not running eRady is returned
 *
 * <b>Coverage</b>
 * @code{c}
 * eTaskGetSate( xTask );
 *
 * if( taskTASK_IS_RUNNING( pxTCB ) == pdTRUE )
 *
 * @endcode
 *
 * configNMBER_OF_CORES > 1
 * INCLUDE_eTaskGetState = 1
 * configUSE_TRACE_FACILITY = 1
 * INCLUDE_xTaskAbortDelay = 1
 */
void test_coverage_eTaskGetState_task_not_running( void )
{
    TCB_t task = { 0 };
    TaskHandle_t xTask = &task;

    task.xTaskRunState = configNUMBER_OF_CORES + 2;
    List_t list = { 0 };
    eTaskState xRet;

    /* Test Expectations */
    vFakePortEnterCriticalSection_Expect();
    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( &list );
    vFakePortExitCriticalSection_Expect();

    /* API Call */
    xRet = eTaskGetState( xTask );

    /* Test Verifications */
    TEST_ASSERT_EQUAL( eReady, xRet );
}

/**
 * @brief This test ensures that when we call vTaskPreemtionDisable with a null
 *        handle, the pxCurrentTCBs of the running core is used
 *
 * <b>Coverage</b>
 * @code{c}
 * vTaskPreemptionEnable( xTask );
 *
 * pxTCB = prvGetTCBFromHandle( xTask );
 *
 * @endcode
 *
 * configNMBER_OF_CORES > 1
 * INCLUDE_eTaskGetState = 1
 * configUSE_TRACE_FACILITY = 1
 * INCLUDE_xTaskAbortDelay = 1
 * INCLUDE_xTaskGetCurrentTaskHandle = 1
 * configUSE_MUTEXES = 1
 */
void test_coverage_vTaskPreemptionDisable_null_handle( void )
{
    TCB_t xTask = { 0 };

    pxCurrentTCBs[ 0 ] = &xTask;

    /* Test Expectations */
    vFakePortEnterCriticalSection_Expect();
    ulFakePortSetInterruptMask_ExpectAndReturn( 0 );
    vFakePortGetCoreID_ExpectAndReturn( 0 );
    vFakePortClearInterruptMask_Expect( 0 );
    vFakePortExitCriticalSection_Expect();

    /* API Call */
    vTaskPreemptionDisable( NULL );

    /* Test Verifications */
    TEST_ASSERT_EQUAL( pdTRUE, pxCurrentTCBs[ 0 ]->xPreemptionDisable );
}

/**
 * @brief This test ensures that when we call vTaskSuspendAll and we task of the
 *        current core has a critical nesting count of 1 only the scheduler is
 *        suspended
 *
 * <b>Coverage</b>
 * @code{c}
 * vTaskSuspendAll();
 *
 * if( portGET_CRITICAL_NESTING_COUNT() == 0U )
 *
 * @endcode
 *
 * configNMBER_OF_CORES > 1
 */
void test_coverage_vTaskSuspendAll_critical_nesting_ne_zero( void )
{
    TCB_t xTask = { 0 };

    xTask.uxCriticalNesting = 1;
    pxCurrentTCBs[ 0 ] = &xTask;
    xSchedulerRunning = pdTRUE;
    uxSchedulerSuspended = 0U;

    /* Test Expectations */
    vFakePortAssertIfISR_Expect();
    ulFakePortSetInterruptMask_ExpectAndReturn( 0 );
    vFakePortGetTaskLock_Expect();
    vFakePortGetISRLock_Expect();
    vFakePortReleaseISRLock_Expect();
    vFakePortGetCoreID_ExpectAndReturn( 0 );
    vFakePortClearInterruptMask_Expect( 0 );

    /* API Call */
    vTaskSuspendAll();

    /* Test Verifications */
    TEST_ASSERT_EQUAL( 1, uxSchedulerSuspended );
}

/**
 * @brief This test ensures that when we call prvGetExpectedIdleTime and the top
 *        ready priority is greater than the idle task, we return zero,
 *        as a suggestion to sleep
 *
 * <b>Coverage</b>
 * @code{c}
 * prvGetExpectedIdleTime();
 *
 * if( uxTopReadyPriority > tskIDLE_PRIORITY )
 *
 * @endcode
 *
 * configNMBER_OF_CORES > 1
 * configUSE_TICKLESS_IDLE != 0
 * configUSE_PORT_OPTIMISED_TASK_SELECTION = 0
 */
void test_coverage_prvGetExpectedIdleTime_top_priority_gt_idle_prio( void )
{
    CEXCEPTION_T e = CEXCEPTION_NONE;
    TCB_t xTCB = { 0 };

    pxCurrentTCBs[ 0 ] = &xTCB;

    xTCB.uxPriority = tskIDLE_PRIORITY + 1;

    /* Test Setup */
    uxDeletedTasksWaitingCleanUp = 0;
    uxTopReadyPriority = tskIDLE_PRIORITY;

    /* Test Expectations */
    vFakePortYield_Expect();


    listCURRENT_LIST_LENGTH_ExpectAnyArgsAndReturn( configNUMBER_OF_CORES - 1 );


    ulFakePortSetInterruptMask_ExpectAndReturn( 0 );
    vFakePortGetCoreID_ExpectAndReturn( 0 );
    vFakePortClearInterruptMask_Expect( 0 );


    listCURRENT_LIST_LENGTH_ExpectAndThrow( &( pxReadyTasksLists[ tskIDLE_PRIORITY ] ),
                                            EXIT_LOOP );


    /* API Call */
    portTASK_FUNCTION( prvIdleTask, args );

    Try
    {
        prvIdleTask( NULL );
    }
    Catch( e )
    {
        if( e == EXIT_LOOP )
        {
            TEST_PASS();
        }
        else
        {
            TEST_FAIL();
        }
    }
    /* Test Verifications */

    /* this function (vPortSuppressTicksAndSleep_Expect) not being called is the aim of this test, it proves that the
     * task  did not go to sleep, technically nothing happens */
}

/**
 * @brief This test ensures that when we call prvGetExpectedIdleTime, and the
 *        ready tasks lists contains more than one element,
 *        then we return zero as a suggestion to sleep
 *
 * <b>Coverage</b>
 * @code{c}
 * prvGetExpectedIdleTime();
 *
 * else if( listCURRENT_LIST_LENGTH( &( pxReadyTasksLists[ tskIDLE_PRIORITY ] ) ) > 1 )
 *
 * @endcode
 *
 * configNMBER_OF_CORES > 1
 * configUSE_TICKLESS_IDLE != 0
 * configUSE_PORT_OPTIMISED_TASK_SELECTION = 0
 */
void test_coverage_prvGetExpectedIdleTime_ready_list_gt_one( void )
{
    CEXCEPTION_T e = CEXCEPTION_NONE;
    TCB_t xTCB = { 0 };

    pxCurrentTCBs[ 0 ] = &xTCB;
    xTCB.uxPriority = tskIDLE_PRIORITY;

    /* Test Setup */
    uxDeletedTasksWaitingCleanUp = 0;
    uxTopReadyPriority = tskIDLE_PRIORITY;

    /* Test Expectations */
    vFakePortYield_Expect();

    listCURRENT_LIST_LENGTH_ExpectAnyArgsAndReturn( configNUMBER_OF_CORES - 1 );

    ulFakePortSetInterruptMask_ExpectAndReturn( 0 );
    vFakePortGetCoreID_ExpectAndReturn( 0 );
    vFakePortClearInterruptMask_Expect( 0 );

    listCURRENT_LIST_LENGTH_ExpectAnyArgsAndReturn( configNUMBER_OF_CORES - 1 );

    listCURRENT_LIST_LENGTH_ExpectAndThrow( &( pxReadyTasksLists[ tskIDLE_PRIORITY ] ),
                                            EXIT_LOOP );

    /* API Call */
    portTASK_FUNCTION( prvIdleTask, args );

    Try
    {
        prvIdleTask( NULL );
    }
    Catch( e )
    {
        if( e == EXIT_LOOP )
        {
            TEST_PASS();
        }
        else
        {
            TEST_FAIL();
        }
    }
    /* Test Verifications */

    /* this function (vPortSuppressTicksAndSleep_Expect) not being called is the aim of this test, it proves that the
     * task  did not go to sleep, technically nothing happens */
}

/**
 * @brief This test ensures that when we call prvIdleTask and the ready tasks
 *        lists contains 1 elemets and  the top ready priority is less or equal
 *        to the idle priority, then we let the suggested time to sleep is
 *        returned
 *
 * <b>Coverage</b>
 * @code{c}
 * prvGetExpectedIdleTime();
 *
 * else if( listCURRENT_LIST_LENGTH( &( pxReadyTasksLists[ tskIDLE_PRIORITY ] ) ) > 1 )
 *
 * @endcode
 *
 * configNMBER_OF_CORES > 1
 * configUSE_TICKLESS_IDLE != 0
 * configUSE_PORT_OPTIMISED_TASK_SELECTION = 0
 */
void test_coverage_prvGetExpectedIdleTime_ready_list_eq_1( void )
{
    CEXCEPTION_T e = CEXCEPTION_NONE;
    TCB_t xTCB = { 0 };

    xTickCount = 230;
    xNextTaskUnblockTime = 240; /* expectedidletime = xNextTaskUnblockTime - xTickCount */
    pxCurrentTCBs[ 0 ] = &xTCB;
    xTCB.uxPriority = tskIDLE_PRIORITY;

    /* Test Setup */
    uxDeletedTasksWaitingCleanUp = 0;
    uxTopReadyPriority = tskIDLE_PRIORITY;

    /* Test Expectations */
    vFakePortYield_Expect();
    listCURRENT_LIST_LENGTH_ExpectAnyArgsAndReturn( 1 );

    ulFakePortSetInterruptMask_ExpectAndReturn( 0 );
    vFakePortGetCoreID_ExpectAndReturn( 0 );
    vFakePortClearInterruptMask_Expect( 0 );

    listCURRENT_LIST_LENGTH_ExpectAnyArgsAndReturn( 1 );

    /* vTaskSuspendAll */
    vFakePortAssertIfISR_Expect();
    ulFakePortSetInterruptMask_ExpectAndReturn( 0 );
    vFakePortGetTaskLock_Expect();
    vFakePortGetISRLock_Expect();
    vFakePortReleaseISRLock_Expect();
    vFakePortClearInterruptMask_Expect( 0 );


    ulFakePortSetInterruptMask_ExpectAndReturn( 0 );
    vFakePortGetCoreID_ExpectAndReturn( 0 );
    vFakePortClearInterruptMask_Expect( 0 );

    listCURRENT_LIST_LENGTH_ExpectAnyArgsAndReturn( 1 );

    /* Test Verifications */

    /* this function being called is the aim of this test, it proves that the
     * task went to sleep the specified amount of time. */
    vPortSuppressTicksAndSleep_Expect( xNextTaskUnblockTime - xTickCount );

    vFakePortEnterCriticalSection_Expect();
    vFakePortGetCoreID_ExpectAndReturn( 0 );
    vFakePortReleaseTaskLock_Expect();
    vFakePortExitCriticalSection_Expect();

    listCURRENT_LIST_LENGTH_ExpectAndThrow( &( pxReadyTasksLists[ tskIDLE_PRIORITY ] ),
                                            EXIT_LOOP );


    /* API Call */
    portTASK_FUNCTION( prvIdleTask, args );

    Try
    {
        prvIdleTask( NULL );
    }
    Catch( e )
    {
        if( e == EXIT_LOOP )
        {
            TEST_PASS();
        }
        else
        {
            TEST_FAIL();
        }
    }
    /* Test Verifications */
    /* the verification of the test is above in the expectations */
}

void port_assert_if_isr_cb( int num_callbacks )
{
    xTickCount = 239;
}

/**
 * @brief This test ensures that when we call prvIdleTask and the ready tasks
 *        lists contains 1 elemets and  the top ready priority is less or equal
 *        to the idle priority, then we let the suggested time to sleep is
 *        returned
 *
 * <b>Coverage</b>
 * @code{c}
 * prvGetExpectedIdleTime();
 *
 * else if( listCURRENT_LIST_LENGTH( &( pxReadyTasksLists[ tskIDLE_PRIORITY ] ) ) > 1 )
 *
 * @endcode
 *
 * configNMBER_OF_CORES > 1
 * configUSE_TICKLESS_IDLE != 0
 * configUSE_PORT_OPTIMISED_TASK_SELECTION = 0
 */
void test_coverage_prvGetExpectedIdleTime_ready_list_eq_2( void )
{
    CEXCEPTION_T e = CEXCEPTION_NONE;
    TCB_t xTCB = { 0 };

    xTickCount = 238;
    xNextTaskUnblockTime = 240; /* expectedidletime = xNextTaskUnblockTime - xTickCount */
    pxCurrentTCBs[ 0 ] = &xTCB;
    xTCB.uxPriority = tskIDLE_PRIORITY;

    /* Test Setup */
    uxDeletedTasksWaitingCleanUp = 0;
    uxTopReadyPriority = tskIDLE_PRIORITY;

    /* Test Expectations */
    vFakePortYield_Expect();
    listCURRENT_LIST_LENGTH_ExpectAnyArgsAndReturn( configNUMBER_OF_CORES + 1 );
    vFakePortYield_Expect();

    /* pxCurrentTCB */
    ulFakePortSetInterruptMask_ExpectAndReturn( 0 );
    vFakePortGetCoreID_ExpectAndReturn( 0 );
    vFakePortClearInterruptMask_Expect( 0 );

    listCURRENT_LIST_LENGTH_ExpectAnyArgsAndReturn( 0 );

    /* vTaskSuspendAll */
    vFakePortAssertIfISR_Stub( port_assert_if_isr_cb );
    ulFakePortSetInterruptMask_ExpectAndReturn( 0 );
    vFakePortGetTaskLock_Expect();
    vFakePortGetISRLock_Expect();
    vFakePortReleaseISRLock_Expect();
    vFakePortClearInterruptMask_Expect( 0 );


    ulFakePortSetInterruptMask_ExpectAndReturn( 0 );
    vFakePortGetCoreID_ExpectAndReturn( 0 );
    vFakePortClearInterruptMask_Expect( 0 );

    listCURRENT_LIST_LENGTH_ExpectAnyArgsAndReturn( 0 );

    vFakePortEnterCriticalSection_Expect();
    vFakePortGetCoreID_ExpectAndReturn( 0 );
    vFakePortReleaseTaskLock_Expect();
    vFakePortExitCriticalSection_Expect();

    listCURRENT_LIST_LENGTH_ExpectAndThrow( &( pxReadyTasksLists[ tskIDLE_PRIORITY ] ),
                                            EXIT_LOOP );

    /* API Call */
    portTASK_FUNCTION( prvIdleTask, args );

    Try
    {
        prvIdleTask( NULL );
    }
    Catch( e )
    {
        if( e == EXIT_LOOP )
        {
            TEST_PASS();
        }
        else
        {
            TEST_FAIL();
        }
    }
    /* Test Verifications */

    /* this function (vPortSuppressTicksAndSleep_Expect) not being called is
     * the aim of this test, it proves that the
     * task  did not go to sleep, technically nothing happens */
}

/**
 * @brief This test ensures that when we call prvGetExpectedIdleTime and the top
 *        ready priority is equal than the idle priority,  and the current task
 *        priority is less than or equal the idle priority nothing happens a
 *        zero is returned
 *
 * <b>Coverage</b>
 * @code{c}
 * prvGetExpectedIdleTime();
 *
 * if( uxTopReadyPriority > tskIDLE_PRIORITY )
 *
 * @endcode
 *
 * configNMBER_OF_CORES > 1
 * configUSE_TICKLESS_IDLE != 0
 * configUSE_PORT_OPTIMISED_TASK_SELECTION = 0
 */
void test_coverage_prvGetExpectedIdleTime_top_ready_prio_gt_idle_prio_current_prio_lt_idle( void )
{
    CEXCEPTION_T e = CEXCEPTION_NONE;
    TCB_t xTCB = { 0 };

    pxCurrentTCBs[ 0 ] = &xTCB;

    /* Test Setup */
    uxDeletedTasksWaitingCleanUp = 0;
    xTCB.uxPriority = tskIDLE_PRIORITY;
    uxTopReadyPriority = tskIDLE_PRIORITY + 1;

    /* Test Expectations */
    vFakePortYield_Expect();

    listCURRENT_LIST_LENGTH_ExpectAnyArgsAndReturn( 0 );

    ulFakePortSetInterruptMask_ExpectAndReturn( 0 );
    vFakePortGetCoreID_ExpectAndReturn( 0 );
    vFakePortClearInterruptMask_Expect( 0 );

    listCURRENT_LIST_LENGTH_ExpectAnyArgsAndReturn( 1 );
    listCURRENT_LIST_LENGTH_ExpectAndThrow( &( pxReadyTasksLists[ tskIDLE_PRIORITY ] ),
                                            EXIT_LOOP );


    /* API Call */
    portTASK_FUNCTION( prvIdleTask, args );

    Try
    {
        prvIdleTask( NULL );
    }
    Catch( e )
    {
        if( e == EXIT_LOOP )
        {
            TEST_PASS();
        }
        else
        {
            TEST_FAIL();
        }
    }
    /* Test Verifications */

    /* this function (vPortSuppressTicksAndSleep_Expect) not being called is
     * the aim of this test, it proves that the
     * task  did not go to sleep, technically nothing happens */
}

/**
 * @brief This test ensures that when we call prvCreateIdleTasks with and idle
 *        name that is just as long as configMAX_TASK_NAME_LEN
 *        no core id number is added at the end
 *
 * <b>Coverage</b>
 * @code{c}
 * prvCreateIdleTasks();
 *
 * if( x < configMAX_TASK_NAME_LEN )
 *
 * @endcode
 *
 * configNMBER_OF_CORES > 1
 */
void test_coverage_prvCreateIdleTasks_name_within_max_len( void )
{
    BaseType_t prvCreateIdleTasks( void );

    TCB_t * xIdleTask;
    TCB_t xTask = { 0 };
    int i;

    pcIdleTaskName = "IDLE longXX";

    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        pxCurrentTCBs[ i ] = &xTask;
    }

    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        /* prvInitialiseNewTask */
        vListInitialiseItem_ExpectAnyArgs();
        vListInitialiseItem_ExpectAnyArgs();
        listSET_LIST_ITEM_VALUE_ExpectAnyArgs();
        pxPortInitialiseStack_ExpectAnyArgsAndReturn( NULL );

        vFakePortEnterCriticalSection_Expect();
        listINSERT_END_ExpectAnyArgs();
        portSetupTCB_CB_ExpectAnyArgs();
        vFakePortGetCoreID_ExpectAndReturn( 0 );
        vFakePortExitCriticalSection_Expect();
    }

    /* API Call */
    prvCreateIdleTasks();

    /* Test Verifications */
    xIdleTask = ( TCB_t * ) xIdleTaskHandles[ 0 ];
    TEST_ASSERT_EQUAL_STRING( configIDLE_TASK_NAME, xIdleTask->pcTaskName );

    /* Clean up idle task. */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        vPortFreeStack( xIdleTaskHandles[ i ]->pxStack );
        vPortFree( xIdleTaskHandles[ i ] );
        xIdleTaskHandles[ i ] = NULL;
    }
}

/**
 * @brief This test ensures that when we call prvCreateIdleTasks with and idle
 *        name that is longer than  configMAX_TASK_NAME_LEN the name is
 *        truncated to configMAX_TASK_NAME_LEN
 *
 * <b>Coverage</b>
 * @code{c}
 * prvCreateIdleTasks();
 *
 * if( x < configMAX_TASK_NAME_LEN )
 *
 * @endcode
 *
 * configNMBER_OF_CORES > 1
 */
void test_coverage_prvCreateIdleTasks_name_too_long( void )
{
    BaseType_t prvCreateIdleTasks( void );

    TCB_t xTask = { 0 };
    TCB_t * xIdleTask;
    int i;

    pcIdleTaskName = "IDLE long name";

    uxCurrentNumberOfTasks = 2;

    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        pxCurrentTCBs[ i ] = &xTask;
    }

    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        /* prvInitialiseNewTask */
        vListInitialiseItem_ExpectAnyArgs();
        vListInitialiseItem_ExpectAnyArgs();
        listSET_LIST_ITEM_VALUE_ExpectAnyArgs();
        pxPortInitialiseStack_ExpectAnyArgsAndReturn( NULL );
        vFakePortEnterCriticalSection_Expect();
        listINSERT_END_ExpectAnyArgs();
        portSetupTCB_CB_ExpectAnyArgs();
        vFakePortGetCoreID_ExpectAndReturn( 0 );
        vFakePortExitCriticalSection_Expect();
    }

    prvCreateIdleTasks();

    xIdleTask = ( TCB_t * ) xIdleTaskHandles[ 0 ];

    /* Test Verifications */
    TEST_ASSERT_EQUAL_STRING_LEN( configIDLE_TASK_NAME,
                                  xIdleTask->pcTaskName,
                                  configMAX_TASK_NAME_LEN - 1 );

    /* Clean up idle task. */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        vPortFreeStack( xIdleTaskHandles[ i ]->pxStack );
        vPortFree( xIdleTaskHandles[ i ] );
        xIdleTaskHandles[ i ] = NULL;
    }
}


/**
 * @brief This test ensures that if the scheduler is not running, and the
 *        scheduler is suspended, taskSCHEDULER_SUSPENDED is returned
 *
 * <b>Coverage</b>
 * @code{c}
 * xTaskGetSchedulerState();
 *
 * taskENTER_CRITICAL();
 * taskEXIT_CRITICAL();
 *
 * @endcode
 *
 * configNMBER_OF_CORES > 1
 * INCLUDE_xTaskGetSchedulerState = 1
 * configUSE_TIMERS = 1
 */
void test_coverage_xTaskGetSchedulerState_scheduler_not_running_and_suspended( void )
{
    BaseType_t xRet;

    xSchedulerRunning = pdTRUE;
    uxSchedulerSuspended = pdTRUE;

    vFakePortEnterCriticalSection_Expect();
    vFakePortExitCriticalSection_Expect();

    xRet = xTaskGetSchedulerState();

    TEST_ASSERT_EQUAL( taskSCHEDULER_SUSPENDED, xRet );
}

/**
 * @brief This test ensures that if the notify is zero and the ticks to wait are
 *        greater than zero, the task is yielded
 *
 * <b>Coverage</b>
 * @code{c}
 *
 * vTaskYieldWithinAPI();
 *
 * @endcode
 *
 * configNMBER_OF_CORES > 1
 * configUSE_TASK_NOTIFICATIONS = 1
 */
void test_coverage_ulTaskGenericNotifyTake( void )
{
    uint32_t ulRet;
    TCB_t xTask = { 0 };
    const UBaseType_t uxIndexToWait = 1;

    xTask.ulNotifiedValue[ uxIndexToWait ] = 0UL;

    pxCurrentTCBs[ 0 ] = &xTask;

    vFakePortEnterCriticalSection_Expect();
    ulFakePortSetInterruptMask_ExpectAndReturn( 0 );
    vFakePortGetCoreID_ExpectAndReturn( 0 );
    vFakePortClearInterruptMask_Expect( 0 );

    ulFakePortSetInterruptMask_ExpectAndReturn( 0 );
    vFakePortGetCoreID_ExpectAndReturn( 0 );
    vFakePortClearInterruptMask_Expect( 0 );

    ulFakePortSetInterruptMask_ExpectAndReturn( 0 );
    vFakePortGetCoreID_ExpectAndReturn( 0 );
    vFakePortClearInterruptMask_Expect( 0 );

    ulFakePortSetInterruptMask_ExpectAndReturn( 0 );
    vFakePortGetCoreID_ExpectAndReturn( 0 );
    vFakePortClearInterruptMask_Expect( 0 );

    uxListRemove_ExpectAnyArgsAndReturn( pdTRUE );

    ulFakePortSetInterruptMask_ExpectAndReturn( 0 );
    vFakePortGetCoreID_ExpectAndReturn( 0 );
    vFakePortClearInterruptMask_Expect( 0 );

    listSET_LIST_ITEM_VALUE_ExpectAnyArgs();

    ulFakePortSetInterruptMask_ExpectAndReturn( 0 );
    vFakePortGetCoreID_ExpectAndReturn( 0 );
    vFakePortClearInterruptMask_Expect( 0 );

    vListInsert_ExpectAnyArgs();
    vFakePortGetCoreID_ExpectAndReturn( 0 );

    vFakePortYield_Expect();
    vFakePortExitCriticalSection_Expect();

    vFakePortEnterCriticalSection_Expect();

    ulFakePortSetInterruptMask_ExpectAndReturn( 0 );
    vFakePortGetCoreID_ExpectAndReturn( 0 );
    vFakePortClearInterruptMask_Expect( 0 );

    ulFakePortSetInterruptMask_ExpectAndReturn( 0 );
    vFakePortGetCoreID_ExpectAndReturn( 0 );
    vFakePortClearInterruptMask_Expect( 0 );

    vFakePortExitCriticalSection_Expect();


    ulRet = ulTaskGenericNotifyTake( uxIndexToWait, 1, 2 );

    TEST_ASSERT_EQUAL( 0,
                       xTask.ucNotifyState[ uxIndexToWait ] );
    TEST_ASSERT_EQUAL( 0UL, ulRet );
}

/**
 * @brief This test ensures that if the task notify state is not recieved, and
 *        the ticks to wait are greater than zero, then we do yield the task
 *        to allow another task to send a notification
 *
 * <b>Coverage</b>
 * @code{c}
 * xTaskGenericNotifyWait()
 *
 * vTaskYieldWithinAPI();
 * @endcode
 *
 * configNMBER_OF_CORES > 1
 * configUSE_TASK_NOTIFICATIONS = 1
 */
/* configUSE_TASK_NOTIFICATIONS  */
void test_coverage_xTaskGenericNotifyWait( void )
{
    UBaseType_t uxIndexToWait = 1;
    uint32_t ulBitsToClearOnEntry = pdTRUE;
    uint32_t ulBitsToClearOnExit = pdTRUE;
    uint32_t ulNotificationValue;
    TickType_t xTicksToWait = 40;
    BaseType_t xRet;
    TCB_t xTask = { 0 };

    /* Test Setup */
    xTask.ulNotifiedValue[ uxIndexToWait ] = 0UL;
    xTask.ucNotifyState[ uxIndexToWait ] = 0; /* taskWAITING_NOTIFICATION */
    xTask.uxCriticalNesting = 1;
    pxCurrentTCBs[ 0 ] = &xTask;

    /* Test Expectations */
    vFakePortEnterCriticalSection_Expect();

    ulFakePortSetInterruptMask_ExpectAndReturn( 0 );
    vFakePortGetCoreID_ExpectAndReturn( 0 );
    vFakePortClearInterruptMask_Expect( 0 );

    ulFakePortSetInterruptMask_ExpectAndReturn( 0 );
    vFakePortGetCoreID_ExpectAndReturn( 0 );
    vFakePortClearInterruptMask_Expect( 0 );

    ulFakePortSetInterruptMask_ExpectAndReturn( 0 );
    vFakePortGetCoreID_ExpectAndReturn( 0 );
    vFakePortClearInterruptMask_Expect( 0 );

    ulFakePortSetInterruptMask_ExpectAndReturn( 0 );
    vFakePortGetCoreID_ExpectAndReturn( 0 );
    vFakePortClearInterruptMask_Expect( 0 );

    ulFakePortSetInterruptMask_ExpectAndReturn( 0 );
    vFakePortGetCoreID_ExpectAndReturn( 0 );
    vFakePortClearInterruptMask_Expect( 0 );

    uxListRemove_ExpectAnyArgsAndReturn( pdFALSE );

    ulFakePortSetInterruptMask_ExpectAndReturn( 0 );
    vFakePortGetCoreID_ExpectAndReturn( 0 );
    vFakePortClearInterruptMask_Expect( 0 );

    listSET_LIST_ITEM_VALUE_ExpectAnyArgs();

    ulFakePortSetInterruptMask_ExpectAndReturn( 0 );
    vFakePortGetCoreID_ExpectAndReturn( 0 );
    vFakePortClearInterruptMask_Expect( 0 );

    vListInsert_ExpectAnyArgs();
    vFakePortGetCoreID_ExpectAndReturn( 0 );
    vFakePortGetCoreID_ExpectAndReturn( 0 );

    vFakePortExitCriticalSection_Expect();

    vFakePortEnterCriticalSection_Expect();

    ulFakePortSetInterruptMask_ExpectAndReturn( 0 );
    vFakePortGetCoreID_ExpectAndReturn( 0 );
    vFakePortClearInterruptMask_Expect( 0 );

    ulFakePortSetInterruptMask_ExpectAndReturn( 0 );
    vFakePortGetCoreID_ExpectAndReturn( 0 );
    vFakePortClearInterruptMask_Expect( 0 );

    ulFakePortSetInterruptMask_ExpectAndReturn( 0 );
    vFakePortGetCoreID_ExpectAndReturn( 0 );
    vFakePortClearInterruptMask_Expect( 0 );

    vFakePortExitCriticalSection_Expect();


    /* API Call */
    xRet = xTaskGenericNotifyWait( uxIndexToWait,
                                   ulBitsToClearOnEntry,
                                   ulBitsToClearOnExit,
                                   &ulNotificationValue,
                                   xTicksToWait );

    /* Test Verification */
    TEST_ASSERT_EQUAL( 0, pxCurrentTCBs[ 0 ]->ucNotifyState[ uxIndexToWait ] ); /* taskNOT_WAITING_NOTIFICATION */
    TEST_ASSERT_EQUAL( 0, xTask.ucNotifyState[ uxIndexToWait ] );               /* taskNOT_WAITING_NOTIFICATION */
    TEST_ASSERT_EQUAL( pdFALSE, xRet );
}
