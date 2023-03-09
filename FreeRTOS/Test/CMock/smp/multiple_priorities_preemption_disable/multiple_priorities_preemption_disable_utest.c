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
/*! @file config_assert_utest.c */

/* C runtime includes. */
#include <stdlib.h>
#include <stdbool.h>
#include <stdint.h>
#include <string.h>
#include <stdio.h>

/* Tasks includes */
#include "FreeRTOS.h"
#include "FreeRTOSConfig.h"
#include "../global_vars.h"
#include "task.h"

/* #include "fake_port.h" */
#include "portmacro.h"

/* Test includes. */
#include "unity.h"
#include "unity_memory.h"
#include "CException.h"


/* Local includes. */
/*#include "../smp_utest_common.h" */

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
 * @brief simulate up to 10 tasks: add more if needed
 * */
#define TCB_ARRAY         10

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
 * @brief Global counter for the number of assertions in code.
 */
static int assertionFailed = 1;

/**
 * @brief Flag which denotes if test need to abort on assertion.
 */
static BaseType_t shouldAbortOnAssertion;

/**
 * @brief Flag which tell the callbacks at which iteration to break the loop of
 *        the idle task
 */
static int break_loop_at = 1;


/* ===========================  EXTERN VARIABLES  =========================== */
extern void vTaskEnterCritical( void );
extern void vTaskExitCritical( void );
extern void vTaskExitCriticalFromISR( UBaseType_t uxSavedInterruptStatus );

extern volatile UBaseType_t uxDeletedTasksWaitingCleanUp;
extern volatile BaseType_t xSchedulerRunning;
extern volatile UBaseType_t uxSchedulerSuspended;
extern TCB_t * volatile pxCurrentTCBs[ configNUMBER_OF_CORES ];
extern volatile BaseType_t xYieldPendings[ configNUMBER_OF_CORES ];
extern volatile UBaseType_t uxTopReadyPriority;
extern List_t pxReadyTasksLists[ configMAX_PRIORITIES ];
extern UBaseType_t uxTaskNumber;
extern volatile TickType_t xTickCount;
extern volatile TickType_t xNextTaskUnblockTime;
extern TaskHandle_t xIdleTaskHandles[ configNUMBER_OF_CORES ];

/* ==========================  STATIC FUNCTIONS  ========================== */
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

void * pvPortMalloc( size_t xSize )
{
    return unity_malloc( xSize );
}

void vPortFree( void * pv )
{
    return unity_free( pv );
}
/* ============================  Unity Fixtures  ============================ */
/*! called before each testcase */
void setUp( void )
{
    uxDeletedTasksWaitingCleanUp;
    vFakeAssert_StubWithCallback( vFakeAssertStub );
}

/*! called after each testcase */
void tearDown( void )
{
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
 * @brief This test ensures that the  first condition is true while the second
 *        condition is false in the if statement, so we will be performing the
 *        action with portYIELD_CORE, and the task is put in the yielding state
 *
 * <b>Coverage</b>
 * @code{c}
 * prvYieldCore( xCoreID );
 *
 * if( ( portCHECK_IF_IN_ISR() == pdTRUE ) && ( xCoreID == portGET_CORE_ID() ) )
 *
 * @endcode
 *
 * configNMBER_OF_CORES > 1
 * configUSE_TASK_PREEMPTION_DISABLE = 1
 */
void test_prvYieldCore_core_id_ne_current_coreid( void )
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
 * @brief This test ensures that when the task is already in the yielding state,
 *        nothing is done
 *
 * <b>Coverage</b>
 * @code{c}
 * prvYieldCore( xCoreID );
 *
 * if( pxCurrentTCBs[ xCoreID ]->xTaskRunState != taskTASK_YIELDING )
 *
 * @endcode
 *
 * configNMBER_OF_CORES > 1
 * configUSE_TASK_PREEMPTION_DISABLE = 1
 */
void test_prvYieldCore_runstate_eq_yielding( void )
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
 * @brief This test ensures that if xTask Delete is caled and the scheuler is
 *        not running, the core is not yielded, but it is removed from the
 *        stateList, the eventList and inserted in the taskwaitingtermination
 *        list, the uxdeletedtaskwaiting for cleanup is increased and the
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
void test_vTaskDelete_scheduler_not_running( void )
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
void test_vTaskDelete_task_not_running( void )
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
void test_eTaskGetState_task_not_running( void )
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
void test_vTaskPreemptionDisable_null_handle( void )
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
void test_vTaskSuspendAll_critical_nesting_ne_zero( void )
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


UBaseType_t list_length_cb( List_t * list,
                            int num_calls )
{
    if( num_calls < break_loop_at )
    {
        return configNUMBER_OF_CORES - 1;
    }
    else
    {
        Throw( EXIT_LOOP );
    }

    return 0;
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
void test_prvGetExpectedIdleTime_top_priority_gt_idle_prio( void )
{
    CEXCEPTION_T e = CEXCEPTION_NONE;
    TCB_t xTCB = { 0 };

    break_loop_at = 1;

    pxCurrentTCBs[ 0 ] = &xTCB;

    xTCB.uxPriority = tskIDLE_PRIORITY + 1;

    /* Test Setup */
    uxDeletedTasksWaitingCleanUp = 0;
    uxTopReadyPriority = tskIDLE_PRIORITY;

    /* Test Expectations */
    vFakePortYield_Expect();

    listCURRENT_LIST_LENGTH_Stub( list_length_cb );

    ulFakePortSetInterruptMask_ExpectAndReturn( 0 );
    vFakePortGetCoreID_ExpectAndReturn( 0 );
    vFakePortClearInterruptMask_Expect( 0 );

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
void test_prvGetExpectedIdleTime_ready_list_gt_one( void )
{
    CEXCEPTION_T e = CEXCEPTION_NONE;
    TCB_t xTCB = { 0 };

    break_loop_at = 2;
    pxCurrentTCBs[ 0 ] = &xTCB;
    xTCB.uxPriority = tskIDLE_PRIORITY;

    /* Test Setup */
    uxDeletedTasksWaitingCleanUp = 0;
    uxTopReadyPriority = tskIDLE_PRIORITY;

    /* Test Expectations */
    vFakePortYield_Expect();

    listCURRENT_LIST_LENGTH_Stub( list_length_cb );

    ulFakePortSetInterruptMask_ExpectAndReturn( 0 );
    vFakePortGetCoreID_ExpectAndReturn( 0 );
    vFakePortClearInterruptMask_Expect( 0 );

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

UBaseType_t list_length_cb2( List_t * list,
                             int num_calls )
{
    if( ( num_calls == 1 ) || ( num_calls == 2 ) )
    {
        return 1;
    }

    if( num_calls < break_loop_at )
    {
        return configNUMBER_OF_CORES - 1;
    }
    else
    {
        Throw( EXIT_LOOP );
    }

    return 0;
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
void test_prvGetExpectedIdleTime_ready_list_eq_1( void )
{
    CEXCEPTION_T e = CEXCEPTION_NONE;
    TCB_t xTCB = { 0 };

    xTickCount = 230;
    xNextTaskUnblockTime = 240; /* expectedidletime = xNextTaskUnblockTime - xTickCount */
    break_loop_at = 3;
    pxCurrentTCBs[ 0 ] = &xTCB;
    xTCB.uxPriority = tskIDLE_PRIORITY;

    /* Test Setup */
    uxDeletedTasksWaitingCleanUp = 0;
    uxTopReadyPriority = tskIDLE_PRIORITY;

    /* Test Expectations */
    vFakePortYield_Expect();

    listCURRENT_LIST_LENGTH_Stub( list_length_cb2 );

    ulFakePortSetInterruptMask_ExpectAndReturn( 0 );
    vFakePortGetCoreID_ExpectAndReturn( 0 );
    vFakePortClearInterruptMask_Expect( 0 );

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

    /* Test Verifications */

    /* this function being called is the aim of this test, it proves that the
     * task went to sleep the specified amount of time. */
    vPortSuppressTicksAndSleep_Expect( xNextTaskUnblockTime - xTickCount );


    vFakePortEnterCriticalSection_Expect();
    vFakePortGetCoreID_ExpectAndReturn( 0 );
    vFakePortReleaseTaskLock_Expect();
    vFakePortExitCriticalSection_Expect();

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

UBaseType_t list_length_cb3( List_t * list,
                             int num_calls )
{
    if( num_calls == 1 )
    {
        return 1;
    }

    if( num_calls < break_loop_at )
    {
        return configNUMBER_OF_CORES - 1;
    }
    else
    {
        Throw( EXIT_LOOP );
    }

    return 0;
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
void test_prvGetExpectedIdleTime_top_ready_prio_gt_idle_prio_current_prio_lt_idle( void )
{
    CEXCEPTION_T e = CEXCEPTION_NONE;
    TCB_t xTCB = { 0 };

    break_loop_at = 2;
    pxCurrentTCBs[ 0 ] = &xTCB;

    /* Test Setup */
    uxDeletedTasksWaitingCleanUp = 0;
    xTCB.uxPriority = tskIDLE_PRIORITY;
    uxTopReadyPriority = tskIDLE_PRIORITY + 1;

    /* Test Expectations */
    vFakePortYield_Expect();

    listCURRENT_LIST_LENGTH_Stub( list_length_cb3 );

    ulFakePortSetInterruptMask_ExpectAndReturn( 0 );
    vFakePortGetCoreID_ExpectAndReturn( 0 );
    vFakePortClearInterruptMask_Expect( 0 );


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
void test_prvCreateIdleTasks_name_too_long( void )
{
    BaseType_t prvCreateIdleTasks( void );

    TCB_t * xIdleTask;
    TCB_t xTask = { 0 };
    int i;

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
}
