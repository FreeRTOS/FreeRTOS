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

/* Test includes. */
#include "unity.h"
#include "unity_memory.h"
#include "CException.h"

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
static int assertionFailed = 0;

/**
 * @brief Flag which denotes if test need to abort on assertion.
 */
static BaseType_t shouldAbortOnAssertion;


/* ===========================  EXTERN VARIABLES  =========================== */
extern void vTaskEnterCritical( void );
extern void vTaskExitCritical( void );
extern void vTaskExitCriticalFromISR( UBaseType_t xSavedInterruptStatus );
extern void prvCheckForRunStateChange( void );

extern volatile UBaseType_t uxDeletedTasksWaitingCleanUp;
extern volatile BaseType_t xSchedulerRunning;
extern volatile UBaseType_t uxSchedulerSuspended;
extern TCB_t * volatile pxCurrentTCBs[ configNUMBER_OF_CORES ];
extern volatile BaseType_t xYieldPendings[ configNUMBER_OF_CORES ];
extern volatile UBaseType_t uxTopReadyPriority;
extern List_t pxReadyTasksLists[ configMAX_PRIORITIES ];
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

static void validate_and_clear_assertions( void )
{
    TEST_ASSERT_EQUAL( 1, assertionFailed );
    assertionFailed = 0;
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

/* ===============================  Callbacks  ============================== */
void port_release_task_lock_cb( int num_calls )
{
    pxCurrentTCBs[ 0 ]->xTaskRunState = -1; /* taskTASK_YIELDING */
}

/* ==============================  Test Cases  ============================== */

/**
 * @brief This test ensures that the code asserts when the TCB's critical
 *        nesting count is less than or equal to zero
 *
 * <b>Coverage</b>
 * @code{c}
 * prvYieldForTask( pxTCB );
 *
 * configASSERT( portGET_CRITICAL_NESTING_COUNT() > 0U );
 * @endcode
 *
 * configUSE_PREEMPTION == 1
 * configNUMBER_OF_CORES > 1
 * configUSE_CORE_AFFINITY == 1
 */
void test_prvYieldForTask_assert_critical_nesting_lteq_zero( void )
{
    UBaseType_t uxCoreAffinityMask;
    TCB_t currentTCB;

    memset( &currentTCB, 0x00, sizeof( TCB_t ) );

    pxCurrentTCBs[ 0 ] = &currentTCB;
    pxCurrentTCBs[ 0 ]->uxCoreAffinityMask = 1;
    pxCurrentTCBs[ 0 ]->uxCriticalNesting = 0;
    pxCurrentTCBs[ 0 ]->xTaskRunState = -1; /* taskTASK_NOT_RUNNING */
    xSchedulerRunning = pdTRUE;

    /* Set the new mask to the last core. */
    uxCoreAffinityMask = ( 1 << ( configNUMBER_OF_CORES - 1 ) );

    vFakePortEnterCriticalSection_Expect();
    vFakePortGetCoreID_ExpectAndReturn( 0 );

    EXPECT_ASSERT_BREAK( vTaskCoreAffinitySet( pxCurrentTCBs[ 0 ],
                                               uxCoreAffinityMask ) );

    validate_and_clear_assertions();
}

/**
 * @brief This test ensures that the code asserts when xYieldPending of the
 *        current core is false and the task is runing
 *
 * <b>Coverage</b>
 * @code{c}
 * prvYieldForTask( pxTCB );
 *
 * configASSERT( ( xYieldPendings[ portGET_CORE_ID() ] == pdTRUE ) ||
 *               ( taskTASK_IS_RUNNING( pxCurrentTCBs[ portGET_CORE_ID() ] ) == pdFALSE ) );
 * @endcode
 *
 * configNUMBER_OF_CORES > 1
 * configRUN_MULTIPLE_PRIORITIES = 0
 * configUSE_TASK_PREEMPTION_DISABLE
 */
void test_prvYieldForTask_assert_yieldpending_core_is_false( void )
{
    TCB_t unblockedTCB[ configNUMBER_OF_CORES ] = { 0 };

    ListItem_t xEventListItem;
    TickType_t xItemValue = 0;

    for( int i = 0; i < configNUMBER_OF_CORES; ++i )
    {
        pxCurrentTCBs[ i ] = &unblockedTCB[ i ];
        unblockedTCB[ i ].xTaskRunState = -1; /* taskTASK_YIELDING  */
    }

    unblockedTCB[ 0 ].uxCriticalNesting = 1;
    unblockedTCB[ 0 ].xTaskRunState = 0;
    unblockedTCB[ 0 ].uxTaskAttributes = 2;
    unblockedTCB[ 0 ].uxPriority = 1;

    unblockedTCB[ 1 ].uxTaskAttributes = 2;
    unblockedTCB[ 1 ].uxPriority = 0;
    unblockedTCB[ 1 ].xTaskRunState = 1;

    unblockedTCB[ 2 ].xTaskRunState = -1;

    unblockedTCB[ 3 ].xTaskRunState = configNUMBER_OF_CORES + 2;

    uxSchedulerSuspended = 3;

    xYieldPendings[ 1 ] = pdFALSE;

    listSET_LIST_ITEM_VALUE_ExpectAnyArgs();
    listGET_LIST_ITEM_OWNER_ExpectAnyArgsAndReturn( &unblockedTCB[ 0 ] );
    listREMOVE_ITEM_ExpectAnyArgs();
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdTRUE );
    listREMOVE_ITEM_ExpectAnyArgs();
    /* in prvAddTaskToReadyList */
    listINSERT_END_ExpectAnyArgs();
    /* back */
    /* taskENTER_CRITICAL */
    vFakePortEnterCriticalSection_Expect();
    /* back */
    /* prvYieldForTask */
    vFakePortGetCoreID_ExpectAndReturn( 0 );
    vFakePortGetCoreID_ExpectAndReturn( 1 );
    vFakePortGetCoreID_ExpectAndReturn( 1 );
    vFakePortGetCoreID_ExpectAndReturn( 1 );
    vFakePortGetCoreID_ExpectAndReturn( 0 );
    vFakePortGetCoreID_ExpectAndReturn( 0 );
    vFakePortGetCoreID_ExpectAndReturn( 0 );

    EXPECT_ASSERT_BREAK( vTaskRemoveFromUnorderedEventList( &xEventListItem,
                                                            xItemValue ) );
    validate_and_clear_assertions();
}

/**
 * @brief This test ensures that the code asserts when we are trying to select
 *        the highest priority task on a specific core while the scheuler is not
 *        running
 *
 * <b>Coverage</b>
 * @code{c}
 * prvSelectHighestPriorityTask( xCoreID );
 *
 * configASSERT( xSchedulerRunning == pdTRUE );
 *
 * @endcode
 *
 * configNUMBER_OF_CORES > 1
 */
void test_prvSelectHighestPriorityTask_assert_scheduler_running_false( void )
{
    TCB_t unblockedTCB[ configNUMBER_OF_CORES ] = { 0 };

    unblockedTCB[ 0 ].uxCriticalNesting = 0;

    pxCurrentTCBs[ 0 ] = &unblockedTCB[ 0 ];

    xSchedulerRunning = pdFALSE; /* causes the assert */
    uxSchedulerSuspended = pdFALSE;

    vFakePortGetTaskLock_Expect();
    vFakePortGetISRLock_Expect();
    vFakePortGetCoreID_ExpectAndReturn( 0 );

    EXPECT_ASSERT_BREAK( vTaskSwitchContext( 1 ) );
    validate_and_clear_assertions();
}

/**
 * @brief This test ensures that the code asserts when the coreID is not equal
 *        to the runstate of the task
 *
 * <b>Coverage</b>
 * @code{c}
 * prvSelectHighestPriorityTask( xCoreID );
 *
 * configASSERT( ( pxTCB->xTaskRunState == xCoreID ) || ( pxTCB->xTaskRunState == taskTASK_YIELDING ) );
 *
 * @endcode
 *
 * configNUMBER_OF_CORES > 1
 */
void test_prvSelectHighestPriorityTask_assert_coreid_ne_runstate( void )
{
    TCB_t unblockedTCB[ configNUMBER_OF_CORES ] = { 0 };

    unblockedTCB[ 0 ].uxCriticalNesting = 0;
    unblockedTCB[ 0 ].xTaskRunState = 2; /* causes the assert coreID != runstate */

    pxCurrentTCBs[ 0 ] = &unblockedTCB[ 0 ];

    xSchedulerRunning = pdTRUE;
    uxSchedulerSuspended = pdFALSE;

    vFakePortGetTaskLock_Expect();
    vFakePortGetISRLock_Expect();
    vFakePortGetCoreID_ExpectAndReturn( 0 );

    listIS_CONTAINED_WITHIN_ExpectAnyArgsAndReturn( pdFALSE );
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdFALSE );
    listGET_LIST_ITEM_OWNER_ExpectAnyArgsAndReturn( &unblockedTCB[ 0 ] );

    EXPECT_ASSERT_BREAK( vTaskSwitchContext( 0 ) );

    validate_and_clear_assertions();
}

/**
 * @brief This test ensures that the code asserts if the scheduler is not
 *        suspended
 *
 * <b>Coverage</b>
 * @code{c}
 * vTaskDelete( xTaskToDelete );
 *
 * configASSERT( uxSchedulerSuspended == 0 );
 * @endcode
 *
 * configNUMBER_OF_CORES > 1
 * INCLUDE_vTaskDelete
 */
void test_vTaskDelete_assert_scheduler_suspended_eq_1( void )
{
    TaskHandle_t xTaskToDelete = NULL;
    TCB_t * pxTCB = malloc( sizeof( TCB_t ) );

    pxTCB->pxStack = malloc( 200 );
    pxTCB->xTaskRunState = 1; /* task running on core 1 */
    xTaskToDelete = ( TaskHandle_t ) pxTCB;

    uxSchedulerSuspended = 1; /* asserts the code */
    xSchedulerRunning = pdTRUE;

    vFakePortEnterCriticalSection_Expect();
    uxListRemove_ExpectAnyArgsAndReturn( pdTRUE );
    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( NULL );
    vListInsertEnd_ExpectAnyArgs();
    vPortCurrentTaskDying_ExpectAnyArgs();
    vFakePortGetCoreID_ExpectAndReturn( 1 );

    EXPECT_ASSERT_BREAK( vTaskDelete( xTaskToDelete ) );

    validate_and_clear_assertions();

    free( pxTCB->pxStack );
    free( pxTCB );
}

/**
 * @brief vTaskSuspend - scheduler suspended assertion.
 *
 * This test ensures that the code asserts when a task is suspended while
 * the scheduler is suspended
 *
 * <b>Coverage</b>
 * @code{c}
 * if( xSchedulerRunning != pdFALSE )
 * {
 *     if( pxTCB->xTaskRunState == ( BaseType_t ) portGET_CORE_ID() )
 *     {
 *         configASSERT( uxSchedulerSuspended == 0 );
 *         vTaskYieldWithinAPI();
 *     }
 *     else
 *     {
 *         prvYieldCore( pxTCB->xTaskRunState );
 *     }
 * }
 * @endcode
 * configASSERT( uxSchedulerSuspended == 0 ) is triggered.
 */
void test_vTaskSuspend_assert_schedulersuspended_ne_zero( void )
{
    TaskHandle_t xTaskToSuspend;
    TCB_t * pxTCB = malloc( sizeof( TCB_t ) );

    xTaskToSuspend = ( TaskHandle_t ) pxTCB;
    xSchedulerRunning = pdTRUE;
    pxTCB->xTaskRunState = 1;
    uxSchedulerSuspended = 1; /* asserts the code */

    vFakePortEnterCriticalSection_Expect();
    uxListRemove_ExpectAnyArgsAndReturn( pdTRUE );
    listLIST_ITEM_CONTAINER_ExpectAnyArgsAndReturn( NULL );
    vListInsertEnd_ExpectAnyArgs();
    listLIST_IS_EMPTY_ExpectAnyArgsAndReturn( pdTRUE );
    vFakePortGetCoreID_ExpectAndReturn( 1 );

    EXPECT_ASSERT_BREAK( vTaskSuspend( xTaskToSuspend ) );

    validate_and_clear_assertions();

    free( pxTCB );
}

/**
 * @brief This test ensures that the code asserts when we try to switch
 *        context with a current task that is holding a
 *        critical section
 *
 * <b>Coverage</b>
 * @code{c}
 * vTaskSwitchContext( xCoreID );
 *
 * configASSERT( portGET_CRITICAL_NESTING_COUNT() == 0 );
 *
 * @endcode
 *
 * configNUMBER_OF_CORES > 1
 */
void test_vTaskSwitchContext_assert_nexting_count_ne_zero( void )
{
    TCB_t currentTCB = { 0 };

    currentTCB.uxCriticalNesting = 1; /* causes the assert */

    pxCurrentTCBs[ 1 ] = &currentTCB;

    vFakePortGetTaskLock_Expect();
    vFakePortGetISRLock_Expect();
    vFakePortGetCoreID_ExpectAndReturn( 1 );

    EXPECT_ASSERT_BREAK( vTaskSwitchContext( 1 ) );

    validate_and_clear_assertions();
}

/**
 * @brief This test ensures that the code asserts when we try to exit a critical
 *        section while the current tasks critical count is zero
 *
 * <b>Coverage</b>
 * @code{c}
 * vTaskExitCritical();
 *
 * configASSERT( portGET_CRITICAL_NESTING_COUNT() > 0U );
 *
 * @endcode
 *
 * configNUMBER_OF_CORES > 1
 */
void test_vTaskExitCritical_assert_critical_nesting_eq_zero( void )
{
    TCB_t currentTCB = { 0 };

    xSchedulerRunning = pdTRUE;
    currentTCB.uxCriticalNesting = 0; /* causes the assert */
    pxCurrentTCBs[ 1 ] = &currentTCB;

    vFakePortGetCoreID_ExpectAndReturn( 1 );

    EXPECT_ASSERT_BREAK( vTaskExitCritical() );

    validate_and_clear_assertions();
}

/**
 * @brief This test ensures that the code asserts when we try to exit a critical
 *        section while the current tasks critical count is zero
 *
 * <b>Coverage</b>
 * @code{c}
 * vTaskExitCriticalFromISR();
 *
 * configASSERT( portGET_CRITICAL_NESTING_COUNT() > 0U );
 *
 * @endcode
 *
 * configNUMBER_OF_CORES > 1
 */
void test_vTaskExitCriticalFromISR_assertcritical_nesting_eq_zero( void )
{
    TCB_t currentTCB = { 0 };

    xSchedulerRunning = pdTRUE;
    currentTCB.uxCriticalNesting = 0; /* causes the assert */
    pxCurrentTCBs[ 1 ] = &currentTCB;

    vFakePortGetCoreID_ExpectAndReturn( 1 );

    EXPECT_ASSERT_BREAK( vTaskExitCriticalFromISR( 1 ) );

    validate_and_clear_assertions();
}

/**
 * @brief This test ensures that the code asserts  when the next unblock time is
 *        less than the xTickCount
 *
 * <b>Coverage</b>
 * @code{c}
 * prvIdleTask();
 *
 * configASSERT( xNextTaskUnblockTime >= xTickCount );
 *
 * @endcode
 *
 * configNUMBER_OF_CORES > 1
 * configUSE_TICKLESS_IDLE != 0
 */
void test_prvGetExpectedIdleTime_assert_nextUnblock_lt_xTickCount( void )
{
    TCB_t xTCB = { 0 };

    xTickCount = 250;
    xNextTaskUnblockTime = 240; /* expectedidletime = xNextTaskUnblockTime - xTickCount */
    pxCurrentTCBs[ 0 ] = &xTCB;
    xTCB.uxPriority = tskIDLE_PRIORITY;

    /* Test Setup */
    uxDeletedTasksWaitingCleanUp = 0;
    uxTopReadyPriority = tskIDLE_PRIORITY;

    /* Test Expectations */
    vFakePortYield_Expect();

    listCURRENT_LIST_LENGTH_ExpectAnyArgsAndReturn( 0 );

    ulFakePortSetInterruptMask_ExpectAndReturn( 0 );
    vFakePortGetCoreID_ExpectAndReturn( 0 );
    vFakePortClearInterruptMask_Expect( 0 );

    listCURRENT_LIST_LENGTH_ExpectAnyArgsAndReturn( 0 );

    /* vTaskSuspendAll */
    vFakePortAssertIfISR_Expect();
    ulFakePortSetInterruptMask_ExpectAndReturn( 0 );
    vFakePortGetCoreID_ExpectAndReturn( 0 );
    vFakePortGetTaskLock_Expect();
    vFakePortGetISRLock_Expect();
    vFakePortReleaseISRLock_Expect();
    vFakePortClearInterruptMask_Expect( 0 );

    /* API Call */
    portTASK_FUNCTION( prvIdleTask, args );
    EXPECT_ASSERT_BREAK( prvIdleTask( NULL ) );

    /* Test Verifications */
    validate_and_clear_assertions();
}

/**
 * @brief vTaskStepTick - assert if scheduler suspended.
 *
 * <b>Coverage</b>
 * @code{c}
 * configASSERT( uxSchedulerSuspended );
 * @endcode
 */
void test_vTaskStepTick_assert_scheduler_not_suspended( void )
{
    TickType_t xTicksToJump;

    xTickCount = 230;
    xTicksToJump = 10;
    xNextTaskUnblockTime = 240;
    uxSchedulerSuspended = pdFALSE;

    /* API Call */
    EXPECT_ASSERT_BREAK( vTaskStepTick( xTicksToJump ) );

    /* Test Verifications */
    validate_and_clear_assertions();
}

/**
 * @brief vTaskStepTick - assert if scheduler suspended.
 *
 * <b>Coverage</b>
 * @code{c}
 * configASSERT( xTicksToJump != ( TickType_t ) 0 );
 * @endcode
 */
void test_vTaskStepTick_assert_tick_to_jump_eq_0( void )
{
    TickType_t xTicksToJump;

    xTickCount = 240;
    xTicksToJump = 0;
    xNextTaskUnblockTime = 240;
    uxSchedulerSuspended = pdTRUE;

    /* API Call */
    EXPECT_ASSERT_BREAK( vTaskStepTick( xTicksToJump ) );

    /* Test Verifications */
    validate_and_clear_assertions();
}

/**
 * @brief xTaskGetIdleTaskHandleForCore - assert if xCoreID is less than 0
 *
 * <b>Coverage</b>
 * @code{c}
 * configASSERT( taskVALID_CORE_ID( xCoreID ) == pdTRUE );
 * @endcode
 * taskVALID_CORE_ID( xCoreID ) is false with xCoreID less than 0.
 */
void test_xTaskGetIdleTaskHandleForCore_assert_invalid_core_id_lt( void )
{
    /* API Call */
    EXPECT_ASSERT_BREAK( xTaskGetIdleTaskHandleForCore( -1 ) );

    /* Test Verifications */
    validate_and_clear_assertions();
}

/**
 * @brief xTaskGetIdleTaskHandleForCore - assert if xCoreID is greater or equal
 * than configNUMBER_OF_CORES
 *
 * <b>Coverage</b>
 * @code{c}
 * configASSERT( taskVALID_CORE_ID( xCoreID ) == pdTRUE );
 * @endcode
 * taskVALID_CORE_ID( xCoreID ) is false with xCoreID greater or equal than configNUMBER_OF_CORES
 */
void test_xTaskGetIdleTaskHandleForCore_assert_invalid_core_id_ge( void )
{
    /* API Call */
    EXPECT_ASSERT_BREAK( xTaskGetIdleTaskHandleForCore( configNUMBER_OF_CORES ) );

    /* Test Verifications */
    validate_and_clear_assertions();
}

/**
 * @brief xTaskGetIdleTaskHandleForCore - assert if idle task handle is NULL due to
 * scheduler not started.
 *
 * <b>Coverage</b>
 * @code{c}
 * configASSERT( ( xIdleTaskHandles[ xCoreID ] != NULL ) );
 * @endcode
 * ( xIdleTaskHandles[ xCoreID ] != NULL ) is false.
 */
void test_xTaskGetIdleTaskHandleForCore_assert_null_idle_task_handle( void )
{
    BaseType_t xCoreID;

    /* Setup the variables and structure. */
    for( xCoreID = 0; xCoreID < configNUMBER_OF_CORES; xCoreID++ )
    {
        xIdleTaskHandles[ xCoreID ] = NULL;
    }

    for( xCoreID = 0; xCoreID < configNUMBER_OF_CORES; xCoreID++ )
    {
        /* API Call */
        EXPECT_ASSERT_BREAK( xTaskGetIdleTaskHandleForCore( xCoreID ) );

        /* Test Verifications */
        validate_and_clear_assertions();
    }
}
