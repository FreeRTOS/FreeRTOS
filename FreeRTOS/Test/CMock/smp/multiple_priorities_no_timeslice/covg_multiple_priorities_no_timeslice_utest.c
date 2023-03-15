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

#define tskSTATICALLY_ALLOCATED_STACK_ONLY      ( ( uint8_t ) 1 )
#define tskSTACK_FILL_BYTE                      ( 0xa5U )
#define TEST_VTASKLIST_BUFFER_SIZE              ( 800 )     /* Size for task list. */

/* ===========================  EXTERN VARIABLES  =========================== */
extern volatile UBaseType_t uxCurrentNumberOfTasks;
extern volatile UBaseType_t uxDeletedTasksWaitingCleanUp;
extern volatile UBaseType_t uxSchedulerSuspended;
extern volatile TCB_t *  pxCurrentTCBs[ configNUMBER_OF_CORES ];
extern volatile BaseType_t xSchedulerRunning;
extern volatile TickType_t xTickCount;
extern List_t pxReadyTasksLists[ configMAX_PRIORITIES ];
extern volatile UBaseType_t uxTopReadyPriority;
extern volatile BaseType_t xYieldPendings[ configNUMBER_OF_CORES ];
extern List_t xTasksWaitingTermination;
extern List_t xSuspendedTaskList;
extern List_t xPendingReadyList;
extern BaseType_t xPendedTicks;
extern List_t xDelayedTaskList1;
extern List_t xDelayedTaskList2;
extern List_t * pxDelayedTaskList;
extern List_t * pxOverflowDelayedTaskList;

/* ===========================  EXTERN FUNCTIONS  =========================== */
extern void prvAddNewTaskToReadyList( TCB_t * pxNewTCB );
extern void prvYieldForTask( TCB_t * pxTCB );
extern void vTaskEnterCritical( void );
extern UBaseType_t vTaskEnterCriticalFromISR( void );
extern void vTaskExitCritical( void );
extern void vTaskExitCriticalFromISR( UBaseType_t uxSavedInterruptStatus );
extern void prvCheckTasksWaitingTermination( void );
extern void prvDeleteTCB( TCB_t * pxTCB );

/* ==============================  Global VARIABLES ============================== */
TaskHandle_t xTaskHandles[configNUMBER_OF_CORES] = { NULL };

/* ============================  Unity Fixtures  ============================ */
/*! called before each testcase */
void setUp( void )
{
    UBaseType_t uxPriority;

    commonSetUp();

    for( uxPriority = (UBaseType_t)0U; uxPriority < (UBaseType_t)configMAX_PRIORITIES; uxPriority++ )
    {
        vListInitialise( &( pxReadyTasksLists[uxPriority] ) );
    }

    vListInitialise( &xSuspendedTaskList );
    vListInitialise( &xPendingReadyList );
    vListInitialise( &xDelayedTaskList1 );
    vListInitialise( &xDelayedTaskList2 );
    vListInitialise( &xTasksWaitingTermination );

    pxDelayedTaskList = &xDelayedTaskList1;
    pxOverflowDelayedTaskList = &xDelayedTaskList2;
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
static void prvPortEnterCriticalSectionCb( int cmock_num_calls )
{
    ( void ) cmock_num_calls;

    /* This simulate the multiple idle tasks tries to clean the deleleted TCB. */
    uxDeletedTasksWaitingCleanUp = 0;
}

static void prvInitialiseTestStack( TCB_t * pxTCB,
                                    const uint32_t ulStackDepth )
{
    StackType_t * pxTopOfStack;

    pxTopOfStack = NULL;

    pxTCB->pxStack = ( StackType_t * ) pvPortMallocStack(
        ( ( ( size_t ) ulStackDepth ) * sizeof( StackType_t ) ) );
    ( void ) memset( pxTCB->pxStack, ( int ) tskSTACK_FILL_BYTE,
                     ( size_t ) ulStackDepth * sizeof( StackType_t ) );

    #if ( portSTACK_GROWTH < 0 )
    {
        pxTopOfStack = &( pxTCB->pxStack[ ulStackDepth - ( uint32_t ) 1 ] );
        pxTopOfStack = ( StackType_t * ) ( ( ( portPOINTER_SIZE_TYPE ) pxTopOfStack ) &
                       ( ~( ( portPOINTER_SIZE_TYPE ) portBYTE_ALIGNMENT_MASK ) ) );

        #if ( configRECORD_STACK_HIGH_ADDRESS == 1 )
        {
            pxTCB->pxEndOfStack = pxTopOfStack;
        }
        #endif /* configRECORD_STACK_HIGH_ADDRESS */
    }
    #else /* portSTACK_GROWTH */
    {
        pxTopOfStack = pxTCB->pxStack;
        pxTCB->pxEndOfStack = pxTCB->pxStack + ( ulStackDepth - ( uint32_t ) 1 );
    }
    #endif /* portSTACK_GROWTH */

    ( void ) pxTopOfStack;
}

/* ==============================  Test Cases  ============================== */

/**
 * @brief vTaskPreemptionEnable - Enable preemption of a task when scheduler is not running.
 *
 * The xPreemptionDisable of the task will be set to pdFALSE.
 *
 * <b>Coverage</b>
 * @code{c}
 * if( xSchedulerRunning != pdFALSE )
 * {
 *     if( taskTASK_IS_RUNNING( pxTCB ) == pdTRUE )
 *     {
 *         xCoreID = ( BaseType_t ) pxTCB->xTaskRunState;
 *         prvYieldCore( xCoreID );
 *     }
 * }
 * @endcode
 * ( xSchedulerRunning != pdFALSE ) is false.
 */
void test_coverage_vTaskPreemptionEnable_scheduler_not_running( void )
{
    TCB_t xTaskTCB = { NULL };

    /* Setup variables. */
    xTaskTCB.xPreemptionDisable = pdTRUE;

    /* Clear callback in commonSetUp. */
    vFakePortEnterCriticalSection_StubWithCallback( NULL );
    vFakePortExitCriticalSection_StubWithCallback( NULL );

    /* Expectations. */
    vFakePortEnterCriticalSection_Expect();
    vFakePortExitCriticalSection_Expect();

    /* API call. */
    vTaskPreemptionEnable( &xTaskTCB );

    /* Validation. */
    TEST_ASSERT( xTaskTCB.xPreemptionDisable == pdFALSE );
}

/**
 * @brief vTaskPreemptionEnable - Enable preemption of a task when scheduler is running.
 *
 * The xPreemptionDisable of the task will be set to pdFALSE.
 *
 * <b>Coverage</b>
 * @code{c}
 * if( xSchedulerRunning != pdFALSE )
 * {
 *     if( taskTASK_IS_RUNNING( pxTCB ) == pdTRUE )
 *     {
 *         xCoreID = ( BaseType_t ) pxTCB->xTaskRunState;
 *         prvYieldCore( xCoreID );
 *     }
 * }
 * @endcode
 * ( xSchedulerRunning != pdFALSE ) is true.
 * ( taskTASK_IS_RUNNING( pxTCB ) == pdTRUE ) is false.
 */
void test_coverage_vTaskPreemptionEnable_scheduler_running( void )
{
    TCB_t xTaskTCB = { NULL };

    /* Setup variable. */
    xTaskTCB.xPreemptionDisable = pdTRUE;
    xTaskTCB.xTaskRunState = -1; /* taskTASK_NOT_RUNNING. */

    xSchedulerRunning = pdTRUE;
    
    /* Clear callback in commonSetUp. */
    vFakePortEnterCriticalSection_StubWithCallback( NULL );
    vFakePortExitCriticalSection_StubWithCallback( NULL );

    /* Expectations. */
    vFakePortEnterCriticalSection_Expect();
    vFakePortExitCriticalSection_Expect();

    /* API call. */
    vTaskPreemptionEnable( &xTaskTCB );

    /* Validation. */
    TEST_ASSERT( xTaskTCB.xPreemptionDisable == pdFALSE );
}

/**
 * @brief vTaskPreemptionEnable - Enable preemption of a task with NULL handle.
 *
 * The xPreemptionDisable of the task on core 0 will be set to pdFALSE.
 *
 * <b>Coverage</b>
 * @code{c}
 * pxTCB = prvGetTCBFromHandle( xTask );
 * @endcode
 * prvGetTCBFromHandle( xTask ) parameter xTask is NULL.
 */
void test_coverage_vTaskPreemptionEnable_null_handle( void )
{
    TCB_t xTaskTCB = { NULL };
    UBaseType_t uxInterruptMask = 0x12345678;

    xTaskTCB.xPreemptionDisable  = pdTRUE;
    xTaskTCB.xTaskRunState = -1; /* taskTASK_NOT_RUNNING. */
    pxCurrentTCBs[ 0 ] = &xTaskTCB;

    /* Clear callback in commonSetUp. */
    vFakePortEnterCriticalSection_StubWithCallback( NULL );
    vFakePortExitCriticalSection_StubWithCallback( NULL );
    ulFakePortSetInterruptMask_StopIgnore();
    vFakePortClearInterruptMask_StubWithCallback( NULL );
    vFakePortGetCoreID_StubWithCallback( NULL );

    /* Expectations. */
    vFakePortEnterCriticalSection_Expect();
    ulFakePortSetInterruptMask_ExpectAndReturn( uxInterruptMask );
    vFakePortGetCoreID_ExpectAndReturn( 0 );
    vFakePortClearInterruptMask_Expect( uxInterruptMask );
    vFakePortExitCriticalSection_Expect();

    /* API call. */
    vTaskPreemptionEnable( NULL );

    /* Expection. */
    TEST_ASSERT( pxCurrentTCBs[ 0 ]->xPreemptionDisable == pdFALSE );
}

/**
 * @brief vTaskPreemptionEnable - Enable preemption of a task which is not running.
 *
 * The xPreemptionDisable of the task will be set to pdFALSE. The xTaskRunState is
 * set to greater than ( configNUMBER_OF_CORES - 1 ).
 *
 * <b>Coverage</b>
 * @code{c}
 * if( xSchedulerRunning != pdFALSE )
 * {
 *     if( taskTASK_IS_RUNNING( pxTCB ) == pdTRUE )
 *     {
 *         xCoreID = ( BaseType_t ) pxTCB->xTaskRunState;
 *         prvYieldCore( xCoreID );
 *     }
 * }
 * @endcode
 * ( xSchedulerRunning != pdFALSE ) is true.
 * ( taskTASK_IS_RUNNING( pxTCB ) == pdTRUE ) is false.
 */
void test_coverage_vTaskPreemptionEnable_task_not_running_gt_cores( void )
{
    TCB_t xTaskTCB = { NULL };

    /* Setup variables. */
    xTaskTCB.xPreemptionDisable  = pdTRUE;
    xTaskTCB.xTaskRunState = configNUMBER_OF_CORES;

    xSchedulerRunning = pdTRUE;

    /* Clear callback in commonSetUp. */
    vFakePortEnterCriticalSection_StubWithCallback( NULL );
    vFakePortExitCriticalSection_StubWithCallback( NULL );

    /* Expectations. */
    vFakePortEnterCriticalSection_Expect();
    vFakePortExitCriticalSection_Expect();

    /* API call. */
    vTaskPreemptionEnable( &xTaskTCB );

    /* Validation. */
    TEST_ASSERT( xTaskTCB.xPreemptionDisable == pdFALSE );
}

/**
 * @brief vTaskPreemptionEnable - Enable preemption of a task which is running.
 *
 * The xPreemptionDisable of the task will be set to pdFALSE.
 *
 * <b>Coverage</b>
 * @code{c}
 * if( xSchedulerRunning != pdFALSE )
 * {
 *     if( taskTASK_IS_RUNNING( pxTCB ) == pdTRUE )
 *     {
 *         xCoreID = ( BaseType_t ) pxTCB->xTaskRunState;
 *         prvYieldCore( xCoreID );
 *     }
 * }
 * @endcode
 * ( xSchedulerRunning != pdFALSE ) is true.
 * ( taskTASK_IS_RUNNING( pxTCB ) == pdTRUE ) is true.
 */
void test_coverage_vTaskPreemptionEnable_task_running( void )
{
    TCB_t xTaskTCB = { NULL };

    /* Setup variables. */
    xTaskTCB.xPreemptionDisable  = pdTRUE;
    xTaskTCB.xTaskRunState = 0;

    xSchedulerRunning = pdTRUE;

    /* Clear callback in commonSetUp. */
    vFakePortCheckIfInISR_StopIgnore();
    vFakePortEnterCriticalSection_StubWithCallback( NULL );
    vFakePortExitCriticalSection_StubWithCallback( NULL );
    vFakePortGetCoreID_StubWithCallback( NULL );

    /* Expectations. */
    vFakePortEnterCriticalSection_Expect();
    vFakePortCheckIfInISR_ExpectAndReturn( 1 ); /* Expection in prvYieldCore. */
    vFakePortGetCoreID_ExpectAndReturn( 0 );    /* Expection in prvYieldCore. */
    vFakePortExitCriticalSection_Expect();

    /* API call. */
    vTaskPreemptionEnable( &xTaskTCB );

    /* Validation. */
    TEST_ASSERT( xTaskTCB.xPreemptionDisable == pdFALSE );
}

/**
 * @brief vTaskCoreAffinityGet - Get the affinity mask of a task.
 *
 * Verify the affinity mask returned with a task handle.
 *
 * <b>Coverage</b>
 * @code{c}
 * taskENTER_CRITICAL();
 * {
 *     pxTCB = prvGetTCBFromHandle( xTask );
 *     uxCoreAffinityMask = pxTCB->uxCoreAffinityMask;
 * }
 * taskEXIT_CRITICAL();
 * @endcode
 * prvGetTCBFromHandle( xTask ) xTask is not NULL.
 */
void test_coverage_vTaskCoreAffinityGet( void )
{
    TCB_t xTaskTCB = { NULL };
    UBaseType_t uxCoreAffinityMask;

    /* Setup variables. */
    xTaskTCB.uxCoreAffinityMask = 0x5555;   /* The value to be verified later. */

    /* Clear callback in commonSetUp. */
    vFakePortEnterCriticalSection_StubWithCallback( NULL );
    vFakePortExitCriticalSection_StubWithCallback( NULL );

    /* Expectations. */
    vFakePortEnterCriticalSection_Expect();
    vFakePortExitCriticalSection_Expect();

    /* API call. */
    uxCoreAffinityMask = vTaskCoreAffinityGet( &xTaskTCB );

    /* Validation. */
    TEST_ASSERT( uxCoreAffinityMask == 0x5555 );
}

/**
 * @brief vTaskCoreAffinityGet - Get the affinity mask of current task.
 *
 * Verify the affinity mask returned with NULL task handle. Current task affinity
 * mask should be returned.
 *
 * <b>Coverage</b>
 * @code{c}
 * taskENTER_CRITICAL();
 * {
 *     pxTCB = prvGetTCBFromHandle( xTask );
 *     uxCoreAffinityMask = pxTCB->uxCoreAffinityMask;
 * }
 * taskEXIT_CRITICAL();
 * @endcode
 * prvGetTCBFromHandle( xTask ) xTask is NULL.
 */
void test_coverage_vTaskCoreAffinityGet_null_handle( void )
{
    TCB_t xTaskTCB = { NULL };
    UBaseType_t uxCoreAffinityMask;

    /* Setup variables. */
    xTaskTCB.uxCoreAffinityMask = 0x5555;   /* The value to be verified later. */
    pxCurrentTCBs[0] = &xTaskTCB;

    /* Clear callback in commonSetUp. */
    vFakePortEnterCriticalSection_StubWithCallback( NULL );
    vFakePortExitCriticalSection_StubWithCallback( NULL );

    /* Expectations. */
    vFakePortEnterCriticalSection_Expect();
    vFakePortExitCriticalSection_Expect();

    /* API call. */
    uxCoreAffinityMask = vTaskCoreAffinityGet( NULL );

    /* Validation. */
    TEST_ASSERT( uxCoreAffinityMask == 0x5555 );
}

/**
 * @brief uxTaskGetTaskNumber - get the task number of a task handle.
 *
 * Verify the task number returned by uxTaskGetTaskNumber.
 *
 * <b>Coverage</b>
 * @code{c}
 *     if( xTask != NULL )
 *     {
 *         pxTCB = xTask;
 *         uxReturn = pxTCB->uxTaskNumber;
 *     }
 *     else
 *     {
 *         uxReturn = 0U;
 *     }
 * @endcode
 * ( xTask != NULL ) is true.
 */
void test_coverage_uxTaskGetTaskNumber_task_handle( void )
{
    TCB_t xTaskTCB = { 0 };
    UBaseType_t uxTaskNumber = 0U;

    /* Setup the variables and structure. */
    xTaskTCB.uxTaskNumber = 0x5a5a;         /* Value to be verified later. */

    /* API call. */
    uxTaskNumber = uxTaskGetTaskNumber( &xTaskTCB );

    /* Validation. */
    TEST_ASSERT_EQUAL( 0x5a5a, uxTaskNumber );
}

/**
 * @brief uxTaskGetTaskNumber - get the task number of a NULL task handle.
 *
 * Verify the task number returned by uxTaskGetTaskNumber.
 *
 * <b>Coverage</b>
 * @code{c}
 *     if( xTask != NULL )
 *     {
 *         pxTCB = xTask;
 *         uxReturn = pxTCB->uxTaskNumber;
 *     }
 *     else
 *     {
 *         uxReturn = 0U;
 *     }
 * @endcode
 * ( xTask != NULL ) is false.
 */
void test_coverage_uxTaskGetTaskNumber_null_task_handle( void )
{
    UBaseType_t uxTaskNumber = 0x5a5a;

    /* API call. */
    uxTaskNumber = uxTaskGetTaskNumber( NULL );

    /* Validation. */
    TEST_ASSERT_EQUAL( 0U, uxTaskNumber );
}

/**
 * @brief vTaskSetTaskNumber - set the task number of a task handle.
 *
 * Verify the task number set by vTaskSetTaskNumber.
 *
 * <b>Coverage</b>
 * @code{c}
 * if( xTask != NULL )
 * {
 *     pxTCB = xTask;
 *     pxTCB->uxTaskNumber = uxHandle;
 * }
 * @endcode
 * ( xTask != NULL ) is true.
 */
void test_coverage_vTaskSetTaskNumber_task_handle( void )
{
    TCB_t xTaskTCB = { 0 };

    /* Setup the variables and structure. */
    xTaskTCB.uxTaskNumber = 0;

    /* API call. */
    vTaskSetTaskNumber( &xTaskTCB, 0x5a5a );

    /* Validation. */
    TEST_ASSERT_EQUAL( 0x5a5a, xTaskTCB.uxTaskNumber );
}

/**
 * @brief vTaskSetTaskNumber - set the task number of a task handle.
 *
 * The test show its result in the coverage report.
 *
 * <b>Coverage</b>
 * @code{c}
 * if( xTask != NULL )
 * {
 *     pxTCB = xTask;
 *     pxTCB->uxTaskNumber = uxHandle;
 * }
 * @endcode
 * ( xTask != NULL ) is false.
 */
void test_coverage_vTaskSetTaskNumber_null_task_handle( void )
{
    /* API call. */
    vTaskSetTaskNumber( NULL, 0x5a5a );

    /* Validation. */
    /* Nothing will be changed. This test shows its result in the coverage report. */
}

/*
The kernel will be configured as follows:
    #define configNUMBER_OF_CORES                               (N > 1)
    #define INCLUDE_uxTaskGetStackHighWaterMark             1

Coverage for 
    UBaseType_t uxTaskGetStackHighWaterMark( TaskHandle_t xTask )
        By passing a valid created Task
*/
void test_task_get_stack_high_water_mark( void )
{
    TaskHandle_t xTaskHandles[1] = { NULL };

    /* Create  tasks  */
    xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 2, &xTaskHandles[0] );

    vTaskStartScheduler();

    uxTaskGetStackHighWaterMark(xTaskHandles[0]);

}

/*
The kernel will be configured as follows:
    #define configNUMBER_OF_CORES                               (N > 1)
    #define INCLUDE_uxTaskGetStackHighWaterMark             1

Coverage for 
        UBaseType_t uxTaskGetStackHighWaterMark( TaskHandle_t xTask )
        By passing a NULL as a  Task
*/
void test_task_get_stack_high_water_mark_NULL_task( void )
{
    TaskHandle_t xTaskHandles[1] = { NULL };

    /* Create  tasks  */
    xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 2, &xTaskHandles[0] );

    vTaskStartScheduler();

    //NULL task for code coverage
    uxTaskGetStackHighWaterMark( NULL );

}

/**
 * @brief xTaskGetCurrentTaskHandleCPU - get current task handle with valid core ID.
 *
 * This test verifis the task handle returned with a valid core ID.
 *
 * <b>Coverage</b>
 * @code{c}
 * TaskHandle_t xTaskGetCurrentTaskHandleCPU( BaseType_t xCoreID )
 * {
 *     TaskHandle_t xReturn = NULL;
 *
 *     if( taskVALID_CORE_ID( xCoreID ) != pdFALSE )
 *     {
 *         xReturn = pxCurrentTCBs[ xCoreID ];
 *     }
 *
 *     return xReturn;
 * }
 * @endcode
 * ( taskVALID_CORE_ID( xCoreID ) != pdFALSE ) is true.
 */
void test_coverage_xTaskGetCurrentTaskHandleCPU_valid_core_id( void )
{
    TCB_t xTaskTCB = { 0 };
    TaskHandle_t xTaskHandle;

    /* Setup the variables and structure. */
    pxCurrentTCBs[ 0 ] = &xTaskTCB;

    /* API calls. */
    xTaskHandle = xTaskGetCurrentTaskHandleCPU( 0 );

    /* Validation. */
    TEST_ASSERT( xTaskHandle == &xTaskTCB );
}

/**
 * @brief xTaskGetCurrentTaskHandleCPU - get current task handle with invalid core ID.
 *
 * This test verifis the task handle returned with an invalid core ID.
 *
 * <b>Coverage</b>
 * @code{c}
 * TaskHandle_t xTaskGetCurrentTaskHandleCPU( BaseType_t xCoreID )
 * {
 *     TaskHandle_t xReturn = NULL;
 *
 *     if( taskVALID_CORE_ID( xCoreID ) != pdFALSE )
 *     {
 *         xReturn = pxCurrentTCBs[ xCoreID ];
 *     }
 *
 *     return xReturn;
 * }
 * @endcode
 * ( taskVALID_CORE_ID( xCoreID ) != pdFALSE ) is false.
 * xCoreID is greater than or equal to configNUMBER_OF_CORES.
 */
void test_coverage_xTaskGetCurrentTaskHandleCPU_invalid_core_id_ge( void )
{
    TCB_t xTaskTCB = { 0 };
    TaskHandle_t xTaskHandle;

    /* Setup the variables and structure. */
    pxCurrentTCBs[ 0 ] = &xTaskTCB;

    /* API calls. */
    xTaskHandle = xTaskGetCurrentTaskHandleCPU( configNUMBER_OF_CORES );

    /* Validation. */
    TEST_ASSERT( xTaskHandle == NULL );
}

/**
 * @brief xTaskGetCurrentTaskHandleCPU - get current task handle with invalid core ID.
 *
 * This test verifis the task handle returned with an invalid core ID.
 *
 * <b>Coverage</b>
 * @code{c}
 * TaskHandle_t xTaskGetCurrentTaskHandleCPU( BaseType_t xCoreID )
 * {
 *     TaskHandle_t xReturn = NULL;
 *
 *     if( taskVALID_CORE_ID( xCoreID ) != pdFALSE )
 *     {
 *         xReturn = pxCurrentTCBs[ xCoreID ];
 *     }
 *
 *     return xReturn;
 * }
 * @endcode
 * ( taskVALID_CORE_ID( xCoreID ) != pdFALSE ) is false.
 * xCoreID is less than 0.
 */
void test_coverage_xTaskGetCurrentTaskHandleCPU_invalid_core_id_lt( void )
{
    TCB_t xTaskTCB = { 0 };
    TaskHandle_t xTaskHandle;

    /* Setup the variables and structure. */
    pxCurrentTCBs[ 0 ] = &xTaskTCB;

    /* API calls. */
    xTaskHandle = xTaskGetCurrentTaskHandleCPU( -1 );

    /* Validation. */
    TEST_ASSERT( xTaskHandle == NULL );
}

/**
 * @brief vTaskList - No task is created.
 *
 * This API is called before any task is created.
 *
 * <b>Coverage</b>
 * @code{c}
 * if( pxTaskStatusArray != NULL )
 * {
 *     ...
 * }
 * @endcode
 * ( pxTaskStatusArray != NULL ) is false.
 */
void test_coverage_vTaskList_no_task_created( void )
{
    char pcWriteBuffer[ TEST_VTASKLIST_BUFFER_SIZE ] = "Test"; /* Validate the string is overwritten in the API call. */

    /* Setup the variables and structure. */
    uxCurrentNumberOfTasks = 0;         /* No task is created. */
    UnityMalloc_StartTest();

    /* API calls. */
    vTaskList( pcWriteBuffer );

    /* Validation. */
    /* Verify the malloc allocate count. */
    UnityMalloc_EndTest();
    /* No task is created. A string with zero legnth is returned. */
    TEST_ASSERT_EQUAL( 0x00, pcWriteBuffer[ 0 ] );
}

/**
 * @brief vTaskList - Task with state eRunning.
 *
 * <b>Coverage</b>
 * @code{c}
 * switch( pxTaskStatusArray[ x ].eCurrentState )
 * {
 *     ...
 *     case eRunning:
 *         cStatus = tskRUNNING_CHAR;
 *         break;
 *     ...
 * }
 * @endcode
 * ( pxTaskStatusArray[ x ].eCurrentState ) is eRunning.
 */
void test_coverage_vTaskList_task_eRunning( void )
{
    TCB_t xTaskTCB = { NULL };
    char pcExpectedResult[ TEST_VTASKLIST_BUFFER_SIZE ] = { 0 };
    char pcWriteBuffer[ TEST_VTASKLIST_BUFFER_SIZE ] = "Test"; /* Validate the string is overwritten in the API call. */
    int xStringCompareResult;
    char pcGeneratedTaskName[ configMAX_TASK_NAME_LEN ];
    uint32_t i;
 
    /* Setup the variables and structure. */
    xSchedulerRunning = pdTRUE;

    /* Create one task with state eDeleted. */
    xTaskTCB.uxPriority = tskIDLE_PRIORITY;
    xTaskTCB.pcTaskName[ 0 ] = '\0';
    xTaskTCB.xStateListItem.pvOwner = &xTaskTCB;
    xTaskTCB.uxCoreAffinityMask = ( ( 1U << configNUMBER_OF_CORES ) - 1U );
    xTaskTCB.uxTaskAttributes = -1;
    xTaskTCB.xTaskRunState = 0;
    xTaskTCB.uxTaskNumber = 0;
    pxCurrentTCBs[ 0 ] = &xTaskTCB;
    xTaskTCB.xStateListItem.pxContainer = &pxReadyTasksLists[ tskIDLE_PRIORITY ];
    listINSERT_END( &pxReadyTasksLists[ tskIDLE_PRIORITY ], &xTaskTCB.xStateListItem );
    prvInitialiseTestStack( &xTaskTCB, configMINIMAL_STACK_SIZE );
    uxCurrentNumberOfTasks = uxCurrentNumberOfTasks + 1;
    
    /* API calls. */
    vTaskList( pcWriteBuffer );
    
    /* Clean up malloc for stack. */
    vPortFreeStack( xTaskTCB.pxStack );

    /* Validation. */
    /* Verify the malloc allocate count. */
    UnityMalloc_EndTest();

    /* Verify the returned string. */
    for( i = 0; i < ( configMAX_TASK_NAME_LEN - 1 ); i++ )
    {
        pcGeneratedTaskName[ i ] = ' ';
    }
    pcGeneratedTaskName[ i ] = '\0';

    sprintf( pcExpectedResult, "%s\t%c\t%u\t%u\t%u\r\n", pcGeneratedTaskName, tskRUNNING_CHAR,
        ( unsigned int ) xTaskTCB.uxPriority, ( unsigned int ) ( configMINIMAL_STACK_SIZE - 1U ),
        ( unsigned int ) xTaskTCB.uxTaskNumber );
    xStringCompareResult = strcmp( pcExpectedResult, pcWriteBuffer );
    TEST_ASSERT_EQUAL( 0, xStringCompareResult );
}

/**
 * @brief vTaskList - Task with state eReady.
 *
 * <b>Coverage</b>
 * @code{c}
 * switch( pxTaskStatusArray[ x ].eCurrentState )
 * {
 *     ...
 *     case eReady:
 *         cStatus = tskREADY_CHAR;
 *         break;
 *     ...
 * }
 * @endcode
 * ( pxTaskStatusArray[ x ].eCurrentState ) is eReady.
 */
void test_coverage_vTaskList_task_eReady( void )
{
    TCB_t xTaskTCB = { NULL };
    char pcExpectedResult[ TEST_VTASKLIST_BUFFER_SIZE ] = { 0 };
    char pcWriteBuffer[ TEST_VTASKLIST_BUFFER_SIZE ] = "Test"; /* Validate the string is overwritten in the API call. */
    int xStringCompareResult;
    char pcGeneratedTaskName[ configMAX_TASK_NAME_LEN ];
    uint32_t i;
 
    /* Setup the variables and structure. */
    xSchedulerRunning = pdTRUE;

    /* Create one task with state eDeleted. */
    xTaskTCB.uxPriority = tskIDLE_PRIORITY;
    xTaskTCB.pcTaskName[ 0 ] = '\0';
    xTaskTCB.xStateListItem.pvOwner = &xTaskTCB;
    xTaskTCB.uxCoreAffinityMask = ( ( 1U << configNUMBER_OF_CORES ) - 1U );
    xTaskTCB.uxTaskAttributes = -1;
    xTaskTCB.xTaskRunState = taskTASK_NOT_RUNNING;
    xTaskTCB.uxTaskNumber = 0;
    pxCurrentTCBs[ 0 ] = &xTaskTCB;
    xTaskTCB.xStateListItem.pxContainer = &pxReadyTasksLists[ tskIDLE_PRIORITY ];
    listINSERT_END( &pxReadyTasksLists[ tskIDLE_PRIORITY ], &xTaskTCB.xStateListItem );
    prvInitialiseTestStack( &xTaskTCB, configMINIMAL_STACK_SIZE );
    uxCurrentNumberOfTasks = uxCurrentNumberOfTasks + 1;
    
    /* API calls. */
    vTaskList( pcWriteBuffer );
    
    /* Clean up malloc for stack. */
    vPortFreeStack( xTaskTCB.pxStack );

    /* Validation. */
    /* Verify the malloc allocate count. */
    UnityMalloc_EndTest();

    /* Verify the returned string. */
    for( i = 0; i < ( configMAX_TASK_NAME_LEN - 1 ); i++ )
    {
        pcGeneratedTaskName[ i ] = ' ';
    }
    pcGeneratedTaskName[ i ] = '\0';

    sprintf( pcExpectedResult, "%s\t%c\t%u\t%u\t%u\r\n", pcGeneratedTaskName, tskREADY_CHAR,
        ( unsigned int ) xTaskTCB.uxPriority, ( unsigned int ) ( configMINIMAL_STACK_SIZE - 1U ),
        ( unsigned int ) xTaskTCB.uxTaskNumber );
    xStringCompareResult = strcmp( pcExpectedResult, pcWriteBuffer );
    TEST_ASSERT_EQUAL( 0, xStringCompareResult );
}

/**
 * @brief vTaskList - Task with state eBlocked.
 *
 * <b>Coverage</b>
 * @code{c}
 * switch( pxTaskStatusArray[ x ].eCurrentState )
 * {
 *     ...
 *     case eBlocked:
 *         cStatus = tskBLOCKED_CHAR;
 *         break;
 *     ...
 * }
 * @endcode
 * ( pxTaskStatusArray[ x ].eCurrentState ) is eBlocked.
 */
void test_coverage_vTaskList_task_eBlocked( void )
{
    TCB_t xTaskTCB = { NULL };
    char pcExpectedResult[ TEST_VTASKLIST_BUFFER_SIZE ] = { 0 };
    char pcWriteBuffer[ TEST_VTASKLIST_BUFFER_SIZE ] = "Test"; /* Validate the string is overwritten in the API call. */
    int xStringCompareResult;
    char pcGeneratedTaskName[ configMAX_TASK_NAME_LEN ];
    uint32_t i;
 
    /* Setup the variables and structure. */
    xSchedulerRunning = pdTRUE;

    /* Create one task with state eDeleted. */
    xTaskTCB.uxPriority = tskIDLE_PRIORITY;
    xTaskTCB.pcTaskName[ 0 ] = '\0';
    xTaskTCB.xStateListItem.pvOwner = &xTaskTCB;
    xTaskTCB.uxCoreAffinityMask = ( ( 1U << configNUMBER_OF_CORES ) - 1U );
    xTaskTCB.uxTaskAttributes = -1;
    xTaskTCB.xTaskRunState = taskTASK_NOT_RUNNING;
    xTaskTCB.uxTaskNumber = 0;
    pxCurrentTCBs[ 0 ] = &xTaskTCB;
    xTaskTCB.xStateListItem.pxContainer = pxDelayedTaskList;
    listINSERT_END( pxDelayedTaskList, &xTaskTCB.xStateListItem );
    prvInitialiseTestStack( &xTaskTCB, configMINIMAL_STACK_SIZE );
    uxCurrentNumberOfTasks = uxCurrentNumberOfTasks + 1;
    
    /* API calls. */
    vTaskList( pcWriteBuffer );
    
    /* Clean up malloc for stack. */
    vPortFreeStack( xTaskTCB.pxStack );

    /* Validation. */
    /* Verify the malloc allocate count. */
    UnityMalloc_EndTest();

    /* Verify the returned string. */
    for( i = 0; i < ( configMAX_TASK_NAME_LEN - 1 ); i++ )
    {
        pcGeneratedTaskName[ i ] = ' ';
    }
    pcGeneratedTaskName[ i ] = '\0';

    sprintf( pcExpectedResult, "%s\t%c\t%u\t%u\t%u\r\n", pcGeneratedTaskName, tskBLOCKED_CHAR,
        ( unsigned int ) xTaskTCB.uxPriority, ( unsigned int ) ( configMINIMAL_STACK_SIZE - 1U ),
        ( unsigned int ) xTaskTCB.uxTaskNumber );
    xStringCompareResult = strcmp( pcExpectedResult, pcWriteBuffer );
    TEST_ASSERT_EQUAL( 0, xStringCompareResult );
}

/**
 * @brief vTaskList - Task with state eSuspended.
 *
 * <b>Coverage</b>
 * @code{c}
 * switch( pxTaskStatusArray[ x ].eCurrentState )
 * {
 *     ...
 *     case eSuspended:
 *         cStatus = tskSUSPENDED_CHAR;
 *         break;
 *     ...
 * }
 * @endcode
 * ( pxTaskStatusArray[ x ].eCurrentState ) is eSuspended.
 */
void test_coverage_vTaskList_task_eSuspended( void )
{
    TCB_t xTaskTCB = { NULL };
    char pcExpectedResult[ TEST_VTASKLIST_BUFFER_SIZE ] = { 0 };
    char pcWriteBuffer[ TEST_VTASKLIST_BUFFER_SIZE ] = "Test"; /* Validate the string is overwritten in the API call. */
    int xStringCompareResult;
    char pcGeneratedTaskName[ configMAX_TASK_NAME_LEN ];
    uint32_t i;
 
    /* Setup the variables and structure. */
    xSchedulerRunning = pdTRUE;

    /* Create one task with state eDeleted. */
    xTaskTCB.uxPriority = tskIDLE_PRIORITY;
    xTaskTCB.pcTaskName[ 0 ] = '\0';
    xTaskTCB.xStateListItem.pvOwner = &xTaskTCB;
    xTaskTCB.uxCoreAffinityMask = ( ( 1U << configNUMBER_OF_CORES ) - 1U );
    xTaskTCB.uxTaskAttributes = -1;
    xTaskTCB.xTaskRunState = taskTASK_NOT_RUNNING;
    xTaskTCB.uxTaskNumber = 0;
    pxCurrentTCBs[ 0 ] = &xTaskTCB;
    xTaskTCB.xStateListItem.pxContainer = &xSuspendedTaskList;
    listINSERT_END( &xSuspendedTaskList, &xTaskTCB.xStateListItem );
    prvInitialiseTestStack( &xTaskTCB, configMINIMAL_STACK_SIZE );
    uxCurrentNumberOfTasks = uxCurrentNumberOfTasks + 1;
    
    /* API calls. */
    vTaskList( pcWriteBuffer );
    
    /* Clean up malloc for stack. */
    vPortFreeStack( xTaskTCB.pxStack );

    /* Validation. */
    /* Verify the malloc allocate count. */
    UnityMalloc_EndTest();

    /* Verify the returned string. */
    for( i = 0; i < ( configMAX_TASK_NAME_LEN - 1 ); i++ )
    {
        pcGeneratedTaskName[ i ] = ' ';
    }
    pcGeneratedTaskName[ i ] = '\0';

    sprintf( pcExpectedResult, "%s\t%c\t%u\t%u\t%u\r\n", pcGeneratedTaskName, tskSUSPENDED_CHAR,
        ( unsigned int ) xTaskTCB.uxPriority, ( unsigned int ) ( configMINIMAL_STACK_SIZE - 1U ),
        ( unsigned int ) xTaskTCB.uxTaskNumber );
    xStringCompareResult = strcmp( pcExpectedResult, pcWriteBuffer );
    TEST_ASSERT_EQUAL( 0, xStringCompareResult );
}

/**
 * @brief vTaskList - Task with state eDeleted.
 *
 * <b>Coverage</b>
 * @code{c}
 * switch( pxTaskStatusArray[ x ].eCurrentState )
 * {
 *     ...
 *     case eDeleted:
 *         cStatus = tskDELETED_CHAR;
 *         break;
 *     ...
 * }
 * @endcode
 * ( pxTaskStatusArray[ x ].eCurrentState ) is eDeleted.
 */
void test_coverage_vTaskList_task_eDeleted( void )
{
    TCB_t xTaskTCB = { NULL };
    char pcExpectedResult[ TEST_VTASKLIST_BUFFER_SIZE ] = { 0 };
    char pcWriteBuffer[ TEST_VTASKLIST_BUFFER_SIZE ] = "Test"; /* Validate the string is overwritten in the API call. */
    int xStringCompareResult;
    char pcGeneratedTaskName[ configMAX_TASK_NAME_LEN ];
    uint32_t i;
 
    /* Setup the variables and structure. */
    xSchedulerRunning = pdTRUE;

    /* Create one task with state eDeleted. */
    xTaskTCB.uxPriority = tskIDLE_PRIORITY;
    xTaskTCB.pcTaskName[ 0 ] = '\0';
    xTaskTCB.xStateListItem.pvOwner = &xTaskTCB;
    xTaskTCB.uxCoreAffinityMask = ( ( 1U << configNUMBER_OF_CORES ) - 1U );
    xTaskTCB.uxTaskAttributes = -1;
    xTaskTCB.xTaskRunState = taskTASK_NOT_RUNNING;
    xTaskTCB.uxTaskNumber = 0;
    pxCurrentTCBs[ 0 ] = &xTaskTCB;
    xTaskTCB.xStateListItem.pxContainer = &xTasksWaitingTermination;
    listINSERT_END( &xTasksWaitingTermination, &xTaskTCB.xStateListItem );
    prvInitialiseTestStack( &xTaskTCB, configMINIMAL_STACK_SIZE );
    uxCurrentNumberOfTasks = uxCurrentNumberOfTasks + 1;
    
    /* API calls. */
    vTaskList( pcWriteBuffer );
    
    /* Clean up malloc for stack. */
    vPortFreeStack( xTaskTCB.pxStack );

    /* Validation. */
    /* Verify the malloc allocate count. */
    UnityMalloc_EndTest();

    /* Verify the returned string. */
    for( i = 0; i < ( configMAX_TASK_NAME_LEN - 1 ); i++ )
    {
        pcGeneratedTaskName[ i ] = ' ';
    }
    pcGeneratedTaskName[ i ] = '\0';

    sprintf( pcExpectedResult, "%s\t%c\t%u\t%u\t%u\r\n", pcGeneratedTaskName, tskDELETED_CHAR,
        ( unsigned int ) xTaskTCB.uxPriority, ( unsigned int ) ( configMINIMAL_STACK_SIZE - 1U ),
        ( unsigned int ) xTaskTCB.uxTaskNumber );
    xStringCompareResult = strcmp( pcExpectedResult, pcWriteBuffer );
    TEST_ASSERT_EQUAL( 0, xStringCompareResult );
}

/*
The kernel will be configured as follows:
    #define configNUMBER_OF_CORES                               (N > 1)
    #define INCLUDE_xTaskDelayUntil                          1

Coverage for: 
        BaseType_t xTaskDelayUntil( TickType_t * const pxPreviousWakeTime,
                                    const TickType_t xTimeIncrement )
*/
void test_task_delay_until_with_config_assert( void )
{
    TaskHandle_t xTaskHandles[configNUMBER_OF_CORES] = { NULL };
    uint32_t i;
    TickType_t previousWakeTime = xTickCount - 3;

    /* Create tasks of equal priority for all available CPU cores */
    for (i = 0; i < configNUMBER_OF_CORES; i++) {
        xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 2, &xTaskHandles[i] );
    }

    vTaskStartScheduler();

    xTaskDelayUntil( &previousWakeTime , 4 );
    
}

/**
 * @brief prvAddNewTaskToReadyList - add a newly created task to the list of ready tasks
 *
 * This test creates two tasks, the second after suspending the first and then
 * starts the scheduler.
 *
 * <b>Coverage</b>
 * @code{c}
 * if( uxCurrentNumberOfTasks == ( UBaseType_t ) 1 )
 * @endcode
 * As two tasks arecreated, this covers both branches of the above conditional
 * in addition to the function body.
 */
void test_coverage_prvAddNewTaskToReadyList_create_two_tasks_with_the_first_suspended( void )
{
    TaskHandle_t xTaskHandles[configNUMBER_OF_CORES] = { NULL };

    xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 1, &xTaskHandles[0] );
    vTaskSuspend(xTaskHandles[0]);

    xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 1, &xTaskHandles[1] );

    vTaskStartScheduler();
}

/**
 * @brief prvAddNewTaskToReadyList - add a new idle task to the list of ready tasks
 *
 * This test covers the prvAddNewTaskToReadyList for SMP, which is surrounded by
 * ( configNUMBER_OF_CORES > 1 ). More tasks than cores are created to test the for
 * loop condition when the scheduler is not running.
 *
 * <b>Coverage</b>
 * @code{c}
 * for( xCoreID = 0; xCoreID < configNUMBER_OF_CORES; xCoreID++ )
 * @endcode
 * for loop condition ( xCoreID < configNUMBER_OF_CORES ) is false.
 */
void test_coverage_prvAddNewTaskToReadyList_create_more_idle_tasks_than_cores( void )
{
    TCB_t xTaskTCBs[ configNUMBER_OF_CORES + 1 ] = { 0 };
    uint32_t i;

    /* Setup the variables and structure. */
    /* Initialize the idle priority ready list and set top ready priority to idle priority. */
    uxTopReadyPriority = tskIDLE_PRIORITY;
    uxCurrentNumberOfTasks = 0;
    xSchedulerRunning = pdFALSE;

    /* Create idle tasks and add it into the ready list. Create one more idle priority level
     * in the loop. */
    for( i = 0; i < ( configNUMBER_OF_CORES + 1U ); i++ )
    {
        xTaskTCBs[ i ].uxPriority = tskIDLE_PRIORITY;
        xTaskTCBs[ i ].xStateListItem.pvOwner = &xTaskTCBs[ i ];
        xTaskTCBs[ i ].uxCoreAffinityMask = ( ( 1U << configNUMBER_OF_CORES ) - 1U );
        xTaskTCBs[ i ].uxTaskAttributes = -1;
        if( i < configNUMBER_OF_CORES )
        {
            /* Create idle tasks with equal number of cores. */
            pxCurrentTCBs[ i ] = &xTaskTCBs[ i ];
            xTaskTCBs[ i ].xTaskRunState = i;
            xTaskTCBs[ i ].xStateListItem.pxContainer = &pxReadyTasksLists[ tskIDLE_PRIORITY ];
            listINSERT_END( &pxReadyTasksLists[ tskIDLE_PRIORITY ], &xTaskTCBs[ i ].xStateListItem );
            uxCurrentNumberOfTasks = uxCurrentNumberOfTasks + 1;
        }
        else
        {
            /* Create one more idle task to be added to ready list. */
            xTaskTCBs[ i ].xTaskRunState = taskTASK_NOT_RUNNING;
        }
    }

    /* API calls. */
    prvAddNewTaskToReadyList( &xTaskTCBs[ configNUMBER_OF_CORES ] );

    /* Validations. The run state of this task is still taskTASK_NOT_RUNNING. */
    configASSERT( xTaskTCBs[ configNUMBER_OF_CORES + 1U ].xTaskRunState == taskTASK_NOT_RUNNING );
}

/**
 * @brief vTaskCoreAffinitySet - limit a task to a set of cores via a bitmask.
 *
 * This test calles vTaskCoreAffinitySet with a NULL task, implicitly referencing the
 * current task and setting the mask to 0xFF with the secheduler running.
 *
 * <b>Coverage</b>
 * @code{c}
 * pxTCB = prvGetTCBFromHandle( xTask );
 * ...
 * if( xSchedulerRunning != pdFALSE )
 *          {
 *              if( taskTASK_IS_RUNNING( pxTCB ) == pdTRUE )
 * ...
 * @endcode
 */
void test_coverage_vTaskCoreAffinitySet_task_core_affinity_set_task_implied( void )
{
    TaskHandle_t xTaskHandles[configNUMBER_OF_CORES] = { NULL };
    UBaseType_t xidx;

    xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 1, &xTaskHandles[0] );

    vTaskStartScheduler();

    for (xidx = 0; xidx < configNUMBER_OF_CORES ; xidx++) {
        xTaskIncrementTick_helper();
    }

    vTaskCoreAffinitySet(NULL, (UBaseType_t)0xFF);
}

/**
 * @brief vTaskCoreAffinitySet - limit a task to a set of cores via a bitmask.
 *
 * This test calles vTaskCoreAffinitySet with an explicit task reference
 * setting the mask to 0xFF adn then starting the scheduler.
 *
 * <b>Coverage</b>
 * @code{c}
 * pxTCB = prvGetTCBFromHandle( xTask );
 * ...
 * if( xSchedulerRunning != pdFALSE )
 *          {
 *              if( taskTASK_IS_RUNNING( pxTCB ) == pdTRUE )
 * ...
 * @endcode
 */
void test_coverage_vTaskCoreAffinitySet_task_core_affinity_set_task_explicit( void )
{
    TaskHandle_t xTaskHandles[configNUMBER_OF_CORES] = { NULL };

    xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 1, &xTaskHandles[0]);
    vTaskCoreAffinitySet(xTaskHandles[0], (UBaseType_t)0xFF);

    vTaskStartScheduler();
}

/**
 * @brief vTaskCoreAffinitySet - limit a task to a set of cores via a bitmask.
 *
 * This test calles vTaskCoreAffinitySet with an explicit task reference
 * setting the mask to one value initially, and then changing the mask while
 * the scheduler is active and the task is running.
 *
 * <b>Coverage</b>
 * @code{c}
 *                   if( ( uxCoreAffinityMask & ( 1 << xCoreID ) ) == 0 )
 *                   {
 *                       prvYieldCore( xCoreID );
 *                   }
 * ...
 * @endcode
 */
void test_coverage_vTaskCoreAffinitySet_task_core_affinity_change_while_running( void )
{
    TaskHandle_t xTaskHandles[configNUMBER_OF_CORES] = { NULL };
    UBaseType_t xidx;

    xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 1, &xTaskHandles[0]);
    vTaskCoreAffinitySet(xTaskHandles[0], (UBaseType_t)0x1);

    vTaskStartScheduler();

    for (xidx = 0; xidx < configNUMBER_OF_CORES ; xidx++) {
        xTaskIncrementTick_helper();
    }

    vTaskCoreAffinitySet(xTaskHandles[0], (UBaseType_t)0x2);

    for (xidx = 0; xidx < configNUMBER_OF_CORES ; xidx++) {
        xTaskIncrementTick_helper();
    }
}

/**
 * @brief vTaskCoreAffinitySet - limit a task to a set of cores via a bitmask.
 *
 * This test calles vTaskCoreAffinitySet with an explicit task reference
 * setting the mask to one value initially, and then re-setting the mask to
 * the same value while the scheduler is active and the task is running.
 *
 * <b>Coverage</b>
 * @code{c}
 *                   if( ( uxCoreAffinityMask & ( 1 << xCoreID ) ) == 0 )
 *                   {
 *                       prvYieldCore( xCoreID );
 *                   }
 * ...
 * @endcode
 */
void test_coverage_vTaskCoreAffinitySet_task_core_affinity_change_while_suspended( void )
{
    TaskHandle_t xTaskHandles[configNUMBER_OF_CORES] = { NULL };
    UBaseType_t xidx;

    xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 1, &xTaskHandles[0]);
    vTaskCoreAffinitySet(xTaskHandles[0], (UBaseType_t)0x1);

    vTaskStartScheduler();

    for (xidx = 0; xidx < configNUMBER_OF_CORES ; xidx++) {
        xTaskIncrementTick_helper();
    }

    vTaskSuspend(xTaskHandles[0]);

    for (xidx = 0; xidx < configNUMBER_OF_CORES ; xidx++) {
        xTaskIncrementTick_helper();
    }

    vTaskCoreAffinitySet(xTaskHandles[0], (UBaseType_t)0x2);

    for (xidx = 0; xidx < configNUMBER_OF_CORES ; xidx++) {
        xTaskIncrementTick_helper();
    }

    vTaskCoreAffinitySet(xTaskHandles[0], (UBaseType_t)0x2);

    for (xidx = 0; xidx < configNUMBER_OF_CORES ; xidx++) {
        xTaskIncrementTick_helper();
    }
}

/**
 * @brief prvYieldForTask - running task with xTaskRunState equals to configNUMBER_OF_CORES.
 *
 * Yield for a task of equal priority. No other task should be requested to yield.
 *
 * <b>Coverage</b>
 * @code{c}
 * if( ( taskTASK_IS_RUNNING( pxCurrentTCBs[ xCoreID ] ) != pdFALSE ) && ( xYieldPendings[ xCoreID ] == pdFALSE ) )
 * {
 *     if( xCurrentCoreTaskPriority <= xLowestPriorityToPreempt )
 *     {
 * @endcode
 * ( taskTASK_IS_RUNNING( pxCurrentTCBs[ xCoreID ] ) != pdFALSE ) is false.
 */
void test_coverage_prvYieldForTask_task_is_running_eq( void )
{
    TCB_t xTaskTCBs[ configNUMBER_OF_CORES + 1U ] = { NULL };
    uint32_t i;

    /* Setup the variables and structure. */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        xTaskTCBs[ i ].uxPriority = 1;
        xTaskTCBs[ i ].xTaskRunState = i;
        xYieldPendings[ i ] = pdFALSE;
        pxCurrentTCBs[ i ] = &xTaskTCBs[ i ];
    }
    /* Set one of the running xTaskRunState equals to configNUMBER_OF_CORES. */
    xTaskTCBs[ 0 ].xTaskRunState = configNUMBER_OF_CORES;

    /* Create one more task with equal priority. */
    xTaskTCBs[ configNUMBER_OF_CORES ].uxPriority = 1;

    /* API call. */
    prvYieldForTask( &xTaskTCBs[ configNUMBER_OF_CORES ] );

    /* Validation. */
    /* Core 0 will not be requested to yield. */
    TEST_ASSERT( xTaskTCBs[ 0 ].xTaskRunState != taskTASK_YIELDING );
    /* No core will be requested to yield. */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        TEST_ASSERT( xYieldPendings[ i ] != pdTRUE );
    }
}

/**
 * @brief prvYieldForTask - running task with xTaskRunState is taskTASK_YIELDING.
 *
 * Yield for a task of equal priority. No other task should be requested to yield.
 *
 * <b>Coverage</b>
 * @code{c}
 * if( ( taskTASK_IS_RUNNING( pxCurrentTCBs[ xCoreID ] ) != pdFALSE ) && ( xYieldPendings[ xCoreID ] == pdFALSE ) )
 * {
 *     if( xCurrentCoreTaskPriority <= xLowestPriorityToPreempt )
 *     {
 * @endcode
 * ( taskTASK_IS_RUNNING( pxCurrentTCBs[ xCoreID ] ) != pdFALSE ) is false.
 */
void test_coverage_prvYieldForTask_task_yielding( void )
{
    TCB_t xTaskTCBs[ configNUMBER_OF_CORES + 1U ] = { NULL };
    uint32_t i;

    /* Setup the variables and structure. */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        xTaskTCBs[ i ].uxPriority = 1;
        xTaskTCBs[ i ].xTaskRunState = i;
        xYieldPendings[ i ] = pdFALSE;
        pxCurrentTCBs[ i ] = &xTaskTCBs[ i ];
    }
    /* Set xTaskRunState of the running task to taskTASK_YIELDING. */
    xTaskTCBs[ 0 ].xTaskRunState = taskTASK_YIELDING;

    /* Create one more task with equal priority. */
    xTaskTCBs[ configNUMBER_OF_CORES ].uxPriority = 1;

    /* API call. */
    prvYieldForTask( &xTaskTCBs[ configNUMBER_OF_CORES ] );

    /* Validation. */
    /* Core 0 remains of state taskTASK_YIELDING. */
    TEST_ASSERT( xTaskTCBs[ 0 ].xTaskRunState == taskTASK_YIELDING );
    /* No core will be requested to yield. */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        TEST_ASSERT( xYieldPendings[ i ] != pdTRUE );
    }
}

/**
 * @brief prvYieldForTask - running task with yield pending.
 *
 * Yield for a task of equal priority. No other task should be requested to yield.
 *
 * <b>Coverage</b>
 * @code{c}
 * if( ( taskTASK_IS_RUNNING( pxCurrentTCBs[ xCoreID ] ) != pdFALSE ) && ( xYieldPendings[ xCoreID ] == pdFALSE ) )
 * {
 *     if( xCurrentCoreTaskPriority <= xLowestPriorityToPreempt )
 *     {
 * @endcode
 * ( xYieldPendings[ xCoreID ] == pdFALSE ) is false.
 */
void test_coverage_prvYieldForTask_task_yield_pending( void )
{
    TCB_t xTaskTCBs[ configNUMBER_OF_CORES + 1U ] = { NULL };
    uint32_t i;

    /* Setup the variables and structure. */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        xTaskTCBs[ i ].uxPriority = 1;
        xTaskTCBs[ i ].xTaskRunState = i;
        xYieldPendings[ i ] = pdFALSE;
        pxCurrentTCBs[ i ] = &xTaskTCBs[ i ];
    }
    /* Set one of the running core with yield pending. */
    xYieldPendings[ 0 ] = pdTRUE;

    /* Create one more task with equal priority. */
    xTaskTCBs[ configNUMBER_OF_CORES ].uxPriority = 1;

    /* API call. */
    prvYieldForTask( &xTaskTCBs[ configNUMBER_OF_CORES ] );

    /* Validation. */
    /* Core 0 remains yield pending. */
    TEST_ASSERT( xYieldPendings[ 0 ] == pdTRUE );
    /* Other core will not be requested to yield. */
    for( i = 1; i < configNUMBER_OF_CORES; i++ )
    {
        TEST_ASSERT( xYieldPendings[ i ] != pdTRUE );
    }
}

/**
 * @brief xTaskRemoveFromEventList - Remove a equal priority task from event list.
 *
 * The task is removed from event list. Verified this task is put back to ready list 
 * and removed from event list. Current core is not requested to yield.
 *
 * <b>Coverage</b>
 * @code{c}
 * #else
 * {
 *     xReturn = pdFALSE;
 *
 *     #if ( configUSE_PREEMPTION == 1 )
 *     {
 *         prvYieldForTask( pxUnblockedTCB );
 *
 *         if( xYieldPendings[ portGET_CORE_ID() ] != pdFALSE )
 *         {
 *             xReturn = pdTRUE;
 *         }
 *     }
 *     #endif
 * }
 * #endif
 * @endcode
 * ( xYieldPendings[ portGET_CORE_ID() ] != pdFALSE ) is false.
 */
void test_coverage_xTaskRemoveFromEventList_remove_eq_priority_task( void )
{
    TCB_t xTaskTCB = { NULL };
    TCB_t xTaskTCBs[ configNUMBER_OF_CORES ] = { NULL };
    List_t xEventList = { 0 };
    uint32_t i;
    BaseType_t xReturn;

    /* Setup the variables and structure. */
    uxSchedulerSuspended = pdFALSE;
    uxTopReadyPriority = tskIDLE_PRIORITY;
    vListInitialise( &xEventList );
    vListInitialise( &( pxReadyTasksLists[ tskIDLE_PRIORITY ] ) );
    vListInitialise( &xSuspendedTaskList );
    vListInitialise( &xDelayedTaskList1 );
    pxDelayedTaskList = &xDelayedTaskList1;

    /* Create idle tasks and add it into the ready list. */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        xTaskTCBs[ i ].uxPriority = tskIDLE_PRIORITY;
        xTaskTCBs[ i ].xStateListItem.pvOwner = &xTaskTCBs[ i ];
        xTaskTCBs[ i ].uxCoreAffinityMask = ( ( 1U << configNUMBER_OF_CORES ) - 1U );
        xTaskTCBs[ i ].uxTaskAttributes = taskATTRIBUTE_IS_IDLE;

        /* Create idle tasks with equal number of cores. */
        pxCurrentTCBs[ i ] = &xTaskTCBs[ i ];
        xTaskTCBs[ i ].xTaskRunState = i;
        xTaskTCBs[ i ].xStateListItem.pxContainer = &pxReadyTasksLists[ tskIDLE_PRIORITY ];
        listINSERT_END( &pxReadyTasksLists[ tskIDLE_PRIORITY ], &xTaskTCBs[ i ].xStateListItem );
        uxCurrentNumberOfTasks = uxCurrentNumberOfTasks + 1;
    }

    /* Create one more task to be removed from event list. */
    xTaskTCB.uxPriority = tskIDLE_PRIORITY;
    xTaskTCB.xStateListItem.pxContainer = &xSuspendedTaskList;
    xTaskTCB.xStateListItem.pvOwner = &xTaskTCB;
    listINSERT_END( &xSuspendedTaskList, &xTaskTCB.xStateListItem );
    xTaskTCB.xEventListItem.pxContainer = &xEventList;
    xTaskTCB.xEventListItem.pvOwner = &xTaskTCB;
    listINSERT_END( &xEventList, &xTaskTCB.xEventListItem );
    xTaskTCB.xTaskRunState = taskTASK_NOT_RUNNING;
    xTaskTCB.uxCoreAffinityMask = ( ( 1U << configNUMBER_OF_CORES ) - 1U );
    uxCurrentNumberOfTasks = uxCurrentNumberOfTasks + 1;

    /* Expectations. */
    vFakePortGetCoreID_StubWithCallback( NULL );
    vFakePortGetCoreID_ExpectAndReturn( 0 );    /* Get portGET_CRITICAL_NESTING_COUNT. */
    vFakePortGetCoreID_ExpectAndReturn( 0 );    /* Get prvYieldCore. */
    vFakePortGetCoreID_ExpectAndReturn( 0 );    /* Get portGET_CRITICAL_NESTING_COUNT. */
    vFakePortGetCoreID_ExpectAndReturn( 0 );    /* Get xYieldPendings. */

    /* API call. */
    xReturn = xTaskRemoveFromEventList( &xEventList );

    /* Validations. */
    /* Yield not required for current core due to equal priority. */
    TEST_ASSERT_EQUAL( pdFALSE, xReturn );
    /* Task is removed from event list. */
    TEST_ASSERT_EQUAL( NULL, xTaskTCB.xEventListItem.pvContainer );
    /* Task is added to ready list. */
    TEST_ASSERT_EQUAL( &pxReadyTasksLists[ xTaskTCB.uxPriority ], xTaskTCB.xStateListItem.pvContainer );
}

/**
 * @brief xTaskRemoveFromEventList - Remove a higher priority task from event list.
 *
 * The task is removed from event list. Verified this task is put back to ready list
 * and removed from event list. Current core is requested to yield.
 *
 * <b>Coverage</b>
 * @code{c}
 * #else
 * {
 *     xReturn = pdFALSE;
 *
 *     #if ( configUSE_PREEMPTION == 1 )
 *     {
 *         prvYieldForTask( pxUnblockedTCB );
 *
 *         if( xYieldPendings[ portGET_CORE_ID() ] != pdFALSE )
 *         {
 *             xReturn = pdTRUE;
 *         }
 *     }
 *     #endif
 * }
 * #endif
 * @endcode
 * ( xYieldPendings[ portGET_CORE_ID() ] != pdFALSE ) is true.
 */
void test_coverage_xTaskRemoveFromEventList_remove_higher_priority_task( void )
{
    TCB_t xTaskTCB = { NULL };
    TCB_t xTaskTCBs[ configNUMBER_OF_CORES ] = { NULL };
    List_t xEventList = { 0 };
    uint32_t i;
    BaseType_t xReturn;

    /* Setup the variables and structure. */
    uxSchedulerSuspended = pdFALSE;
    uxTopReadyPriority = tskIDLE_PRIORITY + 1U;
    vListInitialise( &xEventList );
    vListInitialise( &( pxReadyTasksLists[ tskIDLE_PRIORITY ] ) );
    vListInitialise( &( pxReadyTasksLists[ tskIDLE_PRIORITY + 1U ] ) );
    vListInitialise( &xSuspendedTaskList );
    vListInitialise( &xDelayedTaskList1 );
    pxDelayedTaskList = &xDelayedTaskList1;

    /* Create idle tasks and add it into the ready list. */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        xTaskTCBs[ i ].uxPriority = tskIDLE_PRIORITY;
        xTaskTCBs[ i ].xStateListItem.pvOwner = &xTaskTCBs[ i ];
        xTaskTCBs[ i ].uxCoreAffinityMask = ( ( 1U << configNUMBER_OF_CORES ) - 1U );
        if( i == 0 )
        {
            /* Core 0 is running an idle task in order to be requested to yield. */
            xTaskTCBs[ i ].uxTaskAttributes = taskATTRIBUTE_IS_IDLE;
        }
        else
        {
            /* Others are running a normal task. */
            xTaskTCBs[ i ].uxTaskAttributes = 0;
        }

        /* Create idle tasks with equal number of cores. */
        pxCurrentTCBs[ i ] = &xTaskTCBs[ i ];
        xTaskTCBs[ i ].xTaskRunState = i;
        xTaskTCBs[ i ].xStateListItem.pxContainer = &pxReadyTasksLists[ tskIDLE_PRIORITY ];
        listINSERT_END( &pxReadyTasksLists[ tskIDLE_PRIORITY ], &xTaskTCBs[ i ].xStateListItem );
        uxCurrentNumberOfTasks = uxCurrentNumberOfTasks + 1;
    }

    /* Create one more task to be removed from event list. */
    xTaskTCB.uxPriority = tskIDLE_PRIORITY + 1U;
    xTaskTCB.xStateListItem.pxContainer = &xSuspendedTaskList;
    xTaskTCB.xStateListItem.pvOwner = &xTaskTCB;
    listINSERT_END( &xSuspendedTaskList, &xTaskTCB.xStateListItem );
    xTaskTCB.xEventListItem.pxContainer = &xEventList;
    xTaskTCB.xEventListItem.pvOwner = &xTaskTCB;
    listINSERT_END( &xEventList, &xTaskTCB.xEventListItem );
    xTaskTCB.xTaskRunState = taskTASK_NOT_RUNNING;
    xTaskTCB.uxCoreAffinityMask = ( ( 1U << configNUMBER_OF_CORES ) - 1U );
    uxCurrentNumberOfTasks = uxCurrentNumberOfTasks + 1;

    /* Expectations. */
    vFakePortGetCoreID_StubWithCallback( NULL );
    vFakePortGetCoreID_ExpectAndReturn( 0 );    /* Get portGET_CRITICAL_NESTING_COUNT. */
    vFakePortGetCoreID_ExpectAndReturn( 0 );    /* Get prvYieldCore. */
    vFakePortGetCoreID_ExpectAndReturn( 0 );    /* Get xYieldPendings. */

    /* API call. */
    xReturn = xTaskRemoveFromEventList( &xEventList );

    /* Validations. */
    /* Yield is required for current core due to higher priority. */
    TEST_ASSERT_EQUAL( pdTRUE, xReturn );
    /* Task is removed from event list. */
    TEST_ASSERT_EQUAL( NULL, xTaskTCB.xEventListItem.pvContainer );
    /* Task is added to ready list. */
    TEST_ASSERT_EQUAL( &pxReadyTasksLists[ xTaskTCB.uxPriority ], xTaskTCB.xStateListItem.pvContainer );
}


/**
 * @brief vTaskRemoveFromUnorderedEventList - Remove a higher priority task from event list.
 *
 * The task is removed from event list. Verified this task is put back to ready list
 * and removed from event list. Current core is requested to yield. The item value
 * is set correctly.
 *
 * <b>Coverage</b>
 * @code{c}
 * #else
 * {
 *     #if ( configUSE_PREEMPTION == 1 )
 *     {
 *         taskENTER_CRITICAL();
 *         {
 *             prvYieldForTask( pxUnblockedTCB );
 *         }
 *         taskEXIT_CRITICAL();
 *     }
 *     #endif
 * }
 * #endif
 * @endcode
 */
void test_coverage_vTaskRemoveFromUnorderedEventList_remove_higher_priority_task( void )
{
    TCB_t xTaskTCB = { NULL };
    TCB_t xTaskTCBs[ configNUMBER_OF_CORES ] = { NULL };
    List_t xEventList = { 0 };
    uint32_t i;

    /* Setup the variables and structure. */
    uxSchedulerSuspended = pdFALSE;
    uxTopReadyPriority = tskIDLE_PRIORITY + 1U;
    vListInitialise( &xEventList );
    vListInitialise( &( pxReadyTasksLists[ tskIDLE_PRIORITY ] ) );
    vListInitialise( &( pxReadyTasksLists[ tskIDLE_PRIORITY + 1U ] ) );
    vListInitialise( &xSuspendedTaskList );
    vListInitialise( &xDelayedTaskList1 );
    pxDelayedTaskList = &xDelayedTaskList1;

    /* Create idle tasks and add it into the ready list. */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        xTaskTCBs[ i ].uxPriority = tskIDLE_PRIORITY;
        xTaskTCBs[ i ].xStateListItem.pvOwner = &xTaskTCBs[ i ];
        xTaskTCBs[ i ].uxCoreAffinityMask = ( ( 1U << configNUMBER_OF_CORES ) - 1U );
        if( i == 0 )
        {
            /* Core 0 is running an idle task in order to be requested to yield. */
            xTaskTCBs[ i ].uxTaskAttributes = taskATTRIBUTE_IS_IDLE;
        }
        else
        {
            /* Others are running a normal task. */
            xTaskTCBs[ i ].uxTaskAttributes = 0;
        }

        /* Create idle tasks with equal number of cores. */
        pxCurrentTCBs[ i ] = &xTaskTCBs[ i ];
        xTaskTCBs[ i ].xTaskRunState = i;
        xTaskTCBs[ i ].xStateListItem.pxContainer = &pxReadyTasksLists[ tskIDLE_PRIORITY ];
        listINSERT_END( &pxReadyTasksLists[ tskIDLE_PRIORITY ], &xTaskTCBs[ i ].xStateListItem );
        uxCurrentNumberOfTasks = uxCurrentNumberOfTasks + 1;
    }

    /* Create one more task to be removed from event list. */
    xTaskTCB.uxPriority = tskIDLE_PRIORITY + 1U;
    xTaskTCB.xStateListItem.pxContainer = &xSuspendedTaskList;
    xTaskTCB.xStateListItem.pvOwner = &xTaskTCB;
    listINSERT_END( &xSuspendedTaskList, &xTaskTCB.xStateListItem );
    xTaskTCB.xEventListItem.pxContainer = &xEventList;
    xTaskTCB.xEventListItem.pvOwner = &xTaskTCB;
    listINSERT_END( &xEventList, &xTaskTCB.xEventListItem );
    xTaskTCB.xTaskRunState = taskTASK_NOT_RUNNING;
    xTaskTCB.uxCoreAffinityMask = ( ( 1U << configNUMBER_OF_CORES ) - 1U );
    uxCurrentNumberOfTasks = uxCurrentNumberOfTasks + 1;

    /* Expectations. */
    vFakePortGetCoreID_StubWithCallback( NULL );
    vFakePortGetCoreID_ExpectAndReturn( 0 );    /* Get portGET_CRITICAL_NESTING_COUNT. */
    vFakePortGetCoreID_ExpectAndReturn( 0 );    /* Get prvYieldCore. */

    /* API call. */
    vTaskRemoveFromUnorderedEventList( &xTaskTCB.xEventListItem, 500 | 0x80000000UL );

    /* Validations. */
    /* Task is removed from event list. */
    TEST_ASSERT_EQUAL( NULL, xTaskTCB.xEventListItem.pvContainer );
    /* Task is added to ready list. */
    TEST_ASSERT_EQUAL( &pxReadyTasksLists[ xTaskTCB.uxPriority ], xTaskTCB.xStateListItem.pvContainer );
    /* The event list item value is set. */
    TEST_ASSERT_EQUAL( 500 | 0x80000000UL, xTaskTCB.xEventListItem.xItemValue );
    /* The xYieldPendings is set. */
    TEST_ASSERT_EQUAL( pdTRUE, xYieldPendings[ 0 ] );
}

/**
 * @brief vTaskEnterCritical - task is already in the critical section.
 *
 * Task is already in the critical section. The critical nesting count will be increased.
 *
 * <b>Coverage</b>
 * @code{c}
 * if( portGET_CRITICAL_NESTING_COUNT() == 0U )
 * {
 *     portGET_TASK_LOCK();
 *     portGET_ISR_LOCK();
 * }
 * @endcode
 * ( portGET_CRITICAL_NESTING_COUNT() == 0U ) is false.
 */
void test_coverage_vTaskEnterCritical_task_in_critical_already( void )
{
    TCB_t xTaskTCB = { NULL };

    /* Setup the variables and structure. */
    xTaskTCB.uxCriticalNesting = 1;
    pxCurrentTCBs[ 0 ] = &xTaskTCB;
    xSchedulerRunning = pdTRUE;

    /* Clear callback in commonSetUp. */
    vFakePortDisableInterrupts_StopIgnore();
    vFakePortGetCoreID_StubWithCallback( NULL );

    /* Expectations. */
    vFakePortDisableInterrupts_ExpectAndReturn( 0 );
    vFakePortGetCoreID_ExpectAndReturn( 0 );        /* Get both locks. */
    vFakePortGetCoreID_ExpectAndReturn( 0 );        /* Increment the critical nesting count. */
    vFakePortGetCoreID_ExpectAndReturn( 0 );        /* Check first time enter critical section. */

    /* API call. */
    vTaskEnterCritical();

    /* Validation. */
    TEST_ASSERT_EQUAL( 2, xTaskTCB.uxCriticalNesting );
}

/**
 * @brief vTaskEnterCriticalFromISR - ISR is already in critical section.
 *
 * ISR is already in the critical section. The critical nesting count will be increased.
 *
 * <b>Coverage</b>
 * @code{c}
 * if( portGET_CRITICAL_NESTING_COUNT() == 0U )
 * {
 *     portGET_ISR_LOCK();
 * }
 * @endcode
 * ( portGET_CRITICAL_NESTING_COUNT() == 0U ) is false.
 */
void test_coverage_vTaskEnterCriticalFromISR_isr_in_critical_already( void )
{
    TCB_t xTaskTCB = { NULL };
    UBaseType_t uxSavedInterruptStatus;

    /* Setup the variables and structure. */
    xTaskTCB.uxCriticalNesting = 1;
    pxCurrentTCBs[ 0 ] = &xTaskTCB;
    xSchedulerRunning = pdTRUE;

    /* Clear callback in commonSetUp. */
    ulFakePortSetInterruptMaskFromISR_StopIgnore();
    vFakePortGetCoreID_StubWithCallback( NULL );

    /* Expectations. */
    ulFakePortSetInterruptMaskFromISR_ExpectAndReturn( 0x5a5a );    /* The value to be verified. */
    vFakePortGetCoreID_ExpectAndReturn( 0 );        /* Get ISR locks. */
    vFakePortGetCoreID_ExpectAndReturn( 0 );        /* Increment the critical nesting count. */

    /* API call. */
    uxSavedInterruptStatus = vTaskEnterCriticalFromISR();

    /* Validation. */
    TEST_ASSERT_EQUAL( 2, xTaskTCB.uxCriticalNesting );
    TEST_ASSERT_EQUAL( 0X5a5a, uxSavedInterruptStatus );
}

/**
 * @brief vTaskExitCritical - Task enters the critical section for more than 1 time.
 *
 * Verify the critical nesting count will be decreased in this API.
 *
 * <b>Coverage</b>
 * @code{c}
 * if( pxCurrentTCB->uxCriticalNesting == 0U )
 * {
 *     portENABLE_INTERRUPTS();
 * }
 * else
 * {
 *     mtCOVERAGE_TEST_MARKER();
 * }
 * @endcode
 * ( pxCurrentTCB->uxCriticalNesting == 0U ) is false.
 */
void test_coverage_vTaskExitCritical_task_enter_critical_mt_1( void )
{
    TCB_t xTaskTCB = { NULL };

    /* Setup the variables and structure. */
    xTaskTCB.uxCriticalNesting = 2;
    pxCurrentTCBs[ 0 ] = &xTaskTCB;
    xSchedulerRunning = pdTRUE;

    /* Clear callback in commonSetUp. */
    vFakePortGetCoreID_StubWithCallback( NULL );

    /* Expectations. */
    vFakePortGetCoreID_ExpectAndReturn( 0 );        /* configASSERT. */
    vFakePortGetCoreID_ExpectAndReturn( 0 );        /* Check critical nesting count. */
    vFakePortGetCoreID_ExpectAndReturn( 0 );        /* Decrease the critical nesting count. */
    vFakePortGetCoreID_ExpectAndReturn( 0 );        /* Check exit critical section. */

    /* API call. */
    vTaskExitCritical();

    /* Validation. */
    TEST_ASSERT_EQUAL( 1, xTaskTCB.uxCriticalNesting );
}

/**
 * @brief vTaskExitCritical - Task is not in the critical section.
 *
 * Cover the situation that task is not in the critical section when vTaskExitCritical
 * is called. Critical nesting count won't be updated.
 *
 * <b>Coverage</b>
 * @code{c}
 * if( pxCurrentTCB->uxCriticalNesting > 0U )
 * {
 *     ( pxCurrentTCB->uxCriticalNesting )--;
 *     ...
 * }
 * @endcode
 * ( pxCurrentTCB->uxCriticalNesting > 0U ) is false.
 */
void test_coverage_vTaskExitCritical_task_not_in_critical( void )
{
    TCB_t xTaskTCB = { NULL };

    /* Setup the variables and structure. */
    xTaskTCB.uxCriticalNesting = 0;
    pxCurrentTCBs[ 0 ] = &xTaskTCB;
    xSchedulerRunning = pdTRUE;

    /* Clear callback in commonSetUp. */
    vFakePortGetCoreID_StubWithCallback( NULL );

    /* Expectations. */
    vFakePortGetCoreID_ExpectAndReturn( 0 );        /* configASSERT. */
    vFakePortGetCoreID_ExpectAndReturn( 0 );        /* Check critical nesting count. */

    /* API call. */
    vTaskExitCritical();

    /* Validation. */
    /* Critical section count won't be updated. This test shows it's result in the
     * coverage report. */
}

/**
 * @brief vTaskExitCriticalFromISR - ISR enters critical section more than 1 time.
 *
 * Cover the situation that ISR enters critical section more that 1 time when vTaskExitCriticalFromISR
 * is called. Critical nesting count will be decreased.
 *
 * <b>Coverage</b>
 * @code{c}
 *     if( portGET_CRITICAL_NESTING_COUNT() > 0U )
 *     {
 *         portDECREMENT_CRITICAL_NESTING_COUNT();
 *
 *         if( portGET_CRITICAL_NESTING_COUNT() == 0U )
 *         {
 *             xYieldCurrentTask = xYieldPendings[ portGET_CORE_ID() ];
 *
 *             portRELEASE_ISR_LOCK();
 *             portCLEAR_INTERRUPT_MASK_FROM_ISR( uxSavedInterruptStatus );
 *
 *             if( xYieldCurrentTask != pdFALSE )
 *             {
 *                 portYIELD();
 *             }
 *         }
 *         else
 *         {
 *             mtCOVERAGE_TEST_MARKER();
 *         }
 *     }
 * @endcode
 * ( portGET_CRITICAL_NESTING_COUNT() > 0U ) is ture.
 * ( portGET_CRITICAL_NESTING_COUNT() == 0U ) is false.
 */
void test_coverage_vTaskExitCriticalFromISR_isr_enter_critical_mt_1( void )
{
    TCB_t xTaskTCB = { NULL };

    /* Setup the variables and structure. */
    xTaskTCB.uxCriticalNesting = 2;
    pxCurrentTCBs[ 0 ] = &xTaskTCB;
    xSchedulerRunning = pdTRUE;

    /* Clear callback in commonSetUp. */
    vFakePortGetCoreID_StubWithCallback( NULL );

    /* Expectations. */
    vFakePortGetCoreID_ExpectAndReturn( 0 );        /* configASSERT. */
    vFakePortGetCoreID_ExpectAndReturn( 0 );        /* Check critical nesting count. */
    vFakePortGetCoreID_ExpectAndReturn( 0 );        /* Decrement critical nesting count. */
    vFakePortGetCoreID_ExpectAndReturn( 0 );        /* Check critical nesting count. */

    /* API call. */
    /* The mask value has not effect since ISR enters critical section more than 1 time. */
    vTaskExitCriticalFromISR( 0x5a5a );

    /* Validation. */
    TEST_ASSERT_EQUAL( 1, xTaskTCB.uxCriticalNesting );
}

/**
 * @brief vTaskExitCriticalFromISR - ISR is not in the critical section.
 *
 * Cover the situation that ISR is not in the critical section when vTaskExitCriticalFromISR
 * is called. Critical nesting count won't be updated.
 *
 * <b>Coverage</b>
 * @code{c}
 *     if( portGET_CRITICAL_NESTING_COUNT() > 0U )
 *     {
 *         portDECREMENT_CRITICAL_NESTING_COUNT();
 *
 *         ...
 *     }
 * @endcode
 * ( portGET_CRITICAL_NESTING_COUNT() > 0U ) is false.
 */
void test_coverage_vTaskExitCriticalFromISR_isr_not_in_critical( void )
{
    TCB_t xTaskTCB = { NULL };

    /* Setup the variables and structure. */
    xTaskTCB.uxCriticalNesting = 0;
    pxCurrentTCBs[ 0 ] = &xTaskTCB;
    xSchedulerRunning = pdTRUE;

    /* Clear callback in commonSetUp. */
    vFakePortGetCoreID_StubWithCallback( NULL );

    /* Expectations. */
    vFakePortGetCoreID_ExpectAndReturn( 0 );        /* configASSERT. */
    vFakePortGetCoreID_ExpectAndReturn( 0 );        /* Check critical nesting count. */

    /* API call. */
    /* The mask value has not effect since ISR is not in critlcal section. */
    vTaskExitCriticalFromISR( 0x5a5a );

    /* Validation. */
    /* Critical section count won't be changed. This test shows it's result in the
     * coverage report. */
}

/**
 * @brief  pvTaskGetThreadLocalStoragePointer - xIndex is zero.
 *
 * Cover the situation that xIndex is zero and less than configNUM_THREAD_LOCAL_STORAGE_POINTERS when pvTaskGetThreadLocalStoragePointer
 * is called. 
 * 
 * <b>Coverage</b>
 * @code{c}
 *     if( ( xIndex >= 0 ) &&
            ( xIndex < configNUM_THREAD_LOCAL_STORAGE_POINTERS ) )
        {
            pxTCB = prvGetTCBFromHandle( xTaskToQuery );
            pvReturn = pxTCB->pvThreadLocalStoragePointers[ xIndex ];
        }
 * @endcode
 * ( ( xIndex >= 0 ) && ( xIndex < configNUM_THREAD_LOCAL_STORAGE_POINTERS ) ) is true.
 */
void test_coverage_pvTaskGetThreadLocalStoragePointer_xIndex_is_zero( void )
{
    
    uint32_t i = 454545;
    void * pValue = &i;
    void * ret_pValue;
    TCB_t tcb;
    TaskHandle_t task_handle = &tcb;

     /* Setup */
    /* API Call */
    vTaskSetThreadLocalStoragePointer( task_handle,
                                       0,
                                       pValue );
    ret_pValue = pvTaskGetThreadLocalStoragePointer( task_handle, 0 );
    /* Validations */
    TEST_ASSERT_EQUAL_PTR( pValue, ret_pValue );
}
/**
 * @brief  pvTaskGetThreadLocalStoragePointer - taskhandle is NULL.
 *
 * Cover the situation that xIndex is zero and handle is NULL when pvTaskGetThreadLocalStoragePointer
 * is called. 
 * 
 * <b>Coverage</b>
 * @code{c}
 *     if( ( xIndex >= 0 ) &&
            ( xIndex < configNUM_THREAD_LOCAL_STORAGE_POINTERS ) )
        {
            pxTCB = prvGetTCBFromHandle( xTaskToQuery );
            pvReturn = pxTCB->pvThreadLocalStoragePointers[ xIndex ];
        }
 * @endcode
 * ( ( xIndex >= 0 ) && ( xIndex < configNUM_THREAD_LOCAL_STORAGE_POINTERS ) ) is true.
 */
void test_coverage_pvTaskGetThreadLocalStoragePointer_null_handle( void )
{
    TCB_t xTaskTCB = { NULL };
    uint32_t i = 454545;
    void * pValue = &i;
    void * ret_pValue;
    
    /* Setup */
    /* Create a task as current running task on core 0. */
    pxCurrentTCBs[ 0 ] = &xTaskTCB;

    /* API Call */
    vTaskSetThreadLocalStoragePointer( NULL,
                                       0,
                                       pValue );
    ret_pValue = pvTaskGetThreadLocalStoragePointer( NULL, 0 );

    /* Validations */
    TEST_ASSERT_EQUAL_PTR( pValue, ret_pValue );
}
/**
 * @brief  pvTaskGetThreadLocalStoragePointer - xIndex is greater than configNUM_THREAD_LOCAL_STORAGE_POINTERS .
 *
 * Cover the situation that xIndex is greater than configNUM_THREAD_LOCAL_STORAGE_POINTERS when pvTaskGetThreadLocalStoragePointer
 * is called. 
 * 
 * <b>Coverage</b>
 * @code{c}
 *     if( ( xIndex >= 0 ) &&
            ( xIndex < configNUM_THREAD_LOCAL_STORAGE_POINTERS ) )
        {
            pxTCB = prvGetTCBFromHandle( xTaskToQuery );
            pvReturn = pxTCB->pvThreadLocalStoragePointers[ xIndex ];
        }
        else
        {
            pvReturn = NULL;
        }
 * @endcode
 * ( ( xIndex >= 0 ) && ( xIndex < configNUM_THREAD_LOCAL_STORAGE_POINTERS ) ) is false.
 */
void test_coverage_pvTaskGetThreadLocalStoragePointer_fail( void )
{
    void * ret_pValue;

    ret_pValue = pvTaskGetThreadLocalStoragePointer( NULL,
                                                     configNUM_THREAD_LOCAL_STORAGE_POINTERS + 2 );
    TEST_ASSERT_NULL( ret_pValue );
}

/**
 * @brief xTaskGenericNotifyFromISR - Notify a equal or lower priority task.
 *
 * Notify a equal or lower priority task from ISR. Higher priority task is not woken.
 *
 * <b>Coverage</b>
 * @code{c}
 * #if ( configUSE_PREEMPTION == 1 )
 * {
 *     prvYieldForTask( pxTCB );
 *
 *     if( xYieldPendings[ portGET_CORE_ID() ] == pdTRUE )
 *     {
 *         if( pxHigherPriorityTaskWoken != NULL )
 *         {
 *             *pxHigherPriorityTaskWoken = pdTRUE;
 *         }
 *     }
 * }
 * #endif
 * @endcode
 * ( xYieldPendings[ portGET_CORE_ID() ] == pdTRUE ) is false.
 */
void test_coverage_xTaskGenericNotifyFromISR_priority_le( void )
{
    TCB_t xTaskTCB = { NULL };
    TCB_t xTaskTCBs[ configNUMBER_OF_CORES ] = { NULL };
    UBaseType_t uxIndexToNotify = 0;    /* Use index 0 in this test. */
    uint32_t ulPreviousNotificationValue;
    BaseType_t xHigherPriorityTaskWoken = pdFALSE;
    BaseType_t xReturn;
    BaseType_t xSavedInterruptMask = 0x1234;   /* Interrupt mask to be verified. */
    List_t xEventList = { 0 };
    uint32_t i;

    /* Setup the variables and structure. */
    uxSchedulerSuspended = pdFALSE;
    uxTopReadyPriority = tskIDLE_PRIORITY;
    vListInitialise( &xEventList );
    vListInitialise( &( pxReadyTasksLists[ tskIDLE_PRIORITY ] ) );
    vListInitialise( &xSuspendedTaskList );

    /* Create idle tasks and add it into the ready list. */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        xTaskTCBs[ i ].uxPriority = tskIDLE_PRIORITY;
        xTaskTCBs[ i ].xStateListItem.pvOwner = &xTaskTCBs[ i ];
        xTaskTCBs[ i ].uxCoreAffinityMask = ( ( 1U << configNUMBER_OF_CORES ) - 1U );
        xTaskTCBs[ i ].uxTaskAttributes = 0;

        /* Create idle tasks with equal number of cores. */
        pxCurrentTCBs[ i ] = &xTaskTCBs[ i ];
        xTaskTCBs[ i ].xTaskRunState = i;
        xTaskTCBs[ i ].xStateListItem.pxContainer = &pxReadyTasksLists[ tskIDLE_PRIORITY ];
        listINSERT_END( &pxReadyTasksLists[ tskIDLE_PRIORITY ], &xTaskTCBs[ i ].xStateListItem );
        uxCurrentNumberOfTasks = uxCurrentNumberOfTasks + 1;
    }

    /* Create one more task to be removed from event list. */
    xTaskTCB.uxPriority = tskIDLE_PRIORITY;
    xTaskTCB.xStateListItem.pxContainer = &xSuspendedTaskList;
    xTaskTCB.xStateListItem.pvOwner = &xTaskTCB;
    listINSERT_END( &xSuspendedTaskList, &xTaskTCB.xStateListItem );
    xTaskTCB.xEventListItem.pxContainer = &xEventList;
    xTaskTCB.xEventListItem.pvOwner = &xTaskTCB;
    listINSERT_END( &xEventList, &xTaskTCB.xEventListItem );
    xTaskTCB.xTaskRunState = taskTASK_NOT_RUNNING;
    xTaskTCB.uxCoreAffinityMask = ( ( 1U << configNUMBER_OF_CORES ) - 1U );
    xTaskTCB.ulNotifiedValue[ uxIndexToNotify ] = 0x5a5a; /* Value to be verified in this test. */
    xTaskTCB.ucNotifyState[ uxIndexToNotify ] = taskWAITING_NOTIFICATION;
    uxCurrentNumberOfTasks = uxCurrentNumberOfTasks + 1;

    /* Clear callback in commonSetUp. */
    vFakePortGetCoreID_StubWithCallback( NULL );
    vFakePortEnterCriticalFromISR_StubWithCallback( NULL );
    vFakePortExitCriticalFromISR_StubWithCallback( NULL );

    /* Expectations. */
    vFakePortAssertIfInterruptPriorityInvalid_Expect();
    vFakePortEnterCriticalFromISR_ExpectAndReturn( xSavedInterruptMask );
    vFakePortGetCoreID_ExpectAndReturn( 0 );    /* Get portGET_CRITICAL_NESTING_COUNT. */
    vFakePortGetCoreID_ExpectAndReturn( 0 );    /* Get prvYieldCore. */
    vFakePortExitCriticalFromISR_Expect( xSavedInterruptMask );

    /* API call. */
    xReturn = xTaskGenericNotifyFromISR( &xTaskTCB,
                                         uxIndexToNotify,
                                         0,       /* Value is not used with eNoAction. */
                                         eNoAction,
                                         &ulPreviousNotificationValue,
                                         &xHigherPriorityTaskWoken );

    /* Validation. */
    TEST_ASSERT_EQUAL( pdTRUE, xReturn );
    TEST_ASSERT_EQUAL( 0x5a5a, ulPreviousNotificationValue );
    TEST_ASSERT_NOT_EQUAL( pdTRUE, xHigherPriorityTaskWoken );
}

/**
 * @brief xTaskGenericNotifyFromISR - Notify a higher priority task.
 *
 * Notify a higher priority task from ISR. Higher priority task is woken.
 *
 * <b>Coverage</b>
 * @code{c}
 * #if ( configUSE_PREEMPTION == 1 )
 * {
 *     prvYieldForTask( pxTCB );
 *
 *     if( xYieldPendings[ portGET_CORE_ID() ] == pdTRUE )
 *     {
 *         if( pxHigherPriorityTaskWoken != NULL )
 *         {
 *             *pxHigherPriorityTaskWoken = pdTRUE;
 *         }
 *     }
 * }
 * #endif
 * @endcode
 * ( xYieldPendings[ portGET_CORE_ID() ] == pdTRUE ) is true.
 * ( pxHigherPriorityTaskWoken != NULL ) is true.
 */
void test_coverage_xTaskGenericNotifyFromISR_priority_gt( void )
{
    TCB_t xTaskTCB = { NULL };
    TCB_t xTaskTCBs[ configNUMBER_OF_CORES ] = { NULL };
    UBaseType_t uxIndexToNotify = 0;    /* Use index 0 in this test. */
    uint32_t ulPreviousNotificationValue;
    BaseType_t xHigherPriorityTaskWoken = pdFALSE;
    BaseType_t xReturn;
    BaseType_t xSavedInterruptMask = 0x1234;   /* Interrupt mask to be verified. */
    List_t xEventList = { 0 };
    uint32_t i;

    /* Setup the variables and structure. */
    uxSchedulerSuspended = pdFALSE;
    uxTopReadyPriority = tskIDLE_PRIORITY;
    vListInitialise( &xEventList );
    vListInitialise( &( pxReadyTasksLists[ tskIDLE_PRIORITY ] ) );
    vListInitialise( &xSuspendedTaskList );

    /* Create idle tasks and add it into the ready list. */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        xTaskTCBs[ i ].uxPriority = tskIDLE_PRIORITY;
        xTaskTCBs[ i ].xStateListItem.pvOwner = &xTaskTCBs[ i ];
        xTaskTCBs[ i ].uxCoreAffinityMask = ( ( 1U << configNUMBER_OF_CORES ) - 1U );
        if( i == 0 )
        {
            /* Core 0 is running an idle task in order to be requested to yield. */
            xTaskTCBs[ i ].uxTaskAttributes = taskATTRIBUTE_IS_IDLE;
        }
        else
        {
            /* Others are running a normal task. */
            xTaskTCBs[ i ].uxTaskAttributes = 0;
        }

        /* Create idle tasks with equal number of cores. */
        pxCurrentTCBs[ i ] = &xTaskTCBs[ i ];
        xTaskTCBs[ i ].xTaskRunState = i;
        xTaskTCBs[ i ].xStateListItem.pxContainer = &pxReadyTasksLists[ tskIDLE_PRIORITY ];
        listINSERT_END( &pxReadyTasksLists[ tskIDLE_PRIORITY ], &xTaskTCBs[ i ].xStateListItem );
        uxCurrentNumberOfTasks = uxCurrentNumberOfTasks + 1;
    }

    /* Create one more task to be removed from event list. */
    xTaskTCB.uxPriority = tskIDLE_PRIORITY;
    xTaskTCB.xStateListItem.pxContainer = &xSuspendedTaskList;
    xTaskTCB.xStateListItem.pvOwner = &xTaskTCB;
    listINSERT_END( &xSuspendedTaskList, &xTaskTCB.xStateListItem );
    xTaskTCB.xEventListItem.pxContainer = &xEventList;
    xTaskTCB.xEventListItem.pvOwner = &xTaskTCB;
    listINSERT_END( &xEventList, &xTaskTCB.xEventListItem );
    xTaskTCB.xTaskRunState = taskTASK_NOT_RUNNING;
    xTaskTCB.uxCoreAffinityMask = ( ( 1U << configNUMBER_OF_CORES ) - 1U );
    xTaskTCB.ulNotifiedValue[ uxIndexToNotify ] = 0x5a5a; /* Value to be verified in this test. */
    xTaskTCB.ucNotifyState[ uxIndexToNotify ] = taskWAITING_NOTIFICATION;
    uxCurrentNumberOfTasks = uxCurrentNumberOfTasks + 1;

    /* Clear callback in commonSetUp. */
    vFakePortGetCoreID_StubWithCallback( NULL );
    vFakePortEnterCriticalFromISR_StubWithCallback( NULL );
    vFakePortExitCriticalFromISR_StubWithCallback( NULL );

    /* Expectations. */
    vFakePortAssertIfInterruptPriorityInvalid_Expect();
    vFakePortEnterCriticalFromISR_ExpectAndReturn( xSavedInterruptMask );
    vFakePortGetCoreID_ExpectAndReturn( 0 );
    vFakePortGetCoreID_ExpectAndReturn( 0 );
    vFakePortGetCoreID_ExpectAndReturn( 0 );
    vFakePortExitCriticalFromISR_Expect( xSavedInterruptMask );

    /* API call. */
    xReturn = xTaskGenericNotifyFromISR( &xTaskTCB,
                                         uxIndexToNotify,
                                         0,       /* Value is not used with eNoAction. */
                                         eNoAction,
                                         &ulPreviousNotificationValue,
                                         &xHigherPriorityTaskWoken );

    /* Validation. */
    TEST_ASSERT_EQUAL( pdTRUE, xReturn );
    TEST_ASSERT_EQUAL( 0x5a5a, ulPreviousNotificationValue );
    TEST_ASSERT_EQUAL( pdTRUE, xHigherPriorityTaskWoken );
}

/**
 * @brief xTaskGenericNotifyFromISR - Notify a higher priority task with NULL param.
 *
 * Notify a higher priority task from ISR. Higher priority task is woken. Input param
 * pxHigherPriorityTaskWoken is NULL.
 *
 * <b>Coverage</b>
 * @code{c}
 * #if ( configUSE_PREEMPTION == 1 )
 * {
 *     prvYieldForTask( pxTCB );
 *
 *     if( xYieldPendings[ portGET_CORE_ID() ] == pdTRUE )
 *     {
 *         if( pxHigherPriorityTaskWoken != NULL )
 *         {
 *             *pxHigherPriorityTaskWoken = pdTRUE;
 *         }
 *     }
 * }
 * #endif
 * @endcode
 * ( xYieldPendings[ portGET_CORE_ID() ] == pdTRUE ) is true.
 * ( pxHigherPriorityTaskWoken != NULL ) is false.
 */
void test_coverage_xTaskGenericNotifyFromISR_priority_gt_null_param( void )
{
    TCB_t xTaskTCB = { NULL };
    TCB_t xTaskTCBs[ configNUMBER_OF_CORES ] = { NULL };
    UBaseType_t uxIndexToNotify = 0;    /* Use index 0 in this test. */
    uint32_t ulPreviousNotificationValue;
    BaseType_t xReturn;
    BaseType_t xSavedInterruptMask = 0x1234;   /* Interrupt mask to be verified. */
    List_t xEventList = { 0 };
    uint32_t i;

    /* Setup the variables and structure. */
    uxSchedulerSuspended = pdFALSE;
    uxTopReadyPriority = tskIDLE_PRIORITY;
    vListInitialise( &xEventList );
    vListInitialise( &( pxReadyTasksLists[ tskIDLE_PRIORITY ] ) );
    vListInitialise( &xSuspendedTaskList );

    /* Create idle tasks and add it into the ready list. */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        xTaskTCBs[ i ].uxPriority = tskIDLE_PRIORITY;
        xTaskTCBs[ i ].xStateListItem.pvOwner = &xTaskTCBs[ i ];
        xTaskTCBs[ i ].uxCoreAffinityMask = ( ( 1U << configNUMBER_OF_CORES ) - 1U );
        if( i == 0 )
        {
            /* Core 0 is running an idle task in order to be requested to yield. */
            xTaskTCBs[ i ].uxTaskAttributes = taskATTRIBUTE_IS_IDLE;
        }
        else
        {
            /* Others are running a normal task. */
            xTaskTCBs[ i ].uxTaskAttributes = 0;
        }

        /* Create idle tasks with equal number of cores. */
        pxCurrentTCBs[ i ] = &xTaskTCBs[ i ];
        xTaskTCBs[ i ].xTaskRunState = i;
        xTaskTCBs[ i ].xStateListItem.pxContainer = &pxReadyTasksLists[ tskIDLE_PRIORITY ];
        listINSERT_END( &pxReadyTasksLists[ tskIDLE_PRIORITY ], &xTaskTCBs[ i ].xStateListItem );
        uxCurrentNumberOfTasks = uxCurrentNumberOfTasks + 1;
    }

    /* Create one more task to be removed from event list. */
    xTaskTCB.uxPriority = tskIDLE_PRIORITY;
    xTaskTCB.xStateListItem.pxContainer = &xSuspendedTaskList;
    xTaskTCB.xStateListItem.pvOwner = &xTaskTCB;
    listINSERT_END( &xSuspendedTaskList, &xTaskTCB.xStateListItem );
    xTaskTCB.xEventListItem.pxContainer = &xEventList;
    xTaskTCB.xEventListItem.pvOwner = &xTaskTCB;
    listINSERT_END( &xEventList, &xTaskTCB.xEventListItem );
    xTaskTCB.xTaskRunState = taskTASK_NOT_RUNNING;
    xTaskTCB.uxCoreAffinityMask = ( ( 1U << configNUMBER_OF_CORES ) - 1U );
    xTaskTCB.ulNotifiedValue[ uxIndexToNotify ] = 0x5a5a; /* Value to be verified in this test. */
    xTaskTCB.ucNotifyState[ uxIndexToNotify ] = taskWAITING_NOTIFICATION;
    uxCurrentNumberOfTasks = uxCurrentNumberOfTasks + 1;

    /* Clear callback in commonSetUp. */
    vFakePortGetCoreID_StubWithCallback( NULL );
    vFakePortEnterCriticalFromISR_StubWithCallback( NULL );
    vFakePortExitCriticalFromISR_StubWithCallback( NULL );

    /* Expectations. */
    vFakePortAssertIfInterruptPriorityInvalid_Expect();
    vFakePortEnterCriticalFromISR_ExpectAndReturn( xSavedInterruptMask );
    vFakePortGetCoreID_ExpectAndReturn( 0 );
    vFakePortGetCoreID_ExpectAndReturn( 0 );
    vFakePortGetCoreID_ExpectAndReturn( 0 );
    vFakePortExitCriticalFromISR_Expect( xSavedInterruptMask );

    /* API call. */
    xReturn = xTaskGenericNotifyFromISR( &xTaskTCB,
                                         uxIndexToNotify,
                                         0,       /* Value is not used with eNoAction. */
                                         eNoAction,
                                         &ulPreviousNotificationValue,
                                         NULL );

    /* Validation. */
    TEST_ASSERT_EQUAL( pdTRUE, xReturn );
    TEST_ASSERT_EQUAL( 0x5a5a, ulPreviousNotificationValue );
    TEST_ASSERT_EQUAL( pdTRUE, xYieldPendings[ 0 ] );
}

/**
 * @brief vTaskGenericNotifyGiveFromISR - Notify a equal or lower priority task.
 *
 * Notify a equal or lower priority task from ISR. Higher priority task is not woken.
 *
 * <b>Coverage</b>
 * @code{c}
 * #if ( configUSE_PREEMPTION == 1 )
 * {
 *     prvYieldForTask( pxTCB );
 *
 *     if( xYieldPendings[ portGET_CORE_ID() ] == pdTRUE )
 *     {
 *         if( pxHigherPriorityTaskWoken != NULL )
 *         {
 *             *pxHigherPriorityTaskWoken = pdTRUE;
 *         }
 *     }
 * }
 * #endif
 * @endcode
 * ( xYieldPendings[ portGET_CORE_ID() ] == pdTRUE ) is false.
 */
void test_coverage_vTaskGenericNotifyGiveFromISR_priority_le( void )
{
    TCB_t xTaskTCB = { NULL };
    TCB_t xTaskTCBs[ configNUMBER_OF_CORES ] = { NULL };
    UBaseType_t uxIndexToNotify = 0;    /* Use index 0 in this test. */
    BaseType_t xHigherPriorityTaskWoken = pdFALSE;
    BaseType_t xSavedInterruptMask = 0x1234;   /* Interrupt mask to be verified. */
    List_t xEventList = { 0 };
    uint32_t i;

    /* Setup the variables and structure. */
    uxSchedulerSuspended = pdFALSE;
    uxTopReadyPriority = tskIDLE_PRIORITY;
    vListInitialise( &xEventList );
    vListInitialise( &( pxReadyTasksLists[ tskIDLE_PRIORITY ] ) );
    vListInitialise( &xSuspendedTaskList );

    /* Create idle tasks and add it into the ready list. */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        xTaskTCBs[ i ].uxPriority = tskIDLE_PRIORITY;
        xTaskTCBs[ i ].xStateListItem.pvOwner = &xTaskTCBs[ i ];
        xTaskTCBs[ i ].uxCoreAffinityMask = ( ( 1U << configNUMBER_OF_CORES ) - 1U );
        xTaskTCBs[ i ].uxTaskAttributes = 0;

        /* Create idle tasks with equal number of cores. */
        pxCurrentTCBs[ i ] = &xTaskTCBs[ i ];
        xTaskTCBs[ i ].xTaskRunState = i;
        xTaskTCBs[ i ].xStateListItem.pxContainer = &pxReadyTasksLists[ tskIDLE_PRIORITY ];
        listINSERT_END( &pxReadyTasksLists[ tskIDLE_PRIORITY ], &xTaskTCBs[ i ].xStateListItem );
        uxCurrentNumberOfTasks = uxCurrentNumberOfTasks + 1;
    }

    /* Create one more task to be removed from event list. */
    xTaskTCB.uxPriority = tskIDLE_PRIORITY;
    xTaskTCB.xStateListItem.pxContainer = &xSuspendedTaskList;
    xTaskTCB.xStateListItem.pvOwner = &xTaskTCB;
    listINSERT_END( &xSuspendedTaskList, &xTaskTCB.xStateListItem );
    xTaskTCB.xEventListItem.pxContainer = &xEventList;
    xTaskTCB.xEventListItem.pvOwner = &xTaskTCB;
    listINSERT_END( &xEventList, &xTaskTCB.xEventListItem );
    xTaskTCB.xTaskRunState = taskTASK_NOT_RUNNING;
    xTaskTCB.uxCoreAffinityMask = ( ( 1U << configNUMBER_OF_CORES ) - 1U );
    xTaskTCB.ulNotifiedValue[ uxIndexToNotify ] = 0x5a5a; /* Value to be verified in this test. */
    xTaskTCB.ucNotifyState[ uxIndexToNotify ] = taskWAITING_NOTIFICATION;
    uxCurrentNumberOfTasks = uxCurrentNumberOfTasks + 1;

    /* Clear callback in commonSetUp. */
    vFakePortGetCoreID_StubWithCallback( NULL );
    vFakePortEnterCriticalFromISR_StubWithCallback( NULL );
    vFakePortExitCriticalFromISR_StubWithCallback( NULL );

    /* Expectations. */
    vFakePortAssertIfInterruptPriorityInvalid_Expect();
    vFakePortEnterCriticalFromISR_ExpectAndReturn( xSavedInterruptMask );
    vFakePortGetCoreID_ExpectAndReturn( 0 );    /* Get portGET_CRITICAL_NESTING_COUNT. */
    vFakePortGetCoreID_ExpectAndReturn( 0 );    /* Get prvYieldCore. */
    vFakePortExitCriticalFromISR_Expect( xSavedInterruptMask );

    /* API call. */
    vTaskGenericNotifyGiveFromISR( &xTaskTCB,
                                   uxIndexToNotify,
                                   &xHigherPriorityTaskWoken );

    /* Validation. */
    TEST_ASSERT_EQUAL( 0x5a5a + 1U, xTaskTCB.ulNotifiedValue[ uxIndexToNotify ] );
    TEST_ASSERT_NOT_EQUAL( pdTRUE, xHigherPriorityTaskWoken );
}

/**
 * @brief vTaskGenericNotifyGiveFromISR - Notify a higher priority task.
 *
 * Notify a higher priority task from ISR. Higher priority task is woken.
 *
 * <b>Coverage</b>
 * @code{c}
 * #if ( configUSE_PREEMPTION == 1 )
 * {
 *     prvYieldForTask( pxTCB );
 *
 *     if( xYieldPendings[ portGET_CORE_ID() ] == pdTRUE )
 *     {
 *         if( pxHigherPriorityTaskWoken != NULL )
 *         {
 *             *pxHigherPriorityTaskWoken = pdTRUE;
 *         }
 *     }
 * }
 * #endif
 * @endcode
 * ( xYieldPendings[ portGET_CORE_ID() ] == pdTRUE ) is true.
 * ( pxHigherPriorityTaskWoken != NULL ) is true.
 */
void test_coverage_vTaskGenericNotifyGiveFromISR_priority_gt( void )
{
    TCB_t xTaskTCB = { NULL };
    TCB_t xTaskTCBs[ configNUMBER_OF_CORES ] = { NULL };
    UBaseType_t uxIndexToNotify = 0;    /* Use index 0 in this test. */
    BaseType_t xHigherPriorityTaskWoken = pdFALSE;
    BaseType_t xSavedInterruptMask = 0x1234;   /* Interrupt mask to be verified. */
    List_t xEventList = { 0 };
    uint32_t i;

    /* Setup the variables and structure. */
    uxSchedulerSuspended = pdFALSE;
    uxTopReadyPriority = tskIDLE_PRIORITY;
    vListInitialise( &xEventList );
    vListInitialise( &( pxReadyTasksLists[ tskIDLE_PRIORITY ] ) );
    vListInitialise( &xSuspendedTaskList );

    /* Create idle tasks and add it into the ready list. */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        xTaskTCBs[ i ].uxPriority = tskIDLE_PRIORITY;
        xTaskTCBs[ i ].xStateListItem.pvOwner = &xTaskTCBs[ i ];
        xTaskTCBs[ i ].uxCoreAffinityMask = ( ( 1U << configNUMBER_OF_CORES ) - 1U );
        if( i == 0 )
        {
            /* Core 0 is running an idle task in order to be requested to yield. */
            xTaskTCBs[ i ].uxTaskAttributes = taskATTRIBUTE_IS_IDLE;
        }
        else
        {
            /* Others are running a normal task. */
            xTaskTCBs[ i ].uxTaskAttributes = 0;
        }

        /* Create idle tasks with equal number of cores. */
        pxCurrentTCBs[ i ] = &xTaskTCBs[ i ];
        xTaskTCBs[ i ].xTaskRunState = i;
        xTaskTCBs[ i ].xStateListItem.pxContainer = &pxReadyTasksLists[ tskIDLE_PRIORITY ];
        listINSERT_END( &pxReadyTasksLists[ tskIDLE_PRIORITY ], &xTaskTCBs[ i ].xStateListItem );
        uxCurrentNumberOfTasks = uxCurrentNumberOfTasks + 1;
    }

    /* Create one more task to be removed from event list. */
    xTaskTCB.uxPriority = tskIDLE_PRIORITY;
    xTaskTCB.xStateListItem.pxContainer = &xSuspendedTaskList;
    xTaskTCB.xStateListItem.pvOwner = &xTaskTCB;
    listINSERT_END( &xSuspendedTaskList, &xTaskTCB.xStateListItem );
    xTaskTCB.xEventListItem.pxContainer = &xEventList;
    xTaskTCB.xEventListItem.pvOwner = &xTaskTCB;
    listINSERT_END( &xEventList, &xTaskTCB.xEventListItem );
    xTaskTCB.xTaskRunState = taskTASK_NOT_RUNNING;
    xTaskTCB.uxCoreAffinityMask = ( ( 1U << configNUMBER_OF_CORES ) - 1U );
    xTaskTCB.ulNotifiedValue[ uxIndexToNotify ] = 0x5a5a; /* Value to be verified in this test. */
    xTaskTCB.ucNotifyState[ uxIndexToNotify ] = taskWAITING_NOTIFICATION;
    uxCurrentNumberOfTasks = uxCurrentNumberOfTasks + 1;

    /* Clear callback in commonSetUp. */
    vFakePortGetCoreID_StubWithCallback( NULL );
    vFakePortEnterCriticalFromISR_StubWithCallback( NULL );
    vFakePortExitCriticalFromISR_StubWithCallback( NULL );

    /* Expectations. */
    vFakePortAssertIfInterruptPriorityInvalid_Expect();
    vFakePortEnterCriticalFromISR_ExpectAndReturn( xSavedInterruptMask );
    vFakePortGetCoreID_ExpectAndReturn( 0 );
    vFakePortGetCoreID_ExpectAndReturn( 0 );
    vFakePortGetCoreID_ExpectAndReturn( 0 );
    vFakePortExitCriticalFromISR_Expect( xSavedInterruptMask );

    /* API call. */
    vTaskGenericNotifyGiveFromISR( &xTaskTCB,
                                   uxIndexToNotify,
                                   &xHigherPriorityTaskWoken );

    /* Validation. */
    TEST_ASSERT_EQUAL( 0x5a5a + 1U, xTaskTCB.ulNotifiedValue[ uxIndexToNotify ] );
    TEST_ASSERT_EQUAL( pdTRUE, xHigherPriorityTaskWoken );
}

/**
 * @brief vTaskGenericNotifyGiveFromISR - Notify a higher priority task with NULL param.
 *
 * Notify a higher priority task from ISR. Higher priority task is woken. Input param
 * pxHigherPriorityTaskWoken is NULL.
 *
 * <b>Coverage</b>
 * @code{c}
 * #if ( configUSE_PREEMPTION == 1 )
 * {
 *     prvYieldForTask( pxTCB );
 *
 *     if( xYieldPendings[ portGET_CORE_ID() ] == pdTRUE )
 *     {
 *         if( pxHigherPriorityTaskWoken != NULL )
 *         {
 *             *pxHigherPriorityTaskWoken = pdTRUE;
 *         }
 *     }
 * }
 * #endif
 * @endcode
 * ( xYieldPendings[ portGET_CORE_ID() ] == pdTRUE ) is true.
 * ( pxHigherPriorityTaskWoken != NULL ) is false.
 */
void test_coverage_vTaskGenericNotifyGiveFromISR_priority_gt_null_param( void )
{
    TCB_t xTaskTCB = { NULL };
    TCB_t xTaskTCBs[ configNUMBER_OF_CORES ] = { NULL };
    UBaseType_t uxIndexToNotify = 0;    /* Use index 0 in this test. */
    BaseType_t xSavedInterruptMask = 0x1234;   /* Interrupt mask to be verified. */
    List_t xEventList = { 0 };
    uint32_t i;

    /* Setup the variables and structure. */
    uxSchedulerSuspended = pdFALSE;
    uxTopReadyPriority = tskIDLE_PRIORITY;
    vListInitialise( &xEventList );
    vListInitialise( &( pxReadyTasksLists[ tskIDLE_PRIORITY ] ) );
    vListInitialise( &xSuspendedTaskList );

    /* Create idle tasks and add it into the ready list. */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        xTaskTCBs[ i ].uxPriority = tskIDLE_PRIORITY;
        xTaskTCBs[ i ].xStateListItem.pvOwner = &xTaskTCBs[ i ];
        xTaskTCBs[ i ].uxCoreAffinityMask = ( ( 1U << configNUMBER_OF_CORES ) - 1U );
        if( i == 0 )
        {
            /* Core 0 is running an idle task in order to be requested to yield. */
            xTaskTCBs[ i ].uxTaskAttributes = taskATTRIBUTE_IS_IDLE;
        }
        else
        {
            /* Others are running a normal task. */
            xTaskTCBs[ i ].uxTaskAttributes = 0;
        }

        /* Create idle tasks with equal number of cores. */
        pxCurrentTCBs[ i ] = &xTaskTCBs[ i ];
        xTaskTCBs[ i ].xTaskRunState = i;
        xTaskTCBs[ i ].xStateListItem.pxContainer = &pxReadyTasksLists[ tskIDLE_PRIORITY ];
        listINSERT_END( &pxReadyTasksLists[ tskIDLE_PRIORITY ], &xTaskTCBs[ i ].xStateListItem );
        uxCurrentNumberOfTasks = uxCurrentNumberOfTasks + 1;
    }

    /* Create one more task to be removed from event list. */
    xTaskTCB.uxPriority = tskIDLE_PRIORITY;
    xTaskTCB.xStateListItem.pxContainer = &xSuspendedTaskList;
    xTaskTCB.xStateListItem.pvOwner = &xTaskTCB;
    listINSERT_END( &xSuspendedTaskList, &xTaskTCB.xStateListItem );
    xTaskTCB.xEventListItem.pxContainer = &xEventList;
    xTaskTCB.xEventListItem.pvOwner = &xTaskTCB;
    listINSERT_END( &xEventList, &xTaskTCB.xEventListItem );
    xTaskTCB.xTaskRunState = taskTASK_NOT_RUNNING;
    xTaskTCB.uxCoreAffinityMask = ( ( 1U << configNUMBER_OF_CORES ) - 1U );
    xTaskTCB.ulNotifiedValue[ uxIndexToNotify ] = 0x5a5a; /* Value to be verified in this test. */
    xTaskTCB.ucNotifyState[ uxIndexToNotify ] = taskWAITING_NOTIFICATION;
    uxCurrentNumberOfTasks = uxCurrentNumberOfTasks + 1;

    /* Clear callback in commonSetUp. */
    vFakePortGetCoreID_StubWithCallback( NULL );
    vFakePortEnterCriticalFromISR_StubWithCallback( NULL );
    vFakePortExitCriticalFromISR_StubWithCallback( NULL );

    /* Expectations. */
    vFakePortAssertIfInterruptPriorityInvalid_Expect();
    vFakePortEnterCriticalFromISR_ExpectAndReturn( xSavedInterruptMask );
    vFakePortGetCoreID_ExpectAndReturn( 0 );
    vFakePortGetCoreID_ExpectAndReturn( 0 );
    vFakePortGetCoreID_ExpectAndReturn( 0 );
    vFakePortExitCriticalFromISR_Expect( xSavedInterruptMask );

    /* API call. */
    vTaskGenericNotifyGiveFromISR( &xTaskTCB,
                                   uxIndexToNotify,
                                   NULL );

    /* Validation. */
    TEST_ASSERT_EQUAL( 0x5a5a + 1U, xTaskTCB.ulNotifiedValue[ uxIndexToNotify ] );
    TEST_ASSERT_EQUAL( pdTRUE, xYieldPendings[ 0 ] );
}

/**
 * @brief prvCheckTasksWaitingTermination - multiple idle tasks clean the deleted task.
 *
 * This test case cover the branch that the waiting termination tasks are already been
 * deleted by other idle tasks.
 *
 * <b>Coverage</b>
 * @code{c}
 * taskENTER_CRITICAL();
 * {
 *     ...
 *     if( uxDeletedTasksWaitingCleanUp > ( UBaseType_t ) 0U )
 *     {
 *         pxTCB = listGET_OWNER_OF_HEAD_ENTRY( ( &xTasksWaitingTermination ) );
 * @endcode
 * ( uxDeletedTasksWaitingCleanUp > ( UBaseType_t ) 0U ) is false.
 */
void test_coverage_prvCheckTasksWaitingTermination_multiple_idle_tasks( void )
{
    /* Setup the variables and structure. */
    uxDeletedTasksWaitingCleanUp = 1;

    /* Clear callback in commonSetUp. */
    vFakePortEnterCriticalSection_StubWithCallback( NULL );
    vFakePortExitCriticalSection_StubWithCallback( NULL );

    /* Expectations. */
    vFakePortEnterCriticalSection_StubWithCallback( prvPortEnterCriticalSectionCb );
    vFakePortExitCriticalSection_Expect();

    /* API call. */
    prvCheckTasksWaitingTermination();

    /* Validation. */
    /* No task is waiting to be cleand up. Nothing will be updated in this API. This
     * test case shows its result in the coverage report. */
}

/**
 * @brief prvCheckTasksWaitingTermination - delete not running task.
 *
 * A not running task is deleted. The number of tasks and number of tasks waiting to
 * be deleted are verified in this test case.
 *
 * <b>Coverage</b>
 * @code{c}
 * if( pxTCB->xTaskRunState == taskTASK_NOT_RUNNING )
 * {
 *     ( void ) uxListRemove( &( pxTCB->xStateListItem ) );
 *     --uxCurrentNumberOfTasks;
 *     --uxDeletedTasksWaitingCleanUp;
 * }
 * else
 * {
 *     ...
 *     taskEXIT_CRITICAL();
 *     break;
 * }
 * @endcode
 * ( pxTCB->xTaskRunState == taskTASK_NOT_RUNNING ) is true.
 */
void test_coverage_prvCheckTasksWaitingTermination_delete_not_running_task( void )
{
    TCB_t *pxTaskTCB = NULL;

    /* Setup the variables and structure. */
    UnityMalloc_StartTest();
    uxDeletedTasksWaitingCleanUp = 1;
    uxCurrentNumberOfTasks = 1;

    pxTaskTCB = pvPortMalloc( sizeof( TCB_t ) );
    pxTaskTCB->pxStack = pvPortMalloc( configMINIMAL_STACK_SIZE );
    pxTaskTCB->xTaskRunState = taskTASK_NOT_RUNNING ;
    pxTaskTCB->xStateListItem.pvOwner = pxTaskTCB;
    pxTaskTCB->xStateListItem.pxContainer = &xTasksWaitingTermination;
    listINSERT_END( &xTasksWaitingTermination, &pxTaskTCB->xStateListItem );

    /* Clear callback in commonSetUp. */
    vFakePortEnterCriticalSection_StubWithCallback( NULL );
    vFakePortExitCriticalSection_StubWithCallback( NULL );

    /* Expectations. */
    vFakePortEnterCriticalSection_Expect();
    vFakePortExitCriticalSection_Expect();

    /* API call. */
    prvCheckTasksWaitingTermination();

    /* Validation. */
    TEST_ASSERT_EQUAL( uxCurrentNumberOfTasks, 0 );
    TEST_ASSERT_EQUAL( uxDeletedTasksWaitingCleanUp, 0 );
    /* Validate the memory allocate count. */
    UnityMalloc_EndTest();
}

/**
 * @brief prvCheckTasksWaitingTermination - delete running task.
 *
 * A task to be deleted is still running. Nothing will be updated in this test case.
 * The test shows it's result in the coverage report.
 *
 * <b>Coverage</b>
 * @code{c}
 * if( pxTCB->xTaskRunState == taskTASK_NOT_RUNNING )
 * {
 *     ( void ) uxListRemove( &( pxTCB->xStateListItem ) );
 *     --uxCurrentNumberOfTasks;
 *     --uxDeletedTasksWaitingCleanUp;
 * }
 * else
 * {
 *     ...
 *     taskEXIT_CRITICAL();
 *     break;
 * }
 * @endcode
 * ( pxTCB->xTaskRunState == taskTASK_NOT_RUNNING ) is false.
 */
void test_coverage_prvCheckTasksWaitingTermination_delete_running_task( void )
{
    TCB_t *pxTaskTCB = NULL;

    /* Setup the variables and structure. */
    UnityMalloc_StartTest();
    uxDeletedTasksWaitingCleanUp = 1;
    uxCurrentNumberOfTasks = 1;

    pxTaskTCB = pvPortMalloc( sizeof( TCB_t ) );
    pxTaskTCB->pxStack = pvPortMalloc( configMINIMAL_STACK_SIZE );
    pxTaskTCB->xTaskRunState = 0 ;
    pxTaskTCB->xStateListItem.pvOwner = pxTaskTCB;
    pxTaskTCB->xStateListItem.pxContainer = &xTasksWaitingTermination;
    listINSERT_END( &xTasksWaitingTermination, &pxTaskTCB->xStateListItem );

    /* Clear callback in commonSetUp. */
    vFakePortEnterCriticalSection_StubWithCallback( NULL );
    vFakePortExitCriticalSection_StubWithCallback( NULL );

    /* Expectations. */
    vFakePortEnterCriticalSection_Expect();
    vFakePortExitCriticalSection_Expect();

    /* API call. */
    prvCheckTasksWaitingTermination();

    /* Validation. */
    /* If the task is not of taskTASK_NOT_RUNNING state, nothing will be updated.
     * This test shows it's result in coverage report. Verify that the number of
     * deleted task is not changed. */
    TEST_ASSERT_EQUAL( uxDeletedTasksWaitingCleanUp, 1 );
    TEST_ASSERT_EQUAL( uxCurrentNumberOfTasks, 1 );

    /* Free the resource allocated in this test. Since running task can't be deleted,
     * there won't have double free assertion. */
    vPortFree( pxTaskTCB );
    vPortFree( pxTaskTCB->pxStack );
    /* Validate the memory allocate count. */
    UnityMalloc_EndTest();
}

/**
 * @brief prvDeleteTCB - clean up the memory utilised by a TCB and its stack.
 *
 * <b>Coverage</b>
 * @code{c}
 *  else if( pxTCB->ucStaticallyAllocated == tskSTATICALLY_ALLOCATED_STACK_ONLY )
 *  {
 *      ...
 *      vPortFree( pxTCB )
 * @endcode
 *
 * Cover the case where the stack allocation is static.
 */
void test_coverage_prvDeleteTCB_static_stack_only(void)
{
    TCB_t *pxTaskTCB;

    UnityMalloc_StartTest();
    pxTaskTCB = pvPortMalloc( sizeof(TCB_t) );

    pxTaskTCB->uxPriority = 1;
    pxTaskTCB->xTaskRunState = 0;
    pxTaskTCB->ucStaticallyAllocated = tskSTATICALLY_ALLOCATED_STACK_ONLY;
    /* Default core is 0. This can be updated with vSetCurrentCore. */
    xYieldPendings[ 0 ] = pdFALSE;
    pxCurrentTCBs[ 0 ] = pxTaskTCB;

    prvDeleteTCB( pxTaskTCB );

    /* Validate the memory allocate count to ensure that allocated stack is freed. */
    UnityMalloc_EndTest();
}

/** @brief xTaskResumeFromISR - resume task from within ISR context
 *
 * <b>Coverage</b>
 * @code{c}
 *      if( prvTaskIsTaskSuspended( pxTCB ) != pdFALSE )
 *      {
 *          traceTASK_RESUME_FROM_ISR( pxTCB );
 *          ...
 *          if( uxSchedulerSuspended == ( UBaseType_t ) pdFALSE )
 *          {
 *              ...
 *              prvAddTaskToReadyList( pxTCB );
 * @endcode
 *
 * Cover the case where the scheduler is not suspended, and the
 * task being resumed is suspended.
 *
 */
void test_coverage_xTaskResumeFromISR_task_suspended_uxpriority_greater(void)
{
    TCB_t xTaskTCBs[ 2 ] = { NULL };
    BaseType_t xAlreadyYielded;
    UBaseType_t uxCore;
    List_t xList;

    /* Create a task as current running task on core 0. */
    xTaskTCBs[0].uxPriority = 1;
    xTaskTCBs[0].xTaskRunState = 0;
    vListInitialiseItem(&(xTaskTCBs[0].xStateListItem));
    listINSERT_END( &pxReadyTasksLists[ xTaskTCBs[0].uxPriority ], &xTaskTCBs[0].xStateListItem );
    listSET_LIST_ITEM_OWNER(&(xTaskTCBs[0].xStateListItem), &xTaskTCBs[0]);
    uxCurrentNumberOfTasks = uxCurrentNumberOfTasks + 1;

    /* Create a task in the suspended list. */
    xTaskTCBs[1].uxPriority = 2;
    xTaskTCBs[1].xTaskRunState = taskTASK_NOT_RUNNING;
    vListInitialiseItem(&(xTaskTCBs[1].xStateListItem));
    listSET_LIST_ITEM_OWNER(&(xTaskTCBs[1].xStateListItem), &xTaskTCBs[1]);
    listINSERT_END( &xSuspendedTaskList, &xTaskTCBs[1].xStateListItem );
    vListInitialise(&xList);
    uxCurrentNumberOfTasks = uxCurrentNumberOfTasks + 1;

    uxTopReadyPriority = 1;

    /* Default value for portGET_CORE_ID is 0. This can be changed with vSetCurrentCore. */
    xYieldPendings[ 0 ] = pdFALSE;
    pxCurrentTCBs[ 0 ] = &xTaskTCBs[0];

    for(uxCore = 0U; uxCore < configNUMBER_OF_CORES; uxCore++ )
    {
        if (pxCurrentTCBs[uxCore] == NULL)
        {
            pxCurrentTCBs[uxCore] = &xTaskTCBs[0];
        }
    }

    xSchedulerRunning = pdTRUE;
    uxSchedulerSuspended = pdFALSE;
    xPendedTicks = 0;      /* No pending tick in this test. */

    /* Expectations. */
    vFakePortAssertIfInterruptPriorityInvalid_Ignore();

    /* API call. */
    xAlreadyYielded = xTaskResumeFromISR( &xTaskTCBs[1] );

    /* Validation. */
    /* The task priority is no higher than current running task. */
    TEST_ASSERT_EQUAL( pdFALSE, xAlreadyYielded );
    /* The task in pending ready list should not in any event list now. */
    TEST_ASSERT_EQUAL( xTaskTCBs[1].xEventListItem.pvContainer, NULL );
    /* The task in pending ready list should be added back to ready list. */
    TEST_ASSERT_EQUAL( xTaskTCBs[1].xStateListItem.pvContainer, &pxReadyTasksLists[ xTaskTCBs[1].uxPriority ] );
}

/** @brief xTaskResumeFromISR - resume task from within ISR context
 *
 * <b>Coverage</b>
 * @code{c}
 *      if( prvTaskIsTaskSuspended( pxTCB ) != pdFALSE )
 *      {
 *          traceTASK_RESUME_FROM_ISR( pxTCB );
 *          ...
 *          if( uxSchedulerSuspended == ( UBaseType_t ) pdFALSE )
 *          {
 *              ...
 *              prvAddTaskToReadyList( pxTCB );
 * @endcode
 *
 * Cover the case where the scheduler is not suspended, and the
 * task being resumed is suspended.
 *
 */
void test_coverage_xTaskResumeFromISR_task_suspended_uxpriority_lesser(void)
{
    TCB_t xTaskTCBs[ 2 ] = { NULL };
    BaseType_t xAlreadyYielded;
    UBaseType_t uxCore;
    List_t xList;

    /* Create a task as current running task on core 0. */
    xTaskTCBs[0].uxPriority = 1;
    xTaskTCBs[0].xTaskRunState = 0;
    vListInitialiseItem(&(xTaskTCBs[0].xStateListItem));
    listINSERT_END( &pxReadyTasksLists[ xTaskTCBs[0].uxPriority ], &xTaskTCBs[0].xStateListItem );
    listSET_LIST_ITEM_OWNER(&(xTaskTCBs[0].xStateListItem), &xTaskTCBs[0]);
    uxCurrentNumberOfTasks = uxCurrentNumberOfTasks + 1;

    /* Create a task in the suspended list. */
    xTaskTCBs[1].uxPriority = 0;
    xTaskTCBs[1].xTaskRunState = taskTASK_NOT_RUNNING;
    vListInitialiseItem(&(xTaskTCBs[1].xStateListItem));
    listSET_LIST_ITEM_OWNER(&(xTaskTCBs[1].xStateListItem), &xTaskTCBs[1]);
    listINSERT_END( &xSuspendedTaskList, &xTaskTCBs[1].xStateListItem );
    vListInitialise(&xList);
    uxCurrentNumberOfTasks = uxCurrentNumberOfTasks + 1;

    uxTopReadyPriority = 1;

    /* Default value for portGET_CORE_ID is 0. This can be changed with vSetCurrentCore. */
    xYieldPendings[ 0 ] = pdFALSE;
    pxCurrentTCBs[ 0 ] = &xTaskTCBs[0];

    for(uxCore = 0U; uxCore < configNUMBER_OF_CORES; uxCore++ )
    {
        if (pxCurrentTCBs[uxCore] == NULL)
        {
            pxCurrentTCBs[uxCore] = &xTaskTCBs[0];
        }
    }

    xSchedulerRunning = pdTRUE;
    uxSchedulerSuspended = pdFALSE;
    xPendedTicks = 0;      /* No pending tick in this test. */

    /* Expectations. */
    vFakePortAssertIfInterruptPriorityInvalid_Ignore();

    /* API call. */
    xAlreadyYielded = xTaskResumeFromISR( &xTaskTCBs[1] );

    /* Validation. */
    /* The task priority is no higher than current running task. */
    TEST_ASSERT_EQUAL( pdFALSE, xAlreadyYielded );
    /* The task in pending ready list should not in any event list now. */
    TEST_ASSERT_EQUAL( xTaskTCBs[1].xEventListItem.pvContainer, NULL );
    /* The task in pending ready list should be added back to ready list. */
    TEST_ASSERT_EQUAL( xTaskTCBs[1].xStateListItem.pvContainer, &pxReadyTasksLists[ xTaskTCBs[1].uxPriority ] );
}



/** @brief xTaskResumeAll - resume all suspended tasks
 *
 * <b>Coverage</b>
 * @code{c}
 *  while( listLIST_IS_EMPTY( &xPendingReadyList ) == pdFALSE )
 *  {
 *      ...
 * @endcode
 *
 * Cover the case where the scheduler is running and suspended,
 * there are tasks and at least one is in the pending ready list.
 *
 */
void test_coverage_xTaskResumeAll_task_in_pending_ready_list(void)
{
    TCB_t xTaskTCBs[ 2 ] = { NULL };
    BaseType_t xAlreadyYielded;
    List_t xList;

     /* Create a task as current running task on core 0. */
    xTaskTCBs[0].uxPriority = 1;
    xTaskTCBs[0].xTaskRunState = 0;
    vListInitialiseItem(&(xTaskTCBs[0].xStateListItem));
    listINSERT_END( &pxReadyTasksLists[ xTaskTCBs[0].uxPriority ], &xTaskTCBs[0].xStateListItem );
    listSET_LIST_ITEM_OWNER(&(xTaskTCBs[0].xStateListItem), &xTaskTCBs[0]);
    uxCurrentNumberOfTasks = uxCurrentNumberOfTasks + 1;

    /* Create a task in the pending ready list. */
    xTaskTCBs[1].uxPriority = 2;        /* The priority is not higher than current running task. */
    xTaskTCBs[1].xTaskRunState = taskTASK_NOT_RUNNING;
    vListInitialiseItem(&(xTaskTCBs[1].xStateListItem));
    listSET_LIST_ITEM_OWNER(&(xTaskTCBs[1].xStateListItem), &xTaskTCBs[1]);
    listINSERT_END( &xPendingReadyList, &xTaskTCBs[1].xStateListItem );
    vListInitialise(&xList);
    vListInitialiseItem(&(xTaskTCBs[1].xEventListItem));
    listSET_LIST_ITEM_VALUE(&(xTaskTCBs[1].xEventListItem),
                          taskEVENT_LIST_ITEM_VALUE_IN_USE);
    listINSERT_END(&xList, &(xTaskTCBs[1].xEventListItem));
    uxCurrentNumberOfTasks = uxCurrentNumberOfTasks + 1;

    /* Default value for portGET_CORE_ID is 0. This can be changed with vSetCurrentCore. */
    xYieldPendings[ 0 ] = pdFALSE;
    pxCurrentTCBs[ 0 ] = &xTaskTCBs[0];

    uxTopReadyPriority = 1;
    xSchedulerRunning = pdTRUE;
    uxSchedulerSuspended = pdTRUE;
    xPendedTicks = 0;      /* No pending tick in this test. */

    /* Clear setup in commonSetUp. */
    vFakePortReleaseTaskLock_StubWithCallback( NULL );
    vFakePortExitCriticalSection_StubWithCallback( NULL );

    /* Expectations. */
    vFakePortReleaseTaskLock_Expect();
    vFakePortExitCriticalSection_Expect();

    /* API call. */
    xAlreadyYielded = xTaskResumeAll();

    /* Validation. */
    /* The task priority is no higher than current running task. */
    TEST_ASSERT_EQUAL( pdFALSE, xAlreadyYielded );
    /* The task in pending ready list should not in any event list now. */
    TEST_ASSERT_EQUAL( xTaskTCBs[1].xEventListItem.pvContainer, NULL );
    /* The task in pending ready list should be added back to ready list. */
    TEST_ASSERT_EQUAL( xTaskTCBs[1].xStateListItem.pvContainer, &pxReadyTasksLists[ xTaskTCBs[1].uxPriority ] );
}

/** @brief xTaskResumeAll - resume all suspended tasks
 *
 * <b>Coverage</b>
 * @code{c}
 *  while( listLIST_IS_EMPTY( &xPendingReadyList ) == pdFALSE )
 *  {
 *      ...
 * @endcode
 *
 * Cover the case where the scheduler is running and suspended,
 * there are tasks and at least one is in the pending ready list
 * with a priority less than uxTopReadyPriority.
 *
 */
void test_coverage_xTaskResumeAll_task_in_pending_ready_list_uxpriority_lesser(void)
{
    TCB_t xTaskTCBs[ 2 ] = { NULL };
    BaseType_t xAlreadyYielded;
    List_t xList;

    /* Create a task as current running task on core 0. */
    xTaskTCBs[0].uxPriority = 1;
    xTaskTCBs[0].xTaskRunState = 0;
    vListInitialiseItem(&(xTaskTCBs[0].xStateListItem));
    listINSERT_END( &pxReadyTasksLists[ xTaskTCBs[0].uxPriority ], &xTaskTCBs[0].xStateListItem );
    listSET_LIST_ITEM_OWNER(&(xTaskTCBs[0].xStateListItem), &xTaskTCBs[0]);
    uxCurrentNumberOfTasks = uxCurrentNumberOfTasks + 1;

    /* Create a task in the pending ready list. */
    xTaskTCBs[1].uxPriority = 0;        /* The priority is not higher than current running task. */
    xTaskTCBs[1].xTaskRunState = taskTASK_NOT_RUNNING;
    vListInitialiseItem(&(xTaskTCBs[1].xStateListItem));
    listSET_LIST_ITEM_OWNER(&(xTaskTCBs[1].xStateListItem), &xTaskTCBs[1]);
    listINSERT_END( &xPendingReadyList, &xTaskTCBs[1].xStateListItem );
    vListInitialise(&xList);
    vListInitialiseItem(&(xTaskTCBs[1].xEventListItem));
    listSET_LIST_ITEM_VALUE(&(xTaskTCBs[1].xEventListItem),
                          taskEVENT_LIST_ITEM_VALUE_IN_USE);
    listINSERT_END(&xList, &(xTaskTCBs[1].xEventListItem));
    uxCurrentNumberOfTasks = uxCurrentNumberOfTasks + 1;

    /* Default value for portGET_CORE_ID is 0. This can be changed with vSetCurrentCore. */
    xYieldPendings[ 0 ] = pdFALSE;
    pxCurrentTCBs[ 0 ] = &xTaskTCBs[0];

    uxTopReadyPriority = 1;
    xSchedulerRunning = pdTRUE;
    uxSchedulerSuspended = pdTRUE;
    xPendedTicks = 0;      /* No pending tick in this test. */

    /* Clear setup in commonSetUp. */
    vFakePortReleaseTaskLock_StubWithCallback( NULL );
    vFakePortExitCriticalSection_StubWithCallback( NULL );

    /* Expectations. */
    vFakePortReleaseTaskLock_Expect();
    vFakePortExitCriticalSection_Expect();

    /* API call. */
    xAlreadyYielded = xTaskResumeAll();

    /* Validation. */
    /* The task priority is no higher than current running task. */
    TEST_ASSERT_EQUAL( pdFALSE, xAlreadyYielded );
    /* The task in pending ready list should not in any event list now. */
    TEST_ASSERT_EQUAL( xTaskTCBs[1].xEventListItem.pvContainer, NULL );
    /* The task in pending ready list should be added back to ready list. */
    TEST_ASSERT_EQUAL( xTaskTCBs[1].xStateListItem.pvContainer, &pxReadyTasksLists[ xTaskTCBs[1].uxPriority ] );
}

/**
 * @brief vTaskResume - resume a suspended task.
 *
 * <b>Coverage</b>
 * @code{c}
 * if( pxTCB != NULL )
 * {
 *     ...
 * }
 * @endcode
 * ( pxTCB != NULL ) is false.
 */
void test_coverage_vTaskResume_null_task( void )
{
    vTaskResume(NULL);

    /* In this case no state is changed and so no assertion can be made to
     * validate the operation. */
}

/**
 * @brief xTaskGenericNotify - function to notify a task.
 *
 * <b>Coverage</b>
 * @code{c}
 * if( ucOriginalNotifyState == taskWAITING_NOTIFICATION )
 * {
 *     ...
 * @endcode
 *
 * Cover the case where the ucOriginalNotifyState is taskWAITING_NOTIFICATION.
 */
void test_coverage_xTaskGenericNotify_with_eAction_equalto_eNoAction_taskWAITING_NOTIFICATION_uxpriority_lesser( void )
{
    TCB_t xTaskTCBs[ 2U ] = { NULL };
    UBaseType_t xidx = 0;
    uint32_t prevValue;
    BaseType_t xReturn;
    UBaseType_t uxCoreID;

    xTaskTCBs[ 0 ].uxPriority = 1;
    xTaskTCBs[ 0 ].xTaskRunState = 0;
    vListInitialiseItem( &( xTaskTCBs[0].xStateListItem ) );
    listSET_LIST_ITEM_OWNER( &( xTaskTCBs[0].xStateListItem ), &xTaskTCBs[0] );
    listINSERT_END( &xPendingReadyList, &xTaskTCBs[ 0 ].xStateListItem );

    /* Default core ID is 0. The can be changed with vSetCurrentCore. */
    xYieldPendings[ 0 ] = pdFALSE;
    pxCurrentTCBs[ 0 ] = &xTaskTCBs[ 0 ];

    xTaskTCBs[ 1 ].uxPriority = 1;
    xTaskTCBs[ 1 ].xTaskRunState = -1;

    for( uxCoreID = 0; uxCoreID < configNUMBER_OF_CORES; uxCoreID++ )
    {
        if (pxCurrentTCBs[ uxCoreID ] == NULL)
        {
            pxCurrentTCBs[ uxCoreID ] = &xTaskTCBs[ 1 ];
        }
    }

    uxTopReadyPriority = 2;
    uxSchedulerSuspended = pdTRUE;
    xTaskTCBs[0].ucNotifyState[ xidx ] = taskWAITING_NOTIFICATION;
    xTaskTCBs[0].ulNotifiedValue[ xidx ] = 0xa5a5;      /* Value to be verified later. */

    xReturn = xTaskGenericNotify( &xTaskTCBs[0], xidx, 0x0, eNoAction, &prevValue);

    TEST_ASSERT_EQUAL_UINT32( 0xa5a5, prevValue );
    TEST_ASSERT( xReturn == pdPASS );
}

/**
 * @brief xTaskGenericNotify - function to notify a task.
 *
 * <b>Coverage</b>
 * @code{c}
 * if( ucOriginalNotifyState == taskWAITING_NOTIFICATION )
 * {
 *     ...
 * @endcode
 *
 * Cover the case where the ucOriginalNotifyState is taskWAITING_NOTIFICATION.
 */
void test_coverage_xTaskGenericNotify_with_eAction_equalto_eNoAction_taskWAITING_NOTIFICATION_uxpriority_greater( void )
{
    TCB_t xTaskTCBs[ 2U ] = { NULL };
    UBaseType_t xidx = 0;
    uint32_t prevValue;
    BaseType_t xReturn;
    UBaseType_t uxCoreID;

    xTaskTCBs[ 0 ].uxPriority = 2;
    xTaskTCBs[ 0 ].xTaskRunState = 0;
    vListInitialiseItem( &( xTaskTCBs[0].xStateListItem ) );
    listSET_LIST_ITEM_OWNER( &( xTaskTCBs[0].xStateListItem ), &xTaskTCBs[0] );
    listINSERT_END( &xPendingReadyList, &xTaskTCBs[ 0 ].xStateListItem );

    /* Default core ID is 0. The can be changed with vSetCurrentCore. */
    xYieldPendings[ 0 ] = pdFALSE;
    pxCurrentTCBs[ 0 ] = &xTaskTCBs[ 0 ];

    xTaskTCBs[ 1 ].uxPriority = 1;
    xTaskTCBs[ 1 ].xTaskRunState = -1;

    for( uxCoreID = 0; uxCoreID < configNUMBER_OF_CORES; uxCoreID++ )
    {
        if (pxCurrentTCBs[ uxCoreID ] == NULL)
        {
            pxCurrentTCBs[ uxCoreID ] = &xTaskTCBs[ 1 ];
        }
    }

    uxTopReadyPriority = 1;
    uxSchedulerSuspended = pdTRUE;
    xTaskTCBs[0].ucNotifyState[ xidx ] = taskWAITING_NOTIFICATION;
    xTaskTCBs[0].ulNotifiedValue[ xidx ] = 0xa5a5;      /* Value to be verified later. */

    xReturn = xTaskGenericNotify( &xTaskTCBs[0], xidx, 0x0, eNoAction, &prevValue);

    TEST_ASSERT_EQUAL_UINT32( 0xa5a5, prevValue );
    TEST_ASSERT( xReturn == pdPASS );
}


/**
 * @brief vTaskGetInfo - populate TaskStatus_t and eTaskState
 *
 * <b>Coverage</b>
 * @code{c}
 *        pxTCB = prvGetTCBFromHandle( xTask );
 *          ...
 * @endcode
 *
 * Cover the case where xTask is NULL, and the current task is implicitly
 * referenced and returned by prvGetTCBFromHandle(...);
 */
void test_coverage_vTaskGetInfo_implicit_task( void )
{
    TCB_t xTaskTCBs[ 1U ] = { NULL };
    TaskStatus_t pxTaskStatus;
    BaseType_t xFreeStackSpace = pdFALSE;
    eTaskState taskState = eReady;

    xTaskTCBs[ 0 ].uxPriority = 1;
    xTaskTCBs[ 0 ].uxBasePriority = 0;
    xTaskTCBs[ 0 ].xTaskRunState = 0;
    xTaskTCBs[ 0 ].uxCoreAffinityMask = ( ( 1U << ( configNUMBER_OF_CORES ) ) - 1U );
    xTaskTCBs[ 0 ].uxTCBNumber = 1;
    xTaskTCBs[ 0 ].pxStack = ( StackType_t * ) 0x1234;      /* The value to be verified later. */

    xYieldPendings[ 0 ] = pdFALSE;
    pxCurrentTCBs[ 0 ] = &xTaskTCBs[ 0 ];

    uxTopReadyPriority = 1;
    uxSchedulerSuspended = pdTRUE;

    vTaskGetInfo( NULL, &pxTaskStatus, xFreeStackSpace, taskState );

    TEST_ASSERT_EQUAL( &xTaskTCBs[ 0 ], pxTaskStatus.xHandle );
    TEST_ASSERT_EQUAL( xTaskTCBs[ 0 ].pcTaskName, pxTaskStatus.pcTaskName );
    TEST_ASSERT_EQUAL( ( UBaseType_t ) 1, pxTaskStatus.xTaskNumber );
    TEST_ASSERT_EQUAL( eRunning, pxTaskStatus.eCurrentState );
    TEST_ASSERT_EQUAL( ( BaseType_t ) 1, pxTaskStatus.uxCurrentPriority );
    TEST_ASSERT_EQUAL( ( BaseType_t ) 0, pxTaskStatus.uxBasePriority );
    TEST_ASSERT_EQUAL( ( StackType_t * ) 0x1234, pxTaskStatus.pxStackBase );
    TEST_ASSERT_EQUAL( ( ( 1U << ( configNUMBER_OF_CORES ) ) - 1U ), pxTaskStatus.uxCoreAffinityMask );
    TEST_ASSERT_EQUAL( 0, pxTaskStatus.usStackHighWaterMark );
}

/**
 * @brief vTaskGetInfo - populate TaskStatus_t and eTaskState
 *
 * <b>Coverage</b>
 * @code{c}
 *       if( taskTASK_IS_RUNNING( pxTCB ) == pdTRUE )
 *       {
 *           pxTaskStatus->eCurrentState = eRunning;
 *       }
 *       ...
 * @endcode
 *
 * Cover the case in the taskTASK_IS_RUNNING() macro where the xTaskRunState
 * is out of bounds.
 */
void test_coverage_vTaskGetInfo_oob_xTaskRunState( void )
{
    TCB_t xTaskTCBs[ 1U ] = { NULL };
    TaskStatus_t pxTaskStatus;
    BaseType_t xFreeStackSpace = pdFALSE;
    eTaskState taskState = eSuspended;

    xTaskTCBs[ 0 ].uxPriority = 1;
    xTaskTCBs[ 0 ].xTaskRunState = configNUMBER_OF_CORES;
    xYieldPendings[ 0 ] = pdFALSE;
    pxCurrentTCBs[ 0 ] = &xTaskTCBs[ 0 ];

    uxTopReadyPriority = 1;
    uxSchedulerSuspended = pdTRUE;

    vTaskGetInfo( &xTaskTCBs[ 0 ], &pxTaskStatus, xFreeStackSpace, taskState );

    TEST_ASSERT_EQUAL( ( UBaseType_t ) 0, pxTaskStatus.xTaskNumber );
    TEST_ASSERT_EQUAL( eSuspended, pxTaskStatus.eCurrentState );
    TEST_ASSERT_EQUAL( ( UBaseType_t ) 1, pxTaskStatus.uxCurrentPriority );
    TEST_ASSERT_EQUAL( ( UBaseType_t ) 0, pxTaskStatus.uxBasePriority );
    TEST_ASSERT_EQUAL( 0, pxTaskStatus.usStackHighWaterMark );
}

/**
 * @brief vTaskGetInfo - populate TaskStatus_t and eTaskState
 *
 * <b>Coverage</b>
 * @code{c}
 * if( listLIST_ITEM_CONTAINER( &( pxTCB->xEventListItem ) ) != NULL )
 * {
 *     pxTaskStatus->eCurrentState = eBlocked;
 * }
 * ...
 * @endcode
 *
 * Cover the case where the task is blocked.
 */
void test_coverage_vTaskGetInfo_blocked_task( void )
{
    TCB_t xTaskTCBs[ 1U ] = { NULL };
    TaskStatus_t pxTaskStatus;
    BaseType_t xFreeStackSpace = pdFALSE;
    eTaskState taskState = eSuspended;

    /* Setup the variables and structure. */
    xTaskTCBs[ 0 ].uxPriority = 2;
    xTaskTCBs[ 0 ].uxBasePriority = 0;
    xTaskTCBs[ 0 ].xTaskRunState = -1;
    xTaskTCBs[ 0 ].uxTCBNumber = 1;
    xYieldPendings[ 0 ] = pdFALSE;
    pxCurrentTCBs[ 0 ] = &xTaskTCBs[ 0 ];
    listINSERT_END( &xSuspendedTaskList, &xTaskTCBs[ 0 ].xStateListItem );

    uxTopReadyPriority = 2;
    uxSchedulerSuspended = pdTRUE;

    xTaskTCBs[ 0 ].xEventListItem.pxContainer = ( struct xLIST * ) 1;

    vTaskGetInfo( &xTaskTCBs[ 0 ], &pxTaskStatus, xFreeStackSpace, taskState );

    TEST_ASSERT_EQUAL( ( UBaseType_t ) 1, pxTaskStatus.xTaskNumber );
    TEST_ASSERT_EQUAL( eBlocked, pxTaskStatus.eCurrentState );
    TEST_ASSERT_EQUAL( ( UBaseType_t ) 2, pxTaskStatus.uxCurrentPriority );
    TEST_ASSERT_EQUAL( ( UBaseType_t ) 0, pxTaskStatus.uxBasePriority );
    TEST_ASSERT_EQUAL( 0, pxTaskStatus.usStackHighWaterMark );
}

/**
 * @brief vTaskGetInfo - populate TaskStatus_t and eTaskState
 *
 * <b>Coverage</b>
 * @code{c}
 *       if( taskTASK_IS_RUNNING( pxTCB ) == pdTRUE )
 *       {
 *           pxTaskStatus->eCurrentState = eRunning;
 *       }
 *       ...
 * @endcode
 *
 * Cover the case where xFreeStackSpace is pdTRUE, avoiding the free
 * stack space query.
 */
void test_coverage_vTaskGetInfo_get_free_stack_space( void )
{
    TCB_t xTaskTCBs[ 1U ] = { NULL };
    TaskStatus_t pxTaskStatus;
    BaseType_t xFreeStackSpace = pdTRUE;
    eTaskState taskState = eReady;

    xTaskTCBs[ 0 ].uxPriority = 1;
    xTaskTCBs[ 0 ].uxBasePriority = 0;
    xTaskTCBs[ 0 ].xTaskRunState = 0;
    prvInitialiseTestStack( &xTaskTCBs[ 0 ], configMINIMAL_STACK_SIZE );
    xYieldPendings[ 0 ] = pdFALSE;
    pxCurrentTCBs[ 0 ] = &xTaskTCBs[ 0 ];

    uxTopReadyPriority = 1;
    uxSchedulerSuspended = pdTRUE;

    vTaskGetInfo( &xTaskTCBs[ 0 ], &pxTaskStatus, xFreeStackSpace, taskState );

    TEST_ASSERT_EQUAL( ( UBaseType_t ) 0, pxTaskStatus.xTaskNumber );
    TEST_ASSERT_EQUAL( eRunning, pxTaskStatus.eCurrentState );
    TEST_ASSERT_EQUAL( ( UBaseType_t ) 1, pxTaskStatus.uxCurrentPriority );
    TEST_ASSERT_EQUAL( ( UBaseType_t ) 0, pxTaskStatus.uxBasePriority );
    /* The stack is not used in this test. The high water mark is the index of the stack. */
    TEST_ASSERT_EQUAL( ( configMINIMAL_STACK_SIZE - 1 ) , pxTaskStatus.usStackHighWaterMark );
}

/** 
 * @brief xTaskPriorityInherit - inherit the priority of the mutex holder
 *
 * <b>Coverage</b>
 * @code{c}
 *  if( listIS_CONTAINED_WITHIN( &( pxReadyTasksLists[ pxMutexHolderTCB->uxPriority ] ), &( pxMutexHolderTCB->xStateListItem ) ) != pdFALSE )
 *  {
 *      ...
 *      prvAddTaskToReadyList( pxMutexHolderTCB );
 * @endcode
 *
 * Cover the case where a non-NULL task is specified, and this task has a
 * priority lesser than the current task. Furthermore than the specified
 * task is in the ready task list. Finally that the uxpriority of the
 * specified task is less than uxtopreadypriority.
 *
 */
void test_coverage_xTaskPriorityInherit_task_uxpriority_lesser(void)
{
    TCB_t xTaskTCBs[ 2 ] = { NULL };
    BaseType_t xReturn;
    UBaseType_t uxCore;
    List_t xList;

    /* Create a task as current running task on core 0. */
    xTaskTCBs[0].uxPriority = 1;
    xTaskTCBs[0].xTaskRunState = 0;
    vListInitialiseItem(&(xTaskTCBs[0].xStateListItem));
    listINSERT_END( &pxReadyTasksLists[ xTaskTCBs[0].uxPriority ], &xTaskTCBs[0].xStateListItem );
    listSET_LIST_ITEM_OWNER(&(xTaskTCBs[0].xStateListItem), &xTaskTCBs[0]);
    uxCurrentNumberOfTasks = uxCurrentNumberOfTasks + 1;

    /* Create a task in the suspended list. */
    xTaskTCBs[1].uxPriority = 0;
    xTaskTCBs[1].xTaskRunState = taskTASK_NOT_RUNNING;
    vListInitialiseItem(&(xTaskTCBs[1].xStateListItem));
    listSET_LIST_ITEM_OWNER(&(xTaskTCBs[1].xStateListItem), &xTaskTCBs[1]);
    listINSERT_END( &pxReadyTasksLists[ xTaskTCBs[1].uxPriority ], &xTaskTCBs[1].xStateListItem );
    vListInitialise(&xList);
    uxCurrentNumberOfTasks = uxCurrentNumberOfTasks + 1;

    uxTopReadyPriority = 1;

    /* Default value for portGET_CORE_ID is 0. This can be changed with vSetCurrentCore. */
    xYieldPendings[ 0 ] = pdFALSE;
    pxCurrentTCBs[ 0 ] = &xTaskTCBs[0];

    for(uxCore = 0U; uxCore < configNUMBER_OF_CORES; uxCore++ )
    {
        if (pxCurrentTCBs[uxCore] == NULL)
        {
            pxCurrentTCBs[uxCore] = &xTaskTCBs[0];
        }
    }

    xSchedulerRunning = pdTRUE;
    uxSchedulerSuspended = pdFALSE;
    xPendedTicks = 0;      /* No pending tick in this test. */

    /* API call. */
    xReturn = xTaskPriorityInherit( &xTaskTCBs[1] );

    /* Validation. */
    /* The task priority is no higher than current running task. */
    TEST_ASSERT_EQUAL( pdTRUE, xReturn );
    /* The task in pending ready list should not in any event list now. */
    TEST_ASSERT_EQUAL( xTaskTCBs[1].xEventListItem.pvContainer, NULL );
    /* The task in pending ready list should be added back to ready list. */
    TEST_ASSERT_EQUAL( xTaskTCBs[1].xStateListItem.pvContainer, &pxReadyTasksLists[ xTaskTCBs[1].uxPriority ] );
}

/** 
 * @brief xTaskPriorityInherit - inherit the priority of the mutex holder
 *
 * <b>Coverage</b>
 * @code{c}
 *  if( listIS_CONTAINED_WITHIN( &( pxReadyTasksLists[ pxMutexHolderTCB->uxPriority ] ), &( pxMutexHolderTCB->xStateListItem ) ) != pdFALSE )
 *  {
 *      ...
 *      prvAddTaskToReadyList( pxMutexHolderTCB );
 * @endcode
 *
 * Cover the case where a non-NULL task is specified, and this task has a
 * priority lesser than the current task. Furthermore than the specified
 * task is in the ready task list. Finally that the uxpriority of the
 * specified task is greater than uxtopreadypriority.
 *
 */
void test_coverage_xTaskPriorityInherit_task_uxpriority_greater(void)
{
    TCB_t xTaskTCBs[ 2 ] = { NULL };
    BaseType_t xReturn;
    UBaseType_t uxCore;
    List_t xList;

    /* Create a task as current running task on core 0. */
    xTaskTCBs[0].uxPriority = 3;
    xTaskTCBs[0].xTaskRunState = 0;
    vListInitialiseItem(&(xTaskTCBs[0].xStateListItem));
    listINSERT_END( &pxReadyTasksLists[ xTaskTCBs[0].uxPriority ], &xTaskTCBs[0].xStateListItem );
    listSET_LIST_ITEM_OWNER(&(xTaskTCBs[0].xStateListItem), &xTaskTCBs[0]);
    uxCurrentNumberOfTasks = uxCurrentNumberOfTasks + 1;

    /* Create a task in the suspended list. */
    xTaskTCBs[1].uxPriority = 2;
    xTaskTCBs[1].xTaskRunState = taskTASK_NOT_RUNNING;
    vListInitialiseItem(&(xTaskTCBs[1].xStateListItem));
    listSET_LIST_ITEM_OWNER(&(xTaskTCBs[1].xStateListItem), &xTaskTCBs[1]);
    listINSERT_END( &pxReadyTasksLists[ xTaskTCBs[1].uxPriority ], &xTaskTCBs[1].xStateListItem );
    vListInitialise(&xList);
    uxCurrentNumberOfTasks = uxCurrentNumberOfTasks + 1;

    uxTopReadyPriority = 1;

    /* Default value for portGET_CORE_ID is 0. This can be changed with vSetCurrentCore. */
    xYieldPendings[ 0 ] = pdFALSE;
    pxCurrentTCBs[ 0 ] = &xTaskTCBs[0];

    for(uxCore = 0U; uxCore < configNUMBER_OF_CORES; uxCore++ )
    {
        if (pxCurrentTCBs[uxCore] == NULL)
        {
            pxCurrentTCBs[uxCore] = &xTaskTCBs[0];
        }
    }

    xSchedulerRunning = pdTRUE;
    uxSchedulerSuspended = pdFALSE;
    xPendedTicks = 0;      /* No pending tick in this test. */

    /* API call. */
    xReturn = xTaskPriorityInherit( &xTaskTCBs[1] );

    /* Validation. */
    /* The task priority is no higher than current running task. */
    TEST_ASSERT_EQUAL( pdTRUE, xReturn );
    /* The task in pending ready list should not in any event list now. */
    TEST_ASSERT_EQUAL( xTaskTCBs[1].xEventListItem.pvContainer, NULL );
    /* The task in pending ready list should be added back to ready list. */
    TEST_ASSERT_EQUAL( xTaskTCBs[1].xStateListItem.pvContainer, &pxReadyTasksLists[ xTaskTCBs[1].uxPriority ] );
}

/** 
 * @brief xTaskPriorityDisinherit - restore priority after inheriting the priority of the mutex holder
 *
 * <b>Coverage</b>
 * @code{c}
 *      if( pxTCB->uxMutexesHeld == ( UBaseType_t ) 0 )
 *      {
 *          ...
 *          prvAddTaskToReadyList( pxMutexHolderTCB );
 * @endcode
 *
 * Cover the case where a non-NULL task is specified, and this task has a
 * priority different than its base priority. Finally the uxPriority
 * is lesser than the uxTopReadyPriority.
 *
 */
void test_coverage_xTaskPriorityDisinherit_task_uxpriority_lesser(void)
{
    TCB_t xTaskTCBs[ 2 ] = { NULL };
    BaseType_t xReturn;
    UBaseType_t uxCore;

    /* Create a task as current running task on core 0. */
    xTaskTCBs[0].uxPriority = 1;
    xTaskTCBs[0].xTaskRunState = 0;
    vListInitialiseItem(&(xTaskTCBs[0].xStateListItem));
    listINSERT_END( &pxReadyTasksLists[ xTaskTCBs[0].uxPriority ], &xTaskTCBs[0].xStateListItem );
    listSET_LIST_ITEM_OWNER(&(xTaskTCBs[0].xStateListItem), &xTaskTCBs[0]);
    uxCurrentNumberOfTasks = uxCurrentNumberOfTasks + 1;

    /* Create a task in the suspended list. */
    xTaskTCBs[1].uxPriority = 2;
    xTaskTCBs[1].uxBasePriority = 1;
    xTaskTCBs[1].uxMutexesHeld++;
    xTaskTCBs[1].xTaskRunState = taskTASK_NOT_RUNNING;
    vListInitialiseItem(&(xTaskTCBs[1].xStateListItem));
    listSET_LIST_ITEM_OWNER(&(xTaskTCBs[1].xStateListItem), &xTaskTCBs[1]);
    listINSERT_END( &pxReadyTasksLists[ xTaskTCBs[1].uxPriority ], &xTaskTCBs[1].xStateListItem );
    uxCurrentNumberOfTasks = uxCurrentNumberOfTasks + 1;

    uxTopReadyPriority = 3;

    /* Default value for portGET_CORE_ID is 0. This can be changed with vSetCurrentCore. */
    xYieldPendings[ 0 ] = pdFALSE;
    pxCurrentTCBs[ 0 ] = &xTaskTCBs[0];

    for(uxCore = 0U; uxCore < configNUMBER_OF_CORES; uxCore++ )
    {
        if (pxCurrentTCBs[uxCore] == NULL)
        {
            pxCurrentTCBs[uxCore] = &xTaskTCBs[0];
        }
    }

    xSchedulerRunning = pdTRUE;
    uxSchedulerSuspended = pdFALSE;
    xPendedTicks = 0;      /* No pending tick in this test. */

    /* API call. */
    xReturn = xTaskPriorityDisinherit( &xTaskTCBs[1] );

    /* Validation. */
    /* The task priority is no higher than current running task. */
    TEST_ASSERT_EQUAL( pdTRUE, xReturn );
    /* The task in pending ready list should not in any event list now. */
    TEST_ASSERT_EQUAL( xTaskTCBs[1].xEventListItem.pvContainer, NULL );
    /* The task in pending ready list should be added back to ready list. */
    TEST_ASSERT_EQUAL( xTaskTCBs[1].xStateListItem.pvContainer, &pxReadyTasksLists[ xTaskTCBs[1].uxPriority ] );
}

/** 
 * @brief xTaskPriorityDisinherit - restore priority after inheriting the priority of the mutex holder
 *
 * <b>Coverage</b>
 * @code{c}
 *      if( pxTCB->uxMutexesHeld == ( UBaseType_t ) 0 )
 *      {
 *          ...
 *          prvAddTaskToReadyList( pxMutexHolderTCB );
 * @endcode
 *
 * Cover the case where a non-NULL task is specified, and this task has a
 * priority different than its base priority. Finally the uxPriority
 * is lesser than the uxTopReadyPriority.
 *
 */
void test_coverage_xTaskPriorityDisinherit_task_uxpriority_greater(void)
{
    TCB_t xTaskTCBs[ 2 ] = { NULL };
    BaseType_t xReturn;
    UBaseType_t uxCore;

    /* Create a task as current running task on core 0. */
    xTaskTCBs[0].uxPriority = 1;
    xTaskTCBs[0].xTaskRunState = 0;
    vListInitialiseItem(&(xTaskTCBs[0].xStateListItem));
    listINSERT_END( &pxReadyTasksLists[ xTaskTCBs[0].uxPriority ], &xTaskTCBs[0].xStateListItem );
    listSET_LIST_ITEM_OWNER(&(xTaskTCBs[0].xStateListItem), &xTaskTCBs[0]);
    uxCurrentNumberOfTasks = uxCurrentNumberOfTasks + 1;

    /* Create a task in the suspended list. */
    xTaskTCBs[1].uxPriority = 3;
    xTaskTCBs[1].uxBasePriority = 2;
    xTaskTCBs[1].uxMutexesHeld++;
    xTaskTCBs[1].xTaskRunState = taskTASK_NOT_RUNNING;
    vListInitialiseItem(&(xTaskTCBs[1].xStateListItem));
    listSET_LIST_ITEM_OWNER(&(xTaskTCBs[1].xStateListItem), &xTaskTCBs[1]);
    listINSERT_END( &pxReadyTasksLists[ xTaskTCBs[1].uxPriority ], &xTaskTCBs[1].xStateListItem );
    uxCurrentNumberOfTasks = uxCurrentNumberOfTasks + 1;

    uxTopReadyPriority = 1;

    /* Default value for portGET_CORE_ID is 0. This can be changed with vSetCurrentCore. */
    xYieldPendings[ 0 ] = pdFALSE;
    pxCurrentTCBs[ 0 ] = &xTaskTCBs[0];

    for(uxCore = 0U; uxCore < configNUMBER_OF_CORES; uxCore++ )
    {
        if (pxCurrentTCBs[uxCore] == NULL)
        {
            pxCurrentTCBs[uxCore] = &xTaskTCBs[0];
        }
    }

    xSchedulerRunning = pdTRUE;
    uxSchedulerSuspended = pdFALSE;
    xPendedTicks = 0;      /* No pending tick in this test. */

    /* API call. */
    xReturn = xTaskPriorityDisinherit( &xTaskTCBs[1] );

    /* Validation. */
    /* The task priority is no higher than current running task. */
    TEST_ASSERT_EQUAL( pdTRUE, xReturn );
    /* The task in pending ready list should not in any event list now. */
    TEST_ASSERT_EQUAL( xTaskTCBs[1].xEventListItem.pvContainer, NULL );
    /* The task in pending ready list should be added back to ready list. */
    TEST_ASSERT_EQUAL( xTaskTCBs[1].xStateListItem.pvContainer, &pxReadyTasksLists[ xTaskTCBs[1].uxPriority ] );
}

/** 
 * @brief xTaskPriorityDisinheritAfterTimeout - restore priority after inheriting the priority of the mutex holder
 *
 * <b>Coverage</b>
 * @code{c}
 *      if( pxTCB->uxMutexesHeld == ( UBaseType_t ) 0 )
 *      {
 *          ...
 *          prvAddTaskToReadyList( pxMutexHolderTCB );
 * @endcode
 *
 * Cover the case where a non-NULL task is specified, and this task has a
 * priority different than its base priority. Finally the uxPriority
 * is lesser than the uxTopReadyPriority.
 *
 */
void test_coverage_xTaskPriorityDisinheritAfterTimeout_task_uxpriority_lesser(void)
{
    TCB_t xTaskTCBs[ 2 ] = { NULL };
    UBaseType_t uxCore;

    /* Create a task as current running task on core 0. */
    xTaskTCBs[0].uxPriority = 1;
    xTaskTCBs[0].xTaskRunState = 0;
    vListInitialiseItem(&(xTaskTCBs[0].xStateListItem));
    listINSERT_END( &pxReadyTasksLists[ xTaskTCBs[0].uxPriority ], &xTaskTCBs[0].xStateListItem );
    listSET_LIST_ITEM_OWNER(&(xTaskTCBs[0].xStateListItem), &xTaskTCBs[0]);
    uxCurrentNumberOfTasks = uxCurrentNumberOfTasks + 1;

    /* Create a task in the suspended list. */
    xTaskTCBs[1].uxPriority = 2;
    xTaskTCBs[1].uxBasePriority = 1;
    xTaskTCBs[1].uxMutexesHeld++;
    xTaskTCBs[1].xTaskRunState = taskTASK_NOT_RUNNING;
    vListInitialiseItem(&(xTaskTCBs[1].xStateListItem));
    listSET_LIST_ITEM_OWNER(&(xTaskTCBs[1].xStateListItem), &xTaskTCBs[1]);
    listINSERT_END( &pxReadyTasksLists[ xTaskTCBs[1].uxPriority ], &xTaskTCBs[1].xStateListItem );
    uxCurrentNumberOfTasks = uxCurrentNumberOfTasks + 1;

    uxTopReadyPriority = 3;

    /* Default value for portGET_CORE_ID is 0. This can be changed with vSetCurrentCore. */
    xYieldPendings[ 0 ] = pdFALSE;
    pxCurrentTCBs[ 0 ] = &xTaskTCBs[0];

    for(uxCore = 0U; uxCore < configNUMBER_OF_CORES; uxCore++ )
    {
        if (pxCurrentTCBs[uxCore] == NULL)
        {
            pxCurrentTCBs[uxCore] = &xTaskTCBs[0];
        }
    }

    xSchedulerRunning = pdTRUE;
    uxSchedulerSuspended = pdFALSE;
    xPendedTicks = 0;      /* No pending tick in this test. */

    /* API call. */
    vTaskPriorityDisinheritAfterTimeout( &xTaskTCBs[1], 1 );

    /* Validation. */
    /* The task in pending ready list should not in any event list now. */
    TEST_ASSERT_EQUAL( xTaskTCBs[1].xEventListItem.pvContainer, NULL );
    /* The task in pending ready list should be added back to ready list. */
    TEST_ASSERT_EQUAL( xTaskTCBs[1].xStateListItem.pvContainer, &pxReadyTasksLists[ xTaskTCBs[1].uxPriority ] );
}

/** 
 * @brief xTaskPriorityDisinheritAfterTimeout - restore priority after inheriting the priority of the mutex holder
 *
 * <b>Coverage</b>
 * @code{c}
 *      if( pxTCB->uxMutexesHeld == ( UBaseType_t ) 0 )
 *      {
 *          ...
 *          prvAddTaskToReadyList( pxMutexHolderTCB );
 * @endcode
 *
 * Cover the case where a non-NULL task is specified, and this task has a
 * priority different than its base priority. Finally the uxPriority
 * is lesser than the uxTopReadyPriority.
 *
 */
void test_coverage_xTaskPriorityDisinheritAfterTimeout_task_uxpriority_greater(void)
{
    TCB_t xTaskTCBs[ 2 ] = { NULL };
    UBaseType_t uxCore;

    /* Create a task as current running task on core 0. */
    xTaskTCBs[0].uxPriority = 1;
    xTaskTCBs[0].xTaskRunState = 0;
    vListInitialiseItem(&(xTaskTCBs[0].xStateListItem));
    listINSERT_END( &pxReadyTasksLists[ xTaskTCBs[0].uxPriority ], &xTaskTCBs[0].xStateListItem );
    listSET_LIST_ITEM_OWNER(&(xTaskTCBs[0].xStateListItem), &xTaskTCBs[0]);
    uxCurrentNumberOfTasks = uxCurrentNumberOfTasks + 1;

    /* Create a task in the suspended list. */
    xTaskTCBs[1].uxPriority = 3;
    xTaskTCBs[1].uxBasePriority = 2;
    xTaskTCBs[1].uxMutexesHeld++;
    xTaskTCBs[1].xTaskRunState = taskTASK_NOT_RUNNING;
    vListInitialiseItem(&(xTaskTCBs[1].xStateListItem));
    listSET_LIST_ITEM_OWNER(&(xTaskTCBs[1].xStateListItem), &xTaskTCBs[1]);
    listINSERT_END( &pxReadyTasksLists[ xTaskTCBs[1].uxPriority ], &xTaskTCBs[1].xStateListItem );
    uxCurrentNumberOfTasks = uxCurrentNumberOfTasks + 1;

    uxTopReadyPriority = 1;

    /* Default value for portGET_CORE_ID is 0. This can be changed with vSetCurrentCore. */
    xYieldPendings[ 0 ] = pdFALSE;
    pxCurrentTCBs[ 0 ] = &xTaskTCBs[0];

    for(uxCore = 0U; uxCore < configNUMBER_OF_CORES; uxCore++ )
    {
        if (pxCurrentTCBs[uxCore] == NULL)
        {
            pxCurrentTCBs[uxCore] = &xTaskTCBs[0];
        }
    }

    xSchedulerRunning = pdTRUE;
    uxSchedulerSuspended = pdFALSE;
    xPendedTicks = 0;      /* No pending tick in this test. */

    /* API call. */
    vTaskPriorityDisinheritAfterTimeout( &xTaskTCBs[1], 2 );

    /* Validation. */
    /* The task in pending ready list should not in any event list now. */
    TEST_ASSERT_EQUAL( xTaskTCBs[1].xEventListItem.pvContainer, NULL );
    /* The task in pending ready list should be added back to ready list. */
    TEST_ASSERT_EQUAL( xTaskTCBs[1].xStateListItem.pvContainer, &pxReadyTasksLists[ xTaskTCBs[1].uxPriority ] );
}
