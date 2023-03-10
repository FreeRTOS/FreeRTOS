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

#define tskSTACK_FILL_BYTE (0xa5U)

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
extern List_t xSuspendedTaskList;
extern List_t xPendingReadyList;

/* ===========================  EXTERN FUNCTIONS  =========================== */
extern void prvAddNewTaskToReadyList( TCB_t * pxNewTCB );
extern void prvYieldForTask( TCB_t * pxTCB );
extern void vTaskEnterCritical( void );
extern UBaseType_t vTaskEnterCriticalFromISR( void );
extern void vTaskExitCritical( void );
extern void vTaskExitCriticalFromISR( UBaseType_t uxSavedInterruptStatus );

/* ==============================  Global VARIABLES ============================== */
TaskHandle_t xTaskHandles[configNUMBER_OF_CORES] = { NULL };

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

/* ===========================  EXTERN FUNCTIONS  =========================== */
extern void vTaskEnterCritical(void);

/* ==============================  Helper functions for Test Cases  ============================== */

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
    TEST_ASSERT_EQUAL( uxTaskNumber, 0x5a5a );
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
    TEST_ASSERT_EQUAL( uxTaskNumber, 0U );
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
    TEST_ASSERT_EQUAL( xTaskTCB.uxTaskNumber, 0x5a5a );
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

/*
The kernel will be configured as follows:
    #define configNUMBER_OF_CORES                               (N > 1)
    #define configUSE_TRACE_FACILITY                         1
    #define configUSE_STATS_FORMATTING_FUNCTIONS             1

Coverage for: 
        void vTaskList( char * pcWriteBuffer )
        if( pxTaskStatusArray != NULL ) = False
*/
void test_v_task_list_case_no_task_created( void )
{
    static char	buff[ 800 ] = { 0 };
 
    //Call the List
    vTaskList(buff);

}
/*
The kernel will be configured as follows:
    #define configNUMBER_OF_CORES                               (N > 1)
    #define configUSE_TRACE_FACILITY                         1
    #define configUSE_STATS_FORMATTING_FUNCTIONS             1

Coverage for: 
        void vTaskList( char * pcWriteBuffer )
        case eDeleted
*/
void test_v_task_list_case_eDeleted( void )
{
    static char	buff[ 800 ] = { 0 };

    TaskHandle_t xTaskHandles[configNUMBER_OF_CORES+1] = { NULL };

    uint32_t i;

    /* Create tasks of equal priority for all available CPU cores */
    for (i = 0; i < configNUMBER_OF_CORES; i++) {
        xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 3, &xTaskHandles[i] );
    }

    xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 2, &xTaskHandles[i] );

    vTaskStartScheduler();
 
    vTaskDelete(xTaskHandles[0]);

    //Call the List
    vTaskList(buff);

    /* Delete all priority task responsibly*/
    for (i = 1; i < configNUMBER_OF_CORES; i++) {
        vTaskDelete(xTaskHandles[i]);
    }

}

/*
The kernel will be configured as follows:
    #define configNUMBER_OF_CORES                               (N > 1)
    #define configUSE_TRACE_FACILITY                         1
    #define configUSE_STATS_FORMATTING_FUNCTIONS             1

Coverage for: 
        void vTaskList( char * pcWriteBuffer )
        case eSuspended
*/
void test_v_task_list_case_eSuspended( void )
{
    static char	buff[ 800 ] = { 0 };

    TaskHandle_t xTaskHandles[configNUMBER_OF_CORES+1] = { NULL };

    uint32_t i;

    /* Create tasks of equal priority for all available CPU cores */
    for (i = 0; i < configNUMBER_OF_CORES; i++) {
        xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 3, &xTaskHandles[i] );
    }

    xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 2, &xTaskHandles[i] );

    vTaskStartScheduler();
 
    vTaskSuspend(xTaskHandles[1]);

    //Call the List
    vTaskList(buff);


    /* Delete all priority task responsibly*/
    for (i = 0; i < configNUMBER_OF_CORES; i++) {
        vTaskDelete(xTaskHandles[i]);
    }

}


/*
The kernel will be configured as follows:
    #define configNUMBER_OF_CORES                               (N > 1)
    #define configUSE_TRACE_FACILITY                         1
    #define configUSE_STATS_FORMATTING_FUNCTIONS             1

Coverage for: 
        void vTaskList( char * pcWriteBuffer )
        case eBlocked
*/
void test_v_task_list_case_eblocked( void )
{
    static char	buff[ 800 ] = { 0 };

    TaskHandle_t xTaskHandles[configNUMBER_OF_CORES] = { NULL };

    uint32_t i;

    /* Create tasks of equal priority for all available CPU cores */
    for (i = 0; i < configNUMBER_OF_CORES; i++) {
        xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 2, &xTaskHandles[i] );
    }

    vTaskStartScheduler();

    /* Delay the task running on core ID 0 for 1 ticks. The task will be put into pxDelayedTaskList and added back to ready list after 1 tick. */
    vTaskDelay( 1 );

    //Call the List
    vTaskList(buff);

     /* Delete all priority task responsibly*/
    for (i = 0; i < configNUMBER_OF_CORES; i++) {
        vTaskDelete(xTaskHandles[i]);
    }
}

/*
The kernel will be configured as follows:
    #define configNUMBER_OF_CORES                               (N > 1)
    #define configUSE_TRACE_FACILITY                         1
    #define configUSE_STATS_FORMATTING_FUNCTIONS             1

Coverage for: 
        void vTaskList( char * pcWriteBuffer )
        and
        static char * prvWriteNameToBuffer( char * pcBuffer,
                                            const char * pcTaskName )
*/
void test_v_task_list( void )
{
    static char	buff[ 800 ] = { 0 };

    TaskHandle_t xTaskHandles[configNUMBER_OF_CORES] = { NULL };
    uint32_t i;

    /* Create tasks of equal priority for all available CPU cores */
    for (i = 0; i < configNUMBER_OF_CORES; i++) {
        xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 2, &xTaskHandles[i] );
    }

    vTaskStartScheduler();

    vTaskList(buff);

    /* Delete all priority task responsibly*/
    for (i = 0; i < configNUMBER_OF_CORES; i++) {
        vTaskDelete(xTaskHandles[i]);
    }
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
    vListInitialise( &( pxReadyTasksLists[ tskIDLE_PRIORITY ] ) );
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
    TEST_ASSERT_EQUAL( xTaskTCB.uxCriticalNesting, 2 );
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
    TEST_ASSERT_EQUAL( xTaskTCB.uxCriticalNesting, 2 );
    TEST_ASSERT_EQUAL( uxSavedInterruptStatus, 0x5a5a );
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
    TEST_ASSERT_EQUAL( xTaskTCB.uxCriticalNesting, 1 );
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
    TEST_ASSERT_EQUAL( xTaskTCB.uxCriticalNesting, 1 );
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
    vListInitialise( &xSuspendedTaskList );
    vListInitialise( &xPendingReadyList );

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
