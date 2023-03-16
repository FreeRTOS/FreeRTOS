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

#define MAX_TASKS                                    3

/* ===========================  EXTERN VARIABLES  =========================== */
extern volatile UBaseType_t uxDeletedTasksWaitingCleanUp;
extern volatile UBaseType_t uxSchedulerSuspended;
extern volatile TCB_t *  pxCurrentTCBs[ configNUMBER_OF_CORES ];
extern List_t xSuspendedTaskList;
extern List_t xPendingReadyList;
extern volatile UBaseType_t uxTopReadyPriority;
extern volatile BaseType_t xYieldPendings[ configNUMBER_OF_CORES ];
extern TickType_t xPendedTicks;

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
extern volatile TickType_t xNextTaskUnblockTime;
extern volatile TickType_t xTickCount;
extern volatile UBaseType_t uxSchedulerSuspended;

/* ==============================  Helper functions for Test Cases  ============================== */
void created_task(void* arg)
{
    while(1){
        vTaskDelay(100);
    }
}

void vSetTaskToRunning( int num_calls )
{
    /*
        configASSERT( pxThisTCB->xTaskRunState != taskTASK_YIELDING );
        Requires 2 check conditions when it is and isn't in the yielding state
        Hence, just allow the program to loop through twice for complete coverage
    */
    if (num_calls > 2){
        xTaskHandles[0] -> xTaskRunState =  eRunning;
    }
}

BaseType_t returnFakeTrue(int num_calls){
    
    return 1;
}

BaseType_t UpdateuxSchedulerSuspended2(int num_calls){
    if (num_calls > 1){
        uxSchedulerSuspended = ( UBaseType_t ) 2;
        pxCurrentTCBs[ configNUMBER_OF_CORES ] = 0;    
    }
    else if (num_calls == 0){
        uxSchedulerSuspended = 0U;
    }
    return ( UBaseType_t ) 0;
}

/* ==============================  Test Cases  ============================== */

//Asserts Line 705's configAssert to false by make it 2
void test_task_yelding_state_configAsset_Sucess( void )
{
    vFakePortEnableInterrupts_Stub(&vSetTaskToRunning);

    xTaskHandles[0] = NULL;

    xTaskCreate(vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 1, &xTaskHandles[0]);

    vTaskStartScheduler();

    xTaskHandles[0]->xTaskRunState = taskTASK_YIELDING;
    vTaskSuspendAll();

}

//Asserts Line 705's configAssert to false by make it 2
void test_task_yelding_state_configAssetFail( void )
{
    vFakePortCheckIfInISR_Stub(&UpdateuxSchedulerSuspended2);
    vFakePortEnableInterrupts_Stub(&vSetTaskToRunning);
    //vFakePortReleaseTaskLock_Stub(&vSetTaskToRunning2);

    xTaskHandles[0] = NULL;

    xTaskCreate(vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 1, &xTaskHandles[0]);

    vTaskStartScheduler();

    xTaskHandles[0]->xTaskRunState = taskTASK_YIELDING;
    vTaskSuspendAll();

}

/*
    static void prvCheckForRunStateChange( void );
        covers [portCHECK_IF_IN_ISR()] is false for Line 682 [task.c]
*/
void test_prv_Check_For_Run_State_Change_case_task_yelding_state( void )
{
    //Reset all the globals to gain the deafult null state
    memset(xTaskHandles, 0, sizeof(TaskHandle_t) * configNUMBER_OF_CORES );

    vFakePortEnableInterrupts_Stub(&vSetTaskToRunning); 
    xTaskHandles[0] =  NULL ;
    
    xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 1, &xTaskHandles[0] );

    vTaskStartScheduler();

    xTaskHandles[0] -> xTaskRunState =  taskTASK_YIELDING;

    vTaskEnterCritical();
}

/*
Coverage for 
        static void prvCheckForRunStateChange( void );
        covers the deafult state when the function is just called
*/
void test_prv_Check_For_Run_State_Change_case_1( void )
{
    //Reset all the globals to gain the deafult null state
    memset(xTaskHandles, 0, sizeof(TaskHandle_t) * configNUMBER_OF_CORES );

    //Allow helper function 
    vFakePortCheckIfInISR_Stub(&returnFakeTrue); 

    uint32_t i;

    /* Create tasks of equal priority for all available CPU cores */
    for (i = 0; i < configNUMBER_OF_CORES; i++) {
        xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 2, &xTaskHandles[i] );
    }
    
    vTaskStartScheduler();

    /* Verify all tasks are in the running state */
    for (i = 0; i < configNUMBER_OF_CORES; i++) {
        verifySmpTask( &xTaskHandles[i], eRunning, i );
    }

    /* Lower the priority of task T0 */
    vTaskPrioritySet( xTaskHandles[0], 1 );
    
}

/*
The kernel will be configured as follows:
    #define configNUMBER_OF_CORES                               (N > 1)
    #define configUSE_CORE_AFFINITY                          1
Coverage for 
    static TickType_t prvGetExpectedIdleTime( void )      
*/
/*
Coverage for: UBaseType_t uxTaskGetSystemState( TaskStatus_t * const pxTaskStatusArray,
                                                const UBaseType_t uxArraySize,
                                                configRUN_TIME_COUNTER_TYPE * const pulTotalRunTime )
*/
void test_task_get_system_state( void )
{
    TaskStatus_t *tsk_status_array;
    TaskHandle_t created_handles[3];
    tsk_status_array = calloc(MAX_TASKS, sizeof(TaskStatus_t));

    for(int i = 0; i < 3; i++){
        xTaskCreate( created_task, "Created Task", configMINIMAL_STACK_SIZE, NULL, 1, &created_handles[i] );
    }

    //Get System states
    int no_of_tasks = uxTaskGetSystemState(tsk_status_array, MAX_TASKS, NULL);
    TEST_ASSERT((no_of_tasks > 0) && (no_of_tasks <= MAX_TASKS));
}

/*
Coverage for: UBaseType_t uxTaskGetSystemState( TaskStatus_t * const pxTaskStatusArray,
                                                const UBaseType_t uxArraySize,
                                                configRUN_TIME_COUNTER_TYPE * const pulTotalRunTime )
*/
void test_task_get_system_state_custom_time( void )
{
    TaskStatus_t *tsk_status_array;
    TaskHandle_t created_handles[3];
    uint32_t ulTotalRunTime = (uint32_t) 200;// Custom time value
    tsk_status_array = calloc(MAX_TASKS, sizeof(TaskStatus_t));

    for(int i = 0; i < 3; i++){
        xTaskCreate( created_task, "Created Task", configMINIMAL_STACK_SIZE, NULL, 1, &created_handles[i] );
    }

    //Get System states
    int no_of_tasks = uxTaskGetSystemState(tsk_status_array, MAX_TASKS, &ulTotalRunTime);
    TEST_ASSERT((no_of_tasks > 0) && (no_of_tasks <= MAX_TASKS));
}

/*
Coverage for: UBaseType_t uxTaskGetSystemState( TaskStatus_t * const pxTaskStatusArray,
                                                const UBaseType_t uxArraySize,
                                                configRUN_TIME_COUNTER_TYPE * const pulTotalRunTime )
*/
void test_task_get_system_state_unavilable_task_space( void )
{
    TaskStatus_t *tsk_status_array;
    TaskHandle_t created_handles[3];
    tsk_status_array = calloc(MAX_TASKS, sizeof(TaskStatus_t));

    for(int i = 0; i < 3; i++){
        xTaskCreate( created_task, "Created Task", configMINIMAL_STACK_SIZE, NULL, 1, &created_handles[i] );
    }

    //Get System states
    int no_of_tasks = uxTaskGetSystemState(tsk_status_array, MAX_TASKS-1, NULL);
    TEST_ASSERT((no_of_tasks == 0) && (no_of_tasks <= MAX_TASKS));
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

    /* Expectations. */
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
