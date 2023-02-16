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

#define taskTASK_YIELDING       ( TaskRunning_t ) ( -2 )
#define MAX_TASKS                                    3

/* ===========================  EXTERN VARIABLES  =========================== */
extern volatile UBaseType_t uxDeletedTasksWaitingCleanUp;
extern volatile UBaseType_t uxSchedulerSuspended;
extern volatile TCB_t *  pxCurrentTCBs[ configNUMBER_OF_CORES ];
extern List_t xSuspendedTaskList;
extern List_t xPendingReadyList;
extern volatile UBaseType_t uxTopReadyPriority;
extern volatile BaseType_t xYieldPendings[ configNUMBER_OF_CORES ];

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

/*
The kernel will be configured as follows:
    #define configNUMBER_OF_CORES                               (N > 1)
    #define configUSE_CORE_AFFINITY                          1
    #define configUSE_TICKLESS_IDLE                          1 

Coverage for: 
            void vTaskStepTick( TickType_t xTicksToJump )
            Where
            configASSERT( ( xTickCount + xTicksToJump ) <= xNextTaskUnblockTime ) = False
            and  
                if( ( xTickCount + xTicksToJump ) == xNextTaskUnblockTime ) = False
*/
void test_task_step_tick_xNextTaskUnblockTime_greater( void )
{
    TaskHandle_t xTaskHandles[1] = { NULL };

    /* Create  tasks  */
    xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 2, &xTaskHandles[0] );

    vTaskStartScheduler();
    xNextTaskUnblockTime = 10U;
    xTickCount = 1U;
    vTaskStepTick((TickType_t)10U);
}

/*
The kernel will be configured as follows:
    #define configNUMBER_OF_CORES                               (N > 1)
    #define configUSE_CORE_AFFINITY                          1
    #define configUSE_TICKLESS_IDLE                          1 

Coverage for:
            void vTaskStepTick( TickType_t xTicksToJump )
            Where
                if( ( xTickCount + xTicksToJump ) == xNextTaskUnblockTime )
                                                                            is True
            with 
                configASSERT( xTicksToJump != ( TickType_t ) 0 ) = False;
*/
void test_task_step_tick_xNextTaskUnblockTime_equal_non_zero_xTicksToJump ( void )
{
    TaskHandle_t xTaskHandles[1] = { NULL };

    /* Create  tasks  */
    xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 2, &xTaskHandles[0] );

    xNextTaskUnblockTime = 10U;
    xTickCount = 10U;
    uxSchedulerSuspended = 1U;
    vTaskStepTick((TickType_t)0);
}

/*
The kernel will be configured as follows:
    #define configNUMBER_OF_CORES                               (N > 1)
    #define configUSE_CORE_AFFINITY                          1
    #define configUSE_TICKLESS_IDLE                          1 

Coverage for: 
            void vTaskStepTick( TickType_t xTicksToJump )
            Where 
                if( ( xTickCount + xTicksToJump ) == xNextTaskUnblockTime )
                                                                            is True
            with suspended Scheduler
*/
void test_task_step_tick_xNextTaskUnblockTime_equal_suspended_scheduler ( void )
{
    TaskHandle_t xTaskHandles[1] = { NULL };

    /* Create  tasks  */
    xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 2, &xTaskHandles[0] );

    xNextTaskUnblockTime = 10U;
    xTickCount = 0U;
    uxSchedulerSuspended = 1U;
    vTaskStepTick((TickType_t)10U);
}


/*
The kernel will be configured as follows:
    #define configNUMBER_OF_CORES                               (N > 1)
    #define configUSE_CORE_AFFINITY                          1
    #define configUSE_TICKLESS_IDLE                          1 

Coverage for: 
            void vTaskStepTick( TickType_t xTicksToJump )
            Where 
                if( ( xTickCount + xTicksToJump ) == xNextTaskUnblockTime )
                                                                            is True
*/
void test_task_step_tick_xNextTaskUnblockTime_equal( void )
{
    TaskHandle_t xTaskHandles[1] = { NULL };

    /* Create  tasks  */
    xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 2, &xTaskHandles[0] );

    vTaskStartScheduler();

    xNextTaskUnblockTime = 10U;
    xTickCount = 0U;
    vTaskStepTick((TickType_t)10U);
}

/*
The kernel will be configured as follows:
    #define configNUMBER_OF_CORES                               (N > 1)
    #define configUSE_CORE_AFFINITY                          1
    #define configUSE_TICKLESS_IDLE                          1 
    
Coverage for: 
            void vTaskStepTick( TickType_t xTicksToJump )
            Where 
                if( ( xTickCount + xTicksToJump ) == xNextTaskUnblockTime )
                                                                            is False
*/
void test_task_step_tick_xNextTaskUnblockTime_not_equal( void )
{
    TaskHandle_t xTaskHandles[1] = { NULL };

    /* Create  tasks  */
    xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 2, &xTaskHandles[0] );

    vTaskStartScheduler();
    xTickCount = 0U;
    vTaskStepTick((TickType_t)10U);
}
