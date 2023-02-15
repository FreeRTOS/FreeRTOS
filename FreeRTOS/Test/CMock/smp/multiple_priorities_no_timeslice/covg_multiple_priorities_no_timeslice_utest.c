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


/* ===========================  EXTERN VARIABLES  =========================== */
extern volatile UBaseType_t uxCurrentNumberOfTasks;
extern volatile UBaseType_t uxDeletedTasksWaitingCleanUp;
extern volatile UBaseType_t uxSchedulerSuspended;
extern volatile TCB_t *  pxCurrentTCBs[ configNUMBER_OF_CORES ];
extern volatile BaseType_t xSchedulerRunning;
extern volatile TickType_t xTickCount;

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


/* ==============================  Test Cases  ============================== */

/*
The kernel will be configured as follows:
    #define configNUMBER_OF_CORES                               (N > 1)
    #define configUSE_CORE_AFFINITY                         1
    #define configUSE_TASK_PREEMPTION_DISABLE               1

Coverage for 
        static void vTaskPreemptionEnable( void );
        covers the deafult state when the function is just called
*/
void test_task_preemption_enable( void )
{
    TaskHandle_t xTaskHandles[configNUMBER_OF_CORES] = { NULL };
    uint32_t i;

    /* Create tasks of equal priority */
    for (i = 0; i < configNUMBER_OF_CORES; i++) {
        xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 1, &xTaskHandles[i] );
    }

    vTaskStartScheduler();

    /* Verify tasks are running */
    for (i = 0; i < configNUMBER_OF_CORES; i++) {
        verifySmpTask( &xTaskHandles[i], eRunning, i );
    }

    /* task T0 */
    vTaskPreemptionEnable( xTaskHandles[0] );

}

/*
The kernel will be configured as follows:
    #define configNUMBER_OF_CORES                               (N > 1)
    #define configUSE_CORE_AFFINITY                         1
    #define configUSE_TASK_PREEMPTION_DISABLE               1

Coverage for 
        static void vTaskPreemptionEnable( void );
        covers the deafult state when xSchedulerRunning is set to False
*/
void test_task_preemption_enable_branch_xSchedulerRunning_False( void )
{
    TaskHandle_t xTaskHandles[configNUMBER_OF_CORES] = { NULL };
    uint32_t i;

    /* Create tasks of equal priority */
    for (i = 0; i < configNUMBER_OF_CORES; i++) {
        xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 1, &xTaskHandles[i] );
    }

    //Tasks are created and a task is passed but scheduler is never ran
    vTaskPreemptionEnable( xTaskHandles[0] );

} 

/*
The kernel will be configured as follows:
    #define configNUMBER_OF_CORES                               (N > 1)
    #define configUSE_CORE_AFFINITY                         1
    #define configUSE_TASK_PREEMPTION_DISABLE               1

Coverage for 
        static void vTaskPreemptionEnable( void );
        covers the deafult state when NULL task is passed
*/
void test_task_preemption_enable_branch_NULL_task( void )
{
    TaskHandle_t xTaskHandles[configNUMBER_OF_CORES] = { NULL };
    uint32_t i;

    /* Create tasks of equal priority */
    for (i = 0; i < configNUMBER_OF_CORES; i++) {
        xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 1, &xTaskHandles[i] );
    }

    vTaskStartScheduler();

    /* task T0 */
    vTaskPreemptionEnable( NULL );

} 


/*
The kernel will be configured as follows:
    #define configNUMBER_OF_CORES                               (N > 1)
    #define configUSE_CORE_AFFINITY                         1
    #define configUSE_TASK_PREEMPTION_DISABLE               1

Coverage for 
        static void vTaskPreemptionEnable( void );
        covers the deafult state when passed task's xTaskRunState task is greater than number of cores
*/
void test_task_preemption_enable_branch_Rand_task( void )
{
    TaskHandle_t xTaskHandles[configNUMBER_OF_CORES] = { NULL };
    uint32_t i;

    /* Create tasks of equal priority */
    for (i = 0; i < configNUMBER_OF_CORES; i++) {
        xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 1, &xTaskHandles[i] );
    }

    vTaskStartScheduler();

    /* task T0 */
    xTaskHandles[0]->xTaskRunState = configNUMBER_OF_CORES+1;
    vTaskPreemptionEnable( xTaskHandles[0] );

} 

/*
The kernel will be configured as follows:
    #define configNUMBER_OF_CORES                               (N > 1)
    #define configUSE_CORE_AFFINITY                         1
    #define configUSE_TASK_PREEMPTION_DISABLE               1

Coverage for 
        static void vTaskPreemptionEnable( void );
        covers the deafult state when passed task's xTaskRunState task is negative
*/
void test_task_preemption_enable_branch_negative_task( void )
{
    TaskHandle_t xTaskHandles[configNUMBER_OF_CORES] = { NULL };
    uint32_t i;

    /* Create tasks of equal priority */
    for (i = 0; i < configNUMBER_OF_CORES; i++) {
        xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 1, &xTaskHandles[i] );
    }

    vTaskStartScheduler();

    /* task T0 */
    xTaskHandles[0]->xTaskRunState = -1;
    vTaskPreemptionEnable( xTaskHandles[0] );

} 

/*
The kernel will be configured as follows:
    #define configNUMBER_OF_CORES                               (N > 1)
    #define configUSE_CORE_AFFINITY                         1

Coverage for 
    UBaseType_t vTaskCoreAffinityGet( const TaskHandle_t xTask )
        with a created task handel for xTask
*/
void test_task_Core_Affinity_Get( void )
{
    //Reset all the globals to gain the deafult null state
    memset(xTaskHandles, 0, sizeof(TaskHandle_t) * configNUMBER_OF_CORES );

    uint32_t i;

    /* Create tasks of equal priority */
    for (i = 0; i < configNUMBER_OF_CORES; i++) {
        xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 1, &xTaskHandles[i] );
    }

    vTaskStartScheduler();

    /* Verify tasks are running */
    for (i = 0; i < configNUMBER_OF_CORES; i++) {
        verifySmpTask( &xTaskHandles[i], eRunning, i );
    }

    /* task T0 */
    vTaskCoreAffinityGet( xTaskHandles[0] );

}
/*
The kernel will be configured as follows:
    #define configNUMBER_OF_CORES                               (N > 1)
    #define configUSE_CORE_AFFINITY                         1

Coverage for 
    UBaseType_t vTaskCoreAffinityGet( const TaskHandle_t xTask )
        with a NULL for xTask
*/
void test_task_Core_Affinity_Get_with_null_task( void )
{
    //Reset all the globals to gain the deafult null state
    memset(xTaskHandles, 0, sizeof(TaskHandle_t) * configNUMBER_OF_CORES );

    uint32_t i;

    /* Create tasks of equal priority */
    for (i = 0; i < configNUMBER_OF_CORES; i++) {
        xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 1, &xTaskHandles[i] );
    }

    vTaskStartScheduler();

    /* Verify tasks are running */
    for (i = 0; i < configNUMBER_OF_CORES; i++) {
        verifySmpTask( &xTaskHandles[i], eRunning, i );
    }
    vTaskCoreAffinityGet( NULL );
}

/*
The kernel will be configured as follows:
    #define configNUMBER_OF_CORES                               (N > 1)
    #define configUSE_TRACE_FACILITY                         1

Coverage for 
    UBaseType_t uxTaskGetTaskNumber( TaskHandle_t xTask )
    and
    void vTaskSetTaskNumber( TaskHandle_t xTask,
                             const UBaseType_t uxHandle )
    
    Sets a non-null task's number as taskNumber and then fetches it
*/
void test_task_set_get_task_number_not_null_task( void )
{
    TaskHandle_t xTaskHandles[3] = { NULL };
    uint32_t i;
    UBaseType_t taskNumber = 1;
    UBaseType_t returntaskNumber;


    /* Create  tasks of equal priority */
    for (i = 0; i < (2); i++) {
        xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 2, &xTaskHandles[i] );
    }

    /* Create a single equal priority task */   
    xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 2, &xTaskHandles[i] );

    vTaskStartScheduler();

    vTaskSetTaskNumber(xTaskHandles[0], taskNumber);
    
    /* Set CPU core affinity on the last task for the last CPU core */
    returntaskNumber = uxTaskGetTaskNumber(xTaskHandles[0]);
    
    TEST_ASSERT_EQUAL( returntaskNumber,  taskNumber);
    
}
/*
The kernel will be configured as follows:
    #define configNUMBER_OF_CORES                               (N > 1)
    #define configUSE_TRACE_FACILITY                         1

Coverage for 
    UBaseType_t uxTaskGetTaskNumber( TaskHandle_t xTask )
    and
    void vTaskSetTaskNumber( TaskHandle_t xTask,
                             const UBaseType_t uxHandle )
    
    
    Sets a null task's number as taskNumber and then fetches it 
*/
void test_task_set_get_task_number_null_task( void )
{
    TaskHandle_t xTaskHandles[3] = { NULL };
    UBaseType_t taskNumber = 1;
    UBaseType_t returntaskNumber;

    vTaskStartScheduler();
    
    vTaskSetTaskNumber(xTaskHandles[0], taskNumber);
    
    /* Set CPU core affinity on the last task for the last CPU core */
    returntaskNumber = uxTaskGetTaskNumber(xTaskHandles[0]);
    
    TEST_ASSERT_EQUAL( 0U , returntaskNumber);
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

/*
The kernel will be configured as follows:
    #define configNUMBER_OF_CORES                               (N > 1)
    #define INCLUDE_uxTaskGetStackHighWaterMark              1
    #define configUSE_MUTEXES                                1
Coverage for: 
        TaskHandle_t xTaskGetCurrentTaskHandleCPU( BaseType_t xCoreID )
*/
void test_task_get_current_task_handle_cpu ( void )
{
    TaskHandle_t xTaskHandles[1] = { NULL };

    /* Create  tasks  */
    xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 2, &xTaskHandles[0] );

    vTaskStartScheduler();

    xTaskGetCurrentTaskHandleCPU( vFakePortGetCoreID() );

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

/*
Coverage for
    static void prvAddNewTaskToReadyList( TCB_t * pxNewTCB )
    covers the case where the task being created is not the first or only task.
*/
void test_coverage_prvAddNewTaskToReadyList_create_two_tasks_with_the_first_suspended( void )
{
    TaskHandle_t xTaskHandles[configNUMBER_OF_CORES] = { NULL };

    xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 1, &xTaskHandles[0] );
    vTaskSuspend(xTaskHandles[0]);

    xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 1, &xTaskHandles[1] );

    vTaskStartScheduler();
}

/*
Coverage for
    static void prvAddNewTaskToReadyList( TCB_t * pxNewTCB )
    covers the case where there coreID is out of bounds when looking for a TCB

Notes:
    The prvAddNewTaskToReadyList function contained a subsection that is called
    when the scheudler is not active. Furthermore it contains a loop which
    is called only when the IDLE attribute of a task is set. As new tasks do not begin
    with the IDLE attribute set, combined with the use of break on finding a free slot
    and the entrance paths not calling the function in a way wich will reach the
    for loops boundary condition. It is not currently reachable. One potential
    fix would be to create new tasks with the IDLE attribute set when the scheduler
    if not active. The other simple approach would be to avoid the break in the for
    loop, but that would waste soe cycles. This note remains until a solution
    is found.
*/

void show_task_status( void )
{
    UBaseType_t uxIdx;

    for(uxIdx=0; uxIdx < configNUMBER_OF_CORES; uxIdx++)
    {
        if (pxCurrentTCBs[uxIdx] != NULL)
        {
            printf("    [%d]: 0x%lX\n", (int)uxIdx, pxCurrentTCBs[uxIdx]->uxTaskAttributes);
        }
    }
}

void test_coverage_prvAddNewTaskToReadyList_create_more_tasks_than_there_are_cores( void )
{
    TaskHandle_t xTaskHandles[configNUMBER_OF_CORES+3] = { NULL };

    UBaseType_t uxTaskNum;

    for(uxTaskNum=0; uxTaskNum <= configNUMBER_OF_CORES+1; uxTaskNum++)
    {
        xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 1, &xTaskHandles[uxTaskNum]);
        printf("uxCurrentNumberOfTasks: %d, uxTaskNum=%d\n", (int)uxCurrentNumberOfTasks, (int)uxTaskNum);
        show_task_status();
        vTaskPreemptionDisable( xTaskHandles[uxTaskNum] );
    }

    //TEST_ASSERT_EQUAL( configNUMBER_OF_CORES, uxCurrentNumberOfTasks );
    printf("ALL TASKS RUNNING:\n");
    printf("uxCurrentNumberOfTasks: %d, uxTaskNum=%d\n", (int)uxCurrentNumberOfTasks, (int)configNUMBER_OF_CORES+2);
    show_task_status();
    xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 1, &xTaskHandles[configNUMBER_OF_CORES+2]);
    printf("xTaskHandles[%d]: 0x%lX\n", (int)configNUMBER_OF_CORES+2, xTaskHandles[configNUMBER_OF_CORES+2]->uxTaskAttributes);

    vTaskStartScheduler();

    show_task_status();
}

/*
Coverage for
    void vTaskCoreAffinitySet( const TaskHandle_t xTask, UBaseType_t uxCoreAffinityMask )
    covers the case where vTaskCoreAffinitySet is called with NULL being passed to xTask
    implicitly referring to the current task.
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

/*
Coverage for
    void vTaskCoreAffinitySet( const TaskHandle_t xTask, UBaseType_t uxCoreAffinityMask )
    covers the case where vTaskCoreAffinitySet is called with NULL being passed to xTask 
    implicitly referring to the current task.
*/

void test_coverage_vTaskCoreAffinitySet_task_core_affinity_set_task_explicit( void )
{
    TaskHandle_t xTaskHandles[configNUMBER_OF_CORES] = { NULL };

    xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 1, &xTaskHandles[0]);
    vTaskCoreAffinitySet(xTaskHandles[0], (UBaseType_t)0xFF);

    vTaskStartScheduler();
}

/*
Coverage for
    void vTaskCoreAffinitySet( const TaskHandle_t xTask, UBaseType_t uxCoreAffinityMask )
    covers the case where the affinity mask no longer includes the current core, triggering a yield
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

/*
Coverage for
    void vTaskCoreAffinitySet( const TaskHandle_t xTask, UBaseType_t uxCoreAffinityMask )
    Changes the affinity of a suspended task such that it must yield on the core
    it was originally running.
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

/*
Coverage for
    void vTaskCoreAffinitySet( const TaskHandle_t xTask, UBaseType_t uxCoreAffinityMask )
    Given #define taskTASK_IS_RUNNING( pxTCB )     ( ( pxTCB->xTaskRunState >= 0 ) && ( pxTCB->xTaskRunState < configNUMBER_OF_CORES ) )
    Call the above macro where the second expression evaluates to false.
*/

void test_coverage_vTaskCoreAffinitySet_task_core_affinity_set_with_invalid_running_core( void )
{
    TaskHandle_t xTaskHandles[configNUMBER_OF_CORES] = { NULL };
    UBaseType_t xidx;

    xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 1, &xTaskHandles[0] );
    vTaskCoreAffinitySet(xTaskHandles[0], (UBaseType_t)0x1);

    vTaskStartScheduler();

    for (xidx = 0; xidx < configNUMBER_OF_CORES ; xidx++) {
        xTaskIncrementTick_helper();
    }

    xTaskHandles[0]->xTaskRunState = configNUMBER_OF_CORES+1;
    vTaskCoreAffinitySet(xTaskHandles[0], (UBaseType_t)0x2);

    for (xidx = 0; xidx < configNUMBER_OF_CORES ; xidx++) {
        xTaskIncrementTick_helper();
    }
}

/*
Coverage for
    BaseType_t xTaskGenericNotify( TaskHandle_t xTaskToNotify,
        UBaseType_t uxIndexToNotify,
        uint32_t ulValue,
        eNotifyAction eAction,
        uint32_t * pulPreviousNotificationValue )

    Call w/ eAction = eNoAction.
*/

void test_coverage_xTaskGenericNotify_with_eAction_equalto_eNoAction( void )
{
   TaskHandle_t xTaskHandles[configNUMBER_OF_CORES] = { NULL };
    UBaseType_t xidx;
    uint32_t *prevValue = NULL;
    uint32_t ulValue = 0;

    xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 1, &xTaskHandles[0] );

    vTaskStartScheduler();

    for (xidx = 0; xidx < configNUMBER_OF_CORES ; xidx++) {
        xTaskIncrementTick_helper();
    }

    xTaskGenericNotify( xTaskHandles[0], xidx, ulValue, eNoAction, prevValue);
}

/*
Coverage for
    BaseType_t xTaskGenericNotify( TaskHandle_t xTaskToNotify,
        UBaseType_t uxIndexToNotify,
        uint32_t ulValue,
        eNotifyAction eAction,
        uint32_t * pulPreviousNotificationValue )

    Call w/ eAction = eNoAction and a prevValue from index 0.
*/

void test_coverage_xTaskGenericNotify_with_eAction_equalto_eNoAction_prevValue( void )
{
   TaskHandle_t xTaskHandles[configNUMBER_OF_CORES] = { NULL };
    UBaseType_t xidx = 0;
    uint32_t prevValue;
    uint32_t ulValue = 0;

    xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 1, &xTaskHandles[0] );

    vTaskStartScheduler();

    for (xidx = 0; xidx < configNUMBER_OF_CORES ; xidx++) {
        xTaskIncrementTick_helper();
    }

    xTaskGenericNotify( xTaskHandles[0], xidx, ulValue, eNoAction, &prevValue);
}

/*
Coverage for
    BaseType_t xTaskGenericNotify( TaskHandle_t xTaskToNotify,
        UBaseType_t uxIndexToNotify,
        uint32_t ulValue,
        eNotifyAction eAction,
        uint32_t * pulPreviousNotificationValue )

    Call w/ eAction = eSetBits and a prevValue from index 0.
*/

void test_coverage_xTaskGenericNotify_with_eAction_equalto_eSetBits_prevValue( void )
{
   TaskHandle_t xTaskHandles[configNUMBER_OF_CORES] = { NULL };
    UBaseType_t xidx = 0;
    uint32_t prevValue;
    uint32_t ulValue = 0;

    xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 1, &xTaskHandles[0] );

    vTaskStartScheduler();

    for (xidx = 0; xidx < configNUMBER_OF_CORES ; xidx++) {
        xTaskIncrementTick_helper();
    }

    xTaskGenericNotify( xTaskHandles[0], xidx, ulValue, eSetBits, &prevValue);
}

/*
Coverage for
    BaseType_t xTaskGenericNotify( TaskHandle_t xTaskToNotify,
        UBaseType_t uxIndexToNotify,
        uint32_t ulValue,
        eNotifyAction eAction,
        uint32_t * pulPreviousNotificationValue )

    Call w/ eAction = eIncrement and a prevValue from index 0.
*/

void test_coverage_xTaskGenericNotify_with_eAction_equalto_eIncrement_prevValue( void )
{
   TaskHandle_t xTaskHandles[configNUMBER_OF_CORES] = { NULL };
    UBaseType_t xidx = 0;
    uint32_t prevValue;
    uint32_t ulValue = 0;

    xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 1, &xTaskHandles[0] );

    vTaskStartScheduler();

    for (xidx = 0; xidx < configNUMBER_OF_CORES ; xidx++) {
        xTaskIncrementTick_helper();
    }

    xTaskGenericNotify( xTaskHandles[0], xidx, ulValue, eIncrement, &prevValue);
}

/*
Coverage for
    BaseType_t xTaskGenericNotify( TaskHandle_t xTaskToNotify,
        UBaseType_t uxIndexToNotify,
        uint32_t ulValue,
        eNotifyAction eAction,
        uint32_t * pulPreviousNotificationValue )

    Call w/ eAction = eSetValueWithOverwrite and a prevValue from index 0.
*/

void test_coverage_xTaskGenericNotify_with_eAction_equalto_eSetValueWithOverwrite_prevValue( void )
{
   TaskHandle_t xTaskHandles[configNUMBER_OF_CORES] = { NULL };
    UBaseType_t xidx = 0;
    uint32_t prevValue;
    uint32_t ulValue = 0;

    xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 1, &xTaskHandles[0] );

    vTaskStartScheduler();

    for (xidx = 0; xidx < configNUMBER_OF_CORES ; xidx++) {
        xTaskIncrementTick_helper();
    }

    xTaskGenericNotify( xTaskHandles[0], xidx, ulValue, eSetValueWithOverwrite, &prevValue);
}

/*
Coverage for
    BaseType_t xTaskGenericNotify( TaskHandle_t xTaskToNotify,
        UBaseType_t uxIndexToNotify,
        uint32_t ulValue,
        eNotifyAction eAction,
        uint32_t * pulPreviousNotificationValue )

    Call w/ eAction = eSetValueWithoutOverwrite and a prevValue from index 0.
*/

void test_coverage_xTaskGenericNotify_with_eAction_equalto_eSetValueWithoutOverwrite_prevValue( void )
{
   TaskHandle_t xTaskHandles[configNUMBER_OF_CORES] = { NULL };
    UBaseType_t xidx = 0;
    uint32_t prevValue;
    uint32_t ulValue = 0;

    xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 1, &xTaskHandles[0] );

    vTaskStartScheduler();

    for (xidx = 0; xidx < configNUMBER_OF_CORES ; xidx++) {
        xTaskIncrementTick_helper();
    }

    xTaskGenericNotify( xTaskHandles[0], xidx, ulValue, eSetValueWithoutOverwrite, &prevValue);
}

/*
Coverage for
    BaseType_t xTaskGenericNotify( TaskHandle_t xTaskToNotify,
        UBaseType_t uxIndexToNotify,
        uint32_t ulValue,
        eNotifyAction eAction,
        uint32_t * pulPreviousNotificationValue )

    Call w/ eAction = eSetValueWithoutOverwrite and a prevValue from index 0.
*/

void test_coverage_xTaskGenericNotify_with_eAction_equalto_eSetValueWithoutOverwrite_branch2_prevValue( void )
{
   TaskHandle_t xTaskHandles[configNUMBER_OF_CORES] = { NULL };
    UBaseType_t xidx = 0;
    uint32_t *prevValue = NULL;
    uint32_t ulValue = 0;

    xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 1, &xTaskHandles[0] );

    vTaskStartScheduler();

    for (xidx = 0; xidx < configNUMBER_OF_CORES ; xidx++) {
        xTaskIncrementTick_helper();
    }

    xTaskHandles[0]->ucNotifyState[ xidx ] = /*taskNOTIFICATION_RECEIVED*/ ( ( uint8_t ) 2 );
    xTaskGenericNotify( xTaskHandles[0], xidx, ulValue, eSetValueWithoutOverwrite, prevValue);
}

/*
Coverage for
    BaseType_t xTaskGenericNotify( TaskHandle_t xTaskToNotify,
        UBaseType_t uxIndexToNotify,
        uint32_t ulValue,
        eNotifyAction eAction,
        uint32_t * pulPreviousNotificationValue )

    Call w/ eAction = eNoAction and an internal taskWAITING_NOTIFICATION.
*/

void test_coverage_xTaskGenericNotify_with_eAction_equalto_eNoAction_taskWAITING_NOTIFICATION( void )
{
   TaskHandle_t xTaskHandles[configNUMBER_OF_CORES] = { NULL };
    UBaseType_t xidx = 0;
    uint32_t *prevValue = NULL;
    uint32_t ulValue = 0;

    xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 1, &xTaskHandles[0] );

    vTaskStartScheduler();

    for (xidx = 0; xidx < configNUMBER_OF_CORES ; xidx++) {
        xTaskIncrementTick_helper();
    }

    xTaskHandles[0]->ucNotifyState[ xidx ] = /*taskWAITING_NOTIFICATION*/ ( ( uint8_t ) 1 );
    xTaskGenericNotify( xTaskHandles[0], xidx, ulValue, eNoAction, prevValue);
}

/*
Coverage for
    void vTaskGetInfo( TaskHandle_t xTask,
                       TaskStatus_t * pxTaskStatus,
                       BaseType_t xGetFreeStackSpace,
                       eTaskState eState )

    Call vTaskGetInfo with xTask as NULL, so that implicitly uses the current task.
*/

void test_coverage_vTaskGetInfo_implicit_task( void )
{
    TaskHandle_t xTaskHandles[configNUMBER_OF_CORES] = { NULL };
    TaskStatus_t pxTaskStatus;
    UBaseType_t xidx;
    BaseType_t xFreeStackSpace = pdTRUE;
    eTaskState taskState = eReady;

    xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 1, &xTaskHandles[0] );

    vTaskStartScheduler();

    for (xidx = 0; xidx < configNUMBER_OF_CORES ; xidx++) {
        xTaskIncrementTick_helper();
    }

    vTaskGetInfo( NULL, &pxTaskStatus, xFreeStackSpace, taskState);
}

/*
Coverage for
    void vTaskGetInfo( TaskHandle_t xTask,
                       TaskStatus_t * pxTaskStatus,
                       BaseType_t xGetFreeStackSpace,
                       eTaskState eState )

    Call vTaskGetInfo with an explicit task.
*/

void test_coverage_vTaskGetInfo_explicit_task( void )
{
    TaskHandle_t xTaskHandles[configNUMBER_OF_CORES] = { NULL };
    TaskStatus_t pxTaskStatus;
    UBaseType_t xidx;
    BaseType_t xFreeStackSpace = pdTRUE;
    eTaskState taskState = eReady;

    xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 1, &xTaskHandles[0] );

    vTaskStartScheduler();

    for (xidx = 0; xidx < configNUMBER_OF_CORES ; xidx++) {
        xTaskIncrementTick_helper();
    }

    vTaskGetInfo( xTaskHandles[0], &pxTaskStatus, xFreeStackSpace, taskState);
}

/*
Coverage for
    void vTaskGetInfo( TaskHandle_t xTask,
                       TaskStatus_t * pxTaskStatus,
                       BaseType_t xGetFreeStackSpace,
                       eTaskState eState )

    Call vTaskGetInfo on a suspended task with a non-NULL xEventListItem such that it reports
    that it is blocked.
*/

void test_coverage_vTaskGetInfo_blocked_task( void )
{
    TaskHandle_t xTaskHandles[configNUMBER_OF_CORES] = { NULL };
    TaskStatus_t pxTaskStatus;
    UBaseType_t xidx;
    BaseType_t xFreeStackSpace = pdTRUE;
    eTaskState taskState = eSuspended;

    xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 1, &xTaskHandles[0] );

    vTaskStartScheduler();

    for (xidx = 0; xidx < configNUMBER_OF_CORES ; xidx++) {
        xTaskIncrementTick_helper();
    }

    xTaskHandles[0]->xEventListItem.pxContainer = (struct xLIST *) 1;
    vTaskGetInfo( xTaskHandles[0], &pxTaskStatus, xFreeStackSpace, taskState);

    printf("DEBUG: taskState: %d\n", (int)taskState);
}


/*
Coverage for
    void vTaskGetInfo( TaskHandle_t xTask,
                       TaskStatus_t * pxTaskStatus,
                       BaseType_t xGetFreeStackSpace,
                       eTaskState eState )

    Call vTaskGetInfo with xTaskRunState >= configNUMBER_OF_CORES.
*/

void test_coverage_vTaskGetInfo_oob_xTaskRunState( void )
{
    TaskHandle_t xTaskHandles[configNUMBER_OF_CORES] = { NULL };
    TaskStatus_t pxTaskStatus;
    UBaseType_t xidx;
    BaseType_t xFreeStackSpace = pdTRUE;
    eTaskState taskState = eReady;

    xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 1, &xTaskHandles[0] );

    vTaskStartScheduler();

    for (xidx = 0; xidx < configNUMBER_OF_CORES ; xidx++) {
        xTaskIncrementTick_helper();
    }

    xTaskHandles[0]->xTaskRunState = configNUMBER_OF_CORES;
    vTaskGetInfo( xTaskHandles[0], &pxTaskStatus, xFreeStackSpace, taskState);
}

/*
Coverage for
    void vTaskGetInfo( TaskHandle_t xTask,
                       TaskStatus_t * pxTaskStatus,
                       BaseType_t xGetFreeStackSpace,
                       eTaskState eState )

    Call vTaskGetInfo xGetFreeStackSpace set to pdFALSE.
*/

void test_coverage_vTaskGetInfo_skip_get_free_stack_space( void )
{
    TaskHandle_t xTaskHandles[configNUMBER_OF_CORES] = { NULL };
    TaskStatus_t pxTaskStatus;
    UBaseType_t xidx;
    BaseType_t xFreeStackSpace = pdFALSE;
    eTaskState taskState = eReady;

    xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 1, &xTaskHandles[0] );

    vTaskStartScheduler();

    for (xidx = 0; xidx < configNUMBER_OF_CORES ; xidx++) {
        xTaskIncrementTick_helper();
    }

    vTaskGetInfo( xTaskHandles[0], &pxTaskStatus, xFreeStackSpace, taskState);
}