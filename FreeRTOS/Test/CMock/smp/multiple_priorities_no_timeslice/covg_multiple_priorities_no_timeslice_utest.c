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
#include "portmacro.h"

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

#define taskRECORD_READY_PRIORITY( uxPriority ) \
{                                               \
    if( ( uxPriority ) > uxTopReadyPriority )   \
    {                                           \
        uxTopReadyPriority = ( uxPriority );    \
    }                                           \
} /* taskRECORD_READY_PRIORITY */


/* ===========================  EXTERN VARIABLES  =========================== */
extern volatile UBaseType_t uxCurrentNumberOfTasks;
extern volatile UBaseType_t uxDeletedTasksWaitingCleanUp;
extern volatile UBaseType_t uxSchedulerSuspended;
extern volatile TCB_t *  pxCurrentTCBs[ configNUMBER_OF_CORES ];
extern volatile BaseType_t xSchedulerRunning;
extern volatile TickType_t xTickCount;
extern List_t xSuspendedTaskList;
extern List_t xPendingReadyList;
extern List_t pxReadyTasksLists[ configMAX_PRIORITIES ];
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

/**
 * @brief xTaskPriorityDisinherit - disinherit priority, potentially restoring the original priority used before escalation due to mutex usage
 *
 * <b>Coverage</b>
 * @code{c}
 *     if( pxTCB->uxPriority != pxTCB->uxBasePriority )
 *     {
 *     ...
 *          if( pxTCB->uxMutexesHeld == ( UBaseType_t ) 0 )
 * @endcode
 *
 * Cover the case where priority has changed due to inheritance
 * because of a shared mutex.
 *
 */
void test_coverage_xTaskPriorityDisinherit_current_is_same( void )
{
    TaskHandle_t xTaskHandles[configNUMBER_OF_CORES] = { NULL };
    UBaseType_t xidx;

    xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 0, &xTaskHandles[0]);

    vTaskStartScheduler();

    for (xidx = 0; xidx < configNUMBER_OF_CORES ; xidx++) {
        xTaskIncrementTick_helper();
    }

    vTaskPrioritySet( NULL, 1 );
    xTaskPriorityInherit( xTaskHandles[0] );

    xTaskPriorityDisinherit( xTaskHandles[0] );
}

/**
 * @brief xTaskPriorityDisinherit - disinherit priority, potentially restoring the original priority used before escalation due to mutex usage
 *
 * <b>Coverage</b>
 * @code{c}
 *       if( pxMutexHolder != NULL )
 *       {
 *     ...
 * @endcode
 *
 * Cover the case where a NULL task is specified.
 *
 */
void test_coverage_xTaskPriorityDisinherit_null_task( void )
{
    xTaskPriorityDisinherit( NULL );
}

/**
 * @brief xTaskResumeAll - resume all suspended tasks
 *
 * <b>Coverage</b>
 * @code{c}
 *  if( xSchedulerRunning != pdFALSE )
 *  ...
 *          if( uxCurrentNumberOfTasks > ( UBaseType_t ) 0U )
 * @endcode
 *
 *
* Cover the case where the scheduler is running and there is at least one task.
 */
void test_coverage_xTaskResumeAll_common_case( void )
{
    TCB_t xTaskTCBs[ configNUMBER_OF_CORES + 1U ] = { NULL };
    uint32_t i;
    BaseType_t xAlreadyYielded;
    UBaseType_t uxPriority;

    for(
        uxPriority = ( UBaseType_t ) 0U;
        uxPriority < ( UBaseType_t ) configMAX_PRIORITIES;
        uxPriority++)
    {
        vListInitialise( &( pxReadyTasksLists[ uxPriority ] ) );
    }
    vListInitialise( &xSuspendedTaskList );
    vListInitialise( &xPendingReadyList );

    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        xTaskTCBs[ i ].uxPriority = 1;
        xTaskTCBs[ i ].xTaskRunState = i;
        vListInitialiseItem( &( xTaskTCBs[i].xStateListItem ) );
        listSET_LIST_ITEM_OWNER( &( xTaskTCBs[i].xStateListItem ), &xTaskTCBs[i] );
        xYieldPendings[ i ] = pdTRUE;
        pxCurrentTCBs[ i ] = &xTaskTCBs[ i ];
    }

    xTaskTCBs[ configNUMBER_OF_CORES ].uxPriority = 2;
    vListInitialiseItem( &( xTaskTCBs[configNUMBER_OF_CORES].xStateListItem ) );
    listSET_LIST_ITEM_OWNER( &( xTaskTCBs[configNUMBER_OF_CORES].xStateListItem ), &xTaskTCBs[i] );
    listINSERT_END( &xSuspendedTaskList, &xTaskTCBs[ i ].xStateListItem );
    uxTopReadyPriority = 1;

    uxSchedulerSuspended = pdFALSE;

    xAlreadyYielded = xTaskResumeAll();

    TEST_ASSERT_EQUAL(pdFALSE, xAlreadyYielded);
}

/**
 * @brief xTaskResumeAll - resume all suspended tasks
 *
 * <b>Coverage</b>
 * @code{c}
 *  while( listLIST_IS_EMPTY( &xPendingReadyList ) == pdFALSE )
 *  {
 *      pxTCB = listGET_OWNER_OF_HEAD_ENTRY( ( &xPendingReadyList ) );
 *  ...
 * @endcode
 *
 *
 * Cover the case where the scheduler is running and there are one or more
 * tasks in the pending ready list state.
 */
void test_coverage_xTaskResumeAll_pending_ready_list( void )
{
    TCB_t xTaskTCBs[ configNUMBER_OF_CORES + 1U ] = { NULL };
    uint32_t i;
    BaseType_t xAlreadyYielded;
    UBaseType_t uxPriority;

    for(
        uxPriority = ( UBaseType_t ) 0U;
        uxPriority < ( UBaseType_t ) configMAX_PRIORITIES;
        uxPriority++)
    {
        vListInitialise( &( pxReadyTasksLists[ uxPriority ] ) );
    }
    vListInitialise( &xSuspendedTaskList );
    vListInitialise( &xPendingReadyList );

    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        xTaskTCBs[ i ].uxPriority = 1;
        xTaskTCBs[ i ].xTaskRunState = -1;
        vListInitialiseItem( &( xTaskTCBs[i].xStateListItem ) );
        listSET_LIST_ITEM_OWNER( &( xTaskTCBs[i].xStateListItem ), &xTaskTCBs[i] );
        listINSERT_END( &xPendingReadyList, &xTaskTCBs[ i ].xStateListItem );
        xYieldPendings[ i ] = pdFALSE;
        //pxCurrentTCBs[ i ] = &xTaskTCBs[ i ];
    }
    uxTopReadyPriority = 1;

    uxSchedulerSuspended = pdFALSE;

    xAlreadyYielded = xTaskResumeAll();

    TEST_ASSERT_EQUAL(pdFALSE, xAlreadyYielded);
}

/**
 * @brief xTaskPriorityDisinherit - restore the priority held before inheriting priority due to mutex usage
 *
 * <b>Coverage</b>
 * @code{c}
 *    if( pxTCB->uxPriority != pxTCB->uxBasePriority )
 *    {
 *      ...
 * @endcode
 *
 *
 * Cover the case where the current priority is not the base priority and
 * exactly one mutex is being held.
 */
void test_coverage_xTaskPriorityDisinherit_exactly_one_mutex_priority_delta( void )
{
    TCB_t xTaskTCBs[ 2U ] = { NULL };
    UBaseType_t uxPriority;
    BaseType_t xReturn;

    for(
        uxPriority = ( UBaseType_t ) 0U;
        uxPriority < ( UBaseType_t ) configMAX_PRIORITIES;
        uxPriority++)
    {
        vListInitialise( &( pxReadyTasksLists[ uxPriority ] ) );
    }
    vListInitialise( &xSuspendedTaskList );
    vListInitialise( &xPendingReadyList );

    xTaskTCBs[ 0 ].uxPriority = 1;
    xTaskTCBs[ 0 ].xTaskRunState = -1;
    vListInitialiseItem( &( xTaskTCBs[0].xStateListItem ) );
    listSET_LIST_ITEM_OWNER( &( xTaskTCBs[0].xStateListItem ), &xTaskTCBs[0] );
    listINSERT_END( &xPendingReadyList, &xTaskTCBs[ 0 ].xStateListItem );
    xYieldPendings[ 0 ] = pdFALSE;
    pxCurrentTCBs[ 0 ] = &xTaskTCBs[ 0 ];

    xTaskTCBs[ 1 ].uxPriority = 2;
    xTaskTCBs[ 1 ].xTaskRunState = 1;
    vListInitialiseItem( &( xTaskTCBs[1].xStateListItem ) );
    listSET_LIST_ITEM_OWNER( &( xTaskTCBs[1].xStateListItem ), &xTaskTCBs[1] );
    xYieldPendings[ 1 ] = pdFALSE;
    pxCurrentTCBs[ 1 ] = &xTaskTCBs[ 1 ];

    uxTopReadyPriority = 1;
    uxSchedulerSuspended = pdFALSE;

    /* task 0 priority is lower than task 1. mutex holder state accounting for new priority */
    listSET_LIST_ITEM_VALUE( &( xTaskTCBs[0].xEventListItem ), ( TickType_t ) configMAX_PRIORITIES - ( TickType_t ) xTaskTCBs[1].uxPriority ); /*lint !e961 MISRA exception as the casts are only redundant for some ports. */

    /* task 1 is in the ready state */
    if( uxListRemove( &( xTaskTCBs[0].xStateListItem ) ) == ( UBaseType_t ) 0 )
    {
        ( uxTopReadyPriority ) &= ~( 1UL << ( xTaskTCBs[0].uxPriority ) );
    }

    xTaskTCBs[0].uxPriority = xTaskTCBs[1].uxPriority;
    taskRECORD_READY_PRIORITY( xTaskTCBs[0].uxPriority );
    listINSERT_END( &( pxReadyTasksLists[ xTaskTCBs[0].uxPriority ] ), &( xTaskTCBs[0].xStateListItem ) );
    listINSERT_END( &( pxReadyTasksLists[ xTaskTCBs[1].uxPriority ] ), &( xTaskTCBs[1].xStateListItem ) );
    xTaskTCBs[1].uxMutexesHeld++;

    xReturn = xTaskPriorityDisinherit( &xTaskTCBs[1] );
    TEST_ASSERT_EQUAL(pdTRUE, xReturn);
}

/**
 * @brief xTaskPriorityDisinherit - restore the priority held before inheriting priority due to mutex usage
 *
 * <b>Coverage</b>
 * @code{c}
 *          if( pxTCB->uxMutexesHeld == ( UBaseType_t ) 0 )
 *          {
 *              ...
 * @endcode
 *
 *
 * Cover the case where the current priority is not the base priority and
 * the mutex count is 2
 */
void test_coverage_xTaskPriorityDisinherit_exactly_priority_delta_mutex_count_two( void )
{
    TCB_t xTaskTCBs[ 2U ] = { NULL };
    UBaseType_t uxPriority;
    BaseType_t xReturn;

    for(
        uxPriority = ( UBaseType_t ) 0U;
        uxPriority < ( UBaseType_t ) configMAX_PRIORITIES;
        uxPriority++)
    {
        vListInitialise( &( pxReadyTasksLists[ uxPriority ] ) );
    }
    vListInitialise( &xSuspendedTaskList );
    vListInitialise( &xPendingReadyList );

    xTaskTCBs[ 0 ].uxPriority = 1;
    xTaskTCBs[ 0 ].xTaskRunState = -1;
    vListInitialiseItem( &( xTaskTCBs[0].xStateListItem ) );
    listSET_LIST_ITEM_OWNER( &( xTaskTCBs[0].xStateListItem ), &xTaskTCBs[0] );
    listINSERT_END( &xPendingReadyList, &xTaskTCBs[ 0 ].xStateListItem );
    xYieldPendings[ 0 ] = pdFALSE;
    pxCurrentTCBs[ 0 ] = &xTaskTCBs[ 0 ];

    xTaskTCBs[ 1 ].uxPriority = 2;
    xTaskTCBs[ 1 ].xTaskRunState = 1;
    vListInitialiseItem( &( xTaskTCBs[1].xStateListItem ) );
    listSET_LIST_ITEM_OWNER( &( xTaskTCBs[1].xStateListItem ), &xTaskTCBs[1] );
    xYieldPendings[ 1 ] = pdFALSE;
    pxCurrentTCBs[ 1 ] = &xTaskTCBs[ 1 ];

    uxTopReadyPriority = 1;
    uxSchedulerSuspended = pdFALSE;

    /* task 0 priority is lower than task 1. mutex holder state accounting for new priority */
    listSET_LIST_ITEM_VALUE( &( xTaskTCBs[0].xEventListItem ), ( TickType_t ) configMAX_PRIORITIES - ( TickType_t ) xTaskTCBs[1].uxPriority ); /*lint !e961 MISRA exception as the casts are only redundant for some ports. */

    /* task 1 is in the ready state */
    if( uxListRemove( &( xTaskTCBs[0].xStateListItem ) ) == ( UBaseType_t ) 0 )
    {
        ( uxTopReadyPriority ) &= ~( 1UL << ( xTaskTCBs[0].uxPriority ) );
    }

    xTaskTCBs[0].uxPriority = xTaskTCBs[1].uxPriority;
    taskRECORD_READY_PRIORITY( xTaskTCBs[0].uxPriority );
    listINSERT_END( &( pxReadyTasksLists[ xTaskTCBs[0].uxPriority ] ), &( xTaskTCBs[0].xStateListItem ) );
    listINSERT_END( &( pxReadyTasksLists[ xTaskTCBs[1].uxPriority ] ), &( xTaskTCBs[1].xStateListItem ) );
    xTaskTCBs[1].uxMutexesHeld = 2;

    xReturn = xTaskPriorityDisinherit( &xTaskTCBs[1] );
    TEST_ASSERT_EQUAL(pdFALSE, xReturn);
}

/**
 * @brief xTaskPriorityDisinheritAfterTimeoout - restore the priority held before inheriting priority due to mutex usage
 *
 * <b>Coverage</b>
 * @code{c}
 *    if( pxTCB->uxPriority != pxTCB->uxBasePriority )
 *    {
 *      ...
 * @endcode
 *
 *
 * Cover the case where the current priority is not the base priority and
 * exactly one mutex is being held.
 */
void test_coverage_xTaskPriorityDisinheritAfterTimeout_exactly_one_mutex_basepriority_equal( void )
{
    TCB_t xTaskTCBs[ 2U ] = { NULL };
    UBaseType_t uxPriority;

    for(
        uxPriority = ( UBaseType_t ) 0U;
        uxPriority < ( UBaseType_t ) configMAX_PRIORITIES;
        uxPriority++)
    {
        vListInitialise( &( pxReadyTasksLists[ uxPriority ] ) );
    }
    vListInitialise( &xSuspendedTaskList );
    vListInitialise( &xPendingReadyList );

    xTaskTCBs[ 0 ].uxPriority = 1;
    xTaskTCBs[ 0 ].xTaskRunState = -1;
    vListInitialiseItem( &( xTaskTCBs[0].xStateListItem ) );
    listSET_LIST_ITEM_OWNER( &( xTaskTCBs[0].xStateListItem ), &xTaskTCBs[0] );
    listINSERT_END( &xPendingReadyList, &xTaskTCBs[ 0 ].xStateListItem );
    xYieldPendings[ 0 ] = pdFALSE;
    pxCurrentTCBs[ 0 ] = &xTaskTCBs[ 0 ];

    xTaskTCBs[ 1 ].uxPriority = 2;
    xTaskTCBs[ 1 ].xTaskRunState = 1;
    vListInitialiseItem( &( xTaskTCBs[1].xStateListItem ) );
    listSET_LIST_ITEM_OWNER( &( xTaskTCBs[1].xStateListItem ), &xTaskTCBs[1] );
    xYieldPendings[ 1 ] = pdFALSE;
    pxCurrentTCBs[ 1 ] = &xTaskTCBs[ 1 ];

    uxTopReadyPriority = 1;
    uxSchedulerSuspended = pdFALSE;

    /* task 0 priority is lower than task 1. mutex holder state accounting for new priority */
    listSET_LIST_ITEM_VALUE( &( xTaskTCBs[0].xEventListItem ), ( TickType_t ) configMAX_PRIORITIES - ( TickType_t ) xTaskTCBs[1].uxPriority ); /*lint !e961 MISRA exception as the casts are only redundant for some ports. */

    /* task 1 is in the ready state */
    if( uxListRemove( &( xTaskTCBs[0].xStateListItem ) ) == ( UBaseType_t ) 0 )
    {
        ( uxTopReadyPriority ) &= ~( 1UL << ( xTaskTCBs[0].uxPriority ) );
    }

    xTaskTCBs[0].uxPriority = xTaskTCBs[1].uxPriority;
    taskRECORD_READY_PRIORITY( xTaskTCBs[0].uxPriority );
    listINSERT_END( &( pxReadyTasksLists[ xTaskTCBs[0].uxPriority ] ), &( xTaskTCBs[0].xStateListItem ) );
    listINSERT_END( &( pxReadyTasksLists[ xTaskTCBs[1].uxPriority ] ), &( xTaskTCBs[1].xStateListItem ) );
    xTaskTCBs[1].uxMutexesHeld++;

    printf("TRACE: xTaskTCBs[1].uxBasePriority: %lu\n", xTaskTCBs[1].uxBasePriority);
    vTaskPriorityDisinheritAfterTimeout( &xTaskTCBs[1], (UBaseType_t)0 );
}

/**
 * @brief xTaskPriorityDisinheritAfterTimeout - restore the priority held before inheriting priority due to mutex usage
 *
 * <b>Coverage</b>
 * @code{c}
 *    if( pxTCB->uxPriority != pxTCB->uxBasePriority )
 *    {
 *      ...
 * @endcode
 *
 *
 * Cover the case where the current priority is not the base priority and
 * exactly one mutex is being held.
 */
void test_coverage_xTaskPriorityDisinheritAfterTimeout_exactly_one_mutex_basepriority_delta( void )
{
    TCB_t xTaskTCBs[ 2U ] = { NULL };
    UBaseType_t uxPriority;

    for(
        uxPriority = ( UBaseType_t ) 0U;
        uxPriority < ( UBaseType_t ) configMAX_PRIORITIES;
        uxPriority++)
    {
        vListInitialise( &( pxReadyTasksLists[ uxPriority ] ) );
    }
    vListInitialise( &xSuspendedTaskList );
    vListInitialise( &xPendingReadyList );

    xTaskTCBs[ 0 ].uxPriority = 1;
    xTaskTCBs[ 0 ].xTaskRunState = -1;
    vListInitialiseItem( &( xTaskTCBs[0].xStateListItem ) );
    listSET_LIST_ITEM_OWNER( &( xTaskTCBs[0].xStateListItem ), &xTaskTCBs[0] );
    listINSERT_END( &xPendingReadyList, &xTaskTCBs[ 0 ].xStateListItem );
    xYieldPendings[ 0 ] = pdFALSE;
    pxCurrentTCBs[ 0 ] = &xTaskTCBs[ 0 ];

    xTaskTCBs[ 1 ].uxPriority = 2;
    xTaskTCBs[ 1 ].xTaskRunState = 1;
    vListInitialiseItem( &( xTaskTCBs[1].xStateListItem ) );
    listSET_LIST_ITEM_OWNER( &( xTaskTCBs[1].xStateListItem ), &xTaskTCBs[1] );
    xYieldPendings[ 1 ] = pdFALSE;
    pxCurrentTCBs[ 1 ] = &xTaskTCBs[ 1 ];

    uxTopReadyPriority = 1;
    uxSchedulerSuspended = pdFALSE;

    /* task 0 priority is lower than task 1. mutex holder state accounting for new priority */
    listSET_LIST_ITEM_VALUE( &( xTaskTCBs[0].xEventListItem ), ( TickType_t ) configMAX_PRIORITIES - ( TickType_t ) xTaskTCBs[1].uxPriority ); /*lint !e961 MISRA exception as the casts are only redundant for some ports. */

    /* task 1 is in the ready state */
    if( uxListRemove( &( xTaskTCBs[0].xStateListItem ) ) == ( UBaseType_t ) 0 )
    {
        ( uxTopReadyPriority ) &= ~( 1UL << ( xTaskTCBs[0].uxPriority ) );
    }

    xTaskTCBs[0].uxPriority = xTaskTCBs[1].uxPriority;
    taskRECORD_READY_PRIORITY( xTaskTCBs[0].uxPriority );
    listINSERT_END( &( pxReadyTasksLists[ xTaskTCBs[0].uxPriority ] ), &( xTaskTCBs[0].xStateListItem ) );
    listINSERT_END( &( pxReadyTasksLists[ xTaskTCBs[1].uxPriority ] ), &( xTaskTCBs[1].xStateListItem ) );
    xTaskTCBs[1].uxMutexesHeld++;

    printf("TRACE: xTaskTCBs[1].uxBasePriority: %lu\n", xTaskTCBs[1].uxBasePriority);
    vTaskPriorityDisinheritAfterTimeout( &xTaskTCBs[1], (UBaseType_t)1 );
}

/**
 * @brief xTaskPriorityDisinheritAfterTimeout - restore the priority held before inheriting priority due to mutex usage
 *
 * <b>Coverage</b>
 * @code{c}
 *    if( pxTCB->uxPriority != pxTCB->uxBasePriority )
 *    {
 *      ...
 * @endcode
 *
 *
 * Cover the case where the current priority is not the base priority and
 * exactly one mutex is being held.
 */
void test_coverage_xTaskPriorityDisinheritAfterTimeout_exactly_one_mutex_curpriority_equal( void )
{
    TCB_t xTaskTCBs[ 2U ] = { NULL };
    UBaseType_t uxPriority;

    for(
        uxPriority = ( UBaseType_t ) 0U;
        uxPriority < ( UBaseType_t ) configMAX_PRIORITIES;
        uxPriority++)
    {
        vListInitialise( &( pxReadyTasksLists[ uxPriority ] ) );
    }
    vListInitialise( &xSuspendedTaskList );
    vListInitialise( &xPendingReadyList );

    xTaskTCBs[ 0 ].uxPriority = 1;
    xTaskTCBs[ 0 ].xTaskRunState = -1;
    vListInitialiseItem( &( xTaskTCBs[0].xStateListItem ) );
    listSET_LIST_ITEM_OWNER( &( xTaskTCBs[0].xStateListItem ), &xTaskTCBs[0] );
    listINSERT_END( &xPendingReadyList, &xTaskTCBs[ 0 ].xStateListItem );
    xYieldPendings[ 0 ] = pdFALSE;
    pxCurrentTCBs[ 0 ] = &xTaskTCBs[ 0 ];

    xTaskTCBs[ 1 ].uxPriority = 2;
    xTaskTCBs[ 1 ].xTaskRunState = 1;
    vListInitialiseItem( &( xTaskTCBs[1].xStateListItem ) );
    listSET_LIST_ITEM_OWNER( &( xTaskTCBs[1].xStateListItem ), &xTaskTCBs[1] );
    xYieldPendings[ 1 ] = pdFALSE;
    pxCurrentTCBs[ 1 ] = &xTaskTCBs[ 1 ];

    uxTopReadyPriority = 1;
    uxSchedulerSuspended = pdFALSE;

    /* task 0 priority is lower than task 1. mutex holder state accounting for new priority */
    listSET_LIST_ITEM_VALUE( &( xTaskTCBs[0].xEventListItem ), ( TickType_t ) configMAX_PRIORITIES - ( TickType_t ) xTaskTCBs[1].uxPriority ); /*lint !e961 MISRA exception as the casts are only redundant for some ports. */

    /* task 1 is in the ready state */
    if( uxListRemove( &( xTaskTCBs[0].xStateListItem ) ) == ( UBaseType_t ) 0 )
    {
        ( uxTopReadyPriority ) &= ~( 1UL << ( xTaskTCBs[0].uxPriority ) );
    }

    xTaskTCBs[0].uxPriority = xTaskTCBs[1].uxPriority;
    taskRECORD_READY_PRIORITY( xTaskTCBs[0].uxPriority );
    listINSERT_END( &( pxReadyTasksLists[ xTaskTCBs[0].uxPriority ] ), &( xTaskTCBs[0].xStateListItem ) );
    listINSERT_END( &( pxReadyTasksLists[ xTaskTCBs[1].uxPriority ] ), &( xTaskTCBs[1].xStateListItem ) );
    xTaskTCBs[1].uxMutexesHeld++;

    printf("TRACE: xTaskTCBs[1].uxBasePriority: %lu\n", xTaskTCBs[1].uxBasePriority);
    vTaskPriorityDisinheritAfterTimeout( &xTaskTCBs[1], (UBaseType_t)2 );
}


/**
 * @brief xTaskPriorityDisinheritAfterTimeout - restore the priority held before inheriting priority due to mutex usage
 *
 * <b>Coverage</b>
 * @code{c}
 *    if( pxTCB->uxPriority != pxTCB->uxBasePriority )
 *    {
 *      ...
 * @endcode
 *
 *
 * Cover the case where the current priority is not the base priority and
 * the mutex count is two.
 */
void test_coverage_xTaskPriorityDisinheritAfterTimeout_basepriority_delta_mutex_count_two( void )
{
    TCB_t xTaskTCBs[ 2U ] = { NULL };
    UBaseType_t uxPriority;

    for(
        uxPriority = ( UBaseType_t ) 0U;
        uxPriority < ( UBaseType_t ) configMAX_PRIORITIES;
        uxPriority++)
    {
        vListInitialise( &( pxReadyTasksLists[ uxPriority ] ) );
    }
    vListInitialise( &xSuspendedTaskList );
    vListInitialise( &xPendingReadyList );

    xTaskTCBs[ 0 ].uxPriority = 1;
    xTaskTCBs[ 0 ].xTaskRunState = -1;
    vListInitialiseItem( &( xTaskTCBs[0].xStateListItem ) );
    listSET_LIST_ITEM_OWNER( &( xTaskTCBs[0].xStateListItem ), &xTaskTCBs[0] );
    listINSERT_END( &xPendingReadyList, &xTaskTCBs[ 0 ].xStateListItem );
    xYieldPendings[ 0 ] = pdFALSE;
    pxCurrentTCBs[ 0 ] = &xTaskTCBs[ 0 ];

    xTaskTCBs[ 1 ].uxPriority = 2;
    xTaskTCBs[ 1 ].xTaskRunState = 1;
    vListInitialiseItem( &( xTaskTCBs[1].xStateListItem ) );
    listSET_LIST_ITEM_OWNER( &( xTaskTCBs[1].xStateListItem ), &xTaskTCBs[1] );
    xYieldPendings[ 1 ] = pdFALSE;
    pxCurrentTCBs[ 1 ] = &xTaskTCBs[ 1 ];

    uxTopReadyPriority = 1;
    uxSchedulerSuspended = pdFALSE;

    /* task 0 priority is lower than task 1. mutex holder state accounting for new priority */
    listSET_LIST_ITEM_VALUE( &( xTaskTCBs[0].xEventListItem ), ( TickType_t ) configMAX_PRIORITIES - ( TickType_t ) xTaskTCBs[1].uxPriority ); /*lint !e961 MISRA exception as the casts are only redundant for some ports. */

    /* task 1 is in the ready state */
    if( uxListRemove( &( xTaskTCBs[0].xStateListItem ) ) == ( UBaseType_t ) 0 )
    {
        ( uxTopReadyPriority ) &= ~( 1UL << ( xTaskTCBs[0].uxPriority ) );
    }

    xTaskTCBs[0].uxPriority = xTaskTCBs[1].uxPriority;
    taskRECORD_READY_PRIORITY( xTaskTCBs[0].uxPriority );
    listINSERT_END( &( pxReadyTasksLists[ xTaskTCBs[0].uxPriority ] ), &( xTaskTCBs[0].xStateListItem ) );
    listINSERT_END( &( pxReadyTasksLists[ xTaskTCBs[1].uxPriority ] ), &( xTaskTCBs[1].xStateListItem ) );
    xTaskTCBs[1].uxMutexesHeld = 2;

    printf("TRACE: xTaskTCBs[1].uxBasePriority: %lu\n", xTaskTCBs[1].uxBasePriority);
    vTaskPriorityDisinheritAfterTimeout( &xTaskTCBs[1], (UBaseType_t)1 );
}

/**
 * @brief xTaskPriorityDisinheritAfterTimeoout - restore the priority held before inheriting priority due to mutex usage
 *
 * <b>Coverage</b>
 * @code{c}
 *    if( pxTCB->uxPriority != pxTCB->uxBasePriority )
 *    {
 *      ...
 * @endcode
 *
 *
 * Cover the case where the current priority is not the base priority and
 * exactly one mutex is being held.
 */
void test_coverage_xTaskPriorityDisinheritAfterTimeout_pending_task_exactly_one_mutex_basepriority_equal( void )
{
    TCB_t xTaskTCBs[ 2U ] = { NULL };
    UBaseType_t uxPriority;

    for(
        uxPriority = ( UBaseType_t ) 0U;
        uxPriority < ( UBaseType_t ) configMAX_PRIORITIES;
        uxPriority++)
    {
        vListInitialise( &( pxReadyTasksLists[ uxPriority ] ) );
    }
    vListInitialise( &xSuspendedTaskList );
    vListInitialise( &xPendingReadyList );

    xTaskTCBs[ 0 ].uxPriority = 1;
    xTaskTCBs[ 0 ].xTaskRunState = -1;
    vListInitialiseItem( &( xTaskTCBs[0].xStateListItem ) );
    listSET_LIST_ITEM_OWNER( &( xTaskTCBs[0].xStateListItem ), &xTaskTCBs[0] );
    listINSERT_END( &xPendingReadyList, &xTaskTCBs[ 0 ].xStateListItem );
    xYieldPendings[ 0 ] = pdFALSE;
    pxCurrentTCBs[ 0 ] = &xTaskTCBs[ 0 ];

    xTaskTCBs[ 1 ].uxPriority = 2;
    xTaskTCBs[ 1 ].xTaskRunState = 1;
    vListInitialiseItem( &( xTaskTCBs[1].xStateListItem ) );
    listSET_LIST_ITEM_OWNER( &( xTaskTCBs[1].xStateListItem ), &xTaskTCBs[1] );
    xYieldPendings[ 1 ] = pdFALSE;
    pxCurrentTCBs[ 1 ] = &xTaskTCBs[ 1 ];

    uxTopReadyPriority = 1;
    uxSchedulerSuspended = pdFALSE;

    /* task 0 priority is lower than task 1. mutex holder state accounting for new priority */
    listSET_LIST_ITEM_VALUE( &( xTaskTCBs[0].xEventListItem ), ( TickType_t ) configMAX_PRIORITIES - ( TickType_t ) xTaskTCBs[1].uxPriority ); /*lint !e961 MISRA exception as the casts are only redundant for some ports. */

    listINSERT_END( &( pxReadyTasksLists[ xTaskTCBs[1].uxPriority ] ), &( xTaskTCBs[1].xStateListItem ) );
    xTaskTCBs[0].uxMutexesHeld++;

    printf("TRACE: xTaskTCBs[1].uxBasePriority: %lu\n", xTaskTCBs[1].uxBasePriority);
    vTaskPriorityDisinheritAfterTimeout( &xTaskTCBs[0], (UBaseType_t)0 );
}
