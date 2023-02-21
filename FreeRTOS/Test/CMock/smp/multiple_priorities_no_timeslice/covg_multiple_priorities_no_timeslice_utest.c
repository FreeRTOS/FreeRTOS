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

#if 0
/**
 * @brief prvAddNewTaskToReadyList - add a new idle task to the list of ready tasks
 *
 * This test creates more tasks than ther are cores in order to test the
 * branch related to the limit condition of the for loop.
 *
 * <b>Coverage</b>
 * @code{c}
 * for( xCoreID = 0; xCoreID < configNUMBER_OF_CORES; xCoreID++ )
 * @endcode
 * for loop condition ( xCoreID < configNUMBER_OF_CORES ) is false.
 */
// void test_coverage_prvAddNewTaskToReadyList_create_more_idle_tasks_than_cores( void )
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
            xTaskTCBs[ i ].xTaskRunState = -1;  /* Set run state to taskTASK_NOT_RUNNING. */
        }
    }

    /* API calls. */
    prvAddNewTaskToReadyList( &xTaskTCBs[ configNUMBER_OF_CORES ] );

    /* Validateions. The run state of this task is still taskNOT_RUNNING ( -1 ). */
    configASSERT( xTaskTCBs[ configNUMBER_OF_CORES + 1U ].xTaskRunState == -1 );
}
#endif

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
 * @brief vTaskExitCriticalFromISR - have a task exit a critical section from the ISR context
 *
 * <b>Coverage</b>
 * @code{c}
*       if( xSchedulerRunning != pdFALSE )
*        {
*        ...
*            configASSERT( portGET_CRITICAL_NESTING_COUNT() > 0U );
*
*            if( portGET_CRITICAL_NESTING_COUNT() > 0U )
*            {
*                portDECREMENT_CRITICAL_NESTING_COUNT();
*
*                if( portGET_CRITICAL_NESTING_COUNT() == 0U )
* ...
* @endcode
*
* Cover the case where the critical nesting count is equal to 1 and
* the scheduler is enabled.
*/
void test_coverage_vTaskExitCriticalFromISR_scheduler_enabled( void )
{
    UBaseType_t uxIntStatus;
    TaskHandle_t xTaskHandles[configNUMBER_OF_CORES] = { NULL };
    UBaseType_t xidx;

    xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 1, &xTaskHandles[0]);
    vTaskCoreAffinitySet(xTaskHandles[0], (UBaseType_t)0x1);

    vTaskStartScheduler();

    for (xidx = 0; xidx < configNUMBER_OF_CORES ; xidx++) {
        xTaskIncrementTick_helper();
    }

    uxIntStatus = taskENTER_CRITICAL_FROM_ISR();
    taskEXIT_CRITICAL_FROM_ISR(uxIntStatus);
}

/**
 * @brief vTaskExitCriticalFromISR - have a task exit a critical section from the ISR context
 *
 * <b>Coverage</b>
 * @code{c}
*       if( xSchedulerRunning != pdFALSE )
*        {
*        ...
*            configASSERT( portGET_CRITICAL_NESTING_COUNT() > 0U );
*
*            if( portGET_CRITICAL_NESTING_COUNT() > 0U )
*            {
*                portDECREMENT_CRITICAL_NESTING_COUNT();
*
*                if( portGET_CRITICAL_NESTING_COUNT() == 0U )
* ...
* @endcode
*
* Cover the case where the critical nesting count is equal to 1 and
* the scheduler is disabled.
*/
void test_coverage_vTaskExitCriticalFromISR_scheduler_disabled( void )
{
    UBaseType_t uxIntStatus;
    TaskHandle_t xTaskHandles[configNUMBER_OF_CORES] = { NULL };

    xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 1, &xTaskHandles[0]);
    vTaskCoreAffinitySet(xTaskHandles[0], (UBaseType_t)0x1);

    uxIntStatus = taskENTER_CRITICAL_FROM_ISR();
    taskEXIT_CRITICAL_FROM_ISR(uxIntStatus);
}

/**
 * @brief vTaskExitCriticalFromISR - have a task exit a critical section from the ISR context
 *
 * <b>Coverage</b>
 * @code{c}
*       if( xSchedulerRunning != pdFALSE )
*        {
*        ...
*            configASSERT( portGET_CRITICAL_NESTING_COUNT() > 0U );
*
*            if( portGET_CRITICAL_NESTING_COUNT() > 0U )
*            {
*                portDECREMENT_CRITICAL_NESTING_COUNT();
*
*                if( portGET_CRITICAL_NESTING_COUNT() == 0U )
* ...
* @endcode
*
* Cover the case where the critical nesting count is equal to 1 and
* the scheduler is enabled and the core yielded.
*/
void test_coverage_vTaskExitCriticalFromISR_scheduler_enabled_core_yield( void )
{
    UBaseType_t uxIntStatus;
    TaskHandle_t xTaskHandles[configNUMBER_OF_CORES] = { NULL };
    UBaseType_t xidx;

    xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 1, &xTaskHandles[0]);
    vTaskCoreAffinitySet(xTaskHandles[0], (UBaseType_t)0x1);

    vTaskStartScheduler();

    for (xidx = 0; xidx < configNUMBER_OF_CORES ; xidx++) {
        xTaskIncrementTick_helper();
    }

    uxIntStatus = taskENTER_CRITICAL_FROM_ISR();
    vTaskCoreAffinitySet(NULL, (UBaseType_t)0x0);
    taskEXIT_CRITICAL_FROM_ISR(uxIntStatus);
}