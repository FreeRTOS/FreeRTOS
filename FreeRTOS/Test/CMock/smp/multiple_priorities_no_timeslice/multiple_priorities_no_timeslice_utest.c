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
/*! @file multiple_priorities_no_timeslice_utest.c */

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

/* ===========================  EXTERN VARIABLES  =========================== */

extern volatile UBaseType_t uxDeletedTasksWaitingCleanUp;

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

/* ============================  FreeRTOS static allocate function  ============================ */

void vApplicationGetIdleTaskMemory( StaticTask_t ** ppxIdleTaskTCBBuffer,
                                    StackType_t ** ppxIdleTaskStackBuffer,
                                    uint32_t * pulIdleTaskStackSize )
{
    static StaticTask_t xIdleTaskTCB;
    static StackType_t uxIdleTaskStack[ configMINIMAL_STACK_SIZE ];

    *ppxIdleTaskTCBBuffer = &( xIdleTaskTCB );
    *ppxIdleTaskStackBuffer = &( uxIdleTaskStack[ 0 ] );
    *pulIdleTaskStackSize = configMINIMAL_STACK_SIZE;
}

void vApplicationGetPassiveIdleTaskMemory( StaticTask_t ** ppxIdleTaskTCBBuffer,
                                           StackType_t ** ppxIdleTaskStackBuffer,
                                           uint32_t * pulIdleTaskStackSize,
                                           BaseType_t xPassiveIdleTaskIndex )
{
    static StaticTask_t xIdleTaskTCBs[ configNUMBER_OF_CORES - 1 ];
    static StackType_t uxIdleTaskStacks[ configNUMBER_OF_CORES - 1 ][ configMINIMAL_STACK_SIZE ];

    *ppxIdleTaskTCBBuffer = &( xIdleTaskTCBs[ xPassiveIdleTaskIndex ] );
    *ppxIdleTaskStackBuffer = &( uxIdleTaskStacks[ xPassiveIdleTaskIndex ][ 0 ] );
    *pulIdleTaskStackSize = configMINIMAL_STACK_SIZE;
}

/* ==============================  Test Cases  ============================== */

/**
 * @brief AWS_IoT-FreeRTOS_SMP_TC-33
 * The purpose of this test is to verify when multiple CPU cores are available and
 * the FreeRTOS kernel is configured as (configRUN_MULTIPLE_PRIORITIES = 1) that tasks
 * of equal priority will execute simultaneously. The kernel will be configured as follows:
 *
 * #define configRUN_MULTIPLE_PRIORITIES                    1
 * #define configUSE_TIME_SLICING                           0
 * #define configUSE_CORE_AFFINITY                          1
 * #define configUSE_TASK_PREEMPTION_DISABLE                1
 * #define configNUMBER_OF_CORES                            (N > 1)
 *
 * This test can be run with FreeRTOS configured for any number of cores greater than 1 .
 *
 * Tasks are created prior to starting the scheduler.
 *
 * Task (T1)	    Task (TN)
 * Priority – 1     Priority –1
 * State - Ready	State - Ready
 *
 * After calling vTaskStartScheduler()
 *
 * Task (T1)	               Task (TN)
 * Priority – 1                Priority – 1
 * State - Running (Core 0)	   State - Running (Core N)
 */
void test_priority_verification_tasks_equal_priority( void )
{
    TaskHandle_t xTaskHandles[ configNUMBER_OF_CORES ] = { NULL };
    uint32_t i;

    /* Create configNUMBER_OF_CORES tasks of equal priority */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 1, &xTaskHandles[ i ] );
    }

    vTaskStartScheduler();

    /* Verify all configNUMBER_OF_CORES tasks are in the running state */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        verifySmpTask( &xTaskHandles[ i ], eRunning, i );
    }
}

/**
 * @brief AWS_IoT-FreeRTOS_SMP_TC-34
 * The purpose of this test is to verify when multiple CPU cores are available and
 * the FreeRTOS kernel is configured as (configRUN_MULTIPLE_PRIORITIES = 1) that
 * tasks of different priorities will execute simultaneously. The kernel will be
 * configured as follows:
 *
 * #define configRUN_MULTIPLE_PRIORITIES                    1
 * #define configUSE_TIME_SLICING                           0
 * #define configUSE_CORE_AFFINITY                          1
 * #define configUSE_TASK_PREEMPTION_DISABLE                1
 * #define configNUMBER_OF_CORES                            (N > 1)
 *
 * This test can be run with FreeRTOS configured for any number of cores greater
 * than 1.
 *
 * One high priority task will be created. N low priority tasks will be created
 * per remaining CPU cores.
 *
 * Task (T1)	     Task (TN)
 * Priority – 2      Priority – 1
 * State - Ready	 State - Ready
 *
 * After calling vTaskStartScheduler()
 *
 * Task (T1)	               Task (TN)
 * Priority – 2                Priority – 1
 * State - Running (Core 0)	   State - Running (Core N)
 */
void test_priority_verification_tasks_different_priorities( void )
{
    TaskHandle_t xTaskHandles[ configNUMBER_OF_CORES ] = { NULL };
    uint32_t i;

    /* Create a single task at high priority */
    xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 2, &xTaskHandles[ 0 ] );

    /* Create all remaining tasks at low priority */
    for( i = 1; i < configNUMBER_OF_CORES; i++ )
    {
        xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 1, &xTaskHandles[ i ] );
    }

    vTaskStartScheduler();

    /* Verify tasks are in the running state */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        verifySmpTask( &xTaskHandles[ i ], eRunning, i );
    }
}

/**
 * @brief AWS_IoT-FreeRTOS_SMP_TC-35
 * A task of equal priority will be created for each available CPU core.
 * This test will verify that when the priority of one task is lowered the
 * task remains running.
 *
 * #define configRUN_MULTIPLE_PRIORITIES                    1
 * #define configUSE_TIME_SLICING                           0
 * #define configUSE_CORE_AFFINITY                          1
 * #define configUSE_TASK_PREEMPTION_DISABLE                1
 * #define configNUMBER_OF_CORES                            (N > 1)
 *
 * This test can be run with FreeRTOS configured for any number of cores
 * greater than 1 .
 *
 * Tasks are created prior to starting the scheduler.
 *
 * Task (T1)	    Task (TN)
 * Priority – 2     Priority – 2
 * State - Ready    State - Ready
 *
 * After calling vTaskStartScheduler()
 *
 * Task (T1)	             Task (TN)
 * Priority – 2              Priority – 2
 * State - Running (Core 0)	 State - Running (Core N)
 *
 * After calling vTaskPrioritySet() and lowering the priority of task T1
 *
 * Task (T1)	             Task (TN)
 * Priority – 1              Priority – 2
 * State - Running (Core 0)  State - Running (Core N)
 */
void test_priority_change_tasks_equal_priority_lower( void )
{
    TaskHandle_t xTaskHandles[ configNUMBER_OF_CORES ] = { NULL };
    uint32_t i;
    TaskStatus_t xTaskDetails;

    /* Create tasks of equal priority for all available CPU cores */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 2, &xTaskHandles[ i ] );
    }

    vTaskStartScheduler();

    /* Verify all tasks are in the running state */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        verifySmpTask( &xTaskHandles[ i ], eRunning, i );
    }

    /* Lower the priority of task T0 */
    vTaskPrioritySet( xTaskHandles[ 0 ], 1 );

    /* Verify the priority has been changed */
    vTaskGetInfo( xTaskHandles[ 0 ], &xTaskDetails, pdTRUE, eInvalid );
    TEST_ASSERT_EQUAL( 1, xTaskDetails.xHandle->uxPriority );

    /* Verify all tasks remain in the running state on the same CPU cores */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        verifySmpTask( &xTaskHandles[ i ], eRunning, i );
    }
}

/**
 * @brief AWS_IoT-FreeRTOS_SMP_TC-36
 * A task of equal priority will be created for each available CPU core.
 * This test will verify that when the priority of one task is raised all
 * tasks remain running.
 *
 * #define configRUN_MULTIPLE_PRIORITIES                    1
 * #define configUSE_TIME_SLICING                           0
 * #define configUSE_CORE_AFFINITY                          1
 * #define configUSE_TASK_PREEMPTION_DISABLE                1
 * #define configNUMBER_OF_CORES                            (N > 1)
 *
 * This test can be run with FreeRTOS configured for any number of cores
 * greater than 1.
 *
 * Tasks are created prior to starting the scheduler.
 *
 * Task (T1)	    Task (TN)
 * Priority – 1     Priority – 1
 * State - Ready    State - Ready
 *
 * After calling vTaskStartScheduler()
 *
 * Task (T1)	             Task (TN)
 * Priority – 1              Priority – 1
 * State - Running (Core 0)	 State - Running (Core N)
 *
 * After calling vTaskPrioritySet() and raising the priority of task T1
 *
 * Task (T1)	             Task (T2)
 * Priority – 2              Priority – 1
 * State - Running (Core 0)  State - Running (Core N)
 */
void test_priority_change_tasks_equal_priority_raise( void )
{
    TaskHandle_t xTaskHandles[ configNUMBER_OF_CORES ] = { NULL };
    uint32_t i;
    TaskStatus_t xTaskDetails;

    /* Create tasks of equal priority for all available CPU cores */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 1, &xTaskHandles[ i ] );
    }

    vTaskStartScheduler();

    /* Verify all tasks are in the running state */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        verifySmpTask( &xTaskHandles[ i ], eRunning, i );
    }

    /* Raise the priority of task T0 */
    vTaskPrioritySet( xTaskHandles[ 0 ], 2 );

    /* Verify the priority has been changed */
    vTaskGetInfo( xTaskHandles[ 0 ], &xTaskDetails, pdTRUE, eInvalid );
    TEST_ASSERT_EQUAL( 2, xTaskDetails.xHandle->uxPriority );

    /* Verify T0 is the the running state */
    verifySmpTask( &xTaskHandles[ 0 ], eRunning, 0 );

    /* Verify all tasks are in the running state */
    for( i = 1; i < configNUMBER_OF_CORES; i++ )
    {
        verifySmpTask( &xTaskHandles[ i ], eRunning, i );
    }
}

/**
 * @brief AWS_IoT-FreeRTOS_SMP_TC-37
 * A task of high priority will be created for each available CPU core. An
 * additional task will be created in the ready state at low priority.
 * This test will verify that when the priority of the ready task is raised
 * to match the running tasks it will remain in the ready state. All other
 * tasks will remain in the running state.
 *
 * #define configRUN_MULTIPLE_PRIORITIES                    1
 * #define configUSE_TIME_SLICING                           0
 * #define configUSE_CORE_AFFINITY                          1
 * #define configUSE_TASK_PREEMPTION_DISABLE                1
 * #define configNUMBER_OF_CORES                            (N > 1)
 *
 * This test can be run with FreeRTOS configured for any number of cores
 * greater than 1.
 *
 * Tasks are created prior to starting the scheduler.
 *
 * Task (TN)	    Task (TN + 1)
 * Priority – 2     Priority – 1
 * State - Ready    State - Ready
 *
 * After calling vTaskStartScheduler()
 *
 * Task (TN)	             Task (TN + 1)
 * Priority – 2              Priority – 1
 * State - Running (Core N)	 State - Ready
 *
 * After calling vTaskPrioritySet() and raising the priority of task TN + 1
 *
 * Task (TN)	             Task (TN + 1)
 * Priority – 2              Priority – 2
 * State - Running (Core N)  State - Ready
 */
void test_priority_change_tasks_different_priority_raise_to_equal( void )
{
    TaskHandle_t xTaskHandles[ configNUMBER_OF_CORES + 1 ] = { NULL };
    uint32_t i;
    TaskStatus_t xTaskDetails;

    /* Create tasks at high priority */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 2, &xTaskHandles[ i ] );
    }

    /* Create a single task at low priority */
    xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 1, &xTaskHandles[ i ] );

    vTaskStartScheduler();

    /* Verify each task is in the running state */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        verifySmpTask( &xTaskHandles[ i ], eRunning, i );
    }

    /* Verify the low priority task is in the ready state */
    verifySmpTask( &xTaskHandles[ i ], eReady, -1 );

    /* Raise the priority of the ready task */
    vTaskPrioritySet( xTaskHandles[ i ], 2 );

    /* Verify the priority has been changed */
    vTaskGetInfo( xTaskHandles[ i ], &xTaskDetails, pdTRUE, eInvalid );
    TEST_ASSERT_EQUAL( 2, xTaskDetails.xHandle->uxPriority );

    /* Verify the task remains in the ready state */
    verifySmpTask( &xTaskHandles[ i ], eReady, -1 );

    /* Verify each task is in the running state */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        verifySmpTask( &xTaskHandles[ i ], eRunning, i );
    }
}

/**
 * @brief AWS_IoT-FreeRTOS_SMP_TC-38
 * A task of high priority will be created for each available CPU core. An
 * additional task will be created in the ready state at low priority.
 * This test will verify that when the priority of the ready task is raised
 * to greater than the running tasks it will enter the running state. All
 * other tasks will remain in the running state except for one. This task will
 * now be in the ready state.
 *
 * #define configRUN_MULTIPLE_PRIORITIES                    1
 * #define configUSE_TIME_SLICING                           0
 * #define configUSE_CORE_AFFINITY                          1
 * #define configUSE_TASK_PREEMPTION_DISABLE                1
 * #define configNUMBER_OF_CORES                            (N > 1)
 *
 * This test can be run with FreeRTOS configured for any number of cores
 * greater than 1.
 *
 * Tasks are created prior to starting the scheduler.
 *
 * Task (TN)	    Task (TN + 1)
 * Priority – 2     Priority – 1
 * State - Ready    State - Ready
 *
 * After calling vTaskStartScheduler()
 *
 * Task (TN)	             Task (TN + 1)
 * Priority – 2              Priority – 1
 * State - Running (Core N)	 State - Ready
 *
 * After calling vTaskPrioritySet() and raising the priority of task TN + 1
 *
 * Task (TN)	             Task (TN + 1)
 * Priority – 2              Priority – 3
 * State - Running (Core N)  State - Running (Core N)
 */
void test_priority_change_tasks_different_priority_raise_to_higher( void )
{
    TaskHandle_t xTaskHandles[ configNUMBER_OF_CORES + 1 ] = { NULL };
    uint32_t i;
    TaskStatus_t xTaskDetails;

    /* Create tasks at high priority */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 2, &xTaskHandles[ i ] );
    }

    /* Create a single task at low priority */
    xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 1, &xTaskHandles[ i ] );

    vTaskStartScheduler();

    /* Verify each task is in the running state */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        verifySmpTask( &xTaskHandles[ i ], eRunning, i );
    }

    /* Verify the low priority task is in the ready state */
    verifySmpTask( &xTaskHandles[ i ], eReady, -1 );

    /* Raise the priority of the ready task */
    vTaskPrioritySet( xTaskHandles[ i ], 3 );

    /* Verify the priority has been changed */
    vTaskGetInfo( xTaskHandles[ i ], &xTaskDetails, pdTRUE, eInvalid );
    TEST_ASSERT_EQUAL( 3, xTaskDetails.xHandle->uxPriority );

    /* Verify the task remains in the state */
    verifySmpTask( &xTaskHandles[ i ], eRunning, ( configNUMBER_OF_CORES - 1 ) );

    /* Verify each task is in the running running state */
    for( i = 0; i < configNUMBER_OF_CORES - 1; i++ )
    {
        verifySmpTask( &xTaskHandles[ i ], eRunning, i );
    }

    verifySmpTask( &xTaskHandles[ i ], eReady, -1 );
}

/**
 * @brief AWS_IoT-FreeRTOS_SMP_TC-39
 * A task of high priority will be created for each available CPU core. An
 * additional task will be created in the ready state at low priority.
 * This test will verify that when the priority of a running task is lowered
 * to the priority of the existing ready task it will enter the ready state.
 * The previously ready task will now be running.
 *
 * #define configRUN_MULTIPLE_PRIORITIES                    1
 * #define configUSE_TIME_SLICING                           0
 * #define configUSE_CORE_AFFINITY                          1
 * #define configUSE_TASK_PREEMPTION_DISABLE                1
 * #define configNUMBER_OF_CORES                            (N > 1)
 *
 * This test can be run with FreeRTOS configured for any number of cores
 * greater than 1.
 *
 * Tasks are created prior to starting the scheduler.
 *
 * Task (TN)	    Task (TN + 1)
 * Priority – 2     Priority – 1
 * State - Ready    State - Ready
 *
 * After calling vTaskStartScheduler()
 *
 * Task (TN)	             Task (TN + 1)
 * Priority – 2              Priority – 1
 * State - Running (Core N)	 State - Ready
 *
 * After calling vTaskPrioritySet() and lowering the priority of task T0
 *
 * Task (T0)      Task (TN)	                Task (TN + 1)
 * Priority – 1   Priority – 2              Priority – 1
 * State - Ready  State - Running (Core N)  State - Running (Core 0)
 */
void test_priority_change_tasks_different_priority_lower_to_equal( void )
{
    TaskHandle_t xTaskHandles[ configNUMBER_OF_CORES + 1 ] = { NULL };
    uint32_t i;
    TaskStatus_t xTaskDetails;

    /* Create tasks at high priority */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 2, &xTaskHandles[ i ] );
    }

    /* Create a single task at low priority */
    xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 1, &xTaskHandles[ i ] );

    vTaskStartScheduler();

    /* Verify each task is in the running state */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        verifySmpTask( &xTaskHandles[ i ], eRunning, i );
    }

    /* Verify the low priority task is in the ready state */
    verifySmpTask( &xTaskHandles[ i ], eReady, -1 );

    /* Lower the priority of a running task */
    vTaskPrioritySet( xTaskHandles[ 0 ], 1 );

    /* Verify the priority has been changed */
    vTaskGetInfo( xTaskHandles[ 0 ], &xTaskDetails, pdTRUE, eInvalid );
    TEST_ASSERT_EQUAL( 1, xTaskDetails.xHandle->uxPriority );

    /* Verify the task is now in the ready state */
    verifySmpTask( &xTaskHandles[ 0 ], eReady, -1 );

    /* Verify each other task is in the running state */
    for( i = 1; i < configNUMBER_OF_CORES; i++ )
    {
        verifySmpTask( &xTaskHandles[ i ], eRunning, i );
    }

    verifySmpTask( &xTaskHandles[ i ], eRunning, 0 );
}

/**
 * @brief AWS_IoT-FreeRTOS_SMP_TC-40
 * A task of high priority will be created for each available CPU core. An
 * additional task will be created in the ready state at low priority.
 * This test will verify that when the priority of a running task is set to
 * the lowest priority it will enter the ready state.
 * The previously ready task will now be running.
 *
 * #define configRUN_MULTIPLE_PRIORITIES                    1
 * #define configUSE_TIME_SLICING                           0
 * #define configUSE_CORE_AFFINITY                          1
 * #define configUSE_TASK_PREEMPTION_DISABLE                1
 * #define configNUMBER_OF_CORES                            (N > 1)
 *
 * This test can be run with FreeRTOS configured for any number of cores
 * greater than 1.
 *
 * Tasks are created prior to starting the scheduler.
 *
 * Task (TN)	    Task (TN + 1)
 * Priority – 3     Priority – 2
 * State - Ready    State - Ready
 *
 * After calling vTaskStartScheduler()
 *
 * Task (TN)	             Task (TN + 1)
 * Priority – 3              Priority – 2
 * State - Running (Core N)	 State - Ready
 *
 * After calling vTaskPrioritySet() and lowering the priority of task T0
 *
 * Task (T0)      Task (TN)	                Task (TN + 1)
 * Priority – 1   Priority – 3              Priority – 2
 * State - Ready  State - Running (Core N)  State - Running (Core 0)
 */
void test_priority_change_tasks_different_priority_lower_to_lowest( void )
{
    TaskHandle_t xTaskHandles[ configNUMBER_OF_CORES + 1 ] = { NULL };
    uint32_t i;
    TaskStatus_t xTaskDetails;

    /* Create tasks at high priority */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 3, &xTaskHandles[ i ] );
    }

    /* Create a single task at low priority */
    xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 2, &xTaskHandles[ i ] );

    vTaskStartScheduler();

    /* Verify each task is in the running state */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        verifySmpTask( &xTaskHandles[ i ], eRunning, i );
    }

    /* Verify the low priority task is in the ready state */
    verifySmpTask( &xTaskHandles[ i ], eReady, -1 );

    /* Lower the priority of a running task */
    vTaskPrioritySet( xTaskHandles[ 0 ], 1 );

    /* Verify the priority has been changed */
    vTaskGetInfo( xTaskHandles[ 0 ], &xTaskDetails, pdTRUE, eInvalid );
    TEST_ASSERT_EQUAL( 1, xTaskDetails.xHandle->uxPriority );

    /* Verify the is now in the ready state */
    verifySmpTask( &xTaskHandles[ 0 ], eReady, -1 );

    /* Verify each other task is in the running state */
    for( i = 1; i < configNUMBER_OF_CORES; i++ )
    {
        verifySmpTask( &xTaskHandles[ i ], eRunning, i );
    }

    verifySmpTask( &xTaskHandles[ i ], eRunning, 0 );
}

/**
 * @brief AWS_IoT-FreeRTOS_SMP_TC-110
 * A task of equal priority will be created for each available CPU core. An
 * additional task will be created in the ready state at equal priority.
 * This test will verify that when the priority of running task is raised all
 * the other running tasks remain running.
 *
 * #define configRUN_MULTIPLE_PRIORITIES                    1
 * #define configUSE_TIME_SLICING                           0
 * #define configNUMBER_OF_CORES                            (N > 1)
 *
 * This test can be run with FreeRTOS configured for any number of cores
 * greater than 1.
 *
 * Tasks are created prior to starting the scheduler.
 *
 * Task (T1)	    Task (TN)       Task (TN+1)
 * Priority – 1     Priority – 1    Priority – 1
 * State - Ready    State - Ready   State - Ready
 *
 * After calling vTaskStartScheduler()
 *
 * Task (T1)	        Task (TN)           Task (TN+1)
 * Priority – 1         Priority – 1        Priority – 1
 * State - Running      State - Running     State - Ready
 *
 * After calling vTaskPrioritySet() and raising the priority of task T1
 *
 * Task (T1)	        Task (TN)           Task (TN+1)
 * Priority – 2         Priority – 1        Priority – 1
 * State - Running      State - Running     State - Ready
 */
void test_priority_change_tasks_equal_priority_raise_additional_task( void )
{
    TaskHandle_t xTaskHandles[ configNUMBER_OF_CORES + 1 ] = { NULL };
    uint32_t i;
    TaskStatus_t xTaskDetails;

    /* Create tasks at equal priority. */
    for( i = 0; i < ( configNUMBER_OF_CORES + 1 ); i++ )
    {
        xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 2, &xTaskHandles[ i ] );
    }

    vTaskStartScheduler();

    /* Verify each task is in the running state. */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        verifySmpTask( &xTaskHandles[ i ], eRunning, i );
    }

    /* Verify the last task is in the ready state. */
    verifySmpTask( &xTaskHandles[ i ], eReady, -1 );

    /* Raise the priority of a running task. */
    vTaskPrioritySet( xTaskHandles[ 0 ], 2 );

    /* Verify the priority has been changed. */
    vTaskGetInfo( xTaskHandles[ 0 ], &xTaskDetails, pdTRUE, eInvalid );
    TEST_ASSERT_EQUAL( 2, xTaskDetails.xHandle->uxPriority );

    /* Verify each task is in the running state. */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        verifySmpTask( &xTaskHandles[ i ], eRunning, i );
    }

    /* Verify the last task is in the ready state */
    verifySmpTask( &xTaskHandles[ i ], eReady, -1 );
}

/**
 * @brief AWS_IoT-FreeRTOS_SMP_TC-41
 * A single task of high priority will be created. A low priority task will be
 * created for each remaining available CPU core. The test will first verify
 * that as each low priority task is deleted the high priority task remains in
 * the running state.
 *
 * #define configRUN_MULTIPLE_PRIORITIES                    1
 * #define configUSE_TIME_SLICING                           0
 * #define configUSE_CORE_AFFINITY                          1
 * #define configUSE_TASK_PREEMPTION_DISABLE                1
 * #define configNUMBER_OF_CORES                            (N > 1)
 *
 * This test can be run with FreeRTOS configured for any number of cores
 * greater than 1.
 *
 * Tasks are created prior to starting the scheduler.
 *
 * Task (T1)	  Task (TN)
 * Priority – 2   Priority – 1
 * State - Ready  State - Ready
 *
 * After calling vTaskStartScheduler()
 *
 * Task (T1)	             Task (TN)
 * Priority – 2              Priority – 1
 * State - Running (Core 0)	 State - Running (Core N)
 *
 * Delete each low priority task
 *
 * Task (T1)	              Task (TN)
 * Priority – 2               Priority – 1
 * State - Running (Core 0)	  State - Deleted
 */
void test_task_delete_tasks_different_priorities_delete_low( void )
{
    TaskHandle_t xTaskHandles[ configNUMBER_OF_CORES ] = { NULL };
    uint32_t i;

    /* Create a single task at high priority */
    xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 2, &xTaskHandles[ 0 ] );

    /* Create all remaining tasks at low priority */
    for( i = 1; i < configNUMBER_OF_CORES; i++ )
    {
        xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 1, &xTaskHandles[ i ] );
    }

    vTaskStartScheduler();

    /* Verify all tasks are running */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        verifySmpTask( &xTaskHandles[ i ], eRunning, i );
    }

    /* Verify no tasks are pending deletion */
    TEST_ASSERT_EQUAL( 0, uxDeletedTasksWaitingCleanUp );

    for( i = 1; i < configNUMBER_OF_CORES; i++ )
    {
        /* Delete low priority task */
        vTaskDelete( xTaskHandles[ i ] );

        /* Verify T0 remains running on core 0 */
        verifySmpTask( &xTaskHandles[ 0 ], eRunning, 0 );

        /* Verify task T[i] is in the deleted state */
        verifySmpTask( &xTaskHandles[ i ], eDeleted, -1 );
    }

    /* Verify tasks are pending deletion */
    TEST_ASSERT_EQUAL( ( configNUMBER_OF_CORES - 1 ), uxDeletedTasksWaitingCleanUp );
}

/**
 * @brief AWS_IoT-FreeRTOS_SMP_TC-42
 * A single task of high priority will be created. A low priority task will be
 * created for each remaining available CPU core. The test will delete the high
 * priority task and verify each other core remains in the running state.
 *
 * #define configRUN_MULTIPLE_PRIORITIES                    1
 * #define configUSE_TIME_SLICING                           0
 * #define configUSE_CORE_AFFINITY                          1
 * #define configUSE_TASK_PREEMPTION_DISABLE                1
 * #define configNUMBER_OF_CORES                            (N > 1)
 *
 * This test can be run with FreeRTOS configured for any number of cores
 * greater than 1.
 *
 * Tasks are created prior to starting the scheduler.
 *
 * Task (T1)	  Task (TN)
 * Priority – 2   Priority – 1
 * State - Ready  State - Ready
 *
 * After calling vTaskStartScheduler()
 *
 * Task (T1)	             Task (TN)
 * Priority – 2              Priority – 1
 * State - Running (Core 0)	 State - Running (Core N)
 *
 * Delete the high priority task
 *
 * Task (T1)	      Task (TN)
 * Priority – 2       Priority – 1
 * State - Deleted	  State - Running (Core N)
 */
void test_task_delete_tasks_different_priorities_delete_high( void )
{
    TaskHandle_t xTaskHandles[ configNUMBER_OF_CORES ] = { NULL };
    uint32_t i;

    /* Create a single task at high priority */
    xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 2, &xTaskHandles[ 0 ] );

    /* Create all remaining tasks at low priority */
    for( i = 1; i < configNUMBER_OF_CORES; i++ )
    {
        xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 1, &xTaskHandles[ i ] );
    }

    vTaskStartScheduler();

    /* Verify all tasks are in the running state */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        verifySmpTask( &xTaskHandles[ i ], eRunning, i );
    }

    /* Verify no tasks are pending deletion */
    TEST_ASSERT_EQUAL( 0, uxDeletedTasksWaitingCleanUp );

    /* Delete task T0 */
    vTaskDelete( xTaskHandles[ 0 ] );

    /* Verify the task has been deleted */
    TEST_ASSERT_EQUAL( 1, uxDeletedTasksWaitingCleanUp );
    verifySmpTask( &xTaskHandles[ 0 ], eDeleted, -1 );

    /* Verify core 0 is now running an idle task */
    verifyIdleTask( 0, 0 );

    /* Verify other cores remain in the running state */
    for( i = 1; i < ( configNUMBER_OF_CORES ); i++ )
    {
        verifySmpTask( &xTaskHandles[ i ], eRunning, i );
    }
}

/**
 * @brief AWS_IoT-FreeRTOS_SMP_TC-43
 * A task of high priority will be created for each available CPU core. Two
 * additional tasks will be created, a low priority task and a high priority task.
 * This test will verify that when a running high priority task is deleted, the
 * high priority task in the ready state will move to the running state.
 *
 * #define configRUN_MULTIPLE_PRIORITIES                    1
 * #define configUSE_TIME_SLICING                           0
 * #define configUSE_CORE_AFFINITY                          1
 * #define configUSE_TASK_PREEMPTION_DISABLE                1
 * #define configNUMBER_OF_CORES                            (N > 1)
 *
 * This test can be run with FreeRTOS configured for any number of cores
 * greater than 1.
 *
 * Tasks are created prior to starting the scheduler.
 *
 * Task (TN)	  Task (TN + 1)  Task (TN + 2)
 * Priority – 2   Priority – 1   Priority – 2
 * State - Ready  State - Ready  State - Ready
 *
 * After calling vTaskStartScheduler()
 *
 * Task (TN)	             Task (TN + 1)  Task (TN + 2)
 * Priority – 2              Priority – 1   Priority – 2
 * State - Running (Core N)	 State - Ready  State - Ready
 *
 * Delete the high priority task
 *
 * Task (T0)	      Task (TN)                 Task (TN + 1)   Task (TN + 2)
 * Priority – 2       Priority – 2              Priority – 1    Priority – 2
 * State - Deleted	  State - Running (Core N)  State - Ready   State - Running (Core 0)
 */
void test_task_delete_select_high_priority_task( void )
{
    TaskHandle_t xTaskHandles[ configNUMBER_OF_CORES + 2 ] = { NULL };
    uint32_t i;

    /* Create tasks at high priority for each CPU core */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 2, &xTaskHandles[ i ] );
    }

    /* Create a single task at low priority */
    xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 1, &xTaskHandles[ i ] );

    /* Create a single task at high priority */
    xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 2, &xTaskHandles[ i + 1 ] );

    vTaskStartScheduler();

    /* Verify all tasks are in the running state */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        verifySmpTask( &xTaskHandles[ i ], eRunning, i );
    }

    /* Verify remaining tasks are in the ready states */
    verifySmpTask( &xTaskHandles[ i ], eReady, -1 );
    verifySmpTask( &xTaskHandles[ i + 1 ], eReady, -1 );

    /* Verify no tasks are pending deletion */
    TEST_ASSERT_EQUAL( 0, uxDeletedTasksWaitingCleanUp );

    /* Delete task T0 */
    vTaskDelete( xTaskHandles[ 0 ] );

    /* Verify the task has been deleted */
    TEST_ASSERT_EQUAL( 1, uxDeletedTasksWaitingCleanUp );
    verifySmpTask( &xTaskHandles[ 0 ], eDeleted, -1 );

    /* Verify other cores remain in the running state */
    for( i = 1; i < ( configNUMBER_OF_CORES ); i++ )
    {
        verifySmpTask( &xTaskHandles[ i ], eRunning, i );
    }

    /* High priority task is now running on core 0 */
    verifySmpTask( &xTaskHandles[ i + 1 ], eRunning, 0 );
}

/**
 * @brief AWS_IoT-FreeRTOS_SMP_TC-45
 * Tasks of equal priority will be created for N - 1 CPU cores. The remaining
 * CPU core will be idle. Once the scheduler is started a new task of equal
 * priority shall be created. The test shall verify the new task is in the
 * running state.
 *
 * #define configRUN_MULTIPLE_PRIORITIES                    1
 * #define configUSE_TIME_SLICING                           0
 * #define configUSE_CORE_AFFINITY                          1
 * #define configUSE_TASK_PREEMPTION_DISABLE                1
 * #define configNUMBER_OF_CORES                            (N > 1)
 *
 * This test can be run with FreeRTOS configured for any number of cores
 * greater than 1.
 *
 * Tasks are created prior to starting the scheduler.
 *
 * Task N-1
 * Priority – 1
 * State - Ready
 *
 * After calling vTaskStartScheduler()
 *
 * Task N-1
 * Priority – 1
 * State - Running (Core N)
 *
 * Create a new task with priority 1
 *
 * Task N - 1	             New Task
 * Priority – 1              Priority – 1
 * State - Running (Core N)	 State - Running (Last available core)
 *
 */
void test_task_create_tasks_equal_priority( void )
{
    TaskHandle_t xTaskHandles[ configNUMBER_OF_CORES ] = { NULL };
    uint32_t i;

    /* Create tasks at equal priority */
    for( i = 0; i < ( configNUMBER_OF_CORES - 1 ); i++ )
    {
        xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 1, &xTaskHandles[ i ] );
    }

    vTaskStartScheduler();

    /* Verify all tasks are in the running state */
    for( i = 0; i < configNUMBER_OF_CORES - 1; i++ )
    {
        verifySmpTask( &xTaskHandles[ i ], eRunning, i );
    }

    /* Verify remaining CPU core is running the idle task */
    verifyIdleTask( 0, i );

    /* Create a new task of equal priority */
    xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 1, &xTaskHandles[ i ] );

    /* Verify the new task is in the running state */
    verifySmpTask( &xTaskHandles[ i ], eRunning, i );
}

/**
 * @brief AWS_IoT-FreeRTOS_SMP_TC-46
 * Tasks of equal priority will be created for N - 1 CPU cores. The remaining
 * task will be idle. Once the scheduler is started a new task of lower
 * priority shall be created. The test shall verify the new task is in the
 * running state.
 *
 * #define configRUN_MULTIPLE_PRIORITIES                    1
 * #define configUSE_TIME_SLICING                           0
 * #define configUSE_CORE_AFFINITY                          1
 * #define configUSE_TASK_PREEMPTION_DISABLE                1
 * #define configNUMBER_OF_CORES                            (N > 1)
 *
 * This test can be run with FreeRTOS configured for any number of cores
 * greater than 1.
 *
 * Tasks are created prior to starting the scheduler.
 *
 * Task N-1
 * Priority – 2
 * State - Ready
 *
 * After calling vTaskStartScheduler()
 *
 * Task N-1
 * Priority – 2
 * State - Running (Core N)
 *
 * Create a new task with priority 2
 *
 * Task N - 1	             New Task
 * Priority – 2              Priority – 1
 * State - Running (Core N)	 State - Running
 *
 */
void test_task_create_tasks_lower_priority( void )
{
    TaskHandle_t xTaskHandles[ configNUMBER_OF_CORES ] = { NULL };
    uint32_t i;

    /* Create all tasks at equal priority */
    for( i = 0; i < ( configNUMBER_OF_CORES - 1 ); i++ )
    {
        xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 2, &xTaskHandles[ i ] );
    }

    vTaskStartScheduler();

    /* Verify all tasks are in the running state */
    for( i = 0; i < ( configNUMBER_OF_CORES - 1 ); i++ )
    {
        verifySmpTask( &xTaskHandles[ i ], eRunning, i );
    }

    /* Verify remaining CPU core is running the idle task */
    verifyIdleTask( 0, i );

    /* Create a new task of lower priority */
    xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 1, &xTaskHandles[ i ] );

    /* Verify the new task is in the running state */
    verifySmpTask( &xTaskHandles[ i ], eRunning, i );
}

/**
 * @brief AWS_IoT-FreeRTOS_SMP_TC-47
 * Tasks of equal priority will be created for N - 1 CPU cores. The remaining
 * task will be idle. Once the scheduler is started a new task of higher
 * priority shall be created. The test shall verify the new task is in the
 * running state.
 *
 * #define configRUN_MULTIPLE_PRIORITIES                    1
 * #define configUSE_TIME_SLICING                           0
 * #define configUSE_CORE_AFFINITY                          1
 * #define configUSE_TASK_PREEMPTION_DISABLE                1
 * #define configNUMBER_OF_CORES                            (N > 1)
 *
 * This test can be run with FreeRTOS configured for any number of cores
 * greater than 1.
 *
 * Tasks are created prior to starting the scheduler.
 *
 * Task N-1
 * Priority – 1
 * State - Ready
 *
 * After calling vTaskStartScheduler()
 *
 * Task N-1
 * Priority – 1
 * State - Running (Core N)
 *
 * Create a new task with priority 2
 *
 * Task N-1                  New Task
 * Priority – 1              Priority – 2
 * State - Running (Core N)	 State - Running
 *
 */
void test_task_create_tasks_higher_priority( void )
{
    TaskHandle_t xTaskHandles[ configNUMBER_OF_CORES ] = { NULL };
    uint32_t i;

    /* Create all tasks at equal priority */
    for( i = 0; i < ( configNUMBER_OF_CORES - 1 ); i++ )
    {
        xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 1, &xTaskHandles[ i ] );
    }

    vTaskStartScheduler();

    /* Verify all tasks are in the running state */
    for( i = 0; i < ( configNUMBER_OF_CORES - 1 ); i++ )
    {
        verifySmpTask( &xTaskHandles[ i ], eRunning, i );
    }

    /* Verify remaining CPU core is running the idle task */
    verifyIdleTask( 0, i );

    /* Create a new task of higher priority */
    xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 2, &xTaskHandles[ i ] );

    /* Verify all tasks are in the ready state */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        verifySmpTask( &xTaskHandles[ i ], eRunning, i );
    }
}

/**
 * @brief AWS_IoT-FreeRTOS_SMP_TC-48
 * A task of equal priority will be created for each available CPU core. This
 * test will verify that when a new task of equal priority is created it will
 * be in the ready state.
 *
 * #define configRUN_MULTIPLE_PRIORITIES                    1
 * #define configUSE_TIME_SLICING                           0
 * #define configUSE_CORE_AFFINITY                          1
 * #define configUSE_TASK_PREEMPTION_DISABLE                1
 * #define configNUMBER_OF_CORES                            (N > 1)
 *
 * This test can be run with FreeRTOS configured for any number of cores
 * greater than 1.
 *
 * Tasks are created prior to starting the scheduler.
 *
 * Task (TN)
 * Priority – 1
 * State - Ready
 *
 * After calling vTaskStartScheduler()
 *
 * Task (TN)
 * Priority – 1
 * State - Running (Core N)
 *
 * Create a new task of equal priority
 *
 * Task (TN)	              New Task
 * Priority – 1               Priority – 1
 * State - Running (Core N)	  State - Ready
 */
void test_task_create_all_cores_equal_priority_equal( void )
{
    TaskHandle_t xTaskHandles[ configNUMBER_OF_CORES + 1 ] = { NULL };
    uint32_t i;

    /* Create all tasks at equal priority */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 1, &xTaskHandles[ i ] );
    }

    vTaskStartScheduler();

    /* Verify all tasks are in the running state */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        verifySmpTask( &xTaskHandles[ i ], eRunning, i );
    }

    /* Create a new task of equal priority */
    xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 1, &xTaskHandles[ i ] );

    /* Verify the new task is in the ready state */
    verifySmpTask( &xTaskHandles[ i ], eReady, -1 );

    /* Verify all tasks remain in the running state */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        verifySmpTask( &xTaskHandles[ i ], eRunning, i );
    }
}

/**
 * @brief AWS_IoT-FreeRTOS_SMP_TC-49
 * A task of equal priority will be created for each available CPU core. This
 * test will verify that when a new task of lower priority is created it will
 * be in the ready state.
 *
 * #define configRUN_MULTIPLE_PRIORITIES                    1
 * #define configUSE_TIME_SLICING                           0
 * #define configUSE_CORE_AFFINITY                          1
 * #define configUSE_TASK_PREEMPTION_DISABLE                1
 * #define configNUMBER_OF_CORES                            (N > 1)
 *
 * This test can be run with FreeRTOS configured for any number of cores
 * greater than 1.
 *
 * Tasks are created prior to starting the scheduler.
 *
 * Task (TN)
 * Priority – 2
 * State - Ready
 *
 * After calling vTaskStartScheduler()
 *
 * Task (TN)
 * Priority – 2
 * State - Running (Core N)
 *
 * Create a new task of lower priority
 *
 * Task (TN)	              New Task
 * Priority – 2               Priority – 1
 * State - Running (Core N)	  State - Ready
 */
void test_task_create_all_cores_equal_priority_lower( void )
{
    TaskHandle_t xTaskHandles[ configNUMBER_OF_CORES + 1 ] = { NULL };
    uint32_t i;

    /* Create all tasks at equal priority */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 2, &xTaskHandles[ i ] );
    }

    vTaskStartScheduler();

    /* Verify all tasks are in the running state */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        verifySmpTask( &xTaskHandles[ i ], eRunning, i );
    }

    /* Create a new task of lower priority */
    xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 1, &xTaskHandles[ i ] );

    /* Verify the new task is in the ready state */
    verifySmpTask( &xTaskHandles[ i ], eReady, -1 );

    /* Verify all tasks remain in the running state */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        verifySmpTask( &xTaskHandles[ i ], eRunning, i );
    }
}

/**
 * @brief AWS_IoT-FreeRTOS_SMP_TC-50
 * A task of equal priority will be created for each available CPU core. This
 * test will verify that when a new task of higher priority is created it will
 * be in the running state and a previously running task will now be in the
 * ready state.
 *
 * #define configRUN_MULTIPLE_PRIORITIES                    1
 * #define configUSE_TIME_SLICING                           0
 * #define configUSE_CORE_AFFINITY                          1
 * #define configUSE_TASK_PREEMPTION_DISABLE                1
 * #define configNUMBER_OF_CORES                            (N > 1)
 *
 * This test can be run with FreeRTOS configured for any number of cores
 * greater than 1.
 *
 * Tasks are created prior to starting the scheduler.
 *
 * Task (TN)
 * Priority – 1
 * State - Ready
 *
 * After calling vTaskStartScheduler()
 *
 * Task (TN)
 * Priority – 1
 * State - Running (Core N)
 *
 * Create a new task of higher priority
 *
 * Task (TN)	              New Task
 * Priority – 1               Priority – 2
 * State - Running (Core N)	  State - Running
 */
void test_task_create_all_cores_equal_priority_higher( void )
{
    TaskHandle_t xTaskHandles[ configNUMBER_OF_CORES + 1 ] = { NULL };
    uint32_t i;

    /* Create all tasks at equal priority */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 1, &xTaskHandles[ i ] );
    }

    vTaskStartScheduler();

    /* Verify all tasks are in the running state */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        verifySmpTask( &xTaskHandles[ i ], eRunning, i );
    }

    /* Create a new task of higher priority */
    xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 2, &xTaskHandles[ i ] );

    /* Verify the new task is in the running state */
    verifySmpTask( &xTaskHandles[ i ], eRunning, ( configNUMBER_OF_CORES - 1 ) );

    /* Verify all tasks remain in the running state */
    for( i = 0; i < ( configNUMBER_OF_CORES - 1 ); i++ )
    {
        verifySmpTask( &xTaskHandles[ i ], eRunning, i );
    }

    /* Verify the last original task is in the ready state */
    verifySmpTask( &xTaskHandles[ i ], eReady, -1 );
}

/**
 * @brief AWS_IoT-FreeRTOS_SMP_TC-51
 * A single task of high priority will be created. A low priority task will be
 * created for each remaining available CPU core. The test will create a new
 * high priority task and verify the new task is in the running state. A low
 * priority task will also have been moved to the ready state.
 *
 * #define configRUN_MULTIPLE_PRIORITIES                    1
 * #define configUSE_TIME_SLICING                           0
 * #define configUSE_CORE_AFFINITY                          1
 * #define configUSE_TASK_PREEMPTION_DISABLE                1
 * #define configNUMBER_OF_CORES                            (N > 1)
 *
 * This test can be run with FreeRTOS configured for any number of cores
 * greater than 1.
 *
 * Tasks are created prior to starting the scheduler.
 *
 * Task (T1)       Task (TN)
 * Priority – 2    Priority – 1
 * State - Ready   State - Ready
 *
 * After calling vTaskStartScheduler()
 *
 * Task (T1)                  Task (TN)
 * Priority – 2               Priority – 1
 * State - Running (Core 0)   State - Running (Core N)
 *
 * Create a new high priority task
 *
 * Task (T1)                  Task (TN)                  New Task
 * Priority – 2               Priority – 1               Priority – 2
 * State - Running (Core 0)   State - Ready              State - Running (Last Core)
 */
void test_task_create_all_cores_different_priority_high( void )
{
    TaskHandle_t xTaskHandles[ configNUMBER_OF_CORES + 1 ] = { NULL };
    uint32_t i;

    /* Create single high priority task */
    xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 2, &xTaskHandles[ 0 ] );

    /* Create remaining tasks at low priority */
    for( i = 1; i < configNUMBER_OF_CORES; i++ )
    {
        xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 1, &xTaskHandles[ i ] );
    }

    vTaskStartScheduler();

    /* Verify all tasks are in the running state */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        verifySmpTask( &xTaskHandles[ i ], eRunning, i );
    }

    /* Create a new high priority task */
    xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 2, &xTaskHandles[ i ] );

    /* Verify the new task is in the running state */
    verifySmpTask( &xTaskHandles[ i ], eRunning, ( configNUMBER_OF_CORES - 1 ) );

    /* Verify all tasks remain in the running state */
    for( i = 0; i < ( configNUMBER_OF_CORES - 1 ); i++ )
    {
        verifySmpTask( &xTaskHandles[ i ], eRunning, i );
    }

    /* Verify the last original task is in the ready state */
    verifySmpTask( &xTaskHandles[ i ], eReady, -1 );
}

/**
 * @brief AWS_IoT-FreeRTOS_SMP_TC-52
 * A single task of high priority will be created. A low priority task will be
 * created for each remaining available CPU core. The test will create a new
 * low priority task and verify the new task is in the ready state.
 *
 * #define configRUN_MULTIPLE_PRIORITIES                    1
 * #define configUSE_TIME_SLICING                           0
 * #define configUSE_CORE_AFFINITY                          1
 * #define configUSE_TASK_PREEMPTION_DISABLE                1
 * #define configNUMBER_OF_CORES                            (N > 1)
 *
 * This test can be run with FreeRTOS configured for any number of cores
 * greater than 1.
 *
 * Tasks are created prior to starting the scheduler.
 *
 * Task (T1)       Task (TN)
 * Priority – 2    Priority – 1
 * State - Ready   State - Ready
 *
 * After calling vTaskStartScheduler()
 *
 * Task (T1)                  Task (TN)
 * Priority – 2               Priority – 1
 * State - Running (Core 0)   State - Running (Core N)
 *
 * Create a new low priority task
 *
 * Task (T1)                  Task (TN)                  New Task
 * Priority – 2               Priority – 1               Priority – 1
 * State - Running (Core 0)   State - Running (Core N)   State - Ready
 */
void test_task_create_all_cores_different_priority_low( void )
{
    TaskHandle_t xTaskHandles[ configNUMBER_OF_CORES + 1 ] = { NULL };
    uint32_t i;

    /* Create single high priority task */
    xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 2, &xTaskHandles[ 0 ] );

    /* Create remaining tasks at low priority */
    for( i = 1; i < configNUMBER_OF_CORES; i++ )
    {
        xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 1, &xTaskHandles[ i ] );
    }

    vTaskStartScheduler();

    /* Verify all tasks are in the running state */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        verifySmpTask( &xTaskHandles[ i ], eRunning, i );
    }

    /* Create a new low priority task */
    xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 1, &xTaskHandles[ i ] );

    /* Verify the new task is in the ready state */
    verifySmpTask( &xTaskHandles[ i ], eReady, -1 );

    /* Verify all tasks remain in the running state */
    for( i = 0; i < ( configNUMBER_OF_CORES ); i++ )
    {
        verifySmpTask( &xTaskHandles[ i ], eRunning, i );
    }
}

/**
 * @brief AWS_IoT-FreeRTOS_SMP_TC-53
 * A task of equal priority will be created for each available CPU core. This
 * test will verify that when a task is suspended the CPU core will execute
 * the idle task.
 *
 * #define configRUN_MULTIPLE_PRIORITIES                    1
 * #define configUSE_TIME_SLICING                           0
 * #define configUSE_CORE_AFFINITY                          1
 * #define configUSE_TASK_PREEMPTION_DISABLE                1
 * #define configNUMBER_OF_CORES                            (N > 1)
 *
 * This test can be run with FreeRTOS configured for any number of cores
 * greater than 1.
 *
 * Tasks are created prior to starting the scheduler.
 *
 * Task (TN)
 * Priority – 1
 * State - Ready
 *
 * After calling vTaskStartScheduler()
 *
 * Task (TN)
 * Priority – N
 * State - Running (Core N)
 *
 * Suspend task (T1)
 *
 * Task (T1)	        Task (TN)
 * Priority – 1         Priority – 1
 * State - Suspended	State - Running (Core N)
 *
 * Resume task (T1)
 *
 * Task (TN)
 * Priority – N
 * State - Running (Core N)
 */
void test_task_suspend_all_cores_equal_priority( void )
{
    TaskHandle_t xTaskHandles[ configNUMBER_OF_CORES ] = { NULL };
    uint32_t i;

    /* Create tasks of equal priority */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 1, &xTaskHandles[ i ] );
    }

    vTaskStartScheduler();

    /* Verify tasks are running */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        verifySmpTask( &xTaskHandles[ i ], eRunning, i );
    }

    /* Suspend task T0 */
    vTaskSuspend( xTaskHandles[ 0 ] );

    /* Verify the task has been suspended */
    verifySmpTask( &xTaskHandles[ 0 ], eSuspended, -1 );

    /* Verify all other tasks are running */
    for( i = 1; i < configNUMBER_OF_CORES; i++ )
    {
        verifySmpTask( &xTaskHandles[ i ], eRunning, i );
    }

    /* Verify the idle task is running on core 0 */
    verifyIdleTask( 0, 0 );

    /* Resume task T0 */
    vTaskResume( xTaskHandles[ 0 ] );

    /* Verify all tasks are running */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        verifySmpTask( &xTaskHandles[ i ], eRunning, i );
    }
}

/**
 * @brief AWS_IoT-FreeRTOS_SMP_TC-55
 * A task of high priority will be created for each available CPU core. Two
 * additional tasks will be created, a low priority task and a high priority task.
 * This test will verify that when a running high priority task is suspended, the
 * high priority task in the ready state will move to the running state.
 *
 * #define configRUN_MULTIPLE_PRIORITIES                    1
 * #define configUSE_TIME_SLICING                           0
 * #define configUSE_CORE_AFFINITY                          1
 * #define configUSE_TASK_PREEMPTION_DISABLE                1
 * #define configNUMBER_OF_CORES                            (N > 1)
 *
 * This test can be run with FreeRTOS configured for any number of cores
 * greater than 1.
 *
 * Tasks are created prior to starting the scheduler.
 *
 * Task (TN)	  Task (TN + 1)  Task (TN + 2)
 * Priority – 2   Priority – 1   Priority – 2
 * State - Ready  State - Ready  State - Ready
 *
 * After calling vTaskStartScheduler()
 *
 * Task (TN)	             Task (TN + 1)  Task (TN + 2)
 * Priority – 2              Priority – 1   Priority – 2
 * State - Running (Core N)	 State - Ready  State - Ready
 *
 * Suspend the high priority task
 *
 * Task (T0)	      Task (TN)                 Task (TN + 1)   Task (TN + 2)
 * Priority – 2       Priority – 2              Priority – 1    Priority – 2
 * State - Suspended  State - Running (Core N)  State - Ready   State - Running (Core 0)
 */
void test_task_suspend_select_high_priority_task( void )
{
    TaskHandle_t xTaskHandles[ configNUMBER_OF_CORES + 2 ] = { NULL };
    uint32_t i;

    /* Create tasks at high priority for each CPU core */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 2, &xTaskHandles[ i ] );
    }

    /* Create a single task at low priority */
    xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 1, &xTaskHandles[ i ] );

    /* Create a single task at high priority */
    xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 2, &xTaskHandles[ i + 1 ] );

    vTaskStartScheduler();

    /* Verify all tasks are in the running state */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        verifySmpTask( &xTaskHandles[ i ], eRunning, i );
    }

    /* Verify remaining tasks are in the ready states */
    verifySmpTask( &xTaskHandles[ i ], eReady, -1 );
    verifySmpTask( &xTaskHandles[ i + 1 ], eReady, -1 );

    /* Suspend task T0 */
    vTaskSuspend( xTaskHandles[ 0 ] );

    /* Verify the task has been suspended */
    verifySmpTask( &xTaskHandles[ 0 ], eSuspended, -1 );

    /* Verify other cores remain in the running state */
    for( i = 1; i < ( configNUMBER_OF_CORES ); i++ )
    {
        verifySmpTask( &xTaskHandles[ i ], eRunning, i );
    }

    /* High priority task is now running on core 0 */
    verifySmpTask( &xTaskHandles[ i + 1 ], eRunning, 0 );
}

/**
 * @brief AWS_IoT-FreeRTOS_SMP_TC-57
 * A single task of high priority will be created. A low priority task will be
 * created for each remaining available CPU core. The test will verify that
 * when the high priority task is suspended the low priority tasks will
 * remain in the running state.
 *
 * #define configRUN_MULTIPLE_PRIORITIES                    1
 * #define configUSE_TIME_SLICING                           0
 * #define configUSE_CORE_AFFINITY                          1
 * #define configUSE_TASK_PREEMPTION_DISABLE                1
 * #define configNUMBER_OF_CORES                            (N > 1)
 *
 * This test can be run with FreeRTOS configured for any number of cores
 * greater than 1.
 *
 * Tasks are created prior to starting the scheduler.
 *
 * Task (T1)	  Task (TN)
 * Priority – 2   Priority – 1
 * State - Ready  State - Ready
 *
 * After calling vTaskStartScheduler()
 *
 * Task (T1)	              Task (TN)
 * Priority – 2               Priority – 1
 * State - Running (Core 0)	  State - Running (Core N)
 *
 * Suspend task (T1)
 *
 * Task (T1)	       Task (TN)
 * Priority – 2        Priority – 1
 * State - Suspended   State - Running (Core N)
 *
 * Resume task (T1)
 *
 * Task (T1)	             Task (TN)
 * Priority – 2              Priority – 1
 * State - Running (Core 0)	 State - Running (Core N)
 */
void test_task_suspend_all_cores_different_priority_suspend_high( void )
{
    TaskHandle_t xTaskHandles[ configNUMBER_OF_CORES ] = { NULL };
    uint32_t i;

    /* Create a single task at high priority */
    xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 2, &xTaskHandles[ 0 ] );

    /* Create all remaining tasks at low priority */
    for( i = 1; i < configNUMBER_OF_CORES; i++ )
    {
        xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 1, &xTaskHandles[ i ] );
    }

    vTaskStartScheduler();

    /* Verify all tasks are running */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        verifySmpTask( &xTaskHandles[ i ], eRunning, i );
    }

    /* Suspend the high priority task */
    vTaskSuspend( xTaskHandles[ 0 ] );

    /* Verify the suspended task is not running. */
    verifySmpTask( &xTaskHandles[ 0 ], eSuspended, -1 );

    /* Verify all other tasks are in the running state */
    for( i = 1; i < configNUMBER_OF_CORES; i++ )
    {
        verifySmpTask( &xTaskHandles[ i ], eRunning, i );
    }

    /* Verify idle task is running on core 0 */
    verifyIdleTask( 0, 0 );

    vTaskResume( xTaskHandles[ 0 ] );

    /* Verify all tasks are running */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        verifySmpTask( &xTaskHandles[ 0 ], eRunning, 0 );
    }
}

/**
 * @brief AWS_IoT-FreeRTOS_SMP_TC-54
 * A single task of high priority will be created. A low priority task will be
 * created for each remaining available CPU core. This test will verify that
 * as each low priority task is suspended, the high priority task shall remain
 * in the running state.
 *
 * #define configRUN_MULTIPLE_PRIORITIES                    1
 * #define configUSE_TIME_SLICING                           0
 * #define configUSE_CORE_AFFINITY                          1
 * #define configUSE_TASK_PREEMPTION_DISABLE                1
 * #define configNUMBER_OF_CORES                            (N > 1)
 *
 * This test can be run with FreeRTOS configured for any number of cores
 * greater than 1.
 *
 * Tasks are created prior to starting the scheduler.
 *
 * Task (T1)	  Task (TN)
 * Priority – 2   Priority – 1
 * State - Ready  State - Ready
 *
 * After calling vTaskStartScheduler()
 *
 * Task (T1)	              Task (TN)
 * Priority – 2               Priority – 1
 * State - Running (Core 0)	  State - Running (Core N)
 *
 * Suspend tasks (TN)
 *
 * Task (T1)	             Task (TN)
 * Priority – 2              Priority – 1
 * State - Running (Core 0)  State - Suspended
 *
 * Resume tasks (TN)
 *
 * Task (T1)	             Task (TN)
 * Priority – 2              Priority – 1
 * State - Running (Core 0)	 State - Running (Core N)
 */
void test_task_suspend_all_cores_different_priority_suspend_low( void )
{
    TaskHandle_t xTaskHandles[ configNUMBER_OF_CORES ] = { NULL };
    uint32_t i;

    /* Create a single task at high priority */
    xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 2, &xTaskHandles[ 0 ] );

    /* Create all remaining tasks at low priority */
    for( i = 1; i < configNUMBER_OF_CORES; i++ )
    {
        xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 1, &xTaskHandles[ i ] );
    }

    vTaskStartScheduler();

    /* Verify all tasks are running */
    for( i = 1; i < configNUMBER_OF_CORES; i++ )
    {
        verifySmpTask( &xTaskHandles[ 0 ], eRunning, 0 );
    }

    for( i = 1; i < configNUMBER_OF_CORES; i++ )
    {
        /* Suspend low priority task */
        vTaskSuspend( xTaskHandles[ i ] );

        /* Verify T0 remains running on core 0 */
        verifySmpTask( &xTaskHandles[ 0 ], eRunning, 0 );

        /* Verify task T[i] is in the suspended state */
        verifySmpTask( &xTaskHandles[ i ], eSuspended, -1 );
    }

    for( i = 1; i < configNUMBER_OF_CORES; i++ )
    {
        /* Resume low priority task */
        vTaskResume( xTaskHandles[ i ] );

        /* Verify T0 remains running on core 0 */
        verifySmpTask( &xTaskHandles[ 0 ], eRunning, 0 );

        /* Verify task T[i] is in the running state */
        verifySmpTask( &xTaskHandles[ i ], eRunning, ( configNUMBER_OF_CORES - i ) );
    }
}

/**
 * @brief AWS_IoT-FreeRTOS_SMP_TC-59
 * A task of equal priority will be created for each available CPU core. This
 * test will verify that when a task is blocked the CPU core will execute
 * the idle task.
 *
 * #define configRUN_MULTIPLE_PRIORITIES                    1
 * #define configUSE_TIME_SLICING                           0
 * #define configUSE_CORE_AFFINITY                          1
 * #define configUSE_TASK_PREEMPTION_DISABLE                1
 * #define configNUMBER_OF_CORES                            (N > 1)
 *
 * This test can be run with FreeRTOS configured for any number of cores
 * greater than 1.
 *
 * Tasks are created prior to starting the scheduler.
 *
 * Task (TN)
 * Priority – 1
 * State - Ready
 *
 * After calling vTaskStartScheduler()
 *
 * Task (TN)
 * Priority – 1
 * State - Running (Core N)
 *
 * Block task (T1)
 *
 * Task (T1)	        Task (TN)
 * Priority – 1         Priority – 1
 * State - Blocked      State - Running (Core N)
 *
 * Unblock task (T1)
 *
 * Task (T1)	                   Task (TN)
 * Priority – 1                    Priority – 1
 * State - Running ( Core 0 )      State - Running (Core N)
 */
void test_task_blocked_all_cores_equal_priority( void )
{
    TaskHandle_t xTaskHandles[ configNUMBER_OF_CORES ] = { NULL };
    uint32_t i;

    /* Create tasks of equal priority */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 1, &xTaskHandles[ i ] );
    }

    vTaskStartScheduler();

    /* Verify tasks are running */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        verifySmpTask( &xTaskHandles[ i ], eRunning, i );
    }

    /* Block task T0 */
    vTaskDelay( 10 );

    /* Verify the task has been suspended */
    verifySmpTask( &xTaskHandles[ 0 ], eBlocked, -1 );

    /* Verify all other tasks are running */
    for( i = 1; i < configNUMBER_OF_CORES; i++ )
    {
        verifySmpTask( &xTaskHandles[ i ], eRunning, i );
    }

    /* Verify the idle task is running on core 0 */
    verifyIdleTask( 0, 0 );

    /* Unblock task T0 */
    xTaskAbortDelay( xTaskHandles[ 0 ] );

    /* Verify all tasks are running */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        verifySmpTask( &xTaskHandles[ i ], eRunning, i );
    }
}

/**
 * @brief AWS_IoT-FreeRTOS_SMP_TC-60
 * A single task of high priority will be created. A low priority task will be
 * created for each remaining available CPU core. The test will verify that
 * when the high priority task is blocked the low priority tasks will
 * remain in the running state.
 *
 * #define configRUN_MULTIPLE_PRIORITIES                    1
 * #define configUSE_TIME_SLICING                           0
 * #define configUSE_CORE_AFFINITY                          1
 * #define configUSE_TASK_PREEMPTION_DISABLE                1
 * #define configNUMBER_OF_CORES                            (N > 1)
 *
 * This test can be run with FreeRTOS configured for any number of cores
 * greater than 1.
 *
 * Tasks are created prior to starting the scheduler.
 *
 * Task (T1)	  Task (TN)
 * Priority – 2   Priority – 1
 * State - Ready  State - Ready
 *
 * After calling vTaskStartScheduler()
 *
 * Task (T1)	              Task (TN)
 * Priority – 2               Priority – 1
 * State - Running (Core 0)	  State - Running (Core N)
 *
 * Block task (T1)
 *
 * Task (T1)	       Task (TN)
 * Priority – 2        Priority – 1
 * State - Blocked     State - Running (Core N)
 *
 * Unblock task (T1)
 *
 * Task (T1)	             Task (TN)
 * Priority – 2              Priority – 1
 * State - Running (Core 0)	 State - Running (Core N)
 */
void test_task_blocked_all_cores_different_priority_block_high( void )
{
    TaskHandle_t xTaskHandles[ configNUMBER_OF_CORES ] = { NULL };
    uint32_t i;

    /* Create a single task at high priority */
    xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 2, &xTaskHandles[ 0 ] );

    /* Create all remaining tasks at low priority */
    for( i = 1; i < configNUMBER_OF_CORES; i++ )
    {
        xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 1, &xTaskHandles[ i ] );
    }

    vTaskStartScheduler();

    /* Verify all tasks are running */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        verifySmpTask( &xTaskHandles[ i ], eRunning, i );
    }

    /* Block the high priority task */
    vTaskDelay( 10 );

    /* Verify the blocked task is not running. */
    verifySmpTask( &xTaskHandles[ 0 ], eBlocked, -1 );

    /* Verify all other tasks are in the running state */
    for( i = 1; i < configNUMBER_OF_CORES; i++ )
    {
        verifySmpTask( &xTaskHandles[ i ], eRunning, i );
    }

    /* Verify idle task is running on core 0 */
    verifyIdleTask( 0, 0 );

    /* Unblock task T0 */
    xTaskAbortDelay( xTaskHandles[ 0 ] );

    /* Verify all tasks are running */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        verifySmpTask( &xTaskHandles[ 0 ], eRunning, 0 );
    }
}

/**
 * @brief AWS_IoT-FreeRTOS_SMP_TC-62
 * A single task of high priority will be created for each available CPU core.
 * An additional low priority task shall be created. This test will verify that
 * when a high priority task is blocked the low priority task will enter the
 * running state. When the blocked task is resumed, it will move to the running
 * state.
 *
 * #define configRUN_MULTIPLE_PRIORITIES                    1
 * #define configUSE_TIME_SLICING                           0
 * #define configUSE_CORE_AFFINITY                          1
 * #define configUSE_TASK_PREEMPTION_DISABLE                1
 * #define configNUMBER_OF_CORES                            (N > 1)
 *
 * This test can be run with FreeRTOS configured for any number of cores
 * greater than 1.
 *
 * Tasks are created prior to starting the scheduler.
 *
 * Task (TN)	  Task (TN + 1)
 * Priority – 2   Priority – 1
 * State - Ready  State - Ready
 *
 * After calling vTaskStartScheduler()
 *
 * Task (T1)	              Task (TN)                 Task (TN + 1)
 * Priority – 2               Priority – 2              Priority – 1
 * State - Running (Core 0)	  State - Running (Core N)	State - Ready
 *
 * Block tasks (T1)
 *
 * Task (T1)	       Task (TN)                 Task (TN + 1)
 * Priority – 2        Priority – 1              Priority – 1
 * State - Blocked     State - Running (Core N)  State - Running (Core 0)
 *
 * Unblocked tasks (T1)
 *
 * Task (T1)	             Task (TN)                 Task (TN + 1)
 * Priority – 2              Priority – 1              Priority – 1
 * State - Running (Core 0)	 State - Running (Core N)  State - Ready
 */
void test_task_block_all_cores_high_priority_block( void )
{
    TaskHandle_t xTaskHandles[ configNUMBER_OF_CORES + 1 ] = { NULL };
    uint32_t i;

    /* Create a task for each CPU core at high priority */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 2, &xTaskHandles[ i ] );
    }

    /* Create a single task at low priority */
    xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 1, &xTaskHandles[ i ] );

    vTaskStartScheduler();

    /* Verify all high priority tasks are running */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        verifySmpTask( &xTaskHandles[ i ], eRunning, i );
    }

    /* Verify the low priority task is ready */
    verifySmpTask( &xTaskHandles[ i ], eReady, -1 );

    /* Block the high priority task T0 */
    vTaskDelay( 10 );

    /* Verify the task is blocked */
    verifySmpTask( &xTaskHandles[ 0 ], eBlocked, -1 );

    /* Verify all high priority tasks remain running */
    for( i = 1; i < configNUMBER_OF_CORES; i++ )
    {
        verifySmpTask( &xTaskHandles[ i ], eRunning, i );
    }

    /* Verify the low priority task is in the running state */
    verifySmpTask( &xTaskHandles[ i ], eRunning, 0 );

    /* Resume the high priority task */
    xTaskAbortDelay( xTaskHandles[ 0 ] );

    /* Verify all high priority tasks are running */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        verifySmpTask( &xTaskHandles[ i ], eRunning, i );
    }

    /* Verify the low priority task is in the ready state */
    verifySmpTask( &xTaskHandles[ i ], eReady, -1 );
}

/**
 * @brief AWS_IoT-FreeRTOS_SMP_TC-63
 * A task of high priority will be created for each available CPU core. Two
 * additional tasks will be created, a low priority task and a high priority task.
 * This test will verify that when a running high priority task is blocked, the
 * high priority task in the ready state will move to the running state.
 *
 * #define configRUN_MULTIPLE_PRIORITIES                    1
 * #define configUSE_TIME_SLICING                           0
 * #define configUSE_CORE_AFFINITY                          1
 * #define configUSE_TASK_PREEMPTION_DISABLE                1
 * #define configNUMBER_OF_CORES                            (N > 1)
 *
 * This test can be run with FreeRTOS configured for any number of cores
 * greater than 1.
 *
 * Tasks are created prior to starting the scheduler.
 *
 * Task (TN)	  Task (TN + 1)  Task (TN + 2)
 * Priority – 2   Priority – 1   Priority – 2
 * State - Ready  State - Ready  State - Ready
 *
 * After calling vTaskStartScheduler()
 *
 * Task (TN)	             Task (TN + 1)  Task (TN + 2)
 * Priority – 2              Priority – 1   Priority – 2
 * State - Running (Core N)	 State - Ready  State - Ready
 *
 * Blocked the high priority task
 *
 * Task (T0)	      Task (TN)                 Task (TN + 1)   Task (TN + 2)
 * Priority – 2       Priority – 2              Priority – 1    Priority – 2
 * State - Blocked    State - Running (Core N)  State - Ready   State - Running (Core 0)
 */
void test_task_blocked_select_high_priority_task( void )
{
    TaskHandle_t xTaskHandles[ configNUMBER_OF_CORES + 2 ] = { NULL };
    uint32_t i;

    /* Create tasks at high priority for each CPU core */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 2, &xTaskHandles[ i ] );
    }

    /* Create a single task at low priority */
    xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 1, &xTaskHandles[ i ] );

    /* Create a single task at high priority */
    xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 2, &xTaskHandles[ i + 1 ] );

    vTaskStartScheduler();

    /* Verify all tasks are in the running state */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        verifySmpTask( &xTaskHandles[ i ], eRunning, i );
    }

    /* Verify remaining tasks are in the ready states */
    verifySmpTask( &xTaskHandles[ i ], eReady, -1 );
    verifySmpTask( &xTaskHandles[ i + 1 ], eReady, -1 );

    /* Verify no tasks are pending deletion */
    TEST_ASSERT_EQUAL( 0, uxDeletedTasksWaitingCleanUp );

    /* Block the task on core 0 */
    vTaskDelay( 10 );

    /* Verify the task has been blocked */
    verifySmpTask( &xTaskHandles[ 0 ], eBlocked, -1 );

    /* Verify other cores remain in the running state */
    for( i = 1; i < ( configNUMBER_OF_CORES ); i++ )
    {
        verifySmpTask( &xTaskHandles[ i ], eRunning, i );
    }

    /* High priority task is now running on core 0 */
    verifySmpTask( &xTaskHandles[ i + 1 ], eRunning, 0 );
}

/**
 * @brief AWS_IoT-FreeRTOS_SMP_TC-64
 * A task of equal priority will be created for each available CPU core. The
 * vTaskCoreAffinitySet() API will be used to assign a specific core per task.
 * Once the scheduler has been started the test will verify each task is
 * running on the correctly designated core.
 *
 * #define configRUN_MULTIPLE_PRIORITIES                    1
 * #define configUSE_TIME_SLICING                           0
 * #define configUSE_CORE_AFFINITY                          1
 * #define configUSE_TASK_PREEMPTION_DISABLE                1
 * #define configNUMBER_OF_CORES                            (N > 1)
 *
 * This test can be run with FreeRTOS configured for any number of cores greater
 * than 1.
 *
 * Tasks are created prior to starting the scheduler.
 *
 * Task (T0)	              Task (TN)
 * Priority – 1               Priority – 1
 * Affinity – Last CPU Core   Affinity – (configNUMBER_OF_CORES - 1) - N)
 * State - Ready	          State - Ready
 *
 * After calling vTaskStartScheduler()
 *
 * Task (TN)
 * Priority – 1
 * State - Running ((configNUMBER_OF_CORES - 1) - N))
 */
void test_task_affinity_verification_separate_cores( void )
{
    TaskHandle_t xTaskHandles[ configNUMBER_OF_CORES ] = { NULL };
    uint32_t i;

    /* Create tasks for each CPU core */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 1, &xTaskHandles[ i ] );
    }

    /* Normally each task will run on CPU cores in assending order. Assign the lowest
     * tasks to the largest CPU core numbers */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        vTaskCoreAffinitySet( xTaskHandles[ i ], 1 << ( ( configNUMBER_OF_CORES - 1 ) - i ) );
    }

    vTaskStartScheduler();

    /* Verify all tasks are in the running state on the correct CPU Core */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        verifySmpTask( &xTaskHandles[ i ], eRunning, ( ( configNUMBER_OF_CORES - 1 ) - i ) );
    }
}

/**
 * @brief AWS_IoT-FreeRTOS_SMP_TC-65
 * A task of equal priority will be created for each available CPU core. The
 * vTaskCoreAffinitySet() API will be used to assign the last created task to
 * CPU core 0. The test will verify each task is in the running state except
 * for the last task. The last task will be in the ready state and the idle
 * task will be running on the last available CPU core.
 *
 * #define configRUN_MULTIPLE_PRIORITIES                    1
 * #define configUSE_TIME_SLICING                           0
 * #define configNUMBER_OF_CORES                            (N > 1)
 * #define configUSE_CORE_AFFINITY                          1
 * #define configUSE_TASK_PREEMPTION_DISABLE                1
 *
 * This test can be run with FreeRTOS configured for any number of cores greater
 * than 1.
 *
 * Tasks are created prior to starting the scheduler.
 *
 * Task (T0)	      Task (TN-1)      Task (Last)
 * Priority – 1       Priority – 1     Priority – 1
 * Affinity – None    Affinity – None  Affinity - Core 0
 * State - Ready	  State - Ready    State - Ready
 *
 * After calling vTaskStartScheduler()
 *
 * Task (T0)	             Task (TN-1)               Task (Last)
 * Priority – 1              Priority – 1              Priority – 1
 * Affinity – None           Affinity – None           Affinity - Core 0
 * State - Running (Core 0)	 State - Running (Core N)  State - Ready
 */
void test_task_affinity_verification_same_cores( void )
{
    TaskHandle_t xTaskHandles[ configNUMBER_OF_CORES ] = { NULL };
    uint32_t i;

    /* Create tasks for each CPU core */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 1, &xTaskHandles[ i ] );
    }

    /* Set core affinity for the last task to CPU 0 */
    vTaskCoreAffinitySet( xTaskHandles[ i - 1 ], 1 << 0 );

    vTaskStartScheduler();

    /* Verify all tasks are in the running state */
    for( i = 0; i < configNUMBER_OF_CORES - 1; i++ )
    {
        verifySmpTask( &xTaskHandles[ i ], eRunning, i );
    }

    /* Verify the last task is in the ready state */
    verifySmpTask( &xTaskHandles[ i ], eReady, -1 );

    /* Verify the idle task is running on the last CPU Core */
    verifyIdleTask( 0, ( configNUMBER_OF_CORES - 1 ) );
}

/**
 * @brief AWS_IoT-FreeRTOS_SMP_TC-66
 * A task of equal priority will be created for each available CPU core. The
 * vTaskCoreAffinitySet() API will be used to assign the last created task to
 * CPU core 0. The test will verify each task is in the running state except
 * for the last task. The task running on CPU core 0 will then be suspended.
 * The previously ready task will now be running on CPU core 0. When the
 * suspended task is resumed, it will run on the previously idle CPU core.
 *
 * #define configRUN_MULTIPLE_PRIORITIES                    1
 * #define configUSE_TIME_SLICING                           0
 * #define configUSE_CORE_AFFINITY                          1
 * #define configUSE_TASK_PREEMPTION_DISABLE                1
 * #define configNUMBER_OF_CORES                            (N > 1)
 *
 * This test can be run with FreeRTOS configured for any number of cores greater
 * than 1.
 *
 * Tasks are created prior to starting the scheduler.
 *
 * Task (TN)	       Task (Last)
 * Priority – 1        Priority – 1
 * Affinity – None     Affinity - Core 0
 * State - Ready	   State - Ready
 *
 * After calling vTaskStartScheduler()
 *
 * Task (T0)	             Task (TN-1)               Task (Last)
 * Priority – 1              Priority – 1              Priority – 1
 * Affinity – None           Affinity – None           Affinity - Core 0
 * State - Running (Core 0)	 State - Running (Core N)  State - Ready
 *
 * Suspend Task T0
 *
 * Task (T0)	         Task (TN-1)               Task (Last)
 * Priority – 1          Priority – 1              Priority – 1
 * Affinity – None       Affinity – None           Affinity - Core 0
 * State - Suspended     State - Running (Core N)  State - Running (Core 0)
 *
 * Resume Task T0
 *
 * Task (T0)	                Task (TN-1)               Task (Last)
 * Priority – 1                 Priority – 1              Priority – 1
 * Affinity – None              Affinity – None           Affinity - Core 0
 * State - Running (Last Core)  State - Running (Core N)  State - Running (Core 0)
 */
void test_task_affinity_suspend_same_core_affinity( void )
{
    TaskHandle_t xTaskHandles[ configNUMBER_OF_CORES ] = { NULL };
    uint32_t i;

    /* Create tasks for each CPU core */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 1, &xTaskHandles[ i ] );
    }

    /* Set the last task to have affinity for core 0 only */
    vTaskCoreAffinitySet( xTaskHandles[ i - 1 ], 1 << 0 );

    vTaskStartScheduler();

    /* Verify all but the last task are in the running state */
    for( i = 0; i < configNUMBER_OF_CORES - 1; i++ )
    {
        verifySmpTask( &xTaskHandles[ i ], eRunning, i );
    }

    /* Verify the last task is in the ready state and the last CPU
     * core is idle */
    verifySmpTask( &xTaskHandles[ i ], eReady, -1 );
    verifyIdleTask( 0, ( configNUMBER_OF_CORES - 1 ) );

    /* Suspend task T0 */
    vTaskSuspend( xTaskHandles[ 0 ] );

    /* Verify the previously ready task is now running on core 0 */
    verifySmpTask( &xTaskHandles[ i ], eRunning, 0 );

    /* Resume task T0 */
    vTaskResume( xTaskHandles[ 0 ] );

    /* Verify task T0 is now running on the previously
     * idle CPU core */
    verifySmpTask( &xTaskHandles[ 0 ], eRunning, ( configNUMBER_OF_CORES - 1 ) );
}

/**
 * @brief AWS_IoT-FreeRTOS_SMP_TC-67
 * A task of equal priority will be created for each available CPU core. The
 * vTaskCoreAffinitySet() API will be used to assign the last created task CPU
 * affinity for a core that does not exist. Once the scheduler has been started
 * the test will verify the task does not enter the running state.
 *
 * #define configRUN_MULTIPLE_PRIORITIES                    1
 * #define configUSE_TIME_SLICING                           0
 * #define configUSE_CORE_AFFINITY                          1
 * #define configUSE_TASK_PREEMPTION_DISABLE                1
 * #define configNUMBER_OF_CORES                            (N > 1)
 *
 * This test can be run with FreeRTOS configured for any number of cores greater
 * than 1.
 *
 * Tasks are created prior to starting the scheduler.
 *
 * Task (TN)	      Task (TN + 1)
 * Priority – 1       Priority – 1
 * Affinity – None    Affinity – Out of range
 * State - Ready	  State - Ready
 *
 * After calling vTaskStartScheduler()
 *
 * Task (TN)	              Task (TN + 1)
 * Priority – 1               Priority – 1
 * Affinity – None            Affinity – Out of range
 * State - Running (Core N)	  State - Ready
 *
 * Suspend task T0
 *
 * Task (T0)	         Task (TN)                 Task (TN + 1)
 * Priority – 1          Priority – 1              Priority – 1
 * Affinity – None       Affinity – None           Affinity - Out of range
 * State - Suspended     State - Running (Core N)  State - Ready
 */
void test_task_affinity_out_of_range( void )
{
    TaskHandle_t xTaskHandles[ configNUMBER_OF_CORES + 1 ] = { NULL };
    uint32_t i;

    /* Create tasks for each CPU core */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 1, &xTaskHandles[ i ] );
    }

    /* Create an additional task which will be in the ready state */
    xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 1, &xTaskHandles[ i ] );

    /* Set the affinity mask to a core that is out of range */
    vTaskCoreAffinitySet( xTaskHandles[ i ], 1 << configNUMBER_OF_CORES );

    vTaskStartScheduler();

    /* Verify all tasks are in the running state */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        verifySmpTask( &xTaskHandles[ i ], eRunning, i );
    }

    /* Verify last task is in the ready state */
    verifySmpTask( &xTaskHandles[ i ], eReady, -1 );

    /* Suspend task T0 */
    vTaskSuspend( xTaskHandles[ 0 ] );

    /* Verify last task remains in the ready state */
    verifySmpTask( &xTaskHandles[ i ], eReady, -1 );
}

/**
 * @brief AWS_IoT-FreeRTOS_SMP_TC-69
 * A single task of high priority will be created. A low priority task will be
 * created for each remaining available CPU core. An additional high priority
 * task shall be created in the suspended state and have affinity for CPU core
 * 0. This test shall verify that when the suspended task is resumed it remains
 * in the ready state.
 *
 * #define configRUN_MULTIPLE_PRIORITIES                    1
 * #define configUSE_TIME_SLICING                           0
 * #define configUSE_CORE_AFFINITY                          1
 * #define configUSE_TASK_PREEMPTION_DISABLE                1
 * #define configNUMBER_OF_CORES                            (N > 1)
 *
 * This test can be run with FreeRTOS configured for any number of cores greater
 * than 1.
 *
 * Tasks are created prior to starting the scheduler.
 *
 * Task (T0)	     Task (TN)         Task (TN + 1)
 * Priority – 2      Priority – 1      Priority – 2
 * Affinity – None   Affinity – None   Affinity - Core 0
 * State - Ready     State - Ready     State - Suspended
 *
 * After calling vTaskStartScheduler()
 *
 * Task (T0)	             Task (TN)                  Task (TN + 1)
 * Priority – 2              Priority – 1               Priority – 2
 * Affinity – None           Affinity – None            Affinity - Core 0
 * State - Running (Core 0)  State - Running (Core N)   State - Suspended
 *
 * Resume task T0
 *
 * Task (T0)	             Task (TN)                 Task (TN + 1)
 * Priority – 2              Priority – 1              Priority – 2
 * Affinity – None           Affinity – None           Affinity – Core 0
 * State - Running (Core 0)  State - Running (Core N)  State - Ready
 */
void test_task_affinity_resume_suspended_task( void )
{
    TaskHandle_t xTaskHandles[ configNUMBER_OF_CORES + 1 ] = { NULL };
    uint32_t i;

    /* Create a high priority task */
    xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 2, &xTaskHandles[ 0 ] );

    /* Create tasks for each remaining CPU core */
    for( i = 1; i < configNUMBER_OF_CORES; i++ )
    {
        xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 1, &xTaskHandles[ i ] );
    }

    /* Create an additional high priority task */
    xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 2, &xTaskHandles[ i ] );

    /* Suspend task the last task and set core affinity for CPU 0 */
    vTaskSuspend( xTaskHandles[ i ] );
    vTaskCoreAffinitySet( xTaskHandles[ i ], 1 << 0 );

    vTaskStartScheduler();

    /* Verify all tasks are in the running state */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        verifySmpTask( &xTaskHandles[ i ], eRunning, i );
    }

    /* The last task shall be in the suspended state */
    verifySmpTask( &xTaskHandles[ i ], eSuspended, -1 );

    /* Resume the last task */
    vTaskResume( xTaskHandles[ i ] );

    /* The last task shall be in the ready state */
    verifySmpTask( &xTaskHandles[ i ], eReady, -1 );
}

/**
 * @brief AWS_IoT-FreeRTOS_SMP_TC-70
 * A single task of high priority will be created. A low priority task will be
 * created for each remaining available CPU core. After the scheduler has been
 * started an additional high priority task shall be created with affinity for
 * CPU core 0. This task shall be in the ready state. This test shall verify that
 * when the affinity is changed the task will then enter the running state.
 *
 * #define configRUN_MULTIPLE_PRIORITIES                    1
 * #define configUSE_TIME_SLICING                           0
 * #define configUSE_CORE_AFFINITY                          1
 * #define configUSE_TASK_PREEMPTION_DISABLE                1
 * #define configNUMBER_OF_CORES                            (N > 1)
 *
 * This test can be run with FreeRTOS configured for any number of cores greater
 * than 1.
 *
 * Tasks are created prior to starting the scheduler.
 *
 * Task (T0)	     Task (TN)
 * Priority – 2      Priority – 1
 * Affinity – None   Affinity – None
 * State – Ready     State – Ready
 *
 * After calling vTaskStartScheduler()
 *
 * Task (T0)	             Task (TN)
 * Priority – 2              Priority – 1
 * Affinity – None           Affinity – None
 * State – Running (Core 0)  State – Running (Core N)
 *
 * Create a new high priority task with affinity for CPU core 0
 *
 * Task (T0)	             Task (TN)                 Task (TN + 1)
 * Priority – 2              Priority – 1              Priority – 2
 * Affinity – None           Affinity – None           Affinity – Core 0
 * State – Running (Core 0)  State – Running (Core N)  State – Ready
 *
 * Remove core affinity on the new task
 *
 * Task (T0)                 Task (TN - 1)             Task (TN)                 Task (TN + 1)
 * Priority – 2              Priority – 1              Priority – 1              Priority – 2
 * Affinity – None           Affinity – None           Affinity – None           Affinity – None
 * State – Running (Core 0)  State – Running           State – Ready             State – Running (Last Core)
 */
void test_task_affinity_modify_affinity( void )
{
    TaskHandle_t xTaskHandles[ configNUMBER_OF_CORES + 1 ] = { NULL };
    uint32_t i;

    /* Create a high priority task */
    xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 2, &xTaskHandles[ 0 ] );

    /* Create tasks for each remaining CPU core */
    for( i = 1; i < configNUMBER_OF_CORES; i++ )
    {
        xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 1, &xTaskHandles[ i ] );
    }

    vTaskStartScheduler();

    /* Verify all tasks are in the running state */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        verifySmpTask( &xTaskHandles[ i ], eRunning, i );
    }

    /* Create a new task with affinity for core 0 */
    xTaskCreateAffinitySet( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 2, ( 1 << 0 ), &xTaskHandles[ i ] );

    /* The last task shall be in the ready state */
    verifySmpTask( &xTaskHandles[ i ], eReady, -1 );

    /* Allow the task to run on any core */
    vTaskCoreAffinitySet( xTaskHandles[ i ], tskNO_AFFINITY );

    /* Verify the task is now in the running state */
    verifySmpTask( &xTaskHandles[ i ], eRunning, ( configNUMBER_OF_CORES - 1 ) );
}

/**
 * @brief AWS_IoT-FreeRTOS_SMP_TC-71
 * A single task of high priority will be created. A low priority task will be
 * created for each remaining available CPU core. After the scheduler has been
 * started a new high priority task will be created with affinity for CPU core 0.
 * This test shall verify the new task remains in the ready state until the
 * priority of the task running on core 0 is lowered.
 *
 * #define configRUN_MULTIPLE_PRIORITIES                    1
 * #define configUSE_TIME_SLICING                           0
 * #define configUSE_CORE_AFFINITY                          1
 * #define configUSE_TASK_PREEMPTION_DISABLE                1
 * #define configNUMBER_OF_CORES                            (N > 1)
 *
 * This test can be run with FreeRTOS configured for any number of cores greater
 * than 1.
 *
 * Tasks are created prior to starting the scheduler.
 *
 * Task (T0)	      Task (TN)
 * Priority – 2       Priority – 1
 * Affinity – None    Affinity – None
 * State - Ready	  State - Ready
 *
 * After calling vTaskStartScheduler()
 *
 * Task (T0)	              Task (TN)
 * Priority – 2               Priority – 1
 * Affinity – None            Affinity – None
 * State - Running (Core 0)	  State - Running (Core N)
 *
 * Create a new high priority task with affinity for core 0
 *
 * Task (T0)	             Task (TN)                 Task (TN + 1)
 * Priority – 2              Priority – 1              Priority – 2
 * Affinity – None           Affinity – None           Affinity – Core 0
 * State - Running (Core 0)  State - Running (Core N)  State - Ready
 *
 * Lower the priority of task T0
 *
 * Task (T0)	      Task (TN)                 Task (TN + 1)
 * Priority – 1       Priority – 1              Priority – 2
 * Affinity – None    Affinity – None           Affinity – Core 0
 * State - Ready      State - Running (Core N)  State - Running (Core 0)
 */
void test_task_affinity_modify_priority( void )
{
    TaskHandle_t xTaskHandles[ configNUMBER_OF_CORES + 1 ] = { NULL };
    uint32_t i;

    /* Create a high priority task */
    xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 2, &xTaskHandles[ 0 ] );

    /* Create tasks for each remaining CPU core */
    for( i = 1; i < configNUMBER_OF_CORES; i++ )
    {
        xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 1, &xTaskHandles[ i ] );
    }

    vTaskStartScheduler();

    /* Verify all tasks are in the running state */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        verifySmpTask( &xTaskHandles[ i ], eRunning, i );
    }

    /* Create a new task with affinity for core 0 only */
    xTaskCreateAffinitySet( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 2, ( 1 << 0 ), &xTaskHandles[ i ] );

    /* The last task shall be in the ready state */
    verifySmpTask( &xTaskHandles[ i ], eReady, -1 );

    /* Lower the priority of task T0 */
    vTaskPrioritySet( xTaskHandles[ 0 ], 1 );

    /* The new task will now be running on core 0 */
    verifySmpTask( &xTaskHandles[ i ], eRunning, 0 );
}

/**
 * @brief AWS_IoT-FreeRTOS_SMP_TC-68
 * A single task of low priority will be created. A medium priority task will be
 * created for each remaining available CPU core. A task of the highest priority
 * will be created and suspended. After the scheduler has been started the low
 * priority task will have preemption disabled. This test will verify that when the
 * highest priority task is resumed it will not preempt the lowest priority task.
 * Instead it will replace one of the medium priority tasks.
 *
 * #define configRUN_MULTIPLE_PRIORITIES                    1
 * #define configUSE_TIME_SLICING                           0
 * #define configUSE_CORE_AFFINITY                          1
 * #define configUSE_TASK_PREEMPTION_DISABLE                1
 * #define configNUMBER_OF_CORES                            (N > 1)
 *
 * This test can be run with FreeRTOS configured for any number of cores greater
 * than 1.
 *
 * Tasks are created prior to starting the scheduler.
 *
 * Task (T0)	      Task (TN)         Task (TN + 1)
 * Priority – 1       Priority – 2      Priority – 3
 * State – Ready	  State – Ready     State – Suspended
 *
 * After calling vTaskStartScheduler()
 *
 * Task (T0)	              Task (TN)         Task (TN + 1)
 * Priority – 1               Priority – 2      Priority – 3
 * State - Running (core N)   State - Running   State - Suspended
 *
 * Disable preemption on task T0
 *
 * Task (T0)	              Task (TN)         Task (TN + 1)
 * Priority – 1               Priority – 2      Priority – 3
 * Preemption Disabled
 * State - Running (core N)	  State - Running   State - Suspended
 *
 * Resume task TN + 1
 *
 * Task (T0)	              Task (TN)         Task (TN + 1)
 * Priority – 1               Priority – 2      Priority – 3
 * Preemption Disabled
 * State - Running (core N)	  State - Ready     State - Running
 */
void test_task_preemption_verification( void )
{
    TaskHandle_t xTaskHandles[ configNUMBER_OF_CORES + 1 ] = { NULL };
    uint32_t i;

    /* Create a single low priority task */
    xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 1, &xTaskHandles[ 0 ] );

    /* Create a high priority task task for each remaining CPU core */
    for( i = 1; i < configNUMBER_OF_CORES; i++ )
    {
        xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 2, &xTaskHandles[ i ] );
    }

    /* Create a higher priority task which will be suspended */
    xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 3, &xTaskHandles[ i ] );
    vTaskSuspend( xTaskHandles[ i ] );

    vTaskStartScheduler();

    /* Verify the low priority task is running on the last available CPU core */
    verifySmpTask( &xTaskHandles[ 0 ], eRunning, ( configNUMBER_OF_CORES - 1 ) );

    /* Verify all remaining tasks are in the running state */
    for( i = 1; i < configNUMBER_OF_CORES; i++ )
    {
        verifySmpTask( &xTaskHandles[ i ], eRunning, ( i - 1 ) );
    }

    /* Verify the highest priority task is suspended */
    verifySmpTask( &xTaskHandles[ i ], eSuspended, -1 );

    /* Disable preemption for task T0 */
    vTaskPreemptionDisable( xTaskHandles[ 0 ] );

    /* Resume the highest priority task. Normally T0 would begin running this
     * task since it is the lowest priority. Since preemption is disabled a
     * higher priority task is selected instead. */
    vTaskResume( xTaskHandles[ i ] );

    /* The highest priority task will run on the first available CPU core */
    verifySmpTask( &xTaskHandles[ i ], eRunning, ( configNUMBER_OF_CORES - 2 ) );

    /* The low priority task remains running on the last core */
    verifySmpTask( &xTaskHandles[ 0 ], eRunning, ( configNUMBER_OF_CORES - 1 ) );
}

/**
 * @brief AWS_IoT-FreeRTOS_SMP_TC-72
 * A single task of low priority will be created. A medium priority task will be
 * created for each remaining available CPU core. After the scheduler has been
 * started preemption will be disabled on the low priority task. This test will
 * verify that when a new task of the highest priority is created, it will
 * preempt a medium priority task rather than the low priority task.
 *
 * #define configRUN_MULTIPLE_PRIORITIES                    1
 * #define configUSE_TIME_SLICING                           0
 * #define configUSE_CORE_AFFINITY                          1
 * #define configUSE_TASK_PREEMPTION_DISABLE                1
 * #define configNUMBER_OF_CORES                            (N > 1)
 *
 * This test can be run with FreeRTOS configured for any number of cores greater
 * than 1.
 *
 * Tasks are created prior to starting the scheduler.
 *
 * Task (T0)	      Task (TN)
 * Priority – 1       Priority – 2
 * State – Ready	  State – Ready
 *
 * After calling vTaskStartScheduler()
 *
 * Task (T0)	             Task (TN)
 * Priority – 1              Priority – 2
 * State - Running (core N)	 State - Running
 *
 * Disable preemption on task T0
 *
 * Task (T0)	                Task (TN)
 * Priority – 1                 Priority – 2
 * Preemption Disabled
 * State - Running (core N)	    State - Running
 *
 * Create new task at priority 3
 *
 * Task (T0)	                Task (TN)         Task (TN + 1)
 * Priority – 1                 Priority – 2      Priority – 3
 * Preemption Disabled
 * State - Running (core N)	    State - Ready     State - Running
 */
void test_task_preemption_new_task( void )
{
    TaskHandle_t xTaskHandles[ configNUMBER_OF_CORES + 1 ] = { NULL };
    uint32_t i;

    /* Create a single low priority task */
    xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 1, &xTaskHandles[ 0 ] );

    /* Create tasks for each remaining CPU core */
    for( i = 1; i < configNUMBER_OF_CORES; i++ )
    {
        xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 2, &xTaskHandles[ i ] );
    }

    vTaskStartScheduler();

    /* Verify the low priority task is running on the last available CPU core */
    verifySmpTask( &xTaskHandles[ 0 ], eRunning, ( configNUMBER_OF_CORES - 1 ) );

    /* Verify all remaining tasks are in the running state */
    for( i = 1; i < configNUMBER_OF_CORES; i++ )
    {
        verifySmpTask( &xTaskHandles[ i ], eRunning, ( i - 1 ) );
    }

    /* Disable preemption for low priority task T0 */
    vTaskPreemptionDisable( xTaskHandles[ 0 ] );

    /* Create a high priority task */
    xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 3, &xTaskHandles[ i ] );

    /* The new task will now be a CPU core previously running a priority 2 task */
    verifySmpTask( &xTaskHandles[ i ], eRunning, ( configNUMBER_OF_CORES - 2 ) );

    /* The low priority task remains running on the last core */
    verifySmpTask( &xTaskHandles[ 0 ], eRunning, ( configNUMBER_OF_CORES - 1 ) );
}

/**
 * @brief AWS_IoT-FreeRTOS_SMP_TC-73
 * A single task of low priority will be created. A high priority task will be
 * created for each remaining available CPU core. An additional low priority task
 * shall be created. After the scheduler has been started the first low priority
 * task will have preemption disabled. This test will verify that when the
 * priority is raised on the low priority task in the ready state it will not
 * preempt the lowest priority task currently running. Instead it will replace
 * one of the high priority tasks.
 *
 * #define configRUN_MULTIPLE_PRIORITIES                    1
 * #define configUSE_TIME_SLICING                           0
 * #define configUSE_CORE_AFFINITY                          1
 * #define configUSE_TASK_PREEMPTION_DISABLE                1
 * #define configNUMBER_OF_CORES                            (N > 1)
 *
 * This test can be run with FreeRTOS configured for any number of cores greater
 * than 1.
 *
 * Tasks are created prior to starting the scheduler.
 *
 * Task (T0)	      Task (TN)         Task (TN + 1)
 * Priority – 1       Priority – 2      Priority – 1
 * State – Ready	  State – Ready     State – Ready
 *
 * After calling vTaskStartScheduler()
 *
 * Task (T0)	            Task (TN)         Task (TN + 1)
 * Priority – 1             Priority – 2      Priority – 1
 * State - Running (core N) State - Running   State - Ready
 *
 * Disable preemption on task T0
 *
 * Task (T0)	            Task (TN)         Task (TN + 1)
 * Priority – 1             Priority – 2      Priority – 3
 * Preemption Disabled
 * State - Running (core N) State - Running   State - Ready
 *
 * Raise the priority on task TN + 1
 *
 * Task (T0)	            Task (TN)         Task (TN + 1)
 * Priority – 1             Priority – 2      Priority – 3
 * Preemption Disabled
 * State - Running (core N) State - Ready     State - Running
 */
void test_task_preemption_change_priority( void )
{
    TaskHandle_t xTaskHandles[ configNUMBER_OF_CORES + 1 ] = { NULL };
    uint32_t i;

    /* Create a single low priority task */
    xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 1, &xTaskHandles[ 0 ] );

    /* Create tasks for each remaining CPU core */
    for( i = 1; i < configNUMBER_OF_CORES; i++ )
    {
        xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 2, &xTaskHandles[ i ] );
    }

    /* Create a low priority task */
    xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 1, &xTaskHandles[ i ] );

    vTaskStartScheduler();

    /* Verify the low priority task is running on the last available CPU core */
    verifySmpTask( &xTaskHandles[ 0 ], eRunning, ( configNUMBER_OF_CORES - 1 ) );

    /* Verify all tasks are in the running state */
    for( i = 1; i < configNUMBER_OF_CORES; i++ )
    {
        verifySmpTask( &xTaskHandles[ i ], eRunning, ( i - 1 ) );
    }

    /* Verify the low priority task is not running */
    verifySmpTask( &xTaskHandles[ i ], eReady, -1 );

    /* Disable preemption for low priority task T0 */
    vTaskPreemptionDisable( xTaskHandles[ 0 ] );

    /* Raise the priority on the idle low priority task */
    vTaskPrioritySet( xTaskHandles[ i ], 3 );

    /* The new task will now be a CPU core previously running a priority 2 task */
    verifySmpTask( &xTaskHandles[ i ], eRunning, ( configNUMBER_OF_CORES - 2 ) );

    /* The low priority task remains running on the last core */
    verifySmpTask( &xTaskHandles[ 0 ], eRunning, ( configNUMBER_OF_CORES - 1 ) );
}

/**
 * @brief AWS_IoT-FreeRTOS_SMP_TC-74
 * A single task of low priority will be created. A high priority task will be
 * created for each remaining available CPU core. After the scheduler has been
 * started preemption will be disabled on the low priority task. This test will
 * verify that when a new high priority task is created with affinity for the
 * same core utilized by the low priority task, it shall remain in the ready state.
 * When the new task is allowed to run on any CPU core it will preempt a high
 * priority task rather than the low priority task.
 *
 * #define configRUN_MULTIPLE_PRIORITIES                    1
 * #define configUSE_TIME_SLICING                           0
 * #define configUSE_CORE_AFFINITY                          1
 * #define configUSE_TASK_PREEMPTION_DISABLE                1
 * #define configNUMBER_OF_CORES                            (N > 1)
 *
 * This test can be run with FreeRTOS configured for any number of cores greater
 * than 1.
 *
 * Tasks are created prior to starting the scheduler.
 *
 * Task (T0)	      Task (TN)
 * Priority – 1       Priority – 2
 * State – Ready	  State – Ready
 *
 * After calling vTaskStartScheduler()
 *
 * Task (T0)	               Task (TN)
 * Priority – 1                Priority – 2
 * State - Running (core N)    State - Running
 *
 * Disable preemption on task T0
 *
 * Task (T0)	               Task (TN)
 * Priority – 1                Priority – 2
 * Preemption Disabled
 * State - Running (core N)    State - Running
 *
 * Create new task at priority 3 with affinity for the same CPU core as task T0
 *
 * Task (T0)	                Task (TN)         Task (TN + 1)
 * Priority – 1                 Priority – 2      Priority – 3
 * Preemption Disabled                            Affinity mask set
 * State - Running (core N)	    State - Running   State - Ready
 *
 * Clear the affinity mask for Task TN + 1
 *
 * Task (T0)	                Task (TN)         Task (TN + 1)
 * Priority – 1                 Priority – 2      Priority – 3
 * Preemption Disabled
 * State - Running (core N)	    State - Ready   State - Running
 */
void test_task_preemption_change_affinity( void )
{
    TaskHandle_t xTaskHandles[ configNUMBER_OF_CORES + 1 ] = { NULL };
    uint32_t i;

    /* Create a single low priority task */
    xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 1, &xTaskHandles[ 0 ] );

    /* Create tasks for each remaining CPU core */
    for( i = 1; i < configNUMBER_OF_CORES; i++ )
    {
        xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 2, &xTaskHandles[ i ] );
    }

    vTaskStartScheduler();

    /* Verify the low priority task is running on the last available CPU core */
    verifySmpTask( &xTaskHandles[ 0 ], eRunning, ( configNUMBER_OF_CORES - 1 ) );

    /* Verify all tasks are in the running state */
    for( i = 1; i < configNUMBER_OF_CORES; i++ )
    {
        verifySmpTask( &xTaskHandles[ i ], eRunning, ( i - 1 ) );
    }

    /* Disable preemption for low priority task T0 */
    vTaskPreemptionDisable( xTaskHandles[ 0 ] );

    /* Create a high priority task with affinity for CPU core 0 */
    xTaskCreateAffinitySet( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 3, ( 1 << ( configNUMBER_OF_CORES - 1 ) ), &xTaskHandles[ i ] );

    /* The new task will be in the ready state */
    verifySmpTask( &xTaskHandles[ i ], eReady, -1 );

    /* Allow the task to run on any core */
    vTaskCoreAffinitySet( xTaskHandles[ i ], tskNO_AFFINITY );

    /* The new task will now be a CPU core previously running a priority 2 task */
    verifySmpTask( &xTaskHandles[ i ], eRunning, ( configNUMBER_OF_CORES - 2 ) );

    /* The low priority task remains running on the last core */
    verifySmpTask( &xTaskHandles[ 0 ], eRunning, ( configNUMBER_OF_CORES - 1 ) );
}

/**
 * @brief AWS_IoT-FreeRTOS_SMP_TC-87
 * Tasks of equal priority waiting in the ready queue. The one waiting for the longest
 * time should be selected to run.
 *
 * #define configRUN_MULTIPLE_PRIORITIES                    1
 * #define configUSE_TIME_SLICING                           0
 * #define configUSE_CORE_AFFINITY                          1
 * #define configUSE_TASK_PREEMPTION_DISABLE                1
 * #define configNUMBER_OF_CORES                            (N > 1)
 *
 * This test can be run with FreeRTOS configured for any number of cores greater
 * than 1.
 *
 * Tasks are created prior to starting the scheduler.
 *
 * Task (T0)	      Task (TN)         Task (TN + 1)
 * Priority – 1       Priority – 1      Priority – 1
 * State – Ready	  State – Ready     State – Ready
 *
 * After calling vTaskStartScheduler()
 *
 * Task (T0)	      Task (TN - 1)     Task (TN)         Task (TN + 1)
 * Priority – 1       Priority – 1      Priority – 1      Priority – 1
 * State - Running	  State - Running   State - Ready     State - Ready
 *
 * Task T1 yields on core 1
 *
 * Task (T0)	        Task (T1)	        Task (TN)         Task (TN + 1)
 * Priority – 1         Priority – 1        Priority – 1      Priority – 1
 * State - Running	    State - Ready       State - Running   State - Ready
 *
 * Task T0 yields on core 0
 *
 * Task (T0)	        Task (T1)	        Task (TN)         Task (TN + 1)
 * Priority – 1         Priority – 1        Priority – 1      Priority – 1
 * State - Ready        State - Ready       State - Running   State - Running
 *
 * Task TN yields on core 1
 *
 * Task (T0)	        Task (T1)	        Task (TN)         Task (TN + 1)
 * Priority – 1         Priority – 1        Priority – 1      Priority – 1
 * State - Ready	    State - Running     State - Ready     State - Running
 */
void test_task_yield_run_wait_longest( void )
{
    TaskHandle_t xTaskHandles[ ( configNUMBER_OF_CORES + 2 ) ] = { NULL };
    uint32_t i;

    /* Create ( N + 2 ) tasks of priority 1. The ready list should have tasks
     * in the following orders:
     *      [ T0, T1, T2, ..., TN, TN + 1 ]
     */
    for( i = 0; i < ( configNUMBER_OF_CORES + 2 ); i++ )
    {
        xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 1, &xTaskHandles[ i ] );
    }

    /* Start the scheduler. The tasks running status:
     *      T0 : core 0
     *      T1 : core 1
     *      ...
     *      TN : in ready list
     *      TN + 1 : in ready list
     */
    vTaskStartScheduler();

    for( i = 0; i < ( configNUMBER_OF_CORES + 2 ); i++ )
    {
        if( i < configNUMBER_OF_CORES )
        {
            verifySmpTask( &xTaskHandles[ i ], eRunning, i );
        }
        else
        {
            verifySmpTask( &xTaskHandles[ i ], eReady, -1 );
        }
    }

    /* T1 yield itself on core 1. TN should be selected to run on core 1.
     * The tasks running status:
     *      T0 : core 0
     *      T1 : in ready list
     *      ...
     *      TN : core 1
     *      TN + 1 : in ready list
     */
    vSetCurrentCore( 1 );
    taskYIELD();

    for( i = 0; i < ( configNUMBER_OF_CORES + 2 ); i++ )
    {
        if( i == 1 )
        {
            verifySmpTask( &xTaskHandles[ i ], eReady, -1 );
        }
        else if( i == ( configNUMBER_OF_CORES + 1 ) )
        {
            verifySmpTask( &xTaskHandles[ i ], eReady, -1 );
        }
        else if( i == configNUMBER_OF_CORES )
        {
            verifySmpTask( &xTaskHandles[ i ], eRunning, 1 );
        }
        else
        {
            verifySmpTask( &xTaskHandles[ i ], eRunning, i );
        }
    }

    /* T0 yield itself on core 0. TN + 1 should be selected to run on core 0.
     * The tasks running status:
     *      T0 : in ready list
     *      T1 : in ready list
     *      ...
     *      TN : core 1
     *      TN + 1 : core 0
     */
    vSetCurrentCore( 0 );
    taskYIELD();

    for( i = 0; i < ( configNUMBER_OF_CORES + 2 ); i++ )
    {
        if( ( i == 0 ) || ( i == 1 ) )
        {
            verifySmpTask( &xTaskHandles[ i ], eReady, -1 );
        }
        else if( i == configNUMBER_OF_CORES )
        {
            verifySmpTask( &xTaskHandles[ i ], eRunning, 1 );
        }
        else if( i == ( configNUMBER_OF_CORES + 1 ) )
        {
            verifySmpTask( &xTaskHandles[ i ], eRunning, 0 );
        }
        else
        {
            verifySmpTask( &xTaskHandles[ i ], eRunning, i );
        }
    }

    /* TN yield itself on core 1. T1 should now runs on core 1 since it stop running first.
     * The tasks running status:
     *      T0 : in ready list
     *      T1 : core 1
     *      ...
     *      TN : in ready list
     *      TN + 1 : core 0
     */
    vSetCurrentCore( 1 );
    taskYIELD();

    for( i = 0; i < ( configNUMBER_OF_CORES + 2 ); i++ )
    {
        if( i == 0 )
        {
            verifySmpTask( &xTaskHandles[ i ], eReady, -1 );
        }
        else if( i == configNUMBER_OF_CORES )
        {
            verifySmpTask( &xTaskHandles[ i ], eReady, -1 );
        }
        else if( i == 1 )
        {
            verifySmpTask( &xTaskHandles[ i ], eRunning, 1 );
        }
        else if( i == ( configNUMBER_OF_CORES + 1 ) )
        {
            verifySmpTask( &xTaskHandles[ i ], eRunning, 0 );
        }
        else
        {
            verifySmpTask( &xTaskHandles[ i ], eRunning, i );
        }
    }
}

/**
 * @brief AWS_IoT-FreeRTOS_SMP_TC-88
 * Tasks of equal priority waiting in the ready queue. The new task of equal priority
 * should be selected to run when a running task yields itself.
 *
 * #define configRUN_MULTIPLE_PRIORITIES                    1
 * #define configUSE_TIME_SLICING                           0
 * #define configNUMBER_OF_CORES                            (N > 1)
 *
 * This test can be run with FreeRTOS configured for any number of cores greater
 * than 1.
 *
 * Tasks are created prior to starting the scheduler.
 *
 * Task (T1)	      Task (TN)
 * Priority – 1       Priority – 1
 * State – Ready	  State – Ready
 *
 * After calling vTaskStartScheduler()
 *
 * Task (T1)	      Task (TN)
 * Priority – 1       Priority – 1
 * State – Running	  State – Running
 *
 * Create Task TN + 1
 *
 * Task (T1)	        Task (TN)	        Task (TN + 1)
 * Priority – 1         Priority – 1        Priority – 1
 * State - Running	    State - Running     State - Ready
 *
 * Task T0 yields on core 0
 *
 * Task (T1)	        Task (TN)	        Task (TN + 1)
 * Priority – 1         Priority – 1        Priority – 1
 * State - Ready	    State - Running     State - Running
 */
void test_task_yield_run_equal_priority_new_task( void )
{
    TaskHandle_t xTaskHandles[ ( configNUMBER_OF_CORES + 1 ) ] = { NULL };
    uint32_t i;

    /* Create N tasks. */
    for( i = 0; i < ( configNUMBER_OF_CORES ); i++ )
    {
        xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 1, &xTaskHandles[ i ] );
    }

    vTaskStartScheduler();

    /* Create task TN+1. */
    xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 1, &xTaskHandles[ i ] );

    /* Task T1 yields itself on core 0. */
    taskYIELD();

    /* The new task TN+1 should runs on core 0. */
    verifySmpTask( &xTaskHandles[ i ], eRunning, 0 );
}

/**
 * @brief AWS_IoT-FreeRTOS_SMP_TC-106
 * Task can inherit or disinherit other higher priority task. This test verify that
 * lower priority task will be selected to run when it inherit a higher priority task.
 * The lower priority will be switched out when it disinherits higher priority task.
 *
 * #define configRUN_MULTIPLE_PRIORITIES                    1
 * #define configUSE_TIME_SLICING                           0
 * #define configNUMBER_OF_CORES                            (N > 1)
 *
 * This test can be run with FreeRTOS configured for any number of cores greater
 * than 1.
 *
 * Tasks are created prior to starting the scheduler
 *
 * Task (T1)	      Task (T2)         Task (TN)       Task (TN + 1)
 * Priority – 3       Priority – 2      Priority – 2    Priority – 1
 * State – Ready	  State – Ready     State – Ready   State – Ready
 *
 * After calling vTaskStartScheduler()
 *
 * Task (T1)	      Task (T2)         Task (TN)       Task (TN + 1)
 * Priority – 3       Priority – 2      Priority – 2    Priority – 1
 * State – Running    State – Running   State – Running State – Ready
 *
 * Assuming task TN+1 is holding a mutex. Task TN+1 inherits task T1's priority
 *
 * Task (T1)	      Task (T2)         Task (TN)       Task (TN + 1)
 * Priority – 3       Priority – 2      Priority – 2    Priority – 3
 * State – Running    State – Running   State – Ready   State – Running
 *                                                      uxMutexesHeld - 1
 *
 * Task TN+1 disinherits task T1's priority.
 *
 * Task (T1)	      Task (T2)         Task (TN)       Task (TN + 1)
 * Priority – 3       Priority – 2      Priority – 2    Priority – 1
 * State – Running    State – Running   State – Running State – Ready
 *                                                      uxMutexesHeld - 0
 */
void test_task_priority_inherit_disinherit( void )
{
    TaskHandle_t xTaskHandles[ configNUMBER_OF_CORES + 1 ] = { NULL };
    uint32_t i;
    TaskStatus_t xTaskDetails;

    /* Create 1 high priority task. */
    xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 3, &xTaskHandles[ 0 ] );

    /* Create N - 1 Medium priority task. */
    for( i = 1; i < configNUMBER_OF_CORES; i++ )
    {
        xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 2, &xTaskHandles[ i ] );
    }

    /* Create 1 low priority task. */
    xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 1, &xTaskHandles[ i ] );

    /* Start the scheduler. */
    vTaskStartScheduler();

    /* Verify the high and medium priority tasks running. */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        verifySmpTask( &xTaskHandles[ i ], eRunning, i );
    }

    /* Verify the low priority task is ready. */
    verifySmpTask( &xTaskHandles[ configNUMBER_OF_CORES ], eReady, -1 );

    /* Assuming the low priority task is holding a mutex. */
    xTaskHandles[ configNUMBER_OF_CORES ]->uxMutexesHeld = 1;

    /* Low priority task inherit current core task priority, which is the high priority task. */
    taskENTER_CRITICAL();
    {
        xTaskPriorityInherit( xTaskHandles[ configNUMBER_OF_CORES ] );
    }
    taskEXIT_CRITICAL();

    /* Verify the priority has been changed */
    vTaskGetInfo( xTaskHandles[ configNUMBER_OF_CORES ], &xTaskDetails, pdTRUE, eInvalid );
    TEST_ASSERT_EQUAL( 3, xTaskDetails.xHandle->uxPriority );

    /* Verify that the low priority task is running on last core. */
    verifySmpTask( &xTaskHandles[ configNUMBER_OF_CORES ], eRunning, ( configNUMBER_OF_CORES - 1 ) );

    /* Disinherit low priority task after timeout to it's original priority. */
    taskENTER_CRITICAL();
    {
        xTaskPriorityDisinherit( xTaskHandles[ configNUMBER_OF_CORES ] );
    }
    taskEXIT_CRITICAL();

    /* Verify the priority has been changed */
    vTaskGetInfo( xTaskHandles[ configNUMBER_OF_CORES ], &xTaskDetails, pdTRUE, eInvalid );
    TEST_ASSERT_EQUAL( 1, xTaskDetails.xHandle->uxPriority );

    /* Verify the mutex held count is decreased. */
    TEST_ASSERT_EQUAL( 0U, xTaskHandles[ configNUMBER_OF_CORES ]->uxMutexesHeld );

    /* Verify the high and medium priority tasks running. */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        verifySmpTask( &xTaskHandles[ i ], eRunning, i );
    }

    /* Verify that the low priority task is ready. */
    verifySmpTask( &xTaskHandles[ configNUMBER_OF_CORES ], eReady, -1 );
}

/**
 * @brief AWS_IoT-FreeRTOS_SMP_TC-107
 * Task can inherit or disinherit other higher priority task. This test verify that
 * lower priority task will be selected to run when it inherit a higher priority task.
 * The lower priority will be switched out when it is disinherited by higher priority
 * task due to timeout.
 *
 * #define configRUN_MULTIPLE_PRIORITIES                    1
 * #define configUSE_TIME_SLICING                           0
 * #define configNUMBER_OF_CORES                            (N > 1)
 *
 * This test can be run with FreeRTOS configured for any number of cores greater
 * than 1.
 *
 * Tasks are created prior to starting the scheduler
 *
 * Task (T1)	      Task (T2)         Task (TN)       Task (TN + 1)
 * Priority – 3       Priority – 2      Priority – 2    Priority – 1
 * State – Ready	  State – Ready     State – Ready   State – Ready
 *
 * After calling vTaskStartScheduler()
 *
 * Task (T1)	      Task (T2)         Task (TN)       Task (TN + 1)
 * Priority – 3       Priority – 2      Priority – 2    Priority – 1
 * State – Running    State – Running   State – Running State – Ready
 *
 * Assuming task TN+1 is holding a mutex. Task TN+1 inherits task T1's priority
 *
 * Task (T1)	      Task (T2)         Task (TN)       Task (TN + 1)
 * Priority – 3       Priority – 2      Priority – 2    Priority – 3
 * State – Running    State – Running   State – Ready   State – Running
 *
 * Task TN+1 is disinherited by task T1 due to timeout
 *
 * Task (T1)	      Task (T2)         Task (TN)       Task (TN + 1)
 * Priority – 3       Priority – 2      Priority – 2    Priority – 1
 * State – Running    State – Running   State – Running State – Ready
 */
void test_task_priority_inherit_disinherit_timeout( void )
{
    TaskHandle_t xTaskHandles[ configNUMBER_OF_CORES + 1 ] = { NULL };
    uint32_t i;
    TaskStatus_t xTaskDetails;

    /* Create 1 high priority task. */
    xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 3, &xTaskHandles[ 0 ] );

    /* Create N - 1 Medium priority task. */
    for( i = 1; i < configNUMBER_OF_CORES; i++ )
    {
        xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 2, &xTaskHandles[ i ] );
    }

    /* Create 1 low priority task. */
    xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 1, &xTaskHandles[ i ] );

    /* Start the scheduler. */
    vTaskStartScheduler();

    /* Verify the high and medium priority tasks running. */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        verifySmpTask( &xTaskHandles[ i ], eRunning, i );
    }

    /* Verify the low priority task is ready. */
    verifySmpTask( &xTaskHandles[ configNUMBER_OF_CORES ], eReady, -1 );

    /* Assuming the low priority task is holding a mutex. */
    xTaskHandles[ configNUMBER_OF_CORES ]->uxMutexesHeld = 1;

    /* Low priority task inherit current core task priority, which is the high priority task. */
    taskENTER_CRITICAL();
    {
        xTaskPriorityInherit( xTaskHandles[ configNUMBER_OF_CORES ] );
    }
    taskEXIT_CRITICAL();

    /* Verify the priority has been changed */
    vTaskGetInfo( xTaskHandles[ configNUMBER_OF_CORES ], &xTaskDetails, pdTRUE, eInvalid );
    TEST_ASSERT_EQUAL( 3, xTaskDetails.xHandle->uxPriority );

    /* Verify that the low priority task is running on last core. */
    verifySmpTask( &xTaskHandles[ configNUMBER_OF_CORES ], eRunning, ( configNUMBER_OF_CORES - 1 ) );

    /* Disinherit low priority task after timeout to it's original priority. */
    taskENTER_CRITICAL();
    {
        vTaskPriorityDisinheritAfterTimeout( xTaskHandles[ configNUMBER_OF_CORES ], 1 );
    }
    taskEXIT_CRITICAL();

    /* Verify the priority has been changed */
    vTaskGetInfo( xTaskHandles[ configNUMBER_OF_CORES ], &xTaskDetails, pdTRUE, eInvalid );
    TEST_ASSERT_EQUAL( 1, xTaskDetails.xHandle->uxPriority );

    /* Verify the high and medium priority tasks running. */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        verifySmpTask( &xTaskHandles[ i ], eRunning, i );
    }

    /* Verify that the low priority task is ready. */
    verifySmpTask( &xTaskHandles[ configNUMBER_OF_CORES ], eReady, -1 );
}


/**
 * @brief AWS_IoT-FreeRTOS_SMP_TC-110
 * Yield for the task when setting the core affinity of a task of ready state. This
 * situation happens when the core can't select the task to run before the task
 * core affinity is changed. The vTaskCoreAffinitySet should request a core on which
 * the task is able to run with new core affinity setting.
 *
 * #define configRUN_MULTIPLE_PRIORITIES                    1
 * #define configUSE_TIME_SLICING                           0
 * #define configUSE_CORE_AFFINITY                          1
 * #define configNUMBER_OF_CORES                            (N > 2)
 *
 * This test can be run with FreeRTOS configured for any number of cores greater
 * than 2.
 *
 * Tasks are created prior to starting the scheduler
 *
 * Main task (T1)
 * Priority – 3
 * State – Ready
 *
 * After calling vTaskStartScheduler()
 *
 * Main task (T1)
 * Priority – 3
 * State – Running( 0 )
 *
 * After creating the core task with xTaskCreate(). Core 2 was requested to yield
 * but not yet able to select core task.
 *
 * Main task (T1)	      Core Task (T2)
 * Priority – 3           Priority – 3
 * State – Running( 0 )   State – Ready
 *
 * After setting the core affinity of the core task to core 1 only with vTaskCoreAffinitySet().
 *
 * Main task (T1)	      Core Task (T2)
 * Priority – 3           Priority – 3
 * State – Running( 0 )   Affinity – ( 1 )
 *                        State – Ready
 *
 * After async core yield for core task.
 *
 * Main Task (T1)	      Core Task (T2)
 * Priority – 3           Priority – 3
 * State – Running( 0 )   Affinity – ( 1 )
 *                        State – Running( 1 )
 *
 */
void test_task_create_task_set_affinity_async_yield( void )
{
    TaskHandle_t xMainTaskHandle;
    TaskHandle_t xCoreTaskHandle;
    BaseType_t xCoreID;

    /* The core yield should be manually triggered in the test cases when using
     *　async core yield setup. */
    commonAsyncCoreYieldSetup();

    /* Create high priority main task. */
    xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 3, &xMainTaskHandle );

    /* Start the scheduler. */
    vTaskStartScheduler();

    /* Create high priority core task. */
    xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 3, &xCoreTaskHandle );

    /* Set the core affinity of the core task to core 1. */
    vTaskCoreAffinitySet( xCoreTaskHandle, ( 1 << 1 ) );

    /* Core yield is called here to simulate SMP asynchronous behavior. */
    for( xCoreID = 0; xCoreID < configNUMBER_OF_CORES; xCoreID++ )
    {
        vCheckAndExecuteAsyncCoreYield( xCoreID );
    }

    /* Verify that the task core task can run on core 1. */
    verifySmpTask( &xCoreTaskHandle, eRunning, 1 );
}
