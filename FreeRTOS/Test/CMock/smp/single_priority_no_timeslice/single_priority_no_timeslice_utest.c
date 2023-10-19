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
/*! @file single_priority_no_timeslice_utest.c */

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

/* ==============================  Test Cases  ============================== */

/**
 * @brief AWS_IoT-FreeRTOS_SMP_TC-1
 * The purpose of this test is to verify when multiple CPU cores are available and
 * the FreeRTOS kernel is configured as (configRUN_MULTIPLE_PRIORITIES = 0) that tasks
 * of equal priority will execute simultaneously. The kernel will be configured as follows:
 *
 * #define configRUN_MULTIPLE_PRIORITIES                    0
 * #define configUSE_TIME_SLICING                           0
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
 * @brief AWS_IoT-FreeRTOS_SMP_TC-2
 * The purpose of this test is to verify when multiple CPU cores are available and
 * the FreeRTOS kernel is configured as (configRUN_MULTIPLE_PRIORITIES = 0) that
 * tasks of different priorities will not execute simultaneously. The kernel will be
 * configured as follows:
 *
 * #define configRUN_MULTIPLE_PRIORITIES                    0
 * #define configUSE_TIME_SLICING                           0
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
 * State - Running (Core 0)	   State - Ready
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

    /* Verify the high priority task is running */
    verifySmpTask( &xTaskHandles[ 0 ], eRunning, 0 );

    for( i = 1; i < configNUMBER_OF_CORES; i++ )
    {
        /* Verify all other tasks are in the idle state */
        verifySmpTask( &xTaskHandles[ i ], eReady, -1 );

        /* Verify the idle task is running on all other CPU cores */
        verifyIdleTask( i - 1, i );
    }
}

/**
 * @brief AWS_IoT-FreeRTOS_SMP_TC-3
 * A task of equal priority will be created for each available CPU core.
 * This test will verify that when the priority of one task is lowered the
 * task is no longer running.
 *
 * #define configRUN_MULTIPLE_PRIORITIES                    0
 * #define configUSE_TIME_SLICING                           0
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
 * Task (T1)	   Task (TN)
 * Priority – 1    Priority – 2
 * State - Ready   State - Running (Core N)
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

    /* Verify T0 is the the ready state */
    verifySmpTask( &xTaskHandles[ 0 ], eReady, -1 );

    /* Verify the idle task is now running on CPU core 0 */
    verifyIdleTask( 0, 0 );

    /* Verify all other tasks remain in the running state on the same CPU cores */
    for( i = 1; i < configNUMBER_OF_CORES; i++ )
    {
        verifySmpTask( &xTaskHandles[ i ], eRunning, i );
    }
}

/**
 * @brief AWS_IoT-FreeRTOS_SMP_TC-4
 * A task of equal priority will be created for each available CPU core.
 * This test will verify that when the priority of one task is raised it
 * shall remain running and all other tasks will enter the ready state.
 *
 * #define configRUN_MULTIPLE_PRIORITIES                    0
 * #define configUSE_TIME_SLICING                           0
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
 * State - Running (Core 0)  State - Ready
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

    for( i = 1; i < configNUMBER_OF_CORES; i++ )
    {
        /* Verify all other tasks are in the ready state */
        verifySmpTask( &xTaskHandles[ i ], eReady, -1 );

        /* Verify the idle task is running on all other CPU cores */
        verifyIdleTask( i - 1, i );
    }
}

/**
 * @brief AWS_IoT-FreeRTOS_SMP_TC-111
 * A task of priority higher than idle is created. The test verify that when the priority
 * of the task is raised, running idle task won't be altered.
 *
 * #define configRUN_MULTIPLE_PRIORITIES                    0
 * #define configUSE_TIME_SLICING                           0
 * #define configNUMBER_OF_CORES                            (N > 1)
 *
 * This test can be run with FreeRTOS configured for any number of cores
 * greater than 1.
 *
 * A Task is created prior to starting the scheduler.
 *
 * Task (T1)
 * Priority – 1
 * State - Ready
 *
 * After calling vTaskStartScheduler()
 *
 * Task (T1)                Idle task (1)               Idle task (N)
 * Priority – 1             Priority – idle             Priority – idle
 * State - Running (Core 1) State - Running (Core 2)    State - ready
 *
 * After calling vTaskPrioritySet() and raising the priority of task T1
 *
 * Task (T1)                Idle task (1)              Idle task (N)
 * Priority – 2             Priority – idle            Priority – idle
 * State - Running (Core 0) State - Running (Core 1)   State - ready
 */
void test_priority_change_task_high_priority_raise( void )
{
    TaskHandle_t xTaskHandles[ 1 ] = { NULL };
    uint32_t i;
    TaskStatus_t xTaskDetails;

    /* Create a task to run. */
    xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 1, &xTaskHandles[ 0 ] );

    /* Start scheduler. */
    vTaskStartScheduler();

    /* Verify the task is running. */
    verifySmpTask( &xTaskHandles[ 0 ], eRunning, 0 );

    for( i = 1; i < configNUMBER_OF_CORES; i++ )
    {
        /* Verify the idle task is running on all other CPU cores */
        verifyIdleTask( i - 1, i );
    }

    /* Raise the priority of the running task. */
    vTaskPrioritySet( xTaskHandles[ 0 ], 2 );

    /* Verify the priority has been changed */
    vTaskGetInfo( xTaskHandles[ 0 ], &xTaskDetails, pdTRUE, eInvalid );
    TEST_ASSERT_EQUAL( 2, xTaskDetails.xHandle->uxPriority );

    /* Verify the task is still in the running state */
    verifySmpTask( &xTaskHandles[ 0 ], eRunning, 0 );

    for( i = 1; i < configNUMBER_OF_CORES; i++ )
    {
        /* Verify the idle task is still running on the same core. */
        verifyIdleTask( i - 1, i );
    }
}

/**
 * @brief AWS_IoT-FreeRTOS_SMP_TC-5
 * A single task of high priority will be created. A low priority task will be
 * created for each remaining available CPU core. The test will first verify
 * only the high priority task is in the running state. Each low priority task
 * will then be raised to high priority and enter the running state.
 *
 * #define configRUN_MULTIPLE_PRIORITIES                    0
 * #define configUSE_TIME_SLICING                           0
 * #define configNUMBER_OF_CORES                            (N > 1)
 *
 * This test can be run with FreeRTOS configured for any number of cores greater
 * than 1.
 *
 * Tasks are created prior to starting the scheduler.
 *
 * Task (T1)	   Task (TN)
 * Priority – 2    Priority – 1
 * State - Ready   State - Ready
 *
 * After calling vTaskStartScheduler()
 *
 * Task (T1)	             Task (TN)
 * Priority – 2              Priority – 1
 * State - Running (Core 0)	 State - Ready
 *
 * After calling vTaskPrioritySet() and raising the priority of tasks TN
 *
 * Task (T1)	             Task (TN)
 * Priority – 2              Priority – 2
 * State - Running (Core 0)	 State - Running (Core N)
 */
void test_priority_change_tasks_different_priority_raise( void )
{
    TaskHandle_t xTaskHandles[ configNUMBER_OF_CORES ] = { NULL };
    uint32_t i;
    TaskStatus_t xTaskDetails;

    /* Create a single task at high priority */
    xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 2, &xTaskHandles[ 0 ] );

    /* Create all remaining tasks at low priority */
    for( i = 1; i < configNUMBER_OF_CORES; i++ )
    {
        xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 1, &xTaskHandles[ i ] );
    }

    vTaskStartScheduler();

    /* Verify the high priority task is running */
    verifySmpTask( &xTaskHandles[ 0 ], eRunning, 0 );

    for( i = 1; i < configNUMBER_OF_CORES; i++ )
    {
        /* Verify all other tasks are in the idle state */
        verifySmpTask( &xTaskHandles[ i ], eReady, -1 );

        /* Verify the idle task is running on all other CPU cores */
        verifyIdleTask( i - 1, i );
    }

    for( i = 1; i < configNUMBER_OF_CORES; i++ )
    {
        /* Raise the priority of the task */
        vTaskPrioritySet( xTaskHandles[ i ], 2 );

        /* Verify the priority has been raised */
        vTaskGetInfo( xTaskHandles[ i ], &xTaskDetails, pdTRUE, eInvalid );
        TEST_ASSERT_EQUAL( 2, xTaskDetails.xHandle->uxPriority );

        /* Verify the task is now in the running state */
        verifySmpTask( &xTaskHandles[ i ], eRunning, configNUMBER_OF_CORES - i );
    }
}

/**
 * @brief AWS_IoT-FreeRTOS_SMP_TC-6
 * A single task of high priority will be created. A low priority task will be
 * created for each remaining available CPU core. The test will first verify
 * only the high priority task is in the running state. The high priority task
 * shall be lowered. This will cause all low priority tasks to enter the running
 * state.
 *
 * #define configRUN_MULTIPLE_PRIORITIES                    0
 * #define configUSE_TIME_SLICING                           0
 * #define configNUMBER_OF_CORES                            (N > 1)
 *
 * This test can be run with FreeRTOS configured for any number of cores greater
 * than 1.
 *
 * Tasks are created prior to starting the scheduler.
 *
 * Task (T1)	    Task (TN)
 * Priority – 2     Priority –1
 * State - Ready    State - Ready
 *
 * After calling vTaskStartScheduler()
 *
 * Task (T1)	             Task (TN)
 * Priority – 2              Priority – 1
 * State - Running (Core 0)	 State - Ready
 *
 * After calling vTaskPrioritySet() and lowering the
 * priority of all low priority tasks.
 *
 * Task (T1)	                  Task (T2)                      Task (TN)
 * Priority – 1                   Priority – 1                   Priority – 1
 * State - Running (Core N - 1)	  State - Running (Core 0)       State - Running (Core N - 2)
 */
void test_priority_change_tasks_different_priority_lower( void )
{
    TaskHandle_t xTaskHandles[ configNUMBER_OF_CORES ] = { NULL };
    uint32_t i;
    TaskStatus_t xTaskDetails;

    /* Create a single task at high priority */
    xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 2, &xTaskHandles[ 0 ] );

    /* Create all remaining tasks at low priority */
    for( i = 1; i < configNUMBER_OF_CORES; i++ )
    {
        xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 1, &xTaskHandles[ i ] );
    }

    vTaskStartScheduler();

    /* Verify the high priority task is running */
    verifySmpTask( &xTaskHandles[ 0 ], eRunning, 0 );

    for( i = 1; i < configNUMBER_OF_CORES; i++ )
    {
        /* Verify all other tasks are in the idle state */
        verifySmpTask( &xTaskHandles[ i ], eReady, -1 );

        /* Verify the idle task is running on all other CPU cores */
        verifyIdleTask( i - 1, i );
    }

    /* Lower the priority of the high priority task to match all other tasks */
    vTaskPrioritySet( xTaskHandles[ 0 ], 1 ); /*After this returns task[0] is not running, task[1] is running on 0 */

    /* Verify the priority has been lowered */
    vTaskGetInfo( xTaskHandles[ 0 ], &xTaskDetails, pdTRUE, eInvalid );
    TEST_ASSERT_EQUAL( 1, xTaskDetails.xHandle->uxPriority );

    /* Verify the task remains running. */

    /* When priority dropped in prvSelectHighestPriorityTask, all the idle cores
     * will yield for context switch. The ready queue is a FIFO. Core 0 will choose
     * The first task in the ready queue which is task 1. Task 0 will be selected
     * by the last core which calls context switch.
     * Core 0 choose xTaskHandles[1]
     * Core 1 choose xTaskHandles[2]
     * ....
     * Core N-2 choose xTaskHandles[N-1]
     * Core N-1 choose xTaskHandles[0]
     */
    verifySmpTask( &xTaskHandles[ 0 ], eRunning, ( BaseType_t ) ( configNUMBER_OF_CORES - 1 ) );

    for( i = 1; i < configNUMBER_OF_CORES; i++ )
    {
        /* Verify all other tasks are in the running state */
        verifySmpTask( &xTaskHandles[ i ], eRunning, ( BaseType_t ) ( i - 1 ) );
    }
}

/**
 * @brief AWS_IoT-FreeRTOS_SMP_TC-7
 * Tasks of equal priority will be created for N - 1 CPU cores. The remaining
 * tasks will be idle. Once the scheduler is started a new task of equal
 * priority shall be created. The test shall verify the new task is in the
 * running state.
 *
 * #define configRUN_MULTIPLE_PRIORITIES                    0
 * #define configUSE_TIME_SLICING                           0
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

    /* Create a new task of equal priority */
    xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 1, &xTaskHandles[ i ] );

    /* Verify the new task is in the running state */
    verifySmpTask( &xTaskHandles[ i ], eRunning, i );
}

/**
 * @brief AWS_IoT-FreeRTOS_SMP_TC-8
 * Tasks of equal priority will be created for N - 1 CPU cores. The remaining
 * task will be idle. Once the scheduler is started a new task of lower
 * priority shall be created. The test shall verify the new task is in the
 * ready state.
 *
 * #define configRUN_MULTIPLE_PRIORITIES                    0
 * #define configUSE_TIME_SLICING                           0
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
 * State - Running (Core N)	 State - Ready
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

    /* Verify the new task is in the ready state */
    verifySmpTask( &xTaskHandles[ i ], eReady, -1 );
}

/**
 * @brief AWS_IoT-FreeRTOS_SMP_TC-9
 * Tasks of equal priority will be created for N - 1 CPU cores. The remaining
 * task will be idle. Once the scheduler is started a new task of higher
 * priority shall be created. The test shall verify the new task is in the
 * running state.
 *
 * #define configRUN_MULTIPLE_PRIORITIES                    0
 * #define configUSE_TIME_SLICING                           0
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
 * Task N - 1        New Task
 * Priority – 1      Priority – 2
 * State - Ready	 State - Running (First available core)
 *
 */
void test_task_create_tasks_higher_priority( void )
{
    TaskHandle_t xTaskHandles[ configNUMBER_OF_CORES ] = { NULL };
    uint32_t i, xCoreToRunTask;

    /* Create all tasks at equal priority */
    for( i = 0; i < ( configNUMBER_OF_CORES - 1 ); i++ )
    {
        xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 2, &xTaskHandles[ i ] );
    }

    /* The task running status on each core after scheduler started:
     * core 0 xTaskHandles[0]
     * core 1 xTaskHandles[1]
     * core 2 xTaskHandles[2]
     * .....
     * core N - 2 xTaskHandles[N - 2]
     * core N - 1 xIdleTaskHandles[0]
     */
    vTaskStartScheduler();

    /* Verify all tasks are in the running state */
    for( i = 0; i < ( configNUMBER_OF_CORES - 1 ); i++ )
    {
        verifySmpTask( &xTaskHandles[ i ], eRunning, i );
    }

    /* Verify remaining CPU core is running the idle task */
    verifyIdleTask( 0, i );

    /* Create a new task of higher priority. prvYieldForTask will be called to yield
     * for this task. Since all the core has lower priority than this task. These cores
     * will be requested to yield. The task is choosen by the core yield order.
     * This task is created on core 0.
     * vTaskExitCritical does the following:
     * 1. release the spinlock -> All the other cores yield
     * 2. Check xYieldPendings for this core -> This core yields.
     * core N-1 won't yield since it is already running the idle task.
     * The core yields in the following order.
     * core 1 choose The new task xTaskHandles[N-1]
     * core 2 choose xIdleTaskHandles[1]
     * .....
     * core N - 2 choose xIdleTaskHandles[N-3]
     * core 0 choose xIdleTaskHandles[N-2]
     */
    xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 3, &xTaskHandles[ i ] );

    /* Verify the new task is in the running state. The created task will increase the priority */
    xCoreToRunTask = 1;

    if( xCoreToRunTask == ( configNUMBER_OF_CORES - 1 ) )
    {
        /* Core 1 is the last core ( configNUMBER_OF_CORES - 1 ), then it is already running
         * idle task. The last core to choose task is core 0. */
        xCoreToRunTask = 0;
    }

    verifySmpTask( &xTaskHandles[ i ], eRunning, xCoreToRunTask );

    /* Verify all tasks are in the ready state */
    for( i = 0; i < ( configNUMBER_OF_CORES - 1 ); i++ )
    {
        verifySmpTask( &xTaskHandles[ i ], eReady, -1 );
    }

    /* Verify all the idle task running. */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        if( i == xCoreToRunTask )
        {
            /* This core is running the task. */
        }
        else if( i == 0 )
        {
            /* Core 0 choose the last. It chooses the configNUMBER_OF_CORES - 2 idle task. */
            verifyIdleTask( ( BaseType_t ) ( configNUMBER_OF_CORES - 2 ), i );
        }
        else if( i == ( configNUMBER_OF_CORES - 1 ) )
        {
            /* The last core won't yield, since it is running an idle task already. */
            verifyIdleTask( 0, i );
        }
        else
        {
            verifyIdleTask( ( BaseType_t ) ( i - 1 ), i );
        }
    }
}

/**
 * @brief AWS_IoT-FreeRTOS_SMP_TC-10
 * A task of equal priority will be created for each available CPU core. This
 * test will verify that when a new task of equal priority is created it will
 * be in the ready state.
 *
 * #define configRUN_MULTIPLE_PRIORITIES                    0
 * #define configUSE_TIME_SLICING                           0
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
 * @brief AWS_IoT-FreeRTOS_SMP_TC-11
 * A task of equal priority will be created for each available CPU core. This
 * test will verify that when a new task of lower priority is created it will
 * be in the ready state.
 *
 * #define configRUN_MULTIPLE_PRIORITIES                    0
 * #define configUSE_TIME_SLICING                           0
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
 * @brief AWS_IoT-FreeRTOS_SMP_TC-12
 * A task of equal priority will be created for each available CPU core. This
 * test will verify that when a new task of higher priority is created it will
 * be in the running state and all other tasks will now be in the ready state.
 *
 * #define configRUN_MULTIPLE_PRIORITIES                    0
 * #define configUSE_TIME_SLICING                           0
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
 * State - Ready	          State - Running ( First available core )
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

    /* The created task has higher priority than other tasks. This will cause all
     * the other cores yield. The task is choosen by core yield order which is accending
     * in vYieldCores. Since core 0 create the task, it will yield last due to the mock
     * implementation.
     * core 1 choose xTaskHandles[N]
     * core 2 choose xIdleTaskHandles[0]
     * ...
     * core N-1 choose xIdleTaskHandles[N-3]
     * core 0 choose xIdleTaskHandles[N-2]
     */
    xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 2, &xTaskHandles[ i ] );

    /* Verify the new task is in the ready state */
    verifySmpTask( &xTaskHandles[ i ], eRunning, 1 );

    /* Verify all tasks remain in the running state */
    for( i = 1; i < configNUMBER_OF_CORES; i++ )
    {
        verifySmpTask( &xTaskHandles[ i ], eReady, -1 );
    }

    /* Verify all the idle task. */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        if( i == 0 )
        {
            verifyIdleTask( configNUMBER_OF_CORES - 2, i );
        }
        else if( i == 1 )
        {
            /* This core is running task. */
        }
        else
        {
            verifyIdleTask( i - 2, i );
        }
    }
}

/**
 * @brief AWS_IoT-FreeRTOS_SMP_TC-13
 * A single task of high priority will be created. A low priority task will
 * be created for each remaining available CPU core. This test will verify when
 * a new task is created at priority equal to the running task it will be in
 * the running state. The original low priority task will remain in the ready
 * state.
 *
 * #define configRUN_MULTIPLE_PRIORITIES                    0
 * #define configUSE_TIME_SLICING                           0
 * #define configNUMBER_OF_CORES                            (N > 1)
 *
 * This test can be run with FreeRTOS configured for any number of cores
 * greater than 1.
 *
 * Tasks are created prior to starting the scheduler.
 *
 * Task (T1)	    Task (TN)
 * Priority – 2     Priority – 1
 * State - Running	State - Ready
 *
 * After calling vTaskStartScheduler()
 *
 * Task (T1)	             Task (TN)
 * Priority – 2              Priority – 1
 * State - Running (Core 0)	 State - Ready
 *
 * Create a new task at the same priority as task (T1)
 *
 * Task (T1)	              Task (TN)	     New Task
 * Priority – 2               Priority – 1   Priority – 2
 * State - Running (Core 0)	  State - Ready  State - Running (Last available core)
 */
void test_task_create_all_cores_different_priority_high( void )
{
    TaskHandle_t xTaskHandles[ configNUMBER_OF_CORES + 1 ] = { NULL };
    uint32_t i;

    /* Create a single task at high priority */
    xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 2, &xTaskHandles[ 0 ] );

    /* Create all remaining tasks at low priority */
    for( i = 1; i < configNUMBER_OF_CORES; i++ )
    {
        xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 1, &xTaskHandles[ i ] );
    }

    vTaskStartScheduler();

    /* Verify the high priority task is running */
    verifySmpTask( &xTaskHandles[ 0 ], eRunning, 0 );

    for( i = 1; i < configNUMBER_OF_CORES; i++ )
    {
        /* Verify all other tasks are in the idle state */
        verifySmpTask( &xTaskHandles[ i ], eReady, -1 );

        /* Verify the idle task is running on all other CPU cores */
        verifyIdleTask( i - 1, i );
    }

    /* Create a new task of high priority */
    xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 2, &xTaskHandles[ i ] );

    /* Verify the new task is in the running state */
    verifySmpTask( &xTaskHandles[ i ], eRunning, ( configNUMBER_OF_CORES - 1 ) );

    /* Verify all tasks remain in the ready state */
    for( i = 1; i < configNUMBER_OF_CORES; i++ )
    {
        verifySmpTask( &xTaskHandles[ i ], eReady, -1 );
    }
}

/**
 * @brief AWS_IoT-FreeRTOS_SMP_TC-14
 * A single task of high priority will be created. A low priority task will
 * be created for each remaining available CPU core. This test will verify when
 * a new task is created at low priority it will be in the ready state. The
 * original low priority tasks will also remain in the ready state.
 *
 * #define configRUN_MULTIPLE_PRIORITIES                    0
 * #define configUSE_TIME_SLICING                           0
 * #define configNUMBER_OF_CORES                            (N > 1)
 *
 * This test can be run with FreeRTOS configured for any number of cores
 * greater than 1.
 *
 * Tasks are created prior to starting the scheduler.
 *
 * Task (T1)	    Task (TN)
 * Priority – 2     Priority – 1
 * State - Running	State - Ready
 *
 * After calling vTaskStartScheduler()
 *
 * Task (T1)	             Task (TN)
 * Priority – 2              Priority – 1
 * State - Running (Core 0)	 State - Ready
 *
 * Create a new task at the same priority as task (T1)
 *
 * Task (T1)	              Task (TN)	     New Task
 * Priority – 2               Priority – 1   Priority – 1
 * State - Running (Core 0)	  State - Ready  State - Ready
 */
void test_task_create_all_cores_different_priority_low( void )
{
    TaskHandle_t xTaskHandles[ configNUMBER_OF_CORES + 1 ] = { NULL };
    uint32_t i;

    /* Create a single task at high priority */
    xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 2, &xTaskHandles[ 0 ] );

    /* Create all remaining tasks at low priority */
    for( i = 1; i < configNUMBER_OF_CORES; i++ )
    {
        xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 1, &xTaskHandles[ i ] );
    }

    vTaskStartScheduler();

    /* Verify the high priority task is running */
    verifySmpTask( &xTaskHandles[ 0 ], eRunning, 0 );

    for( i = 1; i < configNUMBER_OF_CORES; i++ )
    {
        /* Verify all other tasks are in the idle state */
        verifySmpTask( &xTaskHandles[ i ], eReady, -1 );

        /* Verify the idle task is running on all other CPU cores */
        verifyIdleTask( i - 1, i );
    }

    /* Create a new task of high priority */
    xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 1, &xTaskHandles[ i ] );

    /* Verify the new task is in the ready state */
    verifySmpTask( &xTaskHandles[ i ], eReady, -1 );

    /* Verify all tasks remain in the ready state */
    for( i = 1; i < configNUMBER_OF_CORES; i++ )
    {
        verifySmpTask( &xTaskHandles[ i ], eReady, -1 );
    }
}

/**
 * @brief AWS_IoT-FreeRTOS_SMP_TC-15
 * Tasks of equal priority shall be created for each available CPU core.
 * This test will verify when a task is deleted the remaining tasks are still
 * in the running state.
 *
 * #define configRUN_MULTIPLE_PRIORITIES                    0
 * #define configUSE_TIME_SLICING                           0
 * #define configNUMBER_OF_CORES                            (N > 1)
 *
 * This test can be run with FreeRTOS configured for any number of cores
 * greater than 1.
 *
 * Tasks are created prior to starting the scheduler.
 *
 * Task (T1)	   Task (TN)
 * Priority – 1    Priority – 1
 * State - Ready   State - Ready
 *
 * After calling vTaskStartScheduler()
 *
 * Task (T1)	              Task (TN)
 * Priority – 1               Priority – 1
 * State - Running (Core 0)	  State - Running (Core N)
 *
 * Delete task (T1)
 *
 * Task (T1)	              Task (TN)
 * Priority – 1               Priority – 1
 * State - Deleted            State - Running (Core N)
 */
void test_task_delete_tasks_equal_priority_delete_task( void )
{
    TaskHandle_t xTaskHandles[ configNUMBER_OF_CORES ] = { NULL };
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

    /* Verify no tasks are pending deletion */
    TEST_ASSERT_EQUAL( 0, uxDeletedTasksWaitingCleanUp );

    /* Delete task T0 */
    vTaskDelete( xTaskHandles[ 0 ] );

    /* Verify a single task is pending deletion */
    TEST_ASSERT_EQUAL( 1, uxDeletedTasksWaitingCleanUp );

    /* Verify task T0 is in the deleted state */
    verifySmpTask( &xTaskHandles[ 0 ], eDeleted, -1 );

    for( i = 1; i < configNUMBER_OF_CORES; i++ )
    {
        /* Verify all remaining tasks are still running */
        verifySmpTask( &xTaskHandles[ i ], eRunning, i );
    }
}

/**
 * @brief AWS_IoT-FreeRTOS_SMP_TC-16
 * A single task of high priority will be created. A low priority task will be
 * created for each remaining available CPU core. The test will first verify
 * only the high priority task is in the running state. Each low priority task
 * will then be deleted.
 *
 * #define configRUN_MULTIPLE_PRIORITIES                    0
 * #define configUSE_TIME_SLICING                           0
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
 * State - Running (Core 0)	 State - Ready
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

    /* Verify the high priority task is running */
    verifySmpTask( &xTaskHandles[ 0 ], eRunning, 0 );

    for( i = 1; i < configNUMBER_OF_CORES; i++ )
    {
        /* Verify all other tasks are in the idle state */
        verifySmpTask( &xTaskHandles[ 1 ], eReady, -1 );

        /* Verify the idle task is running on all other CPU cores */
        verifyIdleTask( i - 1, i );
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

    /* Remains 0 since all deleted tasks were not running */
    TEST_ASSERT_EQUAL( 0, uxDeletedTasksWaitingCleanUp );
}

/**
 * @brief AWS_IoT-FreeRTOS_SMP_TC-17
 * A single task of high priority will be created. A low priority task will be
 * created for each remaining available CPU core. The test will first verify
 * only the high priority task is in the running state. The high priority task
 * will then be deleted.
 *
 * #define configRUN_MULTIPLE_PRIORITIES                    0
 * #define configUSE_TIME_SLICING                           0
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
 * State - Running (Core 0)	 State - Ready
 *
 * Delete the high priority task
 *
 * Task (T1)	      Task (TN)
 * Priority – 2       Priority – 1
 * State - Deleted	  State - Running (Core 0)
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

    /* Verify the high priority task is running */
    verifySmpTask( &xTaskHandles[ 0 ], eRunning, 0 );

    for( i = 1; i < configNUMBER_OF_CORES; i++ )
    {
        /* Verify all other tasks are in the idle state */
        verifySmpTask( &xTaskHandles[ 1 ], eReady, -1 );

        /* Verify the idle task is running on all other CPU cores */
        verifyIdleTask( i - 1, i );
    }

    /* Verify no tasks are pending deletion */
    TEST_ASSERT_EQUAL( 0, uxDeletedTasksWaitingCleanUp );

    /* Delete task T0 */
    vTaskDelete( xTaskHandles[ 0 ] );

    /* Verify the task has been deleted */
    TEST_ASSERT_EQUAL( 1, uxDeletedTasksWaitingCleanUp );
    verifySmpTask( &xTaskHandles[ 0 ], eDeleted, -1 );

    /* Verify all previous ready tasks are now running */
    for( i = 1; i < ( configNUMBER_OF_CORES ); i++ )
    {
        verifySmpTask( &xTaskHandles[ i ], eRunning, i - 1 );
    }
}

/**
 * @brief AWS_IoT-FreeRTOS_SMP_TC-18
 * Tasks of equal priority shall be created for each available CPU core.
 * One additional task shall be created while will be idle. This test will
 * verify when a task is deleted the idle task will begin running.
 *
 * #define configRUN_MULTIPLE_PRIORITIES                    0
 * #define configUSE_TIME_SLICING                           0
 * #define configNUMBER_OF_CORES                            (N > 1)
 *
 * This test can be run with FreeRTOS configured for any number of cores
 * greater than 1.
 *
 * Tasks are created prior to starting the scheduler.
 *
 * Task (T1)	  Task (TN)	      Task (TN + 1)
 * Priority – 1   Priority – 1    Priority - 1
 * State - Ready  State - Ready   State - Ready
 *
 * After calling vTaskStartScheduler()
 *
 * Task (T1)	            Task (TN)	              Task (T2)
 * Priority – 1             Priority – 1              Priority – 1
 * State - Running (Core 0)	State - Running (Core N)  State - Ready
 *
 * Delete task (T1)
 * Task (T1)	    Task (TN)	              Task (T3)
 * Priority – 1     Priority – 1              Priority – 1
 * State - Deleted	State - Running (Core N)  State - Running (Core 0)
 */
void test_task_delete_tasks_equal_priority_delete_running( void )
{
    TaskHandle_t xTaskHandles[ configNUMBER_OF_CORES + 1 ] = { NULL };
    uint32_t i;

    /* Create configNUMBER_OF_CORES + 1 tasks of equal priority */
    for( i = 0; i < ( configNUMBER_OF_CORES + 1 ); i++ )
    {
        xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 1, &xTaskHandles[ i ] );
    }

    vTaskStartScheduler();

    /* Verify tasks are running and one task is ready */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        verifySmpTask( &xTaskHandles[ i ], eRunning, i );
    }

    verifySmpTask( &xTaskHandles[ i ], eReady, -1 );

    /* Verify there are no deleted tasks pending cleanup */
    TEST_ASSERT_EQUAL( 0, uxDeletedTasksWaitingCleanUp );

    /* Delete task 1 running on core 0 */
    vTaskDelete( xTaskHandles[ 0 ] );

    /* Verify a deleted task is now pending cleanup */
    TEST_ASSERT_EQUAL( 1, uxDeletedTasksWaitingCleanUp );

    /* Verify task T0 has been deleted */
    verifySmpTask( &xTaskHandles[ 0 ], eDeleted, -1 );

    for( i = 1; i < ( configNUMBER_OF_CORES ); i++ )
    {
        /* Verify all other tasks are in the running state */
        verifySmpTask( &xTaskHandles[ i ], eRunning, i );
    }

    /* The last task will be running on core 0 */
    verifySmpTask( &xTaskHandles[ i ], eRunning, 0 );
}

/**
 * @brief AWS_IoT-FreeRTOS_SMP_TC-19
 * A task of high priority will be created for each available CPU core. A low
 * priority task will also be created and be in the ready state. This test
 * will verify that when a high priority task is deleted the low priority task
 * will remain in the ready state.
 *
 * #define configRUN_MULTIPLE_PRIORITIES                    0
 * #define configUSE_TIME_SLICING                           0
 * #define configNUMBER_OF_CORES                            (N > 1)
 *
 * This test can be run with FreeRTOS configured for any number of cores
 * greater than 1.
 *
 * Tasks are created prior to starting the scheduler.
 *
 * Task (TN)	  Task (TN + 1)
 * Priority – 2   Priority - 1
 * State - Ready  State - Ready
 *
 * After calling vTaskStartScheduler()
 *
 * Task (TN)	             Task (TN + 1)
 * Priority – 2              Priority - 1
 * State - Running (Core N)	 State - Ready
 *
 * Delete task (T0)
 *
 * Task (T0)	     Task (TN)	               Task (TN + 1)
 * Priority – 2      Priority – 2              Priority – 1
 * State - Deleted	 State - Running (Core N)  State - Ready
 */
void test_task_delete_all_cores_high_priority_delete_high_priority_task( void )
{
    TaskHandle_t xTaskHandles[ configNUMBER_OF_CORES + 1 ] = { NULL };
    uint32_t i;

    /* Create tasks of high priority */
    for( i = 0; i < ( configNUMBER_OF_CORES ); i++ )
    {
        xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 2, &xTaskHandles[ i ] );
    }

    /* Create a single task of low priority */
    xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 1, &xTaskHandles[ i ] );

    vTaskStartScheduler();

    /* Verify tasks are running and one task is ready */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        verifySmpTask( &xTaskHandles[ i ], eRunning, i );
    }

    verifySmpTask( &xTaskHandles[ i ], eReady, -1 );

    /* Verify there are no deleted tasks pending cleanup */
    TEST_ASSERT_EQUAL( 0, uxDeletedTasksWaitingCleanUp );

    /* Delete task running on core 0 */
    vTaskDelete( xTaskHandles[ 0 ] );

    /* Verify a deleted task is now pending cleanup */
    TEST_ASSERT_EQUAL( 1, uxDeletedTasksWaitingCleanUp );

    /* Verify task T0 has been deleted */
    verifySmpTask( &xTaskHandles[ 0 ], eDeleted, -1 );

    /* Verify core 0 is now idle */
    verifyIdleTask( 0, 0 );

    for( i = 1; i < ( configNUMBER_OF_CORES ); i++ )
    {
        /* Verify all other tasks are in the running state */
        verifySmpTask( &xTaskHandles[ i ], eRunning, i );
    }

    /* The last task will remain in the ready state */
    verifySmpTask( &xTaskHandles[ i ], eReady, -1 );
}

/**
 * @brief AWS_IoT-FreeRTOS_SMP_TC-21
 * A task of equal priority will be created for each available CPU core. This
 * test will verify that when a task is suspended the CPU core will execute
 * the idle task.
 *
 * #define configRUN_MULTIPLE_PRIORITIES                    0
 * #define configUSE_TIME_SLICING                           0
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
 * @brief AWS_IoT-FreeRTOS_SMP_TC-22
 * A single task of high priority will be created. A low priority task will be
 * created for each remaining available CPU core. The test will first verify
 * that when the high priority task is suspended the low priority tasks will
 * enter the running state. When the high priority task is resumed, each low
 * priority task will return to the ready state.
 *
 * #define configRUN_MULTIPLE_PRIORITIES                    0
 * #define configUSE_TIME_SLICING                           0
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
 * State - Running (Core 0)	  State - Ready
 *
 * Suspend task (T1)
 *
 * Task (T1)	       Task (TN)
 * Priority – 2        Priority – 1
 * State - Suspended   State - Running (Core N)
 *
 * Resume task (T1)
 *
 * Task (T1)	                             Task (TN)
 * Priority – 2                              Priority – 1
 * State - Running (First available core)	 State - Ready
 */
void test_task_suspend_all_cores_different_priority_suspend_high( void )
{
    TaskHandle_t xTaskHandles[ configNUMBER_OF_CORES ] = { NULL };
    uint32_t i, xCoreToRunTask;

    /* Create a single task at high priority */
    xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 2, &xTaskHandles[ 0 ] );

    /* Create all remaining tasks at low priority */
    for( i = 1; i < configNUMBER_OF_CORES; i++ )
    {
        xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 1, &xTaskHandles[ i ] );
    }

    /* SMP cores start with idle task. Idle task will yield itself when first time it runs
     * The task running status when the scheduler starts.
     * Core 0 : xTaskHandles[0] with priority 2
     * Core 1 : xIdleTaskHandles[0]
     * ...
     * Core N-1 : xIdleTaskHandles[N-2]
     */
    vTaskStartScheduler();

    /* Verify the high priority task is running */
    verifySmpTask( &xTaskHandles[ 0 ], eRunning, 0 );

    for( i = 1; i < configNUMBER_OF_CORES; i++ )
    {
        /* Verify all other tasks are in the idle state */
        verifySmpTask( &xTaskHandles[ i ], eReady, -1 );

        /* Verify the idle task is running on all other CPU cores */
        verifyIdleTask( i - 1, i );
    }

    /* The task running status when xTaskHandles[0] suspend ifself on Core 0.
     * 1. Core 0 will yield itself and call prvSelectHighestPriorityTask
     * 2. In prvSelectHighestPriorityTask, the top running priority is dropped.
     * All the other cores running the idle are requested to yield. The mock implementation
     * assume that cores yield in ascending order.
     * Core 0 will choose xTaskHandles[1]
     * Core 1 will choose xTaskHandles[2]
     * ...
     * Core N-1 will choose xIdleTaskHandles[N-1] since it is the first idle task in ready queue.
     */
    vTaskSuspend( xTaskHandles[ 0 ] );

    /* Verify the suspended task is not running. */
    verifySmpTask( &xTaskHandles[ 0 ], eSuspended, -1 );

    /* Verify all other tasks are in the running state */
    for( i = 1; i < configNUMBER_OF_CORES; i++ )
    {
        verifySmpTask( &xTaskHandles[ i ], eRunning, i - 1 );
    }

    /* Verify the last core will run the last idle task. */
    verifyIdleTask( ( configNUMBER_OF_CORES - 1 ), ( configNUMBER_OF_CORES - 1 ) );

    /* xTaskHandles[0] is resumed from Core 0.
     * 1. prvYieldForTask is called xTaskHandles[0] to find core to run.
     * 2. The cores which is not running idle task and has lower priority than xTaskHandles[0] is request to yield.
     * 3. The core 0 will yield last since it is the core to call the FreeRTOS APIs
     * Core N-1 will not yield since it is already running xIdleTaskHandles[N-1]
     * Other cores will yield in the following order:
     * Tasks will be choosen then idle task in FIFO order
     * Core 1 will choose xTaskHandles[0]
     * Core 2 will choose xIdleTaskHandles[0]
     * ...
     * Core N-2 will choose xIdleTaskHandles[N-4]
     * Core 0 will choose xIdleTaskHandles[N-3]
     */
    vTaskResume( xTaskHandles[ 0 ] );

    /* Verify the high priority task is running */
    xCoreToRunTask = 1;

    if( xCoreToRunTask == ( configNUMBER_OF_CORES - 1 ) )
    {
        /* Core 1 is the last core. Since it is already running the idle task. It
         * won't be request to yield. Core 0 will choose the task to run. */
        xCoreToRunTask = 0;
    }

    verifySmpTask( &xTaskHandles[ 0 ], eRunning, xCoreToRunTask );

    for( i = 1; i < configNUMBER_OF_CORES; i++ )
    {
        /* Verify all other tasks are in the idle state */
        verifySmpTask( &xTaskHandles[ i ], eReady, -1 );
    }

    /* Verify the idle task running status. */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        if( i == xCoreToRunTask )
        {
            /* The core is running task. */
        }
        else if( i == 0 )
        {
            verifyIdleTask( ( configNUMBER_OF_CORES - 3 ), i );
        }
        else if( i == ( configNUMBER_OF_CORES - 1 ) )
        {
            verifyIdleTask( ( configNUMBER_OF_CORES - 1 ), ( configNUMBER_OF_CORES - 1 ) );
        }
        else
        {
            verifyIdleTask( ( ( configNUMBER_OF_CORES + i - 2 ) % configNUMBER_OF_CORES ), i );
        }
    }
}

/**
 * @brief AWS_IoT-FreeRTOS_SMP_TC-23
 * A single task of high priority will be created. A low priority task will be
 * created for each remaining available CPU core. This test will verify that
 * as each low priority task is suspended, the high priority task shall remain
 * in the running state.
 *
 * #define configRUN_MULTIPLE_PRIORITIES                    0
 * #define configUSE_TIME_SLICING                           0
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
 * State - Running (Core 0)	  State - Ready
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
 * State - Running (Core 0)	 State - Ready
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

    /* Verify the high priority task is running */
    verifySmpTask( &xTaskHandles[ 0 ], eRunning, 0 );

    for( i = 1; i < configNUMBER_OF_CORES; i++ )
    {
        /* Verify all other tasks are in the idle state */
        verifySmpTask( &xTaskHandles[ i ], eReady, -1 );

        /* Verify the idle task is running on all other CPU cores */
        verifyIdleTask( i - 1, i );
    }

    for( i = 1; i < configNUMBER_OF_CORES; i++ )
    {
        /* Suspend low priority task */
        vTaskSuspend( xTaskHandles[ i ] );

        /* Verify T0 remains running on core 0 */
        verifySmpTask( &xTaskHandles[ 0 ], eRunning, 0 );

        /* Verify task T[i] is in the deleted state */
        verifySmpTask( &xTaskHandles[ i ], eSuspended, -1 );
    }

    for( i = 1; i < configNUMBER_OF_CORES; i++ )
    {
        /* Resume low priority task */
        vTaskResume( xTaskHandles[ i ] );

        /* Verify T0 remains running on core 0 */
        verifySmpTask( &xTaskHandles[ 0 ], eRunning, 0 );

        /* Verify task T[i] is in the suspended state */
        verifySmpTask( &xTaskHandles[ i ], eReady, -1 );
    }
}

/**
 * @brief AWS_IoT-FreeRTOS_SMP_TC-24
 * A single task of high priority will be created for each available CPU core.
 * An additional low priority task shall be created. This test will verify that
 * when a high priority task is suspended the low priority task will remain in
 * the ready state.
 *
 * #define configRUN_MULTIPLE_PRIORITIES                    0
 * #define configUSE_TIME_SLICING                           0
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
 * Task (TN)	              Task (TN + 1)
 * Priority – 2               Priority – 1
 * State - Running (Core 0)	  State - Ready
 *
 * Suspend tasks (T1)
 *
 * Task (T1)	       Task (TN + 1)
 * Priority – 2        Priority – 1
 * State - Suspended   State - Ready
 *
 * Resume tasks (T1)
 *
 * Task (T1)	             Task (TN)
 * Priority – 2              Priority – 1
 * State - Running (Core 0)	 State - Ready
 */
void test_task_suspend_all_cores_high_priority_suspend( void )
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

    /* Suspend the high priority task */
    vTaskSuspend( xTaskHandles[ 0 ] );

    /* Verify the task is suspended */
    verifySmpTask( &xTaskHandles[ 0 ], eSuspended, -1 );

    /* Verify the idle task is running on core 0 */
    verifyIdleTask( 0, 0 );

    /* Verify all high priority tasks remain running */
    for( i = 1; i < configNUMBER_OF_CORES; i++ )
    {
        verifySmpTask( &xTaskHandles[ i ], eRunning, i );
    }

    /* Resume the high priority task */
    vTaskResume( xTaskHandles[ 0 ] );

    /* Verify all high priority tasks are running */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        verifySmpTask( &xTaskHandles[ i ], eRunning, i );
    }
}

/**
 * @brief AWS_IoT-FreeRTOS_SMP_TC-26
 * A task of equal priority will be created for each available CPU core.
 * An additional task in the ready state shall be created. This test will
 * verify that when a running task is suspended the ready task will move to
 * the running state. When the suspended task is resumed, it shall enter the
 * ready state.
 *
 * #define configRUN_MULTIPLE_PRIORITIES                    0
 * #define configUSE_TIME_SLICING                           0
 * #define configNUMBER_OF_CORES                            (N > 1)
 *
 * This test can be run with FreeRTOS configured for any number of cores
 * greater than 1.
 *
 * Tasks are created prior to starting the scheduler.
 *
 * Task (TN)	  Task (TN + 1)
 * Priority – 1   Priority – 1
 * State - Ready  State - Ready
 *
 * After calling vTaskStartScheduler()
 *
 * Task (TN)	              Task (TN + 1)
 * Priority – 1               Priority – 1
 * State - Running (Core N)	  State - Ready
 *
 * Suspend tasks (T1)
 *
 * Task (T1)	       Task (TN + 1)
 * Priority – 1        Priority – 1
 * State - Suspended   State - Running (Core 0)
 *
 * Resume tasks (T1)
 *
 * Task (T1)	   Task (TN + 1)
 * Priority – 1    Priority – 1
 * State - Ready   State - Running (Core 0)
 */
void test_task_suspend_all_cores_equal_priority_suspend_running( void )
{
    TaskHandle_t xTaskHandles[ configNUMBER_OF_CORES + 1 ] = { NULL };
    uint32_t i;

    /* Create a task for each CPU core at equal priority */
    for( i = 0; i < ( configNUMBER_OF_CORES + 1 ); i++ )
    {
        xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 1, &xTaskHandles[ i ] );
    }

    vTaskStartScheduler();

    /* Verify all tasks are running */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        verifySmpTask( &xTaskHandles[ i ], eRunning, i );
    }

    /* Verify the remaining task is ready */
    verifySmpTask( &xTaskHandles[ i ], eReady, -1 );

    /* Suspend the task on core 0 */
    vTaskSuspend( xTaskHandles[ 0 ] );

    /* Verify the last task is now running on core 0 */
    verifySmpTask( &xTaskHandles[ i ], eRunning, 0 );

    /* Resume the task on core 0 */
    vTaskResume( xTaskHandles[ 0 ] );

    /* Verify task T0 is now in the ready state */
    verifySmpTask( &xTaskHandles[ 0 ], eReady, -1 );
}

/**
 * @brief AWS_IoT-FreeRTOS_SMP_TC-27
 * A task of equal priority will be created for each available CPU core. This
 * test will verify that when a task is blocked the CPU core will execute
 * the idle task.
 *
 * #define configRUN_MULTIPLE_PRIORITIES                    0
 * #define configUSE_TIME_SLICING                           0
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
 * Block task (T1)
 *
 * Task (T1)	        Task (TN)
 * Priority – 1         Priority – 1
 * State - Blocked      State - Running (Core N)
 *
 * Unblock task (T1)
 *
 * Task (TN)
 * Priority – N
 * State - Running (Core N)
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

    /* Verify the task has been blocked */
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
 * @brief AWS_IoT-FreeRTOS_SMP_TC-28
 * A single task of high priority will be created. A low priority task will be
 * created for each remaining available CPU core. The test will first verify
 * that when the high priority task is blocked the low priority tasks will
 * enter the running state. When the high priority task is resumed, each low
 * priority task will return to the ready state.
 *
 * #define configRUN_MULTIPLE_PRIORITIES                    0
 * #define configUSE_TIME_SLICING                           0
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
 * State - Running (Core 0)	  State - Ready
 *
 * Block task (T1)
 *
 * Task (T1)	       Task (TN)
 * Priority – 2        Priority – 1
 * State - Blocked     State - Running (Core N)
 *
 * Unblock task (T1)
 *
 * Task (T1)	                             Task (TN)
 * Priority – 2                              Priority – 1
 * State - Running (First available core)	 State - Ready
 */
void test_task_blocked_all_cores_different_priority_block_high( void )
{
    TaskHandle_t xTaskHandles[ configNUMBER_OF_CORES ] = { NULL };
    uint32_t i, xCoreToRunTask;

    /* Create a single task at high priority */
    xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 2, &xTaskHandles[ 0 ] );

    /* Create all remaining tasks at low priority */
    for( i = 1; i < configNUMBER_OF_CORES; i++ )
    {
        xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 1, &xTaskHandles[ i ] );
    }

    vTaskStartScheduler();

    /* Verify the high priority task is running */
    verifySmpTask( &xTaskHandles[ 0 ], eRunning, 0 );

    for( i = 1; i < configNUMBER_OF_CORES; i++ )
    {
        /* Verify all other tasks are in the idle state */
        verifySmpTask( &xTaskHandles[ i ], eReady, -1 );

        /* Verify the idle task is running on all other CPU cores */
        verifyIdleTask( i - 1, i );
    }

    /* Block task T0 */
    vTaskDelay( 10 );

    /* Verify the task has been blocked */
    verifySmpTask( &xTaskHandles[ 0 ], eBlocked, -1 );

    for( i = 1; i < configNUMBER_OF_CORES; i++ )
    {
        /* Verify all other tasks are in the running state */
        verifySmpTask( &xTaskHandles[ i ], eRunning, i - 1 );
    }

    /* Unblock task T0 */
    xTaskAbortDelay( xTaskHandles[ 0 ] );

    /* Verify the high priority task is running */
    xCoreToRunTask = 1;

    if( xCoreToRunTask == ( configNUMBER_OF_CORES - 1 ) )
    {
        /* Core 1 is the last core. Since it is already running the idle task. It
         * won't be request to yield. Core 0 will choose the task to run. */
        xCoreToRunTask = 0;
    }

    verifySmpTask( &xTaskHandles[ 0 ], eRunning, xCoreToRunTask );

    for( i = 1; i < configNUMBER_OF_CORES; i++ )
    {
        /* Verify all other tasks are in the idle state */
        verifySmpTask( &xTaskHandles[ i ], eReady, -1 );
    }

    /* Verify the idle task running status. */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        if( i == xCoreToRunTask )
        {
            /* The core is running task. */
        }
        else if( i == 0 )
        {
            verifyIdleTask( ( configNUMBER_OF_CORES - 3 ), i );
        }
        else if( i == ( configNUMBER_OF_CORES - 1 ) )
        {
            verifyIdleTask( ( configNUMBER_OF_CORES - 1 ), ( configNUMBER_OF_CORES - 1 ) );
        }
        else
        {
            verifyIdleTask( ( ( configNUMBER_OF_CORES + i - 2 ) % configNUMBER_OF_CORES ), i );
        }
    }
}

/**
 * @brief AWS_IoT-FreeRTOS_SMP_TC-30
 * A single task of high priority will be created for each available CPU core.
 * An additional low priority task shall be created. This test will verify that
 * when a high priority task is blocked the low priority task will remain in
 * the ready state.
 *
 * #define configRUN_MULTIPLE_PRIORITIES                    0
 * #define configUSE_TIME_SLICING                           0
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
 * Task (TN)	              Task (TN + 1)
 * Priority – 2               Priority – 1
 * State - Running (Core 0)	  State - Ready
 *
 * Block tasks (T1)
 *
 * Task (T1)	       Task (TN + 1)
 * Priority – 2        Priority – 1
 * State - Blocked     State - Ready
 *
 * Unblocked tasks (T1)
 *
 * Task (T1)	             Task (TN)
 * Priority – 2              Priority – 1
 * State - Running (Core 0)	 State - Ready
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

    /* Verify the idle task is running on core 0 */
    verifyIdleTask( 0, 0 );

    /* Verify all high priority tasks remain running */
    for( i = 1; i < configNUMBER_OF_CORES; i++ )
    {
        verifySmpTask( &xTaskHandles[ i ], eRunning, i );
    }

    /* Resume the high priority task */
    xTaskAbortDelay( xTaskHandles[ 0 ] );

    /* Verify all high priority tasks are running */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        verifySmpTask( &xTaskHandles[ i ], eRunning, i );
    }
}

/**
 * @brief AWS_IoT-FreeRTOS_SMP_TC-31
 * A task of equal priority will be created for each available CPU core.
 * An additional task in the ready state shall be created. This test will
 * verify that when a running task is blocked the ready task will move to
 * the running state. When the blocked task is resumed, it shall enter the
 * ready state.
 *
 * #define configRUN_MULTIPLE_PRIORITIES                    0
 * #define configUSE_TIME_SLICING                           0
 * #define configNUMBER_OF_CORES                            (N > 1)
 *
 * This test can be run with FreeRTOS configured for any number of cores
 * greater than 1.
 *
 * Tasks are created prior to starting the scheduler.
 *
 * Task (TN)	  Task (TN + 1)
 * Priority – 1   Priority – 1
 * State - Ready  State - Ready
 *
 * After calling vTaskStartScheduler()
 *
 * Task (TN)	              Task (TN + 1)
 * Priority – 1               Priority – 1
 * State - Running (Core N)	  State - Ready
 *
 * Block tasks (T1)
 *
 * Task (T1)	       Task (TN + 1)
 * Priority – 1        Priority – 1
 * State - Blocked     State - Running (Core 0)
 *
 * Unblock tasks (T1)
 *
 * Task (T1)	   Task (TN)
 * Priority – 1    Priority – 1
 * State - Ready   State - Running (Core 0)
 */
void test_task_block_all_cores_equal_priority_block_running( void )
{
    TaskHandle_t xTaskHandles[ configNUMBER_OF_CORES + 1 ] = { NULL };
    uint32_t i;

    /* Create a task for each CPU core at equal priority */
    for( i = 0; i < ( configNUMBER_OF_CORES + 1 ); i++ )
    {
        xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 1, &xTaskHandles[ i ] );
    }

    vTaskStartScheduler();

    /* Verify all tasks are running */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        verifySmpTask( &xTaskHandles[ i ], eRunning, i );
    }

    /* Verify the remaining task is ready */
    verifySmpTask( &xTaskHandles[ i ], eReady, -1 );

    /* Block the task on core 0 */
    vTaskDelay( 10 );

    /* Verify the last task is now running on core 0 */
    verifySmpTask( &xTaskHandles[ i ], eRunning, 0 );

    /* Resume the task on core 0 */
    xTaskAbortDelay( xTaskHandles[ 0 ] );

    /* Verify task T0 is now in the ready state */
    verifySmpTask( &xTaskHandles[ 0 ], eReady, -1 );
}

/**
 * @brief AWS_IoT-FreeRTOS_SMP_TC-108
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
 * State – Running    State – Ready     State – Ready   State – Ready
 *
 * Assuming task TN+1 is holding a mutex. Task TN+1 inherits task T1's priority
 *
 * Task (T1)	      Task (T2)         Task (TN)       Task (TN + 1)
 * Priority – 3       Priority – 2      Priority – 2    Priority – 3
 * State – Running    State – Ready     State – Ready   State – Running
 *                                                      uxMutexesHeld - 1
 *
 * Task TN+1 disinherits task T1's priority.
 *
 * Task (T1)	      Task (T2)         Task (TN)       Task (TN + 1)
 * Priority – 3       Priority – 2      Priority – 2    Priority – 1
 * State – Running    State – Ready     State – Ready   State – Ready
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

    /* Verify the high priority task is running. */
    verifySmpTask( &xTaskHandles[ 0 ], eRunning, 0 );

    /* Verify the medium and low priority tasks are ready. */
    for( i = 1; i < ( configNUMBER_OF_CORES + 1 ); i++ )
    {
        verifySmpTask( &xTaskHandles[ i ], eReady, -1 );
    }

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

    /* Verify the high priority task is running. */
    verifySmpTask( &xTaskHandles[ 0 ], eRunning, 0 );

    /* Verify the medium and low priority tasks are ready. */
    for( i = 1; i < ( configNUMBER_OF_CORES + 1 ); i++ )
    {
        verifySmpTask( &xTaskHandles[ i ], eReady, -1 );
    }
}

/**
 * @brief AWS_IoT-FreeRTOS_SMP_TC-109
 * Task can inherit or disinherit other higher priority task. This test verify that
 * lower priority task will be selected to run when it inherit a higher priority task.
 * The lower priority will be switched out when it is disinherited by higher priority
 * task due to timeout.
 *
 * #define configRUN_MULTIPLE_PRIORITIES                    0
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
 * State – Running    State – Ready     State – Ready   State – Ready
 *
 * Assuming task TN+1 is holding a mutex. Task TN+1 inherits task T1's priority
 *
 * Task (T1)	      Task (T2)         Task (TN)       Task (TN + 1)
 * Priority – 3       Priority – 2      Priority – 2    Priority – 3
 * State – Running    State – Ready     State – Ready   State – Running
 *
 * Task TN+1 is disinherited by task T1 due to timeout
 *
 * Task (T1)	      Task (T2)         Task (TN)       Task (TN + 1)
 * Priority – 3       Priority – 2      Priority – 2    Priority – 1
 * State – Running    State – Ready     State – Ready   State – Ready
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

    /* Verify the high priority task is running. */
    verifySmpTask( &xTaskHandles[ 0 ], eRunning, 0 );

    /* Verify the medium and low priority tasks are ready. */
    for( i = 1; i < ( configNUMBER_OF_CORES + 1 ); i++ )
    {
        verifySmpTask( &xTaskHandles[ i ], eReady, -1 );
    }

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

    /* Verify the high priority task is running. */
    verifySmpTask( &xTaskHandles[ 0 ], eRunning, 0 );

    /* Verify the medium and low priority tasks are ready. */
    for( i = 1; i < ( configNUMBER_OF_CORES + 1 ); i++ )
    {
        verifySmpTask( &xTaskHandles[ i ], eReady, -1 );
    }
}
