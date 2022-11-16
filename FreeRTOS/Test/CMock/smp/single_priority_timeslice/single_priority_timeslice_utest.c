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
/*! @file single_priority_timeslice_utest.c */

/* C runtime includes. */
#include <stdlib.h>
#include <stdbool.h>
#include <stdint.h>
#include <string.h>

/* Tasl includes */
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
 * @brief AWS_IoT-FreeRTOS_SMP_TC-75
 * A task of equal priority will be created for each available CPU core. An
 * additional task will be created in the ready state. This test will verify
 * that as OS ticks are generated the ready task will be made to run on each 
 * CPU core.
 * 
 * #define configRUN_MULTIPLE_PRIORITIES                    0
 * #define configUSE_TIME_SLICING                           1
 * #define configUSE_CORE_AFFINITY                          1
 * #define configNUMBER_OF_CORES                            (N > 1)
 * 
 * This test can be run with FreeRTOS configured for any number of cores greater than 1 .
 * 
 * Tasks are created prior to starting the scheduler.
 * 
 * Task (TN)	    Task (TN + 1)
 * Priority – 1     Priority – 1
 * State - Ready	State - Ready
 * 
 * After calling vTaskStartScheduler()
 * 
 * Task (TN)	               Task (TN + 1)
 * Priority – 1                Priority – 1
 * State - Running (Core N)	   State - Ready
 * 
 * Call xTaskIncrementTick() for each configured CPU core. The kernel will consider CPU 0
 * the core calling the API and therefore will not rotate tasks for that CPU.
 * 
 * Task (TN + 1) when configNUMBER_OF_CORES = 4
 * Tick    Core
 * 1       1
 * 2       2
 * 3       3
 * 4      -1 
 */
void test_timeslice_verification_tasks_equal_priority( void )
{
    TaskHandle_t xTaskHandles[configNUMBER_OF_CORES + 1] = { NULL };
    uint32_t i;

    /* Create configNUMBER_OF_CORES + 1 tasks of equal priority */
    for (i = 0; i < (configNUMBER_OF_CORES + 1); i++) {
        xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 1, &xTaskHandles[i] );
    }
    
    vTaskStartScheduler();

    /* Verify all configNUMBER_OF_CORES tasks are in the running state */
    for (i = 0; i < configNUMBER_OF_CORES; i++) {
        verifySmpTask( &xTaskHandles[i], eRunning, i );
    }

    /* Verify the last task is in the ready state */
    verifySmpTask( &xTaskHandles[i], eReady, -1 );

    /* Generate a tick for each configNUMBER_OF_CORES. This will cause each
       task to be either moved to the ready state or the running state */
    for (i = 0; i < configNUMBER_OF_CORES; i++) {
        
        xTaskIncrementTick();

        int32_t core = i + 1;

        /* Track wrap around to the ready state */
        if (core == configNUMBER_OF_CORES) {
            core = -1;
        }

        /* Verify the last created task runs on each core or enters the ready state */
        verifySmpTask( &xTaskHandles[configNUMBER_OF_CORES], (core == -1) ? eReady : eRunning, core );
    }
}

/**
 * @brief AWS_IoT-FreeRTOS_SMP_TC-76
 * A task of equal priority will be created for each available CPU core
 * except for one. This will leave a CPU core running the idle task. This test
 * will verify that as OS ticks are generated the tasks will remain on the same
 * CPU core.
 * 
 * #define configRUN_MULTIPLE_PRIORITIES                    0
 * #define configUSE_TIME_SLICING                           1
 * #define configUSE_CORE_AFFINITY                          1
 * #define configNUMBER_OF_CORES                            (N > 1)
 * 
 * This test can be run with FreeRTOS configured for any number of cores greater than 1 .
 * 
 * Tasks are created prior to starting the scheduler.
 * 
 * Task (TN - 1)
 * Priority – 1
 * State - Ready
 * 
 * After calling vTaskStartScheduler()
 * 
 * Task (TN - 1)
 * Priority – 1
 * State - Running (Core N - 1)
 * 
 * Call xTaskIncrementTick() for each configured CPU core. The tasks will not change state.
 * 
 * Task (TN - 1)
 * Priority – 1
 * State - Running (Core N - 1)
 */
void test_timeslice_verification_idle_core( void )
{
    TaskHandle_t xTaskHandles[configNUMBER_OF_CORES] = { NULL };
    uint32_t i;

    /* Create configNUMBER_OF_CORES tasks of equal priority */
    for (i = 0; i < (configNUMBER_OF_CORES - 1); i++) {
        xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 1, &xTaskHandles[i] );
    }
    
    vTaskStartScheduler();

    /* Verify all tasks are in the running state prior to incrementing a tick */
    for (i = 0; i < configNUMBER_OF_CORES -1 ; i++) {
        verifySmpTask( &xTaskHandles[i], eRunning, i );
    }

    /* Verify the idle task is running on the last CPU Core */
    verifyIdleTask(0, (configNUMBER_OF_CORES - 1));

    /* Verify all tasks remain in the running state each time a tick is incremented */
    for (i = 0; i < configNUMBER_OF_CORES ; i++) {
        xTaskIncrementTick();

        for (int j = 0; j < configNUMBER_OF_CORES - 1; j++) {
            verifySmpTask( &xTaskHandles[j], eRunning, j );
        }
    }
}

/**
 * @brief AWS_IoT-FreeRTOS_SMP_TC-77
 * A high priority task will be created for each available CPU core. An
 * additional low priority task will be created in the ready state. This test
 * will verify that as OS ticks are generated all CPU cores will remain running
 * their original tasks and the ready task never enters the running state.
 * 
 * #define configRUN_MULTIPLE_PRIORITIES                    0
 * #define configUSE_TIME_SLICING                           1
 * #define configUSE_CORE_AFFINITY                          1
 * #define configNUMBER_OF_CORES                            (N > 1)
 * 
 * This test can be run with FreeRTOS configured for any number of cores greater than 1 .
 * 
 * Tasks are created prior to starting the scheduler.
 * 
 * Task (TN)	    Task (TN + 1)
 * Priority – 2     Priority – 1
 * State - Ready	State - Ready
 * 
 * After calling vTaskStartScheduler()
 * 
 * Task (TN)	              Task (TN + 1)
 * Priority – 2               Priority – 1
 * State - Running (Core N)   State - Ready
 * 
 * Call xTaskIncrementTick() for each configured CPU core. The tasks will not change state.
 * 
 * Task (TN)	              Task (TN + 1)
 * Priority – 2               Priority – 1
 * State - Running (Core N)   State - Ready
 */
void test_timeslice_verification_different_priority_tasks( void )
{
    TaskHandle_t xTaskHandles[configNUMBER_OF_CORES + 1] = { NULL };
    uint32_t i;

    /* Create configNUMBER_OF_CORES tasks of high priority */
    for (i = 0; i < (configNUMBER_OF_CORES); i++) {
        xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 2, &xTaskHandles[i] );
    }
    
    /* Create a single low priority task */
    xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 1, &xTaskHandles[i] );

    vTaskStartScheduler();

    /* Verify all tasks are in the running state */
    for (i = 0; i < configNUMBER_OF_CORES; i++) {
        verifySmpTask( &xTaskHandles[i], eRunning, i );
    }

    /* The remaining task shall be in the ready state */
    verifySmpTask( &xTaskHandles[configNUMBER_OF_CORES], eReady, -1 );

    /* Verify all tasks remain in the running state each time a tick is incremented */
    /* The low priority task should never enter the running state */
    for (i = 0; i < configNUMBER_OF_CORES; i++) {
        xTaskIncrementTick();
        
        for (int j = 0; j < configNUMBER_OF_CORES; j++) {
            verifySmpTask( &xTaskHandles[j], eRunning, j );
        }

        verifySmpTask( &xTaskHandles[configNUMBER_OF_CORES], eReady, -1 );
    }
}

/**
 * @brief AWS_IoT-FreeRTOS_SMP_TC-78
 * A high priority task will be created for each available CPU core. An
 * additional low priority task will be created in the ready state. This test
 * will verify that as OS ticks are generated all CPU cores will remain running
 * their original tasks and the ready task never enters the running state. The
 * test will then increase the priority of the ready task and verify tasks now
 * begin to run on each CPU core.
 * 
 * #define configRUN_MULTIPLE_PRIORITIES                    0
 * #define configUSE_TIME_SLICING                           1
 * #define configUSE_CORE_AFFINITY                          1
 * #define configNUMBER_OF_CORES                            (N > 1)
 * 
 * This test can be run with FreeRTOS configured for any number of cores greater than 1 .
 * 
 * Tasks are created prior to starting the scheduler.
 * 
 * Task (TN)	    Task (TN + 1)
 * Priority – 2     Priority – 1
 * State - Ready	State - Ready
 * 
 * After calling vTaskStartScheduler()
 * 
 * Task (TN)	              Task (TN + 1)
 * Priority – 2               Priority – 1
 * State - Running (Core N)   State - Ready
 * 
 * Call xTaskIncrementTick() for each configured CPU core. The tasks will not change state.
 * 
 * Task (TN)	              Task (TN + 1)
 * Priority – 2               Priority – 1
 * State - Running (Core N)   State - Ready
 * 
 * Raise the priority of task TN + 1 and verify on each tick it executes on a
 * different CPU core
 * 
 * Task (TN + 1) when configNUMBER_OF_CORES = 4
 * Tick    Core
 * 1       3
 * 2      -1
 * 3       2
 * 4       3 
 */
void test_priority_change_tasks_different_priority_raise_to_equal( void )
{
    TaskHandle_t xTaskHandles[configNUMBER_OF_CORES + 1] = { NULL };
    uint32_t i;

    /* Create configNUMBER_OF_CORES tasks of high priority */
    for (i = 0; i < (configNUMBER_OF_CORES); i++) {
        xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 2, &xTaskHandles[i] );
    }

    /* Create a single low priority task */ 
    xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 1, &xTaskHandles[i] );

    vTaskStartScheduler();

    /* Verify all tasks are in the running state */
    for (i = 0; i < configNUMBER_OF_CORES; i++) {
        verifySmpTask( &xTaskHandles[i], eRunning, i );
    }

    /* The remaining task shall be in the ready state */
    verifySmpTask( &xTaskHandles[configNUMBER_OF_CORES], eReady, -1 );

    /* Verify all tasks remain in the running state each time a tick is incremented */
    /* The low priority task should never enter the running state */
    for (i = 0; i < configNUMBER_OF_CORES; i++) {
        xTaskIncrementTick();
        
        for (int j = 0; j < configNUMBER_OF_CORES; j++) {
            verifySmpTask( &xTaskHandles[j], eRunning, j );
        }

        verifySmpTask( &xTaskHandles[configNUMBER_OF_CORES], eReady, -1 );
    }

    /* Raise the priority of the low priority task to match the running tasks */
    vTaskPrioritySet( xTaskHandles[configNUMBER_OF_CORES], 2 );

    /* After the first tick the ready task will be running on the last CPU core */
    int32_t core = (configNUMBER_OF_CORES - 1);

    for (i = 0; i < configNUMBER_OF_CORES; i++) {
        
        xTaskIncrementTick();

        /* Verify the last created task runs on each core or enters the ready state */
        verifySmpTask( &xTaskHandles[configNUMBER_OF_CORES], (core == -1) ? eReady : eRunning, core );

        /* Track wrap around to the ready state */
        if ((i % configNUMBER_OF_CORES) == 0) {
            core = -1;
        } else {
            core = i % configNUMBER_OF_CORES;
        }

        if (core == 0) {
            core = -1;
        }
    }
}

/**
 * @brief AWS_IoT-FreeRTOS_SMP_TC-79
 * A high priority task will be created for each available CPU core. An
 * additional high priority task will be created in the ready state. This test
 * will verify that as OS ticks are generated all tasks will execute on each
 * CPU core. The test will then lower the priority of the last task and verify
 * tasks now remain running on a dedicated CPU core.
 * 
 * #define configRUN_MULTIPLE_PRIORITIES                    0
 * #define configUSE_TIME_SLICING                           1
 * #define configUSE_CORE_AFFINITY                          1
 * #define configNUMBER_OF_CORES                            (N > 1)
 * 
 * This test can be run with FreeRTOS configured for any number of cores greater than 1 .
 * 
 * Tasks are created prior to starting the scheduler.
 * 
 * Task (TN)	    Task (TN + 1)
 * Priority – 2     Priority – 2
 * State - Ready	State - Ready
 * 
 * After calling vTaskStartScheduler()
 * 
 * Task (TN)	              Task (TN + 1)
 * Priority – 2               Priority – 2
 * State - Running (Core N)   State - Ready
 * 
 * Call xTaskIncrementTick() for each configured CPU core. The kernel will consider CPU 0
 * the core calling the API and therefore will not rotate tasks for that CPU.
 * 
 * Task (TN + 1) when configNUMBER_OF_CORES = 4
 * Tick    Core
 * 1       1
 * 2       2
 * 3       3
 * 4      -1 
 * 
 * Lower the priority of task TN + 1
 * 
 * Call xTaskIncrementTick() for each configured CPU core. The tasks will not change state.
 * 
 * Task (TN)	              Task (TN + 1)
 * Priority – 2               Priority – 1
 * State - Running (Core N)   State - Ready
 */
void test_priority_change_tasks_equal_priority( void )
{
    TaskHandle_t xTaskHandles[configNUMBER_OF_CORES + 1] = { NULL };
    uint32_t i;

    /* Create configNUMBER_OF_CORES tasks of equal priority */
    for (i = 0; i < (configNUMBER_OF_CORES); i++) {
        xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 2, &xTaskHandles[i] );
    }
    
    /* Create a single equal priority task */ 
    xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 2, &xTaskHandles[i] );

    vTaskStartScheduler();
    
    /* Verify all tasks are in the running state */
    for (i = 0; i < configNUMBER_OF_CORES; i++) {
        verifySmpTask( &xTaskHandles[i], eRunning, i );
    }

    /* The remaining task shall be in the ready state */
    verifySmpTask( &xTaskHandles[configNUMBER_OF_CORES], eReady, -1 );

    /* After the first tick the ready task will be running on CPU core 1 */
    int32_t core = 1;

    for (i = 0; i < configNUMBER_OF_CORES; i++) {
        
        xTaskIncrementTick();

        /* Verify the last created task runs on each core or enters the ready state */
        verifySmpTask( &xTaskHandles[configNUMBER_OF_CORES], (core == -1) ? eReady : eRunning, core );

        /* Track wrap around to the ready state */
        if ((i % configNUMBER_OF_CORES) == (configNUMBER_OF_CORES - 2)) {
            core = -1;
        } else {
            core = (i % configNUMBER_OF_CORES) + 2;
        }

        if ((i % configNUMBER_OF_CORES) == (configNUMBER_OF_CORES - 1)) {
            core = 1;
        }
    }

    /* Lower the priority of task T0 */
    vTaskPrioritySet( xTaskHandles[configNUMBER_OF_CORES], 1 );

    /* Verify all configNUMBER_OF_CORES tasks are in the running state */
    for (i = 0; i < configNUMBER_OF_CORES; i++) {
        xTaskIncrementTick();
        
        for (int j = 0; j < configNUMBER_OF_CORES; j++) {
            verifySmpTask( &xTaskHandles[j], eRunning, j );
        }

        /* Verify the low priority task remains in the ready state */
        verifySmpTask( &xTaskHandles[configNUMBER_OF_CORES], eReady, -1 );
    }
}

/**
 * @brief AWS_IoT-FreeRTOS_SMP_TC-80
 * A task will be created for each available CPU core. This test will verify that as
 * OS ticks are generated all tasks will execute on a fixed CPU core. A new task
 * will be created. The test will then verify tasks now execute on each
 * available CPU core. 
 * 
 * #define configRUN_MULTIPLE_PRIORITIES                    0
 * #define configUSE_TIME_SLICING                           1
 * #define configUSE_CORE_AFFINITY                          1
 * #define configNUMBER_OF_CORES                            (N > 1)
 * 
 * This test can be run with FreeRTOS configured for any number of cores greater than 1 .
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
 * Priority – 2
 * State - Running (Core N)
 * 
 * Call xTaskIncrementTick() for each configured CPU core. The tasks will not change state.
 * 
 * Task (TN)
 * Priority – 2
 * State - Running (Core N)
 * 
 * Create a new task
 * 
 * Call xTaskIncrementTick() for each configured CPU core. The kernel will consider CPU 0
 * the core calling the API and therefore will not rotate tasks for that CPU.
 * 
 * Task (TN + 1) when configNUMBER_OF_CORES = 4
 * Tick    Core
 * 1       -1
 * 2       1
 * 3       2
 * 4       3 
 */
void test_task_create_tasks_equal_priority( void )
{
    TaskHandle_t xTaskHandles[configNUMBER_OF_CORES + 1] = { NULL };
    uint32_t i;

    /* Create configNUMBER_OF_CORES tasks of equal priority */
    for (i = 0; i < (configNUMBER_OF_CORES); i++) {
        xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 1, &xTaskHandles[i] );
    }

    vTaskStartScheduler();

    /* Verify all tasks remain in the running state each time a tick is incremented */
    for (i = 0; i < configNUMBER_OF_CORES; i++) {
        xTaskIncrementTick();
        
        for (int j = 0; j < configNUMBER_OF_CORES; j++) {
            verifySmpTask( &xTaskHandles[j], eRunning, j );
        }
    } 

    /* Create a new task of equal priority */
    xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 1, &xTaskHandles[configNUMBER_OF_CORES] );

    /* The new task will begin in the ready state */
    int32_t core = -1;

    /* Verify the last created task runs on each core or enters the ready state */
    for (i = 0; i < configNUMBER_OF_CORES; i++) {
        
        xTaskIncrementTick();

        verifySmpTask( &xTaskHandles[configNUMBER_OF_CORES], (core == -1) ? eReady : eRunning, core );

        /* Track wrap around to the ready state */
        if ((i % configNUMBER_OF_CORES) == (configNUMBER_OF_CORES - 1)) {
            core = -1;
        } else {
            core = (i % configNUMBER_OF_CORES) + 1;
        }

        if ((i % configNUMBER_OF_CORES) == 0) {
            core = 1;
        }
    }
}

/**
 * @brief AWS_IoT-FreeRTOS_SMP_TC-81
 * A high priority task will be created for each available CPU core. This test
 * will verify that as OS ticks are generated all tasks will execute on a fixed
 * CPU core. A new low priority task will be created. The test will then verify 
 * the tasks remain executing on the original CPU cores and do not rotate.
 * 
 * #define configRUN_MULTIPLE_PRIORITIES                    0
 * #define configUSE_TIME_SLICING                           1
 * #define configUSE_CORE_AFFINITY                          1
 * #define configNUMBER_OF_CORES                            (N > 1)
 * 
 * This test can be run with FreeRTOS configured for any number of cores greater than 1 .
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
 * Call xTaskIncrementTick() for each configured CPU core. The tasks will not change state.
 * 
 * Task (TN)
 * Priority – 2
 * State - Running (Core N)
 * 
 * Create a new low priority task
 * 
 * Call xTaskIncrementTick() for each configured CPU core. The kernel will consider CPU 0
 * the core calling the API and therefore will not rotate tasks for that CPU.
 * 
 * Task (TN)                  Task (TN + 1)
 * Priority – 2               Priority – 1
 * State - Running (Core N)   State - Ready
 */
void test_task_create_tasks_lower_priority( void )
{
    TaskHandle_t xTaskHandles[configNUMBER_OF_CORES + 1] = { NULL };
    uint32_t i;

    /* Create configNUMBER_OF_CORES tasks of equal priority */
    for (i = 0; i < (configNUMBER_OF_CORES); i++) {
        xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 2, &xTaskHandles[i] );
    }

    vTaskStartScheduler();

    /* Verify all tasks remain in the running state each time a tick is incremented */
    for (i = 0; i < configNUMBER_OF_CORES; i++) {
        xTaskIncrementTick();
        
        for (int j = 0; j < configNUMBER_OF_CORES; j++) {
            verifySmpTask( &xTaskHandles[j], eRunning, j );
        }
    } 

    /* Create a new low priority task */
    xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 1, &xTaskHandles[configNUMBER_OF_CORES] );

    /* Verify all tasks remain in the running state each time a tick is incremented */
    for (i = 0; i < configNUMBER_OF_CORES; i++) {
        xTaskIncrementTick();
        
        for (int j = 0; j < configNUMBER_OF_CORES; j++) {
            verifySmpTask( &xTaskHandles[j], eRunning, j );
        }
    } 
}

/**
 * @brief AWS_IoT-FreeRTOS_SMP_TC-82
 * A high priority task will be created for each available CPU core. An
 * additional high priority task will be created in the ready state. This test
 * will verify that as OS ticks are generated all tasks will execute on each
 * CPU core. A task will be deleted. The test will then verify the tasks remain
 * executing on fixed CPU cores and do not rotate.
 * 
 * #define configRUN_MULTIPLE_PRIORITIES                    0
 * #define configUSE_TIME_SLICING                           1
 * #define configUSE_CORE_AFFINITY                          1
 * #define configNUMBER_OF_CORES                            (N > 1)
 * 
 * This test can be run with FreeRTOS configured for any number of cores greater than 1 .
 * 
 * Tasks are created prior to starting the scheduler.
 * 
 * Task (TN)      Task (TN + 1)
 * Priority – 2   Priority – 2
 * State - Ready  State - Ready
 * 
 * After calling vTaskStartScheduler()
 * 
 * Task (TN)                  Task (TN + 1)
 * Priority – 2               Priority – 2
 * State - Running (Core N)   State - Ready
 * 
 * Call xTaskIncrementTick() for each configured CPU core. The kernel will consider CPU 0
 * the core calling the API and therefore will not rotate tasks for that CPU.
 * 
 * Task (TN + 1) when configNUMBER_OF_CORES = 4
 * Tick    Core
 * 1       1
 * 2       2
 * 3       3
 * 4      -1 
 * 
 * Delete the last created task
 * 
 * Call xTaskIncrementTick() for each configured CPU core. The tasks will not change state.
 * 
 */
void test_task_delete_tasks_equal_priorities_delete_running_task( void )
{
    TaskHandle_t xTaskHandles[configNUMBER_OF_CORES + 1] = { NULL };
    uint32_t i;

    /* Create configNUMBER_OF_CORES tasks of equal priority */
    for (i = 0; i < (configNUMBER_OF_CORES); i++) {
        xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 2, &xTaskHandles[i] );
    }

    /* Create a single equal priority task */ 
    xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 2, &xTaskHandles[i] );

    vTaskStartScheduler();

    /* Verify all tasks are in the running state */
    for (i = 0; i < configNUMBER_OF_CORES; i++) {
        verifySmpTask( &xTaskHandles[i], eRunning, i );
    }

    /* The remaining task shall be in the ready state */
    verifySmpTask( &xTaskHandles[configNUMBER_OF_CORES], eReady, -1 );

    /* After the first tick the ready task will be running on CPU core 1 */
    int32_t core = 1;

    for (i = 0; i < configNUMBER_OF_CORES; i++) {
        
        xTaskIncrementTick();

        /* Verify the last created task runs on each core or enters the ready state */
        verifySmpTask( &xTaskHandles[configNUMBER_OF_CORES], (core == -1) ? eReady : eRunning, core );

        /* Track wrap around to the ready state */
        if ((i % configNUMBER_OF_CORES) == (configNUMBER_OF_CORES - 2)) {
            core = -1;
        } else {
            core = (i % configNUMBER_OF_CORES) + 2;
        }

        if ((i % configNUMBER_OF_CORES) == (configNUMBER_OF_CORES - 1)) {
            core = 1;
        }
    }

    /* Delete last task */
    vTaskDelete(xTaskHandles[configNUMBER_OF_CORES]);

    /* Verify all configNUMBER_OF_CORES tasks are in the running state */
    for (i = 0; i < configNUMBER_OF_CORES; i++) {
        xTaskIncrementTick();
        
        for (int j = 0; j < configNUMBER_OF_CORES; j++) {
            verifySmpTask( &xTaskHandles[j], eRunning, j );
        }
    } 
}

/**
 * @brief AWS_IoT-FreeRTOS_SMP_TC-83
 * A high priority task will be created for each available CPU core. An
 * additional high priority task will be created in the ready state. This test
 * will verify that as OS ticks are generated all tasks will execute on each
 * CPU core. A task will be suspended. The test will then verify the tasks remain
 * executing on fixed CPU cores and do not rotate. When the suspended task is
 * resumed it will begin executing on each CPU core on each tick.
 * 
 * #define configRUN_MULTIPLE_PRIORITIES                    0
 * #define configUSE_TIME_SLICING                           1
 * #define configUSE_CORE_AFFINITY                          1
 * #define configNUMBER_OF_CORES                            (N > 1)
 * 
 * This test can be run with FreeRTOS configured for any number of cores greater than 1 .
 * 
 * Tasks are created prior to starting the scheduler.
 * 
 * Task (TN)      Task (TN + 1)
 * Priority – 2   Priority – 2
 * State - Ready  State - Ready
 * 
 * After calling vTaskStartScheduler()
 * 
 * Task (TN)                  Task (TN + 1)
 * Priority – 2               Priority – 2
 * State - Running (Core N)   State - Ready
 * 
 * Call xTaskIncrementTick() for each configured CPU core. The kernel will consider CPU 0
 * the core calling the API and therefore will not rotate tasks for that CPU.
 * 
 * Task (TN + 1) when configNUMBER_OF_CORES = 4
 * Tick    Core
 * 1       1
 * 2       2
 * 3       3
 * 4      -1 
 * 
 * Suspend the last created task
 * 
 * Call xTaskIncrementTick() for each configured CPU core. The tasks will not change state.
 * 
 * Resume the suspended task. The tasks will now rotate to each CPU on each tick.
 */
void test_task_suspend_running_task( void )
{
    TaskHandle_t xTaskHandles[configNUMBER_OF_CORES + 1] = { NULL };
    uint32_t i;

    /* Create configNUMBER_OF_CORES tasks of equal priority */
    for (i = 0; i < (configNUMBER_OF_CORES); i++) {
        xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 2, &xTaskHandles[i] );
    }

    /* Create a single equal priority task */ 
    xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 2, &xTaskHandles[i] );

    vTaskStartScheduler();
    
    /* Verify all tasks are in the running state */
    for (i = 0; i < configNUMBER_OF_CORES; i++) {
        verifySmpTask( &xTaskHandles[i], eRunning, i );
    }

    /* The remaining task shall be in the ready state */
    verifySmpTask( &xTaskHandles[configNUMBER_OF_CORES], eReady, -1 );

    /* After the first tick the ready task will be running on CPU core 1 */
    int32_t core = 1;

    for (i = 0; i < configNUMBER_OF_CORES; i++) {
        
        xTaskIncrementTick();

        /* Verify the last created task runs on each core or enters the ready state */
        verifySmpTask( &xTaskHandles[configNUMBER_OF_CORES], (core == -1) ? eReady : eRunning, core );

        /* Track wrap around to the ready state */
        if ((i % configNUMBER_OF_CORES) == (configNUMBER_OF_CORES - 2)) {
            core = -1;
        } else {
            core = (i % configNUMBER_OF_CORES) + 2;
        }

        if ((i % configNUMBER_OF_CORES) == (configNUMBER_OF_CORES - 1)) {
            core = 1;
        }
    }

    /* Suspend last task */
    vTaskSuspend(xTaskHandles[configNUMBER_OF_CORES]);

    /* Verify all tasks remain in the running state each time a tick is incremented */
    for (i = 0; i < configNUMBER_OF_CORES; i++) {
        xTaskIncrementTick();
        
        for (int j = 0; j < configNUMBER_OF_CORES; j++) {
            verifySmpTask( &xTaskHandles[j], eRunning, j );
        }
    }

    /* Resume suspended task */
    vTaskResume(xTaskHandles[configNUMBER_OF_CORES]);

    /* After the first tick the ready task will be running on the last CPU core */
    core = (configNUMBER_OF_CORES -1);

    for (i = 0; i < configNUMBER_OF_CORES; i++) {
    
        xTaskIncrementTick();

        verifySmpTask( &xTaskHandles[configNUMBER_OF_CORES], (core == -1) ? eReady : eRunning, core );

        if ((i % configNUMBER_OF_CORES) == 0) {
            core = -1;
        } else {
            core = (i % configNUMBER_OF_CORES);
        }

        if ((i % configNUMBER_OF_CORES) == configNUMBER_OF_CORES) {
            core = 1;
        }
    }
}

/**
 * @brief AWS_IoT-FreeRTOS_SMP_TC-84
 * A high priority task will be created for each available CPU core. An
 * additional high priority task will be created in the ready state. This test
 * will verify that as OS ticks are generated all tasks will execute on each
 * CPU core. A task will be blocked. The test will then verify the tasks remain
 * executing on fixed CPU cores and do not rotate.
 * 
 * #define configRUN_MULTIPLE_PRIORITIES                    0
 * #define configUSE_TIME_SLICING                           1
 * #define configUSE_CORE_AFFINITY                          1
 * #define configNUMBER_OF_CORES                            (N > 1)
 * 
 * This test can be run with FreeRTOS configured for any number of cores greater than 1 .
 * 
 * Tasks are created prior to starting the scheduler.
 * 
 * Task (TN)      Task (TN + 1)
 * Priority – 2   Priority – 2
 * State - Ready  State - Ready
 * 
 * After calling vTaskStartScheduler()
 * 
 * Task (TN)                  Task (TN + 1)
 * Priority – 2               Priority – 2
 * State - Running (Core N)   State - Ready
 * 
 * Call xTaskIncrementTick() for each configured CPU core. The kernel will consider
 * CPU 0 the core calling the API and therefore will not rotate tasks for that CPU.
 * 
 * Task (TN + 1) when configNUMBER_OF_CORES = 4
 * Tick    Core
 * 1       1
 * 2       2
 * 3       3
 * 4      -1
 * 
 * Suspend the last created task
 * 
 * Call xTaskIncrementTick() for each configured CPU core. The tasks will not
 * change state.
 */
void test_task_block_running_task( void )
{
    TaskHandle_t xTaskHandles[configNUMBER_OF_CORES + 1] = { NULL };
    uint32_t i;

    /* Create configNUMBER_OF_CORES tasks of equal priority */
    for (i = 0; i < (configNUMBER_OF_CORES); i++) {
        xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 2, &xTaskHandles[i] );
    }

    /* Create a single equal priority task */   
    xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 2, &xTaskHandles[i] );

    vTaskStartScheduler();

    /* Verify all tasks are in the running state */
    for (i = 0; i < configNUMBER_OF_CORES; i++) {
        verifySmpTask( &xTaskHandles[i], eRunning, i );
    }

    /* The remaining task shall be in the ready state */
    verifySmpTask( &xTaskHandles[configNUMBER_OF_CORES], eReady, -1 );

    /* After the first tick the ready task will be running on CPU core 1 */
    int32_t core = 1;

    for (i = 0; i < configNUMBER_OF_CORES; i++) {
        
        xTaskIncrementTick();

        /* Verify the last created task runs on each core or enters the ready state */
        verifySmpTask( &xTaskHandles[configNUMBER_OF_CORES], (core == -1) ? eReady : eRunning, core );

        /* Track wrap around to the ready state */
        if ((i % configNUMBER_OF_CORES) == (configNUMBER_OF_CORES - 2)) {
            core = -1;
        } else {
            core = (i % configNUMBER_OF_CORES) + 2;
        }

        if ((i % configNUMBER_OF_CORES) == (configNUMBER_OF_CORES - 1)) {
            core = 1;
        }
    }

    /* Block last task */
    vTaskDelay(configNUMBER_OF_CORES);

    /* Verify all configNUMBER_OF_CORES tasks are in the running state */
    for (i = 0; i < configNUMBER_OF_CORES; i++) {
        xTaskIncrementTick();
        
        for (int j = 1; j < configNUMBER_OF_CORES -1 ; j++) {
            verifySmpTask( &xTaskHandles[j], eRunning, j );
        }
    }
}

/**
 * @brief AWS_IoT-FreeRTOS_SMP_TC-85
 * A high priority task will be created for each available CPU core. An
 * additional high priority task will be created with affinity for the larget
 * numbered CPU core. This test will verify that as OS ticks are generated the
 * task with CPU affinity will either be in the ready state or running on the 
 * specified CPU core.
 * 
 * #define configRUN_MULTIPLE_PRIORITIES                    0
 * #define configUSE_TIME_SLICING                           1
 * #define configUSE_CORE_AFFINITY                          1
 * #define configNUMBER_OF_CORES                            (N > 1)
 * 
 * This test can be run with FreeRTOS configured for any number of cores greater than 1 .
 * 
 * Tasks are created prior to starting the scheduler.
 * 
 * Task (TN)        Task (TN + 1)
 * Priority – 2     Priority – 2
 * Affinity – None  Affinity – Last CPU Core 
 * State - Ready    State - Ready
 * 
 * After calling vTaskStartScheduler()
 * 
 * Task (TN)        Task (TN + 1)
 * Priority – 2     Priority – 2
 * Affinity – None  Affinity – Last CPU Core 
 * State - Running  State - Ready
 * 
 * Call xTaskIncrementTick() for each configured CPU core. The kernel will consider
 * CPU 0 the core calling the API and therefore will not rotate tasks for that CPU.
 * 
 * Task (TN + 1) when configNUMBER_OF_CORES = 4
 * Tick    Core
 * 1       3
 * 2       -1
 * 3       3
 * 4      -1
 * 
 */
void test_task_affinity_verification( void )
{
    TaskHandle_t xTaskHandles[configNUMBER_OF_CORES + 1] = { NULL };
    uint32_t i;

    /* Create configNUMBER_OF_CORES tasks of equal priority */
    for (i = 0; i < (configNUMBER_OF_CORES); i++) {
        xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 2, &xTaskHandles[i] );
    }
        
    /* Create a single equal priority task with core affinity for the last CPU core */
    xTaskCreateAffinitySet( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 2, (1 << (configNUMBER_OF_CORES - 1)), &xTaskHandles[i] );

    vTaskStartScheduler();

    /* Verify all tasks are in the running state */
    for (i = 0; i < configNUMBER_OF_CORES; i++) {
        verifySmpTask( &xTaskHandles[i], eRunning, i );
    }

    /* The remaining task shall be in the ready state */
    verifySmpTask( &xTaskHandles[configNUMBER_OF_CORES], eReady, -1 );

    for (i = 0; i < configNUMBER_OF_CORES; i++) {
        
        xTaskIncrementTick();

        /* Verify the task is either in the ready state or running on the last CPU core */
        int32_t core = (i % 2 == 0) ? (configNUMBER_OF_CORES - 1) : -1;

        verifySmpTask( &xTaskHandles[configNUMBER_OF_CORES], (core == -1) ? eReady : eRunning, core );
    }
}

/**
 * @brief AWS_IoT-FreeRTOS_SMP_TC-86
 * A high priority task will be created for each available CPU core. An
 * additional high priority task will be created in the ready state. This test
 * will verify that as OS ticks are generated all tasks will execute on each
 * CPU core. The test will then set the last task to have affinity for the last
 * CPU core. The last task will only run on the last CPU core or be in the ready
 * state.
 * 
 * #define configRUN_MULTIPLE_PRIORITIES                    0
 * #define configUSE_TIME_SLICING                           1
 * #define configUSE_CORE_AFFINITY                          1
 * #define configNUMBER_OF_CORES                            (N > 1)
 * 
 * This test can be run with FreeRTOS configured for any number of cores greater than 1 .
 * 
 * Tasks are created prior to starting the scheduler.
 * 
 * Task (TN)        Task (TN + 1)
 * Priority – 2     Priority – 2
 * Affinity – None  Affinity – None
 * State - Ready    State - Ready
 * 
 * After calling vTaskStartScheduler()
 * 
 * Task (TN)        Task (TN + 1)
 * Priority – 2     Priority – 2
 * Affinity – None  Affinity – None 
 * State - Running  State - Ready
 * 
 * Call xTaskIncrementTick() for each configured CPU core. The kernel will consider
 * CPU 0 the core calling the API and therefore will not rotate tasks for that CPU.
 * 
 * Task (TN + 1) when configNUMBER_OF_CORES = 4
 * Tick    Core
 * 1       1
 * 2       2
 * 3       3
 * 4      -1
 * 
 * Set affinity for the last task to the last CPU core.
 * 
 * Task (TN)        Task (TN + 1)
 * Priority – 2     Priority – 2
 * Affinity – None  Affinity – Last CPU Core 
 * State - Running  State - Ready
 * 
 * Verify the task only runs on the specified core or is in the ready state.
 * 
 * Task (TN + 1) when configNUMBER_OF_CORES = 4
 * Tick    Core
 * 1       3
 * 2      -1
 * 3       3
 * 4      -1
 */
void test_task_affinity_set_affinity_running_task( void )
{
    TaskHandle_t xTaskHandles[configNUMBER_OF_CORES + 1] = { NULL };
    uint32_t i;

    /* Create configNUMBER_OF_CORES tasks of equal priority */
    for (i = 0; i < (configNUMBER_OF_CORES); i++) {
        xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 2, &xTaskHandles[i] );
    }

    /* Create a single equal priority task */   
    xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 2, &xTaskHandles[i] );

    vTaskStartScheduler();

    /* Verify all tasks are in the running state */
    for (i = 0; i < configNUMBER_OF_CORES; i++) {
        verifySmpTask( &xTaskHandles[i], eRunning, i );
    }

    /* The remaining task shall be in the ready state */
    verifySmpTask( &xTaskHandles[configNUMBER_OF_CORES], eReady, -1 );

    /* After the first tick the ready task will be running on CPU core 1 */
    int32_t core = 1;

    for (i = 0; i < configNUMBER_OF_CORES; i++) {
        
        xTaskIncrementTick();

        /* Verify the last created task runs on each core or enters the ready state */
        verifySmpTask( &xTaskHandles[configNUMBER_OF_CORES], (core == -1) ? eReady : eRunning, core );

        /* Track wrap around to the ready state */
        if ((i % configNUMBER_OF_CORES) == (configNUMBER_OF_CORES - 2)) {
            core = -1;
        } else {
            core = (i % configNUMBER_OF_CORES) + 2;
        }

        if ((i % configNUMBER_OF_CORES) == (configNUMBER_OF_CORES - 1)) {
            core = 1;
        }
    }

    /* Set CPU core affinity on the last task for the last CPU core */
    vTaskCoreAffinitySet(xTaskHandles[configNUMBER_OF_CORES], 1 << ((configNUMBER_OF_CORES - 1)) );

    for (i = 0; i < configNUMBER_OF_CORES; i++) {
        
        xTaskIncrementTick();

        /* Verify the task is either in the ready state or running on the last CPU core */
        core = (i % 2 == 0) ? (configNUMBER_OF_CORES - 1) : -1 ;

        verifySmpTask( &xTaskHandles[configNUMBER_OF_CORES], (core == -1) ? eReady : eRunning, core );
    }
}
