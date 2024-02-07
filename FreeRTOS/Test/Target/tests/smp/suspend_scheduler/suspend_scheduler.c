/*
 * FreeRTOS V202212.00
 * Copyright (C) 2022 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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

/**
 * @file suspend_scheduler.c
 * @brief Context switch shall not happen when the scheduler is suspended.
 *
 * Procedure:
 *   - Create 1 low priority task, T0.
 *   - Create n - 1 medium priority task, T1 ~ T(n - 1).
 *   - Suspend the scheduler in testRunner.
 *   - Increase T0's priority to high priority.
 *   - Verify that T0 is not running.
 *   - Resume the scheduler in testRunner.
 *   - Verify that T0 is running.
 * Expected:
 *   - T0 won't run even set higher priority when scheduler is suspended.
 */

/* Standard includes. */
#include <stdint.h>

/* Kernel includes. */
#include "FreeRTOS.h" /* Must come first. */
#include "task.h"     /* RTOS task related API prototypes. */

#include "unity.h"    /* unit testing support functions */
/*-----------------------------------------------------------*/

/**
 * @brief Time to wait for other cores to run.
 */
#define TEST_BUSY_LOOPING_COUNT    ( 10000 )

/**
 * @brief Nop operation for busy looping.
 */
#ifdef portNOP
    #define TEST_NOP    portNOP
#else
    #define TEST_NOP()    __asm volatile ( "nop" )
#endif

/*-----------------------------------------------------------*/

/**
 * @brief Task function for T0.
 */
static void prvPriorityChangeTask( void * pvParameters );

/**
 * @brief Task function for other tasks to occupy the core.
 */
static void prvBusyRunningTask( void * pvParameters );

/**
 * @brief Test case "Suspend Scheduler".
 */
void Test_SuspendScheduler( void );
/*-----------------------------------------------------------*/

#if ( configNUMBER_OF_CORES < 2 )
    #error This test is for FreeRTOS SMP and therefore, requires at least 2 cores.
#endif /* if ( configNUMBER_OF_CORES < 2 ) */

#if ( configRUN_MULTIPLE_PRIORITIES != 1 )
    #error test_config.h must be included at the end of FreeRTOSConfig.h.
#endif /* if ( configRUN_MULTIPLE_PRIORITIES != 1 ) */

#if ( configMAX_PRIORITIES <= 3 )
    #error configMAX_PRIORITIES must be larger than 3 to avoid scheduling idle tasks unexpectedly.
#endif /* if ( configMAX_PRIORITIES <= 3 ) */
/*-----------------------------------------------------------*/

/**
 * @brief Handles of the tasks created in this test.
 */
static TaskHandle_t xTaskHandles[ configNUMBER_OF_CORES ];

/**
 * @brief A flag to indicate if T0 run.
 */
static volatile BaseType_t xTaskIsRunning = pdFALSE;
/*-----------------------------------------------------------*/

static void prvPriorityChangeTask( void * pvParameters )
{
    /* pvParameters is not used in this task. */
    ( void ) pvParameters;

    /* Set the flag to indicate that the test task is running. */
    xTaskIsRunning = pdTRUE;

    /* Busy looping here to occupy the core. */
    for( ; ; )
    {
        TEST_NOP();
    }
}
/*-----------------------------------------------------------*/

static void prvBusyRunningTask( void * pvParameters )
{
    /* pvParameters is not used in this task. */
    ( void ) pvParameters;

    /* Busy looping here to occupy the core. */
    for( ; ; )
    {
        TEST_NOP();
    }
}
/*-----------------------------------------------------------*/

void Test_SuspendScheduler( void )
{
    uint32_t i;
    BaseType_t xTestTaskRunningStatus;
    BaseType_t xTaskCreationResult;

    /* Create configNUMBER_OF_CORES - 1 busy running tasks with medium priority. */
    for( i = 0; i < ( configNUMBER_OF_CORES - 1 ); i++ )
    {
        xTaskCreationResult = xTaskCreate( prvBusyRunningTask,
                                           "BusyRun",
                                           configMINIMAL_STACK_SIZE,
                                           NULL,
                                           configMAX_PRIORITIES - 2,
                                           &xTaskHandles[ i ] );

        TEST_ASSERT_EQUAL_MESSAGE( pdPASS, xTaskCreationResult, "Task creation failed." );
    }

    /* Create the test task with lower priority. */
    xTaskCreationResult = xTaskCreate( prvPriorityChangeTask,
                                       "TestTask",
                                       configMINIMAL_STACK_SIZE,
                                       NULL,
                                       configMAX_PRIORITIES - 3,
                                       &xTaskHandles[ configNUMBER_OF_CORES - 1 ] );

    TEST_ASSERT_EQUAL_MESSAGE( pdPASS, xTaskCreationResult, "Task creation failed." );

    /* Busy loop here to wait for other cores. */
    for( i = 0; i < TEST_BUSY_LOOPING_COUNT; i++ )
    {
        TEST_NOP();
    }

    /* Verify that the test task is not running. TestRunner and T1 ~ T(n - 1)
     * has higher priority than T0. Scheduler won't select T0 to run. */
    TEST_ASSERT_EQUAL( pdFALSE, xTaskIsRunning );

    /* Raise the priority of T0 when scheduler suspended. T0 has higher priority than
     * other busy running tasks. However, the schduler is suspended. T0 should not preempt
     * any busy running task. */
    vTaskSuspendAll();
    {
        /* Raise the test task priority. */
        vTaskPrioritySet( xTaskHandles[ configNUMBER_OF_CORES - 1 ], configMAX_PRIORITIES - 1 );

        /* Busy looping here to wait for other cores. */
        for( i = 0; i < TEST_BUSY_LOOPING_COUNT; i++ )
        {
            TEST_NOP();
        }

        /* Verify the status later to prevent test framework jump to tearDown function. */
        xTestTaskRunningStatus = xTaskIsRunning;
    }
    ( void ) xTaskResumeAll();

    /* Verify that the test task is not scheduled when scheduler is suspended. */
    TEST_ASSERT_EQUAL( pdFALSE, xTestTaskRunningStatus );

    /* Busy looping here to wait for other cores. */
    for( i = 0; i < TEST_BUSY_LOOPING_COUNT; i++ )
    {
        TEST_NOP();
    }

    /* Verify that the test task is scheduled after resuming the scheduler. */
    TEST_ASSERT_EQUAL( pdTRUE, xTaskIsRunning );
}
/*-----------------------------------------------------------*/

/* Runs before every test, put init calls here. */
void setUp( void )
{
    uint32_t i;

    xTaskIsRunning = pdFALSE;

    /* Create configNUMBER_OF_CORES - 1 busy running tasks with medium priority. */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        xTaskHandles[ i ] = NULL;
    }
}
/*-----------------------------------------------------------*/

/* Runs after every test, put clean-up calls here. */
void tearDown( void )
{
    uint32_t i;

    /* Delete all the tasks. */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        if( xTaskHandles[ i ] != NULL )
        {
            vTaskDelete( xTaskHandles[ i ] );
            xTaskHandles[ i ] = NULL;
        }
    }
}
/*-----------------------------------------------------------*/

/**
 * @brief A start entry for test runner to run suspend scheduler test.
 */
void vRunSuspendSchedulerTest( void )
{
    UNITY_BEGIN();

    RUN_TEST( Test_SuspendScheduler );

    UNITY_END();
}
/*-----------------------------------------------------------*/
