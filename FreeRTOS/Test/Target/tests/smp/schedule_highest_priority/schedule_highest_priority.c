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
 * @file schedule_highest_priority.c
 * @brief The scheduler shall correctly schedule the highest priority ready tasks.
 *
 * Procedure:
 *   - Create ( num of cores ) tasks ( T0~Tn-1 ). Priority T0 > T1 > ... > Tn-2 > Tn-1.
 *   - for each task Ti in [T0..Tn-1]:
 *      - Tasks T0..Ti-1 are running. If any of the task in T0..Ti-1 is not
 *        running notify the test runner task about error.
 *      - If i == n -1:
 *          - Notify test runner task about success.
 * Expected:
 *   - When a task runs, all tasks of higher priority are running.
 */

/* Standard includes. */
#include <stdint.h>

/* Kernel includes. */
#include "FreeRTOS.h"
#include "task.h"

/* Unit testing support functions. */
#include "unity.h"
/*-----------------------------------------------------------*/

#if ( configNUMBER_OF_CORES < 2 )
    #error This test is for FreeRTOS SMP and therefore, requires at least 2 cores.
#endif /* #if ( configNUMBER_OF_CORES < 2 ) */

#if ( configMAX_PRIORITIES <= configNUMBER_OF_CORES )
    #error This test creates tasks with different priority, requires configMAX_PRIORITIES to be larger than configNUMBER_OF_CORES.
#endif /* #if ( configMAX_PRIORITIES <= configNUMBER_OF_CORES ) */
/*-----------------------------------------------------------*/

/**
 * @brief Timeout value to stop test.
 */
#define TEST_TIMEOUT_MS    ( 10000U )

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
 * @brief Function that implements a never blocking FreeRTOS task.
 */
static void prvEverRunningTask( void * pvParameters );
/*-----------------------------------------------------------*/

/**
 * @brief Handle of the test runner task.
 */
static TaskHandle_t xTestRunnerTaskHandle;

/**
 * @brief Handles of the tasks created in this test.
 */
static TaskHandle_t xTaskHandles[ configNUMBER_OF_CORES ];

/**
 * @brief Indexes of the tasks created in this test.
 */
static uint32_t xTaskIndexes[ configNUMBER_OF_CORES ];
/*-----------------------------------------------------------*/

/**
 * @brief Ever running task function.
 *
 * Test runner task is notified with the following values:
 * - A value between 0 and ( configNUMBER_OF_CORES -1 ) : Task with the index
 *   equal to value encountered an error during the test.
 * - configNUMBER_OF_CORES : The test finished without any error.
 */
static void prvEverRunningTask( void * pvParameters )
{
    uint32_t i;
    uint32_t uxCurrentTaskIdx = *( ( uint32_t * ) pvParameters );
    eTaskState xTaskState;

    /* Tasks with index smaller than the current task are of higher priority and
     * must be running when this task is running. */
    for( i = 0; i < uxCurrentTaskIdx; i++ )
    {
        xTaskState = eTaskGetState( xTaskHandles[ i ] );

        if( eRunning != xTaskState )
        {
            /* Notify the test runner task about the error.  */
            ( void ) xTaskNotify( xTestRunnerTaskHandle, uxCurrentTaskIdx, eSetValueWithoutOverwrite );
        }
    }

    /* If current task is the last task, then we finish the check because all
     * tasks are checked. */
    if( uxCurrentTaskIdx == ( configNUMBER_OF_CORES - 1 ) )
    {
        /* Notify the test runner task about success.  */
        ( void ) xTaskNotify( xTestRunnerTaskHandle, configNUMBER_OF_CORES, eSetValueWithoutOverwrite );
    }

    for( ; ; )
    {
        /* Busy looping in this task. */
        TEST_NOP();
    }
}
/*-----------------------------------------------------------*/

/**
 * @brief Test running task.
 *
 * It waits for a notification from one of the ever running tasks.
 */
void Test_ScheduleHighestPriority( void )
{
    uint32_t ulNotifiedValue;
    BaseType_t xReturn;

    xReturn = xTaskNotifyWait( 0U, ULONG_MAX, &ulNotifiedValue, pdMS_TO_TICKS( TEST_TIMEOUT_MS ) );

    /* Test runner task is notified within TEST_TIMEOUT_MS. */
    TEST_ASSERT_EQUAL( pdTRUE, xReturn );

    /* The notified value indicates that no error occurred during the test. */
    TEST_ASSERT_EQUAL_INT( configNUMBER_OF_CORES, ulNotifiedValue );
}
/*-----------------------------------------------------------*/

/**
 * @brief Runs before every test, put init calls here.
 */
void setUp( void )
{
    uint32_t i;
    BaseType_t xTaskCreationResult;

    /* Save the test runner task handle here. It is used to notify test runner
     * from ever running tasks. */
    xTestRunnerTaskHandle = xTaskGetCurrentTaskHandle();

    /* Create configNUMBER_OF_CORES tasks with decending priority. */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        xTaskIndexes[ i ] = i;
        xTaskCreationResult = xTaskCreate( prvEverRunningTask,
                                           "EverRun",
                                           configMINIMAL_STACK_SIZE * 2,
                                           &( xTaskIndexes[ i ] ),
                                           configMAX_PRIORITIES - 1 - i,
                                           &( xTaskHandles[ i ] ) );

        TEST_ASSERT_EQUAL_MESSAGE( pdPASS, xTaskCreationResult, "Task creation failed." );
    }
}
/*-----------------------------------------------------------*/

/**
 * @brief Runs after every test, put clean-up calls here.
 */
void tearDown( void )
{
    uint32_t i;

    /* Delete all the tasks. */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        if( xTaskHandles[ i ] != NULL )
        {
            vTaskDelete( xTaskHandles[ i ] );
        }
    }
}
/*-----------------------------------------------------------*/

/**
 * @brief Entry point for test runner to run highest priority test.
 */
void vRunScheduleHighestPriorityTest( void )
{
    UNITY_BEGIN();

    RUN_TEST( Test_ScheduleHighestPriority );

    UNITY_END();
}
/*-----------------------------------------------------------*/
