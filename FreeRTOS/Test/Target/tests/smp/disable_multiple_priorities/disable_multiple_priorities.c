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
 * @file disable_multiple_priorities.c
 * @brief The user shall be able to configure the scheduler to not run a
 *        lower priority task and a higher priority task simultaneously.
 *
 * Procedure:
 *   - Create ( num of cores ) test tasks ( T0~Tn-1 ). Priority T0 > T1 > ... > Tn-2 > Tn-1.
 *   - Verify the following conditions:
 *      - for each task Ti in [T0..Tn-1]:
 *          - Tasks T0~Ti-1 are in suspended state.
 *          - Task Ti is running.
 *          - Tasks Ti+1~Tn-1 are in ready state.
 *          - Suspend task Ti.
 * Expected:
 *   - Only one task is running at the same time since all the test test tasks
 *     are of different priorities.
 */

/* Standard includes. */
#include <stdint.h>

/* Kernel includes. */
#include "FreeRTOS.h"
#include "task.h"

/* Unit testing support functions. */
#include "unity.h"
/*-----------------------------------------------------------*/

/**
 * @brief Timeout value to stop test.
 */
#define TEST_TIMEOUT_MS    ( 1000 )
/*-----------------------------------------------------------*/

#if ( configNUMBER_OF_CORES < 2 )
    #error This test is for FreeRTOS SMP and therefore, requires at least 2 cores.
#endif /* if configNUMBER_OF_CORES != 2 */

#if ( configRUN_MULTIPLE_PRIORITIES != 0 )
    #error configRUN_MULTIPLE_PRIORITIES must be disabled by including test_config.h in FreeRTOSConfig.h.
#endif /* if configRUN_MULTIPLE_PRIORITIES != 0 */

#if ( configUSE_CORE_AFFINITY != 0 )
    #error configUSE_CORE_AFFINITY must be disabled by including test_config.h in FreeRTOSConfig.h.
#endif /* if configUSE_CORE_AFFINITY != 0 */

#if ( configMAX_PRIORITIES <= ( configNUMBER_OF_CORES + 2 ) )
    #error This test creates tasks with different priority, requires configMAX_PRIORITIES to be larger than configNUMBER_OF_CORES.
#endif /* if ( configMAX_PRIORITIES <= ( configNUMBER_OF_CORES + 2 ) ) */
/*-----------------------------------------------------------*/

/**
 * @brief Test case "Disable Multiple Priorities".
 */
void Test_DisableMultiplePriorities( void );

/**
 * @brief Task function that verifies that it is the only running task.
 */
static void prvCheckRunningTask( void * pvParameters );
/*-----------------------------------------------------------*/

/**
 * @brief Handles of the tasks created in this test.
 */
static TaskHandle_t xTaskHandles[ configNUMBER_OF_CORES ];

/**
 * @brief Indexes of the tasks created in this test.
 */
static uint32_t xTaskIndexes[ configNUMBER_OF_CORES ];

/**
 * @brief Test results.
 */
static BaseType_t xTestResults[ configNUMBER_OF_CORES ] = { pdFAIL };
/*-----------------------------------------------------------*/

static void prvCheckRunningTask( void * pvParameters )
{
    uint32_t i = 0;
    uint32_t currentTaskIdx = *( ( uint32_t * ) pvParameters );
    eTaskState taskState;
    BaseType_t xTestResult = pdPASS;

    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        /* All the test tasks are created by the test runner task which runs
         * at the highest priority. The test runs with multiple priorities
         * disabled. Therefore, xTaskHandles[ i ] can not be NULL because none
         * of the test tasks can run until the test runner task has created all
         * the tasks and then blocked itself by calling vTaskDelay. Return
         * pdFAIL in xTestResults to indicate test failure if any of the test
         * task is not created yet. */
        if( xTaskHandles[ i ] == NULL )
        {
            xTestResult = pdFAIL;
        }
        else
        {
            taskState = eTaskGetState( xTaskHandles[ i ] );

            if( i > currentTaskIdx )
            {
                /* Tasks with index greater than current task are of lower
                 * priority than the current task and must be in the ready
                 * state. */
                if( taskState != eReady )
                {
                    xTestResult = pdFAIL;
                }
            }
            else if( i == currentTaskIdx )
            {
                /* Current task must be running. */
                if( taskState != eRunning )
                {
                    xTestResult = pdFAIL;
                }
            }
            else
            {
                /* Tasks with index smaller than current task are of higher
                 * priority than the current task and must be in the suspended
                 * state. */
                if( taskState != eSuspended )
                {
                    xTestResult = pdFAIL;
                }
            }
        }

        if( xTestResult != pdPASS )
        {
            break;
        }
    }

    xTestResults[ currentTaskIdx ] = xTestResult;

    /* Suspend the test task itself. */
    vTaskSuspend( NULL );
}
/*-----------------------------------------------------------*/

void Test_DisableMultiplePriorities( void )
{
    uint32_t i;
    BaseType_t xTaskCreationResult;

    /* Create configNUMBER_OF_CORES low priority tasks. */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        xTaskCreationResult = xTaskCreate( prvCheckRunningTask,
                                           "CheckRunning",
                                           configMINIMAL_STACK_SIZE * 2,
                                           &xTaskIndexes[ i ],
                                           configMAX_PRIORITIES - 2 - i,
                                           &xTaskHandles[ i ] );

        TEST_ASSERT_EQUAL_MESSAGE( pdPASS, xTaskCreationResult, "Task creation failed." );
    }

    /* Waiting for all the test tasks. */
    vTaskDelay( pdMS_TO_TICKS( TEST_TIMEOUT_MS ) );

    /* Verify test results for all the tasks. */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        TEST_ASSERT_EQUAL_MESSAGE( pdPASS, xTestResults[ i ], "Task test result is pdFAIL" );
    }
}
/*-----------------------------------------------------------*/

/* Runs before every test, put init calls here. */
void setUp( void )
{
    uint32_t i;

    /* Initialize variables. */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        xTaskHandles[ i ] = NULL;
        xTaskIndexes[ i ] = i;
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
 * @brief Entry point for test runner to run disable multiple priorities test.
 */
void vRunDisableMultiplePrioritiesTest( void )
{
    UNITY_BEGIN();

    RUN_TEST( Test_DisableMultiplePriorities );

    UNITY_END();
}
/*-----------------------------------------------------------*/
