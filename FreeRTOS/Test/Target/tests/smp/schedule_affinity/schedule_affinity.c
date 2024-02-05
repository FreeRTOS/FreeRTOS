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
 * @file schedule_affinity.c
 * @brief The scheduler shall not schedule a task that is pinned to a specific core on any other core.
 *
 * Procedure:
 *   - Create 2 * ( num of cores ) tasks ( T0, ..., Tn-1, Tn, ..., T2n-1 ).
 *   - Pin T0 to core 0, T1 to core 1, and so on.
 *   - Pin Tn to core 0, Tn+1 to core 1, and so on. Tx and Tn+x will be pinned to the same core.
 *   - Verify the following conditions:
 *     - Tx+n is not running when Tx is running.
 *     - Tx is not running when Tx+n is running.
 *     - Both Tx and Tx+n can only run on core x.
 * Expected:
 *   - All tasks will only run on the cores that they were pinned to.
 */

/* Standard includes. */
#include <stdint.h>

/* Kernel includes. */
#include "FreeRTOS.h" /* Must come first. */
#include "task.h"     /* RTOS task related API prototypes. */

#include "unity.h"    /* unit testing support functions */
/*-----------------------------------------------------------*/

/**
 * @brief Timeout value to stop test.
 */
#define TEST_TIMEOUT_MS    ( 1000 )
/*-----------------------------------------------------------*/

#if ( configNUMBER_OF_CORES < 2 )
    #error This test is for FreeRTOS SMP and therefore, requires at least 2 cores.
#endif /* if configNUMBER_OF_CORES != 2 */

#if ( configMAX_PRIORITIES <= ( configNUMBER_OF_CORES + 2 ) )
    #error configMAX_PRIORITIES must be larger than ( configNUMBER_OF_CORES + 2 ) to avoid scheduling idle tasks unexpectedly.
#endif /* if ( configMAX_PRIORITIES <= ( configNUMBER_OF_CORES + 2 ) ) */
/*-----------------------------------------------------------*/

/**
 * @brief Test case "Schedule Affinity".
 */
void Test_ScheduleAffinity( void );

/**
 * @brief Function that checks if it's pinned to correct core.
 */
static void prvTaskCheckPinCore( void * pvParameters );
/*-----------------------------------------------------------*/

/**
 * @brief Handles of the tasks created in this test.
 */
static TaskHandle_t xTaskHandles[ configNUMBER_OF_CORES * 2 ];

/**
 * @brief Indexes of the tasks created in this test.
 */
static uint32_t xTaskIndexes[ configNUMBER_OF_CORES * 2 ];

/**
 * @brief Flags to indicate if task T0~Tn-1 finish or not.
 */
static BaseType_t xTaskTestResults[ configNUMBER_OF_CORES * 2 ] = { pdFAIL };

/**
 * @brief Flag to indicate test started.
 */
static volatile BaseType_t xTestStarted = pdFALSE;
/*-----------------------------------------------------------*/

static void prvTaskCheckPinCore( void * pvParameters )
{
    uint32_t currentTaskIdx = *( ( int * ) pvParameters );
    uint32_t pinToSameCoreTaskIdx;
    eTaskState taskState;
    BaseType_t testResult = pdPASS;
    BaseType_t xCore;

    /* Busy looping here to wait for test runner creating all the test tasks.
     * Test runner has timeout to prevent infinite blocking here. */
    while( xTestStarted == pdFALSE )
    {
    }

    /* Find out the task index which pin to the same core. */
    if( currentTaskIdx >= configNUMBER_OF_CORES )
    {
        pinToSameCoreTaskIdx = currentTaskIdx - configNUMBER_OF_CORES;
        xCore = pinToSameCoreTaskIdx;
    }
    else
    {
        pinToSameCoreTaskIdx = currentTaskIdx + configNUMBER_OF_CORES;
        xCore = currentTaskIdx;
    }

    /* Verify the current running task state. The task should be of running state.
     * The core index on which this task is running must consistent with affinity
     * mask. */
    taskState = eTaskGetState( xTaskHandles[ currentTaskIdx ] );

    if( taskState != eRunning )
    {
        testResult = pdFAIL;
    }

    if( xCore != portGET_CORE_ID() )
    {
        testResult = pdFAIL;
    }

    /* Verify that the other task pin to the same core should not of running state. */
    taskState = eTaskGetState( xTaskHandles[ pinToSameCoreTaskIdx ] );

    if( taskState == eRunning )
    {
        testResult = pdFAIL;
    }

    xTaskTestResults[ currentTaskIdx ] = testResult;

    /* Suspend the test task. */
    vTaskSuspend( NULL );
}
/*-----------------------------------------------------------*/

void Test_ScheduleAffinity( void )
{
    uint32_t i;
    BaseType_t xTaskCreationResult;

    /* Create configNUMBER_OF_CORES low priority tasks. */
    for( i = 0; i < ( configNUMBER_OF_CORES * 2 ); i++ )
    {
        xTaskCreationResult = xTaskCreateAffinitySet( prvTaskCheckPinCore,
                                                      "CheckPinCore",
                                                      configMINIMAL_STACK_SIZE,
                                                      &xTaskIndexes[ i ],
                                                      configMAX_PRIORITIES - 2 - ( i % configNUMBER_OF_CORES ),
                                                      ( 1U << ( i % configNUMBER_OF_CORES ) ),
                                                      &xTaskHandles[ i ] );

        TEST_ASSERT_EQUAL_MESSAGE( pdPASS, xTaskCreationResult, "Task creation failed." );
    }

    /* Wait for test tasks finish test. */
    xTestStarted = pdTRUE;
    vTaskDelay( pdMS_TO_TICKS( TEST_TIMEOUT_MS ) );

    /* Verify the test result. */
    for( i = 0; i < ( configNUMBER_OF_CORES * 2 ); i++ )
    {
        TEST_ASSERT_TRUE( xTaskTestResults[ i ] == pdPASS );
    }
}
/*-----------------------------------------------------------*/

/* Runs before every test, put init calls here. */
void setUp( void )
{
    uint32_t i;

    xTestStarted = pdFALSE;

    for( i = 0; i < ( configNUMBER_OF_CORES * 2 ); i++ )
    {
        xTaskIndexes[ i ] = i;
        xTaskHandles[ i ] = NULL;
        xTaskTestResults[ i ] = pdFAIL;
    }
}
/*-----------------------------------------------------------*/

/* Runs after every test, put clean-up calls here. */
void tearDown( void )
{
    uint32_t i;

    /* Delete all the tasks created in the test. */
    for( i = 0; i < ( configNUMBER_OF_CORES * 2 ); i++ )
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
 * @brief A start entry for test runner to run schedule affinity test.
 */
void vRunScheduleAffinityTest( void )
{
    UNITY_BEGIN();

    RUN_TEST( Test_ScheduleAffinity );

    UNITY_END();
}
/*-----------------------------------------------------------*/
