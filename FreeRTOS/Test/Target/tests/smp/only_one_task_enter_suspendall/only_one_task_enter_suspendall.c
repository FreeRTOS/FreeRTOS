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
 * @file only_one_task_enter_suspendall.c
 * @brief Only one task shall be able to enter the section protected by
 * vTaskSuspendAll/xTaskResumeAll
 *
 * Procedure:
 *   - Create ( num of cores ) tasks.
 *   - All tasks increment a shared counter for TASK_INCREASE_COUNTER_TIMES
 *     times in the section protected by vTaskSuspendAll/xTaskResumeAll.
 * Expected:
 *   - All tasks have correct value of counter after incrementing.
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
 * @brief Number of times each task increments the shared counter.
 */
#define TASK_INCREASE_COUNTER_TIMES    ( 10000 )

/**
 * @brief Timeout value to stop test.
 */
#define TEST_TIMEOUT_MS                ( 1000 )
/*-----------------------------------------------------------*/

/**
 * @brief Test case "Only one task enters the section protected by
 * vTaskSuspendAll/xTaskResumeAll".
 */
void Test_OnlyOneTaskEnterSuspendAll( void );

/**
 * @brief Task function to increment the shared counter and then block.
 */
static void prvTaskIncCounter( void * pvParameters );
/*-----------------------------------------------------------*/

#if ( configNUMBER_OF_CORES < 2 )
    #error This test is for FreeRTOS SMP and therefore, requires at least 2 cores.
#endif /* if ( configNUMBER_OF_CORES < 2 ) */

#if ( configMAX_PRIORITIES <= 2 )
    #error configMAX_PRIORITIES must be larger than 2 to avoid scheduling idle tasks unexpectedly.
#endif /* if ( configMAX_PRIORITIES <= 2 ) */
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
 * @brief Flags to indicate if tasks T0~Tn-1 detect an error or not.
 */
static BaseType_t xTestResults[ configNUMBER_OF_CORES ] = { pdFAIL };

/**
 * @brief Flags to indicate tasks T0~Tn-1 started running.
 */
static volatile BaseType_t xTaskRunning[ configNUMBER_OF_CORES ] = { pdFALSE };

/**
 * @brief Shared counter for all tasks to increment.
 */
static volatile uint32_t xSharedCounter = 0;
/*-----------------------------------------------------------*/

static void prvTaskIncCounter( void * pvParameters )
{
    uint32_t currentTaskIdx = *( ( uint32_t * ) pvParameters );
    BaseType_t xAllTaskReady = pdFALSE;
    BaseType_t xTestResult = pdPASS;
    uint32_t xLocalCounter = 0;
    uint32_t i;

    /* Wait for all tasks to start running. */
    xTaskRunning[ currentTaskIdx ] = pdTRUE;

    while( xAllTaskReady == pdFALSE )
    {
        for( i = 0; i < configNUMBER_OF_CORES; i++ )
        {
            if( xTaskRunning[ i ] != pdTRUE )
            {
                break;
            }
        }

        if( i == configNUMBER_OF_CORES )
        {
            xAllTaskReady = pdTRUE;
        }
    }

    /* Increment the shared counter in a loop. The expectation is that only one
     * task increments the counter at a time as it is incremented in the section
     * protected by vTaskSuspendAll/xTaskResumeAll. */
    vTaskSuspendAll();
    {
        xLocalCounter = xSharedCounter;

        for( i = 0; i < TASK_INCREASE_COUNTER_TIMES; i++ )
        {
            /* Increment the local variable xLocalCounter and shared variable
             * xSharedCounter. */
            xSharedCounter++;
            xLocalCounter++;

            /* If the implementation of vTaskSuspendAll is not correct and
             * multiple tasks are able to enter the section protected by
             * vTaskSuspendAll/xTaskResumeAll, shared counter will be
             * incremented by multiple tasks and as a result, local counter
             * xLocalCounterwon't be equal to the shared counter
             * xSharedCounter. */
            if( xSharedCounter != xLocalCounter )
            {
                xTestResult = pdFAIL;
                break;
            }
        }
    }
    ( void ) xTaskResumeAll();

    xTestResults[ currentTaskIdx ] = xTestResult;

    /* Blocking the test task. */
    vTaskDelay( portMAX_DELAY );
}
/*-----------------------------------------------------------*/

void Test_OnlyOneTaskEnterSuspendAll( void )
{
    uint32_t i;

    BaseType_t xTaskCreationResult;

    /* Create configNUMBER_OF_CORES test tasks. */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        xTaskIndexes[ i ] = i;
        xTaskCreationResult = xTaskCreate( prvTaskIncCounter,
                                           "IncCounter",
                                           configMINIMAL_STACK_SIZE,
                                           &( xTaskIndexes[ i ] ),
                                           configMAX_PRIORITIES - 2,
                                           &( xTaskHandles[ i ] ) );

        TEST_ASSERT_EQUAL_MESSAGE( pdPASS, xTaskCreationResult, "Task creation failed." );
    }

    /* Delay for other cores to run tasks. */
    vTaskDelay( pdMS_TO_TICKS( TEST_TIMEOUT_MS ) );

    /* Validate that none of the test tasks detected error. */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        TEST_ASSERT_EQUAL_MESSAGE( pdPASS, xTestResults[ i ], "Critical section test task failed." );
    }

    /* Verify the shared counter value. */
    TEST_ASSERT_EQUAL_UINT32( configNUMBER_OF_CORES * TASK_INCREASE_COUNTER_TIMES, xSharedCounter );
}
/*-----------------------------------------------------------*/

/* Runs before every test, put init calls here. */
void setUp( void )
{
    uint32_t i;

    xSharedCounter = 0;

    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        xTaskIndexes[ i ] = i;
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
 * @brief Entry point for test runner to run "only one task enter suspend all"
 * test.
 */
void vRunOnlyOneTaskEnterSuspendAll( void )
{
    UNITY_BEGIN();

    RUN_TEST( Test_OnlyOneTaskEnterSuspendAll );

    UNITY_END();
}
/*-----------------------------------------------------------*/
