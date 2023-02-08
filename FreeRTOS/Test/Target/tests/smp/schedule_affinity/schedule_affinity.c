/*
 * FreeRTOS V202212.00
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

/**
 * @file schedule_affinity.c
 * @brief The scheduler shall not schedule a task that is pinned to a specific core on any other core.
 *
 * Procedure:
 *   - Create ( num of cores ) tasks ( T0~Tn-1 ).
 *   - Pin T0 to core 0, T1 to core 1, and so on.
 *   - Each task will iterate 25 times, with a 10ms yielding delay bectween each
 *     test iteration. The test will confirm it is running on the core it was pinned
 *     to.
 * Expected:
 *   - All tasks will only run on the cores that they were pinned to.
 */

/* Kernel includes. */
#include "FreeRTOS.h" /* Must come first. */
#include "task.h"     /* RTOS task related API prototypes. */

#include "unity.h"    /* unit testing support functions */
/*-----------------------------------------------------------*/

/**
 * @brief Timeout value to stop test.
 */
#define TEST_TIMEOUT_MS    ( 10000 )
/*-----------------------------------------------------------*/

#if ( configNUMBER_OF_CORES < 2 )
    #error This test is for FreeRTOS SMP and therefore, requires at least 2 cores.
#endif /* if configNUMBER_OF_CORES != 2 */

#if ( configUSE_TASK_PREEMPTION_DISABLE != 1 )
    #error Need to include testConfig.h in FreeRTOSConfig.h
#endif /* if configRUN_MULTIPLE_PRIORITIES != 0 */
/*-----------------------------------------------------------*/

/**
 * @brief Test case "Schedule Affinity".
 */
void Test_ScheduleAffinity( void );

/**
 * @brief Function that checks if it's pinned to correct core.
 */
static void vPrvTaskCheckPinCore( void * pvParameters );

/**
 * @brief Function that returns which index does the xCurrntTaskHandle match.
 *        0 for T0, 1 for T1, -1 for not match.
 */
static int lFindTaskIdx( TaskHandle_t xCurrntTaskHandle );
/*-----------------------------------------------------------*/

/**
 * @brief Handles of the tasks created in this test.
 */
static TaskHandle_t xTaskHanldes[ configNUMBER_OF_CORES ];

/**
 * @brief Flas to indicate if task T0~Tn-1 finish or not.
 */
static BaseType_t xHasTaskFinished[ configNUMBER_OF_CORES ] = { pdFALSE };
/*-----------------------------------------------------------*/

static int lFindTaskIdx( TaskHandle_t xCurrntTaskHandle )
{
    int i = 0;
    int lMatchIdx = -1;

    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        if( xCurrntTaskHandle == xTaskHanldes[ i ] )
        {
            lMatchIdx = i;
            break;
        }
    }

    return lMatchIdx;
}
/*-----------------------------------------------------------*/

static void vPrvTaskCheckPinCore( void * pvParameters )
{
    int lCurrentTaskIdx = -1;
    uint32_t ulIter;
    BaseType_t xCore;

    ( void ) pvParameters;

    lCurrentTaskIdx = lFindTaskIdx( xTaskGetCurrentTaskHandle() );
    TEST_ASSERT_TRUE( lCurrentTaskIdx >= 0 && lCurrentTaskIdx < configNUMBER_OF_CORES );

    for( ulIter = 1; ulIter < 25; ulIter++ )
    {
        vTaskDelay( pdMS_TO_TICKS( 10 ) );
        xCore = portGET_CORE_ID();

        if( xCore != lCurrentTaskIdx )
        {
            TEST_ASSERT_EQUAL_INT( xCore, lCurrentTaskIdx );
            break;
        }
    }

    xHasTaskFinished[ lCurrentTaskIdx ] = pdTRUE;

    /* idle the task */
    for( ; ; )
    {
        vTaskDelay( pdMS_TO_TICKS( 100 ) );
    }
}
/*-----------------------------------------------------------*/

void Test_ScheduleAffinity( void )
{
    TickType_t xStartTick = xTaskGetTickCount();
    int i = 0;

    /* Wait other tasks. */
    for( ; ; )
    {
        vTaskDelay( pdMS_TO_TICKS( 100 ) );

        if( ( xTaskGetTickCount() - xStartTick ) / portTICK_PERIOD_MS >= TEST_TIMEOUT_MS )
        {
            break;
        }
    }

    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        TEST_ASSERT_TRUE( xHasTaskFinished[ i ] == pdTRUE );
    }
}
/*-----------------------------------------------------------*/

/* Runs before every test, put init calls here. */
void setUp( void )
{
    int i;
    BaseType_t xTaskCreationResult;

    /* Create configNUMBER_OF_CORES - 1 low priority tasks. */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        xTaskCreationResult = xTaskCreateAffinitySet( vPrvTaskCheckPinCore,
                                                      "CheckPinCore",
                                                      configMINIMAL_STACK_SIZE,
                                                      NULL,
                                                      configMAX_PRIORITIES - 2,
                                                      ( 1U << i ),
                                                      &( xTaskHanldes[ i ] ) );

        TEST_ASSERT_EQUAL_MESSAGE( pdPASS, xTaskCreationResult, "Task creation failed." );
    }
}
/*-----------------------------------------------------------*/

/* Runs after every test, put clean-up calls here. */
void tearDown( void )
{
    int i;

    /* Delete all the tasks. */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        if( xTaskHanldes[ i ] )
        {
            vTaskDelete( xTaskHanldes[ i ] );
        }
    }
}
/*-----------------------------------------------------------*/

/**
 * @brief A start entry for test runner to run FR05.
 */
void vRunScheduleAffinityTest( void )
{
    UNITY_BEGIN();

    RUN_TEST( Test_ScheduleAffinity );

    UNITY_END();
}
/*-----------------------------------------------------------*/
