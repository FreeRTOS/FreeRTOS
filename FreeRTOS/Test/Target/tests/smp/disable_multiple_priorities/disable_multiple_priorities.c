/*
 * FreeRTOS Kernel <DEVELOPMENT BRANCH>
 * Copyright (C) 2022 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * SPDX-License-Identifier: MIT
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
 *   - Create ( num of cores ) tasks ( T0~Tn-1 ). Priority T0 > T1 > ... > Tn-2 > Tn-1.
 *   - All tasks keep looping in below steps:
 *     - Check if only task itself run.
 *     - Delay 100ms for other tasks to run.
 * Expected:
 *   - Only one task runs at the same time for 5 seconds.
 */

/* Kernel includes. */
#include "FreeRTOS.h" /* Must come first. */
#include "task.h"     /* RTOS task related API prototypes. */

#include "unity.h"    /* unit testing support functions */
/*-----------------------------------------------------------*/

/**
 * @brief Timeout value to stop test.
 */
#define TEST_TIMEOUT_MS    ( 5000 )
/*-----------------------------------------------------------*/

#if ( configNUMBER_OF_CORES < 2 )
    #error This test is for FreeRTOS SMP and therefore, requires at least 2 cores.
#endif /* if configNUMBER_OF_CORES != 2 */

#if ( configRUN_MULTIPLE_PRIORITIES != 0 )
    #error Need to include testConfig.h in FreeRTOSConfig.h
#endif /* if configRUN_MULTIPLE_PRIORITIES != 0 */

#if ( configUSE_CORE_AFFINITY != 0 )
    #error Need to include testConfig.h in FreeRTOSConfig.h
#endif /* if configUSE_CORE_AFFINITY != 0 */
/*-----------------------------------------------------------*/

/**
 * @brief Test case "Disable Multiple Priorities".
 */
void Test_DisableMultiplePriorities( void );

/**
 * @brief Function that checks if itself is the only task runs.
 */
static void vPrvCheckRunningTask( void * pvParameters );

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
 * @brief Flas to indicate if task T0~Tn-1 run or not.
 */
static BaseType_t xHasTaskRun[ configNUMBER_OF_CORES ] = { pdFALSE };
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

static void vPrvCheckRunningTask( void * pvParameters )
{
    UBaseType_t xIdx, xNumTasksRunning;
    TaskStatus_t taskStatus[ 16 ];
    UBaseType_t xTaskStatusArraySize = 16;
    unsigned long ulTotalRunTime;
    int lCurrentTaskIdx = -1;

    ( void ) pvParameters;

    lCurrentTaskIdx = lFindTaskIdx( xTaskGetCurrentTaskHandle() );
    TEST_ASSERT_TRUE( lCurrentTaskIdx >= 0 && lCurrentTaskIdx < configNUMBER_OF_CORES );
    xHasTaskRun[ lCurrentTaskIdx ] = pdTRUE;

    for( ; ; )
    {
        xNumTasksRunning = uxTaskGetSystemState( ( TaskStatus_t * const ) &taskStatus, xTaskStatusArraySize, &ulTotalRunTime );

        for( xIdx = 0; xIdx < xNumTasksRunning; xIdx++ )
        {
            int lTaskIdx = lFindTaskIdx( taskStatus[ xIdx ].xHandle );

            if( ( lTaskIdx >= 0 ) && ( lCurrentTaskIdx < configNUMBER_OF_CORES ) && ( taskStatus[ xIdx ].eCurrentState == eRunning ) )
            {
                /* It's one of T0~Tn-1, and only current task should be run. */
                TEST_ASSERT_EQUAL_INT( lTaskIdx, lCurrentTaskIdx );
            }
        }

        vTaskDelay( pdMS_TO_TICKS( 100 ) );
    }
}
/*-----------------------------------------------------------*/

void Test_DisableMultiplePriorities( void )
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
        TEST_ASSERT_TRUE( xHasTaskRun[ i ] == pdTRUE );
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
        xTaskCreationResult = xTaskCreate( vPrvCheckRunningTask,
                                           "CheckRunning",
                                           configMINIMAL_STACK_SIZE * 2,
                                           NULL,
                                           configMAX_PRIORITIES - 1 - i,
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
 * @brief A start entry for test runner to run FR04.
 */
void vRunDisableMultiplePrioritiesTest( void )
{
    UNITY_BEGIN();

    RUN_TEST( Test_DisableMultiplePriorities );

    UNITY_END();
}
/*-----------------------------------------------------------*/
