/*
 * FreeRTOS Kernel <DEVELOPMENT BRANCH>
 * Copyright (C) 2022 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * SPDX-License-Identifier: MIT
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 *
 * https://www.FreeRTOS.org
 * https://github.com/FreeRTOS
 *
 */

/**
 * @file only_one_task_enter_critical.c
 * @brief Only one task/ISR shall be able to enter critical section at a time.
 *
 * Procedure:
 *   - Create ( num of cores - 1 ) tasks.
 *   - All tasks (including test runner) increase the counter for TASK_INCREASE_COUNTER_TIMES times.
 * Expected:
 *   - All tasks have correct value of counter after increasing.
 */
/* Kernel includes. */
#include "FreeRTOS.h" /* Must come first. */
#include "task.h"     /* RTOS task related API prototypes. */

#include "unity.h"    /* unit testing support functions */
/*-----------------------------------------------------------*/

/**
 * @brief As time of loop for task to increase counter.
 */
#define TASK_INCREASE_COUNTER_TIMES    ( 10000 )

/**
 * @brief Timeout value to stop test.
 */
#define TEST_TIMEOUT_MS                ( 10000 )
/*-----------------------------------------------------------*/

/**
 * @brief Test case "Only One Task Enter Critical".
 */
void Test_OnlyOneTaskEnterCritical( void );

/**
 * @brief Task function to increase counter then keep delaying.
 */
static void vPrvTaskIncCounter( void * pvParameters );

/**
 * @brief Function to increase counter in critical section.
 */
static void vLoopIncCounter( void );
/*-----------------------------------------------------------*/

#if ( configNUMBER_OF_CORES < 2 )
    #error This test is for FreeRTOS SMP and therefore, requires at least 2 cores.
#endif /* if configNUMBER_OF_CORES != 2 */

#if configRUN_MULTIPLE_PRIORITIES != 1
    #error test_config.h must be included at the end of FreeRTOSConfig.h.
#endif
/*-----------------------------------------------------------*/

/**
 * @brief Handles of the tasks created in this test.
 */
static TaskHandle_t xTaskHanldes[ configNUMBER_OF_CORES - 1 ];

/**
 * @brief Counter for all tasks to increase.
 */
static BaseType_t xTaskCounter = 0;
/*-----------------------------------------------------------*/

void Test_OnlyOneTaskEnterCritical( void )
{
    TickType_t xStartTick = xTaskGetTickCount();

    /* Yield for other cores to run tasks. */
    taskYIELD();

    /* We need at least two tasks increasing the counter at the same time when configNUMBER_OF_CORES is 2 */
    vLoopIncCounter();

    /* Wait other tasks. */
    while( xTaskCounter < configNUMBER_OF_CORES * TASK_INCREASE_COUNTER_TIMES )
    {
        vTaskDelay( pdMS_TO_TICKS( 10 ) );

        if( ( xTaskGetTickCount() - xStartTick ) / portTICK_PERIOD_MS >= TEST_TIMEOUT_MS )
        {
            break;
        }
    }

    TEST_ASSERT_EQUAL_INT( xTaskCounter, configNUMBER_OF_CORES * TASK_INCREASE_COUNTER_TIMES );
}
/*-----------------------------------------------------------*/

static void vLoopIncCounter( void )
{
    BaseType_t xTempTaskCounter = xTaskCounter;
    BaseType_t xIsTestPass = pdTRUE;
    int i;

    taskENTER_CRITICAL();

    for( i = 0; i < TASK_INCREASE_COUNTER_TIMES; i++ )
    {
        xTaskCounter++;
        xTempTaskCounter++;

        if( xTaskCounter != xTempTaskCounter )
        {
            xIsTestPass = pdFALSE;
        }
    }

    taskEXIT_CRITICAL();

    TEST_ASSERT_TRUE( xIsTestPass );
}

static void vPrvTaskIncCounter( void * pvParameters )
{
    ( void ) pvParameters;

    vLoopIncCounter();

    while( pdTRUE )
    {
        vTaskDelay( pdMS_TO_TICKS( 100 ) );
    }
}
/*-----------------------------------------------------------*/

/* Runs before every test, put init calls here. */
void setUp( void )
{
    int i;
    BaseType_t xTaskCreationResult;

    /* Create configNUMBER_OF_CORES - 1 low priority tasks. */
    for( i = 0; i < configNUMBER_OF_CORES - 1; i++ )
    {
        xTaskCreationResult = xTaskCreate( vPrvTaskIncCounter,
                                           "IncCounter",
                                           configMINIMAL_STACK_SIZE,
                                           NULL,
                                           configMAX_PRIORITIES - 1,
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
    for( i = 0; i < configNUMBER_OF_CORES - 1; i++ )
    {
        if( xTaskHanldes[ i ] )
        {
            vTaskDelete( xTaskHanldes[ i ] );
        }
    }
}
/*-----------------------------------------------------------*/

void vRunOnlyOneTaskEnterCriticalTest( void )
{
    UNITY_BEGIN();

    RUN_TEST( Test_OnlyOneTaskEnterCritical );

    UNITY_END();
}
/*-----------------------------------------------------------*/
