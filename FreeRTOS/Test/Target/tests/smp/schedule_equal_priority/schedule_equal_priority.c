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
 * @file schedule_equal_priority.c
 * @brief The scheduler shall schedule tasks of equal priority in a round robin fashion.
 *
 * Procedure:
 *   - Create ( num of cores + 1 ) tasks ( T0~Tn ). Priority T0 = T1 = ... = Tn-1 = Tn.
 *   - All three tasks are running busyloops
 * Expected:
 *   - All three tasks get a chance to run. The test doesn't currently strictly
 *     validate the round-robin nature of the scheduler as other system tasks,
 *     possibly target specicfic come and go complicating on-target validation.
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
/*-----------------------------------------------------------*/

/**
 * @brief Test case "Only One Task Enter Critical".
 */
void Test_ScheduleHighestPirority( void );

/**
 * @brief Function that implements a never blocking FreeRTOS task.
 */
static void vPrvEverRunningTask( void * pvParameters );

/**
 * @brief Function that returns which index does the xCurrntTaskHandle match.
 *        0 for T0, 1 for T1, -1 for not match.
 */
static int lFindTaskIdx( TaskHandle_t xCurrntTaskHandle );

/**
 * @brief Check if all tasks have run or not.
 */
static BaseType_t xAreAllTasksRun( void );
/*-----------------------------------------------------------*/

/**
 * @brief Handles of the tasks created in this test.
 */
static TaskHandle_t xTaskHanldes[ configNUMBER_OF_CORES + 1 ];

/**
 * @brief Handles of the tasks created in this test.
 */
static BaseType_t xTaskRun[ configNUMBER_OF_CORES + 1 ] = { pdFALSE };
/*-----------------------------------------------------------*/

static BaseType_t xAreAllTasksRun( void )
{
    int i;
    BaseType_t xIsAllTasksRun = pdTRUE;

    for( i = 0; i < configNUMBER_OF_CORES + 1; i++ )
    {
        if( xTaskRun[ i ] != pdTRUE )
        {
            xIsAllTasksRun = pdFALSE;
        }
    }

    return xIsAllTasksRun;
}
/*-----------------------------------------------------------*/

static int lFindTaskIdx( TaskHandle_t xCurrntTaskHandle )
{
    int i = 0;
    int lMatchIdx = -1;

    for( i = 0; i < configNUMBER_OF_CORES + 1; i++ )
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

static void vPrvEverRunningTask( void * pvParameters )
{
    int lCurrentTaskIdx = lFindTaskIdx( xTaskGetCurrentTaskHandle() );

    /* Silence warnings about unused parameters. */
    ( void ) pvParameters;

    xTaskRun[ lCurrentTaskIdx ] = pdTRUE;

    for( ; ; )
    {
        /* Always running, put asm here to avoid optimization by compiler. */
        __asm volatile ( "nop" );
    }
}
/*-----------------------------------------------------------*/

void Test_ScheduleEqualPriority( void )
{
    TickType_t xStartTick = xTaskGetTickCount();
    BaseType_t xAllTasksRun;

    /* Wait other tasks. */
    while( (xAllTasksRun = xAreAllTasksRun()) == pdFALSE )
    {
        vTaskDelay( pdMS_TO_TICKS( 10 ) );

        if( ( xTaskGetTickCount() - xStartTick ) / portTICK_PERIOD_MS >= TEST_TIMEOUT_MS )
        {
            break;
        }
    }

    TEST_ASSERT_TRUE( xAllTasksRun );
}
/*-----------------------------------------------------------*/

/* Runs before every test, put init calls here. */
void setUp( void )
{
    int i;
    BaseType_t xTaskCreationResult;

    /* Create configNUMBER_OF_CORES + 1 low priority tasks. */
    for( i = 0; i < configNUMBER_OF_CORES + 1; i++ )
    {
        xTaskCreationResult = xTaskCreate( vPrvEverRunningTask,
                                           "EverRun",
                                           configMINIMAL_STACK_SIZE,
                                           NULL,
                                           configMAX_PRIORITIES - 2,
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
    for( i = 0; i < configNUMBER_OF_CORES + 1; i++ )
    {
        if( xTaskHanldes[ i ] )
        {
            vTaskDelete( xTaskHanldes[ i ] );
        }
    }
}
/*-----------------------------------------------------------*/

/**
 * @brief A start entry for test runner to run FR03.
 */
void vRunScheduleEqualPriorityTest( void )
{
    UNITY_BEGIN();

    RUN_TEST( Test_ScheduleEqualPriority );

    UNITY_END();
}
/*-----------------------------------------------------------*/
