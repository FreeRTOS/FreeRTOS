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
 * @file schedule_highest_priority.c
 * @brief The scheduler shall correctly schedule the highest priority ready tasks.
 *
 * Procedure:
 *   - Create ( num of cores ) tasks ( T0~Tn-1 ). Priority T0 > T1 > ... > Tn-2 > Tn-1.
 * Expected:
 *   - Make sure that T0 is run first, then T1, ..., and finally Tn-1.
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

#if traceTASK_SWITCHED_IN != test_TASK_SWITCHED_IN
    #error Need to include testConfig.h in FreeRTOSConfig.h
#endif /* if traceTASK_SWITCHED_IN != test_TASK_SWITCHED_IN */
/*-----------------------------------------------------------*/

/**
 * @brief Test case "Only One Task Enter Critical".
 */
void Test_ScheduleHighestPirority( void );

/**
 * @brief Function that implements a never blocking FreeRTOS task.
 */
static void vPrvEverRunningTask( void * pvParameters );
/*-----------------------------------------------------------*/

/**
 * @brief Handles of the tasks created in this test.
 */
static TaskHandle_t xTaskHanldes[ configNUMBER_OF_CORES ];

/**
 * @brief A flag to indicate if test case is finished.
 */
static BaseType_t xIsTestFinished = pdFALSE;
/*-----------------------------------------------------------*/

void test_TASK_SWITCHED_IN( void )
{
    UBaseType_t xIdx, xNumTasksRunning;
    TaskStatus_t taskStatus[ 16 ];
    UBaseType_t xTaskStatusArraySize = 16;
    unsigned long ulTotalRunTime;
    int i = 0, lNextRunTask = 0;

    xNumTasksRunning = uxTaskGetSystemState( ( TaskStatus_t * const ) &taskStatus, xTaskStatusArraySize, &ulTotalRunTime );

    for( xIdx = 0; xIdx < xNumTasksRunning; xIdx++ )
    {
        for( i = 0; i < configNUMBER_OF_CORES; i++ )
        {
            if( ( taskStatus[ xIdx ].xHandle == xTaskHanldes[ i ] ) && ( taskStatus[ xIdx ].eCurrentState == eRunning ) )
            {
                if( i == lNextRunTask )
                {
                    lNextRunTask++;
                    break;
                }
                else if( i > lNextRunTask )
                {
                    TEST_ASSERT_TRUE( i > lNextRunTask );
                    xIsTestFinished = pdTRUE;
                    break;
                }
            }
        }
    }

    if( lNextRunTask >= configNUMBER_OF_CORES )
    {
        xIsTestFinished = pdTRUE;
    }
}
/*-----------------------------------------------------------*/

static void vPrvEverRunningTask( void * pvParameters )
{
    /* Silence warnings about unused parameters. */
    ( void ) pvParameters;

    for( ; ; )
    {
        /* Always running, put asm here to avoid optimization by compiler. */
        __asm volatile ( "nop" );
    }
}
/*-----------------------------------------------------------*/

void Test_ScheduleHighestPirority( void )
{
    TickType_t xStartTick = xTaskGetTickCount();

    /* Wait other tasks. */
    while( xIsTestFinished == pdFALSE )
    {
        vTaskDelay( pdMS_TO_TICKS( 10 ) );

        if( ( xTaskGetTickCount() - xStartTick ) / portTICK_PERIOD_MS >= TEST_TIMEOUT_MS )
        {
            break;
        }
    }

    TEST_ASSERT_TRUE( xIsTestFinished == pdTRUE );
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
        xTaskCreationResult = xTaskCreate( vPrvEverRunningTask,
                                           "EverRun",
                                           configMINIMAL_STACK_SIZE,
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
 * @brief A start entry for test runner to run FR02.
 */
void vRunScheduleHighestPriorityTest( void )
{
    UNITY_BEGIN();

    RUN_TEST( Test_ScheduleHighestPirority );

    UNITY_END();
}
/*-----------------------------------------------------------*/
