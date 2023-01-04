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
 * @file test.c
 * @brief The scheduler shall correctly schedule the highest priority ready tasks.
 *
 * Procedure:
 *   - Create tasks A, B, & C, with unique and ascending priorities respectively.
 *   - All three tasks are alternating between a busy loop and a 10ms yielding delay.
 *   - Use the traceTASK_SWITCHED_IN() hook to observe scheduler behavior.
 * Expected:
 *   - Validate that when A, the lowest priority task runs, the other two tasks have already run.
 */

/* Kernel includes. */

#include "FreeRTOS.h" /* Must come first. */
#include "task.h"     /* RTOS task related API prototypes. */

#include <string.h>

#include "bsl.h"
#include "unity.h" /* unit testing support functions */
/*-----------------------------------------------------------*/

/* Priorities at which the tasks are created.  The max priority can be specified
 * as ( configMAX_PRIORITIES - 1 ). */
#define mainTASK_A_PRIORITY    ( tskIDLE_PRIORITY + 1 )
#define mainTASK_B_PRIORITY    ( tskIDLE_PRIORITY + 2 )
#define mainTASK_C_PRIORITY    ( tskIDLE_PRIORITY + 3 )
/*-----------------------------------------------------------*/

#if configNUMBER_OF_CORES != 2
    #error Require two cores be configured for FreeRTOS
#endif /* if configNUMBER_OF_CORES != 2 */

#if traceTASK_SWITCHED_IN != test_fr2TASK_SWITCHED_IN
    #error Need to include testConfig.h in FreeRTOSConfig.h
#endif /* if traceTASK_SWITCHED_IN != test_fr2TASK_SWITCHED_IN */
/*-----------------------------------------------------------*/

/* Function declaration. */
static void fr02_scheHighestPriority( void );
static void vPrvTaskA( void * pvParameters );
static void vPrvTaskB( void * pvParameters );
static void vPrvTaskC( void * pvParameters );
static void vValidateResult( void );
/*-----------------------------------------------------------*/

static BaseType_t xTestPassed = pdFALSE;
static BaseType_t xTestFailed = pdFALSE;
static TaskHandle_t xTaskAHandler;
static TaskHandle_t xTaskBHandler;
static TaskHandle_t xTaskCHandler;
static BaseType_t xTaskARan = pdFALSE;
static BaseType_t xTaskBRan = pdFALSE;
static BaseType_t xTaskCRan = pdFALSE;
/*-----------------------------------------------------------*/

void test_fr2TASK_SWITCHED_IN( void )
{
    UBaseType_t xIdx, xNumTasksRunning;
    TaskStatus_t taskStatus[ 16 ];
    UBaseType_t xTaskStatusArraySize = 16;
    unsigned long ulTotalRunTime;

    static uint32_t ulTaskSwitchCount = 0;

    if( !( xTestPassed || xTestFailed ) )
    {
        xNumTasksRunning = uxTaskGetSystemState( ( TaskStatus_t * const ) &taskStatus, xTaskStatusArraySize, &ulTotalRunTime );

        for( xIdx = 0; xIdx < xNumTasksRunning; xIdx++ )
        {
            if( ( strcmp( taskStatus[ xIdx ].pcTaskName, "TaskA" ) == 0 ) && ( taskStatus[ xIdx ].eCurrentState == eRunning ) )
            {
                xTaskARan = pdTRUE;
            }

            if( ( strcmp( taskStatus[ xIdx ].pcTaskName, "TaskB" ) == 0 ) && ( taskStatus[ xIdx ].eCurrentState == eRunning ) )
            {
                xTaskBRan = pdTRUE;
            }

            if( ( strcmp( taskStatus[ xIdx ].pcTaskName, "TaskC" ) == 0 ) && ( taskStatus[ xIdx ].eCurrentState == eRunning ) )
            {
                xTaskCRan = pdTRUE;
            }
        }

        if( xTaskARan == pdTRUE )
        {
            if( !( ( xTaskBRan == pdTRUE ) && ( xTaskCRan == pdTRUE ) ) )
            {
                xTestFailed = pdTRUE;
            }
            else
            {
                xTestPassed = pdTRUE;
            }
        }

        ulTaskSwitchCount++;

        if( ulTaskSwitchCount > 2048 )
        {
            xTestFailed = pdTRUE;
        }
    }
}
/*-----------------------------------------------------------*/

static void vValidateResult( void )
{
    while( xTaskARan != pdTRUE )
    {
        vTaskDelay( pdMS_TO_TICKS( 100 ) );
    }

    /* xTestPassed and xTestFailed set by trace hook: test_fr2TASK_SWITCHED_IN */

    TEST_ASSERT_FALSE( xTestFailed == pdTRUE );
    TEST_ASSERT_TRUE( xTestPassed == pdTRUE );
}
/*-----------------------------------------------------------*/

static void fr02_scheHighestPriority( void )
{
    xTaskCreate( vPrvTaskA, "TaskA", configMINIMAL_STACK_SIZE, NULL,
                 mainTASK_A_PRIORITY, &xTaskAHandler );

    xTaskCreate( vPrvTaskB, "TaskB", configMINIMAL_STACK_SIZE, NULL,
                 mainTASK_B_PRIORITY, &xTaskBHandler );

    xTaskCreate( vPrvTaskC, "TaskC", configMINIMAL_STACK_SIZE, NULL,
                 mainTASK_C_PRIORITY, &xTaskCHandler );

    vValidateResult();

    vTaskDelete( xTaskAHandler );
    vTaskDelete( xTaskBHandler );
    vTaskDelete( xTaskCHandler );
}
/*-----------------------------------------------------------*/

static void vPrvTaskA( void * pvParameters )
{
    /* idle the task */
    for( ; ; )
    {
        vTaskDelay( pdMS_TO_TICKS( 10 ) );

        vPortBusyWaitMicroseconds( ( uint32_t ) 100000 );
    }
}
/*-----------------------------------------------------------*/

static void vPrvTaskB( void * pvParameters )
{
    /* idle the task */
    for( ; ; )
    {
        vTaskDelay( pdMS_TO_TICKS( 10 ) );

        vPortBusyWaitMicroseconds( ( uint32_t ) 100000 );
    }
}
/*-----------------------------------------------------------*/

static void vPrvTaskC( void * pvParameters )
{
    /* idle the task */
    for( ; ; )
    {
        vTaskDelay( pdMS_TO_TICKS( 10 ) );

        vPortBusyWaitMicroseconds( ( uint32_t ) 100000 );
    }
}
/*-----------------------------------------------------------*/

/**
 * @brief A start entry for test runner to run FR02.
 */
void vTestRunner( void )
{
    UNITY_BEGIN();

    RUN_TEST( fr02_scheHighestPriority );

    UNITY_END();
}
/*-----------------------------------------------------------*/
