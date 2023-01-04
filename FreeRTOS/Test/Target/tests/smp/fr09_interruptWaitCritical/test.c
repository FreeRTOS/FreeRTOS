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
 * @brief If a task is interrupted while it is waiting to enter a critical section,
 *        it shall relinquish the core instead of continuing to wait to enter critical section.
 *
 * Procedure:
 *   - Create tasks A, B, & C. With A having a priority of 2 and B & C having a priority of 1
 *   - Task A is pinned to the second core.
 *   - Task A enters a critical section, then busy waits for 250ms, then calls vTaskSuspend
 *     to attempt to unschedule task B, and then busy waits for 10sec.
 *   - Task B waits 10ms and then attempts to enter a critical section
 *   - Task C executes a busy wait for 250ms
 *   - traceTASK_SWITCHED_IN is defined in order to validate scheduler behavior.
 * Expected:
 *   - The xTaskNotify will cause TaskB which was waiting to enter a critical section to
 *     yield to taskC which has equal priority.
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
#define mainTASK_A_PRIORITY    ( tskIDLE_PRIORITY + 2 )
#define mainTASK_B_PRIORITY    ( tskIDLE_PRIORITY + 1 )
#define mainTASK_C_PRIORITY    ( tskIDLE_PRIORITY + 1 )

static void vPrvTaskA( void * pvParameters );
static void vPrvTaskB( void * pvParameters );
static void vPrvTaskC( void * pvParameters );
/*-----------------------------------------------------------*/

#if configNUMBER_OF_CORES != 2
    #error Require two cores be configured for FreeRTOS
#endif /* if configNUMBER_OF_CORES != 2 */

#if traceTASK_SWITCHED_IN != test_fr9TASK_SWITCHED_IN
    #error Need to include testConfig.h in FreeRTOSConfig.h
#endif /* if traceTASK_SWITCHED_IN != test_fr2TASK_SWITCHED_IN */
/*-----------------------------------------------------------*/

static TaskHandle_t xTaskAHandler;
static TaskHandle_t xTaskBHandler;
static TaskHandle_t xTaskCHandler;
static BaseType_t xTestFailed = pdFALSE;
static BaseType_t xAllTasksHaveRun = pdFALSE;
static BaseType_t xTaskAHasEnteredCriticalSection = pdFALSE;
static BaseType_t xTaskAHasExitedCriticalSection = pdFALSE;
static BaseType_t xTaskBHasEnteredCriticalSection = pdFALSE;

static uint32_t ulTaskSwitchCount = 0;
static BaseType_t xTaskARan = pdFALSE;
static BaseType_t xTaskBRan = pdFALSE;
static BaseType_t xTaskCRan = pdFALSE;
TaskHandle_t taskA, taskB;
/*-----------------------------------------------------------*/

void test_fr9TASK_SWITCHED_IN( void )
{
    UBaseType_t uxIdx, uxNumTasksRunning;
    TaskStatus_t taskStatus[ 16 ];
    UBaseType_t uxTaskStatusArraySize = 16;
    unsigned long ulTotalRunTime;

    if( ( ( xAllTasksHaveRun == pdFALSE ) && ( xTestFailed == pdFALSE ) ) )
    {
        uxNumTasksRunning = uxTaskGetSystemState( ( TaskStatus_t * const ) &taskStatus, uxTaskStatusArraySize, &ulTotalRunTime );

        for( uxIdx = 0; uxIdx < uxNumTasksRunning; uxIdx++ )
        {
            if( ( strcmp( taskStatus[ uxIdx ].pcTaskName, "TaskA" ) == 0 ) && ( taskStatus[ uxIdx ].eCurrentState == eRunning ) )
            {
                xTaskARan = pdTRUE;
            }

            if( ( strcmp( taskStatus[ uxIdx ].pcTaskName, "TaskB" ) == 0 ) && ( taskStatus[ uxIdx ].eCurrentState == eRunning ) )
            {
                xTaskBRan = pdTRUE;
            }

            if( ( strcmp( taskStatus[ uxIdx ].pcTaskName, "TaskC" ) == 0 ) && ( taskStatus[ uxIdx ].eCurrentState == eRunning ) )
            {
                xTaskCRan = pdTRUE;
            }
        }

        if( ( xTaskARan == pdTRUE ) && ( xTaskCRan == pdTRUE ) && ( xTaskBRan == pdTRUE ) )
        {
            xAllTasksHaveRun = pdTRUE;
        }

        ulTaskSwitchCount++;

        if( ulTaskSwitchCount > 1500 )
        {
            xTestFailed = pdTRUE;
        }
    }
}
/*-----------------------------------------------------------*/

static void fr09_validateAllTasksHaveRun( void )
{
    xTaskCreateAffinitySet( vPrvTaskA, "TaskA", configMINIMAL_STACK_SIZE, NULL,
                            mainTASK_A_PRIORITY, 0x2, &xTaskAHandler );

    xTaskCreate( vPrvTaskB, "TaskB", configMINIMAL_STACK_SIZE, NULL,
                 mainTASK_B_PRIORITY, &xTaskBHandler );

    xTaskCreate( vPrvTaskC, "TaskC", configMINIMAL_STACK_SIZE, NULL,
                 mainTASK_C_PRIORITY, &xTaskCHandler );

    while( !xAllTasksHaveRun )
    {
        vTaskDelay( pdMS_TO_TICKS( 100 ) );
    }

    TEST_ASSERT_TRUE( xTaskBHasEnteredCriticalSection == pdFALSE );
}
/*-----------------------------------------------------------*/

static void vPrvTaskA( void * pvParameters )
{
    taskENTER_CRITICAL();
    xTaskAHasEnteredCriticalSection = pdTRUE;
    vPortBusyWaitMicroseconds( ( uint32_t ) 250000 );
    // xTaskNotify( xTaskBHandler, 0, eNoAction );
    vTaskSuspend( xTaskBHandler );
    vPortBusyWaitMicroseconds( ( uint32_t ) 10000000 );
    taskEXIT_CRITICAL();
    xTaskAHasExitedCriticalSection = pdTRUE;

    /* idle the task */
    for( ; ; )
    {
        vTaskDelay( pdMS_TO_TICKS( 10 ) );
    }
}
/*-----------------------------------------------------------*/

static void vPrvTaskB( void * pvParameters )
{
    vTaskDelay( pdMS_TO_TICKS( 10 ) );

    taskENTER_CRITICAL();
    xTaskBHasEnteredCriticalSection = pdTRUE;
    vPortBusyWaitMicroseconds( ( uint32_t ) 8000000 );
    taskEXIT_CRITICAL();

    /* idle the task */
    for( ; ; )
    {
        vTaskDelay( pdMS_TO_TICKS( 10 ) );
    }
}
/*-----------------------------------------------------------*/

static void vPrvTaskC( void * pvParameters )
{
    vPortBusyWaitMicroseconds( ( uint32_t ) 250000 );

    /* idle the task */
    for( ; ; )
    {
        vTaskDelay( pdMS_TO_TICKS( 10 ) );
    }
}
/*-----------------------------------------------------------*/

/**
 * @brief A start entry for test runner to run FR09.
 */
void vTestRunner( void )
{
    UNITY_BEGIN();

    RUN_TEST( fr09_validateAllTasksHaveRun );

    UNITY_END();
}
/*-----------------------------------------------------------*/
