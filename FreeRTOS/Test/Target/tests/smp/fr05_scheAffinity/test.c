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
 * @brief The scheduler shall not schedule a task that is pinned to a specific core on any other core.
 *
 * Procedure:
 *   -
 *   -
 *   -
 * Expected:
 *   -
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
/*-----------------------------------------------------------*/

static void vPrvTaskA( void * pvParameters );
static void vPrvTaskB( void * pvParameters );
static void fr05_validateTasksOnlyRunOnAssignedCores( void );
/*-----------------------------------------------------------*/

#if configNUMBER_OF_CORES != 2
    #error Require two cores be configured for FreeRTOS
#endif /* if configNUMBER_OF_CORES != 2 */

#if configUSE_TASK_PREEMPTION_DISABLE != 1
    #error configUSE_TASK_PREEMPTION_DISABLE shoud be 1 in this test case. Please check if testConfig.h is included.
#endif /* if configUSE_CORE_AFFINITY != 0 */
/*-----------------------------------------------------------*/

static TaskHandle_t xTaskBHandler;
static BaseType_t xTaskBDone = pdFALSE;
static BaseType_t xTaskAOnCorrectCore = pdTRUE;
static BaseType_t xTaskBOnCorrectCore = pdTRUE;
/*-----------------------------------------------------------*/

static void fr05_validateTasksOnlyRunOnAssignedCores( void )
{
    UBaseType_t uxOriginalTaskPriority = uxTaskPriorityGet( NULL );
    UBaseType_t uxOriginalTaskAffinity = vTaskCoreAffinityGet( NULL );

    vTaskPrioritySet( NULL, mainTASK_A_PRIORITY );
    vTaskCoreAffinitySet( NULL, 0x1 );

    xTaskCreateAffinitySet( vPrvTaskB, "TaskB", configMINIMAL_STACK_SIZE, NULL,
                            mainTASK_B_PRIORITY, 0x2, &xTaskBHandler );

    taskYIELD();

    vPrvTaskA( NULL );

    vTaskPrioritySet( NULL, uxOriginalTaskPriority );
    vTaskCoreAffinitySet( NULL, uxOriginalTaskAffinity );

    vTaskDelete( xTaskBHandler );
}
/*-----------------------------------------------------------*/

static void vPrvTaskA( void * pvParameters )
{
    BaseType_t xCore;

    uint32_t ulIter;

    for( ulIter = 1; ulIter < 25; ulIter++ )
    {
        vTaskDelay( pdMS_TO_TICKS( 10 ) );
        xCore = portGET_CORE_ID();

        if( xCore != 0 )
        {
            xTaskAOnCorrectCore = pdFALSE;
        }
    }

    while( ( xTaskBDone == pdFALSE ) )
    {
        vPortBusyWaitMicroseconds( ( uint32_t ) 100000 );
    }

    TEST_ASSERT_TRUE( xTaskAOnCorrectCore == pdTRUE );
    TEST_ASSERT_TRUE( xTaskBOnCorrectCore == pdTRUE );
}
/*-----------------------------------------------------------*/

static void vPrvTaskB( void * pvParameters )
{
    BaseType_t xCore;
    uint32_t ulIter;

    for( ulIter = 1; ulIter < 25; ulIter++ )
    {
        vTaskDelay( pdMS_TO_TICKS( 10 ) );
        xCore = portGET_CORE_ID();

        if( xCore != 1 )
        {
            xTaskBOnCorrectCore = pdFALSE;
        }
    }

    xTaskBDone = pdTRUE;

    /* idle the task */
    for( ; ; )
    {
        vTaskDelay( pdMS_TO_TICKS( 100 ) );
    }
}
/*-----------------------------------------------------------*/

/**
 * @brief A start entry for test runner to run FR05.
 */
void vTestRunner( void )
{
    UNITY_BEGIN();

    RUN_TEST( fr05_validateTasksOnlyRunOnAssignedCores );

    UNITY_END();
}
/*-----------------------------------------------------------*/
