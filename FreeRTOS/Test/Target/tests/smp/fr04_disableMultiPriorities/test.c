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
 * @brief The user shall be able to configure the scheduler to not run a
 *        lower priority task and a higher priority task simultaneously.
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
static void fr04_validateTasksDoNotRunAtSameTime( void );
/*-----------------------------------------------------------*/

#if configNUMBER_OF_CORES != 2
    #error Require two cores be configured for FreeRTOS
#endif /* if configNUMBER_OF_CORES != 2 */

#if configRUN_MULTIPLE_PRIORITIES != 0
    #error configRUN_MULTIPLE_PRIORITIES shoud be 0 in this test case. Please check if testConfig.h is included.
#endif /* if configRUN_MULTIPLE_PRIORITIES != 0 */

#if configUSE_CORE_AFFINITY != 0
    #error configUSE_CORE_AFFINITY shoud be 0 in this test case. Please check if testConfig.h is included.
#endif /* if configUSE_CORE_AFFINITY != 0 */
/*-----------------------------------------------------------*/

static BaseType_t xTaskBObservedRunning = pdFALSE;
static TaskHandle_t xTaskBHandler;
/*-----------------------------------------------------------*/

static void fr04_validateTasksDoNotRunAtSameTime( void )
{
    UBaseType_t uxOriginalTaskPriority = uxTaskPriorityGet( NULL );

    vTaskPrioritySet( NULL, mainTASK_A_PRIORITY );

    xTaskCreate( vPrvTaskB, "TaskB", configMINIMAL_STACK_SIZE, NULL,
                 mainTASK_B_PRIORITY, &xTaskBHandler );

    /* Run current task as Task A. */
    vPrvTaskA( NULL );

    vTaskPrioritySet( NULL, uxOriginalTaskPriority );

    vTaskDelete( xTaskBHandler );
}
/*-----------------------------------------------------------*/

static void vPrvTaskA( void * pvParameters )
{
    TaskStatus_t taskStatus[ 16 ];
    UBaseType_t xTaskStatusArraySize = 16;
    unsigned long ulTotalRunTime;
    BaseType_t xIdx;
    BaseType_t xAttempt = 1;
    BaseType_t xNumTasksRunning;

    while( !xTaskBObservedRunning )
    {
        xNumTasksRunning = uxTaskGetSystemState( ( TaskStatus_t * const ) &taskStatus, xTaskStatusArraySize, &ulTotalRunTime );

        for( xIdx = 0; xIdx < xNumTasksRunning; xIdx++ )
        {
            if( ( strcmp( taskStatus[ xIdx ].pcTaskName, "TaskB" ) == 0 ) && ( taskStatus[ xIdx ].eCurrentState == eRunning ) )
            {
                xTaskBObservedRunning = true;
            }
        }

        vTaskDelay( pdMS_TO_TICKS( 10 ) );

        xAttempt++;

        if( xAttempt > 25 )
        {
            break;
        }
    }

    TEST_ASSERT_TRUE( !xTaskBObservedRunning );
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

/**
 * @brief A start entry for test runner to run FR04.
 */
void vTestRunner( void )
{
    UNITY_BEGIN();

    RUN_TEST( fr04_validateTasksDoNotRunAtSameTime );

    UNITY_END();
}
/*-----------------------------------------------------------*/
