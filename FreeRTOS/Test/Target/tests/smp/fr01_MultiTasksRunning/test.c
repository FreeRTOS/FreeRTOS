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
 * @brief The user shall be able to schedule tasks across multiple identical processor cores
 *        with one instance of FreeRTOS scheduler.
 *
 * Procedure:
 *   - Create task A & B
 *   - Task B keep in busy loop
 *   - Task A check if task B is running
 * Expected:
 *   - Both task A & B can run at the same time
 */

/* Kernel includes. */
#include "FreeRTOS.h" /* Must come first. */
#include "task.h"     /* RTOS task related API prototypes. */

#include <string.h>

#include "bsl.h"
#include "unity.h" /* unit testing support functions */

/*-----------------------------------------------------------*/

#define mainTASK_A_PRIORITY    ( tskIDLE_PRIORITY + 2 )
#define mainTASK_B_PRIORITY    ( tskIDLE_PRIORITY + 2 )

/*-----------------------------------------------------------*/

#if configNUMBER_OF_CORES != 2
    #error Require two cores be configured for FreeRTOS
#endif /* if configNUMBER_OF_CORES != 2 */

/*-----------------------------------------------------------*/

/* Function declaration. */
static void fr01_validateOtherTaskRuns( void );
static void vPrvTaskA( void );
static void vPrvTaskB( void * pvParameters );

/*-----------------------------------------------------------*/

static BaseType_t xTaskBObservedRunning = pdFALSE;

TaskHandle_t xTaskBHandler;

/*-----------------------------------------------------------*/

static void fr01_validateOtherTaskRuns( void )
{
    UBaseType_t uxOriginalTaskPriority = uxTaskPriorityGet( NULL );

    vTaskPrioritySet( NULL, mainTASK_A_PRIORITY );

    xTaskCreate( vPrvTaskB, "TaskB", configMINIMAL_STACK_SIZE, NULL,
                 mainTASK_B_PRIORITY, &xTaskBHandler );

    /* Run current task as Task A. */
    vPrvTaskA();

    vTaskPrioritySet( NULL, uxOriginalTaskPriority );
}

/*-----------------------------------------------------------*/

static void vPrvTaskA( void )
{
    int32_t lHandlerNum = -1;
    TaskStatus_t xTaskStatus[ 16 ];
    UBaseType_t xTaskStatusArraySize = 16;
    uint32_t ulTotalRunTime;
    UBaseType_t xIdx;
    uint32_t ulAttempt = 1;
    UBaseType_t xNumTasksRunning;

    while( xTaskBObservedRunning == pdFALSE )
    {
        xNumTasksRunning = uxTaskGetSystemState( ( TaskStatus_t * const ) &xTaskStatus, xTaskStatusArraySize, &ulTotalRunTime );

        for( xIdx = 0; xIdx < xNumTasksRunning; xIdx++ )
        {
            if( ( strcmp( xTaskStatus[ xIdx ].pcTaskName, "TaskB" ) == 0 ) && ( xTaskStatus[ xIdx ].eCurrentState == eRunning ) )
            {
                /* Found that task B is run at the same time with task A. */
                xTaskBObservedRunning = pdTRUE;
                break;
            }
        }

        vPortBusyWaitMicroseconds( ( uint32_t ) 10000 );

        ulAttempt++;

        if( ulAttempt > 100 )
        {
            break;
        }
    }

    TEST_ASSERT_TRUE( xTaskBObservedRunning == pdTRUE );

    vTaskDelete( xTaskBHandler );
}

/*-----------------------------------------------------------*/

static void vPrvTaskB( void * pvParameters )
{
    /* busyloop for observation by vPrvTaskA. */
    for( ; ; )
    {
        vPortBusyWaitMicroseconds( ( uint32_t ) 100000 );
    }
}

/*-----------------------------------------------------------*/

/**
 * @brief A start entry for test runner to run FR10.
 */
void vTestRunner( void )
{
    UNITY_BEGIN();

    RUN_TEST( fr01_validateOtherTaskRuns );

    UNITY_END();
}
