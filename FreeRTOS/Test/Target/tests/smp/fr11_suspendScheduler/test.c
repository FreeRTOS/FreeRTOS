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
 * @brief Context switch shall not happen when the scheduler is suspended.
 *
 * Procedure:
 *   - Create tasks A & B, with A having a higher priority.
 *   - Use a testConfgi with configRUN_MULTIPLE_PRIORITIES set to 0
 *   - Task A calls vTaskSuspectAll, incresases a state vairable and
 *     then increases the priority of task B.
 *   - Task B is programmed to increase a state variable
 * Expected:
 *   - Validate that before task A re-enables the scheduler, task B
 *     has not run by checking that it has not incremented its internal
 *     state variable.
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
#define mainTASK_A_PRIORITY      ( tskIDLE_PRIORITY + 2 )
#define mainTASK_B_PRIORITY      ( tskIDLE_PRIORITY + 1 )
/*-----------------------------------------------------------*/

#define TASK_BLOCK_TIME_MS       ( 3000 )
#define TASK_BUSYLOOP_TIME_MS    ( 100 )
/*-----------------------------------------------------------*/

static void vPrvTaskA( void * pvParameters );
static void vPrvTaskB( void * pvParameters );
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

static TaskHandle_t xTaskBHandler;
static uint32_t ulTaskAState = 0;
static uint32_t ulTaskBState = 0;
static uint32_t ulTempTaskBState = 0;
/*-----------------------------------------------------------*/

static void fr11_validate_NoContextSwitchesOccurWhileSchedulerIsSuspended( void )
{
    UBaseType_t uxOriginalTaskPriority = uxTaskPriorityGet( NULL );

    vTaskPrioritySet( NULL, mainTASK_A_PRIORITY );

    xTaskCreate( vPrvTaskB, "TaskB", configMINIMAL_STACK_SIZE, NULL,
                 mainTASK_B_PRIORITY, &xTaskBHandler );

    vPrvTaskA( NULL );

    TEST_ASSERT_TRUE( ulTempTaskBState == 0 );

    vTaskPrioritySet( NULL, uxOriginalTaskPriority );
    vTaskDelete( xTaskBHandler );
}
/*-----------------------------------------------------------*/

static void vPrvTaskA( void * pvParameters )
{
    uint32_t ulAttempTime = 0;

    vTaskSuspendAll();

    ulTaskAState++;

    vTaskPrioritySet( xTaskBHandler, mainTASK_B_PRIORITY + 1 );

    while( ulTaskBState == 0 )
    {
        ulAttempTime++;

        if( ulAttempTime > ( TASK_BLOCK_TIME_MS / TASK_BUSYLOOP_TIME_MS ) )
        {
            /* Break after polling 30 times. (total 3s) */
            break;
        }

        /* Wait 100ms. */
        vPortBusyWaitMicroseconds( ( uint32_t ) ( TASK_BUSYLOOP_TIME_MS * 1000 ) );
    }

    /* Cache uTaskBState before resuming all tasks. */
    ulTempTaskBState = ulTaskBState;

    xTaskResumeAll();
}
/*-----------------------------------------------------------*/

static void vPrvTaskB( void * pvParameters )
{
    while( ulTaskAState == 0 )
    {
        vPortBusyWaitMicroseconds( ( uint32_t ) 10000 );
    }

    ulTaskBState++;

    /* idle the task */
    for( ; ; )
    {
        vPortBusyWaitMicroseconds( ( uint32_t ) 10000 );
    }
}
/*-----------------------------------------------------------*/

/**
 * @brief A start entry for test runner to run FR11.
 */
void vTestRunner( void )
{
    UNITY_BEGIN();

    RUN_TEST( fr11_validate_NoContextSwitchesOccurWhileSchedulerIsSuspended );

    UNITY_END();
}
/*-----------------------------------------------------------*/
