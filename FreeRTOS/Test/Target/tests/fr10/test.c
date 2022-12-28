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
 * @brief Implements FR10 test functions for SMP on target test.
 */

/* Kernel includes. */

#include "FreeRTOS.h" /* Must come first. */
#include "queue.h"    /* RTOS queue related API prototypes. */
#include "semphr.h"   /* Semaphore related API prototypes. */
#include "task.h"     /* RTOS task related API prototypes. */
#include "timers.h"   /* Software timer related API prototypes. */

#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

#include "bsl.h"
#include "unity.h" /* unit testing support functions */

/*-----------------------------------------------------------*/

/**
 * @brief Task priority for task A.
 */
#define mainTASK_A_PRIORITY              ( tskIDLE_PRIORITY + 2 )

/**
 * @brief Task priority for task B.
 */
#define mainTASK_B_PRIORITY              ( tskIDLE_PRIORITY + 1 )

/**
 * @brief Maximum value for counter to increase to.
 */
#define COUNTER_MAX                      ( 3000 )

/**
 * @brief Idle period for prvTestRunnerTask to delay at the end.
 */
#define mainSOFTWARE_TIMER_PERIOD_MS     pdMS_TO_TICKS( 10 )

/**
 * @brief Timeout value for task A to wait for Task B.
 */
#define WAIT_TASK_B_FINISH_TIMEOUT_MS    ( 3000 )

/**
 * @brief Polling value for task A to wait for Task B.
 */
#define WAIT_TASK_B_POLLING_MS           ( 100 )

/*-----------------------------------------------------------*/

#if configNUMBER_OF_CORES <= 1
    #error Require two cores be configured for FreeRTOS
#endif

/*-----------------------------------------------------------*/

/**
 * @brief A counter for task A&B to increase.
 */
static volatile BaseType_t xTaskCounter = 0;

/**
 * @brief A flag to show if task B is finished.
 */
static volatile BaseType_t xIsTaskBFinished = pdFALSE;

/*-----------------------------------------------------------*/

/* Function declaration. */
static void prvTestRunnerTask( void * pvParameters );
static void fr10_onlyOneTaskEnterSuspendAll( void );
static void prvTaskA( void );
static void prvTaskB( void * pvParameters );

/*-----------------------------------------------------------*/

/* Is run before every test, put unit init calls here. */
void setUp( void )
{
}

/*-----------------------------------------------------------*/

/* Is run after every test, put unit clean-up calls here. */
void tearDown( void )
{
}

/*-----------------------------------------------------------*/

int main( void )
{
    vPortInitTestEnvironment();

    /* prvTestRunnerTask run as Task A after setting Unity. */
    xTaskCreate( prvTestRunnerTask, "testRunner", configMINIMAL_STACK_SIZE * 2, NULL,
                 mainTASK_A_PRIORITY, NULL );

    vTaskStartScheduler();

    /* should never reach here */
    panic_unsupported();

    return 0;
}

/*-----------------------------------------------------------*/

/**
 * @brief A start entry for unity to start with.
 *
 * @param[in] pvParameters parameter for task entry, useless in this test.
 */
static void prvTestRunnerTask( void * pvParameters )
{
    UNITY_BEGIN();

    RUN_TEST( fr10_onlyOneTaskEnterSuspendAll );

    UNITY_END();

    /* idle the task */
    for( ; ; )
    {
        vTaskDelay( mainSOFTWARE_TIMER_PERIOD_MS );
    }
}

/*-----------------------------------------------------------*/

/**
 * @brief Test case FR10 to verify that only one task shall be able to enter the section
 * protected by vTaskSuspendAll/xTaskResumeAll. We have two tasks, A and B, running in parallel.
 * Test flow lists in order below:
 *   - Task A calls vTaskSuspendAll
 *   - Task A increases the counter to COUNTER_MAX
 *   - Task A calls xTaskResumeAll
 *   - Task B calls vTaskSuspendAll
 *   - Task B increases the counter by 1
 *   - Task B calls xTaskResumeAll
 */
static void fr10_onlyOneTaskEnterSuspendAll( void )
{
    /* Create task B to run on another core. */
    xTaskCreate( prvTaskB, "TaskB", configMINIMAL_STACK_SIZE * 2, NULL,
                 mainTASK_B_PRIORITY, NULL );

    /* Run as Task A. */
    prvTaskA();
}

/*-----------------------------------------------------------*/

/**
 * @brief Task A entry function, called by prvTestRunnerTask directly.
 */
static void prvTaskA( void )
{
    uint32_t ulIndex = 0;
    int32_t lRemainingWaitTimeMs = WAIT_TASK_B_FINISH_TIMEOUT_MS;
    BaseType_t xTempCounter = 0;

    vTaskSuspendAll();

    for( ulIndex = 0; ulIndex < COUNTER_MAX; ulIndex++ )
    {
        /* Increase xTaskCounter COUNTER_MAX time. xTaskCounter is not COUNTER_MAX if task B enters vTaskSuspendAll. */
        xTaskCounter++;
        vPortBusyWaitMicroseconds( (uint32_t) 1000 );
    }

    /* Record current counter value because we can't get error message from UNITY_ASSERT* functions in vTaskSuspendAll. */
    xTempCounter = xTaskCounter;

    xTaskResumeAll();

    /* If task B increases before task A calling xTaskResumeAll, xTempCounter might NOT be COUNTER_MAX.
     * This checks below scenario:
     *   - Task A read xTaskCounter(N) value to register.
     *   - Task A increases xTaskCounter value by 1(N+1).
     *   - Task A stores xTaskCounter value(N+1) back to memory.
     *   - Task B read xTaskCounter value(N+1) to register.
     *   - Task B increases xTaskCounter value by 1(N+2).
     *   - Task B stores xTaskCounter value(N+2) back to memory. */
    TEST_ASSERT_EQUAL_INT( xTempCounter, COUNTER_MAX );

    while( ( xIsTaskBFinished == pdFALSE ) && ( lRemainingWaitTimeMs > 0 ) )
    {
        vPortBusyWaitMicroseconds( (uint32_t) (WAIT_TASK_B_POLLING_MS * 1000) );
        lRemainingWaitTimeMs -= WAIT_TASK_B_POLLING_MS;
    }

    /* Make sure Task B is finished normally. */
    TEST_ASSERT_TRUE( xIsTaskBFinished == pdTRUE );

    /* If task B increases before task A calling xTaskResumeAll, xTempCounter might NOT be COUNTER_MAX + 1.
     * This checks below scenario:
     *   - Task A read xTaskCounter value(N) to register.
     *   - Task A increases xTaskCounter value by 1(N+1).
     *   - Task B read xTaskCounter value(N) to register.
     *   - Task B increases xTaskCounter value by 1(N+1).
     *   - Task A stores xTaskCounter value(N+1) back to memory.
     *   - Task B stores xTaskCounter value(N+1) back to memory. */
    TEST_ASSERT_EQUAL_INT( xTaskCounter, COUNTER_MAX + 1 );
}

/*-----------------------------------------------------------*/

/**
 * @brief Task B entry function, created by xTaskCreate.
 *
 * @param[in] pvParameters parameter for task entry, useless in this test.
 */
static void prvTaskB( void * pvParameters )
{
    /* Wait task A to start first. */
    while( xTaskCounter < 1 )
    {
        vPortBusyWaitMicroseconds( (uint32_t) 1 );
    }

    vTaskSuspendAll();

    /* Increase 1 to xTaskCounter and it should be COUNTER_MAX + 1 after increasing. */
    xTaskCounter++;

    xTaskResumeAll();

    /* Set xIsTaskBFinished to pdTRUE to let task A know that task B is finished. */
    xIsTaskBFinished = pdTRUE;

    vTaskDelete( NULL );
}

/*-----------------------------------------------------------*/
