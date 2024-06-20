/*
 * FreeRTOS V202212.00
 * Copyright (C) 2022 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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
 * @file interrupt_wait_critical.c
 * @brief If a task is interrupted while it is waiting to enter a critical
 *        section, it shall relinquish the core instead of continuing to wait to
 *        enter the critical section.
 *
 * Procedure:
 *   - Create 1 low priority task, T0.
 *   - Create n - 1 high priority tasks, T1~Tn-1.
 *   - Create 1 high priority task, Tn.
 *   - Tasks T1~Tn-1 suspends themselves.
 *   - Tn enters critical section.
 *   - T0 attempts to enter critical section and busy waits to enter
 *     critical section.
 *   - Tn resumes tasks T1-Tn-1.
 *   - At this point, tasks T1-Tn are ready and must be running. As a result, T0
 *   - must have been interrupted while busy waiting to enter critical section.
 *   - Tn leaves critical section.
 * Expected:
 *   - T0 must not enter the critical section as it was interrupted while busy
 *     waiting to enter critical section.
 */

/* Standard includes. */
#include <stdint.h>

/* Kernel includes. */
#include "FreeRTOS.h"
#include "task.h"

/* Unit testing support functions. */
#include "unity.h"
/*-----------------------------------------------------------*/

/**
 * @brief Busy looping count to wait for other cores.
 */
#define TEST_BUSY_LOOPING_COUNT    ( 10000U )

/**
 * @brief Nop operation for busy looping.
 */
#ifdef portNOP
    #define TEST_NOP    portNOP
#else
    #define TEST_NOP()    __asm volatile ( "nop" )
#endif

/**
 * @brief Timeout value to stop test.
 */
#define TEST_TIMEOUT_MS    ( 1000 )
/*-----------------------------------------------------------*/

#if ( configNUMBER_OF_CORES < 2 )
    #error This test is for FreeRTOS SMP and therefore, requires at least 2 cores.
#endif /* if ( configNUMBER_OF_CORES < 2 ) */

#if ( configRUN_MULTIPLE_PRIORITIES != 1 )
    #error configRUN_MULTIPLE_PRIORITIES must be enabled by including test_config.h in FreeRTOSConfig.h.
#endif /* if ( configRUN_MULTIPLE_PRIORITIES != 1 ) */

#if ( configMAX_PRIORITIES <= 3 )
    #error configMAX_PRIORITIES must be larger than 3 to avoid scheduling idle tasks unexpectedly.
#endif /* if ( configMAX_PRIORITIES <= 3 ) */
/*-----------------------------------------------------------*/

/**
 * @brief Low priority task function that tries to enter critical section.
 */
static void prvLowPriorityEnterCriticalTask( void * pvParameters );

/**
 * @brief High priority task function that tries to enter critical section.
 */
static void prvHighPriorityEnterCriticalTask( void * pvParameters );

/**
 * @brief Function that implements a never blocking FreeRTOS task.
 */
static void prvEverRunningTask( void * pvParameters );

/**
 * @brief Test case "Interrupt Wait Critical".
 */
void Test_InterruptWaitCritical( void );
/*-----------------------------------------------------------*/

/**
 * @brief Handles of the tasks created in this test.
 */
static TaskHandle_t xTaskHandles[ configNUMBER_OF_CORES + 1 ];

/**
 * @brief A flag to trace if high priority task entered critical section.
 */
static volatile BaseType_t xHighPriorityTaskEnterCriticalSection = pdFALSE;

/**
 * @brief A flag to trace if low priority task entered critical section.
 */
static volatile BaseType_t xLowPriorityTaskEnterCriticalSection = pdFALSE;
/*-----------------------------------------------------------*/

static void prvEverRunningTask( void * pvParameters )
{
    /* Silence warnings about unused parameters. */
    ( void ) pvParameters;

    vTaskSuspend( NULL );

    for( ; ; )
    {
        TEST_NOP();
    }
}
/*-----------------------------------------------------------*/

static void prvLowPriorityEnterCriticalTask( void * pvParameters )
{
    /* Silence warnings about unused parameters. */
    ( void ) pvParameters;

    /* Wait for the high priority task Tn to enter the critical section first. */
    while( xHighPriorityTaskEnterCriticalSection == pdFALSE )
    {
    }

    /* The high priority task Tn is inside the critical section. So this low
     * priority task must busy wait here to enter critical section. Tn resumes
     * tasks T1~Tn-1 from within the critical section. As a result, n tasks
     * T1~Tn are ready to run when this task is busy waiting here to enter
     * critical section. Since n higher priority tasks are ready, this low
     * priority task must be interrupted and relinquish the core. */
    taskENTER_CRITICAL();
    {
        /* As this task must relinquish this core instead of entering the
         * critical section, this line must not be run. */
        xLowPriorityTaskEnterCriticalSection = pdTRUE;
    }
    taskEXIT_CRITICAL();

    for( ; ; )
    {
        TEST_NOP();
    }
}
/*-----------------------------------------------------------*/

static void prvHighPriorityEnterCriticalTask( void * pvParameters )
{
    uint32_t i;
    eTaskState taskState;
    BaseType_t xAllTasksInExpectedState = pdFALSE;

    /* Silence warnings about unused parameters. */
    ( void ) pvParameters;

    /* Check that low priority task T0 is running and high priority tasks
     * T1~Tn-1 are suspended. */
    while( xAllTasksInExpectedState == pdFALSE )
    {
        /* Check the state of low priority task T0. */
        taskState = eTaskGetState( xTaskHandles[ 0 ] );

        if( taskState == eRunning )
        {
            /* Check the state of high priority tasks T1~Tn-1. */
            for( i = 1; i < configNUMBER_OF_CORES; i++ )
            {
                taskState = eTaskGetState( xTaskHandles[ i ] );

                if( taskState != eSuspended )
                {
                    break;
                }
            }

            if( i == configNUMBER_OF_CORES )
            {
                xAllTasksInExpectedState = pdTRUE;
            }
        }
    }

    taskENTER_CRITICAL();
    {
        xHighPriorityTaskEnterCriticalSection = pdTRUE;

        /* Busy looping here to wait for low priority task. */
        for( i = 0; i < TEST_BUSY_LOOPING_COUNT; i++ )
        {
            TEST_NOP();
        }

        /* Resume tasks T1~Tn-1. All the n cores must be occupied by tasks T1~Tn
         * as these are higher priority tasks. The low priority task T0 which is
         * busy waiting to enter critical section, must be interrupted. */
        for( i = 1; i < configNUMBER_OF_CORES; i++ )
        {
            vTaskResume( xTaskHandles[ i ] );
        }
    }
    taskEXIT_CRITICAL();

    for( ; ; )
    {
        /* Always running, put asm here to avoid optimization by compiler. */
        TEST_NOP();
    }
}
/*-----------------------------------------------------------*/

void Test_InterruptWaitCritical( void )
{
    uint32_t i;
    BaseType_t xTaskCreationResult;

    /* Create one task T0 with low priority. */
    xTaskCreationResult = xTaskCreate( prvLowPriorityEnterCriticalTask,
                                       "EnterCSLow",
                                       configMINIMAL_STACK_SIZE,
                                       NULL,
                                       configMAX_PRIORITIES - 3,
                                       &( xTaskHandles[ 0 ] ) );

    TEST_ASSERT_EQUAL_MESSAGE( pdPASS, xTaskCreationResult, "Task creation failed." );

    /* Create ( configNUMBER_OF_CORES - 1 ) tasks T1-Tn-1 with high priority. */
    for( i = 1; i < configNUMBER_OF_CORES; i++ )
    {
        xTaskCreationResult = xTaskCreate( prvEverRunningTask,
                                           "EverRunning",
                                           configMINIMAL_STACK_SIZE,
                                           NULL,
                                           configMAX_PRIORITIES - 2,
                                           &( xTaskHandles[ i ] ) );

        TEST_ASSERT_EQUAL_MESSAGE( pdPASS, xTaskCreationResult, "Task creation failed." );
    }

    /* Create one task Tn with high priority. */
    xTaskCreationResult = xTaskCreate( prvHighPriorityEnterCriticalTask,
                                       "EnterCSHigh",
                                       configMINIMAL_STACK_SIZE,
                                       NULL,
                                       configMAX_PRIORITIES - 2,
                                       &( xTaskHandles[ configNUMBER_OF_CORES ] ) );

    TEST_ASSERT_EQUAL_MESSAGE( pdPASS, xTaskCreationResult, "Task creation failed." );

    vTaskDelay( pdMS_TO_TICKS( TEST_TIMEOUT_MS ) );

    /* Verify the high priority task entered the critical section. */
    TEST_ASSERT_EQUAL_MESSAGE( pdTRUE, xHighPriorityTaskEnterCriticalSection, "High priority task not enter the critical section." );

    /* Verify the low priority task relinquishes the core when it is interrupted
     * while waiting to enter a critical section. */
    TEST_ASSERT_EQUAL_MESSAGE( pdFALSE, xLowPriorityTaskEnterCriticalSection, "Low priority task should relinquish the core." );

    /* Suspend the high priority task Tn and block the test runner. The low
     * priority task should be able to enter the critical section now due to a
     * core being available. */
    vTaskSuspend( xTaskHandles[ configNUMBER_OF_CORES ] );
    vTaskDelay( pdMS_TO_TICKS( TEST_TIMEOUT_MS ) );

    /* Verify the low priority task was able to enter the critical section. */
    TEST_ASSERT_EQUAL_MESSAGE( pdTRUE, xLowPriorityTaskEnterCriticalSection, "Low priority task should enter the critical section." );
}
/*-----------------------------------------------------------*/

/* Runs before every test, put init calls here. */
void setUp( void )
{
    uint32_t i;

    for( i = 0U; i < ( configNUMBER_OF_CORES + 1 ); i++ )
    {
        xTaskHandles[ i ] = NULL;
    }

    xHighPriorityTaskEnterCriticalSection = pdFALSE;
    xLowPriorityTaskEnterCriticalSection = pdFALSE;
}
/*-----------------------------------------------------------*/

/* Runs after every test, put clean-up calls here. */
void tearDown( void )
{
    uint32_t i;

    /* Delete all the tasks. */
    for( i = 0; i < ( configNUMBER_OF_CORES + 1 ); i++ )
    {
        if( xTaskHandles[ i ] != NULL )
        {
            vTaskDelete( xTaskHandles[ i ] );
            xTaskHandles[ i ] = NULL;
        }
    }
}
/*-----------------------------------------------------------*/

/**
 * @brief Entry point for test runner to run interrupt task wait critical section test.
 */
void vRunInterruptWaitCriticalTest( void )
{
    UNITY_BEGIN();

    RUN_TEST( Test_InterruptWaitCritical );

    UNITY_END();
}
/*-----------------------------------------------------------*/
