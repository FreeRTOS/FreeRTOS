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
 * @brief If a task is interrupted while it is waiting to enter a critical section,
 *        it shall relinquish the core instead of continuing to wait to enter critical section.
 *
 * Procedure:
 *   - Create 1 low priority task, T0, to enter the critical section.
 *   - Create n - 1 high priority tasks, T1 ~ T(n - 1), to occupy the core.
 *   - Create 1 high priority task, Tn, to enter the critical section.
 *   - Tn enters the critical section. T0 is waiting to enter the critical section.
 *   - T1 ~ T(n - 1) suspend themselves.
 *   - Tn resume T1 ~ T(n - 1) in the critical section then leave the critical section.
 * Expected:
 *   - T0 doesn't enter the critical section since it's waiting for critical section is interrupted.
 */

/* Standard includes. */
#include <stdint.h>

/* Kernel includes. */
#include "FreeRTOS.h" /* Must come first. */
#include "task.h"     /* RTOS task related API prototypes. */

#include "unity.h"    /* unit testing support functions */
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
 * @brief A flag to know if high priority entered critical section.
 */
static volatile BaseType_t xHighPriorityTaskEnterCriticalSection = pdFALSE;

/**
 * @brief A flag to know if low priority entered critical section.
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
        /* Always running, put asm here to avoid optimization by compiler. */
        TEST_NOP();
    }
}
/*-----------------------------------------------------------*/

static void prvLowPriorityEnterCriticalTask( void * pvParameters )
{
    /* Silence warnings about unused parameters. */
    ( void ) pvParameters;

    /* Waiting for high priority task to enter the critical section first. */
    while( xHighPriorityTaskEnterCriticalSection == pdFALSE )
    {
    }

    taskENTER_CRITICAL();
    {
        /* This line should not be run if other higher priority tasks are waken
         * up. This task should relinquish this core instead of entering the critical
         * section. */
        xLowPriorityTaskEnterCriticalSection = pdTRUE;
    }
    taskEXIT_CRITICAL();

    for( ; ; )
    {
        /* Always running, put asm here to avoid optimization by compiler. */
        TEST_NOP();
    }
}
/*-----------------------------------------------------------*/

static void prvHighPriorityEnterCriticalTask( void * pvParameters )
{
    uint32_t i;
    eTaskState taskState;
    BaseType_t xAllTestTaskReady = pdFALSE;

    /* Silence warnings about unused parameters. */
    ( void ) pvParameters;

    /* Check all the test task states before entering critical section. Low priority
     * task should be of running state. Ever running tasks should suspend themselves. */
    while( xAllTestTaskReady == pdFALSE )
    {
        xAllTestTaskReady = pdTRUE;

        /* Check the low priority task status. */
        taskState = eTaskGetState( xTaskHandles[ 0 ] );

        if( taskState != eRunning )
        {
            xAllTestTaskReady = pdFALSE;
        }

        /* Check the ever running priority task status. */
        for( i = 1; i < configNUMBER_OF_CORES; i++ )
        {
            taskState = eTaskGetState( xTaskHandles[ i ] );

            if( taskState != eSuspended )
            {
                xAllTestTaskReady = pdFALSE;
            }
        }
    }

    taskENTER_CRITICAL();
    {
        xHighPriorityTaskEnterCriticalSection = pdTRUE;

        /* Proper busy looping here to wait for low priority task. */
        for( i = 0; i < TEST_BUSY_LOOPING_COUNT; i++ )
        {
            TEST_NOP();
        }

        /* Resume tasks T1 ~ T(n - 1). All the cores are occupied by T1 ~ Tn due to
         * higher priority. The low priority task's waiting for the critical section
         * should be interrupted. */
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

    /* Create one test task with low priority to enter the critical section. */
    xTaskCreationResult = xTaskCreate( prvLowPriorityEnterCriticalTask,
                                       "EnterCSLow",
                                       configMINIMAL_STACK_SIZE,
                                       NULL,
                                       configMAX_PRIORITIES - 3,
                                       &xTaskHandles[ 0 ] );

    TEST_ASSERT_EQUAL_MESSAGE( pdPASS, xTaskCreationResult, "Task creation failed." );

    /* Create configNUMBER_OF_CORES - 1 with high priority to occupy the cores. */
    for( i = 1; i < configNUMBER_OF_CORES; i++ )
    {
        xTaskCreationResult = xTaskCreate( prvEverRunningTask,
                                           "EverRunning",
                                           configMINIMAL_STACK_SIZE,
                                           NULL,
                                           configMAX_PRIORITIES - 2,
                                           &xTaskHandles[ i ] );

        TEST_ASSERT_EQUAL_MESSAGE( pdPASS, xTaskCreationResult, "Task creation failed." );
    }

    /* Create one test task with high priority to enter the critical section. */
    xTaskCreationResult = xTaskCreate( prvHighPriorityEnterCriticalTask,
                                       "EnterCSHigh",
                                       configMINIMAL_STACK_SIZE,
                                       NULL,
                                       configMAX_PRIORITIES - 2,
                                       &xTaskHandles[ configNUMBER_OF_CORES ] );

    TEST_ASSERT_EQUAL_MESSAGE( pdPASS, xTaskCreationResult, "Task creation failed." );

    vTaskDelay( pdMS_TO_TICKS( TEST_TIMEOUT_MS ) );

    /* Verify the high priority task has entered the critical section. */
    TEST_ASSERT_EQUAL_MESSAGE( pdTRUE, xHighPriorityTaskEnterCriticalSection, "High priority task not enter the critical section." );

    /* Verify the low priority task relinquishes the core for higher priority tasks. */
    TEST_ASSERT_EQUAL_MESSAGE( pdFALSE, xLowPriorityTaskEnterCriticalSection, "Low priority task should relinquish the core." );

    /* Suspend the high priority task and block the test runner. The low priority task
     * should be able to enter the critical section now due to core available. */
    vTaskSuspend( xTaskHandles[ configNUMBER_OF_CORES ] );

    vTaskDelay( pdMS_TO_TICKS( TEST_TIMEOUT_MS ) );

    /* Verify the low priority task is able to enter the critical section. */
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
 * @brief A start entry for test runner to run interrupt task wait critical section test.
 */
void vRunInterruptWaitCriticalTest( void )
{
    UNITY_BEGIN();

    RUN_TEST( Test_InterruptWaitCritical );

    UNITY_END();
}
/*-----------------------------------------------------------*/
