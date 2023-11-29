/*
 * FreeRTOS V202212.00
 * Copyright (C) 2022 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 *   - When a task runs, all tasks have higher priority are running.
 */

/* Standard includes. */
#include <stdint.h>

/* Kernel includes. */
#include "FreeRTOS.h" /* Must come first. */
#include "task.h"     /* RTOS task related API prototypes. */

#include "unity.h"    /* unit testing support functions */
/*-----------------------------------------------------------*/

/**
 * @brief Timeout value to stop test.
 */
#define TEST_TIMEOUT_MS    ( 10000 )

/**
 * @brief Nop operation for busy looping
 */
#ifdef portNOP
    #define TEST_NOP       portNOP
#else
    #define TEST_NOP()      __asm volatile ( "nop" )
#endif

/*-----------------------------------------------------------*/

#if ( configNUMBER_OF_CORES < 2 )
    #error This test is for FreeRTOS SMP and therefore, requires at least 2 cores.
#endif /* if configNUMBER_OF_CORES != 2 */

#if ( configMAX_PRIORITIES <= configNUMBER_OF_CORES )
    #error This test creates tasks with different priority, requires configMAX_PRIORITIES to be larger than configNUMBER_OF_CORES.
#endif /* if configNUMBER_OF_CORES != 2 */
/*-----------------------------------------------------------*/

/**
 * @brief Test case "scheduler highest priority task".
 */
void Test_ScheduleHighestPirority( void );

/**
 * @brief Function that implements a never blocking FreeRTOS task.
 */
static void prvEverRunningTask( void * pvParameters );
/*-----------------------------------------------------------*/

/**
 * @brief Handle of the testRunner task.
 */
static TaskHandle_t xTestRunnerTaskHandle;

/**
 * @brief Handles of the tasks created in this test.
 */
static TaskHandle_t xTaskHanldes[ configNUMBER_OF_CORES ];

/**
 * @brief Indexes of the tasks created in this test.
 */
static uint32_t xTaskIndexes[ configNUMBER_OF_CORES ];
/*-----------------------------------------------------------*/

static void prvEverRunningTask( void * pvParameters )
{
    uint32_t i = 0;
    uint32_t uxCurrentTaskIdx = *( ( uint32_t * ) pvParameters );
    eTaskState xTaskState;

    for( i = 0; i < uxCurrentTaskIdx; i++ )
    {
        xTaskState = eTaskGetState( xTaskHanldes[ i ] );

        /* Tasks created in this test are of descending priority order. For example,
         * priority of T0 is higher than priority of T1. A lower priority task is able
         * to run only when the higher priority tasks are running. Verify that higher
         * priority tasks are of running state. */
        if( eRunning != xTaskState )
        {
            /* Notify with eSetValueWithoutOverwrite. The return value can be pdTRUE
             * or pdFALSE. Either case, the test runner is notified with error by
             * this task or other task. */
            ( void ) xTaskNotify( xTestRunnerTaskHandle, uxCurrentTaskIdx, eSetValueWithoutOverwrite );
        }
    }

    /* If the task is the last task, then we finish the check because all tasks are checked. */
    if( uxCurrentTaskIdx == ( configNUMBER_OF_CORES - 1 ) )
    {
        /* Notify with eSetValueWithoutOverwrite. The return value can be pdTRUE or
         * pdFALSE. Either case, the test runner is notified by this task or other
         * task. */
        ( void ) xTaskNotify( xTestRunnerTaskHandle, configNUMBER_OF_CORES, eSetValueWithoutOverwrite );
    }

    for( ; ; )
    {
        /* Busy looping in this task. */
        TEST_NOP();
    }
}
/*-----------------------------------------------------------*/

void Test_ScheduleHighestPirority( void )
{
    uint32_t ulNotifiedValue;
    BaseType_t xReturn;

    xReturn = xTaskNotifyWait( 0x00, ULONG_MAX, &ulNotifiedValue, pdMS_TO_TICKS( TEST_TIMEOUT_MS ) );

    /* Test runner thread is notified within TEST_TIMEOUT_MS. */
    TEST_ASSERT_EQUAL( pdTRUE, xReturn );

    /* The notified value indicates that no error occurred during the test. */
    TEST_ASSERT_EQUAL_INT( configNUMBER_OF_CORES, ulNotifiedValue );
}
/*-----------------------------------------------------------*/

/* Runs before every test, put init calls here. */
void setUp( void )
{
    uint32_t i;
    BaseType_t xTaskCreationResult;

    /* Save the test runner task handle here. Test runner will be notified when test
     * finish or timeout. */
    xTestRunnerTaskHandle = xTaskGetCurrentTaskHandle();

    /* Create configNUMBER_OF_CORES tasks with decending priority. */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        xTaskIndexes[ i ] = i;
        xTaskCreationResult = xTaskCreate( prvEverRunningTask,
                                           "EverRun",
                                           configMINIMAL_STACK_SIZE * 2,
                                           &xTaskIndexes[ i ],
                                           configMAX_PRIORITIES - 1 - i,
                                           &xTaskHanldes[ i ] );

        TEST_ASSERT_EQUAL_MESSAGE( pdPASS, xTaskCreationResult, "Task creation failed." );
    }
}
/*-----------------------------------------------------------*/

/* Runs after every test, put clean-up calls here. */
void tearDown( void )
{
    uint32_t i;

    /* Delete all the tasks. */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        if( xTaskHanldes[ i ] != NULL )
        {
            vTaskDelete( xTaskHanldes[ i ] );
        }
    }
}
/*-----------------------------------------------------------*/

/**
 * @brief A start entry for test runner to run highest priority test.
 */
void vRunScheduleHighestPriorityTest( void )
{
    UNITY_BEGIN();

    RUN_TEST( Test_ScheduleHighestPirority );

    UNITY_END();
}
/*-----------------------------------------------------------*/
