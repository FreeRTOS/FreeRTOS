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
 * @file suspend_scheduler.c
 * @brief Context switch shall not happen when the scheduler is suspended.
 *
 * Procedure:
 *   - configRUN_MULTIPLE_PRIORITIES & configUSE_CORE_AFFINITY should be set to 0.
 *   - Create ( num of cores ) tasks (T0~Tn-1).
 *   - Task T0 has higher priority then T1~Tn-1. Priority T0 > T1~Tn-1.
 *   - Task T0 calls vTaskSuspendAll.
 *   - Task T0 raises priority of task T1. Priority T1 > T0 > T2~Tn-1.
 *   - Task T0 calls xTaskResumeAll.
 *   - Task T1 Runs.
 * Expected:
 *   - T1 shouldn't run before T0 calls xTaskResumeAll.
 *   - T1 should run after T0 calls xTaskResumeAll immediately.
 */

/* Kernel includes. */
#include "FreeRTOS.h" /* Must come first. */
#include "task.h"     /* RTOS task related API prototypes. */

#include "unity.h"    /* unit testing support functions */
/*-----------------------------------------------------------*/

/**
 * @brief Time for T0 to poll T1. This value must be smaller than TEST_TIMEOUT_MS.
 */
#define TEST_T0_POLLING_TIME    ( 0xFFFFFFF0 )

/**
 * @brief Timeout value to stop test.
 */
#define TEST_TIMEOUT_MS         ( 10000 )
/*-----------------------------------------------------------*/

/**
 * @brief Test case "Suspend Scheduler".
 */
static void Test_SuspendScheduler( void );

/**
 * @brief Task function for T0.
 */
static void vPrvTaskSuspendScheduler( void * pvParameters );

/**
 * @brief Task function for other tasks.
 */
static void vPrvTaskSetFlag( void * pvParameters );
/*-----------------------------------------------------------*/

#if ( configNUMBER_OF_CORES < 2 )
    #error This test is for FreeRTOS SMP and therefore, requires at least 2 cores.
#endif /* if configNUMBER_OF_CORES != 2 */

#if configRUN_MULTIPLE_PRIORITIES != 0
    #error test_config.h must be included at the end of FreeRTOSConfig.h.
#endif /* if configRUN_MULTIPLE_PRIORITIES != 0 */

#if configUSE_CORE_AFFINITY != 0
    #error test_config.h must be included at the end of FreeRTOSConfig.h.
#endif /* if configUSE_CORE_AFFINITY != 0 */
/*-----------------------------------------------------------*/

/**
 * @brief Handles of the tasks created in this test.
 */
static TaskHandle_t xTaskHanldes[ configNUMBER_OF_CORES ];

/**
 * @brief A flag to indicate if T1~Tn-1 run.
 */
static BaseType_t xHasOtherTaskRun = pdFALSE;

/**
 * @brief A flag to indicate if T0 run.
 */
static BaseType_t xHasTaskT0Run = pdFALSE;
/*-----------------------------------------------------------*/

static void Test_SuspendScheduler( void )
{
    TickType_t xStartTick = xTaskGetTickCount();

    /* Yield for other cores to run tasks. */
    taskYIELD();

    /* Wait other tasks. */
    while( xHasOtherTaskRun == pdFALSE || xHasTaskT0Run == pdFALSE )
    {
        vTaskDelay( pdMS_TO_TICKS( 10 ) );

        if( ( xTaskGetTickCount() - xStartTick ) / portTICK_PERIOD_MS >= TEST_TIMEOUT_MS )
        {
            break;
        }
    }

    TEST_ASSERT_TRUE( xHasTaskT0Run == pdTRUE );
    TEST_ASSERT_TRUE( xHasOtherTaskRun == pdTRUE );
}
/*-----------------------------------------------------------*/

static void vPrvTaskSuspendScheduler( void * pvParameters )
{
    uint32_t i = 0;

    ( void ) pvParameters;

    vTaskSuspendAll();

    /* Raise T1's task priority to higher than T0. */
    vTaskPrioritySet( xTaskHanldes[ 1 ], tskIDLE_PRIORITY + 3 );

    for( i = 0; i < TEST_T0_POLLING_TIME; i++ )
    {
        if( xHasOtherTaskRun != pdFALSE )
        {
            break;
        }
    }

    TEST_ASSERT_TRUE( xHasOtherTaskRun == pdFALSE );

    ( void ) xTaskResumeAll();

    xHasTaskT0Run = pdTRUE;

    for( ; ; )
    {
        vTaskDelay( pdMS_TO_TICKS( 10 ) );
    }
}
/*-----------------------------------------------------------*/

static void vPrvTaskSetFlag( void * pvParameters )
{
    ( void ) pvParameters;

    xHasOtherTaskRun = pdTRUE;

    for( ; ; )
    {
        vTaskDelay( pdMS_TO_TICKS( 10 ) );
    }
}
/*-----------------------------------------------------------*/

/* Runs before every test, put init calls here. */
void setUp( void )
{
    int i;
    BaseType_t xTaskCreationResult;

    xTaskCreationResult = xTaskCreate( vPrvTaskSuspendScheduler,
                                       "SetFlag",
                                       configMINIMAL_STACK_SIZE,
                                       NULL,
                                       tskIDLE_PRIORITY + 2,
                                       &( xTaskHanldes[ 0 ] ) );

    TEST_ASSERT_EQUAL_MESSAGE( pdPASS, xTaskCreationResult, "Task creation failed." );

    /* Create configNUMBER_OF_CORES low priority tasks. */
    for( i = 1; i < configNUMBER_OF_CORES; i++ )
    {
        xTaskCreationResult = xTaskCreate( vPrvTaskSetFlag,
                                           "SetFlag",
                                           configMINIMAL_STACK_SIZE,
                                           NULL,
                                           tskIDLE_PRIORITY + 1,
                                           &( xTaskHanldes[ i ] ) );

        TEST_ASSERT_EQUAL_MESSAGE( pdPASS, xTaskCreationResult, "Task creation failed." );
    }
}
/*-----------------------------------------------------------*/

/* Runs after every test, put clean-up calls here. */
void tearDown( void )
{
    int i;

    /* Delete all the tasks. */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        if( xTaskHanldes[ i ] )
        {
            vTaskDelete( xTaskHanldes[ i ] );
        }
    }
}
/*-----------------------------------------------------------*/

void vRunSuspendSchedulerTest( void )
{
    UNITY_BEGIN();

    RUN_TEST( Test_SuspendScheduler );

    UNITY_END();
}
/*-----------------------------------------------------------*/
