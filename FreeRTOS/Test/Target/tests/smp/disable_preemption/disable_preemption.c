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
 * @file disable_preemption.c
 * @brief The scheduler shall not preempt a task for which preemption is disabled.
 *
 * Procedure:
 *   - Create ( num of cores ) tasks ( T0~Tn-1 ), each with equal priority.
 *   - Disable preemption for task T0. Task T0 will then decrease
 *     its own priority and busy loop with it still disabled.
 *   - Task T1~Tn-1 will iterate yielding 10ms delay.
 *   - The traceTASK_SWITCHED_IN function is bound in order to track
 *     scheduler activity.
 * Expected:
 *   - That Task T0 will not be interrupted for the 3 seconds that it
 *     has preemption disabled.
 */

/* Kernel includes. */
#include "FreeRTOS.h" /* Must come first. */
#include "task.h"     /* RTOS task related API prototypes. */

#include "unity.h" /* unit testing support functions */
/*-----------------------------------------------------------*/

/**
 * @brief Timeout value to stop test.
 */
#define TEST_TIMEOUT_MS    ( 10000 )

/**
 * @brief Loop value for T0 with preemption disabled.
 */
#define TEST_T0_BUSY_TIME    ( 0xFFFF )
/*-----------------------------------------------------------*/

#if ( configNUMBER_OF_CORES < 2 )
    #error This test is for FreeRTOS SMP and therefore, requires at least 2 cores.
#endif /* if configNUMBER_OF_CORES != 2 */

#if ( configUSE_TASK_PREEMPTION_DISABLE != 1 )
    #error Need to include testConfig.h in FreeRTOSConfig.h
#endif /* if configUSE_TASK_PREEMPTION_DISABLE != 1 */
/*-----------------------------------------------------------*/

/**
 * @brief Test case "Disable DisablePreemption".
 */
void Test_DisablePreemption(void);

/**
 * @brief Function that implements a never blocking FreeRTOS task.
 */
static void prvDelayTask( void * pvParameters );

/**
 * @brief Task for T0 to busy loop with preemption disabled.
 */
static void prvDisablePreemptionTask( void * pvParameters );
/*-----------------------------------------------------------*/

/**
 * @brief Handles of the tasks created in this test.
 */
static TaskHandle_t xTaskHanldes[ configNUMBER_OF_CORES ];

/**
 * @brief Flas to indicate if task T0 run or not.
 */
static BaseType_t xIsTaskT0PreemptDisabled = { pdFALSE };

/**
 * @brief Flas to indicate if task T0 run or not.
 */
static BaseType_t xIsTaskT0Finished = { pdFALSE };
/*-----------------------------------------------------------*/

static int lFindTaskIdx( TaskHandle_t xCurrntTaskHandle )
{
    int i = 0;
    int lMatchIdx = -1;

    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        if( xCurrntTaskHandle == xTaskHanldes[ i ] )
        {
            lMatchIdx = i;
            break;
        }
    }

    return lMatchIdx;
}

void test_TASK_SWITCHED_IN(void) {
    UBaseType_t uxIdx, uxNumTasksRunning;
    TaskStatus_t taskStatus[16];
    UBaseType_t uxTaskStatusArraySize = 16;
    unsigned long ulTotalRunTime;

    uxNumTasksRunning = uxTaskGetSystemState((TaskStatus_t *const)&taskStatus,
                             uxTaskStatusArraySize, &ulTotalRunTime);

    for (uxIdx = 0; uxIdx < uxNumTasksRunning; uxIdx++) {
        // if( taskStatus[uxIdx].eCurrentState == eRunning && lFindTaskIdx(taskStatus[uxIdx].xHandle) != -1 )
        // {
        //     printf("Running Task %s:%d\n", taskStatus[uxIdx].pcTaskName, lFindTaskIdx(taskStatus[uxIdx].xHandle) );
        // }

        if ( taskStatus[uxIdx].xHandle == xTaskHanldes[0] ) 
        {
            if( xIsTaskT0PreemptDisabled == pdTRUE && taskStatus[uxIdx].eCurrentState != eRunning )
            {
                /* Once T0 disables preemption, it shouldn't be switched out. */
                TEST_ASSERT_TRUE( taskStatus[uxIdx].eCurrentState == eRunning );
            }
        }
    }

    // printf("\n" );
}
/*-----------------------------------------------------------*/

static void prvDelayTask( void * pvParameters )
{
    /* Silence warnings about unused parameters. */
    ( void ) pvParameters;

    for( ; ; )
    {
        vTaskDelay( pdMS_TO_TICKS( 10 ) );
    }
}
/*-----------------------------------------------------------*/

static void prvDisablePreemptionTask( void * pvParameters )
{
    uint32_t i=0;

    /* wait with preemption disabled */
    vTaskPreemptionDisable(NULL);
    xIsTaskT0PreemptDisabled = pdTRUE;

    vTaskPrioritySet(NULL, configMAX_PRIORITIES - 3);
    
    for( i=0 ; i<TEST_T0_BUSY_TIME ; i++ )
    {
        // printf("i=%d\n", i);
        
        /* Always running, put asm here to avoid optimization by compiler. */
        __asm volatile ( "nop" );
    }
    xIsTaskT0PreemptDisabled = pdFALSE;
    vTaskPreemptionEnable(NULL);

    xIsTaskT0Finished = pdTRUE;
    printf("xIsTaskT0Finished\n");

    for( ; ; )
    {
        vTaskDelay( pdMS_TO_TICKS( 10 ) );
    }
}
/*-----------------------------------------------------------*/

void Test_DisablePreemption(void) {
    TickType_t xStartTick = xTaskGetTickCount();
    int i = 0;

    /* Wait other tasks. */
    while( xIsTaskT0Finished == pdFALSE )
    {
        printf("xStartTick = %d, current tick = %d, difftime=%d\n", xStartTick, xTaskGetTickCount(), ( xTaskGetTickCount() - xStartTick ) / portTICK_PERIOD_MS);
        vTaskDelay( pdMS_TO_TICKS( 100 ) );

        if( ( xTaskGetTickCount() - xStartTick ) / portTICK_PERIOD_MS >= TEST_TIMEOUT_MS )
        {
            break;
        }
    }

    TEST_ASSERT_TRUE( xIsTaskT0Finished == pdTRUE );
}
/*-----------------------------------------------------------*/

/* Runs before every test, put init calls here. */
void setUp( void )
{
    int i;
    BaseType_t xTaskCreationResult;

    xTaskCreationResult = xTaskCreate( prvDisablePreemptionTask,
                                        "DisablePreemption",
                                        configMINIMAL_STACK_SIZE * 2,
                                        NULL,
                                        configMAX_PRIORITIES - 2,
                                        &( xTaskHanldes[ 0 ] ) );

    TEST_ASSERT_EQUAL_MESSAGE( pdPASS, xTaskCreationResult, "Task creation failed." );

    /* Create configNUMBER_OF_CORES - 1 low priority tasks. */
    for( i = 1; i < configNUMBER_OF_CORES; i++ )
    {
        xTaskCreationResult = xTaskCreate( prvDelayTask,
                                           "KeepDelaying",
                                           configMINIMAL_STACK_SIZE,
                                           NULL,
                                           configMAX_PRIORITIES - 2,
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

/**
 * @brief A start entry for test runner to run FR06.
 */
void vRunDisablePreemptionTest(void) {
  UNITY_BEGIN();

  RUN_TEST(Test_DisablePreemption);

  UNITY_END();
}
/*-----------------------------------------------------------*/
