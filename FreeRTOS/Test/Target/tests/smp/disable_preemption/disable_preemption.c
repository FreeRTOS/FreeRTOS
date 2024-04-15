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
 * @file disable_preemption.c
 * @brief The scheduler shall not preempt a task for which preemption is disabled.
 *
 * Procedure:
 *   - Create ( num of cores + 1 ) tasks ( T0~Tn ) with priorities T0 > T1 > ... Tn.
 *     T0 has the highest priority and Tn has the lowest priority.
 *   - T0~Tn-1 suspend themselves.
 *   - Tn disables preemption for itself and then resumes ( T0~Tn-1 ). Test
 *     runner validates that Tn is still running.
 *   - Test runner enables preemption of Tn. Test runner validates that Tn is
 *     no longer running.
 * Expected:
 *   - Tn will not be switched out when it has disabled preemption for itself.
 *   - Tn will be preempted when the test runner enables preemption for it.
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
 * @brief Timeout value to stop test.
 */
#define TEST_TIMEOUT_MS    ( 1000 )

/**
 * @brief Nop operation for busy looping.
 */
#ifndef portNOP
    #define TEST_NOP()    __asm volatile ( "nop" )
#else
    #define TEST_NOP    portNOP
#endif
/*-----------------------------------------------------------*/

#if ( configNUMBER_OF_CORES < 2 )
    #error This test is for FreeRTOS SMP and therefore, requires at least 2 cores.
#endif /* if configNUMBER_OF_CORES != 2 */

#if ( configUSE_TASK_PREEMPTION_DISABLE != 1 )
    #error configUSE_TASK_PREEMPTION_DISABLE must be enabled by including test_config.h in FreeRTOSConfig.h.
#endif /* if configUSE_TASK_PREEMPTION_DISABLE != 1 */

#if ( configMAX_PRIORITIES <= ( configNUMBER_OF_CORES + 2 ) )
    #error configMAX_PRIORITIES must be larger than ( configNUMBER_OF_CORES + 2 ) to avoid scheduling idle tasks unexpectedly.
#endif /* if ( configMAX_PRIORITIES <= ( configNUMBER_OF_CORES + 2 ) ) */
/*-----------------------------------------------------------*/

/**
 * @brief Test case "Disable Preemption".
 */
void Test_DisablePreemption( void );

/**
 * @brief Disable preemption test task.
 */
static void prvTestPreemptionDisableTask( void * pvParameters );
/*-----------------------------------------------------------*/

/**
 * @brief Handles of the tasks created in this test.
 */
static TaskHandle_t xTaskHandles[ configNUMBER_OF_CORES + 1 ];

/**
 * @brief Indexes of the tasks created in this test.
 */
static uint32_t xTaskIndexes[ configNUMBER_OF_CORES + 1 ];

/**
 * @brief Flags to indicate the test result.
 */
static BaseType_t xTestResult = pdFAIL;
/*-----------------------------------------------------------*/

static void prvTestPreemptionDisableTask( void * pvParameters )
{
    uint32_t currentTaskIdx = *( ( uint32_t * ) pvParameters );
    uint32_t taskIndex;
    eTaskState taskState;
    BaseType_t xAllHighPriorityTasksSuspended = pdFALSE;

    if( currentTaskIdx < configNUMBER_OF_CORES )
    {
        /* Tasks with smaller index have higher priority. Higher priority tasks
         * suspend themselves and are resumed later by the lowest priority task
         * after the lower priority task disables preemption for itself. */
        vTaskSuspend( NULL );
    }
    else
    {
        /* Wait for all the other higher priority tasks to suspend themselves. */
        while( xAllHighPriorityTasksSuspended == pdFALSE )
        {
            for( taskIndex = 0; taskIndex < configNUMBER_OF_CORES; taskIndex++ )
            {
                taskState = eTaskGetState( xTaskHandles[ taskIndex ] );

                if( taskState != eSuspended )
                {
                    break;
                }
            }

            if( taskIndex == configNUMBER_OF_CORES )
            {
                xAllHighPriorityTasksSuspended = pdTRUE;
            }
        }

        /* Disable preemption and resume all the other higher priority tasks.
         * At this point, the number of higher priority ready tasks is equal
         * to the number of cores. Still this lower priority must not be
         * switched out because it has disabled preemption for itself. */
        vTaskPreemptionDisable( NULL );

        for( taskIndex = 0; taskIndex < configNUMBER_OF_CORES; taskIndex++ )
        {
            vTaskResume( xTaskHandles[ taskIndex ] );
        }

        /* This task must not be switched out for any other higher priority
         * ready task because it has disabled preemption for itself. The
         * execution of the next line ensures that this task is not switched out
         * even though a higher priority ready task is available. This variable
         * is checked in the test runner. */
        xTestResult = pdPASS;
    }

    /* Busy looping here to occupy this core. */
    for( ; ; )
    {
        /* Always running, put nop operation here to avoid optimization by compiler. */
        TEST_NOP();
    }
}
/*-----------------------------------------------------------*/

void Test_DisablePreemption( void )
{
    eTaskState taskState;

    uint32_t i;
    BaseType_t xTaskCreationResult;

    /* Create ( configNUMBER_OF_CORES + 1 ) tasks with desending priorities. */
    for( i = 0; i < ( configNUMBER_OF_CORES + 1 ); i++ )
    {
        xTaskCreationResult = xTaskCreate( prvTestPreemptionDisableTask,
                                           "TestPreemptionDisable",
                                           configMINIMAL_STACK_SIZE * 2,
                                           &( xTaskIndexes[ i ] ),
                                           configMAX_PRIORITIES - 2 - i,
                                           &( xTaskHandles[ i ] ) );

        TEST_ASSERT_EQUAL_MESSAGE( pdPASS, xTaskCreationResult, "Task creation failed." );
    }

    /* TEST_TIMEOUT_MS is long enough to run this test. */
    vTaskDelay( pdMS_TO_TICKS( TEST_TIMEOUT_MS ) );

    /* Verify the lowest priority task runs after resuming all test tasks. */
    TEST_ASSERT_EQUAL( pdPASS, xTestResult );

    /* Enable preemption of the lowest priority task. The scheduler must switch
     * out this task now as there is a higher priority ready task available. */
    vTaskPreemptionEnable( xTaskHandles[ configNUMBER_OF_CORES ] );

    /* Verify that the lowest priority task is not running anymore. */
    taskState = eTaskGetState( xTaskHandles[ configNUMBER_OF_CORES ] );
    TEST_ASSERT_EQUAL( eReady, taskState );
}
/*-----------------------------------------------------------*/

/* Runs before every test, put init calls here. */
void setUp( void )
{
    uint32_t i;

    for( i = 0; i < ( configNUMBER_OF_CORES + 1 ); i++ )
    {
        xTaskIndexes[ i ] = i;
        xTaskHandles[ i ] = NULL;
    }
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
 * @brief Entry point for test runner to run disable preemption test.
 */
void vRunDisablePreemptionTest( void )
{
    UNITY_BEGIN();

    RUN_TEST( Test_DisablePreemption );

    UNITY_END();
}
/*-----------------------------------------------------------*/
