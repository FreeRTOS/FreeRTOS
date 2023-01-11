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

#include "unity.h" /* unit testing support functions */

/*-----------------------------------------------------------*/

#if configNUMBER_OF_CORES < 2
    #error Require two cores be configured for FreeRTOS
#endif /* if configNUMBER_OF_CORES != 2 */

#if configRUN_MULTIPLE_PRIORITIES != 1
    #error test_config.h must be included at the end of FreeRTOSConfig.h.
#endif
/*-----------------------------------------------------------*/

/**
 * @brief Function that implements a never blocking FreeRTOS task.
 */
static void prvEverRunningTask( void * pvParameters );

/**
 * @brief Task entry function to start Unity.
 */
static void prvRunMultipleTasksRunningTest( void *pvParameters );

/*-----------------------------------------------------------*/

/**
 * @brief Handles of the tasks created in this test.
 */
TaskHandle_t xTaskHanldes[ configNUMBER_OF_CORES - 1 ];

/*-----------------------------------------------------------*/

static void prvEverRunningTask( void * pvParameters )
{
    /* Silence warnings about unused parameters. */
    ( void ) pvParameters;

    for( ;; )
    {
        /* Always running, put asm here to avoid optimization by compiler. */
        asm("");
    }
}
/*-----------------------------------------------------------*/

/* Runs before every test, put init calls here. */
void setUp( void )
{
    int i;
    BaseType_t xTaskCreationResult;

    /* Create configNUMBER_OF_CORES - 1 low priority tasks. */
    for( i = 0; i < configNUMBER_OF_CORES - 1; i++ )
    {
        xTaskCreationResult =  xTaskCreate( prvEverRunningTask,
                                            "EverRunning",
                                            configMINIMAL_STACK_SIZE,
                                            NULL,
                                            configMAX_PRIORITIES - 2,
                                            &( xTaskHanldes[ i ] ) );

        TEST_ASSERT_EQUAL_MESSAGE( pdPASS, xTaskCreationResult, "Task creation failed." );
    }
}
/*-----------------------------------------------------------*/

/* Run after every test, put clean-up calls here. */
void tearDown( void )
{
    int i;

    /* Delete all the tasks. */
    for( i = 0; i < configNUMBER_OF_CORES - 1; i++ )
    {
        vTaskDelete( xTaskHanldes[ i ] );
    }
}
/*-----------------------------------------------------------*/

/* Function that implements the test case. This function must be called
 * from a FreeRTOS task. */
void Test_Multiple_Tasks_Running( void )
{
    int i;
    UBaseType_t uxOrigTaskPriority;
    eTaskState xTaskState;

    /* Ensure that this is the highest priority task. */
    uxOrigTaskPriority = uxTaskPriorityGet( NULL );
    vTaskPrioritySet( NULL, configMAX_PRIORITIES - 1 );

    /* Invoke the scheduler explicitly. */
    taskYIELD();

    /* Ensure that all the tasks are running. */
    for( i = 0; i < configNUMBER_OF_CORES - 1; i++ )
    {
        xTaskState = eTaskGetState( xTaskHanldes[ i ] );

        TEST_ASSERT_EQUAL_MESSAGE( eRunning, xTaskState, "Task is not running." );
    }

    vTaskPrioritySet( NULL, uxOrigTaskPriority );
}
/*-----------------------------------------------------------*/

static void prvRunMultipleTasksRunningTest( void *pvParameters )
{
    (void) pvParameters;

    UNITY_BEGIN();

    RUN_TEST( Test_Multiple_Tasks_Running );

    UNITY_END();

    for( ; ; )
    {
        vTaskDelay( pdMS_TO_TICKS( 1000 ) );
    }
}
/*-----------------------------------------------------------*/

void runMultipleTasksRunningTest( void )
{
    xTaskCreate( prvRunMultipleTasksRunningTest,
                "testRunner",
                configMINIMAL_STACK_SIZE * 2,
                NULL,
                tskIDLE_PRIORITY + 1,
                NULL );
    
    vTaskStartScheduler();
}
/*-----------------------------------------------------------*/
