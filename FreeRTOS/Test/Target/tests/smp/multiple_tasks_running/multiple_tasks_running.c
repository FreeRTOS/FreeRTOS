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
 * @file multiple_tasks_running.c
 * @brief The user shall be able to schedule tasks across multiple identical processor cores
 *        with one instance of FreeRTOS scheduler.
 *
 * Procedure:
 *   - Create ( num of cores - 1 ) tasks and keep them in busy loop.
 * Expected:
 *   - All tasks are in running state.
 */

/* Kernel includes. */
#include "FreeRTOS.h" /* Must come first. */
#include "task.h"     /* RTOS task related API prototypes. */

#include <string.h>

#include "unity.h" /* unit testing support functions */

/*-----------------------------------------------------------*/

#if ( configNUMBER_OF_CORES < 2 )
    #error This test is for FreeRTOS SMP and therefore, requires at least 2 cores.
#endif /* if configNUMBER_OF_CORES != 2 */

#if configRUN_MULTIPLE_PRIORITIES != 1
    #error test_config.h must be included at the end of FreeRTOSConfig.h.
#endif
/*-----------------------------------------------------------*/

/**
 * @brief Function that implements a never blocking FreeRTOS task.
 */
static void prvEverRunningTask( void * pvParameters );

/*-----------------------------------------------------------*/

/**
 * @brief Handles of the tasks created in this test.
 */
TaskHandle_t xTaskHanldes[ configNUMBER_OF_CORES - 1 ];

/**
 * @brief Original priority of main task.
 */
UBaseType_t uxOrigTaskPriority;

/*-----------------------------------------------------------*/

static void prvEverRunningTask( void * pvParameters )
{
    /* Silence warnings about unused parameters. */
    ( void ) pvParameters;

    for( ; ; )
    {
        /* Always running, put asm here to avoid optimization by compiler. */
        asm ( "" );
    }
}
/*-----------------------------------------------------------*/

static void vCreateEverRunTasks( void )
{
    int i;
    BaseType_t xTaskCreationResult;

    /* Create configNUMBER_OF_CORES - 1 low priority tasks. */
    for( i = 0; i < configNUMBER_OF_CORES - 1; i++ )
    {
        xTaskCreationResult = xTaskCreate( prvEverRunningTask,
                                           "EverRunning",
                                           configMINIMAL_STACK_SIZE,
                                           NULL,
                                           configMAX_PRIORITIES - 2,
                                           &( xTaskHanldes[ i ] ) );

        TEST_ASSERT_EQUAL_MESSAGE( pdPASS, xTaskCreationResult, "Task creation failed." );
    }
}
/*-----------------------------------------------------------*/

static void vResetResources( void )
{
    int i;

    vTaskPrioritySet( NULL, uxOrigTaskPriority );

    /* Delete all the tasks. */
    for( i = 0; i < configNUMBER_OF_CORES - 1; i++ )
    {
        if( xTaskHanldes[ i ] )
        {
            vTaskDelete( xTaskHanldes[ i ] );
        }
    }
}
/*-----------------------------------------------------------*/

/* Function that implements the test case. This function must be called
 * from a FreeRTOS task. */
void Test_MultipleTasksRunning( void )
{
    int i;
    eTaskState xTaskState;

    if( TEST_PROTECT() )
    {
        uxOrigTaskPriority = uxTaskPriorityGet( NULL );

        /* Ensure that this is the highest priority task. */
        vTaskPrioritySet( NULL, configMAX_PRIORITIES - 1 );

        vCreateEverRunTasks();

        /* Invoke the scheduler explicitly. */
        taskYIELD();

        /* Ensure that all the tasks are running. */
        for( i = 0; i < configNUMBER_OF_CORES - 1; i++ )
        {
            xTaskState = eTaskGetState( xTaskHanldes[ i ] );

            TEST_ASSERT_EQUAL_MESSAGE( eRunning, xTaskState, "Task is not running." );
        }

        vResetResources();
    }
    else
    {
        /* When TEST_ASSERT_* is triggered during test, program will jump here. */
        vResetResources();
    }
}
/*-----------------------------------------------------------*/
