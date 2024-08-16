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
 * @file tasks_delete.c
 * @brief When a n RTOS object is deleted, the associated resources shall be freed.
 *
 * Procedure:
 *   - TestRunner records original memory size.
 *   - Create ( num of cores ) tasks T0 ~ T(n - 1).
 *   - Tasks T0 ~ T(n - 1) delete themselves.
 *   - TestRunner checks if memory is freed.
 *   - Create ( num of cores ) tasks T0 ~ T(n - 1).
 *   - Task T0 ~ T(n - 1) delay in loop.
 *   - TestRunner deletes T0 ~ T(n - 1).
 *   - TestRunner checks if memory freed.
 * Expected:
 *   - Have same remaining memory before creating task and after deleting task.
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

/*-----------------------------------------------------------*/

#if ( configNUMBER_OF_CORES < 2 )
    #error This test is for FreeRTOS SMP and therefore, requires at least 2 cores.
#endif /* if ( configNUMBER_OF_CORES < 2 ) */

#if ( configMAX_PRIORITIES <= 2 )
    #error configMAX_PRIORITIES must be larger than 2 to avoid scheduling idle tasks unexpectedly.
#endif /* if ( configMAX_PRIORITIES <= 2 ) */

/*-----------------------------------------------------------*/

/**
 * @brief Test case "Task Delete".
 */
void Test_TaskDelete( void );

/**
 * @brief Partial test case in "Task Delete" for "Self deletion".
 */
static void prvTestTaskSelfDelete( void );

/**
 * @brief Partial test case in "Task Delete" for "Remote deletion".
 */
static void prvTestTaskRemoteDelete( void );

/**
 * @brief Task entry to delete itself.
 */
static void prvSelfDeleteTask( void * pvParameters );

/**
 * @brief Task entry to loop in delay.
 */
static void prvDelayTask( void * pvParameters );
/*-----------------------------------------------------------*/

/**
 * @brief Handles of the tasks created in this test.
 */
static TaskHandle_t xTaskHandles[ configNUMBER_OF_CORES ];

/**
 * @brief Flag to indicate task run status.
 */
static BaseType_t xTaskRunStatus[ configNUMBER_OF_CORES ];

/**
 * @brief The heap size before creating tasks T0 ~ T(n - 1).
 */
static uint32_t ulOriginalFreeHeapSize;
/*-----------------------------------------------------------*/

static void prvSelfDeleteTask( void * pvParameters )
{
    BaseType_t * pxTaskRunStatus = ( BaseType_t * ) pvParameters;

    /* Set the flag to indicate the task has run. */
    *pxTaskRunStatus = pdTRUE;

    vTaskDelete( NULL );

    /* The task delete itself. This line should not be run. */
    *pxTaskRunStatus = pdFALSE;
}
/*-----------------------------------------------------------*/

static void prvDelayTask( void * pvParameters )
{
    BaseType_t * pxTaskRunStatus = ( BaseType_t * ) pvParameters;

    /* Set the flag to indicate the task has run. */
    *pxTaskRunStatus = pdTRUE;

    /* Block this task forever. */
    vTaskDelay( portMAX_DELAY );
}
/*-----------------------------------------------------------*/

static void prvTestTaskSelfDelete( void )
{
    uint32_t i;
    BaseType_t xTaskCreationResult;
    uint32_t ulFreeHeapSize;

    /* Create configNUMBER_OF_CORES low priority tasks. */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        xTaskRunStatus[ i ] = pdFALSE;
        xTaskCreationResult = xTaskCreate( prvSelfDeleteTask,
                                           "SelfDel",
                                           configMINIMAL_STACK_SIZE,
                                           ( void * ) ( &( xTaskRunStatus[ i ] ) ),
                                           configMAX_PRIORITIES - 2,
                                           &( xTaskHandles[ i ] ) );

        TEST_ASSERT_EQUAL_MESSAGE( pdPASS, xTaskCreationResult, "Task creation failed." );
    }

    /* Wait task to delete itself. */
    vTaskDelay( pdMS_TO_TICKS( TEST_TIMEOUT_MS ) );

    /* Verify the task run status. */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        TEST_ASSERT_EQUAL_MESSAGE( pdTRUE, xTaskRunStatus[ i ], "Task hasn't been run." );
        xTaskHandles[ i ] = NULL;
    }

    /* Verify the memory used for task TCB and stack is freed. */
    ulFreeHeapSize = xPortGetFreeHeapSize();
    TEST_ASSERT_EQUAL_INT_MESSAGE( ulOriginalFreeHeapSize, ulFreeHeapSize, "Self deleted task test failed." );
}
/*-----------------------------------------------------------*/

static void prvTestTaskRemoteDelete( void )
{
    uint32_t i;
    BaseType_t xTaskCreationResult;
    uint32_t ulFreeHeapSize;

    /* Create configNUMBER_OF_CORES low priority tasks. */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        xTaskRunStatus[ i ] = pdFALSE;
        xTaskCreationResult = xTaskCreate( prvDelayTask,
                                           "KeepDelay",
                                           configMINIMAL_STACK_SIZE,
                                           ( void * ) ( &( xTaskRunStatus[ i ] ) ),
                                           configMAX_PRIORITIES - 2,
                                           &( xTaskHandles[ i ] ) );

        TEST_ASSERT_EQUAL_MESSAGE( pdPASS, xTaskCreationResult, "Task creation failed." );
    }

    /* Delay a while for tasks just created to run. */
    vTaskDelay( pdMS_TO_TICKS( TEST_TIMEOUT_MS ) );

    /* Verify the task run status. */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        TEST_ASSERT_EQUAL_MESSAGE( pdTRUE, xTaskRunStatus[ i ], "Task hasn't been run." );
    }

    /* Delete tasks remotely. */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        vTaskDelete( xTaskHandles[ i ] );
        xTaskHandles[ i ] = NULL;
    }

    ulFreeHeapSize = xPortGetFreeHeapSize();
    TEST_ASSERT_EQUAL_INT_MESSAGE( ulOriginalFreeHeapSize, ulFreeHeapSize, "Remote deleted task test failed." );
}
/*-----------------------------------------------------------*/

void Test_TaskDelete( void )
{
    prvTestTaskSelfDelete();
    prvTestTaskRemoteDelete();
}
/*-----------------------------------------------------------*/

/* Runs before every test, put init calls here. */
void setUp( void )
{
    /* Get the heap size before creating tasks. */
    ulOriginalFreeHeapSize = xPortGetFreeHeapSize();
}
/*-----------------------------------------------------------*/

/* Runs after every test, put clean-up calls here. */
void tearDown( void )
{
    uint32_t i;

    for( i = 0; i < configNUMBER_OF_CORES; i++ )
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
 * @brief Entry point for test runner to task delete test.
 */
void vRunTaskDeleteTest( void )
{
    UNITY_BEGIN();

    RUN_TEST( Test_TaskDelete );

    UNITY_END();
}
/*-----------------------------------------------------------*/
