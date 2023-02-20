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
 * @file tasks_delete.c
 * @brief When a n RTOS object is deleted, the associated resources shall be freed.
 *
 * Procedure:
 *   - TestRunner records original memory size.
 *   - Create ( num of cores ) tasks ( T0~Tn-1 ).
 *   - Task T0~Tn-1 delete itself.
 *   - TestRunner checks if memory freed.
 *   - Create ( num of cores ) tasks ( T0~Tn-1 ).
 *   - Task T0~Tn-1 are in delay loop.
 *   - TestRunner deletes T0~Tn-1 remotely.
 *   - TestRunner checks if memory freed.
 * Expected:
 *   - Have same remaining memory before creating task and after deleting task.
 */

/* Kernel includes. */
#include "FreeRTOS.h" /* Must come first. */
#include "task.h"     /* RTOS task related API prototypes. */

#include "unity.h"    /* unit testing support functions */
/*-----------------------------------------------------------*/

/**
 * @brief Timeout value to stop test.
 */
#define TEST_TIMEOUT_MS    ( 10000 )
/*-----------------------------------------------------------*/

#if ( configNUMBER_OF_CORES < 2 )
    #error This test is for FreeRTOS SMP and therefore, requires at least 2 cores.
#endif /* if configNUMBER_OF_CORES != 2 */
/*-----------------------------------------------------------*/

/**
 * @brief Test case "Task Delete".
 */
void Test_TaskDelete( void );

/**
 * @brief Partial test case in "Task Delete" for "Self deletion".
 */
BaseType_t Test_TaskSelfDelete( void );

/**
 * @brief Partial test case in "Task Delete" for "Remote deletion".
 */
BaseType_t Test_TaskRemoteDelete( void );

/**
 * @brief Task entry to delete itself.
 */
static void vPrvSelfDeleteTask( void * pvParameters );

/**
 * @brief Task entry to loop in delay.
 */
static void vPrvDelayTask( void * pvParameters );
/*-----------------------------------------------------------*/

/**
 * @brief Handles of the tasks created in this test.
 */
static TaskHandle_t xTaskHanldes[ configNUMBER_OF_CORES ];

/**
 * @brief The heap size before creating tasks T0~Tn-1.
 */
static uint32_t ulOriginalFreeHeapSize;
/*-----------------------------------------------------------*/

void Test_TaskDelete( void )
{
    BaseType_t xTestResult = pdPASS;

    xTestResult = Test_TaskSelfDelete();

    if( xTestResult )
    {
        Test_TaskRemoteDelete();
    }
}
/*-----------------------------------------------------------*/

BaseType_t Test_TaskSelfDelete( void )
{
    int i;
    BaseType_t xTaskCreationResult;
    TickType_t xStartTick = xTaskGetTickCount();
    BaseType_t xTestResult = pdPASS;

    /* Create configNUMBER_OF_CORES - 1 low priority tasks. */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        xTaskHanldes[ i ] = NULL;

        xTaskCreationResult = xTaskCreate( vPrvSelfDeleteTask,
                                           "SelfDel",
                                           configMINIMAL_STACK_SIZE,
                                           NULL,
                                           configMAX_PRIORITIES - 2,
                                           &( xTaskHanldes[ i ] ) );

        if( xTaskCreationResult != pdPASS )
        {
            xTestResult = pdFALSE;
            TEST_ASSERT_EQUAL_MESSAGE( pdPASS, xTaskCreationResult, "Task creation failed." );
            break;
        }
    }

    /* Wait tasks to delete itself. */
    while( ulOriginalFreeHeapSize > xPortGetFreeHeapSize() )
    {
        vTaskDelay( pdMS_TO_TICKS( 10 ) );

        if( ( xTaskGetTickCount() - xStartTick ) / portTICK_PERIOD_MS >= TEST_TIMEOUT_MS )
        {
            break;
        }
    }

    if( ulOriginalFreeHeapSize != xPortGetFreeHeapSize() )
    {
        TEST_ASSERT_EQUAL_INT( ulOriginalFreeHeapSize, xPortGetFreeHeapSize() );
        xTestResult = pdFALSE;
    }

    return xTestResult;
}
/*-----------------------------------------------------------*/

BaseType_t Test_TaskRemoteDelete( void )
{
    int i;
    BaseType_t xTaskCreationResult;
    TickType_t xStartTick = xTaskGetTickCount();
    BaseType_t xTestResult = pdPASS;

    /* Create configNUMBER_OF_CORES - 1 low priority tasks. */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        xTaskHanldes[ i ] = NULL;

        xTaskCreationResult = xTaskCreate( vPrvDelayTask,
                                           "KeepDelay",
                                           configMINIMAL_STACK_SIZE,
                                           NULL,
                                           configMAX_PRIORITIES - 2,
                                           &( xTaskHanldes[ i ] ) );

        if( xTaskCreationResult != pdPASS )
        {
            xTestResult = pdFALSE;
            TEST_ASSERT_EQUAL_MESSAGE( pdPASS, xTaskCreationResult, "Task creation failed." );
            break;
        }
    }

    /* Delay a while for tasks just created to run. */
    vTaskDelay( pdMS_TO_TICKS( 10 ) );

    /* Delete tasks remotely. */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        if( xTaskHanldes[ i ] )
        {
            vTaskDelete( xTaskHanldes[ i ] );
        }
    }

    /* Wait to recycle the memory. */
    while( ulOriginalFreeHeapSize > xPortGetFreeHeapSize() )
    {
        vTaskDelay( pdMS_TO_TICKS( 10 ) );

        if( ( xTaskGetTickCount() - xStartTick ) / portTICK_PERIOD_MS >= TEST_TIMEOUT_MS )
        {
            break;
        }
    }

    if( ulOriginalFreeHeapSize != xPortGetFreeHeapSize() )
    {
        TEST_ASSERT_EQUAL_INT( ulOriginalFreeHeapSize, xPortGetFreeHeapSize() );
        xTestResult = pdFALSE;
    }

    return xTestResult;
}
/*-----------------------------------------------------------*/

static void vPrvSelfDeleteTask( void * pvParameters )
{
    /* Silence warnings about unused parameters. */
    ( void ) pvParameters;

    vTaskDelete( NULL );

    /* Idle the task. It shouldn't be run. */
    for( ; ; )
    {
        vTaskDelay( pdMS_TO_TICKS( 10 ) );
    }
}

/*-----------------------------------------------------------*/

static void vPrvDelayTask( void * pvParameters )
{
    /* Silence warnings about unused parameters. */
    ( void ) pvParameters;

    /* Idle the task */
    for( ; ; )
    {
        vTaskDelay( pdMS_TO_TICKS( 10 ) );
    }
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
    /* Nothing to release in this test case. */
}
/*-----------------------------------------------------------*/

/**
 * @brief A start entry for test runner to run FR10.
 */
void vRunTaskDeleteTest( void )
{
    UNITY_BEGIN();

    RUN_TEST( Test_TaskDelete );

    UNITY_END();
}

/*-----------------------------------------------------------*/
