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
 * @file schedule_equal_priority.c
 * @brief The scheduler shall schedule tasks of equal priority in a round robin fashion.
 *
 * Procedure:
 *   - Create ( num of cores + 1 ) tasks ( T0~Tn ). Priority T0 = T1 = ... = Tn-1 = Tn.
 *   - All tasks are running in busy loop.
 * Expected:
 *   - Equal priority tasks are scheduled in a round robin fashion when configUSE_TIME_SLICING
 *     is set to 1. Verify that all the test tasks get chance to run.
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
#define TEST_TIMEOUT_TICKS    ( ( configNUMBER_OF_CORES + 1U ) * 2U )

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

#if ( configUSE_TIME_SLICING != 1 )
    #error configUSE_TIME_SLICING must be enabled by including test_config.h in FreeRTOSConfig.h.
#endif /* if configUSE_TIME_SLICING != 1 */

#if ( configMAX_PRIORITIES <= 2 )
    #error configMAX_PRIORITIES must be larger than 2 to avoid scheduling idle tasks unexpectedly.
#endif /* if ( configMAX_PRIORITIES <= 2 ) */
/*-----------------------------------------------------------*/

/**
 * @brief Test case "schedule equal priority tasks.".
 */
void Test_ScheduleEqualPriority( void );

/**
 * @brief Function that implements a never blocking FreeRTOS task.
 */
static void prvEverRunningTask( void * pvParameters );
/*-----------------------------------------------------------*/

/**
 * @brief Handles of the tasks created in this test.
 */
static TaskHandle_t xTaskHandles[ configNUMBER_OF_CORES + 1 ];

/**
 * @brief Flags to indicate that all ever running tasks get a chance to run.
 */
static BaseType_t xTaskRun[ configNUMBER_OF_CORES + 1 ];
/*-----------------------------------------------------------*/

static void prvEverRunningTask( void * pvParameters )
{
    BaseType_t * pxTaskRun = ( ( BaseType_t * ) pvParameters );

    /* Set the flag for testRunner to check whether all tasks have run. */
    if( pxTaskRun != NULL )
    {
        *pxTaskRun = pdTRUE;
    }

    for( ; ; )
    {
        /* Always running, put asm here to avoid optimization by compiler. */
        TEST_NOP();
    }
}
/*-----------------------------------------------------------*/

void Test_ScheduleEqualPriority( void )
{
    uint32_t i;
    BaseType_t xTaskCreationResult;

    /* Create ( configNUMBER_OF_CORES + 1 ) low priority tasks. */
    for( i = 0; i < ( configNUMBER_OF_CORES + 1 ); i++ )
    {
        xTaskCreationResult = xTaskCreate( prvEverRunningTask,
                                           "EverRun",
                                           configMINIMAL_STACK_SIZE,
                                           &( xTaskRun[ i ] ),
                                           configMAX_PRIORITIES - 2,
                                           &( xTaskHandles[ i ] ) );

        TEST_ASSERT_EQUAL_MESSAGE( pdPASS, xTaskCreationResult, "Task creation failed." );
    }

    /* TEST_TIMEOUT_TICKS is long enough to run each task. */
    vTaskDelay( TEST_TIMEOUT_TICKS );

    for( i = 0; i < ( configNUMBER_OF_CORES + 1 ); i++ )
    {
        /* After timeout, all tasks must have been scheduled at least once and
         * have set their corresponding flag to pdTRUE. */
        TEST_ASSERT_EQUAL( pdTRUE, xTaskRun[ i ] );
    }
}
/*-----------------------------------------------------------*/

/* Runs before every test, put init calls here. */
void setUp( void )
{
    uint32_t i;

    for( i = 0; i < ( configNUMBER_OF_CORES + 1 ); i++ )
    {
        xTaskRun[ i ] = pdFALSE;
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
 * @brief Entry point for test runner to run schedule equal priority test.
 */
void vRunScheduleEqualPriorityTest( void )
{
    UNITY_BEGIN();

    RUN_TEST( Test_ScheduleEqualPriority );

    UNITY_END();
}
/*-----------------------------------------------------------*/
