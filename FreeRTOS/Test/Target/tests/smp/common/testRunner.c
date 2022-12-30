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
 * @file testRunner.c
 * @brief The implementation of main function to start test runner task.
 *
 * Procedure:
 *   - Initialize environment
 *   - Create test runner task
 *   - Start scheduler
 * Expected:
 *   - Run test case normally
 */

/* Kernel includes. */

#include "FreeRTOS.h" /* Must come first. */
#include "task.h"     /* RTOS task related API prototypes. */

#include "bsl.h"
#include "unity.h" /* unit testing support functions */

/*-----------------------------------------------------------*/

#define TASK_TESTRUNNER_PRIORITY    ( tskIDLE_PRIORITY + 2 )

/*-----------------------------------------------------------*/

static void prvTestRunnerTask( void * pvParameters );

/*-----------------------------------------------------------*/

extern void vTestRunner( void );

/*-----------------------------------------------------------*/

/**
 * @brief A start entry for unity to start with.
 *
 * @param[in] pvParameters parameter for task entry, useless in this test.
 */
static void prvTestRunnerTask( void * pvParameters )
{
    ( void ) pvParameters;

    /* Execute test case provided in test.c */
    vTestRunner();

    for( ; ; )
    {
        vTaskDelay( pdMS_TO_TICKS( 1000 ) );
    }
}

/*-----------------------------------------------------------*/

/* Is run before every test, put unit init calls here. */
void setUp( void )
{
}

/*-----------------------------------------------------------*/

/* Is run after every test, put unit clean-up calls here. */
void tearDown( void )
{
}

/*-----------------------------------------------------------*/

int main( void )
{
    vPortInitTestEnvironment();

    xTaskCreate( prvTestRunnerTask, "testRunner", configMINIMAL_STACK_SIZE * 2, NULL,
                 TASK_TESTRUNNER_PRIORITY, NULL );

    vTaskStartScheduler();

    /* should never reach here */
    panic_unsupported();

    return 0;
}

/*-----------------------------------------------------------*/
