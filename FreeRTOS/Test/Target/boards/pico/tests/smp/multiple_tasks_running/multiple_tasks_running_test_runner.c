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
 * @file multiple_tasks_running_test_runner.c
 * @brief The implementation of test runner task which runs the test.
 */

/* Kernel includes. */
#include "FreeRTOS.h" /* Must come first. */
#include "task.h"     /* RTOS task related API prototypes. */

/* Unity includes. */
#include "unity.h"

/* Pico includes. */
#include "pico/multicore.h"
#include "pico/stdlib.h"

/*-----------------------------------------------------------*/

/**
 * @brief The task that runs the test.
 */
static void prvTestRunnerTask( void * pvParameters );

/**
 * @brief The test case to run.
 */
extern void vRunMultipleTasksRunningTest( void );
/*-----------------------------------------------------------*/

static void prvTestRunnerTask( void * pvParameters )
{
    ( void ) pvParameters;

    /* Run test case. */
    vRunMultipleTasksRunningTest();

    vTaskDelete( NULL );
}
/*-----------------------------------------------------------*/

void vRunTest( void )
{
    xTaskCreate( prvTestRunnerTask,
                 "testRunner",
                 configMINIMAL_STACK_SIZE,
                 NULL,
                 configMAX_PRIORITIES - 1,
                 NULL );
}
/*-----------------------------------------------------------*/
