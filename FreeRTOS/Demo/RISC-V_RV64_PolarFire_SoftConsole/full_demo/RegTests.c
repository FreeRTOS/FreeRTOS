/*
 * FreeRTOS V202112.00
 * Copyright (C) 2021 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 * http://www.FreeRTOS.org
 * http://aws.amazon.com/freertos
 *
 * 1 tab == 4 spaces!
 */

/* Scheduler include files. */
#include "FreeRTOS.h"
#include "task.h"

/* Interface include files. */
#include "RegTests.h"

/* Parameters that are passed into the register check tasks solely for the
 * purpose of ensuring parameters are passed into tasks correctly. */
#define REG_TEST_TASK_1_PARAMETER        ( ( void * ) 0x12345678 )
#define REG_TEST_TASK_2_PARAMETER        ( ( void * ) 0x87654321 )
/*-----------------------------------------------------------*/

/* Tasks that implement register tests. */
static void prvRegisterTest1Task( void *pvParameters );
static void prvRegisterTest2Task( void *pvParameters );
extern void vRegTest1Implementation( void );
extern void vRegTest2Implementation( void );

/* Flag that will be latched to pdTRUE should any unexpected behaviour be
 * detected in any of the tasks. */
static volatile BaseType_t xErrorDetected = pdFALSE;

/* Counters that are incremented on each cycle of a test.  This is used to
 * detect a stalled task - a test that is no longer running. */
volatile uint32_t ulRegisterTest1Counter = 0;
volatile uint32_t ulRegisterTest2Counter = 0;
/*-----------------------------------------------------------*/

static void prvRegisterTest1Task( void *pvParameters )
{
    /* Although the regtest task is written in assembler, its entry point is
     * written in C for convenience of checking the task parameter is being
     * passed in correctly. */
    if( pvParameters == REG_TEST_TASK_1_PARAMETER )
    {
        /* Start the part of the test that is written in assembler. */
        vRegTest1Implementation();
    }

    /* The following line will only execute if the task parameter is found to
     * be incorrect.  The check task will detect that the regtest loop counter
     * is not being incremented and flag an error. */
    vTaskDelete( NULL );
}
/*-----------------------------------------------------------*/

static void prvRegisterTest2Task( void *pvParameters )
{
    /* Although the regtest task is written in assembler, its entry point is
     * written in C for convenience of checking the task parameter is being
     * passed in correctly. */
    if( pvParameters == REG_TEST_TASK_2_PARAMETER )
    {
        /* Start the part of the test that is written in assembler. */
        vRegTest2Implementation();
    }

    /* The following line will only execute if the task parameter is found to
     * be incorrect.  The check task will detect that the regtest loop counter
     * is not being incremented and flag an error. */
    vTaskDelete( NULL );
}
/*-----------------------------------------------------------*/

void vStartRegisterTasks( UBaseType_t uxPriority )
{
    BaseType_t ret;

    ret = xTaskCreate( prvRegisterTest1Task,
                      "RegTest1",
                      configMINIMAL_STACK_SIZE,
                      REG_TEST_TASK_1_PARAMETER,
                      uxPriority,
                      NULL );
    configASSERT( ret == pdPASS );

    ret = xTaskCreate( prvRegisterTest2Task,
                      "RegTest2",
                      configMINIMAL_STACK_SIZE,
                      REG_TEST_TASK_2_PARAMETER,
                      uxPriority,
                      NULL );
    configASSERT( ret == pdPASS );
}
/*-----------------------------------------------------------*/

BaseType_t xAreRegisterTasksStillRunning( void )
{
static uint32_t ulLastRegisterTest1Counter = 0, ulLastRegisterTest2Counter = 0;

    /* If the register test task is still running then we expect the loop
     * counters to have incremented since this function was last called. */
    if( ulLastRegisterTest1Counter == ulRegisterTest1Counter )
    {
        xErrorDetected = pdTRUE;
    }

    if( ulLastRegisterTest2Counter == ulRegisterTest2Counter )
    {
        xErrorDetected = pdTRUE;
    }

    ulLastRegisterTest1Counter = ulRegisterTest1Counter;
    ulLastRegisterTest2Counter = ulRegisterTest2Counter;

    /* Errors detected in the task itself will have latched xErrorDetected
     * to true. */
    return ( BaseType_t ) !xErrorDetected;
}
/*-----------------------------------------------------------*/
