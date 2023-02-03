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
 * @file interrupt_wait_critical.c
 * @brief If a task is interrupted while it is waiting to enter a critical section,
 *        it shall relinquish the core instead of continuing to wait to enter critical section.
 *
 * Procedure:
 *   - Create ( num of cores ) tasks, T0 ~ T(n-1).
 *   - Priority testRunner > T0 > T1~T(n-1)
 *   - TestRunner task enter critical section.
 *   - T0 tries to enter critical section.
 *   - T1 ~ T(n-1) keep in busy loop.
 *   - TestRunner suspends Task T0.
 * Expected:
 *   - T0 is suspended and it never enters critical section.
 *   - Task T1 ~ T(n-1) are running.
 */

/* Kernel includes. */
#include "FreeRTOS.h" /* Must come first. */
#include "task.h"     /* RTOS task related API prototypes. */

#include "unity.h"    /* unit testing support functions */
/*-----------------------------------------------------------*/

#if ( configNUMBER_OF_CORES < 2 )
    #error This test is for FreeRTOS SMP and therefore, requires at least 2 cores.
#endif /* if configNUMBER_OF_CORES != 2 */

#if configRUN_MULTIPLE_PRIORITIES != 1
    #error test_config.h must be included at the end of FreeRTOSConfig.h.
#endif
/*-----------------------------------------------------------*/

/**
 * @brief Task function that tries to enter critical section.
 */
static void prvEnterCriticalTask( void * pvParameters );

/**
 * @brief Function that implements a never blocking FreeRTOS task.
 */
static void prvEverRunningTask( void * pvParameters );

/**
 * @brief Test case "Interrupt Wait Critical".
 */
static void Test_InterruptWaitCritical( void );

/*-----------------------------------------------------------*/

typedef enum CriticalStatus
{
    CS_WAIT = 0,
    CS_ENTERING,
    CS_ENTERED,
    CS_EXIT,
} CriticalSectionStatus_t;
/*-----------------------------------------------------------*/

/**
 * @brief Handles of the tasks created in this test.
 */
static TaskHandle_t xTaskHanldes[ configNUMBER_OF_CORES ];

/**
 * @brief A flag to know if testRunner entered critical section.
 */
static BaseType_t volatile xIsTestRunnerEnteredCritical = pdFALSE;

/**
 * @brief A status to know if T0.
 *        - CS_WAIT:     Waiting for testRunner to enter critical section.
 *        - CS_ENTERING: Entering critical section.
 *        - CS_ENTERED:  Entered critical section.
 *        - CS_EXIT:     Exited critical section.
 */
static CriticalSectionStatus_t volatile xT0CsStatus = CS_WAIT;

/*-----------------------------------------------------------*/

static void Test_InterruptWaitCritical( void )
{
    int i;
    eTaskState xTaskState;
    BaseType_t xIsTestPass = pdTRUE;

    /* Yield for other cores to run tasks. */
    taskYIELD();

    taskENTER_CRITICAL();

    xIsTestRunnerEnteredCritical = pdTRUE;

    /* Busy loop to wait T0 to run. */
    while( xT0CsStatus < CS_ENTERING )
    {
        /* Put asm here to avoid optimization by compiler. */
        __asm volatile ( "nop" );
    }

    for( i = 0; i < 0xFFFF; i++ )
    {
        /* Put asm here to avoid optimization by compiler. */
        __asm volatile ( "nop" );
    }

    vTaskSuspend( xTaskHanldes[ 0 ] );

    taskEXIT_CRITICAL();

    /* When testRunner exits CS, context switch continues.
     * Busy loop here for task T1~T(n-1) to run */
    for( i = 0; i < 0xFFFF; i++ )
    {
        /* Put asm here to avoid optimization by compiler. */
        __asm volatile ( "nop" );
    }

    /* Ensure that T1~T(n-1) are running. */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        xTaskState = eTaskGetState( xTaskHanldes[ i ] );

        if( ( i == 0 ) && ( xTaskState == eRunning ) )
        {
            xIsTestPass = 0x10;
            break;
        }
        else if( ( i != 0 ) && ( xTaskState != eRunning ) )
        {
            xIsTestPass = 0x20 | i;
            break;
        }
    }

    if( xT0CsStatus >= CS_ENTERED )
    {
        xIsTestPass |= 0x40;
    }

    TEST_ASSERT_EQUAL_INT( xIsTestPass, pdTRUE );
}
/*-----------------------------------------------------------*/

static void prvEnterCriticalTask( void * pvParameters )
{
    /* Silence warnings about unused parameters. */
    ( void ) pvParameters;

    while( xIsTestRunnerEnteredCritical == pdFALSE )
    {
        /* Busy loop here intil testRunner enters critical section. */
        __asm volatile ( "nop" );
    }

    xT0CsStatus = CS_ENTERING;

    taskENTER_CRITICAL();
    xT0CsStatus = CS_ENTERED;
    taskEXIT_CRITICAL();

    xT0CsStatus = CS_EXIT;

    for( ; ; )
    {
        /* Always running, put asm here to avoid optimization by compiler. */
        __asm volatile ( "nop" );
    }
}
/*-----------------------------------------------------------*/

static void prvEverRunningTask( void * pvParameters )
{
    /* Silence warnings about unused parameters. */
    ( void ) pvParameters;

    for( ; ; )
    {
        /* Always running, put asm here to avoid optimization by compiler. */
        __asm volatile ( "nop" );
    }
}

/* Runs before every test, put init calls here. */
void setUp( void )
{
    int i;
    BaseType_t xTaskCreationResult;

    xTaskCreationResult = xTaskCreate( prvEnterCriticalTask,
                                       "EnterCS",
                                       configMINIMAL_STACK_SIZE,
                                       NULL,
                                       configMAX_PRIORITIES - 2,
                                       &( xTaskHanldes[ 0 ] ) );

    TEST_ASSERT_EQUAL_MESSAGE( pdPASS, xTaskCreationResult, "Task creation failed." );

    /* Create configNUMBER_OF_CORES - 1 low priority tasks. */
    for( i = 1; i < configNUMBER_OF_CORES; i++ )
    {
        xTaskCreationResult = xTaskCreate( prvEverRunningTask,
                                           "EverRunning",
                                           configMINIMAL_STACK_SIZE,
                                           NULL,
                                           configMAX_PRIORITIES - 3,
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

void vRunInterruptWaitCriticalTest( void )
{
    UNITY_BEGIN();

    RUN_TEST( Test_InterruptWaitCritical );

    UNITY_END();
}
/*-----------------------------------------------------------*/
