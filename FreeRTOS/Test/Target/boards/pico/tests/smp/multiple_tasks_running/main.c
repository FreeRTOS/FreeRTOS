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
 * @file main.c
 * @brief The implementation of main function to start test runner task.
 *
 * Procedure:
 *   - Initialize environment
 *   - Run the test case
 */

/* Kernel includes. */
#include "FreeRTOS.h" /* Must come first. */
#include "task.h"     /* RTOS task related API prototypes. */

#include "unity.h"    /* unit testing support functions */

#include "pico/multicore.h"
#include "pico/stdlib.h"

/*-----------------------------------------------------------*/

#define TASK_TESTRUNNER_PRIORITY    ( tskIDLE_PRIORITY + 1 )

/*-----------------------------------------------------------*/

static void prvTestRunnerTask( void * pvParameters );
extern void Test_MultipleTasksRunning( void );
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
    UNITY_BEGIN();

    RUN_TEST( Test_MultipleTasksRunning );

    UNITY_END();

    for( ; ; )
    {
        vTaskDelay( pdMS_TO_TICKS( 1000 ) );
    }
}
/*-----------------------------------------------------------*/

void vPortInitTestEnvironment( void )
{
    /* Setup LED I/O */
    gpio_init( PICO_DEFAULT_LED_PIN );
    gpio_set_dir( PICO_DEFAULT_LED_PIN, GPIO_OUT );
    gpio_set_irq_enabled( PICO_DEFAULT_LED_PIN,
                          GPIO_IRQ_LEVEL_LOW |
                          GPIO_IRQ_LEVEL_HIGH |
                          GPIO_IRQ_EDGE_FALL |
                          GPIO_IRQ_EDGE_RISE,
                          false );

    /* Want to be able to printf */
    stdio_init_all();

    while( !stdio_usb_connected() )
    {
        gpio_put( PICO_DEFAULT_LED_PIN, 1 );
        sleep_ms( 250 );
        gpio_put( PICO_DEFAULT_LED_PIN, 0 );
        sleep_ms( 250 );
    }
}
/*-----------------------------------------------------------*/

void vApplicationStackOverflowHook( TaskHandle_t xTask,
                                    char * pcTaskName )
{
    ( void ) pcTaskName;
    ( void ) xTask;

    printf( "ERROR: Stack Overflow\n\0" );

    /* Run time stack overflow checking is performed if
     * configconfigCHECK_FOR_STACK_OVERFLOW is defined to 1 or 2.  This hook
     * function is called if a stack overflow is detected.  pxCurrentTCB can be
     * inspected in the debugger if the task name passed into this function is
     * corrupt. */
    for( ; ; )
    {
    }
}
/*-----------------------------------------------------------*/

void vApplicationTickHook( void )
{
    static uint32_t ulCount = 0;

    ulCount++;
}
/*-----------------------------------------------------------*/

void vApplicationMallocFailedHook( void )
{
    printf( "ERROR: Malloc Failed\n\0" );
}
/*-----------------------------------------------------------*/

/* Runs before every test, put init calls here. */
void setUp( void )
{
}
/*-----------------------------------------------------------*/

/* Run after every test, put clean-up calls here. */
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
