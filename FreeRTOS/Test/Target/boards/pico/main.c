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
 * @file main.c
 * @brief The implementation of main function to start test runner task.
 *
 * Procedure:
 *   - Initialize environment.
 *   - Run the test case.
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
 * Initialize required peripherals.
 */
static void prvInitializeHardware( void );

/**
 * @brief Run test.
 */
extern void vRunTest( void );
/*-----------------------------------------------------------*/

static void prvInitializeHardware( void )
{
    /* Needed for printf. */
    stdio_init_all();

    while( !stdio_usb_connected() )
    {
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
     * configCHECK_FOR_STACK_OVERFLOW is defined to 1 or 2.  This hook
     * function is called if a stack overflow is detected.  pxCurrentTCB can be
     * inspected in the debugger if the task name passed into this function is
     * corrupt. */
    for( ; ; )
    {
        /* Always running, put asm here to avoid optimization by compiler. */
        __asm volatile ( "nop" );
    }
}
/*-----------------------------------------------------------*/

void vApplicationTickHook( void )
{
}
/*-----------------------------------------------------------*/

void vApplicationMallocFailedHook( void )
{
    printf( "ERROR: Malloc Failed\n\0" );

    for( ; ; )
    {
        /* Always running, put asm here to avoid optimization by compiler. */
        __asm volatile ( "nop" );
    }
}
/*-----------------------------------------------------------*/

int main( void )
{
    prvInitializeHardware();

    vRunTest();

    vTaskStartScheduler();

    /* Should never reach here. */
    panic_unsupported();

    return 0;
}
/*-----------------------------------------------------------*/
