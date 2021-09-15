/*
 * FreeRTOS V202107.00
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

/* FreeRTOS kernel includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"
#include "timers.h"

/* BSP includes. */
#include "fsl_device_registers.h"
#include "fsl_debug_console.h"
#include "clock_config.h"
#include "fsl_power.h"
#include "pin_mux.h"
#include "board.h"

/*-----------------------------------------------------------*/

/**
 * @brief The task that implements the demo.
 */
static void prvDemoTask( void *pvParameters );

/**
 * @brief Initialize hardware.
 */
static void prvInitializeHardware( void );
/*-----------------------------------------------------------*/

static void prvDemoTask( void *pvParameters )
{
    ( void ) pvParameters;

    for( ; ; )
    {
        vTaskDelay( pdMS_TO_TICKS( 1000 ) );
    }
}
/*-----------------------------------------------------------*/

static void prvInitializeHardware( void )
{
    /* Set BOD VBAT level to 1.65V. */
    POWER_SetBodVbatLevel( kPOWER_BodVbatLevel1650mv, kPOWER_BodHystLevel50mv, false );

    /* Attach main clock divide to FLEXCOMM0 (debug console). */
    CLOCK_AttachClk( BOARD_DEBUG_UART_CLK_ATTACH );

    BOARD_InitBootPins();
    BOARD_InitBootClocks();
    BOARD_InitDebugConsole();
}
/*-----------------------------------------------------------*/

/**
 * @brief Entry point.
 */
int main( void )
{
    static StackType_t xDemoTaskStack[ configMINIMAL_STACK_SIZE ] __attribute__( ( aligned( 32 ) ) );
    TaskParameters_t xDemoTaskParameters =
    {
        .pvTaskCode     = prvDemoTask,
        .pcName         = "Demo",
        .usStackDepth   = configMINIMAL_STACK_SIZE,
        .pvParameters   = NULL,
        .uxPriority     = tskIDLE_PRIORITY,
        .puxStackBuffer = xDemoTaskStack,
        .xRegions       =
        {
            { 0, 0, 0 },
            { 0, 0, 0 },
            { 0, 0, 0 },
        }
    };

    /* Initialize board hardware. */
    prvInitializeHardware();

    xTaskCreateRestricted( &( xDemoTaskParameters ), NULL );

    vTaskStartScheduler();

    /* Should never reach here. */
    for( ; ; );
}
/*-----------------------------------------------------------*/
