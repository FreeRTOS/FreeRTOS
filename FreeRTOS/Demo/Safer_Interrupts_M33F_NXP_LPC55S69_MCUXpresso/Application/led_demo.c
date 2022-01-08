/*
 * FreeRTOS V202112.00
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"

/* BSP includes. */
#include "board.h"

/* Demo interface include. */
#include "led_demo.h"

/**
 * Represents which LEDs are on or off. pdTRUE is on.
 */
typedef struct LedState
{
    BaseType_t xRed;
    BaseType_t xGreen;
    BaseType_t xBlue;
} LedState_t;

/* The following needs to be placed in the shared memory as it is accessed in
 * the button pressed IRQ handler which is unprivileged. */
static LedState_t xLedState __attribute__( ( section( "user_irq_shared_memory" ) ) );
/*-----------------------------------------------------------*/

/**
 * @brief Turn on RGB Led according to the xLedState.
 */
static void prvTurnOnRgbLed( void );

/**
 * @brief Turn off RGB Led.
 */
static void prvTurnOffRgbLed( void );
/*-----------------------------------------------------------*/

static void prvTurnOnRgbLed( void )
{
    /* Setting the GPIO pin activates the color in RGB LED. */
    if( xLedState.xRed == pdTRUE )
    {
        GPIO_PortClear( GPIO, BOARD_LED_RED_GPIO_PORT, 1u << BOARD_LED_RED_GPIO_PIN );
    }
    if( xLedState.xGreen == pdTRUE )
    {
        GPIO_PortClear( GPIO, BOARD_LED_GREEN_GPIO_PORT, 1u << BOARD_LED_GREEN_GPIO_PIN );
    }
    if( xLedState.xBlue == pdTRUE )
    {
        GPIO_PortClear( GPIO, BOARD_LED_BLUE_GPIO_PORT, 1u << BOARD_LED_BLUE_GPIO_PIN );
    }
}
/*-----------------------------------------------------------*/

static void prvTurnOffRgbLed( void )
{
    /* Setting the pins high turns off the LED. */
    GPIO_PortSet( GPIO, BOARD_LED_RED_GPIO_PORT, 1u << BOARD_LED_RED_GPIO_PIN );
    GPIO_PortSet( GPIO, BOARD_LED_GREEN_GPIO_PORT, 1u << BOARD_LED_GREEN_GPIO_PIN );
    GPIO_PortSet( GPIO, BOARD_LED_BLUE_GPIO_PORT, 1u << BOARD_LED_BLUE_GPIO_PIN );
}
/*-----------------------------------------------------------*/

void vLedDemoTask( void * pvParams )
{
    /* Set the initial LED state. */
    xLedState.xRed = pdTRUE;
    xLedState.xGreen = pdTRUE;
    xLedState.xBlue = pdFALSE;

    /* Silence compiler warnings about unused variables. */
    ( void ) pvParams;

    for( ;; )
    {
        prvTurnOnRgbLed();
        vTaskDelay( pdMS_TO_TICKS( 1000 ) );

        prvTurnOffRgbLed();
        vTaskDelay( pdMS_TO_TICKS( 1000 ) );
    }
}
/*-----------------------------------------------------------*/

void vButtonPressedIRQHandler( uint32_t ulData )
{
    BaseType_t xPreviousRed;

    /* Data is not used. */
    ( void ) ulData;

    /* Shift to the next color. */
    xPreviousRed = xLedState.xRed;
    xLedState.xRed = xLedState.xGreen;
    xLedState.xGreen = xLedState.xBlue;
    xLedState.xBlue = xPreviousRed;
}
/*-----------------------------------------------------------*/
