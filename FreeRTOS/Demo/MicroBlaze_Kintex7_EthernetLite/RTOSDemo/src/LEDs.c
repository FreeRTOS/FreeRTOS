/*
 * FreeRTOS Kernel V10.2.0
 * Copyright (C) 2019 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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


/*-----------------------------------------------------------
 * Simple IO routines to control the LEDs.
 *-----------------------------------------------------------*/

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "task.h"

/* Demo includes. */
#include "partest.h"

/* Xilinx includes. */
#include "xgpio.h"


#define partstNUM_LEDS	8

/*-----------------------------------------------------------*/

/* The GPIO instance to which the LEDs are connected. */
static XGpio xOutputGPIOInstance;

/* Maintains the current LED output state. */
static volatile UBaseType_t uxGPIOState = 0U;

/* Constant required by the Xilinx peripheral driver API functions that are
relevant to the particular hardware set up. */
static const unsigned long ulGPIOOutputChannel = 1UL;

/*-----------------------------------------------------------*/

void vParTestInitialise( void )
{
portBASE_TYPE xStatus;
const unsigned char ucSetToOutput = 0U;

	/* Initialize the GPIO for the LEDs. */
	xStatus = XGpio_Initialize( &xOutputGPIOInstance, XPAR_AXI_GPIO_0_DEVICE_ID );
	if( xStatus == XST_SUCCESS )
	{
		/* All bits on this channel are going to be outputs (LEDs). */
		XGpio_SetDataDirection( &xOutputGPIOInstance, ulGPIOOutputChannel, ucSetToOutput );

		/* Start with all LEDs off. */
		uxGPIOState = 0U;
		XGpio_DiscreteWrite( &xOutputGPIOInstance, ulGPIOOutputChannel, ( uint8_t ) uxGPIOState );
	}

	configASSERT( ( xStatus == XST_SUCCESS ) );
}
/*-----------------------------------------------------------*/

void vParTestSetLED( UBaseType_t uxLED, BaseType_t xValue )
{
	if( uxLED < partstNUM_LEDS )
	{
		taskENTER_CRITICAL();
		{
			if( xValue != pdFALSE )
			{
				uxGPIOState |= ( 1UL << uxLED );
			}
			else
			{
				uxGPIOState &= ~( 1UL << uxLED );
			}

			XGpio_DiscreteWrite( &xOutputGPIOInstance, ulGPIOOutputChannel, ( uint8_t ) uxGPIOState );
		}
		taskEXIT_CRITICAL();
	}
}
/*-----------------------------------------------------------*/

void vParTestToggleLED( unsigned portBASE_TYPE uxLED )
{
	if( uxLED < partstNUM_LEDS )
	{
		taskENTER_CRITICAL();
		{
			uxGPIOState ^= ( 1UL << uxLED );
			XGpio_DiscreteWrite( &xOutputGPIOInstance, ulGPIOOutputChannel, ( uint8_t ) uxGPIOState );
		}
		taskEXIT_CRITICAL();
	}
}

