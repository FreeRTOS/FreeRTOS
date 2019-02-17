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
 * Simple parallel port IO routines.
 *-----------------------------------------------------------*/

/* Kernel includes. */
#include "FreeRTOS.h"
#include "task.h"

/* Library includes. */
#include "mss_gpio.h"

#define partstMAX_LEDS		8

static volatile unsigned long ulGPIOState = 0UL;

/*-----------------------------------------------------------*/

void vParTestInitialise( void )
{
long x;

	/* Initialise the GPIO */
	MSS_GPIO_init();

	/* Set up GPIO for the LEDs. */
	for( x = 0; x < partstMAX_LEDS; x++ )
	{
		MSS_GPIO_config( ( mss_gpio_id_t ) x , MSS_GPIO_OUTPUT_MODE );
	}

	/* All LEDs start off. */
	ulGPIOState = 0xffffffffUL;
	MSS_GPIO_set_outputs( ulGPIOState );
}
/*-----------------------------------------------------------*/

void vParTestSetLED( unsigned portBASE_TYPE uxLED, signed portBASE_TYPE xValue )
{
	if( uxLED < partstMAX_LEDS )
	{
		/* A critical section is used as the LEDs are also accessed from an
		interrupt. */
		taskENTER_CRITICAL();
		{
			if( xValue == pdTRUE )
			{
				ulGPIOState &= ~( 1UL << uxLED );
			}
			else
			{
				ulGPIOState |= ( 1UL << uxLED );
			}
			
			MSS_GPIO_set_outputs( ulGPIOState );
		}
		taskEXIT_CRITICAL();
	}
}
/*-----------------------------------------------------------*/

void vParTestSetLEDFromISR( unsigned portBASE_TYPE uxLED, signed portBASE_TYPE xValue )
{
unsigned portBASE_TYPE uxInterruptFlags;

	uxInterruptFlags = portSET_INTERRUPT_MASK_FROM_ISR();
	{
		if( uxLED < partstMAX_LEDS )
		{
			if( xValue == pdTRUE )
			{
				ulGPIOState &= ~( 1UL << uxLED );
			}
			else
			{
				ulGPIOState |= ( 1UL << uxLED );
			}

			MSS_GPIO_set_outputs( ulGPIOState );
		}
	}
	portCLEAR_INTERRUPT_MASK_FROM_ISR( uxInterruptFlags );
}
/*-----------------------------------------------------------*/

void vParTestToggleLED( unsigned portBASE_TYPE uxLED )
{
	if( uxLED < partstMAX_LEDS )
	{
		/* A critical section is used as the LEDs are also accessed from an
		interrupt. */
		taskENTER_CRITICAL();
		{
			if( ( ulGPIOState & ( 1UL << uxLED ) ) != 0UL )
			{
				ulGPIOState &= ~( 1UL << uxLED );
			}
			else
			{
				ulGPIOState |= ( 1UL << uxLED );
			}
			
			MSS_GPIO_set_outputs( ulGPIOState );
		}
		taskEXIT_CRITICAL();
	}
}
/*-----------------------------------------------------------*/

long lParTestGetLEDState( unsigned long ulLED )
{
long lReturn = pdFALSE;

	if( ulLED < partstMAX_LEDS )
	{
		taskENTER_CRITICAL();
		{
			if( ( ulGPIOState & ( 1UL << ulLED ) ) == 0UL )
			{
				lReturn = pdTRUE;
			}
		}
		taskEXIT_CRITICAL();
	}

	return lReturn;
}
/*-----------------------------------------------------------*/
