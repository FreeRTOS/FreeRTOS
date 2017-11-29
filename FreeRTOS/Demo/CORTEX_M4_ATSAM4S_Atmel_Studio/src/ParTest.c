/*
 * FreeRTOS Kernel V10.0.0
 * Copyright (C) 2017 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software. If you wish to use our Amazon
 * FreeRTOS name, please do so in a fair use way that does not cause confusion.
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

/* Library includes. */
#include <board.h>
#include <gpio.h>

/* The number of LEDs available to the user on the evaluation kit. */
#define partestNUM_LEDS			( 3UL )

/* Definitions not included in sam4s_ek.h. */
#define LED2_GPIO 				( PIO_PC20_IDX )

/* One of the LEDs is wired in the inverse to the others as it is also used as
the power LED. */
#define partstsINVERTED_LED		( 0UL )

/* The index of the pins to which the LEDs are connected.  The ordering of the
LEDs in this array is intentional and matches the order they appear on the 
hardware. */
static const uint32_t ulLED[] = { LED2_GPIO, LED0_GPIO, LED1_GPIO };

/*-----------------------------------------------------------*/

void vParTestInitialise( void )
{
unsigned long ul;

	for( ul = 0; ul < partestNUM_LEDS; ul++ )
	{
		/* Configure the LED, before ensuring it starts in the off state. */
		gpio_configure_pin( ulLED[ ul ],  ( PIO_OUTPUT_1 | PIO_DEFAULT ) );
		vParTestSetLED( ul, pdFALSE );
	}
}
/*-----------------------------------------------------------*/

void vParTestSetLED( unsigned portBASE_TYPE uxLED, signed portBASE_TYPE xValue )
{	
	if( uxLED < partestNUM_LEDS )
	{
		if( uxLED == partstsINVERTED_LED )
		{
			xValue = !xValue;					
		}
		
		if( xValue != pdFALSE )
		{
			/* Turn the LED on. */
			taskENTER_CRITICAL();
			{
				gpio_set_pin_low( ulLED[ uxLED ]);
			}
			taskEXIT_CRITICAL();
		}
		else
		{
			/* Turn the LED off. */
			taskENTER_CRITICAL();
			{
				gpio_set_pin_high( ulLED[ uxLED ]);
			}
			taskEXIT_CRITICAL();
		}
	}
}
/*-----------------------------------------------------------*/

void vParTestToggleLED( unsigned portBASE_TYPE uxLED )
{
	if( uxLED < partestNUM_LEDS )
	{
		taskENTER_CRITICAL();
		{			
			gpio_toggle_pin( ulLED[ uxLED ] );
		}
		taskEXIT_CRITICAL();		
	}
}
							


