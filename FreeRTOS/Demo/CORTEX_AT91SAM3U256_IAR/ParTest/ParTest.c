/*
 * FreeRTOS Kernel V10.4.1
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
#include <pio/pio.h>

#define partestNUM_LEDS ( sizeof( xLEDPins ) / sizeof( Pin ) )

static const Pin xLEDPins[] = { PINS_LEDS };

/*-----------------------------------------------------------*/

void vParTestInitialise( void )
{
long l;

	for( l = 0; l < partestNUM_LEDS; l++ )
	{
		PIO_Configure( &( xLEDPins[ l ] ), pdTRUE );
	}
}
/*-----------------------------------------------------------*/

void vParTestSetLED( unsigned portBASE_TYPE uxLED, signed portBASE_TYPE xValue )
{
	if( uxLED < partestNUM_LEDS )
	{
		if( xValue )
		{
			/* Turn the LED on. */
			portENTER_CRITICAL();
			{
				if( xLEDPins[ uxLED ].type == PIO_OUTPUT_0 )
				{			
					PIO_Set( &( xLEDPins[ uxLED ]) );
				}
				else
				{			
					PIO_Clear( &( xLEDPins[ uxLED ] ) );
				}
			}
			portEXIT_CRITICAL();
		}
		else
		{
			/* Turn the LED off. */
			portENTER_CRITICAL();
			{
				if( xLEDPins[ uxLED ].type == PIO_OUTPUT_0 )
				{			
					PIO_Clear( &( xLEDPins[ uxLED ] ) );
				}
				else
				{			
					PIO_Set( &( xLEDPins[ uxLED ] ) );
				}
			}
			portEXIT_CRITICAL();
		}
	}
}
/*-----------------------------------------------------------*/

void vParTestToggleLED( unsigned portBASE_TYPE uxLED )
{
	if( uxLED < partestNUM_LEDS )
	{
		if( PIO_GetOutputDataStatus( &( xLEDPins[ uxLED ] ) ) )
		{		
			PIO_Clear( &( xLEDPins[ uxLED ] ) );
		}
		else
		{		
			PIO_Set( &( xLEDPins[ uxLED ] ) );
		}		
	}
}
							


