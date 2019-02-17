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

#include "FreeRTOS.h"
#include "partest.h"
#include "board.h"

/*-----------------------------------------------------------
 * Simple parallel port IO routines for the LED's.
 *-----------------------------------------------------------*/

const unsigned long led_mask[ NB_LED ]= { LED1, LED2, LED3, LED4 };

void vParTestInitialise( void )
{	
	/* Start with all LED's off. */
	AT91F_PIO_SetOutput( AT91C_BASE_PIOA, LED_MASK );	
}
/*-----------------------------------------------------------*/

void vParTestSetLED( unsigned portBASE_TYPE uxLED, signed portBASE_TYPE xValue )
{
	if( uxLED < ( portBASE_TYPE ) NB_LED )
	{
		if( xValue )
		{
			AT91F_PIO_SetOutput( AT91C_BASE_PIOA, led_mask[ uxLED ] );
		}
		else
		{
			AT91F_PIO_ClearOutput( AT91C_BASE_PIOA, led_mask[ uxLED ]);
		}
	}
}
/*-----------------------------------------------------------*/

void vParTestToggleLED( unsigned portBASE_TYPE uxLED )
{
	if( uxLED < ( portBASE_TYPE ) NB_LED )
	{
		if( AT91F_PIO_GetInput( AT91C_BASE_PIOA ) & led_mask[ uxLED ] )
		{
			AT91F_PIO_ClearOutput( AT91C_BASE_PIOA, led_mask[ uxLED ]);
		}
		else
		{
			AT91F_PIO_SetOutput( AT91C_BASE_PIOA, led_mask[ uxLED ] );					
		}
	}
}


