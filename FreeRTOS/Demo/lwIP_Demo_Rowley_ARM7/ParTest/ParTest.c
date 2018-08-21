/*
 * FreeRTOS Kernel V10.1.0
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

/* Scheduler includes. */
#include "FreeRTOS.h"

/* Demo application includes. */
#include "partest.h"

/* Hardware specific includes. */
#include "Board.h"


/*-----------------------------------------------------------
 * Simple parallel port IO routines for the LED's.  LED's can be set, cleared
 * or toggled.
 *-----------------------------------------------------------*/
const unsigned long ulLED_MASK[ NB_LED ]= { LED1, LED2, LED3, LED4 };

void vParTestInitialise( void )
{	
	/* Start with all LED's off. */
    AT91C_BASE_PIOB->PIO_SODR = LED_MASK;
}
/*-----------------------------------------------------------*/

void vParTestSetLED( unsigned portBASE_TYPE uxLED, signed portBASE_TYPE xValue )
{
	if( uxLED < ( portBASE_TYPE ) NB_LED )
	{
		if( xValue )
		{
			AT91C_BASE_PIOB->PIO_SODR = ulLED_MASK[ uxLED ];
		}
		else
		{
			AT91C_BASE_PIOB->PIO_CODR = ulLED_MASK[ uxLED ];
		}
	}
}
/*-----------------------------------------------------------*/

void vParTestToggleLED( unsigned portBASE_TYPE uxLED )
{
	if( uxLED < ( portBASE_TYPE ) NB_LED )
	{
		if( AT91C_BASE_PIOB->PIO_PDSR & ulLED_MASK[ uxLED ] )
		{
			AT91C_BASE_PIOB->PIO_CODR = ulLED_MASK[ uxLED ];
		}
		else
		{
			AT91C_BASE_PIOB->PIO_SODR = ulLED_MASK[ uxLED ];
		}
	}
}

