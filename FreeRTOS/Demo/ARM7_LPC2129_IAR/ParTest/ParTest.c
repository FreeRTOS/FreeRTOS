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
 * Simple parallel port IO routines for the LED's.
 *-----------------------------------------------------------*/


/* Scheduler includes. */
#include "FreeRTOS.h"

/* Demo application includes. */
#include "partest.h"

/* Board specific defines. */
#define partstFIRST_IO		( ( unsigned long ) 0x10000 )
#define partstNUM_LEDS		( 8 )

/*-----------------------------------------------------------*/

void vParTestInitialise( void )
{	
	/* The ports are setup within prvInitialiseHardware(), called by main(). */
}
/*-----------------------------------------------------------*/

void vParTestSetLED( unsigned portBASE_TYPE uxLED, signed portBASE_TYPE xValue )
{
unsigned long ulLED = partstFIRST_IO;

	if( uxLED < partstNUM_LEDS )
	{
		/* Rotate to the wanted bit of port 1.  Only P16 to P23 have an LED
		attached. */
		ulLED <<= ( unsigned long ) uxLED;

		/* Set or clear the output. */
		if( xValue )
		{
			IO1SET = ulLED;
		}
		else
		{
			IO1CLR = ulLED;			
		}
	}	
}
/*-----------------------------------------------------------*/

void vParTestToggleLED( unsigned portBASE_TYPE uxLED )
{
unsigned long ulLED = partstFIRST_IO, ulCurrentState;

	if( uxLED < partstNUM_LEDS )
	{
		/* Rotate to the wanted bit of port 1.  Only P10 to P13 have an LED
		attached. */
		ulLED <<= ( unsigned long ) uxLED;

		/* If this bit is already set, clear it, and vice versa. */
		ulCurrentState = IO1PIN;
		if( ulCurrentState & ulLED )
		{
			IO1CLR = ulLED;
		}
		else
		{
			IO1SET = ulLED;			
		}
	}	
}


