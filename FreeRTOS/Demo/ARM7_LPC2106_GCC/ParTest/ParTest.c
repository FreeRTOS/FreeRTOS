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

/*
	Changes from V2.5.2
		
	+ All LED's are turned off to start.
*/


#include "FreeRTOS.h"
#include "partest.h"

#define partstFIRST_IO			( ( unsigned long ) 0x400 )
#define partstNUM_LEDS			( 4 )
#define partstALL_OUTPUTS_OFF	( ( unsigned long ) 0xffffffff )

/*-----------------------------------------------------------
 * Simple parallel port IO routines.
 *-----------------------------------------------------------*/

void vParTestInitialise( void )
{
	/* This is performed from main() as the io bits are shared with other setup
	functions. */

	/* Turn all outputs off. */
	GPIO_IOSET = partstALL_OUTPUTS_OFF;
}
/*-----------------------------------------------------------*/

void vParTestSetLED( unsigned portBASE_TYPE uxLED, signed portBASE_TYPE xValue )
{
unsigned long ulLED = partstFIRST_IO;

	if( uxLED < partstNUM_LEDS )
	{
		/* Rotate to the wanted bit of port 0.  Only P10 to P13 have an LED
		attached. */
		ulLED <<= ( unsigned long ) uxLED;

		/* Set of clear the output. */
		if( xValue )
		{
			GPIO_IOCLR = ulLED;
		}
		else
		{
			GPIO_IOSET = ulLED;			
		}
	}	
}
/*-----------------------------------------------------------*/

void vParTestToggleLED( unsigned portBASE_TYPE uxLED )
{
unsigned long ulLED = partstFIRST_IO, ulCurrentState;

	if( uxLED < partstNUM_LEDS )
	{
		/* Rotate to the wanted bit of port 0.  Only P10 to P13 have an LED
		attached. */
		ulLED <<= ( unsigned long ) uxLED;

		/* If this bit is already set, clear it, and vice versa. */
		ulCurrentState = GPIO0_IOPIN;
		if( ulCurrentState & ulLED )
		{
			GPIO_IOCLR = ulLED;
		}
		else
		{
			GPIO_IOSET = ulLED;			
		}
	}	
}

