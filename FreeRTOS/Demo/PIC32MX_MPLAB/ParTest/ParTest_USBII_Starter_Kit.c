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

/* Scheduler includes. */
#include "FreeRTOS.h"

/* Demo app includes. */
#include "partest.h"

#define ptOUTPUT 	0x07
#define ptALL_OFF	0x07
#define ptNUM_LEDS	3

/*-----------------------------------------------------------
 * Simple parallel port IO routines.
 *-----------------------------------------------------------*/

void vParTestInitialise( void )
{
	/* Bottom 3 LEDs output. */
	TRISD = TRISD & ~ptOUTPUT;
	PORTD = PORTD & ~ptALL_OFF;
}
/*-----------------------------------------------------------*/

void vParTestSetLED( unsigned portBASE_TYPE uxLED, signed portBASE_TYPE xValue )
{
unsigned portBASE_TYPE uxLEDBit;

	if( uxLED < ptNUM_LEDS )
	{
		/* Which port A bit is being modified? */
		uxLEDBit = 1 << uxLED;

		if( xValue != 0 )
		{
			/* Turn the LED on.   Use of the PORTASET register removes the need
			to use a critical section. */
			PORTDSET = uxLEDBit;
		}
		else
		{
			/* Turn the LED off.  Use of the PORTACLR register removes the need
			to use a critical section. */
			PORTDCLR = uxLEDBit;
		}
	}
}
/*-----------------------------------------------------------*/

void vParTestToggleLED( unsigned portBASE_TYPE uxLED )
{
unsigned portBASE_TYPE uxLEDBit;

	if( uxLED < ptNUM_LEDS )
	{
		uxLEDBit = 1 << uxLED;

		/* Use of the PORTAINV register removes the need to use a critical section. */
		PORTDINV = uxLEDBit;
	}
}



