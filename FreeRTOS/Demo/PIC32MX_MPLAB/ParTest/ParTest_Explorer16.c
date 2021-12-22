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
 * http://www.FreeRTOS.org
 * http://aws.amazon.com/freertos
 *
 * 1 tab == 4 spaces!
 */

/* Scheduler includes. */
#include "FreeRTOS.h"

/* Demo app includes. */
#include "partest.h"

#define ptOUTPUT 	0
#define ptALL_OFF	0

/*-----------------------------------------------------------
 * Simple parallel port IO routines.
 *-----------------------------------------------------------*/

void vParTestInitialise( void )
{
	/* All LEDs output. */	
	TRISA = ptOUTPUT;	
	PORTA = ptALL_OFF;

	/* Disable the JTAG. */
	DDPCONbits.JTAGEN = 0;
}
/*-----------------------------------------------------------*/

void vParTestSetLED( unsigned portBASE_TYPE uxLED, signed portBASE_TYPE xValue )
{
unsigned portBASE_TYPE uxLEDBit;

	/* Which port A bit is being modified? */
	uxLEDBit = 1 << uxLED;

	if( xValue )
	{
		/* Turn the LED on.   Use of the PORTASET register removes the need
		to use a critical section. */
		PORTASET = uxLEDBit;
	}
	else
	{
		/* Turn the LED off.  Use of the PORTACLR register removes the need
		to use a critical section. */
		PORTACLR = uxLEDBit;
	}
}
/*-----------------------------------------------------------*/

void vParTestToggleLED( unsigned portBASE_TYPE uxLED )
{
unsigned portBASE_TYPE uxLEDBit;
	
	uxLEDBit = 1 << uxLED;

	/* Use of the PORTAINV register removes the need to use a critical section. */
	PORTAINV = uxLEDBit;
}



