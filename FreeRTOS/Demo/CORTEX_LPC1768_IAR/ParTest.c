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

/* FreeRTOS.org includes. */
#include "FreeRTOS.h"

/* Demo application includes. */
#include "partest.h"

/*-----------------------------------------------------------
 * Simple parallel port IO routines.
 *-----------------------------------------------------------*/

#define partstLED1_OUTPUT		( 1 << 25 )
#define partstLED2_OUTPUT		( 1 << 4 )

void vParTestInitialise( void )
{
	/* Set LEDs to output. */
    GPIO1->FIODIR = partstLED1_OUTPUT;
	GPIO0->FIODIR = partstLED2_OUTPUT;

	/* Start with LED off. */
    GPIO1->FIOSET = partstLED1_OUTPUT;
	GPIO0->FIOSET = partstLED2_OUTPUT;
}
/*-----------------------------------------------------------*/

void vParTestSetLED( unsigned long ulLEDIn, signed long xValue )
{
	/* Used to set and clear LEDs on FIO2. */

	if( ulLEDIn == 0 )
	{
		/* Set of clear the output. */
		if( xValue )
		{
			GPIO1->FIOCLR = partstLED1_OUTPUT;
		}
		else
		{
			GPIO1->FIOSET = partstLED1_OUTPUT;
		}
	}
	else if( ulLEDIn == 1 )
	{
		/* Set of clear the output. */
		if( xValue )
		{
			GPIO0->FIOCLR = partstLED2_OUTPUT;
		}
		else
		{
			GPIO0->FIOSET = partstLED2_OUTPUT;
		}
	}
}
/*-----------------------------------------------------------*/

void vParTestToggleLED( unsigned long ulLEDIn )
{
unsigned long ulCurrentState;

	/* Used to toggle LEDs on FIO2. */

	if( ulLEDIn == 0 )
	{
		/* If this bit is already set, clear it, and vice versa. */
		ulCurrentState = GPIO1->FIOPIN;
		if( ulCurrentState & partstLED1_OUTPUT )
		{
			GPIO1->FIOCLR = partstLED1_OUTPUT;
		}
		else
		{
			GPIO1->FIOSET = partstLED1_OUTPUT;
		}
	}
	else if( ulLEDIn == 1 )
	{
		/* If this bit is already set, clear it, and vice versa. */
		ulCurrentState = GPIO0->FIOPIN;
		if( ulCurrentState & partstLED2_OUTPUT )
		{
			GPIO0->FIOCLR = partstLED2_OUTPUT;
		}
		else
		{
			GPIO0->FIOSET = partstLED2_OUTPUT;
		}
	}
}
/*-----------------------------------------------------------*/

long lParTestGetLEDState( void )
{
	if( ( GPIO0->FIOPIN & partstLED2_OUTPUT ) == 0 )
	{
		return pdFALSE;
	}
	else
	{
		return pdTRUE;
	}
}
/*-----------------------------------------------------------*/

void vParTestSetLEDState( long lState )
{
	/* Used to set and clear the LEDs on FIO1. */
	if( lState != pdFALSE )
	{
		GPIO0->FIOCLR = partstLED2_OUTPUT;
	}
	else
	{
		GPIO0->FIOSET = partstLED2_OUTPUT;
	}
}
/*-----------------------------------------------------------*/

