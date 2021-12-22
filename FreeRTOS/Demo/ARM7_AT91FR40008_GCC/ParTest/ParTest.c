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
#include "portable.h"

/* Demo app includes. */
#include "partest.h"

/* Hardware specific definitions. */
#include "AT91R40008.h"
#include "pio.h"
#include "aic.h"

#define partstNUM_LEDS			( 8 )
#define partstALL_OUTPUTS_OFF	( ( unsigned long ) ~(0xFFFFFFFF << partstNUM_LEDS) )

static unsigned long ulLEDReg;

/*-----------------------------------------------------------
 * Simple parallel port IO routines.
 *-----------------------------------------------------------*/

static void SetLeds (unsigned int leds)
{
unsigned long ulPIOSetReg, ulPIOClearReg;

	/* LEDs are grouped in different port bits: P3-P6 and P16-P19.
	A port bit set to '0' turns an LED on, '1' turns it off. */

	ulPIOSetReg = ( (leds & 0xF) << 16 ) | ( (leds & 0xF0) >> 1 );
	ulPIOClearReg = (~ulPIOSetReg) & 0x000F0078;

	AT91C_BASE_PIO->PIO_SODR = ulPIOSetReg;
	AT91C_BASE_PIO->PIO_CODR = ulPIOClearReg;
}
/*-----------------------------------------------------------*/

void vParTestInitialise( void )
{
	/* This is performed from main() as the io bits are shared with other setup
	functions.  Ensure the outputs are off to start. */
	ulLEDReg = partstALL_OUTPUTS_OFF;  

	/* Enable clock to PIO... */
	AT91C_BASE_PS->PS_PCER = AT91C_PS_PIO;

	/* Enable all 8 LEDs and the four switches to be controlled by PIO... */
	AT91C_BASE_PIO->PIO_PER = P3 | P4 | P5 | P6 | P16 | P17 | P18 | P19 | P1 | P2 | P9 | P12;

	/* Configure all LED PIO lines for output... */
	AT91C_BASE_PIO->PIO_OER = P3 | P4 | P5 | P6 | P16 | P17 | P18 | P19;

	/* Configure all switch PIO lines for input... */
	AT91C_BASE_PIO->PIO_ODR = P1 | P2 | P9 | P12;

	/* Set initial state of LEDs. */
	SetLeds( ulLEDReg );
}
/*-----------------------------------------------------------*/

void vParTestSetLED( unsigned portBASE_TYPE uxLED, signed portBASE_TYPE xValue )
{
	/* Switch an LED on or off as requested. */
	if (uxLED < partstNUM_LEDS)
	{
		if( xValue )
		{
			ulLEDReg &= ~(1 << uxLED);
		}
		else
		{
			ulLEDReg |= (1 << uxLED);
		}

		SetLeds( ulLEDReg );
	}
}
/*-----------------------------------------------------------*/

void vParTestToggleLED( unsigned portBASE_TYPE uxLED )
{
	/* Toggle the state of the requested LED. */
	if (uxLED < partstNUM_LEDS)
	{
		ulLEDReg ^= ( 1 << uxLED );
		SetLeds( ulLEDReg );
	}
}

