/*
 * FreeRTOS Kernel V10.1.1
 * Copyright (C) 2018 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 * Simple GPIO (parallel port) IO routines.
 *-----------------------------------------------------------*/

/* Kernel includes. */
#include "FreeRTOS.h"
#include "task.h"

/* Hardware includes. */
#include <XMC1200.h>

/* Standard demo include. */
#include "partest.h"

/* The port bits on which LEDs are connected. */
static const unsigned long ulLEDBits[] = 
{ 
	1UL << 0, /* P0.0 */
	1UL << 2, /* P0.2 */
	1UL << 5, /* P0.5 */
	1UL << 6, /* P0.6 */
	1UL << 7  /* P0.7 */
};

#define partstNUM_LEDS	( sizeof( ulLEDBits ) / sizeof( unsigned long ) )

/* Shift the LED bit into the correct position within the POW register to
perform the desired operation. */
#define partstON_SHIFT	( 16UL )
#define partstOFF_SHIFT	( 0UL )

/*-----------------------------------------------------------*/

void vParTestInitialise( void )
{
	/* Configure relevant port P0 to push pull output to drive LEDs. */
	
	/* P0.0 */
	PORT0->IOCR0 &= ~( ( 0xFFUL <<  0 ) );
	PORT0->IOCR0 |= ( 0x80UL <<  0 );
	vParTestSetLED( 0, pdFALSE );

	/* P0.2 */
	PORT0->IOCR0 &= ~( ( 0xFFUL << 16 ) );
	PORT0->IOCR0 |= ( 0x80UL << 16 );
	vParTestSetLED( 1, pdFALSE );

	/* P0.5 */
	PORT0->IOCR4 &= ~( ( 0xFFUL << 8 ) );
	PORT0->IOCR4 |= ( 0x80UL << 8 );
	vParTestSetLED( 2, pdFALSE );

	/* P0.6 */
	PORT0->IOCR4 &= ~( ( 0xFFUL << 16 ) );
	PORT0->IOCR4 |= ( 0x80UL << 16 );
	vParTestSetLED( 3, pdFALSE );

	/* P0.7 */
	PORT0->IOCR4 &= ~( ( 0xFFUL << 24 ) );
	PORT0->IOCR4 |= ( 0x80UL << 24 );
	vParTestSetLED( 4, pdFALSE );
}
/*-----------------------------------------------------------*/

void vParTestSetLED( unsigned long ulLED, signed portBASE_TYPE xValue )
{
	if( ulLED < partstNUM_LEDS )
	{
		if( xValue == pdTRUE )
		{
			/* Turn the LED on. */			
			PORT0->OMR = ( ulLEDBits[ ulLED ] << partstON_SHIFT );
		}
		else
		{
			/* Turn the LED off. */			
			PORT0->OMR = ( ulLEDBits[ ulLED ] << partstOFF_SHIFT );
		}
	}
}
/*-----------------------------------------------------------*/

void vParTestToggleLED( unsigned long ulLED )
{
	if( ulLED < partstNUM_LEDS )
	{
		/* Setting both the ON and OFF bits simultaneously results in the bit
		being toggled. */
		PORT0->OMR = ( ulLEDBits[ ulLED ] << partstON_SHIFT ) | ( ulLEDBits[ ulLED ] << partstOFF_SHIFT );
	}
}
/*-----------------------------------------------------------*/

