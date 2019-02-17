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
 * Simple GPIO (parallel port) IO routines.
 *-----------------------------------------------------------*/

/* Kernel includes. */
#include "FreeRTOS.h"
#include "task.h"

/* Standard demo include. */
#include "partest.h"

/* Freescale includes. */
#include "common.h"

/* Only the LEDs on one of the two seven segment displays are used. */
#define partstMAX_LEDS		4

/* The bits used to control the LEDs on the TWR-K60N512. */
const unsigned long ulLEDs[ partstMAX_LEDS ] = { ( 1UL << 10UL ), ( 1UL << 29UL ), ( 1UL << 28UL ), ( 1UL << 11UL ) };

/*-----------------------------------------------------------*/

void vParTestInitialise( void )
{
	/* Set PTA10, PTA11, PTA28, and PTA29 (connected to LED's) for GPIO
	functionality. */
	PORTA_PCR10 = ( 0 | PORT_PCR_MUX( 1 ) );
	PORTA_PCR11 = ( 0 | PORT_PCR_MUX( 1 ) );
	PORTA_PCR28 = ( 0 | PORT_PCR_MUX( 1 ) );
	PORTA_PCR29 = ( 0 | PORT_PCR_MUX( 1 ) );
	
	/* Change PTA10, PTA11, PTA28, PTA29 to outputs. */
	GPIOA_PDDR=GPIO_PDDR_PDD( ulLEDs[ 0 ] | ulLEDs[ 1 ] | ulLEDs[ 2 ] | ulLEDs[ 3 ] );	

	/* Start with LEDs off. */
	GPIOA_PTOR = ~0U;	
}
/*-----------------------------------------------------------*/

void vParTestSetLED( unsigned long ulLED, signed portBASE_TYPE xValue )
{
	if( ulLED < partstMAX_LEDS )
	{
		if( xValue == pdTRUE )
		{
			GPIOA_PCOR = ulLEDs[ ulLED ];
		}
		else
		{
			GPIOA_PSOR = ulLEDs[ ulLED ];
		}
	}
}
/*-----------------------------------------------------------*/

void vParTestToggleLED( unsigned long ulLED )
{
	if( ulLED < partstMAX_LEDS )
	{
		GPIOA_PTOR = ulLEDs[ ulLED ];
	}
}
/*-----------------------------------------------------------*/

long lParTestGetLEDState( unsigned long ulLED )
{
long lReturn = pdFALSE;

	if( ulLED < partstMAX_LEDS )
	{
		lReturn = GPIOA_PDOR & ulLEDs[ ulLED ];
		
		if( lReturn == 0 )
		{
			lReturn = pdTRUE;
		}
		else
		{
			lReturn = pdFALSE;
		}
	}

	return lReturn;
}
