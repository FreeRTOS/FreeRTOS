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

/* Scheduler include files. */
#include "FreeRTOS.h"
#include "portable.h"

/* Demo application include files. */
#include "partest.h"

/*-----------------------------------------------------------
 * Simple parallel port IO routines.
 *
 * This is for the demo application which uses port 2 for LED outputs.
 *-----------------------------------------------------------*/

/* Value for the LED to be off. */
#define partstLED_OUTPUTS		( ( unsigned char ) 0xff )

/* P2.0 is not used as an output so there are only 7 LEDs on port 2. */
#define partstMAX_LEDs			( 7 )
#define partstALL_OUTPUTS_OFF	( ( unsigned char ) 0 )

/* Maps the LED outputs used by the standard demo application files to
convenient outputs for the EDK2329.  Mainly this insures that the LED
used by the Check task is one of the on board LEDs so the demo can be
executed on an EDK without any modification. */
static inline unsigned char prvMapLED( unsigned portBASE_TYPE uxLED );

/*-----------------------------------------------------------*/

void vParTestInitialise( void )
{
	/* LED's are connected to port 2.  P2.1 and P2.2 are built onto the EDK.
	P2.3 to P2.7 are soldered onto the expansion port. */
	P2DDR = partstLED_OUTPUTS;
	P2DR = partstALL_OUTPUTS_OFF;
}
/*-----------------------------------------------------------*/

/*
 * Described at the top of the file.
 */
static inline unsigned char prvMapLED( unsigned portBASE_TYPE uxLED )
{
	switch( uxLED )
	{
		case 0	:	return ( unsigned char ) 2;
		case 1	:	return ( unsigned char ) 3;
		case 2	:	return ( unsigned char ) 4;
		case 3 	:	return ( unsigned char ) 5;
		case 4	:	return ( unsigned char ) 6;
		case 5	:	return ( unsigned char ) 0;
		case 6	:	return ( unsigned char ) 1;
		default	:	return 0;
	}
}
/*-----------------------------------------------------------*/

/*
 * Turn an LED on or off.
 */
void vParTestSetLED( unsigned portBASE_TYPE uxLED, signed portBASE_TYPE xValue )
{
unsigned char ucLED;

	if( uxLED < partstMAX_LEDs )
	{
		ucLED = prvMapLED( uxLED );

		/* Set a bit in the required LED position.  LED 0 is bit 1. */
		ucLED = ( unsigned char ) 1 << ( ucLED + 1 );

		if( xValue )
		{
			portENTER_CRITICAL();
				P2DR |= ucLED;
			portEXIT_CRITICAL();
		}
		else
		{
			portENTER_CRITICAL();
				P2DR &= ~ucLED;
			portEXIT_CRITICAL();
		}		
	}
}
/*-----------------------------------------------------------*/

void vParTestToggleLED( unsigned portBASE_TYPE uxLED )
{
unsigned char ucLED;

	if( uxLED < partstMAX_LEDs )
	{
		ucLED = prvMapLED( uxLED );

		/* Set a bit in the required LED position.  LED 0 is bit 1. */
		ucLED = ( unsigned char ) 1 << ( ucLED + 1 );

		portENTER_CRITICAL();
		{
			if( P2DR & ucLED )
			{
				P2DR &= ~ucLED;
			}
			else
			{
				P2DR |= ucLED;
			}
		}
		portEXIT_CRITICAL();
	}	
}



