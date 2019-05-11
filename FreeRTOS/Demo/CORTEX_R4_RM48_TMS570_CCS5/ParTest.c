/*
 * FreeRTOS Kernel V10.2.1
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
 * Simple IO routines to control the LEDs.
 *-----------------------------------------------------------*/

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "task.h"

/* Demo includes. */
#include "partest.h"

/* Library includes. */
#include "het.h"

/* Port bits connected to LEDs. */
const unsigned long ulLEDBits[] = { 25, 18, 29, 	/* Bottom row. */
									17, 31, 0,  	/* Top row. */
									2, 5, 20, 		/* Red1, blue1, green1 */
									4, 27, 16 };	/* Red2, blue2, green2 */

/* 1 turns a white LED on, or a coloured LED off. */
const unsigned long ulOnStates[] = { 1, 1, 1,
									 1, 1, 1,
									 0, 0, 0,
									 0, 0, 0 };

const unsigned long ulNumLEDs = sizeof( ulLEDBits ) / sizeof( unsigned long );

/*-----------------------------------------------------------*/

void vParTestInitialise( void )
{
unsigned long ul;

	/* Initalise the IO ports that drive the LEDs */
	gioSetDirection( hetPORT, 0xFFFFFFFF );

	/* Turn all the LEDs off. */
	for( ul = 0; ul < ulNumLEDs; ul++ )
	{
		gioSetBit( hetPORT, ulLEDBits[ ul ], !ulOnStates[ ul ] );
	}
}
/*-----------------------------------------------------------*/

void vParTestSetLED( unsigned long ulLED, signed long xValue )
{	
	if( ulLED < ulNumLEDs )
	{
		if( xValue == pdFALSE )
		{
			xValue = !ulOnStates[ ulLED ];
		}
		else
		{
			xValue = ulOnStates[ ulLED ];
		}

		gioSetBit( hetPORT, ulLEDBits[ ulLED ], xValue );
	}
}
/*-----------------------------------------------------------*/

void vParTestToggleLED( unsigned long ulLED )
{
unsigned long ulBitState;

	if( ulLED < ulNumLEDs )
	{
		ulBitState = gioGetBit( hetPORT, ulLEDBits[ ulLED ] );
		gioSetBit( hetPORT, ulLEDBits[ ulLED ], !ulBitState );
	}
}
							


