/*
 * FreeRTOS Kernel V10.0.1
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

/*-----------------------------------------------------------
 * Simple IO routines to control the LEDs.
 *-----------------------------------------------------------*/

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "task.h"

/* Demo includes. */
#include "partest.h"

#define partestNUM_LEDS ( 6 )
#define partestALL_LEDS ( usLEDMasks[ 0 ] | usLEDMasks[ 1 ] | usLEDMasks[ 2 ] | usLEDMasks[ 3 ] | usLEDMasks[ 4 ] | usLEDMasks[ 5 ] )

static const unsigned short usLEDMasks[ partestNUM_LEDS ] = { ( 1 << 9 ), ( 1 << 11 ), ( 1 << 12 ), ( 1 << 13 ), ( 1 << 14 ), ( 1 << 15 ) };
/*-----------------------------------------------------------*/

void vParTestInitialise( void )
{
	/* Select port functions for PE9 to PE15. */
	PFC.PECRL3.WORD &= ( unsigned short ) ~partestALL_LEDS;

	/* Turn all LEDs off. */
	PE.DR.WORD &= ( unsigned short ) ~partestALL_LEDS;
	
	/* Set all LEDs to output. */
	PFC.PEIORL.WORD |= ( unsigned short ) partestALL_LEDS;
}
/*-----------------------------------------------------------*/

void vParTestSetLED( unsigned portBASE_TYPE uxLED, signed portBASE_TYPE xValue )
{
	if( uxLED < partestNUM_LEDS )
	{
		if( xValue )
		{
			/* Turn the LED on. */
			taskENTER_CRITICAL();
			{
				PE.DR.WORD |= usLEDMasks[ uxLED ];
			}
			taskEXIT_CRITICAL();
		}
		else
		{
			/* Turn the LED off. */
			taskENTER_CRITICAL();
			{
				PE.DR.WORD &= ( unsigned short ) ~usLEDMasks[ uxLED ];
			}
			taskEXIT_CRITICAL();
		}
	}
}
/*-----------------------------------------------------------*/

void vParTestToggleLED( unsigned portBASE_TYPE uxLED )
{
	if( uxLED < partestNUM_LEDS )
	{
		taskENTER_CRITICAL();
		{
			if( ( PE.DR.WORD & usLEDMasks[ uxLED ] ) != 0x00 )
			{
				PE.DR.WORD &= ( unsigned short ) ~usLEDMasks[ uxLED ];
			}
			else
			{
				PE.DR.WORD |= usLEDMasks[ uxLED ];
			}
		}
		taskEXIT_CRITICAL();
	}
}
/*-----------------------------------------------------------*/
							
long lParTestGetLEDState( void )
{
	/* Returns the state of the fifth LED. */
	return !( PE.DR.WORD & usLEDMasks[ 4 ] );
}
/*-----------------------------------------------------------*/




							