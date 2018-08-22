/*
 * FreeRTOS Kernel V10.1.0
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
 * Simple parallel port IO routines.
 *-----------------------------------------------------------*/


/* Scheduler includes. */
#include "FreeRTOS.h"
#include "task.h"

/* Demo app includes. */
#include "system.h"
#include "altera_avalon_pio_regs.h"
#include "partest.h"

/*---------------------------------------------------------------------------*/

#define partstNUM_LEDS			( 8 )

/*---------------------------------------------------------------------------*/

static unsigned long ulLedStates;

/*---------------------------------------------------------------------------*/

void vParTestInitialise( void )
{
	IOWR_ALTERA_AVALON_PIO_DIRECTION( LED_PIO_BASE, ALTERA_AVALON_PIO_DIRECTION_OUTPUT );
	ulLedStates = 0;    
}
/*-----------------------------------------------------------*/

void vParTestSetLED( unsigned portBASE_TYPE uxLED, signed portBASE_TYPE xValue )
{
	if( uxLED < partstNUM_LEDS )
	{
		taskENTER_CRITICAL();
		{
			if ( xValue > 0 )
			{
				ulLedStates |= 1 << uxLED;
			}
			else
			{
				ulLedStates &= ~( 1 << uxLED );
			}
			IOWR_ALTERA_AVALON_PIO_DATA( LED_PIO_BASE, ulLedStates );
		}
		taskEXIT_CRITICAL();
	}
}
/*-----------------------------------------------------------*/

void vParTestToggleLED( unsigned portBASE_TYPE uxLED )
{
	if( uxLED < partstNUM_LEDS )
	{
		taskENTER_CRITICAL();
		{
			vParTestSetLED( uxLED, !( ulLedStates & ( 1 << uxLED ) ) );
		}	
		taskEXIT_CRITICAL();
	}
}
/*-----------------------------------------------------------*/
