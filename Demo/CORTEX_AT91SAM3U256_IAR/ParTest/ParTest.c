/*
    FreeRTOS V6.0.2 - Copyright (C) 2010 Real Time Engineers Ltd.

    ***************************************************************************
    *                                                                         *
    * If you are:                                                             *
    *                                                                         *
    *    + New to FreeRTOS,                                                   *
    *    + Wanting to learn FreeRTOS or multitasking in general quickly       *
    *    + Looking for basic training,                                        *
    *    + Wanting to improve your FreeRTOS skills and productivity           *
    *                                                                         *
    * then take a look at the FreeRTOS eBook                                  *
    *                                                                         *
    *        "Using the FreeRTOS Real Time Kernel - a Practical Guide"        *
    *                  http://www.FreeRTOS.org/Documentation                  *
    *                                                                         *
    * A pdf reference manual is also available.  Both are usually delivered   *
    * to your inbox within 20 minutes to two hours when purchased between 8am *
    * and 8pm GMT (although please allow up to 24 hours in case of            *
    * exceptional circumstances).  Thank you for your support!                *
    *                                                                         *
    ***************************************************************************

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation AND MODIFIED BY the FreeRTOS exception.
    ***NOTE*** The exception to the GPL is included to allow you to distribute
    a combined work that includes FreeRTOS without being obliged to provide the
    source code for proprietary components outside of the FreeRTOS kernel.
    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT
    ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
    FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
    more details. You should have received a copy of the GNU General Public 
    License and the FreeRTOS license exception along with FreeRTOS; if not it 
    can be viewed here: http://www.freertos.org/a00114.html and also obtained 
    by writing to Richard Barry, contact details for whom are available on the
    FreeRTOS WEB site.

    1 tab == 4 spaces!

    http://www.FreeRTOS.org - Documentation, latest information, license and
    contact details.

    http://www.SafeRTOS.com - A version that is certified for use in safety
    critical systems.

    http://www.OpenRTOS.com - Commercial support, development, porting,
    licensing and training services.
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
#include <board.h>
#include <pio/pio.h>

#define partestNUM_LEDS ( sizeof( xLEDPins ) / sizeof( Pin ) )

static const Pin xLEDPins[] = { PINS_LEDS };

/*-----------------------------------------------------------*/

void vParTestInitialise( void )
{
long l;

	for( l = 0; l < partestNUM_LEDS; l++ )
	{
		PIO_Configure( &( xLEDPins[ l ] ), pdTRUE );
	}
}
/*-----------------------------------------------------------*/

void vParTestSetLED( unsigned portBASE_TYPE uxLED, signed portBASE_TYPE xValue )
{
	if( uxLED < partestNUM_LEDS )
	{
		if( xValue )
		{
			/* Turn the LED on. */
			portENTER_CRITICAL();
			{
				if( xLEDPins[ uxLED ].type == PIO_OUTPUT_0 )
				{			
					PIO_Set( &( xLEDPins[ uxLED ]) );
				}
				else
				{			
					PIO_Clear( &( xLEDPins[ uxLED ] ) );
				}
			}
			portEXIT_CRITICAL();
		}
		else
		{
			/* Turn the LED off. */
			portENTER_CRITICAL();
			{
				if( xLEDPins[ uxLED ].type == PIO_OUTPUT_0 )
				{			
					PIO_Clear( &( xLEDPins[ uxLED ] ) );
				}
				else
				{			
					PIO_Set( &( xLEDPins[ uxLED ] ) );
				}
			}
			portEXIT_CRITICAL();
		}
	}
}
/*-----------------------------------------------------------*/

void vParTestToggleLED( unsigned portBASE_TYPE uxLED )
{
	if( uxLED < partestNUM_LEDS )
	{
		if( PIO_GetOutputDataStatus( &( xLEDPins[ uxLED ] ) ) )
		{		
			PIO_Clear( &( xLEDPins[ uxLED ] ) );
		}
		else
		{		
			PIO_Set( &( xLEDPins[ uxLED ] ) );
		}		
	}
}
							


