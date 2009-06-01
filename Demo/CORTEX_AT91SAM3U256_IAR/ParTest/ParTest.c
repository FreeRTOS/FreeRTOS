/*
	FreeRTOS.org V5.3.0 - Copyright (C) 2003-2009 Richard Barry.

	This file is part of the FreeRTOS.org distribution.

	FreeRTOS.org is free software; you can redistribute it and/or modify it
	under the terms of the GNU General Public License (version 2) as published
	by the Free Software Foundation and modified by the FreeRTOS exception.
	**NOTE** The exception to the GPL is included to allow you to distribute a
	combined work that includes FreeRTOS.org without being obliged to provide
	the source code for any proprietary components.  Alternative commercial
	license and support terms are also available upon request.  See the 
	licensing section of http://www.FreeRTOS.org for full details.

	FreeRTOS.org is distributed in the hope that it will be useful,	but WITHOUT
	ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
	FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
	more details.

	You should have received a copy of the GNU General Public License along
	with FreeRTOS.org; if not, write to the Free Software Foundation, Inc., 59
	Temple Place, Suite 330, Boston, MA  02111-1307  USA.


	***************************************************************************
	*                                                                         *
	* Get the FreeRTOS eBook!  See http://www.FreeRTOS.org/Documentation      *
	*                                                                         *
	* This is a concise, step by step, 'hands on' guide that describes both   *
	* general multitasking concepts and FreeRTOS specifics. It presents and   *
	* explains numerous examples that are written using the FreeRTOS API.     *
	* Full source code for all the examples is provided in an accompanying    *
	* .zip file.                                                              *
	*                                                                         *
	***************************************************************************

	1 tab == 4 spaces!

	Please ensure to read the configuration and relevant port sections of the
	online documentation.

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
							


