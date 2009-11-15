/*
    FreeRTOS V6.0.1 - Copyright (C) 2009 Real Time Engineers Ltd.

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

/* Scheduler includes. */
#include "FreeRTOS.h"

/* Demo application includes. */
#include "partest.h"

/*-----------------------------------------------------------
 * Simple parallel port IO routines for the LED's.  LED's can be set, cleared
 * or toggled.
 *-----------------------------------------------------------*/

#define partstNUM_LEDS		( 4 )
#define partstALL_LEDS		( ulLED_Mask[ 0 ] | ulLED_Mask[ 1 ] | ulLED_Mask[ 2 ] | ulLED_Mask[ 3 ] )
const unsigned long 	ulLED_Mask[ partstNUM_LEDS ]= { (1<<19), (1<<20), (1<<21), (1<<22) };


void vParTestInitialise( void )
{	
	/* Configure the PIO Lines corresponding to LED1 to LED4 to be outputs. */
	AT91C_BASE_PIOB->PIO_PER = partstALL_LEDS; 
	AT91C_BASE_PIOB->PIO_OER = partstALL_LEDS; 

	/* Start with all LED's off. */
    AT91C_BASE_PIOB->PIO_SODR = partstALL_LEDS;
}
/*-----------------------------------------------------------*/

void vParTestSetLED( unsigned portBASE_TYPE uxLED, signed portBASE_TYPE xValue )
{
	if( uxLED < ( portBASE_TYPE ) partstNUM_LEDS )
	{
		if( xValue )
		{
			AT91C_BASE_PIOB->PIO_SODR = ulLED_Mask[ uxLED ];
		}
		else
		{
			AT91C_BASE_PIOB->PIO_CODR = ulLED_Mask[ uxLED ];
		}
	}
}
/*-----------------------------------------------------------*/

void vParTestToggleLED( unsigned portBASE_TYPE uxLED )
{
	if( uxLED < ( portBASE_TYPE ) partstNUM_LEDS )
	{
		if( AT91C_BASE_PIOB->PIO_PDSR & ulLED_Mask[ uxLED ] )
		{
			AT91C_BASE_PIOB->PIO_CODR = ulLED_Mask[ uxLED ];
		}
		else
		{
			AT91C_BASE_PIOB->PIO_SODR = ulLED_Mask[ uxLED ];
		}
	}
}
/*-----------------------------------------------------------*/

unsigned portBASE_TYPE uxParTestGetLED( void )
{
	/* Return the value of LED DS4 for use by the WEB server. */
	return !( AT91C_BASE_PIOB->PIO_PDSR & ulLED_Mask[ partstNUM_LEDS - 1 ] );
}

