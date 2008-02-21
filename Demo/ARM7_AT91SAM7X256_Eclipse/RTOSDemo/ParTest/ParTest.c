/*
	FreeRTOS.org V4.7.2 - Copyright (C) 2003-2008 Richard Barry.

	This file is part of the FreeRTOS.org distribution.

	FreeRTOS.org is free software; you can redistribute it and/or modify
	it under the terms of the GNU General Public License as published by
	the Free Software Foundation; either version 2 of the License, or
	(at your option) any later version.

	FreeRTOS.org is distributed in the hope that it will be useful,
	but WITHOUT ANY WARRANTY; without even the implied warranty of
	MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
	GNU General Public License for more details.

	You should have received a copy of the GNU General Public License
	along with FreeRTOS.org; if not, write to the Free Software
	Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA

	A special exception to the GPL can be applied should you wish to distribute
	a combined work that includes FreeRTOS.org, without being obliged to provide
	the source code for any proprietary components.  See the licensing section 
	of http://www.FreeRTOS.org for full details of how and when the exception
	can be applied.

	***************************************************************************

	Please ensure to read the configuration and relevant port sections of the 
	online documentation.

	+++ http://www.FreeRTOS.org +++
	Documentation, latest information, license and contact details.  

	+++ http://www.SafeRTOS.com +++
	A version that is certified for use in safety critical systems.

	+++ http://www.OpenRTOS.com +++
	Commercial support, development, porting, licensing and training services.

	***************************************************************************
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
const unsigned portLONG 	ulLED_Mask[ partstNUM_LEDS ]= { (1<<19), (1<<20), (1<<21), (1<<22) };


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

