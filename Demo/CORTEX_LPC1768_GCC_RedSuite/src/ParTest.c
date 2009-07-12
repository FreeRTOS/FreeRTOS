/*
	FreeRTOS.org V5.4.0 - Copyright (C) 2003-2009 Richard Barry.

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

/* FreeRTOS.org includes. */
#include "FreeRTOS.h"

/* Demo application includes. */
#include "partest.h"

#define LED_2 ( 1UL << 24UL )
#define LED_3 ( 1UL << 25UL )
#define LED_4 ( 1UL << 28UL )
#define LED_5 ( 1UL << 29UL )

#define partstFIO1_BITS			( LED_2 | LED_3 | LED_4 | LED_5 )
#define partstNUM_LEDS			( 4 )

static unsigned long ulLEDs[] = { LED_3, LED_2, LED_5, LED_4 };

/*-----------------------------------------------------------
 * Simple parallel port IO routines.
 *-----------------------------------------------------------*/

void vParTestInitialise( void )
{
	/* LEDs on port 1. */
	GPIO1->FIODIR  = partstFIO1_BITS;
	
	/* Start will all LEDs off. */
	GPIO1->FIOCLR = partstFIO1_BITS;
}
/*-----------------------------------------------------------*/

void vParTestSetLED( unsigned portBASE_TYPE uxLED, signed portBASE_TYPE xValue )
{
	if( uxLED < partstNUM_LEDS )
	{
		/* Set of clear the output. */
		if( xValue )
		{
			GPIO1->FIOCLR = ulLEDs[ uxLED ];
		}
		else
		{
			GPIO1->FIOSET = ulLEDs[ uxLED ];
		}
	}
}
/*-----------------------------------------------------------*/

void vParTestToggleLED( unsigned portBASE_TYPE uxLED )
{
	if( uxLED < partstNUM_LEDS )
	{
		if( GPIO1->FIOPIN & ulLEDs[ uxLED ] )
		{
			GPIO1->FIOCLR = ulLEDs[ uxLED ];
		}
		else
		{
			GPIO1->FIOSET = ulLEDs[ uxLED ];
		}
	}
}
/*-----------------------------------------------------------*/

unsigned portBASE_TYPE uxParTextGetLED( unsigned portBASE_TYPE uxLED )
{
	if( uxLED < partstNUM_LEDS )
	{
		return ( GPIO1->FIOPIN & ulLEDs[ uxLED ] );
	}
	else
	{
		return 0;
	}
}
/*-----------------------------------------------------------*/







