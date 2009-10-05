/*
    FreeRTOS V6.0.0 - Copyright (C) 2009 Real Time Engineers Ltd.

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it    under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation and modified by the FreeRTOS exception.
    **NOTE** The exception to the GPL is included to allow you to distribute a
    combined work that includes FreeRTOS without being obliged to provide the
    source code for proprietary components outside of the FreeRTOS kernel.
    Alternative commercial license and support terms are also available upon
    request.  See the licensing section of http://www.FreeRTOS.org for full
    license details.

    FreeRTOS is distributed in the hope that it will be useful,    but WITHOUT
    ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
    FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
    more details.

    You should have received a copy of the GNU General Public License along
    with FreeRTOS; if not, write to the Free Software Foundation, Inc., 59
    Temple Place, Suite 330, Boston, MA  02111-1307  USA.


    ***************************************************************************
    *                                                                         *
    * The FreeRTOS eBook and reference manual are available to purchase for a *
    * small fee. Help yourself get started quickly while also helping the     *
    * FreeRTOS project! See http://www.FreeRTOS.org/Documentation for details *
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

/*-----------------------------------------------------------
 * Simple parallel port IO routines.
 *-----------------------------------------------------------*/

#define partstLED1_OUTPUT		( 1 << 25 )
#define partstLED2_OUTPUT		( 1 << 4 )

void vParTestInitialise( void )
{
	/* Set LEDs to output. */
    GPIO1->FIODIR = partstLED1_OUTPUT;
	GPIO0->FIODIR = partstLED2_OUTPUT;

	/* Start with LED off. */
    GPIO1->FIOSET = partstLED1_OUTPUT;
	GPIO0->FIOSET = partstLED2_OUTPUT;
}
/*-----------------------------------------------------------*/

void vParTestSetLED( unsigned long ulLEDIn, signed long xValue )
{
	/* Used to set and clear LEDs on FIO2. */

	if( ulLEDIn == 0 )
	{
		/* Set of clear the output. */
		if( xValue )
		{
			GPIO1->FIOCLR = partstLED1_OUTPUT;
		}
		else
		{
			GPIO1->FIOSET = partstLED1_OUTPUT;
		}
	}
	else if( ulLEDIn == 1 )
	{
		/* Set of clear the output. */
		if( xValue )
		{
			GPIO0->FIOCLR = partstLED2_OUTPUT;
		}
		else
		{
			GPIO0->FIOSET = partstLED2_OUTPUT;
		}
	}	
}
/*-----------------------------------------------------------*/

void vParTestToggleLED( unsigned long ulLEDIn )
{
unsigned long ulCurrentState;

	/* Used to toggle LEDs on FIO2. */

	if( ulLEDIn == 0 )
	{
		/* If this bit is already set, clear it, and visa versa. */
		ulCurrentState = GPIO1->FIOPIN;
		if( ulCurrentState & partstLED1_OUTPUT )
		{
			GPIO1->FIOCLR = partstLED1_OUTPUT;
		}
		else
		{
			GPIO1->FIOSET = partstLED1_OUTPUT;
		}
	}
	else if( ulLEDIn == 1 )
	{
		/* If this bit is already set, clear it, and visa versa. */
		ulCurrentState = GPIO1->FIOPIN;
		if( ulCurrentState & partstLED1_OUTPUT )
		{
			GPIO0->FIOCLR = partstLED2_OUTPUT;
		}
		else
		{
			GPIO0->FIOSET = partstLED2_OUTPUT;
		}
	}	
}
/*-----------------------------------------------------------*/

long lParTestGetLEDState( void )
{
	if( ( GPIO0->FIOPIN & partstLED2_OUTPUT ) == 0 )
	{
		return pdFALSE;
	}
	else
	{
		return pdTRUE;
	}
}
/*-----------------------------------------------------------*/

void vParTestSetLEDState( long lState )
{
	/* Used to set and clear the LEDs on FIO1. */
	if( lState != pdFALSE )
	{
		GPIO0->FIOCLR = partstLED2_OUTPUT;
	}
	else
	{
		GPIO0->FIOSET = partstLED2_OUTPUT;
	}
}
/*-----------------------------------------------------------*/

