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

/* FreeRTOS.org includes. */
#include "FreeRTOS.h"

/* Demo application includes. */
#include "partest.h"

#define partstFIRST_IO			( ( unsigned long ) 0x04 )
#define partstFIO2_BITS			( ( unsigned long ) 0x0000007C )
#define partstFIO1_BITS			( ( unsigned long ) 0xB0000000 )
#define partstNUM_LEDS			( 5 )
#define partstALL_OUTPUTS_OFF	( ( unsigned long ) 0xff )

/*-----------------------------------------------------------
 * Simple parallel port IO routines.
 *-----------------------------------------------------------*/

void vParTestInitialise( void )
{
	/* LEDs on ports 1 and 2 to output. */
	GPIO2->FIODIR  = partstFIO2_BITS;
    GPIO1->FIODIR  = partstFIO1_BITS;

	/* Start will all LEDs off. */
    GPIO2->FIOCLR = partstFIO2_BITS;
    GPIO1->FIOCLR = partstFIO1_BITS;
}
/*-----------------------------------------------------------*/

void vParTestSetLED( unsigned long ulLEDIn, signed long xValue )
{
unsigned long ulLED = partstFIRST_IO;

	/* Used to set and clear LEDs on FIO2. */

	if( ulLEDIn < partstNUM_LEDS )
	{
		/* Rotate to the wanted bit of port */
		ulLED <<= ( unsigned long ) ulLEDIn;

		/* Set of clear the output. */
		if( xValue )
		{
			GPIO2->FIOCLR = ulLED;
		}
		else
		{
			GPIO2->FIOSET = ulLED;
		}
	}
}
/*-----------------------------------------------------------*/

void vParTestToggleLED( unsigned long ulLEDIn )
{
unsigned long ulLED = partstFIRST_IO, ulCurrentState;

	/* Used to toggle LEDs on FIO2. */

	if( ulLEDIn < partstNUM_LEDS )
	{
		/* Rotate to the wanted bit of port 0.  Only P10 to P13 have an LED
		attached. */
		ulLED <<= ( unsigned long ) ulLEDIn;

		/* If this bit is already set, clear it, and visa versa. */
		ulCurrentState = GPIO2->FIOPIN;
		if( ulCurrentState & ulLED )
		{
			GPIO2->FIOCLR = ulLED;
		}
		else
		{
			GPIO2->FIOSET = ulLED;
		}
	}
}
/*-----------------------------------------------------------*/

long lParTestGetLEDState( void )
{
	/* Returns the state of the LEDs on FIO1. */
	if( ( GPIO1->FIOPIN & partstFIO1_BITS ) != 0 )
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
		GPIO1->FIOSET = partstFIO1_BITS;
	}
	else
	{
		GPIO1->FIOCLR = partstFIO1_BITS;
	}
}
/*-----------------------------------------------------------*/

