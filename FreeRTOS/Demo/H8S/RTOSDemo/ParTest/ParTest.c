/*
    FreeRTOS V7.2.0 - Copyright (C) 2012 Real Time Engineers Ltd.
	

    ***************************************************************************
     *                                                                       *
     *    FreeRTOS tutorial books are available in pdf and paperback.        *
     *    Complete, revised, and edited pdf reference manuals are also       *
     *    available.                                                         *
     *                                                                       *
     *    Purchasing FreeRTOS documentation will not only help you, by       *
     *    ensuring you get running as quickly as possible and with an        *
     *    in-depth knowledge of how to use FreeRTOS, it will also help       *
     *    the FreeRTOS project to continue with its mission of providing     *
     *    professional grade, cross platform, de facto standard solutions    *
     *    for microcontrollers - completely free of charge!                  *
     *                                                                       *
     *    >>> See http://www.FreeRTOS.org/Documentation for details. <<<     *
     *                                                                       *
     *    Thank you for using FreeRTOS, and thank you for your support!      *
     *                                                                       *
    ***************************************************************************


    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation AND MODIFIED BY the FreeRTOS exception.
    >>>NOTE<<< The modification to the GPL is included to allow you to
    distribute a combined work that includes FreeRTOS without being obliged to
    provide the source code for proprietary components outside of the FreeRTOS
    kernel.  FreeRTOS is distributed in the hope that it will be useful, but
    WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
    or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
    more details. You should have received a copy of the GNU General Public
    License and the FreeRTOS license exception along with FreeRTOS; if not it
    can be viewed here: http://www.freertos.org/a00114.html and also obtained
    by writing to Richard Barry, contact details for whom are available on the
    FreeRTOS WEB site.

    1 tab == 4 spaces!
    
    ***************************************************************************
     *                                                                       *
     *    Having a problem?  Start by reading the FAQ "My application does   *
     *    not run, what could be wrong?                                      *
     *                                                                       *
     *    http://www.FreeRTOS.org/FAQHelp.html                               *
     *                                                                       *
    ***************************************************************************

    
    http://www.FreeRTOS.org - Documentation, training, latest information, 
    license and contact details.
    
    http://www.FreeRTOS.org/plus - A selection of FreeRTOS ecosystem products,
    including FreeRTOS+Trace - an indispensable productivity tool.

    Real Time Engineers ltd license FreeRTOS to High Integrity Systems, who sell 
    the code with commercial support, indemnification, and middleware, under 
    the OpenRTOS brand: http://www.OpenRTOS.com.  High Integrity Systems also
    provide a safety engineered and independently SIL3 certified version under 
    the SafeRTOS brand: http://www.SafeRTOS.com.
*/

/* Scheduler include files. */
#include "FreeRTOS.h"
#include "portable.h"

/* Demo application include files. */
#include "partest.h"

/*-----------------------------------------------------------
 * Simple parallel port IO routines.
 *
 * This is for the demo application which uses port 2 for LED outputs.
 *-----------------------------------------------------------*/

/* Value for the LED to be off. */
#define partstLED_OUTPUTS		( ( unsigned char ) 0xff )

/* P2.0 is not used as an output so there are only 7 LEDs on port 2. */
#define partstMAX_LEDs			( 7 )
#define partstALL_OUTPUTS_OFF	( ( unsigned char ) 0 )

/* Maps the LED outputs used by the standard demo application files to
convenient outputs for the EDK2329.  Mainly this insures that the LED
used by the Check task is one of the on board LEDs so the demo can be
executed on an EDK without any modification. */
static inline unsigned char prvMapLED( unsigned portBASE_TYPE uxLED );

/*-----------------------------------------------------------*/

void vParTestInitialise( void )
{
	/* LED's are connected to port 2.  P2.1 and P2.2 are built onto the EDK.
	P2.3 to P2.7 are soldered onto the expansion port. */
	P2DDR = partstLED_OUTPUTS;
	P2DR = partstALL_OUTPUTS_OFF;
}
/*-----------------------------------------------------------*/

/*
 * Described at the top of the file.
 */
static inline unsigned char prvMapLED( unsigned portBASE_TYPE uxLED )
{
	switch( uxLED )
	{
		case 0	:	return ( unsigned char ) 2;
		case 1	:	return ( unsigned char ) 3;
		case 2	:	return ( unsigned char ) 4;
		case 3 	:	return ( unsigned char ) 5;
		case 4	:	return ( unsigned char ) 6;
		case 5	:	return ( unsigned char ) 0;
		case 6	:	return ( unsigned char ) 1;
		default	:	return 0;
	}
}
/*-----------------------------------------------------------*/

/*
 * Turn an LED on or off.
 */
void vParTestSetLED( unsigned portBASE_TYPE uxLED, signed portBASE_TYPE xValue )
{
unsigned char ucLED;

	if( uxLED < partstMAX_LEDs )
	{
		ucLED = prvMapLED( uxLED );

		/* Set a bit in the required LED position.  LED 0 is bit 1. */
		ucLED = ( unsigned char ) 1 << ( ucLED + 1 );

		if( xValue )
		{
			portENTER_CRITICAL();
				P2DR |= ucLED;
			portEXIT_CRITICAL();
		}
		else
		{
			portENTER_CRITICAL();
				P2DR &= ~ucLED;
			portEXIT_CRITICAL();
		}		
	}
}
/*-----------------------------------------------------------*/

void vParTestToggleLED( unsigned portBASE_TYPE uxLED )
{
unsigned char ucLED;

	if( uxLED < partstMAX_LEDs )
	{
		ucLED = prvMapLED( uxLED );

		/* Set a bit in the required LED position.  LED 0 is bit 1. */
		ucLED = ( unsigned char ) 1 << ( ucLED + 1 );

		portENTER_CRITICAL();
		{
			if( P2DR & ucLED )
			{
				P2DR &= ~ucLED;
			}
			else
			{
				P2DR |= ucLED;
			}
		}
		portEXIT_CRITICAL();
	}	
}



