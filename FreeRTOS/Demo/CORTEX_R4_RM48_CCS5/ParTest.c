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

/*-----------------------------------------------------------
 * Simple IO routines to control the LEDs.
 *-----------------------------------------------------------*/

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "task.h"

/* Demo includes. */
#include "partest.h"

/* Library includes. */
#include "het.h"

/* Port bits connected to LEDs. */
const unsigned long ulLEDBits[] = { 25, 18, 29, 	/* Bottom row. */
									17, 31, 0,  	/* Top row. */
									2, 5, 20, 		/* Red1, blue1, green1 */
									4, 27, 16 };	/* Red2, blue2, green2 */

/* 1 turns a white LED on, or a coloured LED off. */
const unsigned long ulOnStates[] = { 1, 1, 1,
									 1, 1, 1,
									 0, 0, 0,
									 0, 0, 0 };

const unsigned long ulNumLEDs = sizeof( ulLEDBits ) / sizeof( unsigned long );

/*-----------------------------------------------------------*/

void vParTestInitialise( void )
{
unsigned long ul;

	/* Initalise the IO ports that drive the LEDs */
	gioSetDirection( hetPORT, 0xFFFFFFFF );

	/* Turn all the LEDs off. */
	for( ul = 0; ul < ulNumLEDs; ul++ )
	{
		gioSetBit( hetPORT, ulLEDBits[ ul ], !ulOnStates[ ul ] );
	}
}
/*-----------------------------------------------------------*/

void vParTestSetLED( unsigned long ulLED, signed long xValue )
{	
	if( ulLED < ulNumLEDs )
	{
		if( xValue == pdFALSE )
		{
			xValue = !ulOnStates[ ulLED ];
		}
		else
		{
			xValue = ulOnStates[ ulLED ];
		}

		gioSetBit( hetPORT, ulLEDBits[ ulLED ], xValue );
	}
}
/*-----------------------------------------------------------*/

void vParTestToggleLED( unsigned long ulLED )
{
unsigned long ulBitState;

	if( ulLED < ulNumLEDs )
	{
		ulBitState = gioGetBit( hetPORT, ulLEDBits[ ulLED ] );
		gioSetBit( hetPORT, ulLEDBits[ ulLED ], !ulBitState );
	}
}
							


