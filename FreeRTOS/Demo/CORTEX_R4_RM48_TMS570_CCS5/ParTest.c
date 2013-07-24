/*
    FreeRTOS V7.5.2 - Copyright (C) 2013 Real Time Engineers Ltd.

    VISIT http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

    ***************************************************************************
     *                                                                       *
     *    FreeRTOS provides completely free yet professionally developed,    *
     *    robust, strictly quality controlled, supported, and cross          *
     *    platform software that has become a de facto standard.             *
     *                                                                       *
     *    Help yourself get started quickly and support the FreeRTOS         *
     *    project by purchasing a FreeRTOS tutorial book, reference          *
     *    manual, or both from: http://www.FreeRTOS.org/Documentation        *
     *                                                                       *
     *    Thank you!                                                         *
     *                                                                       *
    ***************************************************************************

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation >>!AND MODIFIED BY!<< the FreeRTOS exception.

    >>! NOTE: The modification to the GPL is included to allow you to distribute
    >>! a combined work that includes FreeRTOS without being obliged to provide
    >>! the source code for proprietary components outside of the FreeRTOS
    >>! kernel.

    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT ANY
    WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
    FOR A PARTICULAR PURPOSE.  Full license text is available from the following
    link: http://www.freertos.org/a00114.html

    1 tab == 4 spaces!

    ***************************************************************************
     *                                                                       *
     *    Having a problem?  Start by reading the FAQ "My application does   *
     *    not run, what could be wrong?"                                     *
     *                                                                       *
     *    http://www.FreeRTOS.org/FAQHelp.html                               *
     *                                                                       *
    ***************************************************************************

    http://www.FreeRTOS.org - Documentation, books, training, latest versions,
    license and Real Time Engineers Ltd. contact details.

    http://www.FreeRTOS.org/plus - A selection of FreeRTOS ecosystem products,
    including FreeRTOS+Trace - an indispensable productivity tool, a DOS
    compatible FAT file system, and our tiny thread aware UDP/IP stack.

    http://www.OpenRTOS.com - Real Time Engineers ltd license FreeRTOS to High
    Integrity Systems to sell under the OpenRTOS brand.  Low cost OpenRTOS
    licenses offer ticketed support, indemnification and middleware.

    http://www.SafeRTOS.com - High Integrity Systems also provide a safety
    engineered and independently SIL3 certified version for use in safety and
    mission critical applications that require provable dependability.

    1 tab == 4 spaces!
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
							


