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
		ulCurrentState = GPIO0->FIOPIN;
		if( ulCurrentState & partstLED2_OUTPUT )
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

