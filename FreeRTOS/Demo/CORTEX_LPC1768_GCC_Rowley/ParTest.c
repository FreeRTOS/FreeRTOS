/*
    FreeRTOS V7.5.1 - Copyright (C) 2013 Real Time Engineers Ltd.

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

