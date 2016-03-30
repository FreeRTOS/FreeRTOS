/*
    FreeRTOS V9.0.0rc2 - Copyright (C) 2016 Real Time Engineers Ltd.
    All rights reserved

    VISIT http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation >>>> AND MODIFIED BY <<<< the FreeRTOS exception.

    ***************************************************************************
    >>!   NOTE: The modification to the GPL is included to allow you to     !<<
    >>!   distribute a combined work that includes FreeRTOS without being   !<<
    >>!   obliged to provide the source code for proprietary components     !<<
    >>!   outside of the FreeRTOS kernel.                                   !<<
    ***************************************************************************

    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT ANY
    WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
    FOR A PARTICULAR PURPOSE.  Full license text is available on the following
    link: http://www.freertos.org/a00114.html

    ***************************************************************************
     *                                                                       *
     *    FreeRTOS provides completely free yet professionally developed,    *
     *    robust, strictly quality controlled, supported, and cross          *
     *    platform software that is more than just the market leader, it     *
     *    is the industry's de facto standard.                               *
     *                                                                       *
     *    Help yourself get started quickly while simultaneously helping     *
     *    to support the FreeRTOS project by purchasing a FreeRTOS           *
     *    tutorial book, reference manual, or both:                          *
     *    http://www.FreeRTOS.org/Documentation                              *
     *                                                                       *
    ***************************************************************************

    http://www.FreeRTOS.org/FAQHelp.html - Having a problem?  Start by reading
    the FAQ page "My application does not run, what could be wrong?".  Have you
    defined configASSERT()?

    http://www.FreeRTOS.org/support - In return for receiving this top quality
    embedded software for free we request you assist our global community by
    participating in the support forum.

    http://www.FreeRTOS.org/training - Investing in training allows your team to
    be as productive as possible as early as possible.  Now you can receive
    FreeRTOS training directly from Richard Barry, CEO of Real Time Engineers
    Ltd, and the world's leading authority on the world's leading RTOS.

    http://www.FreeRTOS.org/plus - A selection of FreeRTOS ecosystem products,
    including FreeRTOS+Trace - an indispensable productivity tool, a DOS
    compatible FAT file system, and our tiny thread aware UDP/IP stack.

    http://www.FreeRTOS.org/labs - Where new FreeRTOS products go to incubate.
    Come and try FreeRTOS+TCP, our new open source TCP/IP stack for FreeRTOS.

    http://www.OpenRTOS.com - Real Time Engineers ltd. license FreeRTOS to High
    Integrity Systems ltd. to sell under the OpenRTOS brand.  Low cost OpenRTOS
    licenses offer ticketed support, indemnification and commercial middleware.

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
		/* If this bit is already set, clear it, and vice versa. */
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
		/* If this bit is already set, clear it, and vice versa. */
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

