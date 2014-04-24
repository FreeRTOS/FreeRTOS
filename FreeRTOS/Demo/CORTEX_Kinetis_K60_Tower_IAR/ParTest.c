/*
    FreeRTOS V8.0.1 - Copyright (C) 2014 Real Time Engineers Ltd. 
    All rights reserved

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

    >>!   NOTE: The modification to the GPL is included to allow you to     !<<
    >>!   distribute a combined work that includes FreeRTOS without being   !<<
    >>!   obliged to provide the source code for proprietary components     !<<
    >>!   outside of the FreeRTOS kernel.                                   !<<

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
 * Simple GPIO (parallel port) IO routines.
 *-----------------------------------------------------------*/

/* Kernel includes. */
#include "FreeRTOS.h"
#include "task.h"

/* Standard demo include. */
#include "partest.h"

/* Freescale includes. */
#include "common.h"

/* Only the LEDs on one of the two seven segment displays are used. */
#define partstMAX_LEDS		4

/* The bits used to control the LEDs on the TWR-K60N512. */
const unsigned long ulLEDs[ partstMAX_LEDS ] = { ( 1UL << 10UL ), ( 1UL << 29UL ), ( 1UL << 28UL ), ( 1UL << 11UL ) };

/*-----------------------------------------------------------*/

void vParTestInitialise( void )
{
	/* Set PTA10, PTA11, PTA28, and PTA29 (connected to LED's) for GPIO
	functionality. */
	PORTA_PCR10 = ( 0 | PORT_PCR_MUX( 1 ) );
	PORTA_PCR11 = ( 0 | PORT_PCR_MUX( 1 ) );
	PORTA_PCR28 = ( 0 | PORT_PCR_MUX( 1 ) );
	PORTA_PCR29 = ( 0 | PORT_PCR_MUX( 1 ) );
	
	/* Change PTA10, PTA11, PTA28, PTA29 to outputs. */
	GPIOA_PDDR=GPIO_PDDR_PDD( ulLEDs[ 0 ] | ulLEDs[ 1 ] | ulLEDs[ 2 ] | ulLEDs[ 3 ] );	

	/* Start with LEDs off. */
	GPIOA_PTOR = ~0U;	
}
/*-----------------------------------------------------------*/

void vParTestSetLED( unsigned long ulLED, signed portBASE_TYPE xValue )
{
	if( ulLED < partstMAX_LEDS )
	{
		if( xValue == pdTRUE )
		{
			GPIOA_PCOR = ulLEDs[ ulLED ];
		}
		else
		{
			GPIOA_PSOR = ulLEDs[ ulLED ];
		}
	}
}
/*-----------------------------------------------------------*/

void vParTestToggleLED( unsigned long ulLED )
{
	if( ulLED < partstMAX_LEDS )
	{
		GPIOA_PTOR = ulLEDs[ ulLED ];
	}
}
/*-----------------------------------------------------------*/

long lParTestGetLEDState( unsigned long ulLED )
{
long lReturn = pdFALSE;

	if( ulLED < partstMAX_LEDS )
	{
		lReturn = GPIOA_PDOR & ulLEDs[ ulLED ];
		
		if( lReturn == 0 )
		{
			lReturn = pdTRUE;
		}
		else
		{
			lReturn = pdFALSE;
		}
	}

	return lReturn;
}
