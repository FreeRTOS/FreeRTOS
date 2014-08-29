/*
    FreeRTOS V8.1.1 - Copyright (C) 2014 Real Time Engineers Ltd. 
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

/* Hardware includes. */
#include <XMC1100.h>

/* Standard demo include. */
#include "partest.h"

/* The port bits on which LEDs are connected. */
static const unsigned long ulLEDPorts[] =
{
	0, /* P0.5 */
	0, /* P0.6 */
	1, /* P1.2 */
	1, /* P1.3 */
	1, /* P1.4 */
	1  /* P1.5 */
};

/* The port bits on which LEDs are connected. */
static const unsigned long ulLEDBits[] =
{
	1 << 5, /* P0.5 */
	1 << 6, /* P0.6 */
	1 << 2, /* P1.2 */
	1 << 3, /* P1.3 */
	1 << 4, /* P1.4 */
	1 << 5  /* P1.5 */
};

#define partstNUM_LEDS	( sizeof( ulLEDBits ) / sizeof( unsigned long ) )

/* Shift the LED bit into the correct position within the POW register to
perform the desired operation. */
#define partstON_SHIFT	( 16UL )
#define partstOFF_SHIFT	( 0UL )

/*-----------------------------------------------------------*/

void vParTestInitialise( void )
{
	/* Configure relevant port P0 to push pull output to drive LEDs. */

	/* P0.5 */
	PORT0->IOCR4 &= ~( ( 0xFFUL <<  8 ) );
	PORT0->IOCR4 |= ( 0x80UL <<  8 );
	vParTestSetLED( 0, pdFALSE );

	/* P0.6 */
	PORT0->IOCR4 &= ~( ( 0xFFUL << 16 ) );
	PORT0->IOCR4 |= ( 0x80UL << 16 );
	vParTestSetLED( 1, pdFALSE );

	/* P1.2 */
	PORT1->IOCR0 &= ~( ( 0xFFUL << 16 ) );
	PORT1->IOCR0 |= ( 0x80UL << 16 );
	vParTestSetLED( 2, pdFALSE );

	/* P1.3 */
	PORT1->IOCR0 &= ~( ( 0xFFUL << 24 ) );
	PORT1->IOCR0 |= ( 0x80UL << 24 );
	vParTestSetLED( 3, pdFALSE );

	/* P1.4 */
	PORT1->IOCR4 &= ~( ( 0xFFUL << 0 ) );
	PORT1->IOCR4 |= ( 0x80UL << 0 );
	vParTestSetLED( 4, pdFALSE );

	/* P1.5 */
	PORT1->IOCR4 &= ~( ( 0xFFUL << 8 ) );
	PORT1->IOCR4 |= ( 0x80UL << 8 );
	vParTestSetLED( 5, pdFALSE );
}
/*-----------------------------------------------------------*/

void vParTestSetLED( unsigned long ulLED, signed portBASE_TYPE xValue )
{
	if( ulLED < partstNUM_LEDS )
	{
		if( xValue == pdTRUE )
		{
			/* Turn the LED on. */
			if( ulLEDPorts[ ulLED ] == 0x00 )
			{
				PORT0->OMR = ( ulLEDBits[ ulLED ] << partstON_SHIFT );
			}
			else
			{
				PORT1->OMR = ( ulLEDBits[ ulLED ] << partstON_SHIFT );
			}
		}
		else
		{
			/* Turn the LED off. */
			if( ulLEDPorts[ ulLED ] == 0x00 )
			{
				PORT0->OMR = ( ulLEDBits[ ulLED ] << partstOFF_SHIFT );
			}
			else
			{
				PORT1->OMR = ( ulLEDBits[ ulLED ] << partstOFF_SHIFT );
			}
		}
	}
}
/*-----------------------------------------------------------*/

void vParTestToggleLED( unsigned long ulLED )
{
	if( ulLED < partstNUM_LEDS )
	{
		/* Setting both the ON and OFF bits simultaneously results in the bit
		being toggled. */
		if( ulLEDPorts[ ulLED ] == 0x00 )
		{
			PORT0->OMR = ( ulLEDBits[ ulLED ] << partstON_SHIFT ) | ( ulLEDBits[ ulLED ] << partstOFF_SHIFT );
		}
		else
		{
			PORT1->OMR = ( ulLEDBits[ ulLED ] << partstON_SHIFT ) | ( ulLEDBits[ ulLED ] << partstOFF_SHIFT );
		}
	}
}
/*-----------------------------------------------------------*/

