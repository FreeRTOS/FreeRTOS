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

/*-----------------------------------------------------------
 * Simple GPIO (parallel port) IO routines.
 *-----------------------------------------------------------*/

/* Kernel includes. */
#include "FreeRTOS.h"
#include "task.h"

/* Hardware includes. */
#include <XMC1300.h>

/* Standard demo include. */
#include "partest.h"

/* The port bits on which LEDs are connected. */
static const unsigned long ulLEDBits[] = 
{ 
	1UL << 0, /* P0.0 */
	1UL << 1, /* P0.1 */
	1UL << 6, /* P0.6 */
	1UL << 7, /* P0.7 */
	1UL << 8  /* P0.8 */
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
	
	/* P0.0 */
	PORT0->IOCR0 &= ~( ( 0xFFUL <<  0 ) );
	PORT0->IOCR0 |= ( 0x80UL <<  0 );
	vParTestSetLED( 0, pdFALSE );

	/* P0.1 */
	PORT0->IOCR0 &= ~( ( 0xFFUL << 8 ) );
	PORT0->IOCR0 |= ( 0x80UL << 8 );
	vParTestSetLED( 1, pdFALSE );

	/* P0.6 */
	PORT0->IOCR4 &= ~( ( 0xFFUL << 16 ) );
	PORT0->IOCR4 |= ( 0x80UL << 16 );
	vParTestSetLED( 2, pdFALSE );

	/* P0.7 */
	PORT0->IOCR4 &= ~( ( 0xFFUL << 24 ) );
	PORT0->IOCR4 |= ( 0x80UL << 24 );
	vParTestSetLED( 4, pdFALSE );

	/* P0.8 */
	PORT0->IOCR8 &= ~( ( 0xFFUL << 0 ) );
	PORT0->IOCR8 |= ( 0x80UL << 0 );
	vParTestSetLED( 3, pdFALSE );
}
/*-----------------------------------------------------------*/

void vParTestSetLED( unsigned long ulLED, signed portBASE_TYPE xValue )
{
	if( ulLED < partstNUM_LEDS )
	{
		if( xValue == pdTRUE )
		{
			/* Turn the LED on. */			
			PORT0->OMR = ( ulLEDBits[ ulLED ] << partstON_SHIFT );
		}
		else
		{
			/* Turn the LED off. */			
			PORT0->OMR = ( ulLEDBits[ ulLED ] << partstOFF_SHIFT );
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
		PORT0->OMR = ( ulLEDBits[ ulLED ] << partstON_SHIFT ) | ( ulLEDBits[ ulLED ] << partstOFF_SHIFT );
	}
}
/*-----------------------------------------------------------*/

