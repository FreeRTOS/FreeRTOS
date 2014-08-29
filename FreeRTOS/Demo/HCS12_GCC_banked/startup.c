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


/*
 * startup.c
 * Author Jefferson L Smith, Robotronics Inc.
 *
 * __premain() is the startup code to init hardware and ram to execute the
 *             C application.
 *
 */

#include <sys/ports.h>
#include "cpu.h"

void ATTR_NEAR __premain (void);

void
__premain (void)
{
	// in case special mode enabled, avoid conflict on PORTE
	PEAR |= NECLK;
	// bgnd mode stops COP and RTI clocks
	COPCTL = RSBCK;
	// stops TCNT counter when debugging stops
	TSCR1 |= (1<<5);			// TFRZ
	
	// PLL
	CLKSEL = 0;				// disable PLL to configure
	// xtal 16MHz, bus 24MHz
	SYNR  = 3 - 1;
	REFDV = 2 - 1;
	while (!(CRGFLG & 0x08))    // wait for PLL LOCK
	cop_optional_reset();
	CLKSEL |= 0x80;             // use PLL

	// init switch inputs
	PERH = 0xff;				// pullups

	// outputs
#if PORT_LED==M6811_PORTB		//PORTB
	DDRB = 0xff;	// init LED
#elif PORT_LED==M6811_PORTA		//PORTA
	DDRA = 0xff;
#elif PORT_LED==M6811_PTT	//PTT
	DDRT = 0xff;
#elif PORT_LED==M6811_PTM	//PTM
	DDRM = 0xff;
#elif PORT_LED==M6811_PTP	//PTP
	DDRP = 0xff;
#elif PORT_LED==M6811_PTH	//PTH
	DDRH = 0xff;
#endif
	
}

