/*
    FreeRTOS V7.0.2 - Copyright (C) 2011 Real Time Engineers Ltd.
	

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

    http://www.FreeRTOS.org - Documentation, latest information, license and
    contact details.

    http://www.SafeRTOS.com - A version that is certified for use in safety
    critical systems.

    http://www.OpenRTOS.com - Commercial support, development, porting,
    licensing and training services.
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

