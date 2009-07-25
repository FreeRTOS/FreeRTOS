/*
	FreeRTOS V5.4.1 - Copyright (C) 2009 Real Time Engineers Ltd.

	This file is part of the FreeRTOS distribution.

	FreeRTOS is free software; you can redistribute it and/or modify it	under 
	the terms of the GNU General Public License (version 2) as published by the 
	Free Software Foundation and modified by the FreeRTOS exception.
	**NOTE** The exception to the GPL is included to allow you to distribute a
	combined work that includes FreeRTOS without being obliged to provide the 
	source code for proprietary components outside of the FreeRTOS kernel.  
	Alternative commercial license and support terms are also available upon 
	request.  See the licensing section of http://www.FreeRTOS.org for full 
	license details.

	FreeRTOS is distributed in the hope that it will be useful,	but WITHOUT
	ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
	FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
	more details.

	You should have received a copy of the GNU General Public License along
	with FreeRTOS; if not, write to the Free Software Foundation, Inc., 59
	Temple Place, Suite 330, Boston, MA  02111-1307  USA.


	***************************************************************************
	*                                                                         *
	* Looking for a quick start?  Then check out the FreeRTOS eBook!          *
	* See http://www.FreeRTOS.org/Documentation for details                   *
	*                                                                         *
	***************************************************************************

	1 tab == 4 spaces!

	Please ensure to read the configuration and relevant port sections of the
	online documentation.

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

