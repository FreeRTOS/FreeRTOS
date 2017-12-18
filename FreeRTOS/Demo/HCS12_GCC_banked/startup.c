/*
 * FreeRTOS Kernel V10.0.1
 * Copyright (C) 2017 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 * http://www.FreeRTOS.org
 * http://aws.amazon.com/freertos
 *
 * 1 tab == 4 spaces!
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

