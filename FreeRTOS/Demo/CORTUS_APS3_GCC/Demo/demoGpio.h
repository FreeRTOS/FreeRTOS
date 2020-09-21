/*
 * FreeRTOS Kernel V10.3.0
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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

/* Layout of pins connected to GPIO on Xilinx FPGA evaluation board 
*/

#include <machine/sfradr.h>

#ifndef DEMOGPIO_H
#define DEMOGPIO_H

typedef struct DemoBoardGpioPins
{
	/* Leds on board */
	unsigned leds:8;
	
	/* 7 segment display */
	unsigned digit:7;

	/* Decimal point */
	unsigned dp:1;

	/* Select anode for digit and decimal pt to light up */
	unsigned an:4;

	/* Unused */
	unsigned _fill:12;

} DemoBoardGpioPins;

typedef struct DemoBoardGpio
{
	volatile DemoBoardGpioPins out;
	volatile DemoBoardGpioPins in;
	volatile DemoBoardGpioPins dir;
	volatile unsigned _fill;
} DemoBoardGpio;

#ifdef SFRADR_GPIO1
#define gpio ((DemoBoardGpio*)SFRADR_GPIO1)
#endif

#endif

// Local Variables:
// tab-width:4
// End:
