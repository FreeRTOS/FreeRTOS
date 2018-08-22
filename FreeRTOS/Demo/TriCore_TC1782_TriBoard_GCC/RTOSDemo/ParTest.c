/*
 * FreeRTOS Kernel V10.1.0
 * Copyright (C) 2018 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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

/* Scheduler Includes. */
#include "FreeRTOS.h"

/* Demo Includes. */
#include "partest.h"

/* Hardware specific includes. */
#include <tc1782.h>

/*---------------------------------------------------------------------------*/

void vParTestInitialise( void )
{
	/* The TriBoard TC1782 v2.1 has 8 LEDs connected to GPIO5. */
	P5_IOCR0.reg = 0xC0C0C0C0UL;
	P5_IOCR4.reg = 0xC0C0C0C0UL;
	P5_PDR.reg = 0x00000000UL;
	P5_OMR.reg = 0x0000FFFFUL;
}
/*---------------------------------------------------------------------------*/

void vParTestSetLED( unsigned portBASE_TYPE uxLED, signed portBASE_TYPE xValue )
{
unsigned long ulBitPattern = 1UL << uxLED;

	if( xValue != 0 )
	{
		P5_OMR.reg = ulBitPattern;
	}
	else
	{
		P5_OMR.reg = ulBitPattern << 16UL;
	}
}
/*---------------------------------------------------------------------------*/

void vParTestToggleLED( unsigned portBASE_TYPE uxLED )
{
unsigned long ulBitPattern = 1UL << uxLED;

	P5_OMR.reg = ( ulBitPattern << 16 ) | ulBitPattern;
}
/*---------------------------------------------------------------------------*/
