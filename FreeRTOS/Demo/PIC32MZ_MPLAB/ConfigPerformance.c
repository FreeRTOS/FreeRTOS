/*
 * FreeRTOS Kernel V10.1.1
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

/*
 * This file implements functions to access and manipulate the PIC32 hardware
 * without reliance on third party library functions that may be liable to
 * change.
 */

/* FreeRTOS includes. */
#include "FreeRTOS.h"

/* Demo includes. */
#include "ConfigPerformance.h"

#define hwUNLOCK_KEY_0					( 0xAA996655UL )
#define hwUNLOCK_KEY_1					( 0x556699AAUL )

/*-----------------------------------------------------------*/

void vHardwareConfigurePerformance( void )
{
	/* set PBCLK2 to deliver 40Mhz clock for PMP/I2C/UART/SPI. */
	SYSKEY = hwUNLOCK_KEY_0;
	SYSKEY = hwUNLOCK_KEY_1;

	/* 200MHz / 5 = 40MHz */
	PB2DIVbits.PBDIV = 0b100;

	/* Timers use clock PBCLK3, set this to 40MHz. */
	PB3DIVbits.PBDIV = 0b100;

	/* Ports use PBCLK4. */
	PB4DIVbits.PBDIV = 0b000;

	SYSKEY = 0;

	/* Disable interrupts - note taskDISABLE_INTERRUPTS() cannot be used here as
	FreeRTOS does not globally disable interrupt. */
	__builtin_disable_interrupts();
}
/*-----------------------------------------------------------*/

void vHardwareUseMultiVectoredInterrupts( void )
{
	/* Enable multi-vector interrupts. */
	_CP0_BIS_CAUSE( 0x00800000U );
	INTCONSET = _INTCON_MVEC_MASK;
	__builtin_enable_interrupts();
}




