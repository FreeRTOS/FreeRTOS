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

/** 
 * ParTest.c controls bits (LEDs) for GCC/HCS12 version of FreeRTOS Demo
 *
 * Modified from CodeWarrior/HCS12 by Jefferson L Smith, Robotronics Inc.
 */

#include <sys/ports.h>

/* Scheduler include files. */
#include "FreeRTOS.h"
#include "portable.h"

/* Demo application include files. */
#include "partest.h"

#define LEDIO	PORTIO_8(PORT_LED)

/*-----------------------------------------------------------
 * Simple parallel port IO routines.
 *-----------------------------------------------------------*/

void vParTestSetLED( unsigned portBASE_TYPE uxLED, signed portBASE_TYPE xValue )
{
	/* This function is required as it is called from the standard demo 
	application files.  It manipulates a bit to control one LED. */
	portENTER_CRITICAL();

	if (xValue) {                       /* Is it one to be written? */
		LEDIO |= (1<<uxLED);            /* Set appropriate bit on port */
	}
	else {                             /* Is it zero to be written? */
		LEDIO &= ~(1<<uxLED);          /* Clear appropriate bit on port */
	}
	portEXIT_CRITICAL();
}
/*-----------------------------------------------------------*/

void vParTestToggleLED( unsigned portBASE_TYPE uxLED )
{
	/* This function is required as it is called from the standard demo
	application files.  It manipulates a bit to control one LED. */
	portENTER_CRITICAL();
		LEDIO ^= (1<<uxLED);           /* Invert appropriate bit on port */
	portEXIT_CRITICAL();
}

