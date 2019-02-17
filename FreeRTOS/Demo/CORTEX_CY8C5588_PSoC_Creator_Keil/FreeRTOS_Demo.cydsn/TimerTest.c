/*
 * FreeRTOS Kernel V10.2.0
 * Copyright (C) 2019 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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

/* High speed timer test as described in main.c. */
#include <device.h>

/* Scheduler includes. */
#include "FreeRTOS.h"

/* The set frequency of the interrupt.  Deviations from this are measured as
the jitter. */
#define timerINTERRUPT_FREQUENCY		( ( unsigned short ) 20000 )

/* The expected time between each of the timer interrupts - if the jitter was
zero. */
#define timerEXPECTED_DIFFERENCE_VALUE	( configCPU_CLOCK_HZ / timerINTERRUPT_FREQUENCY )

/* The number of interrupts to pass before we start looking at the jitter. */
#define timerSETTLE_TIME			5
/*---------------------------------------------------------------------------*/

/*
 * Configures the two timers used to perform the test.
 */
void vSetupTimerTest( void );

/* Interrupt handler in which the jitter is measured. */
CY_ISR_PROTO(vTimer20KHzISR);

/* Stores the value of the maximum recorded jitter between interrupts. */
volatile unsigned short usMaxJitter = 0;
/*---------------------------------------------------------------------------*/

void vSetupTimerTest( void )
{
	/* Install the ISR. */
	isrTimer_20KHz_TC_StartEx(vTimer20KHzISR);
}
/*---------------------------------------------------------------------------*/

CY_ISR(vTimer20KHzISR)
{
static unsigned short usLastCount = 0, usSettleCount = 0, usMaxDifference = 0;
unsigned short usThisCount, usDifference;

	/* Capture the free running timer value as we enter the interrupt. */
	usThisCount = Timer_48MHz_ReadCounter();
		
	if( usSettleCount >= timerSETTLE_TIME )
	{
		/* What is the difference between the timer value in this interrupt
		and the value from the last interrupt. Timer counts down. */
		usDifference = usLastCount + ~usThisCount + 1;

		/* Store the difference in the timer values if it is larger than the
		currently stored largest value.  The difference over and above the
		expected difference will give the 'jitter' in the processing of these
		interrupts. */
		if( usDifference > usMaxDifference )
		{
			usMaxDifference = usDifference;
			
			/* Calculate the Jitter based on the difference we expect. */
			usMaxJitter = usMaxDifference - timerEXPECTED_DIFFERENCE_VALUE;
		}
	}
	else
	{
		/* Don't bother storing any values for the first couple of
		interrupts. */
		usSettleCount++;
	}

	/* Remember what the timer value was this time through, so we can calculate
	the difference the next time through. */
	usLastCount = usThisCount;
}
/*---------------------------------------------------------------------------*/
