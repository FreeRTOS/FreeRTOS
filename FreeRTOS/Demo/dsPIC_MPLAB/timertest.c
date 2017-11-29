/*
 * FreeRTOS Kernel V10.0.0
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
 * copies or substantial portions of the Software. If you wish to use our Amazon
 * FreeRTOS name, please do so in a fair use way that does not cause confusion.
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


/* Scheduler includes. */
#include "FreeRTOS.h"

/* Demo includes. */
#include "partest.h"

/* The number of interrupts to pass before we start looking at the jitter. */
#define timerSETTLE_TIME			5

/* The maximum value the 16bit timer can contain. */
#define timerMAX_COUNT				0xffff

/*-----------------------------------------------------------*/

/*
 * Measure the time between this interrupt and the previous interrupt to 
 * calculate the timing jitter.  Remember the maximum value the jitter has
 * ever been calculated to be.
 */
static void prvCalculateAndStoreJitter( void );

/*-----------------------------------------------------------*/

/* The maximum time (in processor clocks) between two consecutive timer
interrupts so far. */
unsigned short usMaxJitter = 0;

/*-----------------------------------------------------------*/

void vSetupTimerTest( unsigned short usFrequencyHz )
{
	/* T2 is used to generate interrupts.  T4 is used to provide an accurate
	time measurement. */
	T2CON = 0;
	T4CON = 0;
	TMR2 = 0;
	TMR4 = 0;

	/* Timer 2 is going to interrupt at usFrequencyHz Hz. */
	PR2 = ( unsigned short ) ( configCPU_CLOCK_HZ / ( unsigned long ) usFrequencyHz );

	/* Timer 4 is going to free run from minimum to maximum value. */
	PR4 = ( unsigned short ) timerMAX_COUNT;

	/* Setup timer 2 interrupt priority to be above the kernel priority so 
	the timer jitter is not effected by the kernel activity. */
	IPC1bits.T2IP = configKERNEL_INTERRUPT_PRIORITY + 1;

	/* Clear the interrupt as a starting condition. */
	IFS0bits.T2IF = 0;

	/* Enable the interrupt. */
	IEC0bits.T2IE = 1;

	/* Start both timers. */
	T2CONbits.TON = 1;
	T4CONbits.TON = 1;
}
/*-----------------------------------------------------------*/

static void prvCalculateAndStoreJitter( void )
{
static unsigned short usLastCount = 0, usSettleCount = 0;
unsigned short usThisCount, usDifference;

	/* Capture the timer value as we enter the interrupt. */
	usThisCount = TMR4;

	if( usSettleCount >= timerSETTLE_TIME )
	{
		/* What is the difference between the timer value in this interrupt
		and the value from the last interrupt. */
		usDifference = usThisCount - usLastCount;

		/* Store the difference in the timer values if it is larger than the
		currently stored largest value.  The difference over and above the 
		expected difference will give the 'jitter' in the processing of these
		interrupts. */
		if( usDifference > usMaxJitter )
		{
			usMaxJitter = usDifference;
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
/*-----------------------------------------------------------*/

void __attribute__((__interrupt__, auto_psv)) _T2Interrupt( void )
{
	/* Work out the time between this and the previous interrupt. */
	prvCalculateAndStoreJitter();

	/* Clear the timer interrupt. */
	IFS0bits.T2IF = 0;
}


