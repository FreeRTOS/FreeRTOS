/*
 * FreeRTOS V202112.00
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

/* High speed timer test as described in main.c. */


/* Scheduler includes. */
#include "FreeRTOS.h"

/* The maximum value the 16bit timer can contain. */
#define timerMAX_COUNT				0xffff

/* The timer 2 interrupt handler.  As this interrupt uses the FreeRTOS assembly
entry point the IPL setting in the following function prototype has no effect.
The interrupt priority is set by ConfigIntTimer2() in vSetupTimerTest(). */
void __attribute__( (interrupt(IPL0AUTO), vector(_TIMER_2_VECTOR))) vT2InterruptWrapper( void );

/*-----------------------------------------------------------*/

/* Incremented every 20,000 interrupts, so should count in seconds. */
unsigned long ulHighFrequencyTimerInterrupts = 0;

/* The frequency at which the timer is interrupting. */
static unsigned long ulFrequencyHz;

/*-----------------------------------------------------------*/

void vSetupTimerTest( unsigned short usFrequencyHz )
{
	/* Remember the frequency so it can be used from the ISR. */
	ulFrequencyHz = ( unsigned long ) usFrequencyHz;

	/* T2 is used to generate interrupts above the kernel and max syscall interrupt
	priority. */
	T2CON = 0;
	TMR2 = 0;

	/* Timer 2 is going to interrupt at usFrequencyHz Hz. */
	PR2 = ( unsigned short ) ( ( configPERIPHERAL_CLOCK_HZ / ( unsigned long ) usFrequencyHz ) - 1 );

	/* Setup timer 2 interrupt priority to be above the kernel priority so
	the timer jitter is not effected by the kernel activity. */
	IPC2bits.T2IP = ( configMAX_SYSCALL_INTERRUPT_PRIORITY + 1 );

	/* Clear the interrupt as a starting condition. */
	IFS0bits.T2IF = 0;

	/* Enable the interrupt. */
	IEC0bits.T2IE = 1;

	/* Start the timer. */
	T2CONbits.TON = 1;
}
/*-----------------------------------------------------------*/

void vT2InterruptHandler( void )
{
static unsigned long ulCalls = 0;

	++ulCalls;
	if( ulCalls >= ulFrequencyHz )
	{
		/* Increment the count that will be shown on the LCD. 
		The increment occurs once every 20,000 interrupts so
		ulHighFrequencyTimerInterrupts should count in seconds. */
		ulHighFrequencyTimerInterrupts++;
		ulCalls = 0;
	}

	/* Clear the timer interrupt. */
	IFS0CLR = _IFS0_T2IF_MASK;
}


