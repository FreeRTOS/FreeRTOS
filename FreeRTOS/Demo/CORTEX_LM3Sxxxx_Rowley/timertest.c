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

/* High speed timer test as described in main.c. */

/* Scheduler includes. */
#include "FreeRTOS.h"

/* Library includes. */
#include "hw_ints.h"
#include "hw_memmap.h"
#include "hw_types.h"
#include "interrupt.h"
#include "sysctl.h"
#include "lmi_timer.h"

/* The set frequency of the interrupt.  Deviations from this are measured as
the jitter. */
#define timerINTERRUPT_FREQUENCY		( 20000UL )

/* The expected time between each of the timer interrupts - if the jitter was
zero. */
#define timerEXPECTED_DIFFERENCE_VALUE	( configCPU_CLOCK_HZ / timerINTERRUPT_FREQUENCY )

/* The highest available interrupt priority. */
#define timerHIGHEST_PRIORITY			( 0 )

/* Misc defines. */
#define timerMAX_32BIT_VALUE			( 0xffffffffUL )
#define timerTIMER_1_COUNT_VALUE		( * ( ( unsigned long * ) ( TIMER1_BASE + 0x48 ) ) )

/*-----------------------------------------------------------*/

/* Interrupt handler in which the jitter is measured. */
void Timer0IntHandler( void );

/* Stores the value of the maximum recorded jitter between interrupts. */
volatile unsigned long ulMaxJitter = 0UL;

/* Counts the total number of times that the high frequency timer has 'ticked'.
This value is used by the run time stats function to work out what percentage
of CPU time each task is taking. */
volatile unsigned long ulHighFrequencyTimerTicks = 0UL;
/*-----------------------------------------------------------*/

void vSetupHighFrequencyTimer( void )
{
unsigned long ulFrequency;

	/* Timer zero is used to generate the interrupts, and timer 1 is used
	to measure the jitter. */
	SysCtlPeripheralEnable( SYSCTL_PERIPH_TIMER0 );
    SysCtlPeripheralEnable( SYSCTL_PERIPH_TIMER1 );
    TimerConfigure( TIMER0_BASE, TIMER_CFG_32_BIT_PER );
    TimerConfigure( TIMER1_BASE, TIMER_CFG_32_BIT_PER );

	/* Set the timer interrupt to be above the kernel - highest. */
	IntPrioritySet( INT_TIMER0A, timerHIGHEST_PRIORITY );

	/* Just used to measure time. */
    TimerLoadSet(TIMER1_BASE, TIMER_A, timerMAX_32BIT_VALUE );

	/* Ensure interrupts do not start until the scheduler is running. */
	portDISABLE_INTERRUPTS();

	/* The rate at which the timer will interrupt. */
	ulFrequency = configCPU_CLOCK_HZ / timerINTERRUPT_FREQUENCY;
    TimerLoadSet( TIMER0_BASE, TIMER_A, ulFrequency );
    IntEnable( INT_TIMER0A );
    TimerIntEnable( TIMER0_BASE, TIMER_TIMA_TIMEOUT );

	/* Enable both timers. */
    TimerEnable( TIMER0_BASE, TIMER_A );
    TimerEnable( TIMER1_BASE, TIMER_A );
}
/*-----------------------------------------------------------*/

void Timer0IntHandler( void )
{
unsigned long ulDifference;
volatile unsigned long ulCurrentCount;
static unsigned long ulMaxDifference = 0, ulLastCount = 0;

	/* We use the timer 1 counter value to measure the clock cycles between
	the timer 0 interrupts. */
	ulCurrentCount = timerTIMER_1_COUNT_VALUE;

	TimerIntClear( TIMER0_BASE, TIMER_TIMA_TIMEOUT );

	if( ulCurrentCount < ulLastCount )
	{
		/* How many times has timer 1 counted since the last interrupt? */
		ulDifference = 	ulLastCount - ulCurrentCount;

		/* Is this the largest difference we have measured yet? */
		if( ulDifference > ulMaxDifference )
		{
			ulMaxDifference = ulDifference;
			ulMaxJitter = ulMaxDifference - timerEXPECTED_DIFFERENCE_VALUE;
		}
	}

	ulLastCount = ulCurrentCount;

	/* Keep a count of the total number of 20KHz ticks.  This is used by the
	run time stats functionality to calculate how much CPU time is used by
	each task. */
	ulHighFrequencyTimerTicks++;
}





