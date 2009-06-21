/*
	FreeRTOS.org V5.3.1 - Copyright (C) 2003-2009 Richard Barry.

	This file is part of the FreeRTOS.org distribution.

	FreeRTOS.org is free software; you can redistribute it and/or modify it
	under the terms of the GNU General Public License (version 2) as published
	by the Free Software Foundation and modified by the FreeRTOS exception.
	**NOTE** The exception to the GPL is included to allow you to distribute a
	combined work that includes FreeRTOS.org without being obliged to provide
	the source code for any proprietary components.  Alternative commercial
	license and support terms are also available upon request.  See the 
	licensing section of http://www.FreeRTOS.org for full details.

	FreeRTOS.org is distributed in the hope that it will be useful,	but WITHOUT
	ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
	FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
	more details.

	You should have received a copy of the GNU General Public License along
	with FreeRTOS.org; if not, write to the Free Software Foundation, Inc., 59
	Temple Place, Suite 330, Boston, MA  02111-1307  USA.


	***************************************************************************
	*                                                                         *
	* Get the FreeRTOS eBook!  See http://www.FreeRTOS.org/Documentation      *
	*                                                                         *
	* This is a concise, step by step, 'hands on' guide that describes both   *
	* general multitasking concepts and FreeRTOS specifics. It presents and   *
	* explains numerous examples that are written using the FreeRTOS API.     *
	* Full source code for all the examples is provided in an accompanying    *
	* .zip file.                                                              *
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
volatile unsigned portLONG ulMaxJitter = 0UL;

/* Counts the total number of times that the high frequency timer has 'ticked'.
This value is used by the run time stats function to work out what percentage
of CPU time each task is taking. */
volatile unsigned portLONG ulHighFrequencyTimerTicks = 0UL;
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
unsigned portLONG ulDifference;
volatile unsigned portLONG ulCurrentCount;
static unsigned portLONG ulMaxDifference = 0, ulLastCount = 0;

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





