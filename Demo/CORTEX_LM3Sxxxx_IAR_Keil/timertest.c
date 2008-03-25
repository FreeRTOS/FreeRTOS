/*
	FreeRTOS.org V4.8.0 - Copyright (C) 2003-2008 Richard Barry.

	This file is part of the FreeRTOS.org distribution.

	FreeRTOS.org is free software; you can redistribute it and/or modify
	it under the terms of the GNU General Public License as published by
	the Free Software Foundation; either version 2 of the License, or
	(at your option) any later version.

	FreeRTOS.org is distributed in the hope that it will be useful,
	but WITHOUT ANY WARRANTY; without even the implied warranty of
	MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
	GNU General Public License for more details.

	You should have received a copy of the GNU General Public License
	along with FreeRTOS.org; if not, write to the Free Software
	Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA

	A special exception to the GPL can be applied should you wish to distribute
	a combined work that includes FreeRTOS.org, without being obliged to provide
	the source code for any proprietary components.  See the licensing section
	of http://www.FreeRTOS.org for full details of how and when the exception
	can be applied.

	***************************************************************************
	***************************************************************************
	*																		  *
	* SAVE TIME AND MONEY!  Why not get us to quote to get FreeRTOS.org		  *
	* running on your hardware - or even write all or part of your application*
	* for you?  See http://www.OpenRTOS.com for details.					  *
	*																		  *
	***************************************************************************
	***************************************************************************

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
volatile unsigned portLONG ulMaxJitter = 0;

/*-----------------------------------------------------------*/

void vSetupTimer( void )
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
static portLONG ulMaxDifference = 0, ulLastCount = 0;

	/* We use the timer 1 counter value to measure the clock cycles between
	the timer 0 interrupts. */
	ulCurrentCount = timerTIMER_1_COUNT_VALUE;

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

    TimerIntClear( TIMER0_BASE, TIMER_TIMA_TIMEOUT );
}





