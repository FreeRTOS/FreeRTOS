/*
	FreeRTOS V5.4.0 - Copyright (C) 2003-2009 Richard Barry.

	This file is part of the FreeRTOS distribution.

	FreeRTOS is free software; you can redistribute it and/or modify it	under 
	the terms of the GNU General Public License (version 2) as published by the 
	Free Software Foundation and modified by the FreeRTOS exception.
	**NOTE** The exception to the GPL is included to allow you to distribute a
	combined work that includes FreeRTOS without being obliged to provide the 
	source code for proprietary components outside of the FreeRTOS kernel.  
	Alternative commercial license and support terms are also available upon 
	request.  See the licensing section of http://www.FreeRTOS.org for full 
	license details.

	FreeRTOS is distributed in the hope that it will be useful,	but WITHOUT
	ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
	FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
	more details.

	You should have received a copy of the GNU General Public License along
	with FreeRTOS; if not, write to the Free Software Foundation, Inc., 59
	Temple Place, Suite 330, Boston, MA  02111-1307  USA.


	***************************************************************************
	*                                                                         *
	* Looking for a quick start?  Then check out the FreeRTOS eBook!          *
	* See http://www.FreeRTOS.org/Documentation for details                   *
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

/* The maximum value the 16bit timer can contain. */
#define timerMAX_COUNT				0xffff

/* The timer 2 interrupt handler. */
void __attribute__( (interrupt(ipl0), vector(_TIMER_2_VECTOR))) vT2InterruptWrapper( void );

/*-----------------------------------------------------------*/

/* Incremented every 20,000 interrupts, so should count in seconds. */
unsigned portLONG ulHighFrequencyTimerInterrupts = 0;

/* The frequency at which the timer is interrupting. */
static unsigned portLONG ulFrequencyHz;

/*-----------------------------------------------------------*/

void vSetupTimerTest( unsigned portSHORT usFrequencyHz )
{
	/* Remember the frequency so it can be used from the ISR. */
	ulFrequencyHz = ( unsigned portLONG ) usFrequencyHz;

	/* T2 is used to generate interrupts above the kernel and max syscall interrupt
	priority. */
	T2CON = 0;
	TMR2 = 0;

	/* Timer 2 is going to interrupt at usFrequencyHz Hz. */
	PR2 = ( unsigned portSHORT ) ( ( configPERIPHERAL_CLOCK_HZ / ( unsigned portLONG ) usFrequencyHz ) - 1 );

	/* Setup timer 2 interrupt priority to be above the kernel priority so 
	the timer jitter is not effected by the kernel activity. */
	ConfigIntTimer2( T2_INT_ON | ( configMAX_SYSCALL_INTERRUPT_PRIORITY + 1 ) );

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
static unsigned portLONG ulCalls = 0;

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
	IFS0bits.T2IF = 0;
}


