/*
    FreeRTOS V6.1.1 - Copyright (C) 2011 Real Time Engineers Ltd.

    ***************************************************************************
    *                                                                         *
    * If you are:                                                             *
    *                                                                         *
    *    + New to FreeRTOS,                                                   *
    *    + Wanting to learn FreeRTOS or multitasking in general quickly       *
    *    + Looking for basic training,                                        *
    *    + Wanting to improve your FreeRTOS skills and productivity           *
    *                                                                         *
    * then take a look at the FreeRTOS books - available as PDF or paperback  *
    *                                                                         *
    *        "Using the FreeRTOS Real Time Kernel - a Practical Guide"        *
    *                  http://www.FreeRTOS.org/Documentation                  *
    *                                                                         *
    * A pdf reference manual is also available.  Both are usually delivered   *
    * to your inbox within 20 minutes to two hours when purchased between 8am *
    * and 8pm GMT (although please allow up to 24 hours in case of            *
    * exceptional circumstances).  Thank you for your support!                *
    *                                                                         *
    ***************************************************************************

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation AND MODIFIED BY the FreeRTOS exception.
    ***NOTE*** The exception to the GPL is included to allow you to distribute
    a combined work that includes FreeRTOS without being obliged to provide the
    source code for proprietary components outside of the FreeRTOS kernel.
    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT
    ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
    FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
    more details. You should have received a copy of the GNU General Public 
    License and the FreeRTOS license exception along with FreeRTOS; if not it 
    can be viewed here: http://www.freertos.org/a00114.html and also obtained 
    by writing to Richard Barry, contact details for whom are available on the
    FreeRTOS WEB site.

    1 tab == 4 spaces!

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

/* The timer 2 interrupt handler.  As this interrupt uses the FreeRTOS assembly
entry point the IPL setting in the following function prototype has no effect.
The interrupt priority is set by ConfigIntTimer2() in vSetupTimerTest(). */
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


