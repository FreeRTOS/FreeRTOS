/*
	FreeRTOS.org V4.6.1 - Copyright (C) 2003-2007 Richard Barry.

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
	See http://www.FreeRTOS.org for documentation, latest information, license 
	and contact details.  Please ensure to read the configuration and relevant 
	port sections of the online documentation.

	Also see http://www.SafeRTOS.com a version that has been certified for use
	in safety critical systems, plus commercial licensing, development and
	support options.
	***************************************************************************
*/

/* High speed timer test as described in main.c. */


/* Scheduler includes. */
#include "FreeRTOS.h"

/* Demo includes. */
#include "partest.h"

/* The number of interrupts to pass before we start looking at the jitter. */
#define timerSETTLE_TIME			200

/* The maximum value the 16bit timer can contain. */
#define timerMAX_COUNT				0xffff


/*-----------------------------------------------------------*/

/* The maximum time (in processor clocks) between two consecutive timer
interrupts so far. */
unsigned portLONG ulMaxJitter = 0;

/*-----------------------------------------------------------*/

void vSetupTimerTest( unsigned portSHORT usFrequencyHz )
{
	/* T2 is used to generate interrupts.  The core timer is used to provide an 
	accurate time measurement. */
	T2CON = 0;
	TMR2 = 0;

	/* Timer 2 is going to interrupt at usFrequencyHz Hz. */
	PR2 = ( unsigned portSHORT ) ( configPERIPHERAL_CLOCK_HZ / ( unsigned portLONG ) usFrequencyHz );

	/* Setup timer 2 interrupt priority to be above the kernel priority so 
	the timer jitter is not effected by the kernel activity. */
	ConfigIntTimer2( T2_INT_ON | ( configKERNEL_INTERRUPT_PRIORITY + 1 ) );

	/* Clear the interrupt as a starting condition. */
	IFS0bits.T2IF = 0;

	/* Enable the interrupt. */
	IEC0bits.T2IE = 1;

	/* Start the timer. */
	T2CONbits.TON = 1;
}
/*-----------------------------------------------------------*/

void __attribute__( (interrupt(ipl0), vector(_TIMER_2_VECTOR))) vT2InterruptHandler( void );
void vT2InterruptHandler( void )
{
static unsigned portLONG ulLastCount = 0, ulSettleCount = 0;
static unsigned portLONG ulThisCount, ulDifference;

	/* Capture the timer value as we enter the interrupt. */
	ulThisCount = _CP0_GET_COUNT();

	if( ulSettleCount >= timerSETTLE_TIME )
	{
		/* What is the difference between the timer value in this interrupt
		and the value from the last interrupt. */
		ulDifference = ulThisCount - ulLastCount;

		/* Store the difference in the timer values if it is larger than the
		currently stored largest value.  The difference over and above the 
		expected difference will give the 'jitter' in the processing of these
		interrupts. */
		if( ulDifference > ulMaxJitter )
		{
			ulMaxJitter = ulDifference;
		}
	}
	else
	{
		/* Don't bother storing any values for the first couple of 
		interrupts. */
		ulSettleCount++;
	}

	/* Remember what the timer value was this time through, so we can calculate
	the difference the next time through. */
	ulLastCount = ulThisCount;

	/* Clear the timer interrupt. */
	IFS0bits.T2IF = 0;
}


