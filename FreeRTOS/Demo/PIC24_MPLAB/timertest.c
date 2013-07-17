/*
    FreeRTOS V7.5.0 - Copyright (C) 2013 Real Time Engineers Ltd.

    VISIT http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

    ***************************************************************************
     *                                                                       *
     *    FreeRTOS provides completely free yet professionally developed,    *
     *    robust, strictly quality controlled, supported, and cross          *
     *    platform software that has become a de facto standard.             *
     *                                                                       *
     *    Help yourself get started quickly and support the FreeRTOS         *
     *    project by purchasing a FreeRTOS tutorial book, reference          *
     *    manual, or both from: http://www.FreeRTOS.org/Documentation        *
     *                                                                       *
     *    Thank you!                                                         *
     *                                                                       *
    ***************************************************************************

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation >>!AND MODIFIED BY!<< the FreeRTOS exception.

    >>! NOTE: The modification to the GPL is included to allow you to distribute
    >>! a combined work that includes FreeRTOS without being obliged to provide
    >>! the source code for proprietary components outside of the FreeRTOS
    >>! kernel.

    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT ANY
    WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
    FOR A PARTICULAR PURPOSE.  Full license text is available from the following
    link: http://www.freertos.org/a00114.html

    1 tab == 4 spaces!

    ***************************************************************************
     *                                                                       *
     *    Having a problem?  Start by reading the FAQ "My application does   *
     *    not run, what could be wrong?"                                     *
     *                                                                       *
     *    http://www.FreeRTOS.org/FAQHelp.html                               *
     *                                                                       *
    ***************************************************************************

    http://www.FreeRTOS.org - Documentation, books, training, latest versions,
    license and Real Time Engineers Ltd. contact details.

    http://www.FreeRTOS.org/plus - A selection of FreeRTOS ecosystem products,
    including FreeRTOS+Trace - an indispensable productivity tool, a DOS
    compatible FAT file system, and our tiny thread aware UDP/IP stack.

    http://www.OpenRTOS.com - Real Time Engineers ltd license FreeRTOS to High
    Integrity Systems to sell under the OpenRTOS brand.  Low cost OpenRTOS
    licenses offer ticketed support, indemnification and middleware.

    http://www.SafeRTOS.com - High Integrity Systems also provide a safety
    engineered and independently SIL3 certified version for use in safety and
    mission critical applications that require provable dependability.

    1 tab == 4 spaces!
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
unsigned portSHORT usMaxJitter = 0;

/*-----------------------------------------------------------*/

void vSetupTimerTest( unsigned portSHORT usFrequencyHz )
{
	/* T2 is used to generate interrupts.  T4 is used to provide an accurate
	time measurement. */
	T2CON = 0;
	T4CON = 0;
	TMR2 = 0;
	TMR4 = 0;

	/* Timer 2 is going to interrupt at usFrequencyHz Hz. */
	PR2 = ( unsigned portSHORT ) ( configCPU_CLOCK_HZ / ( unsigned portLONG ) usFrequencyHz );

	/* Timer 4 is going to free run from minimum to maximum value. */
	PR4 = ( unsigned portSHORT ) timerMAX_COUNT;

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
static unsigned portSHORT usLastCount = 0, usSettleCount = 0;
unsigned portSHORT usThisCount, usDifference;

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


