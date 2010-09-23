/*
    FreeRTOS V6.1.0 - Copyright (C) 2010 Real Time Engineers Ltd.

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

#include "FreeRTOS.h"
#include "IntQueueTimer.h"
#include "IntQueue.h"

#define timerINTERRUPT3_FREQUENCY	( 2000UL )
#define timerINTERRUPT4_FREQUENCY	( 2001UL )

void vT3InterruptHandler( void );
void vT4InterruptHandler( void );

void __attribute__( (interrupt(ipl0), vector(_TIMER_3_VECTOR))) vT3InterruptWrapper( void );
void __attribute__( (interrupt(ipl0), vector(_TIMER_4_VECTOR))) vT4InterruptWrapper( void );

void vInitialiseTimerForIntQueueTest( void )
{
	/* Timer 1 is used for the tick interrupt, timer 2 is used for the high
	frequency interrupt test.  This file therefore uses timers 3 and 4. */

	T3CON = 0;
	TMR3 = 0;
	PR3 = ( unsigned portSHORT ) ( configPERIPHERAL_CLOCK_HZ / timerINTERRUPT3_FREQUENCY );

	/* Setup timer 3 interrupt priority to be above the kernel priority. */
	ConfigIntTimer3( T3_INT_ON | ( configMAX_SYSCALL_INTERRUPT_PRIORITY - 1 ) );

	/* Clear the interrupt as a starting condition. */
	IFS0bits.T3IF = 0;

	/* Enable the interrupt. */
	IEC0bits.T3IE = 1;

	/* Start the timer. */
	T3CONbits.TON = 1;


	/* Do the same for timer 4. */
	T4CON = 0;
	TMR4 = 0;
	PR4 = ( unsigned portSHORT ) ( configPERIPHERAL_CLOCK_HZ / timerINTERRUPT4_FREQUENCY );

	/* Setup timer 4 interrupt priority to be above the kernel priority. */
	ConfigIntTimer4( T4_INT_ON | ( configMAX_SYSCALL_INTERRUPT_PRIORITY ) );

	/* Clear the interrupt as a starting condition. */
	IFS0bits.T4IF = 0;

	/* Enable the interrupt. */
	IEC0bits.T4IE = 1;

	/* Start the timer. */
	T4CONbits.TON = 1;
}
/*-----------------------------------------------------------*/

void vT3InterruptHandler( void )
{
	IFS0bits.T3IF = 0;
	portEND_SWITCHING_ISR( xFirstTimerHandler() );
}
/*-----------------------------------------------------------*/

void vT4InterruptHandler( void )
{
	IFS0bits.T4IF = 0;
	portEND_SWITCHING_ISR( xSecondTimerHandler() );
}


