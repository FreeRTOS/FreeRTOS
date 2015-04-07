/*
    FreeRTOS V8.2.1 - Copyright (C) 2015 Real Time Engineers Ltd.
    All rights reserved

    VISIT http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation >>!AND MODIFIED BY!<< the FreeRTOS exception.

    ***************************************************************************
    >>!   NOTE: The modification to the GPL is included to allow you to     !<<
    >>!   distribute a combined work that includes FreeRTOS without being   !<<
    >>!   obliged to provide the source code for proprietary components     !<<
    >>!   outside of the FreeRTOS kernel.                                   !<<
    ***************************************************************************

    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT ANY
    WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
    FOR A PARTICULAR PURPOSE.  Full license text is available on the following
    link: http://www.freertos.org/a00114.html

    ***************************************************************************
     *                                                                       *
     *    FreeRTOS provides completely free yet professionally developed,    *
     *    robust, strictly quality controlled, supported, and cross          *
     *    platform software that is more than just the market leader, it     *
     *    is the industry's de facto standard.                               *
     *                                                                       *
     *    Help yourself get started quickly while simultaneously helping     *
     *    to support the FreeRTOS project by purchasing a FreeRTOS           *
     *    tutorial book, reference manual, or both:                          *
     *    http://www.FreeRTOS.org/Documentation                              *
     *                                                                       *
    ***************************************************************************

    http://www.FreeRTOS.org/FAQHelp.html - Having a problem?  Start by reading
    the FAQ page "My application does not run, what could be wrong?".  Have you
    defined configASSERT()?

    http://www.FreeRTOS.org/support - In return for receiving this top quality
    embedded software for free we request you assist our global community by
    participating in the support forum.

    http://www.FreeRTOS.org/training - Investing in training allows your team to
    be as productive as possible as early as possible.  Now you can receive
    FreeRTOS training directly from Richard Barry, CEO of Real Time Engineers
    Ltd, and the world's leading authority on the world's leading RTOS.

    http://www.FreeRTOS.org/plus - A selection of FreeRTOS ecosystem products,
    including FreeRTOS+Trace - an indispensable productivity tool, a DOS
    compatible FAT file system, and our tiny thread aware UDP/IP stack.

    http://www.FreeRTOS.org/labs - Where new FreeRTOS products go to incubate.
    Come and try FreeRTOS+TCP, our new open source TCP/IP stack for FreeRTOS.

    http://www.OpenRTOS.com - Real Time Engineers ltd. license FreeRTOS to High
    Integrity Systems ltd. to sell under the OpenRTOS brand.  Low cost OpenRTOS
    licenses offer ticketed support, indemnification and commercial middleware.

    http://www.SafeRTOS.com - High Integrity Systems also provide a safety
    engineered and independently SIL3 certified version for use in safety and
    mission critical applications that require provable dependability.

    1 tab == 4 spaces!
*/

#include "FreeRTOS.h"
#include "IntQueueTimer.h"
#include "IntQueue.h"

#define timerINTERRUPT3_FREQUENCY	( 2000UL )
#define timerINTERRUPT4_FREQUENCY	( 2001UL )

void vT3InterruptHandler( void );
void vT4InterruptHandler( void );

/* As these interrupts use the FreeRTOS interrupt entry point, the IPL settings
in the following prototypes have no effect.  The interrupt priorities are set
by the ConfigIntTimerX() library calls in vInitialiseTimerForIntQueueTest(). */
void __attribute__( (interrupt(IPL0AUTO), vector(_TIMER_3_VECTOR))) vT3InterruptWrapper( void );
void __attribute__( (interrupt(IPL0AUTO), vector(_TIMER_4_VECTOR))) vT4InterruptWrapper( void );

void vInitialiseTimerForIntQueueTest( void )
{
	/* Timer 1 is used for the tick interrupt, timer 2 is used for the high
	frequency interrupt test.  This file therefore uses timers 3 and 4. */

	T3CON = 0;
	TMR3 = 0;
	PR3 = ( unsigned short ) ( configPERIPHERAL_CLOCK_HZ / timerINTERRUPT3_FREQUENCY );

	/* Setup timer 3 interrupt priority to be above the kernel priority. */
	IPC3bits.T3IP = ( configMAX_SYSCALL_INTERRUPT_PRIORITY - 1 );

	/* Clear the interrupt as a starting condition. */
	IFS0bits.T3IF = 0;

	/* Enable the interrupt. */
	IEC0bits.T3IE = 1;

	/* Start the timer. */
	T3CONbits.TON = 1;


	/* Do the same for timer 4. */
	T4CON = 0;
	TMR4 = 0;
	PR4 = ( unsigned short ) ( configPERIPHERAL_CLOCK_HZ / timerINTERRUPT4_FREQUENCY );

	/* Setup timer 4 interrupt priority to be above the kernel priority. */
	IPC4bits.T4IP = configMAX_SYSCALL_INTERRUPT_PRIORITY;

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
	IFS0CLR = _IFS0_T3IF_MASK;
	portEND_SWITCHING_ISR( xFirstTimerHandler() );
}
/*-----------------------------------------------------------*/

void vT4InterruptHandler( void )
{
	IFS0CLR = _IFS0_T4IF_MASK;
	portEND_SWITCHING_ISR( xSecondTimerHandler() );
}


