/*
	FreeRTOS V5.4.1 - Copyright (C) 2009 Real Time Engineers Ltd.

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

/* Scheduler includes. */
#include "FreeRTOS.h"

/* Demo includes. */
#include "IntQueueTimer.h"
#include "IntQueue.h"

/* Library includes. */
#include "hw_ints.h"
#include "hw_memmap.h"
#include "hw_types.h"
#include "interrupt.h"
#include "sysctl.h"
#include "lmi_timer.h"

#define tmrTIMER_2_FREQUENCY	( 2000UL )
#define tmrTIMER_3_FREQUENCY	( 2001UL )

void vInitialiseTimerForIntQueueTest( void )
{
unsigned long ulFrequency;

	/* Timer 2 and 3 are utilised for this test. */
	SysCtlPeripheralEnable( SYSCTL_PERIPH_TIMER2 );
    SysCtlPeripheralEnable( SYSCTL_PERIPH_TIMER3 );
    TimerConfigure( TIMER2_BASE, TIMER_CFG_32_BIT_PER );
    TimerConfigure( TIMER3_BASE, TIMER_CFG_32_BIT_PER );
	
	/* Set the timer interrupts to be above the kernel.  The interrupts are
	 assigned different priorities so they nest with each other. */
	IntPrioritySet( INT_TIMER2A, configMAX_SYSCALL_INTERRUPT_PRIORITY + ( 1 << 5 ) ); /* Shift left 5 as only the top 3 bits are implemented. */
	IntPrioritySet( INT_TIMER3A, configMAX_SYSCALL_INTERRUPT_PRIORITY );

	/* Ensure interrupts do not start until the scheduler is running. */
	portDISABLE_INTERRUPTS();
	
	/* The rate at which the timers will interrupt. */
	ulFrequency = configCPU_CLOCK_HZ / tmrTIMER_2_FREQUENCY;	
    TimerLoadSet( TIMER2_BASE, TIMER_A, ulFrequency );
    IntEnable( INT_TIMER2A );
    TimerIntEnable( TIMER2_BASE, TIMER_TIMA_TIMEOUT );

	/* The rate at which the timers will interrupt. */
	ulFrequency = configCPU_CLOCK_HZ / tmrTIMER_3_FREQUENCY;	
    TimerLoadSet( TIMER3_BASE, TIMER_A, ulFrequency );
    IntEnable( INT_TIMER3A );
    TimerIntEnable( TIMER3_BASE, TIMER_TIMA_TIMEOUT );

    /* Enable both timers. */	
    TimerEnable( TIMER2_BASE, TIMER_A );
    TimerEnable( TIMER3_BASE, TIMER_A );
}
/*-----------------------------------------------------------*/

void vT2InterruptHandler( void )
{
    TimerIntClear( TIMER2_BASE, TIMER_TIMA_TIMEOUT );	
	portEND_SWITCHING_ISR( xFirstTimerHandler() );
}
/*-----------------------------------------------------------*/

void vT3InterruptHandler( void )
{
	TimerIntClear( TIMER3_BASE, TIMER_TIMA_TIMEOUT );
	portEND_SWITCHING_ISR( xSecondTimerHandler() );
}


