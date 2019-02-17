/*
 * FreeRTOS Kernel V10.2.0
 * Copyright (C) 2019 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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


