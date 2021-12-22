/*
 * FreeRTOS V202112.00
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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

/*
 * Provides the two timers sources for the standard demo IntQueue test.  Also
 * includes a high frequency timer to maximise the interrupt nesting achieved.
 */

/* Standard includes. */
#include <limits.h>

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "task.h"

/* Demo includes. */
#include "IntQueueTimer.h"
#include "IntQueue.h"

/* System includes. */
#include "board.h"
#include "asf.h"

/* The frequencies at which the first two timers expire are slightly offset to
ensure they don't remain synchronised.  The frequency of the highest priority
interrupt is 20 times faster so really hammers the interrupt entry and exit
code. */
#define tmrTIMER_0_FREQUENCY	( 2000UL )
#define tmrTIMER_1_FREQUENCY	( 1003UL )
#define tmrTIMER_2_FREQUENCY	( 5000UL )

/* Priorities used by the timer interrupts - these are set differently to make
nesting likely/common.  The high frequency timer operates above the max
system call interrupt priority, but does not use the RTOS API. */
#define tmrTIMER_0_PRIORITY		( configLIBRARY_MAX_SYSCALL_INTERRUPT_PRIORITY )
#define tmrTIMER_1_PRIORITY		( configLIBRARY_MAX_SYSCALL_INTERRUPT_PRIORITY + 1 )
#define tmrTIMER_2_PRIORITY		( configLIBRARY_MAX_SYSCALL_INTERRUPT_PRIORITY - 1 )

/* The channels used within the TC0 timer. */
#define tmrTIMER_0_CHANNEL		( 0 )
#define tmrTIMER_1_CHANNEL		( 1 )
#define tmrTIMER_2_CHANNEL		( 2 )

/* TC register bit specifics. */
#define tmrTRIGGER_ON_RC		( 1UL << 4UL )
#define trmDIVIDER				( 128 )

/*-----------------------------------------------------------*/

/* Handers for the timer interrupts. */
void TC0_Handler( void );
void TC1_Handler( void );
void TC2_Handler( void );

/*-----------------------------------------------------------*/

/* Incremented by the high frequency timer, which operates above the max
syscall interrupt priority.  This is just for inspection. */
volatile uint32_t ulHighFrequencyTimerInterrupts = 0;

/*-----------------------------------------------------------*/

void vInitialiseTimerForIntQueueTest( void )
{
uint32_t ulInputFrequency;

	/* Calculate the frequency of the clock that feeds the TC. */
	ulInputFrequency = configCPU_CLOCK_HZ;
	ulInputFrequency /= trmDIVIDER;

	/* Three channels are used - two that run at or under 
	configMAX_SYSCALL_INTERRUPT_PRIORITY, and one that runs over
	configMAX_SYSCALL_INTERRUPT_PRIORITY. */
	sysclk_enable_peripheral_clock( ID_TC0 );
	sysclk_enable_peripheral_clock( ID_TC1 );
	sysclk_enable_peripheral_clock( ID_TC2 );
	
	/* Init TC channels to waveform mode - up mode clean on RC match. */
	tc_init( TC0, tmrTIMER_0_CHANNEL, TC_CMR_TCCLKS_TIMER_CLOCK4 | TC_CMR_WAVE | TC_CMR_ACPC_CLEAR | TC_CMR_CPCTRG );
	tc_init( TC0, tmrTIMER_1_CHANNEL, TC_CMR_TCCLKS_TIMER_CLOCK4 | TC_CMR_WAVE | TC_CMR_ACPC_CLEAR | TC_CMR_CPCTRG );
	tc_init( TC0, tmrTIMER_2_CHANNEL, TC_CMR_TCCLKS_TIMER_CLOCK4 | TC_CMR_WAVE | TC_CMR_ACPC_CLEAR | TC_CMR_CPCTRG );
	
	tc_enable_interrupt( TC0, tmrTIMER_0_CHANNEL, tmrTRIGGER_ON_RC );
	tc_enable_interrupt( TC0, tmrTIMER_1_CHANNEL, tmrTRIGGER_ON_RC );
	tc_enable_interrupt( TC0, tmrTIMER_2_CHANNEL, tmrTRIGGER_ON_RC );
	
	tc_write_rc( TC0, tmrTIMER_0_CHANNEL, ( ulInputFrequency / tmrTIMER_0_FREQUENCY ) );
	tc_write_rc( TC0, tmrTIMER_1_CHANNEL, ( ulInputFrequency / tmrTIMER_1_FREQUENCY ) );
	tc_write_rc( TC0, tmrTIMER_2_CHANNEL, ( ulInputFrequency / tmrTIMER_2_FREQUENCY ) );

	NVIC_SetPriority( TC0_IRQn, tmrTIMER_0_PRIORITY );
	NVIC_SetPriority( TC1_IRQn, tmrTIMER_1_PRIORITY );
	NVIC_SetPriority( TC2_IRQn, tmrTIMER_2_PRIORITY );

	NVIC_EnableIRQ( TC0_IRQn );
	NVIC_EnableIRQ( TC1_IRQn );
	NVIC_EnableIRQ( TC2_IRQn );

	tc_start( TC0, tmrTIMER_0_CHANNEL );
	tc_start( TC0, tmrTIMER_1_CHANNEL );
	tc_start( TC0, tmrTIMER_2_CHANNEL );
}
/*-----------------------------------------------------------*/

void TC0_Handler( void )
{
	/* Handler for the first timer in the IntQueue test.  Was the interrupt
	caused by a compare on RC? */
	if( ( tc_get_status( TC0, tmrTIMER_0_CHANNEL ) & ~TC_SR_CPCS ) != 0 )
	{
		portYIELD_FROM_ISR( xFirstTimerHandler() );	
	}
}
/*-----------------------------------------------------------*/

void TC1_Handler( void )
{
	/* Handler for the second timer in the IntQueue test.  Was the interrupt
	caused by a compare on RC? */
	if( ( tc_get_status( TC0, tmrTIMER_1_CHANNEL ) & ~TC_SR_CPCS ) != 0 )
	{
		portYIELD_FROM_ISR( xSecondTimerHandler() );
	}
}
/*-----------------------------------------------------------*/

void TC2_Handler( void )
{
	/* Handler for the high frequency timer that does nothing but increment a
	variable to give an indication that it is running.  Was the interrupt caused
	by a compare on RC? */
	if( ( tc_get_status( TC0, tmrTIMER_2_CHANNEL ) & ~TC_SR_CPCS ) != 0 )
	{
		ulHighFrequencyTimerInterrupts++;
	}
}
