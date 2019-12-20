/*
 * FreeRTOS Kernel V10.2.1
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
#include "task.h"

/* Demo includes. */
#include "IntQueueTimer.h"
#include "IntQueue.h"

/* Driver APIs.*/
#include "fsl_ctimer.h"

/* The priorities for the two timers.  Note that a priority of 0 is the highest
possible on Cortex-M devices. */
#define tmrMAX_PRIORITY				( 0UL )
#define trmSECOND_HIGHEST_PRIORITY ( tmrMAX_PRIORITY + 1 )

void vInitialiseTimerForIntQueueTest( void )
{
ctimer_config_t xConfigTimer0, xConfigTimer1;
ctimer_match_config_t xConfigInterrupt = { 0 };

	memset( &xConfigTimer0, 0x00, sizeof( xConfigTimer0 ) );
	memset( &xConfigTimer1, 0x00, sizeof( xConfigTimer1 ) );

	/* Enable peripheral bus clock for CTIMER0 and CTIMER1. */
	CLOCK_EnableClock( kCLOCK_Ctimer0 );
	CLOCK_EnableClock( kCLOCK_Ctimer1 );

	/* Interrupt settings for timers --
	A timer will generates an interrupt when the count matches the value specified.
	Timer will reset itself and restart the count. The interrupt frequency is fairly
	arbitrary, in a sense that all we need to make sure is IRQs are triggered so that
	queues have items for tasks to process. */
	xConfigInterrupt.enableCounterReset = true;
	xConfigInterrupt.enableCounterStop = false;
	xConfigInterrupt.enableInterrupt = true;
	xConfigInterrupt.matchValue = 0xFFFFF;
	xConfigInterrupt.outControl = kCTIMER_Output_NoAction;
	xConfigInterrupt.outPinInitState = true;

	/* Configuration settings for timers. */
	CTIMER_GetDefaultConfig( &xConfigTimer0 );
	xConfigTimer0.prescale = 1;

	CTIMER_GetDefaultConfig( &xConfigTimer1 );
	xConfigTimer1.prescale = 2;

	/* Initialize timers. */
	CTIMER_Init( CTIMER0, &xConfigTimer0 );
	CTIMER_SetupMatch( CTIMER0, kCTIMER_Match_0, &xConfigInterrupt );

	CTIMER_Init( CTIMER1, &xConfigTimer1 );
	CTIMER_SetupMatch( CTIMER1, kCTIMER_Match_0, &xConfigInterrupt );

	/* Don't generate interrupts until the scheduler has been started.
	Interrupts will be automatically enabled when the first task starts
	running. */
	taskDISABLE_INTERRUPTS();

	/* Set the timer interrupts to be above the kernel.  The interrupts are
	assigned different priorities so they nest with each other. */
	NVIC_SetPriority( CTIMER0_IRQn, trmSECOND_HIGHEST_PRIORITY );
	NVIC_SetPriority( CTIMER1_IRQn, tmrMAX_PRIORITY );

	/* Enable the timer interrupts. */
	NVIC_EnableIRQ( CTIMER0_IRQn );
	NVIC_EnableIRQ( CTIMER1_IRQn );

	/* Start timers. */
	CTIMER_StartTimer( CTIMER0 );
	CTIMER_StartTimer( CTIMER1 );
}
/*-----------------------------------------------------------*/

void CTIMER0_IRQHandler( void )
{
uint32_t ulInterruptStatus;

	/* Get Interrupt status flags */
	ulInterruptStatus = CTIMER_GetStatusFlags( CTIMER0 );

	/* Clear the status flags that were set */
	CTIMER_ClearStatusFlags( CTIMER0, ulInterruptStatus );

	portEND_SWITCHING_ISR( xFirstTimerHandler() );
}
/*-----------------------------------------------------------*/

void CTIMER1_IRQHandler(void)
{
uint32_t ulInterruptStatus;

	/* Get Interrupt status flags */
	ulInterruptStatus = CTIMER_GetStatusFlags( CTIMER1 );

	/* Clear the status flags that were set */
	CTIMER_ClearStatusFlags( CTIMER1, ulInterruptStatus );

	portEND_SWITCHING_ISR( xSecondTimerHandler() );
}
/*-----------------------------------------------------------*/
