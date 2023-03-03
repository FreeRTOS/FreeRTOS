/*
 * FreeRTOS V202212.01
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
 * https://www.FreeRTOS.org
 * https://github.com/FreeRTOS
 *
 */

/* Scheduler includes. */
#include "FreeRTOS.h"

/* Demo includes. */
#include "IntQueueTimer.h"
#include "IntQueue.h"

/* Library includes. */
#include "SMM_MPS2.h"

/* Timer frequencies are slightly offset so they nest. */
#define tmrTIMER_0_FREQUENCY	( 2000UL )
#define tmrTIMER_1_FREQUENCY	( 2001UL )

volatile uint32_t ulNest, ulNestCount;

/*-----------------------------------------------------------*/

void TIMER0_Handler( void )
{
	/* Clear interrupt. */
	CMSDK_TIMER0->INTCLEAR = ( 1ul <<  0 );
	if( ulNest > 0 )
	{
		/* This interrupt occurred in between the nesting count being incremented
		and decremented in the TIMER1_Handler.  Keep a count of the number of
		times this happens as its printed out by the check task in main_full.c.*/
		ulNestCount++;
	}
	portEND_SWITCHING_ISR( xSecondTimerHandler() );
}
/*-----------------------------------------------------------*/

void TIMER1_Handler( void )
{
	/* Increment the nest count while inside this ISR as a crude way of the
	higher priority timer interrupt knowing if it interrupted the execution of
	this ISR. */
	ulNest++;
	/* Clear interrupt. */
	CMSDK_TIMER1->INTCLEAR = ( 1ul <<  0 );
	portEND_SWITCHING_ISR( xFirstTimerHandler() );
	ulNest--;
}
/*-----------------------------------------------------------*/

void vInitialiseTimerForIntQueueTest( void )
{
	/* Clear interrupt. */
	CMSDK_TIMER0->INTCLEAR = ( 1ul <<  0 );

	 /* Reload value is slightly offset from the other timer. */
	CMSDK_TIMER0->RELOAD   = ( configCPU_CLOCK_HZ / tmrTIMER_0_FREQUENCY ) + 1UL;
	CMSDK_TIMER0->CTRL     = ( ( 1ul <<  3 ) | /* Enable Timer interrupt. */
						     ( 1ul <<  0 ) );  /* Enable Timer. */

	CMSDK_TIMER1->INTCLEAR = ( 1ul <<  0 );
	CMSDK_TIMER1->RELOAD   = ( configCPU_CLOCK_HZ / tmrTIMER_1_FREQUENCY ) + 1UL;
	CMSDK_TIMER1->CTRL     = ( ( 1ul <<  3 ) |
						     ( 1ul <<  0 ) );

	NVIC_SetPriority( TIMER0_IRQn, configMAX_SYSCALL_INTERRUPT_PRIORITY );
	NVIC_SetPriority( TIMER1_IRQn, configMAX_SYSCALL_INTERRUPT_PRIORITY + 1 );
	NVIC_EnableIRQ( TIMER0_IRQn );
	NVIC_EnableIRQ( TIMER1_IRQn );
}
/*-----------------------------------------------------------*/

