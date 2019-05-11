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

/*
 * This file initialises three timers as follows:
 *
 * TIM2 and TIM3 provide the interrupts that are used with the IntQ
 * standard demo tasks, which test interrupt nesting and using queues from
 * interrupts.  The timers generate interrupts at slightly different
 * frequencies and use different priorities, resulting in a nesting depth of
 * three (including the tick and PendSV interrupts, which run at lower
 * priorities).
 *
 * TIM4 provides a much higher frequency timer that tests the nesting
 * of interrupts that don't use the FreeRTOS API.  For convenience, the high
 * frequency timer also keeps a count of the number of times it executes, and
 * the count can be used as the time base for the run time stats.
 *
 * All the timers can nest with the tick interrupt - creating a maximum
 * interrupt nesting depth of 4.
 *
 */

/* Scheduler includes. */
#include "FreeRTOS.h"

/* Demo includes. */
#include "IntQueueTimer.h"
#include "IntQueue.h"

/* The frequencies at which the first two timers expire are slightly offset to
ensure they don't remain synchronised.  The frequency of the highest priority
interrupt is 20 times faster so really hammers the interrupt entry and exit
code. */
#define tmrTIMER_2_FREQUENCY	( 2000UL )
#define tmrTIMER_3_FREQUENCY	( 2003UL )
#define tmrTIMER_4_FREQUENCY	( 20000UL )

/* The high frequency interrupt given a priority above the maximum at which
interrupt safe FreeRTOS calls can be made.  The priority of the lower frequency
timers must still be above the tick interrupt priority. */
#define tmrLOWER_PRIORITY		configLIBRARY_MAX_SYSCALL_INTERRUPT_PRIORITY + 1
#define tmrMEDIUM_PRIORITY		configLIBRARY_MAX_SYSCALL_INTERRUPT_PRIORITY
#define tmrHIGHER_PRIORITY		configLIBRARY_MAX_SYSCALL_INTERRUPT_PRIORITY - 1
/*-----------------------------------------------------------*/

/* For convenience the high frequency timer increments a variable that is then
used as the time base for the run time stats. */
volatile uint32_t ulHighFrequencyTimerCounts = 0;

/*-----------------------------------------------------------*/

void vInitialiseTimerForIntQueueTest( void )
{
TIM_HandleTypeDef    xTimHandle;
const uint32_t ulPrescale = 0; /* No prescale. */

	/* Clock the utilised timers. */
	__TIM2_CLK_ENABLE();
	__TIM3_CLK_ENABLE();
	__TIM4_CLK_ENABLE();

	/* Configure TIM2 to generate an interrupt at the required frequency. */
	xTimHandle.Instance = TIM2;
	xTimHandle.Init.Period = ( SystemCoreClock / 2UL ) / ( tmrTIMER_2_FREQUENCY - 1 );
	xTimHandle.Init.Prescaler = ulPrescale;
	xTimHandle.Init.ClockDivision = 0;
	xTimHandle.Init.CounterMode = TIM_COUNTERMODE_UP;
	HAL_TIM_Base_Init( &xTimHandle );
	HAL_TIM_Base_Start_IT( &xTimHandle );

    /* Configure and enable TIM2 interrupt. */
	NVIC_SetPriority( TIM2_IRQn, tmrLOWER_PRIORITY );
    NVIC_ClearPendingIRQ( TIM2_IRQn );
    NVIC_EnableIRQ( TIM2_IRQn );

	/* Repeat for TIM3 and TIM4. */
	xTimHandle.Instance = TIM3;
	xTimHandle.Init.Period = ( SystemCoreClock / 2UL ) / ( tmrTIMER_3_FREQUENCY - 1 );
	HAL_TIM_Base_Init( &xTimHandle );
	HAL_TIM_Base_Start_IT( &xTimHandle );
	NVIC_SetPriority( TIM3_IRQn, tmrMEDIUM_PRIORITY );
    NVIC_ClearPendingIRQ( TIM3_IRQn );
    NVIC_EnableIRQ( TIM3_IRQn );

	xTimHandle.Instance = TIM4;
	xTimHandle.Init.Period = ( SystemCoreClock / 2UL ) / ( tmrTIMER_4_FREQUENCY - 1 );
	HAL_TIM_Base_Init( &xTimHandle );
	HAL_TIM_Base_Start_IT( &xTimHandle );
	NVIC_SetPriority( TIM4_IRQn, tmrHIGHER_PRIORITY );
    NVIC_ClearPendingIRQ( TIM4_IRQn );
    NVIC_EnableIRQ( TIM4_IRQn );
}
/*-----------------------------------------------------------*/

void TIM2_IRQHandler( void )
{
	/* Clear the interrupt and call the IntQTimer test function. */
	TIM2->SR = 0;
	portYIELD_FROM_ISR( xFirstTimerHandler() );
}
/*-----------------------------------------------------------*/

void TIM3_IRQHandler( void )
{
	/* Clear the interrupt and call the IntQTimer test function. */
	TIM3->SR = 0;
	portYIELD_FROM_ISR( xSecondTimerHandler() );
}
/*-----------------------------------------------------------*/

void TIM4_IRQHandler( void )
{
	TIM4->SR = 0;

	/* Keep a count of the number of interrupts to use as a time base for the
	run-time stats. */
	ulHighFrequencyTimerCounts++;
}

