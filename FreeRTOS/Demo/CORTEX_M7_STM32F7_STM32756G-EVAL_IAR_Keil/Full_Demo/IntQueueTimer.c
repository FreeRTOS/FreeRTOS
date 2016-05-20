/*
    FreeRTOS V9.0.0 - Copyright (C) 2016 Real Time Engineers Ltd.
    All rights reserved

    VISIT http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation >>>> AND MODIFIED BY <<<< the FreeRTOS exception.

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

