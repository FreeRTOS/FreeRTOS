/*
 * FreeRTOS Kernel V10.4.1
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
 * This file initialises three timers as follows:
 *
 * Basic timer channels 0 and 1 provide the interrupts that are used with the
 * IntQ standard demo tasks, which test interrupt nesting and using queues from
 * interrupts.  The interrupts use slightly different frequencies so will
 * occasionally nest.
 *
 * Basic timer channel 2 provides a much higher frequency timer that tests the
 * nesting of interrupts that don't use the FreeRTOS API.
 *
 * All the timers can nest with the tick interrupt - creating a maximum
 * interrupt nesting depth of 4 (which is shown as a max nest count of 3 as the
 * tick interrupt does not increment the nesting count variable).
 *
 */

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "task.h"

/* Demo includes. */
#include "IntQueueTimer.h"
#include "IntQueue.h"

/* Library includes. */
#include "common_lib.h"
#include "peripheral_library/interrupt/interrupt.h"
#include "peripheral_library/basic_timer/btimer.h"

/* The frequencies at which the first two timers expire are slightly offset to
ensure they don't remain synchronised.  The frequency of the highest priority
interrupt is 20 times faster so really hammers the interrupt entry and exit
code. */
#define tmrTIMER_0_FREQUENCY	( 2000UL )
#define tmrTIMER_1_FREQUENCY	( 2003UL )
#define tmrTIMER_2_FREQUENCY	( 20000UL )

/* The basic timer channels used for generating the three interrupts. */
#define tmrTIMER_CHANNEL_0		0 /* At tmrTIMER_0_FREQUENCY */
#define tmrTIMER_CHANNEL_1		1 /* At tmrTIMER_1_FREQUENCY */
#define tmrTIMER_CHANNEL_2		2 /* At tmrTIMER_2_FREQUENCY */

/* The high frequency interrupt is given a priority above the maximum at which
interrupt safe FreeRTOS calls can be made.  The priority of the lower frequency
timers must still be above the tick interrupt priority. */
#define tmrLOWER_PRIORITY		( configLIBRARY_MAX_SYSCALL_INTERRUPT_PRIORITY + 1 )
#define tmrMEDIUM_PRIORITY		( configLIBRARY_MAX_SYSCALL_INTERRUPT_PRIORITY + 0 )
#define tmrHIGHER_PRIORITY		( configLIBRARY_MAX_SYSCALL_INTERRUPT_PRIORITY - 1 )

/* Hardware register locations and bit definitions to enable the btimer 
interrupts. */
#define tmrGIRQ23_ENABLE_SET	( * ( volatile uint32_t * ) 0x4000C130 )
#define tmrGIRQ23_BIT_TIMER0	( 1UL << 0UL )
#define tmrGIRQ23_BIT_TIMER1	( 1UL << 1UL )
#define tmrGIRQ23_BIT_TIMER2	( 1UL << 2UL )
#define tmrGIRQ23_TIMER_BITS	( tmrGIRQ23_BIT_TIMER0 | tmrGIRQ23_BIT_TIMER1 | tmrGIRQ23_BIT_TIMER2 )

#define tmrRECORD_NESTING_DEPTH()						\
	ulNestingDepth++;									\
	if( ulNestingDepth > ulMaxRecordedNestingDepth )	\
	{													\
		ulMaxRecordedNestingDepth = ulNestingDepth;		\
	}

/* Used to count the nesting depth, and record the maximum nesting depth. */
volatile uint32_t ulNestingDepth = 0, ulMaxRecordedNestingDepth = 0;

/*-----------------------------------------------------------*/

void vInitialiseTimerForIntQueueTest( void )
{
const uint32_t ulTimer0Count = configCPU_CLOCK_HZ / tmrTIMER_0_FREQUENCY;
const uint32_t ulTimer1Count = configCPU_CLOCK_HZ / tmrTIMER_1_FREQUENCY;
const uint32_t ulTimer2Count = configCPU_CLOCK_HZ / tmrTIMER_2_FREQUENCY;

	tmrGIRQ23_ENABLE_SET = tmrGIRQ23_TIMER_BITS;

	/* Initialise the three timers as described at the top of this file, and
	enable their interrupts in the NVIC. */
	btimer_init( tmrTIMER_CHANNEL_0, BTIMER_AUTO_RESTART | BTIMER_COUNT_DOWN | BTIMER_INT_EN, 0, ulTimer0Count, ulTimer0Count );
	btimer_interrupt_status_get_clr( tmrTIMER_CHANNEL_0 );
	NVIC_SetPriority( TIMER0_IRQn, tmrLOWER_PRIORITY ); //0xc0 into 0xe000e431
	NVIC_ClearPendingIRQ( TIMER0_IRQn );
	NVIC_EnableIRQ( TIMER0_IRQn );
	btimer_start( tmrTIMER_CHANNEL_0 );

	btimer_init( tmrTIMER_CHANNEL_1, BTIMER_AUTO_RESTART | BTIMER_COUNT_DOWN | BTIMER_INT_EN, 0, ulTimer1Count, ulTimer1Count );
	btimer_interrupt_status_get_clr( tmrTIMER_CHANNEL_1 );
	NVIC_SetPriority( TIMER1_IRQn, tmrMEDIUM_PRIORITY ); //0xa0 into 0xe000e432
	NVIC_ClearPendingIRQ( TIMER1_IRQn );
	NVIC_EnableIRQ( TIMER1_IRQn );
	btimer_start( tmrTIMER_CHANNEL_1 );

	btimer_init( tmrTIMER_CHANNEL_2, BTIMER_AUTO_RESTART | BTIMER_COUNT_DOWN | BTIMER_INT_EN, 0, ulTimer2Count, ulTimer2Count );
	btimer_interrupt_status_get_clr( tmrTIMER_CHANNEL_2 );
	NVIC_SetPriority( TIMER2_IRQn, tmrHIGHER_PRIORITY );
	NVIC_ClearPendingIRQ( TIMER2_IRQn );
	NVIC_EnableIRQ( TIMER2_IRQn );
	btimer_start( tmrTIMER_CHANNEL_2 );
}
/*-----------------------------------------------------------*/

/* The TMR0 interrupt is used for different purposes by the low power and full
demos respectively. */
#if( configCREATE_LOW_POWER_DEMO == 0 )

	void NVIC_Handler_TMR0( void )
	{
		tmrRECORD_NESTING_DEPTH();

		/* Call the IntQ test function for this channel. */
		portYIELD_FROM_ISR( xFirstTimerHandler() );

		ulNestingDepth--;
	}

#endif /* configCREATE_LOW_POWER_DEMO */
/*-----------------------------------------------------------*/

void NVIC_Handler_TMR1( void )
{
	tmrRECORD_NESTING_DEPTH();

	/* Just testing the xPortIsInsideInterrupt() functionality. */
	configASSERT( xPortIsInsideInterrupt() == pdTRUE );

	/* Call the IntQ test function for this channel. */
	portYIELD_FROM_ISR( xSecondTimerHandler() );

	ulNestingDepth--;
}
/*-----------------------------------------------------------*/

void NVIC_Handler_TMR2( void )
{
	tmrRECORD_NESTING_DEPTH();
	ulNestingDepth--;
}
/*-----------------------------------------------------------*/

