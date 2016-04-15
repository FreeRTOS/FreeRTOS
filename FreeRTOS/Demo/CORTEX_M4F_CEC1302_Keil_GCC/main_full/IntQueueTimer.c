/*
    FreeRTOS V8.2.3 - Copyright (C) 2015 Real Time Engineers Ltd.
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

/* Hardware register locations. */
#define tmrGIRQ23_ENABLE_SET			( * ( volatile uint32_t * ) 0x4000C130 )

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

	tmrGIRQ23_ENABLE_SET = 0x03;

	/* Initialise the three timers as described at the top of this file, and
	enable their interrupts in the NVIC. */
	btimer_init( tmrTIMER_CHANNEL_0, BTIMER_AUTO_RESTART | BTIMER_COUNT_DOWN | BTIMER_INT_EN, 0, ulTimer0Count, ulTimer0Count );
	btimer_interrupt_status_get_clr( tmrTIMER_CHANNEL_0 );
	enable_timer0_irq();
	NVIC_SetPriority( TIMER0_IRQn, tmrLOWER_PRIORITY ); //0xc0 into 0xe000e431
	NVIC_ClearPendingIRQ( TIMER0_IRQn );
	NVIC_EnableIRQ( TIMER0_IRQn );
	btimer_start( tmrTIMER_CHANNEL_0 );

	btimer_init( tmrTIMER_CHANNEL_1, BTIMER_AUTO_RESTART | BTIMER_COUNT_DOWN | BTIMER_INT_EN, 0, ulTimer1Count, ulTimer1Count );
	btimer_interrupt_status_get_clr( tmrTIMER_CHANNEL_1 );
	enable_timer1_irq();
	NVIC_SetPriority( TIMER1_IRQn, tmrMEDIUM_PRIORITY ); //0xa0 into 0xe000e432
	NVIC_ClearPendingIRQ( TIMER1_IRQn );
	NVIC_EnableIRQ( TIMER1_IRQn );
	btimer_start( tmrTIMER_CHANNEL_1 );

	btimer_init( tmrTIMER_CHANNEL_2, BTIMER_AUTO_RESTART | BTIMER_COUNT_DOWN | BTIMER_INT_EN, 0, ulTimer2Count, ulTimer2Count );
	btimer_interrupt_status_get_clr( tmrTIMER_CHANNEL_2 );
	enable_timer2_irq();
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

