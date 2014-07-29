/*
    FreeRTOS V8.0.1 - Copyright (C) 2014 Real Time Engineers Ltd.
    All rights reserved

    VISIT http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

    ***************************************************************************
     *                                                                       *
     *    FreeRTOS provides completely free yet professionally developed,    *
     *    robust, strictly quality controlled, supported, and cross          *
     *    platform software that has become a de facto standard.             *
     *                                                                       *
     *    Help yourself get started quickly and support the FreeRTOS         *
     *    project by purchasing a FreeRTOS tutorial book, reference          *
     *    manual, or both from: http://www.FreeRTOS.org/Documentation        *
     *                                                                       *
     *    Thank you!                                                         *
     *                                                                       *
    ***************************************************************************

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation >>!AND MODIFIED BY!<< the FreeRTOS exception.

    >>!   NOTE: The modification to the GPL is included to allow you to     !<<
    >>!   distribute a combined work that includes FreeRTOS without being   !<<
    >>!   obliged to provide the source code for proprietary components     !<<
    >>!   outside of the FreeRTOS kernel.                                   !<<

    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT ANY
    WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
    FOR A PARTICULAR PURPOSE.  Full license text is available from the following
    link: http://www.freertos.org/a00114.html

    1 tab == 4 spaces!

    ***************************************************************************
     *                                                                       *
     *    Having a problem?  Start by reading the FAQ "My application does   *
     *    not run, what could be wrong?"                                     *
     *                                                                       *
     *    http://www.FreeRTOS.org/FAQHelp.html                               *
     *                                                                       *
    ***************************************************************************

    http://www.FreeRTOS.org - Documentation, books, training, latest versions,
    license and Real Time Engineers Ltd. contact details.

    http://www.FreeRTOS.org/plus - A selection of FreeRTOS ecosystem products,
    including FreeRTOS+Trace - an indispensable productivity tool, a DOS
    compatible FAT file system, and our tiny thread aware UDP/IP stack.

    http://www.OpenRTOS.com - Real Time Engineers ltd license FreeRTOS to High
    Integrity Systems to sell under the OpenRTOS brand.  Low cost OpenRTOS
    licenses offer ticketed support, indemnification and middleware.

    http://www.SafeRTOS.com - High Integrity Systems also provide a safety
    engineered and independently SIL3 certified version for use in safety and
    mission critical applications that require provable dependability.

    1 tab == 4 spaces!
*/

/*
 * This file initialises three timers as follows:
 *
 * TC0 channels 0 and 1 provide the interrupts that are used with the IntQ
 * standard demo tasks, which test interrupt nesting and using queues from
 * interrupts.  As the interrupt is shared the nesting achieved is not as deep
 * as normal when this test is executed, but still worth while.
 *
 * TC2 channel 0 provides a much higher frequency timer that tests the nesting of
 * interrupts that execute above the maximum syscall interrupt priority.
 *
 * All the timers can nest with the tick interrupt - creating a maximum
 * interrupt nesting depth of 3 (normally 4, if the first two timers used
 * separate interrupts).
 *
 * For convenience, the high frequency timer is also used to provide the time
 * base for the run time stats.
 */

/* Scheduler includes. */
#include "FreeRTOS.h"

/* Demo includes. */
#include "IntQueueTimer.h"
#include "IntQueue.h"

/* Library includes. */
#include "board.h"

/* The frequencies at which the first two timers expire are slightly offset to
ensure they don't remain synchronised.  The frequency of the highest priority
interrupt is 20 times faster so really hammers the interrupt entry and exit
code. */
#define tmrTIMERS_USED	3
#define tmrTIMER_0_FREQUENCY	( 2000UL )
#define tmrTIMER_1_FREQUENCY	( 2003UL )
#define tmrTIMER_2_FREQUENCY	( 20000UL )

/* The channels used in TC0 for generating the three interrupts. */
#define tmrTC0_CHANNEL_0		0 /* At tmrTIMER_0_FREQUENCY */
#define tmrTC0_CHANNEL_1		1 /* At tmrTIMER_1_FREQUENCY */
#define tmrTC1_CHANNEL_0		0 /* At tmrTIMER_2_FREQUENCY */

/* The bit within the RC_SR register that indicates an RC compare. */
#define tmrRC_COMPARE			( 1UL << 4UL )

/* The high frequency interrupt given the highest priority or all.  The priority
of the lower frequency timers must still be above the tick interrupt priority. */
#define tmrLOWER_PRIORITY		1
#define tmrHIGHER_PRIORITY		5
/*-----------------------------------------------------------*/

/* Handlers for the three timer channels. */
static void prvTC0_Handler( void );
static void prvTC1_Handler( void );

/* Used to provide a means of ensuring the intended interrupt nesting depth is
actually being reached. */
extern uint32_t ulPortInterruptNesting;
static uint32_t ulMaxRecordedNesting = 0;

/* For convenience the high frequency timer increments a variable that is then
used as the time base for the run time stats. */
volatile uint32_t ulHighFrequencyTimerCounts = 0;

/*-----------------------------------------------------------*/

void vInitialiseTimerForIntQueueTest( void )
{
const uint32_t ulDivider = 128UL, ulTCCLKS = 3UL;

	/* Enable the TC clocks. */
	PMC->PMC_PCER0 = 1 << ID_TC0;
	PMC->PMC_PCER0 = 1 << ID_TC1;

	/* Configure TC0 channel 0 for a tmrTIMER_0_FREQUENCY frequency and trigger
	on RC compare. */
	TC_Configure( TC0, tmrTC0_CHANNEL_0, ulTCCLKS | TC_CMR_CPCTRG );
	TC0->TC_CHANNEL[ tmrTC0_CHANNEL_0 ].TC_RC = BOARD_MCK / ( tmrTIMER_0_FREQUENCY * ulDivider );
	TC0->TC_CHANNEL[ tmrTC0_CHANNEL_0 ].TC_IER = TC_IER_CPCS;

	/* Configure TC0 channel 1 for a tmrTIMER_1_FREQUENCY frequency and trigger
	on RC compare. */
	TC_Configure( TC0, tmrTC0_CHANNEL_1, ulTCCLKS | TC_CMR_CPCTRG );
	TC0->TC_CHANNEL[ tmrTC0_CHANNEL_1 ].TC_RC = BOARD_MCK / ( tmrTIMER_1_FREQUENCY * ulDivider );
	TC0->TC_CHANNEL[ tmrTC0_CHANNEL_1 ].TC_IER = TC_IER_CPCS;

	/* Configure TC1 channel 0 tmrTIMER_2_FREQUENCY frequency and trigger on
	RC compare. */
	TC_Configure( TC1, tmrTC1_CHANNEL_0, ulTCCLKS | TC_CMR_CPCTRG );
	TC1->TC_CHANNEL[ tmrTC1_CHANNEL_0 ].TC_RC = BOARD_MCK / ( tmrTIMER_2_FREQUENCY * ulDivider );
	TC1->TC_CHANNEL[ tmrTC1_CHANNEL_0 ].TC_IER = TC_IER_CPCS;

	/* Enable interrupts and start the timers. */
	IRQ_ConfigureIT( ID_TC0, tmrLOWER_PRIORITY, prvTC0_Handler );
	IRQ_ConfigureIT( ID_TC1, tmrHIGHER_PRIORITY, prvTC1_Handler );
	IRQ_EnableIT( ID_TC0 );
	IRQ_EnableIT( ID_TC1 );
	TC_Start( TC0, tmrTC0_CHANNEL_0 );
	TC_Start( TC0, tmrTC0_CHANNEL_1 );
	TC_Start( TC1, tmrTC1_CHANNEL_0 );
}
/*-----------------------------------------------------------*/

static void prvTC0_Handler( void )
{
#warning Why can interrupts only be enabled inside the C function?
	__enable_interrupt();

    /* Read will clear the status bit. */
	if( ( TC0->TC_CHANNEL[ tmrTC0_CHANNEL_0 ].TC_SR & tmrRC_COMPARE ) != 0 )
	{
		portYIELD_FROM_ISR( xFirstTimerHandler() );
	}

	if( ( TC0->TC_CHANNEL[ tmrTC0_CHANNEL_1 ].TC_SR & tmrRC_COMPARE ) != 0 )
	{
		portYIELD_FROM_ISR( xSecondTimerHandler() );
	}
}
/*-----------------------------------------------------------*/

static void prvTC1_Handler( void )
{
volatile uint32_t ulDummy;

	__enable_interrupt();

    /* Dummy read to clear status bit. */
    ulDummy = TC1->TC_CHANNEL[ tmrTC1_CHANNEL_0 ].TC_SR;

	/* Latch the maximum nesting count. */
	if( ulPortInterruptNesting > ulMaxRecordedNesting )
	{
		ulMaxRecordedNesting = ulPortInterruptNesting;
	}

	/* Keep a count of the number of interrupts to use as a time base for the
	run-time stats. */
	ulHighFrequencyTimerCounts++;
}

