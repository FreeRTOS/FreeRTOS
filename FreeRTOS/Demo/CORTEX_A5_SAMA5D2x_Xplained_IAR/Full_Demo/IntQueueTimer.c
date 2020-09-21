/*
 * FreeRTOS Kernel V10.3.0
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
 * TC0 channels 0 and 1 provide the interrupts that are used with the IntQ
 * standard demo tasks, which test interrupt nesting and using queues from
 * interrupts.  As the interrupt is shared the nesting achieved is not as deep
 * as normal when this test is executed, but still worth while.
 *
 * TC2 channel 0 provides a much higher frequency timer that tests the nesting
 * of interrupts that don't use the FreeRTOS API.  For convenience, the high
 * frequency timer also keeps a count of the number of time it executes, and the
 * count is used as the time base for the run time stats (which can be viewed
 * through the CLI).
 *
 * All the timers can nest with the tick interrupt - creating a maximum
 * interrupt nesting depth of 3 (normally 4, if the first two timers used
 * separate interrupts).
 *
 */

/* Scheduler includes. */
#include "FreeRTOS.h"

/* Demo includes. */
#include "IntQueueTimer.h"
#include "IntQueue.h"

/* Library includes. */
#include "peripherals/pio.h"
#include "peripherals/pmc.h"
#include "peripherals/aic.h"
#include "peripherals/tc.h"
#include "board.h"

/* The frequencies at which the first two timers expire are slightly offset to
ensure they don't remain synchronised.  The frequency of the highest priority
interrupt is 20 times faster so really hammers the interrupt entry and exit
code. */
#define tmrTIMER_0_FREQUENCY	( 2000UL )
#define tmrTIMER_1_FREQUENCY	( 1690UL )
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

/* Handlers for the two timer peripherals - two channels are used in the TC0
timer. */
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
	/* Enable the TC clocks. */
	pmc_enable_peripheral( ID_TC0 );
	pmc_enable_peripheral( ID_TC1 );

	/* Configure TC0 channel 0 for a tmrTIMER_0_FREQUENCY frequency and trigger
	on RC compare. */
	tc_trigger_on_freq( TC0, tmrTC0_CHANNEL_0, tmrTIMER_0_FREQUENCY );
	TC0->TC_CHANNEL[ tmrTC0_CHANNEL_0 ].TC_IER = TC_IER_CPCS;

	/* Configure TC0 channel 1 for a tmrTIMER_1_FREQUENCY frequency and trigger
	on RC compare. */
	tc_trigger_on_freq( TC0, tmrTC0_CHANNEL_1, tmrTIMER_1_FREQUENCY );
	TC0->TC_CHANNEL[ tmrTC0_CHANNEL_1 ].TC_IER = TC_IER_CPCS;

	/* Configure TC1 channel 0 tmrTIMER_2_FREQUENCY frequency and trigger on
	RC compare. */
	tc_trigger_on_freq( TC1, tmrTC1_CHANNEL_0, tmrTIMER_2_FREQUENCY );
	TC1->TC_CHANNEL[ tmrTC1_CHANNEL_0 ].TC_IER = TC_IER_CPCS;

	/* Enable interrupts and start the timers. */
	aic_configure( ID_TC0, tmrLOWER_PRIORITY );
	aic_set_source_vector( ID_TC0, prvTC0_Handler );
	aic_configure( ID_TC1, tmrHIGHER_PRIORITY );
	aic_set_source_vector( ID_TC1, prvTC1_Handler );
	aic_enable( ID_TC0 );
	aic_enable( ID_TC1 );
	tc_start( TC0, tmrTC0_CHANNEL_0 );
	tc_start( TC0, tmrTC0_CHANNEL_1 );
	tc_start( TC1, tmrTC1_CHANNEL_0 );
}
/*-----------------------------------------------------------*/

static void prvTC0_Handler( void )
{
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

