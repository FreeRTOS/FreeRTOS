/*
 * FreeRTOS V202012.00
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
 * It is intended that the tasks and timers in this file cause interrupts to
 * nest at least one level deeper than they would otherwise.
 *
 * A timer is configured to create an interrupt at moderately high frequency,
 * as defined by the tmrtestHIGH_FREQUENCY_TIMER_TEST_HZ constant.  The
 * interrupt priority is by configHIGH_FREQUENCY_TIMER_PRIORITY, which is set
 * to ( configMAX_SYSCALL_INTERRUPT_PRIORITY - 1UL ), the second highest
 * priority from which interrupt safe FreeRTOS API calls can be made.
 *
 * The timer interrupt handler counts the number of times it is called.  When
 * it has determined that the number of calls means that 10ms has passed, it
 * 'gives' a semaphore, and resets it call count.
 *
 * A high priority task is used to receive the data posted to the queue by the
 * interrupt service routine.  The task should, then, leave the blocked state
 * and 'take' the available semaphore every 10ms.  The frequency at which it
 * actually leaves the blocked state is verified by the demo's check task (see
 * the the documentation for the entire demo on the FreeRTOS.org web site),
 * which then flags an error if the frequency lower than expected.
 */

/* Standard includes. */
#include <stdlib.h>
#include <string.h>

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "semphr.h"

/* Demo application includes. */
#include "InterruptNestTest.h"

/* TriCore specific includes. */
#include <tc1782.h>
#include <machine/intrinsics.h>
#include <machine/cint.h>
#include <machine/wdtcon.h>

/* This constant is specific to this test application.  It allows the high
frequency (interrupt nesting test) timer to know how often to trigger, and the
check task to know how many iterations to expect at any given time. */
#define tmrtestHIGH_FREQUENCY_TIMER_TEST_HZ		( 8931UL )

/*
 * The handler for the high priority timer interrupt.
 */
static void prvPortHighFrequencyTimerHandler( int iArg ) __attribute__((longcall));

/*
 * The task that receives messages posted to a queue by the higher priority
 * timer interrupt.
 */
static void prvHighFrequencyTimerTask( void *pvParameters );

/* Constants used to configure the timer and determine how often the task
should receive data. */
static const unsigned long ulCompareMatchValue = configPERIPHERAL_CLOCK_HZ / tmrtestHIGH_FREQUENCY_TIMER_TEST_HZ;
static const unsigned long ulInterruptsPer10ms = tmrtestHIGH_FREQUENCY_TIMER_TEST_HZ / 100UL;
static const unsigned long ulSemaphoreGiveRate_ms = 10UL;

/* The semaphore used to synchronise the interrupt with the task. */
static SemaphoreHandle_t xHighFrequencyTimerSemaphore = NULL;

/* Holds the count of the number of times the task is unblocked by the timer. */
static volatile unsigned long ulHighFrequencyTaskIterations = 0UL;

/*-----------------------------------------------------------*/

void vSetupInterruptNestingTest( void )
{
unsigned long ulCompareMatchBits;

	/* Create the semaphore used to communicate between the high frequency
	interrupt and the task. */
	vSemaphoreCreateBinary( xHighFrequencyTimerSemaphore );
	configASSERT( xHighFrequencyTimerSemaphore );
	
	/* Create the task that pends on the semaphore that is given by the
	high frequency interrupt. */
	xTaskCreate( prvHighFrequencyTimerTask, "HFTmr", configMINIMAL_STACK_SIZE, NULL, configMAX_PRIORITIES - 1, NULL );
	
	/* Setup the interrupt itself.	The STM module clock divider is setup when 
	the tick interrupt is configured - which is when the scheduler is started - 
	so there is no need	to do it here.

	The tick interrupt uses compare match 0, so this test uses compare match
	1, which means shifting up the values by 16 before writing them to the
	register. */
	ulCompareMatchBits = ( 0x1fUL - __CLZ( ulCompareMatchValue ) );
	ulCompareMatchBits <<= 16UL;
	
	/* Write the values to the relevant SMT registers, without changing other
	bits. */
	taskENTER_CRITICAL();
	{
		STM_CMCON.reg &= ~( 0x1fUL << 16UL );
		STM_CMCON.reg |= ulCompareMatchBits;
		STM_CMP1.reg = ulCompareMatchValue;

		if( 0 != _install_int_handler( configHIGH_FREQUENCY_TIMER_PRIORITY, prvPortHighFrequencyTimerHandler, 0 ) )
		{
			/* Set-up the interrupt. */
			STM_SRC1.reg = ( configHIGH_FREQUENCY_TIMER_PRIORITY | 0x00005000UL );
	
			/* Enable the Interrupt. */
			STM_ISRR.reg &= ~( 0x03UL << 2UL );
			STM_ISRR.reg |= ( 0x1UL << 2UL );
			STM_ICR.reg &= ~( 0x07UL << 4UL );
			STM_ICR.reg |= ( 0x5UL << 4UL );
		}
		else
		{
			/* Failed to install the interrupt. */
			configASSERT( ( ( volatile void * ) NULL ) );
		}
	}
	taskEXIT_CRITICAL();
}
/*-----------------------------------------------------------*/

unsigned long ulInterruptNestingTestGetIterationCount( unsigned long *pulExpectedIncFrequency_ms )
{
unsigned long ulReturn;

	*pulExpectedIncFrequency_ms = ulSemaphoreGiveRate_ms;
	portENTER_CRITICAL();
	{
		ulReturn = ulHighFrequencyTaskIterations;
		ulHighFrequencyTaskIterations = 0UL;
	}

	return ulReturn;
}
/*-----------------------------------------------------------*/

static void prvHighFrequencyTimerTask( void *pvParameters )
{
	/* Just to remove compiler warnings about the unused parameter. */
	( void ) pvParameters;

	for( ;; )
	{
		/* Wait for the next trigger from the high frequency timer interrupt. */
		xSemaphoreTake( xHighFrequencyTimerSemaphore, portMAX_DELAY );
		
		/* Just count how many times the task has been unblocked before
		returning to wait for the semaphore again. */
		ulHighFrequencyTaskIterations++;
	}
}
/*-----------------------------------------------------------*/

static void prvPortHighFrequencyTimerHandler( int iArg )
{
static volatile unsigned long ulExecutionCounter = 0UL;
unsigned long ulHigherPriorityTaskWoken = pdFALSE;

	/* Just to avoid compiler warnings about unused parameters. */
	( void ) iArg;

	/* Clear the interrupt source. */
	STM_ISRR.reg = 1UL << 2UL;

	/* Reload the Compare Match register for X ticks into the future.*/
	STM_CMP1.reg += ulCompareMatchValue;

	ulExecutionCounter++;
	
	if( ulExecutionCounter >= ulInterruptsPer10ms )
	{
		ulExecutionCounter = xSemaphoreGiveFromISR( xHighFrequencyTimerSemaphore, &ulHigherPriorityTaskWoken );
		
		/* If the semaphore was given ulExeuctionCounter will now be pdTRUE. */
		configASSERT( ulExecutionCounter == pdTRUE );
		
		/* Start counting again. */
		ulExecutionCounter = 0UL;
	}
	
	/* Context switch on exit if necessary. */
	portYIELD_FROM_ISR( ulHigherPriorityTaskWoken );
}
