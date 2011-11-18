/*
    FreeRTOS V7.0.2 - Copyright (C) 2011 Real Time Engineers Ltd.


    ***************************************************************************
     *                                                                       *
     *    FreeRTOS tutorial books are available in pdf and paperback.        *
     *    Complete, revised, and edited pdf reference manuals are also       *
     *    available.                                                         *
     *                                                                       *
     *    Purchasing FreeRTOS documentation will not only help you, by       *
     *    ensuring you get running as quickly as possible and with an        *
     *    in-depth knowledge of how to use FreeRTOS, it will also help       *
     *    the FreeRTOS project to continue with its mission of providing     *
     *    professional grade, cross platform, de facto standard solutions    *
     *    for microcontrollers - completely free of charge!                  *
     *                                                                       *
     *    >>> See http://www.FreeRTOS.org/Documentation for details. <<<     *
     *                                                                       *
     *    Thank you for using FreeRTOS, and thank you for your support!      *
     *                                                                       *
    ***************************************************************************


    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation AND MODIFIED BY the FreeRTOS exception.
    >>>NOTE<<< The modification to the GPL is included to allow you to
    distribute a combined work that includes FreeRTOS without being obliged to
    provide the source code for proprietary components outside of the FreeRTOS
    kernel.  FreeRTOS is distributed in the hope that it will be useful, but
    WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
    or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
    more details. You should have received a copy of the GNU General Public
    License and the FreeRTOS license exception along with FreeRTOS; if not it
    can be viewed here: http://www.freertos.org/a00114.html and also obtained
    by writing to Richard Barry, contact details for whom are available on the
    FreeRTOS WEB site.

    1 tab == 4 spaces!

    http://www.FreeRTOS.org - Documentation, latest information, license and
    contact details.

    http://www.SafeRTOS.com - A version that is certified for use in safety
    critical systems.

    http://www.OpenRTOS.com - Commercial support, development, porting,
    licensing and training services.
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

#warning DOCUMENT THIS
/* This constant is specific to this test application.  It allows the high
frequency (interrupt nesting test) timer to know how often to trigger, and the
check task to know how many iterations to expect at any given time. */
#define tmrtestHIGH_FREQUENCY_TIMER_TEST_HZ		( 8931UL )

static void prvPortHighFrequencyTimerHandler( int iArg ) __attribute__((longcall));
static void prvHighFrequencyTimerTask( void *pvParameters );

static const unsigned long ulCompareMatchValue = configPERIPHERAL_CLOCK_HZ / tmrtestHIGH_FREQUENCY_TIMER_TEST_HZ;
static const unsigned long ulInterruptsPer10ms = tmrtestHIGH_FREQUENCY_TIMER_TEST_HZ / 100UL;
static const unsigned long ulSemaphoreGiveRate_ms = 10UL;

static xSemaphoreHandle xHighFrequencyTimerSemaphore = NULL;
static unsigned long ulHighFrequencyCounterIterations = 0UL;

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
	xTaskCreate( prvHighFrequencyTimerTask, ( signed char * ) "HFTmr", configMINIMAL_STACK_SIZE, NULL, configMAX_PRIORITIES - 1, NULL );
	
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
	*pulExpectedIncFrequency_ms = ulSemaphoreGiveRate_ms;
	return ulHighFrequencyCounterIterations;
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
		ulHighFrequencyCounterIterations++;
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
	
	portYIELD_FROM_ISR( ulHigherPriorityTaskWoken );
}
