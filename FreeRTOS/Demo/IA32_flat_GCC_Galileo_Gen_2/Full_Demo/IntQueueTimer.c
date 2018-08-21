/*
 * FreeRTOS Kernel V10.1.0
 * Copyright (C) 2017 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 * Provides the port specific part of the standard IntQ test, which is
 * implemented in FreeRTOS/Demo/Common/Minimal/IntQueue.c.  Three HPET timers
 * are used to generate the interrupts.  The timers are configured in
 * prvSetupHardware(), in main.c.
 */


/* Scheduler includes. */
#include "FreeRTOS.h"

/* Demo includes. */
#include "IntQueueTimer.h"
#include "IntQueue.h"

/*
 * Prototypes of the callback functions which are called from the HPET timer
 * support file.  For demonstration purposes, timer 0 and timer 1 are standard
 * C functions that use the central interrupt handler, and are installed using
 * xPortRegisterCInterruptHandler() - and timer 2 uses its own interrupt entry
 * asm wrapper code and is installed using xPortInstallInterruptHandler().  For
 * convenience the asm wrapper which calls vApplicationHPETTimer1Handler(), is
 * implemented in RegTest.S.  See
 * http://www.freertos.org/RTOS_Intel_Quark_Galileo_GCC.html#interrupts for more
 * details.
 */
void vApplicationHPETTimer0Handler( void );
void vApplicationHPETTimer1Handler( void );
void vApplicationHPETTimer2Handler( void );

/*
 * Set to pdTRUE when vInitialiseTimerForIntQueueTest() is called so the timer
 * callback functions know the scheduler is running and the tests can run.
 */
static volatile BaseType_t xSchedulerRunning = pdFALSE;

/* Used to count the nesting depth to ensure the test is testing what it is
intended to test. */
static volatile uint32_t ulMaxInterruptNesting = 0;
extern volatile uint32_t ulInterruptNesting;

/*-----------------------------------------------------------*/

void vInitialiseTimerForIntQueueTest( void )
{
	/* The HPET timers are set up in main(), before the scheduler is started,
	so there is nothing to do here other than note the scheduler is now running.
	This could be done by calling a FreeRTOS API function, but its convenient
	and efficient just to store the fact in a file scope variable. */
	xSchedulerRunning = pdTRUE;
}
/*-----------------------------------------------------------*/

void vApplicationHPETTimer0Handler( void )
{
BaseType_t xHigherPriorityTaskWoken;

	if( xSchedulerRunning != pdFALSE )
	{
		if( ulInterruptNesting > ulMaxInterruptNesting )
		{
			ulMaxInterruptNesting = ulInterruptNesting;
		}

		xHigherPriorityTaskWoken = xFirstTimerHandler();
		portYIELD_FROM_ISR( xHigherPriorityTaskWoken );
	}
}
/*-----------------------------------------------------------*/

void vApplicationHPETTimer1Handler( void )
{
BaseType_t xHigherPriorityTaskWoken;

	if( xSchedulerRunning != pdFALSE )
	{
		if( ulInterruptNesting > ulMaxInterruptNesting )
		{
			ulMaxInterruptNesting = ulInterruptNesting;
		}

		xHigherPriorityTaskWoken = xSecondTimerHandler();
		portYIELD_FROM_ISR( xHigherPriorityTaskWoken );
	}
}
/*-----------------------------------------------------------*/

void vApplicationHPETTimer2Handler( void )
{
	if( ulInterruptNesting > ulMaxInterruptNesting )
	{
		ulMaxInterruptNesting = ulInterruptNesting;
	}
}

