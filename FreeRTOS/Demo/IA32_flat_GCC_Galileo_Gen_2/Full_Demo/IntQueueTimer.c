/*
    FreeRTOS V8.2.2 - Copyright (C) 2015 Real Time Engineers Ltd.
    All rights reserved

    VISIT http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation >>!AND MODIFIED BY!<< the FreeRTOS exception.

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

