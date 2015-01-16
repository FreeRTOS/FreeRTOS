/*
    FreeRTOS V8.2.0 - Copyright (C) 2015 Real Time Engineers Ltd.
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

#include "FreeRTOS.h"
#include "IntQueueTimer.h"
#include "IntQueue.h"

#define timerINTERRUPT1_FREQUENCY	( 2000UL )
#define timerINTERRUPT2_FREQUENCY	( 2001UL )
#define timerPRESCALE_VALUE			( 2 )

void vInitialiseTimerForIntQueueTest( void )
{
const unsigned short usCompareMatchValue1 = ( unsigned short ) ( ( configCPU_CLOCK_HZ / timerPRESCALE_VALUE ) / timerINTERRUPT1_FREQUENCY );
const unsigned short usCompareMatchValue2 = ( unsigned short ) ( ( configCPU_CLOCK_HZ / timerPRESCALE_VALUE ) / timerINTERRUPT2_FREQUENCY );

	/* Configure interrupt priority and level and unmask interrupt. */
	MCF_INTC0_ICR56 = ( ( configMAX_SYSCALL_INTERRUPT_PRIORITY - 1 ) << 3 );
	MCF_INTC0_IMRH &= ~( MCF_INTC_IMRH_INT_MASK56 );

	MCF_PIT1_PCSR |= MCF_PIT_PCSR_PIF;
	MCF_PIT1_PCSR = ( MCF_PIT_PCSR_PIE | MCF_PIT_PCSR_RLD | MCF_PIT_PCSR_EN );
	MCF_PIT1_PMR = usCompareMatchValue1;

	MCF_INTC0_ICR57 = ( configMAX_SYSCALL_INTERRUPT_PRIORITY << 3 );
	MCF_INTC0_IMRH &= ~( MCF_INTC_IMRH_INT_MASK57 );

	MCF_PIT2_PCSR |= MCF_PIT_PCSR_PIF;
	MCF_PIT2_PCSR = ( MCF_PIT_PCSR_PIE | MCF_PIT_PCSR_RLD | MCF_PIT_PCSR_EN );
	MCF_PIT2_PMR = usCompareMatchValue2;
}
/*-----------------------------------------------------------*/

void __attribute__ ((interrupt)) __cs3_isr_interrupt_120( void )
{
	MCF_PIT1_PCSR |= MCF_PIT_PCSR_PIF;
	portEND_SWITCHING_ISR( xFirstTimerHandler() );
}
/*-----------------------------------------------------------*/

void __attribute__ ((interrupt)) __cs3_isr_interrupt_121( void )
{
	MCF_PIT2_PCSR |= MCF_PIT_PCSR_PIF;
	portEND_SWITCHING_ISR( xSecondTimerHandler() );
}
