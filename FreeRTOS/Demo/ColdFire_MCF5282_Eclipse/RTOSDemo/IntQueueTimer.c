/*
    FreeRTOS V7.1.1 - Copyright (C) 2012 Real Time Engineers Ltd.
	

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
    
    ***************************************************************************
     *                                                                       *
     *    Having a problem?  Start by reading the FAQ "My application does   *
     *    not run, what could be wrong?                                      *
     *                                                                       *
     *    http://www.FreeRTOS.org/FAQHelp.html                               *
     *                                                                       *
    ***************************************************************************

    
    http://www.FreeRTOS.org - Documentation, training, latest information, 
    license and contact details.
    
    http://www.FreeRTOS.org/plus - A selection of FreeRTOS ecosystem products,
    including FreeRTOS+Trace - an indispensable productivity tool.

    Real Time Engineers ltd license FreeRTOS to High Integrity Systems, who sell 
    the code with commercial support, indemnification, and middleware, under 
    the OpenRTOS brand: http://www.OpenRTOS.com.  High Integrity Systems also
    provide a safety engineered and independently SIL3 certified version under 
    the SafeRTOS brand: http://www.SafeRTOS.com.
*/

#include "FreeRTOS.h"
#include "IntQueueTimer.h"
#include "IntQueue.h"

#define timerINTERRUPT1_FREQUENCY	( 2000UL )
#define timerINTERRUPT2_FREQUENCY	( 2001UL )
#define timerPRESCALE_VALUE			( 2 )

void vInitialiseTimerForIntQueueTest( void )
{
const unsigned portSHORT usCompareMatchValue1 = ( unsigned portSHORT ) ( ( configCPU_CLOCK_HZ / timerPRESCALE_VALUE ) / timerINTERRUPT1_FREQUENCY );
const unsigned portSHORT usCompareMatchValue2 = ( unsigned portSHORT ) ( ( configCPU_CLOCK_HZ / timerPRESCALE_VALUE ) / timerINTERRUPT2_FREQUENCY );

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
