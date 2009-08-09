/*
	FreeRTOS V5.4.2 - Copyright (C) 2009 Real Time Engineers Ltd.

	This file is part of the FreeRTOS distribution.

	FreeRTOS is free software; you can redistribute it and/or modify it	under 
	the terms of the GNU General Public License (version 2) as published by the 
	Free Software Foundation and modified by the FreeRTOS exception.
	**NOTE** The exception to the GPL is included to allow you to distribute a
	combined work that includes FreeRTOS without being obliged to provide the 
	source code for proprietary components outside of the FreeRTOS kernel.  
	Alternative commercial license and support terms are also available upon 
	request.  See the licensing section of http://www.FreeRTOS.org for full 
	license details.

	FreeRTOS is distributed in the hope that it will be useful,	but WITHOUT
	ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
	FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
	more details.

	You should have received a copy of the GNU General Public License along
	with FreeRTOS; if not, write to the Free Software Foundation, Inc., 59
	Temple Place, Suite 330, Boston, MA  02111-1307  USA.


	***************************************************************************
	*                                                                         *
	* Looking for a quick start?  Then check out the FreeRTOS eBook!          *
	* See http://www.FreeRTOS.org/Documentation for details                   *
	*                                                                         *
	***************************************************************************

	1 tab == 4 spaces!

	Please ensure to read the configuration and relevant port sections of the
	online documentation.

	http://www.FreeRTOS.org - Documentation, latest information, license and
	contact details.

	http://www.SafeRTOS.com - A version that is certified for use in safety
	critical systems.

	http://www.OpenRTOS.com - Commercial support, development, porting,
	licensing and training services.
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
