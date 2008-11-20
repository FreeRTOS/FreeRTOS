/*
	FreeRTOS.org V5.1.1 - Copyright (C) 2003-2008 Richard Barry.

	This file is part of the FreeRTOS.org distribution.

	FreeRTOS.org is free software; you can redistribute it and/or modify
	it under the terms of the GNU General Public License as published by
	the Free Software Foundation; either version 2 of the License, or
	(at your option) any later version.

	FreeRTOS.org is distributed in the hope that it will be useful,
	but WITHOUT ANY WARRANTY; without even the implied warranty of
	MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
	GNU General Public License for more details.

	You should have received a copy of the GNU General Public License
	along with FreeRTOS.org; if not, write to the Free Software
	Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA

	A special exception to the GPL can be applied should you wish to distribute
	a combined work that includes FreeRTOS.org, without being obliged to provide
	the source code for any proprietary components.  See the licensing section
	of http://www.FreeRTOS.org for full details of how and when the exception
	can be applied.

    ***************************************************************************
    ***************************************************************************
    *                                                                         *
    * SAVE TIME AND MONEY!  We can port FreeRTOS.org to your own hardware,    *
    * and even write all or part of your application on your behalf.          *
    * See http://www.OpenRTOS.com for details of the services we provide to   *
    * expedite your project.                                                  *
    *                                                                         *
    ***************************************************************************
    ***************************************************************************

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
