/*
	FreeRTOS.org V5.0.3 - Copyright (C) 2003-2008 Richard Barry.

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
#include "task.h"

#define portPRESCALE_VALUE			64
#define portPRESCALE_REG_SETTING	( 5 << 8 )
#define portPIT_INTERRUPT_ENABLED	( 0x08 )
#define configPIT0_INTERRUPT_VECTOR	( 55 )

void vApplicationSetupInterrupts( void )
{
const unsigned portSHORT usCompareMatchValue = ( ( configCPU_CLOCK_HZ / portPRESCALE_VALUE ) / configTICK_RATE_HZ );

    /* Configure interrupt priority and level and unmask interrupt. */
    MCF_INTC0_ICR55 = ( 1 | ( configKERNEL_INTERRUPT_PRIORITY << 3 ) );
    MCF_INTC0_IMRH &= ~( MCF_INTC_IMRH_INT_MASK55 );

    MCF_INTC0_ICR63 = ( 0 | configKERNEL_INTERRUPT_PRIORITY << 3 );
    MCF_INTC0_IMRH &= ~( MCF_INTC_IMRH_INT_MASK63 );

    MCF_PIT0_PCSR |= MCF_PIT_PCSR_PIF;
    MCF_PIT0_PCSR = ( portPRESCALE_REG_SETTING | MCF_PIT_PCSR_PIE | MCF_PIT_PCSR_RLD | MCF_PIT_PCSR_EN );
	MCF_PIT0_PMR = usCompareMatchValue;
}
/*-----------------------------------------------------------*/

void __attribute__ ((interrupt)) __cs3_isr_interrupt_119( void )
{
unsigned portLONG ulSavedInterruptMask;

	MCF_PIT0_PCSR |= MCF_PIT_PCSR_PIF;
	ulSavedInterruptMask = portSET_INTERRUPT_MASK_FROM_ISR();
		vTaskIncrementTick();
	portCLEAR_INTERRUPT_MASK_FROM_ISR( ulSavedInterruptMask );

	#if configUSE_PREEMPTION == 1
	{
		taskYIELD();
	}
	#endif
}
