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

__declspec(interrupt:0) void vPIT0InterruptHandler( void );
extern unsigned portLONG __VECTOR_RAM[];

/* Constants used to configure the interrupts. */
#define portPRESCALE_VALUE			64
#define portPRESCALE_REG_SETTING	( 5 << 8 )
#define portPIT_INTERRUPT_ENABLED	( 0x08 )
#define configPIT0_INTERRUPT_VECTOR	( 55 )

/*
 * FreeRTOS.org requires two interrupts - a tick interrupt generated from a
 * timer source, and a spare interrupt vector used for context switching.
 * The configuration below uses PIT0 for the former, and vector 63 for the
 * latter.  **IF YOUR APPLICATION HAS BOTH OF THESE INTERRUPTS FREE THEN YOU DO
 * NOT NEED TO CHANGE ANY OF THIS CODE** - otherwise instructions are provided
 * here for using alternative interrupt sources.
 *
 * To change the tick interrupt source:
 *
 *	1) Modify vApplicationSetupInterrupts() below to be correct for whichever
 *	peripheral is to be used to generate the tick interrupt.
 *
 *	2) Change the name of the function __cs3_isr_interrupt_119() defined within
 *	this file to be correct for the interrupt vector used by the timer peripheral.
 *	The name of the function should contain the vector number, so by default vector
 *	number 119 is being used.
 *
 *	3) Make sure the tick interrupt is cleared within the interrupt handler function.
 *  Currently __cs3_isr_interrupt_119() clears the PIT0 interrupt.
 *
 * To change the spare interrupt source:
 *
 *  1) Modify vApplicationSetupInterrupts() below to be correct for whichever
 *  interrupt vector is to be used.  Make sure you use a spare interrupt on interrupt
 *  controller 0, otherwise the register used to request context switches will also
 *  require modification.
 *
 *  2) Change the definition of configYIELD_INTERRUPT_VECTOR within FreeRTOSConfig.h
 *  to be correct for your chosen interrupt vector.
 *
 *  3) Change the name of the function __cs3_isr_interrupt_127() within portasm.S
 *  to be correct for whichever vector number is being used.  By default interrupt
 *  controller 0 number 63 is used, which corresponds to vector number 127.
 */
void vApplicationSetupInterrupts( void )
{
const unsigned portSHORT usCompareMatchValue = ( ( configCPU_CLOCK_HZ / portPRESCALE_VALUE ) / configTICK_RATE_HZ );

    /* Configure interrupt priority and level and unmask interrupt for PIT0. */
    MCF_INTC0_ICR55 = ( 1 | ( configKERNEL_INTERRUPT_PRIORITY << 3 ) );
    MCF_INTC0_IMRH &= ~( MCF_INTC_IMRH_INT_MASK55 );

    /* Do the same for vector 63 (interrupt controller 0.  I don't think the
    write to MCF_INTC0_IMRH is actually required here but is included for
    completeness. */
    MCF_INTC0_ICR16 = ( 0 | configKERNEL_INTERRUPT_PRIORITY << 3 );
    MCF_INTC0_IMRL &= ~( MCF_INTC_IMRL_INT_MASK16 | 0x01 );

    /* Configure PIT0 to generate the RTOS tick. */
    MCF_PIT0_PCSR |= MCF_PIT_PCSR_PIF;
    MCF_PIT0_PCSR = ( portPRESCALE_REG_SETTING | MCF_PIT_PCSR_PIE | MCF_PIT_PCSR_RLD | MCF_PIT_PCSR_EN );
	MCF_PIT0_PMR = usCompareMatchValue;
}
/*-----------------------------------------------------------*/

__declspec(interrupt:0) void vPIT0InterruptHandler( void )
{
unsigned portLONG ulSavedInterruptMask;

	/* Clear the PIT0 interrupt. */
	MCF_PIT0_PCSR |= MCF_PIT_PCSR_PIF;

	/* Increment the RTOS tick. */
	ulSavedInterruptMask = portSET_INTERRUPT_MASK_FROM_ISR();
		vTaskIncrementTick();
	portCLEAR_INTERRUPT_MASK_FROM_ISR( ulSavedInterruptMask );

	/* If we are using the pre-emptive scheduler then also request a
	context switch as incrementing the tick could have unblocked a task. */
	#if configUSE_PREEMPTION == 1
	{
		taskYIELD();
	}
	#endif
}
