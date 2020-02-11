/*
 * FreeRTOS Kernel
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


/*-----------------------------------------------------------
 * Components that can be compiled to either ARM or THUMB mode are
 * contained in port.c  The ISR routines, which can only be compiled
 * to ARM mode, are contained in this file.
 *----------------------------------------------------------*/

/*
	Changes from V3.2.4

	+ The assembler statements are now included in a single asm block rather
	  than each line having its own asm block.
*/

/* Scheduler includes. */
#include "FreeRTOS.h"
#include "task.h"

#include "AT91SAM7X256.h"

/* Constants required to handle interrupts. */
#define portTIMER_MATCH_ISR_BIT		( ( uint8_t ) 0x01 )
#define portCLEAR_VIC_INTERRUPT		( ( uint32_t ) 0 )

/* Constants required to handle critical sections. */
#define portNO_CRITICAL_NESTING		( ( uint32_t ) 0 )
volatile uint32_t ulCriticalNesting = 9999UL;

/*-----------------------------------------------------------*/

/* ISR to handle manual context switches (from a call to taskYIELD()). */
void vPortYieldProcessor( void ) __attribute__((interrupt("SWI"), naked));

/*
 * The scheduler can only be started from ARM mode, hence the inclusion of this
 * function here.
 */
void vPortISRStartFirstTask( void );
/*-----------------------------------------------------------*/

void vPortISRStartFirstTask( void )
{
	/* Simply start the scheduler.  This is included here as it can only be
	called from ARM mode. */
	portRESTORE_CONTEXT();
}
/*-----------------------------------------------------------*/

/*
 * Called by portYIELD() or taskYIELD() to manually force a context switch.
 *
 * When a context switch is performed from the task level the saved task
 * context is made to look as if it occurred from within the tick ISR.  This
 * way the same restore context function can be used when restoring the context
 * saved from the ISR or that saved from a call to vPortYieldProcessor.
 */
void vPortYieldProcessor( void )
{
	/* Within an IRQ ISR the link register has an offset from the true return
	address, but an SWI ISR does not.  Add the offset manually so the same
	ISR return code can be used in both cases. */
	__asm volatile ( "ADD		LR, LR, #4" );

	/* Perform the context switch.  First save the context of the current task. */
	portSAVE_CONTEXT();

	/* Find the highest priority task that is ready to run. */
	vTaskSwitchContext();

	/* Restore the context of the new task. */
	portRESTORE_CONTEXT();
}
/*-----------------------------------------------------------*/

/*
 * The ISR used for the scheduler tick depends on whether the cooperative or
 * the preemptive scheduler is being used.
 */

#if configUSE_PREEMPTION == 0

	/* The cooperative scheduler requires a normal IRQ service routine to
	simply increment the system tick. */
	void vNonPreemptiveTick( void ) __attribute__ ((interrupt ("IRQ")));
	void vNonPreemptiveTick( void )
	{
		uint32_t ulDummy;

		/* Increment the tick count - which may wake some tasks but as the
		preemptive scheduler is not being used any woken task is not given
		processor time no matter what its priority. */
		xTaskIncrementTick();

		/* Clear the PIT interrupt. */
		ulDummy = AT91C_BASE_PITC->PITC_PIVR;

		/* End the interrupt in the AIC. */
		AT91C_BASE_AIC->AIC_EOICR = ulDummy;
	}

#else

	/* The preemptive scheduler is defined as "naked" as the full context is
	saved on entry as part of the context switch. */
	void vPreemptiveTick( void ) __attribute__((naked));
	void vPreemptiveTick( void )
	{
		/* Save the context of the current task. */
		portSAVE_CONTEXT();

		/* Increment the tick count - this may wake a task. */
		if( xTaskIncrementTick() != pdFALSE )
		{
			/* Find the highest priority task that is ready to run. */
			vTaskSwitchContext();
		}

		/* End the interrupt in the AIC. */
		AT91C_BASE_AIC->AIC_EOICR = AT91C_BASE_PITC->PITC_PIVR;

		portRESTORE_CONTEXT();
	}

#endif
/*-----------------------------------------------------------*/

/*
 * The interrupt management utilities can only be called from ARM mode.  When
 * THUMB_INTERWORK is defined the utilities are defined as functions here to
 * ensure a switch to ARM mode.  When THUMB_INTERWORK is not defined then
 * the utilities are defined as macros in portmacro.h - as per other ports.
 */
void vPortDisableInterruptsFromThumb( void ) __attribute__ ((naked));
void vPortEnableInterruptsFromThumb( void ) __attribute__ ((naked));

void vPortDisableInterruptsFromThumb( void )
{
	__asm volatile (
		"STMDB	SP!, {R0}		\n\t"	/* Push R0.									*/
		"MRS	R0, CPSR		\n\t"	/* Get CPSR.								*/
		"ORR	R0, R0, #0xC0	\n\t"	/* Disable IRQ, FIQ.						*/
		"MSR	CPSR, R0		\n\t"	/* Write back modified value.				*/
		"LDMIA	SP!, {R0}		\n\t"	/* Pop R0.									*/
		"BX		R14" );					/* Return back to thumb.					*/
}

void vPortEnableInterruptsFromThumb( void )
{
	__asm volatile (
		"STMDB	SP!, {R0}		\n\t"	/* Push R0.									*/
		"MRS	R0, CPSR		\n\t"	/* Get CPSR.								*/
		"BIC	R0, R0, #0xC0	\n\t"	/* Enable IRQ, FIQ.							*/
		"MSR	CPSR, R0		\n\t"	/* Write back modified value.				*/
		"LDMIA	SP!, {R0}		\n\t"	/* Pop R0.									*/
		"BX		R14" );					/* Return back to thumb.					*/
}


/* The code generated by the GCC compiler uses the stack in different ways at
different optimisation levels.  The interrupt flags can therefore not always
be saved to the stack.  Instead the critical section nesting level is stored
in a variable, which is then saved as part of the stack context. */
void vPortEnterCritical( void )
{
	/* Disable interrupts as per portDISABLE_INTERRUPTS(); 							*/
	__asm volatile (
		"STMDB	SP!, {R0}			\n\t"	/* Push R0.								*/
		"MRS	R0, CPSR			\n\t"	/* Get CPSR.							*/
		"ORR	R0, R0, #0xC0		\n\t"	/* Disable IRQ, FIQ.					*/
		"MSR	CPSR, R0			\n\t"	/* Write back modified value.			*/
		"LDMIA	SP!, {R0}" );				/* Pop R0.								*/

	/* Now interrupts are disabled ulCriticalNesting can be accessed
	directly.  Increment ulCriticalNesting to keep a count of how many times
	portENTER_CRITICAL() has been called. */
	ulCriticalNesting++;
}

void vPortExitCritical( void )
{
	if( ulCriticalNesting > portNO_CRITICAL_NESTING )
	{
		/* Decrement the nesting count as we are leaving a critical section. */
		ulCriticalNesting--;

		/* If the nesting level has reached zero then interrupts should be
		re-enabled. */
		if( ulCriticalNesting == portNO_CRITICAL_NESTING )
		{
			/* Enable interrupts as per portEXIT_CRITICAL().					*/
			__asm volatile (
				"STMDB	SP!, {R0}		\n\t"	/* Push R0.						*/
				"MRS	R0, CPSR		\n\t"	/* Get CPSR.					*/
				"BIC	R0, R0, #0xC0	\n\t"	/* Enable IRQ, FIQ.				*/
				"MSR	CPSR, R0		\n\t"	/* Write back modified value.	*/
				"LDMIA	SP!, {R0}" );			/* Pop R0.						*/
		}
	}
}

