/*
    FreeRTOS V6.0.4 - Copyright (C) 2010 Real Time Engineers Ltd.

    ***************************************************************************
    *                                                                         *
    * If you are:                                                             *
    *                                                                         *
    *    + New to FreeRTOS,                                                   *
    *    + Wanting to learn FreeRTOS or multitasking in general quickly       *
    *    + Looking for basic training,                                        *
    *    + Wanting to improve your FreeRTOS skills and productivity           *
    *                                                                         *
    * then take a look at the FreeRTOS eBook                                  *
    *                                                                         *
    *        "Using the FreeRTOS Real Time Kernel - a Practical Guide"        *
    *                  http://www.FreeRTOS.org/Documentation                  *
    *                                                                         *
    * A pdf reference manual is also available.  Both are usually delivered   *
    * to your inbox within 20 minutes to two hours when purchased between 8am *
    * and 8pm GMT (although please allow up to 24 hours in case of            *
    * exceptional circumstances).  Thank you for your support!                *
    *                                                                         *
    ***************************************************************************

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation AND MODIFIED BY the FreeRTOS exception.
    ***NOTE*** The exception to the GPL is included to allow you to distribute
    a combined work that includes FreeRTOS without being obliged to provide the
    source code for proprietary components outside of the FreeRTOS kernel.
    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT
    ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
    FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
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

/* Kernel includes. */
#include "FreeRTOS.h"
#include "task.h"

/* Machine includes */
#include <machine/counter.h>
#include <machine/ic.h>
/*-----------------------------------------------------------*/

/* The initial PSR has the Previous Interrupt Enabled (PIEN) flag set. */
#define portINITIAL_PSR			( 0x00020000 )

/*-----------------------------------------------------------*/

/*
 * Perform any hardware configuration necessary to generate the tick interrupt.
 */
static void prvSetupTimerInterrupt( void );
/*-----------------------------------------------------------*/

/* Variables used to hold interrupt and critical nesting depths, with variables
that provide a convenient method of obtaining their addresses. */
volatile unsigned portBASE_TYPE uxInterruptNestingCount = 999UL;
const volatile unsigned portBASE_TYPE *puxInterruptNestingCount = &uxInterruptNestingCount;
volatile unsigned portBASE_TYPE uxInterruptStack[ configMINIMAL_STACK_SIZE ];
const volatile unsigned portBASE_TYPE *puxTopOfInterruptStack = &( uxInterruptStack[ configMINIMAL_STACK_SIZE - 1 ] );
/*-----------------------------------------------------------*/

portSTACK_TYPE *pxPortInitialiseStack( portSTACK_TYPE * pxTopOfStack, pdTASK_CODE pxCode, void *pvParameters )
{
	/* For the time being, mimic the stack when using the
	__attribute__((interrupt)) plus the extra caller saved registers. */
	pxTopOfStack -= 17;

	/* RTT */
	pxTopOfStack[ 16 ] = ( portSTACK_TYPE )pxCode;

	/* PSR */
	pxTopOfStack[ 15 ] = portINITIAL_PSR;

	/* R14 and R15 aka FuncSP and LR, respectively */
	pxTopOfStack[ 14 ] = 0x00000000;
	pxTopOfStack[ 13 ] = ( portSTACK_TYPE )( pxTopOfStack + 17 );

	/* R7 to R2 */
	pxTopOfStack[ 12 ] = 0x07070707;
	pxTopOfStack[ 11 ] = 0x06060606;
	pxTopOfStack[ 10 ] = 0x05050505;
	pxTopOfStack[ 9 ] = 0x04040404;
	pxTopOfStack[ 8 ] = 0x03030303;
	pxTopOfStack[ 7 ] = ( portSTACK_TYPE )pvParameters;

	/* Set the Interrupt Priority on Task entry. */
	pxTopOfStack[ 6 ] = portKERNEL_INTERRUPT_PRIORITY_LEVEL;

	/* R13 to R8. */
	pxTopOfStack[ 5 ] = 0x0D0D0D0D;
	pxTopOfStack[ 4 ] = 0x0C0C0C0C;
	pxTopOfStack[ 3 ] = 0x0B0B0B0B;
	pxTopOfStack[ 2 ] = 0x0A0A0A0A;
	pxTopOfStack[ 1 ] = 0x09090909;
	pxTopOfStack[ 0 ] = 0x08080808;

	return pxTopOfStack;
}
/*-----------------------------------------------------------*/

portBASE_TYPE xPortStartScheduler( void )
{
	/* Set-up the timer interrupt. */
	prvSetupTimerInterrupt();

	/* Enable the TRAP yield. */
	irq[ portIRQ_TRAP_YIELD ].ien = 1;
	irq[ portIRQ_TRAP_YIELD ].ipl = portKERNEL_INTERRUPT_PRIORITY_LEVEL;

	/* Integrated Interrupt Controller: Enable all interrupts. */
	ic->ien = 1;
	uxInterruptNestingCount = 1UL;

	/* Restore calleree saved registers. */
	portRESTORE_CONTEXT_REDUCED();

	/* Mimic an ISR epilogue to start the task executing. */
	asm __volatile__(						\
		"mov	r1, r14					\n"	\
		"ldd	r6, [r1]+0x20			\n"	\
		"mov	psr, r6					\n"	\
		"mov	rtt, r7					\n"	\
		"ldd	r14, [r1]+0x18			\n"	\
		"ldq	r4, [r1]+0x8			\n"	\
		"ldd	r2, [r1]				\n"	\
		"add	r1, #0x28				\n"	\
		"rti							\n"	\
		);									\

	/* Should not get here. */
	return 0;
}
/*-----------------------------------------------------------*/

static void prvSetupTimerInterrupt( void )
{
	/* Enable timer interrupts */
	counter1->reload = ( configCPU_CLOCK_HZ / configTICK_RATE_HZ ) - 1;
	counter1->value = counter1->reload;
	counter1->mask = 1;

	/* Set the IRQ Handler priority and enable it. */
	irq[ IRQ_COUNTER1 ].ien = 1;
	irq[ IRQ_COUNTER1 ].ipl = portKERNEL_INTERRUPT_PRIORITY_LEVEL;
}
/*-----------------------------------------------------------*/

void interrupt_handler( portIRQ_TRAP_YIELD )
{
	/* Save remaining registers. */
	portSAVE_CONTEXT_REDUCED();

	/* Perform the actual Yield. */
	portYIELD_FROM_ISR();

	/* Restore the first lot of registers, the remains will be resotred when
	this function exits. */
	portRESTORE_CONTEXT_REDUCED();
}
/*-----------------------------------------------------------*/

/* Timer tick interrupt handler */
void interrupt_handler( IRQ_COUNTER1 )
{
	portSAVE_CONTEXT_REDUCED();

	asm __volatile__(
			" sub		r1, #4			\n"		/* Make space on the stack.  r1 is stack pointer. */
			" movhi		r2, #16384		\n"		/* Load the pointer to the IC. */
			" ldub		r3, [r2]+2		\n"		/* Copy the Current Priority Level. */
			" st		r3, [r1]		\n"		/* Store it on the stack. */
			" mov 		r3, #%0			\n"		/* Load the highest priority level. */
			" stb		r3, [r2]+2		\n"		/* Set the CPL to the highest level. */
			" call		vTaskIncrementTick	\n"	/* Increment the tick. */
			" ld		r3, [r1]		\n"		/* Load the previous CPL from the stack. */
			" movhi		r2, #16384		\n"		/* Load the pointer to the IC. */
			" stb		r3, [r2]+2		\n"		/* Set the CPL to the previous CPL. */
			" add		r1, #4			"
			:
			:"i"( portSYSTEM_INTERRUPT_PRIORITY_LEVEL + 1 )
			:"r2","r3" /* Fix the stack. */
	);

	#if configUSE_PREEMPTION == 1
		portYIELD_FROM_ISR();
	#endif

	{
		/* Clear the Tick Interrupt. */
		counter1->expired = 0;
	}

	portRESTORE_CONTEXT_REDUCED();
}
/*-----------------------------------------------------------*/

void vPortEndScheduler( void )
{
	/* Nothing to do. Unlikely to want to end. */
}
/*-----------------------------------------------------------*/
