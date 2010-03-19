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

#ifndef PORTMACRO_H
#define PORTMACRO_H

#ifdef __cplusplus
extern "C" {
#endif

#include <machine/ic.h>

/*-----------------------------------------------------------
 * Port specific definitions.
 *
 * The settings in this file configure FreeRTOS correctly for the
 * given hardware and compiler.
 *
 * These settings should not be altered.
 *-----------------------------------------------------------
 */

/* Type definitions. */
#define portCHAR		char
#define portFLOAT		float
#define portDOUBLE		double
#define portLONG		long
#define portSHORT		short
#define portSTACK_TYPE	unsigned portLONG
#define portBASE_TYPE	portLONG

#if( configUSE_16_BIT_TICKS == 1 )
	typedef unsigned portSHORT portTickType;
	#define portMAX_DELAY ( portTickType ) 0xffff
#else
	typedef unsigned portLONG portTickType;
	#define portMAX_DELAY ( portTickType ) 0xffffffff
#endif
/*-----------------------------------------------------------*/

/* Architecture specifics. */
#define portSTACK_GROWTH							( -1 )
#define portTICK_RATE_MS							( ( portTickType ) 1000 / configTICK_RATE_HZ )
#define portBYTE_ALIGNMENT							4
#define portNOP()									__asm__ volatile ( "mov r0,r0; nop" )
#define portCRITICAL_NESTING_IN_TCB					1
#define portIRQ_TRAP_YIELD							31
#define portKERNEL_INTERRUPT_PRIORITY_LEVEL			0
#define portSYSTEM_INTERRUPT_PRIORITY_LEVEL			1
/*-----------------------------------------------------------*/

/* Task utilities. */

extern void vPortYield( void );

/**
 * Interrupt Handlers that access RTOS API functions use a separate interrupt stack
 * and so the nesting depth needs to be recorded to know when to switch from the
 * interrupt stack back to the Task stack.
 */
extern volatile unsigned portBASE_TYPE uxInterruptNestingCount;
/*---------------------------------------------------------------------------*/

#define portYIELD()		asm __volatile__( " trap #%0 "::"i"(portIRQ_TRAP_YIELD):"memory")
/*---------------------------------------------------------------------------*/

#define portYIELD_FROM_ISR()																\
	{																						\
		asm __volatile__(																	\
			" sub		r1, #4			\n"		/* Make space on the stack. */				\
			" movhi		r2, #16384		\n"		/* Load the pointer to the IC. */			\
			" ldub		r3, [r2]+2		\n"		/* Copy the Current Priority Level. */		\
			" st		r3, [r1]		\n"		/* Store it on the stack. */				\
			" mov 		r3, #%0			\n"		/* Load the highest priority level. */		\
			" stb		r3, [r2]+2		\n"		/* Set the CPL to the highest level. */		\
			" call		vTaskSwitchContext	\n"	/* Select a new pxCurrentTCB. */			\
			" ld		r3, [r1]		\n"		/* Load the previous CPL from the stack. */	\
			" movhi		r2, #16384		\n"		/* Load the pointer to the IC. */			\
			" stb		r3, [r2]+2		\n"		/* Set the CPL to the previous CPL. */		\
			" add		r1, #4			"		/* Fix the stack. */						\
			:																				\
			:"i"(portSYSTEM_INTERRUPT_PRIORITY_LEVEL+1)										\
			:"r2","r3");																	\
	}
/*---------------------------------------------------------------------------*/

extern void vTaskEnterCritical( void );
extern void vTaskExitCritical( void );
#define portENTER_CRITICAL()		vTaskEnterCritical()
#define portEXIT_CRITICAL()			vTaskExitCritical()
/*---------------------------------------------------------------------------*/

/* Critical section management. */
#define portDISABLE_INTERRUPTS()									\
	{ /*ic->cpl = ( portSYSTEM_INTERRUPT_PRIORITY_LEVEL + 1 );*/	\
		asm __volatile__(											\
				" movhi r2, #16384		\n"							\
				" mov r3, #%0			\n"							\
				" stb r3, [r2]+2"									\
				:													\
				:"i"(portSYSTEM_INTERRUPT_PRIORITY_LEVEL+1)			\
				:"r2", "r3"				);							\
	}
/*---------------------------------------------------------------------------*/

#define portENABLE_INTERRUPTS()										\
	{ /*ic->cpl = portKERNEL_INTERRUPT_PRIORITY_LEVEL;*/			\
		asm __volatile__(											\
				" movhi r2, #16384		\n"							\
				" mov r3, #%0			\n"							\
				" stb r3, [r2]+2"									\
				:													\
				:"i"(portKERNEL_INTERRUPT_PRIORITY_LEVEL)			\
				:"r2", "r3"				);							\
	}
/*---------------------------------------------------------------------------*/

#define portSAVE_CONTEXT_REDUCED()				\
	{											\
		asm __volatile__(						\
			/* "sub	r1, #0x28"		*/			\
			/* "stq	r4, [r1]+0x8"	*/			\
			/* "mov	r6, psr"		*/			\
			/* "mov	r7, rtt"		*/			\
			/* "std	r6, [r1]+0x20"	*/			\
			/* "std	r14, [r1]+0x18"	*/			\
			/* "std	r2, [r1]"	*/				\
			/* "mov	r14, r1"	*/				\
			"sub	r1, #0x1c				\n"	/* Make space on the stack. */	\
			"stq	r8, [r1]				\n"	/* Store the remaining context registers. */	\
			"std	r12, [r1]+0x10			\n"	\
			"movhi	r2, #16384				\n"	/* Set the pointer to the IC. */	\
			"ldub	r3, [r2]+2				\n"	/* Load the current priority level. */	\
			"st		r3, [r1]+0x18			\n"	/* Store the current priority level on the stack. */ \
			"ldub	r3, [r2]+3				\n"	/* Load the interrupt priority level. */	\
			"add	r3, #1					\n"	/* Increase the priority by one. */	\
			"stb	r3, [r2]+2				\n" /* Set the current priority level to be above this one. */	\
			"ld		r4, [r0]+short(puxInterruptNestingCount)	\n"	/*[r0]+short(puxInterruptNestingCount) */ \
			"ld		r5, [r4]				\n"	\
			"add	r5, #1					\n"	/* Increment the interrupt nesting count. */	\
			"st		r5, [r4]				\n"	\
			"cmp	r5, #1					\n"	/* Is this the first interrupt? */	\
			"bne.s	12						\n" /* If it is then save the stack pointer to the current TCB? */	\
			"ld		r2, [r0]+short(pxCurrentTCB)	\n"	/* Load the pointer to the TCB. */	\
			"st		r1, [r2]				\n"	/* Save the stack pointer into the TCB. */	\
			"ld		r1, [r0]+short(puxTopOfInterruptStack)		\n"	/* Switch to the dedicated interrupt stack. */	/* [r0]+short(uxInterruptStack) */	\
			"mov	r14, r1					\n"	/* Compiler expects r14 to be set to the function stack. */	\
			"movhi	r2, #3					\n"	/* Re-enable interrupts (re-enable breakpoints). */	\
			"mov	psr, r2					\n"	\
			:::"r2","r3","r4","r5","r15"	);	/* Clobber list includes all of the caller saved registers so that they are saved as part of the Interrupt handler pre-amble. */	\
	}
/*---------------------------------------------------------------------------*/

#define portRESTORE_CONTEXT_REDUCED()			\
	{											\
		asm __volatile__(						\
			"movhi	r2, #2					\n"	/* Disable interrupts (disable breakpoints). */	\
			"mov	psr, r2					\n"	\
			"ld		r2, [r0]+short(puxInterruptNestingCount)	\n"	\
			"ld		r3, [r2]				\n"	\
			"sub	r3, #1					\n"	/* Decrement the interrupt nesting count. */	\
			"st		r3, [r2]				\n"	\
			"cmp	r3, r0					\n"	/* Is this the first interrupt? */	\
			"bne.s	8						\n"	/* Are we at the end of unrolling the interrupt nesting? */	\
			"ld		r2, [r0]+short(pxCurrentTCB)	\n"	/* Load the TCB to find the stack pointer and context. */	\
			"ld		r1, [r2]				\n"	\
			"movhi	r2, #16384				\n"	/* Set the pointer to the IC. */	\
			"ld		r3, [r1]+0x18			\n"	/* Load the previous current priority level. */	\
			"stb	r3, [r2]+2  			\n"	/* Set the current priority level to be the previous. */	\
			"ldd	r12, [r1]+0x10			\n"	/* Restore the callee saved registers. Caller saved registers are restored by the function exit. */	\
			"ldq	r8, [r1]				\n"	\
			"add	r1, #0x1c				\n"	\
			"mov	r14, r1					\n"	\
			/* "mov	r1, r14"		*/			\
			/* "ldd	r6, [r1]+0x20"	*/			\
			/* "mov	psr, r6"		*/			\
			/* "mov	rtt, r7"		*/			\
			/* "ldd	r14, [r1]+0x18"	*/			\
			/* "ldq	r4, [r1]+0x8"	*/			\
			/* "ldd	r2, [r1]"		*/			\
			/* "add	r1, #0x28"		*/			\
			/* "rti"				*/			\
			);									\
	}
/*---------------------------------------------------------------------------*/

/* Task function macros as described on the FreeRTOS.org WEB site. */
#define portTASK_FUNCTION_PROTO( vFunction, pvParameters ) void vFunction( void *pvParameters )
#define portTASK_FUNCTION( vFunction, pvParameters ) void vFunction( void *pvParameters )
/*---------------------------------------------------------------------------*/

#ifdef __cplusplus
}
#endif

#endif /* PORTMACRO_H */
