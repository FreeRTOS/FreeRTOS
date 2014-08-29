/*
    FreeRTOS V8.1.1 - Copyright (C) 2014 Real Time Engineers Ltd.
    All rights reserved

    VISIT http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

    ***************************************************************************
     *                                                                       *
     *    FreeRTOS provides completely free yet professionally developed,    *
     *    robust, strictly quality controlled, supported, and cross          *
     *    platform software that has become a de facto standard.             *
     *                                                                       *
     *    Help yourself get started quickly and support the FreeRTOS         *
     *    project by purchasing a FreeRTOS tutorial book, reference          *
     *    manual, or both from: http://www.FreeRTOS.org/Documentation        *
     *                                                                       *
     *    Thank you!                                                         *
     *                                                                       *
    ***************************************************************************

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation >>!AND MODIFIED BY!<< the FreeRTOS exception.

    >>!   NOTE: The modification to the GPL is included to allow you to     !<<
    >>!   distribute a combined work that includes FreeRTOS without being   !<<
    >>!   obliged to provide the source code for proprietary components     !<<
    >>!   outside of the FreeRTOS kernel.                                   !<<

    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT ANY
    WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
    FOR A PARTICULAR PURPOSE.  Full license text is available from the following
    link: http://www.freertos.org/a00114.html

    1 tab == 4 spaces!

    ***************************************************************************
     *                                                                       *
     *    Having a problem?  Start by reading the FAQ "My application does   *
     *    not run, what could be wrong?"                                     *
     *                                                                       *
     *    http://www.FreeRTOS.org/FAQHelp.html                               *
     *                                                                       *
    ***************************************************************************

    http://www.FreeRTOS.org - Documentation, books, training, latest versions,
    license and Real Time Engineers Ltd. contact details.

    http://www.FreeRTOS.org/plus - A selection of FreeRTOS ecosystem products,
    including FreeRTOS+Trace - an indispensable productivity tool, a DOS
    compatible FAT file system, and our tiny thread aware UDP/IP stack.

    http://www.OpenRTOS.com - Real Time Engineers ltd license FreeRTOS to High
    Integrity Systems to sell under the OpenRTOS brand.  Low cost OpenRTOS
    licenses offer ticketed support, indemnification and middleware.

    http://www.SafeRTOS.com - High Integrity Systems also provide a safety
    engineered and independently SIL3 certified version for use in safety and
    mission critical applications that require provable dependability.

    1 tab == 4 spaces!
*/

#ifndef PORTMACRO_H
#define PORTMACRO_H

#ifdef __cplusplus
extern "C" {
#endif

#include <machine/cpu.h>

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
#define portSTACK_TYPE	uint32_t
#define portBASE_TYPE	long

typedef portSTACK_TYPE StackType_t;
typedef long BaseType_t;
typedef unsigned long UBaseType_t;

#if( configUSE_16_BIT_TICKS == 1 )
	typedef uint16_t TickType_t;
	#define portMAX_DELAY ( TickType_t ) 0xffff
#else
	typedef uint32_t TickType_t;
	#define portMAX_DELAY ( TickType_t ) 0xffffffffUL
#endif
/*-----------------------------------------------------------*/

/* Architecture specifics. */
#define portSTACK_GROWTH							( -1 )
#define portTICK_PERIOD_MS							( ( TickType_t ) 1000 / configTICK_RATE_HZ )
#define portBYTE_ALIGNMENT							4
#define portNOP()									__asm__ volatile ( "mov r0, r0" )
#define portCRITICAL_NESTING_IN_TCB					1
#define portIRQ_TRAP_YIELD							31
/*-----------------------------------------------------------*/

/* Task utilities. */

extern void vPortYield( void );

/*---------------------------------------------------------------------------*/

#define portYIELD()		asm __volatile__( " trap #%0 "::"i"(portIRQ_TRAP_YIELD):"memory")
/*---------------------------------------------------------------------------*/

extern void vTaskEnterCritical( void );
extern void vTaskExitCritical( void );
#define portENTER_CRITICAL()		vTaskEnterCritical()
#define portEXIT_CRITICAL()			vTaskExitCritical()
/*---------------------------------------------------------------------------*/

/* Critical section management. */
#define portDISABLE_INTERRUPTS() 	cpu_int_disable()
#define portENABLE_INTERRUPTS() 	cpu_int_enable()

/*---------------------------------------------------------------------------*/

#define portYIELD_FROM_ISR( xHigherPriorityTaskWoken ) if( xHigherPriorityTaskWoken != pdFALSE ) vTaskSwitchContext()

/*---------------------------------------------------------------------------*/

#define portSAVE_CONTEXT()				\
	asm __volatile__																								\
	(																												\
		"sub	r1, #68					\n" /* Make space on the stack for the context. */							\
		"std	r2, [r1] + 	0			\n"																			\
		"stq	r4, [r1] +	8			\n"																			\
		"stq	r8, [r1] +	24			\n"																			\
		"stq	r12, [r1] +	40			\n"																			\
		"mov	r6, rtt					\n"																			\
		"mov	r7, psr					\n"																			\
		"std	r6, [r1] +	56			\n"																			\
		"movhi	r2, #16384				\n"	/* Set the pointer to the IC. */										\
		"ldub	r3, [r2] + 2			\n"	/* Load the current interrupt mask. */									\
		"st		r3, [r1]+ 64			\n"	/* Store the interrupt mask on the stack. */ 							\
		"ld		r2, [r0]+short(pxCurrentTCB)	\n"	/* Load the pointer to the TCB. */								\
		"st		r1, [r2]				\n"	/* Save the stack pointer into the TCB. */								\
		"mov	r14, r1					\n"	/* Compiler expects r14 to be set to the function stack. */				\
	);
/*---------------------------------------------------------------------------*/

#define portRESTORE_CONTEXT()																						\
	asm __volatile__(																								\
		"ld		r2, [r0]+short(pxCurrentTCB)	\n"	/* Load the TCB to find the stack pointer and context. */		\
		"ld		r1, [r2]				\n"																			\
		"movhi	r2, #16384				\n"	/* Set the pointer to the IC. */										\
		"ld		r3, [r1] + 64			\n"	/* Load the previous interrupt mask. */									\
		"stb	r3, [r2] + 2  			\n"	/* Set the current interrupt mask to be the previous. */				\
		"ldd	r6, [r1] + 56			\n"	/* Restore context. */													\
		"mov	rtt, r6					\n"																			\
		"mov	psr, r7					\n"																			\
		"ldd	r2, [r1] + 0			\n"																			\
		"ldq	r4, [r1] +	8			\n"																			\
		"ldq	r8, [r1] +	24			\n"																			\
		"ldq	r12, [r1] +	40			\n"																			\
		"add	r1, #68					\n"																			\
		"rti							\n"																			\
	 );

/*---------------------------------------------------------------------------*/

/* Task function macros as described on the FreeRTOS.org WEB site. */
#define portTASK_FUNCTION_PROTO( vFunction, pvParameters ) void vFunction( void *pvParameters )
#define portTASK_FUNCTION( vFunction, pvParameters ) void vFunction( void *pvParameters )
/*---------------------------------------------------------------------------*/

#ifdef __cplusplus
}
#endif

#endif /* PORTMACRO_H */
