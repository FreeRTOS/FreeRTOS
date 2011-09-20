/*
    FreeRTOS V7.0.2 - Copyright (C) 2011 Real Time Engineers Ltd.
	

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
#define portNOP()									__asm__ volatile ( "mov r0, r0" )
#define portCRITICAL_NESTING_IN_TCB					1
#define portIRQ_TRAP_YIELD							31
#define portKERNEL_INTERRUPT_PRIORITY_LEVEL			0
#define portSYSTEM_INTERRUPT_PRIORITY_LEVEL			0
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
#define portDISABLE_INTERRUPTS() ic->cpl = ( portSYSTEM_INTERRUPT_PRIORITY_LEVEL + 1 )
#define portENABLE_INTERRUPTS() ic->cpl = portKERNEL_INTERRUPT_PRIORITY_LEVEL

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
