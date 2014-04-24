/*
    FreeRTOS V8.0.1 - Copyright (C) 2014 Real Time Engineers Ltd.
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

#include <intrinsics.h>

#ifdef __cplusplus
extern "C" {
#endif

/*-----------------------------------------------------------
 * Port specific definitions.
 *
 * The settings in this file configure FreeRTOS correctly for the
 * given hardware and compiler.
 *
 * These settings should not be altered.
 *-----------------------------------------------------------
 */

/* Type definitions - these are a bit legacy and not really used now, other than
portSTACK_TYPE and portBASE_TYPE. */
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

/* Hardware specifics. */
#define portBYTE_ALIGNMENT			8	/* Could make four, according to manual. */
#define portSTACK_GROWTH			-1
#define portTICK_PERIOD_MS			( ( TickType_t ) 1000 / configTICK_RATE_HZ )
#define portNOP()					__no_operation()

/* Yield equivalent to "*portITU_SWINTR = 0x01; ( void ) *portITU_SWINTR;"
where portITU_SWINTR is the location of the software interrupt register
(0x000872E0).  Don't rely on the assembler to select a register, so instead
save and restore clobbered registers manually. */
#define portYIELD()							\
	__asm volatile 							\
	(										\
		"PUSH.L	R10					\n"		\
		"MOV.L	#0x872E0, R10		\n"		\
		"MOV.B	#0x1, [R10]			\n"		\
		"MOV.L	[R10], R10			\n"		\
		"POP	R10					\n"		\
	)

#define portYIELD_FROM_ISR( x )	if( ( x ) != pdFALSE ) portYIELD()

/* These macros should not be called directly, but through the
taskENTER_CRITICAL() and taskEXIT_CRITICAL() macros.  An extra check is
performed if configASSERT() is defined to ensure an assertion handler does not
inadvertently attempt to lower the IPL when the call to assert was triggered
because the IPL value was found to be above	configMAX_SYSCALL_INTERRUPT_PRIORITY
when an ISR safe FreeRTOS API function was executed.  ISR safe FreeRTOS API
functions are those that end in FromISR.  FreeRTOS maintains a separate
interrupt API to ensure API function and interrupt entry is as fast and as
simple as possible. */
#define portENABLE_INTERRUPTS() 	__set_interrupt_level( ( uint8_t ) 0 )
#ifdef configASSERT
	#define portASSERT_IF_INTERRUPT_PRIORITY_INVALID() configASSERT( ( __get_interrupt_level() <= configMAX_SYSCALL_INTERRUPT_PRIORITY ) )
	#define portDISABLE_INTERRUPTS() 	if( __get_interrupt_level() < configMAX_SYSCALL_INTERRUPT_PRIORITY ) __set_interrupt_level( ( uint8_t ) configMAX_SYSCALL_INTERRUPT_PRIORITY )
#else
	#define portDISABLE_INTERRUPTS() 	__set_interrupt_level( ( uint8_t ) configMAX_SYSCALL_INTERRUPT_PRIORITY )
#endif

/* Critical nesting counts are stored in the TCB. */
#define portCRITICAL_NESTING_IN_TCB ( 1 )

/* The critical nesting functions defined within tasks.c. */
extern void vTaskEnterCritical( void );
extern void vTaskExitCritical( void );
#define portENTER_CRITICAL()	vTaskEnterCritical()
#define portEXIT_CRITICAL()		vTaskExitCritical()

/* As this port allows interrupt nesting... */
#define portSET_INTERRUPT_MASK_FROM_ISR() __get_interrupt_level(); portDISABLE_INTERRUPTS()
#define portCLEAR_INTERRUPT_MASK_FROM_ISR( uxSavedInterruptStatus ) __set_interrupt_level( ( uint8_t ) ( uxSavedInterruptStatus ) )

/*-----------------------------------------------------------*/

/* Task function macros as described on the FreeRTOS.org WEB site. */
#define portTASK_FUNCTION_PROTO( vFunction, pvParameters ) void vFunction( void *pvParameters )
#define portTASK_FUNCTION( vFunction, pvParameters ) void vFunction( void *pvParameters )

#ifdef __cplusplus
}
#endif

#endif /* PORTMACRO_H */

