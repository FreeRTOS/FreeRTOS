/*
    FreeRTOS V9.0.0rc2 - Copyright (C) 2016 Real Time Engineers Ltd.
    All rights reserved

    VISIT http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation >>>> AND MODIFIED BY <<<< the FreeRTOS exception.

    ***************************************************************************
    >>!   NOTE: The modification to the GPL is included to allow you to     !<<
    >>!   distribute a combined work that includes FreeRTOS without being   !<<
    >>!   obliged to provide the source code for proprietary components     !<<
    >>!   outside of the FreeRTOS kernel.                                   !<<
    ***************************************************************************

    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT ANY
    WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
    FOR A PARTICULAR PURPOSE.  Full license text is available on the following
    link: http://www.freertos.org/a00114.html

    ***************************************************************************
     *                                                                       *
     *    FreeRTOS provides completely free yet professionally developed,    *
     *    robust, strictly quality controlled, supported, and cross          *
     *    platform software that is more than just the market leader, it     *
     *    is the industry's de facto standard.                               *
     *                                                                       *
     *    Help yourself get started quickly while simultaneously helping     *
     *    to support the FreeRTOS project by purchasing a FreeRTOS           *
     *    tutorial book, reference manual, or both:                          *
     *    http://www.FreeRTOS.org/Documentation                              *
     *                                                                       *
    ***************************************************************************

    http://www.FreeRTOS.org/FAQHelp.html - Having a problem?  Start by reading
    the FAQ page "My application does not run, what could be wrong?".  Have you
    defined configASSERT()?

    http://www.FreeRTOS.org/support - In return for receiving this top quality
    embedded software for free we request you assist our global community by
    participating in the support forum.

    http://www.FreeRTOS.org/training - Investing in training allows your team to
    be as productive as possible as early as possible.  Now you can receive
    FreeRTOS training directly from Richard Barry, CEO of Real Time Engineers
    Ltd, and the world's leading authority on the world's leading RTOS.

    http://www.FreeRTOS.org/plus - A selection of FreeRTOS ecosystem products,
    including FreeRTOS+Trace - an indispensable productivity tool, a DOS
    compatible FAT file system, and our tiny thread aware UDP/IP stack.

    http://www.FreeRTOS.org/labs - Where new FreeRTOS products go to incubate.
    Come and try FreeRTOS+TCP, our new open source TCP/IP stack for FreeRTOS.

    http://www.OpenRTOS.com - Real Time Engineers ltd. license FreeRTOS to High
    Integrity Systems ltd. to sell under the OpenRTOS brand.  Low cost OpenRTOS
    licenses offer ticketed support, indemnification and commercial middleware.

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
#define portBASE_TYPE	portLONG

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
#define portSTACK_GROWTH			( -1 )
#define portTICK_PERIOD_MS			( ( TickType_t ) 1000 / configTICK_RATE_HZ )
#define portBYTE_ALIGNMENT			8
#define portNOP()					__asm volatile ( "NOP" );
/*-----------------------------------------------------------*/


/* Scheduler utilities. */

/*
 * portRESTORE_CONTEXT, portRESTORE_CONTEXT, portENTER_SWITCHING_ISR
 * and portEXIT_SWITCHING_ISR can only be called from ARM mode, but
 * are included here for efficiency.  An attempt to call one from
 * THUMB mode code will result in a compile time error.
 */

#define portRESTORE_CONTEXT()											\
{																		\
extern volatile void * volatile pxCurrentTCB;							\
extern volatile uint32_t ulCriticalNesting;					\
																		\
	/* Set the LR to the task stack. */									\
	__asm volatile (													\
	"LDR		R0, =pxCurrentTCB								\n\t"	\
	"LDR		R0, [R0]										\n\t"	\
	"LDR		LR, [R0]										\n\t"	\
																		\
	/* The critical nesting depth is the first item on the stack. */	\
	/* Load it into the ulCriticalNesting variable. */					\
	"LDR		R0, =ulCriticalNesting							\n\t"	\
	"LDMFD	LR!, {R1}											\n\t"	\
	"STR		R1, [R0]										\n\t"	\
																		\
	/* Get the SPSR from the stack. */									\
	"LDMFD	LR!, {R0}											\n\t"	\
	"MSR		SPSR, R0										\n\t"	\
																		\
	/* Restore all system mode registers for the task. */				\
	"LDMFD	LR, {R0-R14}^										\n\t"	\
	"NOP														\n\t"	\
																		\
	/* Restore the return address. */									\
	"LDR		LR, [LR, #+60]									\n\t"	\
																		\
	/* And return - correcting the offset in the LR to obtain the */	\
	/* correct address. */												\
	"SUBS	PC, LR, #4											\n\t"	\
	);																	\
	( void ) ulCriticalNesting;											\
	( void ) pxCurrentTCB;												\
}
/*-----------------------------------------------------------*/

#define portSAVE_CONTEXT()												\
{																		\
extern volatile void * volatile pxCurrentTCB;							\
extern volatile uint32_t ulCriticalNesting;					\
																		\
	/* Push R0 as we are going to use the register. */					\
	__asm volatile (													\
	"STMDB	SP!, {R0}											\n\t"	\
																		\
	/* Set R0 to point to the task stack pointer. */					\
	"STMDB	SP,{SP}^											\n\t"	\
	"NOP														\n\t"	\
	"SUB	SP, SP, #4											\n\t"	\
	"LDMIA	SP!,{R0}											\n\t"	\
																		\
	/* Push the return address onto the stack. */						\
	"STMDB	R0!, {LR}											\n\t"	\
																		\
	/* Now we have saved LR we can use it instead of R0. */				\
	"MOV	LR, R0												\n\t"	\
																		\
	/* Pop R0 so we can save it onto the system mode stack. */			\
	"LDMIA	SP!, {R0}											\n\t"	\
																		\
	/* Push all the system mode registers onto the task stack. */		\
	"STMDB	LR,{R0-LR}^											\n\t"	\
	"NOP														\n\t"	\
	"SUB	LR, LR, #60											\n\t"	\
																		\
	/* Push the SPSR onto the task stack. */							\
	"MRS	R0, SPSR											\n\t"	\
	"STMDB	LR!, {R0}											\n\t"	\
																		\
	"LDR	R0, =ulCriticalNesting								\n\t"	\
	"LDR	R0, [R0]											\n\t"	\
	"STMDB	LR!, {R0}											\n\t"	\
																		\
	/* Store the new top of stack for the task. */						\
	"LDR	R0, =pxCurrentTCB									\n\t"	\
	"LDR	R0, [R0]											\n\t"	\
	"STR	LR, [R0]											\n\t"	\
	);																	\
	( void ) ulCriticalNesting;											\
	( void ) pxCurrentTCB;												\
}

extern void vTaskSwitchContext( void );
#define portYIELD_FROM_ISR()		vTaskSwitchContext()
#define portYIELD()					__asm volatile ( "SWI 0" )
/*-----------------------------------------------------------*/


/* Critical section management. */

/*
 * The interrupt management utilities can only be called from ARM mode.  When
 * THUMB_INTERWORK is defined the utilities are defined as functions in
 * portISR.c to ensure a switch to ARM mode.  When THUMB_INTERWORK is not
 * defined then the utilities are defined as macros here - as per other ports.
 */

#ifdef THUMB_INTERWORK

	extern void vPortDisableInterruptsFromThumb( void ) __attribute__ ((naked));
	extern void vPortEnableInterruptsFromThumb( void ) __attribute__ ((naked));

	#define portDISABLE_INTERRUPTS()	vPortDisableInterruptsFromThumb()
	#define portENABLE_INTERRUPTS()		vPortEnableInterruptsFromThumb()

#else

	#define portDISABLE_INTERRUPTS()											\
		__asm volatile (														\
			"STMDB	SP!, {R0}		\n\t"	/* Push R0.						*/	\
			"MRS	R0, CPSR		\n\t"	/* Get CPSR.					*/	\
			"ORR	R0, R0, #0xC0	\n\t"	/* Disable IRQ, FIQ.			*/	\
			"MSR	CPSR, R0		\n\t"	/* Write back modified value.	*/	\
			"LDMIA	SP!, {R0}			" )	/* Pop R0.						*/

	#define portENABLE_INTERRUPTS()												\
		__asm volatile (														\
			"STMDB	SP!, {R0}		\n\t"	/* Push R0.						*/	\
			"MRS	R0, CPSR		\n\t"	/* Get CPSR.					*/	\
			"BIC	R0, R0, #0xC0	\n\t"	/* Enable IRQ, FIQ.				*/	\
			"MSR	CPSR, R0		\n\t"	/* Write back modified value.	*/	\
			"LDMIA	SP!, {R0}			" )	/* Pop R0.						*/

#endif /* THUMB_INTERWORK */

extern void vPortEnterCritical( void );
extern void vPortExitCritical( void );

#define portENTER_CRITICAL()		vPortEnterCritical();
#define portEXIT_CRITICAL()			vPortExitCritical();
/*-----------------------------------------------------------*/

/* Task function macros as described on the FreeRTOS.org WEB site. */
#define portTASK_FUNCTION_PROTO( vFunction, pvParameters ) void vFunction( void *pvParameters )
#define portTASK_FUNCTION( vFunction, pvParameters ) void vFunction( void *pvParameters )

#ifdef __cplusplus
}
#endif

#endif /* PORTMACRO_H */

