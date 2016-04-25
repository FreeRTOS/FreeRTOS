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
 * The settings in this file configure FreeRTOS correctly for the given hardware
 * and compiler.
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

typedef uint32_t TickType_t;
#define portMAX_DELAY ( TickType_t ) 0xffffffffUL

/* 32-bit tick type on a 32-bit architecture, so reads of the tick count do
not need to be guarded with a critical section. */
#define portTICK_TYPE_IS_ATOMIC 1

/*-----------------------------------------------------------*/

/* Hardware specifics. */
#define portSTACK_GROWTH			( -1 )
#define portTICK_PERIOD_MS			( ( TickType_t ) 1000 / configTICK_RATE_HZ )
#define portBYTE_ALIGNMENT			8

/*-----------------------------------------------------------*/

/* Task utilities. */

/* Called at the end of an ISR that can cause a context switch. */
#define portEND_SWITCHING_ISR( xSwitchRequired )\
{												\
extern uint32_t ulPortYieldRequired;			\
												\
	if( xSwitchRequired != pdFALSE )			\
	{											\
		ulPortYieldRequired = pdTRUE;			\
	}											\
}

#define portYIELD_FROM_ISR( x ) portEND_SWITCHING_ISR( x )
#define portYIELD() __asm volatile ( "SWI 0" );


/*-----------------------------------------------------------
 * Critical section control
 *----------------------------------------------------------*/

extern void vPortEnterCritical( void );
extern void vPortExitCritical( void );
extern uint32_t ulPortSetInterruptMask( void );
extern void vPortClearInterruptMask( uint32_t ulNewMaskValue );
extern void vPortInstallFreeRTOSVectorTable( void );

/* These macros do not globally disable/enable interrupts.  They do mask off
interrupts that have a priority below configMAX_API_CALL_INTERRUPT_PRIORITY. */
#define portENTER_CRITICAL()		vPortEnterCritical();
#define portEXIT_CRITICAL()			vPortExitCritical();
#define portDISABLE_INTERRUPTS()	ulPortSetInterruptMask()
#define portENABLE_INTERRUPTS()		vPortClearInterruptMask( 0 )
#define portSET_INTERRUPT_MASK_FROM_ISR()		ulPortSetInterruptMask()
#define portCLEAR_INTERRUPT_MASK_FROM_ISR(x)	vPortClearInterruptMask(x)

/*-----------------------------------------------------------*/

/* Task function macros as described on the FreeRTOS.org WEB site.  These are
not required for this port but included in case common demo code that uses these
macros is used. */
#define portTASK_FUNCTION_PROTO( vFunction, pvParameters )	void vFunction( void *pvParameters )
#define portTASK_FUNCTION( vFunction, pvParameters )	void vFunction( void *pvParameters )

/* Prototype of the FreeRTOS tick handler.  This must be installed as the
handler for whichever peripheral is used to generate the RTOS tick. */
void FreeRTOS_Tick_Handler( void );

/* If configUSE_TASK_FPU_SUPPORT is set to 1 (or left undefined) then tasks are
created without an FPU context and must call vPortTaskUsesFPU() to give
themselves an FPU context before using any FPU instructions.  If
configUSE_TASK_FPU_SUPPORT is set to 2 then all tasks will have an FPU context
by default. */
#if( configUSE_TASK_FPU_SUPPORT != 2 )
	void vPortTaskUsesFPU( void );
#else
	/* Each task has an FPU context already, so define this function away to
	nothing to prevent it being called accidentally. */
	#define vPortTaskUsesFPU()
#endif
#define portTASK_USES_FLOATING_POINT() vPortTaskUsesFPU()

#define portLOWEST_INTERRUPT_PRIORITY ( ( ( uint32_t ) configUNIQUE_INTERRUPT_PRIORITIES ) - 1UL )
#define portLOWEST_USABLE_INTERRUPT_PRIORITY ( portLOWEST_INTERRUPT_PRIORITY - 1UL )

/* Architecture specific optimisations. */
#ifndef configUSE_PORT_OPTIMISED_TASK_SELECTION
	#define configUSE_PORT_OPTIMISED_TASK_SELECTION 1
#endif

#if configUSE_PORT_OPTIMISED_TASK_SELECTION == 1

	/* Store/clear the ready priorities in a bit map. */
	#define portRECORD_READY_PRIORITY( uxPriority, uxReadyPriorities ) ( uxReadyPriorities ) |= ( 1UL << ( uxPriority ) )
	#define portRESET_READY_PRIORITY( uxPriority, uxReadyPriorities ) ( uxReadyPriorities ) &= ~( 1UL << ( uxPriority ) )

	/*-----------------------------------------------------------*/

	#define portGET_HIGHEST_PRIORITY( uxTopPriority, uxReadyPriorities ) uxTopPriority = ( 31UL - ( uint32_t ) __builtin_clz( uxReadyPriorities ) )

#endif /* configUSE_PORT_OPTIMISED_TASK_SELECTION */

#ifdef configASSERT
	void vPortValidateInterruptPriority( void );
	#define portASSERT_IF_INTERRUPT_PRIORITY_INVALID() 	vPortValidateInterruptPriority()
#endif /* configASSERT */

#define portNOP() __asm volatile( "NOP" )
#define portINLINE __inline

#ifdef __cplusplus
	} /* extern C */
#endif


/* The number of bits to shift for an interrupt priority is dependent on the
number of bits implemented by the interrupt controller. */
#if configUNIQUE_INTERRUPT_PRIORITIES == 16
	#define portPRIORITY_SHIFT 4
	#define portMAX_BINARY_POINT_VALUE	3
#elif configUNIQUE_INTERRUPT_PRIORITIES == 32
	#define portPRIORITY_SHIFT 3
	#define portMAX_BINARY_POINT_VALUE	2
#elif configUNIQUE_INTERRUPT_PRIORITIES == 64
	#define portPRIORITY_SHIFT 2
	#define portMAX_BINARY_POINT_VALUE	1
#elif configUNIQUE_INTERRUPT_PRIORITIES == 128
	#define portPRIORITY_SHIFT 1
	#define portMAX_BINARY_POINT_VALUE	0
#elif configUNIQUE_INTERRUPT_PRIORITIES == 256
	#define portPRIORITY_SHIFT 0
	#define portMAX_BINARY_POINT_VALUE	0
#else
	#error Invalid configUNIQUE_INTERRUPT_PRIORITIES setting.  configUNIQUE_INTERRUPT_PRIORITIES must be set to the number of unique priorities implemented by the target hardware
#endif

/* Interrupt controller access addresses. */
#define portICCPMR_PRIORITY_MASK_OFFSET  						( 0x04 )
#define portICCIAR_INTERRUPT_ACKNOWLEDGE_OFFSET 				( 0x0C )
#define portICCEOIR_END_OF_INTERRUPT_OFFSET 					( 0x10 )
#define portICCBPR_BINARY_POINT_OFFSET							( 0x08 )
#define portICCRPR_RUNNING_PRIORITY_OFFSET						( 0x14 )

#define portINTERRUPT_CONTROLLER_CPU_INTERFACE_ADDRESS 		( configINTERRUPT_CONTROLLER_BASE_ADDRESS + configINTERRUPT_CONTROLLER_CPU_INTERFACE_OFFSET )
#define portICCPMR_PRIORITY_MASK_REGISTER 					( *( ( volatile uint32_t * ) ( portINTERRUPT_CONTROLLER_CPU_INTERFACE_ADDRESS + portICCPMR_PRIORITY_MASK_OFFSET ) ) )
#define portICCIAR_INTERRUPT_ACKNOWLEDGE_REGISTER_ADDRESS 	( portINTERRUPT_CONTROLLER_CPU_INTERFACE_ADDRESS + portICCIAR_INTERRUPT_ACKNOWLEDGE_OFFSET )
#define portICCEOIR_END_OF_INTERRUPT_REGISTER_ADDRESS 		( portINTERRUPT_CONTROLLER_CPU_INTERFACE_ADDRESS + portICCEOIR_END_OF_INTERRUPT_OFFSET )
#define portICCPMR_PRIORITY_MASK_REGISTER_ADDRESS 			( portINTERRUPT_CONTROLLER_CPU_INTERFACE_ADDRESS + portICCPMR_PRIORITY_MASK_OFFSET )
#define portICCBPR_BINARY_POINT_REGISTER 					( *( ( const volatile uint32_t * ) ( portINTERRUPT_CONTROLLER_CPU_INTERFACE_ADDRESS + portICCBPR_BINARY_POINT_OFFSET ) ) )
#define portICCRPR_RUNNING_PRIORITY_REGISTER 				( *( ( const volatile uint32_t * ) ( portINTERRUPT_CONTROLLER_CPU_INTERFACE_ADDRESS + portICCRPR_RUNNING_PRIORITY_OFFSET ) ) )

#endif /* PORTMACRO_H */

