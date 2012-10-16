/*
    FreeRTOS V7.3.0 - Copyright (C) 2012 Real Time Engineers Ltd.

    FEATURES AND PORTS ARE ADDED TO FREERTOS ALL THE TIME.  PLEASE VISIT 
    http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

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
    
    ***************************************************************************
     *                                                                       *
     *    Having a problem?  Start by reading the FAQ "My application does   *
     *    not run, what could be wrong?"                                     *
     *                                                                       *
     *    http://www.FreeRTOS.org/FAQHelp.html                               *
     *                                                                       *
    ***************************************************************************

    
    http://www.FreeRTOS.org - Documentation, training, latest versions, license 
    and contact details.  
    
    http://www.FreeRTOS.org/plus - A selection of FreeRTOS ecosystem products,
    including FreeRTOS+Trace - an indispensable productivity tool.

    Real Time Engineers ltd license FreeRTOS to High Integrity Systems, who sell 
    the code with commercial support, indemnification, and middleware, under 
    the OpenRTOS brand: http://www.OpenRTOS.com.  High Integrity Systems also
    provide a safety engineered and independently SIL3 certified version under 
    the SafeRTOS brand: http://www.SafeRTOS.com.
*/


#ifndef PORTMACRO_H
#define PORTMACRO_H

#include <machine.h>

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
#define portSTACK_TYPE	unsigned portLONG
#define portBASE_TYPE	long

#if( configUSE_16_BIT_TICKS == 1 )
	typedef unsigned portSHORT portTickType;
	#define portMAX_DELAY ( portTickType ) 0xffff
#else
	typedef unsigned portLONG portTickType;
	#define portMAX_DELAY ( portTickType ) 0xffffffff
#endif
/*-----------------------------------------------------------*/

/* Hardware specifics. */
#define portBYTE_ALIGNMENT				8
#define portSTACK_GROWTH				-1
#define portTICK_RATE_MS				( ( portTickType ) 1000 / configTICK_RATE_HZ )		
#define portNOP()						nop()
#define portSTART_SCHEDULER_TRAP_NO		( 32 )
#define portYIELD_TRAP_NO				( 33 )
#define portKERNEL_INTERRUPT_PRIORITY	( 1 )

void vPortYield( void );
#define portYIELD()						vPortYield()

extern void vTaskSwitchContext( void );
#define portYIELD_FROM_ISR( x )			if( x != pdFALSE ) vTaskSwitchContext()

/* 
 * This function tells the kernel that the task referenced by xTask is going to 
 * use the floating point registers and therefore requires the floating point 
 * registers saved as part of its context. 
 */
portBASE_TYPE xPortUsesFloatingPoint( void* xTask );

/*
 * The flop save and restore functions are defined in portasm.src and called by
 * the trace "task switched in" and "trace task switched out" macros. 
 */
void vPortSaveFlopRegisters( void *pulBuffer );
void vPortRestoreFlopRegisters( void *pulBuffer );

/*
 * pxTaskTag is used to point to the buffer into which the floating point 
 * context should be saved.  If pxTaskTag is NULL then the task does not use
 * a floating point context.
 */
#define traceTASK_SWITCHED_OUT() if( pxCurrentTCB->pxTaskTag != NULL ) vPortSaveFlopRegisters( pxCurrentTCB->pxTaskTag )
#define traceTASK_SWITCHED_IN() if( pxCurrentTCB->pxTaskTag != NULL ) vPortRestoreFlopRegisters( pxCurrentTCB->pxTaskTag )

/*
 * These macros should be called directly, but through the taskENTER_CRITICAL()
 * and taskEXIT_CRITICAL() macros.
 */
#define portENABLE_INTERRUPTS() 	set_imask( 0x00 )
#define portDISABLE_INTERRUPTS() 	set_imask( portKERNEL_INTERRUPT_PRIORITY )

/* Critical nesting counts are stored in the TCB. */
#define portCRITICAL_NESTING_IN_TCB ( 1 )

/* The critical nesting functions defined within tasks.c. */
extern void vTaskEnterCritical( void );
extern void vTaskExitCritical( void );
#define portENTER_CRITICAL()	vTaskEnterCritical();
#define portEXIT_CRITICAL()		vTaskExitCritical();

/*-----------------------------------------------------------*/

/* Task function macros as described on the FreeRTOS.org WEB site. */
#define portTASK_FUNCTION_PROTO( vFunction, pvParameters ) void vFunction( void *pvParameters )
#define portTASK_FUNCTION( vFunction, pvParameters ) void vFunction( void *pvParameters )

#ifdef __cplusplus
}
#endif

#endif /* PORTMACRO_H */

