/*
    FreeRTOS V7.1.1 - Copyright (C) 2012 Real Time Engineers Ltd.
	

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
     *    not run, what could be wrong?                                      *
     *                                                                       *
     *    http://www.FreeRTOS.org/FAQHelp.html                               *
     *                                                                       *
    ***************************************************************************

    
    http://www.FreeRTOS.org - Documentation, training, latest information, 
    license and contact details.
    
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

/* System include files */
#include <plib.h>

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
#define portSTACK_TYPE	unsigned long
#define portBASE_TYPE	long

#if( configUSE_16_BIT_TICKS == 1 )
	typedef unsigned portSHORT portTickType;
	#define portMAX_DELAY ( portTickType ) 0xffff
#else
	typedef unsigned long portTickType;
	#define portMAX_DELAY ( portTickType ) 0xffffffff
#endif
/*-----------------------------------------------------------*/

/* Hardware specifics. */
#define portBYTE_ALIGNMENT			8
#define portSTACK_GROWTH			-1
#define portTICK_RATE_MS			( ( portTickType ) 1000 / configTICK_RATE_HZ )		
/*-----------------------------------------------------------*/

/* Critical section management. */
#define portIPL_SHIFT				( 10UL )
#define portALL_IPL_BITS			( 0x3fUL << portIPL_SHIFT )
#define portSW0_BIT					( 0x01 << 8 )

/* This clears the IPL bits, then sets them to 
configMAX_SYSCALL_INTERRUPT_PRIORITY.  This function should not be called
from an interrupt, so therefore will not be called with an IPL setting
above configMAX_SYSCALL_INTERRUPT_PRIORITY.  Therefore, when used correctly, the 
instructions in this macro can only result in the IPL being raised, and 
therefore never lowered. */
#define portDISABLE_INTERRUPTS()										\
{																		\
unsigned long ulStatus;													\
																		\
	/* Mask interrupts at and below the kernel interrupt priority. */	\
	ulStatus = _CP0_GET_STATUS();										\
	ulStatus &= ~portALL_IPL_BITS;										\
	_CP0_SET_STATUS( ( ulStatus | ( configMAX_SYSCALL_INTERRUPT_PRIORITY << portIPL_SHIFT ) ) ); \
}

#define portENABLE_INTERRUPTS()											\
{																		\
unsigned long ulStatus;													\
																		\
	/* Unmask all interrupts. */										\
	ulStatus = _CP0_GET_STATUS();										\
	ulStatus &= ~portALL_IPL_BITS;										\
	_CP0_SET_STATUS( ulStatus );										\
}


extern void vTaskEnterCritical( void );
extern void vTaskExitCritical( void );
#define portCRITICAL_NESTING_IN_TCB	1
#define portENTER_CRITICAL()		vTaskEnterCritical()
#define portEXIT_CRITICAL()			vTaskExitCritical()

extern unsigned portBASE_TYPE uxPortSetInterruptMaskFromISR();
extern void vPortClearInterruptMaskFromISR( unsigned portBASE_TYPE );
#define portSET_INTERRUPT_MASK_FROM_ISR() uxPortSetInterruptMaskFromISR()
#define portCLEAR_INTERRUPT_MASK_FROM_ISR( uxSavedStatusRegister ) vPortClearInterruptMaskFromISR( uxSavedStatusRegister )

/*-----------------------------------------------------------*/

/* Task utilities. */

#define portYIELD()								\
{												\
unsigned long ulStatus;							\
												\
	/* Trigger software interrupt. */			\
	ulStatus = _CP0_GET_CAUSE();				\
	ulStatus |= portSW0_BIT;					\
	_CP0_SET_CAUSE( ulStatus );					\
}


#define portNOP()	asm volatile ( 	"nop" )

/*-----------------------------------------------------------*/

/* Task function macros as described on the FreeRTOS.org WEB site. */
#define portTASK_FUNCTION_PROTO( vFunction, pvParameters ) void vFunction( void *pvParameters ) __attribute__((noreturn))
#define portTASK_FUNCTION( vFunction, pvParameters ) void vFunction( void *pvParameters )
/*-----------------------------------------------------------*/

#define portEND_SWITCHING_ISR( xSwitchRequired )	if( xSwitchRequired )	\
													{						\
														portYIELD();		\
													}

/* Required by the kernel aware debugger. */
#ifdef __DEBUG
	#define portREMOVE_STATIC_QUALIFIER
#endif

#ifdef __cplusplus
}
#endif

#endif /* PORTMACRO_H */

