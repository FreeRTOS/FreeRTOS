/*
    FreeRTOS V7.4.2 - Copyright (C) 2013 Real Time Engineers Ltd.

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

    >>>>>>NOTE<<<<<< The modification to the GPL is included to allow you to
    distribute a combined work that includes FreeRTOS without being obliged to
    provide the source code for proprietary components outside of the FreeRTOS
    kernel.

    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT ANY
    WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
    FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more
    details. You should have received a copy of the GNU General Public License
    and the FreeRTOS license exception along with FreeRTOS; if not it can be
    viewed here: http://www.freertos.org/a00114.html and also obtained by
    writing to Real Time Engineers Ltd., contact details for whom are available
    on the FreeRTOS WEB site.

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
    including FreeRTOS+Trace - an indispensable productivity tool, and our new
    fully thread aware and reentrant UDP/IP stack.

    http://www.OpenRTOS.com - Real Time Engineers ltd license FreeRTOS to High 
    Integrity Systems, who sell the code with commercial support, 
    indemnification and middleware, under the OpenRTOS brand.
    
    http://www.SafeRTOS.com - High Integrity Systems also provide a safety 
    engineered and independently SIL3 certified version for use in safety and 
    mission critical applications that require provable dependability.
*/

#ifndef PORTMACRO_H
#define PORTMACRO_H

/* System include files */
#include <xc.h>

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
configMAX_SYSCALL_INTERRUPT_PRIORITY.  	An extra check is performed if 
configASSERT() is defined to ensure an assertion handler does not inadvertently 
attempt to lower the IPL when the call to assert was triggered because the IPL 
value was found to be above	configMAX_SYSCALL_INTERRUPT_PRIORITY when an ISR
safe FreeRTOS API function was executed.  ISR safe FreeRTOS API functions are
those that end in FromISR.  FreeRTOS maintains a separate interrupt API to
ensure API function and interrupt entry is as fast and as simple as possible. */
#ifdef configASSERT
	#define portDISABLE_INTERRUPTS()											\
	{																			\
	unsigned long ulStatus;														\
																				\
		/* Mask interrupts at and below the kernel interrupt priority. */		\
		ulStatus = _CP0_GET_STATUS();											\
																				\
		/* Is the current IPL below configMAX_SYSCALL_INTERRUPT_PRIORITY? */	\
		if( ( ( ulStatus & portALL_IPL_BITS ) >> portIPL_SHIFT ) < configMAX_SYSCALL_INTERRUPT_PRIORITY )	\
		{																		\
			ulStatus &= ~portALL_IPL_BITS;										\
			_CP0_SET_STATUS( ( ulStatus | ( configMAX_SYSCALL_INTERRUPT_PRIORITY << portIPL_SHIFT ) ) ); \
		}																		\
	}
#else /* configASSERT */
	#define portDISABLE_INTERRUPTS()										\
	{																		\
	unsigned long ulStatus;													\
																			\
		/* Mask interrupts at and below the kernel interrupt priority. */	\
		ulStatus = _CP0_GET_STATUS();										\
		ulStatus &= ~portALL_IPL_BITS;										\
		_CP0_SET_STATUS( ( ulStatus | ( configMAX_SYSCALL_INTERRUPT_PRIORITY << portIPL_SHIFT ) ) ); \
	}
#endif /* configASSERT */

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

#if configUSE_PORT_OPTIMISED_TASK_SELECTION == 1

	/* Check the configuration. */
	#if( configMAX_PRIORITIES > 32 )
		#error configUSE_PORT_OPTIMISED_TASK_SELECTION can only be set to 1 when configMAX_PRIORITIES is less than or equal to 32.  It is very rare that a system requires more than 10 to 15 difference priorities as tasks that share a priority will time slice.
	#endif

	/* Store/clear the ready priorities in a bit map. */
	#define portRECORD_READY_PRIORITY( uxPriority, uxReadyPriorities ) ( uxReadyPriorities ) |= ( 1UL << ( uxPriority ) )
	#define portRESET_READY_PRIORITY( uxPriority, uxReadyPriorities ) ( uxReadyPriorities ) &= ~( 1UL << ( uxPriority ) )

	/*-----------------------------------------------------------*/

	#define portGET_HIGHEST_PRIORITY( uxTopPriority, uxReadyPriorities ) uxTopPriority = ( 31 - _clz( ( uxReadyPriorities ) ) )

#endif /* taskRECORD_READY_PRIORITY */

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

#ifdef configASSERT
	#define portCURRENT_INTERRUPT_PRIORITY ( ( _CP0_GET_STATUS() & portALL_IPL_BITS ) >> portIPL_SHIFT )
	#define portASSERT_IF_INTERRUPT_PRIORITY_INVALID() configASSERT( portCURRENT_INTERRUPT_PRIORITY <= configMAX_SYSCALL_INTERRUPT_PRIORITY )
#endif /* configASSERT */


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

