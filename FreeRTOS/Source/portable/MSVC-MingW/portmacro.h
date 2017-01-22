/*
    FreeRTOS V9.0.1 - Copyright (C) 2017 Real Time Engineers Ltd.
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

#include <Windows.h>
#include <WinBase.h>

/******************************************************************************
	Defines
******************************************************************************/
/* Type definitions. */
#define portCHAR		char
#define portFLOAT		float
#define portDOUBLE		double
#define portLONG		long
#define portSHORT		short
#define portSTACK_TYPE	size_t
#define portBASE_TYPE	long
#define portPOINTER_SIZE_TYPE size_t

typedef portSTACK_TYPE StackType_t;
typedef long BaseType_t;
typedef unsigned long UBaseType_t;


#if( configUSE_16_BIT_TICKS == 1 )
    typedef uint16_t TickType_t;
    #define portMAX_DELAY ( TickType_t ) 0xffff
#else
    typedef uint32_t TickType_t;
    #define portMAX_DELAY ( TickType_t ) 0xffffffffUL

	/* 32/64-bit tick type on a 32/64-bit architecture, so reads of the tick
	count do not need to be guarded with a critical section. */
	#define portTICK_TYPE_IS_ATOMIC 1
#endif

/* Hardware specifics. */
#define portSTACK_GROWTH			( -1 )
#define portTICK_PERIOD_MS			( ( TickType_t ) 1000 / configTICK_RATE_HZ )
#define portINLINE __inline

#if defined( __x86_64__) || defined( _M_X64 )
	#define portBYTE_ALIGNMENT		8
#else
	#define portBYTE_ALIGNMENT		4
#endif

#define portYIELD()					vPortGenerateSimulatedInterrupt( portINTERRUPT_YIELD )

/* Simulated interrupts return pdFALSE if no context switch should be performed,
or a non-zero number if a context switch should be performed. */
#define portYIELD_FROM_ISR( x ) return x
#define portEND_SWITCHING_ISR( x ) portYIELD_FROM_ISR( ( x ) )

void vPortCloseRunningThread( void *pvTaskToDelete, volatile BaseType_t *pxPendYield );
void vPortDeleteThread( void *pvThreadToDelete );
#define portCLEAN_UP_TCB( pxTCB )	vPortDeleteThread( pxTCB )
#define portPRE_TASK_DELETE_HOOK( pvTaskToDelete, pxPendYield ) vPortCloseRunningThread( ( pvTaskToDelete ), ( pxPendYield ) )
#define portDISABLE_INTERRUPTS() vPortEnterCritical()
#define portENABLE_INTERRUPTS() vPortExitCritical()

/* Critical section handling. */
void vPortEnterCritical( void );
void vPortExitCritical( void );

#define portENTER_CRITICAL()		vPortEnterCritical()
#define portEXIT_CRITICAL()			vPortExitCritical()

#ifndef configUSE_PORT_OPTIMISED_TASK_SELECTION
	#define configUSE_PORT_OPTIMISED_TASK_SELECTION 1
#endif

#if configUSE_PORT_OPTIMISED_TASK_SELECTION == 1

	/* Check the configuration. */
	#if( configMAX_PRIORITIES > 32 )
		#error configUSE_PORT_OPTIMISED_TASK_SELECTION can only be set to 1 when configMAX_PRIORITIES is less than or equal to 32.  It is very rare that a system requires more than 10 to 15 difference priorities as tasks that share a priority will time slice.
	#endif

	/* Store/clear the ready priorities in a bit map. */
	#define portRECORD_READY_PRIORITY( uxPriority, uxReadyPriorities ) ( uxReadyPriorities ) |= ( 1UL << ( uxPriority ) )
	#define portRESET_READY_PRIORITY( uxPriority, uxReadyPriorities ) ( uxReadyPriorities ) &= ~( 1UL << ( uxPriority ) )


	/*-----------------------------------------------------------*/

	#ifdef __GNUC__
		#define portGET_HIGHEST_PRIORITY( uxTopPriority, uxReadyPriorities )	\
			__asm volatile(	"bsr %1, %0\n\t" 									\
							:"=r"(uxTopPriority) : "rm"(uxReadyPriorities) : "cc" )
	#else
		/* BitScanReverse returns the bit position of the most significant '1'
		in the word. */
		#define portGET_HIGHEST_PRIORITY( uxTopPriority, uxReadyPriorities ) _BitScanReverse( ( DWORD * ) &( uxTopPriority ), ( uxReadyPriorities ) )
	#endif /* __GNUC__ */

#endif /* taskRECORD_READY_PRIORITY */

#ifndef __GNUC__
	__pragma( warning( disable:4211 ) ) /* Nonstandard extension used, as extern is only nonstandard to MSVC. */
#endif


/* Task function macros as described on the FreeRTOS.org WEB site. */
#define portTASK_FUNCTION_PROTO( vFunction, pvParameters ) void vFunction( void * pvParameters )
#define portTASK_FUNCTION( vFunction, pvParameters ) void vFunction( void * pvParameters )

#define portINTERRUPT_YIELD				( 0UL )
#define portINTERRUPT_TICK				( 1UL )

/*
 * Raise a simulated interrupt represented by the bit mask in ulInterruptMask.
 * Each bit can be used to represent an individual interrupt - with the first
 * two bits being used for the Yield and Tick interrupts respectively.
*/
void vPortGenerateSimulatedInterrupt( uint32_t ulInterruptNumber );

/*
 * Install an interrupt handler to be called by the simulated interrupt handler
 * thread.  The interrupt number must be above any used by the kernel itself
 * (at the time of writing the kernel was using interrupt numbers 0, 1, and 2
 * as defined above).  The number must also be lower than 32.
 *
 * Interrupt handler functions must return a non-zero value if executing the
 * handler resulted in a task switch being required.
 */
void vPortSetInterruptHandler( uint32_t ulInterruptNumber, uint32_t (*pvHandler)( void ) );

#endif

