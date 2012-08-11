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
#define portSTACK_TYPE	unsigned portCHAR
#define portBASE_TYPE	char

#if( configUSE_16_BIT_TICKS == 1 )
	typedef unsigned portSHORT portTickType;
	#define portMAX_DELAY ( portTickType ) 0xffff
#else
	typedef unsigned portLONG portTickType;
	#define portMAX_DELAY ( portTickType ) 0xffffffff
#endif
/*-----------------------------------------------------------*/

/* Hardware specifics. */
#define portBYTE_ALIGNMENT			1
#define portSTACK_GROWTH			( -1 )
#define portTICK_RATE_MS			( ( portTickType ) 1000 / configTICK_RATE_HZ )		
#define portYIELD()					__asm( "swi" );
#define portNOP()					__asm( "nop" );
/*-----------------------------------------------------------*/

/* Critical section handling. */
#define portENABLE_INTERRUPTS()				__asm( "cli" )	
#define portDISABLE_INTERRUPTS()			__asm( "sei" )

/*
 * Disable interrupts before incrementing the count of critical section nesting.
 * The nesting count is maintained so we know when interrupts should be
 * re-enabled.  Once interrupts are disabled the nesting count can be accessed
 * directly.  Each task maintains its own nesting count.
 */
#define portENTER_CRITICAL()  									\
{																\
	extern volatile unsigned portBASE_TYPE uxCriticalNesting;	\
																\
	portDISABLE_INTERRUPTS();									\
	uxCriticalNesting++;										\
}

/*
 * Interrupts are disabled so we can access the nesting count directly.  If the
 * nesting is found to be 0 (no nesting) then we are leaving the critical 
 * section and interrupts can be re-enabled.
 */
#define  portEXIT_CRITICAL()									\
{																\
	extern volatile unsigned portBASE_TYPE uxCriticalNesting;	\
																\
	uxCriticalNesting--;										\
	if( uxCriticalNesting == 0 )								\
	{															\
		portENABLE_INTERRUPTS();								\
	}															\
}
/*-----------------------------------------------------------*/

/* Task utilities. */

/* 
 * These macros are very simple as the processor automatically saves and 
 * restores its registers as interrupts are entered and exited.  In
 * addition to the (automatically stacked) registers we also stack the 
 * critical nesting count.  Each task maintains its own critical nesting
 * count as it is legitimate for a task to yield from within a critical
 * section.  If the banked memory model is being used then the PPAGE
 * register is also stored as part of the tasks context.
 */

#ifdef BANKED_MODEL
	/* 
	 * Load the stack pointer for the task, then pull the critical nesting
	 * count and PPAGE register from the stack.  The remains of the 
	 * context are restored by the RTI instruction.
	 */
	#define portRESTORE_CONTEXT()									\
	{																\
		extern volatile void * pxCurrentTCB;						\
		extern volatile unsigned portBASE_TYPE uxCriticalNesting;	\
																	\
		__asm( "ldx pxCurrentTCB" );								\
		__asm( "lds 0, x" );										\
		__asm( "pula" );											\
		__asm( "staa uxCriticalNesting" );							\
		__asm( "pula" );											\
		__asm( "staa 0x30" ); /* 0x30 = PPAGE */					\
	}

	/* 
	 * By the time this macro is called the processor has already stacked the
	 * registers.  Simply stack the nesting count and PPAGE value, then save 
	 * the task stack pointer.
	 */
	#define portSAVE_CONTEXT()										\
	{																\
		extern volatile void * pxCurrentTCB;						\
		extern volatile unsigned portBASE_TYPE uxCriticalNesting;	\
																	\
		__asm( "ldaa 0x30" );  /* 0x30 = PPAGE */					\
		__asm( "psha" );											\
		__asm( "ldaa uxCriticalNesting" );							\
		__asm( "psha" );											\
		__asm( "ldx pxCurrentTCB" );								\
		__asm( "sts 0, x" );										\
	}
#else

	/* 
	 * These macros are as per the BANKED versions above, but without saving
	 * and restoring the PPAGE register.
	 */

	#define portRESTORE_CONTEXT()									\
	{																\
		extern volatile void * pxCurrentTCB;						\
		extern volatile unsigned portBASE_TYPE uxCriticalNesting;	\
																	\
		__asm( "ldx pxCurrentTCB" );								\
		__asm( "lds 0, x" );										\
		__asm( "pula" );											\
		__asm( "staa uxCriticalNesting" );							\
	}

	#define portSAVE_CONTEXT()										\
	{																\
		extern volatile void * pxCurrentTCB;						\
		extern volatile unsigned portBASE_TYPE uxCriticalNesting;	\
																	\
		__asm( "ldaa uxCriticalNesting" );							\
		__asm( "psha" );											\
		__asm( "ldx pxCurrentTCB" );								\
		__asm( "sts 0, x" );										\
	}
#endif

/*
 * Utility macro to call macros above in correct order in order to perform a
 * task switch from within a standard ISR.  This macro can only be used if
 * the ISR does not use any local (stack) variables.  If the ISR uses stack
 * variables portYIELD() should be used in it's place.
 */
#define portTASK_SWITCH_FROM_ISR()								\
	portSAVE_CONTEXT();											\
	vTaskSwitchContext();										\
	portRESTORE_CONTEXT();


/* Task function macros as described on the FreeRTOS.org WEB site. */
#define portTASK_FUNCTION_PROTO( vFunction, pvParameters ) void vFunction( void *pvParameters )
#define portTASK_FUNCTION( vFunction, pvParameters ) void vFunction( void *pvParameters )

#endif /* PORTMACRO_H */

