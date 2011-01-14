/*
    FreeRTOS V6.1.1 - Copyright (C) 2011 Real Time Engineers Ltd.

    ***************************************************************************
    *                                                                         *
    * If you are:                                                             *
    *                                                                         *
    *    + New to FreeRTOS,                                                   *
    *    + Wanting to learn FreeRTOS or multitasking in general quickly       *
    *    + Looking for basic training,                                        *
    *    + Wanting to improve your FreeRTOS skills and productivity           *
    *                                                                         *
    * then take a look at the FreeRTOS books - available as PDF or paperback  *
    *                                                                         *
    *        "Using the FreeRTOS Real Time Kernel - a Practical Guide"        *
    *                  http://www.FreeRTOS.org/Documentation                  *
    *                                                                         *
    * A pdf reference manual is also available.  Both are usually delivered   *
    * to your inbox within 20 minutes to two hours when purchased between 8am *
    * and 8pm GMT (although please allow up to 24 hours in case of            *
    * exceptional circumstances).  Thank you for your support!                *
    *                                                                         *
    ***************************************************************************

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation AND MODIFIED BY the FreeRTOS exception.
    ***NOTE*** The exception to the GPL is included to allow you to distribute
    a combined work that includes FreeRTOS without being obliged to provide the
    source code for proprietary components outside of the FreeRTOS kernel.
    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT
    ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
    FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
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
#define portBYTE_ALIGNMENT			2
#define portSTACK_GROWTH			( -1 )
#define portTICK_RATE_MS			( ( portTickType ) 1000 / configTICK_RATE_HZ )		
#define portYIELD()					asm volatile( "TRAPA #0" )
#define portNOP()					asm volatile( "NOP" )
/*-----------------------------------------------------------*/

/* Critical section handling. */
#define portENABLE_INTERRUPTS()		asm volatile( "ANDC	#0x7F, CCR" );
#define portDISABLE_INTERRUPTS()	asm volatile( "ORC  #0x80, CCR" );

/* Push the CCR then disable interrupts. */
#define portENTER_CRITICAL()  		asm volatile( "STC	CCR, @-ER7" ); \
                               		portDISABLE_INTERRUPTS();

/* Pop the CCR to set the interrupt masking back to its previous state. */
#define  portEXIT_CRITICAL()    	asm volatile( "LDC  @ER7+, CCR" );
/*-----------------------------------------------------------*/

/* Task utilities. */

/* Context switch macros.  These macros are very simple as the context 
is saved simply by selecting the saveall attribute of the context switch 
interrupt service routines.  These macros save and restore the stack
pointer to the TCB. */

#define portSAVE_STACK_POINTER()								\
extern void* pxCurrentTCB;										\
																\
	asm volatile(												\
					"MOV.L	@_pxCurrentTCB, ER5			\n\t" 	\
					"MOV.L	ER7, @ER5					\n\t"	\
				);												\
	( void ) pxCurrentTCB;


#define	portRESTORE_STACK_POINTER()								\
extern void* pxCurrentTCB;										\
																\
	asm volatile(												\
					"MOV.L	@_pxCurrentTCB, ER5			\n\t"	\
					"MOV.L	@ER5, ER7					\n\t"	\
				);												\
	( void ) pxCurrentTCB;

/*-----------------------------------------------------------*/

/* Macros to allow a context switch from within an application ISR. */

#define portENTER_SWITCHING_ISR() portSAVE_STACK_POINTER(); {

#define portEXIT_SWITCHING_ISR( x )							\
	if( x )													\
	{														\
		extern void vTaskSwitchContext( void );				\
		vTaskSwitchContext();								\
	}														\
	} portRESTORE_STACK_POINTER();
/*-----------------------------------------------------------*/

/* Task function macros as described on the FreeRTOS.org WEB site. */
#define portTASK_FUNCTION_PROTO( vFunction, pvParameters ) void vFunction( void *pvParameters )
#define portTASK_FUNCTION( vFunction, pvParameters ) void vFunction( void *pvParameters )

#ifdef __cplusplus
}
#endif

#endif /* PORTMACRO_H */

