/*
	FreeRTOS.org V4.0.5 - Copyright (C) 2003-2006 Richard Barry.

	This file is part of the FreeRTOS.org distribution.

	FreeRTOS.org is free software; you can redistribute it and/or modify
	it under the terms of the GNU General Public License as published by
	the Free Software Foundation; either version 2 of the License, or
	(at your option) any later version.

	FreeRTOS.org is distributed in the hope that it will be useful,
	but WITHOUT ANY WARRANTY; without even the implied warranty of
	MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
	GNU General Public License for more details.

	You should have received a copy of the GNU General Public License
	along with FreeRTOS.org; if not, write to the Free Software
	Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA

	A special exception to the GPL can be applied should you wish to distribute
	a combined work that includes FreeRTOS.org, without being obliged to provide
	the source code for any proprietary components.  See the licensing section 
	of http://www.FreeRTOS.org for full details of how and when the exception
	can be applied.

	***************************************************************************
	See http://www.FreeRTOS.org for documentation, latest information, license 
	and contact details.  Please ensure to read the configuration and relevant 
	port sections of the online documentation.
	***************************************************************************
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
#define portSHORT		int
#define portSTACK_TYPE	unsigned portSHORT
#define portBASE_TYPE	portSHORT

#if( configUSE_16_BIT_TICKS == 1 )
	typedef unsigned portSHORT portTickType;
	#define portMAX_DELAY ( portTickType ) 0xffff
#else
	typedef unsigned portLONG portTickType;
	#define portMAX_DELAY ( portTickType ) 0xffffffff
#endif
/*-----------------------------------------------------------*/	

/* Interrupt control macros. */
#define portDISABLE_INTERRUPTS()	asm volatile ( "DINT" )
#define portENABLE_INTERRUPTS()		asm volatile ( "EINT" )
/*-----------------------------------------------------------*/

/* Critical section control macros. */
#define portNO_CRITICAL_SECTION_NESTING		( ( unsigned portSHORT ) 0 )

#define portENTER_CRITICAL()													\
{																				\
extern volatile unsigned portSHORT usCriticalNesting;							\
																				\
	portDISABLE_INTERRUPTS();													\
																				\
	/* Now interrupts are disabled ulCriticalNesting can be accessed */			\
	/* directly.  Increment ulCriticalNesting to keep a count of how many */	\
	/* times portENTER_CRITICAL() has been called. */							\
	usCriticalNesting++;														\
}

#define portEXIT_CRITICAL()														\
{																				\
extern volatile unsigned portSHORT usCriticalNesting;							\
																				\
	if( usCriticalNesting > portNO_CRITICAL_SECTION_NESTING )					\
	{																			\
		/* Decrement the nesting count as we are leaving a critical section. */	\
		usCriticalNesting--;													\
																				\
		/* If the nesting level has reached zero then interrupts should be */	\
		/* re-enabled. */														\
		if( usCriticalNesting == portNO_CRITICAL_SECTION_NESTING )				\
		{																		\
			portENABLE_INTERRUPTS();											\
		}																		\
	}																			\
}
/*-----------------------------------------------------------*/

/* Task utilities. */
extern void vPortYield( void ) __attribute__ ( ( naked ) );
#define portYIELD()					vPortYield()
#define portNOP()			asm volatile ( "NOP" )
/*-----------------------------------------------------------*/

/* Hardwware specifics. */
#define portBYTE_ALIGNMENT			2
#define portSTACK_GROWTH			( -1 )
#define portTICK_RATE_MS			( ( portTickType ) 1000 / configTICK_RATE_HZ )		
/*-----------------------------------------------------------*/

/* Task function macros as described on the FreeRTOS.org WEB site. */
#define portTASK_FUNCTION_PROTO( vFunction, pvParameters ) void vFunction( void *pvParameters )
#define portTASK_FUNCTION( vFunction, pvParameters ) void vFunction( void *pvParameters )

#endif /* PORTMACRO_H */

