/*
	FreeRTOS V5.4.0 - Copyright (C) 2003-2009 Richard Barry.

	This file is part of the FreeRTOS distribution.

	FreeRTOS is free software; you can redistribute it and/or modify it	under 
	the terms of the GNU General Public License (version 2) as published by the 
	Free Software Foundation and modified by the FreeRTOS exception.
	**NOTE** The exception to the GPL is included to allow you to distribute a
	combined work that includes FreeRTOS without being obliged to provide the 
	source code for proprietary components outside of the FreeRTOS kernel.  
	Alternative commercial license and support terms are also available upon 
	request.  See the licensing section of http://www.FreeRTOS.org for full 
	license details.

	FreeRTOS is distributed in the hope that it will be useful,	but WITHOUT
	ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
	FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
	more details.

	You should have received a copy of the GNU General Public License along
	with FreeRTOS; if not, write to the Free Software Foundation, Inc., 59
	Temple Place, Suite 330, Boston, MA  02111-1307  USA.


	***************************************************************************
	*                                                                         *
	* Looking for a quick start?  Then check out the FreeRTOS eBook!          *
	* See http://www.FreeRTOS.org/Documentation for details                   *
	*                                                                         *
	***************************************************************************

	1 tab == 4 spaces!

	Please ensure to read the configuration and relevant port sections of the
	online documentation.

	http://www.FreeRTOS.org - Documentation, latest information, license and
	contact details.

	http://www.SafeRTOS.com - A version that is certified for use in safety
	critical systems.

	http://www.OpenRTOS.com - Commercial support, development, porting,
	licensing and training services.
*/

#ifndef PORTMACRO_H
#define PORTMACRO_H

/* Hardware specific includes. */
#include "mb91467d.h"

/* Standard includes. */
#include <stddef.h>

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

/* Critical section management. */
#if configKERNEL_INTERRUPT_PRIORITY != 30
	#error configKERNEL_INTERRUPT_PRIORITY (set in FreeRTOSConfig.h) must match the ILM value set in the following line - 30 (1Eh) being the default.
#endif
#define portDISABLE_INTERRUPTS() __asm(" STILM #1Eh ")
#define portENABLE_INTERRUPTS() __asm(" STILM #1Fh ")

#define portENTER_CRITICAL()	\
	__asm(" ST PS,@-R15 ");		\
	__asm(" ANDCCR #0xef ");	\


#define portEXIT_CRITICAL()		\
	__asm(" LD @R15+,PS ");		\

/*-----------------------------------------------------------*/

/* Architecture specifics. */
#define portSTACK_GROWTH			( -1 )
#define portTICK_RATE_MS			( ( portTickType ) 1000 / configTICK_RATE_HZ )		
#define portBYTE_ALIGNMENT			4
#define portNOP()					__asm( " nop " );
/*-----------------------------------------------------------*/

/* portYIELD() uses a SW interrupt */
#define portYIELD()					__asm( " INT #40H " );

/* portYIELD_FROM_ISR() uses delayed interrupt */
#define portYIELD_FROM_ISR()			DICR_DLYI = 1
/*-----------------------------------------------------------*/

/* Task function macros as described on the FreeRTOS.org WEB site. */
#define portTASK_FUNCTION_PROTO( vFunction, pvParameters ) void vFunction( void *pvParameters )
#define portTASK_FUNCTION( vFunction, pvParameters ) void vFunction( void *pvParameters )

#define portMINIMAL_STACK_SIZE configMINIMAL_STACK_SIZE


#endif /* PORTMACRO_H */

