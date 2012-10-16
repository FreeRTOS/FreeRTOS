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

#ifndef FREERTOS_CONFIG_H
#define FREERTOS_CONFIG_H

/*
 * 78K0R Clock Source Configuration
 * 1 = use internal High Speed Clock Source (typically 8Mhz on the 78K0R/Kx3)
 * 0 = use external Clock Source
 */
#define configCLOCK_SOURCE              0

/*
 * 78K0R Memory Model
 * 1 = use far memory mode
 * 0 = use near memory mode
 *
 * This setting must match the setting in the IAR project options.
 */
#define configMEMORY_MODE               1

/*
 * Application specific definitions.
 *
 * These definitions should be adjusted for your particular hardware and
 * application requirements.
 *
 * THESE PARAMETERS ARE DESCRIBED WITHIN THE 'CONFIGURATION' SECTION OF THE
 * FreeRTOS API DOCUMENTATION AVAILABLE ON THE FreeRTOS.org WEB SITE.
 */

#define configUSE_PREEMPTION		1

	/* Only use following section for C files */
	#ifdef __IAR_SYSTEMS_ICC__
	
		#pragma language=extended
		#pragma system_include
	
		#include <intrinsics.h>
	
		#define configUSE_IDLE_HOOK				0
		#define configUSE_TICK_HOOK				0
		#define configTICK_RATE_HZ				( ( portTickType ) 1000 )
		#define configMAX_PRIORITIES			( ( unsigned portBASE_TYPE ) 4 )
		#define configMINIMAL_STACK_SIZE		( ( unsigned short ) 100 )
		#define configMAX_TASK_NAME_LEN			( 10 )
		#define configUSE_TRACE_FACILITY		0
		#define configUSE_16_BIT_TICKS			1
		#define configIDLE_SHOULD_YIELD			1
		#define configCHECK_FOR_STACK_OVERFLOW	2
		#define configUSE_MUTEXES				1
	
		/* Co-routine definitions. */
		#define configUSE_CO_ROUTINES 			0
		#define configMAX_CO_ROUTINE_PRIORITIES ( 2 )
	
		/* Set the following definitions to 1 to include the API function, or zero
		to exclude the API function. */
		#define INCLUDE_vTaskPrioritySet		1
		#define INCLUDE_uxTaskPriorityGet		1
		#define INCLUDE_vTaskDelete				1
		#define INCLUDE_vTaskCleanUpResources	0
		#define INCLUDE_vTaskSuspend			1
		#define INCLUDE_vTaskDelayUntil			1
		#define INCLUDE_vTaskDelay				1
	
		#if configCLOCK_SOURCE == 0
			#define configCPU_CLOCK_HZ			( ( unsigned long ) 20000000 )  /* using the external clock source */
		#else
			#define configCPU_CLOCK_HZ			( ( unsigned long ) 8000000 )   /* using the internal high speed clock */
		#endif /* configCLOCK_SOURCE */
	
		/* Definitions that are specific to the project being used. */
		#ifdef __IAR_78K0R_Kx3__
		
			/* Device specific includes. */
			#include <io78f1166_a0.h>
			#include <io78f1166_a0_ext.h>
		
			#define configTOTAL_HEAP_SIZE			( (size_t ) ( 7000 ) )
		
		#endif /* __IAR_78K0R_Kx3__ */
		
		#ifdef __IAR_78K0R_Kx3L__
		
			/* Device specific includes. */
			#include <io78f1009_64.h>
			#include <io78f1009_64_ext.h>
		
			#define configTOTAL_HEAP_SIZE			( (size_t ) ( 2500 ) )
		
		#endif /* _IAR_78K0R_Kx3L__ */
	
	#endif /* __IAR_SYSTEMS_ICC__ */

#endif /* FREERTOS_CONFIG_H */

