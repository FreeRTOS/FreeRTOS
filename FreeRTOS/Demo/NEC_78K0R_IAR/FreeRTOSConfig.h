/*
 * FreeRTOS Kernel V10.4.1
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 * http://www.FreeRTOS.org
 * http://aws.amazon.com/freertos
 *
 * 1 tab == 4 spaces!
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
		#define configTICK_RATE_HZ				( ( TickType_t ) 1000 )
		#define configMAX_PRIORITIES			( 4 )
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

