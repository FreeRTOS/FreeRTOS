/*
 * FreeRTOS Kernel V10.0.0
 * Copyright (C) 2017 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software. If you wish to use our Amazon
 * FreeRTOS name, please do so in a fair use way that does not cause confusion.
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

/*-----------------------------------------------------------
 * Application specific definitions.
 *
 * These definitions should be adjusted for your particular hardware and
 * application requirements.
 *
 * THESE PARAMETERS ARE DESCRIBED WITHIN THE 'CONFIGURATION' SECTION OF THE
 * FreeRTOS API DOCUMENTATION AVAILABLE ON THE FreeRTOS.org WEB SITE.
 *
 * See http://www.freertos.org/a00110.html.
 *----------------------------------------------------------*/

/* This #ifdef prevents the enclosed code being included from within an
asm file.  It is valid in a C file, but not valid in an asm file. */
#ifdef __IAR_SYSTEMS_ICC__

	#pragma language=extended
	#pragma system_include

	#include <intrinsics.h>

	/* Device specific includes. */
	#include <ior5f100le.h>
	#include <ior5f100le_ext.h>

#endif /* __IAR_SYSTEMS_ICC__ */

#define configUSE_PREEMPTION			1
#define configTICK_RATE_HZ				( ( unsigned short ) 1000 )
#define configMAX_PRIORITIES			( 4 )
#define configMINIMAL_STACK_SIZE		( ( unsigned short ) 80 )
#define configMAX_TASK_NAME_LEN			( 10 )
#define configUSE_TRACE_FACILITY		0
#define configUSE_16_BIT_TICKS			1
#define configIDLE_SHOULD_YIELD			1
#define configTOTAL_HEAP_SIZE			( (size_t ) ( 3420 ) )
#define configCHECK_FOR_STACK_OVERFLOW	2
#define configUSE_MUTEXES				1

/* Hook function definitions. */
#define configUSE_IDLE_HOOK				1
#define configUSE_TICK_HOOK				0
#define configUSE_MALLOC_FAILED_HOOK	1

/* Software timer definitions. */
#define configUSE_TIMERS				1
#define configTIMER_TASK_PRIORITY		( 2 )
#define configTIMER_QUEUE_LENGTH		10
#define configTIMER_TASK_STACK_DEPTH	( configMINIMAL_STACK_SIZE * 2 )

/* Co-routine definitions. */
#define configUSE_CO_ROUTINES 			0
#define configMAX_CO_ROUTINE_PRIORITIES	( 2 )

/* Set the following definitions to 1 to include the API function, or zero
to exclude the API function. */
#define INCLUDE_vTaskPrioritySet			1
#define INCLUDE_uxTaskPriorityGet			1
#define INCLUDE_vTaskDelete					0
#define INCLUDE_vTaskCleanUpResources		0
#define INCLUDE_vTaskSuspend				1
#define INCLUDE_vTaskDelayUntil				0
#define INCLUDE_vTaskDelay					1
#define INCLUDE_xTaskGetIdleTaskHandle 		0
#define INCLUDE_xTimerGetTimerDaemonTaskHandle 	0

/* Tick interrupt vector - this must match the INTIT_vect definition contained
in the ior5fnnnn.h header file included at the top of this file (the value is
dependent on the hardware being used. */
#define configTICK_VECTOR	56

/******************************************************************************
 * PORT SPECIFIC CONFIGURATION OPTIONS
 ******************************************************************************/

/*
 * RL78/G13 Clock Source Configuration
 * 1 = use internal High Speed Clock Source (typically 32Mhz on the RL78/G13)
 * 0 = use external Clock Source
 */
#define configCLOCK_SOURCE			  1

#if configCLOCK_SOURCE == 0
	#define configCPU_CLOCK_HZ		( ( unsigned long ) 20000000 )  /* using the external clock source */
#else
	#define configCPU_CLOCK_HZ		( ( unsigned long ) 32000000 )   /* using the internal high speed clock */
#endif /* configCLOCK_SOURCE */

#define configASSERT( x ) if( ( x ) == 0 ) { taskDISABLE_INTERRUPTS(); for( ;; ); }



#endif /* FREERTOS_CONFIG_H */

