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

#ifdef __XC32__
	#include <xc.h>
#endif

/*-----------------------------------------------------------
 * Application specific definitions.
 *
 * These definitions should be adjusted for your particular hardware and
 * application requirements.
 *
 * THESE PARAMETERS ARE DESCRIBED WITHIN THE 'CONFIGURATION' SECTION OF THE
 * FreeRTOS API DOCUMENTATION AVAILABLE ON THE FreeRTOS.org WEB SITE.
 *
 * See http://www.freertos.org/a00110.html
 *----------------------------------------------------------*/

/* The MEC14xx controller allows interrupts to be aggregated into a single
 * signal which triggers a single interrupt with a fixed priority for all
 * interrupt levels. Alternatively the signals can be disaggregated into unique
 * interrupt events which can be vectored via a dispatch table to unique
 * handlers for each interrupt source.  This mechanism allows, for instance, a 
 * single interrupt handler for a large number of IO pins yet unique handlers 
 * for timers and other signals.
 * 
 * When operating in disaggregated mode certain restrictions apply. The
 * interrupt event and status registers are shared between timers due to their
 * proximity in the memory map.  Similarly the software interrupt control
 * registers are shared with other interrupt sources.  The JTVIC maps interrupt
 * levels into MIPs core interrupt levels consequently JTVIC priorities of 0, 1, 
 * 3, and 4 map to the MIPs core values of 1, 3, 5, and 7.  The parameter 
 * configTIMERS_DISAGGREGATED_ISRS is used to control if the timers in register 
 * GIRQ23 are operating in disaggregated mode.  Similarly 
 * configCPU_DISAGGREGATED_ISRS controls the mode for GIRQ24.
 * 
 * Note:
 * Disaggregated mode is the more natural manner in which to operate the ISRs
 * and currently only this mode has been tested with the demo application.  If
 * you wish to use aggregated mode then an alternative interrupt handler scheme
 * will need to be used that marshals all interrupts from a single GIRQ through 
 * a common handler function that tests which interrupt occurred and dispatches 
 * to the relevant handlers.
 */
#define configTIMERS_DISAGGREGATED_ISRS			 	1
#define configCPU_DISAGGREGATED_ISRS				1

#define configUSE_PREEMPTION						1
#define configUSE_PORT_OPTIMISED_TASK_SELECTION	 	1
#define configUSE_QUEUE_SETS						1
#define configUSE_IDLE_HOOK						 	0
#define configUSE_TICK_HOOK						 	0
#define configTICK_RATE_HZ							( ( TickType_t ) 1000 )
#define configCPU_CLOCK_HZ						 	( 48000000UL )
#define configPERIPHERAL_CLOCK_HZ					( 48000000UL )
#define configMAX_PRIORITIES						( 5UL )
#define configMINIMAL_STACK_SIZE					( 190 )

/* MEC14xx JTVIC HW implements 4 priority levels. */
#define configISR_STACK_SIZE						( 4 * configMINIMAL_STACK_SIZE )
#define configTOTAL_HEAP_SIZE					 	( ( size_t ) 22800 )
#define configMAX_TASK_NAME_LEN						( 8 )
#define configUSE_TRACE_FACILITY					0
#define configUSE_16_BIT_TICKS					 	0
#define configIDLE_SHOULD_YIELD						1
#define configUSE_MUTEXES							1
#define configCHECK_FOR_STACK_OVERFLOW				3
#define configQUEUE_REGISTRY_SIZE					0
#define configUSE_RECURSIVE_MUTEXES					1
#define configUSE_MALLOC_FAILED_HOOK				1
#define configUSE_APPLICATION_TASK_TAG				0
#define configUSE_COUNTING_SEMAPHORES				1
#define configGENERATE_RUN_TIME_STATS				0

/* Co-routine definitions. */
#define configUSE_CO_ROUTINES						0
#define configMAX_CO_ROUTINE_PRIORITIES				( 2 )

/* Software timer definitions. */
#define configUSE_TIMERS							1
#define configTIMER_TASK_PRIORITY					( 2 )
#define configTIMER_QUEUE_LENGTH					5
#define configTIMER_TASK_STACK_DEPTH				( configMINIMAL_STACK_SIZE * 2 )

/* Set the following definitions to 1 to include the API function, or zero
to exclude the API function. */
#define INCLUDE_vTaskPrioritySet					1
#define INCLUDE_uxTaskPriorityGet					1
#define INCLUDE_vTaskDelete							1
#define INCLUDE_vTaskCleanUpResources				0
#define INCLUDE_vTaskSuspend						1
#define INCLUDE_vTaskDelayUntil						1
#define INCLUDE_vTaskDelay						 	1
#define INCLUDE_uxTaskGetStackHighWaterMark			1
#define INCLUDE_eTaskGetState						1
#define INCLUDE_xTimerPendFunctionCall				1

/* The priority at which the tick interrupt runs.
 * Use interrupt controller priority 1 */
#define configKERNEL_INTERRUPT_PRIORITY			 	0x01

/* The maximum interrupt priority from which FreeRTOS.org API functions can
be called.  Only API functions that end in ...FromISR() can be used within
interrupts. This describes the interrupt in a numeric range from 1 to 7 however
 only values 1, 3, 5, and 7 are valid */
#define configMAX_SYSCALL_INTERRUPT_PRIORITY		0x03

/* Prevent C specific syntax being included in assembly files. */
#ifndef __LANGUAGE_ASSEMBLY
	extern void vAssertCalled( const char * pcFile, unsigned long ulLine );
	#define configASSERT( x ) if( ( x ) == 0  ) vAssertCalled( __FILE__, __LINE__ )
#endif

#endif /* FREERTOS_CONFIG_H */
