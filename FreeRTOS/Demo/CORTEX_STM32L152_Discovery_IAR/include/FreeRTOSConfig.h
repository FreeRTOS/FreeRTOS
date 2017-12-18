/*
 * FreeRTOS Kernel V10.0.1
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

/* Ensure stdint and C code is only used by the compiler, and not the
assembler. */
#ifdef __ICCARM__
	#include <stdint.h>
	extern uint32_t SystemCoreClock;
	void vMainPostStopProcessing( void );
	void vAssertCalled( unsigned long ulLine, const char * const pcFileName );
#endif

/* Set configCREATE_LOW_POWER_DEMO to one to run the simple blinky low power
demo, or 0 to run the more comprehensive test and demo application. */
#define configCREATE_LOW_POWER_DEMO			1

/* A few settings are dependent on the configCREATE_LOW_POWER_DEMO setting. */
#if configCREATE_LOW_POWER_DEMO == 1
	#define configTICK_RATE_HZ						( 100 )
	#define configEXPECTED_IDLE_TIME_BEFORE_SLEEP 	( 20 + 1 ) /* ( ( 200 / portTICK_PERIOD_MS ) + 1 ) written out pre-processed to enable #error statements to check its value. */
	#define configUSE_TIMERS						0
#else
	#define configSYSTICK_CLOCK_HZ					( SystemCoreClock >> 3UL ) /* Systick clock is one eighth the system clock. */
	#define configTICK_RATE_HZ						( ( TickType_t ) 1000 )
	#define configUSE_TIMERS						1
#endif /* configCREATE_LOW_POWER_DEMO */

/* Demo specific macros that allow the application writer to insert code to be
executed immediately before the MCU's STOP low power mode is entered and exited
respectively.  These macros are in addition to the standard
configPRE_SLEEP_PROCESSING() and configPOST_SLEEP_PROCESSING() macros, which are
called pre and post the low power SLEEP mode being entered and exited.  These
macros can be used to turn turn off and on IO, clocks, the Flash etc. to obtain
the lowest power possible while the tick is off.  See the comments at the top of
main_low_power.c and in STM32L_low_power_tick_management.c. */
#define configPRE_STOP_PROCESSING()
#define configPOST_STOP_PROCESSING()				vMainPostStopProcessing()

/* The configUSE_TICKLESS_IDLE setting is dependent on the users setting of
configCREATE_LOW_POWER_DEMO at the top of this file. */
#define configUSE_TICKLESS_IDLE					configCREATE_LOW_POWER_DEMO

#define configCPU_CLOCK_HZ						SystemCoreClock
#define configUSE_PREEMPTION					1
#define configUSE_PORT_OPTIMISED_TASK_SELECTION	1
#define configUSE_IDLE_HOOK						1
#define configUSE_TICK_HOOK						1
#define configMAX_PRIORITIES					( 5 )
#define configMINIMAL_STACK_SIZE				( ( unsigned short ) 70 )
#define configTOTAL_HEAP_SIZE					( ( size_t ) ( 14 * 1024 ) )
#define configMAX_TASK_NAME_LEN					( 16 )
#define configUSE_TRACE_FACILITY				1
#define configUSE_16_BIT_TICKS					0
#define configIDLE_SHOULD_YIELD					1
#define configUSE_MUTEXES						1
#define configQUEUE_REGISTRY_SIZE				5
#define configCHECK_FOR_STACK_OVERFLOW			2
#define configUSE_RECURSIVE_MUTEXES				1
#define configUSE_MALLOC_FAILED_HOOK			1
#define configUSE_APPLICATION_TASK_TAG			0
#define configUSE_COUNTING_SEMAPHORES			1

/* Software timer related definitions. */
#define configTIMER_TASK_PRIORITY				( configMAX_PRIORITIES - 1 )
#define configTIMER_QUEUE_LENGTH				10
#define configTIMER_TASK_STACK_DEPTH			configMINIMAL_STACK_SIZE

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

/* Standard assert semantics. */
#define configASSERT( x ) if( ( x ) == 0 ) vAssertCalled( __LINE__, __FILE__ )

/* Use the system definition, if there is one */
#ifdef __NVIC_PRIO_BITS
	#define configPRIO_BITS       __NVIC_PRIO_BITS
#else
	#define configPRIO_BITS       4        /* 15 priority levels */
#endif

#define configLIBRARY_LOWEST_INTERRUPT_PRIORITY			15
#define configLIBRARY_MAX_SYSCALL_INTERRUPT_PRIORITY	5

/* The lowest priority. */
#define configKERNEL_INTERRUPT_PRIORITY 	( configLIBRARY_LOWEST_INTERRUPT_PRIORITY << (8 - configPRIO_BITS) )
/* Priority 5, or 95 as only the top four bits are implemented. */
/* !!!! configMAX_SYSCALL_INTERRUPT_PRIORITY must not be set to zero !!!!
See http://www.FreeRTOS.org/RTOS-Cortex-M3-M4.html. */
#define configMAX_SYSCALL_INTERRUPT_PRIORITY 	( configLIBRARY_MAX_SYSCALL_INTERRUPT_PRIORITY << (8 - configPRIO_BITS) )

/* Run time stats related macros. */
#define configGENERATE_RUN_TIME_STATS	0

/* Definitions that map the FreeRTOS port interrupt handlers to their CMSIS
standard names. */
#define vPortSVCHandler SVC_Handler
#define xPortPendSVHandler PendSV_Handler
#define xPortSysTickHandler SysTick_Handler

#endif /* FREERTOS_CONFIG_H */

