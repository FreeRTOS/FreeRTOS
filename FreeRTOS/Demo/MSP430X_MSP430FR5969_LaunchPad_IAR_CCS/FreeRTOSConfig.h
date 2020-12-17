/*
 * FreeRTOS V202012.00
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

/*-----------------------------------------------------------
 * Application specific definitions.
 *
 * These definitions should be adjusted for your particular hardware and
 * application requirements.
 *
 * THESE PARAMETERS ARE DESCRIBED WITHIN THE 'CONFIGURATION' SECTION OF THE
 * FreeRTOS API DOCUMENTATION AVAILABLE ON THE FreeRTOS.org WEB SITE.
 * http://www.freertos.org/a00110.html
 *----------------------------------------------------------*/

/* The array used as the heap is declared by the application to allow the
__persistent keyword to be used.  See http://www.freertos.org/a00111.html#heap_4 */
#define configAPPLICATION_ALLOCATED_HEAP		1
#define configUSE_PREEMPTION					1
#define configMAX_PRIORITIES					( 5 )
#define configCPU_CLOCK_HZ						( 8000000 )
#define configTICK_RATE_HZ						( 1000 ) /* In this non-real time simulated environment the tick frequency has to be at least a multiple of the Win32 tick frequency, and therefore very slow. */
#define configTOTAL_HEAP_SIZE					( 14 * 1024 )
#define configMAX_TASK_NAME_LEN					( 15 )
#define configUSE_TRACE_FACILITY				1
#define configUSE_16_BIT_TICKS					0
#define configIDLE_SHOULD_YIELD					1
#define configUSE_CO_ROUTINES 					0
#define configUSE_MUTEXES						1
#define configUSE_RECURSIVE_MUTEXES				1
#define configQUEUE_REGISTRY_SIZE				0
#define configUSE_APPLICATION_TASK_TAG			0
#define configUSE_COUNTING_SEMAPHORES			1
#define configUSE_ALTERNATIVE_API				0
#define configNUM_THREAD_LOCAL_STORAGE_POINTERS	0
#define configENABLE_BACKWARD_COMPATIBILITY		0

/* Hook function related definitions. */
#define configUSE_TICK_HOOK				1
#define configUSE_IDLE_HOOK				1
#define configUSE_MALLOC_FAILED_HOOK	1
#define configCHECK_FOR_STACK_OVERFLOW	2

/* Software timer related definitions. */
#define configUSE_TIMERS				1
#define configTIMER_TASK_PRIORITY		( configMAX_PRIORITIES - 1 )
#define configTIMER_QUEUE_LENGTH		5
#define configTIMER_TASK_STACK_DEPTH	( configMINIMAL_STACK_SIZE )

/* Event group related definitions. */
#define configUSE_EVENT_GROUPS			0

/* Run time stats gathering definitions. */
#define configGENERATE_RUN_TIME_STATS	1
#define portCONFIGURE_TIMER_FOR_RUN_TIME_STATS() vConfigureTimerForRunTimeStats()
/* Return the current timer counter value + the overflow counter. */
#define portGET_RUN_TIME_COUNTER_VALUE() 	( ( ( uint32_t ) TA1R ) + ulRunTimeCounterOverflows )

/* Co-routine definitions. */
#define configUSE_CO_ROUTINES 			0
#define configMAX_CO_ROUTINE_PRIORITIES ( 2 )

/* Set the following definitions to 1 to include the API function, or zero
to exclude the API function.  The IAR linker will remove unused functions
anyway, so any INCLUDE_ definition that doesn't have another dependency can be
left at 1 with no impact on the code size. */
#define INCLUDE_vTaskPrioritySet				1
#define INCLUDE_uxTaskPriorityGet				1
#define INCLUDE_vTaskDelete						1
#define INCLUDE_vTaskSuspend					1
#define INCLUDE_vTaskDelayUntil					1
#define INCLUDE_vTaskDelay						1
#define INCLUDE_uxTaskGetStackHighWaterMark		1
#define INCLUDE_xTaskGetSchedulerState			1
#define INCLUDE_xTimerGetTimerTaskHandle		1
#define INCLUDE_xTaskGetIdleTaskHandle			1
#define INCLUDE_xQueueGetMutexHolder			1
#define INCLUDE_eTaskGetState					1
#define INCLUDE_xEventGroupSetBitsFromISR		1
#define INCLUDE_xTimerPendFunctionCall			1

/* Include functions that format system and run-time stats into human readable
tables. */
#define configUSE_STATS_FORMATTING_FUNCTIONS	1

/* Assert call defined for debug builds. */
#define configASSERT( x ) if( ( x ) == 0 ) { taskDISABLE_INTERRUPTS(); for( ;; ); }

/* The MSP430X port uses a callback function to configure its tick interrupt.
This allows the application to choose the tick interrupt source.
configTICK_VECTOR must also be set in FreeRTOSConfig.h to the correct
interrupt vector for the chosen tick interrupt source.  This implementation of
vApplicationSetupTimerInterrupt() generates the tick from timer A0, so in this
case configTICK__VECTOR is set to TIMER0_A0_VECTOR. */
#define configTICK_VECTOR				TIMER0_A0_VECTOR

/* The size of the buffer used by the CLI to place output generated by the CLI.
WARNING:  By default there is no overflow checking when writing to this
buffer. */
#define configCOMMAND_INT_MAX_OUTPUT_SIZE 1500

/* The __persistent qualifier is needed on the buffer used to hold CLI output,
so the buffer must be declared in application code, rather than in
FreeRTOS_CLI.c. */
#define configAPPLICATION_PROVIDES_cOutputBuffer 1

/* Include the command that queries the amount of free heap remaining in the
CLI. */
#define configINCLUDE_QUERY_HEAP_COMMAND	1

/* The baudrate used for the CLI. */
#define configCLI_BAUD_RATE			19200

/* Compiler specifics below here. */
/* Prevent the following line being included from IAR asm files. */
#ifndef __IAR_SYSTEMS_ASM__
	void vConfigureTimerForRunTimeStats( void );
	extern volatile uint32_t ulRunTimeCounterOverflows;
	void vConfigureTimerForRunTimeStats( void );
#endif

#ifdef __ICC430__
	/* Using the IAR pre-processor constants. */
	#if ( __DATA_MODEL__ == __DATA_MODEL_LARGE__ )
		#define configMINIMAL_STACK_SIZE		( ( unsigned short ) 80 )
	#else
		#define configMINIMAL_STACK_SIZE		( ( unsigned short ) 130 )
	#endif
#else
	/* Using the CCS pre-processor constants. */
	#ifdef __LARGE_DATA_MODEL__
		#define configMINIMAL_STACK_SIZE		( ( unsigned short ) 85 )
	#else
		#define configMINIMAL_STACK_SIZE		( ( unsigned short ) 140 )
	#endif
#endif /* IAR_MSP */

#endif /* FREERTOS_CONFIG_H */

