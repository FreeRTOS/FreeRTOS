/*
    FreeRTOS V9.0.0rc2 - Copyright (C) 2016 Real Time Engineers Ltd.
    All rights reserved

    VISIT http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation >>>> AND MODIFIED BY <<<< the FreeRTOS exception.

    ***************************************************************************
    >>!   NOTE: The modification to the GPL is included to allow you to     !<<
    >>!   distribute a combined work that includes FreeRTOS without being   !<<
    >>!   obliged to provide the source code for proprietary components     !<<
    >>!   outside of the FreeRTOS kernel.                                   !<<
    ***************************************************************************

    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT ANY
    WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
    FOR A PARTICULAR PURPOSE.  Full license text is available on the following
    link: http://www.freertos.org/a00114.html

    ***************************************************************************
     *                                                                       *
     *    FreeRTOS provides completely free yet professionally developed,    *
     *    robust, strictly quality controlled, supported, and cross          *
     *    platform software that is more than just the market leader, it     *
     *    is the industry's de facto standard.                               *
     *                                                                       *
     *    Help yourself get started quickly while simultaneously helping     *
     *    to support the FreeRTOS project by purchasing a FreeRTOS           *
     *    tutorial book, reference manual, or both:                          *
     *    http://www.FreeRTOS.org/Documentation                              *
     *                                                                       *
    ***************************************************************************

    http://www.FreeRTOS.org/FAQHelp.html - Having a problem?  Start by reading
    the FAQ page "My application does not run, what could be wrong?".  Have you
    defined configASSERT()?

    http://www.FreeRTOS.org/support - In return for receiving this top quality
    embedded software for free we request you assist our global community by
    participating in the support forum.

    http://www.FreeRTOS.org/training - Investing in training allows your team to
    be as productive as possible as early as possible.  Now you can receive
    FreeRTOS training directly from Richard Barry, CEO of Real Time Engineers
    Ltd, and the world's leading authority on the world's leading RTOS.

    http://www.FreeRTOS.org/plus - A selection of FreeRTOS ecosystem products,
    including FreeRTOS+Trace - an indispensable productivity tool, a DOS
    compatible FAT file system, and our tiny thread aware UDP/IP stack.

    http://www.FreeRTOS.org/labs - Where new FreeRTOS products go to incubate.
    Come and try FreeRTOS+TCP, our new open source TCP/IP stack for FreeRTOS.

    http://www.OpenRTOS.com - Real Time Engineers ltd. license FreeRTOS to High
    Integrity Systems ltd. to sell under the OpenRTOS brand.  Low cost OpenRTOS
    licenses offer ticketed support, indemnification and commercial middleware.

    http://www.SafeRTOS.com - High Integrity Systems also provide a safety
    engineered and independently SIL3 certified version for use in safety and
    mission critical applications that require provable dependability.

    1 tab == 4 spaces!
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

