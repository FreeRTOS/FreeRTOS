/*
    FreeRTOS V202012.00
    All rights reserved

    VISIT http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation >>!AND MODIFIED BY!<< the FreeRTOS exception.

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


/* Required for configuration-dependent settings. */
#include "xtensa_config.h"

/*---------------------------------------------------------------------------
 * Application specific definitions.
 *
 * These definitions should be adjusted for your particular hardware and
 * application requirements.
 *
 * THESE PARAMETERS ARE DESCRIBED WITHIN THE 'CONFIGURATION' SECTION OF THE
 * FreeRTOS API DOCUMENTATION AVAILABLE ON THE FreeRTOS.org WEB SITE.
 *---------------------------------------------------------------------------
 */

#define configUSE_PREEMPTION							1
#define configUSE_IDLE_HOOK								0

#ifdef SMALL_TEST
	#define configUSE_TICK_HOOK							0
#else
	#define configUSE_TICK_HOOK							1
#endif

#define configTICK_RATE_HZ								( 1000 )

/* Default clock rate for simulator */
#define configCPU_CLOCK_HZ								10000000

/* Max possible priorities. */
#define configMAX_PRIORITIES							( 7 )

/**
 * Minimal stack size. This may need to be increased for your application.
 *
 * @note: The FreeRTOS demos may not work reliably with stack size < 4KB. The
 * Xtensa-specific examples should be fine with XT_STACK_MIN_SIZE.
 *
 * @note: The size is defined in terms of StackType_t units not bytes.
 */
#if !( defined XT_STACK_MIN_SIZE )
	#error XT_STACK_MIN_SIZE not defined, did you include xtensa_config.h ?
#endif

#ifdef SMALL_TEST
	#define configMINIMAL_STACK_SIZE					( XT_STACK_MIN_SIZE / sizeof( StackType_t ) )
#else
	#define configMINIMAL_STACK_SIZE					( XT_STACK_MIN_SIZE > 1024 ? XT_STACK_MIN_SIZE : 1024 )
#endif

/**
 * The Xtensa port uses a separate interrupt stack. Adjust the stack size  to
 * suit the needs of your specific application.
 *
 * @note: the size is defined in bytes.
 */
#ifndef configISR_STACK_SIZE
	#define configISR_STACK_SIZE						2048
#endif

/**
 * Minimal heap size to make sure examples can run on memory limited configs.
 * Adjust this to suit your system.
 */
#ifdef SMALL_TEST
	#define configTOTAL_HEAP_SIZE						( ( size_t ) ( 16 * 1024 ) )
#else
	#define configTOTAL_HEAP_SIZE						( ( size_t ) ( 512 * 1024 ) )
#endif

#define configMAX_TASK_NAME_LEN							( 8 )
#define configUSE_TRACE_FACILITY						0
#define configUSE_STATS_FORMATTING_FUNCTIONS			0
#define configUSE_TRACE_FACILITY_2						0	/* Provided by Xtensa port patch. */
#define configBENCHMARK									0	/* Provided by Xtensa port patch. */
#define configUSE_16_BIT_TICKS							0
#define configIDLE_SHOULD_YIELD							0
#define configQUEUE_REGISTRY_SIZE						0

#ifdef SMALL_TEST
	#define configUSE_MUTEXES							1
	#define configUSE_RECURSIVE_MUTEXES					1
	#define configUSE_COUNTING_SEMAPHORES				1
	#define configCHECK_FOR_STACK_OVERFLOW				0
#else
	#define configUSE_MUTEXES							1
	#define configUSE_RECURSIVE_MUTEXES					1
	#define configUSE_COUNTING_SEMAPHORES				1
	#define configCHECK_FOR_STACK_OVERFLOW				2
#endif

/* Co-routine definitions. */
#define configUSE_CO_ROUTINES 							0
#define configMAX_CO_ROUTINE_PRIORITIES					( 2 )

/**
 * Set the following definitions to 1 to include the API function, or zero to
 * exclude the API function.
 */
#define INCLUDE_vTaskPrioritySet						1
#define INCLUDE_uxTaskPriorityGet						1
#define INCLUDE_vTaskDelete								1
#define INCLUDE_vTaskCleanUpResources					0
#define INCLUDE_vTaskSuspend							1
#define INCLUDE_vTaskDelayUntil							1
#define INCLUDE_vTaskDelay								1
#define INCLUDE_uxTaskGetStackHighWaterMark				1
#define INCLUDE_xTaskAbortDelay							1
#define INCLUDE_xTaskGetHandle 							1
#define INCLUDE_xSemaphoreGetMutexHolder				1

/**
 * The priority at which the tick interrupt runs.  This should probably be kept
 * at 1.
 */
#define configKERNEL_INTERRUPT_PRIORITY					1

/**
 * The maximum interrupt priority from which FreeRTOS.org API functions can be
 * called.  Only API functions that end in ...FromISR() can be used within
 * interrupts.
 */
#define configMAX_SYSCALL_INTERRUPT_PRIORITY			XCHAL_EXCM_LEVEL

/**
 * XT_USE_THREAD_SAFE_CLIB is defined in xtensa_config.h and can be overridden
 * from the compiler/make command line. The small test however always disables C
 * lib thread safety to minimize size.
 */
#ifdef SMALL_TEST
	#define configUSE_NEWLIB_REENTRANT					0
#else
	#if ( XT_USE_THREAD_SAFE_CLIB > 0u )
		#if XT_HAVE_THREAD_SAFE_CLIB
			#define configUSE_NEWLIB_REENTRANT			0
		#else
			#error "Error: thread-safe C library support not available for this C library."
		#endif
	#else
		#define configUSE_NEWLIB_REENTRANT				0
	#endif
#endif

/* Test FreeRTOS timers (with timer task) and more. */
#define configUSE_TIMERS								1
#define configTIMER_TASK_PRIORITY						( configMAX_PRIORITIES - 2 )
#define configTIMER_QUEUE_LENGTH						10
#define configTIMER_TASK_STACK_DEPTH					configMINIMAL_STACK_SIZE

#ifdef SMALL_TEST
	#define INCLUDE_xTimerPendFunctionCall				0
	#define INCLUDE_eTaskGetState						0
	#define configUSE_QUEUE_SETS						0
#else
	#define INCLUDE_xTimerPendFunctionCall				1
	#define INCLUDE_eTaskGetState						1
	#define configUSE_QUEUE_SETS						1
#endif

/**
 * Specific config for XTENSA (these can be deleted and they will take default
 * values).
 */
#if ( !defined XT_SIMULATOR ) && ( !defined XT_BOARD )
	#define configXT_SIMULATOR							1	/* Simulator mode. */
	#define configXT_BOARD								0	/* Board mode. */
#endif

#ifndef SMALL_TEST
	#if ( !defined XT_INTEXC_HOOKS )
		#define configXT_INTEXC_HOOKS					1	/* Exception hooks used by certain tests. */
	#endif

	#if configUSE_TRACE_FACILITY_2
		#define configASSERT_2							1	/* Specific to Xtensa port. */
	#endif
#endif

/**
 * It is a good idea to define configASSERT() while developing.  configASSERT()
 * uses the same semantics as the standard C assert() macro.
 */
#if !defined __ASSEMBLER__
	extern void vAssertCalled( unsigned long ulLine, const char * const pcFileName );
#endif
#define configASSERT( x ) if( ( x ) == 0 ) vAssertCalled( __LINE__, __FILE__ )

#define configSTREAM_BUFFER_TRIGGER_LEVEL_TEST_MARGIN	( 2 )	/* Used by stream buffer tests. */

#endif /* FREERTOS_CONFIG_H */
