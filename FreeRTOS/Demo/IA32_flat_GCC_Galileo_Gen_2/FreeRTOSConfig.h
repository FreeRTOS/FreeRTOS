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

/*
 * The FreeRTOS Quark port implements a full interrupt nesting model.
 *
 * Interrupts that are assigned a priority at or below
 * configMAX_API_CALL_INTERRUPT_PRIORITY can call interrupt safe API functions
 * and will nest.
 *
 * Interrupts that are assigned a priority above
 * configMAX_API_CALL_INTERRUPT_PRIORITY cannot call any FreeRTOS API functions,
 * will nest, and will not be masked by FreeRTOS critical sections (although all
 * interrupts are briefly masked by the hardware itself on interrupt entry).
 *
 * FreeRTOS functions that can be called from an interrupt are those that end in
 * "FromISR".  FreeRTOS maintains a separate interrupt safe API to enable
 * interrupt entry to be shorter, faster, simpler and smaller.
 *
 * User definable interrupt priorities range from 2 (the lowest) to 15 (the
 * highest).
 */
#define configMAX_API_CALL_INTERRUPT_PRIORITY	10

/*
 * Interrupt entry code will switch the stack in use to a dedicated system 
 * stack.
 *
 * configISR_STACK_SIZE defines the number of 32-bit values that can be stored
 * on the system stack, and must be large enough to hold a potentially nested
 * interrupt stack frame.
 *
 * Changing this parameter necessitates a complete rebuild so the assembly files
 * also get rebuilt.
 */
#define configISR_STACK_SIZE					350

/*
 * If configSUPPORT_FPU is set to 1 then tasks can optionally have a floating
 * point context (the floating point registers will be saved as part of the task
 * context).  If configSUPPORT_FPU is set to 1 then a task must *not* use any
 * floating point instructions until after it has called vPortTaskUsesFPU().
 *
 * If configSUPPORT_FPU is set to 0 then floating point instructions must never
 * be used.
 */
#define configSUPPORT_FPU						1

/* There are two ways of implementing interrupt handlers:
 *
 * 	1) As standard C functions -
 *
 *	This method can only be used if configUSE_COMMON_INTERRUPT_ENTRY_POINT
 *	is set to 1.  The C function is installed using
 *	xPortRegisterCInterruptHandler().
 *
 *	This is the simplest of the two methods but incurs a slightly longer
 * 	interrupt entry time.
 *
 *	2) By using an assembly stub that wraps the handler in the FreeRTOS
 *	portFREERTOS_INTERRUPT_ENTRY and portFREERTOS_INTERRUPT_EXIT macros.  The handler is installed
 *	using xPortInstallInterruptHandler().
 *
 * This method can always be used.  It is slightly more complex than
 * method 1 but benefits from a faster interrupt entry time.
 *
 * Changing this parameter necessitates a complete clean build.
 */
#define configUSE_COMMON_INTERRUPT_ENTRY_POINT	1

#define configCPU_CLOCK_HZ						( 400000000UL )
#define configUSE_PORT_OPTIMISED_TASK_SELECTION	1
#define configMINIMAL_STACK_SIZE				( 125 )
#define configUSE_TICKLESS_IDLE					0
#define configTICK_RATE_HZ						( ( TickType_t ) 1000 )
#define configUSE_PREEMPTION					1
#define configUSE_IDLE_HOOK						1
#define configUSE_TICK_HOOK						1
#define configMAX_PRIORITIES					( 7 )
#define configTOTAL_HEAP_SIZE					( ( size_t ) ( 55 * 1024 ) )
#define configMAX_TASK_NAME_LEN					( 10 )
#define configUSE_TRACE_FACILITY				0
#define configUSE_16_BIT_TICKS					0
#define configIDLE_SHOULD_YIELD					1
#define configUSE_MUTEXES						1
#define configQUEUE_REGISTRY_SIZE				8
#define configCHECK_FOR_STACK_OVERFLOW			2
#define configUSE_RECURSIVE_MUTEXES				1
#define configUSE_MALLOC_FAILED_HOOK			1
#define configUSE_APPLICATION_TASK_TAG			0
#define configUSE_COUNTING_SEMAPHORES			1
#define configUSE_QUEUE_SETS					1
#define configUSE_TASK_NOTIFICATIONS			1

/* Co-routine definitions. */
#define configUSE_CO_ROUTINES 					0
#define configMAX_CO_ROUTINE_PRIORITIES 		( 2 )

/* Software timer definitions. */
#define configUSE_TIMERS						1
#define configTIMER_TASK_PRIORITY				( configMAX_PRIORITIES - 1 )
#define configTIMER_QUEUE_LENGTH				8
#define configTIMER_TASK_STACK_DEPTH			( configMINIMAL_STACK_SIZE * 2 )

/* Set the following definitions to 1 to include the API function, or zero
to exclude the API function. */
#define INCLUDE_vTaskPrioritySet				1
#define INCLUDE_uxTaskPriorityGet				1
#define INCLUDE_vTaskDelete						1
#define INCLUDE_vTaskCleanUpResources			1
#define INCLUDE_vTaskSuspend					1
#define INCLUDE_vTaskDelayUntil					1
#define INCLUDE_vTaskDelay						1
#define INCLUDE_xTimerPendFunctionCall			1
#define INCLUDE_eTaskGetState					1

/* This demo makes use of one or more example stats formatting functions.  These
format the raw data provided by the uxTaskGetSystemState() function in to human
readable ASCII form.  See the notes in the implementation of vTaskList() within
FreeRTOS/Source/tasks.c for limitations. */
#define configUSE_STATS_FORMATTING_FUNCTIONS	1

/* portCONFIGURE_TIMER_FOR_RUN_TIME_STATS is not required because the time base
comes from the ulHighFrequencyTimerCounts variable which is incremented in a
high frequency timer that is already being started as part of the interrupt
nesting test. */
#define configGENERATE_RUN_TIME_STATS	0

/* The size of the global output buffer that is available for use when there
are multiple command interpreters running at once (for example, one on a UART
and one on TCP/IP).  This is done to prevent an output buffer being defined by
each implementation - which would waste RAM.  In this case, there is only one
command interpreter running. */
#define configCOMMAND_INT_MAX_OUTPUT_SIZE 2096

/* This file is included from assembler files - make sure C code is not included
in assembler files. */
#ifndef __ASSEMBLER__
	void vAssertCalled( const char * pcFile, unsigned long ulLine );
	void vConfigureTickInterrupt( void );
	void vClearTickInterrupt( void );
#endif /* __ASSEMBLER__ */



/* Normal assert() semantics without relying on the provision of an assert.h
header file. */
#define configASSERT( x ) if( ( x ) == 0 ) vAssertCalled( __FILE__, __LINE__ );



/****** Hardware/compiler specific settings. *******************************************/

/*
 * The application must provide a function that configures a peripheral to
 * create the FreeRTOS tick interrupt, then define configSETUP_TICK_INTERRUPT()
 * in FreeRTOSConfig.h to call the function.  This file contains a function
 * that is suitable for use on the Zynq MPU.  FreeRTOS_Tick_Handler() must
 * be installed as the peripheral's interrupt handler.
 */
#define configSETUP_TICK_INTERRUPT() vConfigureTickInterrupt()
#define configCLEAR_TICK_INTERRUPT() vClearTickInterrupt()


/* Compiler specifics. */
#define fabs( x )			__builtin_fabs( ( x ) )

#endif /* FREERTOS_CONFIG_H */

