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
 * The following #error directive is to remind users that a batch file must be
 * executed prior to this project being built.  The batch file *cannot* be 
 * executed from within the IDE!  Once it has been executed, re-open or refresh 
 * the Eclipse project and remove the #error line below.
 */
#error Ensure CreateProjectDirectoryStructure.bat has been executed before building.  See comment immediately above.

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
 */

/*----------------------------------------------------------*/

#define configUSE_PREEMPTION				1
#define configUSE_IDLE_HOOK					1
/* CPU is actually 150MHz but FPIDIV is 1 meaning divide by 2 for the
peripheral clock. */
#define configCPU_CLOCK_HZ					( ( unsigned long ) 150000000UL )
#define configPERIPHERAL_CLOCK_HZ			( ( unsigned long ) configCPU_CLOCK_HZ / 2UL )
#define configTICK_RATE_HZ					( ( portTickType ) 1000UL )
#define configMAX_PRIORITIES				( ( unsigned portBASE_TYPE ) 6 )
#define configMINIMAL_STACK_SIZE			( ( unsigned short ) 128 )
#define configTOTAL_HEAP_SIZE				( ( size_t ) ( 35U * 1024U ) )
#define configMAX_TASK_NAME_LEN				( 16 )
#define configUSE_TRACE_FACILITY			0
#define configUSE_16_BIT_TICKS				0
#define configIDLE_SHOULD_YIELD				0
#define configUSE_MALLOC_FAILED_HOOK 		1
#define configCHECK_FOR_STACK_OVERFLOW		0
#define configUSE_TICK_HOOK					1
#define configUSE_COUNTING_SEMAPHORES 		1
#define configUSE_RECURSIVE_MUTEXES			1
#define configUSE_MUTEXES					1

/* Co-routine definitions. */
#define configUSE_CO_ROUTINES 				0
#define configMAX_CO_ROUTINE_PRIORITIES 	( 2 )

/* Software timer configuration. */
#define configUSE_TIMERS					1
#define configTIMER_TASK_PRIORITY			( 4 )
#define configTIMER_QUEUE_LENGTH			( 5 )
#define configTIMER_TASK_STACK_DEPTH		configMINIMAL_STACK_SIZE

/* Set the following definitions to 1 to include the API function, or zero
 to exclude the API function. */

#define INCLUDE_vTaskPrioritySet				1
#define INCLUDE_uxTaskPriorityGet				1
#define INCLUDE_vTaskDelete						1
#define INCLUDE_vTaskCleanUpResources			1
#define INCLUDE_vTaskSuspend					1
#define INCLUDE_vTaskDelayUntil					1
#define INCLUDE_vTaskDelay						1

#define configMAX_SYSCALL_INTERRUPT_PRIORITY	64 /* Interrupt above priority 64 are not effected by critical sections, but cannot call interrupt safe FreeRTOS functions. */
#define configKERNEL_INTERRUPT_PRIORITY			2  /* This is defined here for clarity, but the value must not be changed from 2. */
#define configKERNEL_YIELD_PRIORITY				1  /* This is defined here for clarity, but must not be changed from its default value of 1. */

/* Interrupt priorities. */
#define configINTERRUPT_PRIORITY_TX				16
#define configINTERRUPT_PRIORITY_RX				18
#define configHIGH_FREQUENCY_TIMER_PRIORITY		( configMAX_SYSCALL_INTERRUPT_PRIORITY - 1UL )

/* Default definition of configASSERT(). */
#define configASSERT( x ) if( ( x ) == 0 ) 		{ portDISABLE_INTERRUPTS(); for( ;; ); }


#endif /* FREERTOS_CONFIG_H */

