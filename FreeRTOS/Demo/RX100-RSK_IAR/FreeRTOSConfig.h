/*
    FreeRTOS V7.4.2 - Copyright (C) 2013 Real Time Engineers Ltd.

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

    >>>>>>NOTE<<<<<< The modification to the GPL is included to allow you to
    distribute a combined work that includes FreeRTOS without being obliged to
    provide the source code for proprietary components outside of the FreeRTOS
    kernel.

    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT ANY
    WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
    FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more
    details. You should have received a copy of the GNU General Public License
    and the FreeRTOS license exception along with FreeRTOS; if not it can be
    viewed here: http://www.freertos.org/a00114.html and also obtained by
    writing to Real Time Engineers Ltd., contact details for whom are available
    on the FreeRTOS WEB site.

    1 tab == 4 spaces!

    ***************************************************************************
     *                                                                       *
     *    Having a problem?  Start by reading the FAQ "My application does   *
     *    not run, what could be wrong?"                                     *
     *                                                                       *
     *    http://www.FreeRTOS.org/FAQHelp.html                               *
     *                                                                       *
    ***************************************************************************


    http://www.FreeRTOS.org - Documentation, books, training, latest versions,
    license and Real Time Engineers Ltd. contact details.

    http://www.FreeRTOS.org/plus - A selection of FreeRTOS ecosystem products,
    including FreeRTOS+Trace - an indispensable productivity tool, and our new
    fully thread aware and reentrant UDP/IP stack.

    http://www.OpenRTOS.com - Real Time Engineers ltd license FreeRTOS to High
    Integrity Systems, who sell the code with commercial support,
    indemnification and middleware, under the OpenRTOS brand.

    http://www.SafeRTOS.com - High Integrity Systems also provide a safety
    engineered and independently SIL3 certified version for use in safety and
    mission critical applications that require provable dependability.
*/


#ifndef FREERTOS_CONFIG_H
#define FREERTOS_CONFIG_H

/* Hardware specifics. */
#include "platform.h"

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

/* DEMO SPECIFIC SETTING:
 * Set configCREATE_LOW_POWER_DEMO to one to run the low power demo with tick
 * suppression, or 0 to run the more comprehensive test and demo application.
 * If configCREATE_LOW_POWER_DEMO is set to 1 then main() calls main_low_power().
 * If configCREATE_LOW_POWER_DEMO is set to 0 then main() calls main_full().
 */
#define configCREATE_LOW_POWER_DEMO		1


#define configUSE_PREEMPTION			1
#define configUSE_TICKLESS_IDLE			configCREATE_LOW_POWER_DEMO
#define configUSE_IDLE_HOOK				0
#define configUSE_TICK_HOOK				0
#define configCPU_CLOCK_HZ				( ICLK_HZ ) /* Set in mcu_info.h. */
#define configPERIPHERAL_CLOCK_HZ		( PCLKB_HZ ) /* Set in muc_info.h. */
#define configTICK_RATE_HZ				( ( portTickType ) 1000 )
#define configMINIMAL_STACK_SIZE		( ( unsigned short ) 100 )
#define configTOTAL_HEAP_SIZE			( ( size_t ) ( 9 * 1024 ) )
#define configMAX_TASK_NAME_LEN			( 12 )
#define configUSE_TRACE_FACILITY		1
#define configUSE_16_BIT_TICKS			0
#define configIDLE_SHOULD_YIELD			1
#define configUSE_CO_ROUTINES 			0
#define configUSE_MUTEXES				1
#define configGENERATE_RUN_TIME_STATS	0
#define configCHECK_FOR_STACK_OVERFLOW	2
#define configUSE_RECURSIVE_MUTEXES		1
#define configQUEUE_REGISTRY_SIZE		0
#define configUSE_MALLOC_FAILED_HOOK	0
#define configUSE_APPLICATION_TASK_TAG	0

#define configMAX_PRIORITIES			( ( unsigned portBASE_TYPE ) 7 )
#define configMAX_CO_ROUTINE_PRIORITIES ( 2 )

/* Software timer definitions - only included when the demo is configured to
build the full demo (as opposed to the low power demo). */
#if configCREATE_LOW_POWER_DEMO == 1
	#define configUSE_TIMERS				0
#else
	#define configUSE_TIMERS				1
	#define configTIMER_TASK_PRIORITY		( 3 )
	#define configTIMER_QUEUE_LENGTH		5
	#define configTIMER_TASK_STACK_DEPTH	( configMINIMAL_STACK_SIZE )
#endif /* configCREATE_LOW_POWER_DEMO */

/*
The interrupt priority used by the kernel itself for the tick interrupt and
the pended interrupt is set by configKERNEL_INTERRUPT_PRIORITY.  This would
normally be the lowest priority (1 in this case).  The maximum interrupt
priority from which FreeRTOS API calls can be made is set by
configMAX_SYSCALL_INTERRUPT_PRIORITY.  Interrupts that use a priority above this
will not be effected by anything the kernel is doing.  Interrupts at or below
this priority can use FreeRTOS API functions - but *only* those that end in
"FromISR".  Both these constants are defined in 'PriorityDefinitions.h' so they
can also be included in assembly source files.
*/
#include "PriorityDefinitions.h"

/* Set the following definitions to 1 to include the API function, or zero
to exclude the API function. */

#define INCLUDE_vTaskPrioritySet			1
#define INCLUDE_uxTaskPriorityGet			1
#define INCLUDE_vTaskDelete					1
#define INCLUDE_vTaskCleanUpResources		0
#define INCLUDE_vTaskSuspend				1
#define INCLUDE_vTaskDelayUntil				1
#define INCLUDE_vTaskDelay					1
#define INCLUDE_uxTaskGetStackHighWaterMark	1
#define INCLUDE_xTaskGetSchedulerState		1

extern void vAssertCalled( void );
#define configASSERT( x ) if( ( x ) == 0 ) vAssertCalled();

/* The configPRE_SLEEP_PROCESSING() and configPOST_SLEEP_PROCESSING() macros
allow the application writer to add additional code before and after the MCU is
placed into the low power state respectively.  The implementations provided in
this demo can be extended to save even more power - for example the analog
input used by the low power demo could be switched off in the pre-sleep macro
and back on again in the post sleep macro. */
void vPreSleepProcessing( unsigned long xExpectedIdleTime );
void vPostSleepProcessing( unsigned long xExpectedIdleTime );
#define configPRE_SLEEP_PROCESSING( xExpectedIdleTime ) vPreSleepProcessing( xExpectedIdleTime );
#define configPOST_SLEEP_PROCESSING( xExpectedIdleTime ) vPostSleepProcessing( xExpectedIdleTime );

/* configTICK_VECTOR must be set to the interrupt vector used by the peripheral
that generates the tick interrupt. */
#define configTICK_VECTOR VECT_CMT0_CMI0

#endif /* FREERTOS_CONFIG_H */
