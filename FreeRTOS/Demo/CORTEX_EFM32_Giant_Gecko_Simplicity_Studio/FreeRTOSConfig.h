/*
 * FreeRTOS Kernel V10.2.1
 * Copyright (C) 2019 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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

#ifdef __cplusplus
extern "C" {
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


/* Set configCREATE_LOW_POWER_DEMO as follows:
 *
 * 0: Build the full test and demo application.
 * 1: Build the simple blinky tickless low power demo, generating the tick
 *    interrupt from the BURTC.  EM3 will be entered, but use of the ULFRCO
 *    clock means timing will be inaccurate.
 * 2: Build the simple blinky tickless low power demo, generating the tick from
 *    the RTC.  EM2 will be entered.  The LXFO clock is used, which is more
 *    accurate than the ULFRCO clock.
 *  See the comments at the top of main.c, main_full.c and main_low_power.c for
 *  more information.
 */
#define configCREATE_LOW_POWER_DEMO		0

/* Some configuration is dependent on the demo being built. */
#if( configCREATE_LOW_POWER_DEMO == 0 )

	/* Tickless mode is not used. */

	/* Some of the standard demo test tasks assume a tick rate of 1KHz, even
	though that is faster than would normally be warranted by a real
	application. */
	#define configTICK_RATE_HZ				( 1000 )

	/* The full demo always has tasks to run so the tick will never be turned
	off.  The blinky demo will use the default tickless idle implementation to
	turn the tick off. */
	#define configUSE_TICKLESS_IDLE			0

	/* Hook function related definitions. */
	#define configUSE_TICK_HOOK				( 1 )
	#define configCHECK_FOR_STACK_OVERFLOW	( 1 )
	#define configUSE_MALLOC_FAILED_HOOK	( 1 )
	#define configUSE_IDLE_HOOK  			( 1 )

	#define configENERGY_MODE				( sleepEM3 )

#elif( configCREATE_LOW_POWER_DEMO == 1 )

	/* Tickless idle mode, generating RTOS tick interrupts from the BURTC, fed
	by the [inaccurate] ULFRCO clock. */

	/* The slow clock used to generate the tick interrupt in the low power demo
	runs at 2KHz.  Ensure the tick rate is a multiple of the clock. */
	#define configTICK_RATE_HZ				( 100 )

	/* The low power demo uses the tickless idle feature. */
	#define configUSE_TICKLESS_IDLE			1

	/* Hook function related definitions. */
	#define configUSE_TICK_HOOK				( 0 )
	#define configCHECK_FOR_STACK_OVERFLOW	( 0 )
	#define configUSE_MALLOC_FAILED_HOOK	( 0 )
	#define configUSE_IDLE_HOOK				( 0 )

	#define configENERGY_MODE				( sleepEM3 )

#elif( configCREATE_LOW_POWER_DEMO == 2 )

	/* Tickless idle mode, generating RTOS tick interrupts from the RTC, fed
	by the LXFO clock. */

	/* The slow clock used to generate the tick interrupt in the low power demo
	runs at 32768/8=4096Hz.  Ensure the tick rate is a multiple of the clock. */
	#define configTICK_RATE_HZ				( 128 )

	/* The low power demo uses the tickless idle feature. */
	#define configUSE_TICKLESS_IDLE			1

	/* Hook function related definitions. */
	#define configUSE_TICK_HOOK				( 0 )
	#define configCHECK_FOR_STACK_OVERFLOW	( 0 )
	#define configUSE_MALLOC_FAILED_HOOK	( 0 )
	#define configUSE_IDLE_HOOK				( 0 )

	#define configENERGY_MODE				( sleepEM3 )

#endif

/* Main functions*/
#define configUSE_PREEMPTION					( 1 )
#define configUSE_PORT_OPTIMISED_TASK_SELECTION	( 1 )
#define configSUPPORT_STATIC_ALLOCATION			( 1 )
#define configCPU_CLOCK_HZ						(( unsigned long ) 14000000)
#define configMAX_PRIORITIES					( 6 )
#define configMINIMAL_STACK_SIZE				(( unsigned short ) 130)
#define configTOTAL_HEAP_SIZE					(( size_t )(24000))
#define configMAX_TASK_NAME_LEN				 	( 10 )
#define configUSE_TRACE_FACILITY				( 0 )
#define configUSE_16_BIT_TICKS					( 0 )
#define configIDLE_SHOULD_YIELD					( 0 )
#define configUSE_MUTEXES						( 1 )
#define configUSE_RECURSIVE_MUTEXES				( 1 )
#define configUSE_COUNTING_SEMAPHORES			( 1 )
#define configUSE_ALTERNATIVE_API				( 0 )/* Deprecated! */
#define configQUEUE_REGISTRY_SIZE				( 10 )
#define configUSE_QUEUE_SETS					( 0 )

/* Run time stats gathering related definitions. */
#define configGENERATE_RUN_TIME_STATS			( 0 )

/* Co-routine related definitions. */
#define configUSE_CO_ROUTINES					( 0 )
#define configMAX_CO_ROUTINE_PRIORITIES			( 1 )

/* Software timer related definitions. */
#define configUSE_TIMERS						( 1 )
#define configTIMER_TASK_PRIORITY				( configMAX_PRIORITIES - 1 ) /* Highest priority */
#define configTIMER_QUEUE_LENGTH				( 10 )
#define configTIMER_TASK_STACK_DEPTH			( configMINIMAL_STACK_SIZE )

/* Cortex-M specific definitions. */
#ifdef __NVIC_PRIO_BITS
	/* __BVIC_PRIO_BITS will be specified when CMSIS is being used. */
	#define configPRIO_BITS		       __NVIC_PRIO_BITS
#else
	#define configPRIO_BITS		       3	/* 7 priority levels */
#endif

/* The lowest interrupt priority that can be used in a call to a "set priority"
function. */
#define configLIBRARY_LOWEST_INTERRUPT_PRIORITY			0x07

/* The highest interrupt priority that can be used by any interrupt service
routine that makes calls to interrupt safe FreeRTOS API functions.  DO NOT CALL
INTERRUPT SAFE FREERTOS API FUNCTIONS FROM ANY INTERRUPT THAT HAS A HIGHER
PRIORITY THAN THIS! (higher priorities are lower numeric values. */
#define configLIBRARY_MAX_SYSCALL_INTERRUPT_PRIORITY	0x05

/* Interrupt priorities used by the kernel port layer itself.  These are generic
to all Cortex-M ports, and do not rely on any particular library functions. */
#define configKERNEL_INTERRUPT_PRIORITY		 ( configLIBRARY_LOWEST_INTERRUPT_PRIORITY << (8 - configPRIO_BITS) )
/* !!!! configMAX_SYSCALL_INTERRUPT_PRIORITY must not be set to zero !!!!
See http://www.FreeRTOS.org/RTOS-Cortex-M3-M4.html. */
#define configMAX_SYSCALL_INTERRUPT_PRIORITY	 ( configLIBRARY_MAX_SYSCALL_INTERRUPT_PRIORITY << (8 - configPRIO_BITS) )


/* Optional functions - most linkers will remove unused functions anyway. */
#define INCLUDE_vTaskPrioritySet				( 1 )
#define INCLUDE_uxTaskPriorityGet				( 1 )
#define INCLUDE_vTaskDelete						( 1 )
#define INCLUDE_vTaskSuspend					( 1 )
#define INCLUDE_xResumeFromISR					( 1 )
#define INCLUDE_vTaskDelayUntil					( 1 )
#define INCLUDE_vTaskDelay						( 1 )
#define INCLUDE_xTaskGetSchedulerState			( 1 )
#define INCLUDE_xTaskGetCurrentTaskHandle		( 1 )
#define INCLUDE_uxTaskGetStackHighWaterMark		( 0 )
#define INCLUDE_xTaskGetIdleTaskHandle			( 0 )
#define INCLUDE_xTimerGetTimerDaemonTaskHandle	( 0 )
#define INCLUDE_eTaskGetState					( 1 )
#define INCLUDE_xTimerPendFunctionCall			( 1 )

/* Stop if an assertion fails. */
#define configASSERT( x )	if( ( x ) == 0 ) { taskDISABLE_INTERRUPTS(); for( ;; ); }

/* Definitions that map the FreeRTOS port interrupt handlers to their CMSIS
standard names. */
#define vPortSVCHandler		SVC_Handler
#define xPortPendSVHandler	 PendSV_Handler
#define xPortSysTickHandler	SysTick_Handler

/* For the linker. */
#define fabs __builtin_fabs

#ifdef __cplusplus
}
#endif
#endif /* FREERTOS_CONFIG_H */

