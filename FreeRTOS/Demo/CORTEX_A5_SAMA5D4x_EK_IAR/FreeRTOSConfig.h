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

#define configCPU_CLOCK_HZ						/* Not used in this port as the value comes from the Atmel libraries. */
#define configUSE_PORT_OPTIMISED_TASK_SELECTION	1
#define configUSE_TICKLESS_IDLE					0
#define configTICK_RATE_HZ						( ( TickType_t ) 1000 )
#define configUSE_PREEMPTION					1
#define configUSE_IDLE_HOOK						1
#define configUSE_TICK_HOOK						1
#define configMAX_PRIORITIES					( 5 )
#define configMINIMAL_STACK_SIZE				( ( unsigned short ) 120 )
#define configTOTAL_HEAP_SIZE					( ( size_t ) ( 38 * 1024 ) )
#define configMAX_TASK_NAME_LEN					( 10 )
#define configUSE_TRACE_FACILITY				1
#define configUSE_16_BIT_TICKS					0
#define configIDLE_SHOULD_YIELD					1
#define configUSE_MUTEXES						1
#define configQUEUE_REGISTRY_SIZE				8
#define configCHECK_FOR_STACK_OVERFLOW			2
#define configUSE_RECURSIVE_MUTEXES				1
#define configUSE_MALLOC_FAILED_HOOK			1
#define configUSE_APPLICATION_TASK_TAG			0
#define configUSE_COUNTING_SEMAPHORES			1

/* Co-routine definitions. */
#define configUSE_CO_ROUTINES 					0
#define configMAX_CO_ROUTINE_PRIORITIES 		( 2 )

/* Software timer definitions. */
#define configUSE_TIMERS						1
#define configTIMER_TASK_PRIORITY				( configMAX_PRIORITIES - 1 )
#define configTIMER_QUEUE_LENGTH				5
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
#define INCLUDE_eTaskGetState					1
#define INCLUDE_xEventGroupSetBitsFromISR		1
#define INCLUDE_xTimerPendFunctionCall			1

/* This demo makes use of one or more example stats formatting functions.  These
format the raw data provided by the uxTaskGetSystemState() function in to human
readable ASCII form.  See the notes in the implementation of vTaskList() within
FreeRTOS/Source/tasks.c for limitations. */
#define configUSE_STATS_FORMATTING_FUNCTIONS	1

/* Cortex-A specific setting:  FPU has 32 (rather than 16) d registers.  See:
http://www.FreeRTOS.org/Using-FreeRTOS-on-Cortex-A-proprietary-interrupt-controller.html */
#define configFPU_D32	1

/* Cortex-A specific setting:  The address of the register within the interrupt
controller from which the address of the current interrupt's handling function
can be obtained.  See:
http://www.FreeRTOS.org/Using-FreeRTOS-on-Cortex-A-proprietary-interrupt-controller.html */
#define configINTERRUPT_VECTOR_ADDRESS	0xFC06E010UL

/* Cortex-A specific setting:  The address of End of Interrupt register within
the interrupt controller.  See:
http://www.FreeRTOS.org/Using-FreeRTOS-on-Cortex-A-proprietary-interrupt-controller.html */
#define configEOI_ADDRESS	0xFC06E038UL

/* Cortex-A specific setting: configCLEAR_TICK_INTERRUPT() is a macro that is
called by the RTOS kernel's tick handler to clear the source of the tick
interrupt.  See:
http://www.FreeRTOS.org/Using-FreeRTOS-on-Cortex-A-proprietary-interrupt-controller.html */
#define configCLEAR_TICK_INTERRUPT() ( void ) ( *( ( volatile uint32_t * ) 0xFC068638UL ) ) /* Read PIT_PIVR to clear interrupt. */

/* Prevent C code being included in assembly files when the IAR compiler is
used. */
#ifndef __IASMARM__

	/* The interrupt nesting test creates a 20KHz timer.  For convenience the
	20KHz timer is also used to generate the run time stats time base, removing
	the need to use a separate timer for that purpose.  The 20KHz timer
	increments ulHighFrequencyTimerCounts, which is used as the time base.
	Therefore the following macro is not implemented. */
	#define configGENERATE_RUN_TIME_STATS	1
	extern volatile uint32_t ulHighFrequencyTimerCounts;
	#define portCONFIGURE_TIMER_FOR_RUN_TIME_STATS()
	#define portGET_RUN_TIME_COUNTER_VALUE() ulHighFrequencyTimerCounts

	/* The size of the global output buffer that is available for use when there
	are multiple command interpreters running at once (for example, one on a UART
	and one on TCP/IP).  This is done to prevent an output buffer being defined by
	each implementation - which would waste RAM.  In this case, there is only one
	command interpreter running. */
	#define configCOMMAND_INT_MAX_OUTPUT_SIZE 3000

	/* Normal assert() semantics without relying on the provision of an assert.h
	header file. */
	void vAssertCalled( const char * pcFile, unsigned long ulLine );
	#define configASSERT( x ) if( ( x ) == 0 ) vAssertCalled( __FILE__, __LINE__ );



	/****** Hardware specific settings. *******************************************/

	/*
	 * The application must provide a function that configures a peripheral to
	 * create the FreeRTOS tick interrupt, then define configSETUP_TICK_INTERRUPT()
	 * in FreeRTOSConfig.h to call the function.  FreeRTOS_Tick_Handler() must
	 * be installed as the peripheral's interrupt handler.
	 */
	void vConfigureTickInterrupt( void );
	#define configSETUP_TICK_INTERRUPT() vConfigureTickInterrupt()

#endif /* __IASMARM__ */

#endif /* FREERTOS_CONFIG_H */

