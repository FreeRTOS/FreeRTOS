/*
    FreeRTOS V9.0.1 - Copyright (C) 2017 Real Time Engineers Ltd.
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


/******************************************************************************
	See http://www.freertos.org/a00110.html for an explanation of the
	definitions contained in this file.
******************************************************************************/

#ifndef FREERTOS_CONFIG_H
#define FREERTOS_CONFIG_H


/* Set mainCREATE_SIMPLE_BLINKY_DEMO_ONLY to one to run the simple blinky demo,
or 0 to run the more comprehensive test and demo application.

The comprehensive demo uses FreeRTOS+CLI to create a simple command line
interface through a UART.

The blinky demo uses FreeRTOS's tickless idle mode to reduce power consumption.
See the notes on the web page below regarding the difference in power saving
that can be achieved between using the generic tickless implementation (as used
by the blinky demo) and a tickless implementation that is tailored specifically
to the MSP432.

See http://www.FreeRTOS.org/TI_MSP432_Free_RTOS_Demo.html for instructions. */
#define configCREATE_SIMPLE_TICKLESS_DEMO	1


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

/* Constants related to the behaviour or the scheduler. */
#define configUSE_PORT_OPTIMISED_TASK_SELECTION	1
#define configUSE_PREEMPTION					1
#define configUSE_TIME_SLICING					1
#define configMAX_PRIORITIES					( 5 )
#define configIDLE_SHOULD_YIELD					1
#define configUSE_16_BIT_TICKS					0 /* Only for 8 and 16-bit hardware. */

/* Constants that describe the hardware and memory usage. */
#define configCPU_CLOCK_HZ						MAP_CS_getMCLK()
#define configMINIMAL_STACK_SIZE				( ( uint16_t ) 100 )
#define configMAX_TASK_NAME_LEN					( 12 )

/* Note heap_5.c is used so this only defines the part of the heap that is in
the first block of RAM on the LPC device.  See the initialisation of the heap
in main.c. */
#define configTOTAL_HEAP_SIZE					( ( size_t ) ( 50 * 1024 ) )

/* Constants that build features in or out. */
#define configUSE_MUTEXES						1
#define configUSE_TICKLESS_IDLE					1
#define configUSE_APPLICATION_TASK_TAG			0
#define configUSE_NEWLIB_REENTRANT 				0
#define configUSE_CO_ROUTINES 					0
#define configUSE_COUNTING_SEMAPHORES 			1
#define configUSE_RECURSIVE_MUTEXES				1
#define configUSE_QUEUE_SETS					0
#define configUSE_TASK_NOTIFICATIONS			1

/* Constants that define which hook (callback) functions should be used. */
#define configUSE_IDLE_HOOK						1
#define configUSE_TICK_HOOK						1
#define configUSE_MALLOC_FAILED_HOOK			1

/* Constants provided for debugging and optimisation assistance. */
#define configCHECK_FOR_STACK_OVERFLOW			2
#define configASSERT( x ) if( ( x ) == 0 ) { taskDISABLE_INTERRUPTS(); for( ;; ); }
#define configQUEUE_REGISTRY_SIZE				0

/* Software timer definitions. */
#define configUSE_TIMERS						1
#define configTIMER_TASK_PRIORITY				( 3 )
#define configTIMER_QUEUE_LENGTH				5
#define configTIMER_TASK_STACK_DEPTH			( configMINIMAL_STACK_SIZE  )

/* Set the following definitions to 1 to include the API function, or zero
to exclude the API function.  NOTE:  Setting an INCLUDE_ parameter to 0 is only
necessary if the linker does not automatically remove functions that are not
referenced anyway. */
#define INCLUDE_vTaskPrioritySet				1
#define INCLUDE_uxTaskPriorityGet				1
#define INCLUDE_vTaskDelete						1
#define INCLUDE_vTaskCleanUpResources			0
#define INCLUDE_vTaskSuspend					1
#define INCLUDE_vTaskDelayUntil					1
#define INCLUDE_vTaskDelay						1
#define INCLUDE_uxTaskGetStackHighWaterMark		0
#define INCLUDE_xTaskGetIdleTaskHandle			0
#define INCLUDE_eTaskGetState					1
#define INCLUDE_xTaskResumeFromISR				0
#define INCLUDE_xTaskGetCurrentTaskHandle		1
#define INCLUDE_xTaskGetSchedulerState			0
#define INCLUDE_xSemaphoreGetMutexHolder		0
#define INCLUDE_xTimerPendFunctionCall			1

/* This demo makes use of one or more example stats formatting functions.  These
format the raw data provided by the uxTaskGetSystemState() function in to human
readable ASCII form.  See the notes in the implementation of vTaskList() within
FreeRTOS/Source/tasks.c for limitations. */
#define configUSE_STATS_FORMATTING_FUNCTIONS	1

/* Dimensions a buffer that can be used by the FreeRTOS+CLI command
interpreter.  See the FreeRTOS+CLI documentation for more information:
http://www.FreeRTOS.org/FreeRTOS-Plus/FreeRTOS_Plus_CLI/ */
#define configCOMMAND_INT_MAX_OUTPUT_SIZE		2048


/* Cortex-M3/4 interrupt priority configuration follows...................... */

/* Use the system definition, if there is one. */
#ifdef __NVIC_PRIO_BITS
	#define configPRIO_BITS       __NVIC_PRIO_BITS
#else
	#define configPRIO_BITS       3     /* 8 priority levels */
#endif

/* The lowest interrupt priority that can be used in a call to a "set priority"
function. */
#define configLIBRARY_LOWEST_INTERRUPT_PRIORITY			0x07

/* The highest interrupt priority that can be used by any interrupt service
routine that makes calls to interrupt safe FreeRTOS API functions.  DO NOT CALL
INTERRUPT SAFE FREERTOS API FUNCTIONS FROM ANY INTERRUPT THAT HAS A HIGHER
PRIORITY THAN THIS! (higher priorities are lower numeric values. */
#define configLIBRARY_MAX_SYSCALL_INTERRUPT_PRIORITY	5

/* Interrupt priorities used by the kernel port layer itself.  These are generic
to all Cortex-M ports, and do not rely on any particular library functions. */
#define configKERNEL_INTERRUPT_PRIORITY 		( configLIBRARY_LOWEST_INTERRUPT_PRIORITY << (8 - configPRIO_BITS) )
/* !!!! configMAX_SYSCALL_INTERRUPT_PRIORITY must not be set to zero !!!!
See http://www.FreeRTOS.org/RTOS-Cortex-M3-M4.html. */
#define configMAX_SYSCALL_INTERRUPT_PRIORITY 	( configLIBRARY_MAX_SYSCALL_INTERRUPT_PRIORITY << (8 - configPRIO_BITS) )

/* Definitions that map the FreeRTOS port interrupt handlers to their CMSIS
standard names - can't be used with CCS due to limitations in the assemblers
pre-processing. */
#ifndef __TI_COMPILER_VERSION__
	#define xPortPendSVHandler 	PendSV_Handler
	#define vPortSVCHandler 	SVC_Handler
	#define xPortSysTickHandler	SysTick_Handler
#endif

/* The trace facility is turned on to make some functions available for use in
CLI commands. */
#define configUSE_TRACE_FACILITY	1

/* Some board specifics.   The LED is on P1.0, configure the pin as output. */
#define configTOGGLE_LED() 		GPIO_toggleOutputOnPin( GPIO_PORT_P1, GPIO_PIN0 )

/* The #ifdef guards against the file being included from IAR assembly files. */
#ifndef __IASMARM__

	/* TI driver library includes. */
	#include <driverlib.h>

	void vPreSleepProcessing( uint32_t ulExpectedIdleTime );
	#define configPRE_SLEEP_PROCESSING( x ) vPreSleepProcessing( x )

	#if configCREATE_SIMPLE_TICKLESS_DEMO == 1

		/* Constants related to the generation of run time stats.  Run time stats
		are gathered in the full demo, not the blinky demo. */
		#define configGENERATE_RUN_TIME_STATS			0
		#define portCONFIGURE_TIMER_FOR_RUN_TIME_STATS()
		#define portGET_RUN_TIME_COUNTER_VALUE()		0

		/* The blinky demo can use a slow tick rate to save power. */
		#define configTICK_RATE_HZ						( ( TickType_t ) 100 )

	#else

		/* Constants related to the generation of run time stats.  Run time stats
		are gathered in the full demo, not the blinky demo. */
		void vConfigureTimerForRunTimeStats( void );
		uint32_t ulGetRunTimeCounterValue( void );
		#define configGENERATE_RUN_TIME_STATS	1
		#define portCONFIGURE_TIMER_FOR_RUN_TIME_STATS() vConfigureTimerForRunTimeStats()
		#define portGET_RUN_TIME_COUNTER_VALUE() ulGetRunTimeCounterValue()

		/* Some of the tests in the full demo expecte a 1ms tick rate. */
		#define configTICK_RATE_HZ						( ( TickType_t ) 1000 )

	#endif /* configCREATE_SIMPLE_TICKLESS_DEMO */
#endif /* __IASMARM__ */

#endif /* FREERTOS_CONFIG_H */

