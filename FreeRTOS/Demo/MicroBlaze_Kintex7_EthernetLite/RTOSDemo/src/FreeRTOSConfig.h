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
 *
 * See http://www.freertos.org/a00110.html
 *----------------------------------------------------------*/

/* configINTERRUPT_CONTROLLER_TO_USE must be set to the ID of the interrupt
controller that is going to be used directly by FreeRTOS itself.  Most hardware
designs will only include on interrupt controller. */
#define configINTERRUPT_CONTROLLER_TO_USE XPAR_INTC_SINGLE_DEVICE_ID

/* If configINSTALL_EXCEPTION_HANDLERS is set to 1, then the kernel will
automatically install its own exception handlers before the kernel is started,
if the application writer has not already caused them to be installed using the
vPortExceptionsInstallHandlers() API function.  See the documentation page for
this demo on the FreeRTOS.org web site for more information. */
#define configINSTALL_EXCEPTION_HANDLERS 		1


/* Constants related to the behaviour or the scheduler. */
#define configUSE_PREEMPTION					1
#define configUSE_TIME_SLICING					1
#define configMAX_PRIORITIES					( 7 )
#define configTICK_RATE_HZ						( ( TickType_t ) 1000 )
#define configIDLE_SHOULD_YIELD					1
#define configUSE_16_BIT_TICKS					0 /* Only for 8 and 16-bit hardware. */
#define configUSE_PORT_OPTIMISED_TASK_SELECTION 1

/* Constants that describe the hardware and memory usage. */
#define configCPU_CLOCK_HZ						( Not used in this demo as it is determined by the hardware )
#define configMINIMAL_STACK_SIZE				( ( uint16_t ) 170 )
#define configTOTAL_HEAP_SIZE					( ( size_t ) ( 80 * 1024 ) ) /* No effect if heap_3.c is used. */
#define configMAX_TASK_NAME_LEN					( 10 )

/* Constants that build features in or out. */
#define configUSE_MUTEXES						1
#define configUSE_TICKLESS_IDLE					0
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
#define configASSERT( x ) if( ( x ) == 0 ) vAssertCalled( __FILE__, __LINE__ )
#define configQUEUE_REGISTRY_SIZE				0

/* Constants related to the generation of run time stats. */
#define configGENERATE_RUN_TIME_STATS			1
#define portCONFIGURE_TIMER_FOR_RUN_TIME_STATS() /* Only used when configGENERATE_RUN_TIME_STATS is 1.  In this case the timer is setup when the tick timer is set up. */
#define portGET_RUN_TIME_COUNTER_VALUE() ulMainGetRunTimeCounterValue()	 /* Only used when configGENERATE_RUN_TIME_STATS is 1. */

/* Software timer definitions. */
#define configUSE_TIMERS						1
#define configTIMER_TASK_PRIORITY				( configMAX_PRIORITIES - 4 )
#define configTIMER_QUEUE_LENGTH				10
#define configTIMER_TASK_STACK_DEPTH			( configMINIMAL_STACK_SIZE )

/* Set the following definitions to 1 to include the API function, or zero
to exclude the API function.  NOTE:  Setting an INCLUDE_ parameter to 0 is only
necessary if the linker does not automatically remove functions that are not
referenced anyway. */
#define INCLUDE_vTaskPrioritySet				1
#define INCLUDE_uxTaskPriorityGet				1
#define INCLUDE_vTaskDelete						1
#define INCLUDE_vTaskSuspend					1
#define INCLUDE_vTaskDelayUntil					1
#define INCLUDE_vTaskDelay						1
#define INCLUDE_uxTaskGetStackHighWaterMark		1
#define INCLUDE_xTaskGetIdleTaskHandle			0
#define INCLUDE_eTaskGetState					1
#define INCLUDE_xTaskResumeFromISR				0
#define INCLUDE_xTaskGetCurrentTaskHandle		1
#define INCLUDE_xTaskGetSchedulerState			0
#define INCLUDE_xSemaphoreGetMutexHolder		0
#define INCLUDE_xTimerPendFunctionCall			1
#define INCLUDE_xTaskAbortDelay					1
#define INCLUDE_xTaskGetHandle					1

/* This demo does not make use of example stats formatting functions.  These
format the raw data provided by the uxTaskGetSystemState() function in to human
readable ASCII form.  See the notes in the implementation of vTaskList() within
FreeRTOS/Source/tasks.c for limitations. */
#define configUSE_TRACE_FACILITY				1
#define configUSE_STATS_FORMATTING_FUNCTIONS	1

/* The size of the global output buffer that is available for use when there
are multiple command interpreters running at once (for example, one on a UART
and one on TCP/IP).  This is done to prevent an output buffer being defined by
each implementation - which would waste RAM.  In this case, there is only one
command interpreter running. */
#define configCOMMAND_INT_MAX_OUTPUT_SIZE 2048

/* Prevent the function prototypes being included from asm files. */
#ifndef __ASSEMBLER__
	uint32_t ulMainGetRunTimeCounterValue( void );
	void vAssertCalled( const char * pcFile, unsigned long ulLine );
#endif


/****** Network configuration settings - only used when the lwIP example is
built.  See the page that documents this demo on the http://www.FreeRTOS.org
website for more information. ***********************************************/

/* The priority for the task that unblocked by the MAC interrupt to process
received packets. */
#define configMAC_INPUT_TASK_PRIORITY		( configMAX_PRIORITIES - 1 )

/* The priority of the task that runs the lwIP stack. */
#define configLWIP_TASK_PRIORITY			( configMAX_PRIORITIES - 2 )

/* The priority of the task that uses lwIP sockets to provide a simple command
line interface. */
#define configCLI_TASK_PRIORITY				( tskIDLE_PRIORITY )

/* MAC address configuration. */
#define configMAC_ADDR0	0x00
#define configMAC_ADDR1	0x13
#define configMAC_ADDR2	0x14
#define configMAC_ADDR3	0x15
#define configMAC_ADDR4	0x15
#define configMAC_ADDR5	0x16

/* IP address configuration. */
#define configIP_ADDR0		10
#define configIP_ADDR1		134
#define configIP_ADDR2		134
#define configIP_ADDR3		200

/* Netmask configuration. */
#define configNET_MASK0		255
#define configNET_MASK1		255
#define configNET_MASK2		255
#define configNET_MASK3		0

#endif /* FREERTOS_CONFIG_H */

