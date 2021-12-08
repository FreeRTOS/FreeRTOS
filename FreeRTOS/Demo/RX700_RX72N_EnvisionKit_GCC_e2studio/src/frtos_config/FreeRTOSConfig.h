/*
 * FreeRTOS V202111.00
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

#define configUSE_PREEMPTION			1
#define configUSE_IDLE_HOOK				1
#define configUSE_TICK_HOOK				1
#define configCPU_CLOCK_HZ				(BSP_ICLK_HZ)
#define configPERIPHERAL_CLOCK_HZ		(BSP_PCLKB_HZ)
#define configTICK_RATE_HZ				(( TickType_t ) 1000)
#define configMINIMAL_STACK_SIZE		(( unsigned short ) 170)
#define configTOTAL_HEAP_SIZE_N			(60)
#define configTOTAL_HEAP_SIZE			(( size_t ) ( configTOTAL_HEAP_SIZE_N * 1024 ))
#define configMAX_TASK_NAME_LEN			(12)
#define configUSE_TRACE_FACILITY		1
#define configUSE_16_BIT_TICKS			0
#define configIDLE_SHOULD_YIELD			1
#define configUSE_CO_ROUTINES 			0
#define configUSE_MUTEXES				1
#define configGENERATE_RUN_TIME_STATS	0
#define configCHECK_FOR_STACK_OVERFLOW	2
#define configUSE_RECURSIVE_MUTEXES		1
#define configQUEUE_REGISTRY_SIZE		0
#define configUSE_MALLOC_FAILED_HOOK	1
#define configUSE_APPLICATION_TASK_TAG	0
#define configUSE_QUEUE_SETS			1
#define configUSE_COUNTING_SEMAPHORES	1
#define configMAX_PRIORITIES			(7)
#define configMAX_CO_ROUTINE_PRIORITIES (2)
#define configUSE_TASK_NOTIFICATIONS     1
#define configRECORD_STACK_HIGH_ADDRESS  0
#define configNUM_THREAD_LOCAL_STORAGE_POINTERS 0

/* Dynamic allocation and static allocation. */
#define configSUPPORT_DYNAMIC_ALLOCATION        1
#define configSUPPORT_STATIC_ALLOCATION         0

/* Run time stats gathering definitions. */
unsigned long ulGetRunTimeCounterValue( void );
void vConfigureTimerForRunTimeStats( void );
#define configGENERATE_RUN_TIME_STATS    0
//#define portCONFIGURE_TIMER_FOR_RUN_TIME_STATS()    vConfigureTimerForRunTimeStats()
//#define portGET_RUN_TIME_COUNTER_VALUE()            ulGetRunTimeCounterValue()

/* This demo makes use of one or more example stats formatting functions.  These
format the raw data provided by the uxTaskGetSystemState() function in to human
readable ASCII form.  See the notes in the implementation of vTaskList() within
FreeRTOS/Source/tasks.c for limitations. */
#define configUSE_STATS_FORMATTING_FUNCTIONS	1

/* Software timer definitions. */
#define configUSE_TIMERS				1
#define configTIMER_TASK_PRIORITY		(6)
#define configTIMER_QUEUE_LENGTH		5
#define configTIMER_TASK_STACK_DEPTH	(configMINIMAL_STACK_SIZE)

/* If configUSE_TASK_DPFPU_SUPPORT is set to 1 (or undefined) then each task will
be created without a DPFPU context, and a task must call vTaskUsesDPFPU() before
making use of any DPFPU registers.  If configUSE_TASK_DPFPU_SUPPORT is set to 2 then
tasks are created with a DPFPU context by default, and calling vTaskUsesDPFPU() has
no effect.  If configUSE_TASK_DPFPU_SUPPORT is set to 0 then tasks never take care
of any DPFPU context (even if DPFPU registers are used). */
#define configUSE_TASK_DPFPU_SUPPORT            1

/* The interrupt priority used by the kernel itself for the tick interrupt and
the pended interrupt.  This would normally be the lowest priority. */
#define configKERNEL_INTERRUPT_PRIORITY         1

/* The maximum interrupt priority from which FreeRTOS API calls can be made.
Interrupts that use a priority above this will not be effected by anything the
kernel is doing. */
#define configMAX_SYSCALL_INTERRUPT_PRIORITY    4

/* The peripheral used to generate the tick interrupt is configured as part of
the application code.  This constant should be set to the vector number of the
peripheral chosen.  As supplied this is CMT0. */
#define configTICK_VECTOR						_CMT0_CMI0

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
#define INCLUDE_eTaskGetState				1
#define INCLUDE_xTimerPendFunctionCall		1

void vAssertCalled( void );
#define configASSERT( x ) if( ( x ) == 0 ) vAssertCalled()

/* The buffer into which output generated by FreeRTOS+CLI is placed.  This must
be at least big enough to contain the output of the task-stats command, as the
example implementation does not include buffer overlow checking. */
#define configCOMMAND_INT_MAX_OUTPUT_SIZE	3500
#define configINCLUDE_QUERY_HEAP_COMMAND	1

/* Override some of the priorities set in the common demo tasks.  This is
required to ensure flase positive timing errors are not reported. */
#define bktPRIMARY_PRIORITY		(( configMAX_PRIORITIES - 3 ))
#define bktSECONDARY_PRIORITY	(( configMAX_PRIORITIES - 4 ))
#define intqHIGHER_PRIORITY		(( configMAX_PRIORITIES - 3 ))

/* When the FIT configurator or the Smart Configurator is used, platform.h has to be used. */
#define configINCLUDE_PLATFORM_H_INSTEAD_OF_IODEFINE_H  1

#endif /* FREERTOS_CONFIG_H */
