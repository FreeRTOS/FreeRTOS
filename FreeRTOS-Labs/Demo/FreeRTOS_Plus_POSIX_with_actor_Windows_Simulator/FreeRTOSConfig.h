/*
 * FreeRTOS Kernel V10.0.1
 * Copyright (C) 2017 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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

#include <stdint.h>

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

#define configUSE_PREEMPTION			1
#define configTICK_RATE_HZ				( 1000 ) /* In this non-real time simulated environment the tick frequency has to be at least a multiple of the Win32 tick frequency, and therefore very slow. */
#define configMINIMAL_STACK_SIZE		( ( unsigned short ) 60 ) /* In this simulated case, the stack only has to hold one small structure as the real stack is part of the Win32 thread. */
#define configMAX_TASK_NAME_LEN			( 7 )
#define configUSE_TRACE_FACILITY		0
#define configUSE_16_BIT_TICKS			0
#define configIDLE_SHOULD_YIELD			1
#define configUSE_CO_ROUTINES 			0
#define configUSE_MUTEXES				1
#define configCHECK_FOR_STACK_OVERFLOW	0 /* Not applicable to the Win32 port. */
#define configUSE_RECURSIVE_MUTEXES		1
#define configQUEUE_REGISTRY_SIZE		0
#define configUSE_APPLICATION_TASK_TAG	1
#define configUSE_COUNTING_SEMAPHORES	1
#define configUSE_ALTERNATIVE_API		0

#define configUSE_TIMERS				1
#define configTIMER_TASK_PRIORITY		2
#define configTIMER_QUEUE_LENGTH		20
#define configTIMER_TASK_STACK_DEPTH	( configMINIMAL_STACK_SIZE * 2 )

#define configMAX_PRIORITIES			( 7 )
#define configMAX_CO_ROUTINE_PRIORITIES ( 2 )

/* Hook functions */
#define configUSE_IDLE_HOOK				0
#define configUSE_TICK_HOOK				0
#define configUSE_MALLOC_FAILED_HOOK	1

/* Co-routine definitions. */
#define configUSE_CO_ROUTINES 			0

/* Set the following definitions to 1 to include the API function, or zero
to exclude the API function. */
#define INCLUDE_vTaskPrioritySet                1
#define INCLUDE_uxTaskPriorityGet               1
#define INCLUDE_vTaskDelete                     1
#define INCLUDE_vTaskCleanUpResources           0
#define INCLUDE_vTaskSuspend                    1
#define INCLUDE_vTaskDelayUntil                 1
#define INCLUDE_vTaskDelay                      1
#define INCLUDE_uxTaskGetStackHighWaterMark     1
#define INCLUDE_xTaskGetSchedulerState          1
#define INCLUDE_xTimerGetTimerTaskHandle        0
#define INCLUDE_xTaskGetIdleTaskHandle          0
#define INCLUDE_xQueueGetMutexHolder            1
#define INCLUDE_eTaskGetState                   1
#define INCLUDE_xEventGroupSetBitsFromISR       1
#define INCLUDE_xTimerPendFunctionCall          1
#define INCLUDE_xTaskGetCurrentTaskHandle       1
#define INCLUDE_xTaskAbortDelay                 1

/* heap_4.c,  */
#define configTOTAL_HEAP_SIZE				( ( size_t ) ( 2048U * 1024U ) )

/* Allow RTOS objects to be created using RAM provided by the application writer. */
#define configSUPPORT_STATIC_ALLOCATION         1

/*  Create RTOS objects using dynamically allocated RAM */
#define configSUPPORT_DYNAMIC_ALLOCATION		1

/* This demo makes use of one or more example stats formatting functions.  These
format the raw data provided by the uxTaskGetSystemState() function in to human
readable ASCII form.  See the notes in the implementation of vTaskList() within
FreeRTOS/Source/tasks.c for limitations. */
#define configUSE_STATS_FORMATTING_FUNCTIONS	1

/* Run time stats gathering definitions. */
#define configGENERATE_RUN_TIME_STATS	0

/* Assert call defined for debug builds. */
extern void vAssertCalled(const char * pcFile, uint32_t ulLine);
#define configASSERT( x )    if( ( x ) == 0 ) vAssertCalled( __FILE__, __LINE__ )

#endif /* FREERTOS_CONFIG_H */
