/*
 * FreeRTOS V202212.00
 * Copyright (C) 2022 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 * https://www.FreeRTOS.org
 * https://github.com/FreeRTOS
 *
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
#include "test_config.h"

/* Scheduler Related */
#ifndef configUSE_PREEMPTION
    #define configUSE_PREEMPTION    1
#endif

#ifndef configUSE_TICKLESS_IDLE
    #define configUSE_TICKLESS_IDLE    0
#endif

#ifndef configUSE_IDLE_HOOK
    #define configUSE_IDLE_HOOK    0
#endif

#ifndef configUSE_TICK_HOOK
    #define configUSE_TICK_HOOK    1
#endif

#ifndef configTICK_RATE_HZ
    #define configTICK_RATE_HZ    ( ( TickType_t ) 1000 )
#endif

#ifndef configMAX_PRIORITIES
    #define configMAX_PRIORITIES    32
#endif

#ifndef configMINIMAL_STACK_SIZE
    #define configMINIMAL_STACK_SIZE    ( configSTACK_DEPTH_TYPE ) 256
#endif

#ifndef configUSE_16_BIT_TICKS
    #define configUSE_16_BIT_TICKS    0
#endif

#ifndef configIDLE_SHOULD_YIELD
    #define configIDLE_SHOULD_YIELD    1
#endif

/* Synchronization Related */
#ifndef configUSE_MUTEXES
    #define configUSE_MUTEXES    1
#endif

#ifndef configUSE_RECURSIVE_MUTEXES
    #define configUSE_RECURSIVE_MUTEXES    1
#endif

#ifndef configUSE_APPLICATION_TASK_TAG
    #define configUSE_APPLICATION_TASK_TAG    0
#endif

#ifndef configUSE_COUNTING_SEMAPHORES
    #define configUSE_COUNTING_SEMAPHORES    1
#endif

#ifndef configQUEUE_REGISTRY_SIZE
    #define configQUEUE_REGISTRY_SIZE    8
#endif

#ifndef configUSE_QUEUE_SETS
    #define configUSE_QUEUE_SETS    1
#endif

#ifndef configUSE_TIME_SLICING
    #define configUSE_TIME_SLICING    1
#endif

#ifndef configUSE_NEWLIB_REENTRANT
    #define configUSE_NEWLIB_REENTRANT    0
#endif

#ifndef configENABLE_BACKWARD_COMPATIBILITY
    #define configENABLE_BACKWARD_COMPATIBILITY    0
#endif

#ifndef configNUM_THREAD_LOCAL_STORAGE_POINTERS
    #define configNUM_THREAD_LOCAL_STORAGE_POINTERS    5
#endif

/* System */
#ifndef configSTACK_DEPTH_TYPE
    #define configSTACK_DEPTH_TYPE    uint32_t
#endif

#ifndef configMESSAGE_BUFFER_LENGTH_TYPE
    #define configMESSAGE_BUFFER_LENGTH_TYPE    size_t
#endif

/* Memory allocation related definitions. */
#ifndef configSUPPORT_STATIC_ALLOCATION
    #define configSUPPORT_STATIC_ALLOCATION    0
#endif

#ifndef configSUPPORT_DYNAMIC_ALLOCATION
    #define configSUPPORT_DYNAMIC_ALLOCATION    1
#endif

#ifndef configTOTAL_HEAP_SIZE
    #define configTOTAL_HEAP_SIZE    ( 128 * 1024 )
#endif

#ifndef configAPPLICATION_ALLOCATED_HEAP
    #define configAPPLICATION_ALLOCATED_HEAP    0
#endif

/* Hook function related definitions. */
#ifndef configCHECK_FOR_STACK_OVERFLOW
    #define configCHECK_FOR_STACK_OVERFLOW    2
#endif

#ifndef configUSE_MALLOC_FAILED_HOOK
    #define configUSE_MALLOC_FAILED_HOOK    1
#endif

#ifndef configUSE_DAEMON_TASK_STARTUP_HOOK
    #define configUSE_DAEMON_TASK_STARTUP_HOOK    0
#endif

/* Run time and task stats gathering related definitions. */
#ifndef configGENERATE_RUN_TIME_STATS
    #define configGENERATE_RUN_TIME_STATS    0
#endif

#ifndef configUSE_TRACE_FACILITY
    #define configUSE_TRACE_FACILITY    1
#endif

#ifndef configUSE_STATS_FORMATTING_FUNCTIONS
    #define configUSE_STATS_FORMATTING_FUNCTIONS    0
#endif

/* Co-routine related definitions. */
#ifndef configUSE_CO_ROUTINES
    #define configUSE_CO_ROUTINES    0
#endif

#ifndef configMAX_CO_ROUTINE_PRIORITIES
    #define configMAX_CO_ROUTINE_PRIORITIES    1
#endif

/* Software timer related definitions. */

#ifndef configUSE_TIMERS
    #define configUSE_TIMERS    1
#endif

#ifndef configTIMER_TASK_PRIORITY
    #define configTIMER_TASK_PRIORITY    ( configMAX_PRIORITIES - 1 )
#endif

#ifndef configTIMER_QUEUE_LENGTH
    #define configTIMER_QUEUE_LENGTH    10
#endif

#ifndef configTIMER_TASK_STACK_DEPTH
    #define configTIMER_TASK_STACK_DEPTH    1024
#endif

/* Interrupt nesting behaviour configuration. */

/*
 #define configKERNEL_INTERRUPT_PRIORITY         [dependent of processor]
 #define configMAX_SYSCALL_INTERRUPT_PRIORITY    [dependent on processor and application]
 #define configMAX_API_CALL_INTERRUPT_PRIORITY   [dependent on processor and application]
 */

/* SMP port only */
#ifndef configNUMBER_OF_CORES
    #define configNUMBER_OF_CORES    2
#endif

#ifndef configTICK_CORE
    #define configTICK_CORE    1
#endif

#ifndef configRUN_MULTIPLE_PRIORITIES
    #define configRUN_MULTIPLE_PRIORITIES    1
#endif

#ifndef configUSE_CORE_AFFINITY
    #define configUSE_CORE_AFFINITY    1
#endif

#ifndef configUSE_MINIMAL_IDLE_HOOK
    #define configUSE_MINIMAL_IDLE_HOOK    0
#endif

#ifndef configUSE_TASK_PREEMPTION_DISABLE
    #define configUSE_TASK_PREEMPTION_DISABLE    0
#endif

/* RP2040 specific */
#ifndef configSUPPORT_PICO_SYNC_INTEROP
    #define configSUPPORT_PICO_SYNC_INTEROP    1
#endif

#ifndef configSUPPORT_PICO_TIME_INTEROP
    #define configSUPPORT_PICO_TIME_INTEROP    1
#endif

#include <assert.h>
/* Define to trap errors during development. */
#ifndef configASSERT
    #define configASSERT( x )    assert( x )
#endif

/* Set the following definitions to 1 to include the API function, or zero
 * to exclude the API function. */
#ifndef INCLUDE_vTaskPrioritySet
    #define INCLUDE_vTaskPrioritySet    1
#endif

#ifndef INCLUDE_uxTaskPriorityGet
    #define INCLUDE_uxTaskPriorityGet    1
#endif

#ifndef INCLUDE_vTaskDelete
    #define INCLUDE_vTaskDelete    1
#endif

#ifndef INCLUDE_vTaskSuspend
    #define INCLUDE_vTaskSuspend    1
#endif

#ifndef INCLUDE_vTaskDelayUntil
    #define INCLUDE_vTaskDelayUntil    1
#endif

#ifndef INCLUDE_vTaskDelay
    #define INCLUDE_vTaskDelay    1
#endif

#ifndef INCLUDE_xTaskGetSchedulerState
    #define INCLUDE_xTaskGetSchedulerState    1
#endif

#ifndef INCLUDE_xTaskGetCurrentTaskHandle
    #define INCLUDE_xTaskGetCurrentTaskHandle    1
#endif

#ifndef INCLUDE_uxTaskGetStackHighWaterMark
    #define INCLUDE_uxTaskGetStackHighWaterMark    1
#endif

#ifndef INCLUDE_xTaskGetIdleTaskHandle
    #define INCLUDE_xTaskGetIdleTaskHandle    1
#endif

#ifndef INCLUDE_eTaskGetState
    #define INCLUDE_eTaskGetState    1
#endif

#ifndef INCLUDE_xTimerPendFunctionCall
    #define INCLUDE_xTimerPendFunctionCall    1
#endif

#ifndef INCLUDE_xTaskAbortDelay
    #define INCLUDE_xTaskAbortDelay    1
#endif

#ifndef INCLUDE_xTaskGetHandle
    #define INCLUDE_xTaskGetHandle    1
#endif

#ifndef INCLUDE_xTaskResumeFromISR
    #define INCLUDE_xTaskResumeFromISR    1
#endif

#ifndef INCLUDE_xQueueGetMutexHolder
    #define INCLUDE_xQueueGetMutexHolder    1
#endif

/* A header file that defines trace macro can be included here. */

#endif /* FREERTOS_CONFIG_H */
