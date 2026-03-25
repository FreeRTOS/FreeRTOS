/*
 * FreeRTOS V202212.00
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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
 * FreeRTOSConfig_Template.h
 *
 * Template configuration file for FreeRTOS.
 *
 * Copy this file to your project directory as "FreeRTOSConfig.h" and
 * adjust the settings below for your particular hardware and application.
 *
 * Each configuration option is documented inline. For the full reference,
 * see: https://www.FreeRTOS.org/a00110.html
 *----------------------------------------------------------*/

/*****************************************************************************
 *                  REQUIRED SETTINGS - Must be defined                       *
 *****************************************************************************/

/* Set to 1 for preemptive scheduling, or 0 for cooperative scheduling. */
#define configUSE_PREEMPTION                            1

/* Frequency of the RTOS tick interrupt in Hz.  Typical values range from
 * 100 Hz to 1000 Hz.  Higher values give better time resolution but increase
 * CPU overhead. */
#define configTICK_RATE_HZ                              ( ( TickType_t ) 1000 )

/* Size of the stack (in words, not bytes) allocated to the idle task.
 * Adjust for your platform's minimum requirements. */
#define configMINIMAL_STACK_SIZE                        ( ( unsigned short ) 128 )

/* Total number of priority levels available to application tasks.
 * The idle task uses priority 0 (the lowest). */
#define configMAX_PRIORITIES                            ( 7 )

/* Set to 1 to include the idle hook function, or 0 to omit it.
 * If 1, you must implement: void vApplicationIdleHook( void ); */
#define configUSE_IDLE_HOOK                             0

/* Set to 1 to include the tick hook function, or 0 to omit it.
 * If 1, you must implement: void vApplicationTickHook( void ); */
#define configUSE_TICK_HOOK                             0

/*****************************************************************************
 *                      TICK TYPE / COUNTER WIDTH                            *
 *****************************************************************************/

/* Define exactly ONE of the following two options:
 *
 * Option A (legacy): configUSE_16_BIT_TICKS
 *   Set to 1 for 16-bit tick type (8/16-bit architectures), 0 for 32-bit.
 *
 * Option B (preferred): configTICK_TYPE_WIDTH_IN_BITS
 *   TICK_TYPE_WIDTH_16_BITS, TICK_TYPE_WIDTH_32_BITS, or
 *   TICK_TYPE_WIDTH_64_BITS.
 */
#define configUSE_16_BIT_TICKS                          0

/* #define configTICK_TYPE_WIDTH_IN_BITS               TICK_TYPE_WIDTH_32_BITS */

/*****************************************************************************
 *                       MEMORY ALLOCATION                                   *
 *****************************************************************************/

/* Set to 1 to enable static object creation APIs (xTaskCreateStatic, etc.).
 * If 1 and configKERNEL_PROVIDED_STATIC_MEMORY is 0, you must implement
 * vApplicationGetIdleTaskMemory() (and vApplicationGetTimerTaskMemory() if
 * timers are enabled). */
#define configSUPPORT_STATIC_ALLOCATION                 0

/* Set to 1 to enable dynamic allocation APIs (xTaskCreate, etc.).
 * Requires a heap implementation (heap_1.c through heap_5.c). */
#define configSUPPORT_DYNAMIC_ALLOCATION                1

/* Total size in bytes of the FreeRTOS heap when using heap_1.c, heap_2.c,
 * heap_4.c, or heap_5.c.  Not used by heap_3.c (which wraps standard
 * malloc/free). */
#define configTOTAL_HEAP_SIZE                           ( ( size_t ) ( 10 * 1024 ) )

/* Set to 1 if the application supplies the heap array (ucHeap[]).
 * Only relevant when using heap_1.c, heap_2.c, heap_4.c, or heap_5.c. */
#define configAPPLICATION_ALLOCATED_HEAP                0

/* Set to 1 to let the kernel provide static memory for internal objects
 * (idle task, timer task) so the application does not need to implement
 * vApplicationGetIdleTaskMemory() / vApplicationGetTimerTaskMemory(). */
#define configKERNEL_PROVIDED_STATIC_MEMORY             0

/* Set to 1 to enable heap integrity canary checks. */
#define configENABLE_HEAP_PROTECTOR                     0

/*****************************************************************************
 *                      SCHEDULING BEHAVIOR                                  *
 *****************************************************************************/

/* Set to 1 to enable time slicing (round-robin) among tasks of equal
 * priority.  Set to 0 to disable -- the running task will not be preempted
 * by another task of the same priority. */
#define configUSE_TIME_SLICING                          1

/* Set to 1 to have the idle task yield when another idle-priority task is
 * ready to run. */
#define configIDLE_SHOULD_YIELD                         1

/* Set to 1 to use a port-optimised method for selecting the next task to
 * run.  Not available on all ports or in SMP configurations. */
#define configUSE_PORT_OPTIMISED_TASK_SELECTION         0

/* Initial value of the RTOS tick counter.  Normally 0.  Can be set to a
 * high value (e.g., 0xFFFFFF00) to test tick counter overflow handling. */
#define configINITIAL_TICK_COUNT                        0

/*****************************************************************************
 *                       SMP (MULTI-CORE) SETTINGS                           *
 *****************************************************************************/

/* Number of cores.  Set to 1 for single-core (default). */
#define configNUMBER_OF_CORES                           1

/* Set to 1 to allow tasks of different priorities to run simultaneously
 * across cores. */
#define configRUN_MULTIPLE_PRIORITIES                    0

/* Set to 1 to enable per-task core affinity (pin tasks to specific cores). */
#define configUSE_CORE_AFFINITY                         0

/* Set to 1 to allow individual tasks to disable their own preemption.
 * Only meaningful when configRUN_MULTIPLE_PRIORITIES is 1. */
#define configUSE_TASK_PREEMPTION_DISABLE               0

/* Set to 1 to enable the passive idle hook (SMP only).
 * If 1, you must implement: void vApplicationPassiveIdleHook( void ); */
#define configUSE_PASSIVE_IDLE_HOOK                     0

/*****************************************************************************
 *                       TASK SETTINGS                                       *
 *****************************************************************************/

/* Maximum number of characters (including null terminator) in a task name. */
#define configMAX_TASK_NAME_LEN                         ( 16 )

/* Type used for stack depth parameters.  Use uint32_t if stack depths can
 * exceed 65535 words. */
#define configSTACK_DEPTH_TYPE                          uint16_t

/* Stack overflow detection method:
 *   0 = None
 *   1 = Check stack pointer on context switch
 *   2 = Also fill stack with known pattern and check for corruption
 * If non-zero, you must implement:
 *   void vApplicationStackOverflowHook( TaskHandle_t xTask, char * pcTaskName );
 */
#define configCHECK_FOR_STACK_OVERFLOW                  0

/* Set to 1 to record the stack high address in the TCB (useful for
 * debugger stack backtrace support). */
#define configRECORD_STACK_HIGH_ADDRESS                 0

/* Set to 1 to enable per-task application tags (set/get with
 * xTaskCallApplicationTaskHook). */
#define configUSE_APPLICATION_TASK_TAG                  0

/*****************************************************************************
 *                       QUEUE / SYNC / IPC                                  *
 *****************************************************************************/

/* Set to 1 to include mutex functionality. */
#define configUSE_MUTEXES                               0

/* Set to 1 to include recursive mutex functionality (requires
 * configUSE_MUTEXES == 1). */
#define configUSE_RECURSIVE_MUTEXES                     0

/* Set to 1 to include counting semaphore functionality. */
#define configUSE_COUNTING_SEMAPHORES                   0

/* Set to 1 to include queue set functionality (allows a task to block on
 * multiple queues/semaphores simultaneously). */
#define configUSE_QUEUE_SETS                            0

/* Maximum number of queues/semaphores registered in the queue registry.
 * The registry is used by kernel-aware debuggers.  Set to 0 to disable. */
#define configQUEUE_REGISTRY_SIZE                       0

/*****************************************************************************
 *                       TASK NOTIFICATIONS                                  *
 *****************************************************************************/

/* Set to 1 to enable task notification APIs.  Each notification is lighter
 * weight than a semaphore or event group. */
#define configUSE_TASK_NOTIFICATIONS                    1

/* Number of notification slots per task (1 to N).  Most applications need
 * only 1. */
#define configTASK_NOTIFICATION_ARRAY_ENTRIES           1

/*****************************************************************************
 *                       SOFTWARE TIMERS                                     *
 *****************************************************************************/

/* Set to 1 to enable software timer functionality.  When enabled, the
 * following three settings MUST also be defined. */
#define configUSE_TIMERS                                0

#if ( configUSE_TIMERS == 1 )

    /* Priority of the timer service/daemon task.
     * (configMAX_PRIORITIES - 1) gives it the highest priority. */
    #define configTIMER_TASK_PRIORITY                   ( configMAX_PRIORITIES - 1 )

    /* Length of the timer command queue. */
    #define configTIMER_QUEUE_LENGTH                    10

    /* Stack depth (in words) for the timer service task. */
    #define configTIMER_TASK_STACK_DEPTH                ( configMINIMAL_STACK_SIZE * 2 )

#endif /* configUSE_TIMERS */

/*****************************************************************************
 *                       CO-ROUTINES (LEGACY)                                *
 *****************************************************************************/

/* Set to 1 to include co-routine support (legacy feature, generally not
 * recommended for new designs). */
#define configUSE_CO_ROUTINES                           0

/* Number of co-routine priority levels.  Only needed when
 * configUSE_CO_ROUTINES is 1. */
#define configMAX_CO_ROUTINE_PRIORITIES                 ( 2 )

/*****************************************************************************
 *                       HOOKS                                               *
 *****************************************************************************/

/* Set to 1 to use the malloc failed hook.
 * If 1, you must implement:
 *   void vApplicationMallocFailedHook( void ); */
#define configUSE_MALLOC_FAILED_HOOK                    0

/* Set to 1 to call a hook when the timer/daemon task starts.
 * If 1, you must implement:
 *   void vApplicationDaemonTaskStartupHook( void ); */
#define configUSE_DAEMON_TASK_STARTUP_HOOK              0

/*****************************************************************************
 *                       TICKLESS IDLE / LOW POWER                           *
 *****************************************************************************/

/* Set to 1 to enable the built-in tickless idle functionality.
 * Set to 2 to use an application-provided tickless implementation. */
#define configUSE_TICKLESS_IDLE                         0

/* Minimum expected idle time (in ticks) before the kernel enters tickless
 * idle mode.  Must be >= 2. */
#define configEXPECTED_IDLE_TIME_BEFORE_SLEEP           2

/* Optional hook macros for low-power mode entry/exit.
 * Define as needed for your hardware. */
/* #define configPRE_SUPPRESS_TICKS_AND_SLEEP_PROCESSING( xExpectedIdleTime )  */
/* #define configPRE_SLEEP_PROCESSING( xExpectedIdleTime )                     */
/* #define configPOST_SLEEP_PROCESSING( xExpectedIdleTime )                    */

/*****************************************************************************
 *                       TRACE / STATS / DEBUG                               *
 *****************************************************************************/

/* Set to 1 to include additional structure members and API functions for
 * trace and visualization tools. */
#define configUSE_TRACE_FACILITY                        0

/* Set to 1 to enable per-task run-time statistics collection.
 * When enabled, you must also define:
 *   portCONFIGURE_TIMER_FOR_RUN_TIME_STATS()
 *   portGET_RUN_TIME_COUNTER_VALUE()  (or portALT_GET_RUN_TIME_COUNTER_VALUE) */
#define configGENERATE_RUN_TIME_STATS                   0

/* Type used for run-time counters. */
#define configRUN_TIME_COUNTER_TYPE                     uint32_t

/* Set to 1 to include vTaskList() and vTaskGetRunTimeStats() helper
 * functions.  Requires configUSE_TRACE_FACILITY and/or
 * configGENERATE_RUN_TIME_STATS to be useful. */
#define configUSE_STATS_FORMATTING_FUNCTIONS            0

/* Maximum buffer length used by stats formatting functions. */
#define configSTATS_BUFFER_MAX_LENGTH                   0xFFFF

/* Define configASSERT() to enable assertion checking.  Useful during
 * development; can be removed for production to reduce code size. */
/* #define configASSERT( x )    if( ( x ) == 0 ) { taskDISABLE_INTERRUPTS(); for( ;; ); } */

/* configPRINTF - application-defined printf wrapper. */
/* #define configPRINTF( X )    printf X */

/*****************************************************************************
 *                       STREAM / MESSAGE BUFFERS                            *
 *****************************************************************************/

/* Set to 1 to enable per-instance send/receive-complete callbacks for
 * stream buffers and message buffers. */
#define configUSE_SB_COMPLETED_CALLBACK                 0

/* Type used for message buffer length fields. */
#define configMESSAGE_BUFFER_LENGTH_TYPE                size_t

/*****************************************************************************
 *                       THREAD-LOCAL STORAGE / C LIBRARY                    *
 *****************************************************************************/

/* Number of application-defined thread-local storage (TLS) pointer slots
 * in each task's TCB. */
#define configNUM_THREAD_LOCAL_STORAGE_POINTERS         0

/* Set to 1 to allocate a Newlib _reent structure for each task. */
#define configUSE_NEWLIB_REENTRANT                      0

/* Set to 1 to enable picolibc TLS integration. */
#define configUSE_PICOLIBC_TLS                          0

/* Set to 1 for generic C runtime TLS support.  When enabled, you must
 * also define configTLS_BLOCK_TYPE, configINIT_TLS_BLOCK,
 * configSET_TLS_BLOCK, and configDEINIT_TLS_BLOCK. */
#define configUSE_C_RUNTIME_TLS_SUPPORT                 0

/*****************************************************************************
 *                       MPU / SECURITY / ARM SETTINGS                       *
 *****************************************************************************/

/* Set to 1 to use MPU wrappers (version 1). */
#define configUSE_MPU_WRAPPERS_V1                       0

/* Set to 1 to enable the access control list for MPU ports. */
#define configENABLE_ACCESS_CONTROL_LIST                0

/* Set to 1 to enable the MPU (ARMv8-M ports). */
#define configENABLE_MPU                                0

/* Set to 1 to enable FPU support (ARMv8-M ports). */
#define configENABLE_FPU                                1

/* Set to 1 to enable MVE support (ARMv8.1-M ports). */
#define configENABLE_MVE                                0

/* Set to 1 to enable TrustZone support (ARMv8-M ports). */
#define configENABLE_TRUSTZONE                          1

/* Set to 1 to run FreeRTOS entirely in the secure side (no non-secure
 * callable functions). */
#define configRUN_FREERTOS_SECURE_ONLY                  0

/* Set to 1 to include application-defined functions that execute in
 * privileged mode. */
#define configINCLUDE_APPLICATION_DEFINED_PRIVILEGED_FUNCTIONS    0

/* FPU context management:
 *   1 = All tasks start with an FPU context (safe default).
 *   2 = FPU context allocated on first FPU instruction (saves RAM). */
#define configUSE_TASK_FPU_SUPPORT                      1

/*****************************************************************************
 *                       BACKWARD COMPATIBILITY / MISC                       *
 *****************************************************************************/

/* Set to 1 to include backward-compatible type names and macros from older
 * FreeRTOS versions. */
#define configENABLE_BACKWARD_COMPATIBILITY             1

/* Set to 1 to use mini list items for internal list optimization. */
#define configUSE_MINI_LIST_ITEM                        1

/* Set to 1 to enable POSIX errno support. */
#define configUSE_POSIX_ERRNO                           0

/* Set to 1 to include the "freertos_tasks_c_additions.h" header at the
 * bottom of tasks.c. */
#define configINCLUDE_FREERTOS_TASK_C_ADDITIONS_H       0

/* Legacy alternative queue API (deprecated). */
#define configUSE_ALTERNATIVE_API                       0

/*****************************************************************************
 *                   INCLUDE / EXCLUDE API FUNCTIONS                         *
 *                                                                           *
 * Set to 1 to include the function, or 0 to exclude it.  Excluding unused   *
 * functions reduces code size.  In most cases, the linker will remove        *
 * unused functions automatically.                                            *
 *****************************************************************************/

#define INCLUDE_vTaskPrioritySet                        1
#define INCLUDE_uxTaskPriorityGet                       1
#define INCLUDE_vTaskDelete                             1
#define INCLUDE_vTaskSuspend                            1
#define INCLUDE_xTaskDelayUntil                         1
#define INCLUDE_vTaskDelay                              1
#define INCLUDE_xTaskGetSchedulerState                  1
#define INCLUDE_xTaskGetCurrentTaskHandle               1
#define INCLUDE_uxTaskGetStackHighWaterMark             0
#define INCLUDE_uxTaskGetStackHighWaterMark2            0
#define INCLUDE_xTaskGetIdleTaskHandle                  0
#define INCLUDE_eTaskGetState                           0
#define INCLUDE_xTimerPendFunctionCall                  0
#define INCLUDE_xTaskAbortDelay                         0
#define INCLUDE_xTaskGetHandle                          0
#define INCLUDE_xTaskResumeFromISR                      1
#define INCLUDE_xQueueGetMutexHolder                    0
#define INCLUDE_xSemaphoreGetMutexHolder                0
#define INCLUDE_xTimerGetTimerDaemonTaskHandle          0
#define INCLUDE_vTaskCleanUpResources                   0

#endif /* FREERTOS_CONFIG_H */
