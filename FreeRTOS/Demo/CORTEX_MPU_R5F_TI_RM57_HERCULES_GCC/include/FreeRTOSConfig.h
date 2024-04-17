/*
 * FreeRTOS V202212.00
 * Copyright (C) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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

/* Section of the file that can't be included in ASM Pre-processor */
#ifndef FREERTOS_ASSEMBLY
    #include <stdint.h>
    #ifndef configASSERT

/* debug ASSERT The first option calls a function that prints to UART
 * The second one loops for when using a debugger. */
extern void vAssertCalled( const char * pcFileName, uint32_t ulLine );
        #define configASSERT( x )                    \
            if( ( x ) == pdFALSE )                   \
            {                                        \
                vAssertCalled( __func__, __LINE__ ); \
            }

extern void vMainSetupTimerInterrupt( void );
        #define configCLEAR_TICK_INTERRUPT()
        #define configSETUP_TICK_INTERRUPT() vMainSetupTimerInterrupt()
    #endif /* configASSERT */
#endif     /* FREERTOS_ASSEMBLY */

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
     * See http://www.freertos.org/a00110.html.
     *----------------------------------------------------------*/

    /** Code Composer Studio will throw errors about NULL not being defined.
     * as such wrap a define for NULL to 0 to remove the errors.
     */
    #ifndef NULL
        #define NULL 0x0
    #endif

    #define configENFORCE_SYSTEM_CALLS_FROM_KERNEL_ONLY            1U
    #define configALLOW_UNPRIVILEGED_CRITICAL_SECTIONS             0U
    #define configENABLE_ACCESS_CONTROL_LIST                       1U

    #define configENABLE_MPU                                       1U
    #define configENABLE_FPU                                       1U
    #define configUSE_MPU_WRAPPERS_V1                              0U
    #define configTOTAL_MPU_REGIONS                                16UL

    #define configNUMBER_OF_CORES                                  1U
    #define configUSE_PREEMPTION                                   1U
    #define configUSE_IDLE_HOOK                                    1U
    #define configUSE_DAEMON_TASK_STARTUP_HOOK                     0
    #define configUSE_TICK_HOOK                                    0
    #define configMAX_PRIORITIES                                   ( 30UL )
    #define configQUEUE_REGISTRY_SIZE                              10U
    #define configSUPPORT_STATIC_ALLOCATION                        1U
    #define configSUPPORT_DYNAMIC_ALLOCATION                       0U

    #define configCPU_CLOCK_HZ                                     ( 110000000U )
    #define configTICK_RATE_HZ                                     ( 1000U )
    #define configMINIMAL_STACK_SIZE                               ( 0x80 )
    #define configSYSTEM_CALL_STACK_SIZE                           configMINIMAL_STACK_SIZE
    #define configTOTAL_HEAP_SIZE                                  ( ( 80 * 512 ) )
    #define configMAX_TASK_NAME_LEN                                ( 0x20U )
    #define configUSE_TRACE_FACILITY                               0U
    #define configUSE_16_BIT_TICKS                                 0
    #define configIDLE_SHOULD_YIELD                                0
    #define configUSE_CO_ROUTINES                                  0
    #define configUSE_MUTEXES                                      1U
    #define configUSE_RECURSIVE_MUTEXES                            1U
    #define configUSE_EVENT_GROUPS                                 0U
    #define configCHECK_FOR_STACK_OVERFLOW                         0
    #define configUSE_QUEUE_SETS                                   1U
    #define configUSE_COUNTING_SEMAPHORES                          1U
    #define configUSE_PORT_OPTIMISED_TASK_SELECTION                1U
    #define configUSE_POSIX_ERRNO                                  0
    #define configUSE_TIME_SLICING                                 0
    #define configUSE_C_RUNTIME_TLS_SUPPORT                        0
    #define configUSE_NEWLIB_REENTRANT                             0
    #define configINCLUDE_FREERTOS_TASK_C_ADDITIONS_H              0
    #define configUSE_MALLOC_FAILED_HOOK                           0
    #define configHEAP_CLEAR_MEMORY_ON_FREE                        0
    #define configSTACK_ALLOCATION_FROM_SEPARATE_HEAP              0
    #define configAPPLICATION_ALLOCATED_HEAP                       0
    #define configUSE_SB_COMPLETED_CALLBACK                        0
    #define configRUN_MULTIPLE_PRIORITIES                          0
    #define configINCLUDE_APPLICATION_DEFINED_PRIVILEGED_FUNCTIONS 0
    #define configPRE_SUPPRESS_TICKS_AND_SLEEP_PROCESSING          0
    #define configNUM_THREAD_LOCAL_STORAGE_POINTERS                0
    #define configUSE_MINI_LIST_ITEM                               0
    #define configPROTECTED_KERNEL_OBJECT_POOL_SIZE                0x20UL

    /* Timer related defines. */
    #define configUSE_TIMERS                                       1
    #define configTIMER_TASK_PRIORITY                              ( configMAX_PRIORITIES - 6UL )
    #define configTIMER_QUEUE_LENGTH                               20
    #define configTIMER_TASK_STACK_DEPTH                           ( configMINIMAL_STACK_SIZE * 2 )
    #define INCLUDE_xTimerGetTimerDaemonTaskHandle                 1
    #define INCLUDE_xTimerPendFunctionCall                         1

    #define configUSE_TASK_NOTIFICATIONS                           1
    #define configTASK_NOTIFICATION_ARRAY_ENTRIES                  3

/* Set the following definitions to 1 to include the API function, or zero
 * to exclude the API function. */

    #define INCLUDE_vTaskPrioritySet                               1
    #define INCLUDE_uxTaskPriorityGet                              1
    #define INCLUDE_vTaskDelete                                    1
    #define INCLUDE_vTaskCleanUpResources                          0
    #define INCLUDE_vTaskSuspend                                   1
    #define INCLUDE_xTaskDelayUntil                                1
    #define INCLUDE_vTaskDelay                                     1
    #define INCLUDE_uxTaskGetStackHighWaterMark                    1
    #define INCLUDE_xTaskGetSchedulerState                         1
    #define INCLUDE_xTaskGetIdleTaskHandle                         1
    #define INCLUDE_xSemaphoreGetMutexHolder                       1
    #define INCLUDE_eTaskGetState                                  1
    #define INCLUDE_xTaskAbortDelay                                1
    #define INCLUDE_xTaskGetHandle                                 1

    /** Note: These value come from the Board Support Package. They are pulled directly
     * from sys_vim.h, and reg_vim.h. These values correspond to hardware registers
     * and keys exclusive to the board that this demo was written for.
     */

    /** @brief Address of MCU Register used to mark the end of an IRQ */
    #define configEOI_ADDRESS                                      0xFFFFFE70UL

    /** @brief Address of Real Time Interrupt (RTI) used for the system clock */
    #define configRTI_ADDRESS                                      0xFFFFFC88UL

    /** @brief Value used to clear a RTI Interrupt */
    #define configRTI_CLEAR_VALUE                                  0x1

    /** @brief Address of Register used to trigger Software Interrupts (SWI) */
    #define configSWI_ADDRESS                                      0xFFFFFFB0UL

    /** @brief Key value that is written to the SWI Interrupt Register */
    #define configSWI_KEY_VAL                                      0x7500UL

    /** @brief Address of Register used to clear SWI Interrupts */
    #define configSWI_CLEAR_ADDRESS                                0xFFFFFFF4UL

    /** @brief Value to write to clear a Software Interrupt (SWI) */
    #define configSWI_CLEAR_VAL                                    0x0

    /** @brief Trigger a pending context swap from inside an ISR */
    #define portYIELD_FROM_ISR( x )                          \
        if( x != pdFALSE )                                   \
        {                                                    \
            configPEND_YIELD_REG = configPEND_YIELD_KEY_VAL; \
            ( void ) configPEND_YIELD_REG;                   \
        }

#endif /* FREERTOS_CONFIG_H */
