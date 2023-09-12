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
#ifndef GLOBAL_VARS_H
#define GLOBAL_VARS_H

#include "task.h"

#include <stdbool.h>

typedef struct tskTaskControlBlock       /* The old naming convention is used to prevent breaking kernel aware debuggers. */
{
    volatile StackType_t * pxTopOfStack; /*< Points to the location of the last item placed on the tasks stack.  THIS MUST BE THE FIRST MEMBER OF THE TCB STRUCT. */

    #if ( portUSING_MPU_WRAPPERS == 1 )
        xMPU_SETTINGS xMPUSettings; /*< The MPU settings are defined as part of the port layer.  THIS MUST BE THE SECOND MEMBER OF THE TCB STRUCT. */
    #endif

    ListItem_t xStateListItem;                  /*< The list that the state list item of a task is reference from denotes the state of that task (Ready, Blocked, Suspended ). */
    ListItem_t xEventListItem;                  /*< Used to reference a task from an event list. */
    UBaseType_t uxPriority;                     /*< The priority of the task.  0 is the lowest priority. */
    StackType_t * pxStack;                      /*< Points to the start of the stack. */
    char pcTaskName[ configMAX_TASK_NAME_LEN ]; /*< Descriptive name given to the task when created.  Facilitates debugging only. */ /*lint !e971 Unqualified char types are allowed for strings and single characters only. */

    #if ( ( portSTACK_GROWTH > 0 ) || ( configRECORD_STACK_HIGH_ADDRESS == 1 ) )
        StackType_t * pxEndOfStack; /*< Points to the highest valid address for the stack. */
    #endif

    #if ( portCRITICAL_NESTING_IN_TCB == 1 )
        UBaseType_t uxCriticalNesting; /*< Holds the critical section nesting depth for ports that do not maintain their own count in the port layer. */
    #endif

    #if ( configUSE_TRACE_FACILITY == 1 )
        UBaseType_t uxTCBNumber;  /*< Stores a number that increments each time a TCB is created.  It allows debuggers to determine when a task has been deleted and then recreated. */
        UBaseType_t uxTaskNumber; /*< Stores a number specifically for use by third party trace code. */
    #endif

    #if ( configUSE_MUTEXES == 1 )
        UBaseType_t uxBasePriority; /*< The priority last assigned to the task - used by the priority inheritance mechanism. */
        UBaseType_t uxMutexesHeld;
    #endif

    #if ( configUSE_APPLICATION_TASK_TAG == 1 )
        TaskHookFunction_t pxTaskTag;
    #endif

    #if ( configNUM_THREAD_LOCAL_STORAGE_POINTERS > 0 )
        void * pvThreadLocalStoragePointers[ configNUM_THREAD_LOCAL_STORAGE_POINTERS ];
    #endif

    #if ( configGENERATE_RUN_TIME_STATS == 1 )
        configRUN_TIME_COUNTER_TYPE ulRunTimeCounter; /*< Stores the amount of time the task has spent in the Running state. */
    #endif

    #if ( configUSE_C_RUNTIME_TLS_SUPPORT == 1 )
        configTLS_BLOCK_TYPE xTLSBlock; /**< Memory block used as Thread Local Storage (TLS) Block for the task. */
    #endif

    #if ( configUSE_TASK_NOTIFICATIONS == 1 )
        volatile uint32_t ulNotifiedValue[ configTASK_NOTIFICATION_ARRAY_ENTRIES ];
        volatile uint8_t ucNotifyState[ configTASK_NOTIFICATION_ARRAY_ENTRIES ];
    #endif

    /* See the comments in FreeRTOS.h with the definition of
     * tskSTATIC_AND_DYNAMIC_ALLOCATION_POSSIBLE. */
    #if ( tskSTATIC_AND_DYNAMIC_ALLOCATION_POSSIBLE != 0 ) /*lint !e731 !e9029 Macro has been consolidated for readability reasons. */
        uint8_t ucStaticallyAllocated;                     /*< Set to pdTRUE if the task is a statically allocated to ensure no attempt is made to free the memory. */
    #endif

    #if ( INCLUDE_xTaskAbortDelay == 1 )
        uint8_t ucDelayAborted;
    #endif

    #if ( configUSE_POSIX_ERRNO == 1 )
        int iTaskErrno;
    #endif
} tskTCB;


/* ===========================  DEFINES CONSTANTS  ========================== */
typedef tskTCB TCB_t;
typedef void (* port_yield_operation)( void );

/* ===========================  GLOBAL VARIABLES  =========================== */


/* ============================  MACRO FUNCTIONS  ============================ */
#define ASSERT_IF_IN_ISR_CALLED()                         \
    do {                                                  \
        TEST_ASSERT_TRUE( port_assert_if_in_isr_called ); \
        port_assert_if_in_isr_called = false;             \
    } while( 0 )
#define ASSERT_IF_IN_ISR_NOT_CALLED()                      \
    do {                                                   \
        TEST_ASSERT_FALSE( port_assert_if_in_isr_called ); \
    } while( 0 )

#define ASSERT_SETUP_TCB_CALLED()                  \
    do {                                           \
        TEST_ASSERT_TRUE( port_setup_tcb_called ); \
        port_setup_tcb_called = false;             \
    } while( 0 )
#define ASSERT_SETUP_TCB_NOT_CALLED()               \
    do {                                            \
        TEST_ASSERT_FALSE( port_setup_tcb_called ); \
    } while( 0 )

#define ASSERT_PORT_YIELD_CALLED()             \
    do {                                       \
        TEST_ASSERT_TRUE( port_yield_called ); \
        port_yield_called = false;             \
    } while( 0 )

#define ASSERT_PORT_YIELD_NOT_CALLED()          \
    do {                                        \
        TEST_ASSERT_FALSE( port_yield_called ); \
    } while( 0 )

#define ASSERT_PORT_ENABLE_INTERRUPT_CALLED()              \
    do {                                                   \
        TEST_ASSERT_TRUE( port_enable_interrupts_called ); \
        port_enable_interrupts_called = false;             \
    } while( 0 )

#define ASSERT_PORT_ENABLE_INTERRUPT_NOT_CALLED()           \
    do {                                                    \
        TEST_ASSERT_FALSE( port_enable_interrupts_called ); \
    } while( 0 )

#define ASSERT_PORT_DISABLE_INTERRUPT_CALLED()              \
    do {                                                    \
        TEST_ASSERT_TRUE( port_disable_interrupts_called ); \
        port_disable_interrupts_called = false;             \
    } while( 0 )

#define ASSERT_PORT_DISABLE_INTERRUPT_NOT_CALLED()           \
    do {                                                     \
        TEST_ASSERT_FALSE( port_disable_interrupts_called ); \
    } while( 0 )

#define ASSERT_PORT_YIELD_WITHIN_API_CALLED()             \
    do {                                                  \
        TEST_ASSERT_TRUE( port_yield_within_api_called ); \
        port_yield_within_api_called = false;             \
    } while( 0 )

#define ASSERT_PORT_YIELD_WITHIN_API_NOT_CALLED()          \
    do {                                                   \
        TEST_ASSERT_FALSE( port_yield_within_api_called ); \
    } while( 0 )

#define ASSERT_TASK_DELETE_CALLED()                \
    do {                                           \
        TEST_ASSERT_TRUE( vTaskDeletePre_called ); \
        vTaskDeletePre_called = false;             \
    } while( 0 )

#define ASSERT_TASK_DELETE_NOT_CALLED()             \
    do {                                            \
        TEST_ASSERT_FALSE( vTaskDeletePre_called ); \
    } while( 0 )

#define ASSERT_APP_TICK_HOOK_CALLED()                    \
    do {                                                 \
        TEST_ASSERT_TRUE( vApplicationTickHook_called ); \
        vApplicationTickHook_called = false;             \
    } while( 0 )

#define  ASSERT_APP_TICK_HOOK_NOT_CALLED()                \
    do {                                                  \
        TEST_ASSERT_FALSE( vApplicationTickHook_called ); \
    } while( 0 )

#define ASSERT_PORT_CLEAR_INTERRUPT_CALLED()            \
    do {                                                \
        TEST_ASSERT_TRUE( portClear_Interrupt_called ); \
        portClear_Interrupt_called = false;             \
    } while( 0 )
#define ASSERT_PORT_CLEAR_INTERRUPT_NOT_CALLED()         \
    do {                                                 \
        TEST_ASSERT_FALSE( portClear_Interrupt_called ); \
    } while( 0 )

#define ASSERT_PORT_CLEAR_INTERRUPT_FROM_ISR_CALLED()            \
    do {                                                         \
        TEST_ASSERT_TRUE( portClear_Interrupt_from_isr_called ); \
        portClear_Interrupt_from_isr_called = false;             \
    } while( 0 )
#define ASSERT_PORT_CLEAR_INTERRUPT_FROM_ISR_NOT_CALLED()         \
    do {                                                          \
        TEST_ASSERT_FALSE( portClear_Interrupt_from_isr_called ); \
    } while( 0 )

#define ASSERT_PORT_SET_INTERRUPT_FROM_ISR_CALLED()            \
    do {                                                       \
        TEST_ASSERT_TRUE( portSet_Interrupt_from_isr_called ); \
        portSet_Interrupt_from_isr_called = false;             \
    } while( 0 )
#define ASSERT_PORT_SET_INTERRUPT_FROM_ISR_NOT_CALLED()         \
    do {                                                        \
        TEST_ASSERT_FALSE( portSet_Interrupt_from_isr_called ); \
    } while( 0 )

#define ASSERT_PORT_SET_INTERRUPT_CALLED()            \
    do {                                              \
        TEST_ASSERT_TRUE( portSet_Interrupt_called ); \
        portSet_Interrupt_called = false;             \
    } while( 0 )
#define ASSERT_PORT_SET_INTERRUPT_NOT_CALLED()         \
    do {                                               \
        TEST_ASSERT_FALSE( portSet_Interrupt_called ); \
    } while( 0 )

#define ASSERT_INVALID_INTERRUPT_PRIORITY_CALLED()         \
    do {                                                   \
        TEST_ASSERT_TRUE( port_invalid_interrupt_called ); \
        port_invalid_interrupt_called = false;             \
    } while( 0 )

#define ASSERT_APPLICATION_IDLE_HOOK_CALLED()            \
    do {                                                 \
        TEST_ASSERT_TRUE( vApplicationIdleHook_called ); \
        vApplicationIdleHook_called = false;             \
    } while( 0 )

#define ASSERT_APPLICATION_IDLE_HOOK_NOT_CALLED()         \
    do {                                                  \
        TEST_ASSERT_FALSE( vApplicationIdleHook_called ); \
    } while( 0 )

#define ASSERT_APPLICATION_MALLOC_FAILED_HOOK_CALLED()           \
    do {                                                         \
        TEST_ASSERT_TRUE( vApplicationMallocFailedHook_called ); \
        vApplicationMallocFailedHook_called = false;             \
    } while( 0 )

#define ASSERT_APPLICATION_MALLOC_FAILED_HOOK_NOT_CALLED()        \
    do {                                                          \
        TEST_ASSERT_FALSE( vApplicationMallocFailedHook_called ); \
    } while( 0 )

#define ASSERT_PORT_ALLOCATE_SECURE_CONTEXT_CALLED()             \
    do {                                                         \
        TEST_ASSERT_TRUE( port_allocate_secure_context_called ); \
        port_allocate_secure_context_called = false;             \
    } while( 0 )

#define ASSERT_PORT_ALLOCATE_SECURE_CONTEXT_NOT_CALLED()          \
    do {                                                          \
        TEST_ASSERT_FALSE( port_allocate_secure_context_called ); \
    } while( 0 )

#define ASSERT_APP_STACK_OVERFLOW_HOOK_CALLED()                   \
    do {                                                          \
        TEST_ASSERT_TRUE( vApplicationStackOverflowHook_called ); \
        vApplicationStackOverflowHook_called = false;             \
    } while( 0 )

#define  ASSERT_APP_STACK_OVERFLOW_HOOK_NOT_CALLED()               \
    do {                                                           \
        TEST_ASSERT_FALSE( vApplicationStackOverflowHook_called ); \
    } while( 0 )

#define ASSERT_GET_IDLE_TASK_MEMORY_CALLED()          \
    do {                                              \
        TEST_ASSERT_TRUE( getIdleTaskMemory_called ); \
        getIdleTaskMemory_called = false;             \
    } while( 0 )

#define ASSERT_GET_IDLE_TASK_MEMORY_NOT_CALLED()       \
    do {                                               \
        TEST_ASSERT_FALSE( getIdleTaskMemory_called ); \
    } while( 0 )

#define RESET_ALL_HOOKS()                             \
    do {                                              \
        vApplicationTickHook_called = false;          \
        vTaskDeletePre_called = false;                \
        getIdleTaskMemory_called = false;             \
        port_yield_called = false;                    \
        port_enable_interrupts_called = false;        \
        port_disable_interrupts_called = false;       \
        port_yield_within_api_called = false;         \
        port_setup_tcb_called = false;                \
        portClear_Interrupt_called = false;           \
        portSet_Interrupt_called = false;             \
        portClear_Interrupt_from_isr_called = false;  \
        portSet_Interrupt_from_isr_called = false;    \
        port_invalid_interrupt_called = false;        \
        vApplicationStackOverflowHook_called = false; \
        port_allocate_secure_context_called = false;  \
        port_assert_if_in_isr_called = false;         \
    } while( 0 )

#define HOOK_DIAG()                            \
    do {                                       \
        printf( "%s Called\n", __FUNCTION__ ); \
    } while( 0 )

#undef HOOK_DIAG
#define HOOK_DIAG()

#endif /* ifndef GLOBAL_VARS_H */
