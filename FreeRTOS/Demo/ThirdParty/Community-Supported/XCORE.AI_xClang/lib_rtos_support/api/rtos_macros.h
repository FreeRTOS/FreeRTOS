// Copyright 2019-2021 XMOS LIMITED.
// This Software is subject to the terms of the XMOS Public Licence: Version 1.

#ifndef RTOS_MACROS_H_
#define RTOS_MACROS_H_

#include "rtos_support_rtos_config.h"

#define RTOS_STRINGIFY_I(...) #__VA_ARGS__
#define RTOS_STRINGIFY(...) RTOS_STRINGIFY_I(__VA_ARGS__)

/*
 * Inserts a compile time memory barrier
 */
#define RTOS_MEMORY_BARRIER() asm volatile( "" ::: "memory" )

/*
 * Returns the number of 32-bit stack words required by the given thread entry function.
 *
 * This will not just "work" if there is any recursion or function pointers in the thread.
 * For function pointers the fptrgroup attribute may be used. For recursive functions, the
 * "stackfunction" #pragma may be used.
 *
 * Example FreeRTOS usage:
 * xTaskCreate( vTask, "task_name", RTOS_THREAD_STACK_SIZE(vTask), pvParameters, uxPriority, &pxTaskHandle );
 */
#define RTOS_THREAD_STACK_SIZE(thread_entry) \
    ({ \
        uint32_t stack_size; \
        asm volatile ( \
                "ldc %0, " RTOS_STRINGIFY(thread_entry) ".nstackwords + " RTOS_STRINGIFY(RTOS_SUPPORT_INTERRUPT_STACK_GROWTH) "\n\t" \
                : "=r"(stack_size) /* output 0 is stack_size */ \
                : /* there are no inputs */ \
                : /* nothing gets clobbered */ \
        ); \
        stack_size; \
    })

#endif /* RTOS_MACROS_H_ */
